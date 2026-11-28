'use strict';

const assert = require('node:assert/strict');
const c = require('./codec');

// Both interpreters receive the same declared mappings, faults and storage
// facts. Callback results never become inputs to the other interpreter.
function lookupOptions(m, facts) {
  const has = (paths, p) => paths?.some(path => m.sameName(path, p)) === true;
  const valueAt = (entries, p) => entries?.find(([path]) => m.sameName(path, p))?.[1];
  const options = { ...facts.credential, authority: facts.authority, asWritten: facts.asWritten ?? [],
    asWrittenTypes: facts.asWrittenTypes, handlerResolvesResiduals: facts.handlerResolvesResiduals,
    nonprojecting: key => facts.nonprojectingKeys?.includes(key) === true,
    isIndirect: p => has(facts.indirect, p),
    resolvePrefix(p) {
      if (has(facts.resolverErrors, p)) throw Error('resolver unavailable');
      if (!has(facts.indirect, p)) return undefined;
      return facts.mappings?.find(row => m.sameName(row.supplied, p))?.canonical ?? null;
    }
  };
  if (facts.ceiling !== undefined) options.ceiling = facts.ceiling;
  if (facts.nameVisibility !== undefined || facts.invisible?.length) {
    options.canName = p => !has(facts.invisible, p) &&
      (facts.nameVisibility === undefined || valueAt(facts.nameVisibility, p) === true);
  }
  if (facts.knownFacts) options.attrsOf = p => {
    if (facts.rowReads && valueAt(facts.rowReads, p) !== true) throw Error('attributes unavailable');
    return {};
  };
  if (facts.faultOutcomesByPath) options.faults = (rule, target) =>
    facts.faultOutcomesByPath.find(entry => entry.rule === rule && m.sameName(entry.path, target))?.fault;
  else if (facts.faults) options.faults = rule => facts.faults.includes(rule);
  return options;
}

function runLookupCases(api, evidence, rng) {
  const m = api.MODEL;
  const source = { ...api.FIXTURE, methods: api.FIXTURE.methods.map(method => method.name === 'GetWidget'
    ? { ...method, authz: { standard: { wildcardVariables: ['team'] } } } : method) };
  const interpretations = new WeakMap();
  function register(declarations, model) {
    const wire = c.descriptor(declarations, model);
    interpretations.set(wire, model);
    return wire;
  }
  const I = m.interpret(source, { fieldGuards: true }), descriptor = register(source, I);
  if (I.errors.length) throw Error(I.errors.join(', '));
  const totals = { cases: 0, privateTwins: 0, matches: 0, misses: 0, collisions: 0 };
  for (let i = 0; i < 128; i++) {
    const parent = ['companies', 'A' + rng.int(8), 'teams', 'B'], prefix = [...parent, 'widgets'];
    const other = [...parent.slice(0,3), 'C', 'widgets', '1'];
    const name = [...prefix, '1'], alias = [...prefix, 'me'], wildcard = [...parent.slice(0,3), '-', 'widgets', '1'];
    const row = (name, owner) => ({ name, predicates: [['owner', owner]], secondaryNames: [] });
    const grant = (key, effect = 'permit', extra = {}) => ({ path: [], keys: [key], effect, ...extra });
    function compare(method, request, rules, storage, key, supplied, status, options = {}) {
      const { descriptor: wire = descriptor, ...facts } = options;
      const model = interpretations.get(wire);
      assert.ok(model, 'every public lookup needs a source descriptor');
      const store = { possibleNames: [], createDestination: null, ...storage };
      const actual = m.handleResourceRequest(rules, model, method, request, store, lookupOptions(m, facts));
      const expectedError = status === 'OK' ? null : JSON.parse(m.errorPayload(status, key, supplied.join('/'), model.apiService));
      assert.deepEqual(JSON.parse(JSON.stringify(actual)), { status, error: expectedError }, method + ' fixture');
      const nativeStore = { ...store, possibleNames: store.possibleNames.map(([name, range]) => [name, c.domain(range)]) };
      const native = { ...facts, indirect: facts.indirect ?? [], mappings: facts.mappings ?? [],
        asWritten: c.domain(facts.asWritten ?? []) };
      if (facts.faults) native.faults = facts.faults.map(c.rule);
      if (facts.faultOutcomesByPath) native.faultOutcomesByPath = facts.faultOutcomesByPath.map(f => ({ ...f, rule: c.rule(f.rule) }));
      evidence.compare({ op: 'lookupRequest', descriptor: wire, method, request, rules: rules.map(c.rule), store: nativeStore, ...native },
        { status: c.status(actual.status), error: actual.error });
      totals.cases++;
      return actual;
    }
    const actor = 'widgets.get';
    const allowed = rng.int(2) === 1, list = rng.int(2) === 1;
    const rules = [grant(actor, 'permit', {pred:'owner'})];
    if (list) rules.push(grant('widgets.list'));
    const raw = (policy, target, owner, exists) => m.readStatus({ exists,
      target: exists ? m.authorize(policy, actor, target, { owner: owner ? 'alice' : 'other' }) : 'UNKNOWN',
      parentList: m.authorize(policy, 'widgets.list', parent) });
    compare('GetWidget', {name}, rules, {rows:[row(name, allowed)]}, actor, name, raw(rules, name, allowed, true));
    if (i === 0) {
      const readModel = declarations => {
        const model = m.interpret(declarations, {fieldGuards:true});
        if (model.errors.length) throw Error(model.errors.join(', '));
        return {model, descriptor:register(declarations, model)};
      };
      const interpret = declarations => readModel(declarations).descriptor;
      const access = (model, method, req, rules, options = {}) => m.authorizeRequest(rules,model,method,req,
        {attrsOf:()=>({}), ...options}).decision === 'PROCEED' ? 'ALLOW' : 'DENY';
      const createStatus = (model, req, rules, exists, get = 'GetWidget') => m.createStatus({
        authorized:access(model,'CreateWidget',req,rules) === 'ALLOW', nameTaken:exists,
        getExisting:access(model,get,{name},rules), listParent:access(model,'ListWidgets',{parent},rules)
      });
      // A parent_target denial echoes a supplied alias first; a direct name echoes its derived parent.
      const attach = readModel({ required: true, resources: {
        Company: { type: 'widgets.example/Company', plural: 'companies', patterns: ['companies/{company}'] },
        Widget: { type: 'widgets.example/Widget', plural: 'widgets', patterns: ['widgets/{widget}', 'companies/{company}/widgets/{widget}'] } },
        methods: [{ name: 'AttachWidget', request: { widget: { resource: 'Widget' } }, authz: { requirements: [
          { accessClass: 'UPDATE', operation: 'update', targetField: 'widget.name' },
          { accessClass: 'CREATE', operation: 'create', targetField: 'widget.name', parentTarget: true }] } }] });
      const latest = ['widgets', 'latest'], topWidget = ['widgets', 'w1'], nestedWidget = ['companies', 'A', 'widgets', 'w1'];
      for (const [requested, stored, supplied] of [[latest, topWidget, latest], [latest, nestedWidget, latest],
        [topWidget, topWidget, []], [nestedWidget, nestedWidget, nestedWidget.slice(0, 2)]]) {
        const via = m.sameName(requested, latest) ? { indirect: [latest], mappings: [{ supplied: latest, canonical: stored }] } : {};
        compare('AttachWidget', { 'widget.name': requested }, [grant('widgets.update')], { rows: [row(stored, true)] },
          'widgets.create', supplied, 'PERMISSION_DENIED', { descriptor: attach.descriptor, ...via });
      }
      // Parent List may disclose absence only after Get's decisive forbids are checked.
      const riskyForbid = grant(actor, 'forbid', {mayError:true});
      const listable = [grant(actor), riskyForbid, grant('widgets.list')];
      for (const authority of ['failClosed', 'skipErrors']) for (const fault of [undefined, false, true]) {
        const opts = fault === undefined ? {authority} : {authority, faults:() => fault};
        const wire = fault === undefined ? {authority} : {authority, faults:fault ? [riskyForbid] : []};
        for (const exists of [false, true]) {
          const status = m.readStatus({exists, target:m.authorize(listable, actor, name, {}, opts),
            parentList:m.authorize(listable, 'widgets.list', parent, {}, opts)});
          assert.equal(status, authority === 'skipErrors' && fault === true ?
            (exists ? 'OK' : 'NOT_FOUND') : 'PERMISSION_DENIED');
          compare('GetWidget', {name}, listable, {rows:exists ? [row(name, true)] : []}, actor, name,
            status, {...wire, knownFacts:true});
        }
      }
      const users = {resources:{User:{type:'example.test/User',plural:'users',patterns:['me/{user}','profiles/{user}']}},
        methods:[{name:'GetUser',request:{name:{type:'User'}},authz:{standard:{}}}]};
      const {model:userModel,descriptor:userDescriptor} = readModel(users);
      const user = ['me','bob'], canonicalUser = ['profiles','bob'], userKey = 'users.get';
      const policy = [grant(userKey)], badSite = ['me'];
      for (const bad of [null, [], canonicalUser]) for (const exists of [false,true]) {
        const callback = path => {
          if (m.sameName(path,badSite)) return bad;
        };
        const gate = m.authorizeRequest(policy,userModel,'GetUser',{name:user},{resolvePrefix:callback});
        const status = m.readStatus({exists, target:gate.decision === 'PROCEED' ? 'ALLOW' : 'DENY'});
        assert.equal(status,exists ? 'OK' : 'NOT_FOUND');
        const response = compare('GetUser',{name:user},policy,{rows:exists?[row(user,true)]:[],
          possibleNames:[[user,[canonicalUser]]]},userKey,user,status,
          {descriptor:userDescriptor,indirect:[badSite],mappings:[{supplied:badSite,canonical:bad}]});
        if (!exists) assert.equal(response.error.domain,'example.test');
      }
      for (const failed of [[],badSite,user]) {
        const gate = m.authorizeRequest(policy,userModel,'GetUser',{name:user},{resolvePrefix:p => {
          if (m.sameName(p,failed)) throw Error('unavailable');
        }});
        const status = m.readStatus({exists:true, target:gate.decision === 'PROCEED' ? 'ALLOW' : 'DENY'});
        assert.equal(status,failed === user ? 'PERMISSION_DENIED' : 'OK');
        compare('GetUser',{name:user},policy,{rows:[row(user,true)]},userKey,user,status,
          {descriptor:userDescriptor,resolverErrors:[failed]});
      }
      // An as-written resource ID may join its indexed row. A collection
      // spelling may not move a resource between these two declared patterns.
      for (const [stored,asWritten,status] of [
        [canonicalUser,[badSite],'NOT_FOUND'], [['me','owner'],[['me','*']],'OK'],
        [['me','owner'],[user],'NOT_FOUND']
      ]) {
        const indexed = {...row(stored,true),secondaryNames:[user]};
        compare('GetUser',{name:user},policy,{rows:[indexed]},userKey,user,status,
          {descriptor:userDescriptor,asWritten:asWritten});
      }
      const type = 'people.example/User', people = {apiService:'people.example',resources:{
        User:{type,plural:'users',patterns:['companies/{company}/users/{user}','directory/{user}']},
        Device:{type:'people.example/Device',plural:'devices',patterns:['companies/{company}/users/{user}/devices/{device}']}
      },methods:[{name:'GetUser',request:{name:{type:'User'}},authz:{standard:{}}}]};
      const {model:peopleModel,descriptor:peopleDescriptor} = readModel(people);
      const owner = ['companies','A'], email = [...owner,'users','name@acme.example'], opaque = [...owner,'users','u123'];
      const options = {asWrittenTypes:[type],descriptor:peopleDescriptor,indirect:[email],mappings:[{supplied:email,canonical:null}]};
      const peopleRules = [{path:owner,keys:[userKey],effect:'permit'}];
      const userRow = {...row(opaque,true),secondaryNames:[email]};
      for (const site of [null,opaque,email,[...opaque,'devices','D'],['directory','u123']]) {
        const policy = site ? [...peopleRules,{path:site,keys:[userKey],effect:'forbid'}] : peopleRules;
        for (const name of [opaque,email]) {
          const server = m.authorizeRequest(policy,peopleModel,'GetUser',{name},{asWrittenTypes:[type],
            resolvePrefix:p => m.sameName(p,email) ? null : undefined});
          const status = m.readStatus({exists:true,target:server.decision === 'PROCEED' ? 'ALLOW' : 'DENY'});
          assert.equal(status,site ? 'PERMISSION_DENIED' : 'OK');
          compare('GetUser',{name},policy,{rows:[userRow]},userKey,name,status,options);
        }
      }
      const scopedUser = [{...grant(userKey),path:user}];
      compare('GetUser',{name:user},scopedUser,{rows:[row(user,true)]},userKey,user,'OK',
        {descriptor:userDescriptor,asWritten:[badSite]});
      const alternate = ['lanes','L','widgets','relocated'];
      const twoPaths = interpret({...source, resources:{...source.resources, Widget:{...source.resources.Widget,
        patterns:[...source.resources.Widget.patterns,'lanes/{lane}/widgets/{widget}']}}});
      for (const [method,key,missing] of [['GetWidget',actor,'NOT_FOUND'],['DeleteWidget','widgets.delete','OK']]) {
        const req = {name:alias, allow_missing:true}, rules = [grant(key)];
        const wrongInput = ['profiles','alias'];
        const checkMapping = (supplied, canonical) => {
          const result = m.authorizeRequest(rules, I, method, {...req, name:supplied}, {
            resolvePrefix:p => m.sameName(p, supplied) ? canonical : undefined
          });
          const status = result.decision === 'PROCEED' ? 'OK' : 'PERMISSION_DENIED';
          assert.equal(status, 'PERMISSION_DENIED');
          return status;
        };
        compare(method,{...req,name:wrongInput},rules,{rows:[row(name,true)]},key,wrongInput,checkMapping(wrongInput,name),
          {indirect:[wrongInput],mappings:[{supplied:wrongInput,canonical:name}]});
        for (const invalid of [[], ['companies'], parent, [...prefix,'..'], [...name,'bogus']]) {
          compare(method,req,rules,{rows:[]},key,alias,checkMapping(alias,invalid),
            {indirect:[alias],mappings:[{supplied:alias,canonical:invalid}]});
        }
        for (const rows of [[],[row(name,true)]]) {
          compare(method,req,rules,{rows,possibleNames:[[alias,[other]]]},key,alias,'PERMISSION_DENIED',
            {indirect:[alias],mappings:[{supplied:alias,canonical:name}]});
        }
        for (const mapped of [null,alternate]) for (const exists of [false,true]) {
          const rows = exists ? [row(alternate,true)] : [];
          compare(method,req,rules,{rows,possibleNames:[[alias,[alternate]]]},key,alias,
            mapped && exists ? 'OK' : missing,{descriptor:twoPaths,indirect:[alias],mappings:[{supplied:alias,canonical:mapped}]});
        }
      }
      const multiWild = ['companies','-','teams','-','widgets','1'];
      const manyVariables = interpret({...source,methods:source.methods.map(method => method.name === 'GetWidget'
        ? {...method,authz:{standard:{wildcardVariables:['company','team']}}} : method)});
      for (const authority of ['failClosed','skipErrors']) {
        for (const [method,key,absent] of [['GetWidget',actor,'NOT_FOUND'],['DeleteWidget','widgets.delete','OK']]) {
          const permit = grant(key,'permit',{pred:'owner'}), forbid = grant(key,'forbid',{pred:'owner'});
          const matched = [permit,forbid,grant('widgets.list')];
          const req = supplied => ({name:supplied,allow_missing:true});
          const options = {authority,indirect:[alias]};
          const variants = [[name,{authority}], [alias,options]];
          if (method === 'GetWidget') variants.push([wildcard,{authority}], [multiWild,{authority,descriptor:manyVariables}]);
          for (const [supplied,base] of variants) {
            for (const owns of [null,false,true]) {
              const hit = owns !== null, rows = hit ? [row(name,owns)] : [];
              const mappings = hit && supplied === alias ? [{supplied:alias,canonical:name}] : [];
              const owners = [false,true].map(owns => m.authorize(matched,key,name,
                {owner:owns ? 'alice' : 'other'},{authority}));
              assert.deepEqual(owners,['DENY','DENY']);
              const expected = hit ? m.readStatus({exists:true,target:owners[Number(owns)]})
                : m.zeroMatchStatus({region:owners[0],regionList:m.authorize(matched,'widgets.list',parent),
                  deleteAllowMissing:method === 'DeleteWidget'});
              compare(method,req(supplied),matched,{rows},key,supplied,expected,{...base,mappings});
            }
          }

          // A different permit at one descendant remains visible through the
          // enclosing cell's hole. The other pattern can have a different depth.
          const range = [[...prefix,'*'],['lanes','*','widgets','*']];
          const store = {rows:[],possibleNames:[[alias,range]]};
          const mixed = [...matched,{...grant(key),path:alternate}];
          compare(method,req(alias),matched,store,key,alias,'PERMISSION_DENIED',{...options,descriptor:twoPaths});
          compare(method,req(alias),mixed,store,key,alias,absent,{...options,descriptor:twoPaths});
          for (const [canonical,status] of [[name,'PERMISSION_DENIED'],[alternate,'OK']])
            compare(method,req(alias),mixed,{...store,rows:[row(canonical,false)]},key,alias,status,
              {...options,descriptor:twoPaths,mappings:[{supplied:alias,canonical}]});

          // A hidden predicate or a nonprojecting operation cannot establish a
          // public regime of denial. The caller can still list every candidate.
          for (const [policy,privacy] of [[matched,{nonprojectingKeys:[key]}],
            [[permit,{...forbid,hidden:true},grant('widgets.list')],{}]]) {
            compare(method,req(alias),policy,{rows:[]},key,alias,absent,{...options,...privacy});
            compare(method,req(alias),policy,{rows:[row(name,true)]},key,alias,'PERMISSION_DENIED',
              {...options,...privacy,mappings:[{supplied:alias,canonical:name}]});
          }
          compare(method,req(alias),[...matched,grant(key,'forbid')],{rows:[]},key,alias,'PERMISSION_DENIED',
            {...options,nonprojectingKeys:[key]});

          const uncertain = {...forbid,mayError:true}, policy = [permit,uncertain,grant('widgets.list')];
          for (const names of [[name],[other],[name,other]]) for (const fault of [true,false,null]) {
            const outcomes = names.map(path => ({path,rule:uncertain,fault:m.sameName(path,other) ? fault : false}));
            const results = names.flatMap(path => [true,false].map(owns => m.authorize(policy,key,path,
              {owner:owns ? 'alice' : 'other'},{authority,faults:(_,at) => outcomes.find(o => m.sameName(o.path,at)).fault})));
            const reason = results.every(result => result === 'DENY') ? 'DENY' : 'UNKNOWN';
            const status = m.zeroMatchStatus({region:reason,regionList:'ALLOW',deleteAllowMissing:method === 'DeleteWidget'});
            compare(method,req(alias),policy,{rows:[],possibleNames:[[alias,names]]},key,alias,status,
              {...options,faultOutcomesByPath:outcomes});
          }
          // Each fixed candidate has its own observed result. A public
          // absence proof here cannot borrow a Get or List grant.
          const possiblePermit = grant(key,'permit',{mayError:true}), fixed = [name,other];
          for (const second of [true,false,null]) {
            const observations = fixed.map(path => ({path,rule:possiblePermit,fault:m.sameName(path,name) ? false : second}));
            const results = fixed.map(path => m.authorize([possiblePermit],key,path,{},
              {authority,faults:(_,target) => observations.find(o => m.sameName(o.path,target)).fault}));
            const region = results.every(result => result === results[0]) ? results[0] : 'UNKNOWN';
            const status = m.zeroMatchStatus({region,regionList:'DENY',deleteAllowMissing:method === 'DeleteWidget'});
            assert.equal(status,second === false ? absent : 'PERMISSION_DENIED');
            compare(method,req(alias),[possiblePermit],{rows:[],possibleNames:[[alias,fixed]]},key,alias,status,
              {...options,faultOutcomesByPath:observations});
            if (second === false) {
              compare(method,req(alias),[possiblePermit],{rows:[],possibleNames:[[alias,fixed]]},key,alias,
                'PERMISSION_DENIED',{...options,faultOutcomesByPath:observations,nonprojectingKeys:[key]});
              compare(method,req(alias),[possiblePermit],{rows:[],possibleNames:[[alias,[[...prefix,'*']]]]},key,alias,
                'PERMISSION_DENIED',{...options,faultOutcomesByPath:observations});
            }
          }
          const allFaulted = fixed.map(path => ({path,rule:uncertain,fault:true}));
          compare(method,req(alias),[grant(key),uncertain],{rows:[],possibleNames:[[alias,fixed]]},key,alias,
            authority === 'skipErrors' ? absent : 'PERMISSION_DENIED',{...options,faultOutcomesByPath:allFaulted});
          const list = grant('widgets.list','permit',{mayError:true}), parents = fixed.map(n => n.slice(0,-2));
          for (const second of [true,false]) {
            const listFaults = parents.map((path,i) => ({path,rule:list,fault:i === 0 ? false : second}));
            compare(method,req(alias),[permit,list],{rows:[],possibleNames:[[alias,fixed]]},key,alias,
              second ? 'PERMISSION_DENIED' : absent,{...options,faultOutcomesByPath:listFaults});
          }
          const broad = [[...parent.slice(0,3),'*','widgets','*']];
          const oneFault = [{path:other,rule:uncertain,fault:true}];
          compare(method,req(alias),policy,{rows:[],possibleNames:[[alias,broad]]},key,alias,
            'PERMISSION_DENIED',options);
          compare(method,req(alias),policy,{rows:[],possibleNames:[[alias,broad]]},key,alias,
            authority === 'skipErrors' ? absent : 'PERMISSION_DENIED',{...options,faultOutcomesByPath:oneFault});
          compare(method,req(alias),policy,{rows:[row(other,true)],possibleNames:[[alias,broad]]},key,alias,
            authority === 'skipErrors' ? 'OK' : 'PERMISSION_DENIED',
            {...options,mappings:[{supplied:alias,canonical:other}],faultOutcomesByPath:oneFault});
        }
      }
      const aliasParent = [...parent.slice(0,-1),'mine'];
      for (const [range,status] of [[parent,'ALREADY_EXISTS'],[other.slice(0,-2),'PERMISSION_DENIED']]) {
        compare('CreateWidget',{parent:aliasParent,populated:[]},[grant('widgets.create'),grant('widgets.get')],
          {rows:[row(name,true)],createDestination:name,possibleNames:[[aliasParent,[range]]]},
          'widgets.create',aliasParent,status,{indirect:[aliasParent],mappings:[{supplied:aliasParent,canonical:parent}]});
      }
      const companyTarget = name.slice(0,2);
      const companyRules = [grant('companies.get','permit',{pred:'owner'}),grant('companies.list')];
      const companyMissing = m.readStatus({exists:false, target:m.projectCell(companyRules,'companies.get',companyTarget),
        parentList:m.authorize(companyRules,'companies.list',[])});
      compare('GetCompany',{name:companyTarget},companyRules,{rows:[]},'companies.get',companyTarget,companyMissing);
      const count = {name:'CountWidgets',authz:{requirements:[{operation:'list',accessClass:'READ'}]},
        request:{parent:{childType:'Widget'}}};
      const inspect = {name:'InspectWidget',authz:{requirements:[{operation:'get',accessClass:'READ'}]},
        request:{name:{type:'Widget'}}};
      // Each read probe supplies only its own address. A separate parent field
      // can bind the service root, even when the Widget address is under a team.
      const candidates = [name,other], possible = [[alias,candidates]];
      for (const list of [false,true]) for (const [field, role, hasRoot] of [
        ['billing_parent',{childType:'Company'},true], ['billing_parent',{childType:'Team'},false],
        ['billing_company',{type:'Company'},false]
      ]) {
        const rpc = list ? 'ListWidgets' : 'GetWidget', address = list ? 'parent' : 'name';
        const key = (role.childType === 'Team' ? 'teams' : 'companies') + '.readDirectory';
        const secondary = {targetField:field,operation:'readDirectory',accessClass:'ADMIN'};
        const read = {name:rpc, request:{[address]:list ? {childType:'Widget'} : {type:'Widget'},[field]:role},
          authz:{requirements:[secondary]}};
        const {model,descriptor} = readModel({resources:source.resources,methods:[inspect,read]});
        for (const [prefix, ceiling, hidden, discovered] of [
          [[],null,false,hasRoot], [parent,null,false,false], [[],['READ'],false,false], [[],null,true,false]
        ]) {
          const policy = [grant(actor,'permit',{pred:'owner'}),{...grant(key),path:prefix}];
          const proves = candidates.every(n => {
            const probe = {[address]:list ? n.slice(0,-2) : n};
            const response = m.authorizeRequest(policy,model,rpc,probe,{attrsOf:()=>({}),ceiling});
            return response.decision === 'PROCEED' && !response.residuals.length;
          });
          const proof = list ? {regionList:proves?'ALLOW':'UNKNOWN',nonprojectingList:hidden}
            : {regionGet:proves?'ALLOW':'UNKNOWN',nonprojectingGet:hidden};
          const miss = m.zeroMatchStatus({region:'UNKNOWN',...proof});
          assert.equal(miss,discovered?'NOT_FOUND':'PERMISSION_DENIED');
          const options = {descriptor,indirect:[alias],credential:{ceiling},nonprojectingKeys:hidden?[key]:[]};
          compare(inspect.name,{name:alias},policy,{rows:[],possibleNames:possible},actor,alias,miss,options);
          for (const owns of [false,true]) {
            const gate = m.authorizeRequest(policy,model,inspect.name,{name},{ceiling,attrsOf:() => ({owner:owns?'alice':'other'})});
            const hit = m.readStatus({exists:true,target:gate.decision === 'PROCEED' && !gate.residuals.length ? 'ALLOW':'DENY'});
            assert.equal(hit,owns?'OK':'PERMISSION_DENIED');
            compare(inspect.name,{name:alias},policy,{rows:[row(name,owns)],possibleNames:possible},actor,alias,hit,
              {...options,mappings:[{supplied:alias,canonical:name}]});
          }
        }
      }
      // Parent-of on the supplied Get address still follows each candidate's
      // actual parent. Access to B alone cannot prove visibility in B and C.
      const scopedRead = {name:'GetWidget',request:{name:{type:'Widget'},billing_parent:{childType:'Company'}},
        authz:{requirements:[{operation:'readDirectory',accessClass:'READ',targetField:'billing_parent'},
          {operation:'readTeam',accessClass:'READ',targetField:'name',parentTarget:true}]}};
      const directoryRead = readModel({resources:source.resources,methods:[inspect,scopedRead]});
      for (const both of [false,true]) {
        const policy = [grant(actor,'permit',{pred:'owner'}),grant('companies.readDirectory'),
          {...grant('widgets.readTeam'),path:both ? parent.slice(0,2) : parent}];
        const allowed = candidates.map(n => access(directoryRead.model,scopedRead.name,{name:n},policy));
        assert.deepEqual(allowed,['ALLOW',both?'ALLOW':'DENY']);
        const miss = m.zeroMatchStatus({region:'UNKNOWN',regionGet:allowed.every(a=>a==='ALLOW')?'ALLOW':'UNKNOWN'});
        compare(inspect.name,{name:alias},policy,{rows:[],possibleNames:possible},actor,alias,miss,
          {descriptor:directoryRead.descriptor,indirect:[alias]});
      }
      const noReads = interpret({...source,methods:[...source.methods.filter(m =>
        !['ListWidgets','GetWidget','CountWidgets'].includes(m.name)),count,inspect]});
      const extraRead = {operation:'inspectCatalog',accessClass:'READ',serviceRoot:true};
      const restrictedReads = interpret({...source,methods:source.methods.map(method => {
        if (!['GetWidget','ListWidgets'].includes(method.name)) return method;
        const list = method.name === 'ListWidgets';
        return {...method,authz:{requirements:[{operation:list?'list':'get',accessClass:'READ',
          targetField:list?'parent':'name'},extraRead]}};
      })});
      const expunge = grant('widgets.expunge','permit',{pred:'owner'});
      const adminInventory = {operation:'inspectInventory',accessClass:'ADMIN',serviceRoot:true};
      const adminKey = 'service.inspectInventory';
      const proofParent = [...parent.slice(0,3),'-'];
      const range = [[...parent.slice(0,3),'*','widgets','*']];
      for (const noSideEffects of [false,true]) for (const optional of [false,true]) {
        const requirements = optional ? [{operation:'list',accessClass:'READ',targetField:'parent'},
          {...adminInventory,condition:'details'}] : [adminInventory];
        const {model,descriptor} = readModel({...source,methods:source.methods.map(method => method.name === 'ListWidgets'
          ? {...method,noSideEffects,request:{...method.request,details:true},authz:{requirements}} : method)});
        const key = optional ? 'widgets.list' : adminKey;
        for (const ceiling of [null,['READ']]) {
          const policy = [grant(key),grant(actor,'permit',{pred:'owner'})];
          const parentList = access(model,'ListWidgets',{parent},policy,{ceiling});
          const status = m.readStatus({exists:false,target:m.projectCell(policy,actor,name),parentList});
          assert.equal(status,optional || ceiling === null ? 'NOT_FOUND' : 'PERMISSION_DENIED');
          compare('GetWidget',{name},policy,{rows:[]},actor,name,status,{descriptor,credential:{ceiling}});
          if (optional) assert.equal(access(model,'ListWidgets',{parent,details:true},policy,{ceiling}),'DENY');
        }
      }
      for (const noSideEffects of [false,true]) for (const rpc of ['GetWidget','ListWidgets']) {
        const list = rpc === 'ListWidgets';
        const target = {operation:'view',accessClass:'READ',targetField:list?'parent':'name',
          ...(list ? {wildcardVariables:['team']} : {})};
        const {model,descriptor} = readModel({...source,methods:source.methods.map(method => method.name === rpc
          ? {...method,noSideEffects,authz:{requirements:[target,adminInventory]}} : method)});
        const witness = list ? {parent} : {name};
        const key = 'widgets.view';
        for (const [keys,ceiling,allowed] of [
          [[key,adminKey],null,true], [[key,adminKey],['READ','CREATE','ADMIN'],true],
          [[key,adminKey],['READ','CREATE'],false], [[adminKey],null,false], [[key],null,false]
        ]) {
          const requirements = keys.map(k => grant(k)), opts = {ceiling};
          const read = access(model,rpc,witness,requirements,opts), declared = read === 'ALLOW';
          assert.equal(declared,allowed);
          const wire = {descriptor,credential:opts};
          const creates = [...requirements,grant('widgets.create')], req = {parent,populated:[]};
          const collision = m.createStatus({authorized:access(model,'CreateWidget',req,creates,opts) === 'ALLOW',
            nameTaken:true,getExisting:list?'DENY':read,listParent:list?read:'DENY'});
          assert.equal(collision,allowed?'ALREADY_EXISTS':'PERMISSION_DENIED');
          compare('CreateWidget',req,creates,{rows:[row(name,true)],createDestination:name},'widgets.create',parent,collision,wire);
          if (list) {
            const ownerOnly = grant(actor,'permit',{pred:'owner'}), rules = [ownerOnly,...requirements];
            const miss = m.readStatus({exists:false,target:m.projectCell(rules,actor,name),parentList:read});
            assert.equal(miss,allowed?'NOT_FOUND':'PERMISSION_DENIED');
            compare('GetWidget',{name},rules,{rows:[]},actor,name,miss,wire);
            const regionList = access(model,rpc,{parent:proofParent},rules,opts);
            const zero = m.zeroMatchStatus({region:'UNKNOWN',regionGet:'UNKNOWN',regionList});
            assert.equal(zero,miss);
            compare('GetWidget',{name:alias},rules,{rows:[],possibleNames:[[alias,range]]},actor,alias,zero,
              {...wire,indirect:[alias]});
            compare('GetWidget',{name:wildcard},rules,{rows:[]},actor,wildcard,
              m.wildcardGetStatus({matches:0,regionGet:'UNKNOWN',regionList}),wire);
          }
        }
      }
      for (const [schema,allowsExtra,visible] of [[noReads,true,false],[restrictedReads,false,false],[restrictedReads,true,true]]) {
        const extras = allowsExtra ? [grant('service.inspectCatalog')] : [];
        const rules = [expunge,grant('widgets.list'),grant('widgets.get'),...extras];
        compare('ExpungeWidget',{name},rules,{rows:[]},'widgets.expunge',name,
          visible?'NOT_FOUND':'PERMISSION_DENIED',{descriptor:schema});
        compare('ExpungeWidget',{name:alias},rules,{rows:[]},'widgets.expunge',alias,
          visible?'NOT_FOUND':'PERMISSION_DENIED',{descriptor:schema,indirect:[alias]});
        for (const read of ['widgets.get','widgets.list']) {
          compare('CreateWidget',{parent,populated:[]},[grant('widgets.create'),grant(read),...extras],
            {rows:[row(name,true)],createDestination:name},'widgets.create',parent,
            visible?'ALREADY_EXISTS':'PERMISSION_DENIED',{descriptor:schema});
        }
      }
      // Real read RPCs can select their own authorization keys. A restricted
      // view also needs a root permission; the full-view flag is absent here.
      const overrides = interpret({...source,methods:source.methods.map(method => {
        if (!['GetWidget','ListWidgets'].includes(method.name)) return method;
        const list = method.name === 'ListWidgets';
        return {...method,request:{...method.request,full_view:true},authz:{requirements:[
          {operation:list?'enumerate':'inspect',accessClass:'READ',targetField:list?'parent':'name'},
          extraRead, {...extraRead,operation:'fullView',condition:'full_view'}
        ]}};
      })});
      for (const [key, allowed] of [['widgets.get',false],['widgets.list',false],
                                    ['widgets.inspect',true],['widgets.enumerate',true]]) {
        for (const hasExtra of [false,true]) {
          const extra = hasExtra ? [grant('service.inspectCatalog')] : [];
          const visible = hasExtra && allowed;
          compare('CreateWidget',{parent,populated:[]},[grant('widgets.create'),grant(key),...extra],
            {rows:[row(name,true)],createDestination:name},'widgets.create',parent,
            visible?'ALREADY_EXISTS':'PERMISSION_DENIED',{descriptor:overrides});
          compare('ExpungeWidget',{name:alias},[expunge,grant(key),...extra],{rows:[]},'widgets.expunge',alias,
            visible?'NOT_FOUND':'PERMISSION_DENIED',{descriptor:overrides,indirect:[alias]});
        }
      }
      const inventoryKey = 'service.readInventory';
      const inventory = {operation:'readInventory',accessClass:'READ',serviceRoot:true};
      for (const prefix of ['', 'widgets.v1.Widgets/']) {
        const get = prefix + 'GetWidget';
        const {model, descriptor:rootRead} = readModel({...source,methods:source.methods.map(m => m.name === 'GetWidget' ?
          {...m,name:get,authz:{requirements:[inventory]}} : m)});
        for (const entitled of [false,true]) {
          const policy = entitled ? [grant(inventoryKey)] : [grant(actor)];
          const descriptor = rootRead;
          for (const exists of [false,true]) {
            const status = m.readStatus({exists,target:access(model,get,{name},policy)});
            assert.equal(status,entitled ? (exists ? 'OK' : 'NOT_FOUND') : 'PERMISSION_DENIED');
            compare(get,{name},policy,{rows:exists ? [row(name,true)] : []},inventoryKey,
              entitled ? name : [],status,{descriptor});
          }
          const req = {parent,populated:[]}, creates = [grant('widgets.create'),...policy];
          const status = createStatus(model,req,creates,true,get);
          assert.equal(status,entitled?'ALREADY_EXISTS':'PERMISSION_DENIED');
          compare('CreateWidget',req,creates,
            {rows:[row(name,true)],createDestination:name},'widgets.create',parent,
            status,{descriptor});
          compare('ExpungeWidget',{name:alias},[expunge,...policy],{rows:[]},'widgets.expunge',alias,
            entitled?'NOT_FOUND':'PERMISSION_DENIED',{descriptor,indirect:[alias]});
        }
        compare(get,{name:parent},[grant(inventoryKey)],{rows:[row(parent,true)]},inventoryKey,[],
          'PERMISSION_DENIED',{descriptor:rootRead});
      }
      const rootList = interpret({...source,methods:source.methods.map(m => m.name === 'ListWidgets' ?
        {...m,authz:{requirements:[inventory]}} : m)});
      for (const entitled of [false,true]) {
        const policy = [expunge,...(entitled?[grant(inventoryKey)]:[grant('widgets.list')])];
        compare('ExpungeWidget',{name},policy,{rows:[]},'widgets.expunge',name,
          entitled?'NOT_FOUND':'PERMISSION_DENIED',{descriptor:rootList});
      }
      const parentCreate = {operation:'provision',accessClass:'CREATE',targetField:'parent'};
      const rootCreate = {operation:'provisionInventory',accessClass:'CREATE',serviceRoot:true};
      const rootCreateKey = 'service.provisionInventory';
      for (const declared of [[parentCreate],[rootCreate,parentCreate],[rootCreate]]) {
        const {model,descriptor} = readModel({...source,methods:source.methods.map(m => m.name === 'CreateWidget' ?
          {...m,authz:{requirements:declared}} : m)});
        const parentGate = declared.includes(parentCreate);
        const keys = declared.map(r => r === parentCreate ? 'widgets.provision' : rootCreateKey);
        const primary = parentGate ? 'widgets.provision' : rootCreateKey, diagnostic = parentGate ? parent : [];
        for (const exists of [false,true]) for (const visible of [false,true]) {
          const store = {rows:exists ? [row(name,true)] : [],createDestination:name};
          const rules = [...keys.map(k => grant(k)),...(visible?[grant(actor)]:[])];
          const req = {parent,populated:[]}, status = createStatus(model,req,rules,exists);
          assert.equal(status,!exists?'OK':visible?'ALREADY_EXISTS':'PERMISSION_DENIED');
          compare('CreateWidget',req,rules,store,primary,diagnostic,status,{descriptor});
          for (const missing of keys) {
            const restricted = rules.filter(r => !r.keys.includes(missing));
            const denied = createStatus(model,req,restricted,exists);
            assert.equal(denied,'PERMISSION_DENIED');
            compare('CreateWidget',req,restricted,store,missing,missing === rootCreateKey ? [] : parent,denied,{descriptor});
          }
        }
        for (const hasGuard of [false,true]) {
          const rules = [...keys.map(k => grant(k)),...(hasGuard?[grant('widgets.setOwner')]:[])];
          const req = {parent,populated:['owner']}, status = createStatus(model,req,rules,false);
          assert.equal(status,hasGuard?'OK':'PERMISSION_DENIED');
          compare('CreateWidget',req,rules,{rows:[],createDestination:name},
            hasGuard?primary:'widgets.setOwner',hasGuard?diagnostic:parent,status,{descriptor});
        }
        const wrongParent = ['profiles','missing'];
        compare('CreateWidget',{parent:wrongParent,populated:[]},keys.map(k => grant(k)),
          {rows:[],createDestination:name},primary,parentGate?wrongParent:[],
          'PERMISSION_DENIED',{descriptor,indirect:[wrongParent],mappings:[{supplied:wrongParent,canonical:parent}]});
      }
      const explicitUpdate = interpret({...source,methods:source.methods.map(m => m.name === 'UpdateWidget' ?
        {...m,authz:{requirements:[{operation:'editInventory',accessClass:'UPDATE',targetField:'widget.name'}]}} : m)});
      const edit = 'widgets.editInventory', create = 'widgets.create', fieldGuard = 'widgets.setOwner';
      for (const exists of [false,true]) for (const allow_missing of [false,true]) {
        const req = {'widget.name':name,allow_missing,update_mask:['owner'],populated:['owner']};
        const store = {rows:exists?[row(name,true)]:[]};
        compare('UpdateWidget',req,[grant(edit),grant(create),grant(fieldGuard)],store,edit,name,
          exists || allow_missing?'OK':'NOT_FOUND',{descriptor:explicitUpdate});
        compare('UpdateWidget',req,[grant(edit),grant(fieldGuard)],store,edit,name,
          exists || allow_missing?'OK':'NOT_FOUND',{descriptor:explicitUpdate});
        compare('UpdateWidget',req,[grant(edit),grant(create)],store,fieldGuard,name,'PERMISSION_DENIED',{descriptor:explicitUpdate});
      }
      const legacy = structuredClone(descriptor);
      for (const method of legacy.methods.filter(m => m.name === 'GetWidget' || m.name === 'DeleteWidget')) {
        delete method.resourceTarget;
        delete method.requestShapeKnown;
        delete method.requestFields;
        delete method.partialSource;
      }
      // A modern roster identifies both declarations as standard and requires their derived addresses.
      evidence.control({op:'descriptor',descriptor:structuredClone(legacy)},false);
      // A boolean cannot supply the reflected method declaration.
      for (const entry of legacy.declaredMethods) {
        if (entry[0] === 'GetWidget' || entry[0] === 'DeleteWidget') entry[1]=false;
      }
      evidence.control({op:'descriptor',descriptor:legacy},false);
      compare('DeleteWidget',{name,allow_missing:true},[grant('widgets.delete')],{rows:[]},'widgets.delete',name,'OK');
      compare('CreateWidget',{parent,populated:[]},[grant('widgets.create'),grant(actor)],
        {rows:[row(name,true)],createDestination:name},'widgets.create',parent,'ALREADY_EXISTS');
      const stream = interpret({...source,methods:source.methods.map(m => m.name === 'GetWidget' ?
        {...m,serverStreaming:true,authz:{requirements:[{operation:'get',accessClass:'READ',targetField:'name'}]}} : m)});
      compare('CreateWidget',{parent,populated:[]},[grant('widgets.create'),grant(actor)],
        {rows:[row(name,true)],createDestination:name},'widgets.create',parent,'PERMISSION_DENIED',{descriptor:stream});
      // The permission uses name as a Widget identifier. The request field has no
      // resource annotation, so this explicit RPC cannot disclose a Create collision.
      const customGet = interpret({...source,methods:source.methods.map(method => method.name === 'GetWidget' ?
        {...method,request:{name:{}},authz:{requirements:[{accessClass:'READ',operation:'get',resourceType:'Widget',targetField:'name'}]}} : method)});
      const collision = (wire,reflected,expected) => {
        evidence.control({op:'descriptor',descriptor:wire},false);
        compare('CreateWidget',{parent,populated:[]},[grant('widgets.create'),grant(actor)],
          {rows:[row(name,true)],createDestination:name},'widgets.create',parent,expected,{descriptor:reflected});
      };
      for (const retained of [undefined, null, {}]) {
        const wire=structuredClone(customGet), method=wire.methods.find(m => m.name === 'GetWidget');
        delete method.requestShapeKnown;
        method.partialSource=retained;
        collision(wire,customGet,'PERMISSION_DENIED');
      }
      for (const [retained,expected] of [
        [{serverStreaming:true},'PERMISSION_DENIED'],
        [{response:'Unrelated'},'PERMISSION_DENIED'], [{response:'Widget'},'ALREADY_EXISTS']
      ]) {
        const wire=structuredClone(legacy), method=wire.methods.find(m => m.name === 'GetWidget');
        method.partialSource=retained;
        const reflected = interpret({...source, methods:source.methods.map(method => method.name === 'GetWidget' ? {
          ...method, returns: retained.response, serverStreaming: retained.serverStreaming,
          authz: {requirements:[{accessClass:'READ', operation:'get', targetField:'name'}]}
        } : method)});
        collision(wire,reflected,expected);
      }
      const rootFirst = interpret({...source,methods:source.methods.map(method => method.name !== 'ListWidgets' ? method :
        {...method,authz:{requirements:[
          {operation:'viewCollection',accessClass:'READ',resourceType:'Widget',serviceRoot:true},
          {operation:'list',accessClass:'READ',targetField:'parent'}
        ]}})});
      for (const entitled of [false,true]) {
        const rules = [expunge, grant('widgets.list'), ...(entitled?[grant('widgets.viewCollection')]:[])];
        compare('ExpungeWidget',{name},rules,{rows:[]},'widgets.expunge',name,
          entitled?'NOT_FOUND':'PERMISSION_DENIED',{descriptor:rootFirst});
      }
      const first = { operation: 'get', accessClass: 'READ', targetField: 'name' };
      const related = { operation: 'get', accessClass: 'READ', targetField: 'related', wildcardVariables: ['company'] };
      const relatedParent = { operation: 'list', accessClass: 'READ', targetField: 'related', parentTarget: true };
      const twoTargets = (name, secondary) => ({ name, authz: { requirements: [first, secondary] },
        request: { name: { type: 'Widget' }, related: { type: 'Team' } } });
      const extended = { ...source, methods: [...source.methods,
        twoTargets('InspectRelatedTeam', related), twoTargets('InspectRelatedParent', relatedParent)] };
      const model = m.interpret(extended, {fieldGuards:true});
      if (model.errors.length) throw Error(model.errors.join(', '));
      const multi = register(extended, model);
      const reference = ['companies','shared','teams','public'];
      const team = ['companies','elsewhere','teams','private'], company = team.slice(0,2);
      const scoped = (key, path, extra = {}) => ({...grant(key), path, ...extra});
      const aliases = {indirect:[reference],mappings:[{supplied:reference,canonical:team}]};
      const teamKey = 'teams.get', parentKey = 'teams.list', itemKey = 'widgets.get';
      const inspection = 'widgets.inspect';
      const checkBoth = (secondField, wildcards = []) => interpret({...source, methods:source.methods.map(method =>
        method.name === 'GetWidget' ? {...method, request:{...method.request, related:{type:'Widget'}},
          authz:{requirements:[
            {...first, wildcardVariables:wildcards},
            {operation:'inspect',accessClass:'READ',targetField:secondField,wildcardVariables:wildcards}
          ]}} : method)});
      const twoFields = checkBoth('related');
      const inspectOwner = grant(inspection,'permit',{pred:'owner'});
      const sameAddress = {name,related:name};
      const seeCollection = grant('widgets.list');
      for (const present of [false,true]) {
        const store = {rows:present ? [row(name,true)] : []};
        compare('GetWidget',sameAddress,[grant(actor),inspectOwner,seeCollection],store,
          inspection,name,present ? 'OK' : 'PERMISSION_DENIED',{descriptor:twoFields});
      }
      // The independent field's absence is assessed without the selected row
      // when the addressed check on that row has already failed.
      const reviewRequired = grant(actor,'permit',{pred:'reviewer'});
      const pendingReview = { ...row(name,true), predicates:[['owner',true],['reviewer',false]] };
      compare('GetWidget',sameAddress,[reviewRequired,inspectOwner,seeCollection],{rows:[pendingReview]},
        inspection,name,'PERMISSION_DENIED',{descriptor:twoFields});

      const sameField = checkBoth('name',['team']);
      const twoChecks = [grant(actor),inspectOwner];
      for (const [target,rows,options] of [
        [wildcard,[row(name,true),row(other,true)],{}],
        [alias,[],{indirect:[alias],resolverErrors:[alias]}],
        [alias,[],{indirect:[alias]}]
      ]) {
        compare('GetWidget',{name:target},twoChecks,{rows},inspection,target,
          'PERMISSION_DENIED',{descriptor:sameField,...options});
      }
      for (const readable of [false,true]) {
        const opts = {indirect:[alias],mappings:[{supplied:alias,canonical:name}],
          knownFacts:true,rowReads:[[name,readable]]};
        compare('GetWidget',{name:alias},[grant(actor)],{rows:[row(name,true)]},actor,alias,'OK',opts);
        compare('GetWidget',{name:alias},[grant(actor)],{rows:[],possibleNames:[[alias,[name]]]},
          actor,alias,'NOT_FOUND',{...opts,mappings:[]});
        compare('GetWidget',{name:alias},[grant(actor,'permit',{pred:'owner'})],{rows:[row(name,true)]},
          actor,alias,readable ? 'OK' : 'PERMISSION_DENIED',opts);
      }
      const guardedWrite = {'widget.name':name,allow_missing:true,update:{mask:['owner'],populated:['owner']}};
      const parentAndGuard = [grant('widgets.update'),grant('widgets.create'),
        grant('widgets.setOwner','permit',{pred:'owner'}),seeCollection];
      compare('UpdateWidget',guardedWrite,parentAndGuard,{rows:[row(parent,true)]},
        'widgets.setOwner',name,'PERMISSION_DENIED');
      const namedParents = [parent,other.slice(0,-2)];
      const createOwned = [grant('widgets.update'),grant('widgets.create','permit',{pred:'owner'}),seeCollection];
      const byAlias = {'widget.name':alias,allow_missing:true,update:{mask:['display_name'],populated:['display_name']}};
      for (const candidates of [[name],[name,other]]) for (const ownsOthers of [false,true]) {
        const rows = [row(namedParents[0],true),row(namedParents[1],ownsOthers)];
        const allParentsAllowed = candidates.length === 1 || ownsOthers;
        compare('UpdateWidget',byAlias,createOwned,{rows,possibleNames:[[alias,candidates]]},
          'widgets.update',alias,allParentsAllowed ? 'NOT_FOUND' : 'PERMISSION_DENIED',{indirect:[alias]});
      }
      for (const hasPrimary of [false, true]) {
        const rows = hasPrimary ? [row(name,true)] : [], status = hasPrimary ? 'OK' : 'NOT_FOUND';
        for (const [method, key, authorizedSite, wrongSite] of [
          ['InspectRelatedTeam', teamKey, team, reference],
          ['InspectRelatedParent', parentKey, company, reference.slice(0,2)]
        ]) {
          const req = {name, related:reference};
          compare(method,req,[grant(itemKey),scoped(key,authorizedSite)],{rows},itemKey,name,status,
            {descriptor:multi,...aliases});
          compare(method,req,[grant(itemKey),scoped(key,authorizedSite)],{rows,possibleNames:[[reference,[reference]]]},
            key,reference,'PERMISSION_DENIED',{descriptor:multi,...aliases});
          const hidden = compare(method,req,[grant(itemKey),scoped(key,wrongSite)],{rows},key,reference,'PERMISSION_DENIED',
            {descriptor:multi,...aliases});
          const absent = compare(method,req,[grant(itemKey),scoped(key,wrongSite)],{rows},key,reference,'PERMISSION_DENIED',
            {descriptor:multi,indirect:[reference]});
          if (JSON.stringify(hidden) !== JSON.stringify(absent)) throw Error('Ancillary alias leaked its mapping');
          compare(method,req,[grant(itemKey),grant(key)],{rows},key,reference,'PERMISSION_DENIED',
            {descriptor:multi,indirect:[reference]});
          totals.privateTwins++;
        }
        const spelling = [...team.slice(0,-1),'account'], condition = grant(teamKey,'permit',{pred:'owner',mayError:true});
        const secondary = {...row(team,true),secondaryNames:[spelling]};
        const asWritten = [[...team.slice(0,-1),'*']];
        const req = {name,related:spelling};
        for (const visible of [false,true]) {
          const joined = [...rows, {...secondary,predicates:[['owner',visible]]}];
          const options = {descriptor:multi,asWritten,authority:'skipErrors',
            faultOutcomesByPath:[{path:team,rule:condition,fault:false}]};
          compare('InspectRelatedTeam',req,[grant(itemKey),condition],{rows:joined},
            visible ? itemKey : teamKey, visible ? name : spelling,visible ? status : 'PERMISSION_DENIED',options);
          if (!visible) compare('InspectRelatedTeam',req,[grant(itemKey),condition],{rows},
            teamKey,spelling,'PERMISSION_DENIED',options);
        }
        // The secondary wildcard is still a RESOLVE_WILDCARD handoff at this
        // boundary. Merely registering a handler cannot authorize the lookup.
        const multiWild = {name,related:['companies','-','teams','private']};
        for (const permits of [[grant(itemKey)], [grant(itemKey),grant(teamKey)]]) {
          const handoff = m.authorizeRequest(permits,model,'InspectRelatedTeam',multiWild,{handlerResolvesResiduals:true});
          if (!handoff.residuals.some(x => x.kind === 'RESOLVE_WILDCARD')) throw Error('Expected a wildcard handoff');
          compare('InspectRelatedTeam',multiWild,permits,{rows},teamKey,multiWild.related,'PERMISSION_DENIED',
            {descriptor:multi,handlerResolvesResiduals:true});
        }
      }
      // Any outstanding wildcard handoff also blocks Create, upsert, and Delete's no-op.
      const primary = {
        CreateWidget:{operation:'create',accessClass:'CREATE',targetField:'parent'},
        UpdateWidget:{operation:'update',accessClass:'UPDATE',targetField:'widget.name'},
        DeleteWidget:{operation:'delete',accessClass:'DELETE',targetField:'name'}
      };
      const wildcardRef = ['companies','-','teams','private'];
      for (const [method, request, key, target, rs] of [
        ['CreateWidget',{parent},teamKey,wildcardRef,[grant('widgets.create')]],
        ['UpdateWidget',{'widget.name':name,allow_missing:true},teamKey,wildcardRef,[grant('widgets.update'),grant('widgets.create'),grant('widgets.setOwner')]],
        ['DeleteWidget',{name,allow_missing:true},teamKey,wildcardRef,[grant('widgets.delete')]]
      ]) {
        const guarded = interpret({...extended,methods:extended.methods.map(x => x.name === method ?
          {...x,request:{...x.request,related:{type:'Team'}},authz:{requirements:[primary[method],related]}} : x)});
        compare(method,{...request,related:wildcardRef},rs,{rows:[],createDestination:name},key,target,
          'PERMISSION_DENIED',{descriptor:guarded,handlerResolvesResiduals:true});
        if (method === 'CreateWidget') for (const rows of [[], [row(name,true)]]) {
          const supplied = {...request, related:wildcardRef}, store = {rows, createDestination:name};
          const opts = {descriptor:guarded, handlerResolvesResiduals:true, knownFacts:true, rowReads:[]};
          compare(method,supplied,[],store,'widgets.create',parent,'PERMISSION_DENIED',opts);
          compare(method,supplied,[grant('widgets.create','permit',{pred:'owner'})],store,teamKey,
            wildcardRef,'PERMISSION_DENIED',opts);
        }
      }
      for (const allow_missing of [true,false]) {
        const req = {'widget.name':alias,update_mask:['owner'],populated:['owner'],allow_missing};
        for (const rows of [[],[row(name,true)]]) {
          const opts = {descriptor:multi,indirect:[alias],mappings:[{supplied:alias,canonical:name}]};
          compare('UpdateWidget',req,[grant('widgets.update'),grant('widgets.create')],{rows},
            allow_missing?'widgets.update':'widgets.setOwner',alias,'PERMISSION_DENIED',opts);
        }
      }
      for (const prefix of ['', 'widgets.v1.Widgets/']) for (const suffix of ['', 'Attachment']) {
        const method = prefix + 'DeleteWidget' + suffix;
        const source = { ...api.FIXTURE, methods: api.FIXTURE.methods.map(m =>
          m.name === 'DeleteWidget' ? { ...m, name: method, authz: suffix ? { requirements: [
            {operation: 'delete', accessClass: 'DELETE', targetField: 'name'}
          ] } : m.authz } : m) };
        const model = m.interpret(source);
        if (model.errors.length) throw Error(model.errors.join(', '));
        const descriptor = register(source, model), key = 'widgets.delete';
        const permit = [grant(key)];
        for (const [allow_missing, rules, expected] of [
          [true, permit, suffix ? 'NOT_FOUND' : 'OK'], [false, permit, 'NOT_FOUND'], [true, [], 'PERMISSION_DENIED']
        ]) {
          compare(method, { name, allow_missing }, rules, { rows: [] }, key, name, expected, { descriptor });
        }
      }
      // Delete is identified by the RPC and its declared name field, even
      // when the first requirement protects an independent root or resource.
      for (const prefix of ['', 'widgets.v1.Widgets/']) for (const suffix of ['', 'Attachment']) {
        const rpc = prefix + 'DeleteWidget' + suffix;
        const remove = {operation:'remove',accessClass:'DELETE',targetField:'name'};
        const secondary = {operation:'inspectTeam',accessClass:'READ',targetField:'team'};
        for (const first of (suffix ? [null] : [null,inventory,secondary])) {
          const descriptor = interpret({...source,methods:source.methods.map(m => m.name === 'DeleteWidget' ?
            {...m,name:rpc,request:{...m.request,team:{type:'Team'},allow_missing:true},
              authz:{requirements:first ? [first,remove] : [remove]}} : m)});
          const initialKey = first === inventory ? inventoryKey : first === secondary ? 'teams.inspectTeam' : 'widgets.remove';
          for (const allow_missing of [false,true]) {
            const req = {name,team:parent,allow_missing};
            const policy = first ? [grant(initialKey),grant('widgets.remove')] : [grant('widgets.remove')];
            compare(rpc,req,policy,{rows:[]},'widgets.remove',name,allow_missing && !suffix?'OK':'NOT_FOUND',{descriptor});
            compare(rpc,req,first ? [grant(initialKey)] : [],{rows:[]},'widgets.remove',name,'PERMISSION_DENIED',{descriptor});
            if (first) compare(rpc,req,[grant('widgets.remove')],{rows:[]},initialKey,first === inventory ? [] : parent,
              'PERMISSION_DENIED',{descriptor});
          }
        }
      }
      for (const prefix of ['', 'widgets.v1.Widgets/']) {
        const rpc = prefix + 'DeleteWidget', key = 'service.manageInventory';
        const descriptor = interpret({...source,methods:source.methods.map(m => m.name === 'DeleteWidget' ?
          {...m,name:rpc,authz:{requirements:[{operation:'manageInventory',accessClass:'ADMIN',serviceRoot:true}]}} : m)});
        for (const allow_missing of [false,true]) {
          compare(rpc,{name,allow_missing},[grant(key)],{rows:[]},key,name,allow_missing?'OK':'NOT_FOUND',{descriptor});
          compare(rpc,{name,allow_missing},[],{rows:[]},key,[],'PERMISSION_DENIED',{descriptor});
        }
      }
      const publicParent = ['companies','mine'], actualParent = parent.slice(0,2);
      const supplied = [...publicParent,...parent.slice(2),'widgets','short'];
      const policyName = [...prefix,'short'];
      for (const readable of [true,false]) {
        const opts = {knownFacts:true, rowReads:[[name,readable]]};
        const attrsOf = () => {
          if (!readable) throw Error('unavailable row');
          return {owner:'alice'};
        };
        const policy = [grant(actor)];
        const auth = m.authorizeRequest(policy,I,'GetWidget',{name},{attrsOf});
        for (const exists of [true,false]) {
          const status = m.readStatus({exists, target:auth.decision === 'PROCEED' ? 'ALLOW' : 'DENY'});
          assert.equal(status, exists ? 'OK' : 'NOT_FOUND');
          compare('GetWidget',{name},policy,{rows:exists ? [row(name,true)] : []},actor,name,status,opts);
        }
        // An unconditional permission also settles an indexed Get and collision
        // disclosure even when the selected row's attributes are unavailable.
        const indexedRow = {...row(name,true),secondaryNames:[policyName]};
        compare('GetWidget',{name:policyName},[grant(actor)],{rows:[indexedRow]},actor,policyName,
          'OK',
          {...opts, rowReads:[[policyName,!readable],[name,readable]], asWritten:[[...prefix,'*']]});
        const create = [grant('widgets.create'),...policy], request = {parent,populated:[]};
        const status = m.createStatus({nameTaken:true,
          authorized:m.authorizeRequest(create,I,'CreateWidget',request,{attrsOf:()=>({})}).decision === 'PROCEED',
          getExisting:auth.decision === 'PROCEED' ? 'ALLOW' : 'DENY', listParent:m.authorize(create,'widgets.list',parent)});
        assert.equal(status, 'ALREADY_EXISTS');
        compare('CreateWidget',request,create,{rows:[row(name,true)],createDestination:name},'widgets.create',parent,
          status,{...opts,rowReads:[[parent,true],[name,readable]]});
      }
      for (const allowed of [true,false]) {
        const indexedRow = { ...row(name,allowed), secondaryNames:[policyName] };
        const rs = [grant(actor,'permit',{pred:'owner'})];
        const auth = m.authorizeRequest(rs,I,'GetWidget',{name:supplied}, {
          resolvePrefix:p => m.sameName(p,publicParent) ? actualParent : undefined,
          attrsOf:p => m.sameName(p,policyName) ? {owner:allowed?'alice':'no'} : {}
        });
        compare('GetWidget',{name:supplied},rs,{rows:[indexedRow]},actor,supplied,
          auth.decision === 'PROCEED' ? 'OK' : 'PERMISSION_DENIED',
          {indirect:[publicParent],mappings:[{supplied:publicParent,canonical:actualParent}],asWritten:[[...prefix,'*']]});
      }
      for (const authority of ['failClosed','skipErrors']) {
        const ownerPermit = grant(actor,'permit',{pred:'owner'});
        const parentList = grant('widgets.list');
        for (const observation of ['infallible','omitted',null,false,true]) {
          const forbid = grant(actor,'forbid',{pred:'owner',mayError:observation !== 'infallible'});
          const policy = [ownerPermit,forbid,parentList];
          const options = {authority}, native = {authority,knownFacts:true};
          if (typeof observation === 'boolean' || observation === null) {
            options.faults = () => observation;
            native.faultOutcomesByPath = [{path:name,rule:forbid,fault:observation}];
          }
          const ownerDecisions = [false,true].map(owns => m.authorize(policy,actor,name,
            {owner:owns ? 'alice' : 'other'},options));
          const canPass = authority === 'skipErrors' && observation === true;
          assert.deepEqual(ownerDecisions, ['DENY',canPass ? 'ALLOW' : 'DENY']);
          for (const owns of [null,false,true]) {
            const rows = owns === null ? [] : [row(name,owns)];
            const decision = owns === null ? (ownerDecisions.includes('ALLOW') ? 'UNKNOWN' : 'DENY')
              : ownerDecisions[Number(owns)];
            const status = m.readStatus({exists:owns !== null,target:decision,
              parentList:m.authorize(policy,'widgets.list',parent)});
            let reads = 0;
            const auth = m.authorizeRequest(policy,I,'GetWidget',{name},{...options,attrsOf:() => {
              reads++; return {owner:owns ? 'alice' : 'other'};
            }});
            if (!canPass) {
              assert.equal(auth.reason,'POLICY');
              assert.equal(reads,0);
            }
            compare('GetWidget',{name},policy,{rows},actor,name,status,native);
          }
        }

        // Two independent stored predicates participate in the same decision.
        const reviewer = grant(actor,'permit',{pred:'reviewer'});
        const alternatives = [ownerPermit,grant(actor,'forbid',{pred:'owner'}),reviewer,parentList];
        compare('GetWidget',{name},alternatives,{rows:[]},actor,name,'NOT_FOUND',{authority});
        for (const owns of [false,true]) for (const reviews of [false,true]) {
          const stored = {...row(name,owns),predicates:[['owner',owns],['reviewer',reviews]]};
          compare('GetWidget',{name},alternatives,{rows:[stored]},actor,name,
            !owns && reviews ? 'OK' : 'PERMISSION_DENIED',{authority});
        }
        for (const effect of ['permit', 'forbid']) {
          const risky = grant(actor, effect, { mayError: true, pred: 'owner' });
          const rules = effect === 'permit' ? [risky] : [grant(actor), risky];
          for (const knownFacts of [false, true]) {
            // Stored attributes alone do not establish a successful rule evaluation.
            for (const rows of [[], [row(name, effect === 'permit')]]) {
              const opts = {authority};
              if (knownFacts) opts.attrsOf = () => rows.length ? {owner:effect === 'permit' ? 'alice' : 'other'} : {};
              const auth = m.authorizeRequest(rules,I,'GetWidget',{name},opts);
              const status = m.readStatus({exists:!!rows.length, target:auth.decision === 'PROCEED' ? 'ALLOW' : 'DENY',
                parentList:m.authorize(rules,'widgets.list',parent)});
              assert.equal(status,'PERMISSION_DENIED');
              compare('GetWidget', {name}, rules, {rows}, actor, name, status, {authority, knownFacts});
            }
          }
          const suppliedName = [...prefix, 'short'];
          const indexedRow = { ...row(name, effect === 'permit'), secondaryNames: [suppliedName] };
          const asWritten = [[...prefix, '*']];
          const faultOutcomesByPath = [{ path: name, rule: risky, fault: false }];
          // The joined row supplies both the condition and its evaluation outcome.
          // Neither is available under the secondary spelling before this join.
          compare('GetWidget', { name: suppliedName }, rules, { rows: [indexedRow] }, actor, suppliedName, 'OK',
            { authority, knownFacts: true, asWritten, faultOutcomesByPath });
          compare('GetWidget', { name: suppliedName }, rules, { rows: [] }, actor, suppliedName, 'PERMISSION_DENIED',
            { authority, knownFacts: true, asWritten, faultOutcomesByPath });
        }
        for (const fault of [false,true]) {
          const uncertain = grant(actor,'permit',{mayError:true});
          // The row is absent, but the adapter observed the permit's fault
          // result without the row. No List permission participates.
          const known = m.authorize([uncertain],actor,name,{}, {authority,faults:()=>fault});
          const missing = m.readStatus({exists:false,target:known,parentList:'DENY'});
          compare('GetWidget',{name},[uncertain],{rows:[]},actor,name,missing,
            {authority,knownFacts:true,faults:fault?[uncertain]:[]});
        }
        const forbid = grant(actor,'forbid',{mayError:true}), permit = grant(actor);
        const known = m.authorize([permit,forbid],actor,name,{}, {authority,faults:r=>r===forbid});
        compare('GetWidget',{name},[permit,forbid],{rows:[]},actor,name,
          m.readStatus({exists:false,target:known,parentList:'DENY'}),
          {authority,knownFacts:true,faults:[forbid]});
      }
    }
    compare('GetWidget', {name}, rules, {rows:[row(other, true)]}, actor, name, raw(rules,name,false,false));
    totals.matches++; totals.misses++;
    // Unknown mapping, hidden matching mapper and a row belonging to another
    // collection all pass through the complete handler. No get/list is derivable.
    const hidden = [grant(actor, 'permit', {pred:'owner'})];
    const store = { possibleNames: [[alias, [[...prefix, '*']]]], rows: [row(name, false)] };
    if (i === 0) {
      const policy=[grant(actor,'forbid',{path:parent}),grant('widgets.list')];
      for (const [observations,answer,visible] of [[undefined,undefined,true],[null,null,false],
        [[[parent,false]],()=>false,false], [[[parent,false]],()=>{throw Error('name unavailable');},false],
        [[[parent,true]],()=>true,true]]) {
        const final=m.finalRegionDenial(policy,actor,parent,{canName:answer});
        assert.equal(final,visible);
        const expected=m.zeroMatchStatus({regionDenyFinal:final,nonprojectingKey:true,nonprojectingGet:true,
          regionList:m.authorize(policy,'widgets.list',parent)});
        assert.equal(expected,visible ? 'PERMISSION_DENIED' : 'NOT_FOUND');
        compare('GetWidget',{name:alias},policy,store,actor,alias,expected,
          {indirect:[alias],nonprojectingKeys:[actor],nameVisibility:observations});
      }
    }
    const mapping = { indirect:[alias], mappings:[{supplied:alias,canonical:name}] };
    const region = m.projectCell(hidden, actor, parent);
    const zero = m.zeroMatchStatus({region, regionGet:region,
      regionList:m.projectCell(hidden,'widgets.list',parent)});
    const x = compare('GetWidget', {name:alias}, hidden, store, actor, alias, zero, {indirect:[alias]});
    const y = compare('GetWidget', {name:alias}, hidden, store, actor, alias, raw(hidden,name,false,true), mapping);
    if (JSON.stringify(x) !== JSON.stringify(y)) throw Error('Hidden/absent alias observations differ');
    totals.privateTwins++;
    const masked = [actor], privacyRules = [grant(actor)];
    if (list) privacyRules.push(grant('widgets.list'));
    if (!allowed) privacyRules.push(grant(actor,'forbid'));
    const privateZero = m.zeroMatchStatus({ region:m.projectCell(privacyRules,actor,parent),
      nonprojectingKey:true, nonprojectingGet:true, regionGet:m.projectCell(privacyRules,actor,parent),
      regionList:m.projectCell(privacyRules,'widgets.list',parent),
      regionDenyFinal:m.finalRegionDenial(privacyRules,actor,parent) });
    compare('GetWidget',{name:alias},privacyRules,store,actor,alias,privateZero,{indirect:[alias],nonprojectingKeys:masked});
    const deniedByCeiling = m.zeroMatchStatus({region:'ALLOW',regionGet:'ALLOW',regionList:'ALLOW',
      regionDenyFinal:m.finalRegionDenial([],actor,parent,{ceilingDenied:true})});
    compare('GetWidget',{name:alias},[grant(actor)],store,actor,alias,deniedByCeiling,
      {indirect:[alias],ceiling:[]});
    // A matching ancestor wildcard must resolve exactly one full name.
    const n = rng.int(3), rows = [row(name, allowed), row(other, true)].slice(0,n);
    const wildStatus = m.wildcardGetStatus({ matches:n, target:m.authorize(rules,actor,name,{owner:allowed?'alice':'no'}),
      region:'UNKNOWN', regionGet:'UNKNOWN', regionList:list?'ALLOW':'DENY' });
    compare('GetWidget', {name:wildcard}, rules, {rows}, actor, wildcard, wildStatus);
    // One public update permission is reported for all upsert failures, including a guard.
    const update='widgets.update', create='widgets.create', guard='widgets.setOwner';
    const rs = [grant(update), grant(create)];
    if (allowed) rs.push(grant(guard));
    const upsert = {'widget.name':alias, allow_missing:true, update_mask:['owner'], populated:['owner']};
    const canon = { ...upsert, 'widget.name':name };
    const bound = m.requirementsFor(I,'UpdateWidget',canon);
    if (!bound.some(r => r.key===guard)) throw Error('Expected an active owner guard');
    const authorized = m.authorizeRequest(rs,I,'UpdateWidget',canon,{attrsOf:()=>({})}).decision==='PROCEED';
    const atMatch = m.indirectUpsertStatus(update, alias.join('/'), true, authorized?'ALLOW':'DENY', 'ALLOW');
    compare('UpdateWidget',upsert,rs,store,update,alias,atMatch.status,mapping);
    const atMiss = m.indirectUpsertStatus(update, alias.join('/'), false, 'NOT_FOUND',
      m.authorize(rs,create,parent), ...bound.filter(r=>r.key===guard).flatMap(r=>r.targets.map(t=>m.authorize(rs,guard,t))));
    compare('UpdateWidget',upsert,rs,store,update,alias,atMiss.status,{indirect:[alias]});
    if (i === 0) {
      const req = { 'widget.name':name, update_mask:['owner'], populated:['owner'] };
      const scoped = [grant(update,'permit',{pred:'owner'})];
      const active = m.requirementsFor(I,'UpdateWidget',req);
      const staticDenial = active.find(r => r.targets.some(t => m.projectCell(scoped,r.key,t) === 'DENY'));
      if (staticDenial?.key !== guard) throw Error('Expected a guard denied independently of row ownership');
      const refused = m.authorizeRequest(scoped,I,'UpdateWidget',req,{handlerResolvesResiduals:true});
      if (refused.decision !== 'DENY') throw Error('Expected policy refusal before row lookup');
      for (const rows of [[],[row(name,true)],[row(name,false)]])
        compare('UpdateWidget',req,scoped,{rows},staticDenial.key,name,refused.decision === 'DENY' ? 'PERMISSION_DENIED' : 'OK');
      totals.privateTwins += 2;

      const conflict = [...scoped,grant(guard,'permit',{pred:'owner'}),grant(guard,'forbid',{pred:'owner'}),
        grant('widgets.list')];
      const blocked = active.find(r => r.targets.some(t => [true,false].every(owns =>
        m.authorize(conflict,r.key,t,{owner:owns ? 'alice' : 'other'}) === 'DENY')));
      assert.equal(blocked.key,guard);
      for (const authority of ['failClosed','skipErrors']) {
        let reads = 0;
        const diagnosis = m.authorizeRequest(conflict,I,'UpdateWidget',req,{authority,attrsOf:() => {
          reads++; return {owner:'alice'};
        }});
        assert.equal(diagnosis.reason,'POLICY');
        assert.equal(reads,0);
        for (const rows of [[],[row(name,false)],[row(name,true)]])
          compare('UpdateWidget',req,conflict,{rows},blocked.key,name,
            diagnosis.decision === 'DENY' ? 'PERMISSION_DENIED' : 'OK',{authority,knownFacts:true});
      }

      const dependent = [...scoped,grant(guard),grant(guard,'forbid',{pred:'owner'})];
      const firstOpaque = active.find(r => r.targets.some(t => m.readStatus({exists:false,
        target:m.projectCell(dependent,r.key,t),parentList:m.authorize(dependent,'widgets.list',parent)
      }) === 'PERMISSION_DENIED'));
      const missing = m.readStatus({exists:false, target:m.projectCell(dependent,firstOpaque.key,name),
        parentList:m.authorize(dependent,'widgets.list',parent)});
      const privateMiss = compare('UpdateWidget',req,dependent,{rows:[]},firstOpaque.key,name,missing);
      for (const owner of [true,false]) {
        const result = m.authorizeRequest(dependent,I,'UpdateWidget',req,{attrsOf:()=>({owner:owner?'alice':'other'})});
        if (result.decision !== 'DENY') throw Error('Expected at least one unsatisfied row predicate');
        const match = compare('UpdateWidget',req,dependent,{rows:[row(name,owner)]},firstOpaque.key,name,
          result.decision === 'DENY' ? 'PERMISSION_DENIED' : 'OK');
        if (JSON.stringify(match) !== JSON.stringify(privateMiss)) throw Error('Canonical opaque responses differ');
        totals.privateTwins++;
      }
      // Listing discloses absence. For an indexed secondary spelling, use
      // the stored row's attributes to identify the permission actually refused.
      const listable = [...dependent,grant('widgets.list')], supplied = [...prefix,'short'];
      const secondary = {...req,'widget.name':supplied};
      const indexed = {...row(name,true),secondaryNames:[supplied]};
      const attrs = {owner:'alice'};
      const failure = m.requirementsFor(I,'UpdateWidget',secondary).find(r =>
        r.targets.some(t => m.authorize(listable,r.key,t,attrs) === 'DENY'));
      if (failure?.key !== guard) throw Error('Expected the owner guard to refuse the indexed row');
      compare('UpdateWidget',secondary,listable,{rows:[indexed]},failure.key,supplied,
        m.readStatus({exists:true,target:m.authorize(listable,failure.key,supplied,attrs)}),
        {asWritten:[[...prefix,'*']]});
    }
    const delRules = allowed ? [grant('widgets.delete')] : [];
    const deletion = m.deleteMissingStatus({target:m.projectCell(delRules,'widgets.delete',name),parentList:'DENY'});
    compare('DeleteWidget',{name,allow_missing:true},delRules,{rows:[]},'widgets.delete',name,deletion);
    const taken = rng.int(2)===1;
    const cr = [grant(create)];
    if (list) cr.push(grant('widgets.list'));
    if (allowed) cr.push(grant(actor));
    const createRequest = {parent, populated:[]};
    const mayCreate = m.authorizeRequest(cr, I, 'CreateWidget', createRequest, {attrsOf:()=>({})}).decision === 'PROCEED';
    const collision = m.createStatus({authorized:mayCreate,nameTaken:taken,
      getExisting:m.authorize(cr,actor,name),listParent:m.authorize(cr,'widgets.list',parent)});
    compare('CreateWidget',createRequest,cr,{rows:taken?[row(name,false)]:[],createDestination:name},create,parent,collision);
    totals.collisions++;
  }
  return totals;
}
module.exports = { runLookupCases };
