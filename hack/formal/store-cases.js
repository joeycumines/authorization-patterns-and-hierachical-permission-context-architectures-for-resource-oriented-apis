'use strict';

const codec = require('./codec');
const assert = require('node:assert/strict');

function resource(r) {
  return { resourceType: r.type, plural: r.plural, patterns: codec.domain(r.patterns),
    protoMessage: r.protoMessage ?? null };
}
function binding(b) {
  const tag = b.scopeKind || (b.path.length ? 'resource' : 'serviceRoot');
  const scope = tag === 'serviceRoot' ? tag : { [tag]: { path: b.path } };
  const recipient = b.group === undefined ? { subject: { id: b.subject } } : { group: { id: b.group } };
  return { scope, recipient, keys: b.keys, roles: b.roles, effect: b.effect, pred: b.pred ?? null,
    hidden: !!b.hidden, mayError: !!b.mayError, final: b.final !== false };
}
function sight(v) {
  if (v.kind === 'get') return { get: { subject: v.subject, resource: v.path } };
  if (v.kind === 'declared') return { declared: { subject: v.subject, scope: v.path } };
  return { list: { subject: v.subject, resourceType: v.type, parent: v.parent } };
}
function boundary(b) {
  return { key: b.key, level: codec.domain([b.pattern])[0] };
}
const editFields = {
  bindings: ['rules', 'bindings', binding], roles: ['roleDefinitions', 'roles', x => x],
  memberships: ['groupMemberships', 'members', x => x], visibility: ['visibility', 'facts', sight],
  boundaries: ['privacyBoundaries', 'levels', boundary], asWrittenTypes: ['nameModes', 'types', x => x]
};
function served(M, resources, methods) {
  const source = { apiService: resources[0].type.split('/')[0], methods: methods.filter(m => m.name),
    imported: methods.filter(m => m.method), importedServices: [['foreign.Teams', ['GetTeam']]],
    resources: Object.fromEntries(resources.map(r => [r.protoMessage ?? r.type.split('/')[1], r])) };
  const descriptor = M.interpret(source);
  assert.deepEqual(Array.from(descriptor.errors), []);
  return { descriptor, wireDescriptor: codec.descriptor(source, descriptor) };
}
function standardGet(type) {
  return { name: 'Get' + type, authz: { standard: {} }, request: { name: { type } } };
}
const getTeam = standardGet('Team');
const listTeams = { name: 'ListTeams', authz: { standard: {} }, request: { parent: { childType: 'Team' } } };

function store(s) {
  const result = { resources: s.resources.map(resource), descriptor: s.wireDescriptor ?? null };
  for (const [field, [, , convert]] of Object.entries(editFields)) result[field] = (field === 'asWrittenTypes' && s[field] === undefined ? [] : s[field]).map(convert);
  return result;
}
function edit({ field, value }) {
  const [tag, payload, convert] = editFields[field];
  return { [tag]: { [payload]: value.map(convert) } };
}

function observation(M, current, accepted, subjects) {
  return { accepted, store: store(current),
    rules: subjects.map(who => M.policyStoreRules(current, who).map(codec.rule)) };
}

function projectStore(M, state, subject, key, patterns, anchor, budget) {
  const nonprojecting = (permission, path) => state.boundaries.some(b => b.key === permission &&
    M.reach(b.pattern, path) && path.length < b.pattern.length);
  const canName = path => M.storeCanName(state, subject, path);
  const ctx = M.projectContext(M.policyStoreRules(state, subject), { [key]: { key, patterns } },
    anchor, { canName, nonprojecting, budget });
  assert.equal(ctx.error, undefined);
  return { claims: ctx.claims.map(codec.claim), descendantsOmitted: ctx.descendantsOmitted };
}

function visibilityCases(M, compare) {
  const company = ['companies', 'A'], team = [...company, 'teams', 'B'];
  const level = ['companies', '*', 'teams', '*'], widgets = [...level, 'widgets', '*'];
  const subject = 'alice', group = 'reviewers', get = 'teams.get', key = 'widgets.get';
  const resources = [{ type: 'demo.example/Team', plural: 'teams', patterns: [level] },
    { type: 'demo.example/Widget', plural: 'widgets', patterns: [widgets] }];
  const baseline = { resources, ...served(M, resources, [getTeam, listTeams, standardGet('Widget')]), roles: [], memberships: [{ group, subject }], visibility: [],
    bindings: [{ subject, path: company, keys: [key], roles: [], effect: 'permit' }],
    boundaries: [{ key: get, pattern: level }] };
  const grant = { group, path: company, keys: [get], roles: [], effect: 'permit' };
  const scopedRule = { group, path: team, keys: [key], roles: [], effect: 'forbid' };
  const bind = value => ({ field: 'bindings', value });
  const cases = [
    ['unconditional get', [grant], true],
    ['unconditional list', [{ ...grant, keys: ['teams.list'] }], true],
    ['group grant on the resource', [{ ...grant, path: team }], false],
    ['hidden permit', [{ ...grant, hidden: true }], false],
    ['conditional permit', [{ ...grant, pred: 'owner' }], false],
    ['possibly erroring permit', [{ ...grant, mayError: true }], false],
    ['unconditional forbid', [grant, { ...grant, effect: 'forbid' }], false],
    ['conditional forbid', [grant, { ...grant, effect: 'forbid', pred: 'owner' }], false],
    ['hidden forbid', [grant, { ...grant, effect: 'forbid', hidden: true }], false],
    ['possibly erroring list forbid', [{ ...grant, keys: ['teams.list'] },
      { ...grant, keys: ['teams.list'], effect: 'forbid', mayError: true }], false]
  ];
  for (const [label, evidence, permitsNaming] of cases) {
    const bindings = [...baseline.bindings, ...evidence];
    const first = [bind(bindings)], second = [bind([...bindings, scopedRule])];
    const installed = M.acceptPolicyTransaction(baseline, first);
    assert.equal(installed.accepted, true, label + ': evidence is independently admissible');
    const checked = M.acceptPolicyTransaction(installed.store, second);
    assert.equal(checked.accepted, permitsNaming, label);
    if (!checked.accepted) assert.equal(checked.store, installed.store, label);
    compare({ op: 'store', store: store(baseline), subjects: [subject], transactions: [first.map(edit), second.map(edit)] },
      [installed, checked].map(s => observation(M, s.store, s.accepted, [subject])));
  }

  const decl = [{ field: 'boundaries', value: [...baseline.boundaries, { key, pattern: level }] }];
  const declared = M.acceptPolicyTransaction(baseline, decl);
  assert.ok(declared.accepted);
  let privateRejections = 0;
  for (const effect of ['permit', 'forbid']) for (const hidden of [false, true]) {
    for (const conditional of [{ mayError: true }, { pred: '' }]) {
      const attempted = [bind([...baseline.bindings, { ...scopedRule, effect, hidden, ...conditional }])];
      const refused = M.acceptPolicyTransaction(declared.store, attempted);
      assert.equal(refused.accepted, false);
      assert.equal(refused.store, declared.store);
      compare({ op: 'store', store: store(baseline), subjects: [subject], transactions: [decl.map(edit), attempted.map(edit)] },
        [declared, refused].map(s => observation(M, s.store, s.accepted, [subject])));
      privateRejections++;
    }
  }
  const privateRule = [bind([...baseline.bindings, { ...scopedRule, hidden: true }])];
  const transactions = [[], decl, privateRule];
  let current = baseline;
  const budget = 0;
  const results = transactions.map(writes => {
    const { store: s, accepted } = M.acceptPolicyTransaction(current, writes);
    current = s;
    assert.equal(accepted, true);
    return { ...observation(M, s, accepted, [subject]),
      projection: projectStore(M, s, subject, key, [widgets], company, budget) };
  });
  assert.equal(results[0].projection.claims[0]?.kind, 'allow');
  assert.deepEqual(results[1].projection, results[2].projection);
  assert.equal(results[1].projection.descendantsOmitted, false);
  assert.equal(results[1].projection.claims.length, 0);
  compare({ op: 'store', store: store(baseline), subjects: [subject], transactions: transactions.map(ws => ws.map(edit)),
    projection: { subject, key, anchor: company, domain: codec.domain([widgets]), budget } }, results);
  const publicEdit = bind([...baseline.bindings, grant, scopedRule]);
  const visible = M.acceptPolicyTransaction(baseline, [publicEdit]);
  assert.ok(visible.accepted);
  assert.ok(M.storeCanName(visible.store, subject, team));
  assert.ok(M.storeCanName(visible.store, subject, { collection: { path: [...team, 'widgets'] } }));
  const projected = projectStore(M, visible.store, subject, key, [widgets], company, 1);
  assert.ok(projected.claims.some(c => c.holes.some(h => M.sameName(h, team))));
  compare({ op: 'store', store: store(baseline), subjects: [subject], transactions: [[edit(publicEdit)]],
    projection: { subject, key, anchor: company, domain: codec.domain([widgets]), budget: 1 } },
    [{ ...observation(M, visible.store, visible.accepted, [subject]), projection: projected }]);
  return cases.length + privateRejections + 2;
}

function servedReadCases(M, compare) {
  const company = ['companies', 'A'], team = [...company, 'teams', 'B'];
  const type = 'demo.example/Team', level = ['companies', '*', 'teams', '*'];
  const resources = [{ type, plural: 'teams', patterns: [level] }];
  const subject = 'alice', group = 'reviewers', key = 'teams.annotate';
  const membership = { group, subject };
  const observe = { operation: 'observe', accessClass: 'READ', serviceRoot: true };
  const compoundGet = { ...getTeam, name: 'demo.Teams/GetTeam', authz: { requirements: [
    { operation: 'inspect', accessClass: 'READ', targetField: 'name' }, observe] } };
  const compoundList = { ...listTeams, name: 'demo.Teams/ListTeams', authz: { requirements: [
    { operation: 'enumerate', accessClass: 'READ', targetField: 'parent' }, observe] } };
  const getSight = { kind: 'get', subject, path: team };
  const listSight = { kind: 'list', subject, type, parent: company };
  const permit = keys => ({ subject, roles: [], effect: 'permit', path: [], keys });
  const guard = { group, path: team, keys: [key], roles: [], effect: 'forbid' };
  const both = permit(['teams.inspect', 'service.observe']);
  let count = 0;
  const trial = (label, catalog, methods, grants, visibility, expected, scoped = guard, legacy = resources, boundaries = []) => {
    const teamType = catalog.find(r => r.type.endsWith('/Team'));
    const annotate = { name: 'AnnotateTeam', request: { name: { type: teamType.protoMessage ?? teamType.type } },
      authz: { requirements: [{ operation: 'annotate', accessClass: 'UPDATE', targetField: 'name' }] } };
    const schema = methods ? served(M, catalog, [...methods, annotate]) : {};
    const initial = { ...schema, resources: legacy, roles: [], memberships: [membership], bindings: grants,
      boundaries, visibility };
    assert.equal(M.acceptPolicyTransaction(initial,[]).accepted,true,label+' initial store');
    const writes = [{ field: 'bindings', value: [...grants, scoped] }];
    const result = M.acceptPolicyTransaction(initial, writes);
    assert.equal(result.accepted, expected, label);
    if (!expected) assert.equal(result.store, initial, label);
    compare({ op: 'store', store: store(initial), subjects: [subject], transactions: [writes.map(edit)] },
      [observation(M, result.store, result.accepted, [subject])]);
    count++;
  };
  const inventory = { operation: 'readInventory', accessClass: 'READ', serviceRoot: true };
  const admin = {operation:'inspectInventory',accessClass:'ADMIN',serviceRoot:true};
  const keyAdmin = 'service.inspectInventory';
  for (const rpc of [getTeam,listTeams]) for (const noSideEffects of [false,true]) {
    const parentRead = rpc === listTeams, field = parentRead ? 'parent' : 'name';
    const method = {...rpc,noSideEffects,authz:{requirements:[admin]}};
    const target = {operation:'view',accessClass:'READ',targetField:field};
    const withExtra = {...method,authz:{requirements:[target,admin]}};
    const required = [permit([keyAdmin]),permit(['teams.view'])];
    trial(rpc.name+' ADMIN-only',resources,[method],[required[0]],[],true);
    trial(rpc.name+' complete read',resources,[withExtra],required,[],true);
    trial(rpc.name+' missing read permission',resources,[withExtra],[required[0]],[],false);
    trial(rpc.name+' missing root permission',resources,[withExtra],[required[1]],[],false);
    trial(rpc.name+' conditional ADMIN grant',resources,[method],[{...required[0],pred:'owner'}],[],false);
    trial(rpc.name+' error-prone ADMIN grant',resources,[method],[{...required[0],mayError:true}],[],false);
    trial(rpc.name+' forbidden ADMIN grant',resources,[method],[required[0],{...required[0],effect:'forbid'}],[],false);
    trial(rpc.name+' hidden ADMIN grant',resources,[method],[{group,path:[],keys:[keyAdmin],effect:'permit',roles:[],hidden:true}],[],false,guard,resources,
      [{key:keyAdmin,pattern:[]}]);
    if (!parentRead) trial('own group permit at the addressed Team', resources,[withExtra],
      [required[0],{group,path:team,keys:['teams.view'],roles:[],effect:'permit'}],[],false,guard,resources,
      [{key:'teams.view',pattern:level}]);
  }
  const message = 'shared.v1.Team', qualified = [{...resources[0],protoMessage:message}];
  trial('qualified catalog message survives the store trace',qualified,[{...getTeam, name:'demo.v1.Teams/GetTeam',
    returns:message, request:{name:{type:message}}}], [permit(['teams.get'])],[],true,guard,qualified);
  for (const [rpc, sight] of [[getTeam, getSight], [listTeams, listSight]]) {
    const method = { ...rpc, request: { ...rpc.request, details: true },
      authz: { requirements: [inventory, { ...observe, condition: 'details' }] } };
    trial(rpc.name + ' root-only permission', resources, [method], [permit(['service.readInventory'])], [], true);
    trial(rpc.name + ' missing root permission', resources, [method], [], [], false);
    trial(rpc.name + ' resource observation cannot authorize service.readInventory', resources, [method], [], [sight], false);
    const wrong = { ...method, request: { details: true } };
    trial(rpc.name + ' without an addressed resource', resources, [wrong], [permit(['service.readInventory'])], [sight], false);
    trial(rpc.name + ' returns no resource data', resources, [{ ...method, returns: 'Empty' }],
      [permit(['service.readInventory'])], [sight], false);
    const primary = { accessClass: 'READ', operation: 'inspect', targetField: rpc === getTeam ? 'name' : 'parent' };
    const two = { ...rpc, authz: { requirements: [primary, { ...primary, operation: 'viewDetails' }] } };
    trial(rpc.name + ' a sight cannot supply two independent permissions', resources, [two], [], [sight], false);
    trial(rpc.name + ' a sight with the other permission', resources, [two], [permit(['teams.viewDetails'])], [sight], true);
  }
  const host = { type: 'demo.example/Facility', plural: 'facilities', patterns: [['facilities', '*']] };
  const imported = { ...resources[0], type: 'foreign.example/Team', external: true };
  const unused = { type: 'other.example/Unit', plural: 'teams', patterns: [['units', '*']], external: true };
  const importedGet = { ...getTeam, authz: { requirements: [inventory] } };
  trial('served Get of an imported resource, with an unrelated import sharing its plural', [host, imported, unused],
    [importedGet], [permit(['service.readInventory'])], [], true);
  trial('foreign addressed resource without its root permission', [host, imported, unused], [importedGet], [], [], false);
  trial('imported RPC retains its request signature', [host, imported, unused],
    [{ method: 'foreign.Teams/GetTeam', request: getTeam.request, authz: { requirements: [inventory] } }],
    [permit(['service.readInventory'])], [], true);
  trial('compound Get lacks service.observe', resources, [compoundGet], [permit(['teams.inspect'])], [], false);
  trial('compound Get with complete authorization', resources, [compoundGet], [both], [], true);
  trial('explicit Get evidence alone', resources, [compoundGet], [], [getSight], false);
  trial('explicit Get plus auxiliary grant', resources, [compoundGet], [permit(['service.observe'])], [getSight], true);
  trial('possible auxiliary forbid', resources, [compoundGet], [both, { ...permit(['service.observe']), effect: 'forbid', mayError: true }], [], false);
  trial('unresolvable extra field', resources, [{ ...compoundGet, request: { ...compoundGet.request, related: { type: 'Team' } },
    authz: { requirements: [...compoundGet.authz.requirements,
      { operation: 'inspect', accessClass: 'READ', targetField: 'related' }] } }], [both], [], false);
  trial('inactive extra requirement', resources, [{ ...compoundGet, request: { ...compoundGet.request, details: true },
    authz: { requirements: [compoundGet.authz.requirements[0], { ...observe, condition: 'details' }] } }], [permit(['teams.inspect'])], [], true);
  trial('absent served method', resources, [], [], [getSight, listSight], false);
  trial('resource-only legacy store', resources, null, [], [getSight, listSight], false);
  trial('similarly bound unrelated RPC', resources, [{ ...compoundGet, name: 'InspectTeam' }], [both], [getSight], false);
  trial('compound List lacks service.observe', resources, [compoundList], [permit(['teams.enumerate'])], [], false);
  trial('compound List with complete authorization', resources, [compoundList], [permit(['teams.enumerate', 'service.observe'])], [], true);
  trial('explicit List plus auxiliary grant', resources, [compoundList], [permit(['service.observe'])], [listSight], true);
  trial('descriptor excludes legacy resource shape', [{ ...resources[0], patterns: [['other', '*']] }], [compoundGet],
    [both], [getSight], false);
  const rootTeams = [{ ...resources[0], patterns: [['teams', '*']] }];
  const rootList = { ...listTeams, name: 'demo.Teams/ListTeams', request: {}, resourceType: 'Team' };
  const rootRule = { ...guard, path: ['teams', 'B'] };
  trial('root-bound ListTeams', rootTeams, [rootList], [permit(['teams.list'])], [], true, rootRule);
  const inventoryRootList = { ...rootList, authz: { requirements: [inventory] } };
  trial('root-bound List with a service-only declaration', rootTeams, [inventoryRootList], [permit(['service.readInventory'])], [], true, rootRule);
  trial('root-bound List sight cannot supply a service permission even at the same root', rootTeams,
    [inventoryRootList], [], [{ kind: 'list', subject, type, parent: [] }], false, rootRule);
  trial('typed observation of root-bound ListTeams', rootTeams, [rootList], [],
    [{ kind: 'list', subject, type, parent: [] }], true, rootRule);
  return count;
}

function projectionSiteCases(M, compare) {
  const key = 'items.get', subject = 'alice';
  const resources = [
    { type: 'demo.example/Item', plural: 'items', patterns: [['items', '*']] },
    { type: 'demo.example/Flag', plural: 'flags', patterns: [['flags', '*']] }
  ];
  const bindings = [{ subject, path: [], keys: [key], roles: [], effect: 'permit' },
    { subject, path: ['flags', 'f'], keys: ['flags.get'], roles: [], effect: 'permit' }];
  const initial = { resources, ...served(M, resources, ['Item','Flag'].map(standardGet)), bindings, roles: [], visibility: [], memberships: [], boundaries: [] };
  const result = M.acceptPolicyTransaction(initial, []);
  assert.equal(result.accepted, true);
  const rules = M.policyStoreRules(result.store, subject);
  const domain = resources[0].patterns, resourcePatterns = resources.flatMap(r => r.patterns);
  const keys = Object.fromEntries(resources.map(r => {
    const k = r.plural + '.get';
    return [k, { key: k, patterns: r.patterns }];
  }));
  let count = 0;
  for (const profile of ['SCOPED_CLAIMS', 'GRANT_SHAPED']) {
    for (const [anchor, valid] of [[['items'], false], [['items', 'i'], true]]) {
      const projection = { subject, key, anchor, domain: codec.domain(domain), budget: 0, profile: codec.enumName(profile) };
      const faults = [];
      const claims = M.projectAnchor(rules, key, anchor, domain, { profile, resourcePatterns, budget: 0,
        onFault: message => faults.push(message) });
      const ctx = M.projectContext(rules, keys, anchor, { profile, budget: 0 });
      assert.deepEqual(ctx.claims, claims);
      assert.equal(ctx.error, valid ? undefined : 'SERVER_FAULT');
      assert.equal(faults.length, valid ? 0 : 1);
      assert.deepEqual(Array.from(claims, c => c.kind), valid ? ['ALLOW'] : []);
      compare({ op: 'store', store: store(initial), subjects: [subject], transactions: [[]], projection },
        [{ ...observation(M, result.store, result.accepted, [subject]),
          projection: { claims: claims.map(codec.claim), descendantsOmitted: ctx.descendantsOmitted ?? false } }]);
      count++;
    }
  }
  return count;
}

function asWrittenCases(M, compare) {
  const user = 'demo.example/User', key = 'users.get', company = ['companies','A'];
  const userLevel = ['companies','*','users','*'], alternate = ['directory','*'];
  const resources = [{type:user,plural:'users',patterns:[userLevel,alternate]},
    {type:'demo.example/Device',plural:'devices',patterns:[[...userLevel,'devices','*'],[...alternate,'devices','*']]},
    {type:'demo.example/Team',plural:'teams',patterns:[['companies','*','teams','*']]}];
  const base = {resources,...served(M,resources,[standardGet('User'),getTeam]),roles:[],bindings:[],memberships:[],visibility:[],boundaries:[]};
  const parent = {subject:'alice',path:company,keys:[key],roles:[],effect:'permit'};
  const sibling = {...parent,path:[...company,'teams','T'],keys:['teams.get']};
  const userGrant = {...parent,path:[...company,'users','u123']};
  const bind = value => ({field:'bindings',value});
  const modes = value => ({field:'asWrittenTypes',value});
  const txs = [
    [[bind([userGrant])],true],
    [[modes([user]),{field:'roles',value:[{name:'changed',keys:[key]}]}],false],
    [[modes([user]),bind([parent,sibling])],true],
    [[modes(['demo.example/Missing'])],false],
    [[modes([user,'demo.example/Missing'])],false],
    [[modes(['User'])],false]
  ];
  for (const path of [userGrant.path,[...company,'users','name@acme.example'],[...userGrant.path,'devices','d'],
    ['directory','u123'],['directory','name@acme.example','devices','d']]) {
    for (const [recipient,effect,extra] of [[{subject:'alice'},'permit',{}],[{subject:'alice'},'forbid',{pred:'owner'}],
      [{group:'empty'},'permit',{hidden:true}],[{group:'empty'},'forbid',{hidden:true,keys:[]}]]) {
      txs.push([[bind([parent,sibling,{path,keys:[key],roles:[],...recipient,effect,...extra}])],false]);
    }
  }
  txs.push([[modes([]),bind([userGrant])],true], [[modes([user])],false], [[bind([sibling]),modes([user])],true]);
  let current = base;
  const expected = txs.map(([writes,want]) => {
    const next = M.acceptPolicyTransaction(current,writes);
    assert.equal(next.accepted,want,JSON.stringify(writes));
    if (!want) assert.strictEqual(next.store,current);
    current = next.store;
    return observation(M,current,next.accepted,['alice']);
  });
  const wire = store(base);
  delete wire.asWrittenTypes; // historical stores have no declaration
  compare({op:'store',store:wire,subjects:['alice'],transactions:txs.map(([ws]) => ws.map(edit))},expected);
  return 1;
}

function storeCases(M, compare, random, count) {
  const pinned = asWrittenCases(M,compare) + visibilityCases(M, compare) + servedReadCases(M, compare) + projectionSiteCases(M, compare);
  for (let i = 0; i < count; i++) {
    const company = ['companies', 'c' + random(100000)];
    const team = [...company, 'teams', 't' + random(100000)];
    const widget = [...team, 'widgets', 'w' + random(100000)];
    const teamPattern = ['companies', '*', 'teams', '*'];
    const widgetPattern = [...teamPattern, 'widgets', '*'];
    const subjects = ['u' + random(100000), 'v' + random(100000)];
    const group = 'g' + random(100000);
    const type = 'team' + i + '.example/Team';
    const initial = { resources: [
      { type, plural: 'teams', patterns: [teamPattern] },
      { type: 'widget.example/Widget', plural: 'widgets',
        patterns: [widgetPattern, ['companies', '*', 'widgets', '*']] }
    ], roles: [], bindings: [], memberships: [], visibility: [], boundaries: [] };
    const approve = { name: 'ApproveWidget', request: { name: { type: 'Widget' } },
      authz: { requirements: [{ operation: 'approve', accessClass: 'UPDATE', targetField: 'name' }] } };
    Object.assign(initial, served(M, initial.resources, [getTeam, listTeams, standardGet('Widget'), approve]));
    const A = 'widgets.get', B = 'widgets.approve';
    const members = subjects.map(subject => ({ group, subject }));
    const bothList = subjects.map(subject => ({
      path: company, subject, effect: 'permit', keys: ['teams.list'], roles: []
    }));
    const groupForbid = { path: team, group, keys: [], roles: ['operator'], effect: 'forbid' };
    const levels = [A, B].map(key => ({ key, pattern: teamPattern }));
    const write = (field, value) => ({ field, value });
    const role = keys => write('roles', [{ name: 'operator', keys }]);
    const assign = roster => write('memberships', roster);
    const bind = bs => write('bindings', bs);
    const declare = ls => write('boundaries', ls);
    const visible = facts => write('visibility', facts);
    const txs = [
      [role([A]), assign(members), bind([groupForbid, ...bothList])],
      [bind([groupForbid, bothList[0]])],
      [declare([levels[0]]), bind([groupForbid])],
      [role([A, B])],
      [assign([]), role([A, B])],
      [assign(members)],
      [assign(members), declare(levels)],
      [bind([{ ...groupForbid, pred: 'classified' }])],
      [visible(subjects.map(subject => ({ kind: 'list', type, subject, parent: company }))),
        bind([{ ...groupForbid, pred: 'classified' }])],
      [visible([])],
      [visible(subjects.map(subject => ({ kind: 'get', subject, path: team })))],
      [bind([{ ...groupForbid, path: [...team, 'widgets'], scopeKind: 'collection' }])],
      [bind([{ ...groupForbid, path: widget, hidden: true }])]
    ];
    const blockGet = { path: [], group, keys: ['teams.get'], roles: [], effect: 'forbid', pred: 'owner' };
    const seen = subjects.map(subject => ({ kind: 'get', subject, path: team }));
    txs.push([assign(members), declare([]), role([A]), bind([groupForbid, blockGet]), visible(seen)],
      [bind([groupForbid]), visible(seen)],
      [bind([groupForbid, {...blockGet, hidden: true, pred: null}]), visible(seen)],
      [visible(subjects.map(subject => ({ kind: 'declared', subject, path: team })))],
      [bind([{...groupForbid, path: company}]), visible(subjects.map(subject => ({kind: 'declared', subject, path: company})))]);
    for (const [path,scopeKind] of [[[],'collection'],[[],'resource'],[[...company,'teams'],'resource'],
        [[...company,'teams','..'],'resource'],[['other','A'],'resource']]) {
      txs.push([bind([{ ...groupForbid, path, scopeKind }])]);
    }
    const randomBinding = () => {
      const b = random(2) ? { ...groupForbid } : { ...bothList[random(2)] };
      b.path = [company, team, widget][random(3)];
      b.keys = [[A], ['teams.list'], [B], []][random(4)];
      b.effect = random(2) ? 'permit' : 'forbid';
      b.hidden = random(5) === 0;
      b.pred = [null, null, 'owner', 'classified'][random(4)];
      b.mayError = random(5) === 0;
      return b;
    };
    const changes = [
      () => bind(Array.from({ length: random(5) }, randomBinding)),
      () => role([[A], [B], [A, B], []][random(4)]),
      () => assign(members.filter(() => random(2))),
      () => visible(subjects.filter(() => random(2)).map(subject => ({ subject,
        kind: ['declared', 'get'][random(2)], path: random(2) ? widget : team }))),
      () => declare(levels.filter(() => random(2)).map(level =>
        ({ ...level, pattern: random(2) ? teamPattern : widgetPattern })))
    ];
    for (let j = 0; j < 6; j++) {
      txs.push(Array.from({ length: 1 + random(3) }, () => changes[random(changes.length)]()));
    }
    let current = initial;
    const expected = txs.map(writes => {
      const result = M.acceptPolicyTransaction(current, writes);
      current = result.store;
      return observation(M, current, result.accepted, subjects);
    });
    compare({ op: 'store', store: store(initial), subjects, transactions: txs.map(ws => ws.map(edit)) },
      expected);
  }
  return count + pinned;
}

module.exports = { storeCases };
