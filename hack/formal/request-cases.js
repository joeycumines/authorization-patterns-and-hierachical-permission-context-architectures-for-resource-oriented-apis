// Replay the calls made by the browser's embedded regression checks. The proxy
// forwards every call and records inputs and public outputs at the normalized
// boundary. The regression assertions themselves still run in the HTML model.
'use strict';

const assert = require('node:assert/strict');
const c = require('./codec');

const timestamp = v => typeof v === 'string' ? Date.parse(v) : v;

function normalizedVerdict(v) {
  if (typeof v === 'string') return c.lower(v);
  if (v.verdict !== undefined) return c.lower(v.verdict);
  return { operation: c.lower(v.operation), items: v.items.map(i => c.lower(i.verdict || i)) };
}

function checkMethodDeclarations(api, queue) {
  const { MODEL, FIXTURE } = api;
  const base = MODEL.interpret(FIXTURE);
  for (const name of ['GetWidget', 'UpdateWidget', 'DeleteWidget', 'InspectAccessPolicy',
    'google.longrunning.Operations/GetOperation']) {
    for (const effect of ['readOnly', 'mutating', 'destructive', 'unknown']) {
      const ir = c.descriptor(FIXTURE, base);
      ir.methods.find(m => m.name === name).effect = effect;
      const input = { op: 'descriptor', descriptor: ir };
      if (effect === c.enumName(base.methods[name].effect)) queue.compare(input, base.errors.length === 0);
      else queue.control(input, false);
    }
  }
  for (const name of ['UpdateWidget', 'InspectAccessPolicy']) {
    const method = FIXTURE.methods.find(m => m.name === name);
    for (const noSideEffects of [false, true]) {
      const source = { resources: FIXTURE.resources, methods: [{ ...method, noSideEffects }] };
      const checked = MODEL.interpret(source);
      const plain = { ...source, methods: [{ ...method, noSideEffects: false }] };
      const ir = c.descriptor(source, MODEL.interpret(plain));
      ir.methods[0].effect = 'readOnly';
      const input = { op: 'descriptor', descriptor: ir };
      if (checked.errors.length || checked.methods[name].effect === 'READ_ONLY') queue.compare(input, checked.errors.length === 0);
      else queue.control(input, false);
    }
  }
  const search = FIXTURE.methods.find(m => m.name === 'SearchWidgets');
  for (const first of ['parent', 'name']) for (const itemFilter of ['get', 'list', 'update', 'absent']) {
    const source = { resources: FIXTURE.resources, methods: [
      ...FIXTURE.methods.filter(m => ['GetWidget', 'ListWidgets', 'UpdateWidget'].includes(m.name)),
      { ...search, request: first === 'parent' ? search.request : { name: { type: 'Widget' } },
        authz: { ...search.authz, itemFilter } }
    ] };
    const result = MODEL.interpret(source);
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(source, result) }, result.errors.length === 0);
  }
  const get = FIXTURE.methods.find(m => m.name === 'GetWidget');
  for (const name of ['ListWidgets', 'SearchWidgets']) {
    const source = filter => ({ resources: FIXTURE.resources, methods: [get, {
      ...search, name, authz: { requirements: search.authz.requirements, ...(filter ? { itemFilter: 'get' } : {}) }
    }] });
    for (const filtered of [false, true]) {
      const raw = source(filtered), result = MODEL.interpret(raw), allowed = name === 'SearchWidgets' || !filtered;
      assert.equal(!result.errors.length, allowed);
      const compiled = allowed ? result : MODEL.interpret(source(false));
      const wire = c.descriptor(raw, compiled);
      const method = wire.methods.find(m => m.name === name);
      method.itemFilter = filtered ? 'get' : null;
      queue.compare({ op: 'descriptor', descriptor: wire }, !result.errors.length);
      const stale = structuredClone(wire);
      stale.methods.find(m => m.name === name).itemFilter = filtered ? null : 'get';
      queue.control({ op: 'descriptor', descriptor: stale }, false);
    }
  }
  const physicalName = 'companies/a/teams/b/widgets/w1'.split('/'), otherName = 'companies/a/teams/c/widgets/w2'.split('/');
  const item = { type: 'Widget' }, alt = { resource: 'Widget' };
  for (const verb of ['Get', 'Delete']) {
    const name = 'Batch' + verb + 'Widgets', key = 'widgets.' + verb.toLowerCase();
    const source = fields => ({ resources: FIXTURE.resources, methods: [{ name, authz: { standard: {} }, request: fields }] });
    const plain = MODEL.interpret(source({ names: item }));
    for (const [field, fields] of [['names[]', { names: item, requests: { alt } }],
      ['requests[].name', { requests: { alt, name: item } }], [null, { names: item, requests: { name: item } }],
      [null, { requests: { alt } }]]) {
      const raw = source(fields), model = MODEL.interpret(raw), accepted = !model.errors.length;
      assert.equal(accepted, field !== null);
      const descriptor = c.descriptor(raw, accepted ? model : plain);
      queue.compare({ op: 'descriptor', descriptor }, accepted);
      if (!accepted) continue;
      const method = model.methods[name], request = { [field]: [physicalName], 'requests[].alt.name': [otherName] };
      assert.equal(method.requirements[0].field, field);
      assert.equal(method.batchItemBinding.field, field);
      for (const path of [physicalName, otherName]) {
        const rules = [{ path, keys: [key], effect: 'permit' }];
        const status = MODEL.batchRequestStatus(rules, model, name, request);
        assert.equal(status, path === physicalName ? 'OK' : 'PERMISSION_DENIED');
        queue.compare({ op: 'batchRequest', descriptor, method: name, request, rules: rules.map(c.rule) }, status);
      }
    }
  }
  const objectNames = ['toString', 'constructor', 'hasOwnProperty', '__proto__'];
  for (const present of [false, true]) {
    const methods = present ? objectNames.map(name => ({ name, authz: { handlerPolicy: 'verify' } })) : [];
    const source = { resources: FIXTURE.resources, methods }, interpreted = MODEL.interpret(source);
    const descriptor = c.descriptor(source, interpreted);
    assert.deepEqual(Array.from(interpreted.errors), []);
    queue.compare({ op: 'descriptor', descriptor }, interpreted.errors.length === 0);
    for (const method of objectNames) {
      const result = MODEL.authorizeRequest([], interpreted, method, {});
      assert.equal(result.decision, present ? 'HANDLER_POLICY' : 'DENY');
      queue.compare({ op: 'authorize', descriptor, method, request: {}, rules: [] }, c.authorization(result));
    }
  }
  const Widget = FIXTURE.resources.Widget;
  for (const accessClass of ['ADMIN', 'UPDATE', 'READ']) {
    const field = { guard: { accessClass, operation: 'setOwner' } };
    const resource = { ...Widget, fields: { settings: { message: true }, 'settings.owner': field } };
    const source = { resources: { Widget: resource }, methods: FIXTURE.methods.filter(m => m.name === 'UpdateWidget') };
    const result = MODEL.interpret(source, { fieldGuards: true });
    const ir = c.descriptor(source, result);
    queue.compare({ op: 'descriptor', descriptor: ir }, result.errors.length === 0);
    // Test a stale guarded occurrence after a field or one of its parents becomes OUTPUT_ONLY.
    for (const path of ['settings', 'settings.owner']) {
      const fields = { ...resource.fields, [path]: { ...resource.fields[path], outputOnly: true } };
      const changed = { ...source, resources: { Widget: { ...resource, fields } } };
      const checked = MODEL.interpret(changed, { fieldGuards: true });
      const stale = c.descriptor(source, result);
      stale.methods[0].guardFields.find(f => f.path === path).outputOnly = true;
      queue.control({ op: 'descriptor', descriptor: stale }, false);
      queue.compare({ op: 'descriptor', descriptor: c.descriptor(changed, checked) }, checked.errors.length === 0);
    }
  }
}

function checkStandardResponses({ FIXTURE, MODEL }, queue) {
  const getBatch = FIXTURE.methods.find(m => m.name === 'BatchGetWidgets');
  const methods = [...FIXTURE.methods.filter(m => m.authz?.standard && /Widgets?$/.test(m.name)),
    { ...getBatch, name: 'BatchDeleteWidgets' }];
  for (const method of methods) {
    const rpc = method.name, batch = rpc.startsWith('Batch'), write = /Create|Update|Delete/.test(rpc);
    const sync = batch || rpc.startsWith('List') ? rpc + 'Response' : 'Widget';
    const request = { ...method.request };
    delete request.return_partial_success;
    const source = { resources: FIXTURE.resources, methods: [{ ...method, request, returns: sync }] };
    const valid = MODEL.interpret(source);
    assert.deepEqual(Array.from(valid.errors), []);
    for (const [returns, normalized, accepted] of [
      ['widgets.v1.' + sync, sync, true], ['UnrelatedResponse', 'UnrelatedResponse', false],
      ['google.longrunning.Operation', 'google.longrunning.Operation', write],
      ['google.protobuf.Empty', 'google.protobuf.Empty', rpc.includes('Delete')]
    ]) {
      const raw = {...source,methods:[{...source.methods[0],returns}]};
      const result = MODEL.interpret(raw);
      assert.equal(result.errors.length === 0, accepted, rpc + ' returns ' + returns);
      const descriptor = c.descriptor(raw, valid);
      descriptor.methods[0].standardReturn = normalized;
      queue.compare({ op: 'descriptor', descriptor }, result.errors.length === 0);
    }
    const name = 'widgets.v1.WidgetService/' + rpc;
    for (const type of ['Widget', '.assets.v2.Widget']) {
      const resources = { [type]: FIXTURE.resources.Widget };
      const fields = JSON.parse(JSON.stringify(request, (k,v) => v === 'Widget' ? type : v));
      const rawMethod = { ...method, name, request:fields };
      const make = (returns, authz = rawMethod.authz) => ({ resources, methods:[{...rawMethod, returns, authz}] });
      const served = MODEL.interpret(make(sync));
      assert.deepEqual(Array.from(served.errors), []);
      const pkg = !batch && !rpc.startsWith('List') && type !== 'Widget' ? 'assets.v2' : 'widgets.v1';
      for (const [returns, accepts] of [[pkg + '.' + sync, true], ['.' + pkg + '.' + sync, true],
        ['foreign.v1.' + sync, false], ['widgets..v1.' + sync, false], ['..' + pkg + '.' + sync, false],
        [FIXTURE.resources.Widget.type, !batch && !rpc.startsWith('List')], [null, false], [17, false]]) {
        const source = make(returns);
        const live = MODEL.interpret(source);
        assert.equal(live.errors.length === 0, accepts, name + ' returns ' + returns);
        // Start with the same valid signature, then pass the reflected return
        // unchanged. An unrelated package has exactly the same normalized leaf.
        const descriptor = c.descriptor(source, served);
        if (accepts) descriptor.methods[0].standardReturn = live.methods[name].standardReturn;
        queue.compare({op:'descriptor', descriptor}, live.errors.length === 0);
        if (/^(BatchGet|Get|List)/.test(rpc)) {
          const authz = {requirements:[{serviceRoot:true, operation:'read', accessClass:'READ'}]};
          const raw = make(returns, authz), explicit = MODEL.interpret(raw);
          assert.deepEqual(Array.from(explicit.errors), []);
          assert.equal(!!explicit.methods[name].resourceTarget, accepts);
          queue.compare({op:'descriptor', descriptor:c.descriptor(raw, explicit)}, explicit.errors.length === 0);
          if (!accepts) {
            const stale = c.descriptor(raw, MODEL.interpret(make(sync, authz)));
            queue.control({op:'descriptor', descriptor:stale}, false);
          }
        }
      }
    }
    if (batch) {
      const servicePermission = { requirements: [{ accessClass: 'ADMIN', operation: 'manage', serviceRoot: true }] };
      for (const authz of [method.authz, servicePermission]) {
        const withParent = childType => ({ ...source, methods: [{ ...source.methods[0], authz,
          request: { ...request, parent: { childType } } }] });
        const baseline = MODEL.interpret(withParent('Widget'));
        assert.deepEqual(Array.from(baseline.errors), []);
        for (const childType of ['Widget', FIXTURE.resources.Widget.type, 'Team', '']) {
          const raw = withParent(childType);
          const accepted = MODEL.interpret(raw).errors.length === 0;
          assert.equal(accepted, childType === 'Widget' || childType === FIXTURE.resources.Widget.type);
          queue.compare({ op: 'descriptor', descriptor: c.descriptor(raw, baseline) }, accepted);
        }
      }
    }
    if (rpc === 'BatchGetWidgets' || (batch && write)) {
      for (const lro of [true,false]) {
        const raw = {...source, methods:[{...source.methods[0], returns:lro ? 'google.longrunning.Operation' : sync,
          request:{...request,return_partial_success:true}}]};
        const descriptor = c.descriptor(raw, valid);
        descriptor.methods[0].standardReturn = lro ? 'google.longrunning.Operation' : sync;
        descriptor.methods[0].partialSuccess = 'requestSelected';
        const checked = MODEL.interpret(raw);
        assert.equal(checked.errors.length === 0, lro && write);
        queue.compare({ op: 'descriptor', descriptor }, checked.errors.length === 0);
      }
    }
  }
}

function checkStandardRegistration({ FIXTURE, MODEL }, recorder, queue) {
  const name = {type:'Widget'}, parent = {childType:'Widget'}, body = {resource:'Widget'};
  const standard = {standard:{}}, inspect = {accessClass:'READ',operation:'inspect',serviceRoot:true};
  const explicit = {requirements:[inspect]}, handler = {handlerPolicy:'streamHandler'};
  const source = (name, request, authz, options = {}) => ({resources:FIXTURE.resources,
    methods:[{name, request, authz, ...options}]});
  const check = (raw, normalized) =>
    queue.compare({op:'descriptor', descriptor:c.descriptor(raw, normalized)}, MODEL.interpret(raw,{fieldGuards:true}).errors.length === 0);
  for (const [rpc, request] of [
    ['GetWidget',{name}], ['ListWidgets',{parent}], ['CreateWidget',{parent, body}],
    ['UpdateWidget',{body, allow_missing:true}], ['DeleteWidget',{name}],
    ['BatchGetWidgets',{names:name}], ['BatchGetWidgets',{requests:{name}}],
    ['BatchCreateWidgets',{requests:{parent,body}}], ['BatchUpdateWidgets',{requests:{body,allow_missing:true}}],
    ['BatchDeleteWidgets',{names:name}], ['BatchDeleteWidgets',{requests:{name}}]
  ]) {
    const raw = source(rpc,request,standard), canonical = MODEL.interpret(raw,{fieldGuards:true});
    assert.deepEqual(Array.from(canonical.errors), []);
    check(raw, canonical);
    const custom = source(rpc,request,explicit), other = MODEL.interpret(custom,{fieldGuards:true});
    assert.deepEqual(Array.from(other.errors), []);
    check(custom,other);
    // The raw declaration still requests standard inference. The other authority
    // was produced by a valid explicit-permission registration for the same RPC.
    queue.control({op:'descriptor',descriptor:c.descriptor(raw,other)},false);
    for (const options of [{serverStreaming:true},{clientStreaming:true},{serverStreaming:true,clientStreaming:true}]) {
      for (const form of [standard,explicit,handler]) {
        const stream = source(rpc,request,form,options), live = MODEL.interpret(stream,{fieldGuards:true});
        const valid = (form === handler || (form === explicit && !options.clientStreaming));
        assert.equal(live.errors.length === 0, valid);
        check(stream,valid ? live : (form === standard ? canonical : other));
        if (valid && form === explicit) queue.control({op:'descriptor',descriptor:c.descriptor(stream,other)},false);
        if (form === explicit && options.clientStreaming) {
          const handled = MODEL.interpret(source(rpc,request,handler,options));
          queue.control({op:'descriptor',descriptor:c.descriptor(stream,handled)},false);
        }
      }
    }
  }
  const topLevel = {Widget:{...FIXTURE.resources.Widget,patterns:['widgets/{widget}']}};
  for (const [name,request,resourceType] of [
    ['ListWidgets',undefined,'Widget'], ['CreateWidget',{body},undefined],
    ['BatchCreateWidgets',{requests:{body}},undefined],
    ['UpdateWidget',{payload:body,unused:{resource:'Team'}},undefined]
  ]) {
    const raw = {...source(name,request,standard,{resourceType}),resources:{...topLevel,Team:FIXTURE.resources.Team}};
    const model = MODEL.interpret(raw, {fieldGuards:true});
    assert.deepEqual(Array.from(model.errors), []);
    check(raw,model);
    if (resourceType) {
      const other = {...raw,methods:[{...raw.methods[0],resourceType:'Team'}]};
      assert.ok(MODEL.interpret(other).errors.length);
      check(other,model);
    }
  }
  const resource = FIXTURE.resources.Widget.type;
  const base = source('GetWidget',{name,other:name}, {standard:{wildcardVariables:['team']}});
  const custom = source('GetWidget',base.methods[0].request,
    {requirements:[{operation:'inspect',accessClass:'READ',targetField:'name',wildcardVariables:['team']}]});
  queue.control({op:'descriptor',descriptor:c.descriptor(base,MODEL.interpret(custom))},false);
  const request = {name:['companies','A','teams','T','widgets','w']};
  for (const raw of [base,custom]) {
    const model = recorder.interpret(raw), key = model.methods.GetWidget.requirements[0].key;
    for (const permission of ['widgets.get','widgets.inspect']) {
      const outcome = recorder.authorizeRequest([{keys:[permission],path:[],effect:'permit'}],model,'GetWidget',request);
      assert.equal(outcome.decision,permission === key ? 'PROCEED' : 'DENY');
    }
  }
  const observed = MODEL.interpret(base);
  for (const change of [
    (m,r) => { r.key='widgets.inspect'; r.info.operation='inspect'; },
    (m,r) => { r.info.accessClass='admin'; m.effect='mutating'; },
    (m,r) => { r.info.explicitGrantOnly=true; },
    (m,r) => { r.field='other'; m.resourceTarget.field='other'; },
    (m,r) => { r.field=null; r.kind='root'; r.patterns=[[]]; },
    (m,r) => { r.parentOf=true; }, (m,r) => { r.perItem=true; },
    (m,r) => { r.condition='enabled'; }, (m,r) => { r.hoisted='name'; },
    (m,r) => { r.wildcardVariables=[]; },
    (m,r) => { m.requirements.push({...r,info:{...r.info,operation:'inspect'},key:'widgets.inspect'}); },
    m => { m.resourceTarget.resourceType=resource.replace('/Widget','/Team'); }
  ]) {
    const stale = c.descriptor(base,observed);
    change(stale.methods[0],stale.methods[0].requirements[0]);
    queue.control({op:'descriptor',descriptor:stale},false);
  }
  const legacy = c.descriptor(custom,MODEL.interpret(custom));
  delete legacy.methods[0].partialSource;
  queue.control({op:'descriptor',descriptor:legacy},false);
}

function checkUpdateMaskSource({ FIXTURE, MODEL }, queue) {
  const target = ['companies', 'a', 'teams', 't', 'widgets', 'w'];
  const permission = { requirements: [{ serviceRoot: true, accessClass: 'ADMIN', operation: 'submit' }] };
  const permit = key => ({ path: [], keys: [key], effect: 'permit' });
  for (const name of ['UpdateWidget', 'BatchUpdateWidgets']) for (const explicit of [false, true]) {
    const batch = name.startsWith('Batch');
    const request = batch ? { 'requests[].widget.name': [target], 'requests[].update': [{ mask: [] }] } :
      { 'widget.name': target, update: { mask: [] } };
    const rules = [permit(explicit ? 'service.submit' : 'widgets.update')];
    const source = mask => {
      const fields = { widget: { resource: 'Widget' }, ...(mask === undefined ? {} : { update_mask: mask }) };
      return { resources: FIXTURE.resources, methods: [{ name, authz: explicit ? permission : { standard: {} },
        request: batch ? { requests: fields } : fields }] };
    };
    const base = MODEL.interpret(source({}), { fieldGuards: true });
    for (const [mask, accepted] of [[undefined, true], [{}, true], [{type: 'google.protobuf.FieldMask'}, true],
      [null, false], [true, false], [[], false], [{other: true}, false], [{type: 'google.protobuf.Timestamp'}, false]]) {
      const raw = source(mask), model = MODEL.interpret(raw, { fieldGuards: true });
      assert.equal(!model.errors.length, accepted, name + ' mask ' + JSON.stringify(mask));
      const wire = c.descriptor(raw, accepted ? model : base);
      queue.compare({ op: 'descriptor', descriptor: wire }, model.errors.length === 0);
      if (!accepted) continue;
      const full = mask === undefined, method = wire.methods[0];
      assert.equal(method.fullReplacement, full);
      const run = (descriptor, grants) => ({ op: 'authorize', descriptor, method: name, request, rules: grants.map(c.rule) });
      const expected = MODEL.authorizeRequest(rules, model, name, request);
      assert.equal(expected.decision, full ? 'DENY' : 'PROCEED');
      const granted = [...rules, permit('widgets.setOwner')], authorized = MODEL.authorizeRequest(granted, model, name, request);
      assert.equal(authorized.decision, 'PROCEED');
      queue.compare(run(wire, rules), c.authorization(expected));
      queue.compare(run(wire, granted), c.authorization(authorized));
      const forged = structuredClone(wire);
      forged.methods[0].fullReplacement = !full;
      queue.control({ op: 'descriptor', descriptor: forged }, false);
      queue.control(run(forged, rules), c.authorization(expected));
      queue.control(run(forged, granted), c.authorization(authorized));
      const legacy = structuredClone(wire);
      delete legacy.methods[0].requestFields;
      legacy.methods[0].fullReplacement = false;
      queue.control({ op: 'descriptor', descriptor: legacy }, false);
    }
  }
  const masks = [{}, { type: 'FieldMask' }, { type: 'google.protobuf.FieldMask' }, { type: '.google.protobuf.FieldMask' }];
  const invalid = [true, { nested: {} }, { type: 'other.FieldMask' }, null];
  for (const explicit of [false, true]) {
    const name = 'BatchUpdateWidgets';
    const source = (outer, inner) => ({ resources: FIXTURE.resources, methods: [{ name,
      authz: explicit ? permission : { standard: {} },
      request: { update_mask: outer, requests: { widget: { resource: 'Widget' }, ...(inner === undefined ? {} : { update_mask: inner }) } }
    }] });
    const valid = MODEL.interpret(source({}, {}), { fieldGuards: true });
    const pairs = masks.flatMap(outer => masks.map(inner => [outer, inner, true])).concat(
      invalid.map(bad => [bad, {}, false]), [...invalid, undefined].map(bad => [{}, bad, false]));
    for (const [outer, inner, accepted] of pairs) {
      const raw = source(outer, inner), model = MODEL.interpret(raw, { fieldGuards: true });
      assert.equal(!model.errors.length, accepted);
      const descriptor = c.descriptor(raw, accepted ? model : valid);
      queue.compare({ op: 'descriptor', descriptor }, !model.errors.length);
      if (!accepted) continue;
      const request = { 'requests[].widget.name': [target], update_mask: ['owner'], 'requests[].update': [{ mask: ['owner'] }] };
      for (const guardGranted of [false, true]) {
        const rules = [permit(explicit ? 'service.submit' : 'widgets.update')];
        if (guardGranted) rules.push(permit('widgets.setOwner'));
        const result = MODEL.authorizeRequest(rules, model, name, request);
        assert.equal(result.decision, guardGranted ? 'PROCEED' : 'DENY');
        queue.compare({ op: 'authorize', method: name, descriptor, request, rules: rules.map(c.rule) }, c.authorization(result));
      }
    }
  }

}

function checkPartialDeclarations({ FIXTURE, MODEL }, recorder, queue) {
  const root = { serviceRoot: true, accessClass: 'ADMIN', operation: 'submit' };
  const item = { targetField: 'names[]', accessClass: 'ADMIN', operation: 'approve' };
  const names = { names: { type: 'Widget' } };
  {
    const method = { name: 'ReviewWidgets', returns: 'Operation', request: { ...names, return_partial_success: true } };
    const make = annotation => ({ resources: FIXTURE.resources, methods: [
      { ...method, authz: { requirements: [item], ...annotation } }
    ] });
    const valid = MODEL.interpret(make({}));
    for (const field of ['partialSuccess', 'partial_success']) {
      for (const [expected, spellings] of [
        ['REQUEST_SELECTED', [0, 'PARTIAL_SUCCESS_UNSPECIFIED', 'UNSPECIFIED', 3, 'REQUEST_SELECTED', 'PARTIAL_SUCCESS_REQUEST_SELECTED']],
        ['NEVER', [1, 'NEVER', 'PARTIAL_SUCCESS_NEVER']],
        ['ALWAYS', [2, 'ALWAYS', 'PARTIAL_SUCCESS_ALWAYS']],
        [null, [4, 'UNKNOWN']]
      ]) {
        for (const spelling of spellings) {
          const raw = make({ [field]: spelling });
          const parsed = MODEL.interpret(raw);
          assert.equal(!parsed.errors.length, expected !== null, JSON.stringify([field, spelling]));
          if (expected !== null) assert.equal(parsed.methods[method.name].partial, expected);
          const descriptor = c.descriptor(raw, parsed.errors.length ? valid : parsed);
          assert.equal(descriptor.methods[0].partialSource.mode, spelling, 'the native decoder receives the original enum');
          queue.compare({ op: 'descriptor', descriptor }, !parsed.errors.length);
        }
      }
    }
  }
  const configured = [
    { name: 'UpdateWidget', request: { widget: { resource: 'Widget' } }, requirements: [root] },
    { name: 'UpdateWidget', request: { widget: { resource: 'Widget' }, ...names }, requirements: [root, item] },
    { name: 'ReviewWidgets', request: names, requirements: [item], partial: true },
    { name: 'ReviewWidgets', request: names, requirements: [root] },
    { name: 'BatchUpdateWidgets', request: { requests: { widget: { resource: 'Widget' } } }, requirements: [root], partial: true },
    { name: 'BatchGetWidgets', request: names, requirements: [item], read: true },
    { name: 'BatchGetSimilarWidgets', request: names, requirements: [item], partial: true },
    { name: 'GetWidget', request: { name: { type: 'Widget' }, ...names }, requirements: [item], read: true },
    { name: 'ListWidgets', request: { parent: { childType: 'Widget' }, ...names }, requirements: [item], read: true }
  ];
  for (const fixture of configured) {
    const { name, requirements, request, partial = false } = fixture;
    for (const standard of [false, true]) {
      if (standard && !['UpdateWidget', 'BatchUpdateWidgets'].includes(name)) continue;
      const authz = standard ? { standard: {} } : { requirements };
      const make = (mode, selector, failedRequests, returns, serverStreaming = false) => ({
        resources: FIXTURE.resources, methods: [{ name, authz: mode === undefined ? authz : { ...authz, partialSuccess: mode },
          returns, serverStreaming, failedRequests, request: selector === undefined ? request : { ...request, return_partial_success: selector } }] });
      // Preserve the valid normalized geometry while submitting each original raw schema to both validators.
      const base = MODEL.interpret(make(undefined, undefined, false, undefined));
      assert.deepEqual([...base.errors], []);
      for (const [declared, selector, failed, returns, mode, streaming = false] of [
        [undefined, undefined, false, 'Operation', 'never'],
        [0, undefined, false, 'Operation', 'never'],
        [undefined, undefined, false, undefined, 'never'],
        [undefined, undefined, true, 'Operation', partial ? 'always' : null],
        ['PARTIAL_SUCCESS_UNSPECIFIED', true, false, '.google.longrunning.Operation', partial ? 'requestSelected' : null],
        [1, undefined, false, undefined, partial && !standard ? 'never' : null],
        [2, undefined, false, 'Operation', partial && !standard ? 'always' : null],
        ['REQUEST_SELECTED', true, false, 'google.longrunning.Operation', partial && !standard ? 'requestSelected' : null],
        ['REQUEST_SELECTED', undefined, true, 'Operation', null],
        ['ALWAYS', undefined, false, undefined, null],
        [undefined, {}, true, 'Operation', null],
        [undefined, true, false, 'ReviewWidgetsResponse', null],
        ['ALWAYS', true, false, 'Operation', null, true],
        ['UNKNOWN', undefined, false, 'Operation', null]
      ]) {
        const source = make(declared, selector, failed, returns, streaming), interpreted = MODEL.interpret(source);
        assert.equal(interpreted.errors.length === 0, mode !== null, JSON.stringify([name, standard, declared, selector, failed, returns, streaming, interpreted.errors]));
        const wire = c.descriptor(source, mode !== null ? interpreted : base);
        if (mode === null && !standard && fixture.read && returns === 'Operation') {
          // The wrong result prevents real read-disclosure registration. Only the raw request still identifies the read.
          wire.methods[0].resourceTarget = null;
          wire.methods[0].batchItemBinding = null;
          wire.methods[0].batchParentType = null;
        }
        queue.compare({ op: 'descriptor', descriptor: wire }, interpreted.errors.length === 0);
        if (mode === null) continue;
        const method = wire.methods[0];
        assert.equal(method.partialSuccess, mode);
        const forged = structuredClone(wire);
        forged.methods[0].partialSuccess = mode === 'never' ? 'always' : 'never';
        queue.control({ op: 'descriptor', descriptor: forged }, false);
        for (const select of [false, true]) {
          const input = { return_partial_success: select };
          assert.equal(MODEL.partialFor(interpreted.methods[name], input), mode === 'always' || mode === 'requestSelected' && select);
        }
        if (mode === 'requestSelected' && !standard && name === 'ReviewWidgets') {
          const verified = recorder.interpret(source);
          const address = ['companies', 'a', 'teams', 't', 'widgets', 'w'];
          for (const select of [false, true]) {
            const invoke = { 'names[]': [address], return_partial_success: select };
            const result = recorder.authorizeRequest([], verified, name, invoke, { handlerResolvesResiduals: true });
            assert.equal(result.decision, select ? 'PROCEED' : 'DENY');
          }
          const legacy = structuredClone(wire);
          delete legacy.methods[0].partialSource;
          queue.control({ op: 'descriptor', descriptor: legacy }, false);
        }
      }
    }
  }
}

function checkBatchWildcards({ FIXTURE, MODEL }, queue) {
  const ref = {type:'Widget'}, parent = {childType:'Widget'};
  const cases = [
    ['BatchGetWidgets', {names:ref}, 'names[]'], ['BatchGetWidgets', {requests:{name:ref}}, 'requests[].name'],
    ['BatchDeleteWidgets', {names:ref}, 'names[]'], ['BatchDeleteWidgets', {requests:{name:ref}}, 'requests[].name'],
    ['BatchCreateWidgets', {requests:{parent, widget:{resource:'Widget'}}}, 'requests[].parent'],
    ['BatchUpdateWidgets', {requests:{widget:{resource:'Widget'},allow_missing:true}}, 'requests[].widget.name']
  ];
  for (const [name, shape, field] of cases) {
    const source = (authz, outer) => ({resources:FIXTURE.resources, methods:[{name, authz,
      request:outer === undefined ? shape : {...shape,parent:outer}}]});
    const standard = vars => ({standard:{wildcardVariables:vars}});
    for (const [outer, vars, valid] of [
      [parent, ['team'], true], [parent, ['widget'], false], [parent, ['missing'], false],
      [undefined, ['team'], false], [{}, ['team'], false], [{type:'Team'}, ['team'], false],
      [undefined, [], true], [parent, [], true]
    ]) {
      const raw = source(standard(vars), outer);
      const checked = MODEL.interpret(raw);
      assert.equal(checked.errors.length === 0, valid, name);
      // The normalized baseline supplies the physical address even for a source
      // the JS interpreter rejects. Parent annotation and type come from raw.
      const base = MODEL.interpret(source(standard([]), outer === parent ? parent : undefined));
      queue.compare({op:'descriptor',descriptor:c.descriptor(raw,base)},checked.errors.length === 0);
    }
    for (const outer of [undefined, parent]) {
      const requirement = {operation:'inspect',accessClass:'READ',targetField:field};
      const raw = source({requirements:[requirement]},outer), base = MODEL.interpret(raw);
      assert.equal(base.errors.length,0,name);
      queue.compare({op:'descriptor',descriptor:c.descriptor(raw,base)},base.errors.length === 0);
      const bad = source({requirements:[{...requirement,wildcardVariables:['team']}]},outer);
      const rejected = MODEL.interpret(bad);
      assert.ok(rejected.errors.length,name);
      const ir = c.descriptor(bad,base);
      ir.methods[0].requirements[0].wildcardVariables = ['team'];
      queue.compare({op:'descriptor',descriptor:ir},rejected.errors.length === 0);
      const mislabeled = c.descriptor(bad,base);
      Object.assign(mislabeled.methods[0].requirements[0], {perItem:false,wildcardVariables:['team']});
      queue.control({op:'descriptor',descriptor:mislabeled},false);
      if (outer) {
        const wrongForm = c.descriptor(raw,base);
        wrongForm.methods[0].standardBatchWildcards = ['team'];
        queue.control({op:'descriptor',descriptor:wrongForm},false);
      }
    }
    const prefix = source(standard(['team']),parent), good = MODEL.interpret(prefix);
    const unsafe = c.descriptor(prefix,good);
    (unsafe.methods[0].batchItemBinding || unsafe.methods[0].writerBinding).wildcardVariables = ['team'];
    queue.control({op:'descriptor',descriptor:unsafe},false);
  }
}

function checkPhysicalBatchParents({ FIXTURE }, recorder, queue) {
  const root = {requirements:[{serviceRoot:true,accessClass:'ADMIN',operation:'dispatch'}]};
  const widget = {type:'Widget'}, child = {childType:'Widget'};
  const team = ['companies','a','teams','b'], wrong = ['companies','a','teams','x'], w = [...team,'widgets','w'];
  const shapes = [
    ['BatchGetWidgets',{names:widget},{'names[]':[w]},'get'],
    ['BatchGetWidgets',{requests:{name:widget}},{'requests[].name':[w]},'get'],
    ['BatchDeleteWidgets',{names:widget},{'names[]':[w]},'delete'],
    ['BatchDeleteWidgets',{requests:{name:widget}},{'requests[].name':[w]},'delete'],
    ['BatchCreateWidgets',{requests:{parent:child,widget:{resource:'Widget'}}},{'requests[].parent':[team],'requests[].id':['w']},'create'],
    ['BatchUpdateWidgets',{requests:{widget:{resource:'Widget'}}},{'requests[].widget.name':[w]},'update']
  ];
  for (const [name,fields,input,op] of shapes) for (const authz of [{standard:{}},root]) {
    const raw = outer => ({resources:FIXTURE.resources, methods:[{name,authz,request:
      outer === undefined ? fields : {...fields,parent:outer}}]});
    const omitted = recorder.interpret(raw(undefined));
    assert.deepEqual([...omitted.errors], []);
    for (const [outer,valid] of [
      [undefined,true], [child,true], [{childType:FIXTURE.resources.Widget.type},true],
      [{type:'Team'},false], [{type:FIXTURE.resources.Team.type},false], [{},false], [true,false], [null,false],
      [[],false], [{childType:'Team'},false], [{childType:''},false], [{childType:17},false],
      [{childType:'Widget',type:'Team'},false], [{childType:'Widget',resource:'Widget'},false]
    ]) {
      const source = raw(outer), interpreted = recorder.interpret(source);
      assert.equal(interpreted.errors.length === 0, valid, name + ' ' + JSON.stringify(outer));
      const wire = c.descriptor(source, valid ? interpreted : omitted);
      queue.compare({op:'descriptor',descriptor:wire},interpreted.errors.length === 0);
      if (!valid) continue;
      const m = wire.methods[0], hasParent = outer !== undefined;
      assert.equal(m.batchLevel.includes('parent'), hasParent);
      assert.equal(m.batchParentType, hasParent ? FIXTURE.resources.Widget.type : null);
      const staleType = structuredClone(wire);
      staleType.methods[0].batchParentType = hasParent ? null : FIXTURE.resources.Widget.type;
      queue.control({op:'descriptor',descriptor:staleType},false);
      const staleMarker = structuredClone(wire);
      staleMarker.methods[0].batchLevel = hasParent ? [] : ['parent'];
      queue.control({op:'descriptor',descriptor:staleMarker},false);
      const legacy = structuredClone(wire);
      delete legacy.methods[0].requestFields;
      // A checked legacy parent type cannot silently lose its runtime check.
      if (hasParent) {
        legacy.methods[0].batchLevel = [];
        queue.control({op:'descriptor',descriptor:legacy},false);
      }
      const rules = [{path:[],keys:[authz.standard ? 'widgets.'+op : 'service.dispatch'],effect:'permit'}];
      for (const [parent,status] of [[undefined,'OK'],[team,'OK'],[wrong,hasParent ? 'INVALID_ARGUMENT':'OK']]) {
        const request = parent ? {...input,parent} : input;
        assert.equal(recorder.batchRequestStatus(rules,interpreted,name,request),status);
        assert.equal(recorder.batchRequestStatus([],interpreted,name,request),'PERMISSION_DENIED');
        const authorized = recorder.authorizeRequest(rules,interpreted,name,request);
        assert.equal(authorized.decision === 'PROCEED' ? 'OK' : authorized.status || authorized.reason,status);
        assert.equal(recorder.authorizeRequest([],interpreted,name,request).reason,'POLICY');
      }
    }
  }
}

function checkResourceCatalog(api, queue) {
  const local = { type: 'catalog.example/Item', plural: 'items', patterns: ['items/{item}'] };
  const foreign = { type: 'other.example/Flag', external: true, patterns: ['flags/{flag}'] };
  const read = { name: 'GetFlag', authz: { standard: {} }, request: { name: { type: 'Flag' } } };
  const compare = (resources, methods = [], opts = {}) => {
    const source = { resources, methods };
    const result = api.MODEL.interpret(source, opts);
    const descriptor = c.descriptor(source, result);
    queue.compare({ op: 'descriptor', descriptor }, result.errors.length === 0);
    return descriptor;
  };
  for (const overrides of [
    {}, { plural: 'items' }, { plural: 'flags', patterns: ['flags/default/items/{item}'] }, { plural: 'flags' }
  ]) {
    const resources = { Item: local, Flag: { ...foreign, ...overrides } };
    const unused = compare(resources);
    const used = compare(resources, [read]);
    if (unused.resources.some(r => r.resourceType === foreign.type) ||
        !used.resources.some(r => r.resourceType === foreign.type)) throw Error('incorrect imported resource catalog');
  }
  const bare = { ...local, plural: undefined };
  const other = { type: 'catalog.example/Flag', patterns: ['flags/{flag}'] };
  compare({ Item: bare, Flag: other });
  compare({ Item: bare, Flag: other }, [read]);
  compare({ Item: { ...bare, plural: '' } });
  const guarded = { ...bare, fields: { owner: { guard: { accessClass: 'ADMIN', operation: 'setOwner' } } } };
  compare({ Item: guarded }, [], { fieldGuards: true });
  compare({ Item: guarded }, [], { fieldGuards: false });
  compare({ Item: { ...guarded, plural: 'items' } }, [], { fieldGuards: true });
  const singleton = { ...local, patterns: ['companies/{company}/flags'] };
  const flags = { ...foreign, plural: 'flags', patterns: ['companies/{parent}/flags/{flag}'] };
  compare({ Item: singleton, Flag: flags });
  compare({ Item: singleton, Flag: flags }, [read]);
  compare({ Flag: { ...flags, external: false, type: other.type }, Item: singleton });
  compare({ Item: { ...local, patterns: [...flags.patterns, ...singleton.patterns] } });
  compare({ Item: { ...local, patterns: ['flags', 'flags/{flag}/settings'] } });
  compare({ Item: { ...local, patterns: ['companies/{company}/settings', 'teams/{team}/settings/{setting}'] } });
  for (const [registryKey, type, valid] of [
    ['Item', undefined, false], ['Item', local.type, true], [local.type, undefined, true]
  ]) {
    const source = { apiService: 'catalog.example', resources: { [registryKey]: { ...local, type } },
      methods: [{ name: 'GetItem', authz: { standard: {} }, request: { name: { type: registryKey } } }] };
    const result = api.MODEL.interpret(source);
    assert.equal(result.errors.length === 0, valid);
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(source, result) }, result.errors.length === 0);
  }
}

// Supply the same input to both models independently of which callbacks JS calls.
function checkDescriptorSources({MODEL:m}, queue) {
  const node = {type:'tree.example/Node', plural:'nodes', patterns:['nodes/{node}', 'nodes/{parent}/children/{child}'],
    fields:{label:{guard:{accessClass:'UPDATE',operation:'setLabel'}}}};
  const resources = {Node:node}, root = {serviceRoot:true, operation:'approve', accessClass:'ADMIN'};
  const update = {name:'UpdateNode',request:{node:{resource:'Node'},allow_missing:true,update_mask:{}},authz:{standard:{}}};
  const check = (source, valid, compiled) => {
    const result = m.interpret(source,{fieldGuards:true});
    assert.equal(!result.errors.length, valid, JSON.stringify(result.errors));
    queue.compare({op:'descriptor',descriptor:c.descriptor(source,compiled ?? result)}, !result.errors.length);
    return result;
  };
  const model = check({resources,methods:[update]},true);
  const valid = {resources,methods:[]};
  const pureQuery = {name:'QueryPermissionContexts',authz:{handlerPolicy:'authenticated_subject_disclosure'},noSideEffects:true,request:{}};
  for (const [extra, accepted] of [
    [{},true], [{apiService:'tree.example'},true], [{apiService:'another.example'},false], [{apiService:null},false],
    [{resources:{}},false], [{resources:{},apiService:'mixed.example'},true],
    [{resources:{},methods:[pureQuery]},true],
    [{resources:{},apiService:'authz.example',methods:[pureQuery]},true],
    // proto3 api_service has no presence (AIP-149): an empty string is the omitted value.
    [{resources:{},apiService:'',methods:[pureQuery]},true], [{resources:{},apiService:''},false],
    [{resources:{},apiService:null,methods:[pureQuery]},false],
    [{resources:{Ext:{type:'iam.example/User',external:true,patterns:['users/{user}']}},methods:[pureQuery]},true],
    [{resources:{},methods:[pureQuery,{name:'Ping',request:{}}]},false],
    [{resources:{},methods:[{name:'Export',authz:{requirements:[root]},request:{}}]},false],
    [{resources:{Ext:{type:'iam.example/User',external:true,plural:'users',patterns:['users/{user}']}},
      methods:[{name:'InspectUser',authz:{requirements:[{accessClass:'READ',operation:'inspect'}]},request:{name:{type:'Ext'}}}]},false],
    [{resources:{},required:true,methods:[{...pureQuery,returns:'google.longrunning.Operation'}],imported:[
      {method:'google.longrunning.Operations/GetOperation',authz:{handlerPolicy:'op'},noSideEffects:true},
      {method:'google.longrunning.Operations/ListOperations',authz:{handlerPolicy:'op'},noSideEffects:true},
      {method:'google.longrunning.Operations/WaitOperation',authz:{handlerPolicy:'op'},noSideEffects:true},
      {method:'google.longrunning.Operations/CancelOperation',unimplemented:true},
      {method:'google.longrunning.Operations/DeleteOperation',unimplemented:true}
    ]},true],
    [{resources:{},methods:[],imported:[{method:'google.longrunning.Operations/CancelOperation',unimplemented:true}]},false]
  ]) check({...valid,...extra},accepted);
  const namelessSource = {resources:{},methods:[pureQuery]};
  const namelessModel = check(namelessSource,true);
  assert.equal(namelessModel.apiService,null);
  for (const bad of [{root:[{type:'/service',cls:'ADMIN'}]}, {bare:[{type:'service',cls:'ADMIN'}]}]) {
    queue.compare({op:'validateRoleSelectors',descriptor:c.descriptor(namelessSource,namelessModel),selectors:bad},
      m.validateRoleSelectors(namelessModel,bad).ok);
  }
  for (const external of [false,true]) for (const explicit of [false,true]) {
    const source = {...valid, resources:{...resources,Leaf:{type:'leaf.example/Leaf',external,patterns:['leaves/{leaf}']}},
      ...(explicit ? {apiService:'mixed.example'} : {})};
    check(source,external !== explicit);
  }
  for (const duplicate of ['nodes/{another}', 'nodes/{parent}/children/{id}']) {
    check({...valid,resources:{...resources,Leaf:{type:'tree.example/Leaf',plural:'leaves',patterns:[duplicate]}}},false);
  }
  const custom = (request, requirements) => ({name:'Review',request,authz:{requirements}});
  for (const spec of [{...root,parentTarget:true},
    {resourceType:'Node',targetField:'parent',parentTarget:true,operation:'inspect',accessClass:'READ'}]) {
    check({resources,methods:[custom({parent:{childType:'Node'}},[spec])]},false);
  }
  const hoisted = custom({target:{sub:true}, requests:{target:{}}}, [
    {targetField:'requests[].target',resourceType:'Node',accessClass:'READ',operation:'inspect'}]);
  check({resources,methods:[hoisted]},false);
  const bare = {...node,plural:undefined,fields:{}};
  check({resources:{Node:bare},methods:[{name:'ListNodes',request:{parent:{childType:'Node'}},authz:{requirements:[root]}}]},true);
  const special = {...update,authz:{requirements:[root]}};
  const create = {name:'CreateNode',request:{parent:{childType:'Node'},node:{resource:'Node'}},authz:{requirements:[
    {resourceType:'Node',targetField:'parent',accessClass:'CREATE',operation:'create',explicitGrantOnly:true}]}};
  const explicit = check({resources,methods:[special,create]},true);
  assert.equal(explicit.keys['nodes.create'].explicitOnly,true);
  const desc = c.descriptor({resources,methods:[update]},model);
  const recognized = c.descriptor({resources,methods:[update]}, {...model,apiService:'unrelated.example'});
  assert.equal(recognized.service,'tree.example');
  for (const key of ['resourceSources','guardSources','declaredMethods']) {
    const absent = structuredClone(desc);
    delete absent[key];
    queue.control({op:'descriptor',descriptor:absent},false);
  }
  const name = ['nodes','n','children','c'], parent = name.slice(0,2);
  const req = {'node.name':name,allow_missing:true,update:{mask:['label'],populated:['label']}};
  const requirements = m.requirementsFor(model,'UpdateNode',req);
  assert.deepEqual(Array.from(requirements.find(r => r.key === 'nodes.setLabel').targets, t => Array.from(t)),[name,parent]);
  const rules = [{path:[],keys:['nodes.update','nodes.create','nodes.setLabel'],effect:'permit'}];
  const auth = m.authorizeRequest(rules,model,'UpdateNode',req);
  assert.equal(auth.decision,'PROCEED');
  queue.compare({op:'authorize',descriptor:desc,method:'UpdateNode',request:req,rules:rules.map(c.rule)},c.authorization(auth));
  const batch = {name:'BatchUpdateNodes', request:{allow_missing:true,requests:update.request}, authz:{requirements:[root]}};
  const batched = {resources,methods:[batch]}, batchModel = check(batched,true);
  const batchRequest = {allow_missing:true, 'requests[].node.name':[name], 'requests[].update':[req.update]};
  const bound = m.requirementsFor(batchModel,batch.name,batchRequest);
  assert.equal(batchModel.methods[batch.name].upsertBinding.hoisted,'allow_missing');
  assert.deepEqual(Array.from(bound.find(r => r.key === 'nodes.setLabel').targets, t => Array.from(t)),[name,parent]);
  for (const site of [name,parent]) {
    const grants = [{path:[], keys:['service.approve'],effect:'permit'}, {path:site,keys:['nodes.setLabel'],effect:'permit'}];
    const result = m.authorizeRequest(grants,batchModel,batch.name,batchRequest);
    assert.equal(result.decision,site === parent ? 'PROCEED' : 'DENY');
    queue.compare({op:'authorize',descriptor:c.descriptor(batched,batchModel),method:batch.name,request:batchRequest,
      rules:grants.map(c.rule)},c.authorization(result));
  }
  const mapKey = 'labels.`en.gb`', fields = {labels:{message:true,repeatedOrMap:true},[mapKey]:{message:true},
    [mapKey + '.text']:{guard:{operation:'localize',accessClass:'UPDATE'}},[mapKey + '.internal']:{outputOnly:true}};
  check({resources:{Node:{...node,fields}},methods:[update]},true);
  const mask = {mask:[mapKey + '.text',mapKey + '.internal']};
  const written = m.effectiveMask(mask,fields);
  assert.deepEqual(Array.from(written),[mapKey + '.text']);
  queue.compare({op:'effectiveMask',request:mask,fields:c.fieldMetadata(fields)},written);
}

function checkFaultEvidence(M, I, descriptor, target, queue) {
  const key = 'widgets.get', get = { name: target };
  const batch = { parent: target.slice(0, -2), 'names[]': [target] };
  const permit = { path: [], keys: [key], effect: 'permit' };
  for (const attrsOf of [null, true, 'owner']) {
    const opts = { authority: 'skipErrors', attrsOf, faults: () => true };
    const rules = [permit, { ...permit, effect: 'forbid', mayError: true }];
    const input = { descriptor, rules: rules.map(c.rule), authority: opts.authority, invalidAttrsOf: true, hasFaults: true,
      faultOutcomesByPath: [{ path: target, rule: c.rule(rules[1]), fault: true }] };
    const auth = M.authorizeRequest(rules, I, 'GetWidget', get, opts);
    assert.equal(auth.reason, 'SERVER_FAULT');
    assert.equal(auth.decision, 'DENY');
    assert.equal(auth.residuals.length, 0);
    const status = M.batchRequestStatus(rules, I, 'BatchGetWidgets', batch, opts);
    assert.equal(status, 'PERMISSION_DENIED');
    queue.compare({ ...input, op: 'authorize', method: 'GetWidget', request: get }, c.authorization(auth));
    queue.compare({ ...input, op: 'batchRequest', method: 'BatchGetWidgets', request: batch }, status);
  }
  const observations = [
    [{}, null], [{ faults: null }, null], [{ faults: true }, null],
    [{ faults: () => undefined }, null], [{ faults: () => null }, null],
    [{ faults: () => 'true' }, null], [{ faults: () => { throw Error('unavailable'); } }, null],
    [{ faults: () => false }, false], [{ faults: () => true }, true]
  ];
  for (const authority of ['failClosed', 'skipErrors']) {
    for (const effect of ['permit', 'forbid']) for (const pred of [null, 'owner']) {
      const risky = { ...permit, effect, pred, mayError: true };
      const rules = effect === 'permit' ? [risky] : [permit, risky];
      const wire = { rules: rules.map(c.rule), authority };
      for (const [options, fault] of observations) {
        const callable = typeof options.faults === 'function';
        const faultOutcomes = callable ? [[c.rule(risky), fault]] : undefined;
        const faultOutcomesByPath = callable ? [{ path: target, rule: c.rule(risky), fault }] : undefined;
        for (const owner of [undefined, false, true]) {
          const attrs = owner === undefined ? {} : { owner: owner ? 'alice' : 'another' };
          const predicates = owner === undefined ? [] : [['owner', owner]];
          const opts = { ...options, authority };
          const knownFacts = owner !== undefined;
          if (knownFacts) opts.attrsOf = () => attrs;
          const permits = effect === 'permit' && fault === false && (!pred || owner === true);
          const clearsForbid = effect === 'forbid' &&
            ((fault === true && authority === 'skipErrors') || (fault === false && pred && owner === false));
          const expected = permits || clearsForbid ? 'ALLOW' : 'DENY';
          const decision = M.authorize(rules, key, target, attrs, opts);
          assert.equal(decision, expected);
          assert.equal(M.decideRequest(rules, I, 'GetWidget', get, () => attrs, opts), expected);
          queue.compare({ ...wire, op: 'decide', key, path: target, predicates, faultOutcomes }, c.lower(decision));

          const requestInput = { ...wire, descriptor, knownFacts, hasFaults: callable, predicates, faultOutcomesByPath };
          const auth = M.authorizeRequest(rules, I, 'GetWidget', get, opts);
          const status = M.batchRequestStatus(rules, I, 'BatchGetWidgets', batch, opts);
          const authorized = expected === 'ALLOW';
          assert.equal(auth.decision, authorized ? 'PROCEED' : 'DENY');
          assert.equal(status, authorized ? 'OK' : 'PERMISSION_DENIED');
          let residual;
          if (!knownFacts && pred && fault === false) residual = 'PREDICATE';
          if (!knownFacts && !callable && authority === 'skipErrors') residual = 'POLICY_EVALUATION';
          assert.deepEqual(Array.from(auth.residuals, r => r.kind), residual ? [residual] : []);
          assert.equal(auth.reason, residual ? 'UNHANDLED_RESIDUAL' : authorized ? undefined : 'POLICY');
          queue.compare({ ...requestInput, op: 'authorize', method: 'GetWidget', request: get }, c.authorization(auth));
          queue.compare({ ...requestInput, op: 'batchRequest', method: 'BatchGetWidgets', request: batch }, status);
        }
      }
    }
  }

  // A positive observation about one rule or item cannot fill a missing result for another.
  const riskyPermit = { ...permit, mayError: true }, riskyForbid = { ...riskyPermit, effect: 'forbid' };
  const rules = [riskyPermit, riskyForbid], other = [...batch.parent, 'widgets', 'w2'];
  const faultOutcomesByPath = [
    { path: target, rule: c.rule(riskyPermit), fault: false },
    { path: target, rule: c.rule(riskyForbid), fault: true },
    { path: other, rule: c.rule(riskyForbid), fault: true }
  ];
  const opts = { authority: 'skipErrors', faults: (r, path) => {
    if (r === riskyForbid) return true;
    if (path.at(-1) === target.at(-1)) return false;
  } };
  for (const knownFacts of [false, true]) {
    const options = knownFacts ? { ...opts, attrsOf: () => ({}) } : opts;
    for (const names of [[target], [other], [target, other]]) {
      const request = { ...batch, 'names[]': names };
      const status = M.batchRequestStatus(rules, I, 'BatchGetWidgets', request, options);
      assert.equal(status, names.includes(other) ? 'PERMISSION_DENIED' : 'OK');
      queue.compare({ op: 'batchRequest', descriptor, method: 'BatchGetWidgets', request, hasFaults: true,
        rules: rules.map(c.rule), authority: opts.authority, knownFacts, faultOutcomesByPath }, status);
    }
  }
}

function checkResolvedRequests({ MODEL: M, FIXTURE }, queue) {
  const review = { name: 'ReviewWidgets', request: { names: { type: 'Widget' }, parent: { childType: 'Widget' } },
    authz: { requirements: [
      { accessClass: 'READ', operation: 'get', targetField: 'names[]' },
      { accessClass: 'ADMIN', operation: 'approve', targetField: 'parent' }
    ] } };
  const batchDelete = { name: 'BatchDeleteWidgets', authz: { standard: {} },
    request: { parent: { childType: 'Widget' }, names: { type: 'Widget' } } };
  const Widget = FIXTURE.resources.Widget;
  const source = { ...FIXTURE, resources: { ...FIXTURE.resources, Widget: { ...Widget,
    patterns: [...Widget.patterns, 'companies/{company}/widgets/{widget}'] } },
    methods: [...FIXTURE.methods.map(m => m.name === 'BatchGetWidgets'
      ? { ...m, authz: { standard: { wildcardVariables: ['team'] } } } : m), review, batchDelete] };
  const I = M.interpret(source);
  assert.deepEqual(Array.from(I.errors), []);
  const descriptor = c.descriptor(source, I);
  const company = ['companies', 'A'], team = [...company, 'teams', 'T'];
  const alias = [...company, 'teams', 'current'], other = [...company, 'teams', 'B'];
  const widget = p => [...p, 'widgets', 'w'];
  const permit = (path, key = 'widgets.get') => ({ path, keys: [key], effect: 'permit' });
  const attrsOf = () => ({});
  function compare(method, request, rules, names, expected, batchStatus) {
    const visited = [];
    const resolvePrefix = p => {
      visited.push(p.join('/'));
      return names.find(([q]) => q.join('/') === p.join('/'))?.[1];
    };
    const opts = { resolvePrefix, attrsOf };
    const wire = { method, request, descriptor, rules: rules.map(c.rule), names, knownFacts: true };
    const auth = M.authorizeRequest(rules, I, method, request, opts);
    assert.equal(auth.decision, expected === 'PROCEED' ? 'PROCEED' : 'DENY', method);
    assert.equal(auth.reason, expected === 'PROCEED' ? undefined : expected, method);
    assert.equal(auth.status, expected === 'BATCH' ? batchStatus : undefined, method);
    queue.compare({ ...wire, op: 'authorize' }, c.authorization(auth));
    if (batchStatus !== undefined) {
      const status = M.batchRequestStatus(rules, I, method, request, opts);
      assert.equal(status, batchStatus, method);
      queue.compare({ ...wire, op: 'batchRequest' }, status);
    } else {
      assert.equal(M.decideRequest(rules, I, method, request, attrsOf, opts), expected === 'PROCEED' ? 'ALLOW' : 'DENY', method);
    }
    return visited;
  }

  const get = { name: widget(alias) };
  const aliases = [[alias, team]];
  compare('GetWidget', get, [permit(team)], aliases, 'PROCEED');
  compare('GetWidget', get, [permit([]), { ...permit(team), effect: 'forbid' }], aliases, 'POLICY');
  // A resolved resource may use another declared pattern and a different parent.
  compare('GetWidget', get, [permit(widget(company))], [[widget(alias), widget(company)]], 'PROCEED');
  compare('GetWidget', get, [permit([])], [[widget(alias), null]], 'UNBOUND');

  const getBatch = (parent, names) => ({ parent, 'names[]': names });
  for (const [parent, item] of [[alias, widget(team)], [team, widget(alias)], [alias, widget(alias)]]) {
    compare('BatchGetWidgets', getBatch(parent, [item]), [permit(team)], aliases, 'PROCEED', 'OK');
  }
  const create = [permit(team, 'widgets.create')];
  for (const parent of [[], alias, team]) {
    compare('BatchCreateWidgets', { parent: alias, 'requests[].parent': [parent] }, create, aliases, 'PROCEED', 'OK');
  }
  compare('BatchGetWidgets', getBatch(alias, [widget(other)]), [permit([])], aliases, 'BATCH', 'INVALID_ARGUMENT');
  compare('BatchGetWidgets', getBatch(alias, [widget(alias), widget(team)]), [permit(team)], aliases, 'BATCH', 'INVALID_ARGUMENT');
  compare('BatchCreateWidgets', { parent: alias, 'requests[].parent': [[], team], 'requests[].id': ['w', 'w'] },
    create, aliases, 'BATCH', 'INVALID_ARGUMENT');
  const pair = [widget(team), [...team, 'widgets', 'w2']];
  for (const [method, field, key] of [
    ['BatchGetWidgets', 'names[]', 'widgets.get'],
    ['BatchDeleteWidgets', 'names[]', 'widgets.delete'],
    ['BatchUpdateWidgets', 'requests[].widget.name', 'widgets.update']
  ]) {
    compare(method, { parent: team, [field]: pair, 'requests[].id': ['same', 'same'] },
      [permit(team, key)], [], 'PROCEED', 'OK');
  }
  compare('BatchCreateWidgets', { parent: team, 'requests[].parent': [team, team], 'requests[].id': ['w', 'w2'] },
    create, [], 'PROCEED', 'OK');
  const companyAlias = ['companies', 'mine'];
  const wildcard = [...company, 'teams', '-'], aliasWildcard = [...companyAlias, 'teams', '-'];
  compare('BatchGetWidgets', getBatch(aliasWildcard, [widget(team)]), [permit(company)],
    [[companyAlias, company]], 'PROCEED', 'OK');
  const list = [permit(company, 'widgets.list')];
  compare('ListWidgets', { parent: aliasWildcard }, list, [[companyAlias, company]], 'PROCEED');
  compare('ListWidgets', { parent: wildcard }, list, [[wildcard, team]], 'SERVER_FAULT');
  compare('ListWidgets', { parent: wildcard }, list, [[wildcard, null]], 'UNBOUND');
  const narrowed = getBatch(wildcard, [widget(team)]);
  compare('BatchGetWidgets', narrowed, [permit(company)], [[wildcard, team]], 'SERVER_FAULT', 'PERMISSION_DENIED');
  compare('BatchGetWidgets', narrowed, [permit(company)], [[wildcard, null]], 'BATCH', 'PERMISSION_DENIED');

  for (const bad of [['companies'], ['unknown', 'id'], team, [], ['companies', '..']]) {
    const names = [[widget(alias), bad]];
    compare('GetWidget', get, [permit([])], names, 'SERVER_FAULT');
    compare('BatchGetWidgets', getBatch(team, [widget(alias)]), [permit([])], names, 'SERVER_FAULT', 'PERMISSION_DENIED');
  }
  // Binding checks precede the resolver. An adapter cannot turn an off-pattern
  // request into a valid target, or turn its input error into a server fault.
  const offPattern = ['outside', 'name'];
  for (const mapped of [widget(team), ['companies']]) {
    const names = [[offPattern, mapped]];
    const singularReads = compare('GetWidget', { name: offPattern }, [permit([])], names, 'UNBOUND');
    const itemReads = compare('BatchGetWidgets', getBatch(team, [offPattern]), [permit(team)], names, 'BATCH', 'INVALID_ARGUMENT');
    assert.ok(![...singularReads, ...itemReads].includes(offPattern.join('/')));
  }
  for (const mapped of [team, ['companies']]) {
    const names = [[offPattern, mapped]];
    const request = getBatch(offPattern, [widget(team)]);
    const reads = compare('BatchGetWidgets', request, [permit(team)], names, 'BATCH', 'INVALID_ARGUMENT');
    assert.ok(!reads.includes(offPattern.join('/')));
    compare('BatchGetWidgets', request, [], names, 'POLICY', 'PERMISSION_DENIED');
    compare('BatchCreateWidgets', { parent: team, 'requests[].parent': [offPattern] }, create, names, 'BATCH', 'INVALID_ARGUMENT');
  }
  for (const parent of ['companies/A', 7, [true], ['companies', null]]) {
    for (const [method, field, item, grants] of [
      ['BatchGetWidgets', 'names[]', widget(team), [permit(team)]],
      ['BatchCreateWidgets', 'requests[].parent', team, create]
    ]) {
      const request = { parent, [field]: [item] };
      compare(method, request, grants, [], 'BATCH', 'INVALID_ARGUMENT');
      compare(method, request, [], [], 'POLICY', 'PERMISSION_DENIED');
      compare(method, { parent, [field]: [] }, grants, [], 'BATCH', 'PERMISSION_DENIED');
      compare(method, { parent, [field]: [['unbound']] }, grants, [], 'BATCH', 'PERMISSION_DENIED');
    }
  }
  for (const parent of [undefined, null, '', []]) {
    compare('BatchGetWidgets', getBatch(parent, [widget(team)]), [permit(team)], [], 'PROCEED', 'OK');
    compare('BatchCreateWidgets', { parent, 'requests[].parent': [team] }, create, [], 'PROCEED', 'OK');
  }
  // A malformed parent mapping can be reached without resolving any item alias.
  compare('BatchGetWidgets', getBatch(alias, [widget(team)]), [permit([])], [[alias, ['companies']]],
    'SERVER_FAULT', 'PERMISSION_DENIED');

  const reads = compare(review.name, getBatch(team, [widget(alias)]), [permit([])],
    [[widget(alias), ['companies']]], 'POLICY', 'PERMISSION_DENIED');
  assert.equal(reads.includes(widget(alias).join('/')), false, 'denied outer operation must precede item resolution');
}

function checkConditionalHoists({ FIXTURE, MODEL }, recorder, queue) {
  const rpc = FIXTURE.methods.find(m => m.name === 'BatchUpdateWidgets'), addr = 'requests[].widget.name';
  const parent = ['companies', 'a', 'teams', 't'], names = ['w', 'x'].map(id => [...parent, 'widgets', id]);
  const primary = { accessClass: 'UPDATE', operation: 'update', targetField: addr };
  const admin = { accessClass: 'ADMIN', operation: 'approve', targetField: addr };
  const make = (request, requirement) => ({ resources: FIXTURE.resources, methods: [{ ...rpc, request,
    authz: { requirements: [primary, requirement], partialSuccess: 'REQUEST_SELECTED' } }] });
  const permit = (keys, path = parent) => ({ keys, path, effect: 'permit' });
  const ordinary = permit(['widgets.update', 'widgets.create']), approval = permit(['widgets.approve']);
  for (const flag of ['allow_missing', 'force', 'options.verify']) {
    const extra = flag.includes('.') ? { options: { verify: true } } : { [flag]: true };
    const child = { ...rpc.request.requests, ...extra };
    const condition = 'requests[].' + flag, req = { ...admin, condition };
    const raw = make({ ...rpc.request, ...extra, requests: child }, req), model = recorder.interpret(raw);
    assert.deepEqual(Array.from(model.errors), []);
    const modern = c.descriptor(raw, model);
    queue.compare({ op: 'descriptor', descriptor: modern }, model.errors.length === 0);
    if (flag === 'allow_missing') {
      const missingCreate = structuredClone(modern), method = missingCreate.methods[0];
      method.requirements = method.requirements.filter(r => !r.parentOf);
      method.upsertBinding = null;
      queue.control({ op: 'descriptor', descriptor: missingCreate }, false);
      const contradictory = structuredClone(modern);
      contradictory.methods[0].requestFields.push(['allow_missing', 'message']);
      queue.control({ op: 'descriptor', descriptor: contradictory }, false);
    }
    const base = { parent, [addr]: names }, main = { ...base, [flag]: true };
    for (const [top, flags, indexes, mismatch] of [
      [true, undefined, [0,1], false], [true, [true,true], [0,1], false], [true, [false,true], [0,1], true],
      [false, [false,true], [1], true], [false, [false,false], [], false], [undefined, [true,false], [0], false],
      [undefined, undefined, [], false]
    ]) {
      const request = { ...base, ...(top === undefined ? {} : { [flag]: top }), ...(flags ? { [condition]: flags } : {}) };
      const got = recorder.requirementsFor(model, rpc.name, request).find(r => r.key === 'widgets.approve');
      assert.deepEqual(Array.from(got?.items || []), indexes);
      for (const [grants, denied] of [[[ordinary], indexes.length > 0], [[ordinary, approval], false]]) {
        const status = denied ? 'PERMISSION_DENIED' : mismatch ? 'INVALID_ARGUMENT' : 'OK';
        assert.equal(recorder.batchRequestStatus(grants, model, rpc.name, request), status);
        const result = recorder.authorizeRequest(grants, model, rpc.name, request);
        assert.equal(result.status ?? (result.decision === 'PROCEED' ? 'OK' : 'PERMISSION_DENIED'), status);
      }
      const partial = { ...request, return_partial_success: true };
      const handoff = recorder.authorizeRequest([ordinary], model, rpc.name, partial, { handlerResolvesResiduals: true });
      assert.equal(handoff.decision, 'PROCEED');
      assert.equal(handoff.residuals[0].keys.includes('widgets.approve'), !!indexes.length);
      const claims = [...ordinary.keys.map(key => ({ key, path: parent, holes: [], kind: 'ALLOW' })),
        { key: 'widgets.approve', path: parent, holes: [], kind: 'DENY' }];
      const frames = [{ seq: 1, contexts: [{ anchor: parent, claims }] }];
      const offered = recorder.offer(model, frames, model.domains, rpc.name, partial);
      assert.deepEqual(Array.from(offered.items), names.map((_, i) => indexes.includes(i) ? 'DENY' : 'ALLOW'));
      assert.equal(recorder.offer(model, frames, model.domains, rpc.name, request), indexes.length ? 'DENY' : 'ALLOW');
    }
    const legacy = structuredClone(modern), method = legacy.methods[0];
    delete method.requestFields;
    delete method.partialSource;
    method.partialSuccess = 'never';
    for (const r of [...method.requirements, method.upsertBinding].filter(Boolean)) delete r.hoisted;
    queue.control({ op: 'descriptor', descriptor: legacy }, false);
    const input = { descriptor: legacy, method: rpc.name, request: main, rules: [c.rule(ordinary)] };
    queue.control({ ...input, op: 'authorize' }, c.authorization({ decision: 'DENY', reason: 'POLICY', residuals: [] }));
    queue.control({ ...input, op: 'batchRequest' }, 'PERMISSION_DENIED');
    const stale = structuredClone(legacy);
    stale.methods[0].requirements.find(r => r.key === 'widgets.approve').hoisted = 'another_field';
    queue.control({ op: 'descriptor', descriptor: stale }, false);
    const rawChildOnly = make({ ...rpc.request, requests: child }, req), childOnly = recorder.interpret(rawChildOnly);
    assert.equal(childOnly.errors.length, 0);
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(rawChildOnly, childOnly) }, childOnly.errors.length === 0);
    assert.equal(recorder.batchRequestStatus([ordinary], childOnly, rpc.name, main), 'OK');
    const mismatch = flag.includes('.') ? { options: { verify: {} } } : { [flag]: { type: 'Widget' } };
    const bad = make({ ...raw.methods[0].request, ...mismatch }, req);
    const rejected = MODEL.interpret(bad);
    assert.ok(rejected.errors.length);
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(bad, model) }, rejected.errors.length === 0);
  }
  for (const field of ['update_mask', 'allow_missing']) {
    const child = { ...rpc.request.requests }, shape = { ...rpc.request, [field]: child[field], requests: child };
    const need = { ...admin, condition: 'return_partial_success' };
    const raw = make(shape, need), baseline = MODEL.interpret(raw);
    assert.equal(baseline.errors.length, 0);
    const missing = { ...child }; delete missing[field];
    const source = make({ ...shape, requests: missing }, need);
    const rejected = MODEL.interpret(source);
    assert.ok(rejected.errors.length);
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(source, baseline) }, rejected.errors.length === 0);
  }
  for (const named of [{ type: 'Team' }, { resource: 'Team' }, { childType: 'Widget' }, true]) {
    const req = { ...admin, targetField: 'requests[].review_team' }, child = { ...rpc.request.requests, review_team: { type: 'Team' } };
    const baseline = make({ ...rpc.request, review_team: { type: 'Team' }, requests: child }, req);
    const raw = make({ ...rpc.request, review_team: named, requests: child }, req);
    const result = MODEL.interpret(raw);
    assert.equal(result.errors.length === 0, named.type === 'Team');
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(raw, MODEL.interpret(baseline)) }, result.errors.length === 0);
  }
  const explicit = { ...admin, targetField: 'requests[].review_team', resourceType: 'Team' };
  const shared = shape => make({ ...rpc.request, review_team: shape,
    requests: { ...rpc.request.requests, review_team: shape } }, explicit);
  const baseline = MODEL.interpret(shared({ type: 'Team' }));
  for (const [kind, valid] of [[{ type: FIXTURE.resources.Team.type }, true], [{ type: 'Widget' }, false], [true, false]]) {
    const raw = shared(kind);
    const result = MODEL.interpret(raw);
    assert.equal(result.errors.length === 0, valid);
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(raw, baseline) }, result.errors.length === 0);
  }
  const unrelated = make({ ...rpc.request, extra: true, requests: { ...rpc.request.requests, extra: {} } }, admin);
  const reader = MODEL.interpret(unrelated);
  assert.equal(reader.errors.length, 0);
  queue.compare({ op: 'descriptor', descriptor: c.descriptor(unrelated, reader) }, reader.errors.length === 0);
}

function checkCustomItemContainers({ FIXTURE, MODEL }, recorder, queue) {
  const root = { serviceRoot:true, accessClass:'ADMIN', operation:'submit' };
  const parent = ['companies','a','teams','t'], other = ['companies','a','teams','other'];
  const widget = { type:'Widget' }, w = [...parent,'widgets','w'], foreign = [...other,'widgets','w'];
  const source = (fields, permissions, mode = 'REQUEST_SELECTED') => ({ resources:FIXTURE.resources, methods:[{
    name:'ReviewWidgets', returns:'Operation', request:fields, authz:{requirements:[root, ...permissions],partialSuccess:mode} }] });
  const path = (field, op, condition) => ({targetField:field, accessClass:'ADMIN', operation:op, condition});
  for (const group of ['requests','records','envelope.records']) {
    const repeated = group + '[].', name = repeated + 'name', flag = repeated + 'approve';
    const child = { name:widget, approve:true };
    const fields = { ...(group.includes('.') ? {envelope:{records:child}} : {[group]:child}), name:widget,
      approve:true, parent:{childType:'Widget'}, return_partial_success:true };
    const permissions = [path(name,'approve',flag)];
    const raw = source(fields, permissions), model = recorder.interpret(raw);
    assert.deepEqual([...model.errors], []);
    const wire = c.descriptor(raw, model);
    queue.compare({op:'descriptor', descriptor:wire}, model.errors.length === 0);
    for (const bad of [{name:{type:'Team'}},{approve:{}},{approve:{type:'Widget'}}]) {
      const changed = source({...fields,...bad}, permissions), invalid = MODEL.interpret(changed);
      assert.ok(invalid.errors.length);
      queue.compare({op:'descriptor',descriptor:c.descriptor(changed, model)}, invalid.errors.length === 0);
    }
    const forged = structuredClone(wire);
    forged.methods[0].batchLevel = [];
    forged.methods[0].requirements[1].hoisted = null;
    queue.control({op:'descriptor',descriptor:forged}, false);
    const run = {path:[],keys:['service.submit'],effect:'permit'};
    const approve = {path:parent,keys:['widgets.approve'],effect:'permit'};
    const req = {parent, [name]:[w], approve:true};
    const denied = recorder.authorizeRequest([run], model, 'ReviewWidgets', req);
    assert.equal(denied.reason, 'POLICY');
    queue.control({op:'authorize', descriptor:forged, method:'ReviewWidgets', request:req,
      rules:[c.rule(run)]}, c.authorization(denied));
    for (const [input, rules, expected] of [
      [req, [run,approve], 'OK'],
      [{...req, [name]:[null]}, [run, approve], 'INVALID_ARGUMENT'],
      [{...req, parent:undefined, [name]:[null]}, [run,approve], 'PERMISSION_DENIED'],
      [{...req, [name]:[foreign]}, [run,approve], 'PERMISSION_DENIED'],
      [{...req, [name]:[foreign]}, [run,{...approve,path:[]}], 'INVALID_ARGUMENT'],
      [{...req, [name]:[w,w]}, [run,approve], 'INVALID_ARGUMENT'],
      [{...req, [flag]:[false]}, [run], 'PERMISSION_DENIED'],
      [{...req, [flag]:[false]}, [run,approve], 'INVALID_ARGUMENT'],
      [{...req, [name]:[null], name:w}, [run,approve], 'OK']
    ]) {
      assert.equal(recorder.batchRequestStatus(rules, model, 'ReviewWidgets', input), expected);
      assert.equal(recorder.authorizeRequest(rules, model, 'ReviewWidgets', input).decision, expected === 'OK' ? 'PROCEED' : 'DENY');
    }
    const orphan = source({...fields,parent:undefined}, permissions);
    delete orphan.methods[0].request.parent;
    const noParent = recorder.interpret(orphan);
    assert.equal(recorder.batchRequestStatus([run,approve], noParent, 'ReviewWidgets', {...req,[name]:[null]}), 'PERMISSION_DENIED');
    for (const [shape,value] of [[true,true],[{childType:'Team'},['companies','a']]]) {
      const different = source({...fields,parent:shape},permissions), separate = recorder.interpret(different);
      assert.deepEqual([...separate.errors], []);
      queue.compare({op:'descriptor',descriptor:c.descriptor(different,separate)}, separate.errors.length === 0);
      assert.equal(recorder.batchRequestStatus([run,approve],separate,'ReviewWidgets',{...req,parent:value}), 'OK');
      assert.equal(recorder.batchRequestStatus([run,approve],separate,'ReviewWidgets',{...req,parent:value,[name]:[null]}), 'PERMISSION_DENIED');
    }
    const forgedPath = structuredClone(wire);
    forgedPath.methods[0].requirements[1].field = group + '[].absent';
    queue.control({op:'descriptor',descriptor:forgedPath}, false);
  }
  const fields = { records:{name:widget, approve:true}, attachments:{name:widget}, approve:true, return_partial_success:true };
  const two = [path('records[].name','review','records[].approve'),path('attachments[].name','inspect')];
  const atomic = source(fields,two,'NEVER'), model = recorder.interpret(atomic);
  assert.deepEqual([...model.errors], []);
  queue.compare({op:'descriptor',descriptor:c.descriptor(atomic,model)}, model.errors.length === 0);
  const rights = [{path:[],keys:['service.submit','widgets.inspect','widgets.review'],effect:'permit'}];
  const input = { 'records[].name':[w], 'attachments[].name':[foreign], approve:true, 'attachments[].approve':[false] };
  assert.equal(recorder.batchRequestStatus(rights, model, 'ReviewWidgets', input), 'OK');
  assert.equal(recorder.batchRequestStatus(rights, model, 'ReviewWidgets', {...input,'records[].approve':[false]}), 'INVALID_ARGUMENT');
  for (const mode of ['ALWAYS','REQUEST_SELECTED',undefined]) {
    const raw = source(fields, two, mode);
    if (mode === undefined) delete raw.methods[0].authz.partialSuccess;
    const result = MODEL.interpret(raw);
    assert.ok(result.errors.length);
    const wire = c.descriptor(raw,model);
    wire.methods[0].partialSuccess = mode === 'ALWAYS' ? 'always' : 'requestSelected';
    queue.compare({op:'descriptor',descriptor:wire}, result.errors.length === 0);
  }
  const resourceItems = source({records:{resource:'Widget'},name:widget}, [path('records[].name','review')], 'NEVER');
  const viaName = recorder.interpret(resourceItems);
  assert.deepEqual([...viaName.errors], []);
  queue.compare({op:'descriptor',descriptor:c.descriptor(resourceItems,viaName)}, viaName.errors.length === 0);
  assert.equal(recorder.batchRequestStatus(rights,viaName,'ReviewWidgets',{'records[].name':[null],name:w}), 'OK');
  for (const group of ['requests','records']) {
    const flag = group + '[].update_mask', name = group + '[].name';
    const raw = source({[group]:{name:widget,update_mask:true},update_mask:true},
      [path(name,'review',flag)],'NEVER');
    const custom = recorder.interpret(raw);
    assert.deepEqual([...custom.errors], []);
    queue.compare({op:'descriptor',descriptor:c.descriptor(raw,custom)}, custom.errors.length === 0);
    assert.equal(recorder.batchRequestStatus(rights,custom,'ReviewWidgets',{[name]:[w], [flag]:[false],update_mask:true}), 'INVALID_ARGUMENT');
    assert.equal(recorder.batchRequestStatus(rights,custom,'ReviewWidgets',{[name]:[w], [flag]:[true],update_mask:true}), 'OK');
  }
}

function checkImportedNames({ FIXTURE, MODEL }, queue) {
  const operations = 'google.longrunning.Operations/';
  const rpc = 'other.v2.Service/Lookup', sample = {method:rpc,authz:{handlerPolicy:'lookup'}};
  const importedServices = [['other.v2.Service',['Lookup']],['Service',['Run']],['_',['_']],
    ['_pkg.two_2._Service',['Read_2']],['__proto__',['constructor']],['constructor',['__proto__']],
    ['pkg.V2.s',['_rpc2']],['other.Service',['lookup','GetOperation']]];
  const withImport = (entry, required, repeat = false) => ({resources:FIXTURE.resources, required,
    importedServices,imported:[entry],services:repeat ? [{imported:[entry]}] : []});
  const valid = ['Service/Run','_/_','_pkg.two_2._Service/Read_2','__proto__/constructor','constructor/__proto__',
    'pkg.V2.s/_rpc2','other.Service/lookup','other.Service/GetOperation'];
  const invalid = ['', 'other.v2.Service', 'other.v2.Service/', '/Get', '/other.Service/Get',
    'other.Service//Get', 'other.Service/Get/extra', 'other..Service/Get', 'other.Service./Get', '.other.Service/Get',
    '9pkg.Service/Get', 'pkg.2Service/Get', 'pkg.Service/2Get', 'pkg.Service/Get.Name', 'pkg-Service/Get',
    'pkg.Service/Get-Q', 'päckage.Service/Get', 'pkg.Service/Répond', 'pkg.Service/Get\n',
    operations+'GetOperation/extra', operations+'getOperation', operations+'Unknown'];
  const operationsNames = FIXTURE.imported.map(m => m.method);
  assert.equal(operationsNames.length,5);
  const base = c.descriptor(withImport(sample,false),MODEL.interpret(withImport(sample,false)));
  for (const required of [false,true]) {
    for (const [name,accepted] of [...valid.map(n => [n,true]),...invalid.map(n => [n,false]),
      ...operationsNames.map(n => [n,true])]) {
      const entry = {...sample,method:name};
      // Supply all five known dispositions when required Operations coverage applies.
      const raw = withImport(entry,required,true);
      if (required && name.startsWith(operations)) raw.imported.push(...FIXTURE.imported.filter(m => m.method !== name));
      if (required && name.startsWith('other.Service/')) raw.imported.push(
        ...['other.Service/lookup','other.Service/GetOperation'].filter(m => m !== name).map(method => ({method,unimplemented:true})));
      const interpreted = MODEL.interpret(raw);
      assert.equal(!interpreted.errors.length,accepted,JSON.stringify(name));
      queue.compare({op:'descriptor',descriptor:c.descriptor(raw,interpreted)},!interpreted.errors.length);
      if (required) continue;
      const retained = structuredClone(base);
      retained.methods[0].name = name;
      retained.declaredMethods[0][0] = name;
      // Keep the compiled method present, so a rejected name cannot pass merely because JS removed its registration.
      queue.control({op:'descriptor',descriptor:retained},accepted);
      const noSource = structuredClone(retained);
      delete noSource.methods[0].partialSource;
      queue.control({op:'descriptor',descriptor:noSource},false);
      const historical = structuredClone(retained);
      historical.declaredMethods = [[name,false]];
      queue.control({op:'descriptor',descriptor:historical},false);
      const noRoster = structuredClone(retained);
      delete noRoster.declaredMethods;
      queue.control({op:'descriptor',descriptor:noRoster},false);
    }
  }
  for (const entry of [null,{}, {method:null},{method:9}]) {
    const raw = withImport(entry,false), interpreted = MODEL.interpret(raw);
    assert.ok(interpreted.errors.length);
    queue.compare({op:'descriptor',descriptor:c.descriptor(raw,interpreted)},!interpreted.errors.length);
  }
}

function checkImportedServices({ FIXTURE, MODEL }, queue) {
  const files = 'storage.v2.Files', jobs = 'work.v1.Jobs', ops = 'google.longrunning.Operations';
  const fileMethods = ['Read','Write','Remove'], jobMethods = ['Run','Stop'];
  const operationMethods = FIXTURE.imported.map(entry => entry.method.split('/')[1]);
  const catalog = [[files,fileMethods],[jobs,jobMethods]];
  const entry = (svc, rpc) => ({method:svc + '/' + rpc,unimplemented:true});
  const fileEntries = fileMethods.map(rpc => entry(files,rpc));
  const jobEntries = jobMethods.map(rpc => entry(jobs,rpc));
  const raw = options => ({resources:FIXTURE.resources,...options});
  const check = (source, expected, normalized) => {
    const live = MODEL.interpret(source);
    assert.equal(live.errors.length === 0,expected,JSON.stringify(source));
    const wire = c.descriptor(source,normalized || live);
    queue.compare({op:'descriptor',descriptor:wire},live.errors.length === 0);
    return wire;
  };
  const control = (wire, expected) => queue.control({op:'descriptor',descriptor:wire},expected);
  for (const required of [false,true]) {
    check(raw({required,importedServices:catalog}),true);
    check(raw({required,importedServices:catalog,imported:fileEntries}),true);
    check(raw({required,importedServices:catalog,imported:fileEntries.slice(1)}),!required);
    check(raw({required,importedServices:catalog,imported:[...fileEntries,...jobEntries.slice(1)]}),!required);
    check(raw({required,services:[
      {imported:[fileEntries[0],jobEntries[0]]},{importedServices:catalog,imported:[...fileEntries.slice(1),...jobEntries.slice(1)]}
    ]}),true);
    check(raw({importedServices:catalog,services:[{required},{imported:[fileEntries[0]]}]}),!required);
    check(raw({required,importedServices:catalog,imported:fileEntries.slice(1),
      methods:[{name:files+'/Read',authz:{handlerPolicy:'local'}}]}),!required);
    check(raw({required,importedServices:catalog,imported:[...fileEntries.slice(1),{method:files+'/Read'}]}),false);
    check(raw({required,importedServices:catalog,imported:fileEntries,
      services:[{importedServices:[[files,[...fileMethods].reverse()]]}]}),true);
    check(raw({required,importedServices:catalog,imported:fileEntries,
      services:[{importedServices:[[files,fileMethods.slice(1)]]}]}),false);
    for (const wrong of [entry(files,'read'),entry(files,'Run'),entry('google.protobuf.Type','InventedRpc'),
      entry('unknown.Service','Read')]) {
      check(raw({required,importedServices:catalog,imported:[wrong]}),false);
    }
    check(raw({required,imported:[fileEntries[0]]}),false);
  }
  for (const [published, accepted] of [
    [[[files,[]]],true], [[[files,fileMethods],[files,[...fileMethods].reverse()]],true],
    [[[ops,[...operationMethods].reverse()]],true], [[[ops,[]]],false],
    [[[ops,[...operationMethods,'Other']]],false], [[[files,['Read','Read']]],false],
    [[[files,fileMethods],[files,fileMethods.slice(1)]],false], [[['broken..Service',['One']]],false],
    [[[files,['Read/extra']]],false], [[[files,[null]]],false], [[[files]],false],
    [[null],false], [null,false], [{[files]:fileMethods},false]
  ]) check(raw({importedServices:published}),accepted);

  // The foreign method remains compiled when the source service disappears or changes its roster.
  const source = raw({importedServices:catalog,imported:fileEntries});
  const normal = MODEL.interpret(source);
  check({...source,importedServices:[[files,['Write','Remove']]]},false,normal);
  check({...source,importedServices:[[jobs,jobMethods]]},false,normal);
  const stale = {...source,required:true,importedServices:[[files,[...fileMethods,'Restore']]]};
  const incomplete = check(stale,false,normal);
  const valid = check({...source,required:true},true);
  const optional = check({...stale,required:false},true,normal);
  for (const requiredApi of [undefined,false]) {
    const knownRequired=structuredClone(incomplete);
    if (requiredApi === undefined) delete knownRequired.requiredApi; else knownRequired.requiredApi=requiredApi;
    control(knownRequired,false);
  }
  // A surviving import marker or raw declaration still identifies the foreign service.
  for (const [wire, accepted] of [[valid,true],[incomplete,false],[optional,true]]) {
    for (const kind of ['supplied','boolean','absent']) {
      const older = structuredClone(wire);
      if (kind === 'boolean') older.declaredMethods = older.methods.map(m => [m.name,false]);
      if (kind === 'absent') delete older.declaredMethods;
      control(structuredClone(older),kind === 'supplied' && accepted);
      for (const missing of [undefined,null,[]]) {
        const unknown = structuredClone(older);
        if (missing === undefined) delete unknown.importedServices; else unknown.importedServices=missing;
        control(unknown,false);
      }
      if (kind === 'supplied') {
        for (const m of older.methods) delete m.partialSource;
        control(older,false);
      }
    }
  }
  // Registration requires source evidence for optional imports too.
  const opaque = structuredClone(valid);
  delete opaque.importedServices;
  delete opaque.declaredMethods;
  delete opaque.requiredApi;
  for (const m of opaque.methods) delete m.partialSource;
  control(opaque,false);
  // A required local Operation must have its reflected roster.
  const lro = raw({required:true,methods:[{name:'StartExport',returns:'Operation',authz:{handlerPolicy:'start'}}]});
  for (const [listed,accepted] of [[[],false],[FIXTURE.imported.slice(1),false],[FIXTURE.imported,true]]) {
    const wire = structuredClone(check({...lro,imported:listed},accepted));
    delete wire.declaredMethods;
    delete wire.importedServices;
    control(wire,false);
    check(raw({required:true,importedServices:catalog,imported:[...listed,
      {method:files+'/Read',returns:'google.longrunning.Operation',authz:{handlerPolicy:'export'}},...fileEntries.slice(1)]}),accepted);
  }
}

function checkMethodDispositions({ FIXTURE, MODEL }, queue) {
  const request = {name:{type:'Widget'}}, name = 'GetWidget';
  const standard = {authz:{standard:{}}}, explicit = {authz:{requirements:[{operation:'inspect',accessClass:'READ'}]}};
  const policy = {authz:{handlerPolicy:'inspect'}}, other = {authz:{handlerPolicy:'change'}}, unimplemented = {unimplemented:true};
  const local = (options,required = false) => ({resources:FIXTURE.resources,required,methods:[{name,request,...options}]});
  const compare = (raw,valid,before) => {
    const result = MODEL.interpret(raw);
    assert.equal(!result.errors.length,valid,JSON.stringify(raw.methods || raw.services));
    queue.compare({op:'descriptor',descriptor:c.descriptor(raw,before || result)},!result.errors.length);
    return result;
  };
  const states = [{},standard,explicit,policy,other];
  for (const form of states) {
    const raw = local(form), valid = compare(raw,true);
    const sparse = c.descriptor(raw,valid);
    delete sparse.methods[0].partialSource;
    queue.control({op:'descriptor',descriptor:sparse},false);
    for (const old of states.filter(s => s !== form)) {
      const stale = c.descriptor(raw,MODEL.interpret(local(old)));
      queue.control({op:'descriptor',descriptor:stale},false);
      const sparse = structuredClone(stale);
      delete sparse.methods[0].partialSource;
      queue.control({op:'descriptor',descriptor:sparse},false);
    }
    if (form !== states[0]) compare(local(form,true),true);
  }
  const optional = MODEL.interpret(local({}));
  const returning = local({...standard,returns:'Widget'});
  const retained = c.descriptor(returning,MODEL.interpret(returning));
  delete retained.methods[0].partialSource;
  delete retained.methods[0].requestFields;
  queue.control({op:'descriptor',descriptor:structuredClone(retained)},false);
  retained.methods[0].requirements[0].key = 'widgets.inspect';
  retained.methods[0].requirements[0].info.operation = 'inspect';
  queue.control({op:'descriptor',descriptor:retained},false);
  const custom = local({request:{name:{}},authz:{requirements:[
    {operation:'inspect',accessClass:'READ',resourceType:'Widget',targetField:'name'}]}});
  const reflected = c.descriptor(custom,MODEL.interpret(custom));
  delete reflected.methods[0].partialSource;
  delete reflected.methods[0].requestShapeKnown;
  queue.control({op:'descriptor',descriptor:structuredClone(reflected)},false);
  reflected.methods[0].requestShapeKnown = false;
  queue.control({op:'descriptor',descriptor:reflected},false);
  for (const invalid of [local({},true),local({authz:{}}),local({authz:{handlerPolicy:''}}),local({authz:{handlerPolicy:17}}),
    local({authz:{standard:{},handlerPolicy:''}}),local({authz:{standard:{},handlerPolicy:'inspect'}}),local({authz:{...explicit.authz,standard:{}}}),
    local({...unimplemented,...policy}),local({...unimplemented,noSideEffects:true})]) compare(invalid,false,optional);
  const fullName = 'other.v1.Service/' + name;
  const catalog = {importedServices:[['other.v1.Service',[name]]]};
  for (const required of [false,true]) {
    compare(local({unimplemented:false},required),!required);
    const imported = {...catalog,resources:FIXTURE.resources,required,imported:[{method:fullName,unimplemented:true}]};
    const registered = compare(imported,true);
    for (const method of [name,fullName]) for (const flags of [unimplemented,{...unimplemented,imported:true},
      {...unimplemented,...policy},{authz:{...policy.authz,unimplemented:true}}]) {
      const raw = {...catalog,...local({name:method,...flags},required)};
      const result = compare(raw,false);
      assert.ok(result.errors.includes(method + ': only an imported_methods entry may set unimplemented'));
    }
    const bad = {...catalog,...local({name:fullName,unimplemented:true},required)};
    const stale = c.descriptor(bad,registered);
    queue.control({op:'descriptor',descriptor:stale},false);
    for (const source of ['method','roster']) {
      const ir = structuredClone(stale);
      if (source === 'method') delete ir.declaredMethods;
      else delete ir.methods[0].partialSource;
      queue.control({op:'descriptor',descriptor:ir},false);
    }
    compare({...imported,imported:[{method:fullName,authz:{...policy.authz,unimplemented:true}}]},false,registered);
    // The full source declaration is required even when a method is unimplemented.
    const legacy = structuredClone(c.descriptor(imported,registered));
    legacy.declaredMethods = [[fullName,false]];
    delete legacy.methods[0].partialSource;
    queue.control({op:'descriptor',descriptor:structuredClone(legacy)},false);
    for (const symbol of [name,fullName + '/extra','other.v1.Service/Invented']) {
      const ir = structuredClone(legacy);
      ir.methods[0].name = symbol;
      ir.declaredMethods[0][0] = symbol;
      queue.control({op:'descriptor',descriptor:ir},false);
    }
    legacy.importedServices[0][1].push('Other');
    queue.control({op:'descriptor',descriptor:legacy},false);
  }
  const entry = {method:'other.v1.Service/Inspect',request,...policy};
  const group = (services,required = false) => ({resources:FIXTURE.resources,services,required,
    importedServices:[['other.v1.Service',['Inspect','Unused']]]});
  const another = {method:'other.v1.Service/Unused',unimplemented:true};
  const emit = (list,required = false) => ({imported:list,required});
  const same = group([emit([entry]),emit([{...entry,noSideEffects:false},another],true)]);
  const baseline = compare(same,true);
  for (const changed of [{...entry,...other},{...entry,request:{name:{type:'Team'}}},{...entry,clientStreaming:true}])
    compare(group([emit([entry]),emit([changed,another])]),false,baseline);
  compare(group([emit([entry,entry,another])]),false,baseline);
  for (const add of [{},standard,{authz:{}},{...unimplemented,...explicit}])
    compare(group([emit([{method:entry.method,request,...add},another])]),false,baseline);
  compare(group([{required:true,methods:[]},{required:false,methods:local({}).methods}]),true);
  compare(group([{required:false,methods:[]},{required:true,methods:local({}).methods}]),false,optional);
  const ops = FIXTURE.imported, subset = ops.filter(m => !m.method.endsWith('/CancelOperation'));
  const async = {methods:[{name:'ExportInventory',returns:'Operation',...policy}]};
  compare(group([async,{required:true},emit(ops)]),true);
  compare(group([async,{required:true},emit(subset)]),false);
  compare(group([async,{required:true}]),false);
  compare(group([async,emit(subset)]),true);
  compare(group([emit([{method:'google.longrunning.Operations/Unknown',unimplemented:true}])]),false);
  for (const form of states) {
    const raw = local(form), old = c.descriptor(raw, MODEL.interpret(raw));
    old.declaredMethods = [[name, form === explicit]];
    delete old.requiredApi;
    queue.control({op:'descriptor',descriptor:old},false);
    if (form === policy) for (const handlerPolicy of ['',null]) {
      const anonymous = structuredClone(old);
      delete anonymous.methods[0].partialSource;
      anonymous.methods[0].handlerPolicy = handlerPolicy;
      queue.control({op:'descriptor',descriptor:anonymous},false);
    }
  }
}

function checkPermissionFields({ FIXTURE, MODEL }, queue) {
  const widget = {type:'Widget'}, team = {type:'Team'}, parent = {childType:'Widget'}, body = {resource:'Widget'};
  const read = {operation:'inspect', accessClass:'READ'}, root = {...read,serviceRoot:true};
  const source = (request, requirements, name = 'InspectWidget') => ({resources:FIXTURE.resources,
    methods:[{name,request,authz:{requirements}}]});
  const valid = (raw, field, kind, type) => {
    const result = MODEL.interpret(raw);
    assert.deepEqual([...result.errors], []);
    const r = result.methods[raw.methods[0].name].requirements[0];
    assert.deepEqual([r.field,r.kind,r.type],[field,kind,type === 'service' ? result.apiService + '/service' : FIXTURE.resources[type].type]);
    queue.compare({op:'descriptor',descriptor:c.descriptor(raw,result)},result.errors.length === 0);
    return result;
  };
  const explicit = {...read,targetField:'name',resourceType:'Widget'};
  const baseline = valid(source({name:widget},[explicit]), 'name','resource','Widget');
  for (const request of [{},{renamed:widget},{name:team},{name:true},{name:[widget]},
    {name:{nested:widget}},{name:body},{name:null}]) {
    const raw = source(request,[explicit]), result = MODEL.interpret(raw);
    assert.ok(result.errors.length);
    queue.compare({op:'descriptor',descriptor:c.descriptor(raw,baseline)},result.errors.length === 0);
    queue.compare({op:'descriptor',descriptor:c.descriptor(raw,result)},result.errors.length === 0);
  }
  for (const [fields,spec,field,kind,type] of [
    [{name:widget,parent},read,'name','resource','Widget'],
    [{parent,body},read,'parent','parent','Widget'],
    [{first:body,other:{resource:'Team'}},read,'first.name','resource','Widget'],
    [{body}, {...read,targetField:'body.name'},'body.name','resource','Widget'],
    [{nested:{body}}, {...read,targetField:'nested.body.name'},'nested.body.name','resource','Widget'],
    [{plain:{}},{...read,targetField:'plain',resourceType:'Widget'},'plain','resource','Widget'],
    [{parent},{...read,targetField:'parent'},'parent','parent','Widget'],
    [{name:widget},{...read,targetField:'name',parentTarget:true},'name','parent','Widget'],
    [{},root,null,'root','service'], [{},{...root,resourceType:'Team'},null,'root','Team'],
    [{name:widget,records:{name:widget}},{...read,targetField:'records[].name'},'records[].name','resource','Widget'],
    [{records:body},{...read,targetField:'records[].name'},'records[].name','resource','Widget']
  ]) valid(source(fields,[spec]),field,kind,type);
  const compareStale = (before,after) => {
    const original = MODEL.interpret(before), current = MODEL.interpret(after);
    assert.deepEqual([...original.errors], []);
    assert.deepEqual([...current.errors], []);
    queue.compare({op:'descriptor',descriptor:c.descriptor(after,current)},current.errors.length === 0);
    queue.control({op:'descriptor',descriptor:c.descriptor(after,original)}, false);
  };
  compareStale(source({name:widget},[read]),source({name:team},[read]));
  compareStale(source({widget:body},[read]),source({widget:body,name:team},[read]));
  const fields = {name:widget,related:team,second:team,body};
  const related = {...read,operation:'inspectTeam',targetField:'related'};
  const permissions = [explicit,related];
  for (const rpc of ['InspectWidget','GetWidget']) {
    const original = source(fields,permissions,rpc);
    compareStale(original,{...original,methods:[]});
    compareStale({...original,methods:[]},original);
    for (const reqs of [[explicit],[explicit,related,root],[related,explicit],[explicit,{...related,targetField:'second'}],
      [explicit,{...related,parentTarget:true}], [root,related], [explicit,{...related,explicitGrantOnly:true}]])
      compareStale(original,source(fields,reqs,rpc));
    const legacy = c.descriptor(original,MODEL.interpret(original));
    delete legacy.methods[0].partialSource.requirementSources;
    queue.control({op:'descriptor',descriptor:structuredClone(legacy)},true);
    const altered = structuredClone(legacy);
    altered.methods[0].requestFields = altered.methods[0].requestFields.filter(([path]) => path !== 'related');
    queue.control({op:'descriptor',descriptor:altered},false);
    delete legacy.methods[0].requestFields;
    queue.control({op:'descriptor',descriptor:legacy},false);
  }
  const untyped = source({name:{}},[read]), rejected = MODEL.interpret(untyped);
  assert.ok(rejected.errors.length);
  queue.compare({op:'descriptor',descriptor:c.descriptor(untyped,baseline)},rejected.errors.length === 0);
  const parentOnly = MODEL.interpret(source({parent},[read]));
  for (const name of [null,false,0,'']) {
    const raw = source({name,parent},[read]), result = MODEL.interpret(raw);
    assert.ok(result.errors.length);
    queue.compare({op:'descriptor',descriptor:c.descriptor(raw,parentOnly)},result.errors.length === 0);
  }
  const imported = {method:'other.v1.Others/Inspect',authz:{requirements:[root]}};
  const registry = {resources:FIXTURE.resources,methods:[{name:'OptionalLocal'}],importedServices:[['other.v1.Others',['Inspect','Unused']]],
    services:[{imported:[imported]},{imported:[imported,{method:'other.v1.Others/Unused',unimplemented:true}]}]};
  const result = MODEL.interpret(registry), encoded = c.descriptor(registry,result);
  assert.deepEqual([...result.errors],[]);
  assert.equal(result.undeclared.has('OptionalLocal'),true);
  assert.equal(result.methods['other.v1.Others/Unused'].disposition,'UNIMPLEMENTED');
  assert.equal(encoded.declaredMethods.length,3);
  queue.compare({op:'descriptor',descriptor:encoded},result.errors.length === 0);
  const historical = structuredClone(encoded);
  delete historical.declaredMethods;
  for (const method of historical.methods) delete method.partialSource;
  queue.control({op:'descriptor',descriptor:historical},false);
}

function checkReflectedAddresses({ FIXTURE, MODEL }, recorder, queue) {
  const root = {operation:'editInventory',accessClass:'ADMIN',serviceRoot:true};
  const name = {type:'Widget'}, parent = {childType:'Widget'}, body = {resource:'Widget'};
  const source = (rpc,request,more = {},resources = FIXTURE.resources) => ({resources,
    methods:[{name:rpc,request,authz:{requirements:[root]},...more}]});
  const register = raw => {
    const model = recorder.interpret(raw,{fieldGuards:true});
    assert.deepEqual(Array.from(model.errors), []);
    queue.compare({op:'descriptor',descriptor:c.descriptor(raw,model)},model.errors.length === 0);
    return model;
  };
  const crossed = (raw,stale) => queue.control({op:'descriptor',descriptor:c.descriptor(raw,stale)},false);
  const top = {...FIXTURE.resources, Widget:{...FIXTURE.resources.Widget,patterns:['widgets/{widget}']}};
  for (const [rpc,fields,want,more,resources] of [
    ['GetWidget',{name},'name'], ['ListWidgets',{parent},'parent'], ['CreateWidget',{parent,body},'parent'],
    ['UpdateWidget',{payload:body,allow_missing:true,update_mask:{}},'payload.name'], ['DeleteWidget',{name},'name'],
    ['BatchGetWidgets',{names:name},'names[]'], ['BatchGetWidgets',{requests:{name}},'requests[].name'],
    ['BatchDeleteWidgets',{names:name},'names[]'], ['BatchDeleteWidgets',{requests:{name}},'requests[].name'],
    ['BatchCreateWidgets',{requests:{parent,body}},'requests[].parent'],
    ['BatchUpdateWidgets',{requests:{payload:body,allow_missing:true}},'requests[].payload.name'],
    ['ListWidgets',{},null,{resourceType:'Widget'},top], ['CreateWidget',{payload:body},null,{},top],
    ['BatchCreateWidgets',{requests:{payload:body}},null,{},top]
  ]) {
    const raw = source(rpc,fields,more,resources);
    const before = source(rpc,{other:name},{},resources), off = register(before), current = register(raw);
    assert.equal(off.methods[rpc].resourceTarget,null);
    assert.equal(current.methods[rpc].resourceTarget.field,want);
    crossed(raw,off);
    crossed(before,current);
    const streamed = source(rpc,fields,{...more,serverStreaming:true},resources), stream = register(streamed);
    assert.equal(stream.methods[rpc].resourceTarget,null);
    crossed(raw,stream);
    crossed(streamed,current);
  }
  for (const [rpc,fields,options] of [
    ['GetWidget',{name},{returns:'Unrelated'}], ['ListWidgets',{parent},{returns:'Unrelated'}],
    ['BatchGetWidgets',{names:name},{returns:'Unrelated'}], ['BatchGetWidgets',{requests:{resource:'Widget'}},{}],
    ['CreateWidget',{body,parent:{childType:'Team'}},{}], ['ListWidgets',{},{resourceType:'Widget'}]
  ]) {
    const raw = source(rpc,fields,options), model = register(raw);
    assert.equal(model.methods[rpc].resourceTarget,null);
  }
  for (const [rpc,fields,options] of [
    ['UpdateWidget',{payload:body,other:body},{}], ['BatchUpdateWidgets',{requests:{payload:body,other:body}},{}],
    ['BatchDeleteWidgets',{names:name,requests:{name}},{}], ['BatchGetWidgets',{names:name,requests:{name}},{}]
  ]) {
    const raw = source(rpc,fields,options), live = MODEL.interpret(raw,{fieldGuards:true});
    assert.ok(live.errors.length);
    const noAddress = register(source(rpc,{}));
    queue.compare({op:'descriptor',descriptor:c.descriptor(raw,noAddress)},live.errors.length === 0);
  }
  const qualified = 'usage.v1.WidgetService/GetWidget';
  const imported = {Team:FIXTURE.resources.Team,'.assets.v2.Widget':{...FIXTURE.resources.Widget,
    type:'assets.example/Widget',external:true}};
  const rawImport = source(qualified,{name:{type:'.assets.v2.Widget'}},{returns:'.assets.v2.Widget'},imported);
  const importedModel = register(rawImport);
  assert.equal(importedModel.methods[qualified].resourceTarget.type,'assets.example/Widget');
  const otherPackage = source(qualified,rawImport.methods[0].request,{returns:'usage.v1.Widget'},imported);
  const custom = register(otherPackage);
  assert.equal(custom.methods[qualified].resourceTarget,null);
  crossed(rawImport,custom);
  crossed(otherPackage,importedModel);

  const rpc = 'UpdateWidget', raw = source(rpc,{payload:body,allow_missing:true,update_mask:{}});
  const old = source(rpc,{}), update = register(raw), unchanged = register(old);
  const target = ['companies','A','teams','T','widgets','W'];
  const req = {'payload.name':target,allow_missing:true,update:{mask:['owner'],populated:['owner']}};
  const allow = keys => [{effect:'permit',keys,path:[]}];
  const keys = ['service.editInventory','widgets.setOwner'];
  assert.deepEqual(Array.from(recorder.requirementsFor(update,rpc,req),r => r.key),keys);
  for (const granted of [keys, [keys[0], 'widgets.create'], [keys[0]]]) {
    const rules = allow(granted);
    assert.equal(recorder.authorizeRequest(rules,update,rpc,req).decision,
      granted.includes('widgets.setOwner') ? 'PROCEED' : 'DENY');
    assert.equal(recorder.authorizeRequest(rules,unchanged,rpc,req).decision,'PROCEED');
  }
  const staleWriter = c.descriptor(old,unchanged);
  staleWriter.methods[0].writes = 'create';
  queue.control({op:'descriptor',descriptor:staleWriter},false);
  // A type used only for an unrelated request field is outside the checked resource catalog.
  const foreign = {Team:FIXTURE.resources.Team, Broken:{external:true,type:'assets.example/Broken',plural:17,
    patterns:[[12,'*']],vars:[25]}};
  register(source('InspectInventory',{object:{type:'Broken'}},{},foreign));
  const legacy = c.descriptor(raw,unchanged);
  delete legacy.methods[0].requestFields;
  delete legacy.methods[0].partialSource;
  queue.control({op:'descriptor',descriptor:legacy},false);
}

function checkStreamingDefaults({FIXTURE,MODEL}, queue) {
  const root = {requirements:[{operation:'editInventory',accessClass:'ADMIN',serviceRoot:true}]};
  const standard = {standard:{}}, handler = {handlerPolicy:'streamHandler'};
  const body = {resource:'Widget'}, name = {type:'Widget'};
  const writes = {payload:body,allow_missing:true,update_mask:{}};
  const make = (rpc,request,authz,flags={}) => ({resources:FIXTURE.resources,methods:[{name:rpc,request,authz,...flags}]});
  const compare = (wire,answer) => queue.compare({op:'descriptor',descriptor:wire},answer);
  const control = (wire,answer) => queue.control({op:'descriptor',descriptor:wire},answer);
  const interpret = raw => MODEL.interpret(raw,{fieldGuards:true});
  for (const [rpc,fields] of [['GetWidget',{name}],['UpdateWidget',writes],
    ['BatchGetWidgets',{names:name}],['BatchUpdateWidgets',{requests:writes}]]) {
    for (const form of [root,standard,handler]) {
      const unary = interpret(make(rpc,fields,form));
      const unaddressed = interpret(make(rpc,{},root));
      assert.deepEqual(Array.from(unary.errors),[]);
      for (const server of [true,false,undefined,null]) for (const client of [true,false,undefined,null]) {
        const flags = {serverStreaming:server,clientStreaming:client};
        const raw = make(rpc,fields,form,flags), live = interpret(raw);
        const valid = !live.errors.length, stream = !!(server || client);
        assert.equal(valid,form === handler || (form === standard ? !stream : !client));
        const encode = normalized => c.descriptor(raw,normalized);
        compare(encode(valid ? live : unary),valid);
        if (form !== handler && valid) control(encode(stream ? unary : unaddressed),false);
      }
    }
    const raw = make(rpc,fields,root), valid = interpret(raw), obsolete = interpret(make(rpc,{},root));
    for (const retained of [undefined,null,{}, {standard:null,failedRequests:null},
      {explicitRequirements:true}, {standard:false,clientStreaming:false}]) {
      for (const normalized of [valid, obsolete]) {
        const wire = c.descriptor(raw,normalized), method=wire.methods[0];
        if (retained === undefined) delete method.partialSource; else method.partialSource=retained;
        control(wire,false);
      }
    }
    if (rpc.includes('Update')) {
      for (const obligation of ['widgets.create','widgets.setOwner']) {
        const wire=c.descriptor(raw,valid), method=wire.methods[0];
        delete method.partialSource;
        if (obligation === 'widgets.create') {
          method.requirements=method.requirements.filter(r => !r.parentOf);
          method.upsertBinding=null;
        } else method.fieldGuards=[];
        control(wire,false);
      }
      const wire=c.descriptor(make(rpc,{},root),obsolete);
      delete wire.methods[0].partialSource;
      wire.methods[0].writes='create';
      control(wire,false);
    }
  }
  // A partial signature cannot establish the declared method form.
  const rpc='GetWidget', fields={name}, raw=make(rpc,fields,standard,{returns:'Widget'});
  for (const retained of [undefined,null,{}, {standard:null}, {standard:true}]) {
    const wire=c.descriptor(raw,interpret(raw)), method=wire.methods[0];
    if (retained === undefined) delete method.partialSource; else method.partialSource=retained;
    control(wire,false);
    const altered=structuredClone(wire), req=altered.methods[0].requirements[0];
    req.key='widgets.inspect'; req.info.operation='inspect';
    control(altered,false);
  }
  const custom=make(rpc,fields,root,{returns:'Unrelated'}), genuine=c.descriptor(custom,interpret(custom));
  genuine.methods[0].partialSource={response:'Unrelated'};
  control(genuine,false);
  const stale=c.descriptor(custom,interpret(make(rpc,fields,root)));
  stale.methods[0].partialSource={response:'Unrelated'};
  control(stale,false);
  for (const flags of [{serverStreaming:true},{clientStreaming:true},{serverStreaming:true,clientStreaming:true}]) {
    const declaration=make(rpc,fields,handler,flags);
    const wire=c.descriptor(declaration,interpret(declaration));
    wire.methods[0].partialSource={...flags,handlerPolicy:'streamHandler'};
    control(wire,false);
  }
  const streamed=make('UpdateWidget',writes,root,{serverStreaming:true});
  const legacyStream=c.descriptor(streamed,interpret(streamed));
  const method=legacyStream.methods[0];
  delete method.requestFields;
  delete legacyStream.guardSources;
  method.partialSource={serverStreaming:true};
  control(legacyStream,false);
  const staleWrite=structuredClone(legacyStream);
  staleWrite.methods[0].writes='update';
  control(staleWrite,false);
}

function checkExplicitWriters(api, recorder, queue) {
  const { FIXTURE, MODEL } = api;
  const parent = ['companies', 'a', 'teams', 't'], target = [...parent, 'widgets', 'w'];
  const grant = (key, path) => ({ keys: [key], path, effect: 'permit' });
  const invoke = grant('service.approve', []);
  for (const name of ['CreateWidget', 'UpdateWidget', 'BatchCreateWidgets', 'BatchUpdateWidgets']) {
    const rpc = FIXTURE.methods.find(m => m.name === name), batch = name.startsWith('Batch'), update = name.includes('Update');
    const root = { resourceType: 'service', serviceRoot: true, accessClass: 'ADMIN', operation: 'approve' };
    const source = { resources: FIXTURE.resources, methods: [{ ...rpc, authz: { requirements: [root] } }] };
    const model = recorder.interpret(source, { fieldGuards: true });
    assert.deepEqual([...model.errors], []);
    const registered = c.descriptor(source, model);
    queue.compare({ op: 'descriptor', descriptor: registered }, model.errors.length === 0);
    const unregistered = MODEL.interpret(source, { rejectUnhandledFieldGuards: true });
    assert.ok(unregistered.errors.length);
    const core = MODEL.interpret(source);
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(source, core) }, core.errors.length === 0);
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(source, core, { rejectUnhandledFieldGuards: true }) }, unregistered.errors.length === 0);
    const removed = c.descriptor(source, model);
    removed.methods[0].fieldGuards = [];
    queue.control({ op: 'descriptor', descriptor: removed }, false);
    const wrong = c.descriptor(source, model);
    wrong.methods[0].writerBinding.field = 'elsewhere';
    queue.control({ op: 'descriptor', descriptor: wrong }, false);
    const staleFields = c.descriptor(source, model);
    const scalar = staleFields.methods[0].guardFields.find(f => f.path === 'owner');
    staleFields.methods[0].guardFields.unshift({ ...scalar, message: true });
    queue.control({ op: 'descriptor', descriptor: staleFields }, false);
    if (update) {
      const extra = c.descriptor(source, model);
      assert.ok(extra.methods[0].upsertBinding);
      assert.ok(extra.methods[0].requirements.every(r => !r.parentOf));
      extra.methods[0].requirements.push(extra.methods[0].upsertBinding);
      queue.control({ op: 'descriptor', descriptor: extra }, false);
    }
    const key = 'widgets.setOwner', prefix = batch ? 'requests[].' : '';
    let request = { parent };
    const set = (field, value) => { request[prefix + field] = batch ? [value] : value; };
    if (update) {
      set('widget.name', target);
      set('update', { mask: ['owner'], populated: ['owner'] });
    } else {
      set('parent', parent);
      set('populated', ['owner']);
      if (batch) set('id', 'w');
    }
    const check = (rules, expect) => {
      assert.equal(recorder.authorizeRequest(rules, model, name, request).decision, expect);
      if (batch) assert.equal(recorder.batchRequestStatus(rules, model, name, request), expect === 'PROCEED' ? 'OK' : 'PERMISSION_DENIED');
    };
    assert.deepEqual(Array.from(recorder.requirementsFor(model, name, request).find(r => r.key === key).targets, p => Array.from(p)),
      [update ? target : parent]);
    check([invoke], 'DENY');
    check([invoke, grant(key, update ? target : parent)], 'PROCEED');
    if (update) {
      request = { ...request };
      set('allow_missing', true);
      set('update', { mask: ['display_name'], populated: ['owner'] });
      const active = recorder.requirementsFor(model, name, request);
      assert.deepEqual(Array.from(active.find(r => r.key === key).targets, p => Array.from(p)), [target, parent]);
      const create = grant('widgets.create', parent);
      check([invoke, grant(key, parent)], 'PROCEED');
      check([invoke, create, grant(key, target)], 'DENY');
      check([invoke, create, grant(key, parent)], 'PROCEED');
    }
  }
  const update = FIXTURE.methods.find(m => m.name === 'UpdateWidget'), other = [...parent, 'widgets', 'other'];
  const source = { resources: FIXTURE.resources, methods: [{ ...update, request: { ...update.request, destination: { type: 'Widget' } },
    authz: { requirements: [{ resourceType: 'Widget', targetField: 'destination', operation: 'update', accessClass: 'UPDATE' }] } }] };
  const model = recorder.interpret(source, { fieldGuards: true });
  assert.deepEqual([...model.errors], []);
  const req = { 'widget.name': target, destination: other, update: { mask: ['owner'], populated: ['owner'] } };
  const change = grant('widgets.update', other);
  assert.equal(recorder.authorizeRequest([change, grant('widgets.setOwner', other)], model, update.name, req).decision, 'DENY');
  assert.equal(recorder.authorizeRequest([change, grant('widgets.setOwner', target)], model, update.name, req).decision, 'PROCEED');
}

function checkGuardDefinitions(api, queue) {
  const { MODEL, FIXTURE } = api, widget = FIXTURE.resources.Widget;
  const get = FIXTURE.methods.find(m => m.name === 'GetWidget'), create = FIXTURE.methods.find(m => m.name === 'CreateWidget');
  const field = (operation = 'setOwner', accessClass = 'ADMIN', explicitGrantOnly = false) =>
    ({ guard: { operation, accessClass, explicitGrantOnly } });
  const build = (fields, methods) => ({ resources: { Widget: { ...widget, fields } }, methods });
  for (const [owner, reviewer, valid] of [
    [field('get'), null, false], [field(), null, true], [field(), field(), true],
    [field(), field('setOwner', 'UPDATE'), false], [field(), field('setOwner', 'ADMIN', true), false],
    [field('bad-name'), null, false], [field('readOwner', 'READ'), null, false]
  ]) {
    const source = build({ owner, ...(reviewer ? { reviewer } : {}) }, [get]);
    const enabled = MODEL.interpret(source, { fieldGuards: true }), core = MODEL.interpret(source);
    assert.equal(enabled.errors.length === 0, valid);
    assert.deepEqual([...core.errors], []);
    const d = c.descriptor(source, enabled);
    queue.compare({ op: 'descriptor', descriptor: d }, enabled.errors.length === 0);
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(source, core, { rejectUnhandledFieldGuards: true }) },
      MODEL.interpret(source, { rejectUnhandledFieldGuards: true }).errors.length === 0);
    if (valid) {
      const grant = { scope: [], selectors: [{ type: widget.type, op: 'setOwner' }] };
      assert.equal(Object.hasOwn(enabled.keys, 'widgets.setOwner'), false);
      const granted = MODEL.keysFor(grant, enabled.keys);
      assert.deepEqual([...granted], []);
      queue.compare({ op: 'expand', descriptor: d, grant: c.grant(grant) }, granted);
      if (!reviewer) for (const change of ['key', 'resourceType']) {
        const stale = c.descriptor(source, enabled), guard = stale.guardSources[0].guards[0];
        if (change === 'key') guard.key = 'widgets.unrelated';
        else guard.info.resourceType = 'other.example/Widget';
        queue.control({ op: 'descriptor', descriptor: stale }, false);
      }
    }
  }
  const examine = { name: 'ExamineOwner', request: get.request, authz: {
    requirements: [{ accessClass: 'ADMIN', operation: 'setOwner', targetField: 'name' }] } };
  for (const explicit of [true, false]) {
    const source = build({ owner: field('setOwner', 'ADMIN', explicit) }, [examine]);
    const enabled = MODEL.interpret(source, { fieldGuards: true });
    assert.equal(enabled.errors.length === 0, !explicit);
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(source, enabled) }, enabled.errors.length === 0);
  }
  for (const rootClass of ['READ', 'ADMIN']) for (const guardClass of ['ADMIN', 'UPDATE']) {
    const fields = { owner: field('setOwner', guardClass) };
    const writer = { ...create, authz: { requirements: [{ serviceRoot: true, accessClass: rootClass, operation: 'submit' }] } };
    const source = build(fields, [writer]), base = MODEL.interpret(source, { fieldGuards: true });
    for (const noSideEffects of [false, true]) {
      const declared = build(fields, [{ ...writer, noSideEffects }]);
      const model = MODEL.interpret(declared, { fieldGuards: true });
      const valid = !noSideEffects || guardClass === 'ADMIN';
      const expectedEffect = noSideEffects ? 'READ_ONLY' : 'MUTATING';
      assert.equal(model.errors.length === 0, valid);
      if (valid) assert.equal(model.methods[writer.name].effect, expectedEffect);
      // Keep the writer in the native input even when the JS loader rejects it.
      for (const effect of ['READ_ONLY', 'MUTATING', 'DESTRUCTIVE']) {
        const ir = c.descriptor(declared, base);
        ir.methods[0].effect = c.enumName(effect);
        const input = { op: 'descriptor', descriptor: ir };
        if (effect === expectedEffect) queue.compare(input, model.errors.length === 0);
        else queue.control(input, false);
      }
    }
  }
}

function checkGuardCapability({ MODEL }, queue) {
  const owner = { guard:{ operation:'setOwner', accessClass:'ADMIN' }, decl:'Content.owner' };
  const resources = {
    Widget:{type:'widgets.example/Widget',plural:'widgets',patterns:['widgets/{widget}']},
    // Both messages have the same resource basename. The body selects the served type.
    Replica:{type:'replicas.example/Widget',plural:'replicas',patterns:['replicas/{replica}'],fields:{}},
    Archive:{type:'widgets.example/Archive',plural:'archives',patterns:['archives/{archive}'],fields:{owner}}
  };
  const forms = {
    standard:{authz:{standard:{}}},
    permissions:{authz:{requirements:[{serviceRoot:true,operation:'writeInventory',accessClass:'ADMIN'}]}},
    handler:{authz:{handlerPolicy:'checkWriter'}},
    optional:{},
    unimplemented:{unimplemented:true}
  };
  const body = {payload:{resource:'Widget'}};
  const registered = (raw, model, opts) => ({op:'descriptor',descriptor:c.descriptor(raw,model,opts)});
  const strict = {rejectUnhandledFieldGuards:true};
  const service = (registry, method, declaration) => {
    const base = {apiService:'widgets.example',resources:registry};
    if (declaration !== forms.unimplemented) return {...base,methods:[{...method,...declaration}]};
    const {name,...signature} = method;
    return {...base,importedServices:[['guard.v1.Writers',['UpdateWidget','CreateWidget','BatchUpdateWidgets',
      'BatchCreateWidgets','GetWidget','UpdateInventory']]],imported:[{method:'guard.v1.Writers/' + name,...signature,...declaration}]};
  };
  for (const [fields, writable] of [
    [{owner},true], [{snapshot:{message:true,outputOnly:true},'snapshot.owner':owner},false]
  ]) {
    const catalog = {...resources,Widget:{...resources.Widget,fields}};
    for (const [rpc, request, writesWidget, flags = {}] of [
      ['UpdateWidget',body,true], ['CreateWidget',body,true],
      ['BatchUpdateWidgets',{requests:body},true], ['BatchCreateWidgets',{requests:body},true],
      ['GetWidget',{name:{type:'Widget'}},false], ['UpdateWidget',{payload:{resource:'Replica'}},false],
      ['UpdateInventory',body,false], ['UpdateWidget',{payload:{}},false],
      ['UpdateWidget',body,false,{serverStreaming:true}], ['UpdateWidget',body,false,{clientStreaming:true}]
    ]) {
      for (const [form, declaration] of Object.entries(forms)) {
        if (form === 'standard' && !writesWidget && rpc !== 'GetWidget' && request.payload?.resource !== 'Replica') continue;
        if (form === 'permissions' && flags.clientStreaming) continue;
        const raw = service(catalog,{name:rpc,request,...flags},declaration);
        const core = MODEL.interpret(raw);
        assert.deepEqual(Array.from(core.errors),[]);
        for (const opts of [{},strict,{fieldGuards:true},{fieldGuards:true,...strict}]) {
          const live = MODEL.interpret(raw,opts);
          const valid = !(opts.rejectUnhandledFieldGuards && !opts.fieldGuards && form !== 'unimplemented' && writesWidget && writable);
          assert.equal(live.errors.length === 0,valid,JSON.stringify({rpc,form,opts,errors:live.errors}));
          queue.compare(registered(raw,valid ? live : core,opts),valid);
        }
        if (writesWidget && writable && (form === 'standard' || form === 'permissions')) {
          queue.control(registered(raw,core,{fieldGuards:true}),false);
          queue.control(registered(raw,MODEL.interpret(raw,{fieldGuards:true}),{fieldGuards:false}),false);
        }
        if (form === 'handler' || form === 'optional') {
          for (const opts of [{},strict]) for (const [loseFields,loseSource] of [[true,false],[false,true],[true,true]]) {
            const input=registered(raw,core,opts), method=input.descriptor.methods[0];
            if (loseFields) delete method.requestFields;
            if (loseSource) delete method.partialSource;
            queue.control(input,false);
          }
        }
      }
    }
  }
  // Checking a served writer's capability requires a usable physical address.
  for (const declaration of [forms.handler,forms.optional,forms.unimplemented]) {
    for (const method of [
      {name:'UpdateWidget',request:{one:{resource:'Widget'},two:{resource:'Replica'}}},
      {name:'BatchUpdateWidgets',request:{requests:body,parent:{childType:'Archive'}}}
    ]) {
      const raw=service(resources,method,declaration);
      const core=MODEL.interpret(raw), live=MODEL.interpret(raw,strict);
      assert.deepEqual(Array.from(core.errors),[]);
      assert.equal(live.errors.length === 0,declaration === forms.unimplemented);
      queue.compare(registered(raw,core,strict),live.errors.length === 0);
    }
  }
  for (const declaration of [forms.permissions,forms.handler,forms.optional,forms.unimplemented]) {
    const raw=service({...resources,Widget:{...resources.Widget,fields:{owner}}},{name:'UpdateWidget',request:body},declaration);
    const core=MODEL.interpret(raw), input=registered(raw,core,strict);
    const expected=MODEL.interpret(raw,strict).errors.length === 0;
    for (const field of ['fieldGuardsEnabled','rejectUnhandledFieldGuards']) {
      const sparse=structuredClone(input);
      delete sparse.descriptor[field];
      queue.control(sparse,expected);
    }
    const missing=structuredClone(input);
    delete missing.descriptor.guardSources;
    queue.control(missing,false);
    // A loader can retain annotations as source metadata while running in plain Core.
    const plain=structuredClone(input);
    plain.descriptor.rejectUnhandledFieldGuards=false;
    queue.control(plain,core.errors.length === 0);
  }
}

function checkGuardPlacement({ MODEL, FIXTURE }, queue) {
  const widget = FIXTURE.resources.Widget, get = FIXTURE.methods.find(m => m.name === 'GetWidget');
  const create = FIXTURE.methods.find(m => m.name === 'CreateWidget');
  const guard = { operation: 'setOwner', accessClass: 'ADMIN' };
  const live = { guard, decl: 'Content.owner' };
  const archived = (field = live) => ({ history: { message: true, outputOnly: true }, 'history.owner': field });
  const other = (fields, external = false) => ({
    type: 'other.example/Review', ...(external ? { external } : { plural: 'reviews' }), patterns: ['reviews/{review}'], fields
  });
  const probe = (fields, review, valid, methods = [get]) => {
    const raw = { apiService: 'widgets.example', resources: { Widget: { ...widget, fields }, ...(review ? { Review: review } : {}) }, methods };
    const opts = { fieldGuards: true }, model = MODEL.interpret(raw, opts);
    assert.equal(model.errors.length === 0, valid, JSON.stringify({ fields, review, errors: [...model.errors] }));
    const ir = c.descriptor(raw, model, opts);
    queue.compare({ op: 'descriptor', descriptor: ir }, model.errors.length === 0);
    return { raw, model, ir };
  };
  const dead = archived();
  probe({ 'config.owner': live }, null, false);
  probe({ config: { message: true }, 'config.inner.owner': live }, null, false);
  probe({ config: { message: true }, 'config.owner': live }, null, true);
  probe({ items: { message: true, repeatedOrMap: true }, 'items.*.owner': live }, null, true);
  const { raw: deadRaw } = probe(dead, null, false);
  probe({ ...dead, unrelated: { guard } }, null, false);
  probe(dead, other(archived()), false);
  const reused = probe({ ...dead, owner: live }, null, true, [get, create]);
  assert.deepEqual(Array.from(reused.ir.methods.find(m => m.name === create.name).fieldGuards, g => g.field), ['owner']);
  probe(dead, other({ owner: live }), true);
  const sharedFallback = probe({ owner: { guard } }, other(archived({ guard, decl: 'Widget.owner' })), true);
  const imported = probe(dead, other({ owner: live }, true), true);
  assert.equal(imported.ir.resources.some(r => r.resourceType === 'other.example/Review'), false);
  assert.deepEqual(Object.keys(imported.model.keys), ['widgets.get']);

  for (const property of ['outputOnly', 'identifier', 'recursive']) {
    const forbidden = { ...live, [property]: true };
    probe({ owner: forbidden }, null, false);
    probe({ owner: forbidden }, other({ owner: live }), false);
    probe({ owner: live }, other({ owner: forbidden }, true), false);
  }
  probe(archived({ ...live, recursive: true }), other({ owner: live }), false);
  for (const name of ['condition', 'targetField', 'serviceRoot', 'resourceType', 'wildcardVariables']) {
    probe(archived({ ...live, guard: { ...guard, [name]: null } }), other({ owner: live }), false);
  }
  for (const malformed of [{}, { ...guard, accessClass: 'admin' }, { ...guard, accessClass: null }, { ...guard, operation: 4 }]) {
    for (const methods of [[get], [create]]) {
      const { raw } = probe({ owner: { guard: malformed } }, null, false, methods);
      const opts = { rejectUnhandledFieldGuards: true }, strict = MODEL.interpret(raw, opts);
      const valid = methods[0] === get;
      assert.equal(strict.errors.length === 0, valid);
      queue.compare({ op: 'descriptor', descriptor: c.descriptor(raw, MODEL.interpret(raw), opts) }, strict.errors.length === 0);
    }
  }
  // Core and a registration-only reader ignore annotations. Writers still need an enforcer on writable fields.
  for (const raw of [deadRaw, reused.raw]) for (const opts of [{}, { rejectUnhandledFieldGuards: true }]) {
    const model = MODEL.interpret(raw, opts), valid = !opts.rejectUnhandledFieldGuards || raw === deadRaw;
    assert.equal(model.errors.length === 0, valid);
    const core = MODEL.interpret(raw, {});
    queue.compare({ op: 'descriptor', descriptor: c.descriptor(raw, core, opts) }, model.errors.length === 0);
  }
  // Placement metadata identifies the declaring resource and its import status.
  for (const [fields, valid] of [[{ owner: { guard } }, true], [dead, false]]) {
    const ir = structuredClone(probe(fields, null, valid).ir);
    for (const source of ir.guardSources) {
      delete source.external;
      source.guards = source.guards.map(({ field, key, info }) => ({ field, key, info }));
    }
    queue.control({ op: 'descriptor', descriptor: ir }, false);
  }
  const stale = structuredClone(sharedFallback.ir);
  stale.guardSources.find(s => s.resourceType === 'other.example/Review').guards[0].declaration = 'unrelated.owner';
  queue.control({ op: 'descriptor', descriptor: stale }, false);
  for (const corrupt of [
    (ir, src) => ir.guardSources.push(src),
    (_, src) => src.fields.push({ ...src.fields[0], outputOnly: true }),
    (_, src) => src.guards.push({ ...src.guards[0], identifier: true }),
    (_, src) => { src.resourceType = 'Review'; src.guards[0].info.resourceType = 'Review'; },
    (_, src) => { src.guards[0].info.resourceType = widget.type; }
  ]) {
    const ir = structuredClone(imported.ir);
    corrupt(ir, ir.guardSources.find(s => s.external));
    queue.control({ op: 'descriptor', descriptor: ir }, false);
  }
}

function checkWriterInputs(api, recorder) {
  const fields = api.FIXTURE.resources.Widget.fields;
  const known = recorder.effectiveMask({ mask: [] }, fields), unknown = recorder.effectiveMask([], fields);
  assert.deepEqual([...known], []);
  assert.ok(unknown.includes('owner'));
  const model = recorder.interpret(api.FIXTURE, { fieldGuards: true });
  const parent = ['companies', 'a', 'teams', 't'], target = [...parent, 'widgets', 'w'];
  for (const batch of [false, true]) for (const update of [false, true]) {
    const method = (batch ? 'Batch' : '') + (update ? 'Update' : 'Create') + (batch ? 'Widgets' : 'Widget');
    const item = update ? 'widget.name' : 'parent', value = update ? target : parent;
    const base = { parent, ...(batch ? { ['requests[].' + item]: [value] } : { [item]: value }) };
    const metadata = update ? 'update' : 'populated', empty = update ? { mask: [] } : [], owner = update ? { mask: ['owner'] } : ['owner'];
    const singular = v => ({ [metadata]: v }), repeated = v => ({ ['requests[].' + metadata]: [v] });
    const actual = batch ? repeated : singular, stray = batch ? singular : repeated;
    const primary = { effect: 'permit', path: [], keys: [update ? 'widgets.update' : 'widgets.create'] };
    const guard = { effect: 'permit', path: [], keys: ['widgets.setOwner'] };
    const probe = (write, guarded) => {
      const req = { ...base, ...write };
      const bindings = recorder.requirementsFor(model, method, req);
      assert.equal(bindings.some(r => r.key === 'widgets.setOwner'), guarded);
      assert.equal(recorder.authorizeRequest([primary], model, method, req).decision, guarded ? 'DENY' : 'PROCEED');
      assert.equal(recorder.authorizeRequest([guard, primary], model, method, req).decision, 'PROCEED');
    };
    probe({ ...actual(empty), ...stray(owner) }, false);
    probe({ ...actual(owner), ...stray(empty) }, true);
    probe(stray(empty), true);
    if (update) probe(actual([]), true);
  }
}

function checkRowReads(api, recorder, I, target) {
  const permit = {path: target, keys: ['widgets.get'], effect: 'permit'};
  const risky = {...permit, effect: 'forbid', mayError: true};
  const fail = api.fixtureCallback(() => { throw Error('row unavailable'); }, {rowReads:[]});
  const get = {name: target}, batch = {'names[]': [target]};
  const auth = (rules, method, request, opts) => {
    const out = recorder.authorizeRequest(rules, I, method, request, opts);
    return out.reason || out.decision;
  };
  for (const authority of ['failClosed', 'skipErrors']) {
    for (const attrsOf of [api.fixtureValue({}), api.fixtureValue(null), fail]) {
      const failed = attrsOf === fail, opts = {authority, attrsOf};
      for (const [rules, faults, passes, actionable] of [
        [[], undefined, false, false], [[permit,{...permit,effect:'forbid'}], undefined, false, false],
        [[permit], undefined, true, false], [[{...permit, pred:'owner'}], undefined, false, true],
        [[permit, risky], undefined, false, false], [[permit, risky], api.fixtureValue(false), false, false],
        [[permit, risky], api.fixtureValue(true), authority === 'skipErrors', false]
      ]) {
        const options = {...opts, faults};
        const expected = failed && actionable ? 'SERVER_FAULT' : passes ? 'PROCEED' : 'POLICY';
        assert.equal(auth(rules, 'GetWidget', get, options), expected);
        assert.equal(auth(rules, 'BatchGetWidgets', batch, options), expected);
        for (const [method, request] of [['GetWidget',get], ['BatchGetWidgets',batch]])
          assert.equal(recorder.decideRequest(rules, I, method, request, attrsOf, options),
            expected === 'PROCEED' ? 'ALLOW' : 'DENY');
        assert.equal(recorder.batchRequestStatus(rules, I, 'BatchGetWidgets', batch, options),
          expected === 'PROCEED' ? 'OK' : 'PERMISSION_DENIED');
      }
    }
  }
  // Each batch entry point uses the same whole-parent proof before reading item rows.
  const parent = target.slice(0, -2), parentGrant = {...permit, path: parent};
  assert.equal(recorder.batchRequestStatus([parentGrant], I, 'BatchGetWidgets', {...batch,parent},
    {attrsOf:fail}), 'OK');
  assert.equal(auth([parentGrant], 'BatchGetWidgets', {...batch,parent}, {attrsOf:fail}), 'PROCEED');

  const update = api.FIXTURE.methods.find(m => m.name === 'BatchUpdateWidgets');
  const guarded = recorder.interpret({...api.FIXTURE, methods:[{...update, authz:{partialSuccess:'REQUEST_SELECTED',
    requirements:[{operation:'dispatch',accessClass:'ADMIN',serviceRoot:true},
      {operation:'modify',accessClass:'UPDATE',targetField:'requests[].widget.name'}]}}]});
  assert.deepEqual(Array.from(guarded.errors), []);
  const outer = {...permit,path:[],keys:['service.dispatch'],pred:'owner'}, item = {...permit,keys:['widgets.modify'],pred:'owner'};
  const req = {'requests[].widget.name':[target]};
  for (const partial of [true,false]) {
    for (const [outerRead, outerGrant, expected] of [
      [true,false,'POLICY'], [false,true,'SERVER_FAULT'], [true,true,partial ? 'PROCEED' : 'SERVER_FAULT']
    ]) {
      const visited = [];
      const opts = {handlerResolvesResiduals:true, attrsOf:api.fixtureCallback(path => {
        visited.push(Array.from(path));
        if (!path.length && outerRead) return {owner:'alice'};
        return fail();
      }, {rowReads:outerRead ? [[[],true]] : [],factsByPath:outerRead ? [[[],true]] : []})};
      const rules = outerGrant ? [outer,item] : [item];
      const result = recorder.authorizeRequest(rules, guarded, update.name, {...req,return_partial_success:partial}, opts);
      assert.equal(result.reason || result.decision, expected);
      assert.deepEqual(visited, !outerGrant ? [] : !partial && outerRead ? [[],target] : [[]]);
      if (expected === 'PROCEED') assert.deepEqual(Array.from(result.residuals, r => r.kind), ['PARTIAL_BATCH']);
    }
  }
}

function checkBatchParentRows(api, recorder, model, target) {
  const parent = target.slice(0,-2), otherParent = [...parent.slice(0,-1),'C'];
  const other = [...otherParent,'widgets','w2'], sibling = [...parent,'widgets','w3'];
  const get = 'BatchGetWidgets', update = 'BatchUpdateWidgets';
  const grant = (path,...keys) => ({path,keys,effect:'permit'});
  const read = grant(parent,'widgets.get'), put = grant(parent,'widgets.update');
  const guard = grant(parent,'widgets.setOwner'), reads = names => ({parent,'names[]':names});
  const check = (I, rpc, request, rules, options, expected, visits, row = api.fixtureCallback(() => {throw Error('item timeout');},{rowReads:[]})) => {
    for (const [i, entry] of ['authorizeRequest','batchRequestStatus','decideRequest'].entries()) {
      const paths = [];
      const attrsOf = api.fixtureCallback(p => { paths.push(Array.from(p)); return row(p); }, c.callbackInputs(row,'attrsOf'));
      const opts = {...options,attrsOf};
      const result = entry === 'decideRequest' ? recorder.decideRequest(rules,I,rpc,request,attrsOf,opts)
        : recorder[entry](rules,I,rpc,request,opts);
      const observed = entry === 'authorizeRequest' ? result.status || result.reason || result.residuals[0]?.kind || result.decision : result;
      assert.equal(observed,expected[i],entry + ' ' + rpc);
      assert.deepEqual(paths,visits[i],entry + ' ' + rpc);
    }
  };
  const ok=['PROCEED','OK','ALLOW'], fault=['SERVER_FAULT','PERMISSION_DENIED','DENY'];
  const denied=['POLICY','PERMISSION_DENIED','DENY'], invalid=['INVALID_ARGUMENT','INVALID_ARGUMENT','DENY'];
  const none=[[],[],[]], at = p => [[p],[p],[p]];
  for (const authority of ['failClosed','skipErrors']) {
    const opts={authority};
    check(model,get,reads([target,sibling]),[read],opts,ok,none);
    check(model,get,reads([target,sibling]),[read],{...opts,ceiling:[]},denied,none);
    check(model,get,reads([target]),[read],{...opts,nonprojecting:api.fixtureValue(true)},ok,none);
    check(model,get,reads([target]),[{...read,pred:'owner'}],opts,fault,at(target));
    check(model,get,reads([target]),[{...read,pred:'owner'}],opts,ok,at(target),api.fixtureValue({owner:'alice'}));
    check(model,get,reads([target]),[read,{...read,path:sibling,effect:'forbid'}],opts,ok,none);
    check(model,get,reads([target,other]),[read,{...grant(other,'widgets.get'),pred:'owner'}],opts,fault,at(other));
    check(model,get,reads([target,other]),[read,grant(other,'widgets.get')],opts,invalid,none);
    check(model,get,reads([target,other]),[read],opts,denied,none);
    check(model,get,reads([target,target]),[read],opts,invalid,none);
    check(model,get,reads([target,['bad']]),[read],opts,invalid,none);
    check(model,get,reads([target,['bad']]),[{...grant(target,'widgets.get'),pred:'owner'}],opts,fault,at(target));
    const alias = [...parent.slice(0,-1),'current'];
    const resolvePrefix = Object.assign(p => p.join('/') === alias.join('/') ? parent : undefined,{aliases:[[alias,parent]]});
    check(model,get,{parent:alias,'names[]':[[...alias,'widgets','w1']]},[read],{...opts,resolvePrefix},ok,none);
    const writes={parent,'requests[].widget.name':[target],'requests[].update':[{mask:['owner']}]};
    check(model,update,writes,[put,guard],opts,ok,none);
    check(model,update,writes,[put],opts,denied,none);
    check(model,update,writes,[put,{...guard,pred:'owner'}],opts,fault,at(target));
    const partial={...writes,return_partial_success:true}, handler={...opts,handlerResolvesResiduals:true};
    check(model,update,partial,[put,guard],handler,['PARTIAL_BATCH','OK','ALLOW'],none);
    check(model,update,partial,[put,{...guard,pred:'owner'}],handler,['PARTIAL_BATCH','PERMISSION_DENIED','DENY'],
      [[],[target],[target]]);
  }
  const declaration=api.FIXTURE.methods.find(m => m.name === get);
  const explicit=recorder.interpret({...api.FIXTURE,methods:[{...declaration,authz:{requirements:[
    {operation:'dispatch',accessClass:'ADMIN',serviceRoot:true},
    {operation:'inspect',accessClass:'READ',targetField:'names[]'}]}}]});
  const dispatch={...grant([],'service.dispatch'),pred:'owner'}, inspect=grant(parent,'widgets.inspect');
  check(explicit,get,reads([target]),[dispatch,inspect],{},ok,at([]),api.fixtureCallback(path => {
    if (path.length) throw Error('unexpected item read');
    return {owner:'alice'};
  },{rowReads:[[[],true]],factsByPath:[[[],true]]}));
  check(explicit,get,reads([target,target]),[dispatch,inspect],{},invalid,at([]),api.fixtureValue({owner:'alice'}));
}

function checkEnforcementVisibility(M, recorder, I, descriptor, queue) {
  const company=['companies','A'], team=[...company,'teams','B'], wildcard=[...company,'teams','-'];
  const widget=[...team,'widgets','1'], otherCompany=['companies','Z'];
  const list='widgets.list', get='widgets.get';
  const permit=(key,path,extra={}) => ({path,keys:[key],effect:'permit',...extra});
  const same=(a,b) => a.length === b.length && a.every((part,i) => part === b[i]);
  const modes = [
    [undefined,true], [null,false], [false,false], [true,false],
    [()=>undefined,false], [()=>null,false], [()=>false,false],
    [()=>{throw Error('visibility unavailable');},false], [()=>'visible',false], [()=>true,true]
  ];
  const forSite=(site,adapter,confirmed) => typeof adapter === 'function' ?
    Object.assign(p => same(site,p) ? adapter() : true, {fixtureInputs:{invisible:confirmed ? [] : [site]}}) : adapter;
  const region=(rules,key,path,opts,expected,subtree=false) => {
    const visibility=c.callbackInputs(opts.canName,'canName');
    const allowed=M.regionAllowed(rules,key,path,I.keys[key].patterns,{...opts,subtree});
    assert.equal(allowed,expected);
    queue.compare({op:'regionAllowed',descriptor,rules:rules.map(c.rule),key,path,subtree,...visibility},allowed);
  };
  for (const [adapter,confirmed] of modes) {
    for (const [site,extra,obstructs] of [
      [team,{},true], [[],{pred:'owner'},true], [company,{mayError:true},true],
      [[],{},false], [otherCompany,{pred:'owner'},false]
    ]) {
      const opts=adapter === undefined ? {} : {canName:forSite(site,adapter,confirmed)};
      const rules=[permit(list,[]),permit(list,site,extra)], req={parent:wildcard};
      const expected=!obstructs || confirmed;
      region(rules,list,wildcard,opts,expected);
      const auth=recorder.authorizeRequest(rules,I,'ListWidgets',req,opts);
      assert.equal(auth.decision,expected ? 'PROCEED' : 'DENY');
      assert.equal(recorder.decideRequest(rules,I,'ListWidgets',req,undefined,opts),expected ? 'ALLOW' : 'DENY');
    }
    const opts=adapter === undefined ? {} : {canName:forSite(widget,adapter,confirmed)};
    const rules=[permit(get,[]),permit(get,widget)];
    region(rules,get,team,opts,confirmed,true);
    for (const rowWorks of [true,false]) {
      let reads=0;
      const attrsOf=Object.assign(()=>{ reads++; if (!rowWorks) throw Error('row unavailable'); return {}; },
        {fixtureInputs:rowWorks ? {} : {rowReads:[]}});
      const options={...opts,attrsOf}, req={parent:team,'names[]':[widget]};
      // An unconditional concrete permit still settles the item if the region proof fails.
      const auth=recorder.authorizeRequest(rules,I,'BatchGetWidgets',req,options);
      assert.equal(auth.decision,'PROCEED');
      assert.equal(recorder.batchRequestStatus(rules,I,'BatchGetWidgets',req,options),'OK');
      assert.equal(recorder.decideRequest(rules,I,'BatchGetWidgets',req,attrsOf,options),'ALLOW');
      assert.equal(reads,0);
    }
  }
  // The original native invisible-path list remains a complete visibility declaration.
  const policy=[permit(list,[]),permit(list,team)], req={parent:wildcard};
  const regionInput={op:'regionAllowed',descriptor,rules:policy.map(c.rule),key:list,path:wildcard};
  queue.control({...regionInput,nameVisibility:[[otherCompany,true]]},false);
  queue.control({...regionInput,invisible:[team],nameVisibility:[[team,true]]},false);
  for (const invisible of [[],[team],[otherCompany]]) {
    const opts={canName:p=>!invisible.some(site=>same(site,p))};
    const wire={descriptor,rules:policy.map(c.rule),invisible};
    const allowed=M.regionAllowed(policy,list,wildcard,I.keys[list].patterns,opts);
    assert.equal(allowed,!invisible.includes(team));
    queue.compare({...wire,op:'regionAllowed',key:list,path:wildcard},allowed);
    queue.compare({...wire,op:'authorize',method:'ListWidgets',request:req},c.authorization(M.authorizeRequest(policy,I,'ListWidgets',req,opts)));
    queue.compare({...wire,op:'decideRequest',method:'ListWidgets',request:req},M.decideRequest(policy,I,'ListWidgets',req,undefined,opts));
    const rules=[permit(get,[]),permit(get,widget)], batch={parent:team,'names[]':[widget]};
    const deniedSites=invisible.includes(team) ? [widget] : invisible, row=()=>{throw Error('row unavailable');};
    const batchOpts={attrsOf:row,canName:p=>!deniedSites.some(site=>same(site,p))};
    const status=M.batchRequestStatus(rules,I,'BatchGetWidgets',batch,batchOpts);
    assert.equal(status,'OK');
    queue.compare({op:'batchRequest',descriptor,method:'BatchGetWidgets',request:batch,rules:rules.map(c.rule),
      invisible:deniedSites,knownFacts:true,rowReads:[]},status);
  }
}

function checkRegionCeilings(M, I, descriptor, queue) {
  const read = 'widgets.get', write = 'widgets.update', list = 'widgets.list';
  const rules = [{ path: [], keys: [read, write, list], effect: 'permit' }];
  const company = ['companies','A'], parent = [...company,'teams','-'];
  const type = I.keys[read].type;
  for (const id of ['w1', 'bad/id', '..', '.', '%2F', 'escaped\\id', '']) for (const subtree of [false, true]) {
    const path = [...parent, 'widgets', id];
    const result = M.regionAllowed(rules, read, path, I.keys[read].patterns, {subtree});
    assert.equal(result, id === 'w1');
    queue.compare({op:'regionAllowed', descriptor, key:read, path, subtree, rules:rules.map(c.rule)}, result);
  }
  const cases = [
    [{}, true, true], [{ceiling:null}, true, true], [{readOnlyCredential:true}, true, false],
    [{readOnlyCredential:false}, true, true], [{readOnlyCredential:null}, true, true],
    [{readOnlyCredential:0}, false, false], [{readOnlyCredential:'true'}, false, false],
    [{ceiling:['UPDATE'],readOnlyCredential:'ignored'}, false, true],
    [{ceiling:[]}, false, false], [{ceiling:['READ']}, true, false],
    [{ceiling:[{type,cls:'READ'}]}, true, false], [{ceiling:[{type,cls:'UPDATE'}]}, false, true],
    [{ceiling:[{type:'*',cls:'UPDATE'}]}, false, true],
    [{ceiling:[{type:'other.example/Widget',cls:'READ'},'UPDATE']}, false, true],
    [{ceiling:'READ'}, false, false], [{ceiling:false}, false, false], [{ceiling:0}, false, false],
    [{ceiling:''}, false, false], [{ceiling:[null,'READ']}, false, false],
    [{ceiling:[{type:'Widget',cls:'UPDATE'},'READ']}, false, false],
    [{ceiling:[{type,cls:'unknown'},'READ']}, false, false]
  ];
  for (const budget of [0, 1, -1, 'invalid']) for (const effect of ['permit', 'forbid']) {
    const grants = [...rules, {path:[...company, 'teams', 'B'], keys:[list], effect}];
    const outcome = M.regionAllowed(grants, list, parent, I.keys[list].patterns, {budget});
    assert.equal(outcome, effect === 'permit');
    queue.compare({op:'regionAllowed', descriptor, key:list, path:parent, rules:grants.map(c.rule), budget}, outcome);
  }
  const request = {name:[...company,'teams','B','widgets','w1']};
  for (const [credential, reads] of cases) {
    const method = 'GetWidget';
    const available = M.methodAvailable(I, method, credential).available;
    assert.equal(available, reads);
    queue.compare({op:'methodAvailable', descriptor, method, credential}, available);
    const offered = M.offer(I, [], I.domains, method, request, credential);
    assert.equal(offered, reads ? 'UNLOADED' : 'UNAVAILABLE');
    queue.compare({op:'methodOffer', descriptor, method, request, now:1, state:c.initialState(I.apiService),
      credential}, normalizedVerdict(offered));
  }
  for (const authority of ['failClosed','skipErrors']) for (const [credential, reads, writes] of cases) {
    const wire = { descriptor, rules:rules.map(c.rule), authority, credential };
    const options = { ...credential, authority };
    for (const [key, path, expected] of [[read,company,reads],[write,company,writes],[list,parent,reads]]) {
      for (const patterns of [I.keys[key].patterns, I.domains[key]]) {
        const value = M.regionAllowed(rules, key, path, patterns, options);
        assert.equal(value, expected);
        queue.compare({ ...wire, op:'regionAllowed', key, path }, value);
      }
    }
    const req = {parent};
    const outcome = M.authorizeRequest(rules, I, 'ListWidgets', req, options);
    assert.equal(outcome.decision, reads ? 'PROCEED' : 'DENY');
    queue.compare({ ...wire, op:'authorize', method:'ListWidgets', request:req }, c.authorization(outcome));
    const batch = { parent:[...company,'teams','B'], 'names[]':[] };
    const status = M.batchRequestStatus(rules, I, 'BatchGetWidgets', batch, options);
    assert.equal(status, reads ? 'INVALID_ARGUMENT' : 'PERMISSION_DENIED');
    queue.compare({ ...wire, op:'batchRequest', method:'BatchGetWidgets', request:batch }, status);
  }
}

function checkRequestEvidence(api, queue) {
  const {MODEL:m,FIXTURE:fixture} = api;
  const scope = ['companies','A'], parent = [...scope,'teams','B'], name = [...parent,'widgets','w'];
  const wild = [...scope,'teams','-'], target = [...wild,'widgets','w'];
  const grant = (key, extra) => ({path:[],effect:'permit',keys:[key],...extra});
  const model = m.interpret(fixture), descriptor = c.descriptor(fixture,model);
  const search = 'widgets.search', read = 'widgets.get';
  const open = grant(search), closed = grant(search,{effect:'forbid'});
  const cases = [
    [[],{},true], [[open],{},false], [[closed,open],{},true],
    [[{...closed,hidden:true},open],{},false], [[closed,open],{invisible:[[]]},false],
    [[],{privateKeys:[search]},false], [[closed,open],{privateKeys:[search]},true],
    [[open],{ceiling:[]},true], [[open],{ceiling:['READ']},false],
    [[open],{ceiling:[{type:'other.example/Widget',cls:'READ'}]},true],
    [[grant(search,{path:['companies','elsewhere']})],{},true]
  ];
  for (const [rules,env,refused] of cases) {
    const opts = {ceiling:env.ceiling,nonprojecting:k => !!env.privateKeys?.includes(k),
      canName:p => !env.invisible?.some(hidden => m.sameName(hidden,p))};
    const wire = {descriptor,key:search,rules:rules.map(c.rule),credential:{ceiling:env.ceiling},
      nonprojectingKeys:env.privateKeys,invisible:env.invisible};
    const answer = m.searchRefusedUpFront(rules,search,wild,opts,model.keys[search]);
    assert.equal(answer,refused);
    queue.compare({...wire,op:'searchRefusedUpFront',parent:wild},answer);
    const request = {parent:wild};
    const decision = m.decideRequest(rules,model,'SearchWidgets',request,undefined,opts);
    assert.equal(decision,refused ? 'DENY' : 'RESOLVE_FIRST');
    queue.compare({...wire,op:'decideRequest',method:'SearchWidgets',request,knownFacts:true},decision);
    const malformed = [...wild,'..'];
    queue.compare({...wire,op:'searchRefusedUpFront',parent:malformed},
      m.searchRefusedUpFront(rules,search,malformed,opts,model.keys[search]));
  }
  for (const authority of ['failClosed','skipErrors']) for (const faults of [undefined,false]) {
    const rules = [grant(read,{mayError:true})], request = {name};
    const opts = {authority,attrsOf:() => {throw Error('unavailable');}};
    if (faults !== undefined) opts.faults = () => faults;
    const actual = m.authorizeRequest(rules,model,'GetWidget',request,opts);
    assert.equal(actual.reason ?? actual.decision,faults === false ? 'PROCEED' : 'POLICY');
    queue.compare({op:'authorize',descriptor,method:'GetWidget',request,rules:rules.map(c.rule),
      authority,knownFacts:true,rowReads:[],faults:faults === false ? [] : undefined},c.authorization(actual));
  }
  const methods = fixture.methods.map(method => {
    if (method.name === 'GetWidget') return {...method,authz:{standard:{wildcardVariables:['team']}}};
    if (method.name !== 'ListWidgets') return method;
    return {...method,request:{...method.request,details:true},authz:{requirements:[
      {operation:'enumerate',accessClass:'READ',targetField:'parent'},
      {operation:'inventory',accessClass:'READ',serviceRoot:true},
      {operation:'detail',accessClass:'READ',targetField:'parent',condition:'details'}]}};
  });
  const sources = {...fixture,methods}, linked = m.interpret(sources), reflected = c.descriptor(sources,linked);
  assert.deepEqual([...linked.errors],[]);
  for (const [key,site,privateList] of [
    ['widgets.enumerate',scope,true], ['service.inventory',[],true], ['widgets.detail',scope,false],
    ['widgets.list',scope,false], ['service.inventory',scope,false]
  ]) {
    const rules = [grant(read)], request = {name:target};
    const opts = {handlerResolvesResiduals:true,nonprojecting:(k,p) => k === key && m.sameName(p,site),
      asWritten:[['companies','*','teams','*']],resolvePrefix:p => {
        if (m.sameName(p,wild)) throw Error('the wildcard is an as-written site');
      }};
    const auth = m.authorizeRequest(rules,linked,'GetWidget',request,opts);
    assert.equal(auth.residuals.find(r => r.kind === 'RESOLVE_WILDCARD')?.nonprojectingList,privateList);
    queue.compare({op:'authorize',descriptor:reflected,method:'GetWidget',request,rules:rules.map(c.rule),
      handlerResolvesResiduals:true,asWritten:c.domain(opts.asWritten),resolverErrors:[wild],
      nonprojectingRegions:[[key,site]]},c.authorization(auth));
  }
  for (const declared of [false,true]) {
    const create = fixture.methods.find(m => m.name === 'BatchCreateWidgets');
    const source = {...fixture,methods:[{...create,request:declared ? create.request : {requests:create.request.requests}}]};
    const I = m.interpret(source), descriptor = c.descriptor(source,I), method = create.name;
    assert.deepEqual([...I.errors],[]);
    for (const item of [null,parent]) {
      const request = {parent,'requests[].parent':[item]}, rules = [grant('widgets.create')];
      const status = m.batchRequestStatus(rules,I,method,request);
      assert.equal(status,declared || item ? 'OK' : 'PERMISSION_DENIED');
      queue.compare({op:'batchRequest',descriptor,method,request,rules:rules.map(c.rule)},status);
    }
  }
  const writer = fixture.methods.find(m => m.name === 'BatchUpdateWidgets');
  const source = {...fixture,methods:[{...writer,request:{...writer.request,update_mask:{}}}]};
  for (const fieldGuards of [false,true]) {
    const I = m.interpret(source,{fieldGuards}), descriptor = c.descriptor(source,I);
    assert.deepEqual([...I.errors],[]);
    const rules = [grant('widgets.update'),grant('widgets.setOwner')];
    const mask = ['display_name','owner'];
    for (const [fields,expected] of [
      [{update_mask:mask,'requests[].update_mask':[[...mask].reverse()]},'OK'],
      [{update_mask:mask,'requests[].update_mask':[['owner']]},'INVALID_ARGUMENT'],
      [{update_mask:mask,'requests[].update':[{}]},'OK'],
      [{update_mask:mask,'requests[].update':[{mask:['owner']}]},'INVALID_ARGUMENT'],
      [{update_mask:mask,'requests[].update':{}},'INVALID_ARGUMENT'],
      [{update_mask:mask,'requests[].update':[null]},'INVALID_ARGUMENT'],
      [{update_mask:null,'requests[].update':[{}]},'INVALID_ARGUMENT']
    ]) {
      const request = {parent,'requests[].widget.name':[name],...fields};
      const actual = m.batchRequestStatus(rules,I,writer.name,request);
      assert.equal(actual,expected);
      queue.compare({op:'batchRequest',descriptor,method:writer.name,request,rules:rules.map(c.rule)},actual);
    }
  }
}

function requestCases(api, check, rng) {
  const M = api.MODEL;
  const sources = new Map();
  const counts = { descriptor: 0, batch: 0, expand: 0, regionAllowed: 0, methodAvailable: 0, methodOffer: 0, bindings: 0, effectiveMask: 0, decide: 0, decideRequest: 0, authorize: 0, batchRequest: 0, fixtureOffer: 0,
    generatedFieldGuards: 0, nativeErrorBranches: 0, grantPolicy: 0, validateRoleSelectors: 0, externalPolicyCallbacks: 0, invalidSelectorReplays: 0, searchRefusedUpFront: 0 };
  function record(send) {
    return (input, expected) => {
      assert.ok(Object.hasOwn(counts, input.op), 'unregistered request operation ' + input.op);
      counts[input.op]++;
      send(input, expected);
    };
  }
  const queue = { compare:record(check.compare), control:record(check.control) };
  const recorder = { ...M }, storedNameModes = new WeakMap();
  const rowRequests = new WeakMap();
  function rowInputs(reader) {
    const facts = c.callbackInputs(reader,'attrsOf');
    if (!facts.requests) return facts;
    const index = rowRequests.get(reader) ?? 0;
    assert.ok(index < facts.requests.length,'missing row fixture for request ' + index);
    rowRequests.set(reader,index + 1);
    return facts.requests[index];
  }
  recorder.policyStoreRules = (store, subject) => {
    const rules = M.policyStoreRules(store,subject);
    if (store.asWrittenTypes) storedNameModes.set(rules,store.asWrittenTypes);
    return rules;
  };
  recorder.interpret = function(source, opts) {
    const I = M.interpret(source, opts);
    sources.set(I, source);
    return I;
  };
  function descriptor(I) {
    if (!I || !I.methods) return { service: 'fixture', methods: [], resources: [], referencedTypes: [] };
    const source = sources.get(I);
    if (!source) throw new Error('fixture used an interpretation with no descriptor source');
    return c.descriptor(source, I);
  }
  recorder.requirementsFor = function(I, method, request, ...args) {
    const rows = M.requirementsFor(I, method, request, ...args);
    const expected = rows && rows.map(r => ({ key: r.key, perItem: !!r.perItem, targets: r.targets,
      items: r.items, unboundItems: [...r.unboundItems], unbound: r.unbound, wildcard: c.lower(r.wildcard || 'concrete') }));
    queue.compare({ op: 'bindings', method, descriptor: descriptor(I), request: request || {} }, expected);
    return rows;
  };
  recorder.effectiveMask = function(request, fields) {
    const value = M.effectiveMask(request, fields);
    queue.compare({ op: 'effectiveMask', request: request ?? null, fields: c.fieldMetadata(fields) }, value);
    return value;
  };
  for (const name of ['authorizeRequest', 'batchRequestStatus', 'decideRequest']) {
    recorder[name] = function(rules, I, method, request, options, pointwiseOptions) {
      const pointwise = name === 'decideRequest';
      if (pointwise) options = {__proto__:pointwiseOptions,...pointwiseOptions,attrsOf:options === undefined ? api.fixtureValue({}) : options};
      const opts = options && typeof options === 'object' ? options : {};
      const knownFacts = typeof opts.attrsOf === 'function';
      const resolver = opts.resolvePrefix, hasResolver = typeof resolver === 'function';
      if (hasResolver && !Array.isArray(resolver.aliases)) throw Error('missing declared name mappings');
      const inputs = {...rowInputs(opts.attrsOf),...c.callbackInputs(opts.faults,'faults',rules),
        ...c.callbackInputs(opts.canName,'canName'),...c.callbackInputs(opts.nonprojecting,'nonprojecting',rules,Object.keys(I?.keys ?? {})),
        names:structuredClone(resolver?.aliases ?? []),resolverErrors:structuredClone(resolver?.failures ?? [])};
      const traced = {__proto__:opts,...opts};
      const readPaths = new Set();
      if (knownFacts) traced.attrsOf = path => {
        const name = JSON.stringify(path);
        assert.ok(!readPaths.has(name), method + ' read the same row twice');
        readPaths.add(name);
        return opts.attrsOf(path);
      };
      const externalPolicy = typeof opts.undeclaredPolicy === 'function' && !I?.methods?.[method] && I?.undeclared?.has(method);
      const out = pointwise ? M.decideRequest(rules, I, method, request, traced.attrsOf, traced)
        : M[name](rules, I, method, request, options === opts ? traced : options);
      if (externalPolicy) {
        counts.externalPolicyCallbacks++;
        return out;
      }
      if (Array.isArray(rules) && rules.some(r => r?.invalidSelectors)) {
        // Lean represents invalid grant selectors as rulesFromGrants = none (tested via expand/grantPolicy).
        if (name === 'authorizeRequest') assert.deepEqual([out.decision, out.reason], ['DENY', 'SERVER_FAULT']);
        else if (name === 'batchRequestStatus') assert.equal(out, 'PERMISSION_DENIED');
        else assert.equal(out, 'DENY');
        counts.invalidSelectorReplays++;
        return out;
      }
      for (const k of Object.keys(opts)) {
        if (!['handlerResolvesResiduals','attrsOf','resolvePrefix','authority','faults','ceiling','readOnlyCredential','asWrittenTypes','asWritten','undeclaredPolicy','budget','nonprojecting','canName'].includes(k)) throw Error('unmapped server option ' + k);
      }
      const op = pointwise ? 'decideRequest' : name === 'authorizeRequest' ? 'authorize' : 'batchRequest';
      queue.compare({ op, rules: rules.map(c.rule), descriptor: descriptor(I), method, request: request || {},
        asWrittenTypes: storedNameModes.has(rules) && (opts.asWrittenTypes === undefined || Array.isArray(opts.asWrittenTypes))
          ? [...storedNameModes.get(rules),...(opts.asWrittenTypes || [])] : opts.asWrittenTypes,
        asWritten: opts.asWritten && c.domain(opts.asWritten),
        budget: opts.budget, handlerResolvesResiduals: opts.handlerResolvesResiduals === true, knownFacts, hasFaults: typeof opts.faults === 'function',
        invalidAttrsOf: opts.attrsOf !== undefined && !knownFacts, filterHandled:opts.handlerResolvesResiduals !== false,
        ...inputs, authority: opts.authority === 'skipErrors' ? 'skipErrors' : 'failClosed',
        credential: { ceiling:opts.ceiling, readOnlyCredential:opts.readOnlyCredential }, invalidNameResolver: resolver != null && !hasResolver },
      op === 'authorize' ? c.authorization(out) : out);
      return out;
    };
  }
  for (const name of ['offer', 'offerDetailed']) {
    recorder[name] = function(I, snapshots, domains, method, request, options) {
      const opts = options || {};
      const multiple = opts.unresolvedSegments !== undefined;
      const field = multiple ? 'unresolvedSegments' : 'unresolvedSegment';
      const classifier = opts[field];
      const inputs = c.callbackInputs(classifier,field);
      const now = opts.now === undefined ? Date.now() : timestamp(opts.now);
      const out = M[name](I, snapshots, domains, method, request, opts);
      for (const k of Object.keys(opts)) {
        if (!['now','maxProfile','ceiling','readOnlyCredential','unresolvedSegment','unresolvedSegments'].includes(k)) {
          throw Error('unmapped offer option ' + k);
        }
      }
      const d = descriptor(I);
      const deliveries = (Array.isArray(snapshots) ? [...snapshots] : []).sort((a,b) => (a?.seq || 0) - (b?.seq || 0));
      queue.compare({ op: 'fixtureOffer', descriptor: d, deliveries, method, request: request || {}, unresolved:[], ...inputs, now, maxProfile: opts.maxProfile,
        credential: { ceiling:opts.ceiling, readOnlyCredential:opts.readOnlyCredential } },
      normalizedVerdict(out));
      return out;
    };
  }
  const failures = api.checks(recorder).filter(r => !r.ok);
  if (failures.length) throw Error('canonical fixture replay failed: ' + JSON.stringify(failures));
  checkMethodDeclarations(api, queue);
  checkRequestEvidence(api, queue);
  checkStandardResponses(api, queue);
  checkStandardRegistration(api, recorder, queue);
  checkUpdateMaskSource(api, queue);
  checkPartialDeclarations(api, recorder, queue);
  checkBatchWildcards(api, queue);
  checkPhysicalBatchParents(api, recorder, queue);
  checkConditionalHoists(api, recorder, queue);
  checkCustomItemContainers(api, recorder, queue);
  checkResourceCatalog(api, queue);
  checkDescriptorSources(api, queue);
  checkExplicitWriters(api, recorder, queue);
  checkReflectedAddresses(api, recorder, queue);
  checkPermissionFields(api, queue);
  checkMethodDispositions(api, queue);
  checkImportedNames(api, queue);
  checkImportedServices(api, queue);
  checkStreamingDefaults(api, queue);
  checkGuardDefinitions(api, queue);
  checkGuardCapability(api, queue);
  checkGuardPlacement(api, queue);
  checkWriterInputs(api, recorder);

  const patternsToCheck = [
    ['items/{x}', 'items/{y}'], ['items/{x}'], ['companies/{company}/settings'], ['settings'],
    ['configs/default/items/{item}'], ['items/{a}_{b}'], ['companies/{id}/items/{id}'],
    ['{item}'], ['items/{item'], ['items/{}'], [''], []
  ].map(patterns => ({ patterns }));
  const nested = ['companies', '*', 'items', '*'];
  patternsToCheck.push({ patterns: [nested], vars: ['company', 'item'] },
    { patterns: [['companies', '*', 'settings']] }, { patterns: [nested], vars: ['id', 'id'] },
    { patterns: [nested], vars: ['company'] });
  for (const declaration of patternsToCheck) {
    const source = { resources: { Item: { type: 'items.example/Item', plural: 'items', ...declaration } },
      methods: [{ name: 'GetItem', authz: { standard: {} }, request: { name: { type: 'Item' } } },
        { name: 'ReadAgain', authz: { requirements: [{ operation: 'get', accessClass: 'READ' }] },
          request: { name: { type: 'Item' } } }] };
    const result = recorder.interpret(source);
    queue.compare({ op: 'descriptor', descriptor: descriptor(result) }, result.errors.length === 0);
  }

  const I = recorder.interpret(api.FIXTURE, { fieldGuards: true });
  const fields = ['owner', 'display_name', 'create_time', 'unknown', '*'];
  for (let j = 0; j < 96; j++) {
    const path = ['companies','A','teams','B','widgets',String(j)];
    const mask = [rng.pick(fields)], populated = [rng.pick(fields)];
    const request = {
      'widget.name': path, allow_missing: !!rng.int(2),
      update: { ...(rng.int(3) ? { mask } : {}), populated }
    };
    recorder.requirementsFor(I,'UpdateWidget',request);
    counts.generatedFieldGuards++;
  }
  const target = ['companies','A','teams','B','widgets','w1'];
  const parent = target.slice(0,-2), other = [...parent,'widgets','w2'], wildcard = ['companies','A','teams','-'];
  const key = 'widgets.get', type = I.keys[key].type;
  const permit = { path: [], effect: 'permit', keys: [key] };
  const risky = { path: [], effect: 'forbid', keys: [key], mayError: true };
  const pair = [permit, risky];
  const read = {type:'widgets.example/Widget', cls:'READ'};
  for (const [selectors, expectedOk] of [
    [api.ROLES, true], [{readers:[read]}, true], [[{selectors:[read, {type:'*',op:'expunge'}]}], true],
    [{service:[{type:I.apiService + '/service',cls:'ADMIN'}]}, true],
    [{declaredOperation:[{...read,op:'expunge'},{type:'*',op:'expunge'}]}, true],
    [[{selectors:[read, {type:'*',op:'approve'}]}], false], [{empty:[]}, false], [[{selectors:[]}], false],
    [{short:[{...read,type:'Widget'}]}, false], [{foreign:[{...read,type:'other.example/User'}]}, false],
    [{unknownClass:[{...read,cls:'OBSERVE'}]}, false], [{badOperation:[{...read,op:'Bad.Op'}]}, false],
    [{undeclaredOperation:[{...read,op:'delet'}]}, false],
    [{wrongTypeOperation:[{type:'widgets.example/Company',op:'expunge'}]}, false], [null, false],
  ]) {
    const ok = M.validateRoleSelectors(I,selectors).ok;
    assert.equal(ok, expectedOk, 'validateRoleSelectors ' + JSON.stringify(selectors));
    queue.compare({op:'validateRoleSelectors', descriptor:descriptor(I), selectors}, ok);
  }
  // Empty, short, foreign, or syntactically invalid-operation forbid selectors fail closed on grant expansion and evaluation.
  const allowAll = { scope: [], selectors: [{ type: '*', cls: 'READ' }], effect: 'permit' };
  for (const badSelectors of [[{ type: 'Widget', cls: 'READ' }], [{ type: 'other.example/User', cls: 'READ' }], [], [{ type: '*', op: 'Bad.Op' }]]) {
    const badForbid = { scope: [], selectors: badSelectors, effect: 'forbid' };
    queue.compare({ op: 'expand', descriptor: descriptor(I), grant: c.grant(badForbid) }, M.keysFor(badForbid, I.keys));
    const gs = [allowAll, badForbid];
    const rules = M.rulesFromGrants(gs, I.keys);
    const decision = M.authorize(rules, key, target);
    assert.equal(decision, 'DENY');
    queue.compare({ op: 'grantPolicy', descriptor: descriptor(I), grants: gs.map(c.grant), key, path: target }, c.lower(decision));
  }
  // Well-formed operations absent from the active descriptor fail authoring validation,
  // but expand to zero keys at runtime instead of failing closed across unrelated RPCs.
  for (const retiredSelectors of [[{ type: 'widgets.example/Widget', op: 'delet' }], [{ type: '*', op: 'retiredOp' }]]) {
    const retiredForbid = { scope: [], selectors: retiredSelectors, effect: 'forbid' };
    assert.equal(M.validateRoleSelectors(I, [retiredForbid]).ok, false);
    queue.compare({ op: 'validateRoleSelectors', descriptor: descriptor(I), selectors: [retiredForbid] }, false);
    queue.compare({ op: 'expand', descriptor: descriptor(I), grant: c.grant(retiredForbid) }, M.keysFor(retiredForbid, I.keys));
    const gs = [allowAll, retiredForbid];
    const rules = M.rulesFromGrants(gs, I.keys);
    assert.equal(!!rules[1].invalidSelectors, false);
    const decision = M.authorize(rules, key, target);
    assert.equal(decision, 'ALLOW');
    queue.compare({ op: 'grantPolicy', descriptor: descriptor(I), grants: gs.map(c.grant), key, path: target }, c.lower(decision));
  }
  // Fault observations are tied to the source grant while the ceiling changes its expanded keys.
  const sourceGrants = [
    {scope:[], mayError:true, selectors:[{type:'*',cls:'READ'},{type:'*',cls:'UPDATE'}]},
    {scope:[], mayError:true, selectors:[{type:'*',op:'get'}]},
  ];
  const originals = M.rulesFromGrants(sourceGrants,I.keys);
  for (const outcomes of [[false,true],[true,false],[true,true]]) {
    const credential = [{type:I.keys[key].type,cls:'READ'}];
    const rules = M.rulesFromGrants(M.underCeiling(sourceGrants,credential),I.keys);
    const observed = rule => outcomes[rule.sourceIndex];
    const result = M.authorize(rules,key,target,{}, {faults:observed});
    queue.compare({op:'grantPolicy',descriptor:descriptor(I),grants:sourceGrants.map(c.grant),
      ceiling:c.ceiling(credential),key,path:target,faultOutcomes:originals.map(r => [c.rule(r),observed(r)])},
      c.lower(result));
  }
  checkFaultEvidence(M, I, descriptor(I), target, queue);
  const complete = {bindable:true,authorized:true,valid:true};
  for (const items of [[],[complete],[{...complete,bindable:false}],[{...complete,valid:false}],
    [complete,{...complete,authorized:false}],[{...complete,bindable:false},{...complete,authorized:false}]]) {
    for (const valid of [false,true]) for (const parentUniversal of [false,true]) for (const operationAllowed of [false,true]) {
      const fields = {items, valid, parentUniversal, operationAllowed};
      queue.compare({op:'batch', ...fields}, M.batchStatus(fields));
    }
  }
  for (const method of ['GetWidget','UpdateWidget','DeleteWidget','MoveWidget','InspectAccessPolicy','OptionalMethod',
    'google.longrunning.Operations/GetOperation','google.longrunning.Operations/CancelOperation']) {
    for (const credential of [{}, {readOnlyCredential:true}, {ceiling:[]}, {ceiling:['ADMIN']}, {ceiling:['UPDATE','CREATE']},
      {ceiling:[{type:I.keys[key].type, cls:'READ'}]}, {ceiling:[{type:'other.example/User', cls:'READ'}]}]) {
      queue.compare({op:'methodAvailable',descriptor:descriptor(I),method,credential},M.methodAvailable(I,method,credential).available);
    }
  }
  // The published row facts stay identical when enforcement skips a read and when it needs that read.
  for (const owner of [true,false]) {
    let reads = 0;
    const input = {factsByPath:[[target,owner]]};
    const attrsOf = api.fixtureCallback(() => { reads++; return {owner:owner ? 'alice' : 'bob'}; }, input);
    assert.equal(recorder.authorizeRequest([permit],I,'GetWidget',{name:target},{attrsOf}).decision,'PROCEED');
    assert.equal(reads,0);
    assert.equal(recorder.authorizeRequest([{...permit,pred:'owner'}],I,'GetWidget',{name:target},{attrsOf}).decision,
      owner ? 'PROCEED' : 'DENY');
    assert.equal(reads,1);
    assert.deepEqual(c.callbackInputs(attrsOf,'attrsOf'),input);
  }
  checkRowReads(api, recorder, I, target);
  checkBatchParentRows(api, recorder, I, target);
  checkEnforcementVisibility(M, recorder, I, descriptor(I), queue);
  checkRegionCeilings(M, I, descriptor(I), queue);
  checkResolvedRequests(api, queue);
  for (const effect of ['permit', 'forbid']) {
    const plain = { effect: 'permit', scope: [], selectors: [{type: '*', op: 'get'}] };
    const guarded = { ...plain, effect, condition: '' };
    const grants = effect === 'permit' ? [guarded] : [plain, guarded];
    const rules = M.rulesFromGrants(grants, I.keys);
    const decision = M.authorize(rules, key, target);
    assert.equal(decision, 'DENY');
    queue.compare({ op: 'grantPolicy', descriptor: descriptor(I), grants: grants.map(c.grant), key, path: target }, c.lower(decision));
  }
  // A stateful callback cannot provide its own native inputs. Missing declarations fail before dispatch.
  let evaluations = 0;
  assert.throws(() => recorder.authorizeRequest([permit, risky], I, 'GetWidget', {name:target},
    {attrsOf:api.fixtureValue({}), authority:'skipErrors', faults:() => ++evaluations === 1}), /missing declared inputs for faults/);
  assert.equal(evaluations,0);
  const stateful = M.authorizeRequest([permit,risky,{...risky}],I,'GetWidget',{name:target},
    {attrsOf:() => ({}), authority:'skipErrors', faults:() => ++evaluations === 1});
  assert.deepEqual([stateful.decision,stateful.reason,evaluations],['DENY','POLICY',2]);
  const readCredential = { type, cls: 'READ' }, foreign = { type: 'other.example/Thing', cls: 'READ' };
  const ceilings = [null, [], ['READ'], [readCredential], [foreign], [{type:'*', cls:'READ'}], ['UPDATE']];
  for (const authority of ['skipErrors','failClosed']) {
    for (const ceiling of ceilings) {
      for (const attrsOf of [undefined, api.fixtureValue({})]) {
        const opts = { authority, ceiling, attrsOf, faults:api.fixtureCallback((r,p) => p.at(-1) === 'w1', {faultOutcomesByPath:[
          {path:target,rule:c.rule(risky),fault:true}, {path:other,rule:c.rule(risky),fault:false}]}), handlerResolvesResiduals: true };
        for (const names of [[target], [target,other], []]) {
          const batch = { parent, 'names[]': names };
          recorder.batchRequestStatus(pair,I,'BatchGetWidgets',batch,opts);
          recorder.authorizeRequest(pair,I,'BatchGetWidgets',batch,opts);
        }
        for (const rules of [[permit],pair]) {
          recorder.authorizeRequest(rules,I,'GetWidget',{ name: target },opts);
          recorder.authorizeRequest(rules,I,'GetWidget',{ name: other },opts);
        }
        const allKeys = [{ ...permit, keys: Object.keys(I.keys) }];
        for (const method of ['ListWidgets','SearchWidgets']) {
          recorder.authorizeRequest(allKeys,I,method,{ parent: wildcard },opts);
        }
        counts.nativeErrorBranches += 12;
      }
      const base = { scope: [], selectors: [{type:'*', op:'get'}] };
      for (const previous of [null, ['READ'], [readCredential], [foreign]]) {
        for (const extra of [[], [{...base, effect:'forbid', ceiling: []}], [{...base, scope: ['bogus']}]]) {
          const gs = [{...base, ceiling: previous}, ...extra];
          const rules = M.rulesFromGrants(M.underCeiling(gs,ceiling),I.keys);
          queue.compare({ op: 'grantPolicy', descriptor: descriptor(I), grants: gs.map(c.grant), ceiling: c.ceiling(ceiling),
            authority, key, path: target }, c.lower(M.authorize(rules,key,target,{}, {authority})));
        }
      }
    }
    const base = { scope: [], selectors: [{type:'*', cls:'READ'}], ceiling: [readCredential] };
    const pinned = { ...base, condition:'owner', hidden:true, mayError:true };
    for (const gs of [[pinned], [base,{...pinned,effect:'forbid'}]]) {
      for (const credential of [[readCredential],[foreign]]) for (const owner of [true,false]) for (const fault of [true,false]) {
        const rules = M.rulesFromGrants(M.underCeiling(gs,credential),I.keys);
        const answer = M.authorize(rules,key,target,{ owner: owner ? 'alice' : 'another' },{ authority, faults:() => fault });
        queue.compare({ op:'grantPolicy', descriptor:descriptor(I), grants:gs.map(c.grant), ceiling:c.ceiling(credential),
          authority, key, path:target, predicates:[['owner',owner]], faults:fault ? rules.filter(r => r.mayError).map(c.rule) : [] },
        c.lower(answer));
      }
    }
    for (const handlerResolvesResiduals of [false,true]) {
      recorder.authorizeRequest(pair,I,'GetWidget',{name:target},{authority,handlerResolvesResiduals});
      counts.nativeErrorBranches++;
    }
  }
  return counts;
}

module.exports = { requestCases };
