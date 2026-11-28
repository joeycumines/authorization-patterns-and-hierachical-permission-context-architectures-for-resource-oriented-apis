// Exercise the canonical model through its normal dispatch, receive and offer
// entry points. Only names, facets and wire metadata are converted for Lean.
'use strict';

const assert = require('node:assert/strict');
const codec = require('./formal/codec');

const receiveAction = result => result.accepted ? result.action.toLowerCase() : 'discard';

function toReply(response) {
  return {
    service: response.service, subject: response.subjectContextId, token: response.snapshotToken,
    expires: response.expireTime, descriptorEtag: response.descriptorEtag,
    profile: response.profile, keySets: response.keySets, contexts: response.contexts
  };
}

function toState(state) {
  return {
    service: state.service, session: state.sessionId, subject: state.subjectContextId,
    token: state.currentToken, generation: state.resetGeneration,
    serial: state.seq,
    loadedEtag: state.loadedDescriptorEtag, lastEtag: state.lastDescriptorEtag,
    history: [...state.snapshots].reverse().map(s => ({ serial: s.seq, reply: toReply(s) }))
  };
}

function runClientCases(api, compare, rng, reject) {
  const m = api.MODEL;
  const names = ['GetWidget', 'ListWidgets', 'MoveWidget', 'BatchUpdateWidgets', 'UpdateWidget'];
  const source = { ...api.FIXTURE, methods: api.FIXTURE.methods.filter(d => names.includes(d.name)) };
  const model = m.interpret(source);
  if (model.errors.length) throw Error('Client test descriptor: ' + model.errors.join(', '));
  const descriptor = codec.descriptor(source, model);
  const domains = Object.fromEntries(Object.entries(model.keys).map(([k,v]) => [k,v.patterns]));
  const service = model.apiService, session = 'client';
  const scopedQuery = { service, maxProfile: 'SCOPED_CLAIMS' };
  function ticket(sent) {
    return { session: sent.sessionId, generation: sent.sentResetGeneration, minToken: sent.sentMinToken,
      service: sent.sentService, maxProfile: codec.enumName(sent.sentMaxProfile) };
  }
  const counts = { traces: 0, deliveries: 0, targetVerdicts: 0, methodOffers: 0,
    partialBatches: 0, directOffers: 0, directPartialOffers: 0, lateReplies: 0, rejected: 0, subjectResets: 0, inPlaceAliases: 0, crossDepthAliases: 0, serverFloorCases: 0 };
  function trace(domains, resources, state, events, actions, queries, scopes, listings, compareState = false) {
    const entries = Object.entries(domains).map(([k, pats]) => [k, codec.domain(pats)]);
    const token = snapshot => snapshot === null ? null : JSON.parse(snapshot)[2];
    const results = queries.map(q => m.evaluate(state.snapshots, domains, q.key, q.q, q).result.toLowerCase());
    const scoped = scopes.map(q => {
      const e = m.evaluateScope(state.snapshots, domains, q.key, q.q, q);
      return { result: e.result.toLowerCase(), token: token(e.snapshot) };
    });
    const regions = listings.map(q => m.usableRegions(state.snapshots, domains, q.key, q)
      .map(r => ({ path: r.path, holes: r.holes, token: token(r.snapshot) })));
    compare({ op: 'trace', service, session, keys: entries, resources: codec.domain(resources),
      events, queries, scopes, listings }, { actions, results, scopes: scoped, listings: regions });
    if (compareState) {
      const input = { state: toState(state), keys: entries, resources: codec.domain(resources) };
      compare({ ...input, op: 'evaluateScope', key: scopes[0].key, scope: scopes[0].q, now: scopes[0].now, maxProfile: scopes[0].maxProfile }, scoped[0]);
      compare({ ...input, op: 'usableRegions', key: listings[0].key, now: listings[0].now, maxProfile: listings[0].maxProfile }, regions[0]);
    }
    counts.scopeVerdicts += scopes.length;
    counts.rootListings += listings.length;
  }
  // A canonical query, its actual grouped response, and the wildcard RPC share a revision.
  counts.groupedWildcardLists = 0;
  {
    const key = 'widgets.list', anchor = ['companies', 'A'], q = [...anchor, 'teams', '-'];
    const stamp = { service, subject: 'reader', etag: 'v1', snapshotToken: 'revision', expireTime: 1000 };
    const metadata = { subjectContextId: stamp.subject, descriptorEtag: stamp.etag,
      snapshotToken: stamp.snapshotToken, expireTime: stamp.expireTime };
    const keys = [[key, codec.domain(domains[key])]], resources = codec.domain(model.resourcePatterns);
    const query = { ...scopedQuery, anchors: [{ resource: anchor.join('/') }] };
    const view = { ...model, keys: { [key]: model.keys[key] } };
    for (const maximum of [{}, { maxProfile: null }, { max_profile: null }]) {
      const request = { service, anchors: query.anchors, ...maximum };
      const wire = m.queryPermissionContexts([], view, request, metadata);
      assert.equal(wire.profile, 'PROFILE_GRANT_SHAPED');
      compare({ op: 'query', protoJson: true, asked: [anchor], keys, resources, stamp,
        profile: 'grantShaped', rules: [] }, wire);
      const tag = m.snapshotRequestTag(null, session, request);
      const accepted = m.acceptNextSnapshot(null, m.decodeProtoJsonResponse(wire, model.domains),
        tag.sentMinToken, { ...tag, now: 1 });
      assert.equal(accepted.accepted, true);
      const rawTicket = { session, service, generation: 0, minToken: '', ...maximum };
      compare({ op: 'trace', service, session, keys, resources,
        events: [{ ticket: rawTicket, reply: wire, protoJson: true, now: 1 }], queries: [] },
        { actions: [receiveAction(accepted)], results: [], scopes: [], listings: [] });
      counts.traces++; counts.deliveries++;
    }
    for (const rules of [[], [{ keys: [key], path: anchor, effect: 'permit' }]]) {
      const raw = m.queryPermissionContexts(rules, view, query, metadata);
      compare({ op: 'query', protoJson: true, asked: [anchor], keys, resources, stamp,
        profile: 'scopedClaims', rules: rules.map(codec.rule) }, raw);
      const sent = m.snapshotRequestTag(null, session, query);
      const decoded = m.decodeProtoJsonResponse(raw, model.domains);
      const read = m.acceptNextSnapshot(null, decoded, sent.sentMinToken, { ...sent, now: 1, domains: model.domains });
      assert.equal(read.accepted, true);
      const evidence = m.evaluate(read.state.snapshots, domains, key, q, { now: 1 }).result;
      compare({ op: 'trace', service, session, keys, resources,
        events: [{ ticket: ticket(sent), reply: raw, protoJson: true, now: 1 }], queries: [{ key, q, now: 1 }] },
        { actions: [receiveAction(read)], results: [evidence.toLowerCase()], scopes: [], listings: [] });
      const request = { parent: q }, method = 'ListWidgets';
      const offered = m.offer(model, read.state.snapshots, domains, method, request, { now: 1 });
      const auth = m.authorizeRequest(rules, model, method, request);
      assert.equal(offered, rules.length ? 'ALLOW' : 'DENY');
      assert.equal(auth.decision, rules.length ? 'PROCEED' : 'DENY');
      compare({ op: 'methodOffer', descriptor, state: toState(read.state), method, request, now: 1 }, offered.toLowerCase());
      compare({ op: 'authorize', descriptor, method, request, rules: rules.map(codec.rule) }, codec.authorization(auth));
      counts.groupedWildcardLists++;
      counts.traces++; counts.deliveries++; counts.targetVerdicts++; counts.methodOffers++;
    }
  }
  counts.scopeVerdicts = 0;
  counts.rootListings = 0;
  counts.multiPatternSchemas = 0;
  {
    const key = 'widgets.get', team = ['companies', 'A', 'teams', 'B'];
    const target = [...team, 'widgets', 'w1'], name = team.join('/');
    const now = Date.UTC(2024, 1, 29);
    const sent = m.snapshotRequestTag(null, session, scopedQuery);
    const options = { ...sent, now, domains: model.domains };
    const base = {
      service, descriptorEtag: 'v1', subjectContextId: 'reader', snapshotToken: 'rev',
      expireTime: '2024-02-29T01:00:01.123456789+01:00', profile: 'PROFILE_SCOPED_CLAIMS',
      keySets: [{ id: 1, keys: [key] }]
    };
    const anchor = { resource: name };
    const claim = { keySet: 1, kind: 'ALLOW', scope: anchor };
    const context = { anchor, requestedAnchors: [anchor], claims: [claim] };
    const response = (ctx = context, envelope = {}) => ({ ...base, ...envelope, contexts: [ctx] });
    counts.wireReplies = 0;
    function check(reply, expected, accepted = true) {
      const decoded = m.decodeProtoJsonResponse(reply, model.domains);
      const read = m.acceptNextSnapshot(null, decoded, sent.sentMinToken, options);
      const observed = m.evaluate(read.state?.snapshots, model.domains, key, target, { now }).result;
      assert.equal(read.accepted, accepted, JSON.stringify(reply));
      assert.equal(observed, expected, JSON.stringify(reply));
      compare({ op: 'trace', service, session, keys: [[key, codec.domain(domains[key])]],
        resources: codec.domain(model.resourcePatterns), events: [{ ticket: ticket(sent), reply, protoJson: true, now }],
        queries: [{ key, q: target, now }] },
        { actions: [receiveAction(read)], results: [observed.toLowerCase()], scopes: [], listings: [] });
      counts.wireReplies++;
      counts.traces++;
      counts.deliveries++;
      counts.targetVerdicts++;
      if (!read.accepted) counts.rejected++;
    }
    for (const [normalized, profiles] of [
      ['GRANT_SHAPED', ['GRANT_SHAPED', 'PROFILE_GRANT_SHAPED', 1]],
      ['SCOPED_CLAIMS', ['SCOPED_CLAIMS', 'PROFILE_SCOPED_CLAIMS', 2]]
    ]) {
      for (const profile of profiles) {
        check(response(context, { profile }), 'ALLOW');
        check(response({ ...context, profile }, { profile: normalized }), 'ALLOW');
        const detached = m.decodeResponse({ contexts: [{ anchor: team, profile }] }, model.domains);
        assert.equal(Object.hasOwn(detached, 'profile'), false);
        assert.equal(detached.contexts[0].profile, normalized);
      }
    }
    for (const repeated of [
      [{ anchor: {resource:'companies'} }, { anchor: {resource:'companies'} }],
      [context, {anchor:{resource:'companies'}, requestedAnchors:[anchor]}],
      [{anchor, requestedAnchors:[{resource:'companies'}]},
        {anchor:{serviceRoot:{}}, requestedAnchors:[{resource:'companies'}]}]
    ]) {
      const reply = {...base, contexts:repeated};
      assert.ok(m.decodeProtoJsonResponse(reply).error);
      check(reply, 'UNLOADED', false);
    }
    const shapes = [['projects','*'], ['preferences']];
    for (const [source, positions, length, expected] of [
      [['projects','mine'], [], 2, ['projects','mine']],
      [['projects','mine'], [1], 1, ['projects']],
      [['projects','-'], [], 2, ['projects','-']],
      [['notProjects','mine'], [], 2, null],
      [['-','mine'], [], 2, null], [['-','mine'], [1], 2, null],
      [['preferences'], [0], 1, null], [['projects','mine'], null, 2, null],
      [['projects','mine'], [], 3, null]
    ]) {
      const widened = m.widenName(source, shapes, positions, length);
      assert.deepEqual(widened == null ? null : Array.from(widened), expected);
      compare({op:'widenName', binding:{key, source, patterns:codec.domain(shapes), unresolved:positions, targetLength:length}}, widened);
    }
    const detached = m.decodeResponse({ contexts: [{ anchor: team }] }, model.domains);
    assert.equal(Object.hasOwn(detached, 'profile'), false);
    assert.equal(Object.hasOwn(detached.contexts[0], 'profile'), false);
    for (const [kind, number] of [['ALLOW', 1], ['DENY', 2], ['CONDITIONAL', 3]]) {
      for (const spelling of [kind, 'CLAIM_KIND_' + kind, number]) {
        check(response({ ...context, claims: [{ ...claim, kind: spelling }] }), kind);
      }
    }
    for (const profile of [0, 'UNSPECIFIED', 'PROFILE_UNSPECIFIED', 'FUTURE']) {
      check(response(context, { profile }), 'UNLOADED', false);
      check(response({ ...context, profile }), 'UNLOADED');
    }
    check(response({ ...context, profile: 1 }), 'UNLOADED');
    for (const kind of [0, 'UNSPECIFIED', 'KIND_UNSPECIFIED', 'CLAIM_KIND_UNSPECIFIED', 4]) {
      check(response({ ...context, claims: [{ ...claim, kind }] }), 'UNLOADED');
    }
    const root = { serviceRoot: {} }, collection = { collection: name + '/widgets' };
    check(response({ anchor: root, requestedAnchors: [root], claims: [{ ...claim, scope: root }] }), 'ALLOW');
    check(response({ ...context, claims: [{ ...claim, scope: collection }] }), 'ALLOW');
    check(response({ ...context, claims: [{ ...claim, holes: [collection] }] }), 'UNLOADED');
    check(response({ ...context, requestedAnchors: [collection] }), 'UNLOADED');
    check(response({ ...context, anchor: { ...anchor, ...root } }), 'UNLOADED');
    check(response({ ...context, claims: [{ ...claim, scope: { collection: name } }] }), 'UNLOADED');
    check(response(context, { expireTime: '2024-02-29T00:00:00.000Z' }), 'UNLOADED', false);
    check(response(context, { expireTime: '2024-02-30T10:00:00Z' }), 'UNLOADED', false);
    check(response(context, { expireTime: now + 1000 }), 'UNLOADED', false);
    check({ service, descriptor_etag: 'v1', subject_context_id: 'reader', snapshot_token: 'rev',
      expire_time: base.expireTime, profile: base.profile, key_sets: base.keySets, contexts: [
        { anchor: { service_root: {} }, requested_anchors: [{ service_root: {} }],
          claims: [{ key_set: 1, kind: 'ALLOW', scope: anchor }] }
      ] }, 'ALLOW');
    check({ ...base, contexts: null }, 'UNLOADED');
    check(response({ ...context, requestedAnchors: null, claims: [{ ...claim, holes: null }] }), 'ALLOW');
    check(response({ ...context, claims: [{ ...claim, keySet: '1' }] },
      { keySets: [{ id: '1', keys: [key] }] }), 'ALLOW');
    check(response({ ...context, claims: [{ ...claim, keySet: '1e2' }] },
      { keySets: [{ id: 100, keys: [key] }] }), 'ALLOW');
    check(response({ ...context, claims: [{ ...claim, keySet: '1.00000000000000001' }] }), 'UNLOADED');
    check(response(context, { keySets: [{ id: '2147483648', keys: [key] }] }), 'UNLOADED', false);
    check(response(context, { keySets: [{ id: '214748364800e-2', keys: [key] }] }), 'UNLOADED', false);
    check(response({ ...context, claims: [claim, null] }), 'UNLOADED');
    check({ ...base, contexts: [context, null] }, 'UNLOADED', false);
    check({ ...base, keySets: [null], contexts: [context] }, 'UNLOADED', false);
    check(response(context, { profile: null }), 'UNLOADED', false);
    // A newer context still supersedes its predecessor when its local expiry is unreadable.
    const first = m.acceptNextSnapshot(null, m.decodeProtoJsonResponse(response(), model.domains), '', options);
    const next = m.snapshotRequestTag(first.state, session, scopedQuery);
    const changed = response({ ...context, expireTime: 'no date' });
    const second = m.acceptNextSnapshot(first.state, m.decodeProtoJsonResponse(changed, model.domains),
      next.sentMinToken, { ...next, now, domains: model.domains });
    assert.equal(second.accepted, true);
    assert.equal(m.evaluate(second.state.snapshots, model.domains, key, target, { now }).result, 'UNLOADED');
    trace(model.domains, model.resourcePatterns, second.state, [
      { ticket: ticket(sent), reply: response(), protoJson: true, now },
      { ticket: ticket(next), reply: changed, protoJson: true, now }
    ], [receiveAction(first), receiveAction(second)], [{ key, q: target, now }], [], []);
    counts.wireReplies += 2;
    counts.traces++;
    counts.deliveries += 2;
    counts.targetVerdicts++;
  }
  {
    const key = 'widgets.get', path = ['companies', 'A', 'teams', 'B', 'widgets', 'w1'];
    const reply = (subjectContextId, snapshotToken, kind) => ({
      service, subjectContextId, snapshotToken, descriptorEtag: 'v1', expireTime: 100, profile: 'SCOPED_CLAIMS',
      contexts: [{ anchor: path, claims: [{ key, kind, path, holes: [] }] }]
    });
    const events = [], actions = [];
    let state = null;
    function receive(sent, value, expected) {
      const read = m.acceptNextSnapshot(state, value, sent.sentMinToken, { ...sent, now: 1 });
      const action = receiveAction(read);
      assert.equal(action, expected);
      if (!read.accepted) assert.strictEqual(read.state, state);
      events.push({ ticket: ticket(sent), reply: toReply(value), now: 1 });
      actions.push(action);
      state = read.state;
    }
    const dispatch = () => m.snapshotRequestTag(state, session, scopedQuery);
    const cold = dispatch();
    receive(cold, reply('alice', 'T1', 'ALLOW'), 'reset');
    const early = dispatch(), later = dispatch();
    receive(later, reply('alice', 'T2', 'DENY'), 'advance');
    receive(early, reply('bob', 'T2', 'ALLOW'), 'discard');
    receive(cold, reply('bob', 'T2', 'ALLOW'), 'discard');
    assert.equal(m.evaluate(state.snapshots, model.domains, key, path, { now: 1 }).result, 'DENY');
    trace(model.domains, model.resourcePatterns, state, events.slice(), actions.slice(), [{ key, q: path, now: 1 }], [], []);
    // A new dispatch at T2 may accept an identity change at the same policy revision.
    receive(dispatch(), reply('bob', 'T2', 'ALLOW'), 'reset');
    trace(model.domains, model.resourcePatterns, state, events, actions, [{ key, q: path, now: 1 }], [], []);
    counts.traces += 2;
    counts.targetVerdicts += 2;
    counts.deliveries += 9;
    counts.rejected += 4;
    counts.lateReplies += 4;
    counts.subjectResets++;
  }
  // Pass untouched key sets and groups to each decoder. Empty or unknown-only
  // groups can carry structural faults even when they contribute no usable key.
  {
    const key = 'widgets.get', a = ['companies','A','teams','B'], b = ['companies','A','teams','D'];
    const targets = [a,b].map(team => [...team,'widgets','w1']);
    const entries = Object.entries(domains).map(([k, patterns]) => [k, codec.domain(patterns)]);
    const sets = [{id:1,keys:[key]}, {id:2}, {id:3,keys:['widgets.future']}];
    const allow = path => ({kind:'ALLOW', keySet:1, scope:{resource:{path}}});
    const good = anchor => ({anchor, requestedAnchors:[anchor], claims:[allow(anchor)]});
    const first = good(a), sibling = good(b), empty = {kind:'ALLOW', keySet:2, path:a};
    const firstWith = claim => ({...first, claims:[...first.claims,claim]});
    counts.groupedReplies = 0;
    for (const profile of ['GRANT_SHAPED','SCOPED_CLAIMS']) {
      const tagged = (arm,path) => ({[arm]:{path}});
      const below = [...a,'widgets'], scoped = profile === 'SCOPED_CLAIMS';
      const probe = (grouped, expected, discarded = false) => {
        const options = {now:1,domains:model.domains}, sent = m.snapshotRequestTag(null,session,scopedQuery);
        const envelope = {service, subjectContextId:'reader', snapshotToken:'wire', descriptorEtag:'etag',
          expireTime:100, profile};
        const wire = {...envelope, ...grouped};
        const read = m.acceptNextSnapshot(null,wire,'',{...sent,...options});
        const verdicts = current => targets.map(t => m.evaluate(current?.snapshots,model.domains,key,t,options).result);
        assert.equal(read.accepted,!discarded);
        assert.equal(m.acceptSnapshot(wire,{...sent,...options}),!discarded);
        assert.deepEqual(verdicts(read.state),expected);
        const decoded = m.decodeResponse(wire,model.domains);
        if (discarded) assert.ok(decoded.error);
        else {
          assert.equal(decoded.error,undefined);
          const restored = JSON.parse(JSON.stringify(decoded));
          for (const value of [decoded,restored]) assert.deepEqual(verdicts(m.acceptNextSnapshot(null,value,'',{...sent,...options}).state),expected);
          const detached = m.decodeResponse(grouped,model.domains);
          assert.deepEqual(verdicts(m.acceptNextSnapshot(null,{...envelope,contexts:detached.contexts},'',{...sent,...options}).state),expected);
        }
        compare({op:'trace',service,session,keys:entries,resources:codec.domain(model.resourcePatterns),
          events:[{ticket:ticket(sent),reply:toReply({...envelope,contexts:[]}),grouped,now:1}],
          queries:targets.map(q => ({key,q,now:1}))},
          {actions:[receiveAction(read)],results:verdicts(read.state).map(v => v.toLowerCase()),scopes:[],listings:[]});
        counts.groupedReplies++;
        counts.traces++;
        counts.deliveries++;
        counts.targetVerdicts += targets.length;
        if (discarded) counts.rejected++;
      };
      const groups = [
        [empty,true], [{...empty,keySet:3},true], [{...empty,kind:'DENY'},scoped],
        [{...empty,kind:'CONDITIONAL'},scoped], [{...empty,holes:[tagged('collection',below)]},scoped],
        [{...empty,kind:'UNKNOWN'},false], [{...empty,kind:'KIND_UNSPECIFIED'},false],
        [{...empty,kind:undefined},false], [{...empty,keySet:9},false], [{...empty,keySet:0},false],
        [{...empty,keySet:'1'},false], [{...empty,path:undefined},false], [{...empty,scope:{}},false],
        [{...empty,scope:a},false], [{...empty,scope:[]},false],
        [{...empty,scope:{future:{path:a}}},false], [{...empty,scope:{resource:{path:a},collection:{path:a}}},false], [{...empty,scope:tagged('resource',b)},false],
        [{...empty,path:['companies','..']},false], [{...empty,path:b},false], [{...empty,holes:'bad'},false],
        [{...empty,holes:[{}]},false], [{...empty,holes:[a]},false], [{...empty,holes:[b]},false],
        [{...empty,holes:[[...a,'%']]},false], [{...empty,keySet:1,scope:tagged('collection',a)},false],
        [{...empty,keySet:1,scope:tagged('resource',a)},true], [{...empty,keySet:3,scope:tagged('collection',a)},true],
        [{...empty,scope:tagged('collection',a)},true], [{...empty,keySet:1,holes:[tagged('resource',below)]},false],
        [{...empty,keySet:1,holes:[tagged('collection',below)]},scoped],
        [{...empty,keySet:1,holes:[tagged('resource',[...below,'one']),[...below,'two']]},scoped],
        [{...empty,keySet:3,holes:[tagged('resource',below)]},scoped],
        [{...empty,keySet:1,path:[...a,'outside']},false], [{...empty,keySet:3,path:[...a,'outside']},true],
        [{...empty,keySet:1,kind:'DENY'},false], [null,false]
      ];
      for (const [claim,valid] of groups) probe({keySets:sets,contexts:[firstWith(claim),sibling]},[valid?'ALLOW':'UNLOADED','ALLOW']);
      for (const bad of [null,{}, {...first,anchor:['companies']}, {...first,claims:null},
        {...first,requestedAnchors:[['companies']]}, {...first,requestedAnchors:[['%']]}]) {
        probe({keySets:sets,contexts:[sibling,bad]},['UNLOADED','ALLOW']);
      }
      probe({keySets:sets,contexts:[{...first,requestedAnchors:[a,a]},sibling]},['ALLOW','ALLOW']);
      for (const claim of [{...empty,keySet:1,path:[]},{keySet:1,kind:'ALLOW',scope:'serviceRoot'}]) {
        probe({keySets:sets,contexts:[{anchor:[],claims:[claim]}]},['ALLOW','ALLOW']);
      }
      for (const invalid of [
        {keySets:[...sets,sets[0]],contexts:[first,sibling]}, {keySets:[{id:0,keys:[]}],contexts:[first,sibling]},
        {keySets:[{id:2147483648,keys:[]}],contexts:[first,sibling]}, {keySets:[{id:1,keys:[key,key]}],contexts:[first,sibling]},
        {keySets:[{id:1,keys:['\uE000','\u{10000}']}],contexts:[first,sibling]},
        {keySets:sets,contexts:[first,firstWith({...empty,kind:'FUTURE'}),sibling]},
        {keySets:sets,contexts:[first,{...sibling,requestedAnchors:[a]}]}
      ]) probe(invalid,['UNLOADED','UNLOADED'],true);
      probe({keySets:[...sets,{id:4,keys:['\u{10000}','\uE000']}],contexts:[first,sibling]},['ALLOW','ALLOW']);
    }
  }
  {
    const key = 'widgets.get', team = ['companies','A','teams','B'], target = [...team,'widgets','one'];
    const entries = Object.entries(domains).map(([k, ps]) => [k,codec.domain(ps)]);
    const rights = {kind:'ALLOW',path:[],holes:[],key}, grant = {anchor:[],claims:[rights]};
    const root = {anchor:[]}, leaf = {anchor:team}, duplicateRequest = [[],team];
    const base = {service, subjectContextId:'reader', snapshotToken:'old', descriptorEtag:'etag', expireTime:100};
    counts.receiptForms = 0;
    counts.importedFrames = 0;
    for (const profile of ['GRANT_SHAPED','SCOPED_CLAIMS']) {
      const envelope = {...base,profile}, opts = {now:1,domains:model.domains};
      const first = {...envelope,contexts:[grant]}, cold = m.snapshotRequestTag(null,session,scopedQuery);
      const cached = m.acceptNextSnapshot(null,first,'',{...cold,...opts}).state;
      const sent = m.snapshotRequestTag(cached,session,scopedQuery);
      for (const token of ['old','new']) {
        for (const table of [{}, {keySets:[]}]) for (const [body,admit,verdict] of [
          [{},true,'ALLOW'], [{contexts:[]},true,'ALLOW'], [{contexts:[root]},true,'UNLOADED'],
          [{contexts:[{...root,claims:[],requestedAnchors:[]}]},true,'UNLOADED'],
          [{contexts:[{claims:[]},root]},true,'UNLOADED'],
          [{contexts:[{...root,requestedAnchors:[team,team]}]},true,'UNLOADED'],
          [{contexts:[root,{...root,claims:null}]},false,'ALLOW'],
          [{contexts:[{...root,requestedAnchors:duplicateRequest},{...leaf,requestedAnchors:[team]}]},false,'ALLOW'],
          [{contexts:null},false,'ALLOW'], [{contexts:[{...root,claims:null}]},true,'ALLOW']
        ]) {
          const payload = {...table,...body}, reply = {...envelope,snapshotToken:token,...payload};
          const read = m.acceptNextSnapshot(cached,reply,sent.sentMinToken,{...sent,...opts});
          const observe = frames => [m.evaluate(frames,model.domains,key,target,opts).result,
            m.evaluateScope(frames,model.domains,key,[],opts).result,m.usableRegions(frames,model.domains,key,opts).length];
          const expected = [verdict,verdict,verdict === 'ALLOW' ? 1 : 0];
          assert.equal(read.accepted,admit);
          if (!admit) assert.strictEqual(read.state,cached);
          assert.equal(m.acceptSnapshot(reply,{...sent,...opts}),admit);
          const decoded = m.decodeResponse(reply,model.domains);
          assert.equal(!!decoded.error,!admit);
          assert.deepEqual(observe(read.state.snapshots),expected);
          assert.deepEqual(observe([...cached.snapshots,{...reply,seq:2}]),expected);
          const events = [{ticket:ticket(cold),reply:toReply(first),now:1}];
          // Both native receipt routes see the omissions, duplicate anchors and malformed fields as supplied.
          const direct = toReply(reply);
          const oldState = toState(cached);
          const stored = {...oldState,serial:2,token,history:[{serial:2,reply:direct},...oldState.history]};
          const evidence = m.evaluate([...cached.snapshots,{...reply,seq:2}],model.domains,key,target,opts);
          compare({op:'evaluate',state:stored,keys:entries,resources:codec.domain(model.resourcePatterns),key,target,now:1},
            {result:evidence.result.toLowerCase(),token:JSON.parse(evidence.snapshot)[2]});
          counts.importedFrames++; counts.targetVerdicts++;
          const detached = {reply:toReply({...envelope,snapshotToken:token,contexts:[]}),grouped:payload};
          for (const input of [{reply:direct},detached]) {
            trace(model.domains,model.resourcePatterns,read.state,[...events,{ticket:ticket(sent),now:1,...input}],
              ['reset',receiveAction(read)],[{key,q:target,now:1}],[{key,q:[],now:1}],[{key,q:[],now:1}]);
            counts.receiptForms++; counts.traces++; counts.deliveries += 2; counts.targetVerdicts++;
            if (!admit) counts.rejected++;
          }
        }
      }
      for (const contexts of [[grant,root],[{...grant,requestedAnchors:[team]},{...leaf,requestedAnchors:[team]}]]) {
        const reply = {...envelope,contexts}, read = m.acceptNextSnapshot(null,reply,'',{...cold,...opts});
        assert.equal(read.accepted,false);
        assert.equal(m.evaluate([{...reply,seq:1}],model.domains,key,target,opts).result,'UNLOADED');
        compare({op:'trace',service,session,keys:entries,resources:codec.domain(model.resourcePatterns),
          events:[{reply:toReply(reply),ticket:ticket(cold),now:1}],queries:[{key,q:target,now:1}]},
          {actions:[receiveAction(read)],results:[m.evaluate(read.state?.snapshots,model.domains,key,target,opts).result.toLowerCase()],scopes:[],listings:[]});
        counts.receiptForms++; counts.traces++; counts.deliveries++; counts.targetVerdicts++; counts.rejected++;
      }
    }
  }
  {
    const key = 'widgets.get', target = ['companies', 'c', 'teams', 't', 'widgets', 'w'];
    const team = target.slice(0, -2), foreign = 'other.example';
    const modelClock = Date.now(), future = 253402300799999, view = { key, q: target, now: modelClock };
    const root = { key, q: [], now: modelClock };
    const response = { service, subjectContextId: 'alice', snapshotToken: 'A', descriptorEtag: 'old',
      profile: 'SCOPED_CLAIMS', expireTime: future,
      contexts: [{ anchor: [], claims: [{ key, kind: 'ALLOW', path: [], holes: [] }] }] };
    const revocation = { expireTime: 1, contexts: [{ anchor: team, claims: [{ key, kind: 'DENY', path: team, holes: [] }] }] };
    const events = [], actions = [];
    let state = null;
    function receive(changes, opts, action) {
      const reply = { ...response, ...changes }, sent = m.snapshotRequestTag(state, session, scopedQuery);
      const result = m.acceptNextSnapshot(state, reply, sent.sentMinToken, { ...sent, ...opts });
      assert.equal(result.accepted ? result.action : 'DISCARD', action);
      if (!result.accepted) { assert.strictEqual(result.state, state); counts.rejected++; }
      state = result.state;
      events.push({ ticket: ticket(sent), reply: toReply(reply), now: opts.now ?? modelClock, expectedService: opts.expectedService });
      actions.push(receiveAction(result));
      counts.deliveries++;
    }
    function confirm(result, regionCount) {
      // Omit now from each JavaScript call. All deadlines are far from the sampled native clock.
      assert.equal(m.evaluate(state.snapshots, domains, key, target).result, result);
      assert.equal(m.evaluateScope(state.snapshots, domains, key, []).result, result);
      assert.equal(m.usableRegions(state.snapshots, domains, key).length, regionCount);
      trace(domains, model.resourcePatterns, state, [...events], [...actions], [view], [root], [root], true);
      counts.traces++;
      counts.targetVerdicts++;
    }
    receive({ expireTime: 1 }, { allowExpired: true }, 'DISCARD');
    receive({}, { expectedService: service }, 'RESET');
    for (const fields of [{ service: foreign }, { service: foreign, snapshotToken: 'B' }, { service: foreign, subjectContextId: 'bob' }]) {
      receive(fields, { expectedService: foreign }, 'DISCARD');
    }
    receive({}, { expectedService: foreign }, 'DISCARD');
    confirm('ALLOW', 1);
    const local = toState(state);
    const method = { op: 'methodOffer', descriptor, method: 'GetWidget', request: { name: target }, now: modelClock };
    const foreignState = { ...local, service: foreign,
      history: local.history.map(f => ({ ...f, reply: { ...f.reply, service: foreign } })) };
    for (const [cache, expectedService, result] of [[state.snapshots, service, 'ALLOW'],
      [state.snapshots, foreign, 'UNLOADED'], [state.snapshots.map(s => ({ ...s, service: foreign })), foreign, 'UNLOADED']]) {
      assert.equal(m.offer(model, cache, domains, method.method, method.request, { expectedService }), result);
    }
    compare({ ...method, state: local },
      m.offer(model, state.snapshots, domains, method.method, method.request, {now:modelClock}).toLowerCase());
    compare({ ...method, state: foreignState }, m.offer(model,
      state.snapshots.map(s => ({...s,service:foreign})), domains, method.method, method.request, {now:modelClock}).toLowerCase());
    counts.methodOffers += 2;
    for (const invalid of [{ service: foreign }, { subject: 'bob' }, { token: '' }, { descriptorEtag: '' }]) {
      reject({ ...method, state: { ...local, history: local.history.map(f => ({ ...f, reply: { ...f.reply, ...invalid } })) } }, 'invalid client history');
    }
    receive(revocation, { now: 1, allowExpired: true }, 'DISCARD');
    receive(revocation, { now: 0 }, 'MERGE');
    confirm('UNLOADED', 0);
    receive({ ...revocation, snapshotToken: 'B', descriptorEtag: 'new' }, { now: 0 }, 'ADVANCE');
    confirm('UNLOADED', 0);
    const final = toState(state);
    const imported = { ...final, history: final.history.map((f, i) => i ? f : { ...f, reply: { ...f.reply, subject: 'bob' } }) };
    const common = { state: imported, keys: [], key, scope: [], now: modelClock };
    for (const op of ['evaluateScope', 'usableRegions', 'offer', 'offerPartial']) {
      reject({ ...common, op, requirements: [], operation: [], items: [] }, 'invalid client history');
    }
    for (const changed of [{ ...final, token: 'old' }, { ...final, history: [...final.history].reverse() },
      { ...final, history: [final.history[0], ...final.history] }]) {
      reject({ ...method, state: changed }, 'invalid client history');
    }
    const emptySession = m.acceptNextSnapshot(null, response, '', m.snapshotRequestTag(null, '', scopedQuery));
    assert.equal(emptySession.accepted, false);
    compare({ op: 'trace', service, session: '', keys: [], events: [{ ...events[1], ticket: { ...events[1].ticket, session: '' } }],
      queries: [] }, { actions:[receiveAction(emptySession)], results:[], scopes:[], listings:[] });
    counts.traces++;
    counts.deliveries++;
    counts.rejected++;
    const traceInput = { op: 'trace', service, session, keys: [], queries: [] };
    const observations = actions => ({ actions, results: [], scopes: [], listings: [] });
    const grant = { ...response, profile: 'GRANT_SHAPED' };
    const cold = m.snapshotRequestTag(null, session, { service });
    const baseTicket = { session, generation: 0, minToken: null, service };
    const first = m.acceptNextSnapshot(null, { ...grant, service: foreign }, '', { ...cold, expectedService: foreign });
    assert.equal(first.accepted, false);
    assert.strictEqual(first.state, null);
    const second = m.acceptNextSnapshot(first.state, grant, '', m.snapshotRequestTag(null, session, {service:foreign}));
    const third = m.acceptNextSnapshot(second.state, grant, '', cold);
    assert.deepEqual([first, second, third].map(receiveAction), ['discard', 'discard', 'reset']);
    compare({ ...traceInput, events: [
      { ticket: baseTicket, reply: toReply({ ...grant, service: foreign }), now: 1, expectedService: foreign },
      { ticket: { ...baseTicket, service: foreign }, reply: toReply(grant), now: 1 },
      { ticket: baseTicket, reply: toReply(grant), now: 1 }
    ] }, observations([first,second,third].map(receiveAction)));
    counts.traces++;
    counts.deliveries += 3;
    counts.rejected += 2;
    for (const invalid of [null, false, 1]) {
      assert.equal(m.acceptNextSnapshot(null, grant, '', m.snapshotRequestTag(null, session, { service: invalid })).accepted, false);
      assert.equal(m.acceptNextSnapshot(null, grant, '', { ...cold, expectedService: invalid }).accepted, false);
      const event = { ticket: baseTicket, reply: toReply(grant), now: 1 };
      reject({ ...traceInput, events: [{ ...event, ticket: { ...baseTicket, service: invalid } }] }, 'invalid requested service');
      reject({ ...traceInput, events: [{ ...event, expectedService: invalid }] }, 'invalid expected service');
      counts.traces += 2;
      counts.deliveries += 2;
      counts.rejected += 2;
    }
    for (const [field, maximum] of [
      ...[undefined, 'PROFILE_UNSPECIFIED', 0, 'GRANT_SHAPED', 1, 'SCOPED_CLAIMS', 2, null, 'unknown', 3].map(v => ['maxProfile', v]),
      ['max_profile', 'PROFILE_GRANT_SHAPED'], ['max_profile', 'PROFILE_SCOPED_CLAIMS'], ['max_profile', 'UNSPECIFIED'],
      ['max_profile', null]
    ]) {
      const query = maximum === undefined ? {} : { [field]: maximum };
      for (const reply of [grant, response]) for (const extra of [{}, { maxProfile: 'SCOPED_CLAIMS' }, { maxProfile: 'GRANT_SHAPED' }]) {
        const sent = m.snapshotRequestTag(null, session, { service, ...query });
        const result = m.acceptNextSnapshot(null, reply, '', { ...sent, ...extra });
        const invalid = ['unknown', 3].includes(maximum);
        const accept = !invalid && (reply.profile === 'GRANT_SHAPED' ||
          (['SCOPED_CLAIMS', 'PROFILE_SCOPED_CLAIMS', 2].includes(maximum) && extra.maxProfile !== 'GRANT_SHAPED'));
        assert.equal(result.accepted, accept);
        const input = { ...traceInput, events: [{ ticket: { ...baseTicket, ...query }, reply: toReply(reply), now: 1, ...extra }] };
        if (invalid) reject(input, 'invalid requested profile');
        else compare(input, observations([receiveAction(result)]));
        counts.traces++;
        counts.deliveries++;
        if (!accept) counts.rejected++;
      }
    }
  }
  {
    const key = 'widgets.get', now = 10, team = ['companies', 'c', 'teams', 't'];
    const sibling = ['companies', 'c', 'teams', 'u'], target = [...team, 'widgets', 'w'], other = [...sibling, 'widgets', 'w'];
    const entries = Object.entries(domains).map(([k, patterns]) => [k, codec.domain(patterns)]);
    const ctx = (anchor, kind) => ({ anchor, claims: kind ? [key, 'widgets.update'].map(k => ({ key: k, kind, path: anchor, holes: [] })) : [] });
    const deliver = (state, token, profile, contexts) => {
      const sent = m.snapshotRequestTag(state, session, { service, maxProfile: profile });
      const reply = { service, subjectContextId: 'alice', snapshotToken: token, descriptorEtag: '1', profile, expireTime: 100, contexts };
      const received = m.acceptNextSnapshot(state, reply, sent.sentMinToken, { ...sent, now: 1 });
      assert.equal(received.accepted, true);
      counts.deliveries++;
      return received.state;
    };
    const first = deliver(null, 'old', 'GRANT_SHAPED', [ctx(team, 'ALLOW'), ctx(sibling, 'ALLOW')]);
    for (const [token, anchor, kind, lower, upper, lowRegions, highRegions] of [
      ['new', team, 'DENY', 'UNLOADED', 'DENY', [sibling], [sibling]],
      ['new', team, 'ALLOW', 'UNLOADED', 'ALLOW', [sibling], [team, sibling]],
      ['old', team, null, 'UNLOADED', 'UNLOADED', [sibling], [sibling]],
      ['old', target, 'DENY', 'UNLOADED', 'UNLOADED', [sibling], [sibling]],
      ['old', target, 'ALLOW', 'ALLOW', 'ALLOW', [team, sibling], [target, team, sibling]]
    ]) {
      const state = deliver(first, token, 'SCOPED_CLAIMS', [ctx(anchor, kind)]);
      const base = { state: toState(state), keys: entries, resources: codec.domain(model.resourcePatterns), key, now };
      for (const [maximum, verdict, visible, elsewhere] of [
        ['GRANT_SHAPED', lower, lowRegions, 'ALLOW'], [0, lower, lowRegions, 'ALLOW'],
        [undefined, upper, highRegions, 'ALLOW'], [2, upper, highRegions, 'ALLOW'],
        ...[null, false, 'scopedClaims', 3, {}].map(max => [max, 'UNLOADED', [], 'UNLOADED'])
      ]) {
        const opts = { now, maxProfile: maximum }, native = { ...base, maxProfile: maximum };
        const verify = (op, name, result, expectedToken, serial) => {
          const row = op === 'evaluate' ? m.evaluate(state.snapshots, domains, key, name, opts) :
            m.evaluateScope(state.snapshots, domains, key, name, opts);
          assert.deepEqual([row.result, JSON.parse(row.snapshot)[2], row.seq], [result, expectedToken, serial]);
          compare({ ...native, op, [op === 'evaluate' ? 'target' : 'scope']: name }, { result: row.result.toLowerCase(), token: JSON.parse(row.snapshot)[2] });
        };
        verify('evaluate', target, verdict, token, 2);
        verify('evaluateScope', team, verdict, token, 2);
        verify('evaluate', other, elsewhere, 'old', 1);
        verify('evaluateScope', sibling, elsewhere, 'old', 1);
        counts.targetVerdicts += 2; counts.scopeVerdicts += 2;
        const list = Array.from(m.usableRegions(state.snapshots, domains, key, opts), r =>
          ({ path: Array.from(r.path), holes: Array.from(r.holes, h => Array.from(h)), token: JSON.parse(r.snapshot)[2] }));
        assert.deepEqual(list, visible.map(p => ({ path: p, holes: [], token: p === sibling ? 'old' : token })));
        compare({ ...native, op: 'usableRegions' }, list);
        counts.rootListings++;
        const single = { name: target }, batch = { 'requests[].widget.name': [target, other], return_partial_success: true };
        const offered = m.offer(model, state.snapshots, domains, 'GetWidget', single, opts);
        assert.equal(offered, verdict);
        const partial = m.offer(model, state.snapshots, domains, 'BatchUpdateWidgets', batch, opts);
        assert.deepEqual([partial.operation, ...partial.items], ['ALLOW', verdict, elsewhere]);
        compare({ ...native, descriptor, op: 'methodOffer', method: 'GetWidget', request: single }, offered.toLowerCase());
        compare({ ...native, descriptor, op: 'methodOffer', method: 'BatchUpdateWidgets', request: batch },
          { operation: partial.operation.toLowerCase(), items: partial.items.map(v => v.toLowerCase()) });
        // These inputs describe the two operations directly, independently of the method binder.
        const patterns = source.resources.Widget.patterns.map(codec.namedPattern);
        const active = (permission, cls, name) => ({info:{resourceType:source.resources.Widget.type,
          operation:permission.split('.')[1],accessClass:cls,explicitGrantOnly:false},deferBinding:false,targets:[
          {key:permission,source:name,patterns,targetLength:name.length,unresolved:[]}]});
        compare({...native,op:'offer',requirements:[active('widgets.get','read',target)]},offered.toLowerCase());
        compare({...native,op:'offerPartial',operation:[],items:[target,other].map(path => [active('widgets.update','update',path)])},
          {operation:partial.operation.toLowerCase(),items:partial.items.map(v => v.toLowerCase())});
        counts.directOffers++; counts.directPartialOffers++;
        counts.methodOffers += 2; counts.partialBatches++;
      }
    }
  }
  for (let i = 0; i < 640; i++) {
    const company = ['companies', 'c' + rng.int(17)];
    const team = [...company, 'teams', 't' + rng.int(17)], sibling = [...company, 'teams', 'other'];
    const widget = [...team, 'widgets', 'w' + rng.int(41)], other = [...sibling, 'widgets', 'z'];
    const wild = [...company, 'teams', '-'];
    const points = [company, team, sibling, widget, other];
    let state = null, now = 10;
    const events = [], actions = [];
    const tag = () => m.snapshotRequestTag(state, session, scopedQuery);
    const grant = (key, path, kind, holes = []) => ({ key, path, kind, holes });
    const response = (subject, token, anchor, claims, ttl, profile = 'SCOPED_CLAIMS') => ({
      service, subjectContextId: subject, snapshotToken: token, expireTime: ttl,
      descriptorEtag: 'v1', profile, contexts: [{ anchor, claims }]
    });
    function receive(sent, reply) {
      const result = m.acceptNextSnapshot(state, reply, sent.sentMinToken, { ...sent, now });
      events.push({ ticket: ticket(sent), reply: toReply(reply), now });
      actions.push(receiveAction(result));
      state = result.state;
      counts.deliveries++;
      if (!result.accepted) counts.rejected++;
    }
    const key = rng.pick(['widgets.get', 'widgets.list', 'widgets.update']);
    const initial = Object.keys(domains).map(k => grant(k, company, 'ALLOW'));
    const first = tag(), concurrentCold = tag();
    receive(first, response('alice', 'A', company, initial, 100));
    const delayed = tag(), outstanding = tag();
    if (i % 5 === 0) {
      // Both were dispatched after the token A reply. A later sequence may
      // still carry a reply from before the subject changed.
      receive(delayed, response('bob', 'B', company, [], 80));
      receive(outstanding, response('alice', 'A', team, [grant(key, team, 'ALLOW')], 90));
      receive(concurrentCold, response('alice', 'A', company, initial, 100));
      counts.subjectResets++;
      counts.lateReplies += 2;
      receive(tag(), response('bob', 'C', rng.pick(points), [], 15));
    } else if (i % 5 === 1) {
      // Keep a contradiction on two anchors at one token through partial expiry.
      receive(outstanding, response('alice', 'A', team, [grant(key, team, 'DENY')], 13));
      receive(delayed, response('alice', 'A', company, initial, 70));
      counts.lateReplies++;
    } else if (i % 5 === 2) {
      // A newer interior anchor supersedes an older grant on a wildcard target.
      receive(outstanding, response('alice', 'B', team, [grant(key, team, 'DENY')], 13));
      receive(delayed, response(i % 2 ? 'alice' : 'bob', 'old', company, initial, 150));
      counts.lateReplies++;
    } else if (i % 5 === 3) {
      // Same-anchor replacement can lower the profile and its own expiry.
      receive(outstanding, response('alice', 'A', company, initial, 13, 'GRANT_SHAPED'));
      const narrow = response('alice', 'A', team, [grant(key, team, 'ALLOW')], 50);
      narrow.contexts[0].expireTime = 20;
      receive(delayed, narrow);
      counts.lateReplies++;
    } else {
      const extra = 1 + rng.int(7);
      for (let j = 0; j < extra; j++) {
        const anchor = rng.pick(points), ticket = tag();
        const hole = anchor === company && rng.int(3) === 0 ? [rng.pick([team, sibling])] : [];
        const cl = grant(key, anchor, rng.pick(['ALLOW', 'CONDITIONAL', 'DENY']), hole);
        receive(ticket, response('alice', rng.int(3) ? state.currentToken : 'N' + j, anchor, [cl], now + 1 + rng.int(15)));
        now++;
      }
    }
    const queries = [12, 13, 24, 101].flatMap(at =>
      [[key, key === 'widgets.list' ? team : widget], ['widgets.get', other], ['widgets.list', wild], ['widgets.update', widget]].map(([k, q]) =>
        ({ key: k, q, now: at, maxProfile: i % 3 === 0 ? 1 : undefined })));
    const scopes = [12, 24, 101].flatMap(at => [[], company, team, widget].map(q => ({ key, q, now: at, maxProfile: i % 3 === 0 ? 1 : undefined })));
    trace(domains, Object.values(domains).flat(), state, events, actions, queries, scopes,
      scopes.filter(q => !q.q.length));
    counts.traces++;
    counts.targetVerdicts += queries.length;
    const cached = toState(state);
    const alias = rng.pick([[], [1], [3, 5], [5], 'CROSS_DEPTH', [99]]);
    if (Array.isArray(alias) && alias.length && alias[0] < 6) counts.inPlaceAliases++;
    if (alias === 'CROSS_DEPTH') counts.crossDepthAliases++;
    const methods = [['GetWidget', { name: widget }], ['MoveWidget', { name: widget, destination_parent: sibling }],
      ['BatchUpdateWidgets', { 'requests[].widget.name': [widget, other], 'requests[].allow_missing': [true, false],
        return_partial_success: true }]];
    for (const [method, request] of methods) {
      const at = rng.pick([12, 13, 24]);
      const ceiling = rng.pick([null, ['READ'], ['READ','UPDATE'], ['CREATE','UPDATE','DELETE']]);
      const opts = { now: at, maxProfile: i % 3 === 0 ? 'GRANT_SHAPED' : undefined, unresolvedSegments: p => p.join('/') === widget.join('/') ? alias : [] };
      if (ceiling) opts.ceiling = ceiling;
      const expected = m.offer(model, state.snapshots, domains, method, request, opts);
      const packed = typeof expected === 'string' ? expected.toLowerCase() :
        { operation: expected.operation.toLowerCase(), items: Array.from(expected.items, s => s.toLowerCase()) };
      compare({ op: 'methodOffer', descriptor, state: cached, method, request, now: at, maxProfile: opts.maxProfile,
        ceiling: codec.ceiling(ceiling), unresolved: [[widget, alias === 'CROSS_DEPTH' ? null : alias]] }, packed);
      counts.methodOffers++;
      if (typeof expected !== 'string') counts.partialBatches++;
    }
  }
  for (let i = 0; i < 96; i++) {
    const branches = ['companies' + rng.int(8), 'teams' + rng.int(8)];
    const singleton = 'settings' + rng.int(7);
    const patterns = [branches[0] + '/{company}/' + singleton, branches[1] + '/{team}/items/{item}'];
    const raw = { resources: { Item: { type: service + '/Item', plural: 'items', patterns } },
      methods: [{ name: 'GetItem', authz: { standard: {} }, request: { name: { type: 'Item' } } }] };
    const schema = m.interpret(raw);
    if (schema.errors.length) throw Error(schema.errors.join(', '));
    const key = 'items.get', id = 'id' + rng.int(12);
    const company = [branches[0], id], item = [...company, singleton], team = [branches[1], id];
    const second = [...team, 'items', 'b'];
    let state = null;
    const events = [], actions = [];
    function deliver(token, anchor, kind, path, holes, expires) {
      const sent = m.snapshotRequestTag(state, session, scopedQuery);
      const reply = { service, subjectContextId: 'alice', snapshotToken: token,
        descriptorEtag: 'v1', profile: i % 7 === 0 ? 'GRANT_SHAPED' : 'SCOPED_CLAIMS', expireTime: expires,
        contexts: [{ anchor, claims: [{ key, kind, path, holes }] }] };
      if (i % 11 === 0) reply.contexts[0].expireTime = 0;
      reply.contexts[0].requestedAnchors = i % 13 === 0 ? [[branches[0]]] : [anchor];
      const got = m.acceptNextSnapshot(state, reply, sent.sentMinToken, { ...sent, now: 1 });
      events.push({ ticket: ticket(sent), reply: toReply(reply), now: 1 });
      actions.push(got.action.toLowerCase());
      state = got.state;
    }
    deliver('shared', [], 'ALLOW', [], i % 2 ? [company] : [second], 90);
    deliver(i % 3 ? 'shared' : 'new', i % 2 ? team : company, 'DENY', i % 2 ? team : company,
      i % 4 ? [] : [i % 2 ? second : item], 12);
    const queries = [6, 18, 100].flatMap(now => [item, second, [branches[0], '-', singleton],
      [branches[1], '-', 'items', '-']].map(q => ({ key, q, now })));
    const scopes = [6, 18, 100].flatMap(now => [[], company, team, item, second].map(q => ({ key, q, now })));
    trace(schema.domains, schema.domains[key], state, events, actions, queries, scopes, scopes.filter(q => !q.q.length), true);
    counts.multiPatternSchemas++;
    counts.targetVerdicts += queries.length;
    counts.traces++;
    counts.deliveries += events.length;
  }
  for (let i = 0; i < 480; i++) {
    const authority = 'authority' + rng.int(3), epoch = 1 + rng.int(5), counter = rng.int(40);
    const server = { authority, epoch, seq: counter, minKnownSeq: rng.int(counter + 1) };
    const floor = rng.pick([null, '', 'malformed', 'v1:bad:0:1', 'v1:bad:1:9007199254740992',
      m.encodeSnapshotToken({ authority, epoch, seq: rng.int(42) }),
      m.encodeSnapshotToken({ authority, epoch: 1 + rng.int(5), seq: rng.int(42) }),
      m.encodeSnapshotToken({ authority: authority + 'other', epoch, seq: counter + 5 })]);
    compare({ op: 'minSnapshot', server: { revision: { authority, epoch, counter }, minKnownCounter: server.minKnownSeq },
      floor }, codec.enumName(m.serveWithMinSnapshot(server, floor)));
    counts.serverFloorCases++;
  }
  return counts;
}

module.exports = { runClientCases };
