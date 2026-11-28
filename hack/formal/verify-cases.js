'use strict';

const assert = require('node:assert/strict');
const path = require('node:path');
const { spawnSync } = require('node:child_process');
const api = require('../load-model')();
const c = require('./codec');
const { MODEL: m } = api;
const exe = path.resolve(__dirname, '../../formal/.lake/build/bin/authz-oracle');
const seed = 0x18c0ffee;
let stream = seed;
const rng = {
  int(n) {
    stream ^= stream << 13;
    stream ^= stream >>> 17;
    stream ^= stream << 5;
    return (stream >>> 0) % n;
  },
  pick(xs) { return xs[this.int(xs.length)]; }
};
const counters = new Map();
const categories = ['differential', 'nativeControls'];
let responses = 0;
let suite = '', pending = [], twins = 0;
function flush() {
  if (!pending.length) return;
  const run = spawnSync(exe, [], { input: pending.map(x => JSON.stringify(x.input)).join('\n') + '\n',
    encoding: 'utf8', maxBuffer: 32 * 1024 * 1024 });
  if (run.error) throw run.error;
  assert.equal(run.status, 0, run.stderr);
  const records = run.stdout.trimEnd().split('\n');
  assert.equal(records.length, pending.length, 'oracle response count');
  for (const [i, { input, expected, observe, error, category, suite: part }] of pending.entries()) {
    const actual = JSON.parse(records[i]);
    const counts = counters.get(part) || { differential: 0, nativeControls: 0, total: 0 };
    const count = counts.total + 1;
    try {
      if (error) assert.deepEqual(actual, { error });
      else {
        assert.ok(!Object.hasOwn(actual, 'error'), actual.error);
        assert.deepEqual(observe(actual.ok), JSON.parse(JSON.stringify(expected)));
      }
    } catch (e) {
      throw new Error(`${part} case ${count} (seed 0x${seed.toString(16)})\n${JSON.stringify(input)}\n${e.message}`, { cause: e });
    }
    counts[category]++;
    counts.total++;
    counters.set(part, counts);
  }
  responses += records.length;
  pending = [];
}
function enqueue(category, input, expectation) {
  assert.ok(categories.includes(category), 'missing or invalid oracle evidence category');
  pending.push({ input, ...expectation, category, suite });
  // A store trace returns the pinned descriptor with every committed state.
  if (input.op === 'store' || pending.length >= 128) flush();
}
function compare(input, expected, observe = x => x) {
  enqueue('differential', input, { expected, observe });
}
function control(input, expected) {
  enqueue('nativeControls', input, { expected, observe: x => x });
}
function reject(input, error) {
  enqueue('nativeControls', input, { error });
}
function accounting() {
  assert.equal(pending.length, 0);
  const counts = { differential: 0, nativeControls: 0, total: 0 };
  for (const row of counters.values()) {
    assert.equal(row.total, row.differential + row.nativeControls);
    for (const key of Object.keys(counts)) counts[key] += row[key];
  }
  assert.equal(counts.total, responses);
  assert.equal(counts.differential + counts.nativeControls, responses);
  return { ...counts, bySuite: Object.fromEntries(counters) };
}
function twin(left, right) {
  assert.deepEqual(JSON.parse(JSON.stringify(left)), JSON.parse(JSON.stringify(right)));
  twins++;
}

function project(rules, key, at, patterns, profile, {budget, nonprojecting = false} = {}) {
  const info = { [key]: { key, patterns } };
  const ctx = m.projectContext(rules, info, at, {profile, budget, nonprojecting:() => nonprojecting});
  compare({ op: 'project', rules: rules.map(c.rule), key, path: at, domain: c.domain(patterns),
    profile: c.enumName(profile), nonprojecting, budget },
    { claims: ctx.claims.map(c.claim), descendantsOmitted: Object.hasOwn(ctx, 'descendantsOmitted') ? ctx.descendantsOmitted : false });
  return ctx;
}
function fixtureCases() {
  const { FIXTURE, ROLES } = api;
  const { A, B, OPS } = api.simulatorFixtures();
  const key = 'widgets.get', target = [...B, 'widgets', 'one'];
  const rule = c.rule({ keys: [key], path: [], effect: 'forbid', mayError: true });
  const decide = { op: 'decide', key, path: target, rules: [rule] };
  for (const effect of ['permit', 'forbid']) {
    const grant = { path: [], keys: [key], effect: 'permit' };
    const restricted = { ...grant, effect, pred: '' };
    const rules = effect === 'permit' ? [restricted] : [grant, restricted];
    const result = m.authorize(rules, key, target);
    assert.equal(result, 'DENY');
    compare({ ...decide, rules: rules.map(c.rule) }, c.lower(result));
  }
  const auth = { op: 'authorize', method: 'GetWidget', request: { name: target }, rules: [rule], knownFacts: true,
    descriptor: c.descriptor(FIXTURE, m.interpret(FIXTURE)) };
  for (const [input, field, observations] of [
    [decide, 'predicates', [['owner', true], ['owner', false]]],
    [decide, 'faultOutcomes', [[rule, false], [rule, null]]],
    [auth, 'factsByPath', [[target, true], [target, false]]],
    [auth, 'rowReads', [[target, true], [target, false]]],
    [auth, 'faultOutcomesByPath', [true, null].map(fault => ({ path: target, rule, fault }))]
  ]) {
    reject({ ...input, [field]: observations }, 'conflicting observations in ' + field);
  }
  for (const fields of [{knownFacts:false, rowReads:[[target,false]]},
    {rowReads:[[target,false]], factsByPath:[[target,true]]}]) {
    reject({...auth, ...fields}, 'rowReads requires a configured reader; owner facts require a successful read');
  }
  for (const fieldGuards of [false, true]) {
    const I = m.interpret(FIXTURE, { fieldGuards });
    const d = c.descriptor(FIXTURE, I);
    assert.deepEqual([...I.errors], []);
    compare({ op: 'descriptor', descriptor: d }, I.errors.length === 0);
    const domains = Object.fromEntries(Object.values(I.keys).map(k => [k.key, k.patterns]));
    for (const selectors of Object.values(ROLES)) {
      const grants = [{ scope: A, selectors }];
      const rules = m.rulesFromGrants(grants, I.keys);
      compare({ op: 'expand', grant: c.grant(grants[0]), descriptor: d }, rules[0].keys);
      const collection = { scope: ['companies'], selectors };
      compare({ op: 'expand', grant: c.grant(collection), descriptor: d }, m.keysFor(collection, I.keys));
      const profile = 'SCOPED_CLAIMS';
      const snap = { seq: 1, profile, contexts: [m.projectContext(rules, I.keys, [], { profile })] };
      for (const { method, request } of Object.values(OPS)) {
        const common = { descriptor: d, method, request };
        compare({ ...common, op: 'authorize', rules: rules.map(c.rule), knownFacts: true, handlerResolvesResiduals: true },
          c.authorization(m.authorizeRequest(rules, I, method, request, { attrsOf: () => ({}), handlerResolvesResiduals: true })));
        compare({ ...common, op: 'methodOffer', state: c.frameState(I.apiService, snap), now: 1 },
          m.offer(I, [snap], domains, method, request).toLowerCase());
      }
      for (const parent of [B, null]) {
        for (const names of [[], [null], [[...B, 'widgets', 'one']], [[...B, 'widgets', 'x'], [...B, 'widgets', 'x']]]) {
          const method = 'BatchGetWidgets', request = { parent, 'names[]': names };
          compare({ op: 'batchRequest', descriptor: d, method, request, rules: rules.map(c.rule) },
            m.batchRequestStatus(rules, I, method, request));
        }
      }
    }
  }
}

function scopeCases() {
  const raw = { resources: { Config: { type: 'demo.example/Config', plural: 'configs', patterns: ['configs/{config}'] } },
    methods: [{ name: 'ListConfigs', authz: { standard: {} }, resourceType: 'Config', request: {} }] };
  const I = m.interpret(raw), descriptor = c.descriptor(raw, I);
  assert.deepEqual([...I.errors], []);
  const stamp = { service: I.apiService, subject: 'alice', etag: 'config', snapshotToken: 'v1', expireTime: 100 };
  const resources = c.domain(I.resourcePatterns), keys = Object.entries(I.domains).map(([k, ps]) => [k, c.domain(ps)]);
  for (const profile of ['SCOPED_CLAIMS', 'GRANT_SHAPED']) {
    const key = 'configs.list', rules = [{ path: [], effect: 'permit', keys: [key] }];
    const claims = m.projectAnchor(rules, key, ['configs'], I.keys[key].patterns,
      { profile, resourcePatterns: I.resourcePatterns });
    assert.equal(claims.length, 0);
    compare({ op: 'project', key, rules: rules.map(c.rule), path: ['configs'], domain: c.domain(I.keys[key].patterns),
      resources, profile: c.enumName(profile) }, claims.map(c.claim), output => output.claims);
  }
  for (const profile of [null, false, 'UNKNOWN', 'PROFILE_UNSPECIFIED']) {
    const key = 'configs.list', domain = I.keys[key].patterns;
    const context = { anchor: [], claims: [] };
    assert.equal(m.projectContext([], I.keys, [], { profile }).error, 'SERVER_FAULT');
    assert.deepEqual(Array.from(m.projectAnchor([], key, [], domain, { profile })), []);
    assert.ok(m.validateContext(context, I.domains, profile));
    const error = typeof profile === 'string' ? 'no inductive constructor matched' : 'no inductive tag found';
    reject({ op: 'project', key, path: [], rules: [], domain: c.domain(domain), resources, profile }, error);
    reject({ op: 'contextValid', keys, resources, context, profile }, error);
  }
  for (const requestedAnchors of [null, 'configs/default', [null]]) {
    const context = { anchor: [], claims: [], requestedAnchors };
    compare({ op: 'contextValid', keys, resources, context, profile: 'scopedClaims' }, m.validateContext(context, I.domains) === null);
  }
  for (const external of [false, true]) {
    const source = {resources:{
      Settings:{type:'app.example/Settings', plural:'settings', patterns:['companies/{company}/settings']},
      Rule:{type:'app.example/Rule', external, plural:'rules', patterns:['companies/{company}/settings/rules/{rule}']}
    },methods:[{name:'GetRule', request:{name:{type:'Rule'}}, authz:{handlerPolicy:'rulesAccess'}}]};
    const model = m.interpret(source);
    assert.equal(model.errors.length === 0, external);
    assert.equal(model.methods.GetRule.disposition, 'HANDLER_POLICY');
    compare({op:'descriptor', descriptor:c.descriptor(source, model)}, model.errors.length === 0);
  }
  for (const site of [[], ['configs'], ['configs', 'default']]) {
    for (const ctx of [{ anchor: site, claims: [] }, { anchor: [], requestedAnchors: [site], claims: [] }]) {
      compare({ op: 'contextValid', keys, resources, context: ctx, profile: 'scopedClaims' }, m.validateContext(ctx, I.domains) === null);
    }
    const reply = m.queryPermissionContexts([], I, {service:I.apiService, maxProfile:'SCOPED_CLAIMS',
      anchors:[site.length ? {resource:site.join('/')} : {serviceRoot:{}}]}, {
      descriptorEtag:stamp.etag, subjectContextId:stamp.subject, snapshotToken:stamp.snapshotToken, expireTime:stamp.expireTime});
    compare({ op:'query', protoJson:true, keys, resources, profile:'scopedClaims', asked:[site], stamp, rules:[] }, reply);
    const rules = [[], site].map(path => ({ path, keys: ['configs.list'], effect: 'permit' }));
    compare({ op: 'authorize', descriptor, method: 'ListConfigs', request: {}, rules: rules.map(c.rule) },
      c.authorization(m.authorizeRequest(rules, I, 'ListConfigs', {})));
  }
}

function serviceNameCases() {
  const label = 'a'.repeat(63), longest = [label, label, label, 'a'.repeat(61)].join('.');
  const names = ['xn--bcher-kva.example', 'my--svc.example', '1password.example', 'widgets', longest, longest + 'a',
    'a'.repeat(64) + '.example', 'a..example', '-a.example', 'a-.example', 'Widgets.example', 'widgets.example.', 'widgets/bad', ''];
  const pure = { name: 'QueryPermissionContexts', authz: { handlerPolicy: 'auth' }, noSideEffects: true, request: {} };
  const root = { name: 'ExportAuditLog', authz: { requirements: [{ operation: 'exportAuditLog', accessClass: 'ADMIN', serviceRoot: true }] }, request: {} };
  for (const name of names) {
    const sources = [{ apiService: name, methods: [pure] }, { apiService: name, methods: [root] },
      { resources: { X: { type: name + '/X', plural: 'xs', patterns: ['xs/{x}'] } }, methods: [] }];
    for (const source of sources) {
      const model = m.interpret(source);
      compare({ op: 'descriptor', descriptor: c.descriptor(source, model) }, model.errors.length === 0);
    }
  }
  const I = m.interpret(api.FIXTURE), descriptor = c.descriptor(api.FIXTURE, I);
  for (const name of names) {
    const credential = { ceiling: [{ type: '*', cls: 'READ' }, { type: name + '/service', cls: 'ADMIN' }] };
    compare({ op: 'methodAvailable', descriptor, method: 'GetWidget', credential }, m.methodAvailable(I, 'GetWidget', credential).available);
  }
}
function parentTargetCases() {
  const { FIXTURE } = api;
  const need = (accessClass, operation, extra = {}) => ({ accessClass, operation, ...extra });
  const upsert = (create, request = { widget: { resource: 'Widget' }, allow_missing: true }) => ({ name: 'UpsertWidget', request,
    authz: { requirements: [need('UPDATE', 'update', { targetField: 'widget.name' }), need('CREATE', 'create', { condition: 'allow_missing', ...create })] } });
  const guarded = { ...FIXTURE.resources.Widget, fields: { ...FIXTURE.resources.Widget.fields, owner: { guard: need('ADMIN', 'setOwner', { parentTarget: true }) } } };
  for (const [source, fieldGuards, valid] of [
    [{ ...FIXTURE, methods: [...FIXTURE.methods, upsert({ targetField: 'widget.name', parentTarget: true })] }, false, true],
    [{ ...FIXTURE, methods: [...FIXTURE.methods, upsert({ parentTarget: true, serviceRoot: true })] }, false, false],
    [{ ...FIXTURE, methods: [...FIXTURE.methods, upsert({ targetField: 'parent', parentTarget: true },
      { widget: { resource: 'Widget' }, parent: { childType: 'Widget' }, allow_missing: true })] }, false, false],
    [{ ...FIXTURE, resources: { ...FIXTURE.resources, Widget: guarded } }, true, false]
  ]) {
    const model = m.interpret(source, { fieldGuards });
    assert.equal(model.errors.length === 0, valid, JSON.stringify(model.errors));
    compare({ op: 'descriptor', descriptor: c.descriptor(source, model) }, valid);
  }
}
function literalStarCases() {
  const key = 'teams.get', patterns = [['companies', '*', 'teams', '*']];
  const domain = c.domain(patterns), target = id => ['companies', '-', 'teams', id];
  const claim = { key, kind: 'DENY', path: ['companies', 'A', 'teams', 'B'], holes: [] };
  const snapshot = { seq: 1, profile: 'SCOPED_CLAIMS', contexts: [{ anchor: [], claims: [claim] }] };
  const queries = ['*', 'B', '-'].map(id => ({ key, q: target(id), now: 1 }));
  const expected = ['unloaded', 'deny', 'deny'];
  const frame = c.frameState('teams.example', snapshot).history[0];
  const sent = m.snapshotRequestTag(null, 'parity', { service:'teams.example', maxProfile:snapshot.profile });
  const received = m.acceptNextSnapshot(null, { ...snapshot, service:frame.reply.service, subjectContextId:frame.reply.subject,
    snapshotToken:frame.reply.token, descriptorEtag:frame.reply.descriptorEtag, expireTime:frame.reply.expires }, '', {...sent,now:1});
  assert.equal(received.action, 'RESET');
  const results = queries.map(({q,now}) => c.lower(m.evaluate(received.state.snapshots, { [key]: patterns }, key, q, {now}).result));
  assert.deepEqual(results, expected);
  compare({ op: 'trace', service: 'teams.example', session: 'parity', keys: [[key, domain]], resources: domain, queries,
    events: [{ ticket: { session: 'parity', generation: 0, minToken: null, service: 'teams.example', maxProfile: 'scopedClaims' },
      reply: frame.reply, now: 1 }] },
  { actions: [c.lower(received.action)], results, scopes: [], listings: [] });
}

function privateFaultCases() {
  const key = 'teams.get', pattern = ['companies', '*', 'teams', '*'];
  const company = ['companies', 'A'], team = [...company, 'teams', 'B'];
  const domain = c.domain([pattern]), grant = { path: [], effect: 'permit', keys: [key] };
  for (const profile of ['SCOPED_CLAIMS', 'GRANT_SHAPED']) for (const effect of ['permit', 'forbid']) {
    for (const hidden of [true, false]) for (const [site, anchor] of [[company, team], [team, team], [team, company]]) {
      const rules = [grant, { effect, hidden, mayError: true, path: site, keys: [key] }];
      const invisible = hidden ? [] : [site];
      let alerts = 0;
      const options = { profile, canName: p => !invisible.some(x => m.sameName(x, p)), alert: () => alerts++ };
      const claims = m.projectAnchor(rules, key, anchor, [pattern], options);
      assert.equal(claims.length, 0);
      assert.equal(alerts, 1);
      compare({ op: 'project', rules: rules.map(c.rule), key, path: anchor, domain, invisible,
        profile: c.enumName(profile) }, claims.map(c.claim), output => output.claims);
    }
    const sibling = ['companies', 'elsewhere'];
    const rules = [grant, { effect, hidden: true, mayError: true, path: sibling, keys: [key] }];
    const expected = [{ kind: 'allow', key, path: team, holes: [] }];
    const claims = m.projectAnchor(rules, key, team, [pattern], { profile });
    assert.deepEqual(JSON.parse(JSON.stringify(claims.map(c.claim))), expected);
    compare({ op: 'project', rules: rules.map(c.rule), key, path: team, domain, profile: c.enumName(profile) },
      claims.map(c.claim), output => output.claims);
  }
}

function generatedSchema(n) {
  const type = 'differential.example/Item';
  const named = [];
  const count = 2 + rng.int(3);
  for (let branch = 0; branch < count; branch++) {
    const parts = [`groups${branch}`, '{group}'];
    const depth = rng.int(5);
    for (let i = 0; i < depth; i++) parts.push(`levels${rng.int(8)}`, `{v${i}}`);
    parts.push(rng.pick(['items', 'revisions', 'members']));
    if (rng.int(4)) parts.push('{item}');
    named.push(parts.join('/'));
  }
  const resources = { Item: { type, plural: 'items', patterns: named } };
  const methods = [{ name: 'GetItem', authz: { standard: {} }, request: { name: { type: 'Item' } } },
    { name: 'ActOnItem', authz: { requirements: [{ operation: 'act', accessClass: 'UPDATE', explicitGrantOnly: !!(n % 2) }] },
      request: { name: { type: 'Item' } } }];
  return { resources, methods };
}
function generatedCase(n) {
  const raw = generatedSchema(n);
  const I = m.interpret(raw);
  assert.equal(I.errors.length, 0, JSON.stringify(I.errors));
  const d = c.descriptor(raw, I), method = rng.pick(['GetItem', 'ActOnItem']);
  const decl = I.methods[method].requirements[0], key = decl.key, pats = decl.patterns;
  compare({ op: 'descriptor', descriptor: d }, I.errors.length === 0);
  const instantiate = p => p.map(x => x === '*' ? 'v' + rng.int(4) : x);
  const target = instantiate(rng.pick(pats)), path = target.slice(0, 2 * rng.int(1 + Math.floor(target.length / 2)));
  const scopes = [[], path, target, ...pats.map(p => instantiate(p).slice(0, 2 + rng.int(p.length - 1)))];
  const grants = scopes.map(p => ({ scope: p.length && !m.isResourceName(pats, p) ? p.slice(0, -1) : p, selectors: [rng.int(2) ? { type: '*', op: decl.op } : { type: decl.type, cls: decl.cls }],
    effect: rng.int(3) ? 'permit' : 'forbid', condition: rng.pick([undefined, undefined, 'owner', 'unknown']),
    mayError: !rng.int(5), hidden: !rng.int(8), ceiling: rng.pick([undefined, [], ['READ'], [decl.cls]]) }));
  const rs = m.rulesFromGrants(grants, I.keys), rules = rs.map(c.rule);
  compare({ op: 'expand', grant: c.grant(grants[0]), descriptor: d }, rs[0].keys);
  const owner = rng.pick(['alice', 'bob']);
  const predicates = [['owner', owner === 'alice']];
  compare({ op: 'decide', key, path: target, rules, predicates }, c.lower(m.authorize(rs, key, target, { owner })));
  const faults = rs.filter(r => r.mayError && rng.int(2));
  const failedSources = new Set(faults.map(r => r.sourceIndex));
  compare({ op: 'decide', authority: 'skipErrors', key, path: target, rules, predicates, faults: faults.map(c.rule) },
    c.lower(m.authorize(rs, key, target, { owner }, { authority: 'skipErrors',
      faults: rule => failedSources.has(rule.sourceIndex) })));
  const profile = rng.pick(['GRANT_SHAPED', 'SCOPED_CLAIMS']);
  project(rs, key, path, pats, profile, { budget: rng.int(6) });
  const hole = rng.pick(scopes);
  compare({ op: 'region', domain: c.domain(pats), path, holes: [hole] }, m.domainNonEmpty(pats, path, [hole]));
  const hidden = { path: target, keys: [key], effect: 'forbid', hidden: true };
  const privacy = {nonprojecting:true, budget:rng.int(4)};
  twin(project(rs, key, [], pats, profile, privacy), project([...rs, hidden], key, [], pats, profile, privacy));
  const request = { name: target }, opts = { attrsOf: () => ({ owner }) };
  compare({ op: 'authorize', descriptor: d, method, request, rules, knownFacts: true, predicates },
    c.authorization(m.authorizeRequest(rs, I, method, request, opts)));
  const snap = { seq: 1, profile, contexts: [m.projectContext(rs, I.keys, [], { profile })] };
  const keys = Object.fromEntries(Object.values(I.keys).map(k => [k.key, k.patterns]));
  compare({ op: 'methodOffer', descriptor: d, method, request, state: c.frameState(d.service, snap), now: 1 },
    c.lower(m.offer(I, [snap], keys, method, request)));
}

function zeroMatchDefaults() {
  const check = (query, expected, wildcard = false) => {
    const actual = wildcard ? m.wildcardGetStatus(query) : m.zeroMatchStatus(query);
    assert.equal(actual, expected, JSON.stringify(query));
    const wire = structuredClone(query), knowledge = {ALLOW:'allow',DENY:'deny',UNKNOWN:'needsRow'};
    for (const field of ['region','regionList','regionGet','target'])
      if (wire && Object.hasOwn(knowledge, wire[field])) wire[field] = knowledge[wire[field]];
    compare({op:wildcard ? 'wildcardGet' : 'zeroMatch',query:wire},actual);
  };
  const denied = 'PERMISSION_DENIED', missing = 'NOT_FOUND';
  for (const query of [undefined,null,0,'',[]]) {
    check(query,denied);
    check(query,denied,true);
  }
  check(Object.create({region:'ALLOW'}),denied);
  check(Object.assign(Object.create({target:'ALLOW'}),{matches:1}),denied,true);
  const observations = [
    [undefined,undefined,true], [false,undefined,true], [true,undefined,false], [null,undefined,false],
    [0,undefined,false], ['false',undefined,false], [true,false,true], [false,true,false],
    [null,false,true], [null,true,false], [undefined,null,false], [false,null,false],
    [true,null,false], [undefined,0,false], [false,'',false], [false,{},false]
  ];
  for (const [global,local,publiclyKnown] of observations) {
    for (const [region,flag] of [['region','nonprojectingKey'],['regionList','nonprojectingList'],['regionGet','nonprojectingGet']]) {
      const evidence = {[region]:'ALLOW'};
      if (global !== undefined) evidence.nonprojecting = global;
      if (local !== undefined) evidence[flag] = local;
      for (const deleteAllowMissing of [false,true])
        check({...evidence,deleteAllowMissing},publiclyKnown ? (deleteAllowMissing ? 'OK' : missing) : denied);
      const get = {...evidence,matches:0,deleteAllowMissing:true};
      if (region === 'region') { delete get.region; get.regionGet = 'ALLOW'; }
      check(get,publiclyKnown ? missing : denied,true);
    }
  }
  for (const q of [
    {region:'ALLOW',nonprojectingKey:null,regionList:'ALLOW',nonprojectingList:false},
    {region:'DENY',nonprojectingKey:null,regionGet:'ALLOW',nonprojectingGet:false},
    {regionGet:'ALLOW',nonprojectingGet:0,regionList:'ALLOW',nonprojectingList:false}
  ]) check(q,missing);
  for (const regionDenyFinal of [true,null,'false',0])
    check({region:'ALLOW',regionList:'ALLOW',regionDenyFinal},denied);
  check({region:'DENY',regionList:'ALLOW'},denied);
  check({region:'ALLOW',deleteAllowMissing:'true'},missing);
  for (const [generic,get] of [[true,false],[false,true],[null,false],[false,0]]) {
    const q = {matches:0,regionGet:'ALLOW',nonprojectingKey:generic,nonprojectingGet:get};
    check(q,denied,true);
    check({...q,regionList:'ALLOW'},missing,true);
  }
  for (const [matches,target,status] of [[1,'ALLOW','OK'],[1,'DENY',denied],[2,'ALLOW',denied]])
    check({matches,target,nonprojecting:true},status,true);
}

function disclosureCase(n) {
  const val = () => rng.pick(['ALLOW', 'DENY', 'UNKNOWN']);
  const q = { region: val(), regionList: val(), regionGet: val(), nonprojectingKey: !!rng.int(2),
    nonprojectingList: !!rng.int(2), nonprojectingGet: !!rng.int(2), regionDenyFinal: !rng.int(5),
    deleteAllowMissing: !!rng.int(2) };
  const known = s => s === 'UNKNOWN' ? 'needsRow' : c.lower(s);
  compare({ op: 'zeroMatch', query: { ...q, region: known(q.region), regionList: known(q.regionList), regionGet: known(q.regionGet) } },
    m.zeroMatchStatus(q));
  const exists = !!rng.int(2), target = val(), parentList = !!rng.int(2);
  compare({ op: 'read', exists, target: known(target), parentList }, m.readStatus({ exists, target, parentList: parentList ? 'ALLOW' : 'DENY' }));
  const authorized = !!rng.int(2), taken = !!rng.int(2), getExisting = !!rng.int(2);
  compare({ op: 'create', authorized, taken, getExisting, listParent: parentList }, m.createStatus({
    authorized, nameTaken: taken, getExisting: getExisting ? 'ALLOW' : 'DENY', listParent: parentList ? 'ALLOW' : 'DENY' }));
  const name = `users/u${n}@domain/keys/k1`, prefix = name.split('/').slice(0, 2), key = 'keys.get';
  const payload = (r, t) => JSON.parse(m.errorPayload(m.readStatus({ exists: r, target: t }), key, name));
  twin(payload(true, 'DENY'), payload(false, 'UNKNOWN'));
  compare({ op: 'error', key, supplied: name, domain: 'widgets.example', status: 'denied' }, payload(true, 'DENY'));
  const isName = s => m.isResourceName([['users', '*', 'keys', '*']], s.split('/'));
  const lookup = canonical => m.queryAnchors([{ name }], () => canonical, () => false, isName, p => p === prefix.join('/'));
  twin(lookup(null), lookup('users/private'));
  const visible = !!rng.int(2), canonical = rng.int(3) ? ['users', 'u' + rng.int(10)] : null;
  const got = m.queryAnchors([{ name }], () => canonical?.join('/') ?? null, () => visible, isName, p => p === prefix.join('/'));
  compare({ op: 'resolve', resources:c.domain([['users','*','keys','*']]), source: name.split('/'), indirect: [prefix], mappings: [{ supplied: prefix, canonical, visible }] },
    got.anchors.length ? got.anchors[0].split('/') : null);
}

suite = 'evidence accounting';
assert.throws(() => enqueue(undefined, {}, {}), /evidence category/);
const segmentCase = { op: 'segment', value: 'w1' };
compare(segmentCase, m.segmentOk(segmentCase.value));
reject({ op: 'accountingControl' }, 'unknown oracle operation accountingControl');
flush();
assert.deepEqual(accounting().bySuite[suite], { differential: 1, nativeControls: 1, total: 2 });

suite = 'canonical fixture';
fixtureCases();
scopeCases();
serviceNameCases();
parentTargetCases();
literalStarCases();
privateFaultCases();
flush();
suite = 'generated schemas';
const schemas = 2048;
for (let n = 0; n < schemas; n++) generatedCase(n);
suite = 'disclosure';
zeroMatchDefaults();
for (let n = 0; n < 512; n++) disclosureCase(n);
flush();
suite = 'embedded request replay';
const requests = require('./request-cases').requestCases(api, { compare, control }, rng);
flush();
suite = 'complete responses';
const queries = require('./query-cases').queryCases(api, compare, rng);
flush();
suite = 'client traces and offers';
const client = require('../formal-client-cases').runClientCases(api, compare, rng, reject);
flush();
suite = 'resource lookups';
const lookups = require('./lookup-cases').runLookupCases(api, { compare, control }, rng);
flush();
suite = 'policy store traces';
const store = require('./store-cases').storeCases(m, compare, n => rng.int(n), 256);
flush();
console.log(JSON.stringify({ requests, queries, client, lookups, store, seed: '0x' + seed.toString(16), schemas, twinPairs: twins, oracleCases: accounting() }));
