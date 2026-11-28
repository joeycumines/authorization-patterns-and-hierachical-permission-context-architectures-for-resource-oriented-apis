const api = require('../load-model.js')(process.argv[2]); const M = api.MODEL, F = api.FIXTURE, I = M.interpret(F), R = api.ROLES;
const need = (accessClass, operation, extra = {}) => ({ accessClass, operation, ...extra });
const A = ['companies', 'A'], B = [...A, 'teams', 'B'], C = [...A, 'teams', 'C'], D = [...A, 'teams', 'D'], w1 = [...B, 'widgets', 'w1'];
const K = I.keys, CAT = (J) => Object.fromEntries(Object.values(J.keys).map((k) => [k.key, k.patterns]));
const grant = (role, scope, extra = {}) => ({ scope, selectors: R[role], ...extra });
const show = (l, v) => console.log(l.padEnd(78), typeof v === 'string' ? v : JSON.stringify(v));
// 1. The newest context for an anchor wins within a single snapshot token.
const meta = { service: I.apiService, descriptorEtag: M.descriptorEtag(I), subjectContextId: 'u', snapshotToken: 's1',
  profile: 'SCOPED_CLAIMS', expireTime: 300 };
const cl = (kind, path) => ({ key: 'widgets.update', kind, path, holes: [] });
show('1 scoped: old ALLOW at w1, refresh says DENY ->', M.evaluate([{ ...meta, seq: 1, contexts: [{ anchor: w1, claims: [cl('ALLOW', w1)] }] }, { ...meta, seq: 2, contexts: [{ anchor: w1, claims: [cl('DENY', w1)] }] }], CAT(I), 'widgets.update', w1, { now: 100 }).result);
show('1 grant-shaped: old ALLOW at w1, refresh says nothing ->', M.evaluate([{ ...meta, seq: 1, profile: 'GRANT_SHAPED', contexts: [{ anchor: w1, claims: [cl('ALLOW', w1)] }] }, { ...meta, seq: 2, profile: 'GRANT_SHAPED', contexts: [{ anchor: w1, claims: [] }] }], CAT(I), 'widgets.update', w1, { now: 100 }).result);
// 2. private conditional rule at the boundary (team level): what the anchor at D and below gets
const W = K['widgets.get'].patterns[0], g0 = { path: A, keys: ['widgets.get'], effect: 'permit' }, hid = { path: D, keys: ['widgets.get'], effect: 'forbid', hidden: true, pred: 'x' }, np = { nonprojecting: (k, an) => an.length < 4 };
show('2 no private rule: claims at anchor D', M.projectAnchor([g0], 'widgets.get', D, [W], np).map((c) => c.kind));
show('2 private conditional forbid at D: claims at anchor D', M.projectAnchor([g0, hid], 'widgets.get', D, [W], np).map((c) => c.kind));
show('2 private conditional forbid at D: claims at anchor D/w4', M.projectAnchor([g0, hid], 'widgets.get', [...D, 'widgets', 'w4'], [W], np).map((c) => c.kind));
// 3.1 wildcard batch parent and a forbid deeper than the parent
const WB = M.interpret({ ...F, methods: F.methods.map((m) => (m.name === 'BatchGetWidgets' ? { ...m, authz: { standard: { wildcardVariables: ['team'] } } } : m)) });
const forbidW1 = M.rulesFromGrants([grant('viewer', A), grant('viewer', w1, { effect: 'forbid' })], WB.keys);
show('3.1 authorize(widgets.get, B/w1) with forbid at w1', M.authorize(forbidW1, 'widgets.get', w1));
show('3.1 BatchGet(parent=A/teams/-, names=[B/w1]) status', M.batchRequestStatus(forbidW1, WB, 'BatchGetWidgets', { parent: [...A, 'teams', '-'], 'names[]': [w1] }));
show('3.1 universal subtree check for wildcard batch parent', M.regionAllowed(forbidW1, 'widgets.get', [...A, 'teams', '-'], WB.keys['widgets.get'].patterns, { subtree: true }));
show('3.1 same, concrete parent B: status', M.batchRequestStatus(forbidW1, WB, 'BatchGetWidgets', { parent: B, 'names[]': [w1] }));
// 3.2 BatchCreate wildcard parent
const WC = M.interpret({ ...F, methods: F.methods.map((m) => (m.name === 'BatchCreateWidgets' ? { ...m, authz: { standard: { wildcardVariables: ['team'] } } } : m)) });
show('3.2 BatchCreate wildcard build errors', WC.errors);
show('3.2 BatchCreate(parent=A/teams/-, item under B) as admin', M.batchRequestStatus(M.rulesFromGrants([grant('admin', A)], WC.keys), WC, 'BatchCreateWidgets', { parent: [...A, 'teams', '-'], 'requests[].parent': [B] }));
// 3.3 One malformed item alongside a bindable item outside the grant.
const editorB = M.rulesFromGrants([grant('editor', B)], K);
show('3.3 requirementsFor BatchGet [C/w1 (bindable), garbage]', M.requirementsFor(I, 'BatchGetWidgets', { parent: B, 'names[]': [[...C, 'widgets', 'w1'], ['bad']] }).map((r) => [r.key, r.targets.length, r.unbound]));
show('3.3 status: editor of B, parent B, items [C/w1, garbage]', M.batchRequestStatus(editorB, I, 'BatchGetWidgets', { parent: B, 'names[]': [[...C, 'widgets', 'w1'], ['bad']] }));
// 3.4 BatchUpdate wildcard + allow_missing
const WU = M.interpret({ ...F, methods: F.methods.map((m) => (m.name === 'BatchUpdateWidgets' ? { ...m, authz: { standard: { wildcardVariables: ['team'] } } } : m)) });
show('3.4 BatchUpdate wildcard: per requirement wildcardVariables', WU.errors.length ? WU.errors : WU.methods.BatchUpdateWidgets.requirements.map((r) => [r.key, r.wildcardVariables]));
// 3.5 item under a concrete parent but not its child (multi-pattern widgets under companies and teams)
const MP = M.interpret({ ...F, resources: { ...F.resources, Widget: { ...F.resources.Widget, patterns: [...F.resources.Widget.patterns, 'companies/{company}/widgets/{widget}'] } } });
show('3.5 BatchGet(parent=A, names=[B/w1]) as admin', M.batchRequestStatus(M.rulesFromGrants([grant('admin', A)], MP.keys), MP, 'BatchGetWidgets', { parent: A, 'names[]': [w1] }));
show('3.5 BatchGet(parent=A/%2E%2E (concrete), names=[]) as admin', M.batchRequestStatus(M.rulesFromGrants([grant('admin', A)], K), I, 'BatchGetWidgets', { parent: ['companies', '%2E%2E'], 'names[]': [] }));
// 5.4 perItem collision
const CC = (authz) => M.descriptorEtag(M.interpret({ ...F, methods: [...F.methods, { name: 'BatchCreateCompanies', authz, request: { requests: { company: { resource: 'Company' } } } }] }));
const x = CC({ standard: {} }), y = CC({ requirements: [need('CREATE', 'create', { serviceRoot: true, resourceType: 'Company' })] });
show('5.4 standard vs requirements BatchCreateCompanies: same descriptor ETag?', x === y);
// 5.5 BatchGet with requests[]
show('5.5 BatchGet with requests[] build errors', M.interpret({ ...F, methods: [...F.methods.filter((m) => m.name !== 'BatchGetWidgets'), { name: 'BatchGetWidgets', authz: { standard: {} }, request: { parent: { childType: 'Widget' }, requests: { name: { type: 'Widget' } } } }] }).errors);
// 5.7 offer order and ceilings
show('5.7 offer InspectAccessPolicy, read-only, no name', M.offer(I, [], CAT(I), 'InspectAccessPolicy', {}, { readOnlyCredential: true }));
show('5.7 offer undeclared method, ceiling [READ] without the flag', M.offer(I, [], CAT(I), 'NoSuchMethod', {}, { ceiling: ['READ'] }));
show('5.7 offer handler policy (UNKNOWN effect), empty ceiling', M.offer(M.interpret({ ...F, methods: [...F.methods, { name: 'PurgeTenant', authz: { handlerPolicy: 'p' }, request: {} }] }), [], CAT(I), 'PurgeTenant', {}, { ceiling: [] }));
// 6.3 The server validates the epoch inside a snapshot floor. Clients treat tokens as opaque.
const server = { authority: 'auth', epoch: 1, seq: 5 };
show('6.3 server floor status for token epochs 0, -1, abc, 1', ['0', '-1', 'abc', '1']
  .map((epoch) => M.serveWithMinSnapshot(server, 'v1:auth:' + epoch + ':1')));
// 6.4 An unimplemented import has no effect to describe.
show('6.4 unimplemented with no_side_effects: build errors', M.interpret({ ...F, imported: [...F.imported.filter((i) => !/CancelOperation/.test(i.method)), { method: 'google.longrunning.Operations/CancelOperation', unimplemented: true, noSideEffects: true }] }).errors);
