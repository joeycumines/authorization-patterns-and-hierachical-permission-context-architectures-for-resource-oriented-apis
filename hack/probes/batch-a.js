const api = require('../load-model.js')(process.argv[2]); const M = api.MODEL, I = M.interpret(api.FIXTURE), K = I.keys;
const CAT = Object.fromEntries(Object.values(K).map((k) => [k.key, k.patterns]));
const A = ['companies', 'A'], B = [...A, 'teams', 'B'], C = [...A, 'teams', 'C'];
const show = (l, v) => console.log(l.padEnd(66), JSON.stringify(v));
// Names: does the client accept odd segments in contexts?
for (const seg of ['..', '.', '', '%2E%2E', '-', 'a/b'])
  show(`context anchored at companies/A/teams/${JSON.stringify(seg)} accepted?`, M.validateContext({ anchor: [...A, 'teams', seg], claims: [{ key: 'widgets.get', kind: 'ALLOW', path: [...A, 'teams', seg], holes: [] }] }, CAT) === null);
show('server binds GetWidget(companies/A/teams/%2E%2E/widgets/w1)?', M.requirementsFor(I, 'GetWidget', { name: [...A, 'teams', '%2E%2E', 'widgets', 'w1'] }).map((r) => !r.unbound));
// Grant-shaped merge: viewer at A and at Team B, forbid on reads at Team C.
const rules = M.rulesFromGrants([{ scope: A, selectors: api.ROLES.viewer }, { scope: B, selectors: api.ROLES.viewer }, { scope: C, selectors: api.ROLES.viewer, effect: 'forbid' }], K);
show('grant-shaped root context, widgets.get claims', M.projectContext(rules, K, [], { profile: 'GRANT_SHAPED' }).claims.filter((c) => c.key === 'widgets.get').map((c) => c.path.join('/')));
show('scoped-claims root context, widgets.get claims', M.projectContext(rules, K, []).claims.filter((c) => c.key === 'widgets.get').map((c) => [c.kind, c.path.join('/') || '(root)', c.holes.map((h) => h.join('/'))]));
// DENY claims with holes exist, so budget truncation must cover them too.
const r2 = M.rulesFromGrants([{ scope: B, selectors: api.ROLES.viewer }], K);
show('Team-B-only viewer, root context for widgets.get', M.projectContext(r2, K, []).claims.filter((c) => c.key === 'widgets.get').map((c) => [c.kind, c.path.join('/') || '(root)', c.holes.map((h) => h.join('/'))]));
