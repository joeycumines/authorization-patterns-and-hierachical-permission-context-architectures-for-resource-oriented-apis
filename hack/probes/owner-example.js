// Alice can create and update widgets and set their owners in company A, except the owner of w1.
const api = require('../load-model.js')(process.argv[2]); const M = api.MODEL, I = M.interpret(api.FIXTURE, { fieldGuards: true }), K = I.keys;
const A = ['companies', 'A'], B = [...A, 'teams', 'B'], w1 = [...B, 'widgets', 'w1'];
const type = api.FIXTURE.resources.Widget.type;
const rules = M.rulesFromGrants([
  { scope: A, selectors: [{ type, cls: 'CREATE' }, { type, cls: 'UPDATE' }, { type, op: 'setOwner' }] },
  { scope: w1, selectors: [{ type, op: 'setOwner' }], effect: 'forbid' }], K);
const dom = Object.fromEntries(Object.values(K).map((k) => [k.key, k.patterns]));
const fmt = (c) => `  ${c.kind.padEnd(6)} ${c.key.padEnd(18)} over ${c.path.join('/')}${c.holes.length ? '   except ' + c.holes.map((h) => h.join('/')).join(', ') : ''}`;
for (const profile of ['GRANT_SHAPED', 'SCOPED_CLAIMS']) {
  const ctx = M.projectContext(rules, K, B, { profile });
  console.log(`\n${profile} context for anchor ${B.join('/')}:`);
  ctx.claims.filter((c) => ['widgets.create', 'widgets.update', 'widgets.setOwner'].includes(c.key)).forEach((c) => console.log(fmt(c)));
  const view = [{ seq: 1, contexts: [ctx] }];
  console.log('  frontend: CreateWidget in team B with an owner  ->', M.offer(I, view, dom, 'CreateWidget', { parent: B, populated: ['owner'] }));
  console.log('  frontend: change the owner of w1                ->', M.offer(I, view, dom, 'UpdateWidget', { 'widget.name': w1, update: { mask: ['owner'] } }));
}
console.log('\nserver: CreateWidget in team B with an owner      ->', M.decideRequest(rules, I, 'CreateWidget', { parent: B, populated: ['owner'] }));
console.log('server: change the owner of w1                    ->', M.decideRequest(rules, I, 'UpdateWidget', { 'widget.name': w1, update: { mask: ['owner'] } }));
