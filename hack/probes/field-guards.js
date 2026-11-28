// Field guards: which review claims hold in the model?
const api = require('../load-model.js')(process.argv[2]); const M = api.MODEL, F = api.FIXTURE, I = M.interpret(F, { fieldGuards: true }), K = I.keys;
const a = ['companies', 'A'], b = [...a, 'teams', 'B'], w1 = [...b, 'widgets', 'w1'], w2 = [...b, 'widgets', 'w2'];
const show = (l, v) => console.log(l.padEnd(70), JSON.stringify(v));
const sel = (cls, op) => [{ type: F.resources.Widget.type, ...(op ? { op } : { cls }) }];
const rules = (gs) => M.rulesFromGrants(gs.map(([s, selectors, effect]) => ({ scope: s, selectors, effect: effect || 'permit' })), K);
const domains = Object.fromEntries(Object.values(K).map((key) => [key.key, key.patterns]));
show('guard key binding patterns', K['widgets.setOwner'].patterns.map((p) => p.join('/')));
// Compare the proof for a team-level Create when an individual widget has a setOwner forbid.
const R1 = rules([[a, [{ type: '*', cls: 'ADMIN' }, ...sel('CREATE')]], [w1, sel(null, 'setOwner'), 'forbid']]);
const createOwner = { parent: b, populated: ['owner'] };
show('server: CreateWidget(parent=B, owner) with setOwner forbid at w1', M.decideRequest(R1, I, 'CreateWidget', createOwner));
for (const anchor of [[], a, b]) for (const profile of ['GRANT_SHAPED', 'SCOPED_CLAIMS']) {
  const view = [{ seq: 1, contexts: [M.projectContext(R1, K, anchor, { profile })] }];
  show(`  client verdict at anchor ${anchor.join('/') || '(root)'} ${profile}`, M.offer(I, view, domains, 'CreateWidget', createOwner));
}
// 2. Upsert vs Create: holds create on B, update + setOwner only on w1.
const R2 = rules([[b, sel('CREATE')], [w1, sel('UPDATE')], [w1, sel(null, 'setOwner')]]);
show('upsert UpdateWidget(w1, allow_missing, owner)', M.decideRequest(R2, I, 'UpdateWidget', { 'widget.name': w1, allow_missing: true, update: { populated: ['owner'] } }));
show('CreateWidget(parent=B, owner) for the same caller', M.decideRequest(R2, I, 'CreateWidget', { parent: b, populated: ['owner'] }));
// 3. Batch: item 1 writes owner, item 2 does not. Which targets get the guard?
const bt = M.requirementsFor(I, 'BatchUpdateWidgets', {
  'requests[].widget.name': [w1, w2],
  'requests[].update': [{ mask: ['owner'] }, { mask: ['display_name'] }]
});
show('batch guard targets when only w1 writes owner', bt.filter((r) => r.key === 'widgets.setOwner').flatMap((r) => r.targets.map((t) => t.join('/'))));
// 4. Empty mask, '*' mask, nested output-only, Create output-only
show('effectiveMask(empty mask)', M.effectiveMask({ mask: [], populated: ['owner'] }, F.resources.Widget.fields));
show('effectiveMask(* mask)', M.effectiveMask({ mask: ['*'] }, F.resources.Widget.fields));
show('effectiveMask(nested output-only meta.create_time)', M.effectiveMask({ mask: ['meta.create_time'], populated: [] }, { meta: {}, 'meta.create_time': { outputOnly: true } }));
show('Create populating an output-only field: required keys', M.requirementsFor(I, 'CreateWidget', { parent: b, populated: ['create_time'] }).map((r) => r.key));
