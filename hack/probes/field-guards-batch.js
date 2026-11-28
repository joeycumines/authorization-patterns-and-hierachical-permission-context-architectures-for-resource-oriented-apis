const { MODEL: M, FIXTURE } = require('../load-model.js')(process.argv[2]);
const fields = {
  ...FIXTURE.resources.Widget.fields,
  items: {},
  'items.*.owner': { guard: { accessClass: 'ADMIN', operation: 'setItemOwner' } }
};
const I = M.interpret({
  ...FIXTURE,
  resources: { ...FIXTURE.resources, Widget: { ...FIXTURE.resources.Widget, fields } }
}, { fieldGuards: true });
if (I.errors.length) throw new Error(I.errors.join('\n'));

const b = ['companies', 'A', 'teams', 'B'], w1 = [...b, 'widgets', 'w1'], w2 = [...b, 'widgets', 'w2'];

function reportOwners(label, method, request) {
  const requirements = M.requirementsFor(I, method, request);
  const owners = requirements.filter((r) => r.key === 'widgets.setOwner').flatMap((r) =>
    Array.from(r.itemTargets, ([item, paths]) => ({ item, targets: paths.map((path) => path.join('/')) })));
  console.log(label, JSON.stringify(owners));
}

reportOwners('per-item masks, owner only on item 0', 'BatchUpdateWidgets', {
  'requests[].widget.name': [w1, w2],
  'requests[].update': [{ mask: ['owner'] }, { mask: ['display_name'] }]
});
reportOwners('per-item upsert, owner populated on item 1', 'BatchUpdateWidgets', {
  'requests[].widget.name': [w1, w2],
  'requests[].allow_missing': [false, true],
  'requests[].update': [
    { mask: ['display_name'], populated: ['display_name'] },
    { mask: ['display_name'], populated: ['owner'] }
  ]
});
reportOwners('batch create, owner only on item 1', 'BatchCreateWidgets', {
  parent: b,
  'requests[].parent': [b, b],
  'requests[].populated': [['display_name'], ['owner']]
});
console.log('mask with * segment items.*.owner', M.requirementsFor(I, 'UpdateWidget', {
  'widget.name': w1, update: { mask: ['items.*.owner'] }
}).map((r) => r.key));
