// Which dangerous or meaningless declarations does the build accept today?
const api = require('../load-model.js')(process.argv[2]); const M = api.MODEL, F = api.FIXTURE;
const need = (accessClass, operation, extra = {}) => ({ accessClass, operation, ...extra });
const add = (...ms) => M.interpret({ ...F, methods: [...F.methods, ...ms] }).errors;
const swap = (name, patch) => M.interpret({ ...F, methods: F.methods.map((m) => (m.name === name ? { ...m, ...patch } : m)) }).errors;
const res = (type, patch) => M.interpret({ ...F, resources: { ...F.resources, [type]: { ...F.resources[type], ...patch } } }, { fieldGuards: true }).errors;
const rows = {
  'wildcard_variables on CreateWidget': swap('CreateWidget', { authz: { standard: { wildcardVariables: ['team'] } } }),
  'wildcard_variables on DeleteWidget': swap('DeleteWidget', { authz: { standard: { wildcardVariables: ['team'] } } }),
  'BatchListWidgets declared standard': add({ name: 'BatchListWidgets', authz: { standard: {} }, request: { parent: { childType: 'Widget' } } }),
  'a resource whose plural is "service"': M.interpret({ ...F, resources: { ...F.resources, Gadget: { type: 'widgets.example/Gadget', plural: 'service', patterns: ['gadgets/{gadget}'] } }, methods: [...F.methods, { name: 'GetGadget', authz: { standard: {} }, request: { name: { type: 'Gadget' } } }, { name: 'AuditService', authz: { requirements: [need('ADMIN', 'get', { serviceRoot: true })] }, request: {} }] }).errors,
  'every requirement conditional': add({ name: 'PokeWidget', authz: { requirements: [need('EXECUTE', 'poke', { condition: 'force' })] }, request: { name: { type: 'Widget' }, force: true } }),
  'condition naming a field that does not exist': add({ name: 'NudgeWidget', authz: { requirements: [need('EXECUTE', 'nudge'), need('ADMIN', 'override', { condition: 'no_such_flag' })] }, request: { name: { type: 'Widget' } } }),
  'item_filter naming a create operation': swap('SearchWidgets', { authz: { ...F.methods.find((m) => m.name === 'SearchWidgets').authz, itemFilter: 'create' } }),
  'field guard on an output-only field': res('Widget', { fields: { ...F.resources.Widget.fields, create_time: { outputOnly: true, guard: need('ADMIN', 'stamp') } } }),
  'the same imported method listed twice': M.interpret({ ...F, imported: [...F.imported, F.imported[0]] }).errors,
  'custom requirement targeting widget.name (nested path)': add({ name: 'TagWidget', authz: { requirements: [need('UPDATE', 'tag', { targetField: 'widget.name' })] }, request: { widget: { resource: 'Widget' } } }),
};
for (const [k, v] of Object.entries(rows)) console.log(k.padEnd(56), v.length ? 'REJECTED: ' + v.join('; ').slice(0, 90) : 'accepted');
