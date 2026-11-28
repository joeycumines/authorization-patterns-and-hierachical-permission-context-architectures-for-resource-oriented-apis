const fs = require('fs');
const file = process.argv[2] || require.resolve('../../index.html');
const api = require('../load-model.js')(file); const M = api.MODEL, F = api.FIXTURE, I = M.interpret(F);
const need = (accessClass, operation, extra = {}) => ({ accessClass, operation, ...extra });
const A = ['companies', 'A'], B = [...A, 'teams', 'B'], C = [...A, 'teams', 'C'], w = [...B, 'widgets', 'w1'];
const CAT = (J) => Object.fromEntries(Object.values(J.keys).map((k) => [k.key, k.patterns]));
const show = (l, v) => console.log(l.padEnd(70), typeof v === 'string' ? v : JSON.stringify(v));
const html = fs.readFileSync(file, 'utf8');
show('Figure 2 still lists contract in the namespace?', /one namespace: service, authority, epoch, contract, subject context/.test(html));
// a v2 server adds a parent pattern; a v1 client validates a v2 context
const V2 = M.interpret({ ...F, resources: { ...F.resources, Widget: { ...F.resources.Widget, patterns: [...F.resources.Widget.patterns, 'companies/{company}/widgets/{widget}'] } } });
const rules = M.rulesFromGrants([{ scope: A, selectors: api.ROLES.viewer }, { scope: [...A, 'widgets', 'w9'], selectors: api.ROLES.viewer, effect: 'forbid' }], V2.keys);
const ctx = M.projectContext(rules, V2.keys, A);
show('v1 client validates a v2 context mentioning the new pattern', M.validateContext(ctx, CAT(I)) || 'valid');
// guard patterns when there is no CreateWidget
const guards = { fieldGuards: true };
const NOC = M.interpret({ ...F, methods: F.methods.filter((m) => !['CreateWidget', 'BatchCreateWidgets', 'MoveWidget'].includes(m.name)) }, guards);
show('setOwner patterns with Update(allow_missing) but no Create', [...NOC.keys['widgets.setOwner'].named]);
const withField = (fields) => M.interpret({
  ...F, resources: { ...F.resources, Widget: { ...F.resources.Widget, fields: { ...F.resources.Widget.fields, ...fields } } }
}, guards);
show('guard with an invalid operation, build errors', withField({ tag: { guard: need('ADMIN', 'Not Camel') } }).errors);
show('guard with no operation, build errors', withField({ tag: { guard: { accessClass: 'ADMIN' } } }).errors);
show('guard reachable only inside an output-only message, build errors', withField({
  meta: { outputOnly: true }, 'meta.owner': { guard: need('ADMIN', 'setMetaOwner') }
}).errors);
const MAP = withField({ items: {}, 'items.*.owner': { guard: need('ADMIN', 'setItemOwner') } });
show('map entry: mask items.foo.owner triggers the items.*.owner guard?', M.requirementsFor(MAP, 'UpdateWidget', { 'widget.name': w, update: { mask: ['items.foo.owner'] } }).some((r) => r.key === 'widgets.setItemOwner'));
show('usableAt for a holed ALLOW over company A', M.usableAt([{ key: 'widgets.get', kind: 'ALLOW', path: A, holes: [C] }], 'widgets.get'));
let crash = 'no crash'; try { M.validateContext({ anchor: A, claims: [{ key: 'toString', kind: 'ALLOW', path: A, holes: [] }, { key: 'toString', kind: 'DENY', path: B, holes: [] }] }, CAT(I)); } catch (e) { crash = 'THROWS: ' + e.message; }
show('validateContext with a key named toString', crash);
show('two resource types with the same plural accepted?', M.interpret({ ...F, resources: { ...F.resources, Gizmo: { plural: 'widgets', patterns: ['gizmos/{gizmo}'] } }, methods: [...F.methods, { name: 'GetGizmo', authz: { standard: {} }, request: { name: { type: 'Gizmo' } } }] }).errors);
show('target expanding two repeated fields accepted?', M.interpret({ ...F, methods: [...F.methods, { name: 'TagAll', authz: { requirements: [need('UPDATE', 'tag', { targetField: 'groups[].names[]' })] }, request: { groups: { names: { type: 'Widget' } } } }] }).errors);
const RC = M.interpret({ ...F, methods: [...F.methods, { name: 'ArchiveWidget', authz: { requirements: [need('UPDATE', 'archive'), need('DELETE', 'purge', { condition: 'requests[].purge' })] }, request: { name: { type: 'Widget' }, requests: { purge: true } } }] });
show('requests[] condition on a non-batch method: build errors / applied without flag', [RC.errors, RC.methods.ArchiveWidget && M.requirementsFor(RC, 'ArchiveWidget', { name: w }).map((r) => r.key)]);
let alerted = false; M.regionAllowed(M.rulesFromGrants([{ scope: A, selectors: api.ROLES.viewer }, { scope: C, selectors: api.ROLES.viewer, effect: 'forbid', hidden: true }], I.keys), 'widgets.list', [...A, 'teams', '-'], I.keys['widgets.list'].patterns, { alert: () => { alerted = true; } });
show("regionAllowed passes the caller's alert through?", alerted);
const ro = { readOnlyCredential: true };
show('offer() for an undeclared method on a read-only credential', M.offer(I, [], {}, 'NoSuchMethod', {}, ro));
