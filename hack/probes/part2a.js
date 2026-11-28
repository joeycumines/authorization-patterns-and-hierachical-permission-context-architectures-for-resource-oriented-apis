// Descriptor evolution, batch conditions and role reach.
const { MODEL: M, FIXTURE: F, ROLES } = require('../load-model.js')(process.argv[2]);
const I = M.interpret(F);
const show = (label, value) => console.log(label.padEnd(62), JSON.stringify(value));
const a = ['companies', 'A'], b = [...a, 'teams', 'B'], w1 = [...b, 'widgets', 'w1'];
const add = (method) => M.interpret({ ...F, methods: [...F.methods, method] });
const change = (name, edit) => M.interpret({ ...F, methods: F.methods.map((m) => m.name === name ? edit(m) : m) });
const domains = Object.fromEntries(Object.values(I.keys).map((k) => [k.key, k.patterns]));
const etag = M.descriptorEtag(I);

const next = add({ name: 'ExportWidgets', authz: { requirements: [{ accessClass: 'READ', operation: 'export' }] }, request: { parent: { childType: 'Widget' } } });
show('C1 additive RPC changes descriptor ETag', M.descriptorEtag(next) !== etag);
for (const [label, server] of [['v1', I], ['v2', next]]) {
  const rules = M.rulesFromGrants([{ scope: a, selectors: ROLES.viewer }], server.keys);
  const response = { service: server.apiService, descriptorEtag: M.descriptorEtag(server), subjectContextId: 'u',
    snapshotToken: 's1', profile: 'SCOPED_CLAIMS', expireTime: 500, contexts: [M.projectContext(rules, server.keys, a)] };
  const client = { service: I.apiService, loadedDescriptorEtag: etag };
  const ticket = M.snapshotRequestTag(client, 'probe', { service: client.service, maxProfile: 'SCOPED_CLAIMS' });
  const received = M.acceptNextSnapshot(client, response, ticket.sentMinToken, { ...ticket, now: 100 });
  show('C1 v1 client, ' + label + ' server', {
    refreshDescriptors: received.refreshDescriptors,
    getWidget: M.offer(I, received.state.snapshots, domains, 'GetWidget', { name: w1 }, { now: 100 })
  });
}

const hoisted = change('BatchUpdateWidgets', (m) => ({ ...m, request: { ...m.request, allow_missing: true } }));
show('C2 hoisting allow_missing changes descriptor ETag', M.descriptorEtag(hoisted) !== etag);
for (const [label, model] of [['item only', I], ['hoisted', hoisted]]) {
  const request = { 'requests[].widget.name': [w1, [...b, 'widgets', 'w2']], allow_missing: true };
  show('C2 top-level allow_missing with ' + label + ' declaration',
    M.requirementsFor(model, 'BatchUpdateWidgets', request).map((r) => [r.key, r.items]));
}
const fields = { ...F.resources.Widget.fields, label: { guard: { accessClass: 'UPDATE', operation: 'setLabel' } } };
const guardedEtag = (fields) => M.descriptorEtag(M.interpret({
  ...F, resources: { ...F.resources, Widget: { ...F.resources.Widget, fields } }
}, { fieldGuards: true }));
show('C2 reordering guard declarations preserves descriptor ETag',
  guardedEtag(fields) === guardedEtag(Object.fromEntries(Object.entries(fields).reverse())));
const reordered = change('MoveWidget', (m) => ({ ...m, authz: { requirements: [...m.authz.requirements].reverse() } }));
show('C3 reversing MoveWidget requirements changes descriptor ETag', M.descriptorEtag(reordered) !== etag);

// Inspect the interpretation directly. The ETag itself is opaque.
show('C4.1 local and imported method names', Object.keys(I.methods).filter((n) => n === 'GetWidget' || n.includes('/')));
show('C4.2/5 list key', I.keys['widgets.list']);
show('C4.3 service-root key', I.keys['service.exportAuditLog']);
show('C4.5 UpdateWidget create requirement', I.methods.UpdateWidget.requirements.find((r) => r.parentOf));
const guarded = M.interpret(F, { fieldGuards: true });
show('C4.6 UpdateWidget guards when enabled', guarded.methods.UpdateWidget.fieldGuards);

const audit = add({ name: 'AuditTeams', authz: { requirements: [{ accessClass: 'CREATE', operation: 'audit' }] }, request: { parent: { childType: 'Team' } } });
show('VI editor role gains', M.capabilityDiff(I.keys, audit.keys, ROLES).editor.gained);
show('VI editor grant at Team B reaches teams.audit', M.keysFor({ scope: b, selectors: ROLES.editor }, audit.keys).includes('teams.audit'));
