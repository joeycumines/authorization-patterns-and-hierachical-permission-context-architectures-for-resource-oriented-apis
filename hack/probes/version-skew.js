// Compare client offers during a descriptor refresh with enforcement by the serving version.
const api = require('../load-model.js')(process.argv[2]); const M = api.MODEL, F = api.FIXTURE;
const need = (accessClass, operation, extra = {}) => ({ accessClass, operation, ...extra });
const a = ['companies', 'A'], b = [...a, 'teams', 'B'], w1 = [...b, 'widgets', 'w1'];
const dom = (I) => Object.fromEntries(Object.entries(I.keys).map(([k, v]) => [k, v.patterns]));
const swap = (name, authz) => ({ ...F, methods: F.methods.map((m) => (m.name === name ? { ...m, authz } : m)) });
const cases = {
  'new unrelated method (ExportWidgets)': [{ ...F, methods: [...F.methods, { name: 'ExportWidgets', authz: { requirements: [need('READ', 'export')] }, request: { parent: { childType: 'Widget' } } }] }, 'GetWidget', { name: w1 }, 'viewer', a],
  'CreateWidget gains an approve requirement': [swap('CreateWidget', { requirements: [need('CREATE', 'create', { targetField: 'parent' }), need('ADMIN', 'approve', { targetField: 'parent' })] }), 'CreateWidget', { parent: b, populated: [] }, 'editor', a],
  'widgets.count reclassified READ -> ADMIN': [swap('CountWidgets', { requirements: [need('ADMIN', 'count')] }), 'CountWidgets', { parent: b }, 'viewer', a],
  'MoveWidget drops its delete requirement': [swap('MoveWidget', { requirements: [need('CREATE', 'create', { targetField: 'destination_parent' })] }), 'MoveWidget', { name: w1, destination_parent: [...a, 'teams', 'D'] }, 'widget-writer', b],
};
const OLD = M.interpret(F);
for (const [label, [desc, method, req, role, scope]] of Object.entries(cases)) {
  const NEW = M.interpret(desc);
  if (NEW.errors.length) throw Error(label + ' — ' + NEW.errors.join(', '));
  for (const [clientI, serverI, who] of [[OLD, NEW, 'old client / new server'], [NEW, OLD, 'new client / old server']]) {
    const grants = [{ scope, selectors: api.ROLES[role] }, ...(role === 'widget-writer' ? [{ scope: [...a, 'teams', 'D'], selectors: api.ROLES[role] }] : [])];
    const rules = M.rulesFromGrants(grants, serverI.keys);
    const response = { service: serverI.apiService, descriptorEtag: M.descriptorEtag(serverI), subjectContextId: 'u',
      snapshotToken: 's1', expireTime: 500, profile: 'SCOPED_CLAIMS', contexts: [M.projectContext(rules, serverI.keys, a)] };
    const client = { service: clientI.apiService, loadedDescriptorEtag: M.descriptorEtag(clientI) };
    const ticket = M.snapshotRequestTag(client, 'probe', { service: client.service, maxProfile: 'SCOPED_CLAIMS' });
    const received = M.acceptNextSnapshot(client, response, ticket.sentMinToken, { ...ticket, now: 100 });
    const offer = (model) => M.offer(model, received.state.snapshots, dom(model), method, req, { now: 100 });
    const server = M.decideRequest(rules, serverI, method, req);
    console.log(label.padEnd(44), who.padEnd(24), 'refresh requested', received.refreshDescriptors,
      ' offer before refresh', offer(clientI), ' after refresh', offer(serverI), ' server', server);
  }
}
