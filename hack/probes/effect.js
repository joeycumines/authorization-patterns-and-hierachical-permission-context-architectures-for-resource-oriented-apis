const { MODEL: M, FIXTURE } = require('../load-model.js')(process.argv[2]);

function withMethod(name, accessClass, operation, noSideEffects) {
  const method = {
    name, noSideEffects,
    authz: { requirements: [{ accessClass, operation }] },
    request: { name: { type: 'Widget' } }
  };
  return M.interpret({ ...FIXTURE, methods: [...FIXTURE.methods, method] });
}

const base = M.interpret(FIXTURE);
const purge = withMethod('PurgeWidget', 'DELETE', 'purge', false);
const cases = [
  ['DELETE + no_side_effects', 'PurgeWidget', withMethod('PurgeWidget', 'DELETE', 'purge', true)],
  ['EXECUTE + no_side_effects', 'PublishWidget', withMethod('PublishWidget', 'EXECUTE', 'publish', true)],
  ['ADMIN + no_side_effects', 'InspectAccessPolicy', base],
  ['handler policy + no_side_effects', 'google.longrunning.Operations/GetOperation', base],
  ['DELETE', 'PurgeWidget', purge]
];
for (const [label, name, model] of cases) {
  const method = model.methods[name];
  console.log(label, name, method ? method.effect : model.errors);
}

const readOnly = { readOnlyCredential: true };
const widget = ['companies', 'A', 'teams', 'B', 'widgets', 'w1'];
console.log('read-only credential, GetOperation', M.offerDetailed(base, [], {}, 'google.longrunning.Operations/GetOperation', {}, readOnly));
console.log('read-only credential, PurgeWidget', M.offerDetailed(purge, [], {}, 'PurgeWidget', { name: widget }, readOnly));
