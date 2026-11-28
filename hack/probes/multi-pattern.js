// Compare wildcard binding in the team and company patterns for Widget.
const api = require('../load-model.js')(process.argv[2]); const M = api.MODEL, F = api.FIXTURE;
const MP = { ...F, resources: { ...F.resources, Widget: { ...F.resources.Widget, patterns: [...F.resources.Widget.patterns, 'companies/{company}/widgets/{widget}'] } },
  methods: F.methods.map((m) => (m.name === 'GetWidget' ? { ...m, authz: { standard: { wildcardVariables: ['team'] } } } : m)) };
const I = M.interpret(MP);
console.log('build errors                          ', JSON.stringify(I.errors));
console.log('widgets.get binding patterns (named)  ', JSON.stringify(I.keys['widgets.get'].named));
const r = M.requirementsFor(I, 'GetWidget', { name: ['companies', 'A', 'widgets', '-'] });
console.log("GetWidget(companies/A/widgets/-)      ", JSON.stringify(r.map((x) => ({ key: x.key, unbound: x.unbound, wildcard: x.wildcard }))));
const ok = M.requirementsFor(I, 'GetWidget', { name: ['companies', 'A', 'teams', '-', 'widgets', 'w1'] });
console.log("GetWidget(companies/A/teams/-/widgets/w1)", JSON.stringify(ok.map((x) => ({ unbound: x.unbound, wildcard: x.wildcard }))));
