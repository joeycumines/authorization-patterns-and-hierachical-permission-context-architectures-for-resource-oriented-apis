const file = process.argv[2] || require.resolve('../../index.html');
const api = require('../load-model.js')(file); const M = api.MODEL, I = M.interpret(api.FIXTURE), K = I.keys;
const A = ['companies', 'A'], B = [...A, 'teams', 'B'], C = [...A, 'teams', 'C'], w1 = [...B, 'widgets', 'w1'];
const show = (l, v) => console.log(l.padEnd(72), JSON.stringify(v));
const fmt = (cs) => cs.map((c) => [c.kind, c.path.join('/'), c.holes.map((h) => h.join('/'))]);
const V = api.ROLES.viewer;
// Privacy boundary at Team level for widget reads; a private forbid on ONE widget (below the boundary)
const np = { nonprojecting: (k, an) => ['widgets.get'].includes(k) && an.length < 4 };
for (const hidden of [false, true]) {
  const rules = M.rulesFromGrants([{ scope: A, selectors: V }, ...(hidden ? [{ scope: w1, selectors: V, effect: 'forbid', hidden: true }] : [])], K);
  show(`boundary at Team, private forbid on w1 ${hidden ? 'PRESENT' : 'absent '} -> context at Team B`, fmt(M.projectAnchor(rules, 'widgets.get', B, K['widgets.get'].patterns, np)));
}
// Settings singleton: verdictRegion with a domain-empty DENY claim
const S = K['settings.get'].patterns;
show('verdictRegion(settings.get over Team B) with DENY at B minus hole B/settings', M.verdictRegion([{ key: 'settings.get', kind: 'DENY', path: B, holes: [[...B, 'settings']] }, { key: 'settings.get', kind: 'ALLOW', path: [...B, 'settings'], holes: [] }], 'settings.get', B, S));
// acceptPrivateRule: a hidden permit below; who is protected?
show('acceptPrivateRule(hidden permit at Team B; audience = a holder of a broader claim)', M.acceptPrivateRule({ key: 'widgets.get', path: B }, [{ key: 'widgets.get', path: A, holder: 'alice' }], () => false));
show('acceptPrivateRule(hidden permit at Team B; audience = nobody holds a broader grant)', M.acceptPrivateRule({ key: 'widgets.get', path: B }, [], () => false));
show('is acceptPrivateRule called anywhere outside checks?', /acceptPrivateRule\(/.test(require('node:fs').readFileSync(file, 'utf8').split('function checks(M)')[0].split('function acceptPrivateRule')[1].slice(200)));
// queryAnchors: canonical name when the caller cannot see it
show('queryAnchors(canonical companies/A, canSee false)', M.queryAnchors([{ name: 'companies/A' }], (s) => s.name, () => false, name => M.isResourceName(Object.values(K).flatMap(k => k.patterns), name.split('/'))));
