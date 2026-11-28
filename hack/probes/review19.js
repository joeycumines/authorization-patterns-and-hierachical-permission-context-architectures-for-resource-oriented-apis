const api = require('../load-model.js')(process.argv[2]); const M = api.MODEL, F = api.FIXTURE, R = api.ROLES;
const show = (l, v) => console.log(l.padEnd(80), typeof v === 'string' ? v : JSON.stringify(v));
const A = ['companies', 'A'], B = [...A, 'teams', 'B'], C = [...A, 'teams', 'C'], w1 = [...B, 'widgets', 'w1'];
// 1. widgets under companies and under teams; viewer at the root, forbid at Team C; list widgets of every company
const MP = M.interpret({ ...F, resources: { ...F.resources, Widget: { ...F.resources.Widget, patterns: [...F.resources.Widget.patterns, 'companies/{company}/widgets/{widget}'] } } });
const rules = M.rulesFromGrants([{ scope: [], selectors: R.viewer }, { scope: C, selectors: R.viewer, effect: 'forbid' }], MP.keys);
const q = ['companies', '-'], pats = MP.keys['widgets.list'].patterns;
show('1 widgets.list patterns', pats.map((p) => p.join('/')));
show('1 decide widgets.list on companies/A (a parent the wildcard matches)', M.authorize(rules, 'widgets.list', A));
show('1 regionAllowed(widgets.list, companies/-)', M.regionAllowed(rules, 'widgets.list', q, pats));
const claims = M.projectAnchor(rules, 'widgets.list', [], pats);
show('1 client verdict for companies/-', M.verdictWildcard(claims, 'widgets.list', q));
// 2. A row-dependent rule stays conditional at the widget as well as its team.
const I = M.interpret(F);
const cat = Object.fromEntries(Object.values(I.keys).map((k) => [k.key, k.patterns]));
const ownerRules = [{ path: B, keys: ['widgets.update'], effect: 'permit', pred: 'owner' }];
const contexts = [B, w1].map((anchor) => M.projectContext(ownerRules, I.keys, anchor));
const response = { service: I.apiService, descriptorEtag: M.descriptorEtag(I), subjectContextId: 'u',
  profile: 'SCOPED_CLAIMS', expireTime: 500, contexts };
const oldToken = M.encodeSnapshotToken({ authority: 'a1', epoch: 1, seq: 10 });
const cold = M.snapshotRequestTag(null, 'probe', { service: I.apiService, maxProfile: 'SCOPED_CLAIMS' });
const first = M.acceptNextSnapshot(null, { ...response, snapshotToken: oldToken }, cold.sentMinToken, { ...cold, now: 100 });
show('2 owner-only update under team and widget contexts', M.evaluate(first.state.snapshots, cat, 'widgets.update', w1, { now: 100 }).result);

// 3. The server checks the floor. The client compares opaque tokens across authorities.
const newAuthority = { authority: 'a2', epoch: 1, seq: 2 };
const next = { ...response, snapshotToken: M.encodeSnapshotToken(newAuthority) };
show('3 server receives a floor issued by another authority', M.serveWithMinSnapshot(newAuthority, oldToken));
const current = M.snapshotRequestTag(first.state, 'probe', { maxProfile: 'SCOPED_CLAIMS' });
show('3 client receives the reply sent with its current floor', M.acceptNextSnapshot(first.state, next, current.sentMinToken, { ...current, now: 100 }).action);
show('3 client receives an older in-flight request without that floor', M.acceptNextSnapshot(first.state, next, cold.sentMinToken, { ...cold, now: 100 }).reason);
// minor: requested anchor with a bad segment
show('m3 decodeResponse with one malformed requested anchor', M.decodeResponse({ keySets: [], contexts: [{ anchor: A, requestedAnchors: [['users', '..']], claims: [] }, { anchor: B, requestedAnchors: [B], claims: [] }] }));
