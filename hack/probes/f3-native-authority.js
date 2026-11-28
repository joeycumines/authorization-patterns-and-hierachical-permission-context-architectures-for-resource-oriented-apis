// F3: is fail-closed projection sound against an authority with native Cedar error semantics
// (a policy that errors is skipped, forbids included)? Same 6^3 rule sweep as the [Claims] check,
// but every subset of possibly-erroring rules is tried as "errored this time".
const M = require('../load-model.js')(process.argv[2]).MODEL;
const a = ['companies', 'A'], b = [...a, 'teams', 'B'], c = [...a, 'teams', 'C'], key = 'widgets.get';
const W = ['companies', '*', 'teams', '*', 'widgets', '*'];
const w = [...b, 'widgets', 'w1'], z = [...c, 'widgets', 'z1'], fut = [...a, 'teams', 'future', 'widgets', 'future'];
const PRED = { owner: (x) => x.owner === 'alice' };
const native = (rules, t, attrs, errored) => {
  const live = rules.filter((r) => r.keys.includes(key) && M.prefix(r.path, t) && !errored.has(r));
  const holds = (r) => (!r.pred ? true : PRED[r.pred] ? PRED[r.pred](attrs) : false);
  if (live.some((r) => r.effect === 'forbid' && holds(r))) return 'DENY';
  return live.some((r) => r.effect === 'permit' && holds(r)) ? 'ALLOW' : 'DENY';
};
const KINDS6 = [null, { effect: 'permit' }, { effect: 'forbid' }, { effect: 'permit', pred: 'owner' }, { effect: 'permit', mayError: true }, { effect: 'forbid', mayError: true }];
let cases = 0, withheldButNativeAllows = 0, problems = [];
for (const ar of KINDS6) for (const br of KINDS6) for (const cr of KINDS6) {
  const rules = [[a, ar], [b, br], [c, cr]].filter(([, r]) => r).map(([p, r]) => ({ path: p, keys: [key], ...r }));
  const claims = M.projectAnchor(rules, key, a, [W]);
  const erring = rules.filter((r) => r.mayError);
  for (const t of [w, z, fut]) {
    const got = M.verdict(claims, key, t);
    const outcomes = [];
    for (let mask = 0; mask < 1 << erring.length; mask++) {
      const errored = new Set(erring.filter((_, i) => mask & (1 << i)));
      for (const owner of ['alice', 'bob']) outcomes.push(native(rules, t, { owner }, errored));
    }
    cases++;
    if (got === 'ALLOW' && outcomes.some((x) => x !== 'ALLOW')) problems.push('unsound ALLOW ' + JSON.stringify([ar, br, cr]) + ' ' + t.join('/'));
    if (got === 'DENY' && outcomes.some((x) => x !== 'DENY')) problems.push('unsound DENY ' + JSON.stringify([ar, br, cr]) + ' ' + t.join('/'));
    if (got !== 'ALLOW' && got !== 'DENY' && outcomes.every((x) => x === 'ALLOW')) withheldButNativeAllows++;
  }
}
console.log({ cases, unsound: problems.length, firstProblems: problems.slice(0, 3), withheldWhereNativeAuthorityAlwaysAllows: withheldButNativeAllows });
