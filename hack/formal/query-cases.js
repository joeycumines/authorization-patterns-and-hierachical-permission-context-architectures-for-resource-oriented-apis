'use strict';
const assert = require('node:assert/strict');
const codec = require('./codec');

function queryCases(api, compare, rng) {
  const { MODEL: m, FIXTURE } = api;
  const I = m.interpret(FIXTURE);
  const { A, B, D } = api.simulatorFixtures();
  const keys = { 'widgets.get': I.keys['widgets.get'], 'teams.get': I.keys['teams.get'] };
  const hierarchy = Object.values(FIXTURE.resources).flatMap(r => r.patterns.map(codec.namedPattern));
  const patterns = Object.values(I.keys).flatMap(k => k.patterns);
  const stamp = { service: I.apiService, subject: 'alice', etag: 'fixture', snapshotToken: 'revision', expireTime: 100 };
  let fullResponses = 0;
  function checkQuery({ asked, catalog = I.resourcePatterns, selected = {}, rules = [], subject = stamp.subject,
    profile = 'SCOPED_CLAIMS', mappings = [], ownedAliases = [], readableTargets, types,
    budget, privateKeys = [], boundaryDepth = 0, nameVisibility, adapter }) {
    const reads = readableTargets ?? mappings.filter(row => row.visible && row.canonical)
      .map(row => ({subject, target: row.canonical}));
    const find = name => mappings.find(row => row.supplied.join('/') === name);
    const view = { ...I, keys: selected, resourcePatterns: catalog };
    const snapshot = { descriptorEtag: stamp.etag, subjectContextId: subject, snapshotToken: stamp.snapshotToken, expireTime: stamp.expireTime };
    const request = { service: stamp.service, maxProfile: profile,
      anchors: asked.map(path => path.length ? {resource: path.join('/')} : {serviceRoot: {}}) };
    const result = m.queryPermissionContexts(rules, view, request, snapshot, {
      budget, asWrittenTypes: types, canName: adapter,
      nonprojecting: (key, anchor) => privateKeys.includes(key) && anchor.length < boundaryDepth,
      isIndirect: name => !!find(name), resolve: ({name}) => find(name)?.canonical?.join('/'),
      ownsAlias: (who, supplied, target) => ownedAliases.some(row =>
        row.subject === who && row.supplied.join('/') === supplied && row.target.join('/') === target),
      canReadNow: (who, name) => reads.some(row => row.subject === who && row.target.join('/') === name)
    });
    compare({ op: 'query', protoJson: true, asked, resources: codec.domain(catalog),
      keys: Object.entries(selected).map(([key, info]) => [key, codec.domain(info.patterns)]),
      stamp: { ...stamp, subject }, profile: codec.enumName(profile), rules: rules.map(codec.rule),
      mappings, indirect: mappings.map(row => row.supplied), ownedAliases, readableTargets: reads,
      asWrittenTypes: types, descriptor: types ? codec.descriptor(FIXTURE,I) : undefined,
      budget, privateKeys, boundaryDepth, nameVisibility }, result);
    fullResponses++;
    return result;
  }
  const suppliedParent = ['companies', 'mine'], actualParent = ['companies', 'A'];
  const supplied = [...suppliedParent, 'teams', 'mine'], secondAlias = [...actualParent, 'teams', 'mine'];
  const actual = [...actualParent, 'teams', 'B'];
  const isName = name => m.isResourceName(patterns, name.split('/'));
  const userPatterns = [['me','*'], ['profiles','*'], ['me','*','settings'], ['profiles','*','settings'], ['preferences']];
  const resources = codec.domain(userPatterns), userSite = name => m.isResourceName(userPatterns,name.split('/'));
  const collection = ['me'], alias = ['me','current'], canonical = ['profiles','bob'];
  const singleton = [...canonical,'settings'], preference = ['preferences'];
  // The same canonical target may have a caller-owned spelling and an ordinary
  // lookup spelling. Ownership attests to the first mapping only.
  const account = ['users', 'u1'], own = ['users', 'me'], directory = ['users', 'contact'];
  const recent = [...account, 'documents', 'recent'], doc = [...account, 'documents', 'd1'];
  const accountNames = [['users', '*'], ['users', '*', 'documents', '*']];
  const aliasRequests = [own, directory, [...own, 'documents', 'recent']];
  const aliases = [[own, account], [directory, account], [recent, doc]]
    .map(([supplied, canonical]) => ({supplied, canonical}));
  const owned = {subject: 'alice', supplied: own, target: account};
  const current = target => ({subject: 'alice', target});
  const accessCases = [
    ['alice', [owned], [], [0]],
    ['alice', [owned], [current(doc)], [0, 2]],
    ['alice', [owned], [current(account), current(doc)], [0, 1, 2]],
    ['alice', [], [current(account)], [0, 1]],
    ['alice', [{...owned, target: ['users', 'u2']}], [current(doc)], []],
    ['bob', [owned], [current(account), current(doc)], []]
  ];
  const aliasRequest = aliasRequests.map(p => ({name:p.join('/')}));
  for (const [subject, ownedAliases, readableTargets, included] of accessCases) {
    const access = {
      ownsAlias: (who, source, target) => ownedAliases.some(r =>
        r.subject === who && r.supplied.join('/') === source && r.target.join('/') === target),
      canReadNow: (who, target) => readableTargets.some(r => r.subject === who && r.target.join('/') === target)
    };
    const find = name => aliases.find(r => r.supplied.join('/') === name);
    const js = m.queryAnchors(aliasRequest, ({name}) => find(name)?.canonical.join('/'), access,
      name => m.isResourceName(accountNames, name.split('/')), name => !!find(name), subject);
    const disclosed = js.anchors.flatMap(name => Array.from(js.requested[name])).sort();
    assert.deepEqual(Array.from(disclosed), included.map(i => aliasRequest[i].name).sort());
    const packed = checkQuery({asked:aliasRequests, catalog:accountNames, subject, mappings:aliases, ownedAliases, readableTargets});
    assert.deepEqual(Array.from(packed.contexts.flatMap(ctx => ctx.requestedAnchors.map(a => a.resource))).sort(), Array.from(disclosed));

  }
  {
    const key = 'teams.get', info = I.keys[key], types = [info.type];
    const declared = m.asWrittenDomain(types,I.resources);
    const deployment = {asWrittenTypes:types,descriptor:codec.descriptor(FIXTURE,I)};
    const mappings = [{supplied,canonical:actual,visible:true}];
    const name = supplied.join('/');
    const names = m.queryAnchors([{name}],() => {throw Error('as-written lookup');},() => false,isName,s => {
      const p = s.split('/');
      return s === name && !declared.some(pat => p.length === pat.length && m.reach(pat,p));
    });
    assert.deepEqual(Array.from(names.anchors),[name]);
    compare({op:'resolve',source:supplied,resources:hierarchy,indirect:[supplied],mappings,...deployment},names.anchors[0].split('/'));
    for (const bad of [false,true]) {
      const parentGrant = {keys:[key],effect:'permit',path:suppliedParent};
      const rules = bad ? [parentGrant,{...parentGrant,path:supplied}] : [parentGrant];
      const options = {asWrittenTypes:types};
      const claims = m.projectAnchor(rules,key,supplied,info.patterns,options);
      assert.equal(claims.length,bad ? 0 : 1);
      compare({op:'project',key,path:supplied,resources:hierarchy,domain:codec.domain(info.patterns),
        rules:rules.map(codec.rule),...deployment},claims.map(codec.claim), output => output.claims);
      const allowed = m.regionAllowed(rules,key,supplied,info.patterns,options);
      assert.equal(allowed,!bad);
      compare({op:'regionAllowed',key,path:supplied,rules:rules.map(codec.rule),...deployment},allowed);
      const ctx = m.projectContext(rules,I.keys,supplied,options);
      assert.equal(ctx.error,bad ? 'SERVER_FAULT' : undefined);
      const answer = checkQuery({asked:[supplied], types, mappings, rules, selected:{[key]:info}});
      assert.equal(answer.error,ctx.error);
    }
  }
  {
    const asked = [singleton, [], canonical];
    const request = asked.map(path => path.length ? { name: path.join('/') } : { root: true });
    const noLookup = () => { throw new Error('unexpected canonical lookup'); };
    const result = m.queryAnchors(request, undefined, noLookup, userSite, () => false);
    assert.deepEqual(Array.from(result.anchors), ['', canonical.join('/'), singleton.join('/')]);
    checkQuery({asked, catalog:userPatterns});
  }
  for (const [source, mapped, visible, expected] of [
    [[], null, false, []], [['me','bob'], null, false, ['me','bob']],
    [alias, canonical, false, null], [alias, canonical, true, canonical],
    [[...alias,'settings'], canonical, true, preference],
    [preference, null, false, null]
  ]) {
    const mappings = [
      {supplied:[], canonical:['invalid'], visible:true},
      {supplied:collection, canonical:['invalid'], visible:true},
      {supplied:alias, canonical:mapped, visible},
      {supplied:singleton, canonical:preference, visible:true},
      {supplied:preference, canonical:null, visible:false}
    ];
    const row = path => mappings.find(entry => m.sameName(entry.supplied,path.split('/')));
    const resource = path => { assert.ok(userSite(path), 'consulted a collection or root'); return row(path); };
    const request = [source.length ? {name:source.join('/')} : {root:true}];
    for (const classify of [undefined, path => !!resource(path)]) {
      const consulted = [];
      const outcome = m.queryAnchors(request, ({name}) => {
        consulted.push(name);
        const entry = resource(name);
        return entry ? entry.canonical?.join('/') ?? null : name;
      }, name => { assert.ok(userSite(name)); return mappings.some(r => r.visible && r.canonical?.join('/') === name); },
      userSite, classify);
      const hit = outcome.anchors?.[0];
      const picked = outcome.error ? outcome : hit === undefined ? null : hit ? hit.split('/') : [];
      assert.deepEqual(picked,expected);
      if (!source.length) assert.deepEqual(consulted,[]);
      compare({op:'resolve', source, resources, indirect:mappings.map(r => r.supplied), mappings},picked);
      checkQuery({asked:[source], catalog:userPatterns, mappings});
    }
  }
  for (const asked of [[A, A], [A, [], B, []], [B, A, A]]) {
    let consulted = 0;
    const unavailable = () => { consulted++; throw new Error('adapter unavailable'); };
    const raw = asked.map(p => p.length ? { name: p.join('/') } : { root: true });
    const result = m.queryAnchors(raw, unavailable, unavailable, unavailable, unavailable);
    assert.equal(result.error, 'INVALID_ARGUMENT');
    assert.equal(consulted, 0);
    assert.equal(checkQuery({asked, rules:[{path:['invalid'],keys:[],effect:'permit'}]}).error, result.error);
  }
  for (const parentVisible of [true, false]) for (const childVisible of [true, false]) {
    const mappings = [
      { supplied: suppliedParent, canonical: actualParent, visible: parentVisible },
      { supplied: secondAlias, canonical: actual, visible: childVisible }
    ];
    const expected = parentVisible && childVisible ? actual : null;
    const resolve = ({ name }) => mappings.find(r => r.supplied.join('/') === name)?.canonical.join('/') ?? name;
    const canSee = name => mappings.some(r => r.canonical.join('/') === name && r.visible);
    const isIndirect = name => mappings.some(r => r.supplied.join('/') === name);
    let anchors;
    for (const classifier of [undefined, isIndirect]) {
      const queried = [];
      const resolvePrefix = a => { queried.push(a.name); return resolve(a); };
      const args = [[{ name: supplied.join('/') }], resolvePrefix, canSee, isName];
      if (classifier) args.push(classifier);
      anchors = m.queryAnchors(...args).anchors;
      assert.deepEqual(Array.from(anchors), expected ? [expected.join('/')] : []);
      if (!parentVisible) assert.ok(!queried.includes(secondAlias.join('/')));
    }
    compare({ op: 'resolve', resources:hierarchy, source: supplied, indirect: [suppliedParent, secondAlias], mappings }, anchors.length ? anchors[0].split('/') : null);
  }
  // The slash after "acme" sorts after "-" and before "0". The supplementary
  // IDs begin with UTF-16 high surrogates, which sort before U+E000.
  const ids = ['acme!', 'acme-1', 'acme.', 'acme', 'acme0', '\uD7FF',
    '\u{10000}', '\u{10001}', '\u{1F600}', '\u{10FFFF}', '\uE000'];
  const team = id => 'companies/' + id + '/teams/blue';
  const names = ids.map(team), direct = ['', 'companies/acme', ...names], shared = team('acme0');
  const key = 'teams.get', info = {[key]:I.keys[key]}, rules = [{path:[], keys:[key], effect:'permit'}];
  const path = s => s ? s.split('/') : [];
  for (const [adapter,visible] of [[undefined,true],[null,false],[()=>false,false],
    [()=>{throw Error('name unavailable');},false],[()=>true,true]]) {
    const at=['companies','acme'], site=[...at,'teams','blue'];
    const policy=[...rules,{path:site,keys:[key],effect:'permit'}];
    // Supply the native model the adapter's declared answer at every rule site.
    const nameVisibility = adapter === undefined ? undefined : policy.map(r => [r.path, visible]);
    const ctx=m.projectContext(policy,info,at,{profile:'SCOPED_CLAIMS',canName:adapter});
    assert.equal(ctx.claims.length,visible ? 1 : 0);
    const packed = checkQuery({asked:[at], selected:info, rules:policy, adapter, nameVisibility});
    assert.equal(packed.contexts[0].claims.length,ctx.claims.length);
    compare({op:'project',rules:policy.map(codec.rule),key,path:at,profile:'scopedClaims',
      domain:codec.domain(info[key].patterns),resources:hierarchy,nameVisibility},
      { claims:ctx.claims.map(codec.claim), descendantsOmitted:Object.hasOwn(ctx, 'descendantsOmitted') ? ctx.descendantsOmitted : false });
  }
  for (const coalesce of [false, true]) for (const reverse of [false, true]) {
    const asked = reverse ? [...direct].reverse() : direct;
    const aliases = coalesce ? names.filter(name => name !== shared) : [];
    const mappings = aliases.map(name => ({supplied:path(name), canonical:path(shared), visible:true}));
    const resolved = m.queryAnchors(asked.map(name => name ? {name} : {root:true}), () => shared,
      () => true, isName, name => aliases.includes(name));
    assert.deepEqual(Array.from(resolved.anchors), coalesce ? ['', 'companies/acme', shared] : direct);
    for (const name of resolved.anchors) {
      assert.deepEqual(Array.from(resolved.requested[name]),coalesce && name === shared ? names : [name]);
    }
    for (const profile of ['GRANT_SHAPED','SCOPED_CLAIMS']) {
      const packed = checkQuery({asked:asked.map(path), selected:info, rules, mappings, profile});
      assert.deepEqual(Array.from(packed.contexts, ctx => ctx.anchor.resource ?? ''), Array.from(resolved.anchors));
      assert.deepEqual(Array.from(packed.keySets, set => Array.from(set.keys)), [[key]]);
    }
  }
  const cuts = names.map(name => ({ path:path(name), keys:[key], effect:'forbid' }));
  const ordered = checkQuery({asked:[[]], selected:info, rules:rules.concat(cuts.slice().reverse())});
  const parent = ordered.contexts[0].claims.find(c => c.kind === 'ALLOW');
  assert.deepEqual(Array.from(parent.holes, h => h.resource), names);
  // Above the Team boundary, widget claims are withheld while the team key
  // still projects. The same private addition can change a Team-level query.
  for (let i = 0; i < 128; i++) {
    const alias = ['companies', 'me'];
    const profile = rng.pick(['GRANT_SHAPED', 'SCOPED_CLAIMS']);
    const budget = rng.int(4), visible = !!rng.int(2);
    const pub = [{ path: A, effect: 'permit', keys: Object.keys(keys) },
      { path: B, effect: 'forbid', keys: ['teams.get'] }];
    const secret = { path: D, effect: rng.pick(['permit','forbid']), keys: ['widgets.get'], hidden: true };
    for (const asked of [[[], A, alias], [B], [A, B]]) {
      let previous;
      for (const added of [false, true]) {
        const rules = added ? [...pub, secret] : pub;
        const packed = checkQuery({asked, selected:keys, rules, profile, budget,
          mappings:[{supplied:alias,canonical:A,visible}], privateKeys:['widgets.get'], boundaryDepth:4});
        if (added) assert.deepEqual(packed, previous, 'the complete response changed');
        previous = packed;
      }
    }
  }
  return { aliasEvidenceQueries: accessCases.length, privateWorldPairs: 384, fullResponses, nestedAliasResolutions: 4 };
}
module.exports = { queryCases };
