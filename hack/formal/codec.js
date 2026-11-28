// Representation conversion at the normalized descriptor boundary. Decisions,
// target binding, projection, and snapshot transitions stay in the two models.
'use strict';

const lower = s => s.toLowerCase();
const enumName = s => lower(s).replace(/_([a-z])/g, (_, c) => c.toUpperCase());
const literal = value => ({ lit: { value } });
const variable = name => ({ var: { name } });

function namedPattern(s) {
  return s === '' ? [] : s.split('/').map(part =>
    /^\{[^{}*]+\}$/.test(part) ? variable(part.slice(1, -1)) : literal(part));
}

function domain(patterns) {
  return patterns.map(p => p.map(s => s === '*' ? variable('_') : literal(s)));
}

function requirement(r) {
  return { key: r.key, info: { resourceType: r.type, operation: r.op, accessClass: lower(r.cls),
    explicitGrantOnly: r.explicitOnly }, patterns: r.named.map(namedPattern),
    kind: r.kind, field: r.field, parentOf: r.parentOf, perItem: r.perItem,
    condition: r.condition, hoisted: r.hoisted, wildcardVariables: r.wildcardVariables };
}

function fieldMetadata(fields) {
  return Object.entries(fields || {}).map(([path, f]) => ({
    path, message: !!f?.message, outputOnly: !!f?.outputOnly, oneof: f?.oneof || null,
    repeatedOrMap: !!f?.repeatedOrMap, proto3Optional: !!f?.proto3Optional
  }));
}

function guardInfo(resourceType, operation, cls, explicitOnly) {
  if (typeof operation !== 'string' || !['READ', 'CREATE', 'UPDATE', 'DELETE', 'ADMIN', 'EXECUTE'].includes(cls)) return null;
  return { resourceType, operation, accessClass: lower(cls), explicitGrantOnly: !!explicitOnly };
}

function descriptor(source, interpretation, opts = {}) {
  const sourceResources = source.resources || {};
  const declarations = Object.entries(sourceResources);
  const resourceSources = declarations.map(([name, resource]) => [
    resource?.type === undefined ? name : typeof resource.type === 'string' ? resource.type : '',
    !!resource?.external]);
  const sourceService = source.apiService === undefined || source.apiService === '' ? null : typeof source.apiService === 'string' ? source.apiService : '';
  const prefixes = new Set(resourceSources.filter(([, external]) => !external).map(([type]) => type.split('/')[0]));
  const service = sourceService ?? (prefixes.size === 1 ? [...prefixes][0] : '');
  const catalog = declarations.filter(([name, r]) =>
    !r.external || interpretation.referencedTypes.has(r.type || name));
  const resourceDecl = ([name, r]) => ({
    resourceType: r.type || name, plural: r.plural == null || typeof r.plural === 'string' ? r.plural : '',
    protoMessage: name.includes('.') && !name.includes('/') ? name.replace(/^\./, '') : null,
    patterns: (Array.isArray(r.patterns) ? r.patterns : []).map(pattern => {
      if (typeof pattern === 'string') return namedPattern(pattern);
      if (!Array.isArray(pattern)) return [];
      let i = 0;
      return pattern.map(s => {
        if (s !== '*') return literal(typeof s === 'string' ? s : '');
        const id = Array.isArray(r.vars) ? r.vars[i] ?? '' : 'id' + i;
        i++;
        return variable(typeof id === 'string' ? id : '');
      });
    })
  });
  const resources = catalog.map(resourceDecl);
  const signatureTypes = new Set();
  const batchParents = new Map(), requests = new Map();
  const partialSources = new Map();
  const declarationsByName = new Map();
  const standardBatchWildcards = new Map();
  function sourceRequirement(raw) {
    const text = value => typeof value === 'string' ? value || null : value == null ? null : '!';
    const type = text(raw?.resourceType);
    const typeName = type === 'service' ? type : sourceResources[type]?.type ?? type;
    const vars = raw?.wildcardVariables;
    return { targetField: text(raw?.targetField), resourceType: typeName, serviceRoot: !!raw?.serviceRoot,
      parentTarget: !!raw?.parentTarget, operation: text(raw?.operation) || '',
      accessClass: ['READ','CREATE','UPDATE','DELETE','ADMIN','EXECUTE'].includes(raw?.accessClass) ? lower(raw.accessClass) : null,
      explicitGrantOnly: !!raw?.explicitGrantOnly, condition: text(raw?.condition),
      wildcardVariables: vars == null ? [] : Array.isArray(vars) && vars.every(v => typeof v === 'string') ? vars : ['!'] };
  }
  function recordRequest(name, raw, imported, serviceIndex, required) {
    const vars = raw.authz?.standard?.wildcardVariables;
    const validVars = Array.isArray(vars) && vars.every(v => typeof v === 'string');
    const wildcards = vars == null ? [] : (validVars ? vars : ['']);
    const a = raw.authz || {};
    const mode = Object.hasOwn(a, 'partialSuccess') && Object.hasOwn(a, 'partial_success') ? 'INVALID' :
      a.partialSuccess ?? a.partial_success ?? null;
    partialSources.set(name, { standard: !!a.standard, mode,
      response: raw.returns === undefined ? null : typeof raw.returns === 'string' ? raw.returns : '', failedRequests: !!raw.failedRequests,
      serverStreaming: !!raw.serverStreaming, clientStreaming: !!raw.clientStreaming, imported,
      itemFilter: typeof raw.authz?.itemFilter === 'string' ? raw.authz.itemFilter : raw.authz?.itemFilter ? '!' : '',
      explicitRequirements: raw.authz?.requirements !== undefined, handlerPolicy: raw.authz?.handlerPolicy == null ? null :
        typeof raw.authz.handlerPolicy === 'string' ? raw.authz.handlerPolicy : '',
      wildcardVariables: raw.authz?.standard ? wildcards : null, rootType: sourceResources[raw.resourceType]?.type ?? raw.resourceType ?? null });
    signatureTypes.add(partialSources.get(name).rootType);
    partialSources.get(name).requirementSources = null;
    const requirements = raw.authz?.requirements === undefined ? null :
      Array.isArray(raw.authz.requirements) ? raw.authz.requirements.map(sourceRequirement) : [];
    const { standard, handlerPolicy, response } = partialSources.get(name);
    const entry = { serviceIndex, required, imported, hasAuthorization: !!raw.authz,
      unimplemented: !!(raw.unimplemented || raw.authz?.unimplemented), standard, requirements, handlerPolicy, response, importSignature: null };
    if (!declarationsByName.has(name)) declarationsByName.set(name, []);
    declarationsByName.get(name).push({ entry, raw });
    const type = raw.request && Object.hasOwn(raw.request, 'parent') ? raw.request.parent?.childType : undefined;
    if (typeof type === 'string') batchParents.set(name, sourceResources[type]?.type ?? type);
    if (typeof name === 'string' && name.split('/').pop().startsWith('Batch') && raw.authz?.standard)
      standardBatchWildcards.set(name, wildcards);
    const fields = [];
    function visit(path, value) {
      if (value === true) { fields.push([path, 'bool']); return; }
      if (!value || typeof value !== 'object' || Array.isArray(value)) { fields.push([path, 'invalid']); return; }
      if (path === 'parent' && value.childType !== undefined && (value.type !== undefined || value.resource !== undefined)) {
        fields.push([path, 'invalid']); return;
      }
      const role = ['childType', 'resource', 'type'].find(k => value[k] !== undefined);
      if (role) {
        const type = sourceResources[value[role]]?.type ?? value[role];
        signatureTypes.add(type);
        fields.push([path, role + ':' + type]);
        if (role === 'resource') fields.push([path + '.name', 'type:' + type]);
        return;
      }
      fields.push([path, 'message']);
      for (const [field, child] of Object.entries(value)) visit(path + '.' + field, child);
    }
    for (const [field, value] of Object.entries(raw.request || {})) visit(field, value);
    requests.set(name, fields);
  }
  const noSideEffects = new Set();
  const services = [source, ...(source.services || [])];
  const importedServices = services.flatMap(service => {
    if (!Object.hasOwn(service, 'importedServices')) return [];
    if (!Array.isArray(service.importedServices)) return [['', []]];
    return service.importedServices.map(entry => Array.isArray(entry) && entry.length === 2 && typeof entry[0] === 'string' &&
      Array.isArray(entry[1]) && entry[1].every(rpc => typeof rpc === 'string') ? entry : ['', []]);
  });
  for (const [serviceIndex, service] of services.entries()) {
    for (const m of service.methods || []) {
      recordRequest(m.name, m, false, serviceIndex, !!service.required);
      if (m.noSideEffects) noSideEffects.add(m.name);
    }
    for (const m of service.imported || []) {
      recordRequest(m?.method, m ?? {}, true, serviceIndex, !!service.required);
      if (m?.noSideEffects) noSideEffects.add(m.method);
    }
  }
  const methods = Object.entries(interpretation.methods).map(([name, m]) => ({
    name, disposition: enumName(m.disposition), effect: enumName(m.effect || 'UNKNOWN'), noSideEffects: noSideEffects.has(name),
    partialSuccess: enumName(m.partial || 'NEVER'), writes: m.writes, itemFilter: m.itemFilter,
    partialSource: partialSources.get(name),
    standardReturn: m.standardReturn ?? null,
    standardBatchWildcards: standardBatchWildcards.get(name) ?? null,
    requestShapeKnown: Object.hasOwn(m, 'resourceTarget'),
    requestFields: requests.get(name) ?? null,
    batchParentType: m.batchItemBinding || m.writerBinding?.perItem ? batchParents.get(name) ?? null : null,
    batchItemBinding: m.batchItemBinding ? requirement(m.batchItemBinding) : null,
    writerBinding: m.writerBinding ? requirement(m.writerBinding) : null,
    upsertBinding: m.upsertBinding ? requirement(m.upsertBinding) : null,
    resourceTarget: m.resourceTarget ? { resourceType: m.resourceTarget.type, kind: m.resourceTarget.kind,
      field: m.resourceTarget.field, patterns: m.resourceTarget.named.map(namedPattern) } : null,
    handlerPolicy: m.handlerPolicy ?? null, batchLevel: m.batchLevel || [], fullReplacement: !!m.fullReplacement,
    guardFields: fieldMetadata(m.guardFields),
    fieldGuards: (m.fieldGuards || []).flatMap(g => {
      const k = interpretation.keys[g.key], info = guardInfo(g.type, k?.op, g.cls, k?.explicitOnly);
      // An unrepresentable annotation remains in guardSources for descriptor validation.
      return info ? [{ field: g.field, key: g.key, info }] : [];
    }),
    requirements: (m.requirements || []).map(requirement)
  }));
  for (const name of interpretation.undeclared) {
    methods.push({ name, disposition: 'undeclared', effect: 'unknown', requirements: [],
      noSideEffects: noSideEffects.has(name), partialSuccess: 'never', guardFields: [], fieldGuards: [], batchLevel: [], fullReplacement: false,
      partialSource: partialSources.get(name), requestFields: requests.get(name) ?? null });
  }
  const fieldGuardsEnabled = Object.hasOwn(opts, 'fieldGuards') ? !!opts.fieldGuards : interpretation.fieldGuardsEnabled;
  const guardSources = (fieldGuardsEnabled || opts.rejectUnhandledFieldGuards) ? declarations.flatMap(([type, r]) => {
    const resourceType = r.type || type;
    const guards = Object.entries(r.fields || {}).filter(([, f]) => f?.guard).map(([field, f]) => {
      const { guard } = f;
      return { field, declaration: typeof f.decl === 'string' ? f.decl : type + '.' + field,
        identifier: !!f.identifier, recursive: !!f.recursive,
        optionFields: Object.keys(guard).filter(k => guard[k] !== undefined),
        key: r.plural ? r.plural + '.' + guard.operation : '',
        info: guardInfo(resourceType, guard.operation, guard.accessClass, guard.explicitGrantOnly) };
    });
    return guards.length ? [{ resourceType, external: !!r.external, fields: fieldMetadata(r.fields), guards }] : [];
  }) : [];
  // A stale interpretation can omit a foreign type that the current request
  // now addresses. Keep its reflected declaration outside the checked catalog.
  const signatureImports = declarations.filter(([name,r]) => r.external &&
    signatureTypes.has(r.type || name) && !interpretation.referencedTypes.has(r.type || name)).map(resourceDecl);
  // The same import may be declared on sibling services if all its options agree.
  const sorted = value => Array.isArray(value) ? value.map(sorted) : value && typeof value === 'object' ?
    Object.fromEntries(Object.keys(value).sort().map(k => [k, sorted(value[k])])) : value;
  const declaredMethods = [...declarationsByName].map(([name, group]) => [
    typeof name === 'string' ? name : '', group.map(({ entry, raw }) => {
      if (group.length === 1 || !entry.imported) return entry;
      const signature = { authz: raw.authz, request: raw.request, resourceType: raw.resourceType, returns: raw.returns,
        failedRequests: !!raw.failedRequests, noSideEffects: !!raw.noSideEffects, unimplemented: !!raw.unimplemented,
        clientStreaming: !!raw.clientStreaming, serverStreaming: !!raw.serverStreaming };
      return { ...entry, importSignature: JSON.stringify(sorted(signature)) };
    })
  ]);
  return { service, sourceService, resourceSources, resources, methods, referencedTypes: [...interpretation.referencedTypes],
    fieldGuardsEnabled, rejectUnhandledFieldGuards: !!opts.rejectUnhandledFieldGuards, guardSources, signatureImports,
    declaredMethods, requiredApi: services.some(s => s.required), importedServices };
}

const scope = path => path.length ? { resource: { first: path[0], rest: path.slice(1) } } : 'serviceRoot';
function grant(g) {
  return {
    site: scope(g.scope), effect: g.effect || 'permit', ceiling: ceiling(g.ceiling),
    pred: g.condition ?? null, hidden: !!g.hidden, mayError: !!g.mayError, final: g.final !== false,
    selectors: g.selectors.map(s => ({ resourceType: s.type === '*' ? null : s.type,
      kind: s.op ? { operation: { name: s.op } } : { accessClass: { cls: lower(s.cls) } } }))
  };
}
const ceiling = c => c == null ? null : c.map(e => typeof e === 'string'
  ? { resourceType: null, accessClass: lower(e) }
  : { resourceType: e.type === '*' ? null : e.type, accessClass: lower(e.cls) });
const rule = r => ({ path: r.path, keys: r.keys, effect: r.effect, pred: r.pred ?? null,
  sourceIndex:r.sourceIndex ?? null,
  hidden: !!r.hidden, mayError: !!r.mayError, final: r.final !== false });
const claim = c => ({ key: c.key, path: c.path, holes: c.holes, kind: lower(c.kind) });
const status = code => ({ OK: 'ok', PERMISSION_DENIED: 'denied', NOT_FOUND: 'notFound',
  ALREADY_EXISTS: 'alreadyExists', INVALID_ARGUMENT: 'invalidArgument' })[code];

// Adapter inputs are declared by the fixture. Copy them before either model executes.
function callbackInputs(callback, kind, rules = [], keys = []) {
  if (typeof callback !== 'function') {
    if (kind === 'canName' && callback !== undefined) return {nameVisibility:null};
    if (kind.startsWith('unresolved')) return {unresolvedDefault:callback === undefined ? [] : null};
    return {};
  }
  if (Object.hasOwn(callback,'fixtureInputs')) return structuredClone(callback.fixtureInputs);
  if (!Object.hasOwn(callback,'fixtureValue')) throw Error('missing declared inputs for ' + kind + ' ' + String(callback).slice(0,130));
  const value = callback.fixtureValue;
  if (kind === 'attrsOf') return value?.owner == null ? {} : {predicates:[['owner',value.owner === 'alice']]};
  if (kind === 'faults') return typeof value === 'boolean' ? {faults:value ? rules.map(rule) : []} : {};
  if (kind === 'nonprojecting') return {nonprojectingKeys:value === false ? [] : keys};
  if (kind === 'unresolvedSegment' || kind === 'unresolvedSegments') {
    const positions = kind === 'unresolvedSegments' ? value : value === -1 ? [] : [value];
    return {unresolvedDefault:Array.isArray(positions) && positions.every(i => Number.isSafeInteger(i) && i >= 0) ? [...positions] : null};
  }
  throw Error('unexpected constant fixture for ' + kind);
}

function authorization(a) {
  return {
    decision: a.decision, reason: a.reason || null, handlerPolicy: a.handlerPolicy || null,
    status: a.status ? status(a.status) : null,
    residuals: a.residuals.map(r => ({
      kind: r.kind, key: r.key || null, target: r.target || null, keys: r.keys || [],
      predicates: r.predicates || [], nonprojectingGet: !!r.nonprojectingGet,
      nonprojectingList: !!r.nonprojectingList
    }))
  };
}

function initialState(service) {
  return { service, session: 'parity', generation: 0, serial: 0,
    subject: null, token: null, loadedEtag: null, lastEtag: null, history: [] };
}

function frameState(service, snap) {
  const state = initialState(service);
  if (!snap) return state;
  const reply = { service, subject: 'fixture', token: 'snapshot', expires: 100, descriptorEtag: 'fixture',
    profile: enumName(snap.profile), keySets: snap.keySets,
    contexts: snap.contexts };
  return { ...state, subject: reply.subject, token: reply.token, serial: 1, history: [{ serial: 1, reply }] };
}

module.exports = { lower, enumName, callbackInputs, namedPattern, domain, descriptor, fieldMetadata, ceiling, grant, rule,
  claim, status, authorization, initialState, frameState };
