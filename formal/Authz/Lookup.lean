import Authz.Server

/-! Singular resource handlers at a single storage/policy snapshot (§4.3).
Rows carry complete resource names, including all collection-membership ancestors.
The resolver supplies a data-independent upper bound on possible names even
when a lookup has no match. The default for an indirect identifier is the full
declared resource domain. -/
namespace Authz
open Lean (Json)
open Disclosure (Status Knowledge)

structure ResourceRow where
  name : Path
  predicates : List (String × Bool) := []
  secondaryNames : List Path := []
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

structure LookupStore where
  rows : List ResourceRow := []
  possibleNames : List (Path × Domain) := []
  createDestination : Option Path := none
  deriving Repr, Lean.FromJson, Lean.ToJson

structure LookupOutcome where
  status : Status
  error : Option Disclosure.ErrorInfo
  deriving Repr, Lean.FromJson, Lean.ToJson

def lookupOutcome (status : Status) (domain permission : String) (supplied : Path) : LookupOutcome :=
  ⟨status, if status == .ok then none else
    some (Disclosure.errorPayload status domain permission (String.intercalate "/" supplied))⟩

/-- Intersect a public resolver range with the declaring resource's patterns.
Parent depth is taken from the original descriptor, even when ID variables
become fixed literals in the restricted result. -/
private def intersectPatterns : Pattern → Pattern → Option Pattern
  | [], [] => some []
  | a :: as, b :: bs => do
    let rest ← intersectPatterns as bs
    match a, b with
    | .lit x, .lit y => if x == y then return a :: rest else none
    | .var _, _ => return b :: rest
    | _, .var _ => return a :: rest
  | _, _ => none

private def coveredPattern : Pattern → Pattern → Bool
  | [], [] => true
  | a :: as, b :: bs => (match a, b with
    | .var _, _ => true
    | .lit x, .lit y => x == y
    | _, _ => false) && coveredPattern as bs
  | _, _ => false

private def regionPair (patterns restrictions : Domain) : List (Pattern × Pattern) :=
  patterns.flatMap fun p => restrictions.filterMap fun restriction => do
    let selected ← intersectPatterns p restriction
    return (selected, selected.take (Pattern.parent p).length)

private def commonPrefix : Path → Path → Path
  | a :: as, b :: bs => if a == b then a :: commonPrefix as bs else []
  | _, _ => []

private def fixedPath : Domain → Path
  | [] => []
  | p :: ps => ps.foldl (fun acc pat => commonPrefix acc (Pattern.literals pat)) (Pattern.literals p)

private def disclosureAnchor (d : Descriptor) (domain : Domain) : Path :=
  let fixed := fixedPath domain
  let lengths := (List.range (fixed.length+1)).reverse
  let n := lengths.find? (fun i => d.resources.any fun res => res.patterns.any fun p =>
    let name := fixed.take i
    Pattern.matches p name || (i > 0 && Pattern.reach p name &&
      (p[i-1]?).any (fun a => match a with | .var _ => true | _ => false)))
  fixed.take (n.getD 0)

private def visibleFinal (rules : List Rule) (r : Requirement) (domain : Domain) (opts : ServerOptions) :=
  !opts.ceiling.permits r.info || rules.any fun rule => rule.keys.contains r.key &&
    rule.finalForbid && !rule.hidden && opts.canName rule.path && rule.path.isPrefixOf (fixedPath domain)

private def singleName (domain : Domain) : Option Path :=
  match domain.eraseDups with
  | [p] => p.mapM (fun a => match a with | .lit s => some s | .var _ => none)
  | _ => none

/-- An as-written index entry may change only segments at declared
as-written sites. Bind every remaining segment to the addressed collection. -/
def storedAsWritten (resources : Domain) (resolver : NameResolver) (query : Path) (row : ResourceRow) : Bool :=
  row.secondaryNames.contains query && resources.isResource query && resources.isResource row.name &&
    query.length == row.name.length &&
    (query.zip row.name).zipIdx.all fun ((supplied, id), i) =>
      supplied == id || (resources.isResource (query.take (i+1)) && resources.isResource (row.name.take (i+1)) &&
        resolver.asWritten.any (fun pat => pat.getLast?.any Atom.isVariable &&
          Pattern.matches pat (query.take (i+1)) && Pattern.matches pat (row.name.take (i+1))))

private def rowsAt (resources : Domain) (store : LookupStore) (opts : ServerOptions) (name : Path) :=
  store.rows.filter fun row => row.name == name || storedAsWritten resources opts.names name row

private def rowFacts (opts : ServerOptions) (row : ResourceRow) : Facts :=
  let base := opts.available row.name
  {base with predicate := fun p => (row.predicates.lookup p).or (base.predicate p)}

private def factsAt (resources : Domain) (store : LookupStore) (opts : ServerOptions) (name : Path) : Facts :=
  match rowsAt resources store opts name with
  | [row] => rowFacts opts row
  | _ => opts.available name

private def observedNameAt (resources : Domain) (store : LookupStore) (opts : ServerOptions) (name : Path) : Path :=
  match rowsAt resources store opts name with
  | [row] => row.name
  | _ => name

private def lookupServerOptions (resources : Domain) (store : LookupStore) (opts : ServerOptions) : ServerOptions :=
  let observed := observedNameAt resources store opts
  {opts with factsOf := some (factsAt resources store opts),
             faultsOf := opts.faultsOf.map (fun observe p => observe (observed p)),
             rowReadFailed := fun p => opts.rowReadFailed (observed p)}

/-- Without either fault source, no later join can establish a fault outcome. -/
private def rangeFaults (opts : ServerOptions) : Option (Rule → Option Bool) :=
  if opts.factsOf.isNone && opts.faultsOf.isNone then some (fun _ => none) else none

private def lookupFaults (opts : ServerOptions) (resources : Domain) (target : Path) : Option (Rule → Option Bool) :=
  (rangeFaults opts).or <|
    let indexed := (List.range target.length).any fun i =>
      let site := target.take (i+1)
      resources.isResource site && Domain.contains opts.names.asWritten site
    if indexed then none else opts.faultsOf.map (· target)

/-- A row can supply arbitrary predicates. Faults are fixed only when the
policy name and source of the observation are already known. -/
private def preflightOptions (mode : Authority) (observed : Option (Rule → Option Bool)) : ServerOptions :=
  {mode, factsOf := some (fun _ => {}), faultsOf := observed.map (fun observe _ => observe), pendingLookup := true}

def ServerOptions.beforeLookup (opts : ServerOptions) (resources : Domain) (target : Path) : ServerOptions :=
  preflightOptions opts.mode (lookupFaults opts resources target)

/-- Rule applicability is constant within an unmerged partition cell. A
literal candidate also has a fixed name for separately observed faults.
A free ID can select a different fault outcome at every possible name. -/
private def patternCellAll (resources : Domain) (opts : ServerOptions)
    (check : Path → Option (Rule → Option Bool) → Bool) (c : Claim) (pat : Pattern) : Bool :=
  (pat.fixedPrefix c.path).all fun fixed =>
    c.holes.any (·.isPrefixOf fixed) ||
      if Pattern.matches pat fixed then check fixed (lookupFaults opts resources fixed)
      else check c.path (rangeFaults opts)

private def allCandidateCells (resources : Domain) (rules : List Rule) (key : String)
    (domain : Domain) (opts : ServerOptions) (check : Path → Option (Rule → Option Bool) → Bool) : Bool :=
  (partition rules key (bounds rules key [] domain)).all fun cell =>
    domain.all (patternCellAll resources opts check cell)

def uniformPolicyDenial (resources : Domain) (rules : List Rule) (key : String)
    (domain : Domain) (opts : ServerOptions) : Bool :=
  allCandidateCells resources rules key domain opts fun site observed =>
    policyDeniesBeforeRow rules key site (preflightOptions opts.mode observed)

def uniformPolicyAllow (resources : Domain) (rules : List Rule) (key : String)
    (domain : Domain) (opts : ServerOptions) : Bool :=
  allCandidateCells resources rules key domain opts fun site observed =>
    decide opts.mode {faults := observed.getD (fun _ => none)} rules key site == .allow

private theorem cell_preflight_sound {rules key a b mode observed} (facts : Facts)
    (same : rules.filter (applies key a) = rules.filter (applies key b))
    (denied : policyDeniesBeforeRow rules key a (preflightOptions mode observed)) :
    decide mode {facts with faults := observed.getD facts.faults} rules key b = .deny := by
  let actual : ServerOptions := {mode, factsOf := some (fun _ => facts), faultsOf := observed.map (fun observe _ => observe), pendingLookup := true}
  have blocked : policyDeniesBeforeRow rules key b actual := by
    unfold policyDeniesBeforeRow at denied ⊢
    rw [← same]
    cases observed <;> exact denied
  have outcome := pre_row_denial_sound blocked
  cases observed <;> exact outcome

private theorem matched_length {pat : Pattern} {x : Path} (hit : Pattern.matches pat x) : pat.length = x.length := by
  induction pat generalizing x with
  | nil => cases x <;> simp_all [Pattern.matches]
  | cons atom rest ih =>
    cases x with
    | nil => simp [Pattern.matches] at hit
    | cons s xs => simpa using ih (Bool.and_eq_true_iff.mp hit).2

private theorem all_candidate_cells_at {resources rules key domain opts x check}
    (uniform : allCandidateCells resources rules key domain opts check)
    (member : Domain.contains domain x) :
    ∃ site observed, rules.filter (applies key site) = rules.filter (applies key x) ∧
      (∀ obs, observed = some obs → lookupFaults opts resources x = some obs) ∧ check site observed := by
  obtain ⟨pat, declared, hit⟩ := List.any_eq_true.mp member
  have root : [] ∈ bounds rules key [] domain := by simp [bounds]
  obtain ⟨c, hc, covers⟩ := partition_total rules key _ root (List.nil_prefix (l := x))
  have same := partition_inherits hc covers member
  have within := claim_covers_iff.mp covers
  have checked := List.all_eq_true.mp (List.all_eq_true.mp uniform c hc) pat declared
  obtain ⟨tail, path⟩ := within.1
  have consumed := (Pattern.consume_matches pat x).2 hit
  rw [← path, Pattern.consume_append] at consumed
  cases step : Pattern.consume pat c.path with
  | none => simp [step] at consumed
  | some rest =>
    have suffix : Pattern.matches rest tail := (Pattern.consume_matches _ _).1 (by simpa [step] using consumed)
    let fixed := c.path ++ Pattern.literals rest
    have canonical : fixed <+: x := by rw [← path]; exact (List.prefix_append_right_inj _).mpr (Pattern.literals_prefix suffix)
    have holes : c.holes.any (·.isPrefixOf fixed) = false := List.any_eq_false.mpr fun h hh hprefix =>
      within.2 ⟨h, hh, (List.isPrefixOf_iff_prefix.mp hprefix).trans canonical⟩
    simp only [patternCellAll, Pattern.fixedPrefix, step, Option.map_some, Option.all_some] at checked
    change (c.holes.any (·.isPrefixOf fixed) || _) = true at checked
    rw [holes, Bool.false_or] at checked
    split at checked
    next exactName =>
      have eq := canonical.eq_of_length ((matched_length exactName).symm.trans (matched_length hit))
      change check fixed (lookupFaults opts resources fixed) = true at checked
      rw [eq] at checked
      exact ⟨x, _, rfl, fun _ h => h, checked⟩
    next =>
      refine ⟨c.path, _, same, ?_, checked⟩
      intro obs known
      simp [lookupFaults, known]

/-- Every candidate in a uniformly denied range is denied for every row.
An independent fault observation constrains that row only at its actual
policy name. No representative row or name stands in for a free ID. -/
theorem uniform_policy_denial_sound {resources rules key domain opts x}
    (uniform : uniformPolicyDenial resources rules key domain opts)
    (member : Domain.contains domain x) (row : Facts) :
    decide opts.mode {row with faults := (lookupFaults opts resources x).getD row.faults} rules key x = .deny := by
  obtain ⟨site, observed, same, compatible, refused⟩ := all_candidate_cells_at uniform member
  let facts := {row with faults := (lookupFaults opts resources x).getD row.faults}
  have outcome := cell_preflight_sound facts same refused
  cases observed with
  | none => exact outcome
  | some obs => simpa [facts, compatible obs rfl] using outcome

/-- A uniform allow must hold with all row predicates missing. Future row
facts may complete those predicates and must retain fixed fault observations. -/
theorem uniform_policy_allow_sound {resources rules key domain opts x}
    (uniform : uniformPolicyAllow resources rules key domain opts)
    (member : Domain.contains domain x) (valid : pathOk x) (row : Facts) :
    decide opts.mode {row with faults := (lookupFaults opts resources x).getD row.faults} rules key x = .allow := by
  obtain ⟨site, observed, same, compatible, test⟩ := all_candidate_cells_at uniform member
  let partialFacts : Facts := {faults := observed.getD (fun _ => none)}
  have allow : decide opts.mode partialFacts rules key site = .allow := beq_iff_eq.mp test
  have point : decide opts.mode partialFacts rules key x = .allow := by
    unfold decide at allow ⊢
    split at allow
    · contradiction
    · rename_i wellFormed
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at wellFormed
      simp only [valid, Bool.not_true, Bool.false_or, wellFormed.2, ← same]
      exact allow
  apply decide_allow_of_more_facts _ point
  constructor
  · intro _ _ h
    contradiction
  · intro rule b known
    cases observed with
    | none => contradiction
    | some obs => simpa [partialFacts, compatible obs rfl] using known

private def restriction (d : Descriptor) (rules : List Rule) (r : Requirement) (domain : Domain)
    (opts : ServerOptions) : Knowledge := Id.run do
  if !opts.ceiling.permits r.info then return .deny
  if domain.isEmpty || !domain.all (fun p => (d.domain r.key).any (coveredPattern · p)) then return .needsRow
  let anchor := disclosureAnchor d domain
  let cells := regionClaims rules r.key anchor domain
    {nonprojecting := opts.nonprojecting r.key anchor, canName := opts.canName}
  if cells.isEmpty then return .needsRow
  if cells.all (·.kind == .deny) || uniformPolicyDenial d.resourcePatterns rules r.key domain opts then return .deny
  if cells.all (·.kind == .allow) || uniformPolicyAllow d.resourcePatterns rules r.key domain opts then return .allow
  return .needsRow

private def deniedBeforeJoin (resources : Domain) (rules : List Rule) (r : Requirement)
    (target : Path) (opts : ServerOptions) :=
  !opts.ceiling.permits r.info || policyDeniesBeforeRow rules r.key target (opts.beforeLookup resources target)

private def permissionAt (resources : Domain) (store : LookupStore) (opts : ServerOptions) (rules : List Rule)
    (r : Requirement) (t : Path) : Bool :=
  !deniedBeforeJoin resources rules r t opts && (rowsAt resources store opts t).length ≤ 1 &&
    allowed rules r t (lookupServerOptions resources store opts)

def Authorization.complete (a : Authorization) := a.decision == "PROCEED" && a.residuals.isEmpty

theorem Authorization.complete_iff {a : Authorization} : a.complete = true ↔
    a.decision = "PROCEED" ∧ a.residuals = [] := by
  simp [Authorization.complete]

private def canReadAt (d : Descriptor) (rules : List Rule) (opts : ServerOptions) (store : LookupStore)
    (resourceType op : String) (name : Path) : Bool :=
  (d.readMethods resourceType op).any fun (method, binding) =>
    (binding.readRequest? name).any fun request =>
      let readOpts := {lookupServerOptions d.resourcePatterns store opts with
        names := {asWritten := opts.names.asWritten}}
      (authorizeRequest d method.name request rules readOpts).complete && (rowsAt d.resourcePatterns store opts name).length ≤ 1

private def readRegions (d : Descriptor) (method : MethodDecl) (binding : ResourceTarget)
    (req : Requirement) (region : Domain) : Option Domain := do
  if binding.field.isNone || req.field != binding.field then
    -- Only the read address is populated. Bind every other field as it would
    -- arrive on the ordinary read request, including a missing root parent.
    let fixed ← (requirementsFor d method (Json.mkObj [])).find? (·.decl == req)
    guard (!fixed.unbound && !fixed.resolverFault)
    return (fixed.targets.map fun (_, t) => t.target.map Atom.lit).eraseDups
  let source := if req.parentOf then (d.resourceFor req.info.resourceType).elim [] (·.patterns) else req.patterns
  guard (region.all fun p => source.any (coveredPattern · p))
  return if req.parentOf then ((regionPair source region).map Prod.snd).eraseDups else region

/-- A uniform read proof must cover each mandatory requirement on the
read RPC's own request. Optional boolean conditions are absent on this probe.
An arbitrary runtime guard hook cannot supply a uniform symbolic proof. -/
private def canReadRegion (d : Descriptor) (rules : List Rule) (opts : ServerOptions)
    (resourceType op : String) (region : Domain) : Bool :=
  !region.isEmpty && opts.extraGuards.isNone && (d.readMethods resourceType op).any fun (method, binding) =>
    region.all (fun p => binding.patterns.any (coveredPattern · p)) && method.requirements.all fun req =>
      req.condition.isSome || (readRegions d method binding req region).any fun targets =>
        !opts.nonprojecting req.key (disclosureAnchor d targets) && restriction d rules req targets opts == .allow

private def missingKnowledge (rules : List Rule) (r : Requirement) (name : Path) (opts : ServerOptions) : Knowledge :=
  if !opts.ceiling.permits r.info then .deny else
  if policyAllowsBeforeRow rules r.key name opts then .allow else
  if opts.rowReadFailed name then .deny else
  let facts := opts.available name
  let app := rules.filter (applies r.key name)
  if decideApplied opts.mode facts app == .allow then .allow else
  -- An observed false predicate eliminates that permit. A known matching
  -- forbid already fixes the decision. Other predicates could still resolve.
  let possible := app.filter fun rule => rule.effect == .forbid || rule.evaluate facts != .none
  let observed := {opts with faultsOf := some (fun _ => facts.faults)}
  if app.any (fun rule => rule.evaluate facts == .forbid) ||
      policyDeniesBeforeRow possible r.key name observed then .deny else .needsRow

def rangeKnowledge (d : Descriptor) (rules : List Rule) (r : Requirement)
    (resourceType : String) (domain resourceNames parentNames : Domain) (opts : ServerOptions) : Disclosure.ZeroMatch :=
  let sight := fun op region => if canReadRegion d rules opts resourceType op region then Knowledge.allow else .needsRow
  let blocked := fun op region => (d.readMethods resourceType op).all fun (method, binding) =>
    method.requirements.any fun req => req.condition.isNone && (readRegions d method binding req region).any
      (fun targets => opts.nonprojecting req.key (disclosureAnchor d targets))
  {
    region := restriction d rules r domain opts
    regionList := sight "list" parentNames, regionGet := sight "get" resourceNames
    nonprojectingKey := opts.nonprojecting r.key (disclosureAnchor d domain)
    nonprojectingList := blocked "list" parentNames, nonprojectingGet := blocked "get" resourceNames
    regionDenyFinal := visibleFinal rules r domain opts }

/-- For a projecting key with a disclosed, nonempty range, a uniform policy
denial takes precedence over Get and List discovery, including Delete with
allow-missing. Private or withheld regions use the other §4.3 proofs. -/
theorem projecting_denial_precedes_discovery {d rules r domain opts}
    (publicKey : opts.nonprojecting r.key (disclosureAnchor d domain) = false)
    (inhabited : domain.isEmpty = false)
    (inKey : domain.all (fun p => (d.domain r.key).any (coveredPattern · p)) = true)
    (visible : (regionClaims rules r.key (disclosureAnchor d domain) domain
      {nonprojecting := false, canName := opts.canName}).isEmpty = false)
    (blocked : uniformPolicyDenial d.resourcePatterns rules r.key domain opts) (resourceType resources parents allowMissing) :
    Disclosure.zeroMatchStatus {rangeKnowledge d rules r resourceType domain resources parents opts with
      deleteAllowMissing := allowMissing} = .denied := by
  have knowledge : restriction d rules r domain opts = .deny := by
    cases cap : opts.ceiling.permits r.info <;>
      simp [restriction, cap, inhabited, inKey, publicKey, visible, blocked]
  simp [Disclosure.zeroMatchStatus, rangeKnowledge, knowledge, publicKey]

private def anyIndirect (resources : Domain) (opts : ServerOptions) (name : Path) :=
  (List.range name.length).any fun i =>
    let p := name.take (i+1)
    opts.names.indirectAt resources p

structure ResourceLookupPlan where
  method : MethodDecl
  primary : Requirement
  field : String
  supplied : Path
  requirements : List BoundRequirement
  resource : ResourceDecl
  catalog : Domain
  pairs : List (Pattern × Pattern)
  indirect : Bool
  upsert : Bool

inductive LookupBinding where
  | response (result : LookupOutcome)
  | bound (plan : ResourceLookupPlan)

/-- Ordered permission checks include conditional requirements and triggered field guards. -/
def lookupTargets (rs : List BoundRequirement) : List (Requirement × TargetBinding) :=
  rs.flatMap fun r => r.targets.map fun (_, t) => (r.decl, t)

def ResourceLookupPlan.region (p : ResourceLookupPlan) (t : TargetBinding) : Domain :=
  if t.targetLength < t.source.length then (p.pairs.map Prod.snd).eraseDups
  else (p.pairs.map Prod.fst).eraseDups

/-- A pre-lookup denial uses request facts. Disjoint spellings are checked over
their public range. An as-written secondary spelling can join a canonical row
with its own fault evidence, so defer those outcomes until the row check. -/
def requestDenied (d : Descriptor) (rules : List Rule) (opts : ServerOptions)
    (p : ResourceLookupPlan) (entry : Requirement × TargetBinding) : Bool :=
  let (r, t) := entry
  if !opts.ceiling.permits r.info then true
  else if r.field == some p.field && p.indirect then
    let region := p.region t
    visibleFinal rules r region opts ||
      (!opts.nonprojecting r.key (disclosureAnchor d region) && restriction d rules r region opts == .deny)
  else if !anyIndirect d.resourcePatterns opts t.source && !t.target.contains "-" then
    deniedBeforeJoin d.resourcePatterns rules r t.target opts
  else false

private def TargetBinding.suppliedTarget (t : TargetBinding) (resources : Domain) (opts : ServerOptions) : Path :=
  if anyIndirect resources opts t.source || t.source.contains "-" then t.source else t.target

def ResourceLookupPlan.denial (p : ResourceLookupPlan) (d : Descriptor) (opts : ServerOptions)
    (entry : Requirement × TargetBinding) : LookupOutcome :=
  let (r, t) := entry
  let upsert := p.indirect && p.upsert
  let name := if upsert then p.supplied else t.suppliedTarget d.resourcePatterns opts
  lookupOutcome .denied d.service (if upsert then p.primary.key else r.key) name

/-- Derive the parent after resolving the full source. Alternate collection
paths can have different lengths. The original binding supplies the echo name. -/
private def targetAt? (t : TargetBinding) (source : Path) : Option Path := do
  let pat ← t.patterns.find? (Pattern.matches · source)
  return if t.targetLength < t.source.length then source.take (Pattern.parent pat).length else source

private def inDeclaredRange (resources : Domain) (opts : ServerOptions) (store : LookupStore) (supplied destination : Path) :=
  !anyIndirect resources opts supplied || (store.possibleNames.lookup supplied).all fun range =>
    range.all (·.all Atom.valid) && Domain.contains range destination

private def targetDenied (d : Descriptor) (rules : List Rule) (opts : ServerOptions) (store : LookupStore)
    (entry : Requirement × TargetBinding) : Bool := Id.run do
  let (r, t) := entry
  let some source := (opts.names.canonical d.resourcePatterns t.source).toOption.join | return true
  if !inDeclaredRange d.resourcePatterns opts store t.source source then return true
  if source.contains "-" then
    return !(r.kind == .parent && !r.parentOf &&
      r.patterns.any (Pattern.matchesWildcard · r.wildcardVariables source) &&
      regionAllowed d rules r source false opts)
  let some target := targetAt? t source | return true
  return !permissionAt d.resourcePatterns store opts rules r target

def ancillaryDenied (d : Descriptor) (rules : List Rule) (opts : ServerOptions) (store : LookupStore)
    (field : String) (entry : Requirement × TargetBinding) : Bool :=
  entry.1.field != some field && targetDenied d rules opts store entry

def checkedCreate (d : Descriptor) (m : MethodDecl) (request : Json) (rules : List Rule)
    (opts : ServerOptions) (store : LookupStore) (shape : ResourceTarget) (primary : Requirement)
    (supplied destination : Path) (bound : List BoundRequirement) : LookupOutcome :=
  let diagnostic := if primary.kind == .root then [] else supplied
  let finish := fun status => lookupOutcome status d.service primary.key diagnostic
  let auth := authorizeRequest d m.name request rules (lookupServerOptions d.resourcePatterns store opts)
  let canonicalParent := (opts.names.canonical d.resourcePatterns supplied).toOption.join
  let parent := (d.resourceFor shape.resourceType).bind fun res => (res.patterns.find? (Pattern.matches · destination)).map
    (fun pat => destination.take (Pattern.parent pat).length)
  if let some (failed, target) := (lookupTargets bound).find? (fun (r,t) =>
      !anyIndirect d.resourcePatterns opts t.source && (if t.source.contains "-" then
        targetDenied d rules opts store (r,t) else deniedBeforeJoin d.resourcePatterns rules r t.target opts)) then
    lookupOutcome .denied d.service failed.key (target.suppliedTarget d.resourcePatterns opts)
  else if !Domain.contains shape.patterns supplied || !canonicalParent.any (inDeclaredRange d.resourcePatterns opts store supplied) ||
      parent.isNone || canonicalParent != parent || parent.any (fun p => (rowsAt d.resourcePatterns store opts p).length > 1) then finish .denied
  else if let some (failed, t) := (lookupTargets bound).find? (targetDenied d rules opts store) then
    lookupOutcome .denied d.service failed.key (t.suppliedTarget d.resourcePatterns opts)
  else if !auth.complete then finish .denied
  else
    let taken := store.rows.any (·.name == destination)
    let see := canReadAt d rules opts store shape.resourceType "get" destination
    let list := parent.any (canReadAt d rules opts store shape.resourceType "list")
    finish (Disclosure.createStatus true taken see list)

/-- Reporting a collision requires completed authorization for the Create
request and a served Get or List that the caller can invoke. -/
theorem create_collision_requires_read {d m request rules opts store shape primary supplied destination bound}
    (reported : (checkedCreate d m request rules opts store shape primary supplied destination bound).status = .alreadyExists) :
    (authorizeRequest d m.name request rules (lookupServerOptions d.resourcePatterns store opts)).complete = true ∧
      store.rows.any (·.name == destination) = true ∧
      (canReadAt d rules opts store shape.resourceType "get" destination = true ∨
        ∃ resource ∈ d.resourceFor shape.resourceType, ∃ pat ∈ resource.patterns,
          pat.matches destination = true ∧
          canReadAt d rules opts store shape.resourceType "list" (destination.take pat.parent.length) = true) := by
  simp only [checkedCreate] at reported
  split at reported
  · contradiction
  split at reported
  · contradiction
  split at reported
  · contradiction
  split at reported
  · contradiction
  next authorized =>
    refine ⟨by simpa using authorized, ?_⟩
    change Disclosure.createStatus true _ _ _ = .alreadyExists at reported
    simp only [Disclosure.createStatus, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at reported
    split at reported
    · contradiction
    next taken =>
      refine ⟨by simpa using taken, ?_⟩
      split at reported
      next read =>
        rcases Bool.or_eq_true_iff.mp read with get | list
        · exact Or.inl get
        · right
          simp only [Option.any_eq_true, Option.bind_eq_some_iff,
            Option.map_eq_some_iff] at list
          obtain ⟨parent, ⟨res, declared, pat, matched, rfl⟩, canList⟩ := list
          exact ⟨res, declared, pat, List.mem_of_find?_eq_some matched,
            List.find?_some (p := fun p : Pattern => p.matches destination) matched, canList⟩
      · contradiction

def absenceBlocked (d : Descriptor) (rules : List Rule) (opts : ServerOptions) (store : LookupStore)
    (p : ResourceLookupPlan) (entry : Requirement × TargetBinding) : Bool := Id.run do
  let (r, t) := entry
  if r.field != some p.field then return false
  let resources := (p.pairs.map Prod.fst).eraseDups
  let parents := (p.pairs.map Prod.snd).eraseDups
  let region := p.region t
  if p.upsert && p.indirect && t.targetLength < t.source.length then
    return !region.all fun candidate =>
      match singleName [candidate] with
      | some parent => permissionAt d.resourcePatterns store opts rules r parent
      | none => !opts.nonprojecting r.key (disclosureAnchor d [candidate]) &&
          restriction d rules r [candidate] opts == .allow
  if let some n := singleName region then
    if t.targetLength < t.source.length then
      return !permissionAt d.resourcePatterns store opts rules r n
    if !p.indirect then
      let parentList := (singleName parents).any (canReadAt d rules opts store p.resource.resourceType "list")
      return Disclosure.readStatus false (missingKnowledge rules r n opts) parentList == .denied
  return Disclosure.zeroMatchStatus (rangeKnowledge d rules r p.resource.resourceType region resources parents opts) == .denied

def missChecks (d : Descriptor) (rules : List Rule) (opts : ServerOptions) (store : LookupStore)
    (p : ResourceLookupPlan) :=
  (lookupTargets p.requirements).find? (absenceBlocked d rules opts store p)

/-- First consider the permissions for the missing address, then the independent
fields as they stand without that resource. Both checks keep descriptor order. -/
def absentFailure (d : Descriptor) (rules : List Rule) (opts : ServerOptions)
    (store : LookupStore) (p : ResourceLookupPlan) :=
  missChecks d rules opts store p <|>
    (lookupTargets p.requirements).find? (ancillaryDenied d rules opts store p.field)

/-- Execute a declared singular method against one policy/storage snapshot. A
malformed binding is denied before lookup. An indirect miss is still a bound
request and is checked over the full public candidate range. -/
def bindResourceLookup (d : Descriptor) (methodName : String) (request : Json)
    (rules : List Rule) (store : LookupStore) (opts : ServerOptions := {}) : LookupBinding := Id.run do
  let reject := fun key p => lookupOutcome .denied d.service key p
  let some m := d.method? methodName | return .response (reject methodName [])
  let some first := m.requirements.head? | return .response (reject methodName [])
  let addressed := m.addressedTarget? d
  let shape := addressed.getD ⟨first.info.resourceType, first.kind, first.field, first.patterns⟩
  let raw := shape.field.map (requestField request)
  let decoded : Option Path := raw.bind fun value => (Lean.fromJson? value).toOption
  let supplied := decoded.getD []
  let primary := (m.requirements.find? (fun r => r.condition.isNone && !r.parentOf &&
    r.field == shape.field && r.kind == shape.kind && r.info.resourceType == shape.resourceType)).getD first
  let finish := fun status => lookupOutcome status d.service primary.key (if primary.kind == .root then [] else supplied)
  if !request.getObj?.isOk || m.disposition != .requirements || m.requirements.any (·.perItem) || !m.resourceTarget.all (·.valid d) ||
     !rules.all (d.resourcePatterns.validSite ·.path) || !opts.names.rulesAllowed d.resourcePatterns rules then return .response (finish .denied)
  let all := requirementsFor d m request (fun _ => some []) opts.guards
  if all.isEmpty || all.any (·.unbound) then return .response (finish .denied)
  let create := addressed.any fun target => (target.kind == .parent || target.kind == .root) &&
    (m.name.splitOn "/").getLast? == (target.resourceType.splitOn "/").getLast?.map ("Create" ++ ·)
  if m.writes == some "create" || create then
    let some target := store.createDestination | return .response (finish .denied)
    if decoded.isNone && raw.any (fun v => v != .null && v != .str "") then return .response (finish .denied)
    return .response (checkedCreate d m request rules opts store shape primary supplied target all)
  if shape.kind != .resource || supplied.isEmpty then return .response (finish .denied)
  let some field := shape.field | return .response (finish .denied)
  let some res := d.resourceFor shape.resourceType | return .response (finish .denied)
  let wildcardVariables := (m.requirements.filter (fun r => r.field == shape.field && r.kind == .resource &&
    r.info.resourceType == shape.resourceType)).flatMap (·.wildcardVariables)
  if !res.patterns.any (Pattern.matchesWildcard · wildcardVariables supplied) then return .response (finish .denied)
  let indirect := anyIndirect d.resourcePatterns opts supplied || supplied.contains "-"
  let rawRange := if anyIndirect d.resourcePatterns opts supplied then (store.possibleNames.lookup supplied).getD res.patterns
    else candidates res.patterns supplied
  if !rawRange.all (·.all Atom.valid) then return .response (finish .denied)
  let pairs := regionPair res.patterns rawRange
  if pairs.isEmpty then return .response (finish .denied)
  let upsert := m.upsert?.isSome &&
    requestField request "allow_missing" == .bool true
  return .bound ⟨m, primary, field, supplied, all, res, d.resourcePatterns, pairs, indirect, upsert⟩

def selectResourceRows (p : ResourceLookupPlan) (opts : ServerOptions) (store : LookupStore) :
    Option (List ResourceRow) := do
  let mapped ← (opts.names.canonical p.catalog p.supplied).toOption
  let some resolved := mapped | return []
  let selected := candidates p.resource.patterns resolved
  let permitted := p.pairs.map Prod.fst
  guard (!selected.isEmpty && selected.all fun pat => permitted.any (coveredPattern · pat))
  return store.rows.filter fun row => selected.any (Pattern.matches · row.name) ||
    (storedAsWritten p.catalog opts.names resolved row && p.resource.patterns.any (Pattern.matches · row.name))

/-- A resolver that returns a name must select a nonempty region of the
addressed type contained in its declared range, even when storage has no rows. -/
theorem lookup_checks_primary_resolution {p opts store rows q}
    (mapped : opts.names.canonical p.catalog p.supplied = .ok (some q))
    (accepted : selectResourceRows p opts store = some rows) :
    (candidates p.resource.patterns q).isEmpty = false ∧
      ∀ pat ∈ candidates p.resource.patterns q, ∃ pair ∈ p.pairs, coveredPattern pair.1 pat = true := by
  let scope := candidates p.resource.patterns q
  have good : (!scope.isEmpty && scope.all (fun pat => (p.pairs.map Prod.fst).any (coveredPattern · pat))) = true := by
    cases test : (!scope.isEmpty && scope.all (fun pat => (p.pairs.map Prod.fst).any (coveredPattern · pat)))
    · dsimp only [scope] at test
      simp [selectResourceRows, mapped, Except.toOption, guard, failure] at accepted
      rw [test] at accepted
      contradiction
    · rfl
  obtain ⟨nonempty, envelope⟩ := Bool.and_eq_true_iff.mp good
  refine ⟨by simpa using nonempty, ?_⟩
  intro pat member
  obtain ⟨allowed, mem, covers⟩ := List.any_eq_true.mp (List.all_eq_true.mp envelope pat member)
  obtain ⟨pair, inPairs, eq⟩ := List.mem_map.mp mem
  exact ⟨pair, inPairs, by simpa [eq] using covers⟩

def matchedName (opts : ServerOptions) (plan : ResourceLookupPlan) (row : ResourceRow) : Path :=
  let resolved := (opts.names.canonical plan.catalog plan.supplied).toOption.join.getD plan.supplied
  if storedAsWritten plan.catalog opts.names resolved row then resolved else row.name

def matchedRequest (request : Json) (p : ResourceLookupPlan) (name : Path) : Json :=
  match request with
  | .obj fields => Json.obj (fields.insert p.field (Lean.toJson name))
  | _ => Json.null

/-- An as-written secondary name is a policy target. Its attributes and
evaluation faults come from the joined canonical row. -/
def matchedFacts (resources : Domain) (store : LookupStore) (opts : ServerOptions) (policyName : Path)
    (row : ResourceRow) (target : Path) : Facts :=
  if target != policyName then factsAt resources store opts target else rowFacts opts row

private def matchedServerOptions (resources : Domain) (store : LookupStore) (opts : ServerOptions) (policyName : Path)
    (row : ResourceRow) : ServerOptions :=
  let observed := fun p => if p == policyName then row.name else observedNameAt resources store opts p
  {opts with factsOf := some (matchedFacts resources store opts policyName row),
             faultsOf := opts.faultsOf.map (fun observe p => observe (observed p)),
             rowReadFailed := fun p => opts.rowReadFailed (observed p)}

def completeResourceLookup (d : Descriptor) (request : Json) (rules : List Rule) (store : LookupStore)
    (opts : ServerOptions) (p : ResourceLookupPlan) : LookupOutcome := Id.run do
  let finish := fun status => lookupOutcome status d.service p.primary.key
    (if status == .denied && p.primary.kind == .root then [] else p.supplied)
  let reject := p.denial d opts
  if let some failure := (lookupTargets p.requirements).find? (requestDenied d rules opts p) then
    return reject failure
  let opaqueFailure := fun absent =>
    (absentFailure d rules opts absent p).elim (finish .denied) reject
  let some rows := selectResourceRows p opts store | return opaqueFailure store
  match rows with
  | [] =>
    if let some failed := absentFailure d rules opts store p then return reject failed
    if p.method.itemFilter.isSome then return finish .denied
    let allowMissing := requestField request "allow_missing" == .bool true
    let rpc := (p.method.name.splitOn "/").getLast?.getD ""
    let resource := (p.resource.resourceType.splitOn "/").getLast?.getD ""
    if allowMissing && rpc == "Delete" ++ resource && (p.method.addressedTarget? d).any
        (fun target => target.kind == .resource && target.field == some "name") then return finish .ok
    if p.upsert && !p.indirect then
      let check := authorizeRequest d p.method.name request rules (lookupServerOptions d.resourcePatterns store opts)
      if check.complete then return finish .ok
      let failed := (lookupTargets p.requirements).find? (targetDenied d rules opts store)
      return failed.elim (finish .denied) reject
    return finish .notFound
  | [row] =>
    let policyName := matchedName opts p row
    let canonical := matchedRequest request p policyName
    let enforcement := matchedServerOptions d.resourcePatterns store opts policyName row
    let check := authorizeRequest d p.method.name canonical rules enforcement
    let ancillary := (lookupTargets p.requirements).find? (ancillaryDenied d rules opts store p.field)
    if check.complete && ancillary.isNone then return finish .ok
    -- An opaque refusal has the same diagnostic that the public request and
    -- ancillary rows justify in the absence of the addressed row.
    let absent := {store with rows := store.rows.erase row}
    if let some failed := absentFailure d rules opts absent p then return reject failed
    let failure := (lookupTargets p.requirements).find? fun (r, t) => r.field == some p.field &&
      (targetAt? t policyName).all (fun target => !allowed rules r target enforcement)
    return failure.elim (finish .denied) reject
  | rows => return opaqueFailure {store with rows := store.rows.filter (!rows.contains ·)}

private theorem denial_status (p : ResourceLookupPlan) (opts : ServerOptions) (e : Requirement × TargetBinding) :
    (p.denial d opts e).status = .denied := rfl

/-- A matched row can succeed only after all interceptor obligations have been
discharged and all independent targets have passed their own checks. -/
theorem matched_lookup_authorized {d request rules store opts p row}
    (selected : selectResourceRows p opts store = some [row])
    (success : (completeResourceLookup d request rules store opts p).status = .ok) :
    let name := matchedName opts p row
    let auth := authorizeRequest d p.method.name (matchedRequest request p name) rules
      (matchedServerOptions d.resourcePatterns store opts name row)
    auth.decision = "PROCEED" ∧ auth.residuals = [] ∧
      ∀ entry ∈ lookupTargets p.requirements, ancillaryDenied d rules opts store p.field entry = false := by
  dsimp only
  unfold completeResourceLookup at success
  simp only [selected, Id.run, pure] at success
  split at success
  · simp [denial_status] at success
  · split at success
    next yes =>
      obtain ⟨authorized, rest⟩ := Bool.and_eq_true_iff.mp yes
      obtain ⟨proceed, clear⟩ := Authorization.complete_iff.mp authorized
      exact ⟨proceed, clear, fun entry he => Bool.eq_false_iff.mpr
        (List.find?_eq_none.mp (Option.isNone_iff_eq_none.mp rest) entry he)⟩
    next =>
      split at success
      · simp [denial_status] at success
      · unfold Option.elim at success
        split at success <;> contradiction

/-- Both the Delete no-op and the absent-row upsert must pass every
independent target check before either can return success. -/
theorem missing_lookup_checks_all {d request rules store opts p}
    (absent : selectResourceRows p opts store = some [])
    (success : (completeResourceLookup d request rules store opts p).status = .ok) :
    missChecks d rules opts store p = none ∧
      ∀ entry ∈ lookupTargets p.requirements, ancillaryDenied d rules opts store p.field entry = false := by
  cases pre : (lookupTargets p.requirements).find? (requestDenied d rules opts p)
  · cases primary : missChecks d rules opts store p
    · cases other : (lookupTargets p.requirements).find? (ancillaryDenied d rules opts store p.field)
      · exact ⟨rfl, fun x hx => Bool.eq_false_iff.mpr (List.find?_eq_none.mp other x hx)⟩
      · simp [completeResourceLookup, absentFailure, pre, absent, primary, other, denial_status] at success
    · simp [completeResourceLookup, absentFailure, pre, absent, primary, denial_status] at success
  · simp [completeResourceLookup, pre, denial_status] at success

/-- A resolver failure or an ambiguous match uses the same public diagnostic
as a missing address. Multiple matching rows contribute no independent facts
to that diagnostic. -/
theorem inconclusive_lookup_diagnostic {d request rules store opts p denied}
    (pre : (lookupTargets p.requirements).find? (requestDenied d rules opts p) = none)
    (failure :
      (selectResourceRows p opts store = none ∧ absentFailure d rules opts store p = some denied) ∨
      ∃ a b more, selectResourceRows p opts store = some (a :: b :: more) ∧
        absentFailure d rules opts {store with rows := store.rows.filter (!(a :: b :: more).contains ·)} p = some denied) :
    completeResourceLookup d request rules store opts p = p.denial d opts denied := by
  rcases failure with ⟨selection, diagnostic⟩ | ⟨a, b, more, selection, diagnostic⟩ <;>
    simp only [completeResourceLookup, pre, selection, Id.run, pure, diagnostic, Option.elim_some]

/-- A denied match reports the public failure seen with that row removed.
This includes an independent requirement that uses the same canonical row. -/
theorem denied_match_uses_absent_diagnostic {d request rules store opts p row failed}
    (pre : (lookupTargets p.requirements).find? (requestDenied d rules opts p) = none)
    (hit : selectResourceRows p opts store = some [row])
    (diagnostic : absentFailure d rules opts {store with rows := store.rows.erase row} p = some failed)
    (denied : (completeResourceLookup d request rules store opts p).status = .denied) :
    completeResourceLookup d request rules store opts p = p.denial d opts failed := by
  simp only [completeResourceLookup, pre, hit, diagnostic, Id.run, pure] at denied ⊢
  split at denied <;> rename_i branch
  · contradiction
  · rw [ite_eq_right branch]

/-- An indirect upsert can disclose absence only after the parent requirement
passes at every concrete candidate parent, even when List is available. -/
theorem indirect_upsert_checks_each_parent {d request rules store opts plan r t candidate parent}
    (miss : selectResourceRows plan opts store = some [])
    (disclosed : (completeResourceLookup d request rules store opts plan).status = .notFound)
    (active : (r,t) ∈ lookupTargets plan.requirements) (source : r.field = some plan.field)
    (upsert : plan.upsert = true) (indirect : plan.indirect = true)
    (derived : t.targetLength < t.source.length) (member : candidate ∈ plan.region t)
    (named : singleName [candidate] = some parent) :
    permissionAt d.resourcePatterns store opts rules r parent = true := by
  have cleared : missChecks d rules opts store plan = none := by
    cases pre : (lookupTargets plan.requirements).find? (requestDenied d rules opts plan) with
    | some e => simp [completeResourceLookup, pre, denial_status] at disclosed
    | none =>
      cases check : missChecks d rules opts store plan with
      | none => rfl
      | some e => simp [completeResourceLookup, pre, miss, absentFailure, check, denial_status] at disclosed
  have test := Bool.eq_false_iff.mpr (List.find?_eq_none.mp cleared (r,t) active)
  simp [absenceBlocked, source, upsert, indirect, derived] at test
  simpa only [named] using test candidate member

/-- The direct missing-row upsert checks each write permission before a create.
When one fails, its own bound target supplies the denial diagnostic. -/
theorem direct_upsert_denied_key {d request rules store opts p failure}
    (pre : (lookupTargets p.requirements).find? (requestDenied d rules opts p) = none)
    (miss : selectResourceRows p opts store = some []) (clear : absentFailure d rules opts store p = none)
    (noFilter : p.method.itemFilter = none) (upsert : p.upsert = true) (direct : p.indirect = false)
    (failed : (lookupTargets p.requirements).find? (targetDenied d rules opts store) = some failure)
    (refused : (completeResourceLookup d request rules store opts p).status = .denied) :
    completeResourceLookup d request rules store opts p = p.denial d opts failure := by
  simp only [completeResourceLookup, pre, miss, clear, noFilter, upsert, direct, failed, Id.run,
    Option.isSome_none, Bool.false_eq_true, Bool.not_false, Bool.and_self, ↓reduceIte, pure, Option.elim_some] at refused ⊢
  split at refused <;> rename_i deletion
  · contradiction
  · rw [ite_eq_right deletion]
    split at refused <;> rename_i granted
    · contradiction
    · rw [ite_eq_right granted]

/-- Two request fields can carry the same name. Success still requires the
permission on the independent field, for a missing or a matched address. -/
theorem independent_field_authorized {d request rules store opts p r t}
    (independent : r.field ≠ some p.field) (active : (r,t) ∈ lookupTargets p.requirements)
    (row : selectResourceRows p opts store = some [] ∨ ∃ one, selectResourceRows p opts store = some [one])
    (ok : (completeResourceLookup d request rules store opts p).status = .ok) :
    targetDenied d rules opts store (r,t) = false := by
  have safe : ancillaryDenied d rules opts store p.field (r,t) = false := by
    rcases row with missing | ⟨one, matched⟩
    · exact (missing_lookup_checks_all missing ok).2 (r,t) active
    · exact (matched_lookup_authorized matched ok).2.2 (r,t) active
  simpa [ancillaryDenied, independent] using safe

/-- Public request handler. The storage lookup starts after the descriptor
establishes that the declaration and supplied name are bindable. -/
def handleResourceRequest (d : Descriptor) (methodName : String) (request : Json)
    (rules : List Rule) (store : LookupStore) (opts : ServerOptions := {}) : LookupOutcome :=
  match bindResourceLookup d methodName request rules store opts with
  | .response result => result
  | .bound plan => completeResourceLookup d request rules store opts plan

/-- If any concrete target is refused by the shared pre-row policy check, or
its credential ceiling excludes it, the handler returns the first request
denial for every store. No row, parent List permission, or resolver result
can change that diagnostic. -/
theorem lookup_preflight_denial {d rules opts p r t}
    (bound : (r, t) ∈ lookupTargets p.requirements)
    (policy : opts.ceiling.permits r.info = false ∨
      ((r.field == some p.field && p.indirect) = false ∧ anyIndirect d.resourcePatterns opts t.source = false ∧
       t.target.contains "-" = false ∧
       policyDeniesBeforeRow rules r.key t.target (opts.beforeLookup d.resourcePatterns t.target) = true)) :
    ∃ entry ∈ lookupTargets p.requirements, ∀ request store,
      completeResourceLookup d request rules store opts p = p.denial d opts entry := by
  have fails : requestDenied d rules opts p (r, t) = true := by
    rcases policy with excluded | ⟨direct, ordinary, concrete, refused⟩
    · simp [requestDenied, excluded]
    · have ordinaryTarget : "-" ∉ t.target := by simpa using concrete
      cases cap : opts.ceiling.permits r.info <;>
        simp [requestDenied, cap, direct, ordinary, ordinaryTarget, deniedBeforeJoin, refused]
  have found := List.find?_isSome.mpr ⟨_, bound, fails⟩
  cases first : (lookupTargets p.requirements).find? (requestDenied d rules opts p) with
  | none => simp [first] at found
  | some entry => exact ⟨entry, List.mem_of_find?_eq_some first, fun _ _ => by simp [completeResourceLookup, first]⟩

/-- A ceiling exclusion or the lack of any applicable permit for a direct
target is settled before storage. The first such check in descriptor order
determines the complete denial, however many predicates the method also has. -/
theorem lookup_denial_before_storage {d method request rules opts a b p r t}
    (left : bindResourceLookup d method request rules a opts = .bound p)
    (right : bindResourceLookup d method request rules b opts = .bound p)
    (bound : (r, t) ∈ lookupTargets p.requirements)
    (policy : opts.ceiling.permits r.info = false ∨
      ((r.field == some p.field && p.indirect) = false ∧ anyIndirect d.resourcePatterns opts t.source = false ∧
        t.target.contains "-" = false ∧ ∀ g ∈ rules, applies r.key t.target g = true → g.effect ≠ .permit)) :
    handleResourceRequest d method request rules a opts = handleResourceRequest d method request rules b opts := by
  have early := lookup_preflight_denial (d := d) (rules := rules) (opts := opts) bound
  obtain ⟨_, _, fixed⟩ := early (policy.imp_right fun ⟨direct, ordinary, concrete, noPermit⟩ =>
    ⟨direct, ordinary, concrete, structural_denial_before_row (Or.inl noPermit)⟩)
  simp only [handleResourceRequest, left, right, fixed]

/-- A request-dependent permission cannot establish absence at a concrete
name unless the parent is listable. An indirect range can also use a public
uniform allow for the operation, Get, or List. The `full` premise selects the
non-derived-parent branch (`t.source.length ≤ t.targetLength`), complementary to
the derived-parent branch (`t.targetLength < t.source.length`) in
`indirect_upsert_checks_each_parent`. -/
inductive OpaqueBinding (d : Descriptor) (rules : List Rule) (opts : ServerOptions) (s : LookupStore)
    (p : ResourceLookupPlan) (r : Requirement) (t : TargetBinding) : Prop where
  | concrete (source : r.field = some p.field) (full : t.source.length ≤ t.targetLength)
      (direct : p.indirect = false) (name : singleName (p.region t) = some n)
      (dependsOnRow : missingKnowledge rules r n opts = .needsRow)
      (cannotList : ∀ parent ∈ singleName ((p.pairs.map Prod.snd).eraseDups),
        canReadAt d rules opts s p.resource.resourceType "list" parent = false)
  | indirect (source : r.field = some p.field) (full : t.source.length ≤ t.targetLength)
      (mapping : p.indirect = true)
      (range : q = rangeKnowledge d rules r p.resource.resourceType (p.region t)
        ((p.pairs.map Prod.fst).eraseDups) ((p.pairs.map Prod.snd).eraseDups) opts)
      (operation : q.nonprojectingKey = true ∨ q.region ≠ .allow)
      (get : q.nonprojectingGet = true ∨ q.regionGet ≠ .allow)
      (list : q.nonprojectingList = true ∨ q.regionList ≠ .allow)

private theorem OpaqueBinding.blocks {d rules opts s p r t} (h : OpaqueBinding d rules opts s p r t) :
    absenceBlocked d rules opts s p (r, t) = true := by
  cases h with
  | concrete source full direct name dependsOnRow cannotList =>
    have noList : (singleName ((p.pairs.map Prod.snd).eraseDups)).any (canReadAt d rules opts s p.resource.resourceType "list") = false := by
      cases parent : singleName ((p.pairs.map Prod.snd).eraseDups) with
      | none => rfl
      | some n => exact cannotList n parent
    have length : ¬ t.targetLength < t.source.length := Nat.not_lt.mpr full
    simp [absenceBlocked, name, source, length, direct, dependsOnRow, noList, Disclosure.readStatus]
  | indirect source full mapping range operation get list =>
    have length : ¬ t.targetLength < t.source.length := Nat.not_lt.mpr full
    have refuse (q : Disclosure.ZeroMatch)
        (op : q.nonprojectingKey = true ∨ q.region ≠ .allow)
        (get : q.nonprojectingGet = true ∨ q.regionGet ≠ .allow)
        (list : q.nonprojectingList = true ∨ q.regionList ≠ .allow) :
        Disclosure.zeroMatchStatus q = .denied := by
      rcases op with op | op <;> rcases get with g | g <;> rcases list with l | l <;>
        simp [Disclosure.zeroMatchStatus, op, g, l]
    cases one : singleName (p.region t) <;>
      simp [absenceBlocked, one, source, length, mapping, ← range, refuse _ operation get list]

/-- Low request state can be shared while alias mappings differ. -/
def ServerOptions.withLookup (opts : ServerOptions) (lookup : Path → Option Path) : ServerOptions :=
  {opts with names := {opts.names with lookup}}

/-- Compare an absent resource with a hidden row on a bound singular method.
One permission depends on an undiscoverable row or range in the absent
world. Any concrete requirement, including another triggered guard, may deny
the matched row under the actual policy and attributes. Both worlds share the
descriptor, method, request, rules, ancillary rows, and every `ServerOptions`
field except the alias lookup (including authority mode, `factsOf`, `faultsOf`,
row failures, ceiling, remaining name-resolver settings, `canName`, and
`nonprojecting`); no agreement on the private alias mapping is required. -/
theorem resource_lookup_opacity {opts : ServerOptions} {d method request rules s p row mapA mapB opaqueReq opaqueTarget req item}
    (boundA : bindResourceLookup d method request rules s (opts.withLookup mapA) = .bound p)
    (boundB : bindResourceLookup d method request rules {s with rows := row :: s.rows}
      (opts.withLookup mapB) = .bound p)
    (absent : selectResourceRows p (opts.withLookup mapA) s = some [])
    (present : selectResourceRows p (opts.withLookup mapB) {s with rows := row :: s.rows} = some [row])
    (unseen : (opaqueReq, opaqueTarget) ∈ lookupTargets p.requirements)
    (hidden : OpaqueBinding d rules (opts.withLookup mapA) s p opaqueReq opaqueTarget)
    (declared : d.method? p.method.name = some p.method)
    (concrete : item.2.target.contains "-" = false)
    (inRequirement : item ∈ req.targets)
    (rowPolicy :
      let matched := {s with rows := row :: s.rows}
      let b := opts.withLookup mapB
      let name := matchedName b p row
      let enforcement := matchedServerOptions d.resourcePatterns matched b name row
      req ∈ serverBindings d p.method (matchedRequest request p name) enforcement false ∧
        (attributeReadFailed rules req.decl.key item.2.target enforcement = true ∨ b.ceiling.permits req.decl.info = false ∨
          decide b.mode (enforcement.available item.2.target) rules req.decl.key item.2.target = .deny)) :
    handleResourceRequest d method request rules s (opts.withLookup mapA) =
      handleResourceRequest d method request rules {s with rows := row :: s.rows} (opts.withLookup mapB) := by
  let a := opts.withLookup mapA
  let b := opts.withLookup mapB
  let matched := {s with rows := row :: s.rows}
  let name := matchedName b p row
  let canonical := matchedRequest request p name
  let enforcement := matchedServerOptions d.resourcePatterns matched b name row
  obtain ⟨active, blocked⟩ := rowPolicy
  have denied : (authorizeRequest d p.method.name canonical rules enforcement).decision ≠ "PROCEED" := by
    intro proceed
    obtain ⟨pending, ok⟩ := authorizeRequest_outer_accepts declared proceed active inRequirement
    have ⟨readable, clear⟩ := checkTarget_row_complete concrete (by simp [enforcement, matchedServerOptions]) ok
    subst pending
    have pass := checkTarget_concrete_sound concrete ok {}
    change b.ceiling.permits req.decl.info = true ∧
      decide b.mode (enforcement.available item.2.target) rules req.decl.key item.2.target = .allow at pass
    change attributeReadFailed rules req.decl.key item.2.target enforcement = true ∨ b.ceiling.permits req.decl.info = false ∨
      decide b.mode (enforcement.available item.2.target) rules req.decl.key item.2.target = .deny at blocked
    rcases blocked with failedRead | excluded | failed
    · exact Bool.noConfusion (readable.symm.trans failedRead)
    · exact Bool.noConfusion (excluded.symm.trans pass.1)
    · exact Decision.noConfusion (failed.symm.trans pass.2)
  have miss : (missChecks d rules a s p).isSome :=
    List.find?_isSome.mpr ⟨_, unseen, hidden.blocks⟩
  have samePreflight : requestDenied d rules b p = requestDenied d rules a p := rfl
  have sameMiss : missChecks d rules b s p = missChecks d rules a s p := rfl
  have sameDenial : p.denial d a = p.denial d b := rfl
  cases pre : (lookupTargets p.requirements).find? (requestDenied d rules a p) with
  | some entry =>
    simp only [handleResourceRequest, boundA, boundB]
    change completeResourceLookup d request rules s a p = completeResourceLookup d request rules matched b p
    simp [completeResourceLookup, samePreflight, sameDenial, pre]
  | none =>
    cases missed : missChecks d rules a s p with
    | none => simp [missed] at miss
    | some failure =>
      have hit : selectResourceRows p b matched = some [row] := present
      have zero : selectResourceRows p a s = some [] := absent
      have erased : {matched with rows := matched.rows.erase row} = s := by simp [matched]
      simp only [handleResourceRequest, boundA, boundB]
      change completeResourceLookup d request rules s a p = completeResourceLookup d request rules matched b p
      simp [completeResourceLookup, absentFailure, samePreflight, pre, zero, hit, missed, Authorization.complete, denied, erased, sameMiss, sameDenial,
        enforcement, canonical, name] at *

/-- When a permission cannot disclose absence, resolver failure and multiple
matches return the same complete status as the missing row. Removing every
matched row leaves the same independent rows and public resolver range. -/
theorem inconclusive_lookup_opacity {d method request rules opts s other p mapA mapB r t}
    (boundA : bindResourceLookup d method request rules s (ServerOptions.withLookup opts mapA) = .bound p)
    (boundB : bindResourceLookup d method request rules other (opts.withLookup mapB) = .bound p)
    (missing : selectResourceRows p (opts.withLookup mapA) s = some [])
    (inconclusive :
      (selectResourceRows p (opts.withLookup mapB) other = none ∧ other = s) ∨
      ∃ a b rest, selectResourceRows p (opts.withLookup mapB) other = some (a :: b :: rest) ∧
        {other with rows := other.rows.filter (!(a :: b :: rest).contains ·)} = s)
    (active : (r,t) ∈ lookupTargets p.requirements)
    (hidden : OpaqueBinding d rules (opts.withLookup mapA) s p r t) :
    handleResourceRequest d method request rules s (opts.withLookup mapA) =
      handleResourceRequest d method request rules other (opts.withLookup mapB) := by
  let a := opts.withLookup mapA
  let b := opts.withLookup mapB
  simp only [handleResourceRequest, boundA, boundB]
  change completeResourceLookup d request rules s a p = completeResourceLookup d request rules other b p
  have samePreflight : requestDenied d rules b p = requestDenied d rules a p := rfl
  have sameDenial : p.denial d a = p.denial d b := rfl
  cases pre : (lookupTargets p.requirements).find? (requestDenied d rules a p) with
  | some e => simp only [completeResourceLookup, samePreflight, pre, sameDenial, Id.run, pure]
  | none =>
    have blocked : (missChecks d rules a s p).isSome := List.find?_isSome.mpr ⟨_, active, hidden.blocks⟩
    obtain ⟨failed, found⟩ := Option.isSome_iff_exists.mp blocked
    have diagnostic (world : ServerOptions) (agree : missChecks d rules world s p = missChecks d rules a s p) :
        absentFailure d rules world s p = some failed := by simp [absentFailure, agree, found]
    have zero : selectResourceRows p a s = some [] := missing
    rw [show completeResourceLookup d request rules s a p = p.denial d a failed by
      simp [completeResourceLookup, pre, zero, diagnostic a rfl]]
    rw [sameDenial]
    symm
    apply inconclusive_lookup_diagnostic (samePreflight ▸ pre)
    rcases inconclusive with ⟨selection, rfl⟩ | ⟨first, second, rest, selection, erased⟩
    · exact Or.inl ⟨selection, diagnostic b rfl⟩
    · exact Or.inr ⟨first, second, rest, selection, erased ▸ diagnostic b rfl⟩

theorem lookup_nonmember {p opts s row} (resolved : opts.names.canonical p.catalog p.supplied = .ok (some q))
    (outside : ¬(candidates p.resource.patterns q).any (Pattern.matches · row.name))
    (noAlias : storedAsWritten p.catalog opts.names q row = false) :
    selectResourceRows p opts {s with rows := row :: s.rows} = selectResourceRows p opts s := by
  simp [selectResourceRows, resolved, Except.toOption, outside, noAlias]


namespace LookupExample

private def users : Pattern := [.lit "users", .var "id"]
private def get : Requirement := {
  key := "users.get"
  info := ⟨"api.example/User", "get", .read, false⟩
  patterns := [users]
  field := some "name" }
private def descriptor : Descriptor :=
  let method : MethodDecl := {
    name := "GetUser", disposition := .requirements, effect := .readOnly, requirements := [get]
    requestFields := some [("name", "type:api.example/User")], requestShapeKnown := true
    resourceTarget := some ⟨"api.example/User", .resource, "name", [users]⟩
    partialSource := some {
      standard := true, failedRequests := false, clientStreaming := false,
      serverStreaming := false, explicitRequirements := false, imported := false } }
  let rpc : SourceMethod := {
    serviceIndex := 0, required := false, imported := false, hasAuthorization := true, unimplemented := false,
    standard := true, requirements := none, handlerPolicy := none, response := none, importSignature := none }
  { service := "api.example", resources := [⟨"api.example/User", "users", [users], none⟩],
    methods := [method], resourceSources := [("api.example/User", false)], guardSources := some [],
    declaredMethods := [("GetUser", MethodDeclarations.sources [rpc])],
    fieldGuardsEnabled := false, rejectUnhandledFieldGuards := false }

#guard descriptor.valid

private def aliasName : Path := ["users", "me"]
private def canonical : Path := ["users", "u1"]
private def whereOwner : List Rule := [{ path := [], keys := ["users.get"], effect := .permit, pred := some "owner" }]
private def getMe (mapping : Option Path) (rows : List ResourceRow) :=
  handleResourceRequest descriptor "GetUser" (Json.mkObj [("name", Lean.toJson aliasName)]) whereOwner
    { rows, possibleNames := [(aliasName,[users])] }
    { names := { indirect := (· == aliasName), lookup := fun _ => mapping } }

set_option maxRecDepth 16384 in
/-- One predicate distinguishes hidden from visible matches. Unknown and
hidden aliases have identical complete denials; an authorized match succeeds. -/
theorem hidden_alias_witness :
    getMe none [] = getMe (some canonical) [{name := canonical, predicates := [("owner", false)]}] ∧
    (getMe none []).status = .denied ∧
    (getMe (some canonical) [{name := canonical, predicates := [("owner", true)]}]).status = .ok := by
  constructor
  · cbv
  · constructor <;> cbv

private def getWithRowFault (mode : Authority) (fault : Option Bool) :=
  let rules := whereOwner ++ [{path := [], keys := ["users.get"], effect := .forbid, pred := some "owner", mayError := true}]
  handleResourceRequest descriptor "GetUser" (Json.mkObj [("name", Lean.toJson canonical)]) rules
    {rows := [{name := canonical, predicates := [("owner", true)]}]}
    {mode, factsOf := some fun n => {faults := fun _ => if n == canonical then fault else none}}

set_option maxRecDepth 16384 in
/-- The row-only observer supplies the forbid's actual outcome at the join.
Only an observed fault under skip-errors lets the matching owner permit grant. -/
theorem joined_fault_witness :
    (getWithRowFault .skipErrors (some true)).status = .ok ∧
    (getWithRowFault .skipErrors (some false)).status = .denied ∧
    (getWithRowFault .skipErrors none).status = .denied ∧
    (getWithRowFault .failClosed (some true)).status = .denied := by
  constructor
  · cbv
  · constructor
    · cbv
    · constructor <;> cbv

end LookupExample

end Authz

namespace Authz.Oracle
open Lean

structure LookupMapping where
  supplied : Path
  canonical : Option Path
  deriving FromJson

/-- The oracle's storage adapter supplies disjoint alias mappings and the same
public range declaration whether that alias exists, points to a hidden row or
has no current mapping. -/
def lookupHandle (j : Json) (opts : ServerOptions) : Except String Json := do
  let mappings : List LookupMapping ← j.getObjValAs? _ "mappings"
  let indirect : List Path ← j.getObjValAs? _ "indirect"
  let names : NameResolver := { opts.names with
    indirect := indirect.contains
    lookup := fun n => (mappings.find? (·.supplied == n)).bind (·.canonical) }
  return toJson (handleResourceRequest (← j.getObjValAs? _ "descriptor") (← j.getObjValAs? _ "method")
    (← j.getObjVal? "request") (← j.getObjValAs? _ "rules") (← j.getObjValAs? _ "store")
    {opts with names})

end Authz.Oracle
