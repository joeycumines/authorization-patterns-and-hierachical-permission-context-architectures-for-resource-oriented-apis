import Authz.Query
import Authz.Server

namespace Authz

/-- Authoring runs on the post-edit set of affected subjects. Each entry is an
effective audience member for this key, including members without any permit. -/
structure AudienceEntry where
  holder : String
  key : String
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

def acceptPrivateRule (rule : Rule) (key : String) (directHolder : Option String)
    (audience : List AudienceEntry) (canSee : String → Path → Bool)
    (privateCapableAt : String → Path → Bool) : Bool :=
  let directViolation := rule.effect == .permit &&
    directHolder.any (fun subject => rule.hidden || !canSee subject rule.path)
  let unnameable := rule.hidden ||
    audience.any (fun member => member.key == key && !canSee member.holder rule.path)
  !directViolation && (!unnameable || (rule.pred.isNone && !rule.mayError && privateCapableAt key rule.path))

inductive Recipient where
  | subject (id : String)
  | group (id : String)
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

structure RoleDef where
  name : String
  keys : List String
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

/-- Direct selectors are already expanded against the pinned descriptor. A role
reference remains symbolic so editing the role changes every referring binding. -/
structure PolicyBinding where
  scope : Scope
  recipient : Recipient
  keys : List String := []
  roles : List String := []
  effect : Effect := .permit
  pred : Option String := none
  hidden : Bool := false
  mayError : Bool := false
  final : Bool := true
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

structure Membership where
  group : String
  subject : String
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

/-- A normalized, snapshot-pinned visibility observation. List grants cover the
potential direct children of the named type under the parent, including future IDs.
The deployment can also explicitly disclose a non-represented local scope. -/
inductive Sight where
  | get (subject : String) (resource : Path)
  | list (subject resourceType : String) (parent : Path)
  | declared (subject : String) (scope : Path)
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

structure PrivacyBoundary where
  key : String
  level : Pattern
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

structure PolicyStore where
  descriptor : Option Descriptor := none
  resources : List ResourceDecl := []
  asWrittenTypes : List String := []
  roles : List RoleDef := []
  bindings : List PolicyBinding := []
  memberships : List Membership := []
  visibility : List Sight := []
  boundaries : List PrivacyBoundary := []
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

/-- Resource-only catalogs describe name geometry. Validating a binding with
effective permission keys also requires the pinned descriptor's binding domains. -/
def PolicyStore.catalog (s : PolicyStore) := s.descriptor.elim s.resources (·.resources)

def PolicyStore.nameResolver (s : PolicyStore) (base : NameResolver := {}) : NameResolver :=
  let configured := asWrittenDomain? s.catalog s.asWrittenTypes
  { base with asWritten := base.asWritten ++ configured.getD [], configured := base.configured && configured.isSome }

def PolicyStore.effectiveRule (s : PolicyStore) (b : PolicyBinding) : Rule :=
  let roleKeys := (s.roles.filter (fun r => b.roles.contains r.name)).flatMap (·.keys)
  { path := b.scope.path, keys := (b.keys ++ roleKeys).eraseDups, effect := b.effect,
    pred := b.pred, hidden := b.hidden, mayError := b.mayError, final := b.final }

def PolicyStore.subjects (s : PolicyStore) : Recipient → List String
  | .subject id => [id]
  | .group id => (s.memberships.filter (·.group == id)).map (·.subject)

def PolicyStore.rulesFor (s : PolicyStore) (subject : String) : List Rule :=
  (s.bindings.filter (fun b => (s.subjects b.recipient).contains subject)).map s.effectiveRule

/-- A snapshot observation supplies only the primary read at its observed target.
Every other active permission still needs independent policy evidence. -/
def observationKeys (seen : Bool) (method : MethodDecl) (address : ResourceTarget) : List (Option String) :=
  none :: (if seen then method.requirements.filterMap fun r =>
    if r.info.resourceType == address.resourceType && r.kind == address.kind && r.field == address.field &&
        !r.parentOf && r.condition.isNone then some (some r.key) else none
    else [])

def readEvidence (rules : List Rule) (observedKey : Option String) (anchor : Path)
    (req : BoundRequirement) (target : Path) : List Rule :=
  if observedKey == some req.decl.key && target == anchor then
    rules ++ [{ path := anchor, keys := [req.decl.key], effect := .permit }]
  else rules

def readAuthorized (d : Descriptor) (method : MethodDecl) (request : Lean.Json)
    (rules : List Rule) (observedKey : Option String) (anchor : Path) :=
  let active := requirementsFor d method request
  !active.isEmpty && active.all fun req =>
    !req.unbound && !req.resolverFault && req.wildcard == .concrete && req.targets.all fun pair =>
      let t := pair.2.target
      let evidence := readEvidence rules observedKey anchor req t
      pathOk t && evidence.all (pathOk ·.path) && classify (evidence.filter (applies req.decl.key t)) == .allow

theorem readAuthorized_all_targets {d method request rules observedKey anchor}
    (allowed : readAuthorized d method request rules observedKey anchor = true) :
    (requirementsFor d method request).isEmpty = false ∧
      ∀ req ∈ requirementsFor d method request, req.unbound = false ∧ req.resolverFault = false ∧
        req.wildcard = .concrete ∧ ∀ pair ∈ req.targets, ∀ mode facts,
          decide mode facts (readEvidence rules observedKey anchor req pair.2.target) req.decl.key pair.2.target = .allow := by
  obtain ⟨nonempty, all⟩ := Bool.and_eq_true_iff.mp allowed
  refine ⟨by simpa using nonempty, ?_⟩
  intro req active
  have each := List.all_eq_true.mp all req active
  have flags := (Bool.and_eq_true_iff.mp each).1
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at flags
  refine ⟨flags.1.1, flags.1.2, flags.2, ?_⟩
  intro pair bound mode facts
  have target := List.all_eq_true.mp (Bool.and_eq_true_iff.mp each).2 pair bound
  simp only [Bool.and_eq_true, beq_iff_eq] at target
  simp only [decide, target.1.1, target.1.2, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  exact classified_allow _ _ _ target.2

/-- A permission may be granted at a site only if it can bind there or below it. -/
def PolicyStore.keyReaches (s : PolicyStore) (key : String) (p : Path) :=
  s.descriptor.any fun d => (d.domain key).any (Pattern.reach · p)

private def PolicyStore.visibilityBindings (s : PolicyStore) (holder : String) (p : Path)
    (ancestors : List Path) :=
  s.bindings.filter fun b =>
    (s.subjects b.recipient).contains holder && (b.effect == .forbid ||
      (!b.hidden && (b.recipient == .subject holder ||
        (strictDescendant b.scope.path p && ancestors.contains b.scope.path))))

private def PolicyStore.observesResource (s : PolicyStore) (subject : String) (p : Path)
    (rules : List Rule) (resource : ResourceDecl) (pat : Pattern) : Bool := Id.run do
  let some d := s.descriptor | return false
  if !Pattern.matches pat p then return false
  let parent := p.take (Pattern.parent pat).length
  let visible := fun op target sight => (d.readMethods resource.resourceType op).any fun (method, binding) =>
    (binding.readRequest? target).any fun request =>
      (observationKeys (s.visibility.contains sight) method binding).any fun k =>
        readAuthorized d method request rules k target
  return visible "get" p (.get subject p) || visible "list" parent (.list subject resource.resourceType parent)

private def localParent (resources : List ResourceDecl) (p : Path) :=
  let patterns : Domain := resources.flatMap (·.patterns)
  patterns.isResource p && !(Domain.contains patterns p)

def PolicyStore.directlyNameable (s : PolicyStore) (holder : String) (p : Path) :=
  p.isEmpty || (localParent s.catalog p && s.visibility.contains (.declared holder p)) ||
    s.bindings.any (fun b => b.recipient == .subject holder && b.effect == .permit &&
      !b.hidden && b.scope.path == p && (s.effectiveRule b).keys.any (s.keyReaches · p))

private def PolicyStore.nameableStep (s : PolicyStore) (holder : String) (p : Path)
    (ancestors : List Path) :=
  s.directlyNameable holder p ||
    let rules := (s.visibilityBindings holder p ancestors).map s.effectiveRule
    s.catalog.any fun r => r.patterns.any (s.observesResource holder p rules r)

/-- Visit prefixes from the root outwards. Each step may use group permits only
at strictly earlier sites for which a disclosure has already been established. -/
private def PolicyStore.namedPrefixes (s : PolicyStore) (holder : String) : Path → List Path
  | [] => [[]]
  | x :: xs =>
    let prior := s.namedPrefixes holder xs
    let p := (x :: xs).reverse
    if s.nameableStep holder p prior then p :: prior else prior

def PolicyStore.canName (s : PolicyStore) (holder : String) (scope : Scope) :=
  let p := match scope with
    | .serviceRoot => []
    | .resource path => path
    | .collection path => path.dropLast
  s.nameableStep holder p (s.namedPrefixes holder p.reverse.tail)

/-- Evidence for disclosing a name. A read can use any subset of the holder's
visible permits, but must retain every forbid. Every group permit used in the
read has a separate, finite derivation for its ancestor site. -/
inductive Nameable (s : PolicyStore) (holder : String) : Path → Prop where
  | root : Nameable s holder []
  | localScope {p} (site : localParent s.catalog p = true)
      (seen : Sight.declared holder p ∈ s.visibility) : Nameable s holder p
  | direct {p b d key pat} (binding : b ∈ s.bindings) (recipient : b.recipient = .subject holder)
      (permit : b.effect = .permit) (visible : b.hidden = false) (site : b.scope.path = p)
      (selected : key ∈ (s.effectiveRule b).keys) (descriptor : s.descriptor = some d)
      (declared : pat ∈ d.domain key) (reaches : Pattern.reach pat p = true) : Nameable s holder p
  | read {p} (evidence : List PolicyBinding)
      (held : ∀ b ∈ evidence, b ∈ s.bindings ∧ holder ∈ s.subjects b.recipient)
      (forbids : ∀ b ∈ s.bindings, holder ∈ s.subjects b.recipient → b.effect = .forbid → b ∈ evidence)
      (publicPermits : ∀ b ∈ evidence, b.effect = .permit → b.hidden = false ∧
        (b.recipient = .subject holder ∨ strictDescendant b.scope.path p = true))
      (ancestors : ∀ b ∈ evidence, b.effect = .permit → b.recipient ≠ .subject holder →
        Nameable s holder b.scope.path)
      {r pat} (resource : r ∈ s.catalog) (pattern : pat ∈ r.patterns)
      (allowed : s.observesResource holder p (evidence.map s.effectiveRule) r pat = true) : Nameable s holder p

private theorem PolicyStore.nameableStep_sound {s : PolicyStore} {holder p prior}
    (earlier : ∀ q ∈ prior, Nameable s holder q) (hit : s.nameableStep holder p prior = true) :
    Nameable s holder p := by
  rcases Bool.or_eq_true_iff.mp hit with direct | read
  · simp only [directlyNameable, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
      List.isEmpty_iff, List.contains_iff_mem, beq_iff_eq, Bool.not_eq_true'] at direct
    rcases direct with ((rfl | ⟨site, seen⟩) | ⟨b, hb, ⟨⟨⟨⟨who, eff⟩, visible⟩, site⟩, key, hk, reaches⟩⟩)
    · exact .root
    · exact .localScope site seen
    · simp only [keyReaches, Option.any_eq_true, List.any_eq_true] at reaches
      obtain ⟨d, hd, pat, hp, hr⟩ := reaches
      exact .direct hb who eff visible site hk hd hp hr
  · obtain ⟨r, hr, allowed⟩ := List.any_eq_true.mp read
    obtain ⟨pat, hp, ok⟩ := List.any_eq_true.mp allowed
    apply Nameable.read (s.visibilityBindings holder p prior) _ _ _ _ hr hp ok
    · intro b hb
      obtain ⟨bound, h⟩ := List.mem_filter.mp hb
      exact ⟨bound, List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp h).1⟩
    · intro b hb member eff
      exact List.mem_filter.mpr ⟨hb, by simp [member, eff]⟩
    · intro b hb permit
      have h := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hb).2).2
      simp [permit, Bool.and_eq_true, Bool.or_eq_true] at h
      exact ⟨h.1, h.2.imp_right And.left⟩
    · intro b hb permit indirect
      have h := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hb).2).2
      simp [permit, indirect, Bool.and_eq_true] at h
      exact earlier _ h.2.2

private theorem PolicyStore.namedPrefixes_sound (s : PolicyStore) (holder : String) (rev : Path) :
    ∀ q ∈ s.namedPrefixes holder rev, Nameable s holder q := by
  induction rev with
  | nil => simpa [namedPrefixes] using (Nameable.root (s := s) (holder := holder))
  | cons x xs ih =>
    intro q hq
    simp only [namedPrefixes] at hq
    split at hq
    · rename_i accepted
      rcases List.mem_cons.mp hq with rfl | old
      · exact nameableStep_sound ih accepted
      · exact ih q old
    · exact ih q hq

theorem canName_resource_sound (s : PolicyStore) (holder : String) (p : Path)
    (named : s.canName holder (.resource p) = true) : Nameable s holder p :=
  s.nameableStep_sound (s.namedPrefixes_sound holder p.reverse.tail) named

def PolicyStore.privateCapableAt (s : PolicyStore) (key : String) (p : Path) :=
  s.boundaries.any (fun b => b.key == key && Pattern.reach b.level p)

def Recipient.directHolder : Recipient → Option String
  | .subject id => some id
  | .group _ => none

def PolicyStore.acceptsKey (s : PolicyStore) (b : PolicyBinding) (k : String) :=
  let audience := (s.subjects b.recipient).map (fun subject => AudienceEntry.mk subject k)
  s.keyReaches k b.scope.path && acceptPrivateRule (s.effectiveRule b) k b.recipient.directHolder audience
    (fun holder _ => s.canName holder b.scope) s.privateCapableAt

def PolicyStore.validSite (s : PolicyStore) : Scope → Bool
  | .serviceRoot => true
  | .collection _ => false
  | .resource p => !p.isEmpty && Domain.validSite (s.catalog.flatMap (·.patterns)) p

def PolicyStore.admissible (s : PolicyStore) :=
  s.descriptor.all Descriptor.valid &&
  s.nameResolver.rulesAllowed (s.catalog.flatMap (·.patterns)) (s.bindings.map s.effectiveRule) &&
  s.bindings.all fun b => s.validSite b.scope && (s.effectiveRule b).keys.all (s.acceptsKey b)

inductive PolicyEdit where
  | nameModes (types : List String)
  | rules (bindings : List PolicyBinding)
  | roleDefinitions (roles : List RoleDef)
  | groupMemberships (members : List Membership)
  | visibility (facts : List Sight)
  | privacyBoundaries (levels : List PrivacyBoundary)
  deriving Repr, Lean.FromJson, Lean.ToJson

def PolicyStore.edit (s : PolicyStore) : PolicyEdit → PolicyStore
  | .nameModes types => {s with asWrittenTypes := types}
  | .rules b => { s with bindings := b }
  | .roleDefinitions rs => { s with roles := rs }
  | .groupMemberships ms => { s with memberships := ms }
  | .visibility vs => { s with visibility := vs }
  | .privacyBoundaries bs => { s with boundaries := bs }

/-- Commit all writes atomically or retain the entire previous store. The guard
re-expands roles and recomputes subjects and visibility on the candidate store. -/
def PolicyStore.commit (s : PolicyStore) (writes : List PolicyEdit) :=
  let candidate := writes.foldl PolicyStore.edit s
  if candidate.admissible then candidate else s

def PolicyStore.run (s : PolicyStore) (transactions : List (List PolicyEdit)) :=
  transactions.foldl PolicyStore.commit s

theorem rejected_commit_retains_store (s : PolicyStore) (writes : List PolicyEdit)
    (invalid : (writes.foldl PolicyStore.edit s).admissible = false) :
    s.commit writes = s := by simp [PolicyStore.commit, invalid]

theorem commit_admissible {s : PolicyStore} (h : s.admissible) (writes) :
    (s.commit writes).admissible = true := by
  unfold PolicyStore.commit
  dsimp only
  split <;> assumption

theorem policy_trace_admissible {s : PolicyStore} (h : s.admissible) (transactions) :
    (s.run transactions).admissible = true := by
  induction transactions generalizing s with
  | nil => exact h
  | cons ws ts ih => exact ih (commit_admissible h ws)

/-- Every subject's effective rules meet the server's as-written policy guard
after an arbitrary sequence of commits, including changes to the name modes. -/
theorem reachable_as_written_rules {s : PolicyStore} (initial : s.admissible) (transactions subject) :
    let current := s.run transactions
    current.nameResolver.rulesAllowed (current.catalog.flatMap (·.patterns)) (current.rulesFor subject) = true := by
  let current := s.run transactions
  have guardAll := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (policy_trace_admissible initial transactions)).1).2
  have ⟨configured, allRules⟩ := Bool.and_eq_true_iff.mp guardAll
  apply Bool.and_eq_true_iff.mpr
  refine ⟨configured, ?_⟩
  simp only [Bool.not_eq_true', List.any_eq_false] at allRules ⊢
  intro r hr
  obtain ⟨binding, selected, rfl⟩ := List.mem_map.mp hr
  exact allRules _ (List.mem_map.mpr ⟨binding,(List.mem_filter.mp selected).1,rfl⟩)

theorem reachable_grant_sites {s : PolicyStore} (initial : s.admissible) (transactions)
    (b : PolicyBinding) (hb : b ∈ (s.run transactions).bindings) :
    (s.run transactions).validSite b.scope = true :=
  (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (policy_trace_admissible initial transactions)).2 b hb)).1

/-- Every effective key in a committed binding reaches a served binding domain,
including keys contributed by a role edited in the same transaction. -/
theorem reachable_key_domain {s : PolicyStore} (initial : s.admissible) (transactions)
    (b : PolicyBinding) (key : String) (hb : b ∈ (s.run transactions).bindings)
    (hk : key ∈ ((s.run transactions).effectiveRule b).keys) :
    ∃ d, (s.run transactions).descriptor = some d ∧
      ∃ pat ∈ d.domain key, Pattern.reach pat b.scope.path = true := by
  have checked := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (policy_trace_admissible initial transactions)).2 b hb
  have accepted := List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 key hk
  have reaches := (Bool.and_eq_true_iff.mp accepted).1
  simpa only [PolicyStore.keyReaches, Option.any_eq_true, List.any_eq_true] using reaches

theorem acceptPrivateRule_iff (r k direct audience see capable) :
    acceptPrivateRule r k direct audience see capable = true ↔
    (r.effect = .permit → ∀ holder ∈ direct, r.hidden = false ∧ see holder r.path = true) ∧
    ((r.hidden = true ∨ ∃ a ∈ audience, a.key = k ∧ see a.holder r.path = false) →
      r.pred = none ∧ r.mayError = false ∧ capable k r.path = true) := by
  cases direct <;> cases r with
  | mk path keys eff pred hidden mayErr fin =>
    cases eff <;> cases hidden <;> cases pred <;> cases mayErr <;>
      simp [acceptPrivateRule, ← Bool.not_eq_true] <;> grind

/-- Every unnameable rule for an affected subject, throughout an unbounded trace
of policy transactions, is unconditional, error-free and covered by a predeclared boundary. -/
theorem reachable_private_rules {s : PolicyStore} (initial : s.admissible) (transactions)
    (b : PolicyBinding) (key holder : String)
    (hb : b ∈ (s.run transactions).bindings)
    (hk : key ∈ ((s.run transactions).effectiveRule b).keys)
    (who : holder ∈ (s.run transactions).subjects b.recipient)
    (privateRule : b.hidden = true ∨ (s.run transactions).canName holder b.scope = false) :
    b.pred = none ∧ b.mayError = false ∧ (s.run transactions).privateCapableAt key b.scope.path = true := by
  let current := s.run transactions
  have checked := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (policy_trace_admissible initial transactions)).2 b hb
  have guarded := List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 key hk
  simp only [PolicyStore.acceptsKey] at guarded
  have condition := (acceptPrivateRule_iff ..).mp (Bool.and_eq_true_iff.mp guarded).2
  apply condition.2
  rcases privateRule with marked | invisible
  · exact Or.inl marked
  · exact Or.inr ⟨⟨holder, key⟩, List.mem_map.mpr ⟨holder, who, rfl⟩, rfl, invisible⟩

def PolicyStore.visibilityRules (s : PolicyStore) (holder : String) (p : Path) : List Rule :=
  (s.visibilityBindings holder p (s.namedPrefixes holder p.reverse.tail)).map s.effectiveRule

/-- Without a privacy boundary or an independent direct disclosure, publishing a
resource-scoped rule requires an actual, fully authorized Get or List invocation. -/
theorem reachable_public_rule_read {s : PolicyStore} (initial : s.admissible) (transactions)
    (b : PolicyBinding) (key holder : String) (p : Path) (site : b.scope = .resource p)
    (hb : b ∈ (s.run transactions).bindings) (hk : key ∈ ((s.run transactions).effectiveRule b).keys)
    (who : holder ∈ (s.run transactions).subjects b.recipient)
    (noBoundary : (s.run transactions).privateCapableAt key p = false)
    (noDirect : (s.run transactions).directlyNameable holder p = false) :
    ∃ d, (s.run transactions).descriptor = some d ∧ ∃ r ∈ d.resources, ∃ pat ∈ r.patterns,
      Pattern.matches pat p = true ∧ ∃ op target sight,
      ((op = "get" ∧ target = p ∧ sight = Sight.get holder p) ∨
        (op = "list" ∧ target = p.take (Pattern.parent pat).length ∧ sight = Sight.list holder r.resourceType target)) ∧
      ∃ pair ∈ d.readMethods r.resourceType op, ∃ request, pair.2.readRequest? target = some request ∧
        ∃ k ∈ observationKeys ((s.run transactions).visibility.contains sight) pair.1 pair.2,
        readAuthorized d pair.1 request ((s.run transactions).visibilityRules holder p) k target = true := by
  let current := s.run transactions
  have named : current.canName holder b.scope = true := by
    cases h : current.canName holder b.scope with
    | true => rfl
    | false =>
      have capable := (reachable_private_rules initial transactions b key holder hb hk who (Or.inr h)).2.2
      simp [site, Scope.path, noBoundary] at capable
  change current.directlyNameable holder p = false at noDirect
  rw [site] at named
  simp only [PolicyStore.canName, PolicyStore.nameableStep, noDirect, Bool.false_or] at named
  obtain ⟨r, hr, hit⟩ := List.any_eq_true.mp named
  obtain ⟨pat, hp, read⟩ := List.any_eq_true.mp hit
  cases hd : current.descriptor with
  | none => simp [PolicyStore.observesResource, hd] at read
  | some d =>
    have hr' : r ∈ d.resources := by simpa [PolicyStore.catalog, hd] using hr
    cases hm : Pattern.matches pat p with
    | false => simp [PolicyStore.observesResource, hd, hm] at read
    | true =>
      refine ⟨d, rfl, r, hr', pat, hp, hm, ?_⟩
      simp only [PolicyStore.observesResource, hd, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Id.run, pure, Bool.or_eq_true, List.any_eq_true, Option.any_eq_true] at read
      rcases read with get | list
      · exact ⟨"get", p, .get holder p, Or.inl ⟨rfl, rfl, rfl⟩, get⟩
      · exact ⟨"list", _, _, Or.inr ⟨rfl, rfl, rfl⟩, list⟩

/-- Withhold the key wherever a declared private level can still be reached
strictly below the requested anchor, even in a store with no private binding. -/
def PolicyStore.nonprojecting (s : PolicyStore) (key : String) (anchor : Path) :=
  s.boundaries.any fun b => b.key == key && Pattern.reach b.level anchor && anchor.length < b.level.length

def PolicyStore.projectionOptions (s : PolicyStore) (subject : String) (anchor : Path)
    (key : String) (opts : ProjectOptions) : ProjectOptions :=
  {opts with nonprojecting := s.nonprojecting key anchor, canName := fun p => s.canName subject (.resource p)}

private theorem reached_length {p : Pattern} {xs : Path} (hit : Pattern.reach p xs = true) :
    xs.length ≤ p.length := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
    cases p with
    | nil => simp [Pattern.reach, Pattern.consume] at hit
    | cons a p =>
      cases ha : a.accepts x <;> simp [Pattern.reach, Pattern.consume, ha] at hit
      exact Nat.succ_le_succ (ih hit)

private theorem private_descendant_nonprojecting {s : PolicyStore} {key : String} {anchor site : Path}
    (privateSite : s.privateCapableAt key site = true) (below : strictDescendant anchor site = true) :
    s.nonprojecting key anchor = true := by
  obtain ⟨b, mem, hb⟩ := List.any_eq_true.mp privateSite
  obtain ⟨hk, reach⟩ := Bool.and_eq_true_iff.mp hb
  obtain ⟨pref, ne⟩ := Bool.and_eq_true_iff.mp below
  have pref' := List.isPrefixOf_iff_prefix.mp pref
  have shorter : anchor.length < site.length := by
    have hne : anchor ≠ site := by simpa using ne
    exact Nat.lt_of_le_of_ne pref'.length_le (fun e => hne (pref'.eq_of_length e))
  refine List.any_eq_true.mpr ⟨b, mem, ?_⟩
  have le := reached_length reach
  obtain ⟨tail, rfl⟩ := pref'
  have ha : Pattern.reach b.level anchor = true := by
    unfold Pattern.reach at *
    rw [Pattern.consume_append] at reach
    cases h : Pattern.consume b.level anchor <;> simp_all
  simp [hk, ha, Nat.lt_of_lt_of_le shorter le]

private theorem admissible_effective_rule {s : PolicyStore} (admitted : s.admissible)
    {subject key : String} {r : Rule} (mem : r ∈ s.rulesFor subject) (hk : key ∈ r.keys)
    (privateRule : r.hidden = true ∨ s.canName subject (.resource r.path) = false) :
    r.pred = none ∧ r.mayError = false ∧ s.privateCapableAt key r.path = true := by
  obtain ⟨b, hmem, rfl⟩ := List.mem_map.mp mem
  obtain ⟨hb, recipient⟩ := List.mem_filter.mp hmem
  have valid := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp admitted).2 b hb)).1
  have same : s.canName subject (.resource b.scope.path) = s.canName subject b.scope := by
    cases h : b.scope <;> simp_all [PolicyStore.canName, PolicyStore.validSite, Scope.path]
  apply reachable_private_rules admitted [] b key subject hb hk (List.contains_iff_mem.mp recipient)
  simpa only [PolicyStore.effectiveRule, PolicyStore.run, List.foldl_nil, same] using privateRule

/-- The projector reaches its obstruction guard only for projecting keys.
In an admitted store it never raises the runtime alert on those keys. -/
theorem admissible_no_private_obstruction {s : PolicyStore} (admitted : s.admissible)
    (subject key : String) (anchor : Path) (opts : ProjectOptions)
    (projects : s.nonprojecting key anchor = false) :
    (s.rulesFor subject).any (privateObstruction (s.projectionOptions subject anchor key opts) key anchor) = false := by
  apply List.any_eq_false.mpr
  intro r mem
  intro ob
  obtain ⟨app, how⟩ := Bool.and_eq_true_iff.mp ob
  obtain ⟨hk, hidden⟩ := Bool.and_eq_true_iff.mp app
  obtain ⟨hp, errorFree, capable⟩ := admissible_effective_rule admitted mem (List.contains_iff_mem.mp hk)
    (by simpa [PolicyStore.projectionOptions] using (Bool.or_eq_true_iff.mp hidden))
  rcases Bool.or_eq_true_iff.mp how with below | cond
  · simp [private_descendant_nonprojecting capable below] at projects
  · simp [hp, errorFree] at cond


/-- Bind policy lookup, visibility and privacy levels to the same committed state. -/
def PolicyStore.queryView (s : PolicyStore) (subject : String) (v : Query.View) : Query.View :=
  {v with
    resources := s.catalog.flatMap ResourceDecl.patterns
    indirect := fun p => !Domain.contains s.nameResolver.asWritten p && v.indirect p
    options := fun a k => s.projectionOptions subject a k (v.options a k)}

theorem as_written_query_uses_supplied_name {s : PolicyStore} {p : Path}
    (configured : Domain.contains s.nameResolver.asWritten p = true) (subject view) :
    (s.queryView subject view).indirectAt p = false := by
  simp [Query.View.indirectAt, PolicyStore.queryView, configured]

def PolicyStore.queryWorld (s : PolicyStore) (subject : String)
    (aliases : Query.World) : Query.World :=
  {aliases with rules := s.rulesFor subject}

private def PolicyStore.publicOptions (s : PolicyStore) (v : Query.View) (a : Path) (k : String) :=
  {v.options a k with nonprojecting := s.nonprojecting k a, canName := fun _ => true}

private theorem PolicyStore.context_public_options {s : PolicyStore} (admitted : s.admissible)
    (subject : String) (v : Query.View) (anchor : Path) :
    projectContext (s.rulesFor subject) v.keys (s.catalog.flatMap ResourceDecl.patterns) anchor v.profile
      ((s.queryView subject v).options anchor) =
    projectContext (s.rulesFor subject) v.keys (s.catalog.flatMap ResourceDecl.patterns) anchor v.profile
      (s.publicOptions v anchor) := by
  unfold projectContext
  split
  · rfl
  dsimp only
  congr 1 <;> congr 1 <;> apply List.map_congr_left <;> rintro ⟨key, d⟩ _
  all_goals
    let opts := {v.options anchor key with profile := v.profile}
    cases h : s.nonprojecting key anchor with
    | true => simp [projectKey, queryView, projectionOptions, publicOptions, h]
    | false =>
      have no := admissible_no_private_obstruction admitted subject key anchor opts h
      let rules := (s.rulesFor subject).filter (·.keys.contains key)
      have actual : rules.any (privateObstruction (s.projectionOptions subject anchor key opts) key anchor) = false :=
        List.any_eq_false.mpr fun r mem => List.any_eq_false.mp no _ (List.mem_filter.mp mem).1
      have publicNo : rules.any (privateObstruction {s.publicOptions v anchor key with profile := v.profile} key anchor) = false := by
        apply List.any_eq_false.mpr
        intro r mem ob
        apply List.any_eq_false.mp actual r mem
        simp only [privateObstruction, publicOptions, Bool.not_true, Bool.or_false, Bool.and_eq_true] at ob
        exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ob.1.1,
          Bool.or_eq_true_iff.mpr (Or.inl ob.1.2)⟩, ob.2⟩
      unfold projectKey
      simp only [queryView]
      change (if s.nonprojecting key anchor || !pathOk anchor || !rules.all (pathOk ·.path) then _ else
        if rules.any (privateObstruction (s.projectionOptions subject anchor key opts) key anchor) then _ else _) =
        (if s.nonprojecting key anchor || !pathOk anchor || !rules.all (pathOk ·.path) then _ else
        if rules.any (privateObstruction {s.publicOptions v anchor key with profile := v.profile} key anchor) then _ else _)
      rw [actual, publicNo]
      rfl

private theorem PolicyStore.rules_valid_sites {s : PolicyStore} (admitted : s.admissible) (subject : String) :
    (s.rulesFor subject).all (Domain.validSite (s.catalog.flatMap ResourceDecl.patterns) ·.path) = true := by
  apply List.all_eq_true.mpr
  intro r mem
  obtain ⟨b, candidate, rfl⟩ := List.mem_map.mp mem
  have valid := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp admitted).2 b (List.mem_filter.mp candidate).1)).1
  change Domain.validSite _ b.scope.path = true
  cases h : b.scope with
  | serviceRoot => rfl
  | collection p => simp [PolicyStore.validSite, h] at valid
  | resource p =>
    rw [h] at valid
    exact (Bool.and_eq_true_iff.mp valid).2

/-- In a projecting branch, a rule at or above the anchor can affect the
answer. Below it, only rules that the subject can name are public inputs. -/
noncomputable def PolicyStore.observableAt (s : PolicyStore) (subject key : String) (anchor : Path) (r : Rule) : Bool := by
  classical
  exact r.comparableAt key anchor &&
    (r.path.isPrefixOf anchor || (!r.hidden && Decidable.decide (Nameable s subject r.path)))

private theorem PolicyStore.observable_rules {s : PolicyStore} (admitted : s.admissible)
    (subject key : String) (anchor : Path) (projects : s.nonprojecting key anchor = false) :
    (s.rulesFor subject).filter (Rule.comparableAt key anchor) =
      (s.rulesFor subject).filter (s.observableAt subject key anchor) := by
  apply List.filter_congr
  intro r mem
  cases hc : r.comparableAt key anchor with
  | false => simp [observableAt, hc]
  | true =>
    simp only [observableAt, hc, Bool.true_and, Bool.true_eq]
    obtain ⟨hk, comparable⟩ := Bool.and_eq_true_iff.mp hc
    cases ha : r.path.isPrefixOf anchor with
    | true => simp
    | false =>
      have below : strictDescendant anchor r.path = true := by
        have pref := (Bool.or_eq_true_iff.mp comparable).resolve_left (by simp [ha])
        have ne : anchor ≠ r.path := fun eq => Bool.noConfusion (ha.symm.trans (List.isPrefixOf_iff_prefix.mpr (eq ▸ List.prefix_rfl)))
        simp [strictDescendant, pref, ne]
      have ok := List.any_eq_false.mp (admissible_no_private_obstruction admitted subject key anchor {} projects) r mem
      simp [privateObstruction, below, projectionOptions] at ok
      have safe : r.hidden = false ∧ s.canName subject (.resource r.path) = true := by
        simpa [Bool.not_eq_true] using ok (List.contains_iff_mem.mp hk)
      simp [safe.1, canName_resource_sound s subject r.path safe.2]


/-- Policy twins share the public catalog and declared privacy levels. Rules
elsewhere in the tree and private descendants need not agree. Each alias must
give the same visible resolution in the two worlds. -/
structure PolicyStore.QueryAgreement (s t : PolicyStore) (subject : String) (v : Query.View)
    (left right : Query.World) (asked : List Path) : Prop where
  resources : s.catalog = t.catalog
  nameModes : s.asWrittenTypes = t.asWrittenTypes
  boundaries : s.boundaries = t.boundaries
  aliases : ∀ p, (s.queryView subject v).indirectAt p = true →
    (left.resolve p).filter (left.mayResolve subject p) = (right.resolve p).filter (right.mayResolve subject p)
  mappedLeft : Query.ValidMappings (s.queryView subject v) left
  mappedRight : Query.ValidMappings (t.queryView subject v) right
  rules : ∀ anchor ∈ (Query.resolveNames (s.queryView subject v) left subject asked).map Prod.snd,
    ∀ k d, (k, d) ∈ v.keys → s.nonprojecting k anchor = false →
    (s.rulesFor subject).filter (s.observableAt subject k anchor) =
      (t.rulesFor subject).filter (t.observableAt subject k anchor)

def PolicyStore.query (s : PolicyStore) (v : Query.View)
    (aliases : Query.World) (stamp : Query.Stamp) (asked : List Path) :=
  Query.queryPermissionContexts (s.queryView stamp.subject v) (s.queryWorld stamp.subject aliases) stamp asked

/-- A complete response at the same public revision, including holes, budgets,
key sets, echoed anchors and expiry, depends only on the admitted public inputs. -/
theorem admissible_response_private_twins {s t : PolicyStore} (hs : s.admissible) (ht : t.admissible)
    {v left right asked} (stamp : Query.Stamp) (twins : s.QueryAgreement t stamp.subject v left right asked) :
    s.query v left stamp asked = t.query v right stamp asked := by
  let subject := stamp.subject
  let va := s.queryView subject v
  let vb := t.queryView subject v
  let wa := s.queryWorld subject left
  let wb := t.queryWorld subject right
  let shared := {va with options := s.publicOptions v}
  have sameView : {vb with options := t.publicOptions v} = shared := by
    simp [shared, va, vb, PolicyStore.queryView, PolicyStore.nameResolver, twins.resources, twins.nameModes]
    funext a k
    simp [PolicyStore.publicOptions, PolicyStore.nonprojecting, twins.boundaries]
  have normA := Query.queryPermissionContexts_congr_options va wa stamp asked (s.publicOptions v)
    (s.context_public_options hs subject v)
  have normB := Query.queryPermissionContexts_congr_options vb wb stamp asked (t.publicOptions v)
    (t.context_public_options ht subject v)
  rw [sameView] at normB
  refine normA.trans (Eq.trans ?_ normB.symm)
  apply Query.response_private_twins
  · exact twins.aliases
  · exact twins.mappedLeft
  · intro p site target mapping
    change Query.View.indirectAt shared p = true at site
    change Query.validCanonical shared target = true
    rw [← sameView] at site ⊢
    exact twins.mappedRight p site target mapping
  · exact s.rules_valid_sites hs subject
  · change (t.rulesFor subject).all (Domain.validSite (s.catalog.flatMap ResourceDecl.patterns) ·.path) = true
    rw [twins.resources]
    exact t.rules_valid_sites ht subject
  · intro anchor member k d known projecting
    have ps : s.nonprojecting k anchor = false := projecting
    have pt : t.nonprojecting k anchor = false := by simpa [PolicyStore.nonprojecting, twins.boundaries] using ps
    exact (s.observable_rules hs subject k anchor ps).trans
      ((twins.rules anchor member k d known ps).trans (t.observable_rules ht subject k anchor pt).symm)

/-- Policy validation at commit supplies both safety results for every subsequent query. -/
theorem reachable_response_private_twins {s t : PolicyStore} (hs : s.admissible) (ht : t.admissible)
    (writes edits : List (List PolicyEdit)) {v left right asked} (stamp : Query.Stamp)
    (twins : (s.run writes).QueryAgreement (t.run edits) stamp.subject v left right asked) :
    (s.run writes).query v left stamp asked = (t.run edits).query v right stamp asked :=
  admissible_response_private_twins (policy_trace_admissible hs writes) (policy_trace_admissible ht edits) stamp twins

theorem reachable_no_private_obstruction {s : PolicyStore} (hs : s.admissible) (writes)
    (subject key anchor opts) (projects : (s.run writes).nonprojecting key anchor = false) :
    ((s.run writes).rulesFor subject).any (privateObstruction
      ((s.run writes).projectionOptions subject anchor key opts) key anchor) = false :=
  admissible_no_private_obstruction (policy_trace_admissible hs writes) subject key anchor opts projects

end Authz
