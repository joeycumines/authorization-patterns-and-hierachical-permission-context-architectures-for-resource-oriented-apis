import Authz.Request
import Authz.Projection
import Authz.Disclosure

namespace Authz
open Lean (Json)

/-- The service recognizes disjoint reserved spellings without consulting storage.
For overlapping secondary keys it instead declares the as-written sites, where
no rule may be attached or inherited from a strict descendant. -/
structure NameResolver where
  indirect : Path → Bool := fun _ => false
  lookup : Path → Option Path := fun _ => none
  failed : Path → Bool := fun _ => false
  asWritten : Domain := []
  configured : Bool := true

/-- Resolution is attempted only at resource sites. A wildcard at an ID site
can be recognized, but its mapping cannot narrow the declared region. -/
def NameResolver.indirectAt (resolver : NameResolver) (resources : Domain) (p : Path) : Bool :=
  let site := if p.contains "-" then resources.any fun pat =>
    p.length ≤ pat.length && (pat.length == p.length || (pat[p.length - 1]?).any Atom.isVariable) &&
    (pat.zip p).all fun (a, s) => if s == "-" then a.isVariable else a.accepts s
    else resources.isResource p
  let written := resolver.asWritten.any fun pat => p.length == pat.length &&
    (pat.zip p).all (fun (a, s) => a.isVariable || a.accepts s)
  site && !written && (resolver.failed p || resolver.indirect p)

private def NameResolver.walk (resolver : NameResolver) (resources : Domain) (base : Path) : Path → Except Unit (Option Path)
  | [] => .ok (some base)
  | s :: rest => do
    let current := base ++ [s]
    if !resolver.indirectAt resources current then
      return ← resolver.walk resources current rest
    if resolver.failed current then throw ()
    let some canonical := resolver.lookup current | return none
    if current.contains "-" || !pathOk canonical || !resources.isResource canonical then throw ()
    return ← resolver.walk resources canonical rest

def NameResolver.canonical (resolver : NameResolver) (resources : Domain) : ResolveName := resolver.walk resources []

def NameResolver.rulesAllowed (resolver : NameResolver) (resources : Domain) (rules : List Rule) :=
  resolver.configured && !rules.any (fun r => resolver.asWritten.any (fun pat =>
    let site := r.path.take pat.length
    resources.isResource site && Pattern.matches pat site))

structure ServerOptions where
  mode : Authority := .failClosed
  factsOf : Option (Path → Facts) := none
  rowReadFailed : Path → Bool := fun _ => false
  faultsOf : Option (Path → Rule → Option Bool) := none
  /-- A symbolic lookup can still select a row with different fault observations. -/
  pendingLookup : Bool := false
  ceiling : Ceiling := none
  nonprojecting : String → Path → Bool := fun _ _ => false
  canName : Path → Bool := fun _ => true
  handlerResolvesResiduals : Bool := false
  names : NameResolver := {}
  extraGuards : Option GuardBindings := none

def ServerOptions.guards (opts : ServerOptions) : GuardBindings :=
  opts.extraGuards.getD (fun _ _ _ _ => [])

/-- The row provides predicates and may carry its own observed faults. A separate
fault adapter, when configured, supplies the fault outcome for every rule. -/
def ServerOptions.available (opts : ServerOptions) (p : Path) (fallback : Facts := {}) : Facts :=
  let row := opts.factsOf.elim fallback (· p)
  {row with faults := opts.faultsOf.elim row.faults (· p)}

/-- Both adapters are independent. An explicit unknown overrides any fault value
attached to the row. If the fault adapter is absent, the row's evidence survives. -/
theorem ServerOptions.available_sources (opts : ServerOptions) (p : Path) (fallback : Facts) :
    let row := opts.factsOf.elim fallback (· p)
    (opts.available p fallback).predicate = row.predicate ∧
      (∀ observe, opts.faultsOf = some observe → (opts.available p fallback).faults = observe p) ∧
      (opts.faultsOf = none → (opts.available p fallback).faults = row.faults) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro observe h
    simp [available, h]
  · intro h
    simp [available, h]

-- A row records an older successful permit evaluation. An independent adapter
-- with no result for this rule must leave it unresolved.
theorem unknown_fault_overrides_stale_row :
    let permit : Rule := {path := [], keys := ["get"], effect := .permit, pred := some "owner", mayError := true}
    let row : Facts := {predicate := fun _ => some true, faults := fun _ => some false}
    let opts : ServerOptions := {mode := .skipErrors, factsOf := some (fun _ => row)}
    let fresh := {opts with faultsOf := some (fun _ _ => none)}
    decide opts.mode (opts.available []) [permit] "get" [] = .allow ∧
      decide fresh.mode (fresh.available []) [permit] "get" [] = .deny := by decide

structure Residual where
  kind : String
  key : Option String := none
  target : Option Path := none
  keys : List String := []
  predicates : List String := []
  nonprojectingGet : Bool := false
  nonprojectingList : Bool := false
  deriving Repr, Lean.FromJson, Lean.ToJson

structure Authorization where
  decision : String
  reason : Option String := none
  status : Option Disclosure.Status := none
  residuals : List Residual := []
  handlerPolicy : Option String := none
  deriving Repr, Lean.FromJson, Lean.ToJson

def wildcardAnchor (q : Path) := q.take (q.idxOf "-" - 1)

private def restrictRegion (subtree : Bool) : Pattern → Path → Option Pattern
  | p, [] => if subtree || p.isEmpty then some p else none
  | [], _ :: _ => none
  | a :: as, v :: vs => do
    let rest ← restrictRegion subtree as vs
    if v == "-" then return a :: rest
    guard (a.accepts v)
    return .lit v :: rest

/-- One universal proof covers the specified parent region. Scoped Claims can
carry holes, so the entire candidate domain participates in the hole test. -/
def regionAllowed (d : Descriptor) (rules : List Rule) (r : Requirement) (q : Path)
    (subtree : Bool) (opts : ServerOptions) : Bool :=
  let wildcard := q.contains "-"
  let anchor := if wildcard then wildcardAnchor q else q
  let dom := d.domain r.key
  let selected := dom.filterMap (fun p => restrictRegion (subtree || !wildcard) p q)
  let claims := regionClaims rules r.key anchor dom
    { nonprojecting := opts.nonprojecting r.key anchor, canName := opts.canName }
  (opts.ceiling.permits r.info && opts.names.rulesAllowed d.resourcePatterns rules) && (rules.all (d.resourcePatterns.validSite ·.path) && !selected.isEmpty) &&
    claims.any fun c =>
    c.kind == .allow && c.path.isPrefixOf (q.takeWhile (· != "-")) &&
    (if wildcard then !c.holes.any (fun h => Domain.nonemptyRegion selected h [])
     else !c.holes.any (fun h => h.isPrefixOf q || q.isPrefixOf h))

/-- For an exact wildcard target both paths end together. A subtree question
also includes descendants of each matching parent. -/
def InRequestRegion (subtree : Bool) : Path → Path → Prop
  | [], x => subtree = true ∨ x = []
  | _ :: _, [] => False
  | q :: qs, y :: ys => (q = "-" ∨ q = y) ∧ InRequestRegion subtree qs ys

private theorem restrict_contains (matched : Pattern.matches p x = true)
    (member : InRequestRegion subtree q x) :
    ∃ sel, restrictRegion subtree p q = some sel ∧ Pattern.matches sel x = true := by
  induction q generalizing p x with
  | nil =>
    rcases member with h | rfl
    · exact ⟨p, by simp [restrictRegion, h], matched⟩
    · cases p with
      | nil => exact ⟨[], by simp [restrictRegion], rfl⟩
      | cons a p => simp [Pattern.matches] at matched
  | cons q qs ih =>
    cases x with
    | nil => exact False.elim member
    | cons y ys =>
      cases p with
      | nil => simp [Pattern.matches] at matched
      | cons a ps =>
        obtain ⟨ok, tail⟩ := Bool.and_eq_true_iff.mp matched
        obtain ⟨sel, hr, hm⟩ := ih tail member.2
        by_cases wild : q = "-"
        · exact ⟨a :: sel, by simp [restrictRegion, hr, wild], Bool.and_eq_true_iff.mpr ⟨ok, hm⟩⟩
        · have eq := member.1.resolve_left wild
          subst q
          have sy := (Bool.and_eq_true_iff.mp ok).1
          exact ⟨.lit y :: sel, by simp [restrictRegion, hr, wild, ok, guard],
            by simp [Pattern.matches, Atom.accepts, sy, hm]⟩

private theorem region_prefix (member : InRequestRegion sub q x) :
    q.takeWhile (· != "-") <+: x := by
  induction q generalizing x with
  | nil => simp
  | cons q qs ih =>
    cases x with
    | nil => exact False.elim member
    | cons y ys =>
      by_cases wild : q = "-"
      · simp [wild]
      · have eq := member.1.resolve_left wild
        subst y
        simpa [List.takeWhile, bne_iff_ne.mpr wild] using ih member.2

/-- Every concrete name selected by an allowed region passes the same
permission and credential ceiling under either evaluation authority. -/
theorem regionAllowed_sound {d rules r q subtree opts x}
    (allowedRegion : regionAllowed d rules r q subtree opts = true)
    (domain : Domain.contains (d.domain r.key) x = true)
    (member : InRequestRegion (subtree || !q.contains "-") q x) (valid : pathOk x)
    (mode : Authority) (facts : Facts) :
    opts.ceiling.permits r.info = true ∧ decide mode facts rules r.key x = .allow := by
  obtain ⟨⟨ceiling, _⟩, witness⟩ := Bool.and_eq_true_iff.mp allowedRegion |>.imp_left Bool.and_eq_true_iff.mp
  obtain ⟨c, hc, test⟩ := List.any_eq_true.mp witness
  obtain ⟨left, holes⟩ := Bool.and_eq_true_iff.mp test
  obtain ⟨allowKind, below⟩ := Bool.and_eq_true_iff.mp left
  have hp := (List.isPrefixOf_iff_prefix.mp below).trans (region_prefix member)
  refine ⟨(Bool.and_eq_true_iff.mp ceiling).1, (projected_decision hc (claim_covers_iff.mpr ⟨hp, ?_⟩) domain valid mode facts).1
    (beq_iff_eq.mp allowKind)⟩
  rintro ⟨h, hh, pre⟩
  cases wild : q.contains "-" with
  | false =>
    have noWild : "-" ∉ q := by simpa using wild
    have prefixQ : q <+: x := by
      have same {ps : Path} (no : "-" ∉ ps) : ps.takeWhile (· != "-") = ps := by
        induction ps with
        | nil => rfl
        | cons p ps ih =>
          have ne : p ≠ "-" := fun h => no (by simp [h])
          simp [List.takeWhile, bne_iff_ne.mpr ne, ih (fun h => no (List.mem_cons_of_mem _ h))]
      simpa only [same noWild] using region_prefix member
    simp only [wild, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true',
      List.any_eq_false] at holes
    have miss := holes h hh
    have comp := List.prefix_or_prefix_of_prefix pre prefixQ
    simp [List.isPrefixOf_iff_prefix, comp] at miss
  | true =>
    obtain ⟨p, hd, hm⟩ := List.any_eq_true.mp domain
    obtain ⟨sel, hr, matchesSel⟩ := restrict_contains hm member
    have reaches := Pattern.reach_of_matches matchesSel pre
    have hit : Domain.nonemptyRegion ((d.domain r.key).filterMap
        (restrictRegion (subtree || !q.contains "-") · q)) h [] = true := by
      apply List.any_eq_true.mpr
      refine ⟨sel, List.mem_filterMap.mpr ⟨p, hd, hr⟩, ?_⟩
      unfold Pattern.reach at reaches
      cases eq : Pattern.consume sel h <;> simp_all [Pattern.fixedPrefix]
    simp only [wild, ↓reduceIte, Bool.not_true, Bool.or_false, Bool.not_eq_true',
      List.any_eq_false] at holes hit
    exact holes h hh hit

/-- The most favorable predicate value for this rule. A separately configured
fault observation is already known. A row may still carry its own fault evidence. -/
private def beforeRowFacts (opts : ServerOptions) (p : Path) (r : Rule) : Facts :=
  { predicate := fun _ => some (r.effect == .permit)
    faults := opts.faultsOf.elim (fun rule =>
      if opts.factsOf.isSome && !opts.pendingLookup then (opts.available p).faults rule
      else if opts.factsOf.isSome || opts.mode == .skipErrors then
        some (r.effect == .forbid && opts.mode == .skipErrors)
      else none) (· p) }

private def excludesPermit (opts : ServerOptions) (p : Path) (permit forbid : Rule) :=
  forbid.pred.isSome && forbid.pred == permit.pred &&
    forbid.blocks opts.mode {(beforeRowFacts opts p forbid) with predicate := fun _ => some true}

def policyDeniesBeforeRow (rules : List Rule) (k : String) (p : Path) (opts : ServerOptions) :=
  let app := rules.filter (applies k p)
  app.any (fun r => r.blocks opts.mode (beforeRowFacts opts p r)) ||
    !app.any (fun r => r.grants (beforeRowFacts opts p r) && !app.any (excludesPermit opts p r))

private theorem forbid_ne_permit_beq : (GrantEffect.forbid == GrantEffect.permit) = false := rfl
private theorem permit_ne_forbid_beq : (GrantEffect.permit == GrantEffect.forbid) = false := rfl
private theorem skip_ne_closed_beq : (Authority.skipErrors == Authority.failClosed) = false := rfl
private theorem closed_ne_skip_beq : (Authority.failClosed == Authority.skipErrors) = false := rfl
attribute [local simp] forbid_ne_permit_beq permit_ne_forbid_beq skip_ne_closed_beq closed_ne_skip_beq

private theorem optimistic_rule (opts : ServerOptions) (p : Path) (r : Rule) :
    (r.grants (opts.available p) → r.grants (beforeRowFacts opts p r)) ∧
    (r.blocks opts.mode (beforeRowFacts opts p r) → r.blocks opts.mode (opts.available p)) := by
  have common (f g : Facts) (agree : g.faults r.faultIdentity = f.faults r.faultIdentity)
      (pred : ∀ k, g.predicate k = some (r.effect == .permit)) :
      (r.grants f → r.grants g) ∧ (r.blocks opts.mode g → r.blocks opts.mode f) := by
    cases effect : r.effect <;> cases may : r.mayError <;> cases condition : r.pred <;>
      simp [Rule.grants, Rule.blocks, Rule.evaluate, effect, may, condition, pred, agree] <;>
      split <;> simp_all <;> split <;> simp_all
  cases adapter : opts.faultsOf with
  | some fn => exact common _ _ (by simp [ServerOptions.available, beforeRowFacts, adapter]) (by simp [beforeRowFacts])
  | none =>
    cases row : opts.factsOf with
    | none =>
      cases mode : opts.mode <;> cases effect : r.effect <;> cases may : r.mayError <;> cases condition : r.pred <;>
        simp [Rule.grants, Rule.blocks, Rule.evaluate, ServerOptions.available, beforeRowFacts,
          effect, may, condition, mode, adapter, row]
    | some read =>
      cases pending : opts.pendingLookup
      · exact common _ _ (by simp [beforeRowFacts, row, pending, adapter]) (by simp [beforeRowFacts])
      cases effect : r.effect <;> cases mode : opts.mode <;> cases may : r.mayError <;> cases condition : r.pred <;>
        simp [Rule.grants, Rule.blocks, Rule.evaluate, ServerOptions.available, beforeRowFacts,
          effect, mode, may, condition, adapter, row, pending] <;> split <;> simp_all <;> split <;> simp_all

private theorem granted_predicate {r : Rule} {facts : Facts} (grant : r.grants facts) :
    r.pred.elim (some true) facts.predicate = some true := by
  unfold Rule.grants Rule.evaluate at grant
  cases observed : (if r.mayError then facts.faults r.faultIdentity else some false) with
  | none => simp [observed] at grant
  | some fault =>
    cases fault <;> simp only [observed] at grant
    · cases value : r.pred.elim (some true) facts.predicate with
      | none => simp [value] at grant
      | some yes => cases yes <;> simp_all
    · contradiction

private theorem excluded_permit_blocks {opts p permit forbid} (grants : permit.grants (opts.available p))
    (exclusion : excludesPermit opts p permit forbid) : forbid.blocks opts.mode (opts.available p) := by
  obtain ⟨⟨_, same⟩, blocked⟩ := Bool.and_eq_true_iff.mp exclusion |>.imp_left Bool.and_eq_true_iff.mp
  have pred : forbid.pred.elim (some true) (opts.available p).predicate = some true := by
    rw [beq_iff_eq.mp same]
    exact granted_predicate grants
  have constant : forbid.pred.elim (some true) (fun _ => some true) = some true := by
    cases forbid.pred <;> rfl
  unfold Rule.blocks Rule.evaluate at blocked ⊢
  simp only [pred, constant] at blocked ⊢
  cases adapter : opts.faultsOf with
  | some fn => simpa only [ServerOptions.available, beforeRowFacts, adapter, Option.elim_some] using blocked
  | none =>
    cases row : opts.factsOf with
    | none =>
      cases mode : opts.mode <;> cases effect : forbid.effect <;> cases may : forbid.mayError <;>
        simp_all [ServerOptions.available, beforeRowFacts]
    | some read =>
      cases pending : opts.pendingLookup
      · simpa [beforeRowFacts, adapter, row, pending] using blocked
      cases mode : opts.mode <;> cases effect : forbid.effect <;> cases may : forbid.mayError <;>
        simp [ServerOptions.available, beforeRowFacts, adapter, row, pending, mode, effect, may] at blocked ⊢
      cases h : (read p).faults forbid.faultIdentity with
      | none => rfl
      | some b => cases b <;> rfl

theorem pre_row_denial_sound {rules k p opts} (deny : policyDeniesBeforeRow rules k p opts) :
    decide opts.mode (opts.available p) rules k p = .deny := by
  unfold decide decideApplied
  split <;> try rfl
  unfold policyDeniesBeforeRow at deny
  rcases Bool.or_eq_true_iff.mp deny with block | absent
  · obtain ⟨r, member, yes⟩ := List.any_eq_true.mp block
    have actual : (rules.filter (applies k p)).any (·.blocks opts.mode (opts.available p)) :=
      List.any_eq_true.mpr ⟨r, member, (optimistic_rule opts p r).2 yes⟩
    simp only [actual, ↓reduceIte]
  · cases denial : (rules.filter (applies k p)).any (·.blocks opts.mode (opts.available p)) <;> try rfl
    have no : (rules.filter (applies k p)).any (·.grants (opts.available p)) = false := by
      apply List.any_eq_false.mpr
      intro r member grants
      have safe : (rules.filter (applies k p)).any (excludesPermit opts p r) = false := by
        apply List.any_eq_false.mpr
        intro other otherMember excludes
        exact List.any_eq_false.mp denial other otherMember (excluded_permit_blocks grants excludes)
      have hit : (rules.filter (applies k p)).any (fun r => r.grants (beforeRowFacts opts p r) &&
          !(rules.filter (applies k p)).any (excludesPermit opts p r)) :=
        List.any_eq_true.mpr ⟨r, member, by simp only [(optimistic_rule opts p r).1 grants, safe, Bool.not_false, Bool.and_self]⟩
      rw [hit] at absent
      contradiction
    simp [no]

/-- An absent permit or an unconditional, fault-free forbid settles a
concrete denial without consulting a row or its predicate values. -/
theorem structural_denial_before_row {rules k p opts}
    (denial : (∀ r ∈ rules, applies k p r → r.effect ≠ .permit) ∨
      ∃ r ∈ rules, applies k p r ∧ r.effect = .forbid ∧ r.pred = none ∧ r.mayError = false) :
    policyDeniesBeforeRow rules k p opts = true := by
  unfold policyDeniesBeforeRow
  apply Bool.or_eq_true_iff.mpr
  rcases denial with missing | ⟨r, member, applied, forbid, plain, safe⟩
  · right
    suffices empty : (rules.filter (applies k p)).any (fun r => r.grants (beforeRowFacts opts p r) &&
        !(rules.filter (applies k p)).any (excludesPermit opts p r)) = false by
      simp only [empty, Bool.not_false]
    apply List.any_eq_false.mpr
    intro r member grants
    obtain ⟨stored, applies⟩ := List.mem_filter.mp member
    exact missing _ stored applies (Rule.effect_of_grants (Bool.and_eq_true_iff.mp grants).1)
  · left
    exact List.any_eq_true.mpr ⟨r, List.mem_filter.mpr ⟨member, applied⟩, by
      simp [Rule.blocks, Rule.evaluate, forbid, plain, safe]⟩

private def targetDeniedBeforeRow (d : Descriptor) (rules : List Rule) (opts : ServerOptions)
    (r : BoundRequirement) (t : Path) : Bool :=
  !opts.ceiling.permits r.decl.info ||
    if t.contains "-" then r.wildcard == .universal && !regionAllowed d rules r.decl t false opts
    else policyDeniesBeforeRow rules r.decl.key t opts

private def phaseDenies (d : Descriptor) (rules : List Rule) (opts : ServerOptions) (rs : List BoundRequirement) :=
  rs.any fun r => r.targets.any
    (fun pair => targetDeniedBeforeRow d rules opts r pair.2.target)

/-- The caller already has an allow with every row predicate and every
row-supplied fault unknown. Independent policy fault observations still apply. -/
def policyAllowsBeforeRow (rules : List Rule) (k : String) (p : Path) (opts : ServerOptions) :=
  decide opts.mode {faults := opts.faultsOf.elim (fun _ => none) (· p)} rules k p == .allow

def attributeReadFailed (rules : List Rule) (k : String) (p : Path) (opts : ServerOptions) :=
  !policyAllowsBeforeRow rules k p opts && opts.rowReadFailed p

theorem allow_before_row_sound {rules k p opts} (known : policyAllowsBeforeRow rules k p opts)
    (fallback : Facts) : decide opts.mode (opts.available p fallback) rules k p = .allow := by
  apply decide_allow_of_more_facts (allow := beq_iff_eq.mp known)
  constructor
  · intro _ _ impossible
    contradiction
  · intro r b observed
    cases fo : opts.faultsOf <;> simp_all [ServerOptions.available]

def allowed (rules : List Rule) (r : Requirement) (p : Path) (opts : ServerOptions) :=
  opts.ceiling.permits r.info && (policyAllowsBeforeRow rules r.key p opts ||
    (!opts.rowReadFailed p && decide opts.mode (opts.available p) rules r.key p == .allow))

private theorem allowed_decision {rules req x opts} (yes : allowed rules req x opts = true)
    (fallback : Facts) : opts.ceiling.permits req.info = true ∧
      decide opts.mode (opts.available x fallback) rules req.key x = .allow := by
  obtain ⟨ceiling, evaluated⟩ := Bool.and_eq_true_iff.mp yes
  refine ⟨ceiling, ?_⟩
  rcases Bool.or_eq_true_iff.mp evaluated with early | read
  · exact allow_before_row_sound early fallback
  apply decide_allow_of_more_facts (allow := beq_iff_eq.mp (Bool.and_eq_true_iff.mp read).2)
  constructor
  · intro k b known
    cases fa : opts.factsOf <;> simp_all [ServerOptions.available]
  · intro r b known
    cases fa : opts.factsOf <;> cases fo : opts.faultsOf <;> simp_all [ServerOptions.available]

private def hasParentShape (m : MethodDecl) (request : Json) (r : Requirement) (parent : Path) :=
  let vars := m.standardBatchWildcards.getD <| (m.requirements.filter fun req =>
    req.field == some "parent" && req.kind == .parent && !req.perItem &&
      req.condition.all (fun field => requestField request field == .bool true)).flatMap (·.wildcardVariables)
  r.patterns.any fun pat =>
    Pattern.matchesWildcard (if r.kind == .resource then Pattern.parent pat else pat) vars parent

private def parentMatches (parent target : Path) :=
  parent.length ≤ target.length && (parent.zip target).all (fun (p,t) => p == "-" || p == t)

private theorem parent_region {p x : Path} (bound : parentMatches p x = true) :
    InRequestRegion true p x := by
  induction p generalizing x with
  | nil => exact Or.inl rfl
  | cons hd tl ih =>
    cases x with
    | nil => simp [parentMatches] at bound
    | cons y ys =>
      simp [parentMatches] at bound
      exact ⟨bound.2.1, ih (by simpa [parentMatches] using And.intro bound.1 bound.2.2)⟩

def MethodDecl.isBatch (m : MethodDecl) :=
  m.requirements.any (·.perItem) || m.batchItem?.isSome

private def batchDeclarations (m : MethodDecl) :=
  match m.batchItem? with
  | some item => [item]
  | none => m.requirements.filter (·.perItem)

/-- A malformed resolved address prevents enforcing a guard on the written resource. -/
def singularWriterFault (d : Descriptor) (m : MethodDecl) (request : Json) (opts : ServerOptions) :=
  !m.fieldGuards.isEmpty && m.writer?.any (!·.perItem) &&
    (bindWriter d m request (fun _ => some []) (opts.names.canonical d.resourcePatterns)).any (·.resolverFault)

/-- A standard batch carries item addresses even when its permissions bind only at the root. -/
def physicalBatchItem (d : Descriptor) (m : MethodDecl) (request : Json) (opts : ServerOptions) :=
  bindBatchItem d m request (fun _ => some []) (opts.names.canonical d.resourcePatterns)

def batchGeometry (addresses : Option BoundRequirement) (items : List BoundRequirement) :=
  addresses.elim (items.filter (!·.derivedGuard)) (fun r => [r])

def batchHasAuthority (d : Descriptor) (m : MethodDecl) (request : Json)
    (opts : ServerOptions) (items : List BoundRequirement) :=
  !items.isEmpty || ((physicalBatchItem d m request opts).isSome &&
    !(requirementsFor d m request (fun _ => some []) opts.guards (opts.names.canonical d.resourcePatterns) (some false)).isEmpty)

def batchNeedsParentProof (d : Descriptor) (m : MethodDecl) (request : Json)
    (opts : ServerOptions) (items : List BoundRequirement) :=
  !batchHasAuthority d m request opts items || items.any (·.unbound) ||
    (physicalBatchItem d m request opts).any (·.unbound)

def batchItemsBound (d : Descriptor) (m : MethodDecl) (request : Json) (opts : ServerOptions) :=
  (physicalBatchItem d m request opts).all fun w => !w.resolverFault && !w.unbound

private def suppliedBatchParent (m : MethodDecl) (request : Json) :=
  if m.batchLevel.contains "parent" then requestField request "parent" else .null

def batchParent (m : MethodDecl) (decls : List Requirement) (request : Json) : Option Path :=
  let rootOnly := !decls.isEmpty && decls.all (fun r =>
    r.kind == .root || r.patterns.all (fun p => (if r.kind == .resource then Pattern.parent p else p).isEmpty))
  let v := suppliedBatchParent m request
  if rootOnly && (v == .null || v == .str "") then some []
  else (Lean.fromJson? (α := Path) v).toOption.filter (fun t => rootOnly || !t.isEmpty)

inductive BatchParentError where
  | missing | resolverFault
  deriving DecidableEq, Repr

/-- An omitted optional parent imposes no constraint. A supplied alias must
resolve before it can prove a region or constrain an item's canonical parent. -/
def resolvedBatchParent (d : Descriptor) (m : MethodDecl) (request : Json)
    (opts : ServerOptions) : Except BatchParentError (Option Path) := do
  let decls := batchDeclarations m
  let some supplied := batchParent m decls request | return none
  if supplied.isEmpty || !decls.all (hasParentShape m request · supplied) then return some supplied
  match opts.names.canonical d.resourcePatterns supplied with
  | .error () => throw .resolverFault
  | .ok none => throw .missing
  | .ok (some canonical) =>
    if !decls.all (hasParentShape m request · canonical) then throw .resolverFault
    return some canonical

private def parentResolverFault : Except BatchParentError (Option Path) → Bool
  | .error .resolverFault => true
  | _ => false

private def itemParent (r : Requirement) (t : Path) :=
  if r.kind != .resource then t else
    (r.patterns.find? (Pattern.matches · t)).elim t (fun p => t.take (Pattern.parent p).length)

private def createIds (m : MethodDecl) (request : Json) (addresses : Option BoundRequirement) :
    List (Path × String) := Id.run do
  if m.writes != some "create" then return []
  let some items := addresses | return []
  return (fieldArray request "requests[].id").toList.zipIdx.filterMap fun (v,i) => do
    let id ← v.getStr?.toOption
    guard (!id.isEmpty)
    let parent ← items.targets.lookup i
    return (parent.target, id)

/-- Child and top-level values for a hoisted field must match. The authorization
phase still covers every field selected by either representation. -/
def hoistedFieldsMatch (m : MethodDecl) (request : Json) : Bool := Id.run do
  let writerMask := m.writes == some "update" && m.writer?.any (·.perItem) && m.batchLevel.contains "update_mask"
  if writerMask then
    let top := (request.getObjVal? "update_mask").toOption
    let readMask (mask : Json) := (Lean.fromJson? (α := List String) mask).toOption
    let agrees (mask : Json) := (readMask mask).any fun paths => top.all fun value =>
      (readMask value).any (fun selected => paths.all selected.contains && selected.all paths.contains)
    if !top.all (fun value => (readMask value).isSome) then return false
    if let .ok entries := request.getObjVal? "requests[].update" then
      if !entries.getArr?.toOption.any (fun items => items.all fun item =>
          item.getObj?.isOk && (item.getObjVal? "mask").toOption.all agrees) then return false
    if let .ok entries := request.getObjVal? "requests[].update_mask" then
      if !entries.getArr?.toOption.any (fun items => items.all (fun mask => mask == .null || agrees mask)) then return false
  let fields := ((request.getObj?).toOption.map (·.toList)).getD []
  return fields.all fun (path, entries) => Id.run do
    let some field := m.hoistedItemField? path | return true
    let top := requestField request field
    if (writerMask && path == "requests[].update_mask") || top == .null || entries == .null then return true
    return entries.getArr?.toOption.any fun values => values.all (fun v => v == .null || v == top)

private def outerAllowed (d : Descriptor) (rules : List Rule) (opts : ServerOptions)
    (outer : List BoundRequirement) := !phaseDenies d rules opts outer && outer.all fun r =>
  !r.resolverFault && !r.unbound && r.targets.all fun (_,binding) =>
    let t := binding.target
    if t.contains "-" then
      r.wildcard == .universal && regionAllowed d rules r.decl t false opts
    else allowed rules r.decl t opts

private def validBatchParentShape (m : MethodDecl) (request : Json) (parent : Option Path) :=
  let raw := suppliedBatchParent m request
  (raw == .null || raw == .str "" || (Lean.fromJson? (α := Path) raw).isOk) &&
    parent.all (fun p => (batchDeclarations m).all (hasParentShape m request · p))

private def batchProofParent (d : Descriptor) (m : MethodDecl) (request : Json) (opts : ServerOptions) :=
  let parent := (resolvedBatchParent d m request opts).toOption.join
  if validBatchParentShape m request parent then parent else none

def coveredByParent (d : Descriptor) (rules : List Rule) (opts : ServerOptions)
    (parent : Option Path) (r : BoundRequirement) (t : Path) :=
  parent.any fun p => parentMatches p t && !t.contains "-" && (d.domain r.decl.key).contains t &&
    regionAllowed d rules r.decl p true opts

private theorem coveredByParent_iff {d rules opts parent r t} :
    coveredByParent d rules opts parent r t ↔ ∃ p, parent = some p ∧ parentMatches p t ∧
      t.contains "-" = false ∧ (d.domain r.decl.key).contains t ∧ regionAllowed d rules r.decl p true opts := by
  cases parent <;> simp [coveredByParent, and_assoc]

/-- A batch parent proves the item's key for every combination of row facts,
including when no item row is available. -/
theorem coveredByParent_sound {d rules opts parent r t} (proof : coveredByParent d rules opts parent r t)
    (valid : pathOk t) (mode : Authority) (facts : Facts) :
    opts.ceiling.permits r.decl.info = true ∧ decide mode facts rules r.decl.key t = .allow := by
  obtain ⟨_, _, under, _, domain, region⟩ := coveredByParent_iff.mp proof
  exact regionAllowed_sound region domain (by simpa only [Bool.true_or] using parent_region under) valid mode facts

/-- Bound items are inspected only after the operation-level checks. -/
private def batchItemStatus (d : Descriptor) (m : MethodDecl) (request : Json)
    (rules : List Rule) (opts : ServerOptions) (rs : List BoundRequirement) (itemsAuthorized : Bool := false) : Disclosure.Status := Id.run do
  let resolved := resolvedBatchParent d m request opts
  let addresses := physicalBatchItem d m request opts
  if rs.any (·.resolverFault) || !resolved.isOk || addresses.any (·.resolverFault) then return .denied
  let parent := resolved.toOption.join
  let validParent := validBatchParentShape m request parent
  let universal (r : BoundRequirement) := validParent &&
    parent.any (fun p => regionAllowed d rules r.decl p true opts)
  let refused := !itemsAuthorized && (phaseDenies d rules opts rs || rs.any fun r => r.targets.any fun (_, binding) =>
    let t := binding.target
    !coveredByParent d rules opts (batchProofParent d m request opts) r t && !allowed rules r.decl t opts)
  if refused then return .denied
  if batchNeedsParentProof d m request opts rs then
    return if batchHasAuthority d m request opts rs && validParent && parent.isSome && rs.all universal then .invalidArgument else .denied
  if !validParent || !hoistedFieldsMatch m request then return .invalidArgument
  let geometry := batchGeometry addresses rs
  let malformed := geometry.any fun r =>
    let targets := r.targets.map (fun pair => pair.2.target)
    parent.any (fun p => targets.any fun t =>
      let ip := itemParent r.decl t
      p.length != ip.length || !parentMatches p ip) ||
      (r.decl.kind == .resource && !targets.Nodup)
  return if malformed || !(createIds m request addresses).Nodup then .invalidArgument else .ok

def batchRequestStatus (d : Descriptor) (methodName : String) (request : Json)
    (rules : List Rule) (opts : ServerOptions := {}) : Disclosure.Status := Id.run do
  let some m := d.method? methodName | return .denied
  if m.disposition != .requirements || !rules.all (d.resourcePatterns.validSite ·.path) || !opts.names.rulesAllowed d.resourcePatterns rules then return .denied
  let bind perItem := requirementsFor d m request (fun _ => some []) opts.guards (opts.names.canonical d.resourcePatterns) perItem
  if !outerAllowed d rules opts (bind (some false)) then return .denied
  return batchItemStatus d m request rules opts (bind (some true))

/-- A physical batch item can be validated without its own permission key
only when an active operation-level requirement authorized the call. -/
theorem batch_ok_has_active_permission {d name request opts rules m}
    (method : d.method? name = some m)
    (ok : batchRequestStatus d name request rules opts = .ok) :
    let bind := fun perItem => requirementsFor d m request (fun _ => some []) opts.guards
      (opts.names.canonical d.resourcePatterns) (some perItem)
    bind true ≠ [] ∨ bind false ≠ [] := by
  intro bind
  by_cases item : bind true = []
  · right
    intro outer
    dsimp [bind] at item outer
    simp only [batchRequestStatus, method, Id.run, pure, outer, outerAllowed, phaseDenies, List.any_nil, List.all_nil, Bool.not_false, Bool.true_and, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, item] at ok
    split at ok <;> try contradiction
    simp [batchItemStatus, batchNeedsParentProof, batchHasAuthority, outer] at ok
  · exact Or.inl item

/-- A missing or invalid alias mapping for a supplied top-level parent cannot
authorize an atomic batch or justify an input-validation disclosure. -/
theorem batchRequestStatus_parent_denied {d name request opts m}
    (method : d.method? name = some m)
    (unresolved : (resolvedBatchParent d m request opts).isOk = false) (rules : List Rule) :
    batchRequestStatus d name request rules opts = .denied := by
  simp only [batchRequestStatus, method, Id.run, pure]
  split <;> try rfl
  split <;> try rfl
  simp [batchItemStatus, unresolved]

/-- Every bound item in an OK batch passed a pointwise decision or the
hole-free part of a universal claim on the actual parent. -/
theorem batchRequestStatus_item_sound {d methodName request rules opts m}
    (method : d.method? methodName = some m)
    (success : batchRequestStatus d methodName request rules opts = .ok)
    (req : BoundRequirement) (hr : req ∈ requirementsFor d m request (fun _ => some [])
      opts.guards (opts.names.canonical d.resourcePatterns) (some true)) (pair : Nat × TargetBinding) (bound : pair ∈ req.targets)
    (_domain : Domain.contains (d.domain req.decl.key) pair.2.target)
    (valid : pathOk pair.2.target) (fallback : Facts) :
    opts.ceiling.permits req.decl.info = true ∧ decide opts.mode
      (opts.available pair.2.target fallback) rules req.decl.key pair.2.target = .allow := by
  simp only [batchRequestStatus, method, Id.run, pure] at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  simp only [batchItemStatus, Id.run, pure] at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  rename_i checked
  have h := List.any_eq_false.mp (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr checked)).2 req hr
  have point := List.any_eq_false.mp (Bool.eq_false_iff.mpr h) pair bound
  by_cases individual : allowed rules req.decl pair.2.target opts = true
  · exact allowed_decision individual fallback
  · have parent := Bool.eq_false_iff.mpr individual
    simp only [parent, Bool.not_false, Bool.and_true, Bool.not_eq_true', Bool.not_eq_false] at point
    exact coveredByParent_sound point valid _ _

/-- Once validation succeeds, each ordinary item's parent matches the resolved
top-level parent, including every concrete position in a wildcard parent. -/
theorem batchRequestStatus_step4_parent {d methodName request rules opts m parent}
    (method : d.method? methodName = some m)
    (success : batchRequestStatus d methodName request rules opts = .ok)
    (resolved : resolvedBatchParent d m request opts = .ok (some parent))
    (r : BoundRequirement) (member : r ∈ batchGeometry (physicalBatchItem d m request opts)
      (requirementsFor d m request (fun _ => some []) opts.guards (opts.names.canonical d.resourcePatterns) (some true)))
    (pair : Nat × TargetBinding) (bound : pair ∈ r.targets) :
    let actual := itemParent r.decl pair.2.target
    parent.length = actual.length ∧ parentMatches parent actual = true := by
  simp only [batchRequestStatus, method, Id.run, pure] at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  simp only [batchItemStatus, Id.run, pure, resolved, Except.toOption, Option.join_some,
    Option.any_some] at success
  repeat' split at success <;> try contradiction
  rename_i passed
  have clean := Bool.eq_false_iff.mpr passed
  have item := List.any_eq_false.mp (Bool.or_eq_false_iff.mp clean).1 r member
  have correct := List.any_eq_false.mp (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr item)).1 pair.2.target
    (List.mem_map.mpr ⟨pair, bound, rfl⟩)
  simpa using correct

/-- An accepted batch agrees on every field supplied at both levels. -/
theorem batch_ok_hoisted_fields_match {d name request rules opts m}
    (method : d.method? name = some m)
    (ok : batchRequestStatus d name request rules opts = .ok) :
    hoistedFieldsMatch m request = true := by
  cases agrees : hoistedFieldsMatch m request
  · simp only [batchRequestStatus, method, Id.run, pure] at ok
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    simp only [batchItemStatus, agrees, Bool.not_false, Bool.or_true, ↓reduceIte, Id.run, pure] at ok
    repeat' split at ok <;> try contradiction
  · rfl

/-- Successful batches address each named resource at most once, even when
a single permission on the service authorizes all physical items. -/
theorem batch_ok_unique_resources {d methodName request rules opts m addresses}
    (method : d.method? methodName = some m)
    (success : batchRequestStatus d methodName request rules opts = .ok)
    (geometry : physicalBatchItem d m request opts = some addresses)
    (resources : addresses.decl.kind = .resource) :
    (addresses.targets.map (fun pair => pair.2.target)).Nodup := by
  simp only [batchRequestStatus, method, Id.run, pure] at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  simp only [batchItemStatus, Id.run, pure] at success
  repeat' split at success <;> try contradiction
  rename_i passed
  have valid := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr passed)).1
  simp [batchGeometry, geometry, resources] at valid
  exact valid.2

/-- Reporting malformed input for an empty or unbound batch requires one
publicly provable top-level parent for every active key, including field guards. -/
theorem batchRequestStatus_step3_validation {d methodName request opts rules m}
    (method : d.method? methodName = some m)
    (invalid : batchRequestStatus d methodName request rules opts = .invalidArgument) :
    let items := requirementsFor d m request (fun _ => some []) opts.guards (opts.names.canonical d.resourcePatterns) (some true)
    batchNeedsParentProof d m request opts items →
      batchHasAuthority d m request opts items ∧ ∃ parent ∈ (resolvedBatchParent d m request opts).toOption.join,
        ∀ r ∈ items, regionAllowed d rules r.decl parent true opts := by
  intro items missing
  simp only [batchRequestStatus, method, Id.run, pure] at invalid
  split at invalid <;> try contradiction
  split at invalid <;> try contradiction
  simp only [batchItemStatus, Id.run, pure] at invalid
  split at invalid <;> try contradiction
  split at invalid <;> try contradiction
  change batchNeedsParentProof d m request opts _ = true at missing
  split at invalid <;> try contradiction
  rename_i accepted
  obtain ⟨⟨⟨active, _⟩, hasParent⟩, permits⟩ := by simpa only [Bool.and_eq_true] using accepted
  cases eq : (resolvedBatchParent d m request opts).toOption.join with
  | none => simp [eq] at hasParent
  | some parent =>
    refine ⟨active, parent, rfl, ?_⟩
    intro r member
    simpa only [eq, Option.any_some] using (Bool.and_eq_true_iff.mp (List.all_eq_true.mp permits r member)).2

/-- Step 3 withholds validation for an unbindable item whenever any required
key may carry private rules under the batch parent. This holds across arbitrary
changes to policy, even if another bound item or the outer operation is denied. -/
theorem batchRequestStatus_step3_private {d methodName request opts m}
    (method : d.method? methodName = some m)
    (unbound : batchNeedsParentProof d m request opts
      (requirementsFor d m request (fun _ => some []) opts.guards
        (opts.names.canonical d.resourcePatterns) (some true)) = true)
    (privateKey : ∃ req ∈ requirementsFor d m request (fun _ => some []) opts.guards
        (opts.names.canonical d.resourcePatterns) (some true),
      ∀ p ∈ (resolvedBatchParent d m request opts).toOption.join,
        opts.nonprojecting req.decl.key (if p.contains "-" then wildcardAnchor p else p) = true)
    (rules : List Rule) :
    batchRequestStatus d methodName request rules opts = .denied := by
  obtain ⟨req, hr, hidden⟩ := privateKey
  let reqs := requirementsFor d m request (fun _ => some []) opts.guards (opts.names.canonical d.resourcePatterns) (some true)
  let parent := (resolvedBatchParent d m request opts).toOption.join
  have withheld : parent.any (fun p => regionAllowed d rules req.decl p true opts) = false := by
    cases eq : parent with
    | none => rfl
    | some p =>
      have hp := hidden p (by change p ∈ parent; simp [eq])
      cases wild : p.contains "-" <;>
        simp only [wild, Bool.false_eq_true, ↓reduceIte] at hp <;>
        simp only [Option.any_some, regionAllowed, regionClaims, projectKey, wild,
          Bool.false_eq_true, ↓reduceIte, hp, Bool.true_or, List.any_nil, Bool.and_false]
  have deniedAll (validParent : Bool) : reqs.all (fun r => validParent &&
      parent.any (fun p => regionAllowed d rules r.decl p true opts)) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    have checked := List.all_eq_true.mp yes req hr
    simp [withheld] at checked
  unfold batchRequestStatus
  simp only [method, Id.run, pure]
  split <;> try rfl
  split <;> try rfl
  unfold batchItemStatus
  simp only [Id.run, pure]
  split <;> try rfl
  split <;> try rfl
  simp only [reqs, parent] at deniedAll
  simp only [deniedAll, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

private def denied (reason : String) : Authorization := { decision := "DENY", reason := some reason }

private def siblingKey (key op : String) := String.intercalate "." ((key.splitOn ".").dropLast ++ [op])

private def listNonprojecting (d : Descriptor) (resourceType : String) (anchor : Path) (opts : ServerOptions) :=
  let lists := d.readMethods resourceType "list"
  !lists.isEmpty && lists.all fun (method, _) => method.requirements.any fun r =>
    r.condition.isNone && opts.nonprojecting r.key (if r.kind == .root then [] else anchor)

private def partialTarget (rules : List Rule) (k : String) (t : Path) (opts : ServerOptions) :
    Except String (List Residual) := do
  let app := rules.filter (applies k t)
  let fault := fun (x : Rule) => if x.mayError then (opts.available t).faults x.faultIdentity else some false
  let deferred := opts.faultsOf.isNone && opts.mode == .skipErrors
  let blocks := app.any fun x => x.effect == .forbid && match fault x with
    | some false => x.pred.isNone
    | some true => opts.mode == .failClosed
    | none => !deferred
  if blocks then throw "POLICY"
  let live := app.filter (fun x => fault x == some false)
  let permits := live.filter (·.effect == .permit)
  let pending := app.filter (fun x => (fault x).isNone)
  if permits.isEmpty && !(deferred && pending.any (·.effect == .permit)) then throw "POLICY"
  let unconditional := permits.any (·.pred.isNone)
  if deferred && (pending.any (·.effect == .forbid) || (!unconditional && !pending.isEmpty)) then
    return [{kind := "POLICY_EVALUATION", key := some k, target := some t}]
  let forbids := live.filter (·.effect == .forbid)
  let needed := forbids ++ (if unconditional then [] else permits)
  return [{kind := "PREDICATE", key := some k, target := some t,
           predicates := (needed.filterMap (·.pred)).eraseDups}]

def checkTarget (d : Descriptor) (rules : List Rule) (r : BoundRequirement)
    (t : Path) (opts : ServerOptions) : Except String (List Residual) := do
  let k := r.decl.key
  if !opts.ceiling.permits r.decl.info then throw "POLICY"
  if t.contains "-" then
    match r.wildcard with
    | .filtered => return [{kind := "PARENT_FILTER", key := some k, target := some t}]
    | .resolve =>
      let a := wildcardAnchor t
      return [{kind := "RESOLVE_WILDCARD", key := some k, target := some t,
               nonprojectingGet := opts.nonprojecting k a,
               nonprojectingList := listNonprojecting d r.decl.info.resourceType a opts}]
    | _ =>
      if regionAllowed d rules r.decl t false opts then return [] else throw "POLICY"
  if policyDeniesBeforeRow rules k t opts then throw "POLICY"
  if attributeReadFailed rules r.decl.key t opts then throw "SERVER_FAULT"
  if allowed rules r.decl t opts then return []
  if opts.factsOf.isSome then throw "POLICY"
  partialTarget rules k t opts

theorem checkTarget_failed_read {d rules r t opts}
    (concrete : t.contains "-" = false) (permitted : opts.ceiling.permits r.decl.info)
    (possible : policyDeniesBeforeRow rules r.decl.key t opts = false) (failed : attributeReadFailed rules r.decl.key t opts) :
    checkTarget d rules r t opts = .error "SERVER_FAULT" := by
  simp only [checkTarget, concrete, permitted, possible, failed, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, throw, bind, Except.bind]
  rfl

theorem checkTarget_row_complete {d rules r t opts pending} (concrete : t.contains "-" = false)
    (row : opts.factsOf.isSome = true) (ok : checkTarget d rules r t opts = .ok pending) :
    attributeReadFailed rules r.decl.key t opts = false ∧ pending = [] := by
  cases cap : opts.ceiling.permits r.decl.info <;> cases veto : policyDeniesBeforeRow rules r.decl.key t opts <;>
    cases failed : attributeReadFailed rules r.decl.key t opts <;> cases decision : allowed rules r.decl t opts <;>
    simp only [checkTarget, concrete, row, cap, veto, failed, decision, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind, throw] at ok <;>
    cases ok <;> exact ⟨rfl, rfl⟩

/-- An immediate concrete permit has a successful authoritative decision. When
facts are missing, it is valid for every completion of the predicates and faults. -/
theorem checkTarget_concrete_sound {d rules r t opts}
    (concrete : t.contains "-" = false)
    (immediate : checkTarget d rules r t opts = .ok []) (fallback : Facts) :
    opts.ceiling.permits r.decl.info = true ∧
      decide opts.mode (opts.available t fallback) rules r.decl.key t = .allow := by
  by_cases veto : policyDeniesBeforeRow rules r.decl.key t opts
  · cases cap : opts.ceiling.permits r.decl.info <;>
      simp only [checkTarget, concrete, veto, cap, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        throw, bind, Except.bind] at immediate
    all_goals contradiction
  apply allowed_decision (fallback := fallback)
  cases yes : allowed rules r.decl t opts
  · cases cap : opts.ceiling.permits r.decl.info
    · simp only [checkTarget, cap, Bool.not_false, ↓reduceIte] at immediate
      contradiction
    · cases failure : attributeReadFailed rules r.decl.key t opts
      · simp only [checkTarget, veto, partialTarget, concrete, cap, yes, failure, ↓reduceIte, Bool.false_eq_true,
          Bool.not_true, Except.pure, Except.bind, bind, pure, throw] at immediate
        repeat first | split at immediate | (solve | simp at immediate)
      · simp only [checkTarget, veto, concrete, cap, failure, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at immediate
        contradiction
  · rfl

private def checkBoundTarget (d : Descriptor) (rules : List Rule) (opts : ServerOptions)
    (parent : Option Path) (r : BoundRequirement) (t : Path) : Except String (List Residual) :=
  if coveredByParent d rules opts parent r t then .ok [] else checkTarget d rules r t opts

@[simp] private theorem checkBoundTarget_none {d rules opts r t} :
    checkBoundTarget d rules opts none r t = checkTarget d rules r t opts := rfl

def checkBindings (d : Descriptor) (rules : List Rule) (opts : ServerOptions)
    (rs : List BoundRequirement) (parent : Option Path := none) : Except String (List Residual) := do
  if rs.any (·.resolverFault) then throw "SERVER_FAULT"
  if phaseDenies d rules opts rs then throw "POLICY"
  let targets := rs.flatMap fun r => r.targets.map fun (_, b) => (r, b.target)
  let results ← targets.mapM fun (r, t) => checkBoundTarget d rules opts parent r t
  return results.flatten

/-- A denial at any concrete target in the authorization phase fixes its
outcome before any target's row failure can change the reported reason. -/
theorem phase_denial_precedes_rows {d rules opts rs r item}
    (clean : rs.any BoundRequirement.resolverFault = false) (member : r ∈ rs) (bound : item ∈ r.targets)
    (concrete : item.2.target.contains "-" = false)
    (refused : policyDeniesBeforeRow rules r.decl.key item.2.target opts) :
    checkBindings d rules opts rs = .error "POLICY" := by
  have hit : phaseDenies d rules opts rs := List.any_eq_true.mpr ⟨r, member,
    List.any_eq_true.mpr ⟨item, bound, by
      simp only [targetDeniedBeforeRow, concrete, Bool.false_eq_true, ↓reduceIte, refused, Bool.or_true]⟩⟩
  simp only [checkBindings, clean, hit, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, throw]
  rfl

/-- Concrete bound names passed to an enforcing server with complete facts. -/
def BoundDecisions (opts : ServerOptions)
    (rules : List Rule) (rs : List BoundRequirement) : Prop :=
  ∀ r ∈ rs, ¬r.resolverFault ∧ ¬r.unbound ∧ ∀ pair ∈ r.targets,
    pair.2.target.contains "-" = false ∧ opts.rowReadFailed pair.2.target = false ∧ opts.ceiling.permits r.decl.info ∧
      decide opts.mode (opts.available pair.2.target) rules r.decl.key pair.2.target = .allow

private theorem complete_phase {d opts rules rs} (pass : BoundDecisions opts rules rs) :
    phaseDenies d rules opts rs = false := by
  apply List.any_eq_false.mpr
  intro r hr
  apply Bool.eq_false_iff.mp
  apply List.any_eq_false.mpr
  intro pair hp
  obtain ⟨concrete, _, cap, allowed⟩ := (pass r hr).2.2 pair hp
  simp only [targetDeniedBeforeRow, cap, concrete, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  intro blocked
  have denied := pre_row_denial_sound blocked
  rw [allowed] at denied
  contradiction

private theorem batch_validation_only {d m request rules opts rs}
    (resolved : (resolvedBatchParent d m request opts).isOk = true)
    (physical : batchItemsBound d m request opts)
    (decisions : BoundDecisions opts rules rs)
    (present : batchHasAuthority d m request opts rs) :
    batchItemStatus d m request rules opts rs true = .ok ∨
      batchItemStatus d m request rules opts rs true = .invalidArgument := by
  have noFault : rs.any BoundRequirement.resolverFault = false :=
    List.any_eq_false.mpr fun r h => (decisions r h).1
  have bound : rs.any BoundRequirement.unbound = false :=
    List.any_eq_false.mpr fun r h => (decisions r h).2.1
  have writerSafe : (physicalBatchItem d m request opts).any (·.resolverFault) = false ∧
      (physicalBatchItem d m request opts).any (·.unbound) = false := by
    unfold batchItemsBound at physical
    cases eq : physicalBatchItem d m request opts <;> simp_all
  simp only [batchItemStatus, Id.run, pure, noFault, resolved, writerSafe.1, Bool.not_true, Bool.false_and,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, batchNeedsParentProof, present, bound, writerSafe.2]
  split <;> first | exact Or.inr rfl | (split <;> first | exact Or.inl rfl | exact Or.inr rfl)

private theorem mapChecks_empty {xs : List α} {f : α → Except String (List Residual)} :
    (do let results ← xs.mapM f; pure results.flatten : Except String (List Residual)) = .ok [] ↔
      ∀ x ∈ xs, f x = .ok [] := by
  induction xs with
  | nil => simp [List.mapM_nil, bind, pure, Except.bind, Except.pure]
  | cons x xs ih =>
    rw [List.mapM_cons]
    cases hx : f x with
    | error err => simp [hx, bind, Except.bind]
    | ok pending =>
      cases rest : xs.mapM f with
      | error err => simp_all [bind, Except.bind]
      | ok results => simp_all [bind, pure, Except.bind, Except.pure]

theorem checkBindings_immediate_iff {d rules opts rs parent} :
    checkBindings d rules opts rs parent = .ok [] ↔
      (rs.any BoundRequirement.resolverFault = false ∧ phaseDenies d rules opts rs = false) ∧
        ∀ r ∈ rs, ∀ item ∈ r.targets, checkBoundTarget d rules opts parent r item.2.target = .ok [] := by
  cases fault : rs.any BoundRequirement.resolverFault <;> cases denied : phaseDenies d rules opts rs
  · simp only [checkBindings, fault, denied, and_self, Bool.false_eq_true, ↓reduceIte, mapChecks_empty, true_and]
    simp [List.mem_flatMap]
    grind
  all_goals simp [checkBindings, fault, denied, bind, Except.bind]

/-- Every item covered by the independent parent proof passes immediately,
including when its row reader fails. Resolver and policy refusals retain priority. -/
theorem batch_parent_authorizes_without_rows {d rules opts rs parent}
    (resolved : rs.any BoundRequirement.resolverFault = false) (permitted : phaseDenies d rules opts rs = false)
    (covered : ∀ r ∈ rs, ∀ item ∈ r.targets, coveredByParent d rules opts (some parent) r item.2.target) :
    checkBindings d rules opts rs (some parent) = .ok [] := by
  apply checkBindings_immediate_iff.mpr
  refine ⟨⟨resolved, permitted⟩, ?_⟩
  intro r hr item hi
  simp [checkBoundTarget, covered r hr item hi]

private theorem complete_checks {d rules opts rs parent}
    (pass : BoundDecisions opts rules rs) : checkBindings d rules opts rs parent = .ok [] := by
  apply checkBindings_immediate_iff.mpr
  refine ⟨⟨List.any_eq_false.mpr fun r h => (pass r h).1, complete_phase pass⟩, ?_⟩
  intro r hr pair hp
  unfold checkBoundTarget
  split
  · rfl
  obtain ⟨concrete, readable, ceiling, decision⟩ := (pass r hr).2.2 pair hp
  have veto : policyDeniesBeforeRow rules r.decl.key pair.2.target opts = false := by
    cases h : policyDeniesBeforeRow rules r.decl.key pair.2.target opts <;> try rfl
    exact absurd (pre_row_denial_sound h) (by simp [decision])
  simp only [checkTarget, veto, concrete, attributeReadFailed, readable, Bool.and_false, Bool.or_true, ceiling, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, ↓reduceIte, allowed, decision, beq_self_eq_true, Bool.and_true,
    pure, Except.pure]

private def finishAuthorization (d : Descriptor) (m : MethodDecl) (request : Json)
    (rules : List Rule) (opts : ServerOptions) (batch splitItems : Bool)
    (byItem : List BoundRequirement) (pending : List Residual) : Authorization := Id.run do
  let filters : List Residual := (m.itemFilter.bind fun filter => m.requirements.head?.map fun first =>
    {kind := "ITEM_FILTER", key := some (siblingKey first.key filter)}).toList
  let pending := pending ++ filters
  let pending := if batch && !splitItems && !pending.isEmpty then
    pending ++ [{kind := "ATOMIC_BATCH"}] else pending
  if !pending.isEmpty && !opts.handlerResolvesResiduals then
    return {denied "UNHANDLED_RESIDUAL" with residuals := pending}
  if batch && !splitItems && pending.isEmpty then
    let status := batchItemStatus d m request rules opts byItem true
    if status != .ok then return {denied "BATCH" with status := some status}
  return {decision := "PROCEED", residuals := pending}

private theorem finish_proceed {d m request rules opts batch splitItems byItem pending}
    (proceed : (finishAuthorization d m request rules opts batch splitItems byItem pending).decision = "PROCEED") :
    let out := finishAuthorization d m request rules opts batch splitItems byItem pending
    (out.residuals = [] → pending = []) ∧
      (out.residuals ≠ [] → opts.handlerResolvesResiduals = true) := by
  by_cases good : batchItemStatus d m request rules opts byItem true = .ok <;>
    cases handler : opts.handlerResolvesResiduals <;> cases batch <;> cases splitItems <;>
    cases pending <;> simp [finishAuthorization, handler, good, denied] at proceed ⊢ <;>
    split at proceed <;> simp_all

private theorem finish_unhandled {d m request rules opts batch splitItems byItem pending}
    (unregistered : opts.handlerResolvesResiduals = false) :
    let out := finishAuthorization d m request rules opts batch splitItems byItem pending
    out.residuals ≠ [] → out.decision = "DENY" ∧ out.reason = some "UNHANDLED_RESIDUAL" := by
  by_cases good : batchItemStatus d m request rules opts byItem true = .ok <;>
    cases batch <;> cases splitItems <;> cases pending <;>
    simp [finishAuthorization, unregistered, good, denied] <;> split <;> simp_all

def serverBindings (d : Descriptor) (m : MethodDecl) (request : Json) (opts : ServerOptions)
    (perItem : Bool) :=
  requirementsFor d m request (fun _ => some []) opts.guards (opts.names.canonical d.resourcePatterns) (some perItem)

/-- A rule at this scope can be inherited by a parent matching the wildcard. -/
private def matchesSearchParent (scope parent : Path) :=
  scope.length ≤ parent.length && (scope.zip parent).all fun (s, t) => t == "-" || s == t

/-- Refuse before running a wildcard Search only when public evidence rules
out every matching parent. Resolving the filter remains the handler's job. -/
def searchRefusedUpFront (d : Descriptor) (rules : List Rule) (r : Requirement)
    (parent : Path) (opts : ServerOptions) : Bool :=
  let anchor := wildcardAnchor parent
  let app := rules.filter (fun rule => rule.keys.contains r.key)
  parent.contains "-" && parent.all (fun s => s == "-" || segmentOk s) &&
    rules.all (d.resourcePatterns.validSite ·.path) && opts.names.rulesAllowed d.resourcePatterns rules &&
    (!opts.ceiling.permits r.info ||
      app.any (fun rule => rule.finalForbid && !rule.hidden && opts.canName rule.path && rule.path.isPrefixOf anchor) ||
      (!opts.nonprojecting r.key anchor && !app.any (fun rule => matchesSearchParent rule.path parent &&
        (rule.effect == .permit || rule.hidden || !opts.canName rule.path))))

theorem search_refusal_public {d rules r parent opts}
    (refused : searchRefusedUpFront d rules r parent opts = true)
    (credential : opts.ceiling.permits r.info) (privateRules : opts.nonprojecting r.key (wildcardAnchor parent)) :
    ∃ rule ∈ rules, rule.keys.contains r.key ∧ rule.finalForbid ∧ rule.hidden = false ∧
      opts.canName rule.path ∧ rule.path.isPrefixOf (wildcardAnchor parent) := by
  simp only [searchRefusedUpFront, credential, privateRules, Bool.not_true, Bool.false_or,
    Bool.false_and, Bool.or_false, Bool.and_eq_true] at refused
  obtain ⟨rule, member, proof⟩ := List.any_eq_true.mp refused.2
  obtain ⟨source, key⟩ := List.mem_filter.mp member
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at proof
  exact ⟨rule, source, key, proof.1.1.1, proof.1.1.2, proof.1.2, proof.2⟩

/-- Each request phase either resolves to a decision or records whether it
contributed active permissions. The outer phase runs before any item checks. -/
private def pointwisePhase (d : Descriptor) (m : MethodDecl) (request : Json) (rules : List Rule)
    (opts : ServerOptions) (filterHandled perItem : Bool) : Except String Bool := do
  let rs := serverBindings d m request opts perItem
  let fault := if perItem then (physicalBatchItem d m request opts).any (·.resolverFault)
    else singularWriterFault d m request opts
  if fault || rs.any (fun r => r.unbound || r.resolverFault) || phaseDenies d rules opts rs then throw "DENY"
  if m.itemFilter.isSome && !filterHandled then throw "DENY"
  if rs.any (fun r => r.wildcard == .filtered &&
      r.targets.any (fun b => searchRefusedUpFront d rules r.decl b.2.target opts)) then throw "DENY"
  if rs.any (fun r => r.wildcard == .resolve || r.wildcard == .filtered) then throw "RESOLVE_FIRST"
  let parent := if perItem && partialFor m request then batchProofParent d m request opts else none
  unless rs.all (fun r => r.targets.all fun (_, b) => b.target.contains "-" ||
      coveredByParent d rules opts parent r b.target || allowed rules r.decl b.target opts) do throw "DENY"
  return !rs.isEmpty

/-- A pointwise caller supplies row facts and resolves handler obligations.
An atomic batch also needs to pass the same request validation as the interceptor. -/
def decideRequest (d : Descriptor) (name : String) (request : Json) (rules : List Rule)
    (opts : ServerOptions) (filterHandled : Bool := true) : String := Id.run do
  let some m := d.method? name | return "DENY"
  match m.disposition with
  | .unimplemented => return "UNIMPLEMENTED"
  | .handlerPolicy => return "HANDLER_POLICY"
  | .undeclared => return "DENY"
  | .requirements => pure ()
  unless rules.all (d.resourcePatterns.validSite ·.path) && opts.names.rulesAllowed d.resourcePatterns rules do return "DENY"
  if m.isBatch && !partialFor m request then
    return if batchRequestStatus d name request rules opts == .ok then "ALLOW" else "DENY"
  match pointwisePhase d m request rules opts filterHandled false with
  | .error why => return why
  | .ok outer =>
    match pointwisePhase d m request rules opts filterHandled true with
    | .error why => return why
    | .ok items => return if outer || items then "ALLOW" else "DENY"

/-- A bound, filtered Search is refused only on the public up-front check
after the other preconditions pass. Otherwise its pointwise decision defers. -/
theorem decideRequest_filtered_search {d name request rules opts m}
    (served : d.method? name = some m) (decl : m.disposition = .requirements)
    (sites : rules.all (d.resourcePatterns.validSite ·.path)) (names : opts.names.rulesAllowed d.resourcePatterns rules)
    (singular : m.isBatch = false) (resolved : singularWriterFault d m request opts = false)
    (bound : (serverBindings d m request opts false).any (fun r => r.unbound || r.resolverFault) = false)
    (policy : phaseDenies d rules opts (serverBindings d m request opts false) = false)
    (wild : (serverBindings d m request opts false).any (fun r => r.wildcard == .resolve || r.wildcard == .filtered)) :
    decideRequest d name request rules opts true =
      if (serverBindings d m request opts false).any (fun r => r.wildcard == .filtered &&
        r.targets.any (fun b => searchRefusedUpFront d rules r.decl b.2.target opts)) then "DENY" else "RESOLVE_FIRST" := by
  cases refusal : (serverBindings d m request opts false).any (fun r => r.wildcard == .filtered &&
    r.targets.any (fun b => searchRefusedUpFront d rules r.decl b.2.target opts)) <;>
    simp [decideRequest, pointwisePhase, served, decl, sites, names, singular, resolved, bound, policy, wild, refusal,
      throw, bind, Except.bind, pure, Except.pure] <;> rfl

private def authorizeItems (d : Descriptor) (m : MethodDecl) (request : Json)
    (rules : List Rule) (opts : ServerOptions) (batch : Bool)
    (outer : List BoundRequirement) (outerPending : List Residual) : Authorization := Id.run do
  let splitItems := batch && partialFor m request
  if splitItems then
    let raw := requirementsFor d m request (fun _ => some []) opts.guards
      (fun p => .ok (some p)) (some true)
    let pending := {kind := "PARTIAL_BATCH", keys := (raw.map (·.decl.key)).eraseDups} :: outerPending
    return finishAuthorization d m request rules opts batch splitItems [] pending
  if batch && outerPending.isEmpty then
    let items := serverBindings d m request opts true
    let addresses := physicalBatchItem d m request opts
    if addresses.any (·.resolverFault) then return denied "SERVER_FAULT"
    match checkBindings d rules opts items (batchProofParent d m request opts) with
    | .error reason => return denied reason
    | .ok pending =>
      let unbound := addresses.any (·.unbound) || items.any (·.unbound) || (items.isEmpty && outer.isEmpty)
      if pending.isEmpty && (unbound || m.itemFilter.isNone) &&
          parentResolverFault (resolvedBatchParent d m request opts) then return denied "SERVER_FAULT"
      if unbound then
        let status := if pending.isEmpty then batchItemStatus d m request rules opts items true else .denied
        return {denied "BATCH" with status := some status}
      return finishAuthorization d m request rules opts batch splitItems items pending
  return finishAuthorization d m request rules opts batch splitItems [] outerPending

def authorizeRequest (d : Descriptor) (methodName : String) (request : Json)
    (rules : List Rule) (opts : ServerOptions := {}) : Authorization := Id.run do
  let some m := d.method? methodName | return denied "ABSENT_METHOD"
  match m.disposition with
  | .unimplemented => return {decision := "UNIMPLEMENTED"}
  | .handlerPolicy => return {decision := "HANDLER_POLICY", handlerPolicy := m.handlerPolicy}
  | .undeclared => return denied "UNDECLARED"
  | .requirements => pure ()
  if !rules.all (d.resourcePatterns.validSite ·.path) || !opts.names.rulesAllowed d.resourcePatterns rules then return denied "SERVER_FAULT"
  let batch := m.isBatch
  let outer := serverBindings d m request opts false
  if singularWriterFault d m request opts || outer.any (·.resolverFault) then return denied "SERVER_FAULT"
  if outer.any (·.unbound) || (!batch && outer.isEmpty) then return denied "UNBOUND"
  match checkBindings d rules opts outer with
  | .error reason => return denied reason
  | .ok outerPending => return authorizeItems d m request rules opts batch outer outerPending

/-- For a well-bound request with all concrete decisions allowed, batch
validation can still report malformed input. A registered handler accepts
any remaining filtering or partial-success obligations. -/
theorem authorizeRequest_of_decisions {d name request rules opts m}
    (method : d.method? name = some m) (decl : m.disposition = .requirements)
    (store : rules.all (d.resourcePatterns.validSite ·.path)) (aliases : opts.names.rulesAllowed d.resourcePatterns rules)
    (handler : opts.handlerResolvesResiduals = true)
    (address : singularWriterFault d m request opts = false)
    (parent : m.isBatch → partialFor m request = false →
      (resolvedBatchParent d m request opts).isOk = true ∧ batchItemsBound d m request opts)
    (outer : BoundDecisions opts rules (serverBindings d m request opts false))
    (items : BoundDecisions opts rules (serverBindings d m request opts true))
    (present : if m.isBatch then batchHasAuthority d m request opts (serverBindings d m request opts true) = true
      else serverBindings d m request opts false ≠ []) :
    let out := authorizeRequest d name request rules opts
    out.decision = "PROCEED" ∨ (out.reason = some "BATCH" ∧ out.status = some .invalidArgument) := by
  have fault (item : Bool) : (serverBindings d m request opts item).any BoundRequirement.resolverFault = false := by
    cases item <;> apply List.any_eq_false.mpr <;> intro r hr
    · exact (outer r hr).1
    · exact (items r hr).1
  have bound (item : Bool) : (serverBindings d m request opts item).any BoundRequirement.unbound = false := by
    cases item <;> apply List.any_eq_false.mpr <;> intro r hr
    · exact (outer r hr).2.1
    · exact (items r hr).2.1
  simp only [authorizeRequest, method, decl, store, aliases, Bool.not_true, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, Id.run, pure, address, fault, bound, complete_checks outer, authorizeItems, complete_checks items]
  cases batch : m.isBatch with
  | false =>
    simp only [batch, Bool.false_eq_true, ↓reduceIte] at present
    simp [List.isEmpty_eq_false_iff.mpr present, finishAuthorization, handler]
  | true =>
    simp only [batch, ↓reduceIte] at present
    cases splitItems : partialFor m request with
    | true =>
      simp [finishAuthorization, handler]
    | false =>
      obtain ⟨ready, writer⟩ := parent batch splitItems
      have writerSafe : (physicalBatchItem d m request opts).any (·.resolverFault) = false ∧
          (physicalBatchItem d m request opts).any (·.unbound) = false := by
        unfold batchItemsBound at writer
        cases eq : physicalBatchItem d m request opts <;> simp_all
      have active : ((serverBindings d m request opts true).isEmpty && (serverBindings d m request opts false).isEmpty) = false := by
        unfold batchHasAuthority at present
        change (!(_ : List BoundRequirement).isEmpty || (_ && !(serverBindings d m request opts false).isEmpty)) = true at present
        cases h₁ : (serverBindings d m request opts true).isEmpty <;> cases h₂ : (serverBindings d m request opts false).isEmpty <;> simp_all
      have good := batch_validation_only (d := d) (m := m) (request := request) ready writer items present
      cases e : resolvedBatchParent d m request opts with
      | error failure => simp [e, Except.isOk, Except.toBool] at ready
      | ok canonical =>
        rcases good with check | check <;>
          simp [finishAuthorization, active, writerSafe.1, writerSafe.2, parentResolverFault, check, handler, denied] <;>
          split <;> simp <;> split <;> first | exact Or.inl rfl | exact Or.inr ⟨rfl, rfl⟩

/-- The interceptor hands a partial batch to its registered handler once its
outer targets pass, without resolving item names or validating their rows. -/
theorem authorizeRequest_partial_proceed {d name request rules opts m}
    (method : d.method? name = some m) (decl : m.disposition = .requirements)
    (batch : m.isBatch) (selected : partialFor m request)
    (address : singularWriterFault d m request opts = false)
    (store : rules.all (d.resourcePatterns.validSite ·.path)) (aliases : opts.names.rulesAllowed d.resourcePatterns rules)
    (handler : opts.handlerResolvesResiduals)
    (outer : BoundDecisions opts rules (serverBindings d m request opts false)) :
    let out := authorizeRequest d name request rules opts
    out.decision = "PROCEED" ∧ out.residuals.any (·.kind == "PARTIAL_BATCH") := by
  have fault : (serverBindings d m request opts false).any BoundRequirement.resolverFault = false :=
    List.any_eq_false.mpr fun r hr => (outer r hr).1
  have bound : (serverBindings d m request opts false).any BoundRequirement.unbound = false :=
    List.any_eq_false.mpr fun r hr => (outer r hr).2.1
  simp only [authorizeRequest, method, decl, store, aliases, Bool.not_true, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, Id.run, pure, address, fault, bound, batch, Bool.false_and,
    complete_checks outer, authorizeItems, selected, Bool.and_true, finishAuthorization, handler]
  simp

private theorem items_proceed {d m request rules opts batch outer pending} :
    let out := authorizeItems d m request rules opts batch outer pending
    out.decision = "PROCEED" →
      (out.residuals ≠ [] → opts.handlerResolvesResiduals = true) ∧
      (out.residuals = [] → pending = [] ∧
        (batch = true → checkBindings d rules opts (serverBindings d m request opts true) (batchProofParent d m request opts) = .ok [])) := by
  simp only [authorizeItems, Id.run, pure]
  split
  · intro proceed
    have result := finish_proceed proceed
    exact ⟨result.2, fun none => by have := result.1 none; contradiction⟩
  · split
    · rename_i active
      obtain ⟨isBatch, noOuter⟩ := Bool.and_eq_true_iff.mp active
      split
      · simp [denied]
      cases check : checkBindings d rules opts (serverBindings d m request opts true) (batchProofParent d m request opts) with
      | error reason => simp [denied]
      | ok acc =>
        dsimp only
        split
        · simp [denied]
        split
        · simp [denied]
        · intro proceed
          have result := finish_proceed proceed
          exact ⟨result.2, fun none => ⟨List.isEmpty_iff.mp noOuter, fun _ => by rw [result.1 none]⟩⟩
    · rename_i inactive
      intro proceed
      have result := finish_proceed proceed
      exact ⟨result.2, fun none => ⟨result.1 none, fun batch => by
        simp [batch, result.1 none] at inactive⟩⟩

/-- Every immediate authorization checked all bound outer and atomic item
targets. A proceed with outstanding work requires an enforcing handler.
The statements hold for every disposition and error authority. -/
theorem authorizeRequest_checked {d name request rules opts} :
    let out := authorizeRequest d name request rules opts
    out.decision = "PROCEED" →
      (out.residuals ≠ [] → opts.handlerResolvesResiduals = true) ∧
      (out.residuals = [] → ∃ m, d.method? name = some m ∧ m.disposition = .requirements ∧
        rules.all (d.resourcePatterns.validSite ·.path) = true ∧
        checkBindings d rules opts (serverBindings d m request opts false) = .ok [] ∧
        (m.isBatch = true →
          checkBindings d rules opts (serverBindings d m request opts true) (batchProofParent d m request opts) = .ok [])) := by
  simp only [authorizeRequest, Id.run, pure]
  cases method : d.method? name with
  | none => simp [denied]
  | some m =>
    cases disp : m.disposition <;> simp only [disp] <;> try (intro h; contradiction)
    split
    · simp [denied]
    · rename_i valid
      split
      · simp [denied]
      · split
        · simp [denied]
        · cases check : checkBindings d rules opts (serverBindings d m request opts false) with
          | error e => simp [denied]
          | ok pending =>
            intro proceed
            have result := items_proceed proceed
            refine ⟨result.1, fun clear => ?_⟩
            have ⟨noOuter, items⟩ := result.2 clear
            simp only [Option.some.injEq, exists_eq_left', disp, true_and]
            have paths : rules.all (d.resourcePatterns.validSite ·.path) = true := by
              cases h : rules.all (d.resourcePatterns.validSite ·.path) <;> simp_all
            exact ⟨paths, noOuter ▸ check, items⟩

/-- The reason and the presence of the pending work are observable together.
No method can hand unresolved checks to an unregistered handler. -/
theorem authorizeRequest_unhandled {d name request rules opts}
    (unregistered : opts.handlerResolvesResiduals = false) :
    let out := authorizeRequest d name request rules opts
    out.residuals ≠ [] → out.decision = "DENY" ∧ out.reason = some "UNHANDLED_RESIDUAL" := by
  simp only [authorizeRequest, Id.run, pure]
  split <;> try simp [denied]
  split <;> try (intro h; exact (h rfl).elim)
  split <;> try (intro h; exact (h rfl).elim)
  split <;> try (intro h; exact (h rfl).elim)
  split <;> try (intro h; exact (h rfl).elim)
  split <;> try (intro h; exact (h rfl).elim)
  unfold authorizeItems
  simp only [Id.run, pure]
  repeat' first | apply finish_unhandled unregistered | (intro h; exact (h rfl).elim) | split

/-- Outer failure fixes the authorization result before any item is resolved,
including on a partial batch. -/
theorem authorizeRequest_outer_denial {d name request rules opts m e}
    (method : d.method? name = some m) (decl : m.disposition = .requirements)
    (store : rules.all (d.resourcePatterns.validSite ·.path)) (aliases : opts.names.rulesAllowed d.resourcePatterns rules)
    (batch : m.isBatch) (address : singularWriterFault d m request opts = false)
    (bound : (serverBindings d m request opts false).any BoundRequirement.unbound = false)
    (fault : (serverBindings d m request opts false).any BoundRequirement.resolverFault = false)
    (failure : checkBindings d rules opts (serverBindings d m request opts false) = .error e) :
    authorizeRequest d name request rules opts = {decision := "DENY", reason := some e} := by
  simp only [authorizeRequest, method, decl, store, aliases, Id.run, pure, Bool.not_true, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, batch, address, bound, fault, Bool.false_and, failure, denied]

private theorem mapChecks_accept {xs : List α} {f : α → Except String (List Residual)}
    (checked : xs.mapM f = .ok results) {x : α} (member : x ∈ xs) : ∃ v, f x = .ok v := by
  induction xs generalizing results with
  | nil => contradiction
  | cons y ys ih =>
    rw [List.mapM_cons] at checked
    cases head : f y with
    | error err => simp [head, bind, Except.bind] at checked
    | ok val =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨val, head⟩
      · cases rest : ys.mapM f with
        | error e => simp [head, rest, bind, Except.bind] at checked
        | ok vs => exact ih rest tail

/-- A PROCEED with remaining item or handler obligations has already checked
every outer target. Resolving a batch item cannot override an outer denial. -/
theorem authorizeRequest_outer_accepts {d name request rules opts m r item}
    (decl : d.method? name = some m)
    (proceed : (authorizeRequest d name request rules opts).decision = "PROCEED")
    (hr : r ∈ serverBindings d m request opts false) (hb : item ∈ r.targets) :
    ∃ residuals, checkTarget d rules r item.2.target opts = .ok residuals := by
  simp only [authorizeRequest, decl, Id.run, pure] at proceed
  cases disp : m.disposition <;> simp only [disp] at proceed <;> try contradiction
  split at proceed <;> try contradiction
  split at proceed <;> try contradiction
  split at proceed <;> try contradiction
  cases run : checkBindings d rules opts (serverBindings d m request opts false) with
  | error err => simp [run, denied] at proceed
  | ok pending =>
    have clean : (serverBindings d m request opts false).any BoundRequirement.resolverFault = false := by
      cases eq : (serverBindings d m request opts false).any BoundRequirement.resolverFault <;> try rfl
      simp [checkBindings, eq, bind, Except.bind] at run
    have clear : phaseDenies d rules opts (serverBindings d m request opts false) = false := by
      cases eq : phaseDenies d rules opts (serverBindings d m request opts false) <;> try rfl
      simp [checkBindings, clean, eq, bind, Except.bind] at run
    simp only [checkBindings, clean, clear, Bool.false_eq_true, ↓reduceIte] at run
    cases results : List.mapM (fun pair : BoundRequirement × Path =>
        checkTarget d rules pair.1 pair.2 opts) ((serverBindings d m request opts false).flatMap
        (fun req => req.targets.map (fun (_, b) => (req, b.target)))) with
    | error err => simp [results, bind, Except.bind] at run
    | ok vs =>
      apply mapChecks_accept results (x := (r, item.2.target))
      exact List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨item, hb, rfl⟩⟩

/-- An immediate PROCEED authorizes every concrete bound target and every
name in a requested wildcard. Item bindings include automatically triggered
field guards. In-flight handler obligations cannot witness this theorem. -/
theorem authorizeRequest_target_sound {d name request rules opts m}
    (decl : d.method? name = some m) (proceed : (authorizeRequest d name request rules opts).decision = "PROCEED")
    (clear : (authorizeRequest d name request rules opts).residuals = [])
    (req : BoundRequirement) (member : req ∈ serverBindings d m request opts false ++
      (if m.isBatch then serverBindings d m request opts true else []))
    (item : Nat × TargetBinding) (hasItem : item ∈ req.targets) (x : Path) (valid : pathOk x = true)
    (target : if item.2.target.contains "-" then Domain.contains (d.domain req.decl.key) x = true ∧
      InRequestRegion false item.2.target x else x = item.2.target) (fallback : Facts) :
    opts.ceiling.permits req.decl.info = true ∧
      decide opts.mode (opts.available x fallback) rules req.decl.key x = .allow := by
  obtain ⟨m', hm', _, store, outer, items⟩ := (authorizeRequest_checked proceed).2 clear
  have eq : m' = m := Option.some.inj (hm'.symm.trans decl)
  subst m'
  have checked : checkTarget d rules req item.2.target opts = .ok [] ∨
      coveredByParent d rules opts (batchProofParent d m request opts) req item.2.target = true := by
    rcases List.mem_append.mp ‹req ∈ _› with hr | hr
    · exact Or.inl ((checkBindings_immediate_iff.mp outer).2 req hr item ‹_›)
    · split at hr
      next yes =>
        have result := (checkBindings_immediate_iff.mp (items yes)).2 req hr item ‹_›
        unfold checkBoundTarget at result
        split at result <;> simp_all
      next => contradiction
  rcases checked with checked | covered
  case inr =>
    obtain ⟨_, _, _, concrete, _, _⟩ := coveredByParent_iff.mp covered
    simp only [concrete, Bool.false_eq_true, ↓reduceIte] at target
    subst x
    exact coveredByParent_sound covered valid _ _
  cases wild : item.2.target.contains "-" with
  | false =>
    simp only [wild, Bool.false_eq_true, ↓reduceIte] at target
    subst x
    exact checkTarget_concrete_sound wild checked fallback
  | true =>
    simp only [wild, ↓reduceIte] at target
    have yes : regionAllowed d rules req.decl item.2.target false opts = true := by
      cases region : regionAllowed d rules req.decl item.2.target false opts
      · cases ceiling : opts.ceiling.permits req.decl.info <;> cases usage : req.wildcard <;>
          simp only [checkTarget, ceiling, Bool.not_true, Bool.not_false, wild, usage, region, ↓reduceIte,
            Bool.false_eq_true, bind, Except.bind, pure, Except.pure] at checked <;> simp at checked
      · rfl
    exact regionAllowed_sound yes target.1 (by simpa only [wild, Bool.not_true, Bool.false_or] using target.2) valid _ _

/-- A protected singular invocation either proceeds (possibly with handler
work) or is refused. Registration and malformed inputs obey the same split. -/
theorem singular_authorization_result {d name m} (method : d.method? name = some m)
    (protectedMethod : m.disposition = .requirements) (singular : m.isBatch = false) (request rules opts) :
    let result := authorizeRequest d name request rules opts
    result.decision = "DENY" ∨ result.decision = "PROCEED" := by
  simp only [authorizeRequest, method, protectedMethod, singular, Id.run, pure]
  repeat' first | exact Or.inl rfl | exact Or.inr rfl | split
  simp only [authorizeItems, finishAuthorization, Id.run, pure, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  split <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The pointwise entry point uses the checked atomic batch's actual status. -/
theorem decideRequest_atomic_batch {d name request rules opts m} (served : d.method? name = some m)
    (decl : m.disposition = .requirements) (sites : rules.all (d.resourcePatterns.validSite ·.path))
    (aliases : opts.names.rulesAllowed d.resourcePatterns rules) (batch : m.isBatch)
    (atomic : partialFor m request = false) :
    decideRequest d name request rules opts = (if batchRequestStatus d name request rules opts == .ok then "ALLOW" else "DENY") := by
  simp [decideRequest, served, decl, sites, aliases, batch, atomic]

private theorem restrictRegion_exact (p : Pattern) (q : Path) :
    restrictRegion false p q = p.restrictTarget q := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      cases rest : Pattern.restrictTarget p q <;> cases wild : b == "-" <;> cases legal : a.accepts b <;>
        simp [restrictRegion, Pattern.restrictTarget, ih, rest, wild, legal, bind, Option.bind, guard, pure, failure]

/-- The interceptor checks the same exact-name domain and hole exclusion as the
client for a universal wildcard List. The public policy revision and disclosure
settings determine which server claim can discharge the check. -/
theorem wildcard_region_claim {d : Descriptor} {rules r q opts c}
    (wild : q.contains "-") (credential : opts.ceiling.permits r.info)
    (store : rules.all (d.resourcePatterns.validSite ·.path)) (names : opts.names.rulesAllowed d.resourcePatterns rules)
    (nonempty : (candidates (d.domain r.key) q).isEmpty = false)
    (projected : c ∈ regionClaims rules r.key (wildcardAnchor q) (d.domain r.key)
      { nonprojecting := opts.nonprojecting r.key (wildcardAnchor q), canName := opts.canName })
    (kind : c.kind = .allow) (covers : coversTarget q (candidates (d.domain r.key) q) c) :
    regionAllowed d rules r q false opts := by
  unfold candidates at nonempty covers
  simp only [regionAllowed, wild, ↓reduceIte, Bool.not_true, Bool.false_or, restrictRegion_exact,
    credential, names, store, nonempty, Bool.not_false, Bool.true_and]
  exact List.any_eq_true.mpr ⟨c, projected, by simpa [kind, coversTarget] using covers⟩

theorem authorize_wildcard_list {d : Descriptor} {name request rules opts m r b i}
    (method : d.method? name = some m) (decl : m.disposition = .requirements) (single : m.isBatch = false)
    (address : singularWriterFault d m request opts = false) (outer : serverBindings d m request opts false = [r])
    (bound : r.unbound = false) (resolved : r.resolverFault = false) (targets : r.targets = [(i,b)])
    (wildcard : r.wildcard = .universal) (wild : b.target.contains "-") (filter : m.itemFilter = none)
    (credential : opts.ceiling.permits r.decl.info) (store : rules.all (d.resourcePatterns.validSite ·.path))
    (names : opts.names.rulesAllowed d.resourcePatterns rules) (region : regionAllowed d rules r.decl b.target false opts) :
    (authorizeRequest d name request rules opts).decision = "PROCEED" := by
  have checked : checkBindings d rules opts [r] = .ok [] := by
    apply checkBindings_immediate_iff.mpr
    simp only [List.any_cons, List.any_nil, Bool.or_false, resolved, phaseDenies, targets,
      targetDeniedBeforeRow, credential, wild, wildcard, region, beq_self_eq_true, Bool.not_true,
      Bool.false_or, Bool.and_false, true_and, ↓reduceIte, List.mem_singleton, forall_eq]
    simp [checkBoundTarget, checkTarget, coveredByParent, credential, List.contains_iff_mem.mp wild, wildcard, region, pure, Except.pure]
  simp [authorizeRequest, method, decl, store, names, single, outer, resolved, bound, address, checked,
    authorizeItems, finishAuthorization, filter]

/-- The pointwise List decision runs the same universal wildcard check after
both bound phases have passed their structural and resolver checks. -/
theorem decideRequest_wildcard_list {d : Descriptor} {name request rules opts m r b i}
    (method : d.method? name = some m) (decl : m.disposition = .requirements) (single : m.isBatch = false)
    (address : singularWriterFault d m request opts = false) (outer : serverBindings d m request opts false = [r])
    (items : serverBindings d m request opts true = [])
    (physical : (physicalBatchItem d m request opts).any BoundRequirement.resolverFault = false)
    (bound : r.unbound = false) (resolved : r.resolverFault = false) (targets : r.targets = [(i,b)])
    (wildcard : r.wildcard = .universal) (wild : b.target.contains "-") (filter : m.itemFilter = none)
    (store : rules.all (d.resourcePatterns.validSite ·.path)) (names : opts.names.rulesAllowed d.resourcePatterns rules) :
    decideRequest d name request rules opts = if opts.ceiling.permits r.decl.info &&
      regionAllowed d rules r.decl b.target false opts then "ALLOW" else "DENY" := by
  cases cap : opts.ceiling.permits r.decl.info <;> cases region : regionAllowed d rules r.decl b.target false opts <;>
    simp [decideRequest, pointwisePhase, method, decl, single, address, outer, items, physical, bound, resolved,
      targets, wildcard, List.contains_iff_mem.mp wild, filter, store, names, cap, region, phaseDenies,
      targetDeniedBeforeRow, throw, bind, pure, Except.bind, Except.pure] <;> rfl

end Authz
