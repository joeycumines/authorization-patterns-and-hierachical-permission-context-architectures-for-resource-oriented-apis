import Authz.ClientSoundness

namespace Authz

/-- The service promises that resolution preserves length and changes only
declared alias positions or caller-written wildcards. Unknown positions cannot
satisfy this relation. Indices refer to the full supplied resource name. -/
def TargetBinding.InPlaceResolution (b : TargetBinding) (canonical : Path) : Prop :=
  ∃ positions, b.unresolved = some positions ∧ canonical.length = b.source.length ∧
    ∀ i, i ∉ positions → b.source[i]? = some "-" ∨ b.source[i]? = canonical[i]?

private theorem masked_query (source canonical : Path) (positions : List Nat) (start : Nat)
    (lengths : canonical.length = source.length)
    (unchanged : ∀ i, start + i ∉ positions →
      source[i]? = some "-" ∨ source[i]? = canonical[i]?) :
    matchesQuery ((source.zipIdx start).map fun (s,i) => if positions.contains i then "-" else s)
      canonical = true := by
  induction source generalizing canonical start with
  | nil =>
    have h : canonical = [] := List.length_eq_zero_iff.mp lengths
    subst canonical
    rfl
  | cons s ss ih =>
    cases canonical with
    | nil => simp at lengths
    | cons x xs =>
      have tail := ih xs (start + 1) (by simpa using lengths) (by
        intro i known
        simpa using unchanged (i + 1) (by simpa [Nat.add_assoc, Nat.add_comm 1 i] using known))
      by_cases altered : start ∈ positions
      · simpa [matchesQuery, altered] using tail
      · have head := unchanged 0 (by simpa using altered)
        rcases head with wildcard | same <;> simp at *
        · simp [matchesQuery, wildcard, altered, tail]
        · simp [matchesQuery, same, altered, tail]

private theorem matchesQuery_take {q x : Path} (m : matchesQuery q x = true) (n : Nat) :
    matchesQuery (q.take n) (x.take n) = true := by
  induction n generalizing q x with
  | zero => rfl
  | succ k ih =>
    cases q <;> cases x <;> simp_all [matchesQuery]

/-- Widening the supplied name includes every permitted resolver result. Taking
the target prefix happens after widening, including for a derived service root. -/
theorem widenName_matches_canonical {b : TargetBinding} {q canonical}
    (widened : widenName b = some q) (resolved : b.InPlaceResolution canonical) :
    matchesQuery q (canonical.take b.targetLength) = true := by
  obtain ⟨positions, declared, len, unchanged⟩ := resolved
  have full := masked_query b.source canonical positions 0 len (by simpa using unchanged)
  simp [widenName, declared, guard, pure, bind] at widened
  split at widened <;> simp_all [failure, Option.bind]
  split at widened <;> simp_all
  subst q
  exact matchesQuery_take full _

private theorem Pattern.matches_shape_take {p : Pattern} {x : Path} (m : Pattern.matches p x = true)
    (n : Nat) : Pattern.matches (Pattern.shape (p.take n)) (x.take n) = true := by
  induction n generalizing p x with
  | zero => rfl
  | succ n ih =>
    cases p with
    | nil => cases x <;> simp_all [Pattern.matches, Pattern.shape]
    | cons a p =>
      cases x with
      | nil => simp [Pattern.matches] at m
      | cons v vs =>
        simp only [Pattern.matches, Bool.and_eq_true] at m
        cases a <;> simp [Pattern.matches, Pattern.shape, Atom.accepts] at m ⊢ <;>
          exact ⟨m.1, by simpa [Pattern.shape] using ih m.2⟩

/-- A binding pattern is checked on the full canonical name. Its target prefix
is a pattern of the permission key: the whole pattern for resource authorization,
and the declared parent pattern for a derived-parent requirement. -/
def TargetBinding.CanonicalShape (b : TargetBinding) (dom : Domain) (canonical : Path) : Prop :=
  ∃ p ∈ b.patterns, Pattern.matches p canonical = true ∧ Pattern.shape (p.take b.targetLength) ∈ dom

theorem widenName_contains_canonical {b : TargetBinding} {q dom canonical}
    (widened : widenName b = some q) (resolved : b.InPlaceResolution canonical)
    (shape : b.CanonicalShape dom canonical) :
    Domain.contains (candidates dom q) (canonical.take b.targetLength) = true := by
  obtain ⟨p, _, hm, declared⟩ := shape
  exact (candidate_matches ..).2 ⟨List.any_eq_true.mpr
    ⟨_, declared, Pattern.matches_shape_take hm _⟩, widenName_matches_canonical widened resolved⟩

private theorem Descriptor.lookup_domain_eq {d : Descriptor} {key dom}
    (known : d.keyDomains.lookup key = some dom) : dom = d.domain key := by
  obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp known
  have mem : (key, dom) ∈ d.keyDomains.entries := by rw [eq]; simp
  obtain ⟨k, _, eq⟩ := List.mem_map.mp mem
  change (k, d.domain k) = (key, dom) at eq
  cases eq
  rfl

/-- Atomic and partial-success request evidence uses one token for every
required canonical target in that request or item. -/
theorem RequestAllowed.canonical_targets {d : Descriptor} {s ceiling rs now policy mode facts}
    (h : RequestAllowed s d.keyDomains ceiling rs now policy mode facts) :
    ∃ token, ∀ r ∈ rs, ∀ b ∈ r.targets, ∀ canonical, b.InPlaceResolution canonical →
      b.CanonicalShape (d.domain b.key) canonical →
      (evaluateBinding s d.keyDomains b now).token = some token ∧
      decide mode (facts (canonical.take b.targetLength)) (s.policyAt policy token)
        b.key (canonical.take b.targetLength) = .allow := by
  obtain ⟨token, _, granted⟩ := h
  refine ⟨token, ?_⟩
  intro r hr b hb canonical realized shape
  obtain ⟨q, dom, widened, known, shared, _, sound⟩ := (granted r hr).2.2 b hb
  have inst := widenName_contains_canonical widened realized ((d.lookup_domain_eq known).symm ▸ shape)
  obtain ⟨inDomain, query⟩ := (candidate_matches ..).1 inst
  exact ⟨shared, sound _ inDomain query⟩

/-- The actual atomic method offer authorizes the resolved target of every
binding at one accepted subject snapshot. The canonical name matches the
declared resource pattern and its target prefix belongs to the key's domain.
The client never needs to know the values returned by the resolver. -/
theorem method_offer_canonical_allow (d : Descriptor) (wf : d.WellFormed)
    (session policy events method request now ceiling unresolved guards mode) (facts : Path → Facts)
    (allowed : offerRequest d (projectedTrace d.service session policy d.keyDomains events)
      method request now ceiling unresolved guards = .single .allow) :
    let s := projectedTrace d.service session policy d.keyDomains events
    ∃ m token, d.method? method = some m ∧
      ∀ r ∈ (offerBindings d m request unresolved guards).map (·.forClient none),
      ∀ b ∈ r.targets, ∀ canonical, b.InPlaceResolution canonical →
        b.CanonicalShape (d.domain b.key) canonical →
        (evaluateBinding s d.keyDomains b now).token = some token ∧
        decide mode (facts (canonical.take b.targetLength)) (s.policyAt policy token)
          b.key (canonical.take b.targetLength) = .allow := by
  obtain ⟨m, found, evidence⟩ := (method_offer_sound d wf session policy events
    method request now ceiling unresolved guards mode facts).1 allowed
  obtain ⟨token, granted⟩ := evidence.canonical_targets
  exact ⟨m, token, found, granted⟩

private theorem matches_fixed_target {q x : Path} (fixed : "-" ∉ q)
    (fits : matchesQuery q x = true) : x = q := by
  induction q generalizing x with
  | nil => cases x <;> simp_all [matchesQuery]
  | cons s q ih =>
    cases x with
    | nil => simp [matchesQuery] at fits
    | cons y ys =>
      simp only [List.mem_cons, not_or] at fixed
      simp only [matchesQuery, beq_iff_eq, Bool.and_eq_true, Bool.or_eq_true] at fits
      have head := fits.1.resolve_left (Ne.symm fixed.1)
      cases head
      exact congrArg (s :: ·) (ih fixed.2 fits.2)

/-- A policy DENY can only come from a binding with its original target
prefix intact. Aliases below a derived parent may still be unresolved. -/
theorem denied_binding_query {s keys b now q} (widened : widenName b = some q)
    (denied : (evaluateBinding s keys b now).result = .deny) :
    q = b.source.take b.targetLength := by
  cases unresolved : b.unresolved with
  | none => simp [widenName, unresolved] at widened
  | some positions =>
    have outside : ∀ i ∈ positions, b.targetLength ≤ i := by
      intro i hi
      apply Nat.le_of_not_gt
      intro affected
      have changed : positions.any (· < b.targetLength) := List.any_eq_true.mpr ⟨_, hi, by simpa using affected⟩
      simp [evaluateBinding, widened, unresolved, changed] at denied
      split at denied <;> simp_all
    simp [widenName, unresolved, guard, pure, bind] at widened
    split at widened <;> simp_all [failure, Option.bind]
    split at widened <;> simp_all
    subst q
    apply List.ext_getElem (by simp)
    intro i hi _
    have bound : i < b.targetLength := Nat.lt_of_lt_of_le hi (List.length_take_le ..)
    have keep : i ∉ positions := fun h => Nat.not_le_of_lt bound (outside i h)
    simp [List.getElem_take, List.getElem_zipIdx, keep]

/-- A concrete or fixed-parent denial reaches every admissible canonical
resolution. A declared wildcard denial supplies a denying candidate in its
binding domain. In both cases the evidence retains its snapshot token. -/
def CanonicalRequestDenied (d : Descriptor) (s : ClientState) (ceiling : Ceiling)
    (rs : List ActiveRequirement) (now : Nat) (policy : PolicyHistory) (mode : Authority)
    (facts : Path → Facts) : Prop :=
  (∃ r ∈ rs, ceiling.permits r.info = false) ∨
  ∃ r ∈ rs, ∃ b ∈ r.targets, ∃ token x,
    (evaluateBinding s d.keyDomains b now).token = some token ∧
    Domain.contains (d.domain b.key) x ∧ matchesQuery (b.source.take b.targetLength) x ∧
    decide mode (facts x) (s.policyAt policy token) b.key x = .deny ∧
    (∀ canonical, b.InPlaceResolution canonical → "-" ∉ b.source.take b.targetLength →
      canonical.take b.targetLength = x)

theorem RequestDenied.canonical_targets {d : Descriptor} {s ceiling rs now policy mode facts}
    (h : RequestDenied s d.keyDomains ceiling rs now policy mode facts) :
    CanonicalRequestDenied d s ceiling rs now policy mode facts := by
  rcases h with ceiling | ⟨r, hr, b, hb, q, dom, token, x, widened, known, tag, hx, query, no, binding⟩
  · exact Or.inl ceiling
  · have original := denied_binding_query widened binding
    subst q
    refine Or.inr ⟨r, hr, b, hb, token, x, tag, d.lookup_domain_eq known ▸ hx, query, no, ?_⟩
    intro canonical realized fixed
    exact (matches_fixed_target fixed (widenName_matches_canonical widened realized)).trans
      (matches_fixed_target fixed query).symm

theorem method_offer_canonical_deny (d : Descriptor) (wf : d.WellFormed)
    (session policy events method request now ceiling unresolved guards mode facts)
    (denied : offerRequest d (projectedTrace d.service session policy d.keyDomains events)
      method request now ceiling unresolved guards = .single .deny) :
    ∃ m, d.method? method = some m ∧
      CanonicalRequestDenied d (projectedTrace d.service session policy d.keyDomains events) ceiling
        ((offerBindings d m request unresolved guards).map (·.forClient none)) now policy mode facts := by
  obtain ⟨m, found, evidence⟩ := (method_offer_sound d wf session policy events
    method request now ceiling unresolved guards mode facts).2 denied
  exact ⟨m, found, evidence.canonical_targets⟩

/-- Every allowed partial-batch item authorizes each of its resolved targets at one
accepted snapshot. A denied item retains either the ceiling or the failing binding. -/
theorem method_partial_canonical (d : Descriptor) (wf : d.WellFormed)
    (session policy events method request now ceiling unresolved guards mode facts) {result : PartialOffer}
    (offered : offerRequest d (projectedTrace d.service session policy d.keyDomains events)
      method request now ceiling unresolved guards = .partialBatch result) :
    let s := projectedTrace d.service session policy d.keyDomains events
    ∃ m, d.method? method = some m ∧ partialFor m request = true ∧
      let (operation, items) := partialRequirements m (offerBindings d m request unresolved guards) request
      result.items.length = requestItemCount request m.itemContainers ∧ ∀ (i : Nat) (item : List ActiveRequirement), items[i]? = some item →
        (result.items[i]? = some .allow → ∃ token, ∀ r ∈ operation ++ item, ∀ b ∈ r.targets, ∀ canonical,
          b.InPlaceResolution canonical → b.CanonicalShape (d.domain b.key) canonical →
          (evaluateBinding s d.keyDomains b now).token = some token ∧
            decide mode (facts (canonical.take b.targetLength)) (s.policyAt policy token)
              b.key (canonical.take b.targetLength) = .allow) ∧
        (result.items[i]? = some .deny →
          CanonicalRequestDenied d s ceiling (operation ++ item) now policy mode facts) := by
  obtain ⟨m, found, partialMethod, _, _, size, itemAt⟩ := method_partial_offer_sound d wf
    session policy events method request now ceiling unresolved guards mode facts offered
  refine ⟨m, found, partialMethod, size, ?_⟩
  intro i item atIndex
  exact ⟨fun yes => ((itemAt i item atIndex).1 yes).canonical_targets,
         fun no => ((itemAt i item atIndex).2 no).canonical_targets⟩

end Authz
