import Authz.Trie
import Authz.Policy

namespace Authz

/-- A collection can be a hole or a claim scope, but cannot own a grant. -/
inductive GrantSite where
  | serviceRoot
  | resource (first : String) (rest : Path)
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

def GrantSite.path : GrantSite → Path
  | .serviceRoot => []
  | .resource x xs => x :: xs

def UniversalAt (d : Domain) (allowed : Path → Prop) (s : Path) : Prop :=
  ∀ x, Domain.contains d x = true → s <+: x → allowed x

def DownwardMonotone (d : Domain) (allowed : Path → Prop) : Prop :=
  ∀ s, Domain.contains d s = true → allowed s → UniversalAt d allowed s

/-- Theorem 1.1(1), on the binding domain, at a fixed snapshot. -/
theorem monotone_iff_pointwise_universal (d : Domain) (allowed : Path → Prop) :
    DownwardMonotone d allowed ↔
      ∀ s, Domain.contains d s = true → (allowed s ↔ UniversalAt d allowed s) := by
  constructor
  · intro mono s hs
    exact ⟨mono s hs, fun universal => universal s hs List.prefix_rfl⟩
  · intro heq s hs
    exact (heq s hs).1

def AdditiveAllow (sites : List GrantSite) (x : Path) : Prop :=
  ∃ g ∈ sites, g.path <+: x

/-- Theorem 1.1(2), forward direction, including anchors outside the domain. -/
theorem ancestor_permit_universal (here : AdditiveAllow sites s) :
    UniversalAt d (AdditiveAllow sites) s := by
  obtain ⟨g, hg, covers⟩ := here
  exact fun _ _ below => ⟨g, hg, covers.trans below⟩

/-- The matching pathway forces a *resource* strictly below the
anchor, reached through literal segments alone. A literal collection prefix can
never be the returned witness because it cannot occur in the grant store. -/
def FixedResourceBelow (p : Pattern) (anchor : Path) (g : GrantSite) : Prop :=
  g ≠ .serviceRoot ∧ anchor <+: g.path ∧ anchor ≠ g.path ∧
    ∃ rest, Pattern.consume p anchor = some rest ∧ g.path <+: anchor ++ Pattern.literals rest

/-- Theorem 1.1(2), converse. For every target and *each* matching pathway,
a finite permit store either grants at/above the anchor or covers that target
from a fixed resource descendant. No enumeration of a finite sample of IDs suffices. -/
theorem universal_permit_fixed_resource {d : Domain} {s : Path} {sites : List GrantSite}
    (valid : ∀ p ∈ d, p.all Atom.valid = true)
    (universal : UniversalAt d (AdditiveAllow sites) s)
    (noAncestor : ¬AdditiveAllow sites s)
    {p : Pattern} (hp : p ∈ d) {x : Path}
    (hm : Pattern.matches p x = true) (hbelow : s <+: x) :
    ∃ g ∈ sites, FixedResourceBelow p s g ∧ g.path <+: x := by
  obtain ⟨tail, rfl⟩ := hbelow
  have hc := (Pattern.consume_matches _ _).2 hm
  rw [Pattern.consume_append] at hc
  cases consumed : Pattern.consume p s with
  | none => simp [consumed] at hc
  | some rest =>
    have residual : Pattern.matches rest tail = true :=
      (Pattern.consume_matches _ _).1 (by simpa [consumed] using hc)
    let fixed := s ++ Pattern.literals rest
    have fbelow : fixed <+: s ++ tail :=
      (List.prefix_append_right_inj _).2 (Pattern.literals_prefix residual)
    have empty : Domain.nonemptyRegion [p] s (sites.map GrantSite.path) ≠ true := by
      intro test
      have hvalid : ∀ a ∈ [p], a.all Atom.valid = true := by simpa using valid p hp
      obtain ⟨candidate, hcand, scope, avoids⟩ := (Domain.nonemptyRegion_iff hvalid).1 test
      have hb : Domain.contains d candidate = true := by
        apply List.any_eq_true.2
        exact ⟨p, hp, by simpa [Domain.contains] using hcand⟩
      obtain ⟨g, hg, hit⟩ := universal candidate hb scope
      exact avoids _ (List.mem_map_of_mem hg) hit
    have someGrant : ∃ g ∈ sites, g.path <+: fixed := by
      simpa [Domain.nonemptyRegion, Pattern.fixedPrefix, consumed, List.any_eq_true,
        List.isPrefixOf_iff_prefix, fixed] using empty
    obtain ⟨g, hg, hits⟩ := someGrant
    have gNotAbove : ¬g.path <+: s := fun h => noAncestor ⟨g, hg, h⟩
    have below := (List.prefix_or_prefix_of_prefix (List.prefix_append s _) hits).resolve_right gNotAbove
    refine ⟨g, hg, ⟨?_, below, ?_, rest, consumed, hits⟩, hits.trans fbelow⟩
    · rintro rfl
      exact gNotAbove (List.nil_prefix ..)
    · rintro rfl
      exact gNotAbove List.prefix_rfl

private theorem literal_at (p : Pattern) (i : Nat) (hi : i < (Pattern.literals p).length) :
    ∃ s, p[i]? = some (.lit s) := by
  induction p generalizing i with
  | nil => simp [Pattern.literals] at hi
  | cons a p ih =>
    cases a with
    | var => simp [Pattern.literals] at hi
    | lit s =>
      cases i with
      | zero => exact ⟨s, rfl⟩
      | succ i =>
        exact ih i (by simpa [Pattern.literals] using hi)

private theorem Pattern.consume_index {p rest : Pattern} {s : Path}
    (hc : Pattern.consume p s = some rest) (i : Nat) :
    p[s.length + i]? = rest[i]? := by
  induction s generalizing p with
  | nil => simp_all [Pattern.consume]
  | cons y ys ih =>
    cases p with
    | nil => simp [Pattern.consume] at hc
    | cons a p =>
      by_cases ha : a.accepts y
      · simp [Pattern.consume, ha] at hc
        simpa [Nat.succ_add] using ih hc
      · simp [Pattern.consume, ha] at hc

private theorem matches_of_reach_length {p : Pattern} {x : Path}
    (h : Pattern.reach p x = true) (hlen : p.length = x.length) :
    Pattern.matches p x = true := by
  induction x generalizing p with
  | nil => simp_all [Pattern.matches]
  | cons hd tl ih =>
    cases p with
    | nil => simp at hlen
    | cons a p =>
      by_cases ok : a.accepts hd
      · simp only [Pattern.reach, Pattern.consume, ok, ↓reduceIte] at h
        exact Bool.and_eq_true_iff.mpr ⟨ok, ih h (by simpa using hlen)⟩
      · simp [Pattern.reach, Pattern.consume, ok] at h

/-- Theorem 1.1(2), including grants on implicit local parents. At a fixed
literal below the anchor, alternation rules out an ordinary resource ID in
every resource pattern. A valid grant site there must be a singleton. -/
theorem universal_permit_singleton {desc : Descriptor} (wf : desc.WellFormed)
    {k : String} {s : Path} {sites : List GrantSite}
    (typed : ∀ g ∈ sites, g ≠ .serviceRoot → desc.resourcePatterns.isResource g.path = true)
    (universal : UniversalAt (desc.domain k) (AdditiveAllow sites) s)
    (noAncestor : ¬AdditiveAllow sites s)
    {p : Pattern} (hp : p ∈ desc.domain k) {x : Path} (hm : Pattern.matches p x = true)
    (hbelow : s <+: x) :
    ∃ g ∈ sites, FixedResourceBelow p s g ∧ g.path <+: x ∧
      ∃ q ∈ desc.resourcePatterns, Pattern.matches q g.path = true ∧ ∃ v, q.getLast? = some (.lit v) := by
  obtain ⟨g, hg, fixed, covers⟩ := universal_permit_fixed_resource
    (fun _ => desc.domain_valid wf) universal noAncestor hp hm hbelow
  have site := typed g hg fixed.1
  refine ⟨g, hg, fixed, covers, ?_⟩
  obtain ⟨nr, beneath, strict, rest, consumed, bound⟩ := fixed
  have longer : s.length < g.path.length := by
    have := beneath.length_le
    exact Nat.lt_of_le_of_ne this (fun he => strict (beneath.eq_of_length he))
  have len := bound.length_le
  simp only [List.length_append] at len
  have ix : g.path.length - 1 - s.length < (Pattern.literals rest).length := by omega
  obtain ⟨name, lit⟩ := literal_at rest _ ix
  have hidx := Pattern.consume_index consumed (g.path.length - 1 - s.length)
  rw [show s.length + (g.path.length - 1 - s.length) = g.path.length - 1 by omega, lit] at hidx
  have atLiteral := Pattern.alternates_at (desc.domain_alternates wf hp) hidx
  obtain ⟨q, hq, hit⟩ := List.any_eq_true.1 (Bool.and_eq_true_iff.mp site).2
  obtain ⟨reaches, endpoint⟩ := Bool.and_eq_true_iff.mp hit
  have endpointId : ∀ n, q[g.path.length - 1]? ≠ some (.var n) := by
    intro n hv
    have atVar := Pattern.alternates_at (desc.resource_alternates wf hq) hv
    simp_all [Atom.isVariable]
  have hlen : q.length = g.path.length := by
    rcases Bool.or_eq_true_iff.mp endpoint with same | localId
    · exact beq_iff_eq.mp same
    · cases e : q[g.path.length - 1]? with
      | none => simp [e] at localId
      | some a =>
        cases a with
        | lit v => simp [e] at localId
        | var n => exact False.elim (endpointId n e)
  refine ⟨q, hq, matches_of_reach_length reaches hlen, ?_⟩
  rw [List.getLast?_eq_getElem?, hlen]
  cases e : q[g.path.length - 1]? with
  | none =>
    have hi : g.path.length - 1 < q.length := by omega
    simp [List.getElem?_eq_getElem hi] at e
  | some a =>
    cases a with
    | lit v => exact ⟨v, rfl⟩
    | var n => exact False.elim (endpointId n e)

inductive SelectorKind where
  | operation (name : String)
  | accessClass (cls : AccessClass)
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure Selector where
  resourceType : Option String
  kind : SelectorKind
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

def Selector.selects (s : Selector) (k : KeyInfo) (effect : GrantEffect) : Bool :=
  s.resourceType.all (· == k.resourceType) && match s.kind with
  | .operation op => op == k.operation
  | .accessClass cls => cls == k.accessClass && (!k.explicitGrantOnly || effect == .forbid)

structure Grant where
  site : GrantSite
  effect : GrantEffect
  selectors : List Selector
  ceiling : Ceiling := none
  pred : Option String := none
  hidden : Bool := false
  mayError : Bool := false
  final : Bool := true
  sourceIndex : Option Nat := none
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

/-- Authoring and CI selector validation: requires canonical declared types (or `*`),
and either an operation the selected type declares (for `*`, any type) or one of the
six access classes. -/
def validateRoleSelectors (d : Descriptor) (raw : Lean.Json) : Bool := Id.run do
  let some sources := d.resourceSources | return false
  let validSelector := fun (s : Lean.Json) => Id.run do
    let .ok type := (s.getObjValD "type").getStr? | return false
    unless type == "*" || (!d.service.isEmpty && type == d.service ++ "/service") || sources.any (·.1 == type) do return false
    if let .ok op := s.getObjVal? "op" then
      return op.getStr?.toOption.any fun op => identifierOk op &&
        d.requirements.any fun r => (type == "*" || r.info.resourceType == type) && r.info.operation == op
    return (["READ","CREATE","UPDATE","DELETE","ADMIN","EXECUTE"] : List String).any fun cls => s.getObjValD "cls" == .str cls
  let validGroup := fun (group : Lean.Json) => group.getArr?.toOption.any fun selectors =>
    !selectors.isEmpty && selectors.all validSelector
  match raw with
  | .arr grants => return grants.all fun grant => validGroup (grant.getObjValD "selectors")
  | .obj roles => return roles.toList.all fun (_, group) => validGroup group
  | _ => return false

def Grant.selects (g : Grant) (k : KeyInfo) : Bool :=
  (g.effect == .forbid || Ceiling.permits g.ceiling k) &&
    g.selectors.any (fun sel => sel.selects k g.effect)

theorem Grant.forbid_ignores_ceiling (g : Grant) (h : g.effect = .forbid)
    (credential : Ceiling) (key : KeyInfo) :
    ({g with ceiling := credential} : Grant).selects key = g.selects key := by
  simp [Grant.selects, h]

private def CeilingEntry.intersect (a b : CeilingEntry) : Option CeilingEntry :=
  if a.accessClass == b.accessClass && a.resourceType.all (fun t => b.resourceType.all (· == t))
  then some {a with resourceType := a.resourceType.or b.resourceType}
  else none

def Ceiling.intersect : Ceiling → Ceiling → Ceiling
  | none, c | c, none => c
  | some xs, some ys => some (xs.flatMap fun a => ys.filterMap (a.intersect ·))

theorem Ceiling.permits_intersect (a b : Ceiling) (k : KeyInfo) :
    (a.intersect b).permits k = (a.permits k && b.permits k) := by
  cases a with
  | none => simp [Ceiling.intersect, Ceiling.permits]
  | some xs =>
    cases b with
    | none => simp [Ceiling.intersect, Ceiling.permits]
    | some ys =>
      apply Bool.eq_iff_iff.2
      simp only [Ceiling.intersect, Ceiling.permits, Option.all_some, List.any_eq_true,
        Bool.and_eq_true, List.mem_flatMap, List.mem_filterMap, beq_iff_eq]
      constructor
      · rintro ⟨e, ⟨a, ha, b, hb, he⟩, hc, ht⟩
        refine ⟨⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩⟩ <;>
          cases a with | mk ta ca =>
          cases b with | mk tb cb =>
          cases ta <;> cases tb <;> simp_all [CeilingEntry.intersect] <;> grind
      · rintro ⟨⟨a, ha, hca, hta⟩, ⟨b, hb, hcb, htb⟩⟩
        refine ⟨{a with resourceType := a.resourceType.or b.resourceType}, ⟨a, ha, b, hb, ?_⟩, hca, ?_⟩ <;>
          cases a with | mk ta ca =>
          cases b with | mk tb cb =>
          cases ta <;> cases tb <;> simp_all [CeilingEntry.intersect]

def Grant.underCeiling (g : Grant) (credential : Ceiling) : Grant :=
  if g.effect == .forbid then g else {g with ceiling := g.ceiling.intersect credential}

theorem Grant.selects_underCeiling (g : Grant) (c : Ceiling) (k : KeyInfo) :
    (g.underCeiling c).selects k =
      ((g.effect == .forbid || c.permits k) && g.selects k) := by
  cases g with | mk site effect selectors ceiling =>
  cases effect <;> simp [Grant.underCeiling, Grant.selects, Ceiling.permits_intersect,
    show (GrantEffect.permit == .forbid) = false by decide, Bool.and_assoc, Bool.and_left_comm]

def Selector.valid (d : Descriptor) (s : Selector) : Bool :=
  (match s.resourceType with
  | none => true
  | some t => (!d.service.isEmpty && t == d.service ++ "/service") ||
      match d.resourceSources with
      | some sources => sources.any (·.1 == t)
      | none => d.resources.any (·.resourceType == t)) &&
  match s.kind with
  | .operation op => identifierOk op
  | .accessClass _ => true

def Grant.validSite (d : Descriptor) (g : Grant) : Bool :=
  d.resourcePatterns.validSite g.site.path

def Grant.validSelectors (d : Descriptor) (g : Grant) : Bool :=
  !g.selectors.isEmpty && g.selectors.all (Selector.valid d)

def Grant.valid (d : Descriptor) (g : Grant) : Bool :=
  g.validSite d && g.validSelectors d

def expandedKeys (d : Descriptor) (g : Grant) : List String :=
  if g.valid d then
    let reachable := d.trie.reachable g.site.path
    ((d.requirements.filter fun r => g.selects r.info && reachable.contains r.key).map (·.key)).eraseDups
  else []

structure ExpandedGrant where
  path : Path
  effect : GrantEffect
  keys : List String
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

def expandGrant (d : Descriptor) (g : Grant) : Option ExpandedGrant :=
  if g.valid d then some ⟨g.site.path, g.effect, expandedKeys d g⟩ else none

def combineGrants (effects : List GrantEffect) : Bool :=
  effects.contains .permit && !effects.contains .forbid

def decideGrants (d : Descriptor) (gs : List Grant) (r : Requirement) (x : Path) : Bool :=
  gs.all (Grant.valid d) && combineGrants ((gs.filter fun g => g.site.path.isPrefixOf x && g.selects r.info).map (·.effect))

def evaluateExpanded (entries : List (Option ExpandedGrant)) (key : String) (x : Path) : Bool :=
  entries.all Option.isSome && combineGrants ((entries.reduceOption.filter fun e => e.path.isPrefixOf x && e.keys.contains key).map (·.effect))

theorem Descriptor.key_unique {d : Descriptor} {a b : Requirement} (consistent : d.consistentKeys = true)
    (ha : a ∈ d.requirements) (hb : b ∈ d.requirements) (hk : a.key = b.key) :
    a.info = b.info := by
  have h := (List.all_eq_true.1 (List.all_eq_true.1 consistent _ ha)) _ hb
  simpa [hk] using h

private theorem expanded_domain_iff {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys = true) (hr : r ∈ d.requirements)
    (hm : Domain.contains (d.domain r.key) x = true) (g : Grant) (site : g.valid d = true) (hp : g.site.path <+: x) :
    (expandedKeys d g).contains r.key = g.selects r.info := by
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem, expandedKeys, site, ite_true, List.mem_eraseDups, List.mem_map,
    List.mem_filter, Bool.and_eq_true]
  constructor
  · rintro ⟨other, ⟨ho, hs, _⟩, hk⟩
    rwa [Descriptor.key_unique consistent ho hr hk] at hs
  · intro h
    obtain ⟨p, member, hit⟩ := List.any_eq_true.1 hm
    have shape := Pattern.reach_of_matches hit hp
    exact ⟨r, ⟨hr, h, d.trie_reaches_iff .. |>.mpr ⟨_, member, shape⟩⟩, rfl⟩

private theorem expanded_iff {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys = true) (hr : r ∈ d.requirements)
    (hm : Domain.contains r.patterns x = true) (g : Grant) (site : g.valid d = true) (hp : g.site.path <+: x) :
    (expandedKeys d g).contains r.key = g.selects r.info := by
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem, expandedKeys, site, ite_true, List.mem_eraseDups, List.mem_map,
    List.mem_filter, Bool.and_eq_true]
  constructor
  · rintro ⟨other, ⟨ho, hs, _⟩, hk⟩
    rwa [Descriptor.key_unique consistent ho hr hk] at hs
  · intro h
    obtain ⟨p, hmem, hit⟩ := List.any_eq_true.1 hm
    have member : Pattern.shape p ∈ d.domain r.key := by
      simp only [Descriptor.domain, Descriptor.namedDomain, List.mem_eraseDups, List.mem_map, List.mem_flatMap,
        List.mem_filter, beq_iff_eq]
      exact ⟨p, ⟨r, ⟨hr, rfl⟩, hmem⟩, rfl⟩
    have shape : (Pattern.shape p).reach g.site.path = true := by
      have same := Pattern.reach_of_matches hit hp
      rwa [Pattern.reach_shape]
    exact ⟨r, ⟨hr, h, d.trie_reaches_iff .. |>.mpr ⟨_, member, shape⟩⟩, rfl⟩

/-- Proposition 3.1. Compare the two folds over actual, unrestricted grant lists.
The client reads only paths, signs and expanded *strings*, whereas the service
uses the requirement's selectors, class, marker and ceiling. -/
theorem unconditional_projection_exact {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys = true)
    (hr : r ∈ d.requirements) (hm : Domain.contains r.patterns x = true) (gs : List Grant) :
    evaluateExpanded (gs.map (expandGrant d)) r.key x = decideGrants d gs r x := by
  unfold evaluateExpanded decideGrants
  have allValid : (gs.map (expandGrant d)).all Option.isSome =
      gs.all (Grant.valid d) := by
    simp only [List.all_map]
    congr 1
    funext g
    cases site : g.valid d <;> simp [expandGrant, site]
  rw [allValid]
  clear allValid
  cases h : gs.all (Grant.valid d) with
  | false => rfl
  | true =>
    simp only [Bool.true_and]
    congr 1
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      obtain ⟨site, rest⟩ := Bool.and_eq_true_iff.mp h
      let entry : ExpandedGrant := ⟨g.site.path, g.effect, expandedKeys d g⟩
      have equalTest : (entry.path.isPrefixOf x && entry.keys.contains r.key) =
          (g.site.path.isPrefixOf x && g.selects r.info) := by
        by_cases hp : g.site.path <+: x
        · simp only [entry, expanded_iff consistent hr hm g site hp]
        · have hfalse : g.site.path.isPrefixOf x = false := by
            simpa [← Bool.not_eq_true, List.isPrefixOf_iff_prefix] using hp
          simp [entry, hfalse]
      have head : expandGrant d g = some entry := by simp [expandGrant, site, entry]
      have reduce (es : List (Option ExpandedGrant)) :
          (some entry :: es).reduceOption = entry :: es.reduceOption := rfl
      simp only [List.map_cons, head, reduce, List.filter_cons, equalTest]
      split <;> simp only [List.map_cons, entry, ih rest]


def ExpandedGrant.toRule (e : ExpandedGrant) : Rule :=
  { path := e.path, effect := e.effect, keys := e.keys }

/-- A malformed grant invalidates the entire policy, even when a different
grant permits the request. -/
def unconditionalRulesFromGrants (d : Descriptor) (gs : List Grant) : Option (List Rule) :=
  let es := gs.map (expandGrant d)
  if es.all Option.isSome then some (es.reduceOption.map ExpandedGrant.toRule) else none

private theorem rule_fold (es : List ExpandedGrant) (key : String) (t : Path)
    (mode : Authority) (facts : Facts) :
    (decideApplied mode facts ((es.map ExpandedGrant.toRule).filter (applies key t)) == .allow) =
      combineGrants ((es.filter (fun e => e.path.isPrefixOf t && e.keys.contains key)).map (·.effect)) := by
  have sign (effect : GrantEffect) :
      (((es.map ExpandedGrant.toRule).filter (applies key t)).any (fun r => r.effect == effect)) =
        (((es.filter (fun e => e.path.isPrefixOf t && e.keys.contains key)).map (·.effect)).contains effect) := by
    apply Bool.eq_iff_iff.2
    simp [List.any_eq_true, ExpandedGrant.toRule, applies]
    grind
  have blocks (e : ExpandedGrant) : e.toRule.blocks mode facts = (e.effect == .forbid) := by
    cases e with | mk p effect ks => cases effect <;> rfl
  have grants (e : ExpandedGrant) : e.toRule.grants facts = (e.effect == .permit) := by
    cases e with | mk p effect ks => cases effect <;> rfl
  unfold decideApplied
  generalize he : ((es.map ExpandedGrant.toRule).filter (applies key t)) = rules at *
  have same (test prop : Rule → Bool) (h : ∀ e : ExpandedGrant, test e.toRule = prop e.toRule) :
      rules.any test = rules.any prop := by
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true]
    have eq (r : Rule) (hr : r ∈ rules) : test r = prop r := by
      rw [← he] at hr
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hr).1
      exact h e
    grind
  rw [same (fun r => r.blocks mode facts) (fun r => r.effect == .forbid) blocks,
      same (fun r => r.grants facts) (fun r => r.effect == .permit) grants,
      sign, sign]
  let effects := (es.filter fun e => e.path.isPrefixOf t && e.keys.contains key).map (·.effect)
  change ((if effects.contains .forbid then Decision.deny else if effects.contains .permit then .allow else .deny) == .allow) =
    (effects.contains .permit && !effects.contains .forbid)
  cases effects.contains .forbid <;> cases effects.contains .permit <;> rfl

theorem unconditional_policy_exact {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys = true)
    (hr : r ∈ d.requirements) (hm : Domain.contains r.patterns x = true) (path : pathOk x = true)
    (gs : List Grant) (mode : Authority) (facts : Facts) :
    (unconditionalRulesFromGrants d gs).any (fun rules => decide mode facts rules r.key x == .allow) =
      decideGrants d gs r x := by
  rw [← unconditional_projection_exact consistent hr hm gs]
  let es := gs.map (expandGrant d)
  change (if es.all Option.isSome then some (es.reduceOption.map _) else none).any _ = evaluateExpanded es _ _
  have paths : (es.reduceOption.map ExpandedGrant.toRule).all (pathOk ·.path) = true := by
    apply List.all_eq_true.mpr
    intro rule mem
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp mem
    obtain ⟨o, ho, eq⟩ := List.mem_filterMap.mp (show e ∈ es.filterMap id from he)
    have em : some e ∈ es := (show o = some e from eq) ▸ ho
    obtain ⟨g, _, produced⟩ := List.mem_map.mp em
    unfold expandGrant at produced
    split at produced
    · rename_i valid
      cases Option.some.inj produced
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1
    · contradiction
  unfold evaluateExpanded
  cases good : es.all Option.isSome with
  | false => rfl
  | true =>
    simp only [ite_true, Option.any_some, Bool.true_and, decide, path, paths, Bool.not_true, Bool.false_or]
    exact rule_fold ..

private theorem narrowed_grants {d : Descriptor} (gs : List Grant) (c : Ceiling) (r : Requirement) (x : Path) :
    decideGrants d (gs.map (·.underCeiling c)) r x = (c.permits r.info && decideGrants d gs r x) := by
  have site (g : Grant) : (g.underCeiling c).site = g.site := by simp [Grant.underCeiling]; split <;> rfl
  have sels (g : Grant) : (g.underCeiling c).selectors = g.selectors := by simp [Grant.underCeiling]; split <;> rfl
  have sign (g : Grant) : (g.underCeiling c).effect = g.effect := by simp [Grant.underCeiling]; split <;> rfl
  have occurs (es : List Grant) (eff : GrantEffect) :
      ((es.filter fun g => g.site.path.isPrefixOf x && g.selects r.info).map (·.effect)).contains eff =
      es.any (fun g => g.site.path.isPrefixOf x && g.selects r.info && g.effect == eff) := by
    apply Bool.eq_iff_iff.2
    simp [List.any_eq_true]
    grind
  simp only [decideGrants, combineGrants, occurs, List.any_map, List.all_map, Function.comp_def,
    Grant.valid, Grant.validSite, Grant.validSelectors, site, sels, sign, Grant.selects_underCeiling]
  cases hc : c.permits r.info with
  | true => simp; rfl
  | false =>
    have cannot (g : Grant) : (g.site.path.isPrefixOf x && ((g.effect == .forbid) && g.selects r.info) &&
        g.effect == .permit) = false := by cases g.effect <;> simp
    simp [cannot]

/-- The credential narrows each permit in addition to its own ceiling.
Expanding once without the credential and gating the authoritative decision
gives the same answer, including when a forbid survives the narrowing. -/
theorem expanded_policy_under_ceiling {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys = true)
    (hr : r ∈ d.requirements) (hm : Domain.contains r.patterns x = true) (path : pathOk x = true)
    (gs : List Grant) (c : Ceiling) (mode : Authority) (facts : Facts) :
    (unconditionalRulesFromGrants d (gs.map (·.underCeiling c))).any (fun rules => decide mode facts rules r.key x == .allow) =
      (c.permits r.info && (unconditionalRulesFromGrants d gs).any (fun rules => decide mode facts rules r.key x == .allow)) := by
  simp only [unconditional_policy_exact consistent hr hm path, narrowed_grants]

/-- The compiled rule retains the original condition and evaluator metadata.
Credential narrowing affects only the keys selected by the originating grant. -/
def Grant.evaluator (g : Grant) : Rule :=
  { path := g.site.path, effect := g.effect, keys := [], pred := g.pred, hidden := g.hidden,
    mayError := g.mayError, final := g.final, sourceIndex := some (g.sourceIndex.getD 0) }

def Grant.toRule (g : Grant) (d : Descriptor) (c : Ceiling) : Rule :=
  { g.evaluator with keys := expandedKeys d (g.underCeiling c) }

private def compileGrants (d : Descriptor) (gs : List Grant) (c : Ceiling := none) : Option (List Rule) :=
  if gs.all (Grant.valid d) then some (gs.map (fun g => g.toRule d c)) else none

def indexGrants (gs : List Grant) := gs.zipIdx.map fun (g, i) => { g with sourceIndex := some i }

def rulesFromGrants (d : Descriptor) (gs : List Grant) (c : Ceiling := none) :=
  compileGrants d (indexGrants gs) c

/-- A grant with an empty selector list, an undeclared selector resource type, or a
syntactically invalid operation invalidates grant compilation, so malformed or
undeclared-type forbids fail closed instead of silently expanding to zero keys.
Well-formed operations absent from the active descriptor are caught by
`validateRoleSelectors` at policy or CI validation rather than failing closed at
runtime compilation. -/
theorem invalid_selector_fails_closed {d : Descriptor} {gs : List Grant} {g : Grant}
    (mem : g ∈ gs) (bad : g.validSelectors d = false) (c : Ceiling := none) :
    rulesFromGrants d gs c = none := by
  have invalid : (indexGrants gs).all (Grant.valid d) = false := by
    apply Bool.eq_false_iff.mpr
    intro all
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mem
    have inIdx : ({ gs[i] with sourceIndex := some i } : Grant) ∈ indexGrants gs := by
      apply List.mem_map.mpr
      refine ⟨(gs[i], i), ?_, rfl⟩
      exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hi])
    have good := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp all _ inIdx)
    have hsel : gs[i].validSelectors d = true := good.2
    rw [bad] at hsel
    exact Bool.noConfusion hsel
  simp [rulesFromGrants, compileGrants, invalid]

private theorem narrowed_applies {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys = true)
    (hr : r ∈ d.requirements) (hm : Domain.contains r.patterns x = true) (g : Grant) (valid : g.valid d)
    (c : Ceiling) : applies r.key x (g.toRule d c) =
      ((g.effect == .forbid || c.permits r.info) && applies r.key x (g.toRule d none)) := by
  have site (b : Ceiling) : (g.underCeiling b).site = g.site := by unfold Grant.underCeiling; split <;> rfl
  have sels (b : Ceiling) : (g.underCeiling b).selectors = g.selectors := by unfold Grant.underCeiling; split <;> rfl
  by_cases below : g.site.path <+: x
  · have keys (b : Ceiling) := expanded_iff consistent hr hm (g.underCeiling b)
      (by simpa only [Grant.valid, Grant.validSite, Grant.validSelectors, site, sels] using valid)
      (by simpa only [site] using below)
    have yes := List.isPrefixOf_iff_prefix.mpr below
    simp only [applies, Grant.toRule, Grant.evaluator, keys, yes, Bool.and_true, Grant.selects_underCeiling]
    simp [Ceiling.permits]
  · have no : g.site.path.isPrefixOf x = false := Bool.eq_false_iff.mpr (fun h => below (List.isPrefixOf_iff_prefix.mp h))
    simp only [applies, Grant.toRule, Grant.evaluator, no, Bool.and_false]

private theorem compiled_any (gs : List Grant) (d : Descriptor) (c : Ceiling) (key : String) (x : Path)
    (test : Rule → Bool) :
    (((gs.map (fun g => g.toRule d c)).filter (applies key x)).any test) =
      gs.any (fun g => applies key x (g.toRule d c) && test (g.toRule d c)) := by
  apply Bool.eq_iff_iff.2
  simp [List.any_eq_true]

/-- The native decision on expanded grants commutes with a credential ceiling,
including conditional and erroring grants. The adapter supplies the same fault
outcome for the same originating grant before and after key expansion. -/
private theorem compiled_indexed_grant_ceiling {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys = true)
    (hr : r ∈ d.requirements) (hm : Domain.contains r.patterns x = true)
    (gs : List Grant) (c : Ceiling) (mode : Authority) (facts : Facts)
    : (compileGrants d gs c).any (fun rs => decide mode facts rs r.key x == .allow) =
      (c.permits r.info && (compileGrants d gs).any (fun rs => decide mode facts rs r.key x == .allow)) := by
  cases valid : gs.all (Grant.valid d) with
  | false => simp [compileGrants, valid]
  | true =>
    have evaluated (g : Grant) : (g.toRule d c).evaluate facts = (g.toRule d none).evaluate facts := rfl
    have blocks (g : Grant) (mem : g ∈ gs) :
        (applies r.key x (g.toRule d c) && (g.toRule d c).blocks mode facts) =
        (applies r.key x (g.toRule d none) && (g.toRule d none).blocks mode facts) := by
      rw [narrowed_applies consistent hr hm g (List.all_eq_true.mp valid _ mem) c]
      unfold Rule.blocks
      rw [evaluated g]
      change ((_ || _) && _ && ((g.effect == .forbid) && _)) = (_ && ((g.effect == .forbid) && _))
      cases g.effect == .forbid <;> simp
    have grants (g : Grant) (mem : g ∈ gs) :
        (applies r.key x (g.toRule d c) && (g.toRule d c).grants facts) =
        (c.permits r.info && (applies r.key x (g.toRule d none) && (g.toRule d none).grants facts)) := by
      rw [narrowed_applies consistent hr hm g (List.all_eq_true.mp valid _ mem) c]
      simp only [Rule.grants, evaluated g]
      cases eq : (g.toRule d none).evaluate facts == .permit
      · simp
      · have eff := Rule.effect_of_grants (r := g.toRule d none) (facts := facts) eq
        change g.effect = .permit at eff
        simp [eff, show (GrantEffect.permit == .forbid) = false by decide]
    have same (f h : Grant → Bool) (eq : ∀ g ∈ gs, f g = h g) : gs.any f = gs.any h := by
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      grind
    have paths (b : Ceiling) : (gs.map (fun g => g.toRule d b)).all (pathOk ·.path) =
        gs.all (fun g => pathOk g.site.path) := by simp [Grant.toRule, Grant.evaluator, Function.comp_def]
    simp only [compileGrants, valid, ↓reduceIte, Option.any_some, decide, paths]
    split
    · simp
    · simp only [decideApplied, compiled_any, same _ _ blocks, same _ _ grants]
      cases c.permits r.info <;> simp <;> split <;> simp

theorem compiled_grant_ceiling {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys = true)
    (hr : r ∈ d.requirements) (hm : Domain.contains r.patterns x = true)
    (gs : List Grant) (c : Ceiling) (mode : Authority) (facts : Facts) :
    (rulesFromGrants d gs c).any (fun rs => decide mode facts rs r.key x == .allow) =
      (c.permits r.info && (rulesFromGrants d gs).any (fun rs => decide mode facts rs r.key x == .allow)) :=
  compiled_indexed_grant_ceiling consistent hr hm (indexGrants gs) c mode facts

/-- Direct interpretation of a grant's selector at a concrete permission and
site, before the descriptor expands the selector to a list of keys. -/
def selectorRulesAt (gs : List Grant) (info : KeyInfo) (target : Path) (c : Ceiling) :=
  ((indexGrants gs).filter fun g => g.site.path.isPrefixOf target && (g.underCeiling c).selects info).map Grant.evaluator

private theorem applicable_origins {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys)
    (registered : r ∈ d.requirements) (target : Domain.contains (d.domain r.key) x)
    (c : Ceiling) (gs : List Grant) (valid : gs.all (Grant.valid d)) :
    (((gs.map (fun g => g.toRule d c)).filter (applies r.key x)).map Rule.faultIdentity) =
      (gs.filter (fun g => g.site.path.isPrefixOf x && (g.underCeiling c).selects r.info)).map Grant.evaluator := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨site, tail⟩ := Bool.and_eq_true_iff.mp valid
    have sameSite : (g.underCeiling c).site = g.site := by unfold Grant.underCeiling; split <;> rfl
    have sameSels : (g.underCeiling c).selectors = g.selectors := by unfold Grant.underCeiling; split <;> rfl
    have eq : applies r.key x (g.toRule d c) =
        (g.site.path.isPrefixOf x && (g.underCeiling c).selects r.info) := by
      by_cases below : g.site.path <+: x
      · have keys := expanded_domain_iff consistent registered target (g.underCeiling c)
          (by simpa only [Grant.valid, Grant.validSite, Grant.validSelectors, sameSite, sameSels] using site)
          (by simpa only [sameSite] using below)
        simp only [applies, Grant.toRule, Grant.evaluator, keys, List.isPrefixOf_iff_prefix.mpr below, Bool.true_and, Bool.and_true]
      · have no := Bool.eq_false_iff.mpr (fun yes => below (List.isPrefixOf_iff_prefix.mp yes))
        simp [applies, Grant.toRule, Grant.evaluator, no]
    simp only [List.map_cons, List.filter_cons, eq]
    split <;> simp only [List.map_cons, ih tail]
    rfl

private theorem evaluated_identity (r : Rule) (facts : Facts) :
    r.faultIdentity.evaluate facts = r.evaluate facts := by
  cases r with | mk path keys effect pred hidden mayError final sourceIndex =>
    cases sourceIndex <;> rfl

private theorem fold_identities (rules : List Rule) (mode : Authority) (facts : Facts) :
    decideApplied mode facts (rules.map Rule.faultIdentity) = decideApplied mode facts rules := by
  have grants (r : Rule) : r.faultIdentity.grants facts = r.grants facts := by simp [Rule.grants, evaluated_identity]
  have blocks (r : Rule) : r.faultIdentity.blocks mode facts = r.blocks mode facts := by
    have eff : r.faultIdentity.effect = r.effect := by unfold Rule.faultIdentity; split <;> rfl
    simp [Rule.blocks, eff, evaluated_identity]
  simp [decideApplied, List.any_map, Function.comp_def, grants, blocks]

/-- Proposition 3.1 for both authority modes and arbitrary predicate/fault
observations. The source interpreter selects grants directly at the target. -/
theorem expanded_policy_exact {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys)
    (registered : r ∈ d.requirements) (target : Domain.contains (d.domain r.key) x)
    (path : pathOk x) (gs : List Grant) (c : Ceiling) (mode : Authority) (facts : Facts)
    (valid : (indexGrants gs).all (Grant.valid d)) :
    (rulesFromGrants d gs c).map (fun rs => decide mode facts rs r.key x) =
      some (decideApplied mode facts (selectorRulesAt gs r.info x c)) := by
  have sites : ((indexGrants gs).map (fun g => g.toRule d c)).all (pathOk ·.path) := by
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun g member => (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid g member)).1).1
  simp only [rulesFromGrants, compileGrants, valid, ↓reduceIte, Option.map_some, decide, path, sites,
    Bool.not_true, Bool.false_or, Bool.false_eq_true]
  rw [← fold_identities, applicable_origins consistent registered target c _ valid]
  rfl

/-- Expansion preserves the authoritative cell classification as well as the
pointwise decision when conditions or possible evaluator errors are present. -/
theorem expanded_projection_exact {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys)
    (registered : r ∈ d.requirements) (target : Domain.contains (d.domain r.key) x)
    (gs : List Grant) (c : Ceiling) (valid : (indexGrants gs).all (Grant.valid d)) :
    (rulesFromGrants d gs c).map (fun rs => classify (rs.filter (applies r.key x))) =
      some (classify (selectorRulesAt gs r.info x c)) := by
  have keeps (rs : List Rule) : classify (rs.map Rule.faultIdentity) = classify rs := by
    have sure (r : Rule) : r.faultIdentity.surePermit = r.surePermit := by unfold Rule.faultIdentity; split <;> rfl
    have final (r : Rule) : r.faultIdentity.finalForbid = r.finalForbid := by unfold Rule.faultIdentity; split <;> rfl
    have effect (r : Rule) : r.faultIdentity.effect = r.effect := by unfold Rule.faultIdentity; split <;> rfl
    simp [classify, List.any_map, Function.comp_def, sure, final, effect]
  simp only [rulesFromGrants, compileGrants, valid, ↓reduceIte, Option.map_some]
  rw [← keeps, applicable_origins consistent registered target c _ valid]
  rfl

def Grant.unconditionalPermit (g : Grant) := g.effect == .permit && g.pred.isNone && !g.mayError

def selectedPermitSites (gs : List Grant) (c : Ceiling) (info : KeyInfo) :=
  ((indexGrants gs).filter (fun g => (g.underCeiling c).selects info)).map Grant.site

private theorem indexed_valid {d gs} (sites : gs.all (Grant.valid d)) :
    (indexGrants gs).all (Grant.valid d) := by
  apply List.all_eq_true.mpr
  intro g member
  obtain ⟨⟨original, i⟩, pos, rfl⟩ := List.mem_map.mp member
  exact List.all_eq_true.mp sites original (List.fst_mem_of_mem_zipIdx pos)

private theorem indexed_additive {gs : List Grant} (all : gs.all Grant.unconditionalPermit)
    (member : g ∈ indexGrants gs) : g.unconditionalPermit := by
  obtain ⟨⟨original, i⟩, pos, rfl⟩ := List.mem_map.mp member
  exact List.all_eq_true.mp all original (List.fst_mem_of_mem_zipIdx pos)

/-- At a binding name, the executable policy over unconditional permits grants
exactly when an applicable source grant occurs on the ancestor chain. -/
theorem additive_policy_allows_iff {d : Descriptor} {r : Requirement} (consistent : d.consistentKeys)
    (registered : r ∈ d.requirements) (target : Domain.contains (d.domain r.key) x)
    (gs : List Grant) (sites : gs.all (Grant.valid d)) (only : gs.all Grant.unconditionalPermit)
    (c : Ceiling) (mode : Authority) (facts : Facts) :
    (rulesFromGrants d gs c).map (fun rs => decide mode facts rs r.key x) = some .allow ↔
      AdditiveAllow (selectedPermitSites gs c r.info) x := by
  rw [expanded_policy_exact consistent registered target (Domain.contains_pathOk target) gs c mode facts (indexed_valid sites)]
  let candidates := (indexGrants gs).filter fun g => g.site.path.isPrefixOf x && (g.underCeiling c).selects r.info
  have purePermit (g : Grant) (member : g ∈ candidates) :
      g.evaluator.blocks mode facts = false ∧ g.evaluator.grants facts = true := by
    have permit := indexed_additive only (List.mem_filter.mp member).1
    simp only [Grant.unconditionalPermit, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
      Bool.not_eq_true'] at permit
    simp [Grant.evaluator, Rule.blocks, Rule.grants, Rule.evaluate, permit.1.1, permit.1.2, permit.2]
  have clear : (candidates.map Grant.evaluator).any (·.blocks mode facts) = false := by
    apply List.any_eq_false.mpr
    intro _ mem
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp mem
    exact Bool.eq_false_iff.mp (purePermit g hg).1
  change some (decideApplied mode facts (candidates.map Grant.evaluator)) = some .allow ↔ _
  simp only [decideApplied, clear, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
  have yes : (candidates.map Grant.evaluator).any (·.grants facts) = true ↔ ∃ g, g ∈ candidates := by
    simp only [List.any_map, Function.comp_def, List.any_eq_true]
    exact ⟨fun ⟨g, member, _⟩ => ⟨g, member⟩, fun ⟨g, member⟩ => ⟨g, member, (purePermit g member).2⟩⟩
  simp [AdditiveAllow, selectedPermitSites, List.isPrefixOf_iff_prefix, candidates] at yes ⊢
  grind

/-- Theorem 1.1(1) at a snapshot of actual executable grants, for any supported
authority and target-dependent row observations. -/
theorem grant_policy_monotone_iff_universal (d : Descriptor) (gs : List Grant) (c : Ceiling)
    (key : String) (mode : Authority) (facts : Path → Facts) :
    let allowed := fun x => (rulesFromGrants d gs c).map (fun rs => decide mode (facts x) rs key x) = some .allow
    DownwardMonotone (d.domain key) allowed ↔
      ∀ s, Domain.contains (d.domain key) s → (allowed s ↔ UniversalAt (d.domain key) allowed s) :=
  monotone_iff_pointwise_universal _ _

/-- Theorem 1.1(2) for the same policy evaluated by the server. When its permits
cover every target below the anchor and no applicable grant is an ancestor,
each matching path must pass through a granted singleton. -/
theorem grant_policy_universal_singleton {d : Descriptor} (wf : d.WellFormed) {r : Requirement}
    (registered : r ∈ d.requirements) (gs : List Grant) (sites : gs.all (Grant.valid d))
    (only : gs.all Grant.unconditionalPermit) (credential : Ceiling) (mode : Authority)
    (facts : Path → Facts) (anchor : Path)
    (all : UniversalAt (d.domain r.key) (fun x =>
      (rulesFromGrants d gs credential).map (fun rs => decide mode (facts x) rs r.key x) = some .allow) anchor)
    (noAncestor : ¬AdditiveAllow (selectedPermitSites gs credential r.info) anchor)
    {p x} (pattern : p ∈ d.domain r.key) (hit : Pattern.matches p x) (below : anchor <+: x) :
    ∃ g ∈ gs, FixedResourceBelow p anchor g.site ∧ g.site.path <+: x ∧
      (g.underCeiling credential).selects r.info ∧ ∃ q ∈ d.resourcePatterns,
        Pattern.matches q g.site.path = true ∧ ∃ v, q.getLast? = some (.lit v) := by
  have consistent : d.consistentKeys := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp wf).1).2
  have universal : UniversalAt (d.domain r.key) (AdditiveAllow (selectedPermitSites gs credential r.info)) anchor :=
    fun t matchT scope => (additive_policy_allows_iff consistent registered matchT gs sites only credential mode (facts t)).mp
      (all t matchT scope)
  have typed : ∀ s ∈ selectedPermitSites gs credential r.info, s ≠ .serviceRoot → d.resourcePatterns.isResource s.path := by
    intro s member notRoot
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp member
    have valid := List.all_eq_true.mp (indexed_valid sites) _ (List.mem_filter.mp hg).1
    obtain ⟨_, atSite⟩ := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1
    cases tag : g.site <;> simp_all [GrantSite.path]
  obtain ⟨site, member, fixed, covers, singleton⟩ :=
    universal_permit_singleton wf typed universal noAncestor pattern hit below
  obtain ⟨g, selected, rfl⟩ := List.mem_map.mp member
  obtain ⟨indexed, select⟩ := List.mem_filter.mp selected
  obtain ⟨⟨original,i⟩, pos, rfl⟩ := List.mem_map.mp indexed
  refine ⟨original, List.fst_mem_of_mem_zipIdx pos, fixed, covers, ?_, singleton⟩
  simp only [Grant.selects_underCeiling] at select ⊢
  exact select

end Authz
