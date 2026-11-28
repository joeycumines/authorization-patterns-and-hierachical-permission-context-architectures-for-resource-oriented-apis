import Authz.Policy
import Authz.Domain

namespace Authz

def strictDescendant (parent child : Path) : Bool :=
  parent.isPrefixOf child && parent != child

def descendantIndex (rules : List Rule) (key : String) (anchor : Path)
    (domain : Domain) : List Rule :=
  rules.filter fun r => r.keys.contains key && strictDescendant anchor r.path &&
    domain.any (fun p => Pattern.reach p r.path)

/-- Insert into an antichain of roots. Every input subtree remains represented. -/
def insertRoot (p : Path) (roots : List Path) : List Path :=
  if roots.any (·.isPrefixOf p) then roots
  else p :: roots.filter (fun r => !p.isPrefixOf r)

def rootScopes (paths : List Path) := paths.foldr insertRoot []

private def Hits (roots : List Path) (t : Path) := ∃ p ∈ roots, p <+: t

theorem insertRoot_hits (p : Path) (roots : List Path) (t : Path) :
    Hits (insertRoot p roots) t ↔ p <+: t ∨ Hits roots t := by
  unfold insertRoot
  split
  next h =>
    obtain ⟨q, hq, hp⟩ := List.any_eq_true.mp h
    have hp' := List.isPrefixOf_iff_prefix.mp hp
    exact ⟨Or.inr, fun h' => h'.elim (fun hpt => ⟨q, hq, hp'.trans hpt⟩) id⟩
  next =>
    simp only [Hits, List.mem_cons, List.mem_filter, Bool.not_eq_true', exists_eq_or_imp]
    constructor
    · rintro (hp | ⟨x, ⟨hx, _⟩, hxt⟩)
      · exact Or.inl hp
      · exact Or.inr ⟨x, hx, hxt⟩
    · rintro (hp | ⟨x, hx, hxt⟩)
      · exact Or.inl hp
      · by_cases h : p <+: x
        · exact Or.inl (h.trans hxt)
        · exact Or.inr ⟨x, ⟨hx, Bool.eq_false_iff.mpr (fun hit => h (List.isPrefixOf_iff_prefix.mp hit))⟩, hxt⟩

theorem rootScopes_hits (paths : List Path) (t : Path) :
    Hits (rootScopes paths) t ↔ Hits paths t := by
  induction paths with
  | nil => rfl
  | cons p ps ih =>
    change Hits (insertRoot p (rootScopes ps)) t ↔ _
    rw [insertRoot_hits, ih]
    simp [Hits]

theorem rootScopes_subset {p : Path} {paths : List Path} (hp : p ∈ rootScopes paths) :
    p ∈ paths := by
  induction paths with
  | nil => exact hp
  | cons x xs ih =>
    change p ∈ insertRoot x (rootScopes xs) at hp
    unfold insertRoot at hp
    split at hp
    · exact List.mem_cons_of_mem _ (ih hp)
    · rcases List.mem_cons.mp hp with eq | h
      · simp [eq]
      · exact List.mem_cons_of_mem _ (ih (List.mem_filter.mp h).1)

private def Antichain (paths : List Path) :=
  ∀ x ∈ paths, ∀ y ∈ paths, x <+: y → x = y

theorem rootScopes_antichain (paths : List Path) : Antichain (rootScopes paths) := by
  induction paths with
  | nil => simp [rootScopes, Antichain]
  | cons p ps ih =>
    change Antichain (insertRoot p (rootScopes ps))
    unfold insertRoot
    split
    · exact ih
    next h =>
      simp only [List.any_eq_true, List.isPrefixOf_iff_prefix, not_exists] at h
      intro x hx y hy hxy
      rcases List.mem_cons.mp hx with rfl | hx <;> rcases List.mem_cons.mp hy with rfl | hy
      · rfl
      · have hnot := (List.mem_filter.mp hy).2
        simp [List.isPrefixOf_iff_prefix.mpr hxy] at hnot
      · exact (h x ⟨(List.mem_filter.mp hx).1, hxy⟩).elim
      · exact ih _ (List.mem_filter.mp hx).1 _ (List.mem_filter.mp hy).1 hxy

def bounds (rules : List Rule) (key : String) (anchor : Path) (d : Domain) : List Path :=
  (anchor :: (descendantIndex rules key anchor d).map (·.path)).eraseDups

def partition (rules : List Rule) (key : String) (roots : List Path) : List Claim :=
  roots.map fun p =>
    ⟨key, classify (rules.filter (applies key p)), p,
      rootScopes (roots.filter (strictDescendant p))⟩

@[simp] theorem claim_covers_iff {c : Claim} {t : Path} :
    c.covers t = true ↔ c.path <+: t ∧ ¬Hits c.holes t := by
  simp [Claim.covers, Hits, List.any_eq_false]

private theorem bound_mem {rules key anchor domain} {p : Path}
    (hp : p ∈ bounds rules key anchor domain) : anchor <+: p := by
  simp [bounds, descendantIndex, strictDescendant] at hp
  rcases hp with rfl | ⟨r, h, rfl⟩
  · exact List.prefix_refl _
  · grind

private theorem relevant_bound {rules key anchor domain} {r : Rule} {t : Path}
    (hr : r ∈ rules) (hk : key ∈ r.keys) (h : anchor <+: r.path) (ht : r.path <+: t)
    (hd : Domain.contains domain t) : r.path ∈ bounds rules key anchor domain := by
  by_cases he : anchor = r.path
  · simp [bounds, he]
  · obtain ⟨pat, hpat, hm⟩ := List.any_eq_true.mp hd
    simp only [bounds, List.mem_eraseDups, List.mem_cons, List.mem_map]
    right
    exact ⟨r, List.mem_filter.mpr ⟨hr, by
      simp [strictDescendant, hk, he, List.isPrefixOf_iff_prefix.mpr h]
      exact ⟨pat, hpat, Pattern.reach_of_matches hm ht⟩⟩, rfl⟩

/-- A target outside all strict descendant cells inherits exactly its cell's rules. -/
theorem partition_inherits {rules key anchor domain c t}
    (hc : c ∈ partition rules key (bounds rules key anchor domain))
    (ht : c.covers t) (hd : Domain.contains domain t) :
    rules.filter (applies key c.path) = rules.filter (applies key t) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  have ha := bound_mem hp
  obtain ⟨hpt, hholes⟩ := claim_covers_iff.mp ht
  simp only at hpt hholes
  rw [rootScopes_hits] at hholes
  apply List.filter_congr
  intro r hr
  by_cases hk : key ∈ r.keys
  · have equiv : r.path <+: p ↔ r.path <+: t := by
      refine ⟨(·.trans hpt), fun hrt => ?_⟩
      rcases List.prefix_or_prefix_of_prefix hrt hpt with h | h
      · exact h
      · by_cases eq : p = r.path
        · simp [eq]
        · have mem := relevant_bound hr hk (ha.trans h) hrt hd
          exact (hholes ⟨r.path, List.mem_filter.mpr ⟨mem, by
            simp [strictDescendant, h, eq]⟩, hrt⟩).elim
    simp only [applies, List.contains_iff_mem.mpr hk, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simpa using equiv
  · simp [applies, hk]


theorem partition_classifies {rules key anchor domain c t}
    (hc : c ∈ partition rules key (bounds rules key anchor domain))
    (ht : c.covers t) (hd : Domain.contains domain t) :
    c.key = key ∧ c.kind = classify (rules.filter (applies key t)) := by
  have same := partition_inherits hc ht hd
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
  exact ⟨rfl, congrArg classify same⟩

/-- Every descendant name of the anchor lies in a cell, at arbitrary depth. -/
theorem partition_total (rules : List Rule) (key : String) (roots : List Path) {p t : Path}
    (hp : p ∈ roots) (hpt : p <+: t) :
    ∃ c ∈ partition rules key roots, c.covers t = true := by
  by_cases split : Hits (roots.filter (strictDescendant p)) t
  · obtain ⟨q, hq, hqt⟩ := split
    obtain ⟨hq, hstrict⟩ := List.mem_filter.mp hq
    have hlt : p.length < q.length := by
      simp [strictDescendant] at hstrict
      have := hstrict.1.length_le
      apply Nat.lt_of_le_of_ne this
      exact fun he => hstrict.2 (hstrict.1.eq_of_length he)
    exact partition_total rules key roots hq hqt
  · refine ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, claim_covers_iff.mpr ⟨hpt, ?_⟩⟩
    exact fun hit => split ((rootScopes_hits _ _).mp hit)
termination_by t.length - p.length
decreasing_by have := hqt.length_le; omega

def Claim.WellFormed (c : Claim) :=
  (∀ h ∈ c.holes, c.path <+: h ∧ c.path ≠ h) ∧ Antichain c.holes

private theorem partition_wf {c rules key roots} (hc : c ∈ partition rules key roots) :
    c.WellFormed := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  refine ⟨fun h hh => ?_, rootScopes_antichain _⟩
  simpa [strictDescendant] using (List.mem_filter.mp (rootScopes_subset hh)).2

private def absorbable (parent c : Claim) :=
  c.key == parent.key && c.kind == parent.kind && parent.holes.contains c.path

def mergedHoles (parent : Claim) (kids : List Claim) : List Path :=
  (parent.holes.filter fun h => !kids.any (·.path == h)) ++ kids.flatMap (·.holes)

private def mergedClaim (parent : Claim) (kids : List Claim) : Claim :=
  { parent with holes := rootScopes (mergedHoles parent kids) }

/-- No distinct child root of an antichain can cover the same name. -/
private theorem same_hit {holes : List Path} (hac : Antichain holes)
    {p q t : Path} (hp : p ∈ holes) (hq : q ∈ holes) (hpt : p <+: t) (hqt : q <+: t) : p = q := by
  rcases List.prefix_or_prefix_of_prefix hpt hqt with h | h
  · exact hac _ hp _ hq h
  · exact (hac _ hq _ hp h).symm

/-- An enclosing region absorbs *all* its selected direct children at once.
Membership in the result equals membership in their union, even off-domain. -/
theorem merge_exact {parent : Claim} {kids : List Claim} (wf : parent.WellFormed)
    (direct : ∀ c ∈ kids, c.path ∈ parent.holes)
    (childWF : ∀ c ∈ kids, c.WellFormed)
    (unique : ∀ a ∈ kids, ∀ b ∈ kids, a.path = b.path → a = b)
    (t : Path) :
    (mergedClaim parent kids).covers t = true ↔
      parent.covers t = true ∨ ∃ c ∈ kids, c.covers t = true := by
  simp only [claim_covers_iff, mergedClaim, rootScopes_hits]
  constructor
  · rintro ⟨hp, hh⟩
    by_cases hit : Hits parent.holes t
    · obtain ⟨h, hmem, hht⟩ := hit
      by_cases used : ∃ c ∈ kids, c.path = h
      · obtain ⟨c, hc, rfl⟩ := used
        refine Or.inr ⟨c, hc, hht, ?_⟩
        rintro ⟨g, hg, hgt⟩
        exact hh ⟨g, List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hc, hg⟩), hgt⟩
      · apply False.elim
        apply hh
        refine ⟨h, List.mem_append_left _ (List.mem_filter.mpr ⟨hmem, ?_⟩), hht⟩
        simpa using used
    · exact Or.inl ⟨hp, hit⟩
  · rintro (⟨hp, hh⟩ | ⟨c, hc, hct, hh⟩)
    · refine ⟨hp, ?_⟩
      rintro ⟨h, hmem, hht⟩
      rcases List.mem_append.mp hmem with rem | add
      · exact hh ⟨h, (List.mem_filter.mp rem).1, hht⟩
      · obtain ⟨c, hc, hg⟩ := List.mem_flatMap.mp add
        exact hh ⟨_, direct c hc, ((childWF c hc).1 _ hg).1.trans hht⟩
    · refine ⟨(wf.1 _ (direct _ hc)).1.trans hct, ?_⟩
      rintro ⟨h, hmem, hht⟩
      rcases List.mem_append.mp hmem with rem | add
      · obtain ⟨hr, unused⟩ := List.mem_filter.mp rem
        have eq := same_hit wf.2 hr (direct _ hc) hht hct
        simp [eq, List.any_eq_true.mpr (show ∃ x ∈ kids, (x.path == c.path) = true from
          ⟨c, hc, by simp⟩)] at unused
      · obtain ⟨d, hd, hg⟩ := List.mem_flatMap.mp add
        have hdt := ((childWF d hd).1 _ hg).1.trans hht
        have eq := same_hit wf.2 (direct _ hc) (direct _ hd) hct hdt
        cases unique _ hc _ hd eq
        exact hh ⟨h, hg, hht⟩

private theorem merged_wf {parent : Claim} {kids : List Claim} (wf : parent.WellFormed)
    (direct : ∀ c ∈ kids, c.path ∈ parent.holes)
    (childWF : ∀ c ∈ kids, c.WellFormed) :
    (mergedClaim parent kids).WellFormed := by
  refine ⟨?_, rootScopes_antichain _⟩
  intro h hh
  rcases List.mem_append.mp (rootScopes_subset hh) with rem | add
  · exact wf.1 _ (List.mem_filter.mp rem).1
  · obtain ⟨c, hc, hg⟩ := List.mem_flatMap.mp add
    obtain ⟨hpc, ne⟩ := wf.1 _ (direct _ hc)
    have hch := ((childWF c hc).1 _ hg).1
    exact ⟨hpc.trans hch, fun he => ne (hpc.eq_of_length_le (by rw [show parent.path = h from he]; exact hch.length_le))⟩


private def Layout (cells : List Claim) :=
  (∀ c ∈ cells, c.WellFormed) ∧ ∀ a ∈ cells, ∀ b ∈ cells, a.path = b.path → a = b

def Claim.sameKindChildren (parent : Claim) (cells : List Claim) :=
  cells.filter (absorbable parent)

private def replaceGroup (parent : Claim) (kids cells : List Claim) :=
  mergedClaim parent kids :: cells.filter (fun c => c != parent && !kids.contains c)

def mergeAt (profile : Profile) (path : Path) (cells : List Claim) : List Claim :=
  match cells.find? (·.path == path) with
  | none => cells
  | some parent =>
    let kids := parent.sameKindChildren cells
    if kids.isEmpty || (profile == .grantShaped && !(mergedHoles parent kids).isEmpty)
    then cells else replaceGroup parent kids cells

private theorem candidate_props {parent c : Claim} {cells} (hc : c ∈ parent.sameKindChildren cells) :
    c ∈ cells ∧ c.key = parent.key ∧ c.kind = parent.kind ∧ c.path ∈ parent.holes := by
  simpa [Claim.sameKindChildren, absorbable, and_assoc] using hc

private theorem replace_layout {parent cells} (hp : parent ∈ cells) (hl : Layout cells) :
    Layout (replaceGroup parent (parent.sameKindChildren cells) cells) := by
  let kids := parent.sameKindChildren cells
  have cw : (mergedClaim parent kids).WellFormed :=
    merged_wf (hl.1 _ hp) (fun _ hc => (candidate_props hc).2.2.2)
      (fun c hc => hl.1 c (candidate_props hc).1)
  constructor
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact cw
    · exact hl.1 _ (List.mem_filter.mp hc).1
  · intro a ha b hb eq
    rcases List.mem_cons.mp ha with rfl | ha <;> rcases List.mem_cons.mp hb with rfl | hb
    · rfl
    · obtain ⟨hb, diff⟩ := List.mem_filter.mp hb
      have e := hl.2 _ hp _ hb eq
      simp [e] at diff
    · obtain ⟨ha, diff⟩ := List.mem_filter.mp ha
      have e := hl.2 _ ha _ hp eq
      simp [e] at diff
    · exact hl.2 _ (List.mem_filter.mp ha).1 _ (List.mem_filter.mp hb).1 eq

/-- When a merge is eligible, every same-kind direct child in this pass is
absorbed. The witness records the actual merged parent in the resulting list. -/
theorem all_same_kind_children_absorbed (profile : Profile) (path : Path) (cells : List Claim) (parent : Claim)
    (found : cells.find? (fun c : Claim => c.path == path) = some parent)
    (formed : parent.WellFormed)
    (hasChild : (parent.sameKindChildren cells).isEmpty = false)
    (permitted : profile = Profile.scopedClaims ∨ mergedHoles parent (parent.sameKindChildren cells) = []) :
    mergedClaim parent (parent.sameKindChildren cells) ∈ mergeAt profile path cells ∧
    ∀ c ∈ cells, c.key = parent.key → c.kind = parent.kind → c.path ∈ parent.holes →
      c ∉ mergeAt profile path cells := by
  have reduced : mergeAt profile path cells = replaceGroup parent (parent.sameKindChildren cells) cells := by
    rcases permitted with rfl | hempty
    · simp [mergeAt, found, hasChild]
    · simp [mergeAt, found, hasChild, hempty]
  rw [reduced]
  refine ⟨List.mem_cons_self, ?_⟩
  intro c hc hk hv hh out
  have isKid : c ∈ parent.sameKindChildren cells := by simp [Claim.sameKindChildren, absorbable, hc, hk, hv, hh]
  rcases List.mem_cons.mp out with eq | kept
  · have pathEq := congrArg Claim.path eq
    exact (formed.1 c.path hh).2 pathEq.symm
  · simpa [isKid] using (List.mem_filter.mp kept).2

def Supports (cells : List Claim) (key : String) (kind : Kind) (t : Path) :=
  ∃ c ∈ cells, c.key = key ∧ c.kind = kind ∧ c.covers t = true

private theorem replace_support {parent cells} (hp : parent ∈ cells) (hl : Layout cells)
    (key : String) (kind : Kind) (t : Path) :
    Supports (replaceGroup parent (parent.sameKindChildren cells) cells) key kind t ↔
    Supports cells key kind t := by
  let kids := parent.sameKindChildren cells
  have hx := merge_exact (kids := kids) (wf := hl.1 _ hp)
    (fun _ hc => (candidate_props hc).2.2.2)
    (fun _ hc => hl.1 _ (candidate_props hc).1)
    (fun _ ha _ hb => hl.2 _ (candidate_props ha).1 _ (candidate_props hb).1) t
  constructor
  · rintro ⟨c, hc, hk, hv, ht⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · rcases hx.mp ht with ht | ⟨c, hc, ht⟩
      · exact ⟨_, hp, hk, hv, ht⟩
      · obtain ⟨hm, ck, cv, _⟩ := candidate_props hc
        exact ⟨_, hm, ck.trans hk, cv.trans hv, ht⟩
    · exact ⟨_, (List.mem_filter.mp hc).1, hk, hv, ht⟩
  · rintro ⟨c, hc, hk, hv, ht⟩
    by_cases he : c = parent
    · subst c
      exact ⟨_, List.mem_cons_self, hk, hv, hx.mpr (Or.inl ht)⟩
    · by_cases hit : c ∈ kids
      · obtain ⟨_, ck, cv, _⟩ := candidate_props hit
        exact ⟨_, List.mem_cons_self, ck.symm.trans hk, cv.symm.trans hv,
          hx.mpr (Or.inr ⟨c, hit, ht⟩)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hc, by
          simpa [he, kids] using hit⟩), hk, hv, ht⟩

private theorem mergeAt_spec (profile path cells) (hl : Layout cells) :
    Layout (mergeAt profile path cells) ∧
    ∀ key kind t, Supports (mergeAt profile path cells) key kind t ↔ Supports cells key kind t := by
  unfold mergeAt
  split
  next => exact ⟨hl, fun _ _ _ => Iff.rfl⟩
  next parent hf =>
    dsimp only
    split
    · exact ⟨hl, fun _ _ _ => Iff.rfl⟩
    · have hp := List.mem_of_find?_eq_some hf
      exact ⟨replace_layout hp hl, replace_support hp hl⟩

private theorem mergeAll_spec (profile : Profile) (order : List Path) (cells : List Claim)
    (hl : Layout cells) :
    Layout (order.foldl (fun live p => mergeAt profile p live) cells) ∧
    ∀ key kind t, Supports (order.foldl (fun live p => mergeAt profile p live) cells) key kind t ↔
      Supports cells key kind t := by
  induction order generalizing cells with
  | nil => exact ⟨hl, fun _ _ _ => Iff.rfl⟩
  | cons p ps ih =>
    have step := mergeAt_spec profile p cells hl
    have tail := ih _ step.1
    exact ⟨tail.1, fun k v t => (tail.2 k v t).trans (step.2 k v t)⟩

def mergeCells (profile : Profile) (cells : List Claim) :=
  let paths := (cells.map (·.path)).mergeSort (fun p q => p.length >= q.length)
  paths.foldl (fun live p => mergeAt profile p live) cells

/-- Both profiles absorb a complete nested chain of same-kind cells, even when
the middle cell has a hole at the start of the pass. -/
theorem mergeCells_nested_same_kind (profile key kind) (outer middle leaf : Path)
    (first : outer.length < middle.length) (second : middle.length < leaf.length) :
    mergeCells profile [⟨key,kind,leaf,[]⟩, ⟨key,kind,middle,[leaf]⟩, ⟨key,kind,outer,[middle]⟩] =
      [⟨key,kind,outer,[]⟩] := by
  have lm : leaf ≠ middle := by intro h; subst leaf; omega
  have mo : middle ≠ outer := by intro h; subst middle; omega
  have lo : leaf ≠ outer := by intro h; subst leaf; omega
  have sorted : [leaf,middle,outer].Pairwise (fun p q => Decidable.decide (p.length >= q.length) = true) := by
    simp; omega
  simp [mergeCells, List.mergeSort_of_pairwise sorted, mergeAt, Claim.sameKindChildren, absorbable, mergedHoles,
    replaceGroup, mergedClaim, rootScopes, beq_iff_eq, lm, mo, lo, Ne.symm lm, Ne.symm mo, Ne.symm lo]

private theorem partition_layout (rules key roots) : Layout (partition rules key roots) := by
  refine ⟨fun _ hc => partition_wf hc, ?_⟩
  intro a ha b hb he
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hb
  change p = q at he
  cases he
  rfl

theorem mergeCells_exact (profile rules key roots k v t) :
    Supports (mergeCells profile (partition rules key roots)) k v t ↔
      Supports (partition rules key roots) k v t :=
  (mergeAll_spec _ _ _ (partition_layout _ _ _)).2 k v t

/-- Per-key options are evaluated at the response's anchor before inspecting private rules. -/
structure ProjectOptions where
  profile : Profile := .scopedClaims
  nonprojecting : Bool := false
  canName : Path → Bool := fun _ => true
  budget : Option Nat := none

structure KeyProjection where
  claims : List Claim := []
  descendantsOmitted : Bool := false
  deriving Repr, DecidableEq, Lean.ToJson

def privateObstruction (opts : ProjectOptions) (key : String) (anchor : Path) (r : Rule) :=
  r.keys.contains key && (r.hidden || !opts.canName r.path) &&
    (strictDescendant anchor r.path || ((r.pred.isSome || r.mayError) && r.path.isPrefixOf anchor))

def projectKey (rules : List Rule) (key : String) (anchor : Path) (d : Domain)
    (opts : ProjectOptions := {}) : KeyProjection :=
  if opts.nonprojecting || !pathOk anchor || !rules.all (pathOk ·.path) then {} else
  if rules.any (privateObstruction opts key anchor) then {} else
  let roots := bounds rules key anchor d
  if opts.budget.any (roots.length - 1 > ·) then { descendantsOmitted := true } else
  let cells := mergeCells opts.profile (partition rules key roots)
  ⟨cells.filter (fun c => d.nonemptyRegion c.path c.holes &&
    (opts.profile == .scopedClaims || (c.kind == .allow && c.holes.isEmpty))), false⟩

def regionClaims (rules : List Rule) (key : String) (anchor : Path) (d : Domain)
    (opts : ProjectOptions := {}) := (projectKey rules key anchor d opts).claims

/-- A direct projection accepts service root and catalog resources as anchors.
The binding domain may cover only one key in a larger resource catalog. -/
def projectResourceKey (rules : List Rule) (key : String) (anchor : Path) (domain : Domain)
    (opts : ProjectOptions := {}) (resources : Domain := domain) : KeyProjection :=
  if resources.validSite anchor && rules.all (resources.validSite ·.path) then
    projectKey rules key anchor domain opts
  else {}

def projectAnchor (rules : List Rule) (key : String) (anchor : Path) (domain : Domain)
    (opts : ProjectOptions := {}) (resources : Domain := domain) :=
  (projectResourceKey rules key anchor domain opts resources).claims

theorem projectAnchor_valid_site {rules key anchor domain opts resources c}
    (claim : c ∈ projectAnchor rules key anchor domain opts resources) :
    resources.validSite anchor ∧ rules.all (resources.validSite ·.path) ∧
    c ∈ regionClaims rules key anchor domain opts := by
  unfold projectAnchor projectResourceKey at claim
  split at claim
  next ok => exact ⟨(Bool.and_eq_true_iff.mp ok).1, (Bool.and_eq_true_iff.mp ok).2, claim⟩
  next => contradiction

theorem private_twins (left right : List Rule) (key anchor d opts)
    (h : opts.nonprojecting = true) :
    projectKey left key anchor d opts = projectKey right key anchor d opts := by
  simp [projectKey, h]

theorem projectAnchor_classifies {rules key anchor d opts c t}
    (hc : c ∈ regionClaims rules key anchor d opts) (hit : c.covers t)
    (domain : Domain.contains d t) :
    c.key = key ∧ c.kind = classify (rules.filter (applies key t)) := by
  unfold regionClaims projectKey at hc
  dsimp only at hc
  split at hc <;> try contradiction
  split at hc <;> try contradiction
  split at hc <;> try contradiction
  have mem := (List.mem_filter.mp hc).1
  have after : Supports _ c.key c.kind t := ⟨c, mem, rfl, rfl, hit⟩
  obtain ⟨raw, hr, hk, hv, hcov⟩ := (mergeCells_exact ..).mp after
  obtain ⟨rk, rv⟩ := partition_classifies hr hcov domain
  exact ⟨hk.symm.trans rk, hv.symm.trans rv⟩

theorem projectAnchor_key {rules key anchor d opts c}
    (valid : ∀ p ∈ d, p.all Atom.valid = true)
    (hc : c ∈ regionClaims rules key anchor d opts) : c.key = key := by
  have nonempty : Domain.nonemptyRegion d c.path c.holes := by
    unfold regionClaims projectKey at hc
    dsimp only at hc
    split at hc <;> try contradiction
    split at hc <;> try contradiction
    split at hc <;> try contradiction
    have out := (List.mem_filter.mp hc).2
    simp only [Bool.and_eq_true] at out
    exact out.1
  obtain ⟨t, hd, hp, hh⟩ := (Domain.nonemptyRegion_iff valid).mp nonempty
  exact (projectAnchor_classifies hc (claim_covers_iff.mpr ⟨hp, by
    rintro ⟨h, hm, ht⟩; exact hh h hm ht⟩) hd).1

private def PathsIn (roots : List Path) (cells : List Claim) :=
  ∀ c ∈ cells, c.path ∈ roots ∧ c.holes ⊆ roots

private theorem merge_paths {roots cells} (known : PathsIn roots cells) (profile path) :
    PathsIn roots (mergeAt profile path cells) := by
  unfold mergeAt
  split
  · exact known
  next parent found =>
    dsimp only
    split
    · exact known
    · have hp := known parent (List.mem_of_find?_eq_some found)
      intro c hc
      rcases List.mem_cons.mp hc with rfl | old
      · refine ⟨hp.1, ?_⟩
        intro h hh
        rcases List.mem_append.mp (rootScopes_subset hh) with kept | inherited
        · exact hp.2 (List.mem_filter.mp kept).1
        · obtain ⟨child, kid, before⟩ := List.mem_flatMap.mp inherited
          exact (known child (candidate_props kid).1).2 before
      · exact known c (List.mem_filter.mp old).1

private theorem merged_paths (profile rules key roots) :
    PathsIn roots (mergeCells profile (partition rules key roots)) := by
  have start : PathsIn roots (partition rules key roots) := by
    intro c member
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp member
    exact ⟨hp, fun _ hh => (List.mem_filter.mp (rootScopes_subset hh)).1⟩
  have steps (order : List Path) (cells : List Claim) (known : PathsIn roots cells) :
      PathsIn roots (order.foldl (fun live p => mergeAt profile p live) cells) := by
    induction order generalizing cells with
    | nil => exact known
    | cons x xs ih => exact ih _ (merge_paths known profile x)
  exact steps _ _ start

/-- Claim paths and holes come from the actual partition boundaries. Merging
can promote a grandchild boundary to a hole but preserves its reachable path. -/
theorem projectAnchor_structure {rules key anchor d opts c}
    (reachable : d.any (Pattern.reach · anchor) = true)
    (claim : c ∈ regionClaims rules key anchor d opts) :
    pathOk c.path ∧ anchor <+: c.path ∧ d.any (Pattern.reach · c.path) ∧
      (opts.profile = .scopedClaims ∨ (c.kind = .allow ∧ c.holes = [])) ∧
      ∀ h ∈ c.holes, pathOk h ∧ c.path <+: h ∧ c.path ≠ h ∧ d.any (Pattern.reach · h) := by
  unfold regionClaims projectKey at claim
  dsimp only at claim
  split at claim <;> try contradiction
  next enabled =>
    split at claim <;> try contradiction
    split at claim <;> try contradiction
    have ⟨merged, filter⟩ := List.mem_filter.mp claim
    have paths := merged_paths opts.profile rules key (bounds rules key anchor d) c merged
    have well := (mergeAll_spec opts.profile _ _ (partition_layout rules key (bounds rules key anchor d))).1.1 c merged
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at enabled
    have legal (p) (hp : p ∈ bounds rules key anchor d) : pathOk p ∧ d.any (Pattern.reach · p) := by
      simp only [bounds, List.mem_eraseDups, List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨rule, hr, rfl⟩
      · exact ⟨enabled.1.2, reachable⟩
      · have ⟨mem, accepted⟩ := List.mem_filter.mp hr
        exact ⟨List.all_eq_true.mp enabled.2 rule mem, (Bool.and_eq_true_iff.mp accepted).2⟩
    have form := (Bool.and_eq_true_iff.mp filter).2
    refine ⟨(legal _ paths.1).1, bound_mem paths.1, (legal _ paths.1).2,
      by simpa using form, ?_⟩
    intro h hh
    have ok := legal _ (paths.2 hh)
    exact ⟨ok.1, (well.1 h hh).1, (well.1 h hh).2, ok.2⟩

/-- At every name in the binding domain the claim's definitive kind agrees with
either declared authority, for every assignment of dynamic facts and faults. -/
theorem projected_decision {rules key anchor d opts c t}
    (hc : c ∈ regionClaims rules key anchor d opts) (hit : c.covers t)
    (domain : Domain.contains d t) (valid : pathOk t) (mode : Authority) (facts : Facts) :
    (c.kind = .allow → decide mode facts rules key t = .allow) ∧
    (c.kind = .deny → decide mode facts rules key t = .deny) := by
  obtain ⟨_, h⟩ := projectAnchor_classifies hc hit domain
  have well : rules.all (pathOk ·.path) := by
    cases hn : rules.all (pathOk ·.path) <;> simp_all [regionClaims, projectKey]
  simp only [decide, valid, well, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  exact ⟨fun ha => classified_allow _ _ _ (h.symm.trans ha),
    fun hd => classified_deny _ _ _ (h.symm.trans hd)⟩

theorem projection_no_mixed_overlap {rules key anchor d opts a b t}
    (ha : a ∈ regionClaims rules key anchor d opts) (hb : b ∈ regionClaims rules key anchor d opts)
    (atarget : a.covers t) (btarget : b.covers t) (hd : Domain.contains d t) : a.kind = b.kind :=
  (projectAnchor_classifies ha atarget hd).2.trans (projectAnchor_classifies hb btarget hd).2.symm


private def FreeAllow (cells : List Claim) (key : String) (t : Path) :=
  ∃ c ∈ cells, c.key = key ∧ c.kind = .allow ∧ c.holes = [] ∧ c.path <+: t

private theorem mergeAt_keeps_grant {cells key t} (hl : Layout cells) (path : Path)
    (openGrant : FreeAllow cells key t) : FreeAllow (mergeAt .grantShaped path cells) key t := by
  unfold mergeAt
  split
  next => exact openGrant
  next parent hf =>
    dsimp only
    split
    · exact openGrant
    next h =>
      have hp := List.mem_of_find?_eq_some hf
      let kids := parent.sameKindChildren cells
      have empty : mergedHoles parent kids = [] := by
        simpa [kids] using (show (mergedHoles parent (parent.sameKindChildren cells)).isEmpty = true by grind)
      have noHoles : (mergedClaim parent kids).holes = [] := by simp [mergedClaim, empty, rootScopes]
      obtain ⟨c, hc, hk, hv, hh, hct⟩ := openGrant
      by_cases he : c = parent
      · subst c
        exact ⟨_, List.mem_cons_self, hk, hv, noHoles, hct⟩
      · by_cases hit : c ∈ kids
        · obtain ⟨_, ck, cv, dir⟩ := candidate_props hit
          exact ⟨_, List.mem_cons_self, ck.symm.trans hk, cv.symm.trans hv, noHoles,
            ((hl.1 _ hp).1 _ dir).1.trans hct⟩
        · refine ⟨c, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hc, ?_⟩), hk, hv, hh, hct⟩
          simpa [he, kids] using hit

private theorem mergeAll_keeps_grant (order : List Path) (cells : List Claim) (hl : Layout cells)
    (key : String) (t : Path) (grant : FreeAllow cells key t) :
    FreeAllow (order.foldl (fun live p => mergeAt .grantShaped p live) cells) key t := by
  induction order generalizing cells with
  | nil => exact grant
  | cons p ps ih =>
    exact ih _ (mergeAt_spec _ _ _ hl).1 (mergeAt_keeps_grant hl p grant)

/-- A previously hole-free ALLOW remains covered by a hole-free ALLOW after
bottom-up Grant-Shaped merging; coarsening can therefore emit it. -/
theorem grantShaped_keeps_child (rules key roots c t)
    (hc : c ∈ partition rules key roots) (hk : c.kind = .allow)
    (holes : c.holes = []) (hct : c.path <+: t) :
    ∃ out ∈ mergeCells .grantShaped (partition rules key roots),
      out.key = c.key ∧ out.kind = .allow ∧ out.holes = [] ∧ out.path <+: t :=
  mergeAll_keeps_grant _ _ (partition_layout ..) _ _ ⟨c, hc, rfl, hk, holes, hct⟩

/-- Scoped Claims represents the unique classification at every potential target,
including names absent from storage, whenever disclosure and budget permit it. -/
theorem scoped_projection_total (rules : List Rule) (key : String) (anchor : Path)
    (d : Domain) (opts : ProjectOptions) (profile : opts.profile = .scopedClaims)
    (enabled : opts.nonprojecting = false) (well : rules.all (pathOk ·.path) = true)
    (path : pathOk anchor = true) (available : rules.any (privateObstruction opts key anchor) = false)
    (budget : opts.budget.any ((bounds rules key anchor d).length - 1 > ·) = false)
    (valid : ∀ p ∈ d, p.all Atom.valid = true)
    {t : Path} (domain : Domain.contains d t) (within : anchor <+: t) :
    Supports (regionClaims rules key anchor d opts) key (classify (rules.filter (applies key t))) t := by
  let roots := bounds rules key anchor d
  have base : anchor ∈ roots := by simp [roots, bounds]
  obtain ⟨raw, hr, hit⟩ := partition_total rules key roots base within
  obtain ⟨hk, hv⟩ := partition_classifies hr hit domain
  have before : Supports (partition rules key roots) key (classify (rules.filter (applies key t))) t :=
    ⟨raw, hr, hk, hv, hit⟩
  obtain ⟨out, hout, hkey, hkind, covers⟩ :=
    (mergeCells_exact opts.profile rules key roots _ _ t).mpr before
  obtain ⟨inside, holes⟩ := claim_covers_iff.mp covers
  have live := (Domain.nonemptyRegion_iff valid).mpr
    ⟨t, domain, inside, fun h hm ht => holes ⟨h, hm, ht⟩⟩
  refine ⟨out, ?_, hkey, hkind, covers⟩
  simp only [regionClaims, projectKey, enabled, path, well, Bool.not_true, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, available, budget, List.mem_filter]
  exact ⟨hout, by simp [profile, live]⟩

/-- A child that becomes exception-free during bottom-up merging is eligible
for publication, including a child that originally had same-kind descendants. -/
theorem grantShaped_publishes_merged (rules : List Rule) (key : String) (anchor : Path)
    (d : Domain) (opts : ProjectOptions) (profile : opts.profile = .grantShaped)
    (enabled : opts.nonprojecting = false) (well : rules.all (pathOk ·.path) = true)
    (path : pathOk anchor = true) (available : rules.any (privateObstruction opts key anchor) = false)
    (budget : opts.budget.any ((bounds rules key anchor d).length - 1 > ·) = false)
    (valid : ∀ p ∈ d, p.all Atom.valid = true)
    {c : Claim} (merged : c ∈ mergeCells .grantShaped (partition rules key (bounds rules key anchor d)))
    (kind : c.kind = .allow) (free : c.holes = []) {t : Path}
    (domain : Domain.contains d t) (within : c.path <+: t) :
    Supports (regionClaims rules key anchor d opts) c.key .allow t := by
  have live : Domain.nonemptyRegion d c.path c.holes = true := (Domain.nonemptyRegion_iff valid).mpr
    ⟨t, domain, within, by simp [free]⟩
  refine ⟨c, ?_, rfl, kind, claim_covers_iff.mpr ⟨within, by simp [free, Hits]⟩⟩
  simp only [regionClaims, projectKey, enabled, path, well, Bool.not_true, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, available, budget, profile, List.mem_filter]
  exact ⟨merged, by simp only [live, Bool.true_and]; simp [kind, free]⟩

/-- A child may acquire an exception-free allow at its own turn in the merge.
Later merges preserve that allow up to the published projection. -/
theorem grantShaped_publishes_after_absorption (rules : List Rule) (key : String) (anchor : Path)
    (d : Domain) (opts : ProjectOptions) (profile : opts.profile = .grantShaped)
    (enabled : opts.nonprojecting = false) (well : rules.all (pathOk ·.path) = true)
    (path : pathOk anchor = true) (available : rules.any (privateObstruction opts key anchor) = false)
    (budget : opts.budget.any ((bounds rules key anchor d).length - 1 > ·) = false)
    (valid : ∀ p ∈ d, p.all Atom.valid = true)
    {c : Claim} {processed later : List Path} {t : Path}
    (kind : c.kind = .allow) (domain : Domain.contains d t) (within : c.path <+: t) :
    let raw := partition rules key (bounds rules key anchor d)
    let before := processed.foldl (fun cells p => mergeAt .grantShaped p cells) raw
    (raw.map (·.path)).mergeSort (fun p q => p.length >= q.length) = processed ++ c.path :: later →
    before.find? (fun cell => cell.path == c.path) = some c →
    (c.sameKindChildren before).isEmpty = false → mergedHoles c (c.sameKindChildren before) = [] →
    Supports (regionClaims rules key anchor d opts) c.key .allow t := by
  intro raw before schedule found children closed
  have layout := (mergeAll_spec .grantShaped processed raw (partition_layout ..)).1
  have formed := layout.1 c (List.mem_of_find?_eq_some found)
  have absorbed := (all_same_kind_children_absorbed .grantShaped c.path before c found formed children (Or.inr closed)).1
  have free : FreeAllow (mergeAt .grantShaped c.path before) c.key t :=
    ⟨_, absorbed, rfl, kind, by simp [mergedClaim, closed, rootScopes], within⟩
  obtain ⟨out, member, same, allow, empty, covers⟩ := mergeAll_keeps_grant later _
    (mergeAt_spec .grantShaped c.path before layout).1 c.key t free
  have published : out ∈ mergeCells .grantShaped raw := by
    simpa only [mergeCells, schedule, List.foldl_append, List.foldl_cons, before] using member
  exact same ▸ grantShaped_publishes_merged rules key anchor d opts profile enabled well path available budget
    valid published allow empty domain covers

/-- Projection and coarsening retain the target of an exception-free child grant
whenever the key is disclosable, the index budget suffices, and a binding exists. -/
theorem grantShaped_publishes_child (rules : List Rule) (key : String) (anchor : Path)
    (d : Domain) (opts : ProjectOptions) (profile : opts.profile = .grantShaped)
    (enabled : opts.nonprojecting = false) (well : rules.all (pathOk ·.path) = true)
    (path : pathOk anchor = true) (available : rules.any (privateObstruction opts key anchor) = false)
    (budget : opts.budget.any ((bounds rules key anchor d).length - 1 > ·) = false)
    (valid : ∀ p ∈ d, p.all Atom.valid = true)
    {c : Claim} (raw : c ∈ partition rules key (bounds rules key anchor d))
    (kind : c.kind = .allow) (free : c.holes = [])
    {t : Path} (domain : Domain.contains d t) (within : c.path <+: t) :
    Supports (regionClaims rules key anchor d opts) key .allow t := by
  have hct := claim_covers_iff.mpr (show c.path <+: t ∧ ¬Hits c.holes t from
    ⟨within, by simp [free, Hits]⟩)
  have keyEq := (partition_classifies raw hct domain).1
  obtain ⟨out, hm, hk, hv, hh, hp⟩ := grantShaped_keeps_child _ _ _ _ _ raw kind free within
  have live : Domain.nonemptyRegion d out.path out.holes = true := (Domain.nonemptyRegion_iff valid).mpr
    ⟨t, domain, hp, by simp [hh]⟩
  refine ⟨out, ?_, hk.trans keyEq, hv, claim_covers_iff.mpr ⟨hp, by simp [hh, Hits]⟩⟩
  simp only [regionClaims, projectKey, enabled, path, well, Bool.not_true, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, available, budget, profile, List.mem_filter]
  exact ⟨hm, by simp only [live, Bool.true_and]; simp [hv, hh]⟩

structure ContextProjection where
  anchor : Path
  profile : Profile
  claims : List Claim
  descendantsOmitted : Bool
  error : Option String := none
  deriving Repr, DecidableEq, Lean.ToJson

/-- At one public anchor the service computes the budget bit solely from keys
eligible to project. The descriptor fixes key order in both worlds. -/
def projectContext (rules : List Rule) (keys : List (String × Domain)) (resources : Domain) (anchor : Path)
    (profile : Profile) (options : String → ProjectOptions) : ContextProjection :=
  if !resources.validSite anchor || !rules.all (resources.validSite ·.path) then
    ⟨anchor, profile, [], false, some "SERVER_FAULT"⟩
  else
  let parts := (keys.filter fun kd => kd.2.any (fun p => Pattern.reach p anchor)).map fun (key, d) =>
    projectKey (rules.filter (·.keys.contains key)) key anchor d
      { options key with profile }
  ⟨anchor, profile, parts.flatMap (·.claims), parts.any (·.descendantsOmitted), none⟩

/-- Only ancestors and descendants of this anchor can affect its cells. -/
def Rule.comparableAt (key : String) (anchor : Path) (r : Rule) : Bool :=
  r.keys.contains key && (r.path.isPrefixOf anchor || anchor.isPrefixOf r.path)

private theorem narrower_filters {l r : List α} {localRule test : α → Bool}
    (agree : l.filter localRule = r.filter localRule)
    (implies : ∀ x, test x = true → localRule x = true) :
    l.filter test = r.filter test := by
  have absorb (rules : List α) : (rules.filter localRule).filter test = rules.filter test := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    cases h : test x <;> simp_all
  rw [← absorb l, agree, absorb r]

/-- At a projecting anchor, sibling rules affect neither the budget nor any
cell, hole, or claim. Invalid grant paths still fail the whole projection. -/
theorem projectKey_comparable {l r : List Rule} {key anchor d opts}
    (validL : l.all (pathOk ·.path) = true) (validR : r.all (pathOk ·.path) = true)
    (agree : l.filter (Rule.comparableAt key anchor) = r.filter (Rule.comparableAt key anchor)) :
    projectKey l key anchor d opts = projectKey r key anchor d opts := by
  have obstacles : l.filter (privateObstruction opts key anchor) =
      r.filter (privateObstruction opts key anchor) := by
    apply narrower_filters agree
    intro rule h
    simp only [privateObstruction, strictDescendant, Rule.comparableAt, Bool.and_eq_true,
      Bool.or_eq_true] at h ⊢
    rcases h with ⟨⟨hasKey, _⟩, ⟨below, _⟩ | ⟨_, above⟩⟩
    · exact ⟨hasKey, Or.inr below⟩
    · exact ⟨hasKey, Or.inl above⟩
  have blocked : l.any (privateObstruction opts key anchor) =
      r.any (privateObstruction opts key anchor) := by
    apply Bool.eq_iff_iff.mpr
    have eq := congrArg (fun xs : List Rule => ∃ r, r ∈ xs) obstacles
    simpa only [List.mem_filter, List.any_eq_true, eq_iff_iff] using eq
  have roots : bounds l key anchor d = bounds r key anchor d := by
    unfold bounds descendantIndex
    congr 3
    apply narrower_filters agree
    intro rule h
    simp only [Rule.comparableAt, strictDescendant, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    exact ⟨h.1.1, Or.inr h.1.2.1⟩
  have cells : partition l key (bounds l key anchor d) = partition r key (bounds l key anchor d) := by
    apply List.map_congr_left
    intro p member
    have below := bound_mem member
    have same : l.filter (applies key p) = r.filter (applies key p) := by
      apply narrower_filters agree
      intro rule h
      simp only [applies, Rule.comparableAt, Bool.and_eq_true, Bool.or_eq_true,
        List.isPrefixOf_iff_prefix] at h ⊢
      exact ⟨h.1, List.prefix_or_prefix_of_prefix h.2 below⟩
    simp only [same]
  simp only [projectKey, validL, validR, blocked, ← roots, cells]

/-- Whole-context equality at one anchor, including withheld keys and budgets. -/
theorem context_private_twins (l r : List Rule) (keys) (resources : Domain) (anchor profile options)
    (validL : l.all (resources.validSite ·.path) = true) (validR : r.all (resources.validSite ·.path) = true)
    (visibleRules : ∀ k d, (k, d) ∈ keys → (options k).nonprojecting = false →
      l.filter (Rule.comparableAt k anchor) = r.filter (Rule.comparableAt k anchor)) :
    projectContext l keys resources anchor profile options = projectContext r keys resources anchor profile options := by
  have paths {rules : List Rule} (v : rules.all (resources.validSite ·.path) = true) (k : String) :
      (rules.filter (·.keys.contains k)).all (pathOk ·.path) = true :=
    List.all_eq_true.mpr fun rule hr => (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp v rule (List.mem_filter.mp hr).1)).1
  have comparable (rules : List Rule) (k : String) :
      (rules.filter (·.keys.contains k)).filter (Rule.comparableAt k anchor) =
      rules.filter (Rule.comparableAt k anchor) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro rule _
    simp [Rule.comparableAt]
    exact fun h _ => h
  simp only [projectContext, validL, validR, Bool.not_true, Bool.or_false]
  split
  · rfl
  congr 1 <;> congr 1 <;> apply List.map_congr_left <;>
    rintro ⟨k, d⟩ hm <;> cases hn : (options k).nonprojecting
  all_goals first
    | exact private_twins _ _ _ _ _ _ rfl
    | apply projectKey_comparable (paths validL k) (paths validR k)
      simpa only [comparable] using visibleRules k d (List.mem_filter.mp hm).1 hn

/-- The private rule has no descendant boundary at an anchor that inherits it.
With no matching permit on that branch, every affected cell was already DENY. -/
theorem projectKey_inherited_forbid {rules : List Rule} {key anchor d opts site}
    (inherited : site <+: anchor) (legal : pathOk site)
    (absent : ∀ r ∈ rules, key ∈ r.keys → (r.path <+: anchor ∨ anchor <+: r.path) → r.effect ≠ .permit) :
    let block : Rule := {path := site, keys := [key], effect := .forbid, hidden := true}
    projectKey rules key anchor d opts = projectKey (rules ++ [block]) key anchor d opts := by
  intro block
  have strict : strictDescendant anchor site = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨below, different⟩ := Bool.and_eq_true_iff.mp h
    exact (bne_iff_ne.mp different) ((List.isPrefixOf_iff_prefix.mp below).eq_of_length_le inherited.length_le)
  have roots : bounds (rules ++ [block]) key anchor d = bounds rules key anchor d := by
    simp [bounds, descendantIndex, block, strict]
  have cells : partition (rules ++ [block]) key (bounds rules key anchor d) =
      partition rules key (bounds rules key anchor d) := by
    apply List.map_congr_left
    intro p atRoot
    have below := bound_mem atRoot
    have appliesBlock : applies key p block := by simp [applies, block, inherited.trans below]
    let app := rules.filter (applies key p)
    have no (r) (member : r ∈ app) : r.effect ≠ .permit := by
      obtain ⟨hr, keyAndPath⟩ := List.mem_filter.mp member
      obtain ⟨keyAt, path⟩ := Bool.and_eq_true_iff.mp keyAndPath
      exact absent r hr (List.contains_iff_mem.mp keyAt)
        (List.prefix_or_prefix_of_prefix (List.isPrefixOf_iff_prefix.mp path) below)
    have permits : app.any (·.effect == .permit) = false := List.any_eq_false.mpr fun r h => by simp [no r h]
    have sure : app.any Rule.surePermit = false := List.any_eq_false.mpr fun r h => by simp [Rule.surePermit, no r h]
    have base : classify app = .deny := by simp [classify, permits, sure]
    simp only [List.filter_append, List.filter_cons_of_pos appliesBlock, List.filter_nil]
    change Claim.mk key (classify (app ++ [block])) _ _ = Claim.mk key (classify app) _ _
    simp [classify, block, Rule.finalForbid, permits, sure]
  have unblocked : privateObstruction opts key anchor block = false := by simp [privateObstruction, block, strict]
  simp [projectKey, roots, cells, unblocked, block, legal]

/-- The declaration withholds the key above the private scope. On an
eligible branch the scope is disjoint, or its ancestors and descendants
carry no permit for this key. Other keys and their budgets are unrestricted. -/
theorem context_forbid_absent (rules : List Rule) (keys) (resources : Domain) (anchor profile)
    (options : String → ProjectOptions) (key site)
    (valid : rules.all (resources.validSite ·.path) = true) (legal : resources.validSite site)
    (boundary : (options key).nonprojecting = true ∨
      (¬site <+: anchor ∧ ¬anchor <+: site) ∨
      (site <+: anchor ∧ ∀ r ∈ rules, key ∈ r.keys →
        (r.path <+: anchor ∨ anchor <+: r.path) → r.effect ≠ .permit)) :
    let block : Rule := {path := site, keys := [key], effect := .forbid, hidden := true}
    projectContext rules keys resources anchor profile options =
      projectContext (rules ++ [block]) keys resources anchor profile options := by
  intro block
  have allPaths : rules.all (pathOk ·.path) = true := by
    apply List.all_eq_true.mpr
    intro r hr
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid r hr)).1
  have legalPath : pathOk site := (Bool.and_eq_true_iff.mp legal).1
  have same (k dom) :
      projectKey (rules.filter (·.keys.contains k)) k anchor dom {options k with profile} =
      projectKey ((rules ++ [block]).filter (·.keys.contains k)) k anchor dom {options k with profile} := by
    by_cases eq : k = key
    · subst k
      simp only [List.filter_append]
      have classified : [block].filter (·.keys.contains key) = [block] := by simp [block]
      rw [classified]
      rcases boundary with withheld | away | ⟨inherited, absent⟩
      · exact private_twins _ _ _ _ _ _ withheld
      · apply projectKey_comparable
        · exact List.all_eq_true.mpr fun r hr => List.all_eq_true.mp allPaths r (List.mem_filter.mp hr).1
        · simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true]
          exact Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr (fun r hr =>
            List.all_eq_true.mp allPaths r (List.mem_filter.mp hr).1), legalPath⟩
        · simp [block, Rule.comparableAt, away.1, away.2]
      · apply projectKey_inherited_forbid inherited legalPath
        exact fun r hr => absent r (List.mem_filter.mp hr).1
    · simp [List.filter_append, block, eq]
  simp only [projectContext, List.all_append, List.all_cons, List.all_nil, valid,
    show resources.validSite block.path = true from legal, Bool.and_self]
  split
  · rfl
  congr 1 <;> congr 1 <;> apply List.map_congr_left <;> rintro ⟨k,dom⟩ _ <;> exact same k dom

end Authz
