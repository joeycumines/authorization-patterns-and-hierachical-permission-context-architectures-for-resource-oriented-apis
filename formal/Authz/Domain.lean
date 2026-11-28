import Authz.Descriptor

namespace Authz

/-- JavaScript orders wire strings by UTF-16 code units. Supplementary
characters compare by their surrogate pair. -/
def utf16Units (value : String) : List Nat :=
  value.toList.flatMap fun c =>
    let n := c.toNat
    if n < 0x10000 then [n] else
      let offset := n - 0x10000
      [0xd800 + offset / 0x400, 0xdc00 + offset % 0x400]

/-- A matching endpoint includes singletons. A matching interior ID names its
resource even when the parent type has no declaration of its own. -/
def Domain.isResource (d : Domain) (p : Path) : Bool :=
  !p.isEmpty && d.any fun pat => Pattern.reach pat p &&
    (pat.length == p.length || (pat[p.length - 1]?).any fun a => match a with
      | .var _ => true | _ => false)

theorem Domain.contains_pathOk {d : Domain} {x : Path} (hit : Domain.contains d x = true) :
    pathOk x = true := by
  obtain ⟨p, mem, hm⟩ := List.any_eq_true.mp hit
  clear hit mem
  unfold pathOk
  induction x generalizing p with
  | nil => rfl
  | cons a x ih =>
    cases p with
    | nil => simp [Pattern.matches] at hm
    | cons b p =>
      simp [Pattern.matches] at hm
      simp only [List.all_cons, (Bool.and_eq_true_iff.mp hm.1).1, ih p hm.2, Bool.and_self]

def Domain.validSite (domain : Domain) (site : Path) : Bool :=
  pathOk site && (site.isEmpty || domain.isResource site)

/-- Deployment name modes use every declared path of the named type. An unknown
type cannot silently enable an unrestricted policy. -/
def asWrittenDomain? (catalog : List ResourceDecl) (types : List String) : Option Domain := do
  let domains ← types.mapM fun t => do
    let patterns := (catalog.filter (·.resourceType == t)).flatMap ResourceDecl.patterns
    guard (fullTypeOk t && !patterns.isEmpty && patterns.all (fun p => p.all Atom.valid))
    return patterns
  return domains.flatten

/-- Construct a valid ID longer than every segment in a finite exclusion list. -/
def freshId (used : List String) : String :=
  String.ofList ('a' :: List.replicate ((used.map String.length).sum) 'a')

theorem freshId_valid (used : List String) : segmentOk (freshId used) = true := by
  simp [segmentOk, String.isEmpty_eq_false_iff, freshId, ← String.toList_inj,
    show "".toList = [] from rfl, show ".".toList = ['.'] from rfl,
    show "..".toList = ['.', '.'] from rfl, show "-".toList = ['-'] from rfl]

theorem freshId_fresh {s : String} (hs : s ∈ used) : freshId used ≠ s := by
  have bound : s.length ≤ (used.map String.length).sum := by
    induction used with
    | nil => simp_all
    | cons hd tl ih =>
      simp only [List.mem_cons] at hs
      simp only [List.map_cons, List.sum_cons]
      rcases hs with rfl | hm
      · omega
      · have := ih hm; omega
  intro eq
  have := congrArg String.length eq
  simp only [freshId, String.length_ofList, List.length_cons, List.length_replicate] at this
  omega

private theorem Pattern.consume_valid (v : p.all Atom.valid = true)
    (h : Pattern.consume p xs = some rest) : rest.all Atom.valid = true := by
  induction xs generalizing p with
  | nil => simp_all [Pattern.consume]
  | cons x xs ih =>
    cases p with
    | nil => simp [Pattern.consume] at h
    | cons a p =>
      by_cases ha : a.accepts x <;> simp_all [Pattern.consume]
      exact ih v.2 h

private def Pattern.fill (fresh : String) : Pattern → Path
  | [] => []
  | .var _ :: rest => fresh :: Pattern.fill fresh rest
  | .lit s :: rest => s :: Pattern.fill fresh rest

private theorem Pattern.matches_fill (v : p.all Atom.valid = true)
    (hf : segmentOk fresh = true) : Pattern.matches p (Pattern.fill fresh p) = true := by
  induction p with
  | nil => rfl
  | cons a p ih => cases a <;> simp_all [Pattern.fill, Pattern.matches, Atom.valid, Atom.accepts]

theorem Pattern.literals_prefix {x : Path} (hm : Pattern.matches p x = true) :
    Pattern.literals p <+: x := by
  induction p generalizing x with
  | nil => simp [Pattern.literals]
  | cons a p ih =>
    cases a with
    | var => simp [Pattern.literals]
    | lit s =>
      cases x with
      | nil => simp [Pattern.matches] at hm
      | cons y ys => simp_all [Pattern.literals, Pattern.matches, Atom.accepts]

private theorem Pattern.fill_remainder (p : Pattern) (fresh : String) :
    Pattern.fill fresh p = Pattern.literals p ∨
      ∃ tail, Pattern.fill fresh p = Pattern.literals p ++ fresh :: tail := by
  induction p with
  | nil => exact Or.inl rfl
  | cons a p ih =>
    cases a with
    | var => exact Or.inr ⟨_, rfl⟩
    | lit s =>
      rcases ih with h | ⟨tail, h⟩
      · exact Or.inl (by simp [Pattern.fill, Pattern.literals, h])
      · exact Or.inr ⟨tail, by simp [Pattern.fill, Pattern.literals, h]⟩

private theorem prefix_before_fresh {fixed hole tail : Path} {fresh : String}
    (h : hole <+: fixed ++ fresh :: tail) (hf : fresh ∉ hole) : hole <+: fixed := by
  induction fixed generalizing hole with
  | nil =>
    cases hole with
    | nil => simp
    | cons x xs => simp_all
  | cons s ss ih =>
    cases hole with
    | nil => simp
    | cons x xs => simp_all

/-- Proof of the unbounded-domain test in the JS function domainNonEmpty. The
fresh ID evades all deeper holes at once, regardless of their number or depth. -/
theorem Domain.nonemptyRegion_iff {d : Domain} {anchor : Path} {holes : List Path}
    (valid : ∀ p ∈ d, p.all Atom.valid = true) :
    Domain.nonemptyRegion d anchor holes = true ↔
      ∃ x, Domain.contains d x = true ∧ anchor <+: x ∧ ∀ h ∈ holes, ¬h <+: x := by
  simp only [Domain.nonemptyRegion, Domain.contains, List.any_eq_true]
  constructor
  · rintro ⟨p, hp, test⟩
    cases consumed : Pattern.consume p anchor with
    | none => simp [Pattern.fixedPrefix, consumed] at test
    | some rest =>
      simp [Pattern.fixedPrefix, consumed, List.any_eq_false, List.isPrefixOf_iff_prefix] at test
      let id := freshId holes.flatten
      let x := anchor ++ Pattern.fill id rest
      refine ⟨x, ⟨p, hp, (Pattern.consume_matches _ _).1 ?_⟩, List.prefix_append .., ?_⟩
      · rw [Pattern.consume_append, consumed, Option.bind_some]
        exact (Pattern.consume_matches _ _).2
          (Pattern.matches_fill (Pattern.consume_valid (valid _ hp) consumed) (freshId_valid _))
      · intro hole hh covers
        apply test hole hh
        rcases Pattern.fill_remainder rest id with heq | ⟨tail, heq⟩
        · simpa [x, heq] using covers
        · apply prefix_before_fresh (tail := tail) (fresh := id)
          · simpa [x, heq, List.append_assoc] using covers
          · intro hmem
            exact freshId_fresh (List.mem_flatten.2 ⟨hole, hh, hmem⟩) rfl
  · rintro ⟨x, ⟨p, hp, hm⟩, ⟨tail, rfl⟩, hx⟩
    refine ⟨p, hp, ?_⟩
    have h := (Pattern.consume_matches _ _).2 hm
    rw [Pattern.consume_append] at h
    cases consumed : Pattern.consume p anchor with
    | none => simp [consumed] at h
    | some rest =>
      have matchTail : Pattern.matches rest tail = true :=
        (Pattern.consume_matches _ _).1 (by simpa [consumed] using h)
      simp [Pattern.fixedPrefix, consumed, List.any_eq_false, List.isPrefixOf_iff_prefix]
      intro hole hh hprefix
      exact hx _ hh (hprefix.trans ((List.prefix_append_right_inj _).2
        (Pattern.literals_prefix matchTail)))

end Authz
