import Authz.Domain

namespace Authz

/-- Check a tagged scope against the service catalog, including implicit resource
parents. A collection stays distinct from both the service root and a resource. -/
def Scope.valid (domain : Domain) : Scope → Bool
  | .serviceRoot => true
  | .resource p => pathOk p && domain.isResource p
  | .collection p => pathOk p && !p.isEmpty && !domain.isResource p &&
      domain.any (Pattern.reach · p)

def Descriptor.reachableDomains (d : Descriptor) (p : Path) : List (String × Domain) :=
  (d.trie.reachable p).eraseDups.map (fun k => (k, d.domain k))

private theorem reach_cons (a : Atom) (p : Pattern) (x : String) (xs : Path) :
    Pattern.reach (a :: p) (x :: xs) = (a.accepts x && Pattern.reach p xs) := by
  cases h : a.accepts x <;> simp [Pattern.reach, Pattern.consume, h]

theorem Pattern.reach_shape (p : Pattern) (x : Path) : (Pattern.shape p).reach x = Pattern.reach p x := by
  induction p generalizing x with
  | nil => rfl
  | cons a p ih =>
    cases x with
    | nil => cases a <;> rfl
    | cons v x =>
      cases a <;> simp [Pattern.shape, reach_cons, Atom.accepts] at ih ⊢ <;> exact congrArg (_ && ·) (ih x)

/-- Each insertion contributes its key exactly at prefixes that can reach the
inserted pattern. A matching literal edge never masks a variable sibling. -/
theorem PatternTrie.reachable_insert (t : PatternTrie) (p : Pattern)
    (k query : String) (xs : Path) :
    query ∈ (t.insert k p).reachable xs ↔
      (query = k ∧ Pattern.reach p xs = true) ∨ query ∈ t.reachable xs := by
  fun_induction PatternTrie.insert k p t generalizing xs with
  | case1 =>
    cases xs <;> simp [PatternTrie.reachable, Pattern.reach, Pattern.consume]
  | case2 a p ih =>
    cases xs with
    | nil => simp [PatternTrie.reachable, ih, Pattern.reach, Pattern.consume]
    | cons x xs => cases h : a.accepts x <;> simp [PatternTrie.reachable, ih, reach_cons, h]
  | case3 p k' more hp =>
    have he : p = [] ∧ k = k' := by simpa using hp
    obtain ⟨rfl, rfl⟩ := he
    cases xs <;> simp [PatternTrie.reachable, Pattern.reach, Pattern.consume]
  | case4 p k' more _ ih =>
    simp [PatternTrie.reachable, ih]
    grind
  | case5 a child more =>
    cases xs <;> simp [PatternTrie.reachable, Pattern.reach, Pattern.consume]
  | case6 a child more b p eq ih =>
    have h : b = a := by simpa using eq
    subst b
    cases xs with
    | nil => simp [PatternTrie.reachable, ih, Pattern.reach, Pattern.consume]; grind
    | cons x xs => cases h : a.accepts x <;> simp [PatternTrie.reachable, ih, reach_cons, h]; grind
  | case7 a child more b p ne ih =>
    cases xs with
    | nil => simp [PatternTrie.reachable, ih]; grind
    | cons x xs => cases h : a.accepts x <;> simp [PatternTrie.reachable, ih, reach_cons, h]; grind

private theorem insertPatterns_reaches (ps : Domain) (k query : String) (path : Path) (base : PatternTrie) :
    query ∈ (ps.foldl (fun t p => t.insert k (Pattern.shape p)) base).reachable path ↔
      (∃ p ∈ ps, query = k ∧ Pattern.reach (Pattern.shape p) path = true) ∨ query ∈ base.reachable path := by
  induction ps generalizing base with
  | nil => simp
  | cons p ps ih => simp only [List.foldl_cons, ih, PatternTrie.reachable_insert, List.mem_cons]; grind

private theorem insertRequirements_reach (ds : List Requirement) (query : String)
    (path : Path) (base : PatternTrie) :
    query ∈ (ds.foldl (fun t r => r.patterns.foldl (fun tr p => tr.insert r.key (Pattern.shape p)) t)
      base).reachable path ↔
      (∃ r ∈ ds, ∃ p ∈ r.patterns, query = r.key ∧ Pattern.reach (Pattern.shape p) path = true) ∨
        query ∈ base.reachable path := by
  induction ds generalizing base with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons, ih, insertPatterns_reaches, List.mem_cons]
    grind

theorem Descriptor.trie_reaches_iff (d : Descriptor) (key : String) (path : Path) :
    key ∈ d.trie.reachable path ↔ ∃ p ∈ d.domain key, Pattern.reach p path = true := by
  simp only [Descriptor.trie, insertRequirements_reach, PatternTrie.reachable, List.not_mem_nil,
    or_false, Descriptor.domain, Descriptor.namedDomain, List.mem_eraseDups, List.mem_map, List.mem_flatMap, List.mem_filter,
    beq_iff_eq]
  constructor
  · rintro ⟨r, hr, p, hp, rfl, reach⟩
    exact ⟨_, ⟨p, ⟨r, ⟨hr, rfl⟩, hp⟩, rfl⟩, reach⟩
  · rintro ⟨_, ⟨p, ⟨r, ⟨hr, rfl⟩, hp⟩, rfl⟩, reach⟩
    exact ⟨r, hr, p, hp, rfl, reach⟩

end Authz
