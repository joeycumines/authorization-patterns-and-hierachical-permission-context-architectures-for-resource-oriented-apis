import Authz.Descriptor

namespace Authz

abbrev Effect := GrantEffect

inductive Kind where
  | allow | deny | conditional
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

inductive Decision where
  | allow | deny
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

inductive Authority where
  | failClosed | skipErrors
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

inductive Profile where
  | scopedClaims | grantShaped
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure Rule where
  path : Path
  keys : List String
  effect : Effect
  pred : Option String := none
  hidden : Bool := false
  mayError : Bool := false
  final : Bool := true
  /-- Position of the originating grant in this policy snapshot. -/
  sourceIndex : Option Nat := none
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

/-- A compiled grant has one fault outcome at a target even when its expanded
permission keys change. Standalone rules retain their supplied identity. -/
def Rule.faultIdentity (r : Rule) : Rule := if r.sourceIndex.isSome then { r with keys := [] } else r

structure Claim where
  key : String
  kind : Kind
  path : Path
  holes : List Path := []
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

def Claim.covers (c : Claim) (t : Path) :=
  c.path.isPrefixOf t && !c.holes.any (·.isPrefixOf t)

/-- A fault observation of `some false` records a successful evaluation,
`some true` records a fault and `none` means the outcome is unknown. -/
structure Facts where
  predicate : String → Option Bool := fun _ => none
  faults : Rule → Option Bool := fun _ => none

inductive Evaluation where
  | none | permit | forbid | unresolved | error
  deriving DecidableEq, Repr

def Rule.evaluate (r : Rule) (facts : Facts) : Evaluation :=
  match (if r.mayError then facts.faults r.faultIdentity else some false) with
  | none => .unresolved
  | some true => .error
  | some false =>
    match r.pred.elim (some true) facts.predicate with
    | none => .unresolved
    | some false => .none
    | some true => match r.effect with
      | .permit => .permit
      | .forbid => .forbid

def Rule.blocks (r : Rule) (mode : Authority) (facts : Facts) : Bool :=
  r.effect == .forbid && match r.evaluate facts with
    | .forbid | .unresolved => true
    | .error => mode == .failClosed
    | _ => false

def Rule.grants (r : Rule) (facts : Facts) : Bool :=
  r.evaluate facts == .permit

def applies (key : String) (t : Path) (r : Rule) :=
  r.keys.contains key && r.path.isPrefixOf t

def decideApplied (mode : Authority) (facts : Facts) (rules : List Rule) : Decision :=
  if rules.any (·.blocks mode facts) then .deny
  else if rules.any (·.grants facts) then .allow else .deny

def decide (mode : Authority) (facts : Facts) (rules : List Rule) (key : String) (t : Path) : Decision :=
  if !pathOk t || !rules.all (pathOk ·.path) then .deny
  else decideApplied mode facts (rules.filter (applies key t))

theorem blocking_rule_denies {r rules key t mode facts}
    (member : r ∈ rules) (matched : applies key t r = true) (block : r.blocks mode facts = true) :
    decide mode facts rules key t = .deny := by
  have anyBlock : (rules.filter (applies key t)).any (·.blocks mode facts) :=
    List.any_eq_true.mpr ⟨r, List.mem_filter.mpr ⟨member, matched⟩, block⟩
  simp [decide, decideApplied, anyBlock]

/-- A completion retains all observed values and may fill gaps in the adapter's evidence. -/
structure Facts.Extends (full partialFacts : Facts) : Prop where
  predicates : ∀ k b, partialFacts.predicate k = some b → full.predicate k = some b
  faults : ∀ r b, partialFacts.faults r = some b → full.faults r = some b

private theorem Rule.resolved_stable (r : Rule) (more : full.Extends partialFacts)
    (known : r.evaluate partialFacts ≠ .unresolved) : r.evaluate full = r.evaluate partialFacts := by
  unfold Rule.evaluate at *
  have pred : ∀ b, r.pred.elim (some true) partialFacts.predicate = some b →
      r.pred.elim (some true) full.predicate = some b := by
    cases h : r.pred <;> simp only [Option.elim_none, Option.elim_some]
    · exact fun _ h => h
    · exact more.predicates _
  cases may : r.mayError <;> simp [may] at known ⊢
  · cases h : r.pred.elim (some true) partialFacts.predicate with
    | none => simp [h] at known
    | some b => rw [pred b h]
  · cases e : partialFacts.faults r.faultIdentity with
    | none => simp [e] at known
    | some b =>
      rw [more.faults r.faultIdentity b e]
      cases b
      · cases h : r.pred.elim (some true) partialFacts.predicate with
        | none => simp [e, h] at known
        | some b => rw [pred b h]
      · rfl

/-- An immediate allow under partial facts remains valid for every completion
that preserves the fault and predicate results already observed. -/
theorem decide_allow_of_more_facts (more : full.Extends partialFacts)
    (allow : decide mode partialFacts rules k t = .allow) : decide mode full rules k t = .allow := by
  unfold decide at allow ⊢
  split at allow
  · contradiction
  · rename_i valid
    simp only [valid]
    unfold decideApplied at allow ⊢
    split at allow <;> try contradiction
    rename_i clean
    split at allow <;> try contradiction
    rename_i grant
    have noBlock : (rules.filter (applies k t)).any (·.blocks mode full) = false := by
      apply List.any_eq_false.mpr
      intro r hr
      have no := List.any_eq_false.mp (Bool.eq_false_iff.mpr clean) r hr
      by_cases pending : r.evaluate partialFacts = .unresolved
      · cases eff : r.effect <;> simp_all [Rule.blocks]
      · simpa [Rule.blocks, r.resolved_stable more pending] using no
    obtain ⟨r, hr, yes⟩ := List.any_eq_true.mp grant
    have stable := r.resolved_stable more (by intro h; simp [Rule.grants, h] at yes)
    have grants : (rules.filter (applies k t)).any (·.grants full) :=
      List.any_eq_true.mpr ⟨r, hr, by simpa [Rule.grants, stable] using yes⟩
    simp [noBlock, grants]

/-- Either authority withholds a possibly failing permit and enforces a possibly
failing forbid until the adapter supplies the rule's fault outcome. -/
theorem Rule.unknown_fault_fails_closed {r : Rule} {facts : Facts} (mode : Authority)
    (possible : r.mayError = true) (unknown : facts.faults r.faultIdentity = none) :
    r.grants facts = false ∧ r.blocks mode facts = (r.effect == .forbid) := by
  simp [Rule.grants, Rule.blocks, Rule.evaluate, possible, unknown]

def Rule.surePermit (r : Rule) :=
  r.effect == .permit && r.pred.isNone && !r.mayError

def Rule.finalForbid (r : Rule) :=
  r.effect == .forbid && r.pred.isNone && !r.mayError && r.final

/-- Steps 1–4 of §3.6. The input contains exactly the rules inherited by the cell. -/
def classify (rules : List Rule) : Kind :=
  if rules.any Rule.finalForbid then .deny
  else if !rules.any (·.effect == .forbid) && rules.any Rule.surePermit then .allow
  else if !rules.any (·.effect == .permit) then .deny
  else .conditional

private theorem sure_permit_grants {r : Rule} (facts : Facts)
    (h : r.surePermit = true) : r.grants facts = true := by
  obtain ⟨_, _, effect, pred, _, err, fin⟩ := r
  cases effect <;> cases pred <;> cases err <;>
    simp_all [Rule.surePermit, Rule.grants, Rule.evaluate]

private theorem final_forbid_blocks {r : Rule} (mode : Authority) (facts : Facts)
    (h : r.finalForbid = true) : r.blocks mode facts = true := by
  obtain ⟨_, _, effect, pred, _, err, fin⟩ := r
  cases effect <;> cases pred <;> cases err <;>
    simp_all [Rule.finalForbid, Rule.blocks, Rule.evaluate]

theorem Rule.effect_of_grants {r : Rule} {facts : Facts} (h : r.grants facts = true) :
    r.effect = .permit := by
  unfold Rule.grants Rule.evaluate at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases he : r.effect <;> simp_all

/-- Filtering permits at the queried key preserves the original rules and
their fault outcomes. This applies to conditional rules under both authorities. -/
theorem decide_permit_ceiling (c : Ceiling) (r : Requirement) (rules : List Rule)
    (mode : Authority) (facts : Facts) (x : Path) :
    (decide mode facts (rules.filter (fun g => g.effect == .forbid || c.permits r.info)) r.key x == .allow) =
      (c.permits r.info && (decide mode facts rules r.key x == .allow)) := by
  cases c.permits r.info with
  | true =>
    have keep : rules.filter (fun _ => true) = rules := List.filter_eq_self.mpr (by simp)
    simp [keep]
  | false =>
    simp only [Bool.or_false, Bool.false_and, decide]
    split
    · rfl
    · let remaining := (rules.filter (fun g => g.effect == .forbid)).filter (applies r.key x)
      have none : remaining.any (·.grants facts) = false := by
        apply List.any_eq_false.mpr
        intro g hg allowed
        have forbids := (List.mem_filter.mp (List.mem_filter.mp hg).1).2
        simp [Rule.effect_of_grants allowed] at forbids
      change (decideApplied mode facts remaining == .allow) = false
      unfold decideApplied
      rw [none]
      split <;> rfl

theorem classified_allow (rules : List Rule) (mode : Authority) (facts : Facts)
    (h : classify rules = .allow) : decideApplied mode facts rules = .allow := by
  unfold classify at h
  split at h <;> try contradiction
  split at h
  next hallow =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at hallow
    obtain ⟨noForbid, r, hr, hs⟩ := hallow
    have hb : rules.any (·.blocks mode facts) = false := by
      apply List.any_eq_false.mpr
      intro x hx
      have := List.any_eq_false.mp noForbid x hx
      simp_all [Rule.blocks]
    have hg : rules.any (·.grants facts) := List.any_eq_true.mpr ⟨r, hr, sure_permit_grants facts hs⟩
    simp [decideApplied, hb, hg]
  next => split at h <;> contradiction

theorem classified_deny (rules : List Rule) (mode : Authority) (facts : Facts)
    (h : classify rules = .deny) : decideApplied mode facts rules = .deny := by
  unfold classify at h
  split at h
  next hfinal =>
    obtain ⟨r, hr, hf⟩ := List.any_eq_true.mp hfinal
    have hb : rules.any (·.blocks mode facts) = true := List.any_eq_true.mpr ⟨r, hr, final_forbid_blocks mode facts hf⟩
    simp [decideApplied, hb]
  next =>
    split at h <;> try contradiction
    split at h <;> try contradiction
    next hn =>
      simp only [Bool.not_eq_true'] at hn
      have hg : rules.any (·.grants facts) = false := by
        apply List.any_eq_false.mpr
        intro r hr
        intro hp
        have := List.any_eq_false.mp hn r hr
        simp_all [Rule.effect_of_grants hp]
      simp [decideApplied, hg]

end Authz
