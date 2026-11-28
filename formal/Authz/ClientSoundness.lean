import Authz.ClientSafety
import Authz.Projection
import Authz.Server
import Authz.WireScalars

namespace Authz

def matchesQuery : Path → Path → Bool
  | [], [] => true
  | q :: qs, x :: xs => (q == "-" || q == x) && matchesQuery qs xs
  | _, _ => false

private theorem accepted_valid {a : Atom} {s : String} (ok : a.accepts s = true) : segmentOk s = true := by
  simp only [Atom.accepts, Bool.and_eq_true] at ok
  exact ok.1

theorem restricted_matches (p : Pattern) (q x : Path) :
    (Pattern.restrictTarget p q).any (Pattern.matches · x) =
      (Pattern.matches p x && matchesQuery q x) := by
  induction p generalizing q x with
  | nil => cases q <;> cases x <;> rfl
  | cons a p ih =>
    cases q with
    | nil => cases x <;> simp [Pattern.restrictTarget, Pattern.matches, matchesQuery]
    | cons b bs =>
      cases hr : Pattern.restrictTarget p bs with
      | none =>
        cases x with
        | nil => simp [Pattern.restrictTarget, hr, Pattern.matches]
        | cons y ys =>
          have tail := ih bs ys
          simp [hr] at tail
          simp [Pattern.restrictTarget, hr, Pattern.matches, matchesQuery]
          grind
      | some tail =>
        cases x with
        | nil =>
          by_cases b = "-" <;> by_cases a.accepts b <;>
            simp_all [Pattern.restrictTarget, Pattern.matches]
        | cons y ys =>
          have eq := ih bs ys
          simp [hr] at eq
          by_cases wild : b = "-"
          · simp [Pattern.restrictTarget, hr, wild, Pattern.matches, matchesQuery, eq, Bool.and_assoc]
          · by_cases same : b = y
            · subst y
              by_cases ok : a.accepts b = true
              · have ordinary : (b == "-") = false := beq_eq_false_iff_ne.mpr wild
                have accepted : (Atom.lit b).accepts b = true := by simp [Atom.accepts, accepted_valid ok]
                simp [Pattern.restrictTarget, hr, ordinary, ok, Pattern.matches, matchesQuery, eq, accepted]
              · have bad : a.accepts b = false := Bool.eq_false_iff.mpr ok
                simp [Pattern.restrictTarget, hr, wild, bad, Pattern.matches]
            · have neq : (b == y) = false := beq_eq_false_iff_ne.mpr same
              have rev : (y == b) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
              have ordinary : (b == "-") = false := beq_eq_false_iff_ne.mpr wild
              have rejected : (Atom.lit b).accepts y = false := by simp [Atom.accepts, rev]
              cases ok : a.accepts b <;>
                simp [Pattern.restrictTarget, hr, ordinary, ok, Pattern.matches, matchesQuery, neq, rejected]

theorem candidate_matches (d : Domain) (q x : Path) :
    Domain.contains (candidates d q) x = true ↔ Domain.contains d x = true ∧ matchesQuery q x = true := by
  simp only [Domain.contains, candidates, List.any_eq_true, List.mem_filterMap]
  constructor
  · rintro ⟨j, ⟨p, hp, hh⟩, hm⟩
    have eq := restricted_matches p q x
    simp [hh, hm] at eq
    exact ⟨⟨_, hp, eq.1⟩, eq.2⟩
  · rintro ⟨⟨p, hp, hm⟩, hq⟩
    have eq := restricted_matches p q x
    rw [hm, hq] at eq
    cases hh : Pattern.restrictTarget p q with
    | none => simp [hh] at eq
    | some j => exact ⟨j, ⟨_, hp, hh⟩, by simpa [hh] using eq⟩

theorem restricted_valid (p : Pattern) (q r) (v : p.all Atom.valid = true)
    (h : Pattern.restrictTarget p q = some r) : r.all Atom.valid = true := by
  induction p generalizing q r with
  | nil => cases q <;> simp_all [Pattern.restrictTarget]
  | cons a p ih =>
    cases q with
    | nil => simp [Pattern.restrictTarget] at h
    | cons x xs =>
      cases hr : Pattern.restrictTarget p xs with
      | none => simp [Pattern.restrictTarget, hr] at h
      | some rest =>
        simp only [List.all_cons, Bool.and_eq_true] at v
        have hv := ih xs rest v.2 hr
        by_cases wild : x = "-"
        · simp [Pattern.restrictTarget, hr, wild] at h
          subst r
          simp [v, hv]
        · by_cases ok : a.accepts x
          · simp [Pattern.restrictTarget, hr, wild, ok] at h
            subst r
            have good := accepted_valid ok
            simp [Atom.valid, good, hv]
          · simp [Pattern.restrictTarget, hr, wild, ok] at h

theorem candidates_valid (valid : ∀ p ∈ d, p.all Atom.valid = true) (q : Path) :
    ∀ r ∈ candidates d q, r.all Atom.valid = true := by
  intro r hr
  obtain ⟨p, hp, h⟩ := List.mem_filterMap.mp hr
  exact restricted_valid p q r (valid p hp) h

private theorem query_prefix {q x : Path} (m : matchesQuery q x = true) :
    q.takeWhile (· != "-") <+: x := by
  induction q generalizing x with
  | nil => simp
  | cons a q ih =>
    cases x with
    | nil => simp [matchesQuery] at m
    | cons b x =>
      by_cases wild : a = "-"
      · simp [wild]
      · simp [matchesQuery, wild] at m
        obtain ⟨rfl, tail⟩ := m
        simp [wild, ih tail]

theorem covers_all_candidates {d q c x} (valid : ∀ p ∈ d, p.all Atom.valid = true)
    (cover : coversTarget q (candidates d q) c = true)
    (inDomain : Domain.contains d x = true) (target : matchesQuery q x = true) :
    c.covers x = true := by
  simp [coversTarget, List.isPrefixOf_iff_prefix, List.any_eq_false] at cover
  simp [Claim.covers, List.isPrefixOf_iff_prefix, cover.1.trans (query_prefix target), List.any_eq_false]
  intro h hh pre
  have miss := cover.2 _ hh
  have hit : Domain.nonemptyRegion (candidates d q) h [] = true := (Domain.nonemptyRegion_iff (candidates_valid valid q)).2
    ⟨x, (candidate_matches d q x).2 ⟨inDomain, target⟩, pre, by simp⟩
  simp_all

theorem deny_has_candidate {d q} {c : Claim} (valid : ∀ p ∈ d, p.all Atom.valid = true)
    (hit : Domain.nonemptyRegion (candidates d q) c.path c.holes = true) :
    ∃ x, Domain.contains d x = true ∧ matchesQuery q x = true ∧ c.covers x = true := by
  obtain ⟨x, hc, hp, holes⟩ := (Domain.nonemptyRegion_iff (candidates_valid valid q)).1 hit
  obtain ⟨hd, hq⟩ := (candidate_matches d q x).1 hc
  exact ⟨x, hd, hq, by simp [Claim.covers, List.isPrefixOf_iff_prefix, hp, List.any_eq_false]; exact holes⟩

/-- A revision token is opaque and may be shared across callers and services.
Its policy belongs to the full snapshot identity from §3.8. -/
structure PolicyIdentity where
  service : String
  subject : String
  token : String
  deriving DecidableEq, Repr

abbrev PolicyHistory := PolicyIdentity → List Rule

def SnapshotReply.identity (r : SnapshotReply) : PolicyIdentity := ⟨r.service, r.subject, r.token⟩

def ClientState.policyAt (s : ClientState) (policy : PolicyHistory) (token : String) :=
  s.subject.elim [] (fun subject => policy ⟨s.service, subject, token⟩)

/-- Packing sorts holes; the transmitted claim has the same kind and covers
exactly the same names as its originating projection cell. -/
def ProjectedClaim (rules : List Rule) (key : String) (anchor : Path) (d : Domain)
    (opts : ProjectOptions) (c : Claim) : Prop :=
  ∃ source ∈ regionClaims rules key anchor d opts, source.kind = c.kind ∧
    ∀ x, source.covers x = c.covers x

private theorem transported_decision {rules key anchor d opts c t}
    (source : ProjectedClaim rules key anchor d opts c) (hit : c.covers t)
    (domain : Domain.contains d t) (valid : pathOk t) (mode : Authority) (facts : Facts) :
    (c.kind = .allow → decide mode facts rules key t = .allow) ∧
    (c.kind = .deny → decide mode facts rules key t = .deny) := by
  obtain ⟨original, projected, kind, same⟩ := source
  simpa [kind] using projected_decision projected ((same t).symm ▸ hit) domain valid mode facts

/-- Every claim comes from the projector at the stated snapshot. -/
def FromProjector (policy : PolicyHistory) (keys : KeyDomains) (r : SnapshotReply) :=
  ∀ ctx ∈ r.contexts, ∀ c ∈ ctx.claims, ∀ d, keys.lookup c.key = some d →
    ∃ opts, ProjectedClaim (policy r.identity) c.key ctx.anchor d opts c

def ProducedState (policy : PolicyHistory) (keys : KeyDomains) (s : ClientState) :=
  ∀ f ∈ s.history, f.reply.service = s.service ∧ s.subject = some f.reply.subject ∧
    FromProjector policy keys f.reply

private theorem live_origin {s keys key hits d now maximum token c} {policy : PolicyHistory}
    (produced : ProducedState policy keys s) (known : keys.lookup key = some d)
    (hc : c ∈ claimsForKey key ((latestMatching s.history keys hits token).filter (TimedContext.usable now maximum))) :
    ∃ anchor opts, ProjectedClaim (s.policyAt policy token) key anchor d opts c := by
  obtain ⟨contexts, isKey⟩ := List.mem_filter.mp hc
  obtain ⟨timed, timedMem, claimMem⟩ := List.mem_flatMap.mp contexts
  obtain ⟨f, hf, received⟩ := List.mem_flatMap.mp (dedup_subset (List.mem_filter.mp timedMem).1)
  split at received <;> try contradiction
  next belongs =>
    obtain ⟨ctx, ctxMem, eq⟩ := List.mem_map.mp received
    subst timed
    have actual : ctx ∈ f.reply.contexts := (List.mem_filter.mp ctxMem).1
    simp only [beq_iff_eq] at belongs isKey
    obtain ⟨service, subject, origin⟩ := produced f hf
    obtain ⟨opts, h⟩ := origin ctx actual c claimMem d (isKey ▸ known)
    exact ⟨_, opts, by simpa [ClientState.policyAt, SnapshotReply.identity, subject, service, belongs, isKey] using h⟩

private theorem pathOk_of_domain {d : Domain} {x : Path} (hit : Domain.contains d x = true) :
    pathOk x = true := Domain.contains_pathOk hit

/-- A definitive verdict implies the decision at its snapshot for every
candidate of an ALLOW or at least one candidate of a universal wildcard DENY. -/
theorem evaluated_projection_sound {s keys key q now d} (policy : PolicyHistory)
    (produced : ProducedState policy keys s) (known : keys.lookup key = some d)
    (valid : ∀ p ∈ d, p.all Atom.valid = true) (mode : Authority) (facts : Path → Facts) (maximum : Option Profile := some .scopedClaims) :
    ((evaluate s keys key q now maximum).result = .allow →
      ∃ token, (evaluate s keys key q now maximum).token = some token ∧
      ∀ x, Domain.contains d x → matchesQuery q x → decide mode (facts x) (s.policyAt policy token) key x = .allow) ∧
    ((evaluate s keys key q now maximum).result = .deny →
      ∃ token x, (evaluate s keys key q now maximum).token = some token ∧ Domain.contains d x ∧
        matchesQuery q x ∧ decide mode (facts x) (s.policyAt policy token) key x = .deny) := by
  cases wins : winner s.history keys q with
  | none => simp [evaluate, known, wins]
  | some f =>
    by_cases empty : (candidates d q).isEmpty
    · simp [evaluate, known, wins, empty]
    · simp only [evaluate, known, wins, empty, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro res
        unfold targetVerdict at res
        dsimp only at res
        split at res <;> try contradiction
        split at res
        next yes =>
          obtain ⟨c, hc, decision⟩ := List.any_eq_true.mp yes
          simp only [Bool.and_eq_true, beq_iff_eq] at decision
          obtain ⟨anchor, opts, fromProj⟩ := live_origin produced known hc
          refine ⟨_, rfl, ?_⟩
          intro x hx hq
          exact (transported_decision fromProj (covers_all_candidates valid decision.2 hx hq) hx
            (pathOk_of_domain hx) mode (facts x)).1 decision.1
        next =>
          split at res
          · contradiction
          · split at res <;> contradiction
      · intro res
        unfold targetVerdict at res
        dsimp only at res
        split at res <;> try contradiction
        split at res <;> try contradiction
        split at res
        next yes =>
          obtain ⟨c, hc, decision⟩ := List.any_eq_true.mp yes
          simp only [Bool.and_eq_true, beq_iff_eq] at decision
          obtain ⟨x, hx, hq, covered⟩ := deny_has_candidate valid decision.2
          obtain ⟨anchor, opts, fromProj⟩ := live_origin produced known hc
          exact ⟨_, x, rfl, hx, hq, (transported_decision fromProj covered hx
            (pathOk_of_domain hx) mode (facts x)).2 decision.1⟩
        next => split at res <;> contradiction

private theorem scopeHit_witness {d : Domain} {scope : Path} {c : Claim}
    (valid : ∀ p ∈ d, p.all Atom.valid = true) (hit : scopeHit d scope c.path c.holes) :
    ∃ x, Domain.contains d x ∧ scope <+: x ∧ c.covers x := by
  unfold scopeHit at hit
  split at hit
  next pre =>
    obtain ⟨x, hx, hpath, holes⟩ := (Domain.nonemptyRegion_iff valid).1 hit
    exact ⟨x, hx, (List.isPrefixOf_iff_prefix.mp pre).trans hpath,
      claim_covers_iff.mpr ⟨hpath, fun ⟨h, hh, pre⟩ => holes h hh pre⟩⟩
  next =>
    obtain ⟨pre, hit⟩ := Bool.and_eq_true_iff.mp hit
    obtain ⟨x, hx, hscope, holes⟩ := (Domain.nonemptyRegion_iff valid).1 hit
    exact ⟨x, hx, hscope, claim_covers_iff.mpr ⟨(List.isPrefixOf_iff_prefix.mp pre).trans hscope, fun ⟨h, hh, pre⟩ => holes h hh pre⟩⟩

private theorem coversScope_point {scope x : Path} {c : Claim} (whole : coversScope scope c)
    (inside : scope <+: x) : c.covers x := by
  simp [coversScope, List.isPrefixOf_iff_prefix] at whole
  refine claim_covers_iff.mpr ⟨whole.1.trans inside, ?_⟩
  rintro ⟨h, hh, pre⟩
  rcases List.prefix_or_prefix_of_prefix pre inside with before | after
  · exact (whole.2 h hh).1 before
  · exact (whole.2 h hh).2 after

theorem evaluateScope_sound {s keys key scope now d} (policy : PolicyHistory)
    (produced : ProducedState policy keys s) (known : keys.lookup key = some d)
    (valid : ∀ p ∈ d, p.all Atom.valid = true) (mode : Authority) (facts : Path → Facts) (maximum : Option Profile := some .scopedClaims) :
    let e := evaluateScope s keys key scope now maximum
    (e.result = .allow → ∃ token, e.token = some token ∧
      ∀ x, Domain.contains d x → scope <+: x → decide mode (facts x) (s.policyAt policy token) key x = .allow) ∧
    (e.result = .deny → ∃ token x, e.token = some token ∧ Domain.contains d x ∧ scope <+: x ∧
      decide mode (facts x) (s.policyAt policy token) key x = .deny) := by
  simp only [evaluateScope, known, Id.run, pure]
  split
  · cases wins : scopeWinner s.history keys d scope with
    | none => simp
    | some f =>
      dsimp only
      constructor
      · intro allow
        unfold scopeVerdict at allow
        dsimp only at allow
        split at allow <;> try contradiction
        split at allow
        next yes =>
          obtain ⟨c, hc, decision⟩ := List.any_eq_true.mp yes
          obtain ⟨kind, whole⟩ := Bool.and_eq_true_iff.mp decision
          obtain ⟨anchor, opts, origin⟩ := live_origin produced known hc
          exact ⟨_, rfl, fun x hx hscope => (transported_decision origin (coversScope_point whole hscope)
            hx (pathOk_of_domain hx) mode (facts x)).1 (beq_iff_eq.mp kind)⟩
        next => split at allow <;> contradiction
      · intro deny
        unfold scopeVerdict at deny
        dsimp only at deny
        split at deny <;> try contradiction
        split at deny <;> try contradiction
        split at deny <;> try contradiction
        next yes =>
          obtain ⟨c, hc, decision⟩ := List.any_eq_true.mp yes
          obtain ⟨kind, hit⟩ := Bool.and_eq_true_iff.mp decision
          obtain ⟨anchor, opts, origin⟩ := live_origin produced known hc
          obtain ⟨x, hx, hscope, covered⟩ := scopeHit_witness valid hit
          exact ⟨_, x, rfl, hx, hscope, (transported_decision origin covered hx
            (pathOk_of_domain hx) mode (facts x)).2 (beq_iff_eq.mp kind)⟩
  · simp

theorem usableRegions_sound {s keys key now maximum d r} (policy : PolicyHistory)
    (produced : ProducedState policy keys s) (known : keys.lookup key = some d)
    (listed : r ∈ usableRegions s keys key now maximum) (mode : Authority) (facts : Path → Facts) :
    Domain.nonemptyRegion d r.claim.path r.claim.holes ∧
    (∀ x, Domain.contains d x → r.claim.covers x →
      decide mode (facts x) (s.policyAt policy r.token) key x = .allow) ∧
    ∃ f ∈ listingFrames s keys, f.reply.token = r.token ∧ !listingSuperseded s keys d f r.claim ∧
      ∀ b ∈ claimsForKey key (latestMatching s.history keys (fun _ => true) r.token),
        b.kind = .deny → overlapIn d r.claim b = false := by
  simp only [usableRegions, known] at listed
  obtain ⟨f, hf, mem⟩ := List.mem_flatMap.mp (dedup_subset listed)
  obtain ⟨c, selected, rfl⟩ := List.mem_map.mp mem
  obtain ⟨hc, checks⟩ := List.mem_filter.mp selected
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_false] at checks
  obtain ⟨anchor, opts, origin⟩ := live_origin produced known hc
  exact ⟨checks.1.1.2, fun x hx covered =>
    (transported_decision origin covered hx (pathOk_of_domain hx) mode (facts x)).1 checks.1.1.1,
    f, hf, rfl, by simpa using checks.2, fun b hb deny => Bool.eq_false_iff.mpr (fun hit => checks.1.2 b hb ⟨deny, hit⟩)⟩

def ValidKeyDomains (keys : KeyDomains) :=
  ∀ k d, keys.lookup k = some d → ∀ p ∈ d, p.all Atom.valid = true

/-- Stamp a reply for a pinned policy snapshot. Its metadata, queried anchors
and disclosure options may vary freely between requests at the same token. -/
def projectedReply (policy : PolicyHistory) (keys : KeyDomains) (base : SnapshotReply)
    (anchors : List Path) (options : String → Path → ProjectOptions) : SnapshotReply :=
  { base with contexts := anchors.map fun anchor =>
      ⟨anchor, (keys.entries.map Prod.fst).flatMap fun k =>
        match keys.lookup k with
        | none => []
        | some d => projectAnchor (policy base.identity) k anchor d
            { options k anchor with profile := base.profile } keys.resources, none, some [anchor]⟩ }

theorem projectedReply_origin (policy keys base anchors options) (valid : ValidKeyDomains keys) :
    FromProjector policy keys (projectedReply policy keys base anchors options) := by
  intro ctx hctx c hc d known
  obtain ⟨anchor, _, rfl⟩ := List.mem_map.mp hctx
  obtain ⟨k, _, proj⟩ := List.mem_flatMap.mp hc
  dsimp only at proj
  cases hk : keys.lookup k with
  | none => simp [hk] at proj
  | some dom =>
    simp only [hk] at proj
    have fromCells := (projectAnchor_valid_site proj).2.2
    have eq := projectAnchor_key (valid _ _ hk) fromCells
    simp [eq, hk] at known
    subst d
    exact ⟨_, c, by simpa [projectedReply, SnapshotReply.identity, eq] using fromCells, rfl, fun _ => rfl⟩

/-- Follow a received group to the actual cell before the per-key input filter
and hole sorting. The disclosed region keeps its exact scope and holes. -/
theorem grouped_receipt_geometry {view : Query.View} {world stamp asked packed reply}
    (sent : Query.queryPermissionContexts view world stamp asked = .ok packed)
    (received : GroupedReply.receive? ⟨view.keys, view.resources⟩ packed.protoJson none true = some reply)
    (tableBound : packed.keySets.length ≤ 2147483647)
    (valid : ValidKeyDomains ⟨view.keys, view.resources⟩)
    (unique : ∀ k d, (k,d) ∈ view.keys → view.keys.lookup k = some d)
    (store : world.rules.all (view.resources.validSite ·.path)) {ctx c d}
    (context : ctx ∈ reply.contexts) (member : c ∈ ctx.claims) (known : view.keys.lookup c.key = some d) :
    ∃ src ∈ regionClaims world.rules c.key ctx.anchor d {view.options ctx.anchor c.key with profile := view.profile},
      src.kind = c.kind ∧ src.path = c.path ∧ src.holes.Perm c.holes := by
  have legal := GroupedReply.received_context_valid received context
  have site := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp legal).1).1
  obtain ⟨src, proj, key, kind, path, holes⟩ := Query.ledger_origin sent
    (GroupedReply.canonical_claim_in_table (GroupedReply.canonical_fields_of_query sent tableBound) received context member)
  simp only [projectContext, site, store, Bool.not_true, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, List.mem_flatMap, List.mem_map, List.mem_filter] at proj
  obtain ⟨_, ⟨⟨k,dom⟩, ⟨entry,_⟩,rfl⟩, cl⟩ := proj
  have lookup := unique _ _ entry
  have spelling := projectAnchor_key (valid k dom lookup) cl
  have ck : c.key = k := key.symm.trans spelling
  rw [ck] at known ⊢
  change view.keys.lookup k = some d at known
  cases Option.some.inj (known.symm.trans lookup)
  have paths : world.rules.all (pathOk ·.path) := List.all_eq_true.mpr fun rule hr =>
    (Bool.and_eq_true_iff.mp (List.all_eq_true.mp store rule hr)).1
  have memberPaths : (world.rules.filter (·.keys.contains k)).all (pathOk ·.path) :=
    List.all_eq_true.mpr fun rule hr => List.all_eq_true.mp paths rule (List.mem_filter.mp hr).1
  have comparable : (world.rules.filter (·.keys.contains k)).filter (Rule.comparableAt k ctx.anchor) =
      world.rules.filter (Rule.comparableAt k ctx.anchor) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro rule _
    simp [Rule.comparableAt]
    exact fun h _ => h
  refine ⟨src, ?_, kind, path, holes⟩
  unfold regionClaims
  rw [← projectKey_comparable memberPaths paths comparable]
  exact cl

/-- Canonical wire fields recover the sent arrays, table IDs and scope names.
An accepted claim then has an originating policy cell at the stamped revision. -/
theorem grouped_receipt_origin {view : Query.View} {world stamp asked packed reply}
    (policy : PolicyHistory) (sent : Query.queryPermissionContexts view world stamp asked = .ok packed)
    (received : GroupedReply.receive? ⟨view.keys, view.resources⟩ packed.protoJson none true = some reply)
    (tableBound : packed.keySets.length ≤ 2147483647)
    (pinned : world.rules = policy ⟨stamp.service,stamp.subject,stamp.snapshotToken⟩)
    (valid : ValidKeyDomains ⟨view.keys, view.resources⟩)
    (unique : ∀ k d, (k,d) ∈ view.keys → view.keys.lookup k = some d)
    (store : world.rules.all (view.resources.validSite ·.path)) :
    FromProjector policy ⟨view.keys,view.resources⟩ reply := by
  intro ctx context c member d known
  obtain ⟨source, projected, kind, path, holes⟩ :=
    grouped_receipt_geometry sent received tableBound valid unique store context member known
  obtain ⟨service, subject, token⟩ := GroupedReply.canonical_received_stamp received
  have stampEq := Query.response_stamp sent
  have identity : reply.identity = ⟨stamp.service,stamp.subject,stamp.snapshotToken⟩ := by
    simp only [SnapshotReply.identity, service, subject, token]
    exact congrArg (fun s : Query.Stamp => PolicyIdentity.mk s.service s.subject s.snapshotToken) stampEq
  refine ⟨{view.options ctx.anchor c.key with profile := view.profile}, source, ?_, kind, ?_⟩
  · rw [identity, ← pinned]
    exact projected
  · intro x
    simp only [Claim.covers, path, holes.any_eq]

private theorem overlap_witness {d : Domain} {a b : Claim} (valid : ∀ p ∈ d, p.all Atom.valid)
    (hit : overlapIn d a b) : ∃ x, Domain.contains d x ∧ a.covers x ∧ b.covers x := by
  unfold overlapIn at hit
  have joint {p} (nonempty : Domain.nonemptyRegion d p (a.holes ++ b.holes))
      (left : a.path <+: p) (right : b.path <+: p) :
      ∃ x, Domain.contains d x ∧ a.covers x ∧ b.covers x := by
    obtain ⟨x, hx, below, clear⟩ := (Domain.nonemptyRegion_iff valid).mp nonempty
    exact ⟨x, hx, claim_covers_iff.mpr ⟨left.trans below, fun ⟨h, hh, pre⟩ =>
      clear _ (List.mem_append_left _ hh) pre⟩, claim_covers_iff.mpr ⟨right.trans below,
        fun ⟨h, hh, pre⟩ => clear _ (List.mem_append_right _ hh) pre⟩⟩
  split at hit
  next pre => exact joint hit (List.isPrefixOf_iff_prefix.mp pre) List.prefix_rfl
  next =>
    split at hit
    next pre => exact joint hit List.prefix_rfl (List.isPrefixOf_iff_prefix.mp pre)
    next => contradiction

/-- A context produced from the service's validated rules and schema passes the
client's complete validation, including all hole scopes and cross-claim conflicts. -/
theorem projectContext_valid {keys : KeyDomains} (valid : ValidKeyDomains keys)
    (unique : ∀ k d, (k, d) ∈ keys.entries → keys.lookup k = some d)
    (rules anchor profile options) (site : keys.resources.validSite anchor)
    (stored : rules.all (keys.resources.validSite ·.path)) :
    let projected := projectContext rules keys.entries keys.resources anchor profile options
    contextValid keys profile ⟨projected.anchor, projected.claims, none, some [anchor]⟩ = true := by
  let ctx := projectContext rules keys.entries keys.resources anchor profile options
  have atAnchor : ctx.anchor = anchor := by simp [ctx, projectContext, site, stored]
  have origin {c : Claim} (hc : c ∈ ctx.claims) :
      ∃ d, keys.lookup c.key = some d ∧ d.any (Pattern.reach · anchor) ∧
        c ∈ regionClaims (rules.filter (·.keys.contains c.key)) c.key anchor d
          {options c.key with profile} := by
    simp only [ctx, projectContext, site, stored, Bool.not_true, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_map, List.mem_filter] at hc
    obtain ⟨proj, ⟨⟨k, d⟩, ⟨hd, reach⟩, rfl⟩, claim⟩ := hc
    have key := projectAnchor_key (valid _ _ (unique k d hd)) claim
    rw [key]
    exact ⟨d, unique _ _ hd, reach, claim⟩
  change contextValid keys profile ⟨ctx.anchor, ctx.claims, none, some [anchor]⟩ = true
  simp only [contextValid, atAnchor, site, List.all_cons, List.all_nil, Bool.and_true,
    Option.any_some, Bool.true_and, List.all_eq_true]
  intro c hc
  obtain ⟨d, known, reach, proj⟩ := origin hc
  have ⟨path, below, inDomain, form, holes⟩ := projectAnchor_structure reach proj
  simp only [known, Option.all_some, Option.any_some, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, List.isEmpty_iff, List.isPrefixOf_iff_prefix, List.all_eq_true,
    Bool.not_eq_true', List.any_eq_false]
  refine ⟨⟨⟨⟨⟨path, below⟩, form⟩, Or.inr inDomain⟩, ?_⟩, ?_⟩
  · intro h hh
    obtain ⟨legal, sub, strict, reachable⟩ := holes h hh
    exact ⟨⟨⟨legal, sub⟩, bne_iff_ne.mpr strict⟩, reachable⟩
  · intro other member collision
    obtain ⟨⟨sameKey, distinct⟩, hit⟩ := collision
    obtain ⟨otherD, knownOther, _, second⟩ := origin member
    rw [sameKey, known] at knownOther
    cases knownOther
    rw [sameKey] at second
    obtain ⟨x, hx, left, right⟩ := overlap_witness (valid _ _ known) hit
    exact (bne_iff_ne.mp distinct) (projection_no_mixed_overlap second proj right left hx)

private theorem accepted_identity {s t reply now profile}
    (accepted : snapshotAction s t reply now profile ≠ .discard) :
    reply.service = s.service ∧
      (snapshotAction s t reply now profile ≠ .reset → s.subject = some reply.subject) := by
  constructor
  · by_cases same : reply.service = s.service
    · exact same
    · exact (accepted (by simp [snapshotAction, same])).elim
  · intro kept
    unfold snapshotAction at accepted kept
    dsimp only at accepted kept
    split at accepted <;> try contradiction
    next well =>
      simp only [well] at kept
      split at accepted <;> try contradiction
      next floor =>
        simp only [floor] at kept
        cases hs : s.subject with
        | none => simp [hs] at kept
        | some id => by_cases eq : id = reply.subject <;> simp_all

theorem accepted_projection_origin {s keys policy t reply now profile}
    (hs : ProducedState policy keys s) (hr : FromProjector policy keys reply) :
    ProducedState policy keys (acceptSnapshot s t reply now profile) := by
  by_cases ignored : snapshotAction s t reply now profile = .discard
  · simpa [acceptSnapshot, ignored] using hs
  obtain ⟨service, sameSubject⟩ := accepted_identity ignored
  intro f hf
  have keep : (snapshotAction s t reply now profile == .discard) = false := beq_eq_false_iff_ne.mpr ignored
  simp only [acceptSnapshot, keep, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hf ⊢
  rcases hf with rfl | past
  · exact ⟨service, rfl, hr⟩
  · split at past <;> try contradiction
    next retained =>
      have prior := hs f past
      exact ⟨prior.1, (sameSubject (by simpa using retained)).symm.trans prior.2.1, prior.2.2⟩

def ProjectedEvent (policy : PolicyHistory) (keys : KeyDomains) : ClientEvent → Prop
  | .receive _ r _ _ => FromProjector policy keys r
  | _ => True

theorem trace_projection_origin {s keys policy} (hs : ProducedState policy keys s)
    (events : List ClientEvent) (tagged : ∀ e ∈ events, ProjectedEvent policy keys e) :
    ProducedState policy keys (runTrace s events) := by
  induction events generalizing s with
  | nil => exact hs
  | cons e es ih =>
    apply ih _ (fun x hx => tagged _ (by simp [hx]))
    cases e with
    | receive t r n p => exact accepted_projection_origin hs (tagged (.receive t r n p) (by simp))
    | elapse => exact hs
    | signIn session => simp [ProducedState, ClientEvent.apply]

private theorem definite_binding {s keys b now v}
    (definite : v = .allow ∨ v = .deny)
    (h : (evaluateBinding s keys b now).result = v) :
    ∃ q, widenName b = some q ∧ evaluateBinding s keys b now = evaluate s keys b.key q now := by
  cases widened : widenName b with
  | none => rcases definite with rfl | rfl <;> simp [evaluateBinding, widened] at h
  | some q =>
    refine ⟨q, rfl, ?_⟩
    simp only [evaluateBinding, widened] at h ⊢
    split at h
    next guard => rcases definite with rfl | rfl <;> contradiction
    next guard => simp [guard]

private theorem definitive_domain {s keys key q now v}
    (definite : v = .allow ∨ v = .deny) (h : (evaluate s keys key q now).result = v) :
    ∃ d, keys.lookup key = some d := by
  cases eq : keys.lookup key with
  | some d => exact ⟨d, rfl⟩
  | none => rcases definite with rfl | rfl <;> simp [evaluate, eq] at h

theorem allow_has_candidate {s keys key q d now} (known : keys.lookup key = some d)
    (valid : ∀ p ∈ d, p.all Atom.valid = true) (h : (evaluate s keys key q now).result = .allow) :
    ∃ x, Domain.contains d x ∧ matchesQuery q x := by
  cases eq : candidates d q with
  | nil => cases wins : winner s.history keys q <;> simp [evaluate, known, eq, wins] at h
  | cons p ps =>
    have nonempty : Domain.nonemptyRegion (candidates d q) [] [] := by
      simp [Domain.nonemptyRegion, eq, Pattern.fixedPrefix, Pattern.consume]
    obtain ⟨x, hx, _⟩ := (Domain.nonemptyRegion_iff (candidates_valid valid q)).1 nonempty
    exact ⟨x, (candidate_matches _ _ _).1 hx⟩

def RequestAllowed (s : ClientState) (keys : KeyDomains) (ceiling : Ceiling) (rs : List ActiveRequirement)
    (now : Nat) (policy : PolicyHistory) (mode : Authority) (facts : Path → Facts) : Prop :=
    ∃ token, (rs ≠ [] ∧ ∀ r ∈ rs, r.deferBinding = false) ∧ ∀ r ∈ rs, ceiling.permits r.info ∧ r.targets ≠ [] ∧ ∀ b ∈ r.targets, ∃ q d,
      widenName b = some q ∧ keys.lookup b.key = some d ∧
      (evaluateBinding s keys b now).token = some token ∧ (∃ x, Domain.contains d x ∧ matchesQuery q x) ∧
      ∀ x, Domain.contains d x → matchesQuery q x →
        decide mode (facts x) (s.policyAt policy token) b.key x = .allow

def RequestDenied (s : ClientState) (keys : KeyDomains) (ceiling : Ceiling) (rs : List ActiveRequirement)
    (now : Nat) (policy : PolicyHistory) (mode : Authority) (facts : Path → Facts) : Prop :=
    (∃ r ∈ rs, ceiling.permits r.info = false) ∨
    ∃ r ∈ rs, ∃ b ∈ r.targets, ∃ q d token x, widenName b = some q ∧ keys.lookup b.key = some d ∧
      (evaluateBinding s keys b now).token = some token ∧ Domain.contains d x ∧ matchesQuery q x ∧
      decide mode (facts x) (s.policyAt policy token) b.key x = .deny ∧
      (evaluateBinding s keys b now).result = .deny

/-- T2 for an offered request. All concrete realizations of its wildcard or
in-place alias targets authorize in one snapshot, under either authority. -/
theorem offer_projection_allow {s keys ceiling rs now} (policy : PolicyHistory)
    (produced : ProducedState policy keys s) (valid : ValidKeyDomains keys)
    (mode : Authority) (facts : Path → Facts) (h : offer s keys ceiling rs now = .allow) :
    RequestAllowed s keys ceiling rs now policy mode facts := by
  obtain ⟨token, binds, together⟩ := offer_allow_one_snapshot h
  have ready : ∀ r ∈ rs, r.deferBinding = false := by
    intro r hr
    cases deferred : r.deferBinding <;> try rfl
    have blocked : rs.any (fun r => r.deferBinding || r.targets.isEmpty) :=
      List.any_eq_true.mpr ⟨r, hr, by simp [deferred]⟩
    unfold offer at h
    split at h <;> try contradiction
    split at h <;> try contradiction
  refine ⟨token, ⟨fun empty => binds (by simp [empty]), ready⟩, ?_⟩
  intro r hr
  constructor
  · cases denied : ceiling.permits r.info <;> try rfl
    have failure : rs.any (fun r => !ceiling.permits r.info) :=
      List.any_eq_true.mpr ⟨r, hr, by simp [denied]⟩
    have nonempty : rs.isEmpty = false := List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hr)
    simp [offer, nonempty, failure] at h
  · have nonempty : r.targets ≠ [] := by
      intro empty
      have bad : rs.any (fun r => r.deferBinding || r.targets.isEmpty) :=
        List.any_eq_true.mpr ⟨r, hr, by simp [empty]⟩
      unfold offer at h
      split at h <;> try contradiction
      split at h <;> try contradiction
    refine ⟨nonempty, ?_⟩
    intro b hb
    have evidence := together _ hr _ hb
    have yes : (evaluateBinding s keys b now).result = .allow := by simp [evidence]
    obtain ⟨q, widen, eq⟩ := definite_binding (Or.inl rfl) yes
    have yes' := eq ▸ yes
    obtain ⟨d, known⟩ := definitive_domain (Or.inl rfl) yes'
    obtain ⟨t, tokenEq, decisions⟩ := (evaluated_projection_sound policy produced known
      (valid _ _ known) mode facts).1 yes'
    have tok : t = token := by simpa [← eq, evidence] using tokenEq.symm
    exact ⟨q, d, widen, known, by simp [evidence], allow_has_candidate known (valid _ _ known) yes', tok ▸ decisions⟩

private theorem combined_deny {xs : List Evidence} (h : combine xs = .deny) :
    ∃ x ∈ xs, x.result = .deny := by
  unfold combine at h
  split at h
  next yes => simpa [List.any_eq_true] using yes
  next =>
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases xs <;> simp_all
    split at h <;> contradiction

/-- A denial either follows from the active credential ceiling or has a
denying in-domain witness at the selected target's snapshot. -/
theorem offer_projection_deny {s keys ceiling rs now} (policy : PolicyHistory)
    (produced : ProducedState policy keys s) (valid : ValidKeyDomains keys)
    (mode : Authority) (facts : Path → Facts) (h : offer s keys ceiling rs now = .deny) :
    RequestDenied s keys ceiling rs now policy mode facts := by
  unfold offer at h
  split at h <;> try contradiction
  split at h
  next fail => exact Or.inl (by simpa [List.any_eq_true] using fail)
  next =>
    split at h <;> try contradiction
    obtain ⟨e, he, deny⟩ := combined_deny h
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
    obtain ⟨r, hr, ht⟩ := List.mem_flatMap.mp hb
    obtain ⟨q, widen, eq⟩ := definite_binding (Or.inr rfl) deny
    have no := eq ▸ deny
    obtain ⟨d, known⟩ := definitive_domain (Or.inr rfl) no
    obtain ⟨tok, x, tag, hx, hq, denied⟩ := (evaluated_projection_sound policy produced known
      (valid _ _ known) mode facts).2 no
    exact Or.inr ⟨r, hr, b, ht, q, d, tok, x, widen, known, eq ▸ tag, hx, hq, denied, deny⟩

/-- A successful canonical grouped receipt extends the real cache. A definitive
offer after that transition has a policy witness under either authority. -/
theorem grouped_offer_sound {view : Query.View} {world stamp asked packed reply} (policy : PolicyHistory)
    (sent : Query.queryPermissionContexts view world stamp asked = .ok packed)
    (received : GroupedReply.receive? ⟨view.keys,view.resources⟩ packed.protoJson none true = some reply)
    (tableBound : packed.keySets.length ≤ 2147483647) (pinned : world.rules = policy ⟨stamp.service,stamp.subject,stamp.snapshotToken⟩)
    (valid : ValidKeyDomains ⟨view.keys,view.resources⟩)
    (unique : ∀ k d, (k,d) ∈ view.keys → view.keys.lookup k = some d)
    (stored : world.rules.all (view.resources.validSite ·.path))
    (s ticket clock profile ceiling requirements now mode facts)
    (past : ProducedState policy ⟨view.keys,view.resources⟩ s) :
    let keys := KeyDomains.mk view.keys view.resources
    let next := acceptSnapshot s ticket reply clock profile
    (offer next keys ceiling requirements now = .allow → RequestAllowed next keys ceiling requirements now policy mode facts) ∧
    (offer next keys ceiling requirements now = .deny → RequestDenied next keys ceiling requirements now policy mode facts) := by
  have origin := grouped_receipt_origin policy sent received tableBound pinned valid unique stored
  have next := accepted_projection_origin (t := ticket) (now := clock) (profile := profile) past origin
  exact ⟨offer_projection_allow policy next valid mode facts, offer_projection_deny policy next valid mode facts⟩

/-- A canonical Scoped Claims reply decoded from ProtoJSON is discarded on receipt
whenever the dispatched ticket or the client's receipt-time profile maximum caps the
request at Grant-Shaped. -/
theorem grouped_reply_respects_maxProfile {view : Query.View} {world stamp asked packed reply}
    (isScoped : view.profile = .scopedClaims)
    (sent : Query.queryPermissionContexts view world stamp asked = .ok packed)
    (received : GroupedReply.receive? ⟨view.keys, view.resources⟩ packed.protoJson none true = some reply)
    (s ticket clock profile)
    (capped : ticket.maxProfile = .grantShaped ∨ profile = .grantShaped) :
    acceptSnapshot s ticket reply clock profile = s := by
  have packedProfile : packed.profile = .scopedClaims := by
    unfold Query.queryPermissionContexts at sent
    cases h : Query.requestedNames view world stamp.subject asked with
    | error _ => simp [h, Except.map] at sent
    | ok _ => simp [h, Except.map] at sent; subst packed; exact isScoped
  have replyProfile : reply.profile = .scopedClaims :=
    (GroupedReply.canonical_received_envelope received).2.2.2.2.trans packedProfile
  rcases capped with cap | cap <;> simp [acceptSnapshot, snapshotAction, cap, replyProfile]

/-- Projection inputs before any claim exists. The producer stamps each reply
from its service, subject and revision's policy, with per-key disclosure and truncation choices. -/
inductive ProjectionEvent where
  | receive (ticket : SnapshotTicket) (base : SnapshotReply) (anchors : List Path)
      (options : String → Path → ProjectOptions) (now : Nat) (maxProfile : Profile)
  | elapse
  | signIn (session : String)

def ProjectionEvent.deliver (policy : PolicyHistory) (keys : KeyDomains) : ProjectionEvent → ClientEvent
  | .receive t r anchors options n p => .receive t (projectedReply policy keys r anchors options) n p
  | .elapse => .elapse
  | .signIn session => .signIn session

def projectedTrace (service session : String) (policy : PolicyHistory) (keys : KeyDomains)
    (events : List ProjectionEvent) :=
  runTrace { service, session } (events.map (ProjectionEvent.deliver policy keys))

theorem projectedTrace_produced (valid : ValidKeyDomains keys) (service session policy events) :
    ProducedState policy keys (projectedTrace service session policy keys events) := by
  apply trace_projection_origin (by simp [ProducedState])
  intro e he
  obtain ⟨input, _, rfl⟩ := List.mem_map.mp he
  cases input with
  | receive _ base anchors opts _ _ => exact projectedReply_origin _ _ _ _ _ valid
  | elapse | signIn => trivial

/-- The complete normalized client path, from policy at arbitrary snapshots
through projection, out-of-order delivery, anchor selection and request
combination. The denying witness may come from a different snapshot than
another requirement's evidence, as specified in §4.4. -/
theorem projected_offer_sound (service session keys policy events ceiling rs now mode facts)
    (valid : ValidKeyDomains keys) :
    let s := projectedTrace service session policy keys events
    (offer s keys ceiling rs now = .allow → RequestAllowed s keys ceiling rs now policy mode facts) ∧
    (offer s keys ceiling rs now = .deny → RequestDenied s keys ceiling rs now policy mode facts) := by
  let produced := projectedTrace_produced valid service session policy events
  exact ⟨offer_projection_allow policy produced valid mode facts,
    offer_projection_deny policy produced valid mode facts⟩

theorem Descriptor.validKeyDomains {d : Descriptor} (wf : d.WellFormed) : ValidKeyDomains d.keyDomains := by
  intro k dom known p hp
  obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp known
  have mem : (k, dom) ∈ d.keyDomains.entries := by rw [eq]; simp
  obtain ⟨key, _, eq⟩ := List.mem_map.mp mem
  change (key, d.domain key) = (k, dom) at eq
  cases eq
  exact d.domain_valid wf hp

theorem Descriptor.registeredLookup (d : Descriptor) :
    ∀ k dom, (k,dom) ∈ d.keyDomains.entries → d.keyDomains.lookup k = some dom := by
  intro k dom member
  obtain ⟨key, mem, eq⟩ := List.mem_map.mp member
  change (key, d.domain key) = (k, dom) at eq
  cases eq
  change ((List.map (fun k => (k, d.domain k)) _).lookup k) = some (d.domain k)
  generalize old : (d.requirements.map (·.key)).eraseDups = ks at mem ⊢
  clear old
  induction ks with
  | nil => contradiction
  | cons hd ks ih =>
    by_cases same : hd = k
    · simp [same]
    · simp [List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm same), ih (by simpa [Ne.symm same] using mem)]

theorem Descriptor.projectContext_valid {d : Descriptor} (wf : d.WellFormed)
    (rules anchor profile options) (site : d.resourcePatterns.validSite anchor)
    (stored : rules.all (d.resourcePatterns.validSite ·.path)) :
    let ctx := projectContext rules d.keyDomains.entries d.resourcePatterns anchor profile options
    contextValid d.keyDomains profile ⟨ctx.anchor, ctx.claims, none, some [anchor]⟩ := by
  exact Authz.projectContext_valid (d.validKeyDomains wf) d.registeredLookup rules anchor profile options site stored

/-- The executable descriptor/request binder feeds precisely the normalized
requirements whose snapshot proofs establish a definitive atomic offer. -/
private theorem atomic_offer_evidence {d : Descriptor} {s : ClientState} {method request now ceiling unresolved guards v}
    (sameService : s.service = d.service)
    (definite : v = .allow ∨ v = .deny)
    (h : offerRequest d s method request now ceiling unresolved guards = .single v) :
    ∃ m, d.method? method = some m ∧
      offer s d.keyDomains ceiling
        ((offerBindings d m request unresolved guards).map (·.forClient none)) now = v := by
  cases hm : d.method? method with
  | none =>
    rcases definite with rfl | rfl <;>
      simp [offerRequest, hm] at h <;> split at h <;> cases h
  | some m =>
    refine ⟨m, rfl, ?_⟩
    by_cases available : methodAvailable (some m) ceiling
    · by_cases req : m.disposition = .requirements
      · by_cases selected : partialFor m request
        · rcases definite with rfl | rfl <;>
            simp [offerRequest, hm, available, req, selected, sameService] at h <;>
            split at h <;> cases h
        · simpa [offerRequest, hm, available, req, selected, sameService] using h
      · rcases definite with rfl | rfl <;> simp [offerRequest, hm, available, req] at h
    · rcases definite with rfl | rfl <;> simp [offerRequest, hm, available] at h

theorem method_offer_sound (d : Descriptor) (wf : d.WellFormed) (session policy events method request
    now ceiling unresolved guards mode facts) :
    let keys := d.keyDomains
    let s := projectedTrace d.service session policy keys events
    let offered := offerRequest d s method request now ceiling unresolved guards
    (offered = .single .allow → ∃ m, d.method? method = some m ∧ RequestAllowed s keys ceiling
      ((offerBindings d m request unresolved guards).map (·.forClient none)) now policy mode facts) ∧
    (offered = .single .deny → ∃ m, d.method? method = some m ∧ RequestDenied s keys ceiling
      ((offerBindings d m request unresolved guards).map (·.forClient none)) now policy mode facts) := by
  dsimp only
  constructor
  · intro h
    obtain ⟨m, found, offer⟩ := atomic_offer_evidence (trace_preserves_service _ _) (Or.inl rfl) h
    exact ⟨m, found, (projected_offer_sound _ _ _ _ _ _ _ _ _ _ (d.validKeyDomains wf)).1 offer⟩
  · intro h
    obtain ⟨m, found, offer⟩ := atomic_offer_evidence (trace_preserves_service _ _) (Or.inr rfl) h
    exact ⟨m, found, (projected_offer_sound _ _ _ _ _ _ _ _ _ _ (d.validKeyDomains wf)).2 offer⟩

/-- Transport and resolver agreement for a concrete server call. Each bound
server name realizes a candidate the client evaluated for that key. This
condition mentions descriptor bindings and names only. -/
def RealizesTarget (keys : KeyDomains) (client : List ActiveRequirement) (r : BoundRequirement)
    (target : Path) : Prop :=
  ∃ cr ∈ client, cr.info = r.decl.info ∧ ∃ b ∈ cr.targets, b.key = r.decl.key ∧
    (∀ q, widenName b = some q → matchesQuery q target) ∧
    ∀ d, keys.lookup b.key = some d → Domain.contains d target

def RealizesBindings (keys : KeyDomains) (client : List ActiveRequirement)
    (server : List BoundRequirement) : Prop :=
  ∀ r ∈ server, ¬r.resolverFault ∧ ¬r.unbound ∧ ∀ pair ∈ r.targets,
    pair.2.target.contains "-" = false ∧ RealizesTarget keys client r pair.2.target

def BindingsAtToken (s : ClientState) (keys : KeyDomains) (client : List ActiveRequirement)
    (now : Nat) (token : String) : Prop :=
  ∀ cr ∈ client, ∀ b ∈ cr.targets, (evaluateBinding s keys b now).token = some token

private theorem realized_permits {s keys client now policy opts}
    (allowed : RequestAllowed s keys opts.ceiling client now policy opts.mode (fun p => opts.available p)) :
    ∃ token, BindingsAtToken s keys client now token ∧
      (∀ r target, RealizesTarget keys client r target → opts.ceiling.permits r.decl.info ∧
        decide opts.mode (opts.available target) (s.policyAt policy token) r.decl.key target = .allow) ∧
      ∀ server, RealizesBindings keys client server →
        (∀ r ∈ server, ∀ pair ∈ r.targets, opts.rowReadFailed pair.2.target = false) →
        BoundDecisions opts (s.policyAt policy token) server := by
  obtain ⟨token, _, permitted⟩ := allowed
  have point (r target) (real : RealizesTarget keys client r target) :
      opts.ceiling.permits r.decl.info ∧
        decide opts.mode (opts.available target) (s.policyAt policy token) r.decl.key target = .allow := by
    obtain ⟨cr, hc, info, b, hb, key, candidate, domain⟩ := real
    obtain ⟨cap, _, results⟩ := permitted cr hc
    obtain ⟨q, dom, widened, lookup, _, _, yes⟩ := results b hb
    exact And.intro (show opts.ceiling.permits r.decl.info = true from info ▸ cap)
      (show decide opts.mode (opts.available target) (s.policyAt policy token) r.decl.key target = .allow
        from key ▸ yes _ (domain _ lookup) (candidate _ widened))
  refine ⟨token, ?_, point, ?_⟩
  · intro cr hc b hb
    obtain ⟨_, _, _, _, atToken, _⟩ := (permitted cr hc).2.2 b hb
    exact atToken
  · intro server matchesServer readable r hr
    obtain ⟨resolved, bound, targets⟩ := matchesServer r hr
    exact ⟨resolved, bound, fun pair hp => ⟨(targets pair hp).1, readable r hr pair hp, point _ _ (targets pair hp).2⟩⟩

/-- On canonical transport the complete client binder contains both server
phases, including every field guard the interpreted update mask activated. -/
theorem canonical_offer_bindings (d m request) (opts : ServerOptions)
    (canonical : ∀ p, SuppliedName request p → opts.names.canonical d.resourcePatterns p = .ok (some p)) :
    offerBindings d m request (fun _ => some []) opts.guards =
      serverBindings d m request opts false ++ serverBindings d m request opts true := by
  simp only [offerBindings, serverBindings]
  have phase (flag : Bool) := requirementsFor_congr_resolver d m request (fun _ => some [])
    opts.guards (some flag) (left := fun p => .ok (some p)) (right := opts.names.canonical d.resourcePatterns)
    (fun p supplied => (canonical p supplied).symm)
  rw [phase false, phase true]

private theorem widened_concrete {b : TargetBinding} {q : Path} (known : b.unresolved = some [])
    (wide : widenName b = some q) : q = b.target := by
  simp [widenName, known, guard, TargetBinding.target] at wide ⊢
  split at wide <;> simp_all [failure]

private theorem matches_concrete {q x : Path} (literal : q.contains "-" = false)
    (matched : matchesQuery q x = true) : x = q := by
  induction q generalizing x with
  | nil => cases x <;> simp_all [matchesQuery]
  | cons s q ih =>
    rw [List.contains_cons] at literal
    have clean := Bool.or_eq_false_iff.mp literal
    cases x with
    | nil => contradiction
    | cons t xs =>
      obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp matched
      have ordinary : (s == "-") = false := beq_eq_false_iff_ne.mpr (Ne.symm (beq_eq_false_iff_ne.mp clean.1))
      have eq : s = t := by simpa [ordinary] using head
      rw [eq, ih clean.2 tail]

/-- Geometry only. No policy conclusions or client/server membership
relationships are inputs to this predicate. -/
def ConcreteBinding (b : TargetBinding) : Prop :=
  b.unresolved = some [] ∧ b.target.contains "-" = false

private theorem whole_binding_ready {s keys ceiling client now policy mode facts} {r : BoundRequirement}
    (offered : RequestAllowed s keys ceiling client now policy mode facts)
    (member : r.forClient none ∈ client) : ¬r.resolverFault ∧ ¬r.unbound := by
  have ready := offered.choose_spec.1.2 _ member
  cases fault : r.resolverFault <;> cases bound : r.unbound <;>
    simp_all [BoundRequirement.forClient]

private theorem same_binding_realizes {s keys ceiling client now policy mode facts r b item}
    (offered : RequestAllowed s keys ceiling client now policy mode facts)
    (member : r.forClient item ∈ client) {i : Nat} (selected : item.all (· == i))
    (bound : (i,b) ∈ r.targets) (concrete : ConcreteBinding b) :
    RealizesTarget keys client r b.target := by
  let point := {b with key := r.decl.key}
  have present : point ∈ (r.forClient item).targets := List.mem_map.mpr
    ⟨(i,b), List.mem_filter.mpr ⟨bound, selected⟩, rfl⟩
  obtain ⟨_, _, permissions⟩ := offered
  obtain ⟨q, dom, wide, lookup, _, ⟨x, inside, matched⟩, _⟩ :=
    (permissions _ member).2.2 point present
  have exactName := widened_concrete (b := point) concrete.1 wide
  change q = b.target at exactName
  subst q
  have actual := matches_concrete concrete.2 matched
  subst x
  exact ⟨r.forClient item, member, rfl, point, present, rfl,
    fun q h => by rw [Option.some.inj (h.symm.trans wide)]; exact matched,
    fun dom' h => by rw [Option.some.inj (h.symm.trans lookup)]; exact inside⟩

/-- Run an atomic offer on the canonical, completely bound inputs at its
evidence revision. The server performs its own batch input validation. -/
theorem method_offer_authorizes (d : Descriptor) (wf : d.WellFormed) (session policy events name request now)
    (opts : ServerOptions) (canonical : ∀ p, SuppliedName request p → opts.names.canonical d.resourcePatterns p = .ok (some p))
    (handler : opts.handlerResolvesResiduals)
    {m : MethodDecl} (method : d.method? name = some m) (decl : m.disposition = .requirements)
    (address : singularWriterFault d m request opts = false)
    (parent : m.isBatch → partialFor m request = false →
      (resolvedBatchParent d m request opts).isOk = true ∧ batchItemsBound d m request opts)
    (present : if m.isBatch then batchHasAuthority d m request opts (serverBindings d m request opts true) = true
      else serverBindings d m request opts false ≠ []) :
    let rs := offerBindings d m request (fun _ => some []) opts.guards
    (∀ r ∈ rs, ∀ pair ∈ r.targets,
      ConcreteBinding pair.2 ∧ opts.rowReadFailed pair.2.target = false) →
    let s := projectedTrace d.service session policy d.keyDomains events
    offerRequest d s name request now opts.ceiling (fun _ => some []) opts.guards = .single .allow →
    ∃ token, BindingsAtToken s d.keyDomains (rs.map (·.forClient none)) now token ∧
      let rules := s.policyAt policy token
      rules.all (d.resourcePatterns.validSite ·.path) → opts.names.rulesAllowed d.resourcePatterns rules →
      let out := authorizeRequest d name request rules opts
      out.decision = "PROCEED" ∨ (out.reason = some "BATCH" ∧ out.status = some .invalidArgument) := by
  intro rs inputs s offered
  obtain ⟨m', found, allowed⟩ := (method_offer_sound d wf session policy events name
    request now opts.ceiling _ opts.guards opts.mode (fun p => opts.available p)).1 offered
  have eq : m' = m := Option.some.inj (found.symm.trans method)
  subst m'
  have member {phase r} (hr : r ∈ serverBindings d m request opts phase) : r ∈ rs := by
    dsimp only [rs]
    rw [canonical_offer_bindings _ _ _ _ canonical]
    cases phase <;> simp_all
  obtain ⟨token, marked, _, decide⟩ := realized_permits (opts := opts) allowed
  have phase (flag : Bool) := decide (serverBindings d m request opts flag)
    (fun r hr => by
      have included : r.forClient none ∈ rs.map (·.forClient none) := List.mem_map.mpr ⟨r, member hr, rfl⟩
      obtain ⟨fault, bound⟩ := whole_binding_ready allowed included
      exact ⟨fault, bound, fun pair hp => ⟨(inputs _ (member hr) _ hp).1.2,
        same_binding_realizes allowed included (by rfl) hp (inputs _ (member hr) _ hp).1⟩⟩)
    (fun r hr pair hp => (inputs r (member hr) pair hp).2)
  exact ⟨token, marked, fun store aliases => authorizeRequest_of_decisions method decl store aliases
    handler address parent (phase false) (phase true) present⟩

/-- The List reprojects scoped claims at its wildcard anchor, without a query
budget. The stamp and name-resolution evidence come from the actual receipt. -/
def listQueryView (d : Descriptor) (opts : ServerOptions) : Query.View :=
  ⟨d.keyDomains.entries, d.resourcePatterns, .scopedClaims,
    fun anchor k => {nonprojecting := opts.nonprojecting k anchor, canName := opts.canName},
    opts.names.indirect⟩

def ListFrameSource (d : Descriptor) (opts : ServerOptions) (rules : List Rule) (q : Path)
    (frame : Frame) : Prop :=
  ∃ world stamp asked packed, world.rules = rules ∧
    Query.queryPermissionContexts (listQueryView d opts) world stamp asked = .ok packed ∧
    GroupedReply.receive? d.keyDomains packed.protoJson none true = some frame.reply ∧
    packed.keySets.length ≤ 2147483647 ∧ ∀ ctx ∈ frame.reply.contexts, ctx.anchor = wildcardAnchor q

private theorem live_list_geometry {d : Descriptor} {s : ClientState} {key q opts rules} {f : Frame} {c now}
    (wf : d.WellFormed) (known : d.keyDomains.lookup key = some (d.domain key))
    (stored : rules.all (d.resourcePatterns.validSite ·.path))
    (sources : ∀ g ∈ s.history, g.reply.token = f.reply.token → ListFrameSource d opts rules q g)
    (hc : c ∈ claimsForKey key ((latestContexts s.history d.keyDomains q f.reply.token).filter
      (TimedContext.usable now (some .scopedClaims)))) :
    ∃ source ∈ regionClaims rules key (wildcardAnchor q) (d.domain key)
      { nonprojecting := opts.nonprojecting key (wildcardAnchor q), canName := opts.canName },
      source.kind = c.kind ∧ source.path = c.path ∧ source.holes.Perm c.holes := by
  obtain ⟨inside, isKey⟩ := List.mem_filter.mp hc
  obtain ⟨timed, hm, member⟩ := List.mem_flatMap.mp inside
  obtain ⟨g, storedFrame, actual⟩ := List.mem_flatMap.mp (dedup_subset (List.mem_filter.mp hm).1)
  split at actual <;> try contradiction
  next token =>
    obtain ⟨ctx, selected, rfl⟩ := List.mem_map.mp actual
    have delivered := (List.mem_filter.mp selected).1
    obtain ⟨world, stamp, asked, packed, history, sent, received, tableBound, anchors⟩ :=
      sources _ storedFrame (beq_iff_eq.mp token)
    have same := beq_iff_eq.mp isKey
    have raw := grouped_receipt_geometry sent received tableBound (d.validKeyDomains wf) d.registeredLookup
      (history ▸ stored) delivered member (same ▸ known)
    rw [same, anchors ctx delivered, history] at raw
    exact raw

/-- A universal List can reuse a cached wildcard claim when the service
reprojects the same claim geometry at the same revision and wildcard anchor.
An item filter or a change of projection budget or disclosure may defer it. -/
theorem wildcard_list_offer_authorizes {d : Descriptor} {s : ClientState} {name request now opts m r b i rules}
    (method : d.method? name = some m) (decl : m.disposition = .requirements) (singular : m.isBatch = false)
    (service : s.service = d.service) (canonical : ∀ p, SuppliedName request p →
      opts.names.canonical d.resourcePatterns p = .ok (some p))
    (address : singularWriterFault d m request opts = false)
    (outer : serverBindings d m request opts false = [r]) (items : serverBindings d m request opts true = [])
    (targets : r.targets = [(i,b)]) (fault : r.resolverFault = false) (bound : r.unbound = false)
    (universal : r.wildcard = .universal) (fixed : b.unresolved = some []) (wild : b.target.contains "-")
    (filter : m.itemFilter = none) (known : d.keyDomains.lookup r.decl.key = some (d.domain r.decl.key))
    (stored : rules.all (d.resourcePatterns.validSite ·.path)) (names : opts.names.rulesAllowed d.resourcePatterns rules)
    (wf : d.WellFormed) (sources : ∀ f, winner s.history d.keyDomains b.target = some f →
      ∀ g ∈ s.history, g.reply.token = f.reply.token → ListFrameSource d opts rules b.target g)
    (offer : offerRequest d s name request now opts.ceiling (fun _ => some []) opts.guards = .single .allow) :
    (authorizeRequest d name request rules opts).decision = "PROCEED" := by
  obtain ⟨found, atName, permission⟩ := atomic_offer_evidence service (Or.inl rfl) offer
  cases Option.some.inj (atName.symm.trans method)
  rw [canonical_offer_bindings d m request opts canonical, outer, items, List.append_nil] at permission
  let target := {b with key := r.decl.key}
  have included : target ∈ (r.forClient none).targets := by simp [target, BoundRequirement.forClient, targets]
  obtain ⟨token, _, each⟩ := offer_allow_one_snapshot permission
  have evidence := each (r.forClient none) (by simp) target included
  have cap : opts.ceiling.permits r.decl.info := by
    cases hc : opts.ceiling.permits r.decl.info <;> try rfl
    simp [Authz.offer, BoundRequirement.forClient, hc] at permission
  have yes : (evaluateBinding s d.keyDomains target now).result = .allow := by rw [evidence]
  obtain ⟨q, wide, eq⟩ := definite_binding (Or.inl rfl) yes
  have original := widened_concrete (b := target) fixed wide
  change q = b.target at original
  subst q
  rw [eq] at yes
  change (evaluate s d.keyDomains r.decl.key b.target now).result = .allow at yes
  obtain ⟨f, win, _⟩ := evaluated_provenance yes
  cases empty : (candidates (d.domain r.decl.key) b.target).isEmpty with
  | true => simp [evaluate, known, win, empty] at yes
  | false =>
    simp only [evaluate, known, win, empty, Bool.false_eq_true, ↓reduceIte] at yes
    simp only [targetVerdict] at yes
    split at yes <;> try contradiction
    split at yes
    next live =>
      obtain ⟨c, member, ok⟩ := List.any_eq_true.mp live
      obtain ⟨kind, region⟩ := Bool.and_eq_true_iff.mp ok
      obtain ⟨source, projected, sameKind, samePath, holes⟩ := live_list_geometry wf known stored (sources f win) member
      have cover : coversTarget b.target (candidates (d.domain r.decl.key) b.target) source := by
        simpa only [coversTarget, samePath, holes.any_eq] using region
      exact authorize_wildcard_list method decl singular address outer bound fault targets universal wild filter cap
        stored names (wildcard_region_claim wild cap stored names empty projected (sameKind.trans (beq_iff_eq.mp kind)) cover)
    next =>
      split at yes
      · contradiction
      · split at yes <;> contradiction

/-- For a canonical protected singular request, a definitive client denial
refuses the actual server call at the denying evidence revision. A complete
row adapter discharges pointwise predicate residuals. A ceiling refusal holds
at any revision. Partial items and unresolved aliases are outside this statement. -/
theorem method_offer_refuses (d : Descriptor) (wf : d.WellFormed) (session policy events name request now)
    (opts : ServerOptions) {m : MethodDecl} (method : d.method? name = some m)
    (decl : m.disposition = .requirements) (singular : m.isBatch = false)
    (canonical : ∀ p, SuppliedName request p → opts.names.canonical d.resourcePatterns p = .ok (some p))
    (items : serverBindings d m request opts true = [])
    (pointwise : ∀ r ∈ serverBindings d m request opts false, r.targets ≠ [] ∧
      ∀ pair ∈ r.targets, ConcreteBinding pair.2)
    (reader : opts.factsOf.isSome) :
    let s := projectedTrace d.service session policy d.keyDomains events
    offerRequest d s name request now opts.ceiling (fun _ => some []) opts.guards = .single .deny →
    (∀ rules, (authorizeRequest d name request rules opts).decision = "DENY") ∨
      ∃ b token, (evaluateBinding s d.keyDomains b now).token = some token ∧
        (authorizeRequest d name request (s.policyAt policy token) opts).decision = "DENY" := by
  intro s offer
  obtain ⟨other, found, refusal⟩ := (method_offer_sound d wf session policy events name request
    now opts.ceiling _ opts.guards opts.mode (fun p => opts.available p)).2 offer
  cases Option.some.inj (found.symm.trans method)
  rw [canonical_offer_bindings _ _ _ _ canonical, items, List.append_nil] at refusal
  rcases refusal with ⟨client, member, excluded⟩ | ⟨client, member, b, slot, q, dom, token, x,
    widened, _, atToken, _, matched, cannot, _⟩
  · left
    intro rules
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp member
    obtain ⟨item, hi⟩ := List.exists_mem_of_ne_nil _ (pointwise _ hr).1
    rcases singular_authorization_result method decl singular request rules opts with denied | proceed
    · exact denied
    obtain ⟨pending, checked⟩ := authorizeRequest_outer_accepts method proceed hr hi
    have concrete := ((pointwise _ hr).2 item hi).2
    obtain ⟨_, rfl⟩ := checkTarget_row_complete concrete reader checked
    have cap := (checkTarget_concrete_sound concrete checked {}).1
    change opts.ceiling.permits r.decl.info = false at excluded
    simp [cap] at excluded
  · right
    refine ⟨b, token, atToken, ?_⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp member
    obtain ⟨item, selected, rfl⟩ := List.mem_map.mp slot
    have hi := (List.mem_filter.mp selected).1
    have geometry := (pointwise _ hr).2 item hi
    have atName := widened_concrete (b := {item.2 with key := r.decl.key}) geometry.1 widened
    change q = item.2.target at atName
    subst q
    obtain rfl := matches_concrete geometry.2 matched
    rcases singular_authorization_result method decl singular request (s.policyAt policy token) opts with denied | proceed
    · exact denied
    obtain ⟨pending, checked⟩ := authorizeRequest_outer_accepts method proceed hr hi
    obtain ⟨_, rfl⟩ := checkTarget_row_complete geometry.2 reader checked
    have allows := (checkTarget_concrete_sound geometry.2 checked {}).2
    change decide opts.mode (opts.available item.2.target) (s.policyAt policy token) r.decl.key item.2.target = .deny at cannot
    rw [cannot] at allows
    contradiction

/-- Any real matched name in two opposing claims forces a conflict at every
evaluation time. This includes contexts with different expiration times. -/
theorem conflict_at_name {s : ClientState} {keys key q d f} {a b : Claim} {x : Path}
    (known : keys.lookup key = some d) (wf : ∀ p ∈ d, p.all Atom.valid = true)
    (wins : winner s.history keys q = some f)
    (ca : a ∈ claimsForKey key (latestContexts s.history keys q f.reply.token))
    (cb : b ∈ claimsForKey key (latestContexts s.history keys q f.reply.token))
    (allow : a.kind = .allow) (deny : b.kind = .deny)
    (hx : Domain.contains d x) (hq : matchesQuery q x) (ha : a.covers x) (hb : b.covers x)
    (now : Nat) : (evaluate s keys key q now).result = .unloaded := by
  have nonempty (path : Path) (hp : path <+: x) :
      Domain.nonemptyRegion (candidates d q) path (a.holes ++ b.holes) = true := by
    apply (Domain.nonemptyRegion_iff (candidates_valid wf q)).2
    refine ⟨x, (candidate_matches d q x).2 ⟨hx, hq⟩, hp, ?_⟩
    simp only [Claim.covers, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
      List.isPrefixOf_iff_prefix] at ha hb
    intro hole hh
    rcases List.mem_append.mp hh with h | h
    · exact ha.2 _ h
    · exact hb.2 _ h
  simp only [Claim.covers, Bool.and_eq_true, List.isPrefixOf_iff_prefix] at ha hb
  have intersect : overlapIn (candidates d q) a b := by
    rcases List.prefix_or_prefix_of_prefix ha.1 hb.1 with ab | ba
    · simp [overlapIn, List.isPrefixOf_iff_prefix, ab, nonempty _ hb.1]
    · by_cases ab : a.path <+: b.path <;>
        simp [overlapIn, List.isPrefixOf_iff_prefix, ab, ba, nonempty _ ha.1, nonempty _ hb.1]
  have conflict : anyConflict (candidates d q)
      (claimsForKey key (latestContexts s.history keys q f.reply.token)) := by
    simp only [anyConflict, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact ⟨a, ca, allow, b, cb, deny, intersect⟩
  simp only [evaluate, known, wins]
  split <;> simp_all [targetVerdict]

/-- Every partial-success item uses the same request proof, with its
operation-level requirements included. An operation denial reaches all items. -/
theorem partial_offer_sound {s keys policy} (produced : ProducedState policy keys s)
    (valid : ValidKeyDomains keys) (mode facts ceiling operation items now) (i : Nat) (item : List ActiveRequirement)
    (atIndex : items[i]? = some item) :
    let verdict := (offerPartial s keys ceiling operation items now).items[i]?
    (verdict = some .allow →
      RequestAllowed s keys ceiling (operation ++ item) now policy mode facts) ∧
    (verdict = some .deny →
      RequestDenied s keys ceiling operation now policy mode facts ∨
      RequestDenied s keys ceiling (operation ++ item) now policy mode facts) := by
  dsimp only [offerPartial]
  let op := if operation.isEmpty then Verdict.allow else offer s keys ceiling operation now
  by_cases stopped : (op == .deny || op == .defer) = true
  · simp only [show (if operation.isEmpty then Verdict.allow else offer s keys ceiling operation now) = op
        from rfl, stopped, ↓reduceIte, List.getElem?_map, atIndex, Option.map_some, Option.some.injEq]
    simp only [Bool.or_eq_true, beq_iff_eq] at stopped
    constructor
    · intro unavailable
      rcases stopped with same | same <;> simp_all
    · intro denied
      left
      apply offer_projection_deny policy produced valid mode facts
      dsimp [op] at denied
      split at denied <;> first | contradiction | assumption
  · have ne : items.isEmpty = false := by
      cases items <;> simp_all
    simp only [show (if operation.isEmpty then Verdict.allow else offer s keys ceiling operation now) = op
        from rfl, stopped, Bool.false_eq_true, ↓reduceIte, ne, List.getElem?_map, atIndex,
        Option.map_some, Option.some.injEq]
    cases hi : item.isEmpty
    · simp
      exact ⟨offer_projection_allow policy produced valid mode facts,
        fun h => Or.inr (offer_projection_deny policy produced valid mode facts h)⟩
    · simp

private theorem partial_length (s keys ceiling operation items now) :
    (offerPartial s keys ceiling operation items now).items.length = items.length := by
  unfold offerPartial
  generalize (if operation.isEmpty then Verdict.allow else offer s keys ceiling operation now) = op
  cases op <;> cases items <;> simp

private theorem partial_operation {s keys ceiling operation items now v}
    (definite : v = .allow ∨ v = .deny)
    (h : (offerPartial s keys ceiling operation items now).operation = v) :
    (if operation.isEmpty then Verdict.allow else offer s keys ceiling operation now) = v := by
  unfold offerPartial at h
  generalize (if operation.isEmpty then Verdict.allow else offer s keys ceiling operation now) = op at *
  rcases definite with rfl | rfl <;> cases op <;> cases items <;> simp_all

/-- A partial method result is the evaluation of the actual operation and items
bound from this request, including its selected field guards and upsert branches. -/
theorem method_partial_offer_sound (d : Descriptor) (wf : d.WellFormed)
    (session policy events method request now ceiling unresolved guards mode facts) {result : PartialOffer}
    (offered : offerRequest d (projectedTrace d.service session policy d.keyDomains events)
      method request now ceiling unresolved guards = .partialBatch result) :
    let s := projectedTrace d.service session policy d.keyDomains events
    ∃ m, d.method? method = some m ∧ partialFor m request = true ∧
      let (operation, items) := partialRequirements m (offerBindings d m request unresolved guards) request
      (result.operation = .allow → operation = [] ∨ RequestAllowed s d.keyDomains ceiling operation now policy mode facts) ∧
      (result.operation = .deny → RequestDenied s d.keyDomains ceiling operation now policy mode facts) ∧
      result.items.length = requestItemCount request m.itemContainers ∧
      ∀ (i : Nat) (item : List ActiveRequirement), items[i]? = some item →
        (result.items[i]? = some .allow →
          RequestAllowed s d.keyDomains ceiling (operation ++ item) now policy mode facts) ∧
        (result.items[i]? = some .deny →
          RequestDenied s d.keyDomains ceiling (operation ++ item) now policy mode facts) := by
  dsimp only
  unfold offerRequest at offered
  have partition : (projectedTrace d.service session policy d.keyDomains events).service = d.service :=
    trace_preserves_service _ _
  simp only [Id.run, pure, partition, ↓reduceIte] at offered
  split at offered <;> try contradiction
  split at offered <;> try contradiction
  rename_i m found
  split at offered <;> try contradiction
  split at offered <;> try contradiction
  rename_i selected
  split at offered <;> try contradiction
  cases offered
  have produced := projectedTrace_produced (d.validKeyDomains wf) d.service session policy events
  refine ⟨m, found, by simpa using selected, ?_, ?_, ?_, ?_⟩
  · intro h
    have op := partial_operation (Or.inl rfl) h
    split at op
    · left
      apply List.nil_of_isEmpty
      assumption
    · exact Or.inr (offer_projection_allow policy produced (d.validKeyDomains wf) mode facts op)
  · intro h
    have op := partial_operation (Or.inr rfl) h
    split at op <;> try contradiction
    exact offer_projection_deny policy produced (d.validKeyDomains wf) mode facts op
  · exact (partial_length ..).trans (partialRequirements_count ..)
  · intro i item atIndex
    obtain ⟨yes, no⟩ := partial_offer_sound produced
      (d.validKeyDomains wf) mode facts ceiling _ _ now i item atIndex
    refine ⟨yes, fun h => ?_⟩
    rcases no h with denied | denied
    · rcases denied with ⟨r, hr, rejected⟩ | ⟨r, hr, rejected⟩
      · exact Or.inl ⟨r, List.mem_append_left _ hr, rejected⟩
      · exact Or.inr ⟨r, List.mem_append_left _ hr, rejected⟩
    · exact denied

private theorem partial_item_member {m rs request i item r}
    (atIndex : (partialRequirements m rs request).2[i]? = some item)
    (member : r ∈ rs) (perItem : r.decl.perItem)
    (active : r.unboundItems.contains i || r.targets.any (·.1 == i)) :
    r.forClient (some i) ∈ item := by
  unfold partialRequirements at atIndex
  simp only [List.getElem?_map, Option.map_eq_some_iff] at atIndex
  obtain ⟨j, index, rfl⟩ := atIndex
  obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp index
  have same : i = j := by simpa using eq
  rw [← same]
  apply List.mem_map.mpr
  exact ⟨r, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨member, perItem⟩, active⟩, rfl⟩

/-- The offered item covers every active permission and guard at that index
and every outer requirement. Other items can fail to bind or authorize. -/
theorem method_partial_offer_authorizes (d : Descriptor) (wf : d.WellFormed)
    (session policy events name request now) (opts : ServerOptions)
    (canonical : ∀ p, SuppliedName request p → opts.names.canonical d.resourcePatterns p = .ok (some p))
    (handler : opts.handlerResolvesResiduals)
    {m : MethodDecl} (method : d.method? name = some m) (decl : m.disposition = .requirements)
    (batch : m.isBatch) (address : singularWriterFault d m request opts = false) (i : Nat) (item : List ActiveRequirement) :
    let s := projectedTrace d.service session policy d.keyDomains events
    let rs := offerBindings d m request (fun _ => some []) opts.guards
    let (outer, items) := partialRequirements m rs request
    (∀ r ∈ rs, r.decl.perItem = false → ∀ pair ∈ r.targets, ConcreteBinding pair.2 ∧ opts.rowReadFailed pair.2.target = false) →
    (∀ r ∈ rs, r.decl.perItem = true → ∀ b, (i,b) ∈ r.targets → ConcreteBinding b) →
    ∀ result, offerRequest d s name request now opts.ceiling (fun _ => some []) opts.guards = .partialBatch result →
      items[i]? = some item → result.items[i]? = some .allow →
      ∃ token, BindingsAtToken s d.keyDomains (outer ++ item) now token ∧
        let rules := s.policyAt policy token
        rules.all (d.resourcePatterns.validSite ·.path) → opts.names.rulesAllowed d.resourcePatterns rules →
        let out := authorizeRequest d name request rules opts
        (out.decision = "PROCEED" ∧ out.residuals.any (·.kind == "PARTIAL_BATCH")) ∧
          ∀ r ∈ serverBindings d m request opts true, i ∉ r.unboundItems ∧ ∀ b, (i, b) ∈ r.targets →
            opts.ceiling.permits r.decl.info ∧ decide opts.mode (opts.available b.target) rules r.decl.key b.target = .allow := by
  intro s rs inputs selectedInput result offered atIndex allow
  let outer := (partialRequirements m rs request).1
  obtain ⟨m', found, selected, _, _, _, perItem⟩ := method_partial_offer_sound d wf session policy events
    name request now opts.ceiling _ opts.guards opts.mode (fun p => opts.available p) offered
  have eq : m' = m := Option.some.inj (found.symm.trans method)
  subst m'
  have evidence := (perItem i item atIndex).1 allow
  obtain ⟨token, marked, target, decisions⟩ := realized_permits (opts := opts) evidence
  have member {phase r} (hr : r ∈ serverBindings d m request opts phase) : r ∈ rs := by
    dsimp only [rs]
    rw [canonical_offer_bindings _ _ _ _ canonical]
    cases phase <;> simp_all
  have outerMember {r} (hr : r ∈ serverBindings d m request opts false) : r.forClient none ∈ outer :=
    List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨member hr, by simp [requirementsFor_phase hr]⟩, rfl⟩
  have outerDecisions := decisions (serverBindings d m request opts false)
    (fun r hr => by
      have included := List.mem_append_left item (outerMember hr)
      obtain ⟨fault, bound⟩ := whole_binding_ready evidence included
      have actual := inputs r (member hr) (requirementsFor_phase hr)
      exact ⟨fault, bound, fun pair hp => ⟨(actual pair hp).1.2,
        same_binding_realizes evidence included (by rfl) hp (actual pair hp).1⟩⟩)
    (fun r hr pair hp => (inputs r (member hr) (requirementsFor_phase hr) pair hp).2)
  refine ⟨token, marked, fun store aliases => ⟨authorizeRequest_partial_proceed method decl batch selected address
    store aliases handler outerDecisions, ?_⟩⟩
  intro r hr
  have physical := requirementsFor_phase hr
  have inOffer (active : r.unboundItems.contains i || r.targets.any (·.1 == i)) :=
    List.mem_append_right outer (partial_item_member atIndex (member hr) physical active)
  constructor
  · intro missing
    have missing' : r.unboundItems.contains i := List.contains_iff_mem.mpr missing
    have ready := evidence.choose_spec.1.2 _ (inOffer (Bool.or_eq_true_iff.mpr (Or.inl missing')))
    simp [BoundRequirement.forClient] at ready
    exact ready.1.1.2 missing
  · intro b bound
    have boundAt : r.targets.any (·.1 == i) := List.any_eq_true.mpr ⟨(i,b), bound, by simp⟩
    exact target r b.target (same_binding_realizes evidence (inOffer (Bool.or_eq_true_iff.mpr (Or.inr boundAt)))
      (by simp) bound (selectedInput r (member hr) physical b bound))

namespace SubjectResetExample

private def key := "items.get"
private def keys : KeyDomains := ⟨[(key, [[.lit "items", .var "item"]])], [[.lit "items", .var "item"]]⟩
private def target : Path := ["items", "i"]
private def revision := "shared-revision"
private def service := "items.example"

private def policy : PolicyHistory := fun id =>
  if id = ⟨service, "alice", revision⟩ then [{path := [], keys := [key], effect := .permit}] else []

private def reply (subject : String) : SnapshotReply :=
  projectedReply policy keys ⟨service, "descriptor", subject, revision, 100, .scopedClaims, []⟩
    [[]] (fun _ _ => {})

private def receive (s : ClientState) (subject : String) :=
  acceptSnapshot s (s.dispatch .scopedClaims) (reply subject) 0

/-- Both callers receive the same revision. The accepted subject reset discards
Alice's frame, and the projector issues Bob's denial under his own policy. -/
theorem same_revision_different_subjects :
    let alice := receive {service, session := "session"} "alice"
    let bob := receive alice "bob"
    evaluate alice keys key target 1 = ⟨.allow, some revision⟩ ∧
    evaluate bob keys key target 1 = ⟨.deny, some revision⟩ ∧
    bob.history.map (·.reply.subject) = ["bob"] ∧
    Authz.decide .failClosed {} (alice.policyAt policy revision) key target = .allow ∧
    Authz.decide .failClosed {} (bob.policyAt policy revision) key target = .deny := by
  set_option maxRecDepth 20000 in
    decide +kernel

end SubjectResetExample

end Authz
