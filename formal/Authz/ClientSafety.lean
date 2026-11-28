import Authz.Client

namespace Authz

inductive ClientEvent where
  | receive (ticket : SnapshotTicket) (reply : SnapshotReply) (now : Nat) (maxProfile : Profile)
  | elapse
  | signIn (session : String)
  deriving Repr, Lean.FromJson, Lean.ToJson

def ClientEvent.apply (s : ClientState) : ClientEvent → ClientState
  | .receive t r n p => acceptSnapshot s t r n p
  | .elapse => s
  | .signIn session => { service := s.service, session, serial := s.serial }

def runTrace (s : ClientState) (events : List ClientEvent) :=
  events.foldl ClientEvent.apply s

theorem stale_generation_discard {s : ClientState} {t : SnapshotTicket}
    (h : t.generation ≠ s.generation) (r n p) : acceptSnapshot s t r n p = s := by
  simp [acceptSnapshot, snapshotAction, h]

theorem foreign_or_expired_reply_discard {s : ClientState} {r : SnapshotReply} {now : Nat}
    (h : r.service ≠ s.service ∨ r.expires ≤ now) (t p expected) : acceptSnapshot s t r now p expected = s := by
  rcases h with h | h <;> simp [acceptSnapshot, snapshotAction, h]

/-- A canonical anchor can occur only once. Each requested name can belong
to only one context, including when those contexts have no claims. -/
theorem duplicate_context_identity_discard {s : ClientState} {r : SnapshotReply} (name : Path)
    (duplicate :
      let contexts := r.contexts.filter fun c => pathOk c.anchor
      1 < (contexts.map (·.anchor)).count name ∨
      1 < (contexts.flatMap fun c =>
        (c.requestedAnchors.filter (·.all pathOk)).toList.flatMap List.eraseDups).count name)
    (t now profile expected) : acceptSnapshot s t r now profile expected = s := by
  have invalid : r.uniqueContexts = false := by
    apply Bool.eq_false_iff.mpr
    intro valid
    obtain ⟨canonical, requested⟩ := Bool.and_eq_true_iff.mp valid
    rcases duplicate with h | h
    · exact (Nat.not_lt_of_ge ((List.nodup_iff_count.mp (of_decide_eq_true canonical)) name)) h
    · exact (Nat.not_lt_of_ge ((List.nodup_iff_count.mp (of_decide_eq_true requested)) name)) h
  simp [acceptSnapshot, snapshotAction, invalid]

theorem dispatch_service_or_ceiling_discard {t : SnapshotTicket} {r : SnapshotReply}
    (mismatch : (∃ service, t.service = some service ∧ service ≠ r.service) ∨
      (t.maxProfile = .grantShaped ∧ r.profile = .scopedClaims)) (s now ceiling expected) :
    acceptSnapshot s t r now ceiling expected = s := by
  rcases mismatch with ⟨service, bound, foreign⟩ | ⟨cap, above⟩
  · simp [acceptSnapshot, snapshotAction, bound, foreign]
  · simp [acceptSnapshot, snapshotAction, cap, above]

theorem trace_preserves_service (s : ClientState) (events : List ClientEvent) :
    (runTrace s events).service = s.service := by
  induction events generalizing s with
  | nil => rfl
  | cons e es ih =>
    change (runTrace (e.apply s) es).service = _
    rw [ih]
    cases e with
    | receive t r n p => simp [ClientEvent.apply, acceptSnapshot]; split <;> rfl
    | elapse | signIn => rfl

/-- Any selected snapshot in this state was accepted no earlier than the
barrier. No winning snapshot also satisfies the property. -/
private def selectedFrame (history : List Frame) (keys : KeyDomains) (hits : Path → Bool) :=
  history.find? fun f => !(f.selectContexts keys hits).isEmpty

private def MatchingFloor (floor : Nat) (keys : KeyDomains) (hits : Path → Bool) (s : ClientState) : Prop :=
  floor ≤ s.serial ∧ ∀ f, selectedFrame s.history keys hits = some f → floor ≤ f.serial

def SelectionFloor (floor : Nat) (keys : KeyDomains) (q : Path) (s : ClientState) : Prop :=
  floor ≤ s.serial ∧ ∀ f, winner s.history keys q = some f → floor ≤ f.serial

private theorem floor_cons {floor : Nat} {keys : KeyDomains} {hits : Path → Bool}
    {f : Frame} {past : List Frame} (recent : floor ≤ f.serial)
    (prior : ∀ x, selectedFrame past keys hits = some x → floor ≤ x.serial) :
    ∀ x, selectedFrame (f :: past) keys hits = some x → floor ≤ x.serial := by
  intro x found
  rw [selectedFrame, List.find?_cons_eq_some] at found
  rcases found with ⟨_, rfl⟩ | ⟨_, hx⟩
  · exact recent
  · exact prior _ hx

private theorem matchingFloor_step {floor keys hits s} (safe : MatchingFloor floor keys hits s) (e : ClientEvent) :
    MatchingFloor floor keys hits (e.apply s) := by
  rcases safe with ⟨bound, prior⟩
  cases e with
  | elapse => exact ⟨bound, prior⟩
  | signIn => exact ⟨bound, by simp [ClientEvent.apply, selectedFrame]⟩
  | receive t r n p =>
    dsimp [ClientEvent.apply, acceptSnapshot]
    split
    · exact ⟨bound, prior⟩
    · refine ⟨Nat.le_succ_of_le bound, floor_cons (Nat.le_succ_of_le bound) ?_⟩
      split
      · simp [selectedFrame]
      · exact prior

theorem selectionFloor_step {floor keys q s} (safe : SelectionFloor floor keys q s) (e : ClientEvent) :
    SelectionFloor floor keys q (e.apply s) :=
  matchingFloor_step (hits := (intersectsTarget · q)) safe e

/-- Starting when a newer reply first covers a point (possibly an interior
anchor of a wildcard), arbitrary later events can select only that reply or a
newer one. Time never removes coverage from winner selection. -/
theorem no_resurrection {floor keys q s} (safe : SelectionFloor floor keys q s) (events : List ClientEvent) :
    SelectionFloor floor keys q (runTrace s events) := by
  induction events generalizing s with
  | nil => exact safe
  | cons e es ih => exact ih (selectionFloor_step safe e)

theorem covering_reply_establishes_floor (s : ClientState) (t r now profile keys q)
    (accept : snapshotAction s t r now profile ≠ .discard)
    (covers : (Frame.mk (s.serial + 1) r |>.intersecting keys q).isEmpty = false) :
    SelectionFloor (s.serial + 1) keys q (acceptSnapshot s t r now profile) := by
  simp [SelectionFloor, acceptSnapshot, accept, winner, covers]

/-- A covering scope reply establishes a floor even if it subsequently expires. -/
theorem scope_no_resurrection (s : ClientState) (t r now profile keys d scope)
    (accept : snapshotAction s t r now profile ≠ .discard)
    (covers : ((Frame.mk (s.serial + 1) r).selectContexts keys (reachesScope d scope)).isEmpty = false)
    (events : List ClientEvent) :
    ∀ f, scopeWinner (runTrace (acceptSnapshot s t r now profile) events).history keys d scope = some f →
      s.serial + 1 ≤ f.serial := by
  have start : MatchingFloor (s.serial + 1) keys (reachesScope d scope) (acceptSnapshot s t r now profile) := by
    simp [MatchingFloor, selectedFrame, acceptSnapshot, accept, covers]
  have keep {state : ClientState} (h : MatchingFloor (s.serial + 1) keys (reachesScope d scope) state)
      (es : List ClientEvent) : MatchingFloor (s.serial + 1) keys (reachesScope d scope) (runTrace state es) := by
    induction es generalizing state with
    | nil => exact h
    | cons e es ih => exact ih (matchingFloor_step h e)
  exact (keep start events).2

theorem scope_conflict_survives_expiry {s keys key d scope f} (known : keys.lookup key = some d)
    (wins : scopeWinner s.history keys d scope = some f)
    (conflict : scopeConflict d scope (claimsForKey key
      (latestMatching s.history keys (reachesScope d scope) f.reply.token))) (now : Nat)
    (maximum : Option Profile := some .scopedClaims) :
    (evaluateScope s keys key scope now maximum).result = .unloaded := by
  simp [evaluateScope, known, wins, scopeVerdict, conflict]
  split <;> rfl

/-- The contradiction check reads the latest context at each anchor before
filtering by expiry, hence remains decisive at every later time. -/
theorem conflict_survives_expiry {s : ClientState} {keys key q d f}
    (known : keys.lookup key = some d) (wins : winner s.history keys q = some f)
    (conflict : anyConflict (candidates d q)
      (claimsForKey key (latestContexts s.history keys q f.reply.token)) = true)
    (now : Nat) (maximum : Option Profile := some .scopedClaims) : (evaluate s keys key q now maximum).result = .unloaded := by
  simp only [evaluate, known, wins]
  split <;> simp_all [targetVerdict]

theorem scoped_claims_cannot_prove_grant_shaped {contexts : List TimedContext}
    (allScoped : ∀ c ∈ contexts, c.profile = .scopedClaims) (key q d now) :
    targetVerdict key q d contexts now (some .grantShaped) = .unloaded ∧
    scopeVerdict key q d contexts now (some .grantShaped) = .unloaded := by
  have empty : contexts.filter (TimedContext.usable now (some .grantShaped)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro c hc
    simp [TimedContext.usable, allScoped c hc]
  simp [targetVerdict, scopeVerdict, empty, claimsForKey]

theorem combined_allow_one_snapshot {xs : List Evidence} (h : combine xs = .allow) :
    ∃ token : String, xs ≠ [] ∧ ∀ e ∈ xs, e.result = .allow ∧ e.token = some token := by
  unfold combine at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases xs with
  | nil => contradiction
  | cons e es =>
    dsimp only at h
    split at h <;> try contradiction
    next ok =>
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ok
      obtain ⟨token, ht⟩ := Option.isSome_iff_exists.mp ok.1
      exact ⟨token, by simp, fun x hx => ⟨(ok.2 _ hx).1, (ok.2 _ hx).2.trans ht⟩⟩

theorem offer_allow_one_snapshot {s keys ceiling rs now maximum} (h : offer s keys ceiling rs now maximum = .allow) :
    ∃ token : String, (rs.flatMap (·.targets)) ≠ [] ∧
      ∀ r ∈ rs, ∀ t ∈ r.targets, evaluateBinding s keys t now maximum = ⟨.allow, some token⟩ := by
  unfold offer at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  obtain ⟨token, hn, he⟩ := combined_allow_one_snapshot h
  refine ⟨token, ?_, ?_⟩
  · intro hempty
    exact hn (by simp [hempty])
  · intro r hr t ht
    have mem : evaluateBinding s keys t now maximum ∈
        ((rs.flatMap (·.targets)).map fun x => evaluateBinding s keys x now maximum) :=
      List.mem_map_of_mem (List.mem_flatMap.2 ⟨r, hr, ht⟩)
    obtain ⟨allow, tok⟩ := he _ mem
    cases eq : evaluateBinding s keys t now maximum with
    | mk result token' => simp_all

theorem evaluated_provenance {s keys key q now maximum} (h : (evaluate s keys key q now maximum).result = .allow) :
    ∃ f, winner s.history keys q = some f ∧ (evaluate s keys key q now maximum).token = some f.reply.token := by
  cases known : keys.lookup key <;> cases wins : winner s.history keys q <;>
    simp [evaluate, known, wins] at h ⊢
  split at h <;> simp_all

theorem no_resurrected_allow {floor keys q s} (safe : SelectionFloor floor keys q s)
    (events : List ClientEvent) {key now}
    (h : (evaluate (runTrace s events) keys key q now).result = .allow) :
    ∃ f, floor ≤ f.serial ∧ winner (runTrace s events).history keys q = some f ∧
      (evaluate (runTrace s events) keys key q now).token = some f.reply.token := by
  obtain ⟨f, wins, tok⟩ := evaluated_provenance h
  exact ⟨f, (no_resurrection safe events).2 _ wins, wins, tok⟩

end Authz
