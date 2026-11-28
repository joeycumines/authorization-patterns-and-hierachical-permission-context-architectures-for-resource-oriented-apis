import Authz.ClientSafety

namespace Authz

/-- These components belong to the server. ClientState contains only Strings.
The codec is the reference model's example v1 authority/epoch/counter codec. -/
structure Revision where
  authority : String
  epoch : Nat
  counter : Nat
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

def decodeSnapshotToken (token : String) : Option Revision := do
  let ["v1", authority, e, n] := token.splitOn ":" | none
  guard (!authority.isEmpty && !authority.toList.any Char.isWhitespace)
  let epoch ← e.toNat?
  let seq ← n.toNat?
  guard (epoch > 0 && epoch ≤ 9007199254740991 && seq ≤ 9007199254740991)
  return ⟨authority, epoch, seq⟩

structure RevisionServer where
  revision : Revision
  minKnownCounter : Nat := 0
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

inductive FloorStatus where
  | ok | invalidArgument | unavailable
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

def RevisionServer.serves (s : RevisionServer) (floor : Revision) : Bool :=
  floor.authority != s.revision.authority || floor.epoch < s.revision.epoch ||
    (floor.epoch == s.revision.epoch && s.minKnownCounter ≤ floor.counter && floor.counter ≤ s.revision.counter)

def serveWithMinSnapshot (s : RevisionServer) (floor : Option String) : FloorStatus :=
  match floor with
  | none | some "" => .ok
  | some raw => match decodeSnapshotToken raw with
    | none => .invalidArgument
    | some r => if s.serves r then .ok else .unavailable

/-- The deployment retires an old revision authority before its successor
serves. Rank witnesses that external retirement order when authorities differ. -/
def Revision.le (rank : String → Nat) (a b : Revision) : Prop :=
  rank a.authority < rank b.authority ∨
    (a.authority = b.authority ∧ (a.epoch < b.epoch ∨ (a.epoch = b.epoch ∧ a.counter ≤ b.counter)))

theorem Revision.le_refl (rank) (a : Revision) : a.le rank a := by
  simp [Revision.le]

theorem Revision.le_trans {a b c : Revision} {rank} (h : a.le rank b) (j : b.le rank c) : a.le rank c := by
  unfold Revision.le at *
  rcases h with lt | ⟨eq, same⟩ <;> rcases j with lt' | ⟨eq', same'⟩
  · exact Or.inl (Nat.lt_trans lt lt')
  · exact Or.inl (eq' ▸ lt)
  · exact Or.inl (eq ▸ lt')
  · refine Or.inr ⟨eq.trans eq', ?_⟩
    rcases same with _ | ⟨_, _⟩ <;> rcases same' with _ | ⟨_, _⟩ <;> omega

def ConformingReply (rank : String → Nat) (t : SnapshotTicket) (r : SnapshotReply) : Prop :=
  ∃ server : RevisionServer, decodeSnapshotToken r.token = some server.revision ∧
    ∀ floorToken, t.minToken = some floorToken →
      ∃ floor, decodeSnapshotToken floorToken = some floor ∧ server.serves floor ∧
        (floor.authority ≠ server.revision.authority → rank floor.authority < rank server.revision.authority)

private theorem served_later {s : RevisionServer} {floor : Revision}
    (ok : s.serves floor) (fenced : floor.authority ≠ s.revision.authority →
      rank floor.authority < rank s.revision.authority) : floor.le rank s.revision := by
  by_cases same : floor.authority = s.revision.authority
  · apply Or.inr
    refine ⟨same, ?_⟩
    simp [RevisionServer.serves, same] at ok
    rcases ok with lt | ⟨⟨eq, _⟩, count⟩
    · exact Or.inl lt
    · exact Or.inr ⟨eq, count⟩
  · exact Or.inl (fenced same)

theorem accepted_current_floor {s t r n p token}
    (accepted : snapshotAction s t r n p ≠ .discard) (current : s.token = some token) :
    token = r.token ∨ t.minToken = some token := by
  unfold snapshotAction at accepted
  dsimp only at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  next pass =>
    simp [current] at pass
    by_cases same : token = r.token
    · exact Or.inl same
    · exact Or.inr (pass same)

/-- A new subject can be installed only by a request sent at the current floor,
including when the reply itself carries the current revision. -/
theorem accepted_subject_change_floor {s t r n p token who}
    (accepted : snapshotAction s t r n p ≠ .discard)
    (current : s.token = some token) (established : s.subject = some who)
    (changed : who ≠ r.subject) : t.minToken = some token ∧ token ≠ "" := by
  by_cases floor : t.minToken = some token
  · refine ⟨floor, fun empty => accepted ?_⟩
    simp [snapshotAction, current, established, changed, floor, empty]
  · exact False.elim (accepted (by simp [snapshotAction, current, established, changed, floor]))

theorem stale_subject_change_preserves_state {s t r n p token who}
    (current : s.token = some token) (established : s.subject = some who)
    (changed : who ≠ r.subject) (stale : t.minToken ≠ some token) :
    acceptSnapshot s t r n p = s := by
  by_cases discard : snapshotAction s t r n p = .discard
  · simp [acceptSnapshot, discard]
  · exact False.elim (stale (accepted_subject_change_floor discard current established changed).1)

theorem accepted_revision_order {s t r n p raw old rank}
    (accepted : snapshotAction s t r n p ≠ .discard) (current : s.token = some raw)
    (decoded : decodeSnapshotToken raw = some old) (server : ConformingReply rank t r) :
    ∃ next, decodeSnapshotToken r.token = some next ∧ old.le rank next := by
  rcases server with ⟨replica, produces, floors⟩
  refine ⟨_, produces, ?_⟩
  rcases accepted_current_floor accepted current with eq | sent
  · have eq' : old = replica.revision := Option.some.inj ((eq ▸ decoded).symm.trans produces)
    exact eq' ▸ Revision.le_refl _ _
  · obtain ⟨floor, dec, served, fence⟩ := floors _ sent
    have eq' : old = floor := Option.some.inj (decoded.symm.trans dec)
    exact eq' ▸ served_later served fence

/-- Within this sign-in, the current revision and every intersecting snapshot
accepted since the barrier must be at or above the revision it established. -/
structure RevisionBarrier (rank : String → Nat) (rev : Revision) (floor : Nat) (s : ClientState) : Prop where
  current : ∃ token parsed, s.token = some token ∧ decodeSnapshotToken token = some parsed ∧ rev.le rank parsed
  retained : ∀ f ∈ s.history, floor ≤ f.serial →
    ∃ parsed, decodeSnapshotToken f.reply.token = some parsed ∧ rev.le rank parsed

theorem revisionBarrier_receive {s r t now p rank rev floor}
    (h : RevisionBarrier rank rev floor s) (ok : ConformingReply rank t r) :
    RevisionBarrier rank rev floor (acceptSnapshot s t r now p) := by
  by_cases ignored : snapshotAction s t r now p = .discard
  · simpa [acceptSnapshot, ignored] using h
  · obtain ⟨token, old, current, dec, lower⟩ := h.current
    obtain ⟨newer, denotes, increasing⟩ := accepted_revision_order ignored current dec ok
    have ordered := Revision.le_trans lower increasing
    refine ⟨⟨r.token, newer, by simp [acceptSnapshot, ignored], denotes, ordered⟩, ?_⟩
    intro f hf bound
    simp only [acceptSnapshot, ignored, beq_iff_eq, ↓reduceIte, List.mem_cons] at hf
    rcases hf with rfl | past
    · exact ⟨_, denotes, ordered⟩
    · split at past <;> try contradiction
      exact h.retained f past bound

def ConformingEvent (rank : String → Nat) : ClientEvent → Prop
  | .receive t r _ _ => ConformingReply rank t r
  | .elapse => True
  | .signIn _ => False

theorem revisionBarrier_trace {s rank rev floor} (h : RevisionBarrier rank rev floor s)
    (events : List ClientEvent) (proper : ∀ e ∈ events, ConformingEvent rank e) :
    RevisionBarrier rank rev floor (runTrace s events) := by
  induction events generalizing s with
  | nil => exact h
  | cons e es ih =>
    refine ih ?_ (fun x hx => proper _ (by simp [hx]))
    have ok := proper e (by simp)
    cases e with
    | receive => exact revisionBarrier_receive h ok
    | elapse => exact h
    | signIn => exact False.elim ok

theorem no_older_revision_allow {s rank rev floor keys q key now}
    (h : RevisionBarrier rank rev floor s) (selected : SelectionFloor floor keys q s)
    (events : List ClientEvent) (proper : ∀ e ∈ events, ConformingEvent rank e)
    (allow : (evaluate (runTrace s events) keys key q now).result = .allow) :
    ∃ token parsed, (evaluate (runTrace s events) keys key q now).token = some token ∧
      decodeSnapshotToken token = some parsed ∧ rev.le rank parsed := by
  obtain ⟨f, recent, wins, token⟩ := no_resurrected_allow selected events allow
  obtain ⟨parsed, decode, bound⟩ := (revisionBarrier_trace h events proper).retained f
    (List.mem_of_find?_eq_some wins) recent
  exact ⟨_, parsed, token, decode, bound⟩

def SerialsBounded (s : ClientState) := ∀ frame ∈ s.history, frame.serial ≤ s.serial

theorem accepted_serials_bounded {s : ClientState} (hs : SerialsBounded s) (t r n p) :
    SerialsBounded (acceptSnapshot s t r n p) := by
  unfold SerialsBounded
  dsimp [acceptSnapshot]
  split
  · exact hs
  · intro frame hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | past
    · exact Nat.le_refl _
    · split at past <;> try contradiction
      exact Nat.le_succ_of_le (hs _ past)

theorem trace_serials_bounded {s : ClientState} (hs : SerialsBounded s) (events) :
    SerialsBounded (runTrace s events) := by
  induction events generalizing s with
  | nil => exact hs
  | cons e es ih =>
    apply ih
    cases e with
    | receive => exact accepted_serials_bounded hs _ _ _ _
    | elapse => exact hs
    | signIn => simp [SerialsBounded, ClientEvent.apply]

theorem covering_revision_barrier {s : ClientState} (bounded : SerialsBounded s)
    {t r n p rank rev} (accept : snapshotAction s t r n p ≠ .discard)
    (decoded : decodeSnapshotToken r.token = some rev) :
    RevisionBarrier rank rev (s.serial + 1) (acceptSnapshot s t r n p) := by
  refine ⟨⟨r.token, rev, by simp [acceptSnapshot, accept], decoded, Revision.le_refl ..⟩, ?_⟩
  intro f hf recent
  simp only [acceptSnapshot, beq_iff_eq, accept, ↓reduceIte, List.mem_cons] at hf
  rcases hf with rfl | past
  · exact ⟨_, decoded, Revision.le_refl ..⟩
  · split at past <;> try contradiction
    have := bounded _ past
    omega

/-- Once an accepted reply covers a target at rev, even an interior part of a
wildcard, every later ALLOW uses rev or a newer revision. Both local and server
order follow from the receipt. Subsequent replies may arrive in any order. -/
theorem revocation_never_rolls_back {s : ClientState} (bounded : SerialsBounded s)
    {t r n p keys q rank rev} (accept : snapshotAction s t r n p ≠ .discard)
    (covers : (Frame.mk (s.serial + 1) r |>.intersecting keys q).isEmpty = false)
    (decoded : decodeSnapshotToken r.token = some rev) (events : List ClientEvent)
    (proper : ∀ e ∈ events, ConformingEvent rank e) (key now) :
    let final := runTrace (acceptSnapshot s t r n p) events
    (evaluate final keys key q now).result = .allow →
    ∃ token parsed, (evaluate final keys key q now).token = some token ∧
      decodeSnapshotToken token = some parsed ∧ rev.le rank parsed :=
  no_older_revision_allow (covering_revision_barrier bounded accept decoded)
    (covering_reply_establishes_floor _ _ _ _ _ _ _ accept covers) events proper

theorem old_session_discard {s : ClientState} {t : SnapshotTicket} {r n p} (old : t.session ≠ s.session) :
    acceptSnapshot s t r n p = s := by
  simp [acceptSnapshot, snapshotAction, old]

theorem sign_in_clears_history (s : ClientState) (fresh : String) :
    ((ClientEvent.signIn fresh).apply s).history = [] := rfl

end Authz
