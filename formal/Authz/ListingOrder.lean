import Authz.ClientSafety

namespace Authz

/-- Deduplication keeps the first representative of a given key. In particular,
it comes no later in the input than the witness supplied by the caller. -/
private theorem firstRepresentative [BEq β] [LawfulBEq β] (key : α → β)
    (before : List α) (w : α) (after : List α) :
    ∃ x ∈ (before ++ w :: after).eraseDupsBy (fun a b => key a == key b),
      key x = key w ∧ (x = w ∨ x ∈ before) := by
  match before with
  | [] => exact ⟨w, by simp [List.eraseDupsBy_cons], rfl, Or.inl rfl⟩
  | h :: tail =>
    rw [List.cons_append, List.eraseDupsBy_cons]
    by_cases hit : key h = key w
    · exact ⟨h, List.mem_cons_self, hit, Or.inr List.mem_cons_self⟩
    · let keep := fun a => (key a == key h) = false
      have keepW : keep w := by simp [keep, Ne.symm hit]
      obtain ⟨x, mem, same, origin⟩ := firstRepresentative key (tail.filter keep) w (after.filter keep)
      refine ⟨x, List.mem_cons_of_mem _ ?_, same, origin.imp_right (fun m => List.mem_cons_of_mem _ (List.mem_filter.mp m).1)⟩
      simpa [List.filter_append, List.filter_cons, keep, Ne.symm hit] using mem
termination_by before.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

/-- Refreshing an anchor in the same token can replace its claims or expiry,
but that anchor stays present when the client checks for supersession. -/
private theorem anchor_remains {s : ClientState} {keys : KeyDomains} {f : Frame} {ctx : ClientContext} (stored : f ∈ s.history)
    (selected : ctx ∈ f.selectContexts keys (fun _ => true)) :
    ∃ c ∈ latestMatching s.history keys (fun _ => true) f.reply.token, c.context.anchor = ctx.anchor := by
  unfold latestMatching
  let timed := TimedContext.mk ctx (ctx.expires.elim f.reply.expires (min f.reply.expires)) f.reply.profile
  have mem : timed ∈ s.history.flatMap (fun g => if g.reply.token == f.reply.token then
      (g.selectContexts keys (fun _ => true)).map (fun c =>
        TimedContext.mk c (c.expires.elim g.reply.expires (min g.reply.expires)) g.reply.profile) else []) := by
    exact List.mem_flatMap.mpr ⟨f, stored, by simp only [beq_self_eq_true, ↓reduceIte]; exact List.mem_map.mpr ⟨ctx, selected, rfl⟩⟩
  obtain ⟨pre, post, eq⟩ := List.append_of_mem mem
  rw [eq]
  obtain ⟨x, keep, same, _⟩ := firstRepresentative (fun c : TimedContext => c.context.anchor) pre timed post
  exact ⟨x, keep, same⟩

theorem trace_bounds_frame_serial (s : ClientState) (events : List ClientEvent)
    (initial : ∀ f ∈ s.history, f.serial ≤ s.serial) :
    ∀ f ∈ (runTrace s events).history, f.serial ≤ (runTrace s events).serial := by
  induction events generalizing s with
  | nil => exact initial
  | cons e rest ih =>
    apply ih
    cases e with
    | elapse => exact initial
    | signIn => simp [ClientEvent.apply]
    | receive t r n p =>
      by_cases discard : snapshotAction s t r n p = .discard
      · simpa [ClientEvent.apply, acceptSnapshot, discard] using initial
      · simp only [ClientEvent.apply, acceptSnapshot, beq_iff_eq, discard, ↓reduceIte]
        intro f stored
        rcases List.mem_cons.mp stored with rfl | past
        · exact Nat.le_refl _
        · split at past
          · exact False.elim (List.not_mem_nil past)
          · exact Nat.le_succ_of_le (initial f past)

private def RetiredListing (floor : Nat) (old : String) (barrier : Frame) (s : ClientState) : Prop :=
  floor ≤ s.serial ∧
  (∀ f ∈ s.history, f.reply.token = old → f.serial < floor) ∧
  ((∀ f ∈ s.history, f.reply.token ≠ old) ∨
    ∃ pre post, s.history = pre ++ barrier :: post ∧ ∀ f ∈ pre, floor ≤ f.serial)

/-- The server may publish new revisions, merge the current revision, and
reset the subject. An accepted return to the retired token requires a separate
revision-order guarantee from the server. Discarded replies are harmless. -/
private def preservesRetirement (old : String) (s : ClientState) : ClientEvent → Prop
  | .receive t r n p => snapshotAction s t r n p = .discard ∨ r.token ≠ old
  | _ => True

private theorem retired_step {old floor barrier s} (safe : RetiredListing floor old barrier s)
    (event : ClientEvent) (order : preservesRetirement old s event) :
    RetiredListing floor old barrier (event.apply s) := by
  rcases safe with ⟨bound, serials, cover⟩
  cases event with
  | elapse => exact ⟨bound, serials, cover⟩
  | signIn => exact ⟨bound, by simp [ClientEvent.apply], Or.inl (by simp [ClientEvent.apply])⟩
  | receive t r n p =>
    by_cases discard : snapshotAction s t r n p = .discard
    · simpa [ClientEvent.apply, acceptSnapshot, discard] using (show RetiredListing floor old barrier s from ⟨bound, serials, cover⟩)
    · have other := order.resolve_left discard
      simp only [ClientEvent.apply, acceptSnapshot, beq_iff_eq, discard, ↓reduceIte, RetiredListing]
      refine ⟨Nat.le_succ_of_le bound, ?_, ?_⟩
      · intro f mem same
        rcases List.mem_cons.mp mem with rfl | past
        · exact False.elim (other same)
        · split at past <;> simp_all
      · split
        · exact Or.inl (by simpa using other)
        · rcases cover with gone | ⟨pre, post, eq, recent⟩
          · exact Or.inl (by simpa [other] using gone)
          · exact Or.inr ⟨_ :: pre, post, congrArg (_ :: ·) eq, by simpa [Nat.le_succ_of_le bound] using recent⟩

/-- A retired token can appear in a late discarded reply. It must never be
accepted as a fresh revision after the barrier. -/
def ClientEvent.orderedAfter (old : String) (s : ClientState) : List ClientEvent → Prop
  | [] => True
  | e :: rest => preservesRetirement old s e ∧ orderedAfter old (e.apply s) rest

private theorem retired_trace {s old barrier floor} (safe : RetiredListing floor old barrier s)
    (events : List ClientEvent) (ordered : ClientEvent.orderedAfter old s events) :
    RetiredListing floor old barrier (runTrace s events) := by
  induction events generalizing s with
  | nil => exact safe
  | cons e rest ih => exact ih (retired_step safe e ordered.1) ordered.2

/-- After an accepted newer reply covers a region, no listing of that region
from the retired token can return at any later time on an ordered trace. -/
theorem usableRegions_no_resurrection (s : ClientState) (t r now profile keys key d)
    (known : keys.lookup key = some d) (old : String) (changed : r.token ≠ old)
    (serials : ∀ f ∈ s.history, f.serial ≤ s.serial)
    (accept : snapshotAction s t r now profile ≠ .discard)
    (ctx : ClientContext) (valid : ctx ∈ (Frame.mk (s.serial + 1) r).selectContexts keys (fun _ => true))
    (events : List ClientEvent) (ordered : ClientEvent.orderedAfter old (acceptSnapshot s t r now profile) events)
    (later maximum) (region : ListedRegion) (token : region.token = old)
    (hit : d.any (Pattern.reach · ctx.anchor) &&
      (ctx.anchor.isPrefixOf region.claim.path ||
        (region.claim.path.isPrefixOf ctx.anchor && Domain.nonemptyRegion d ctx.anchor region.claim.holes))) :
    region ∉ usableRegions (runTrace (acceptSnapshot s t r now profile) events) keys key later maximum := by
  let barrier := Frame.mk (s.serial + 1) r
  have start : RetiredListing (s.serial + 1) old barrier (acceptSnapshot s t r now profile) := by
    simp only [RetiredListing, acceptSnapshot, beq_iff_eq, accept, ↓reduceIte, Nat.le_refl, true_and]
    constructor
    · intro f mem same
      rcases List.mem_cons.mp mem with rfl | past
      · contradiction
      · split at past <;> simp_all [Nat.lt_succ_iff]
    · exact Or.inr ⟨[], _, rfl, by simp⟩
  let last := runTrace (acceptSnapshot s t r now profile) events
  obtain ⟨_, older, cover⟩ := retired_trace start events ordered
  intro listed
  simp only [usableRegions, known] at listed
  obtain ⟨f, member, entry⟩ := List.mem_flatMap.mp (dedup_subset listed)
  obtain ⟨claim, permitted, eq⟩ := List.mem_map.mp entry
  subst region
  have stored : f ∈ last.history := (List.mem_filter.mp (dedup_subset member)).1
  rcases cover with gone | ⟨pre, post, history, recent⟩
  · exact gone f stored token
  · have mem : ctx ∈ barrier.selectContexts keys (fun _ => true) := valid
    let nonempty := fun g : Frame => !(g.selectContexts keys (fun _ => true)).isEmpty
    have has : nonempty barrier = true := by simpa [nonempty, List.isEmpty_iff] using List.ne_nil_of_mem mem
    obtain ⟨newer, inList, tag, origin⟩ :=
      firstRepresentative (fun g : Frame => g.reply.token) (pre.filter nonempty) barrier (post.filter nonempty)
    have newerListed : newer ∈ listingFrames last keys := by
      unfold listingFrames
      rw [show last.history = _ from history, List.filter_append, List.filter_cons]
      simpa [nonempty, has] using inList
    have newerSerial : s.serial + 1 ≤ newer.serial := origin.elim (fun eq => eq ▸ Nat.le_refl _)
      (fun m => recent _ (List.mem_filter.mp m).1)
    have retiredSerial := older f stored token
    obtain ⟨c, seen, anchor⟩ := anchor_remains (s := last) (f := barrier)
      (by rw [show last.history = _ from history]; simp) mem
    have replaced : listingSuperseded last keys d f claim := by
      apply List.any_eq_true.mpr
      refine ⟨newer, newerListed, Bool.and_eq_true_iff.mpr ⟨by simpa using Nat.lt_of_lt_of_le retiredSerial newerSerial, ?_⟩⟩
      apply List.any_eq_true.mpr
      exact ⟨c, tag ▸ seen, by simpa [anchor] using hit⟩
    have denied := (List.mem_filter.mp permitted).2
    simp [show listingSuperseded last keys d f claim = true from replaced, last] at denied

end Authz
