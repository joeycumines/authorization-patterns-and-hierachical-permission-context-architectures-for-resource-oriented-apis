import Authz.GroupedWire

namespace Authz.GroupedReply
open Lean Query

private theorem forIn_preserves {m : Type → Type} [Monad m] [LawfulMonad m]
    (xs : List α) (init : β) (step : α → β → m (ForInStep β))
    (stable : ∀ x ∈ xs, step x init = pure (.yield init)) :
    forIn xs init step = pure init := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, stable x List.mem_cons_self, pure_bind]
    exact ih (fun a ha => stable a (List.mem_cons_of_mem _ ha))

private theorem fields_canonical (obj : Std.TreeMap.Raw String Json compare)
    (aliases : List (String × String)) (nullable : List String)
    (missing : ∀ x ∈ aliases, obj.get? x.2 = none)
    (populated : ∀ n ∈ nullable, obj.get? n ≠ some Json.null) :
    fields (.obj obj) true aliases nullable = .ok (.obj obj) := by
  simp only [fields, Json.getObj?, pure_bind, ↓reduceIte]
  rw [forIn_preserves aliases obj _ (by
    intro ⟨k, n⟩ mem
    have h : obj.get? n = none := missing (k,n) mem
    simp only [h])]
  simp only [pure_bind]
  rw [forIn_preserves nullable obj _ (by
    intro n mem
    split
    · rename_i h
      exact False.elim (populated n mem h)
    · rfl)]
  rfl

private theorem top_fields (r : Response) : groupedFields r.protoJson true = .ok r.protoJson := by
  apply fields_canonical
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    rfl
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl <;> intro h <;> cases h

private theorem context_fields (c : WireContext) : contextFields c.protoJson true = .ok c.protoJson := by
  apply fields_canonical
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rfl
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · change some (wireAnchor c.anchor) ≠ some Json.null
      unfold wireAnchor
      split <;> intro h <;> cases h
    all_goals intro h; cases h

private theorem claim_fields (g : WireClaim) :
    fields g.protoJson true [("keySet","key_set")] ["scope","keySet","kind","holes"] = .ok g.protoJson := by
  apply fields_canonical
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    rfl
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · change some (wireScope g.scope) ≠ some Json.null
      cases g.scope <;> intro h <;> cases h
    all_goals intro h; cases h

private theorem key_fields (ks : KeySet) :
    fields (toJson ks) true [] ["keys","id"] = .ok (toJson ks) := by
  apply fields_canonical
  · simp
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl <;> intro h <;> cases h

private theorem scope_fields (s : Scope) :
    fields (wireScope s) true [("serviceRoot","service_root")] ["serviceRoot","collection","resource"] =
      .ok (wireScope s) := by
  cases s <;> apply fields_canonical
  all_goals first
    | intro x hx; simp only [List.mem_singleton] at hx; subst x; rfl
    | intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl <;> intro h <;> cases h

private theorem natural_canonical (n : Nat) (bound : n ≤ 2147483647) : natural (toJson n) true = some n := by
  have inside : (n : Int) ≤ 2147483647 := by omega
  change natural (.num ⟨n,0⟩) true = some n
  simp [natural, Json.getNum?, Except.toOption, pure, Except.pure, inside]

private theorem canonical_path (p : Path) (valid : pathOk p) (nonempty : p ≠ []) :
    ((("/".intercalate p).split '/').toList.map (·.copy)) = p := by
  have clean (s : String) (mem : s ∈ p) : '/' ∉ s.toList := by
    have good := List.all_eq_true.mp valid s mem
    have chars := (Bool.and_eq_true_iff.mp good).2
    intro slash
    have check := List.all_eq_true.mp chars '/' slash
    contradiction
  exact (String.toList_split_intercalate clean).trans (by simp [nonempty])

private theorem list_payload [ToJson α] (xs : List α) :
    toJson xs = .arr (xs.map toJson).toArray := by
  change Json.arr (xs.toArray.map toJson) = _
  simp

private theorem array_decode [FromJson α] (xs : List β) (emit : β → Json) (get : β → α)
    (read : ∀ x ∈ xs, fromJson? (emit x) = .ok (get x)) :
    fromJson? (Json.arr (xs.map emit).toArray) = .ok (xs.map get) := by
  change Except.map Array.toList ((xs.map emit).toArray.mapM fromJson?) = _
  have h : (xs.map emit).mapM fromJson? = (Except.ok (xs.map get) : Except String _) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.mapM_cons, read x List.mem_cons_self,
        ih (fun y hy => read y (List.mem_cons_of_mem _ hy))]
      rfl
  rw [List.mapM_toArray, h]
  rfl

private theorem repeated_canonical [FromJson α] (j : Json) (name : String) (xs : List β)
    (emit : β → Json) (get : β → α)
    (field : j.getObjVal? name = .ok (.arr (xs.map emit).toArray))
    (nonNull : ∀ x ∈ xs, emit x ≠ .null)
    (read : ∀ x ∈ xs, fromJson? (emit x) = .ok (get x)) :
    repeated j name true = .ok (xs.map get) := by
  let isNull : Json → Bool := fun | .null => true | _ => false
  have clean : (xs.map emit).toArray.any isNull = false := by
    simp only [List.any_toArray, List.any_eq_false, List.mem_map, forall_exists_index, and_imp]
    intro j x mem eq
    subst j
    cases h : emit x <;> simp [isNull] <;> exact False.elim (nonNull x mem h)
  simp only [repeated, field, Json.getArr?, pure_bind, Bool.true_and]
  change (do
    if (xs.map emit).toArray.any isNull then throw _
    return ← fromJson? (Json.arr (xs.map emit).toArray)) = _
  rw [clean, array_decode xs emit get read]
  rfl

private theorem scope_canonical (s : Scope) (valid : pathOk s.path)
    (nonempty : s ≠ .serviceRoot → s.path ≠ []) :
    part (wireScope s) true = some (s.path, some s) := by
  simp only [part, scope_fields, Except.toOption, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases s with
  | serviceRoot => rfl
  | resource p =>
    have path := canonical_path p valid (nonempty (by intro eq; cases eq))
    change (do
      let path : Path ← pure ((("/".intercalate p).split '/').toList.map String.Slice.copy)
      let scope ← pure (Scope.resource path)
      guard (pathOk scope.path && (scope == Scope.serviceRoot || !scope.path.isEmpty))
      return (scope.path, some scope)) = (some _ : Option (Path × Option Scope))
    have inhabited : p ≠ [] := nonempty (by intro eq; cases eq)
    change pathOk p = true at valid
    simp [path, Scope.path, inhabited, valid, guard, pure]
  | collection p =>
    have path := canonical_path p valid (nonempty (by intro eq; cases eq))
    change (do
      let path : Path ← pure ((("/".intercalate p).split '/').toList.map String.Slice.copy)
      let scope ← pure (Scope.collection path)
      guard (pathOk scope.path && (scope == Scope.serviceRoot || !scope.path.isEmpty))
      return (scope.path, some scope)) = (some _ : Option (Path × Option Scope))
    have inhabited : p ≠ [] := nonempty (by intro eq; cases eq)
    change pathOk p = true at valid
    simp [path, Scope.path, inhabited, valid, guard, pure]


private theorem anchor_canonical (c : WireContext) (valid : pathOk c.anchor) :
    decodedAnchor c.protoJson true = some c.anchor := by
  have get : c.protoJson.getObjVal? "anchor" = .ok (wireAnchor c.anchor) := by rfl
  simp only [decodedAnchor, get, Except.toOption, Option.bind, wireAnchor]
  by_cases empty : c.anchor = []
  · simp [empty, anchorPath]
    rfl
  · have read := scope_canonical (.resource c.anchor) valid (fun _ => empty)
    simp [empty, anchorPath, read]
    rfl

private theorem repeated_raw [ToJson β] (j : Json) (name : String) (xs : List β)
    (field : j.getObjVal? name = .ok (toJson xs)) (nonNull : ∀ x ∈ xs, toJson x ≠ .null) :
    wireList j name true = .ok (xs.map toJson) := by
  exact repeated_canonical j name xs toJson toJson
    (field.trans (congrArg Except.ok (list_payload xs))) nonNull (fun _ _ => rfl)

private theorem repeated_json (j : Json) (name : String) (xs : List Json)
    (field : j.getObjVal? name = .ok (toJson xs)) (nonNull : ∀ x ∈ xs, x ≠ .null) :
    wireList j name true = .ok xs := by
  have read := repeated_raw j name xs field nonNull
  change wireList j name true = .ok (xs.map id) at read
  simpa only [List.map_id] using read

private theorem key_canonical (ks : KeySet) (bound : ks.id ≤ 2147483647) :
    keyEntry (toJson ks) true = .ok (ks.id,ks.keys) := by
  have get : (toJson ks).getObjVal? "id" = .ok (toJson ks.id) := by rfl
  have keyGet : (toJson ks).getObjVal? "keys" = .ok (toJson ks.keys) := by rfl
  have raw := repeated_canonical (toJson ks) "keys" ks.keys toJson id
    (keyGet.trans (congrArg Except.ok (list_payload ks.keys))) (fun _ _ h => nomatch h) (fun _ _ => rfl)
  simp only [List.map_id] at raw
  simp only [keyEntry, key_fields, bind, Except.bind, get, natural_canonical _ bound, raw]
  rfl

/-- The only input conditions for inverting the generated group fields are the
int32 bounds and the lexical grammar of the encoded scope and anchor names. -/
theorem canonical_fields_of_lexical (r : Response)
    (tableIds : ∀ ks ∈ r.keySets, ks.id ≤ 2147483647)
    (anchors : ∀ c ∈ r.contexts, pathOk c.anchor)
    (refs : ∀ c ∈ r.contexts, ∀ g ∈ c.claims, g.keySet ≤ 2147483647)
    (names : ∀ c ∈ r.contexts, ∀ g ∈ c.claims, ∀ s ∈ g.scope :: g.holes,
      pathOk s.path ∧ (s ≠ .serviceRoot → s.path ≠ [])) : CanonicalFields r := by
  refine ⟨top_fields r, ?_, ?_, fun ks mem => key_canonical ks (tableIds ks mem),
    fun c _ => context_fields c, fun c mem => anchor_canonical c (anchors c mem),
    ?_, fun _ _ g _ => claim_fields g, fun c hc g hg => natural_canonical g.keySet (refs c hc g hg),
    ?_, ?_, ?_⟩
  · exact repeated_raw _ _ _ (by rfl) (fun _ _ eq => nomatch eq)
  · apply repeated_json _ _ _ (by rfl)
    intro v hv
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hv
    intro eq
    cases eq
  · intro c _; apply repeated_json _ _ _ (by rfl)
    intro v hv
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hv
    intro eq
    cases eq
  · intro c hc g hg
    exact scope_canonical g.scope (names c hc g hg _ List.mem_cons_self).1
      (names c hc g hg _ List.mem_cons_self).2
  · intro _ _ g _; apply repeated_json _ _ _ (by rfl)
    intro v hv
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hv
    cases s <;> intro eq <;> cases eq
  · intro c hc g hg s hs
    exact scope_canonical s (names c hc g hg _ (List.mem_cons_of_mem _ hs)).1
      (names c hc g hg _ (List.mem_cons_of_mem _ hs)).2

/-- An actual query response has readable group fields whenever its one-based
key-set identifiers fit the transport's signed int32 range. -/
theorem canonical_fields_of_query {v w stamp asked r}
    (sent : queryPermissionContexts v w stamp asked = .ok r)
    (bound : r.keySets.length ≤ 2147483647) : CanonicalFields r := by
  obtain ⟨ids, anchors, refs, names⟩ := response_fields_lexical sent
  exact canonical_fields_of_lexical r (fun k hk => Nat.le_trans (ids k hk) bound) anchors
    (fun c hc g hg => Nat.le_trans (refs c hc g hg) bound) names

/-- A successful canonical ProtoJSON receipt preserves the producer's envelope
service, descriptor ETag, subject, snapshot token, and response profile. -/
theorem canonical_received_envelope {keys} {packed : Response} {reply}
    (received : receive? keys packed.protoJson none true = some reply) :
    reply.service = packed.service ∧ reply.descriptorEtag = packed.etag ∧
    reply.subject = packed.subject ∧ reply.token = packed.snapshotToken ∧
    reply.profile = packed.profile := by
  unfold receive? at received
  obtain ⟨base, parsed, h⟩ := Option.bind_eq_some_iff.mp received
  obtain ⟨_, _, eq⟩ := Option.bind_eq_some_iff.mp h
  cases eq
  have prepared : fields packed.protoJson true [("subjectContextId","subject_context_id"),
      ("snapshotToken","snapshot_token"), ("descriptorEtag","descriptor_etag"), ("expireTime","expire_time")] []
      = .ok packed.protoJson := by
    apply fields_canonical
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> rfl
    · simp
  have service : packed.protoJson.getObjValAs? String "service" = .ok packed.service := by rfl
  have etag : packed.protoJson.getObjValAs? String "descriptorEtag" = .ok packed.etag := by rfl
  have subject : packed.protoJson.getObjVal? "subjectContextId" = .ok (.str packed.subject) := by rfl
  have token : packed.protoJson.getObjVal? "snapshotToken" = .ok (.str packed.snapshotToken) := by rfl
  have profileVal : packed.protoJson.getObjVal? "profile" =
      .ok (.str (if packed.profile == .grantShaped then "PROFILE_GRANT_SHAPED" else "PROFILE_SCOPED_CLAIMS")) := by rfl
  have profileRead : responseProfile (.str (if packed.profile == .grantShaped then "PROFILE_GRANT_SHAPED" else "PROFILE_SCOPED_CLAIMS")) false =
      some packed.profile := by cases packed.profile <;> rfl
  unfold envelope? at parsed
  obtain ⟨_, preparedOk, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  rw [prepared] at preparedOk
  cases preparedOk
  have bindValue {α β : Type} (x : α) (f : α → Option β) : (some x >>= f) = f x := rfl
  have firstValue {α : Type} (x : α) : (some x <|> none) = some x := rfl
  simp only [service, etag, subject, token, profileVal, Bool.not_true, profileRead, ↓reduceIte, Except.toOption,
    firstValue, Json.getStr?, pure, Except.pure, bindValue] at parsed
  obtain ⟨_, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨_, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨_, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  cases parsed
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A successful receipt keeps the service, subject and snapshot token carried
by the producer's canonical ProtoJSON envelope. -/
theorem canonical_received_stamp {keys} {packed : Response} {reply}
    (received : receive? keys packed.protoJson none true = some reply) :
    reply.service = packed.service ∧ reply.subject = packed.subject ∧ reply.token = packed.snapshotToken := by
  obtain ⟨service, _, subject, token, _⟩ := canonical_received_envelope received
  exact ⟨service, subject, token⟩

end Authz.GroupedReply
