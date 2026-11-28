import Authz.Projection
import Authz.Disclosure

namespace Authz.Query

structure Stamp where
  service : String
  subject : String
  etag : String
  snapshotToken : String
  expireTime : Nat
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

structure Shape where
  kind : Kind
  scope : Scope
  holes : List Scope
  deriving Repr, DecidableEq, Lean.ToJson

structure WireClaim extends Shape where
  keySet : Nat
  deriving Repr, DecidableEq, Lean.ToJson

structure WireContext where
  anchor : Path
  requestedAnchors : List Path
  claims : List WireClaim
  descendantsOmitted : Bool
  deriving Repr, DecidableEq, Lean.ToJson

structure KeySet where
  id : Nat
  keys : List String
  deriving Repr, DecidableEq, Lean.ToJson

/-- Logical fields of §4.1; the transport maps paths to protobuf Anchor arms. -/
structure Response extends Stamp where
  profile : Profile
  keySets : List KeySet
  contexts : List WireContext
  deriving Repr, DecidableEq, Lean.ToJson

def wireScope : Scope → Lean.Json
  | .serviceRoot => .mkObj [("serviceRoot", .mkObj [])]
  | .resource p => .mkObj [("resource", .str (String.intercalate "/" p))]
  | .collection p => .mkObj [("collection", .str (String.intercalate "/" p))]

def wireAnchor (path : Path) := wireScope (if path.isEmpty then .serviceRoot else .resource path)

def WireClaim.protoJson (c : WireClaim) : Lean.Json := .mkObj [
  ("kind", .str (match c.kind with | .allow => "ALLOW" | .deny => "DENY" | .conditional => "CONDITIONAL")),
  ("scope", wireScope c.scope), ("holes", Lean.toJson (c.holes.map wireScope)), ("keySet", Lean.toJson c.keySet)]

def WireContext.protoJson (ctx : WireContext) : Lean.Json := .mkObj [
  ("anchor", wireAnchor ctx.anchor), ("requestedAnchors", Lean.toJson (ctx.requestedAnchors.map wireAnchor)),
  ("descendantsOmitted", Lean.toJson ctx.descendantsOmitted),
  ("claims", Lean.toJson (ctx.claims.map WireClaim.protoJson))]

/-- Encode the packed response without changing group, key-set or hole order. -/
def Response.protoJson (r : Response) : Lean.Json := Id.run do
  let utc := Std.Time.DateTime.ofTimestampWithZone (.ofMillisecondsSinceUnixEpoch ⟨r.expireTime⟩) .UTC
  let contexts := r.contexts.map WireContext.protoJson
  return .mkObj [("service", .str r.service), ("descriptorEtag", .str r.etag), ("subjectContextId", .str r.subject),
    ("snapshotToken", .str r.snapshotToken), ("expireTime", .str (utc.format "uuuu-MM-dd'T'HH:mm:ss.SSS'Z'")),
    ("profile", .str (if r.profile == .grantShaped then "PROFILE_GRANT_SHAPED" else "PROFILE_SCOPED_CLAIMS")),
    ("keySets", Lean.toJson r.keySets), ("contexts", Lean.toJson contexts)]

structure View where
  keys : List (String × Domain)
  resources : Domain
  profile : Profile
  options : Path → String → ProjectOptions
  indirect : Path → Bool

structure World where
  rules : List Rule
  resolve : Disclosure.Resolver
  /-- Request-scoped identity evidence for this exact alias and its resolution. -/
  ownsAlias : String → Path → Path → Bool
  /-- Result of authorizing the caller's read of the canonical target now. -/
  canReadNow : String → Path → Bool

def World.mayResolve (w : World) (subject : String) (supplied target : Path) : Bool :=
  w.ownsAlias subject supplied target || w.canReadNow subject target

def scopeTag (v : View) (p : Path) : Scope :=
  if p.isEmpty then .serviceRoot
  else if v.resources.isResource p then .resource p
  else .collection p

/-- Compare the complete resource name, including its separators. -/
private def nameLE (a b : Path) : Bool :=
  utf16Units (String.intercalate "/" a) ≤ utf16Units (String.intercalate "/" b)

def shape (v : View) (c : Claim) : Shape :=
  ⟨c.kind, scopeTag v c.path, (c.holes.mergeSort nameLE).map (scopeTag v)⟩

theorem shape_ordered_holes (v : View) (c : Claim) :
    (shape v c).holes.map Scope.path = c.holes.mergeSort nameLE := by
  have back : Scope.path ∘ scopeTag v = id := by
    funext path
    cases path with
    | nil => rfl
    | cons s rest =>
      cases tag : v.resources.isResource (s :: rest) <;> simp [scopeTag, Scope.path, tag]
  simp [shape, List.map_map, back]

private structure Grouped where
  anchor : Path
  requested : List Path
  groups : List (Shape × List String)
  omitted : Bool

private def pack (stamp : Stamp) (profile : Profile) (contexts : List Grouped) : Response :=
  let sets := (contexts.flatMap fun ctx => ctx.groups.map Prod.snd).eraseDups
  let entries := sets.zipIdx.map fun (keys, i) => KeySet.mk (i + 1) keys
  let encoded := contexts.map fun ctx =>
    let claims := ctx.groups.map fun (form, keys) => WireClaim.mk form (sets.idxOf keys + 1)
    WireContext.mk ctx.anchor ctx.requested claims ctx.omitted
  ⟨stamp, profile, entries, encoded⟩

private def echoes (names : List (Path × Path)) (anchor : Path) :=
  ((names.filter (·.2 == anchor)).map Prod.fst).mergeSort nameLE

private def groupContext (v : View) (names : List (Path × Path)) (ctx : ContextProjection) : Grouped :=
  let asked := echoes names ctx.anchor
  let forms := (ctx.claims.map (shape v)).eraseDups
  let groups := forms.map fun form =>
    (form, ((ctx.claims.filter (fun c => shape v c == form)).map Claim.key).eraseDups.mergeSort (fun a b => utf16Units a ≤ utf16Units b))
  ⟨ctx.anchor, asked, groups, ctx.descendantsOmitted⟩

private def answer (v : View) (w : World) (stamp : Stamp) (names : List (Path × Path)) : Response :=
  pack stamp v.profile (((names.map Prod.snd).eraseDups.mergeSort nameLE).map fun anchor =>
    groupContext v names (projectContext w.rules v.keys v.resources anchor v.profile (v.options anchor)))

def View.indirectAt (v : View) (p : Path) := v.resources.isResource p && v.indirect p

def resolveNames (v : View) (w : World) (subject : String) (asked : List Path) :=
  asked.filterMap fun p =>
    (Disclosure.resolveAnchor v.indirectAt w.resolve (w.mayResolve subject) [] p).map (p, ·)

def validCanonical (v : View) (p : Path) := !p.isEmpty && pathOk p && scopeTag v p == .resource p

private def resolveChecked (v : View) (w : World) (subject : String) (base : Path) :
    Path → Except Disclosure.Status (Option Path)
  | [] => .ok (some base)
  | s :: rest => do
    let p := base ++ [s]
    if !v.indirectAt p then return ← resolveChecked v w subject p rest
    let some target := w.resolve p | return none
    if !validCanonical v target then throw .serverFault
    else if w.mayResolve subject p target then resolveChecked v w subject target rest
    else return none

private def checkedNames (v : View) (w : World) (subject : String) : List Path → Except Disclosure.Status (List (Path × Path))
  | [] => .ok []
  | name :: names => do
    let hit ← resolveChecked v w subject [] name
    let tail ← checkedNames v w subject names
    return (hit.map (name, ·)).toList ++ tail

def ValidMappings (v : View) (w : World) :=
  ∀ p, v.indirectAt p = true → ∀ target, w.resolve p = some target → validCanonical v target = true

private theorem checked_path {v w} (subject : String) (valid : ValidMappings v w) (base path : Path) :
    resolveChecked v w subject base path = .ok (Disclosure.resolveAnchor v.indirectAt w.resolve (w.mayResolve subject) base path) := by
  induction path generalizing base with
  | nil => rfl
  | cons s rest ih =>
    cases isAlias : v.indirectAt (base ++ [s]) with
    | false => simp [resolveChecked, Disclosure.resolveAnchor, Disclosure.resolvePrefix, isAlias, ih]
    | true =>
      cases lookup : w.resolve (base ++ [s]) with
      | none => simp [resolveChecked, Disclosure.resolveAnchor, Disclosure.resolvePrefix, isAlias, lookup] <;> rfl
      | some target =>
        have targetOk := valid _ isAlias _ lookup
        cases see : w.mayResolve subject (base ++ [s]) target <;>
          simp [resolveChecked, Disclosure.resolveAnchor, Disclosure.resolvePrefix, isAlias, lookup,
            targetOk, Option.filter, see, ih] <;> rfl

private theorem checked_names {v w} (subject : String) (valid : ValidMappings v w) (names : List Path) :
    checkedNames v w subject names = .ok (resolveNames v w subject names) := by
  induction names with
  | nil => rfl
  | cons p ps ih =>
    simp only [checkedNames, checked_path subject valid, ih]
    cases hit : Disclosure.resolveAnchor v.indirectAt w.resolve (w.mayResolve subject) [] p <;>
      simp [resolveNames, hit, pure, bind, Except.bind, Except.pure]

/-- Validate the request and its resolved resource anchors before projection. -/
def requestedNames (v : View) (w : World) (subject : String) (asked : List Path) :
    Except Disclosure.Status (List (Path × Path)) :=
  if asked.isEmpty || (asked.eraseDups.length != asked.length) ||
      !asked.all (fun p => pathOk p && (p.isEmpty || scopeTag v p == .resource p)) then .error .invalidArgument
  else if !w.rules.all (v.resources.validSite ·.path) then .error .serverFault
  else do
    let names ← checkedNames v w subject asked
    if names.all (fun pair => pair.1.isEmpty || validCanonical v pair.2) then return names
    else throw .serverFault

/-- Query at a pinned revision after the server token floor has been validated. -/
def queryPermissionContexts (v : View) (w : World) (stamp : Stamp) (asked : List Path) :
    Except Disclosure.Status Response :=
  (requestedNames v w stamp.subject asked).map (answer v w stamp)

/-- A checked path records the canonical base after each supplied segment.
For an indirect prefix the evidence names the caller and the actual resolution. -/
inductive AuthorizedPath (v : View) (w : World) (subject : String) : Path → Path → Path → Prop where
  | done (base) : AuthorizedPath v w subject base [] base
  | direct {base seg rest result} (literal : v.indirectAt (base ++ [seg]) = false)
      (tail : AuthorizedPath v w subject (base ++ [seg]) rest result) :
      AuthorizedPath v w subject base (seg :: rest) result
  | indirect {base seg rest target result} (alias : v.indirectAt (base ++ [seg]) = true)
      (resolved : w.resolve (base ++ [seg]) = some target) (valid : validCanonical v target = true)
      (authorized : w.ownsAlias subject (base ++ [seg]) target = true ∨ w.canReadNow subject target = true)
      (tail : AuthorizedPath v w subject target rest result) :
      AuthorizedPath v w subject base (seg :: rest) result

private theorem checked_path_authorized {v w subject base path result}
    (ok : resolveChecked v w subject base path = .ok (some result)) :
    AuthorizedPath v w subject base path result := by
  induction path generalizing base with
  | nil =>
    have eq : base = result := by simpa [resolveChecked, pure, Except.pure] using ok
    subst result
    exact .done base
  | cons seg rest ih =>
    cases alias : v.indirectAt (base ++ [seg]) with
    | false =>
      apply AuthorizedPath.direct alias
      apply ih
      simpa [resolveChecked, alias] using ok
    | true =>
      cases mapped : w.resolve (base ++ [seg]) with
      | none => simp [resolveChecked, alias, mapped, pure, Except.pure] at ok
      | some target =>
        cases valid : validCanonical v target with
        | false => simp [resolveChecked, alias, mapped, valid] at ok
        | true =>
          cases allowed : w.mayResolve subject (base ++ [seg]) target with
          | false => simp [resolveChecked, alias, mapped, valid, allowed, pure, Except.pure] at ok
          | true =>
            apply AuthorizedPath.indirect alias mapped valid (Bool.or_eq_true_iff.mp allowed)
            exact ih (by simpa [resolveChecked, alias, mapped, valid, allowed] using ok)

private theorem checked_names_authorized {v w subject asked pairs}
    (ok : checkedNames v w subject asked = .ok pairs) :
    ∀ pair ∈ pairs, pair.1 ∈ asked ∧ AuthorizedPath v w subject [] pair.1 pair.2 := by
  induction asked generalizing pairs with
  | nil =>
    have empty : pairs = [] := by simpa [checkedNames] using ok.symm
    simp [empty]
  | cons head rest ih =>
    cases first : resolveChecked v w subject [] head with
    | error err => simp [checkedNames, first, bind, Except.bind] at ok
    | ok resolved =>
      cases others : checkedNames v w subject rest with
      | error err => simp [checkedNames, first, others, bind, Except.bind] at ok
      | ok tail =>
        simp [checkedNames, first, others, bind, Except.bind, pure, Except.pure] at ok
        subst pairs
        intro pair member
        rcases List.mem_append.mp member with headHit | tailHit
        · cases resolved with
          | none => simp at headHit
          | some target =>
            simp at headHit
            subst pair
            exact ⟨List.mem_cons_self, checked_path_authorized first⟩
        · obtain ⟨asked, path⟩ := ih others pair tailHit
          exact ⟨List.mem_cons_of_mem _ asked, path⟩

theorem response_stamp {v w stamp asked reply}
    (sent : queryPermissionContexts v w stamp asked = .ok reply) : reply.toStamp = stamp := by
  unfold queryPermissionContexts at sent
  cases names : requestedNames v w stamp.subject asked with
  | error err => simp [names, Except.map] at sent
  | ok pairs => simp only [names, Except.map, Except.ok.injEq] at sent; cases sent; rfl

private theorem mem_echoes {names anchor source} :
    source ∈ echoes names anchor ↔ (source, anchor) ∈ names := by
  simp only [echoes, List.mem_mergeSort, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨member, rfl⟩, rfl⟩
    exact member
  · intro member
    exact ⟨_, ⟨member, rfl⟩, rfl⟩

private theorem packed_echoes {v w stamp names ctx}
    (member : ctx ∈ (answer v w stamp names).contexts) :
    (∃ source, source ∈ ctx.requestedAnchors) ∧
      ∀ source ∈ ctx.requestedAnchors, (source, ctx.anchor) ∈ names := by
  obtain ⟨group, groupMem, rfl⟩ := List.mem_map.mp member
  obtain ⟨anchor, anchorMem, rfl⟩ := List.mem_map.mp groupMem
  have same : (projectContext w.rules v.keys v.resources anchor v.profile (v.options anchor)).anchor = anchor := by
    unfold projectContext
    split <;> rfl
  simp only [groupContext, same, mem_echoes]
  obtain ⟨⟨source, p⟩, pair, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp (List.mem_mergeSort.mp anchorMem))
  exact ⟨⟨source, pair⟩, fun _ h => h⟩

/-- A group ID in a produced response recovers exactly the keys that shared
its projected kind, scope, and holes. No two encoded lists can share an ID. -/
private theorem packed_group_key {stamp profile contexts ctx claim entry key}
    (inContext : ctx ∈ (pack stamp profile contexts).contexts) (inGroup : claim ∈ ctx.claims)
    (inTable : entry ∈ (pack stamp profile contexts).keySets) (reference : entry.id = claim.keySet)
    (member : key ∈ entry.keys) :
    ∃ source ∈ contexts, source.anchor = ctx.anchor ∧ ∃ pair ∈ source.groups,
      pair.1 = claim.toShape ∧ key ∈ pair.2 := by
  let sets := (contexts.flatMap fun ctx => ctx.groups.map Prod.snd).eraseDups
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp inContext
  obtain ⟨⟨form, keys⟩, hg, rfl⟩ := List.mem_map.mp inGroup
  obtain ⟨⟨other, i⟩, he, rfl⟩ := List.mem_map.mp inTable
  change i + 1 = sets.idxOf keys + 1 at reference
  have pos := Nat.add_right_cancel reference
  have inKeys : keys ∈ sets := List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨source, hs,
    List.mem_map.mpr ⟨(form,keys), hg, rfl⟩⟩)
  have same : keys = other := by
    have slot := List.mem_zipIdx_iff_getElem?.mp he
    change sets[i]? = some other at slot
    simpa [pos, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem inKeys)] using slot
  exact ⟨source, hs, rfl, (form,keys), hg, rfl, same ▸ member⟩

theorem packed_claim_origin {v w stamp asked reply ctx claim entry key}
    (sent : queryPermissionContexts v w stamp asked = .ok reply)
    (inContext : ctx ∈ reply.contexts) (inGroup : claim ∈ ctx.claims)
    (inTable : entry ∈ reply.keySets) (reference : entry.id = claim.keySet) (member : key ∈ entry.keys) :
    ∃ c ∈ (projectContext w.rules v.keys v.resources ctx.anchor v.profile (v.options ctx.anchor)).claims,
      c.key = key ∧ shape v c = claim.toShape := by
  unfold queryPermissionContexts at sent
  cases result : requestedNames v w stamp.subject asked with
  | error err => simp [result, Except.map] at sent
  | ok names =>
    simp only [result, Except.map, Except.ok.injEq] at sent
    subst reply
    obtain ⟨source, hs, atAnchor, pair, hp, eq, hk⟩ := packed_group_key inContext inGroup inTable reference member
    obtain ⟨anchor, _, rfl⟩ := List.mem_map.mp hs
    let ctxProjection := projectContext w.rules v.keys v.resources anchor v.profile (v.options anchor)
    have same : ctxProjection.anchor = anchor := by unfold ctxProjection projectContext; split <;> rfl
    change ctxProjection.anchor = ctx.anchor at atAnchor
    have named : ctx.anchor = anchor := atAnchor.symm.trans same
    obtain ⟨form, _, rfl⟩ := List.mem_map.mp hp
    have listed := List.mem_eraseDups.mp (List.mem_mergeSort.mp hk)
    obtain ⟨c, keep, fromKey⟩ := List.mem_map.mp listed
    obtain ⟨origin, shaped⟩ := List.mem_filter.mp keep
    rw [named]
    exact ⟨c, origin, fromKey, (beq_iff_eq.mp shaped).trans eq⟩

/-- Expand the typed key-set table, retaining the anchor on each claim. -/
def Response.ledger (r : Response) : List (Path × Claim) :=
  r.contexts.flatMap fun ctx => ctx.claims.flatMap fun group =>
    (r.keySets.filter (·.id == group.keySet)).flatMap fun entry => entry.keys.map fun key =>
      (ctx.anchor, ⟨key, group.kind, group.scope.path, group.holes.map Scope.path⟩)

theorem ledger_origin {v w stamp asked reply anchor c}
    (sent : queryPermissionContexts v w stamp asked = .ok reply) (mem : (anchor,c) ∈ reply.ledger) :
    ∃ source ∈ (projectContext w.rules v.keys v.resources anchor v.profile (v.options anchor)).claims,
      source.key = c.key ∧ source.kind = c.kind ∧ source.path = c.path ∧ source.holes.Perm c.holes := by
  obtain ⟨ctx, hc, entry⟩ := List.mem_flatMap.mp mem
  obtain ⟨group, hg, table⟩ := List.mem_flatMap.mp entry
  obtain ⟨ks, set, included⟩ := List.mem_flatMap.mp table
  obtain ⟨key, contained, eq⟩ := List.mem_map.mp included
  cases eq
  obtain ⟨hks, same⟩ := List.mem_filter.mp set
  obtain ⟨source, projected, fromKey, shapeEq⟩ := packed_claim_origin sent hc hg hks (beq_iff_eq.mp same) contained
  have path : (shape v source).scope.path = source.path := by
    change (scopeTag v source.path).path = source.path
    cases h : source.path with
    | nil => rfl
    | cons seg rest => cases tag : v.resources.isResource (seg :: rest) <;> simp [scopeTag, tag, Scope.path]
  have holes := shape_ordered_holes v source
  rw [shapeEq] at path holes
  exact ⟨source, projected, fromKey, congrArg Shape.kind shapeEq, path.symm,
    holes.symm ▸ (List.mergeSort_perm source.holes nameLE).symm⟩

private theorem packed_ids (stamp profile groups) :
    let r := pack stamp profile groups
    (∀ ks ∈ r.keySets, ks.id ≤ r.keySets.length) ∧
    ∀ c ∈ r.contexts, ∀ g ∈ c.claims, g.keySet ≤ r.keySets.length := by
  let sets := (groups.flatMap fun (g : Grouped) => g.groups.map Prod.snd).eraseDups
  have size : (pack stamp profile groups).keySets.length = sets.length := by simp [pack, sets]
  dsimp only
  rw [size]
  constructor
  · intro ks mem
    obtain ⟨⟨keys,i⟩, slot, rfl⟩ := List.mem_map.mp mem
    have pos : sets[i]? = some keys := List.mk_mem_zipIdx_iff_getElem?.mp slot
    exact (List.getElem?_eq_some_iff.mp pos).1
  · intro c hc g hg
    obtain ⟨src, member, rfl⟩ := List.mem_map.mp hc
    obtain ⟨⟨shape,keys⟩, pair, rfl⟩ := List.mem_map.mp hg
    have key : keys ∈ sets := List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨src, member,
      List.mem_map.mpr ⟨(shape,keys), pair, rfl⟩⟩)
    exact List.idxOf_lt_length_of_mem key

private theorem scopeTag_lexical (v : View) (p : Path) (valid : pathOk p) :
    pathOk (scopeTag v p).path ∧ (scopeTag v p ≠ .serviceRoot → (scopeTag v p).path ≠ []) := by
  cases p with
  | nil => simp [scopeTag, Scope.path, pathOk]
  | cons x rest =>
    cases tag : v.resources.isResource (x :: rest) <;> simpa [scopeTag, tag, Scope.path] using valid

private theorem packed_scopes {v w stamp pairs ctx g} (site : ctx ∈ (answer v w stamp pairs).contexts)
    (member : g ∈ ctx.claims) (s : Scope) (name : s ∈ g.scope :: g.holes) :
    pathOk s.path ∧ (s ≠ .serviceRoot → s.path ≠ []) := by
  obtain ⟨group, hgroup, rfl⟩ := List.mem_map.mp site
  obtain ⟨anchor, _, rfl⟩ := List.mem_map.mp hgroup
  obtain ⟨⟨form,keys⟩, source, rfl⟩ := List.mem_map.mp member
  obtain ⟨sh, shapeMem, eq⟩ := List.mem_map.mp source
  cases eq
  obtain ⟨c, projected, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp shapeMem)
  unfold projectContext at projected
  split at projected
  · contradiction
  · obtain ⟨proj, fromDomain, claim⟩ := List.mem_flatMap.mp projected
    obtain ⟨⟨k,d⟩, filtered, rfl⟩ := List.mem_map.mp fromDomain
    have valid := projectAnchor_structure (List.mem_filter.mp filtered).2 claim
    rcases List.mem_cons.mp name with rfl | hole
    · exact scopeTag_lexical v c.path valid.1
    · obtain ⟨p, present, rfl⟩ := List.mem_map.mp hole
      exact scopeTag_lexical v p (valid.2.2.2.2 p (List.mem_mergeSort.mp present)).1

private theorem packed_anchor {v w stamp pairs ctx asked}
    (ok : requestedNames v w stamp.subject asked = .ok pairs)
    (inContext : ctx ∈ (answer v w stamp pairs).contexts) : pathOk ctx.anchor := by
  obtain ⟨⟨p, hp⟩, echoes⟩ := packed_echoes inContext
  have pair := echoes p hp
  unfold requestedNames at ok
  split at ok
  · contradiction
  split at ok
  · contradiction
  cases result : checkedNames v w stamp.subject asked with
  | error err => simp [result, bind, Except.bind] at ok
  | ok entries =>
    simp [result, bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · rename_i all
      cases ok
      have accepted := List.all_eq_true.mp all (p,ctx.anchor) pair
      rcases Bool.or_eq_true_iff.mp accepted with root | target
      · have empty : p = [] := List.isEmpty_iff.mp root
        subst p
        have trace := (checked_names_authorized result ([],ctx.anchor) pair).2
        generalize ctx.anchor = a at trace ⊢
        cases trace
        rfl
      · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp target).1).2
    · contradiction

/-- Packing uses one-based positions in its own key table. The projected paths
and sorted holes retain the lexical validity of their partition boundaries. -/
theorem response_fields_lexical {v w stamp asked r}
    (sent : queryPermissionContexts v w stamp asked = .ok r) :
    (∀ ks ∈ r.keySets, ks.id ≤ r.keySets.length) ∧
    (∀ c ∈ r.contexts, pathOk c.anchor) ∧
    (∀ c ∈ r.contexts, ∀ g ∈ c.claims, g.keySet ≤ r.keySets.length) ∧
    (∀ c ∈ r.contexts, ∀ g ∈ c.claims, ∀ s ∈ g.scope :: g.holes,
      pathOk s.path ∧ (s ≠ .serviceRoot → s.path ≠ [])) := by
  cases checked : requestedNames v w stamp.subject asked with
  | error err => simp [queryPermissionContexts, checked, Except.map] at sent
  | ok pairs =>
    simp only [queryPermissionContexts, checked, Except.map, Except.ok.injEq] at sent
    subst r
    exact ⟨(packed_ids _ _ _).1, fun _ hc => packed_anchor checked hc,
      (packed_ids _ _ _).2, fun _ hc _ hg => packed_scopes hc hg⟩

/-- Every canonical anchor in the actual packed response has an echoed input.
Every echoed input follows an authorized path from the root to that anchor. -/
theorem response_alias_disclosure {v w stamp asked reply}
    (ok : queryPermissionContexts v w stamp asked = .ok reply) (ctx : WireContext) (sent : ctx ∈ reply.contexts) :
    (∃ source, source ∈ ctx.requestedAnchors) ∧
      ∀ source ∈ ctx.requestedAnchors, source ∈ asked ∧ AuthorizedPath v w stamp.subject [] source ctx.anchor := by
  cases names : requestedNames v w stamp.subject asked with
  | error err => simp [queryPermissionContexts, names, Except.map] at ok
  | ok pairs =>
    simp [queryPermissionContexts, names, Except.map] at ok
    subst reply
    obtain ⟨nonempty, echoes⟩ := packed_echoes sent
    refine ⟨nonempty, ?_⟩
    unfold requestedNames at names
    split at names
    · contradiction
    split at names
    · contradiction
    cases checked : checkedNames v w stamp.subject asked with
    | error err => simp [checked, bind, Except.bind] at names
    | ok hits =>
      simp [checked, bind, Except.bind, pure, Except.pure] at names
      split at names
      · cases names
        intro source echo
        exact checked_names_authorized checked _ (echoes source echo)
      · contradiction

/-- Exact duplicates are invalid for every catalog, policy and resolver. -/
theorem duplicate_anchors_rejected (v : View) (w : World) (stamp : Stamp) (asked : List Path)
    (duplicate : asked.eraseDups.length ≠ asked.length) :
    queryPermissionContexts v w stamp asked = .error .invalidArgument := by
  simp [queryPermissionContexts, requestedNames, duplicate]
  rfl

/-- Changing the projection options is unobservable when every anchor still
produces the same context. This includes responses with alias resolution. -/
theorem queryPermissionContexts_congr_options (v : View) (w : World) (stamp : Stamp)
    (asked : List Path) (opts : Path → String → ProjectOptions)
    (same : ∀ anchor, projectContext w.rules v.keys v.resources anchor v.profile (v.options anchor) =
      projectContext w.rules v.keys v.resources anchor v.profile (opts anchor)) :
    queryPermissionContexts v w stamp asked =
      queryPermissionContexts {v with options := opts} w stamp asked := by
  have answers (names : List (Path × Path)) :
      answer v w stamp names = answer {v with options := opts} w stamp names := by
    apply congrArg (pack stamp v.profile)
    apply List.map_congr_left
    intro anchor _
    rw [same anchor]
    rfl
  have resolve (base path : Path) : resolveChecked v w stamp.subject base path =
      resolveChecked {v with options := opts} w stamp.subject base path := by
    induction path generalizing base with
    | nil => rfl
    | cons seg rest ih => simp only [resolveChecked, ih, validCanonical, scopeTag, View.indirectAt]
  have checked (paths : List Path) : checkedNames v w stamp.subject paths =
      checkedNames {v with options := opts} w stamp.subject paths := by
    induction paths with
    | nil => rfl
    | cons p ps ih => simp only [checkedNames, resolve, ih]
  simp only [queryPermissionContexts, requestedNames, checked, scopeTag, validCanonical]
  congr 1
  funext names
  exact answers names

/-- Self-composition of resolution, per-key budget and projection, grouping,
key-set interning, and response stamping, at identical public wire metadata. -/
theorem response_private_twins (v : View) (a b : World) (stamp : Stamp) (asked : List Path)
    (aliases : ∀ p, v.indirectAt p = true →
      (a.resolve p).filter (a.mayResolve stamp.subject p) = (b.resolve p).filter (b.mayResolve stamp.subject p))
    (mapsA : ValidMappings v a) (mapsB : ValidMappings v b)
    (validA : a.rules.all (v.resources.validSite ·.path) = true)
    (validB : b.rules.all (v.resources.validSite ·.path) = true)
    (rules : ∀ anchor ∈ (resolveNames v a stamp.subject asked).map Prod.snd, ∀ key d, (key, d) ∈ v.keys → ((v.options anchor) key).nonprojecting = false →
      a.rules.filter (Rule.comparableAt key anchor) = b.rules.filter (Rule.comparableAt key anchor)) :
    queryPermissionContexts v a stamp asked = queryPermissionContexts v b stamp asked := by
  have names : resolveNames v a stamp.subject asked = resolveNames v b stamp.subject asked := by
    unfold resolveNames
    simp only [Disclosure.anchor_opacity _ _ _ _ _ aliases]
  have result : answer v a stamp (resolveNames v a stamp.subject asked) = answer v b stamp (resolveNames v a stamp.subject asked) := by
    apply congrArg (pack stamp v.profile)
    apply List.map_congr_left
    intro anchor ha
    have hm : anchor ∈ (resolveNames v a stamp.subject asked).map Prod.snd := by simpa using ha
    rw [context_private_twins _ _ _ _ _ _ _ validA validB (rules anchor hm)]
  simp only [queryPermissionContexts, requestedNames, validA, validB, checked_names stamp.subject mapsA, checked_names stamp.subject mapsB, ← names]
  split
  · rfl
  · simp [pure, bind, Except.bind, Except.pure]
    split
    · exact congrArg Except.ok result
    · rfl

/-- Adding an unconditional private forbid changes neither the packed claims,
holes and budget flag nor the resolver status when every returned anchor is
withheld, disjoint, or inherits the forbid with no permit on that branch.
The two calls share their public stamp and resolver observations. -/
theorem response_private_forbid_absent (v : View) (w : World) (stamp : Stamp) (asked : List Path)
    (key : String) (site : Path) (maps : ValidMappings v w)
    (valid : w.rules.all (v.resources.validSite ·.path)) (legal : v.resources.validSite site)
    (boundary : ∀ anchor ∈ (resolveNames v w stamp.subject asked).map Prod.snd,
      (v.options anchor key).nonprojecting = true ∨ (¬site <+: anchor ∧ ¬anchor <+: site) ∨
      (site <+: anchor ∧ ∀ r ∈ w.rules, key ∈ r.keys →
        (r.path <+: anchor ∨ anchor <+: r.path) → r.effect ≠ .permit)) :
    let block : Rule := {path := site, keys := [key], effect := .forbid, hidden := true}
    queryPermissionContexts v w stamp asked =
      queryPermissionContexts v {w with rules := w.rules ++ [block]} stamp asked := by
  intro block
  let other := {w with rules := w.rules ++ [block]}
  have validOther : other.rules.all (v.resources.validSite ·.path) := by simp [other, block, valid, legal]
  have names : resolveNames v other stamp.subject asked = resolveNames v w stamp.subject asked := rfl
  have packed : answer v w stamp (resolveNames v w stamp.subject asked) =
      answer v other stamp (resolveNames v w stamp.subject asked) := by
    apply congrArg (pack stamp v.profile)
    apply List.map_congr_left
    intro anchor h
    have belongs : anchor ∈ (resolveNames v w stamp.subject asked).map Prod.snd := by simpa using h
    exact congrArg _ (context_forbid_absent w.rules v.keys v.resources anchor v.profile (v.options anchor)
      key site valid legal (boundary _ belongs))
  change queryPermissionContexts v w stamp asked = queryPermissionContexts v other stamp asked
  simp only [queryPermissionContexts, requestedNames, valid, validOther, Bool.not_true,
    checked_names stamp.subject maps, checked_names (w := other) stamp.subject maps, names]
  split
  · rfl
  · simp [bind, pure, Except.bind, Except.pure]
    split
    · exact congrArg Except.ok packed
    · rfl

/-- Even an empty visible projection distinguishes different stamped revisions. -/
theorem distinct_stamps (v : View) (a b : World) (x y : Stamp) (pathsA pathsB)
    (different : x.snapshotToken ≠ y.snapshotToken) :
    answer v a x pathsA ≠ answer v b y pathsB :=
  fun same => different (congrArg (fun r : Response => r.snapshotToken) same)

namespace BoundaryExample
private def company := ["companies", "A"]
private def team := company ++ ["teams", "D"]
private def names : Domain := [[.lit "companies", .var "co", .lit "teams", .var "team"]]
private def view : View := {
  keys := [("teams.get", names), ("teams.audit", names)]
  resources := names
  profile := .scopedClaims
  options := fun anchor key => { nonprojecting := key == "teams.audit" && anchor.length < 4 }
  indirect := fun _ => false }
private def base : World := {
  rules := [{ path := company, keys := ["teams.get", "teams.audit"], effect := .permit }]
  resolve := fun _ => none
  ownsAlias := fun _ _ _ => false
  canReadNow := fun _ _ => false }
private def withForbid : World := { base with rules := base.rules ++
  [{ path := team, keys := ["teams.audit"], effect := .forbid, hidden := true }] }
private def stamp : Stamp := ⟨"demo", "alice", "d", "v1:auth:1:1", 100⟩
private def result (w : World) (p : Path) := (queryPermissionContexts view w stamp [p]).toOption

/-- A private policy change on Team D is invisible at every requested anchor
that either withholds the key or lies on a different branch. -/
theorem private_change_off_branch (asked : List Path)
    (outside : ∀ p ∈ (resolveNames view base stamp.subject asked).map Prod.snd,
      p.length < 4 ∨ (¬team <+: p ∧ ¬p <+: team)) :
    queryPermissionContexts view base stamp asked =
    queryPermissionContexts view withForbid stamp asked := by
  apply response_private_twins
  · simp [View.indirectAt, view]
  · simp [ValidMappings, View.indirectAt, view]
  · simp [ValidMappings, View.indirectAt, view]
  · decide
  · decide
  · intro anchor member k dom known projecting
    simp [view] at known
    rcases known with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rcases outside anchor member with above | ⟨outsideD, outsideAnchor⟩
      · simp [view, above] at projecting
      · simp [withForbid, Rule.comparableAt, outsideD, outsideAnchor]

theorem private_change_at_boundary :
    queryPermissionContexts view base stamp [company] =
    queryPermissionContexts view withForbid stamp [company] := by
  apply private_change_off_branch
  decide

private def sibling := company ++ ["teams", "B"]

theorem private_change_at_sibling :
    queryPermissionContexts view base stamp [sibling] =
    queryPermissionContexts view withForbid stamp [sibling] := by
  apply private_change_off_branch
  decide

theorem private_change_at_company_and_sibling :
    queryPermissionContexts view base stamp [company, sibling] =
    queryPermissionContexts view withForbid stamp [company, sibling] := by
  apply private_change_off_branch
  decide

#guard ((result base company).map (fun r => r.keySets.isEmpty)) == some false
#guard result base team != result withForbid team
end BoundaryExample

end Authz.Query
