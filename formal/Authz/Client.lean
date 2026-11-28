import Authz.Policy
import Authz.Trie
import Std.Time.Format

namespace Authz

inductive Verdict where
  | allow | deny | conditional | unloaded | defer | unavailable
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure ClientContext where
  anchor : Path
  claims : List Claim
  expires : Option Nat := none
  requestedAnchors : Option (List Path) := some []
  deriving DecidableEq, Repr, Lean.ToJson

instance : Lean.FromJson ClientContext where
  fromJson? j := do
    let requested := match j.getObjVal? "requestedAnchors" with
      | .error _ => some []
      | .ok value => (Lean.fromJson? (α := List Path) value).toOption
    return {
      anchor := ← j.getObjValAs? Path "anchor"
      claims := ← Lean.fromJson? ((j.getObjVal? "claims").toOption.getD (.arr #[]))
      expires := ← Lean.fromJson? ((j.getObjVal? "expires").toOption.getD .null)
      requestedAnchors := requested }

structure SnapshotReply where
  service : String
  descriptorEtag : String
  subject : String
  token : String
  expires : Nat
  profile : Profile
  contexts : List ClientContext := []
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure Frame where
  serial : Nat
  reply : SnapshotReply
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure ClientState where
  service : String
  session : String
  generation : Nat := 0
  serial : Nat := 0
  subject : Option String := none
  token : Option String := none
  loadedEtag : Option String := none
  lastEtag : Option String := none
  history : List Frame := []
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure SnapshotTicket where
  session : String
  generation : Nat
  minToken : Option String
  service : Option String := none
  maxProfile : Profile := .grantShaped
  deriving DecidableEq, Repr

instance : Lean.ToJson SnapshotTicket where
  toJson t := Lean.Json.mkObj <| [
    ("session", Lean.toJson t.session), ("generation", Lean.toJson t.generation),
    ("minToken", Lean.toJson t.minToken), ("maxProfile", Lean.toJson t.maxProfile)] ++
    t.service.toList.map fun service => ("service", Lean.toJson service)

/-- The wire zero value and an omitted request ceiling select Grant-Shaped. -/
def requestedProfile (j : Lean.Json) (fallback : Profile := .grantShaped) (normalized : Bool := true)
    (nullAsAbsent : Bool := false) : Except String Profile := do
  let value ← match j.getObjVal? "maxProfile", j.getObjVal? "max_profile" with
    | .ok _, .ok _ => throw "duplicate requested profile"
    | .ok v, _ | _, .ok v => pure v
    | _, _ => return fallback
  match value with
  | .null => if nullAsAbsent then return fallback else throw "invalid requested profile"
  | .str "PROFILE_UNSPECIFIED" | .str "PROFILE_GRANT_SHAPED" | .str "UNSPECIFIED" | .str "GRANT_SHAPED" => return .grantShaped
  | .str "PROFILE_SCOPED_CLAIMS" | .str "SCOPED_CLAIMS" => return .scopedClaims
  | .str "grantShaped" => if normalized then return .grantShaped else throw "invalid requested profile"
  | .str "scopedClaims" => if normalized then return .scopedClaims else throw "invalid requested profile"
  | .num n =>
    if n == 0 || n == 1 then return .grantShaped
    if n == 2 then return .scopedClaims
    throw "invalid requested profile"
  | _ => throw "invalid requested profile"

/-- Evaluation uses all accepted profiles unless a caller restricts the evidence.
An unrecognized maximum admits no positive or negative claim. -/
def evaluationProfile (j : Lean.Json) : Option Profile :=
  (requestedProfile j .scopedClaims false).toOption

instance : Lean.FromJson SnapshotTicket where
  fromJson? j := do
    let service ← match j.getObjVal? "service" with
      | .error _ => pure none
      | .ok value => do
        let .ok name := value.getStr? | throw "invalid requested service"
        pure (some name)
    return {
      session := ← j.getObjValAs? _ "session"
      generation := ← j.getObjValAs? _ "generation"
      minToken := ← Lean.fromJson? ((j.getObjVal? "minToken").toOption.getD .null)
      service
      maxProfile := ← requestedProfile j (nullAsAbsent := true) }

def ClientState.dispatch (s : ClientState) (maxProfile : Profile := .grantShaped) : SnapshotTicket :=
  ⟨s.session, s.generation, s.token, some s.service, maxProfile⟩

inductive ReplyAction where
  | discard | reset | merge | advance
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

/-- Canonical anchors are unique within a response, and two contexts cannot
answer the same requested spelling. A repetition inside one context has one owner. -/
def SnapshotReply.uniqueContexts (r : SnapshotReply) : Bool :=
  let contexts := r.contexts.filter fun c => pathOk c.anchor
  let anchors := contexts.map (·.anchor)
  let requests := contexts.flatMap fun c =>
    (c.requestedAnchors.filter (·.all pathOk)).toList.flatMap List.eraseDups
  anchors.Nodup && requests.Nodup

def snapshotAction (s : ClientState) (request : SnapshotTicket) (r : SnapshotReply)
    (now : Nat) (maxProfile : Profile) (expectedService : Option String := none) : ReplyAction :=
  let changed := s.subject.any (· != r.subject)
  let same := s.subject == some r.subject && s.token == some r.token
  if r.service != s.service || request.service.any (· != r.service) || expectedService.any (· != r.service) ||
      !r.uniqueContexts || r.service.isEmpty || r.descriptorEtag.isEmpty ||
      r.subject.isEmpty || r.token.isEmpty || r.expires ≤ now ||
      ((request.maxProfile == .grantShaped || maxProfile == .grantShaped) && r.profile != .grantShaped) ||
      s.session.isEmpty || request.session != s.session || request.generation != s.generation ||
      (changed && s.token.isSome &&
        ((request.minToken.getD "").isEmpty || request.minToken != s.token)) then .discard
  else if s.token.isSome && s.token != some r.token && request.minToken != s.token then .discard
  else if changed || s.subject.isNone then .reset
  else if same then .merge
  else .advance

def acceptSnapshot (s : ClientState) (request : SnapshotTicket) (r : SnapshotReply)
    (now : Nat) (maxProfile : Profile := request.maxProfile) (expectedService : Option String := none) : ClientState :=
  let action := snapshotAction s request r now maxProfile expectedService
  if action == .discard then s else
  let reset := action == .reset
  let frame : Frame := ⟨s.serial + 1, r⟩
  { s with
    generation := if reset && s.subject.isSome then s.generation + 1 else s.generation
    serial := frame.serial
    subject := some r.subject
    token := some r.token
    loadedEtag := s.loadedEtag.or (some r.descriptorEtag)
    lastEtag := some r.descriptorEtag
    history := frame :: (if reset then [] else s.history) }

def intersectsTarget : Path → Path → Bool
  | [], _ => true
  | a :: as, t :: ts => (t == "-" || a == t) && intersectsTarget as ts
  | _, [] => false

/-- Restrict all binding patterns to exactly the names selected by the query.
A singleton literal stays fixed even at a wildcard position. -/
def Pattern.restrictTarget : Pattern → Path → Option Pattern
  | [], [] => some []
  | a :: as, q :: qs => do
    let rest ← Pattern.restrictTarget as qs
    if q == "-" then return a :: rest
    else if a.accepts q then return .lit q :: rest
    else none
  | _, _ => none

def candidates (d : Domain) (q : Path) := d.filterMap (Pattern.restrictTarget · q)

def overlapIn (d : Domain) (a b : Claim) : Bool :=
  if a.path.isPrefixOf b.path then Domain.nonemptyRegion d b.path (a.holes ++ b.holes)
  else if b.path.isPrefixOf a.path then Domain.nonemptyRegion d a.path (a.holes ++ b.holes)
  else false

structure KeyDomains where
  entries : List (String × Domain)
  resources : Domain
  deriving Repr, DecidableEq

def KeyDomains.lookup (keys : KeyDomains) (key : String) := keys.entries.lookup key

def contextValid (keys : KeyDomains) (profile : Profile) (c : ClientContext) : Bool :=
  keys.resources.validSite c.anchor && c.requestedAnchors.any (·.all keys.resources.validSite) &&
  c.claims.all fun cl =>
    let d := keys.lookup cl.key
    pathOk cl.path && c.anchor.isPrefixOf cl.path &&
    (profile == .scopedClaims || (cl.kind == .allow && cl.holes.isEmpty)) &&
    d.all (fun dom => cl.path.isEmpty || dom.any (Pattern.reach · cl.path)) &&
    cl.holes.all (fun h => pathOk h && cl.path.isPrefixOf h && cl.path != h &&
      d.all (fun dom => dom.any (Pattern.reach · h))) &&
    !c.claims.any (fun other => other.key == cl.key && other.kind != cl.kind &&
      d.any (overlapIn · cl other))

namespace GroupedReply
open Lean

/-- Canonicalize protobuf field names before message validation. The transport
accepts null as absence. A stored frame keeps its original presence semantics. -/
def fields (j : Json) (protoJson : Bool) (aliases : List (String × String))
    (nullable : List String) : Except String Json := do
  let mut obj ← j.getObj?
  for (name, proto) in aliases do
    if let some value := obj.get? proto then
      if obj.contains name then throw ("duplicate field " ++ name)
      obj := (obj.erase proto).insert name value
  if protoJson then
    for name in nullable do
      if let some .null := obj.get? name then obj := obj.erase name
  return .obj obj

def repeated [FromJson α] (j : Json) (name : String) (protoJson : Bool) : Except String (List α) := do
  let .ok raw := j.getObjVal? name | return []
  let values ← raw.getArr?
  if protoJson && values.any (fun | .null => true | _ => false) then throw ("null element in " ++ name)
  return ← fromJson? raw

/-- Decimal and exponent notation may express an integer exactly. Work from
the decimal digits so a fractional key id cannot round to an existing id. -/
def natural (raw : Json) (quoted : Bool := false) : Option Nat := do
  let value ← match raw with
    | .str s => do
      guard (quoted && s.trimAscii.toString == s)
      (Json.parse s).toOption
    | _ => some raw
  let n ← value.getNum?.toOption
  if n.exponent == 0 && n.mantissa ≥ 0 && n.mantissa ≤ 2147483647 then return n.mantissa.toNat
  if n.mantissa == 0 then return 0
  let (sign, digits, magnitude) := n.normalize
  guard (sign > 0 && magnitude > 0 && magnitude ≤ 16 && digits.repr.length ≤ magnitude.toNat)
  return digits * 10 ^ (magnitude.toNat - digits.repr.length)

def responseProfile (value : Json) (native : Bool) : Option Profile := do
  match value with
  | .str "GRANT_SHAPED" | .str "PROFILE_GRANT_SHAPED" => some .grantShaped
  | .str "SCOPED_CLAIMS" | .str "PROFILE_SCOPED_CLAIMS" => some .scopedClaims
  | .str _ => if native then (fromJson? value).toOption else none
  | _ => match ← natural value with
    | 1 => some .grantShaped | 2 => some .scopedClaims | _ => none

def responseKind (value : Json) (native : Bool) : Option Kind := do
  match value with
  | .str "ALLOW" | .str "CLAIM_KIND_ALLOW" => some .allow
  | .str "DENY" | .str "CLAIM_KIND_DENY" => some .deny
  | .str "CONDITIONAL" | .str "CLAIM_KIND_CONDITIONAL" => some .conditional
  | .str _ => if native then (fromJson? value).toOption else none
  | _ => match ← natural value with
    | 1 => some .allow | 2 => some .deny | 3 => some .conditional | _ => none

/-- Snapshot clocks have millisecond resolution. Parse the offset and validate
calendar fields using the standard ISO 8601 implementation. -/
private def timestamp (value : Json) : Option Nat := do
  if let .str s := value then
    guard (s.length ≥ 20 && s.length ≤ 35 && s.take 4 != "0000")
    let base := (s.take 19).toString
    let rest := s.drop 19
    let (ms, zone) ← if rest.startsWith "." then do
      let sub := rest.drop 1
      let fraction := (sub.takeWhile Char.isDigit).toString
      guard (!fraction.isEmpty && fraction.length ≤ 9)
      let ms ← ((fraction ++ "00").take 3).toString.toNat?
      pure (ms, (sub.drop fraction.length).toString)
    else pure (0, rest.toString)
    guard (zone == "Z" || (zone.length == 6 && (zone.startsWith "+" || zone.startsWith "-")))
    let parsed ← (Std.Time.DateTime.fromISO8601String (base ++ zone)).toOption
    return (parsed.toTimestamp.toMillisecondsSinceUnixEpoch.val + (ms : Int)).toNat
  let n ← natural value
  guard (n ≤ 9007199254740991)
  return n

/-- A normalized transport may already have converted a scope to segments.
A tagged arm retains its resource/collection assertion until its keys are known. -/
def part (j : Json) (protoJson : Bool) : Option (Path × Option Scope) := do
  if !protoJson then
    if let .ok path := fromJson? (α := Path) j then
      guard (pathOk path)
      return (path, none)
    if j == .str "serviceRoot" then return ([], some .serviceRoot)
  let raw ← (fields j protoJson [("serviceRoot", "service_root")] ["serviceRoot","collection","resource"]).toOption
  let [(tag, value)] := (← raw.getObj?.toOption).toList | none
  let scope ← match tag with
    | "serviceRoot" => do
      guard (value.getObj?.toOption.any (·.isEmpty))
      pure Scope.serviceRoot
    | "resource" | "collection" => do
      let path ← match value with
        | .str name => pure ((name.split '/').toList.map (·.copy))
        | _ => do
          guard (!protoJson)
          (value.getObjValAs? Path "path").toOption
      pure (if tag == "resource" then Scope.resource path else Scope.collection path)
    | _ => none
  guard (pathOk scope.path && (scope == .serviceRoot || !scope.path.isEmpty))
  return (scope.path, some scope)

def anchorPath (raw : Json) (protoJson : Bool) : Option Path := do
  let (p, tag) ← part raw protoJson
  guard (tag != some (.collection p))
  return p

structure Group where
  keys : List String
  kind : Kind
  path : Path
  holes : List Path

private def checkedGroupValues (j : Json) (keys : KeyDomains) (profile : Profile)
    (anchor : Path) (expanded : Bool) (selected : List String) (kind : Kind)
    (path : Path) (arm : Option Scope) (holes : List (Path × Option Scope)) : Option Unit := do
  guard (anchor.isPrefixOf path && holes.all (fun h => path.isPrefixOf h.1 && path != h.1))
  guard (profile == .scopedClaims || (kind == .allow && holes.isEmpty))
  if selected.any (fun key => (keys.lookup key).isSome) then
    guard (arm.all (Scope.valid keys.resources) && holes.all (fun h => h.2.all (Scope.valid keys.resources)))
    if expanded then
      let agrees : Json → Path → Bool := fun saved p => match saved with
        | .str "serviceRoot" => p.isEmpty
        | .str "resource" => Scope.valid keys.resources (.resource p)
        | .str "collection" => Scope.valid keys.resources (.collection p)
        | _ => false
      if let .ok saved := j.getObjVal? "scopeKind" then guard (agrees saved path)
      if let .ok saved := j.getObjVal? "holeKinds" then
        let tags ← saved.getArr?.toOption
        guard (tags.size == holes.length && holes.zipIdx.all fun (h,i) => (tags[i]?).all fun t => t == .null || agrees t h.1)
  return ()

def group (keys : KeyDomains) (sets : List (Nat × List String)) (profile : Profile)
    (anchor : Path) (grouped nativeKinds protoJson : Bool) (raw : Json) : Option Group := do
  let j ← (fields raw protoJson [("keySet","key_set")] ["scope","keySet","kind","holes"]).toOption
  let expanded := !protoJson && !grouped && !(j.getObjVal? "keySet").isOk && !(j.getObjVal? "scope").isOk
  let selected ← if expanded then (j.getObjValAs? String "key").toOption.map ([·])
    else sets.lookup (← natural (← (j.getObjVal? "keySet").toOption) protoJson)
  let kind ← responseKind (← (j.getObjVal? "kind").toOption) (expanded && nativeKinds)
  let (path, arm) ← part (← ((j.getObjVal? "scope").toOption <|> (j.getObjVal? "path").toOption)) protoJson
  guard ((j.getObjVal? "scope").isOk == arm.isSome)
  if let .ok spelling := j.getObjVal? "path" then
    guard ((fromJson? (α := Path) spelling).toOption == some path)
  let holes ← (← (repeated (α := Json) j "holes" protoJson).toOption).mapM (part · protoJson)
  checkedGroupValues j keys profile anchor expanded selected kind path arm holes
  return ⟨selected, kind, path, holes.map Prod.fst⟩

def groupedFields (j : Json) (proto : Bool) :=
  fields j proto [("keySets","key_sets")] ["keySets","contexts"]

def contextFields (j : Json) (proto : Bool) :=
  fields j proto [("expireTime","expire_time"), ("requestedAnchors","requested_anchors"),
    ("descendantsOmitted","descendants_omitted")] ["anchor","requestedAnchors","claims","descendantsOmitted"]

def wireList (j : Json) (name : String) (proto : Bool) := repeated (α := Json) j name proto

def decodedAnchor (entry : Json) (proto : Bool) :=
  (entry.getObjVal? "anchor").toOption.bind (anchorPath · proto)

def keyEntry (value : Json) (proto : Bool) : Except String (Nat × List String) := do
  let entry ← fields value proto [] ["keys","id"]
  let some id := natural (← entry.getObjVal? "id") proto | throw "invalid key set id"
  return (id, ← repeated entry "keys" proto)

def TableSource (table : List Json) (proto : Bool) (sets : List (Nat × List String)) : Prop :=
  ∀ pair ∈ sets, ∃ value ∈ table, keyEntry value proto = .ok pair

private def checkedTable (table : List Json) (proto : Bool) :
    Except String {sets : List (Nat × List String) // TableSource table proto sets} := do
  let mut sets : {xs : List (Nat × List String) // TableSource table proto xs} := ⟨[], by simp [TableSource]⟩
  for item in table.attach do
    match parsed : keyEntry item.val proto with
    | .error reason => throw reason
    | .ok pair =>
      let (id,values) := pair
      if id == 0 || id > 2147483647 || (sets.val.lookup id).isSome ||
          !(values.zip (values.drop 1)).all (fun (a,b) => utf16Units a < utf16Units b) then
        throw "invalid key set"
      sets := ⟨pair :: sets.val, by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | old
        · exact ⟨item.val, item.property, parsed⟩
        · exact sets.property p old⟩
  return sets

def Group.expand (g : Group) :=
  g.keys.map fun key => Claim.mk key g.kind g.path g.holes

/-- An accepted claim identifies the original raw context, claim group and key
table entries, including the result of each decoder used to construct it. -/
def RawOrigin (keys : KeyDomains) (input : Json) (native proto : Bool) (anchor : Path) (cl : Claim) : Prop :=
  ∃ wire table sets entries entry ctx claims item profile g,
    groupedFields input proto = .ok wire ∧ wireList wire "keySets" proto = .ok table ∧
    TableSource table proto sets ∧ wireList wire "contexts" proto = .ok entries ∧ entry ∈ entries ∧
    contextFields entry proto = .ok ctx ∧ decodedAnchor ctx proto = some anchor ∧
    wireList ctx "claims" proto = .ok claims ∧ item ∈ claims ∧
    group keys sets profile anchor (wire.getObjVal? "keySets").isOk native proto item = some g ∧ cl ∈ g.expand

private theorem mapM_source {f : α → Option β} {xs : List α} {ys y}
    (mapped : xs.mapM f = some ys) (mem : y ∈ ys) : ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at mapped; subst ys; contradiction
  | cons x xs ih =>
    cases h : f x <;> cases rest : xs.mapM f <;> simp [List.mapM_cons, h, rest] at mapped
    cases mapped
    rcases List.mem_cons.mp mem with rfl | tail
    · exact ⟨x, List.mem_cons_self, h⟩
    · obtain ⟨other, ho, eq⟩ := ih rest tail
      exact ⟨other, List.mem_cons_of_mem _ ho, eq⟩

private def observedOk (r : Except ε α) : Except ε {x // r = .ok x} :=
  match r with
  | .error reason => .error reason
  | .ok value => .ok ⟨value, rfl⟩

private def observedSome (r : Option α) : Option {x // r = some x} :=
  match r with
  | none => none
  | some value => some ⟨value, rfl⟩

/-- Decode normalized claim groups before key expansion loses evidence about
empty sets. The source witnesses are proofs and erase from the executable. -/
private def checkedContexts (keys : KeyDomains) (declared : Option Profile) (input : Json) (nativeKinds protoJson : Bool) :
    Except String (List { c : ClientContext // contextValid keys (declared.getD .scopedClaims) c ∧
      ∀ cl ∈ c.claims, RawOrigin keys input nativeKinds protoJson c.anchor cl }) := do
  let ⟨wire,hw⟩ ← observedOk (groupedFields input protoJson)
  let ⟨table,ht⟩ ← observedOk (wireList wire "keySets" protoJson)
  let sets ← checkedTable table protoJson
  let ⟨entries,he⟩ ← observedOk (wireList wire "contexts" protoJson)
  let mut anchors : List Path := []
  let mut requested : List Path := []
  let mut result := #[]
  for entry in entries.attach do
    let .ok ⟨c,hc⟩ := observedOk (contextFields entry.val protoJson) | continue
    let some ⟨anchor,ha⟩ := observedSome (decodedAnchor c protoJson) | continue
    unless pathOk anchor do continue
    if anchors.contains anchor then throw "duplicate canonical anchor"
    anchors := anchor :: anchors
    let .ok names := repeated (α := Json) c "requestedAnchors" protoJson | continue
    let some asks := names.mapM (anchorPath · protoJson) | continue
    unless asks.all pathOk do continue
    if asks.any requested.contains then throw "duplicate requested anchor"
    requested := asks ++ requested
    unless keys.resources.validSite anchor && asks.all keys.resources.validSite do continue
    let some localProfile := (c.getObjVal? "profile").toOption.mapM
      (responseProfile · (nativeKinds && !protoJson)) | continue
    unless declared.all (fun p => localProfile.all (· == p)) do continue
    let profile := (declared.or localProfile).getD .scopedClaims
    if protoJson && (c.getObjVal? "descendantsOmitted").toOption.any (!·.getBool?.isOk) then continue
    let .ok ⟨raw,hl⟩ := observedOk (wireList c "claims" protoJson) | continue
    if profile == .grantShaped && (c.getObjVal? "requiresScopedClaims").toOption == some (.bool true) then continue
    let some ⟨groups,hg⟩ := observedSome (raw.mapM (group keys sets.val profile anchor (wire.getObjVal? "keySets").isOk nativeKinds protoJson)) | continue
    let claims := groups.flatMap Group.expand
    let expires := match c.getObjVal? "expireTime", c.getObjVal? "expires" with
      | .ok v, _ => some ((timestamp v).getD 0)
      | _, .ok .null => none
      | _, .ok v => some ((timestamp v).getD 0)
      | _, _ => none
    let ctx : ClientContext := ⟨anchor, claims, expires, some asks⟩
    if valid : contextValid keys (declared.getD .scopedClaims) ctx then
      result := result.push ⟨ctx, valid, by
        intro claim incl
        obtain ⟨g, decoded, member⟩ := List.mem_flatMap.mp incl
        obtain ⟨original, fromInput, eq⟩ := mapM_source hg decoded
        exact ⟨wire,table,sets.val,entries,entry.val,c,raw,original,profile,g,hw,ht,sets.property,
          he,entry.property,hc,ha,hl,fromInput,eq,member⟩⟩
  return result.toList

def contexts (keys : KeyDomains) (profile : Option Profile) (wire : Json)
    (nativeKinds : Bool := false) (protoJson : Bool := false) : Except String (List ClientContext) :=
  (checkedContexts keys profile wire nativeKinds protoJson).map (List.map Subtype.val)

def envelope? (raw : Json) (protoJson : Bool := false) : Option SnapshotReply := do
  let j ← (fields raw protoJson [("subjectContextId","subject_context_id"), ("snapshotToken","snapshot_token"),
    ("descriptorEtag","descriptor_etag"), ("expireTime","expire_time")] []).toOption
  let read (name legacy : String) := (j.getObjVal? name).toOption <|>
    (if protoJson then none else (j.getObjVal? legacy).toOption)
  let expiry ← read "expireTime" "expires"
  guard (!protoJson || expiry.getStr?.isOk)
  return { service := ← (j.getObjValAs? String "service").toOption
           descriptorEtag := ← (j.getObjValAs? String "descriptorEtag").toOption
           subject := ← (← read "subjectContextId" "subject").getStr?.toOption
           token := ← (← read "snapshotToken" "token").getStr?.toOption
           expires := ← timestamp expiry
           profile := ← responseProfile (← (j.getObjVal? "profile").toOption) (!protoJson) }

/-- The envelope and the context ledger may arrive together or as separate normalized records. -/
def receive? (keys : KeyDomains) (envelope : Json) (groups : Option Json := none)
    (protoJson : Bool := false) : Option SnapshotReply := do
  let reply ← envelope? envelope protoJson
  let decoded ← (contexts keys reply.profile (groups.getD envelope) groups.isNone protoJson).toOption
  return { reply with contexts := decoded }

theorem received_context_valid {keys envelope groups protoJson reply ctx}
    (received : receive? keys envelope groups protoJson = some reply) (mem : ctx ∈ reply.contexts) :
    contextValid keys reply.profile ctx := by
  unfold receive? at received
  obtain ⟨stamp, _, h⟩ := Option.bind_eq_some_iff.mp received
  obtain ⟨decoded, ok, eq⟩ := Option.bind_eq_some_iff.mp h
  cases eq
  unfold contexts at ok
  cases checked : checkedContexts keys stamp.profile (groups.getD envelope) groups.isNone protoJson with
  | error err => simp [checked, Except.map, Except.toOption] at ok
  | ok values =>
    simp [checked, Except.map, Except.toOption] at ok
    subst decoded
    obtain ⟨c, _, eq⟩ := List.mem_map.mp mem
    exact eq ▸ c.property.1

theorem received_claim_source {keys envelope groups protoJson reply ctx cl}
    (received : receive? keys envelope groups protoJson = some reply)
    (mem : ctx ∈ reply.contexts) (claim : cl ∈ ctx.claims) :
    RawOrigin keys (groups.getD envelope) groups.isNone protoJson ctx.anchor cl := by
  unfold receive? at received
  obtain ⟨stamp, _, h⟩ := Option.bind_eq_some_iff.mp received
  obtain ⟨decoded, ok, eq⟩ := Option.bind_eq_some_iff.mp h
  cases eq
  unfold contexts at ok
  cases checked : checkedContexts keys stamp.profile (groups.getD envelope) groups.isNone protoJson with
  | error err => simp [checked, Except.map, Except.toOption] at ok
  | ok values =>
    simp [checked, Except.map, Except.toOption] at ok
    subst decoded
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp mem
    exact c.property.2 cl claim

end GroupedReply

def Frame.selectContexts (f : Frame) (keys : KeyDomains) (hits : Path → Bool) :=
  f.reply.contexts.filter fun c =>
    f.reply.uniqueContexts && contextValid keys f.reply.profile c && hits c.anchor

def Frame.intersecting (f : Frame) (keys : KeyDomains) (q : Path) : List ClientContext :=
  f.selectContexts keys (intersectsTarget · q)

def winner (history : List Frame) (keys : KeyDomains) (q : Path) :=
  history.find? fun f => !(f.intersecting keys q).isEmpty

structure TimedContext where
  context : ClientContext
  expires : Nat
  profile : Profile
  deriving DecidableEq, Repr

theorem dedup_subset {xs : List α} {r : α → α → Bool} :
    xs.eraseDupsBy r ⊆ xs := by
  have loop (as bs : List α) : ∀ x ∈ List.eraseDupsBy.loop r as bs, x ∈ as ∨ x ∈ bs := by
    induction as generalizing bs with
    | nil => simp [List.eraseDupsBy.loop]
    | cons a as ih =>
      intro x hx
      cases test : bs.any (r a)
      · simp [List.eraseDupsBy.loop, test] at hx
        have mem := ih _ x hx
        simp_all only [List.mem_cons]
        grind
      · simp [List.eraseDupsBy.loop, test] at hx
        have mem := ih _ x hx
        simp_all only [List.mem_cons]
        grind
  intro x hx
  simpa using loop xs [] x hx

/-- Most recent valid context per anchor within the winning snapshot. The history
is ordered by acceptance. Expiration never removes a context from this step. -/
def latestMatching (history : List Frame) (keys : KeyDomains) (hits : Path → Bool) (token : String) :=
  let contexts := history.flatMap fun f =>
    if f.reply.token == token then
      (f.selectContexts keys hits).map fun c => TimedContext.mk c (c.expires.elim f.reply.expires (min f.reply.expires)) f.reply.profile
    else []
  contexts.eraseDupsBy (fun a b => a.context.anchor == b.context.anchor)

def latestContexts (history : List Frame) (keys : KeyDomains) (q : Path) (token : String) :=
  latestMatching history keys (intersectsTarget · q) token

def anyConflict (dom : Domain) (claims : List Claim) :=
  claims.any fun a => a.kind == .allow && claims.any fun d => d.kind == .deny && overlapIn dom a d

def coversTarget (q : Path) (dom : Domain) (c : Claim) :=
  c.path.isPrefixOf (q.takeWhile (· != "-")) && !c.holes.any (fun h => Domain.nonemptyRegion dom h [])

def claimsForKey (key : String) (contexts : List TimedContext) :=
  (contexts.flatMap (·.context.claims)).filter (·.key == key)

/-- Every accepted profile participates in supersession and conflicts. Only live
contexts within the evaluator's ceiling can supply a claim. -/
def TimedContext.usable (now : Nat) (maximum : Option Profile) (c : TimedContext) : Bool :=
  match maximum with
  | some .scopedClaims => now < c.expires
  | some .grantShaped => now < c.expires && c.profile == .grantShaped
  | none => false

def targetVerdict (key : String) (q : Path) (d : Domain) (contexts : List TimedContext) (now : Nat) (maximum : Option Profile := some .scopedClaims) : Verdict :=
  let dom := candidates d q
  let all := claimsForKey key contexts
  let live := claimsForKey key (contexts.filter (TimedContext.usable now maximum))
  if anyConflict dom all then .unloaded
  else if live.any (fun c => c.kind == .allow && coversTarget q dom c) then .allow
  else if live.any (fun c => c.kind == .deny && Domain.nonemptyRegion dom c.path c.holes) then .deny
  else if !q.contains "-" && live.any (fun c => c.kind == .conditional && c.covers q) then .conditional
  else .unloaded

structure Evidence where
  result : Verdict
  token : Option String := none
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

def evaluate (s : ClientState) (keys : KeyDomains) (key : String) (q : Path) (now : Nat) (maximum : Option Profile := some .scopedClaims) : Evidence :=
  match keys.lookup key, winner s.history keys q with
  | some d, some f =>
    if (candidates d q).isEmpty then ⟨.unloaded, none⟩
    else ⟨targetVerdict key q d (latestContexts s.history keys q f.reply.token) now maximum, some f.reply.token⟩
  | _, _ => ⟨.unloaded, none⟩

def reachesScope (d : Domain) (scope anchor : Path) :=
  anchor.isPrefixOf scope || (scope.isPrefixOf anchor && d.any (Pattern.reach · anchor))

/-- Test whether the two subtrees share a binding name outside the holes. -/
def scopeHit (d : Domain) (scope path : Path) (holes : List Path) :=
  if scope.isPrefixOf path then Domain.nonemptyRegion d path holes
  else path.isPrefixOf scope && Domain.nonemptyRegion d scope holes

def scopeConflict (d : Domain) (scope : Path) (claims : List Claim) :=
  claims.any fun a => a.kind == .allow && claims.any fun b => b.kind == .deny &&
    (if a.path.isPrefixOf b.path then scopeHit d scope b.path (a.holes ++ b.holes)
     else b.path.isPrefixOf a.path && scopeHit d scope a.path (a.holes ++ b.holes))

def coversScope (scope : Path) (c : Claim) :=
  c.path.isPrefixOf scope && !c.holes.any (fun h => h.isPrefixOf scope || scope.isPrefixOf h)

def scopeWinner (history : List Frame) (keys : KeyDomains) (d : Domain) (scope : Path) :=
  history.find? fun f => !(f.selectContexts keys (reachesScope d scope)).isEmpty

def scopeVerdict (key : String) (scope : Path) (d : Domain) (contexts : List TimedContext) (now : Nat) (maximum : Option Profile := some .scopedClaims) :=
  let live := claimsForKey key (contexts.filter (TimedContext.usable now maximum))
  if scopeConflict d scope (claimsForKey key contexts) then Verdict.unloaded
  else if live.any (fun c => c.kind == .allow && coversScope scope c) then .allow
  else if live.any (fun c => c.kind == .deny && scopeHit d scope c.path c.holes) then .deny
  else .unloaded

def evaluateScope (s : ClientState) (keys : KeyDomains) (key : String) (scope : Path) (now : Nat) (maximum : Option Profile := some .scopedClaims) : Evidence := Id.run do
  let some d := keys.lookup key | return ⟨.unloaded, none⟩
  unless pathOk scope && d.any (Pattern.reach · scope) do return ⟨.unloaded, none⟩
  let some f := scopeWinner s.history keys d scope | return ⟨.unloaded, none⟩
  return ⟨scopeVerdict key scope d (latestMatching s.history keys (reachesScope d scope) f.reply.token) now maximum,
    some f.reply.token⟩

structure ListedRegion where
  claim : Claim
  token : String
  deriving Repr, DecidableEq

/-- A snapshot participates in discovery as soon as it contains one valid context,
even if that context has expired. Each token keeps its newest serial number. -/
def listingFrames (s : ClientState) (keys : KeyDomains) :=
  (s.history.filter (fun f => !(f.selectContexts keys (fun _ => true)).isEmpty)).eraseDupsBy
    (fun f g => f.reply.token == g.reply.token)

def listingSuperseded (s : ClientState) (keys : KeyDomains) (d : Domain) (f : Frame) (c : Claim) :=
  (listingFrames s keys).any fun newer => newer.serial > f.serial &&
    (latestMatching s.history keys (fun _ => true) newer.reply.token).any fun entry =>
      let a := entry.context.anchor
      d.any (Pattern.reach · a) && (a.isPrefixOf c.path ||
        (c.path.isPrefixOf a && Domain.nonemptyRegion d a c.holes))

def listedClaims (s : ClientState) (keys : KeyDomains) (key : String) (d : Domain) (f : Frame) (now : Nat) (maximum : Option Profile := some .scopedClaims) :=
  let contexts := latestMatching s.history keys (fun _ => true) f.reply.token
  let all := claimsForKey key contexts
  (claimsForKey key (contexts.filter (TimedContext.usable now maximum))).filter fun c =>
    c.kind == .allow && Domain.nonemptyRegion d c.path c.holes &&
    !all.any (fun b => b.kind == .deny && overlapIn d c b) && !listingSuperseded s keys d f c

def usableRegions (s : ClientState) (keys : KeyDomains) (key : String) (now : Nat) (maximum : Option Profile := some .scopedClaims) : List ListedRegion :=
  match keys.lookup key with
  | none => []
  | some d =>
    ((listingFrames s keys).flatMap fun f =>
      (listedClaims s keys key d f now maximum).map fun c => ListedRegion.mk c f.reply.token).eraseDupsBy
      (fun a b => a.token == b.token && a.claim.path == b.claim.path &&
        a.claim.holes.mergeSort == b.claim.holes.mergeSort)

/-- A normalized binding retains the supplied resource name through widening.
A missing list of unresolved positions means its collection/depth is unknown. -/
structure TargetBinding where
  key : String
  source : Path
  patterns : Domain
  targetLength : Nat
  unresolved : Option (List Nat) := some []
  deriving Repr, Lean.FromJson, Lean.ToJson

/-- A caller may supply a wildcard only at an ID slot in a resource name. -/
def Pattern.acceptsSource (p : Pattern) (source : Path) : Bool :=
  p.length == source.length &&
    (p.zip source).all fun (atom, value) => if value == "-" then atom.isVariable else atom.accepts value

def widenName (b : TargetBinding) : Option Path := do
  let positions ← b.unresolved
  let matching := b.patterns.filter (·.acceptsSource b.source)
  guard (!matching.isEmpty && b.targetLength ≤ b.source.length)
  guard (positions.all fun i => matching.all fun p => (p[i]?).any fun a =>
    match a with | .var _ => true | _ => false)
  return (b.source.zipIdx.map (fun (s, i) => if positions.contains i then "-" else s)).take b.targetLength

theorem widenName_outside_patterns (b : TargetBinding)
    (outside : ∀ p ∈ b.patterns, p.acceptsSource b.source = false) : widenName b = none := by
  have empty : b.patterns.filter (·.acceptsSource b.source) = [] :=
    List.filter_eq_nil_iff.mpr fun p hp => by simp [outside p hp]
  cases h : b.unresolved <;> simp [widenName, h, empty, guard, failure]

def evaluateBinding (s : ClientState) (keys : KeyDomains) (b : TargetBinding) (now : Nat) (maximum : Option Profile := some .scopedClaims) : Evidence :=
  match widenName b with
  | none => ⟨.unloaded, none⟩
  | some q =>
    let e := evaluate s keys b.key q now maximum
    if b.unresolved.any (List.any · (· < b.targetLength)) && e.result != .allow then
      { e with result := .unloaded }
    else e

def combine (evidence : List Evidence) : Verdict :=
  if evidence.any (·.result == .deny) then .deny
  else if evidence.any (·.result == .unloaded) then .unloaded
  else if evidence.any (·.result == .conditional) then .conditional
  else match evidence with
    | [] => .unloaded
    | e :: es =>
      if e.token.isSome && (e :: es).all (fun p => p.result == .allow && p.token == e.token)
      then .allow else .unloaded

structure ActiveRequirement where
  info : KeyInfo
  targets : List TargetBinding
  deferBinding : Bool := false
  deriving Repr, Lean.FromJson, Lean.ToJson

def offer (s : ClientState) (keys : KeyDomains) (ceiling : Ceiling)
    (requirements : List ActiveRequirement) (now : Nat) (maximum : Option Profile := some .scopedClaims) : Verdict :=
  if requirements.isEmpty then .defer
  else if requirements.any (fun r => !ceiling.permits r.info) then .deny
  else if requirements.any (fun r => r.deferBinding || r.targets.isEmpty) then .defer
  else combine ((requirements.flatMap (·.targets)).map fun t => evaluateBinding s keys t now maximum)

structure PartialOffer where
  operation : Verdict
  items : List Verdict
  deriving Repr, Lean.FromJson, Lean.ToJson

def offerPartial (s : ClientState) (keys : KeyDomains) (ceiling : Ceiling)
    (operation : List ActiveRequirement) (items : List (List ActiveRequirement)) (now : Nat) (maximum : Option Profile := some .scopedClaims) : PartialOffer :=
  let op := if operation.isEmpty then .allow else offer s keys ceiling operation now maximum
  if op == .deny || op == .defer then ⟨op, items.map fun _ => op⟩
  else if items.isEmpty then ⟨.defer, []⟩ else
    ⟨op, items.map fun rs => if rs.isEmpty then .defer else offer s keys ceiling (operation ++ rs) now maximum⟩

end Authz
