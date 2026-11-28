import Authz.Lookup
import Authz.Server
import Authz.SnapshotOrder
import Authz.Query
import Authz.StoreOracle
import Authz.RequestOracle
import Authz.Client
import Authz.Grants
import Authz.Disclosure

namespace Authz.Oracle
open Lean Disclosure

private def field [FromJson α] (j : Json) (name : String) : Except String α :=
  j.getObjValAs? α name

private def optional [FromJson α] (j : Json) (name : String) (fallback : α) : Except String α :=
  match j.getObjVal? name with
  | .ok v => fromJson? v
  | .error _ => pure fallback

structure Delivery where
  ticket : SnapshotTicket
  reply : Json
  now : Nat
  maxProfile : Profile
  expectedService : Option String := none
  grouped : Option Json := none
  protoJson : Bool := false

instance : FromJson Delivery where
  fromJson? j := do
    let ticket : SnapshotTicket ← field j "ticket"
    let expectedService ← match j.getObjVal? "expectedService" with
      | .error _ => pure none
      | .ok value => do
        let .ok name := value.getStr? | throw "invalid expected service"
        pure (some name)
    return {
      ticket
      reply := ← field j "reply"
      now := ← field j "now"
      maxProfile := ← requestedProfile j ticket.maxProfile
      expectedService
      grouped := (j.getObjVal? "grouped").toOption
      protoJson := ← optional j "protoJson" false }

structure Query where
  key : String
  q : Path
  now : Nat
  maximum : Option Profile

instance : FromJson Query where
  fromJson? j := do
    return ⟨← field j "key", ← field j "q", ← field j "now", evaluationProfile j⟩

private def clientDomains (j : Json) : Except String KeyDomains := do
  let entries : List (String × Domain) ← field j "keys"
  return ⟨entries, ← optional j "resources" (entries.flatMap Prod.snd)⟩

/-- Serialized client histories enter the oracle without going through receipt.
Check the service and subject partition and newest-first receipt order. -/
private def clientState (j : Json) (keys : KeyDomains) : Except String ClientState := do
  let raw ← j.getObjVal? "state"
  let _ ← raw.getObj?
  let s : ClientState ← fromJson? (raw.setObjVal! "history" (.arr #[]))
  let mut previous : Option Nat := none
  let mut history := #[]
  for frame in (← optional raw "history" ([] : List Json)) do
    let serial : Nat ← field frame "serial"
    let envelope ← frame.getObjVal? "reply"
    let some r := GroupedReply.envelope? envelope | throw "invalid client history"
    -- A rejected response supplies no coverage to an imported history either.
    let contexts := (GroupedReply.contexts keys r.profile envelope true).toOption.getD []
    let f : Frame := ⟨serial, { r with contexts }⟩
    if s.session.isEmpty || r.service.isEmpty || r.service != s.service ||
        r.subject.isEmpty || some r.subject != s.subject || r.token.isEmpty || r.descriptorEtag.isEmpty ||
        f.serial == 0 || (previous.elim (f.serial != s.serial || some r.token != s.token) (· ≤ f.serial)) then
      throw "invalid client history"
    previous := some f.serial
    history := history.push f
  return { s with history := history.toList }

private def regionsJson (regions : List ListedRegion) :=
  toJson (regions.map fun r => Json.mkObj [("path", toJson r.claim.path),
    ("holes", toJson r.claim.holes), ("token", toJson r.token)])

def trace (j : Json) : Except String Json := do
  let mut state : ClientState := { service := ← field j "service", session := ← field j "session" }
  let mut actions := #[]
  let keys ← clientDomains j
  for e in (← field j "events" : List Delivery) do
    let some reply := GroupedReply.receive? keys e.reply e.grouped e.protoJson | do
      actions := actions.push .discard
      continue
    actions := actions.push (snapshotAction state e.ticket reply e.now e.maxProfile e.expectedService)
    state := acceptSnapshot state e.ticket reply e.now e.maxProfile e.expectedService
  let results := (← field j "queries" : List Query).map fun q =>
    (evaluate state keys q.key q.q q.now q.maximum).result
  let scopes ← optional j "scopes" ([] : List Query)
  let listings ← optional j "listings" ([] : List Query)
  let scopeResults := scopes.map fun q => evaluateScope state keys q.key q.q q.now q.maximum
  let regions := listings.map fun q => regionsJson (usableRegions state keys q.key q.now q.maximum)
  return Json.mkObj [("actions", toJson actions), ("results", toJson results),
    ("scopes", toJson scopeResults), ("listings", toJson regions)]

structure AliasMapping where
  supplied : Path
  canonical : Option Path
  visible : Option Bool := none
  deriving FromJson

private structure OwnedAlias where
  subject : String
  supplied : Path
  target : Path
  deriving FromJson, BEq

private structure ReadableTarget where
  subject : String
  target : Path
  deriving FromJson, BEq

/-- Both lists contain observations supplied for this request. Old fixtures use
mapping.visible to represent an authorized current read by their sole caller. -/
private def aliasWorld (j : Json) (subject : String) (mappings : List AliasMapping)
    (rules : List Rule) : Except String Query.World := do
  let owned : List OwnedAlias ← optional j "ownedAliases" []
  let legacyReads := mappings.filterMap fun row =>
    if row.visible == some true then row.canonical.map (ReadableTarget.mk subject) else none
  let reads : List ReadableTarget ← optional j "readableTargets" legacyReads
  return { rules, resolve := fun p => (mappings.find? (·.supplied == p)).bind (·.canonical)
           ownsAlias := fun who supplied target => owned.contains ⟨who, supplied, target⟩
           canReadNow := fun who target => reads.contains ⟨who, target⟩ }

private def deploymentNames (j : Json) : NameResolver := Id.run do
  let some raw := (optional j "asWritten" ([] : Domain)).toOption | return {configured := false}
  let some types := (optional j "asWrittenTypes" ([] : List String)).toOption | return {configured := false}
  unless raw.all (fun pat => pat.all Atom.valid) do return {configured := false}
  if types.isEmpty then return {asWritten := raw}
  let .ok d := field (α := Descriptor) j "descriptor" | return {configured := false}
  let some declared := asWrittenDomain? d.resources types | return {configured := false}
  return {asWritten := raw ++ declared}

private def resolve (j : Json) : Except String Json := do
  let rows : List AliasMapping ← field j "mappings"
  let indirect : List Path ← field j "indirect"
  let subject ← optional j "subject" ""
  let names := deploymentNames j
  let view : Query.View := {
    resources := ← field j "resources", keys := [], profile := .scopedClaims
    options := fun _ _ => {}, indirect := fun p => !Domain.contains names.asWritten p && indirect.contains p }
  let world ← aliasWorld j subject rows []
  match Query.requestedNames view world subject [← field j "source"] with
  | .error status => return Json.mkObj [("error", toJson status.code)]
  | .ok resolved => return if names.configured then toJson (resolved.head?.map Prod.snd)
        else Json.mkObj [("error", toJson Disclosure.Status.serverFault.code)]

private def checkObservations [BEq α] [BEq β] (fieldName : String) (xs : List (α × β)) : Except String Unit := do
  unless xs.all (fun (key, value) => xs.lookup key == some value) do
    throw s!"conflicting observations in {fieldName}"

/-- Without a visibility adapter, only explicitly invisible sites are withheld.
A configured adapter must confirm the exact rule path before it may be named. -/
private def nameVisibility (j : Json) : Except String (Path → Bool) := do
  let invisible : List Path ← optional j "invisible" []
  let .ok wire := j.getObjVal? "nameVisibility" | return fun path => !invisible.contains path
  if wire == .null then return fun _ => false
  let observed : List (Path × Option Bool) ← fromJson? wire
  checkObservations "nameVisibility" observed
  return fun path => !invisible.contains path && (observed.lookup path).join == some true

private def queryResponse (j : Json) : Except String Json := do
  let keys ← field j "keys"
  let resources ← field j "resources"
  let profile ← field j "profile"
  let hiddenKeys : List String ← optional j "privateKeys" []
  let boundary : Nat ← optional j "boundaryDepth" 0
  let budget : Option Nat ← optional j "budget" none
  let canName ← nameVisibility j
  let indirect : List Path ← optional j "indirect" []
  let mappings : List AliasMapping ← optional j "mappings" []
  let names := deploymentNames j
  let view : Query.View := {
    keys, resources, profile, indirect := fun p => !Domain.contains names.asWritten p && indirect.contains p
    options := fun a k => { nonprojecting := hiddenKeys.contains k && a.length < boundary, canName, budget } }
  let stamp : Query.Stamp ← field j "stamp"
  let world ← aliasWorld j stamp.subject mappings (← field j "rules")
  let protoJson ← optional j "protoJson" false
  match Query.queryPermissionContexts view world stamp (← field j "asked") with
  | .ok r => return if names.rulesAllowed resources world.rules then (if protoJson then r.protoJson else toJson r)
        else Json.mkObj [("error", toJson Disclosure.Status.serverFault.code)]
  | .error e => return Json.mkObj [("error", toJson e.code)]

def factsFrom (j : Json) : Except String Facts := do
  let predicates : List (String × Bool) ← optional j "predicates" []
  let faults : Option (List Rule) ← optional j "faults" none
  let outcomes : Option (List (Rule × Option Bool)) ← optional j "faultOutcomes" none
  let faults := faults.map (List.map Rule.faultIdentity)
  let outcomes := outcomes.map (List.map fun (r, b) => (r.faultIdentity, b))
  checkObservations "predicates" predicates
  checkObservations "faultOutcomes" (outcomes.getD [])
  return {
    predicate := fun k => predicates.lookup k
    faults := fun r => outcomes.elim (faults.map (·.contains r)) (fun xs => (xs.lookup r).join) }

private structure FaultAtPath where
  path : Path
  rule : Rule
  fault : Option Bool := none
  deriving FromJson

/-- Read the caller-facing class strings and typed entries independently of
the JavaScript credential normalizer. -/
private def wireCredential (opts : Json) : Except String Ceiling := do
  let wire := (opts.getObjVal? "ceiling").toOption.getD .null
  if wire == .null then
    let hint := (opts.getObjVal? "readOnlyCredential").toOption.getD .null
    if hint == .null then return none
    return if ← hint.getBool? then some [⟨none, .read⟩] else none
  let values ← wire.getArr?
  return some (← values.toList.mapM fun entry => do
    let (type, name) ← match entry with
      | .str name => pure (none, name)
      | _ => do
        let type : String ← field entry "type"
        let name : String ← field entry "cls"
        unless type == "*" || fullTypeOk type ||
          (type.dropSuffix? "/service").any (fun service => serviceNameOk service.toString)
          do throw "invalid ceiling resource type"
        pure (if type == "*" then none else some type, name)
    unless name == name.toUpper do throw "invalid ceiling class"
    let cls ← fromJson? (α := AccessClass) (Json.str name.toLower)
    return ⟨type, cls⟩)

private def callerCredential (j : Json) : Except String Ceiling :=
  match j.getObjVal? "credential" with
  | .ok wire => wireCredential wire
  | .error _ => optional j "ceiling" none

private def serverOptions (j : Json) : Except String ServerOptions := do
  let facts ← factsFrom j
  let supplied ← optional j "knownFacts" false
  let owners : List (Path × Bool) ← optional j "factsByPath" []
  let reads : Option (List (Path × Bool)) ← optional j "rowReads" none
  let failedRows : List Path ← optional j "failedRows" []
  let faulty : Option (List (Path × Rule)) ← optional j "faultsByPath" none
  let rows : Option (List FaultAtPath) ← optional j "faultOutcomesByPath" none
  let faulty := faulty.map (List.map fun (p, r) => (p, r.faultIdentity))
  let outcomes := rows.map (List.map (fun x => ((x.path, x.rule.faultIdentity), x.fault)))
  checkObservations "factsByPath" owners
  checkObservations "rowReads" (reads.getD [])
  if let some observed := reads then
    unless supplied && owners.all (fun (p, _) => observed.lookup p == some true) do
      throw "rowReads requires a configured reader; owner facts require a successful read"
  checkObservations "faultOutcomesByPath" (outcomes.getD [])
  let names := deploymentNames j
  let aliases : List (Path × Option Path) ← optional j "names" []
  let resolverErrors : List Path ← optional j "resolverErrors" []
  let invalidResolver : Bool ← optional j "invalidNameResolver" false
  let privateKeys : List String ← optional j "nonprojectingKeys" []
  let privateRegions : List (String × Path) ← optional j "nonprojectingRegions" []
  let privateDepth : Nat ← optional j "nonprojectingDepth" 0
  let globalFaults := ["faults", "faultOutcomes"].any fun k => (j.getObjVal? k).toOption.any (· != Json.null)
  let hasFaults ← optional j "hasFaults" (outcomes.isSome || faulty.isSome || globalFaults)
  let faultsAt := fun (p : Path) (r : Rule) => outcomes.elim
    (faulty.elim (facts.faults r) (fun xs => some (xs.contains (p,r))))
    (fun xs => (xs.lookup (p,r)).join)
  let atPath := fun (p : Path) => {
    predicate := fun k => if k == "owner" then (owners.lookup p).or (facts.predicate k) else facts.predicate k }
  return {
    mode := ← optional j "authority" .failClosed
    factsOf := if supplied then some atPath else none
    rowReadFailed := fun p => failedRows.contains p || reads.any fun observed => observed.lookup p != some true
    faultsOf := if hasFaults then some faultsAt else none
    names := { names with
               indirect := fun p => (aliases.lookup p).isSome, lookup := fun p => (aliases.lookup p).join,
               failed := fun p => invalidResolver || resolverErrors.contains p }
    ceiling := (callerCredential j).toOption.getD (some [])
    nonprojecting := fun k p => p.length < privateDepth || privateKeys.contains k || privateRegions.contains (k,p)
    canName := ← nameVisibility j
    handlerResolvesResiduals := ← optional j "handlerResolvesResiduals" false }

def handle (j : Json) : Except String Json := do
  match (← field j "op" : String) with
  | "segment" => return toJson (segmentOk (← field j "value"))
  | "contextValid" => return toJson (contextValid (← clientDomains j) (← field j "profile") (← field j "context"))
  | "descriptor" => return toJson ((← field j "descriptor" : Descriptor).valid)
  | "searchRefusedUpFront" =>
    let d : Descriptor ← field j "descriptor"
    let key : String ← field j "key"
    let some r := d.requirements.find? (·.key == key) | return toJson false
    return toJson (searchRefusedUpFront d (← field j "rules") r (← field j "parent") (← serverOptions j))
  | "region" => return toJson (Domain.nonemptyRegion (← field j "domain") (← field j "path") (← field j "holes"))
  | "regionAllowed" =>
    let d : Descriptor ← field j "descriptor"
    let key : String ← field j "key"
    let some requirement := d.requirements.find? (·.key == key) | return toJson false
    return toJson (d.valid && regionAllowed d (← field j "rules") requirement (← field j "path")
      (← optional j "subtree" false) (← serverOptions j))
  | "validateRoleSelectors" => return toJson (validateRoleSelectors (← field j "descriptor") (← field j "selectors"))
  | "expand" => return toJson (expandedKeys (← field j "descriptor") (← field j "grant"))
  | "grantPolicy" =>
    let gs : List Grant ← field j "grants"
    let c : Ceiling ← optional j "ceiling" none
    let rules := rulesFromGrants (← field j "descriptor") gs c
    let mode ← optional j "authority" .failClosed
    let facts ← factsFrom j
    let key ← field j "key"
    let target ← field j "path"
    return toJson (rules.elim Decision.deny fun rs => decide mode facts rs key target)
  | "decide" => return toJson (decide (← optional j "authority" .failClosed)
      (← factsFrom j) (← field j "rules") (← field j "key") (← field j "path"))
  | "project" =>
    let options : ProjectOptions := {
      profile := ← optional j "profile" .scopedClaims
      nonprojecting := ← optional j "nonprojecting" false, canName := ← nameVisibility j,
      budget := ← optional j "budget" none }
    let domain ← field j "domain"
    let resources ← optional j "resources" domain
    let rules ← field j "rules"
    unless (deploymentNames j).rulesAllowed resources rules do return toJson ({} : KeyProjection)
    return toJson (projectResourceKey rules (← field j "key") (← field j "path") domain options resources)
  | "minSnapshot" => return toJson (serveWithMinSnapshot (← field j "server") (← field j "floor"))
  | "trace" => trace j
  | "evaluate" =>
    let keys ← clientDomains j
    return toJson (evaluate (← clientState j keys) keys
      (← field j "key") (← field j "target") (← field j "now") (evaluationProfile j))
  | "evaluateScope" =>
    let keys ← clientDomains j
    return toJson (evaluateScope (← clientState j keys) keys
      (← field j "key") (← field j "scope") (← field j "now") (evaluationProfile j))
  | "usableRegions" =>
    let keys ← clientDomains j
    return regionsJson (usableRegions (← clientState j keys) keys
      (← field j "key") (← field j "now") (evaluationProfile j))
  | "bindings" | "effectiveMask" => RequestOracle.handle j
  | "methodAvailable" =>
    let .ok ceiling := callerCredential j | return .bool false
    let d : Descriptor ← field j "descriptor"
    return toJson (methodAvailable (d.method? (← field j "method")) ceiling)
  | "fixtureOffer" =>
    let .ok ceiling := callerCredential j | return toJson Verdict.unavailable
    RequestOracle.fixtureOffer j ceiling
  | "store" => storeHandle j
  | "query" => queryResponse j
  | "lookupRequest" => lookupHandle j (← serverOptions j)
  | "resolve" => resolve j
  | "methodOffer" =>
    let .ok ceiling := callerCredential j | return toJson Verdict.unavailable
    let mappings : List (Path × Option (List Nat)) ← optional j "unresolved" []
    let d : Descriptor ← field j "descriptor"
    let result := offerRequest d (← clientState j d.keyDomains)
      (← field j "method") (← field j "request") (← field j "now")
      ceiling (fun path => (mappings.lookup path).getD (some [])) (maximum := evaluationProfile j)
    match result with
    | .single v => return toJson v
    | .partialBatch v => return toJson v
  | "authorize" =>
    let d : Descriptor ← field j "descriptor"
    let method ← field j "method"
    if (← optional j "invalidAttrsOf" false) && (d.method? method).any (·.disposition == .requirements) then
      return toJson ({decision := "DENY", reason := some "SERVER_FAULT"} : Authorization)
    return toJson (authorizeRequest d method (← field j "request") (← field j "rules") (← serverOptions j))
  | "batchRequest" =>
    if ← optional j "invalidAttrsOf" false then return toJson Status.denied.code
    return toJson (batchRequestStatus (← field j "descriptor")
      (← field j "method") (← field j "request") (← field j "rules") (← serverOptions j)).code
  | "decideRequest" =>
    let d : Descriptor ← field j "descriptor"
    let method ← field j "method"
    if (← optional j "invalidAttrsOf" false) && (d.method? method).any (·.disposition == .requirements) then return "DENY"
    return toJson (decideRequest d method (← field j "request") (← field j "rules")
      (← serverOptions j) (← optional j "filterHandled" true))
  | "widenName" => return toJson (widenName (← field j "binding"))
  | "offer" =>
    let keys ← clientDomains j
    return toJson (offer (← clientState j keys) keys
      (← optional j "ceiling" none) (← field j "requirements") (← field j "now") (evaluationProfile j))
  | "offerPartial" =>
    let keys ← clientDomains j
    return toJson (offerPartial (← clientState j keys) keys
      (← optional j "ceiling" none) (← field j "operation") (← field j "items") (← field j "now") (evaluationProfile j))
  | "read" => return toJson (readStatus (← field j "exists") (← field j "target") (← field j "parentList")).code
  | "create" => return toJson (createStatus (← field j "authorized") (← field j "taken")
      (← field j "getExisting") (← field j "listParent")).code
  | "zeroMatch" => return toJson (zeroMatchStatus (← optional j "query" {})).code
  | "wildcardGet" =>
    let q ← optional j "query" Json.null
    let count := (q.getObjVal? "matches").toOption.bind (fun v => v.getNat?.toOption)
    let answer := if count == some 0 then zeroMatchStatus (ZeroMatch.ofJson q true)
      else if count == some 1 && (q.getObjVal? "target").toOption == some (.str "allow") then Status.ok
      else Status.denied
    return toJson answer.code
  | "error" => return toJson (errorPayload (← field j "status") (← field j "domain") (← field j "key") (← field j "supplied"))
  | "batch" =>
    let items ← field j "items"
    let universal ← field j "parentUniversal"
    let valid ← optional j "valid" true
    return toJson (batchStatus (← optional j "operationAllowed" true) (fun _ => items)
      (fun _ => universal) (fun _ => valid)).code
  | op => throw s!"unknown oracle operation {op}"

end Authz.Oracle
