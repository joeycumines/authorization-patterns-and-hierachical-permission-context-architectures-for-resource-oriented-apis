import Authz.Request

namespace Authz.RequestOracle
open Lean

private def bindingSummary (r : BoundRequirement) : Json :=
  let ts := r.targets.map (fun (i,b) => (i,b.target))
  let indices := if r.derivedGuard then ((ts.map Prod.fst) ++ r.unboundItems).eraseDups
                 else ts.map Prod.fst
  let targets := ts.map Prod.snd
  Json.mkObj [("key", toJson r.decl.key), ("perItem", toJson r.decl.perItem),
    ("targets", toJson (if r.derivedGuard then targets.eraseDups else targets)),
    ("items", toJson indices), ("unboundItems", toJson r.unboundItems), ("unbound", toJson r.unbound),
    ("wildcard", toJson r.wildcard)]

private def effective (j : Json) : Except String Json := do
  let fs : List FieldMeta ← j.getObjValAs? _ "fields"
  let body ← j.getObjVal? "request"
  let optStrings (key : String) : Except String (Option (List String)) :=
    (body.getObjVal? key).toOption.mapM (fun v => fromJson? v)
  match optStrings "mask", optStrings "populated" with
  | .ok mask, .ok pop =>
    if body.getObj?.isOk then
      return toJson (FieldGuards.effectiveMask fs mask pop ((requestField body "allow_missing") == .bool true))
    return toJson ((FieldGuards.writable fs (fs.map (·.path))).mergeSort)
  | _, _ => return toJson ((FieldGuards.writable fs (fs.map (·.path))).mergeSort)

/-- Legacy §4.6 examples identify a stored frame by its sequence. A missing
frame profile leaves each context responsible for its own claim shape. The
frame can participate under a Scoped Claims ceiling. -/
private def storedFrame? (d : Descriptor) (frame : Json) : Option SnapshotReply := do
  let seq ← (frame.getObjValAs? Nat "seq").toOption
  guard (seq > 0 && seq ≤ 9007199254740991)
  if ["service","subjectContextId","snapshotToken","descriptorEtag"].any (frame.getObjVal? · |>.isOk) then
    return ← GroupedReply.receive? d.keyDomains frame
  let stamp := Json.mkObj [("service", toJson d.service), ("subject", "fixture"),
    ("token", toJson ("fixture-" ++ toString seq)), ("descriptorEtag", "fixture"),
    ("expires", (frame.getObjVal? "expireTime").toOption.getD (toJson 9007199254740991)),
    ("profile", (frame.getObjVal? "profile").toOption.getD "SCOPED_CLAIMS")]
  let reply ← GroupedReply.envelope? stamp
  let declared := (frame.getObjVal? "profile").toOption.map fun _ => reply.profile
  let contexts ← (GroupedReply.contexts d.keyDomains declared frame).toOption
  return {reply with contexts}

def fixtureOffer (j : Json) (ceiling : Ceiling) : Except String Json := do
  let d : Descriptor ← j.getObjValAs? _ "descriptor"
  let mut state : ClientState := {service := d.service, session := "fixture-replay"}
  let deliveries : List Json ← j.getObjValAs? _ "deliveries"
  for value in deliveries do
    if let some reply := storedFrame? d value then
      state := acceptSnapshot state (state.dispatch .scopedClaims) reply 0
  let mappings : List (Path × Option (List Nat)) ← j.getObjValAs? _ "unresolved"
  let defaultPositions : Option (List Nat) ← fromJson? ((j.getObjVal? "unresolvedDefault").toOption.getD (.arr #[]))
  let result := offerRequest d state (← j.getObjValAs? _ "method") (← j.getObjVal? "request")
    (← j.getObjValAs? _ "now") ceiling
    (fun p => (mappings.lookup p).getD defaultPositions) (maximum := evaluationProfile j)
  match result with
  | .single v => return toJson v
  | .partialBatch v => return toJson v

def handle (j : Json) : Except String Json := do
  match ← j.getObjValAs? String "op" with
  | "effectiveMask" => effective j
  | "bindings" =>
    let d : Descriptor ← j.getObjValAs? _ "descriptor"
    let m := d.method? (← j.getObjValAs? _ "method")
    let some m := m.filter (·.disposition == .requirements) | return .null
    return toJson ((requirementsFor d m (← j.getObjVal? "request")).map bindingSummary)
  | op => throw s!"unknown request operation {op}"

end Authz.RequestOracle
