import Authz.ClientSoundness

namespace Authz.WireListExample
open Lean

private def parent : Domain := [[.lit "companies", .var "company"]]
private def widgets : ResourceDecl :=
  ⟨"demo.example/Widget", "widgets", [[.lit "companies", .var "company", .lit "widgets", .var "widget"]], none⟩
private def req : Requirement :=
  {key := "widgets.list", info := ⟨widgets.resourceType, "list", .read, false⟩,
   kind := .parent, field := some "parent", patterns := parent, wildcardVariables := ["company"]}
private def desc : Descriptor :=
  {service := "demo.example", resources := [⟨"demo.example/Company", "companies", parent, none⟩, widgets],
   methods := [{name := "ListWidgets", effect := .readOnly, disposition := .requirements, requirements := [req]}]}
private def view : Query.View := ⟨desc.keyDomains.entries, desc.resourcePatterns, .scopedClaims, fun _ _ => {}, fun _ => false⟩
private def world (grant : Bool) : Query.World :=
  ⟨if grant then [{path := [], keys := ["widgets.list"], effect := .permit}] else [], fun _ => none,
   fun _ _ _ => false, fun _ _ => false⟩
private def stamp : Query.Stamp := ⟨desc.service,"alice","v1","r1",1000⟩
private def request := Json.mkObj [("parent", toJson (["companies","-"] : Path))]
private def state : ClientState := {service := desc.service, session := "session", loadedEtag := some "v1"}
private def interactions (grant : Bool) : Option (MethodOffer × String × String) := do
  let packed ← (Query.queryPermissionContexts view (world grant) stamp [[]]).toOption
  let reply ← GroupedReply.receive? desc.keyDomains packed.protoJson none true
  let cached := acceptSnapshot state (state.dispatch .scopedClaims) reply 1 .scopedClaims
  return (offerRequest desc cached "ListWidgets" request 1 none (fun _ => some []),
          (authorizeRequest desc "ListWidgets" request (world grant).rules).decision,
          decideRequest desc "ListWidgets" request (world grant).rules {})
/- Both outcomes traverse the producer, tagged ProtoJSON, receipt, cache,
method offer, pointwise decision and server interceptor. -/
#guard match interactions true, interactions false with
  | some (.single .allow, "PROCEED", "ALLOW"), some (.single .deny, "DENY", "DENY") => true
  | _, _ => false
end Authz.WireListExample
