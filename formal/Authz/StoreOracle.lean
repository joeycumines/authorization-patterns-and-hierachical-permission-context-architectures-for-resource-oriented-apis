import Authz.PolicyStore

namespace Authz.Oracle
open Lean

private structure StoreProjection where
  subject : String
  key : String
  anchor : Path
  domain : Domain
  budget : Nat
  profile : Option Profile := none
  deriving FromJson

/-- Return the acceptance decision and resulting effective rules for each commit.
Rejecting a transaction retains all rules and visibility from the preceding state. -/
def storeHandle (request : Json) : Except String Json := do
  let raw ← request.getObjVal? "store"
  let fields ← raw.getObj?
  let stored := if fields.contains "asWrittenTypes" then raw else raw.setObjVal! "asWrittenTypes" (.arr #[])
  let initial : PolicyStore ← fromJson? stored
  unless initial.admissible do throw "initial policy store violates the authoring invariant"
  let transactions ← request.getObjValAs? (List (List PolicyEdit)) "transactions"
  let subjects ← request.getObjValAs? (List String) "subjects"
  let projection : Option StoreProjection ← fromJson? ((request.getObjVal? "projection").toOption.getD .null)
  let mut state := initial
  let mut results := #[]
  for writes in transactions do
    let candidate := writes.foldl PolicyStore.edit state
    state := state.commit writes
    let observed := projection.toList.map fun q =>
      let opts := state.projectionOptions q.subject q.anchor q.key { budget := some q.budget, profile := q.profile.getD .scopedClaims }
      let resources := state.catalog.flatMap ResourceDecl.patterns
      ("projection", toJson (projectResourceKey (state.rulesFor q.subject) q.key q.anchor q.domain opts resources))
    results := results.push (Json.mkObj (observed ++ [
      ("accepted", toJson candidate.admissible),
      ("rules", toJson (subjects.map state.rulesFor)),
      ("store", toJson state)]))
  return Json.arr results

end Authz.Oracle
