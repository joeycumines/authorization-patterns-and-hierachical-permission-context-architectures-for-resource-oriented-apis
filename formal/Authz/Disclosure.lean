import Lean

/-! Observable server replies at the normalized lookup boundary (§3.4 and §4.3).
The caller supplies the name echoed in an error. A lookup supplies only the
row under the addressed parent, or the canonical name of an indirect prefix. -/
namespace Authz.Disclosure

inductive Status where
  | ok | denied | notFound | alreadyExists | invalidArgument | serverFault
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

def Status.code : Status → String
  | .ok => "OK"
  | .denied => "PERMISSION_DENIED"
  | .notFound => "NOT_FOUND"
  | .alreadyExists => "ALREADY_EXISTS"
  | .invalidArgument => "INVALID_ARGUMENT"
  | .serverFault => "SERVER_FAULT"

structure Metadata where
  permission : String
  resource : String
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

structure ErrorInfo where
  code : String
  message : String
  reason : String
  domain : String
  metadata : Metadata
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

def errorPayload (status : Status) (domain key supplied : String) : ErrorInfo :=
  let message := if status != .denied then status.code else if supplied.isEmpty then
    s!"Permission '{key}' denied (or the resource might not exist)."
    else s!"Permission '{key}' denied on resource '{supplied}' (or it might not exist)."
  ⟨status.code, message, if status == .denied then "AUTHZ_DENIED" else status.code,
    domain, ⟨key, supplied⟩⟩

inductive Knowledge where
  | allow | deny | needsRow
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

def readStatus (exists_ : Bool) (target : Knowledge) (parentList : Bool) : Status :=
  if exists_ then (if target == .allow then .ok else .denied)
  else match target with
    | .allow => .notFound
    | .deny => .denied
    | .needsRow => if parentList then .notFound else .denied

structure Row where
  parent : List String
  id : String
  allowed : Bool
  deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

def lookup (parent : List String) (id : String) (rows : List Row) : Option Row :=
  rows.find? (fun r => r.parent == parent && r.id == id)

def read (nameDecision : Knowledge) (parentList : Bool) (row : Option Row) : Status :=
  let target := match nameDecision, row with
    | .needsRow, some r => if r.allowed then .allow else .deny
    | d, _ => d
  readStatus row.isSome target parentList

/-- An absent row, and a present row denied by its attribute policy, are
indistinguishable to a caller who cannot discover the row by listing. -/
theorem hidden_read (r : Row) (hidden : r.allowed = false) (domain key supplied : String) :
    errorPayload (read .needsRow false (some r)) domain key supplied =
    errorPayload (read .needsRow false none) domain key supplied := by
  simp [read, readStatus, hidden]

theorem denied_read (row : Option Row) (domain key supplied : String) :
    errorPayload (read .deny false row) domain key supplied =
    errorPayload .denied domain key supplied := by
  cases row <;> rfl

theorem other_collection (r : Row) (rows : List Row) (parent : List String) (id : String)
    (other : r.parent ≠ parent) :
    lookup parent id (r :: rows) = lookup parent id rows := by
  simp [lookup, other]

def createStatus (authorized taken getExisting listParent : Bool) : Status :=
  if !authorized then .denied else if !taken then .ok
  else if getExisting || listParent then .alreadyExists else .denied

theorem hidden_collision_denial_payload (domain key supplied : String) :
    errorPayload (createStatus true true false false) domain key supplied =
    errorPayload (createStatus false false false false) domain key supplied := rfl

/-- With create permission but no discovery permission, the same caller
succeeds on a free ID and receives an opaque denial on a hidden collision. -/
theorem authorized_create_distinguishes :
    createStatus true false false false = .ok ∧
    createStatus true true false false = .denied := by decide

structure ZeroMatch where
  region : Knowledge := .needsRow
  regionList : Knowledge := .needsRow
  regionGet : Knowledge := .needsRow
  nonprojectingKey : Bool := false
  nonprojectingList : Bool := false
  nonprojectingGet : Bool := false
  regionDenyFinal : Bool := false
  deleteAllowMissing : Bool := false
  deriving Repr, Lean.ToJson

/-- Decode the standalone lookup evidence. A missing privacy flag inherits the
deployment default; a present value establishes public visibility only if false. -/
def ZeroMatch.ofJson (j : Lean.Json) (wildcardGet := false) : ZeroMatch :=
  let value := fun name => (j.getObjVal? name).toOption
  let knowledge := fun name => ((value name).bind (fun v => (Lean.fromJson? v).toOption)).getD Knowledge.needsRow
  let restrictive := fun v => v != Lean.Json.bool false
  let fallback := (value "nonprojecting").any restrictive
  let privateFor := fun (keys : List String) => match keys.filterMap value with
    | [] => fallback
    | flags => flags.any restrictive
  let key := privateFor (if wildcardGet then ["nonprojectingKey","nonprojectingGet"] else ["nonprojectingKey"])
  { region := knowledge (if wildcardGet then "regionGet" else "region")
    regionList := knowledge "regionList", regionGet := knowledge "regionGet"
    nonprojectingKey := key, nonprojectingList := privateFor ["nonprojectingList"]
    nonprojectingGet := if wildcardGet then key else privateFor ["nonprojectingGet"]
    regionDenyFinal := (value "regionDenyFinal").any restrictive
    deleteAllowMissing := !wildcardGet && value "deleteAllowMissing" == some (.bool true) }

instance : Lean.FromJson ZeroMatch where
  fromJson? j := pure (ZeroMatch.ofJson j)

def zeroMatchStatus (q : ZeroMatch) : Status :=
  let absent := if q.deleteAllowMissing then Status.ok else .notFound
  if q.regionDenyFinal then .denied
  else if !q.nonprojectingKey && q.region == .deny then .denied
  else if (!q.nonprojectingKey && q.region == .allow) ||
          (!q.nonprojectingList && q.regionList == .allow) ||
          (!q.nonprojectingGet && q.regionGet == .allow) then absent
  else .denied

theorem zeroMatch_private (q : ZeroMatch) (a b : Knowledge) :
    zeroMatchStatus { q with region := a, nonprojectingKey := true } =
    zeroMatchStatus { q with region := b, nonprojectingKey := true } := by
  simp [zeroMatchStatus]

theorem hidden_indirect_read (q : ZeroMatch) (hfinal : q.regionDenyFinal = false)
    (hk : q.nonprojectingKey = true ∨ q.region ≠ .allow)
    (hl : q.nonprojectingList = true ∨ q.regionList ≠ .allow)
    (hg : q.nonprojectingGet = true ∨ q.regionGet ≠ .allow)
    (domain key supplied : String) :
    errorPayload (zeroMatchStatus q) domain key supplied =
    errorPayload (readStatus true .deny false) domain key supplied := by
  rcases hk with hk | hk <;> rcases hl with hl | hl <;> rcases hg with hg | hg <;>
    simp [zeroMatchStatus, hfinal, hk, hl, hg, readStatus]

/-- Batch item data after the descriptor has bound its required names.
Evaluation of the outer operation precedes any item lookup. The final
validation thunk includes duplicate IDs and parent/child consistency. -/
structure BatchItem where
  bindable : Bool
  authorized : Bool
  valid : Bool
  deriving Repr, Lean.FromJson, Lean.ToJson

def batchStatus (operationAllowed : Bool) (items : Unit → List BatchItem)
    (parentUniversal : Unit → Bool) (valid : Unit → Bool) : Status :=
  if !operationAllowed then .denied
  else
    let bound := items ()
    if bound.any (fun i => i.bindable && !i.authorized) then .denied
    else if bound.isEmpty || bound.any (fun i => !i.bindable) then
      if parentUniversal () then .invalidArgument else .denied
    else if valid () && bound.all (·.valid) then .ok else .invalidArgument

theorem batch_outer_denied (items : Unit → List BatchItem) (parent valid : Unit → Bool) :
    batchStatus false items parent valid = .denied := rfl

abbrev NamePath := List String
abbrev Resolver := NamePath → Option NamePath

/-- Syntactically direct segments (including as-written secondary keys) do
not invoke storage. Every indirect prefix is resolved and visibility-gated
before the next segment is appended. -/
def resolvePrefix (indirect : NamePath → Bool) (resolve : Resolver)
    (mayResolve : NamePath → NamePath → Bool) (p : NamePath) : Option NamePath :=
  if indirect p then (resolve p).filter (mayResolve p) else some p

def resolveAnchor (indirect : NamePath → Bool) (resolve : Resolver)
    (mayResolve : NamePath → NamePath → Bool) (base : NamePath) : List String → Option NamePath
  | [] => some base
  | s :: rest => (resolvePrefix indirect resolve mayResolve (base ++ [s])).bind fun canonical =>
      resolveAnchor indirect resolve mayResolve canonical rest

/-- Twin stores agree on visible mappings. They can contain arbitrarily
different missing, hidden and redirected prefixes, including nested aliases. -/
theorem anchor_opacity (indirect : NamePath → Bool) (a b : Resolver)
    (visibleA visibleB : NamePath → NamePath → Bool)
    (low : ∀ p, indirect p = true → (a p).filter (visibleA p) = (b p).filter (visibleB p))
    (rest base : NamePath) :
    resolveAnchor indirect a visibleA base rest = resolveAnchor indirect b visibleB base rest := by
  induction rest generalizing base with
  | nil => rfl
  | cons s rest ih =>
    have same : resolvePrefix indirect a visibleA (base ++ [s]) =
        resolvePrefix indirect b visibleB (base ++ [s]) := by
      unfold resolvePrefix
      split
      · exact low _ (by assumption)
      · rfl
    simp only [resolveAnchor, same]
    cases resolvePrefix indirect b visibleB (base ++ [s]) with
    | none => rfl
    | some c => exact ih c

end Authz.Disclosure
