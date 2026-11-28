import Authz.Client
import Authz.FieldGuards

/-! The request adapter accepts the same flattened fields as §4.6. A field such
as `requests[].widget.name` is an array of segment lists. Missing slots keep their
original item index through conditional requirements and partial-success offers. -/
namespace Authz
open Lean (Json)

def Descriptor.keyDomains (d : Descriptor) : KeyDomains :=
  ⟨(d.requirements.map (·.key)).eraseDups.map (fun k => (k, d.domain k)), d.resourcePatterns⟩

def Descriptor.method? (d : Descriptor) (name : String) :=
  d.methods.find? (·.name == name)

/-- Older normalized descriptors retained typed request fields only on permission
bindings. An explicit schema classification takes precedence, including when
the schema identified a custom or streaming RPC. -/
def MethodDecl.addressedTarget? (m : MethodDecl) (d : Descriptor) : Option ResourceTarget := do
  guard (!m.partialSource.any (fun source => source.clientStreaming.getD false || source.serverStreaming.getD false))
  if m.requestFields.isSome || m.requestShapeKnown == some true || m.resourceTarget.isSome then return ← m.resourceTarget
  let rpc ← (m.name.splitOn "/").getLast?
  m.requirements.findSome? fun r => do
    guard (!r.perItem && !r.parentOf && r.condition.isNone)
    let res ← d.resources.find? (·.resourceType == r.info.resourceType)
    let singular ← (res.resourceType.splitOn "/").getLast?
    let singularName := r.kind == .resource && r.field == some "name" &&
      (rpc == "Get" ++ singular || rpc == "Delete" ++ singular)
    let list := res.plural.any (fun plural => rpc == "List" ++ plural.capitalize) &&
      r.kind == .parent && r.field == some "parent"
    guard (singularName || list)
    let op := if list then "list" else if rpc.startsWith "Delete" then "delete" else "get"
    guard (m.acceptsPhysicalResponse res op false)
    let target : ResourceTarget := ⟨res.resourceType, r.kind, r.field, r.patterns⟩
    guard (target.valid d)
    return target

private def MethodDecl.readTargetFor (method : MethodDecl) (d : Descriptor)
    (resourceType rpc op : String) : Option ResourceTarget := do
  let target ← method.addressedTarget? d
  guard (target.resourceType == resourceType && target.valid d &&
    (method.name.splitOn "/").getLast? == some rpc && method.disposition == .requirements &&
    method.writes.isNone && method.itemFilter.isNone && method.partialSuccess == .never &&
    !method.requirements.isEmpty && !method.requirements.any (·.perItem))
  guard (if op == "get" then target.kind == .resource && target.field == some "name"
    else (target.kind == .parent && target.field == some "parent") || target.kind == .root)
  return target

private def Descriptor.readRpc? (d : Descriptor) (resourceType op : String) : Option String := do
  let res ← d.resourceFor resourceType
  match op with
  | "get" => (resourceType.splitOn "/").getLast?.map ("Get" ++ ·)
  | "list" => res.plural.map (fun p => "List" ++ p.capitalize)
  | _ => none

/-- Get and uniform List can establish disclosure only for the resource named
by their request schema. Each served RPC keeps its own authorization policy. -/
def Descriptor.readMethods (d : Descriptor) (resourceType op : String) : List (MethodDecl × ResourceTarget) :=
  (d.readRpc? resourceType op).elim [] fun rpc =>
    d.methods.filterMap fun method => (method.readTargetFor d resourceType rpc op).map (method, ·)

/-- Effect classification does not change which served Get and List invocations
can disclose a resource. Each invocation still goes through its own policy. -/
theorem readMethods_effect_independent (d : Descriptor) (effects : MethodDecl → MethodEffect)
    (resourceType op : String) :
    let revised : Descriptor := {d with methods := d.methods.map fun m => ({m with effect := effects m} : MethodDecl)}
    (revised.readMethods resourceType op).map (fun (m, target) => (m.name, target)) =
      (d.readMethods resourceType op).map (fun (m, target) => (m.name, target)) := by
  let edit := fun m : MethodDecl => {m with effect := effects m}
  let revised := {d with methods := d.methods.map edit}
  change ((revised.readRpc? resourceType op).elim [] _).map _ = ((d.readRpc? resourceType op).elim [] _).map _
  rw [show revised.readRpc? resourceType op = d.readRpc? resourceType op from rfl]
  cases d.readRpc? resourceType op with
  | none => rfl
  | some rpc =>
    simp only [Option.elim_some, List.map_filterMap]
    change (d.methods.map edit).filterMap _ = d.methods.filterMap _
    rw [List.filterMap_map]
    congr 1
    funext m
    simp only [Function.comp_def, Option.map_map]
    rfl

/-- Build an ordinary read probe with its optional boolean flags absent. -/
def ResourceTarget.readRequest? (target : ResourceTarget) (name : Path) : Option Json := do
  guard (Domain.contains target.patterns name)
  return Json.mkObj ((target.field.map (fun field => (field, Lean.toJson name))).toList)

def requestField (request : Json) (field : String) := (request.getObjVal? field).toOption.getD .null

def fieldArray (request : Json) (field : String) :=
  ((requestField request field).getArr?).toOption.getD #[]

private def asPath (value : Json) : Option Path := (Lean.fromJson? value).toOption

private def countArrayFields (request : Json) (matchesField : String → Bool) : Nat :=
  ((request.getObj?).toOption.map (·.toList)).getD [] |>.foldl (fun n (k,v) =>
    if matchesField k then max n (((v.getArr?).toOption.map (·.size)).getD 0) else n) 0

def requestItemCount (request : Json) (containers : List String) :=
  countArrayFields request fun k => containers.any fun c => k == c ++ "[]" || k.startsWith (c ++ "[].")

inductive WildcardUse where
  | concrete | universal | filtered | resolve
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure BoundRequirement where
  decl : Requirement
  targets : List (Nat × TargetBinding)
  unboundItems : List Nat
  wildcard : WildcardUse
  resolverFault : Bool := false
  derivedGuard : Bool := false
  writerUnbound : Bool := false
  deriving Repr, Lean.FromJson, Lean.ToJson

def BoundRequirement.unbound (r : BoundRequirement) :=
  r.targets.isEmpty || !r.unboundItems.isEmpty || r.writerUnbound

def BoundRequirement.forClient (r : BoundRequirement) (item : Option Nat) : ActiveRequirement :=
  let mine := r.targets.filter (fun pair => item.all (· == pair.1))
  let unbound := item.elim r.unbound r.unboundItems.contains
  ⟨r.decl.info, mine.map (fun pair => {pair.2 with key := r.decl.key}), r.resolverFault || unbound || r.wildcard == .filtered || r.wildcard == .resolve⟩

def TargetBinding.target (t : TargetBinding) := t.source.take t.targetLength

private def emptyParent (v : Json) := v == .null || v == .str "" || v == .arr #[]

abbrev ResolveName := Path → Except Unit (Option Path)

/-- Names can originate at the service root, a scalar request field, or a
repeated request field. The inherited parent uses its ordinary scalar slot. -/
inductive RequestValue (request : Json) : Json → Prop where
  | root : RequestValue request (.arr #[])
  | field (name : String) : RequestValue request (requestField request name)
  | item (name : String) (i : Nat) : RequestValue request ((fieldArray request name)[i]?.getD .null)

def SuppliedName (request : Json) (p : Path) : Prop :=
  p = [] ∨ ∃ v, RequestValue request v ∧ asPath v = some p

private abbrev RequestResolver (request : Json) :=
  (p : Path) → SuppliedName request p → Except Unit (Option Path)

private def suppliedPath {request : Json} (v : Json) (source : RequestValue request v) :
    Option {p // SuppliedName request p} :=
  (asPath v).attach.map (fun p => ⟨p.val, Or.inr ⟨v, source, p.property⟩⟩)

private def bindValue (d : Descriptor) (m : MethodDecl) (r : Requirement) {request : Json}
    (raw : Json) (origin : RequestValue request raw) (unresolved : Path → Option (List Nat))
    (resolve : RequestResolver request) : Except Unit (Option TargetBinding) := do
  let parent := requestField request "parent"
  let empty := r.kind == .parent && !r.parentOf && emptyParent raw
  let inheritParent := empty && r.perItem && m.writes == some "create" &&
    r.field == some "requests[].parent" && m.batchLevel.contains "parent"
  let supplied := if inheritParent && !emptyParent parent then suppliedPath parent (.field "parent")
    else if empty then some ⟨[], Or.inl rfl⟩ else suppliedPath raw origin
  let some ⟨supplied, suppliedHere⟩ := supplied | return none
  if !supplied.all (fun s => s == "-" || segmentOk s) then return none
  if (r.perItem || r.parentOf) && supplied.contains "-" then return none
  let patterns := if r.parentOf then (d.resourceFor r.info.resourceType).elim [] (·.patterns)
    else r.patterns
  let acceptsName := fun name p => Pattern.matchesWildcard p r.wildcardVariables name
  if !patterns.any (acceptsName supplied) then return none
  let some source ← resolve supplied suppliedHere | return none
  if (r.perItem || r.parentOf) && source.contains "-" then throw ()
  let some pat := patterns.find? (acceptsName source) | throw ()
  let targetLength := if r.parentOf then (Pattern.parent pat).length else source.length
  return some ⟨r.key, source, patterns, targetLength, unresolved source⟩

private def bindingValues (m : MethodDecl) (r : Requirement) (request : Json) (field : String)
    (root : Bool) (i : Nat) : List {v // RequestValue request v} := Id.run do
  if root then return [⟨.arr #[], .root⟩]
  if !r.perItem then return [⟨requestField request field, .field field⟩]
  let child := (fieldArray request field)[i]?.getD .null
  let childValue : {v // RequestValue request v} := ⟨child, .item field i⟩
  let some name := m.hoistedItemField? field | return [childValue]
  let top := requestField request name
  if top == .null then return [childValue]
  let topValue : {v // RequestValue request v} := ⟨top, .field name⟩
  return if child == .null || child == top then [topValue] else [childValue, topValue]

/-- A shared field contributes its batch-level target at every active index.
A supplied child value contributes its target at that same index. -/
theorem hoisted_target_values {m : MethodDecl} {r : Requirement} {request field name i} (item : r.perItem)
    (shared : m.hoistedItemField? field = some name) (top : (requestField request name == .null) = false) :
    let child := (fieldArray request field)[i]?.getD .null
    let values := (bindingValues m r request field false i).map Subtype.val
    requestField request name ∈ values ∧
      ((child == .null || child == requestField request name) = false → child ∈ values) := by
  simp [bindingValues, item, shared, top]
  split <;> simp_all [RequestValue.field, RequestValue.item]
  grind

private def bindRequirement (d : Descriptor) (m : MethodDecl) (r : Requirement) (first : Bool)
    (request : Json) (unresolved : Path → Option (List Nat))
    (resolve : RequestResolver request) : Option BoundRequirement := Id.run do
  let field := r.field.getD ""
  let condition := r.condition.getD ""
  let byItem := condition.contains "[]"
  if r.condition.isSome && !byItem && requestField request condition != .bool true then return none
  let raw := requestField request field
  let malformedItems := r.perItem && raw != .null && !raw.getArr?.isOk
  let container := ((field.splitOn "[]").headD "") ++ "[]"
  let flags := fieldArray request condition
  let useFlags := byItem && !((m.hoistedItemField? condition).any (fun k => requestField request k == .bool true))
  if useFlags && !flags.contains (.bool true) then return none
  let root := r.kind == .root && r.field.isNone
  let n := if !r.perItem then 1 else if root then requestItemCount request ["requests"] else
    max (if useFlags then flags.size else 0)
      (countArrayFields request (fun k => k == container || k.startsWith (container ++ ".")))
  let mut bound := []
  let mut failed := []
  let mut fault := false
  for i in [:n] do
    if useFlags && flags[i]? != some (.bool true) then continue
    let mut missing := malformedItems
    for ⟨value, source⟩ in bindingValues m r request field root i do
      if !r.perItem && !value.getArr?.isOk &&
          !(r.kind == .parent && !r.parentOf && emptyParent value) then continue
      match bindValue d m r value source unresolved resolve with
      | .ok (some target) => bound := (i, target) :: bound
      | .ok none => missing := true
      | .error () => fault := true
    if missing then failed := i :: failed
  let wildcard := if !bound.any (fun (_,t) => t.target.contains "-") then .concrete
    else if r.kind == .resource then .resolve
    else if first && m.itemFilter.isSome then .filtered else .universal
  return some ⟨r, bound.reverse, failed.reverse, wildcard, fault, false, false⟩

private def upsertFor (m : MethodDecl) (request : Json) (i : Nat) :=
  m.upsert?.any fun r =>
    let key := r.condition.getD ""
    if r.perItem then ((m.hoistedItemField? key).any fun k => requestField request k == .bool true) ||
      (fieldArray request key)[i]? == some (.bool true)
    else requestField request key == .bool true

private def bindWriterIn (d : Descriptor) (m : MethodDecl) (request : Json)
    (unresolved : Path → Option (List Nat)) (resolve : RequestResolver request) : Option BoundRequirement := do
  let writer ← m.writer?
  bindRequirement d m writer false request unresolved resolve

def bindWriter (d : Descriptor) (m : MethodDecl) (request : Json)
    (unresolved : Path → Option (List Nat)) (resolve : ResolveName) : Option BoundRequirement :=
  bindWriterIn d m request unresolved (fun p _ => resolve p)

def bindBatchItem (d : Descriptor) (m : MethodDecl) (request : Json)
    (unresolved : Path → Option (List Nat)) (resolve : ResolveName) : Option BoundRequirement := do
  let item ← m.batchItem?
  bindRequirement d m item false request unresolved (fun p _ => resolve p)

private def fieldGuardBindingsIn (d : Descriptor) (m : MethodDecl) (request : Json) (core : List BoundRequirement)
    (unresolved : Path → Option (List Nat)) (resolve : RequestResolver request) (perItem : Option Bool) :
    List BoundRequirement := Id.run do
  if m.fieldGuards.isEmpty then return []
  let some writer := m.writer? | return []
  unless perItem.all (· == writer.perItem) do return []
  let some base := core.find? (·.decl == writer) <|> bindWriterIn d m request unresolved resolve | return []
  let upsert := m.upsert?.bind fun decl =>
    core.find? (·.decl == decl) <|> bindRequirement d m decl false request unresolved resolve
  let bound := base.targets.map Prod.fst
  let possible := if writer.perItem then List.range (requestItemCount request writer.itemContainer?.toList) else [0]
  let indices := (bound ++ possible).eraseDups
  let defs := m.guardRequirements.eraseDupsBy (fun a b => a.1.key == b.1.key)
  return defs.filterMap fun (g, decl) => Id.run do
    let fields := (m.fieldGuards.filter (·.key == g.key)).map (·.field)
    let mut targets := []
    let mut missing := []
    for i in indices do
      let writeSet := FieldGuards.written m request i (upsertFor m request i)
      if !writeSet.all (fun ps => fields.any (FieldGuards.touches ps)) then continue
      let sources := base.targets.filter (·.1 == i)
      let parents := (upsert.toList.flatMap (·.targets)).filter (·.1 == i)
      if sources.isEmpty || base.unboundItems.contains i || upsert.any (·.unboundItems.contains i) then
        missing := i :: missing
      for (_, binding) in sources ++ parents do
        targets := (i, {binding with key := g.key}) :: targets
    if targets.isEmpty && missing.isEmpty then return none
    return some {decl, targets := targets.reverse, unboundItems := missing.reverse,
                 wildcard := .concrete, resolverFault := base.resolverFault || upsert.any (·.resolverFault), derivedGuard := true, writerUnbound := base.unbound}

def fieldGuardBindings (d : Descriptor) (m : MethodDecl) (request : Json) (core : List BoundRequirement)
    (unresolved : Path → Option (List Nat)) (resolve : ResolveName) (perItem : Option Bool) :=
  fieldGuardBindingsIn d m request core unresolved (fun p _ => resolve p) perItem

/-- Adapters may append additional normalized guard requirements. Existing
declarations on the interpreted writer automatically run the §4.5 hook. -/
abbrev GuardBindings := Descriptor → MethodDecl → Json → List BoundRequirement → List BoundRequirement

private def requirementsIn (d : Descriptor) (m : MethodDecl) (request : Json)
    (unresolved : Path → Option (List Nat)) (guards : GuardBindings)
    (resolve : RequestResolver request) (perItem : Option Bool) : List BoundRequirement :=
  let core := m.requirements.zipIdx.filterMap (fun (r,i) =>
    if perItem.all (· == r.perItem) then bindRequirement d m r (i == 0) request unresolved resolve else none)
  let active := core ++ fieldGuardBindingsIn d m request core unresolved resolve perItem ++ guards d m request core
  active.filter (fun r => perItem.all (· == r.decl.perItem))

def requirementsFor (d : Descriptor) (m : MethodDecl) (request : Json)
    (unresolved : Path → Option (List Nat) := fun _ => some [])
    (guards : GuardBindings := fun _ _ _ _ => [])
    (resolve : ResolveName := fun p => .ok (some p)) (perItem : Option Bool := none) : List BoundRequirement :=
  requirementsIn d m request unresolved guards (fun p _ => resolve p) perItem

theorem requirementsFor_congr_resolver (d m request unresolved guards phase) {left right : ResolveName}
    (same : ∀ p, SuppliedName request p → left p = right p) :
    requirementsFor d m request unresolved guards left phase = requirementsFor d m request unresolved guards right phase := by
  unfold requirementsFor
  exact congrArg (fun resolve => requirementsIn d m request unresolved guards resolve phase)
    (funext fun p => funext fun supplied => same p supplied)

theorem requirementsFor_phase {d m request unresolved guards resolve phase r}
    (mem : r ∈ requirementsFor d m request unresolved guards resolve (some phase)) : r.decl.perItem = phase := by
  have same : (phase == r.decl.perItem) = true := (List.mem_filter.mp mem).2
  exact (beq_iff_eq.mp same).symm

/-- Apply the operation and item phases of the guard adapter to precisely the
same inputs as the interceptor. The client does not resolve names through storage. -/
@[irreducible] def offerBindings (d : Descriptor) (m : MethodDecl) (request : Json)
    (unresolved : Path → Option (List Nat)) (guards : GuardBindings) :=
  let bind := fun phase => requirementsFor d m request unresolved guards (fun p => .ok (some p)) (some phase)
  bind false ++ bind true

def partialFor (m : MethodDecl) (request : Json) :=
  m.partialCapable && m.validPartial && (m.partialSuccess == .always ||
    (m.partialSuccess == .requestSelected && requestField request "return_partial_success" == .bool true))

theorem no_items_stays_atomic {m : MethodDecl} (noPhysical : m.batchItem? = none)
    (noItemPermission : m.requirements.any (·.perItem) = false) (request : Json) :
    partialFor m request = false := by
  simp [partialFor, MethodDecl.partialCapable, noPhysical, noItemPermission]

def methodAvailable (m : Option MethodDecl) (ceiling : Ceiling) : Bool :=
  let readOnly := ceiling.any fun entries => entries.all (·.accessClass == .read)
  match m with
  | none => !readOnly
  | some method =>
    match method.disposition with
    | .unimplemented => false
    | .undeclared => !readOnly
    | .handlerPolicy => !readOnly || method.effect == .readOnly
    | .requirements =>
      (!readOnly || method.effect == .readOnly) &&
      method.requirements.all (fun r => r.condition.isSome || ceiling.permits r.info)

inductive MethodOffer where
  | single (result : Verdict)
  | partialBatch (results : PartialOffer)
  deriving Repr, Lean.FromJson, Lean.ToJson

/-- The operation and individual item requirements of the bound batch, in request order. -/
def partialRequirements (m : MethodDecl) (reqs : List BoundRequirement) (request : Json) :
    List ActiveRequirement × List (List ActiveRequirement) :=
  let outer := (reqs.filter (!·.decl.perItem)).map (·.forClient none)
  let byItem := reqs.filter (·.decl.perItem)
  let count := requestItemCount request m.itemContainers
  let items := (List.range count).map fun i =>
    (byItem.filter fun r => r.unboundItems.contains i || r.targets.any (·.1 == i)).map
      (·.forClient (some i))
  (outer, items)

theorem partialRequirements_count (m : MethodDecl) (reqs request) :
    (partialRequirements m reqs request).2.length = requestItemCount request m.itemContainers := by
  simp [partialRequirements]

def offerRequest (d : Descriptor) (state : ClientState) (methodName : String)
    (request : Json) (now : Nat) (ceiling : Ceiling := none)
    (unresolved : Path → Option (List Nat) := fun _ => some [])
    (guards : GuardBindings := fun _ _ _ _ => []) (maximum : Option Profile := some .scopedClaims) : MethodOffer := Id.run do
  let method := d.method? methodName
  if !methodAvailable method ceiling then return .single .unavailable
  let some m := method | return .single .defer
  if m.disposition != .requirements then return .single .defer
  let reqs := offerBindings d m request unresolved guards
  let domains := d.keyDomains
  let state := if state.service = d.service then state else { state with history := [] }
  if !partialFor m request then
    return .single (offer state domains ceiling (reqs.map (·.forClient none)) now maximum)
  let (outer, items) := partialRequirements m reqs request
  let result := offerPartial state domains ceiling outer items now maximum
  if result.operation == .defer then return .single .defer
  return .partialBatch result

end Authz
