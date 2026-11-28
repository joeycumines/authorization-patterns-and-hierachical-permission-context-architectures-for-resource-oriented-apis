import Lean

namespace Authz

abbrev Path := List String

def segmentOk (s : String) : Bool :=
  !s.isEmpty && s != "." && s != ".." && s != "-" &&
    s.toList.all (fun c => c != '%' && c != '/' && c != '\\')

def pathOk (p : Path) := p.all segmentOk

inductive Scope where
  | serviceRoot
  | resource (path : Path)
  | collection (path : Path)
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

def Scope.path : Scope → Path
  | .serviceRoot => []
  | .resource p | .collection p => p

/-- A variable retains its descriptor name for AIP-159 wildcard validation. -/
inductive Atom where
  | lit (value : String)
  | var (name : String)
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

abbrev Pattern := List Atom
abbrev Domain := List Pattern

def Atom.valid : Atom → Bool
  | .lit s => segmentOk s
  | .var n => !n.isEmpty

def Atom.isVariable : Atom → Bool
  | .var _ => true
  | .lit _ => false

def Pattern.alternates (p : Pattern) : Bool :=
  p.zipIdx.all fun (atom, i) => atom.isVariable == (i % 2 == 1)

/-- A resource declaration consists of whole segments and has a distinct name
for each variable. Its last segment may be a singleton literal. -/
def Pattern.validResource (p : Pattern) : Bool :=
  !p.isEmpty && p.alternates &&
    p.all (fun a =>
      let s := match a with | .var n | .lit n => n
      segmentOk s && !s.toList.any (fun c => c == '{' || c == '}' || c == '*')) &&
    (p.filterMap (fun a => match a with | .var n => some n | .lit _ => none)).Nodup

theorem Pattern.alternates_at {p : Pattern} (h : p.alternates = true)
    (hi : p[i]? = some a) : a.isVariable = (i % 2 == 1) :=
  beq_iff_eq.mp <| List.all_eq_true.1 h (a, i) (List.mk_mem_zipIdx_iff_getElem?.2 (by simpa using hi))

def Atom.accepts (a : Atom) (s : String) : Bool :=
  segmentOk s && match a with
  | .lit expected => s == expected
  | .var _ => true

def Pattern.matches : Pattern → Path → Bool
  | [], [] => true
  | a :: as, x :: xs => a.accepts x && Pattern.matches as xs
  | _, _ => false

def Pattern.matchesWildcard (p : Pattern) (variables : List String) (path : Path) : Bool :=
  match p, path with
  | [], [] => true
  | a :: as, x :: xs =>
    (if x == "-" then match a with
      | .var n => variables.contains n
      | .lit _ => false
    else a.accepts x) && Pattern.matchesWildcard as variables xs
  | _, _ => false

def Pattern.consume : Pattern → Path → Option Pattern
  | p, [] => some p
  | [], _ :: _ => none
  | a :: as, x :: xs => if a.accepts x then Pattern.consume as xs else none

def Pattern.reach (p : Pattern) (scope : Path) := (Pattern.consume p scope).isSome

def Pattern.literals : Pattern → Path
  | .lit s :: rest => s :: Pattern.literals rest
  | _ => []

/-- Common prefix of all completions below the anchor. After the first free ID, no
further segment is fixed across *all* completions, even if it is a literal. -/
def Pattern.fixedPrefix (p : Pattern) (anchor : Path) : Option Path :=
  (Pattern.consume p anchor).map (fun rest => anchor ++ Pattern.literals rest)

def Domain.nonemptyRegion (domain : Domain) (anchor : Path) (holes : List Path) : Bool :=
  domain.any fun p => (Pattern.fixedPrefix p anchor).any fun fixed =>
    !holes.any (·.isPrefixOf fixed)

def Domain.contains (d : Domain) (path : Path) := d.any (fun p => Pattern.matches p path)

def Pattern.parent (p : Pattern) : Pattern :=
  match p.getLast? with
  | some (.var _) => p.dropLast.dropLast
  | _ => p.dropLast

def Pattern.shape (p : Pattern) : Pattern :=
  p.map fun a => match a with
    | .var _ => .var "_"
    | .lit x => .lit x

def Pattern.overlaps : Pattern → Pattern → Bool
  | [], [] => true
  | a :: as, b :: bs => (match a, b with
    | .lit x, .lit y => x == y
    | _, _ => true) && Pattern.overlaps as bs
  | _, _ => false

inductive AccessClass where
  | read | create | update | delete | admin | execute
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure KeyInfo where
  resourceType : String
  operation : String
  accessClass : AccessClass
  explicitGrantOnly : Bool := false
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure CeilingEntry where
  resourceType : Option String := none
  accessClass : AccessClass
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

abbrev Ceiling := Option (List CeilingEntry)

def Ceiling.permits (c : Ceiling) (k : KeyInfo) :=
  c.all fun entries => entries.any fun e =>
    e.accessClass == k.accessClass && e.resourceType.all (· == k.resourceType)

inductive BindingKind where
  | resource | parent | root
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure Requirement where
  key : String
  info : KeyInfo
  patterns : Domain
  kind : BindingKind := .resource
  field : Option String := none
  parentOf : Bool := false
  perItem : Bool := false
  condition : Option String := none
  wildcardVariables : List String := []
  hoisted : Option String := none
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

inductive Disposition where
  | requirements | handlerPolicy | unimplemented | undeclared
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

inductive MethodEffect where
  | readOnly | mutating | destructive | unknown
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

inductive PartialSuccess where
  | never | always | requestSelected
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

/-- Retain the source option spelling separately from the method's derived mode. -/
inductive PartialSuccessOption where
  | name (text : String) | number (value : Int) | invalid
  deriving DecidableEq, Repr

instance : Lean.FromJson PartialSuccessOption where
  fromJson? j := pure <| match j with
    | .str text => .name text
    | .num n =>
      match ([0,1,2,3] : List Nat).find? (fun i => compare n (Lean.JsonNumber.fromNat i) == .eq) with
      | some i => .number i
      | none => .invalid
    | _ => .invalid

instance : Lean.ToJson PartialSuccessOption where
  toJson
    | .name s => .str s
    | .number n => Lean.toJson n
    | .invalid => .str "INVALID"

def PartialSuccessOption.decode : PartialSuccessOption → Option (Option PartialSuccess)
  | .name "PARTIAL_SUCCESS_UNSPECIFIED" | .name "UNSPECIFIED" | .number 0 => some none
  | .name "PARTIAL_SUCCESS_NEVER" | .name "NEVER" | .number 1 => some (some .never)
  | .name "PARTIAL_SUCCESS_ALWAYS" | .name "ALWAYS" | .number 2 => some (some .always)
  | .name "PARTIAL_SUCCESS_REQUEST_SELECTED" | .name "REQUEST_SELECTED" | .number 3 => some (some .requestSelected)
  | _ => none

/-- Permission options as declared, before field inference or writer obligations. -/
structure RequirementSource where
  targetField : Option String := none
  resourceType : Option String := none
  serviceRoot : Bool
  /-- `Requirement.parent_target`: bind the parent of the resource the field names. -/
  parentTarget : Bool
  operation : String
  accessClass : Option AccessClass
  explicitGrantOnly : Bool
  condition : Option String := none
  wildcardVariables : List String
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure PartialSource where
  standard : Option Bool := none
  mode : Option PartialSuccessOption := none
  response : Option String := none
  failedRequests : Option Bool := none
  serverStreaming : Option Bool := none
  clientStreaming : Option Bool := none
  explicitRequirements : Option Bool := none
  handlerPolicy : Option String := none
  imported : Option Bool := none
  wildcardVariables : Option (List String) := none
  rootType : Option String := none
  itemFilter : Option String := none
  requirementSources : Option (List RequirementSource) := none
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

namespace FieldGuards

/-- Backtick-quoted map keys keep literal dots in one AIP-161 path segment. -/
def splitPath (s : String) : List String := Id.run do
  let mut out := []
  let mut part := ""
  let mut quoted := false
  for c in s.toList do
    if c == '`' then quoted := !quoted
    else if c == '.' && !quoted then
      out := part :: out
      part := ""
    else part := part.push c
  return (part :: out).reverse

end FieldGuards

structure FieldMeta where
  path : String
  message : Bool := false
  outputOnly : Bool := false
  oneof : Option String := none
  repeatedOrMap : Bool := false
  proto3Optional : Bool := false
  deriving DecidableEq, Repr, Lean.ToJson

instance : Lean.FromJson FieldMeta where
  fromJson? j := do
    let flag (name : String) := Lean.fromJson? (α := Bool) ((j.getObjVal? name).toOption.getD (.bool false))
    return { path := ← j.getObjValAs? _ "path", message := ← flag "message",
             outputOnly := ← flag "outputOnly", oneof := ← Lean.fromJson? (j.getObjValD "oneof"),
             repeatedOrMap := ← flag "repeatedOrMap", proto3Optional := ← flag "proto3Optional" }

/-- Proto3 optional presence uses a synthetic oneof with no competing arms. -/
def FieldMeta.realOneof (f : FieldMeta) :=
  if f.proto3Optional then none else f.oneof.filter (!·.isEmpty)

/-- A wildcard selects an element of the preceding field. Every named parent
on a guard's descriptor path must have its own field metadata. -/
def FieldMeta.parentsDeclared (fields : List FieldMeta) (path : Path) :=
  path.dropLast.zipIdx.all fun (seg, i) =>
    seg == "*" || fields.any (fun f => FieldGuards.splitPath f.path == path.take (i+1))

def FieldMeta.atPath (fields : List FieldMeta) (path : Path) :=
  fields.find? fun f =>
    let segs := FieldGuards.splitPath f.path
    path.length == segs.length && (segs.zip path).all (fun (x,y) => x == "*" || x == y)

def FieldMeta.writablePath (fields : List FieldMeta) (path : Path) :=
  fields.any (fun f => FieldGuards.splitPath f.path == path.take 1) &&
    !(List.range path.length).any (fun i => (FieldMeta.atPath fields (path.take (i+1))).any (·.outputOnly))

structure GuardDecl where
  field : String
  key : String
  info : KeyInfo
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

/-- The resource or parent addressed by the standard RPC's request schema.
Its location is independent of the permissions protecting the method. -/
structure ResourceTarget where
  resourceType : String
  kind : BindingKind
  field : Option String
  patterns : Domain
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure MethodDecl where
  name : String
  disposition : Disposition
  effect : MethodEffect
  requirements : List Requirement
  partialSuccess : PartialSuccess := .never
  partialSource : Option PartialSource := none
  writes : Option String := none
  itemFilter : Option String := none
  handlerPolicy : Option String := none
  guardFields : List FieldMeta := []
  fieldGuards : List GuardDecl := []
  batchLevel : List String := []
  requestFields : Option (List (String × String)) := none
  batchParentType : Option String := none
  /-- A standard batch declares its wildcards on the outer parent. -/
  standardBatchWildcards : Option (List String) := none
  fullReplacement : Bool := false
  noSideEffects : Bool := false
  standardReturn : Option String := none
  resourceTarget : Option ResourceTarget := none
  requestShapeKnown : Option Bool := none
  batchItemBinding : Option Requirement := none
  writerBinding : Option Requirement := none
  upsertBinding : Option Requirement := none
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

private def MethodDecl.standardForm (m : MethodDecl) :=
  m.partialSource.any (·.standard == some true)

structure ResourceDecl where
  resourceType : String
  plural : Option String
  patterns : Domain
  protoMessage : Option String := none
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

structure SourceGuard where
  field : String
  key : String
  info : Option KeyInfo
  declaration : Option String := none
  identifier : Option Bool := none
  recursive : Option Bool := none
  optionFields : Option (List String) := none
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

private def SourceGuard.registration? (g : SourceGuard) : Option GuardDecl :=
  g.info.map fun info => { field := g.field, key := g.key, info }

structure GuardSource where
  resourceType : String
  fields : List FieldMeta
  guards : List SourceGuard
  external : Option Bool := none
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

/-- An RPC declaration before identical imports on sibling services are merged. -/
structure SourceMethod where
  serviceIndex : Nat
  required : Bool
  imported : Bool
  hasAuthorization : Bool
  unimplemented : Bool
  standard : Bool
  requirements : Option (List RequirementSource)
  handlerPolicy : Option String
  response : Option String
  /-- The complete declaration is compared only for repeated imports. -/
  importSignature : Option String
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

inductive MethodDeclarations where
  | legacy (explicitRequirements : Bool)
  | sources (entries : List SourceMethod)
  deriving DecidableEq, Repr

instance : Lean.FromJson MethodDeclarations where
  fromJson? j := match j with
    | .bool b => pure (.legacy b)
    | _ => .sources <$> Lean.fromJson? j

instance : Lean.ToJson MethodDeclarations where
  toJson
    | .legacy b => Lean.toJson b
    | .sources entries => Lean.toJson entries

structure Descriptor where
  service : String
  resources : List ResourceDecl
  methods : List MethodDecl
  /-- Source references include enabled field guards with no consuming writer. -/
  referencedTypes : List String := []
  guardSources : Option (List GuardSource) := none
  fieldGuardsEnabled : Option Bool := none
  rejectUnhandledFieldGuards : Option Bool := none
  /-- Imported types named by request signatures can be absent from an older registration. -/
  signatureImports : List ResourceDecl := []
  declaredMethods : Option (List (String × MethodDeclarations)) := none
  requiredApi : Option Bool := none
  /-- Reflected protobuf services and their short RPC names, collected across siblings. -/
  importedServices : Option (List (String × List String)) := none
  /-- Raw ServiceAuthz.api_service, before Rule 1 derives a logical service name. -/
  sourceService : Option String := none
  /-- Every declared resource type and whether it was imported, including unused imports. -/
  resourceSources : Option (List (String × Bool)) := none
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

def Requirement.itemContainer? (r : Requirement) : Option String := do
  guard r.perItem
  return ((r.field.getD "requests[]").splitOn "[]").headD "requests"

def MethodDecl.itemContainers (m : MethodDecl) : List String :=
  ((m.requirements ++ m.writerBinding.toList ++ m.batchItemBinding.toList).filterMap Requirement.itemContainer?).eraseDups

private def batchFieldKey (container field : String) :=
  if container == "requests" then field else container ++ "[]." ++ field

/-- The batch uses its enclosing parent separately from ordinary hoisted fields. -/
def MethodDecl.hoistedItemField? (m : MethodDecl) (path : String) : Option String := do
  let [container, name] := path.splitOn "[]." | none
  let first := (name.splitOn ".").headD ""
  guard (!name.isEmpty && first != "parent" && m.itemContainers.contains container)
  let declared : Bool := match m.requestFields with
    | some fields => !m.itemContainers.contains first && (fields.lookup first).isSome &&
      (fields.lookup (container ++ "." ++ first)).isSome
    | none => m.batchLevel.contains (batchFieldKey container first)
  guard declared
  return name

def MethodDecl.writer? (m : MethodDecl) :=
  m.writerBinding <|> m.requirements.find? fun r => m.writes == some r.info.operation && !r.parentOf

/-- A standard batch identifies its items even when all permissions bind at the
service root. Create and Update already carry the writer's item address. -/
def MethodDecl.batchItem? (m : MethodDecl) :=
  m.batchItemBinding <|> m.writer?.filter (·.perItem)

def MethodDecl.partialCapable (m : MethodDecl) :=
  match m.batchItem? with
  | some item => ["create", "update", "delete"].contains item.info.operation
  | none => m.resourceTarget.isNone && m.requirements.any (·.perItem)

def MethodDecl.maskKindAt (m : MethodDecl) (path : String) : Option String := do
  let fields ← m.requestFields
  let kind ← fields.lookup path
  return if kind == "message" && fields.any (fun f => f.1.startsWith (path ++ ".")) then "invalid" else kind

def MethodDecl.updateMaskKind (m : MethodDecl) :=
  m.maskKindAt (if m.writer?.any (·.perItem) then "requests.update_mask" else "update_mask")

private def fieldMaskKind (kind : String) :=
  ["message", "type:FieldMask", "type:google.protobuf.FieldMask", "type:.google.protobuf.FieldMask"].contains kind

/-- Without the RPC schema a normalized Update cannot establish mask support. -/
def MethodDecl.replacesResource (m : MethodDecl) := !m.updateMaskKind.any fieldMaskKind

private def operationResponse (response : Option String) :=
  response.any (["Operation", "google.longrunning.Operation", ".google.longrunning.Operation"].contains ·)

def MethodDecl.validPartial (m : MethodDecl) : Bool := Id.run do
  if m.partialSuccess != .never && m.itemContainers.length != 1 then return false
  let selector := (m.requestFields.getD []).lookup "return_partial_success"
  let some source := m.partialSource | return false
  let some declared := source.mode.elim (some none) PartialSuccessOption.decode | return false
  if m.disposition != .requirements then return declared.isNone && m.partialSuccess == .never
  if m.standardForm && declared.isSome then return false
  if (declared.isSome || selector.isSome || source.failedRequests.getD false) && (!m.partialCapable || source.serverStreaming.getD false) then return false
  if selector.any (· != "bool") || (declared == some .requestSelected && selector.isNone) then return false
  let mode := declared.getD (if selector.isSome then .requestSelected else if source.failedRequests.getD false then .always else .never)
  let response := source.response <|> m.standardReturn
  return m.partialSuccess == mode && (mode == .never || operationResponse response)

/-- A changed response cannot turn a Get, List or BatchGet request into a partial batch. -/
private def MethodDecl.validReadAtomicity (m : MethodDecl) (d : Descriptor) := Id.run do
  if m.disposition != .requirements then return true
  let some fields := m.requestFields | return false
  let requested := m.partialSource.any fun source =>
    source.failedRequests.getD false || source.mode.any (·.decode != some none)
  if m.partialSuccess == .never && !requested && (fields.lookup "return_partial_success").isNone then return true
  let rpc := (m.name.splitOn "/").getLast?
  return !d.resources.any fun res =>
    let short := (res.resourceType.splitOn "/").getLast?
    let nameRef := some ("type:" ++ res.resourceType)
    let get := rpc == short.map ("Get" ++ ·) && fields.lookup "name" == nameRef
    let batchGet := rpc == res.plural.map (fun p => "BatchGet" ++ p.capitalize) &&
      (fields.lookup "names" == nameRef || fields.lookup "requests.name" == nameRef)
    let list := rpc == res.plural.map (fun p => "List" ++ p.capitalize) &&
      (fields.lookup "parent" == some ("childType:" ++ res.resourceType) ||
       ((fields.lookup "parent").isNone && (m.partialSource.bind (·.rootType)) == some res.resourceType &&
        res.patterns.any (·.parent.isEmpty)))
    get || batchGet || list

/-- The parent address of an Update that supports allow_missing. An explicit
permission list can use this address for its field guards without requiring create. -/
def MethodDecl.upsert? (m : MethodDecl) := m.upsertBinding

def MethodDecl.guardRequirements (m : MethodDecl) : List (GuardDecl × Requirement) := Id.run do
  let some writer := m.writer? | return []
  let upsert := m.upsert?
  let ps := (writer.patterns ++ upsert.elim [] (·.patterns)).eraseDups
  return m.fieldGuards.map fun g => (g, {writer with key := g.key, info := g.info, patterns := ps})

/-- An Update field guard covers the upsert parent whenever its writer can
create there, including a writer whose explicit permission list has no create key. -/
theorem MethodDecl.guard_covers_upsert_parent {m : MethodDecl} {w u g parent}
    (writer : m.writer? = some w) (upsert : m.upsert? = some u)
    (field : g ∈ m.fieldGuards) (candidate : parent ∈ u.patterns) :
    ∃ r, (g, r) ∈ m.guardRequirements ∧ parent ∈ r.patterns ∧ r.field = w.field ∧ r.key = g.key := by
  unfold MethodDecl.guardRequirements
  simp only [writer, upsert, Option.elim_some, Id.run, pure, List.mem_map, Prod.mk.injEq]
  exact ⟨_, ⟨g, field, rfl, rfl⟩, List.mem_eraseDups.mpr (List.mem_append_right _ candidate), rfl, rfl⟩

def Descriptor.requirements (d : Descriptor) :=
  d.methods.flatMap fun m => m.requirements ++ m.guardRequirements.map Prod.snd

def Descriptor.namedDomain (d : Descriptor) (key : String) : Domain :=
  ((d.requirements.filter (·.key == key)).flatMap (·.patterns)).eraseDups

def Descriptor.domain (d : Descriptor) (key : String) : Domain :=
  ((d.namedDomain key).map Pattern.shape).eraseDups

def identifierOk (s : String) := match s.toList with
  | [] => false
  | c :: cs => c.isLower && cs.all Char.isAlphanum

/-- Normalized declarations retain the full original resource patterns when deriving
parent bindings. In particular, an ordinary terminal collection/ID pair drops two
segments and an AIP-156 singleton drops just its terminal literal. -/
def Requirement.bindings (r : Requirement) (resource : ResourceDecl) : Domain :=
  match r.kind with
  | .root => [[]]
  | .parent => resource.patterns.map Pattern.parent
  | .resource => resource.patterns

def Descriptor.consistentKeys (d : Descriptor) : Bool :=
  d.requirements.all fun a => d.requirements.all fun b =>
    a.key != b.key || a.info == b.info

private def pairwiseBool (compatible : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => xs.all (compatible x) && pairwiseBool compatible xs

def Descriptor.resourceFor (d : Descriptor) (type : String) : Option ResourceDecl :=
  if !d.service.isEmpty && type == d.service ++ "/service" then some ⟨type, "service", [[]], none⟩
  else d.resources.find? (·.resourceType == type)

def ResourceTarget.valid (target : ResourceTarget) (d : Descriptor) : Bool :=
  d.resources.any fun res =>
    let parents := res.patterns.map Pattern.parent
    let patterns := match target.kind with
      | .resource => res.patterns
      | .parent => parents
      | .root => [[]]
    target.resourceType == res.resourceType && !patterns.isEmpty &&
      (if target.kind == .root then target.field.isNone && List.contains parents [] else target.field.any (!·.isEmpty)) &&
      patterns.all (List.contains target.patterns ·) && target.patterns.all (List.contains patterns ·)

/-- Match the normalized AIP-123 service and type grammar used by interpret:
lowercase RFC 1123 labels of 1 to 63 characters, at most 253 characters in total.
Foreign resource definitions retain their own service prefix. -/
private def dnsLabelOk (label : List Char) : Bool :=
  !label.isEmpty && label.length ≤ 63 && label.head? != some '-' && label.getLast? != some '-' &&
    label.all fun c => c.isLower || c.isDigit || c == '-'

private def serviceCharsOk (cs : List Char) : Bool :=
  cs.length ≤ 253 && (cs.splitOn '.').all dnsLabelOk

def serviceNameOk (s : String) := serviceCharsOk s.toList

theorem serviceNameOk_empty : serviceNameOk "" = false := by decide

def fullTypeOk (s : String) :=
  match s.toList.splitOn '/' with
  | [service, first :: rest] =>
    serviceCharsOk service && first.isUpper && rest.all Char.isAlphanum
  | _ => false

/-- A service whose declared RPCs are all handler policies (plus any
unimplemented imported RPCs), with at least one handler policy and no
requirement-bearing or undeclared RPCs. -/
def Descriptor.pureHandlerPolicy (d : Descriptor) : Bool :=
  d.methods.any (·.disposition == .handlerPolicy) &&
    d.methods.all (fun m => m.disposition == .handlerPolicy || m.disposition == .unimplemented)

/-- Rule 1 derives the logical API service from locally declared resource types.
An explicit service is required when there is no shared local prefix, except for
a pure handler-policy service with no local resource types. -/
def Descriptor.derivedService? (d : Descriptor) : Option String := do
  let sources ← d.resourceSources
  guard (sources.all (fun (type, _) => fullTypeOk type) && (sources.map Prod.fst).Nodup)
  guard (d.sourceService.all serviceNameOk)
  let prefixes := ((sources.filter (!·.2)).map (fun (type, _) => String.ofList (type.toList.takeWhile (· != '/')))).eraseDups
  match prefixes with
  | [service] => do
    guard (d.sourceService.all (· == service))
    return service
  | [] =>
    match d.sourceService with
    | some service => return service
    | none =>
      guard d.pureHandlerPolicy
      return ""
  | _ => d.sourceService

private def Descriptor.sourceCatalogValid (d : Descriptor) := d.resourceSources.any fun sources =>
  let registered := (sources.filter fun (t, external) => !external || d.referencedTypes.contains t).map Prod.fst
  registered.all (fun t => d.resources.any (·.resourceType == t)) &&
    d.resources.all (fun r => registered.contains r.resourceType) &&
    d.signatureImports.all (fun r => sources.lookup r.resourceType == some true)

def MethodDecl.hasSourceSignature (m : MethodDecl) := m.requestFields.isSome && m.partialSource.any fun s =>
  s.standard.isSome && s.explicitRequirements.isSome && s.imported.isSome &&
  s.failedRequests.isSome && s.serverStreaming.isSome && s.clientStreaming.isSome

private def Descriptor.sourceEvidence (d : Descriptor) :=
  d.derivedService? == some d.service && d.sourceCatalogValid && d.guardSources.isSome &&
  d.declaredMethods.isSome && d.methods.all MethodDecl.hasSourceSignature

private def ResourceDecl.hasParentVariable (res : ResourceDecl) (v : String) :=
  res.patterns.any (·.contains (.var v)) && !res.patterns.any (fun p => p.getLast? == some (.var v))

def Requirement.valid (r : Requirement) (d : Descriptor) : Bool := Id.run do
  let some res := d.resourceFor r.info.resourceType | return false
  let some plural := res.plural | return false
  let bindings := r.bindings res
  return identifierOk r.info.operation && r.key == plural ++ "." ++ r.info.operation &&
    (r.kind == .root) == r.field.isNone && (!r.parentOf || r.kind == .parent) &&
    r.field.all (fun field => !field.isEmpty && (field.splitOn "[]").length ≤ 2 && r.perItem == field.contains "[]") &&
    (r.patterns.all (List.contains bindings ·) && bindings.all (List.contains r.patterns ·)) &&
    r.wildcardVariables.all (fun v => !r.perItem && r.info.accessClass == .read && r.kind != .root && res.hasParentVariable v)

private def MethodDecl.validEffect (m : MethodDecl) : Bool :=
  match m.disposition with
  | .requirements =>
    let classes := m.requirements.map (·.info.accessClass) ++ m.fieldGuards.map (·.info.accessClass)
    if m.noSideEffects then
      classes.all (fun c => c == .read || c == .admin) && m.effect == .readOnly
    else
      m.effect == (if classes.all (· == .read) then .readOnly
        else if classes.contains .delete then .destructive else .mutating)
  | .handlerPolicy => m.effect == (if m.noSideEffects then .readOnly else .unknown)
  | .unimplemented => !m.noSideEffects && m.effect == .unknown
  | .undeclared => m.effect == .unknown

private def plainNameField (fields : List (String × String)) (path : String) :=
  fields.lookup path == some "message" && !fields.any (fun f => f.1.startsWith (path ++ "."))

private def Requirement.acceptsField (r : Requirement) (fields : List (String × String)) (path : String) :=
  let kind := fields.lookup path
  let name := kind == some ("type:" ++ r.info.resourceType) || plainNameField fields path
  let parent := kind == some ("childType:" ++ r.info.resourceType)
  match r.kind with
  | .root => false
  | .resource => name && !r.parentOf
  | .parent => if r.parentOf then name else parent

/-- Reflection checks the physical upsert address even for explicit permissions,
where it supplies parent targets only to the field-guard and lookup adapters. -/
private def MethodDecl.validUpsertAddress (m : MethodDecl) (d : Descriptor) := m.upsert?.all fun r =>
  m.writer?.any fun writer =>
    let condition := if writer.perItem then "requests[].allow_missing" else "allow_missing"
    writer.info.operation == "update" && r.valid d && r.parentOf && r.kind == .parent &&
      r.info == { writer.info with operation := "create", accessClass := .create, explicitGrantOnly := false } &&
      r.field == writer.field && r.perItem == writer.perItem && r.condition == some condition &&
      r.hoisted == m.hoistedItemField? condition && r.wildcardVariables.isEmpty

private def MethodDecl.validConditionsAndHoists (m : MethodDecl) : Bool := Id.run do
  let requirements := m.requirements ++ m.writerBinding.toList ++ m.batchItemBinding.toList
  let some fields := m.requestFields | return false
  if m.fullReplacement && !m.writer?.any (fun r => r.info.operation == "update") then return false
  unless (fields.map Prod.fst).Nodup do return false
  let top := (fields.map Prod.fst).filter (!·.contains '.')
  let containers := m.itemContainers
  let addresses := m.batchItem?.elim (m.requirements.filter (·.perItem)) (fun r => [r])
  let hasParent := !addresses.isEmpty && addresses.all fun r =>
    fields.lookup "parent" == some ("childType:" ++ r.info.resourceType)
  let batch := (if hasParent then ["parent"] else []) ++ containers.flatMap fun c =>
    (top.filter fun name => name != "parent" && !containers.contains name && (fields.lookup (c ++ "." ++ name)).isSome).map (batchFieldKey c)
  unless batch.all m.batchLevel.contains && m.batchLevel.all batch.contains do return false
  let children := fun (path : String) => fields.filterMap fun (field, kind) =>
    let stem := path ++ "."
    if field.startsWith stem then some ((field.dropPrefix stem).toString, kind) else none
  let compatible := fun (container path : String) => (path.splitOn ".").zipIdx.all fun (_, i) =>
    let name := ".".intercalate ((path.splitOn ".").take (i+1))
    (fields.lookup name).any fun kind => kind != "invalid" && some kind == fields.lookup (container ++ "." ++ name) &&
      (kind != "message" || name != path ||
        let outer := children name
        let inner := children (container ++ "." ++ name)
        outer.all inner.contains && inner.all outer.contains)
  if let some writer := m.writer? then
    if writer.info.operation == "update" then
      let stem := if writer.perItem then "requests." else ""
      let upsert := fields.lookup (stem ++ "allow_missing")
      if upsert.any (· != "bool") || upsert.isSome != m.upsert?.isSome then return false
      if m.updateMaskKind.isSome && m.replacesResource || m.fullReplacement != m.replacesResource then return false
      if writer.perItem && (fields.lookup "allow_missing").isSome && !compatible "requests" "allow_missing" then return false
      if writer.perItem && (fields.lookup "update_mask").isSome &&
          (m.replacesResource || !(m.maskKindAt "update_mask").any fieldMaskKind) then return false
  for r in requirements do
    match r.field with
    | none => unless r.kind == .root && !r.parentOf do return false
    | some path =>
      unless (path.splitOn "[]").length ≤ 2 && r.acceptsField fields (path.replace "[]" "") do return false
    if let some condition := r.condition then
      if fields.lookup (condition.replace "[]" "") != some "bool" then return false
      let repeated := condition.splitOn "[]"
      if repeated.length > 2 || (repeated.length == 2 && !(r.perItem &&
          r.field.any (fun path => (path.splitOn "[]").head? == repeated.head? && path.contains "[]"))) then return false
    unless r.hoisted == r.condition.bind m.hoistedItemField? do return false
    unless [r.field, r.condition].all (fun field => field.all fun path =>
      (m.hoistedItemField? path).all (compatible ((path.splitOn "[]").headD ""))) do return false
    if let some target := r.field.bind m.hoistedItemField? then
      unless r.acceptsField fields target do return false
  return true

private def MethodDecl.validItemFilter (m : MethodDecl) (d : Descriptor) : Bool :=
  m.partialSource.all (fun src => src.itemFilter.all fun op =>
    m.itemFilter == (if op.isEmpty then none else some op)) &&
  m.itemFilter.all fun op => m.resourceTarget.isNone && m.requirements.head?.any fun first =>
    first.kind != .resource && d.methods.any fun method => method.requirements.any fun r =>
      r.kind == .resource && r.info.resourceType == first.info.resourceType &&
      r.info.operation == op && r.info.accessClass == .read

private def GuardDecl.validAnnotation (g : GuardDecl) :=
  (g.info.accessClass == .update || g.info.accessClass == .admin) && identifierOk g.info.operation

private def GuardDecl.validFor (g : GuardDecl) (res : ResourceDecl) :=
  g.validAnnotation && g.info.resourceType == res.resourceType &&
    res.plural.any (fun plural => g.key == plural ++ "." ++ g.info.operation)

private def SourceGuard.declId (g : SourceGuard) (source : GuardSource) :=
  g.declaration.getD (source.resourceType ++ "." ++ g.field)

private def GuardSource.underOutputOnly (source : GuardSource) (field : String) :=
  let path := FieldGuards.splitPath field
  (List.range (path.length - 1)).any fun i => (FieldMeta.atPath source.fields (path.take (i+1))).any (·.outputOnly)

private def Descriptor.guardsDisabled (d : Descriptor) :=
  d.fieldGuardsEnabled == some false || (d.fieldGuardsEnabled.isNone && d.rejectUnhandledFieldGuards.isSome)

private def Descriptor.rejectsUnhandledGuards (d : Descriptor) :=
  d.guardsDisabled && d.rejectUnhandledFieldGuards.getD d.guardSources.isSome

/-- Unused writable guards still define the class and selector behavior of
their keys. Only a served requirement contributes a binding domain. -/
private def Descriptor.validGuardSources (d : Descriptor) : Bool := Id.run do
  if d.guardsDisabled then return d.methods.all (·.fieldGuards.isEmpty)
  let some sources := d.guardSources | return false
  unless (sources.map (·.resourceType)).Nodup do return false
  let reachable := sources.flatMap fun source => source.guards.filterMap fun g => do
    let field ← source.fields.find? (·.path == g.field)
    guard (!field.outputOnly && !g.identifier.getD false && !source.underOutputOnly g.field)
    return g.declId source
  let mut definitions := d.requirements.map fun r => (r.key, r.info)
  for source in sources do
    unless fullTypeOk source.resourceType && (source.fields.map (·.path)).Nodup &&
        (source.guards.map (·.field)).Nodup do return false
    let res := d.resources.find? (·.resourceType == source.resourceType)
    if (d.resourceSources.bind (·.lookup source.resourceType)) != source.external then return false
    if res.isNone && !source.external.getD false then return false
    for g in source.guards do
      let some field := source.fields.find? (·.path == g.field) | return false
      unless FieldMeta.parentsDeclared source.fields (FieldGuards.splitPath g.field) do return false
      if field.outputOnly || g.identifier.getD false || g.recursive.getD false ||
          (source.underOutputOnly g.field && !reachable.contains (g.declId source)) then return false
      let some decl := g.registration? | return false
      unless decl.validAnnotation && decl.info.resourceType == source.resourceType &&
          !(g.optionFields.getD []).any (["targetField", "serviceRoot", "parentTarget", "resourceType", "condition", "wildcardVariables"].contains ·)
        do return false
      let some res := res | continue
      if FieldMeta.writablePath source.fields (FieldGuards.splitPath g.field) then
        unless decl.validFor res && (definitions.lookup decl.key).all (· == decl.info) do return false
        definitions := (decl.key, decl.info) :: definitions
  return true

private def protoIdentifier (name : String) := match name.toList with
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun ch => ch.isAlphanum || ch == '_')
  | [] => false

private def operationsService := "google.longrunning.Operations"
private def operationMethods := ["CancelOperation","DeleteOperation","GetOperation","ListOperations","WaitOperation"]

private def Descriptor.serviceRpcs (d : Descriptor) (service : String) : Option (List String) :=
  if service == operationsService then some operationMethods else (d.importedServices.getD []).lookup service

private def Descriptor.validImportCatalog (d : Descriptor) := (d.importedServices.getD []).all fun (service,rpcs) =>
  (service.splitOn ".").all protoIdentifier && rpcs.all protoIdentifier && rpcs.Nodup &&
    (d.serviceRpcs service).any (fun known => known.all rpcs.contains && rpcs.all known.contains)

private def importedName? (name : String) : Option (String × String) := do
  let [service, rpc] := name.splitOn "/" | none
  guard ((service.splitOn ".").all protoIdentifier && protoIdentifier rpc)
  return (service, rpc)

private def Descriptor.validImportedName (d : Descriptor) (name : String) :=
  (importedName? name).any fun (service, rpc) => (d.serviceRpcs service).any (·.contains rpc)

private def protoResponse? (raw : String) : Option String := do
  if ["Operation", "google.longrunning.Operation", ".google.longrunning.Operation"].contains raw then
    return "google.longrunning.Operation"
  if ["Empty", "google.protobuf.Empty", ".google.protobuf.Empty"].contains raw then return "google.protobuf.Empty"
  if raw.contains '/' then return raw
  let name := (raw.dropPrefix ".").toString
  guard ((name.splitOn ".").all protoIdentifier)
  return name

private def responseShort (name : String) :=
  if name.contains '/' || ["google.longrunning.Operation", "google.protobuf.Empty"].contains name then name
  else (name.splitOn ".").getLast!

private def standardVerbs : List (String × AccessClass) := [("get",.read), ("list",.read), ("create",.create),
  ("update",.update), ("delete",.delete)]

private def ResourceDecl.rpcName (res : ResourceDecl) (op : String) (batch : Bool) : Option String := do
  let suffix ← if batch || op == "list" then res.plural.map String.capitalize else (res.resourceType.splitOn "/").getLast?
  return (if batch then "Batch" else "") ++ op.capitalize ++ suffix

private def MethodDecl.responseMatches (m : MethodDecl) (res : ResourceDecl)
    (op : String) (batch : Bool) (result : String) : Bool := Id.run do
  if result == "google.longrunning.Operation" then return ["create","update","delete"].contains op
  if result == "google.protobuf.Empty" then return op == "delete"
  let parts := m.name.splitOn "/"
  let wrapper := batch || op == "list"
  let expected := if wrapper then parts.getLast! ++ "Response" else (res.resourceType.splitOn "/").getLast!
  if result == expected || (!wrapper && result == res.resourceType) then return true
  if result.contains '/' || !result.contains '.' then return false
  if !wrapper then
    if let some message := res.protoMessage then return result == message
  let pkg := if parts.length > 1 then String.intercalate "." ((parts.head!).splitOn ".").dropLast else ""
  return if pkg.isEmpty then responseShort result == expected else result == pkg ++ "." ++ expected

/-- A reflected response constrains standard RPCs and explicit Get/List signatures.
A legacy registration may retain only its normalized standard return. -/
def MethodDecl.acceptsPhysicalResponse (m : MethodDecl) (res : ResourceDecl) (op : String) (batch : Bool) :=
  (!m.standardForm && op != "get" && op != "list") ||
  ((m.partialSource.bind (·.response)) <|> m.standardReturn).all fun raw =>
    (protoResponse? raw).any (m.responseMatches res op batch)

/-- Check the reflected message identity before trusting a normalized name. -/
private def MethodDecl.validStandardReturn (m : MethodDecl) (d : Descriptor) : Bool := Id.run do
  let source := m.partialSource
  let raw := source.bind (·.response)
  let parsed := raw.bind protoResponse?
  if m.standardForm then
    if m.resourceTarget.isNone || (raw.isSome && m.standardReturn != parsed.map responseShort) then return false
  else if m.standardReturn.isSome then return false
  let some target := m.resourceTarget | return m.standardReturn.isNone
  if raw.isNone && m.standardReturn.isNone then return true
  let some res := d.resourceFor target.resourceType | return false
  let rpc := (m.name.splitOn "/").getLast!
  let batch := rpc.startsWith "Batch"
  let verb := standardVerbs.find? fun (op,_) => res.rpcName op batch == some rpc
  if !m.standardForm && source.isSome && !verb.any (fun (op,_) => op == "get" || op == "list") then return true
  let some (op, _) := verb | return false
  let some result := (if raw.isSome then parsed else m.standardReturn.bind protoResponse?) | return false
  return m.disposition == .requirements && m.responseMatches res op batch result &&
    (m.partialSuccess == .never || (batch && result == "google.longrunning.Operation"))

private def MethodDecl.validBatchItem (m : MethodDecl) (d : Descriptor) : Bool := Id.run do
  let some target := m.resourceTarget | return m.batchItemBinding.isNone
  let some res := d.resourceFor target.resourceType | return false
  let some plural := res.plural | return m.batchItemBinding.isNone
  let rpc := (m.name.splitOn "/").getLast?
  let get := rpc == some ("BatchGet" ++ plural.capitalize)
  let delete := rpc == some ("BatchDelete" ++ plural.capitalize)
  if !get && !delete then return m.batchItemBinding.isNone
  let some item := m.batchItemBinding | return false
  return m.disposition == .requirements && (!get || m.partialSuccess == .never) && target.kind == .resource && item.kind == .resource &&
    (item.field == some "names[]" || item.field == some "requests[].name") && item.field == target.field &&
    item.info.resourceType == target.resourceType && item.info.operation == (if get then "get" else "delete") &&
    item.info.accessClass == (if get then .read else .delete) && item.perItem && !item.parentOf &&
    item.condition.isNone && item.valid d

private def MethodDecl.validWriter (m : MethodDecl) (d : Descriptor) : Bool := Id.run do
  let expected := m.resourceTarget.any fun t => (d.resourceFor t.resourceType).any fun res =>
    let verb := if t.kind == .resource then "Update" else "Create"
    let rpc := (m.name.splitOn "/").getLast?
    rpc == (res.resourceType.splitOn "/").getLast?.map (verb ++ ·) ||
      rpc == res.plural.map (fun p => "Batch" ++ verb ++ p.capitalize)
  let some writer := m.writer? | return m.fieldGuards.isEmpty && m.writes.isNone && !expected
  let some res := d.resourceFor writer.info.resourceType | return false
  let some short := (res.resourceType.splitOn "/").getLast? | return false
  let some plural := res.plural | return false
  let op := writer.info.operation
  let name := (if writer.perItem then "Batch" else "") ++ op.capitalize ++ (if writer.perItem then plural.capitalize else short)
  unless m.disposition == .requirements && m.writes == some op && (m.name.splitOn "/").getLast? == some name &&
      !writer.parentOf && writer.condition.isNone && writer.valid d &&
      ((op == "update" && writer.info.accessClass == .update && writer.kind == .resource) ||
       (op == "create" && writer.info.accessClass == .create && writer.kind != .resource)) do return false
  unless m.resourceTarget.all (fun target => target.resourceType == res.resourceType && target.field == writer.field &&
      target.kind == writer.kind && target.patterns.all (List.contains writer.patterns ·) &&
      writer.patterns.all (List.contains target.patterns ·)) do return false
  if d.guardsDisabled && !d.rejectsUnhandledGuards then return m.fieldGuards.isEmpty
  let some sources := d.guardSources | return false
  let registered := sources.filter (·.resourceType == res.resourceType)
  if registered.isEmpty then return m.fieldGuards.isEmpty
  return registered.all fun source =>
    let guards := source.guards.filter fun g => FieldMeta.writablePath source.fields (FieldGuards.splitPath g.field)
    guards.all (fun g => g.registration?.any (m.fieldGuards.contains ·)) &&
      m.fieldGuards.all (fun g => guards.any fun raw => raw.registration? == some g) &&
      (guards.isEmpty || (source.fields.all (List.contains m.guardFields ·) &&
        m.guardFields.all (List.contains source.fields ·)))

def Descriptor.resourcePatterns (d : Descriptor) : Domain := d.resources.flatMap ResourceDecl.patterns

private def reflectedType (fields : List (String × String)) (name role : String) : Option String := do
  let tag ← fields.lookup name
  let marker := role ++ ":"
  guard (tag.startsWith marker && tag != marker)
  return (tag.dropPrefix marker).toString

def RequirementSource.matches (s : RequirementSource) (r : Requirement) (d : Descriptor)
    (schema : Option (List (String × String))) : Bool := Id.run do
  let sourceType := s.resourceType.map fun type => if type == "service" then d.service ++ "/service" else type
  unless s.operation == r.info.operation && s.accessClass == some r.info.accessClass &&
      s.explicitGrantOnly == r.info.explicitGrantOnly && s.condition == r.condition &&
      s.wildcardVariables == r.wildcardVariables && sourceType.all (· == r.info.resourceType) do return false
  if s.serviceRoot then
    return !s.parentTarget && s.targetField.isNone && r.field.isNone && r.kind == .root && !r.perItem && !r.parentOf &&
      r.info.resourceType == sourceType.getD (d.service ++ "/service")
  if r.kind == .root || r.parentOf != s.parentTarget then return false
  let some fields := schema | return s.targetField.all (fun target => r.field == some target)
  let field := s.targetField <|> (["name", "parent"].find? fun f => (fields.lookup f).isSome) <|>
    (fields.find? fun (f, k) => !f.contains '.' && k.startsWith "resource:").map Prod.fst
  let some target := field | return false
  let path := target.replace "[]" ""
  if let some t := reflectedType fields path "resource" then
    return s.targetField.isNone && r.field == some (target ++ ".name") && r.info.resourceType == t
  return r.field == some target && (!plainNameField fields path || s.resourceType.isSome) &&
    r.acceptsField fields path

def MethodDecl.matchesRequirements (m : MethodDecl) (d : Descriptor) (annotations : List RequirementSource) :=
  !annotations.isEmpty && m.requirements.length == annotations.length &&
    (annotations.zip m.requirements).all fun (s, r) => s.matches r d m.requestFields

private def MethodDecl.validDeclaredRequirements (m : MethodDecl) (d : Descriptor) : Bool := Id.run do
  let some annotations := m.partialSource.bind (·.requirementSources) | return true
  if annotations.isEmpty || m.disposition != .requirements || m.standardForm ||
      m.partialSource.any (fun s => s.explicitRequirements == some false || s.handlerPolicy.isSome) then return false
  return m.matchesRequirements d annotations

/-- Read the physical address from the RPC signature, independently of the
declared permission keys and the normalized address supplied for registration.
An ambiguous item or writer is a registration error even for an explicit policy. -/
private def MethodDecl.reflectedAddress (m : MethodDecl) (d : Descriptor) (source : PartialSource)
    (fields : List (String × String)) : Except Unit (Option ResourceTarget) := do
  if source.clientStreaming.getD false || source.serverStreaming.getD false then return none
  let rpc := (m.name.splitOn "/").getLast!
  let batch := rpc.startsWith "Batch"
  let bare := (rpc.dropPrefix "Batch").toString
  let some (op,_) := standardVerbs.find? (fun (op,_) => bare.startsWith op.capitalize && bare != op.capitalize)
    | return none
  if batch && op == "list" then return none
  let names := batch && (op == "get" || op == "delete")
  let direct := names && (reflectedType fields "names" "type").isSome
  let nested := fields.lookup "requests" == some "message"
  if batch && !direct && !nested then return none
  let stem := if batch && !direct then "requests." else ""
  let path := if batch && !direct then "requests[]." else ""
  let resources := d.resources ++ d.signatureImports
  let mut type := none
  let mut field := none
  let mut kind := BindingKind.resource
  if op == "get" || op == "delete" then
    type := reflectedType fields (if direct then "names" else stem ++ "name") "type"
    field := some (if direct then "names[]" else path ++ "name")
  else
    let mut bodyType := none
    if op != "list" then
      let bodies := fields.filter fun (key,tag) =>
        key.startsWith stem && !(key.dropPrefix stem).toString.contains '.' &&
          resources.any (fun res => tag == "resource:" ++ res.resourceType && res.rpcName op batch == some rpc)
      if bodies.length > 1 then throw ()
      let some (key,_) := bodies.head? | return none
      bodyType := reflectedType fields key "resource"
      if op == "update" then
        type := bodyType
        field := some (path ++ (key.dropPrefix stem).toString ++ ".name")
    if op != "update" then
      if (fields.lookup (stem ++ "parent")).isSome then
        type := reflectedType fields (stem ++ "parent") "childType"
        kind := .parent
        field := some (path ++ "parent")
      else
        type := source.rootType <|> bodyType
        kind := .root
      if bodyType.isSome && type != bodyType then return none
  let some res := resources.find? (fun r => some r.resourceType == type) | return none
  if res.rpcName op batch != some rpc then return none
  unless m.acceptsPhysicalResponse res op batch do return none
  if direct && nested && (reflectedType fields "requests.name" "type").isSome then throw ()
  if !res.plural.any identifierOk || res.patterns.isEmpty || !res.patterns.all Pattern.validResource then throw ()
  let parents := (res.patterns.map Pattern.parent).eraseDups
  if kind == .root && !parents.contains [] then return none
  if batch && (fields.lookup "parent").any (· != "childType:" ++ res.resourceType) then throw ()
  let patterns := match kind with | .resource => res.patterns.eraseDups | .parent => parents | .root => [[]]
  return some ⟨res.resourceType,kind,field,patterns⟩

/-- A strict Core server can serve a writer only when the field annotations for
its resource are known and every guarded path is stripped from writes. -/
private def Descriptor.needsGuardCapability (d : Descriptor) (resourceType : String) :=
  d.guardSources.all fun sources => sources.any fun s => s.resourceType == resourceType &&
    s.guards.any fun g => FieldMeta.writablePath s.fields (FieldGuards.splitPath g.field)

private def MethodDecl.validRegistration (m : MethodDecl) (d : Descriptor) : Bool := Id.run do
  let some source := m.partialSource | return false
  let some fields := m.requestFields | return false
  if m.disposition == .unimplemented then
    let some (service, rpc) := importedName? m.name | return false
    if source.imported == some false || (d.importedServices.isSome || service == operationsService) &&
        !(d.serviceRpcs service).any (·.contains rpc) then return false
  if source.imported == some true && !d.validImportedName m.name then return false
  if let some explicit := source.explicitRequirements then
    if explicit != (m.disposition == .requirements && !m.standardForm) || m.handlerPolicy != source.handlerPolicy ||
        source.handlerPolicy.isSome != (m.disposition == .handlerPolicy) then return false
  if source.handlerPolicy.any (fun policy => m.disposition != .handlerPolicy || m.handlerPolicy != some policy) then return false
  let streaming := source.clientStreaming.getD false || source.serverStreaming.getD false
  let rpc := (m.name.splitOn "/").getLast!
  let verb := (rpc.dropPrefix "Batch").toString
  let checkGuards := d.rejectsUnhandledGuards && !streaming && m.disposition != .unimplemented &&
    (verb.startsWith "Create" || verb.startsWith "Update")
  if m.disposition == .requirements || checkGuards then
    let .ok reflected := m.reflectedAddress d source fields | return false
    if checkGuards && reflected.any (fun target => d.needsGuardCapability target.resourceType) then return false
    if m.disposition == .requirements then
      match reflected, m.resourceTarget with
      | some target, some actual =>
        if {actual with patterns := target.patterns} != target then return false
      | none, none =>
        if m.writes.isSome || m.writer?.isSome || m.batchItem?.isSome ||
            (source.explicitRequirements.isSome && m.requestShapeKnown == some false) then return false
      | _, _ => return false
  if !m.standardForm then
    return !(source.clientStreaming.getD false && m.disposition == .requirements) &&
      (!streaming || (m.resourceTarget.isNone && m.writes.isNone && m.writer?.isNone && m.batchItem?.isNone)) &&
      m.standardBatchWildcards.isNone
  if streaming || source.imported.getD false || m.disposition != .requirements || m.itemFilter.isSome ||
      m.handlerPolicy.isSome then return false
  let some target := m.resourceTarget | return false
  let some res := d.resourceFor target.resourceType | return false
  let some plural := res.plural | return false
  let rpc := (m.name.splitOn "/").getLast!
  let batch := rpc.startsWith "Batch"
  let some (op, cls) := standardVerbs.find? (fun (op,_) => res.rpcName op batch == some rpc) | return false
  let parent := op == "list" || op == "create"
  if (batch && op == "list") || (target.kind == .resource) == parent ||
      (batch && target.kind == .root && m.requestFields.any (fun fields => (fields.lookup "parent").isSome)) then return false
  let some base := m.requirements.head? | return false
  let vars := source.wildcardVariables.getD (if batch then m.standardBatchWildcards.getD [] else base.wildcardVariables)
  if (batch && source.wildcardVariables.isSome && m.standardBatchWildcards != some vars) ||
      (!batch && m.standardBatchWildcards.isSome) || (!batch && cls != .read && !vars.isEmpty) then return false
  let expected : Requirement := {
    key := plural ++ "." ++ op, info := ⟨res.resourceType, op, cls, false⟩,
    kind := target.kind, field := target.field, patterns := base.patterns, perItem := batch,
    wildcardVariables := if batch then [] else vars }
  if base != expected then return false
  let writer := op == "update" || op == "create"
  if (if writer then m.writer? != some base else m.writer?.isSome) then return false
  if batch && (op == "get" || op == "delete") && m.batchItem? != some base then return false
  let some upsert := m.upsert? | return m.requirements == [base]
  let condition := if batch then "requests[].allow_missing" else "allow_missing"
  let create : Requirement := { base with
    key := plural ++ ".create", info := ⟨res.resourceType, "create", .create, false⟩,
    patterns := upsert.patterns, kind := .parent, parentOf := true, condition := some condition,
    hoisted := m.hoistedItemField? condition }
  return op == "update" && m.requirements == [base, create]

/-- A physical batch's declared outer parent names the item type. Its normalized
type and the runtime parent check must agree with the reflected field. -/
def MethodDecl.validBatchParent (m : MethodDecl) : Bool := Id.run do
  let some item := m.batchItem? | return m.batchParentType.isNone
  let t := item.info.resourceType
  let some fields := m.requestFields | return m.batchParentType.all fun declared =>
    declared == t && m.batchLevel.contains "parent"
  match fields.lookup "parent" with
  | none => return m.batchParentType.isNone && !m.batchLevel.contains "parent"
  | some kind => return kind == "childType:" ++ t && m.batchParentType == some t && m.batchLevel.contains "parent"

theorem MethodDecl.declared_batch_parent {m : MethodDecl} {item fields kind}
    (physical : m.batchItem? = some item) (reflection : m.requestFields = some fields)
    (declared : fields.lookup "parent" = some kind) (valid : m.validBatchParent) :
    kind = "childType:" ++ item.info.resourceType ∧ m.batchParentType = some item.info.resourceType ∧
      "parent" ∈ m.batchLevel := by
  simpa [MethodDecl.validBatchParent, physical, reflection, declared, and_assoc] using valid

private def MethodDecl.validBatchWildcards (m : MethodDecl) (d : Descriptor) : Bool := Id.run do
  let some vars := m.standardBatchWildcards | return true
  let some item := m.batchItem? | return false
  let some res := d.resourceFor item.info.resourceType | return false
  return m.resourceTarget.isSome && m.requirements == item :: m.upsertBinding.toList &&
    (vars.isEmpty || (m.batchLevel.contains "parent" && m.batchParentType == some res.resourceType &&
      vars.all res.hasParentVariable))

private def Descriptor.distinctSingletonScopes (d : Descriptor) : Bool :=
  d.resourcePatterns.all fun p =>
    p.getLast?.all fun last => last.isVariable ||
      !d.resourcePatterns.any (fun q => p.length < q.length && p.overlaps (q.take p.length))

private def SourceMethod.matches (s : SourceMethod) (m : MethodDecl) (d : Descriptor) : Bool := Id.run do
  if s.imported && !d.validImportedName m.name then return false
  let src := m.partialSource.getD {}
  let explicit := s.requirements.isSome
  unless src.standard.all (· == s.standard) && src.explicitRequirements.all (· == explicit) &&
      src.requirementSources.all (fun annotations => some annotations == s.requirements) &&
      src.imported.all (· == s.imported) && src.handlerPolicy == s.handlerPolicy && src.response == s.response &&
      m.handlerPolicy == s.handlerPolicy do return false
  let count := [s.standard, explicit, s.handlerPolicy.isSome].count true
  if s.unimplemented then return s.imported && !s.hasAuthorization && count == 0 && m.disposition == .unimplemented
  if !s.hasAuthorization then return !s.required && !s.imported && count == 0 && m.disposition == .undeclared
  if count != 1 then return false
  if let some policy := s.handlerPolicy then return !policy.isEmpty && m.disposition == .handlerPolicy
  if m.disposition != .requirements then return false
  let reflected := {src with
    standard := some s.standard, imported := some s.imported, response := s.response
    explicitRequirements := some explicit, requirementSources := s.requirements}
  let method := {m with partialSource := some reflected}
  return (s.standard || !m.standardForm) && method.validRegistration d &&
    method.validStandardReturn d

private def Descriptor.validExplicitPermissions (d : Descriptor) := d.declaredMethods.any fun roster =>
  roster.all fun (name, evidence) => match evidence with
    | .legacy _ => false
    | .sources sources => (d.methods.find? (·.name == name)).any fun m =>
      sources.all fun src => src.requirements.all (m.matchesRequirements d)

private def Descriptor.validMethodDeclarations (d : Descriptor) : Bool := Id.run do
  unless d.validImportCatalog do return false
  let some roster := d.declaredMethods | return false
  if roster.length != d.methods.length || !(roster.map Prod.fst).Nodup then return false
  let mut imports := (d.methods.filter fun m => m.disposition == .unimplemented ||
    m.partialSource.any (·.imported == some true)).map (·.name)
  let mut usesOperations := d.methods.any fun m => operationResponse m.standardReturn ||
    m.partialSource.any (fun source => operationResponse source.response)
  let mut required := d.requiredApi.getD false
  for (name, evidence) in roster do
    let some m := d.methods.find? (·.name == name) | return false
    match evidence with
    | .legacy _ => return false
    | .sources entries =>
      let first :: rest := entries | return false
      unless !name.isEmpty && (entries.map (·.serviceIndex)).Nodup &&
          entries.all (fun s => s.matches m d) do return false
      unless rest.all (fun s => first.imported && s.imported && first.importSignature.isSome &&
          first.importSignature == s.importSignature) do return false
      if first.imported then imports := name :: imports
      if entries.any (·.required) then required := true
      if operationResponse first.response then usesOperations := true
  -- A reflected service is implemented by listing one of its RPCs. An
  -- Operation response also identifies Operations before any imports are listed.
  let services := (imports.map (fun name => (name.splitOn "/").head!)).eraseDups
  let implemented := if usesOperations then operationsService :: services else services
  return !required || implemented.all fun service => (d.serviceRpcs service).any fun methods =>
    methods.all (fun rpc => imports.contains (service ++ "/" ++ rpc))

private def Descriptor.distinctResourcePatterns (d : Descriptor) :=
  d.resources.all (fun r => pairwiseBool (fun a b => !Pattern.overlaps a b) r.patterns) &&
  d.resources.all fun r => d.resources.all fun s =>
    r.resourceType == s.resourceType || r.patterns.all fun a => s.patterns.all fun b => !Pattern.overlaps a b

private def Descriptor.keyPatternsCompatible (d : Descriptor) (r : Requirement) (a b : Pattern) :=
  !a.overlaps b || (d.resourceFor r.info.resourceType).any fun res =>
    let parents := res.patterns.map Pattern.parent
    (List.contains res.patterns a && parents.contains b) || (List.contains res.patterns b && parents.contains a)

def Descriptor.valid (d : Descriptor) : Bool :=
  d.sourceEvidence && (serviceNameOk d.service || (d.service.isEmpty && d.pureHandlerPolicy)) && d.distinctSingletonScopes &&
  d.referencedTypes.all (fun t => (d.resourceFor t).isSome) &&
  (d.resources.map (·.resourceType)).Nodup &&
  (d.resources.filterMap (·.plural)).Nodup &&
  (d.methods.map (·.name)).Nodup &&
  d.distinctResourcePatterns && d.validExplicitPermissions && d.validMethodDeclarations &&
  d.validGuardSources &&
  d.resources.all (fun r => fullTypeOk r.resourceType &&
    r.plural.all (fun s => identifierOk s && s != "service") &&
    (!d.referencedTypes.contains r.resourceType || r.plural.isSome) &&
    r.resourceType != d.service ++ "/service" && !r.patterns.isEmpty &&
    r.patterns.all Pattern.validResource) &&
  d.methods.all (fun m => (m.disposition == .handlerPolicy) == m.handlerPolicy.isSome &&
    m.handlerPolicy.all (!·.isEmpty) && match m.disposition with
    | .requirements => m.requirements.any (·.condition.isNone)
    | _ => m.requirements.isEmpty) &&
  d.methods.all (fun m => m.validConditionsAndHoists && m.validPartial && m.validReadAtomicity d && m.validEffect && m.validItemFilter d && m.resourceTarget.all (·.valid d) &&
    m.requirements.all (·.valid d) && m.validDeclaredRequirements d && m.validRegistration d && m.validBatchWildcards d &&
    m.validBatchParent &&
    m.validStandardReturn d && m.validBatchItem d && m.validWriter d && m.validUpsertAddress d &&
    m.fieldGuards.all (fun g => m.guardFields.any (·.path == g.field) &&
      FieldMeta.parentsDeclared m.guardFields (FieldGuards.splitPath g.field) &&
      FieldMeta.writablePath m.guardFields (FieldGuards.splitPath g.field) &&
      m.writer?.any (·.info.resourceType == g.info.resourceType) &&
      (d.resourceFor g.info.resourceType).any g.validFor)) &&
  d.consistentKeys &&
  d.requirements.all (fun r => (d.domain r.key).all (fun p => p.all Atom.valid && p.alternates) &&
    pairwiseBool (d.keyPatternsCompatible r) (d.namedDomain r.key))

def Descriptor.WellFormed (d : Descriptor) : Prop := d.valid = true

private theorem Descriptor.checked_sources {d : Descriptor} (wf : d.WellFormed) : d.sourceEvidence := by
  simp only [Descriptor.WellFormed, Descriptor.valid, Bool.and_eq_true] at wf
  grind only

theorem Descriptor.registered_service_derived {d : Descriptor} (wf : d.WellFormed) :
    d.derivedService? = some d.service := by
  have checked := d.checked_sources wf
  simp only [Descriptor.sourceEvidence, Bool.and_eq_true, beq_iff_eq] at checked
  exact checked.1.1.1.1

/-- A well-formed descriptor that omits `api_service` is a pure handler-policy
service with no permission requirements or keys to project. -/
theorem Descriptor.nameless_pure_handler_policy {d : Descriptor} (wf : d.WellFormed)
    (nameless : d.service = "") : d.pureHandlerPolicy = true ∧ d.requirements = [] := by
  have checked : (serviceNameOk d.service || (d.service.isEmpty && d.pureHandlerPolicy)) = true := by
    simp only [Descriptor.WellFormed, Descriptor.valid, Bool.and_eq_true] at wf
    grind only
  have pure : d.pureHandlerPolicy = true := by
    simpa [nameless, serviceNameOk_empty] using checked
  have noReqs : ∀ m ∈ d.methods, m.requirements = [] ∧ m.fieldGuards = [] := by
    intro m hm
    have methodOk : (match m.disposition with
        | .requirements => m.requirements.any (·.condition.isNone)
        | _ => m.requirements.isEmpty) = true := by
      simp only [Descriptor.WellFormed, Descriptor.valid, Bool.and_eq_true, List.all_eq_true] at wf
      exact (wf.1.1.1.2 m hm).2
    have writerOk : m.validWriter d = true := by
      simp only [Descriptor.WellFormed, Descriptor.valid, Bool.and_eq_true, List.all_eq_true] at wf
      grind only
    have disp : m.disposition = .handlerPolicy ∨ m.disposition = .unimplemented := by
      have allDisp := (Bool.and_eq_true_iff.mp pure).2
      simpa [Bool.or_eq_true, beq_iff_eq] using List.all_eq_true.mp allDisp m hm
    have reqEmpty : m.requirements = [] := by
      rcases disp with h | h <;> simpa [h] using methodOk
    have guardsEmpty : m.fieldGuards = [] := by
      unfold MethodDecl.validWriter at writerOk
      cases hw : m.writer? with
      | none =>
        simp [hw, Bool.and_eq_true] at writerOk
        exact writerOk.1.1
      | some w =>
        rcases disp with h | h <;> (
          simp [hw, h] at writerOk
          cases h1 : d.resourceFor w.info.resourceType with
          | none => simp [h1, Id.run] at writerOk
          | some res =>
            cases h2 : (res.resourceType.splitOn "/").getLast? with
            | none => simp [h1, h2, Id.run] at writerOk
            | some _ =>
              cases h3 : res.plural <;> simp [h1, h2, h3, Id.run] at writerOk)
    exact ⟨reqEmpty, guardsEmpty⟩
  refine ⟨pure, ?_⟩
  unfold Descriptor.requirements
  rw [List.flatMap_eq_nil_iff]
  intro m hm
  obtain ⟨hr, hg⟩ := noReqs m hm
  cases hw : m.writer? <;> simp [hr, MethodDecl.guardRequirements, hw, hg]

theorem Descriptor.registered_source_signature {d : Descriptor} (wf : d.WellFormed) (declared : m ∈ d.methods) :
    d.guardSources.isSome ∧ d.declaredMethods.isSome ∧ m.hasSourceSignature := by
  have checked := d.checked_sources wf
  simp only [Descriptor.sourceEvidence, Bool.and_eq_true, List.all_eq_true] at checked
  exact ⟨checked.1.1.2, checked.1.2, checked.2 _ declared⟩

/-- Explicit writers retain precisely their declared permissions, including
each key's explicit-grant-only flag and activation condition. -/
theorem Descriptor.explicit_permissions_exact {d : Descriptor} (wf : d.WellFormed)
    (roster : d.declaredMethods = some entries) (decl : (name, .sources sources) ∈ entries)
    (method : d.methods.find? (·.name == name) = some m)
    (member : src ∈ sources) (explicit : src.requirements = some annotations) :
    m.requirements.length = annotations.length ∧
      ∀ pair ∈ annotations.zip m.requirements, pair.1.matches pair.2 d m.requestFields := by
  have checked : d.validExplicitPermissions := by
    simp only [Descriptor.WellFormed, Descriptor.valid, Bool.and_eq_true] at wf
    grind only
  simp only [Descriptor.validExplicitPermissions, roster, Option.any_some, List.all_eq_true] at checked
  have rpc := checked _ decl
  simp only [method, Option.any_some, List.all_eq_true] at rpc
  have requirements := rpc _ member
  simp only [explicit, Option.all_some, MethodDecl.matchesRequirements, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true] at requirements
  exact ⟨requirements.1.2, requirements.2⟩

theorem Descriptor.distinct_resources_disjoint {d : Descriptor} (wf : d.WellFormed)
    (left : r ∈ d.resources) (right : s ∈ d.resources) (distinct : r.resourceType ≠ s.resourceType)
    (fromLeft : a ∈ r.patterns) (fromRight : b ∈ s.patterns) : a.overlaps b = false := by
  have checked : d.distinctResourcePatterns := by
    simp only [Descriptor.WellFormed, Descriptor.valid, Bool.and_eq_true] at wf
    grind only
  simp only [Descriptor.distinctResourcePatterns, Bool.and_eq_true, List.all_eq_true] at checked
  have pair := checked.2 r left s right
  simp [distinct, List.all_eq_true] at pair
  exact pair _ fromLeft _ fromRight

/-- A writer in the accepted descriptor retains the metadata of every named
parent on each guarded path, including paths through a repeated element. -/
theorem Descriptor.guarded_parents_declared {d : Descriptor} (wf : d.WellFormed)
    (method : m ∈ d.methods) (declared : g ∈ m.fieldGuards)
    (ancestor : (segment, i) ∈ (FieldGuards.splitPath g.field).dropLast.zipIdx) (named : segment ≠ "*") :
    ∃ parent ∈ m.guardFields, FieldGuards.splitPath parent.path = (FieldGuards.splitPath g.field).take (i+1) := by
  simp only [Descriptor.WellFormed, Descriptor.valid, Bool.and_eq_true, List.all_eq_true] at wf
  have methodOk := wf.1.1.2 m method
  have guardOk := methodOk.2 g declared
  have parents := guardOk.1.1.1.2
  unfold FieldMeta.parentsDeclared at parents
  have entry := List.all_eq_true.mp parents _ ancestor
  simpa [named, List.any_eq_true] using entry

private theorem Descriptor.domain_checked {d : Descriptor} (wf : d.WellFormed)
    (hp : p ∈ d.domain k) : (p.all Atom.valid && p.alternates) = true := by
  have all : d.requirements.all (fun r => (d.domain r.key).all (fun p => p.all Atom.valid && p.alternates) &&
    pairwiseBool (d.keyPatternsCompatible r) (d.namedDomain r.key)) = true :=
    (Bool.and_eq_true_iff.mp wf).2
  have inUnion := hp
  simp only [Descriptor.domain, Descriptor.namedDomain, List.mem_eraseDups, List.mem_map, List.mem_flatMap,
    List.mem_filter, beq_iff_eq] at inUnion
  obtain ⟨_, ⟨r, ⟨hr, hk⟩, _⟩, _⟩ := inUnion
  have checked := (Bool.and_eq_true_iff.mp (List.all_eq_true.1 all r hr)).1
  rw [hk] at checked
  exact (List.all_eq_true.1 checked) p hp

theorem Descriptor.domain_valid {d : Descriptor} (wf : d.WellFormed)
    (hp : p ∈ d.domain k) : p.all Atom.valid = true :=
  (Bool.and_eq_true_iff.mp (d.domain_checked wf hp)).1

theorem Descriptor.domain_alternates {d : Descriptor} (wf : d.WellFormed)
    (hp : p ∈ d.domain k) : p.alternates = true :=
  (Bool.and_eq_true_iff.mp (d.domain_checked wf hp)).2

theorem Descriptor.resource_alternates {d : Descriptor} (wf : d.WellFormed)
    (hp : p ∈ d.resourcePatterns) : p.alternates = true := by
  obtain ⟨r, hr, hp⟩ := List.mem_flatMap.1 hp
  simp only [Descriptor.WellFormed, Descriptor.valid, Bool.and_eq_true] at wf
  have checked := List.all_eq_true.1 wf.1.1.1.1.2 r hr
  simp only [Bool.and_eq_true] at checked
  have pat := List.all_eq_true.1 checked.2 p hp
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp pat).1).1).2

private theorem overlaps_reachable_prefix {p q : Pattern} {x : Path}
    (matched : p.matches x = true) (reaches : q.reach x = true) :
    p.overlaps (q.take p.length) = true := by
  induction p generalizing q x with
  | nil => simp [Pattern.overlaps]
  | cons a p ih =>
    cases x with
    | nil => simp [Pattern.matches] at matched
    | cons s xs =>
      obtain ⟨ha, hm⟩ := Bool.and_eq_true_iff.mp matched
      cases q with
      | nil => simp [Pattern.reach, Pattern.consume] at reaches
      | cons b q =>
        by_cases hb : b.accepts s = true
        · have tail : Pattern.reach q xs = true := by
            simpa [Pattern.reach, Pattern.consume, hb] using reaches
          have rest := ih hm tail
          cases a <;> cases b <;>
            simp_all [Pattern.overlaps, Atom.accepts]
        · simp [Pattern.reach, Pattern.consume, hb] at reaches

/-- A singleton name is never a collection prefix of a longer catalog pattern,
even when the two patterns use different names for the same parent ID. -/
theorem Descriptor.singleton_not_collection {d : Descriptor} (wf : d.WellFormed)
    (hp : p ∈ d.resourcePatterns) (hq : q ∈ d.resourcePatterns)
    (singleton : p.getLast? = some (.lit last)) (hm : Pattern.matches p x = true)
    (longer : p.length < q.length) : Pattern.reach q x = false := by
  have check : d.distinctSingletonScopes = true := by
    simp only [Descriptor.WellFormed, Descriptor.valid, Bool.and_eq_true] at wf
    grind only
  have allowed := List.all_eq_true.mp check p hp
  simp [singleton, Atom.isVariable] at allowed
  cases h : Pattern.reach q x with
  | false => rfl
  | true => simpa [longer, overlaps_reachable_prefix hm h] using allowed q hq

inductive GrantEffect where
  | permit | forbid
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

/-- Literal and variable branches can both be reached by one concrete segment.
A forest encodes siblings explicitly so traversal decreases structurally. -/
inductive PatternTrie where
  | empty
  | terminal (key : String) (siblings : PatternTrie)
  | edge (atom : Atom) (children siblings : PatternTrie)
  deriving Repr, Inhabited

def PatternTrie.insert (key : String) (p : Pattern) : PatternTrie → PatternTrie
  | .empty => match p with
    | [] => .terminal key .empty
    | a :: rest => .edge a (PatternTrie.insert key rest .empty) .empty
  | .terminal k more =>
    if p.isEmpty && key == k then .terminal k more
    else .terminal k (PatternTrie.insert key p more)
  | .edge old child more => match p with
    | [] => .terminal key (.edge old child more)
    | a :: rest => if a == old then .edge old (PatternTrie.insert key rest child) more
      else .edge old child (PatternTrie.insert key p more)
termination_by t => (sizeOf t, p.length)

def PatternTrie.reachable : PatternTrie → Path → List String
  | .empty, _ => []
  | .terminal k more, xs => (if xs.isEmpty then [k] else []) ++ more.reachable xs
  | .edge _ child more, [] => child.reachable [] ++ more.reachable []
  | .edge a child more, x :: xs =>
    (if a.accepts x then child.reachable xs else []) ++ more.reachable (x :: xs)

def Descriptor.trie (d : Descriptor) : PatternTrie :=
  d.requirements.foldl (fun t r =>
    r.patterns.foldl (fun tr p => tr.insert r.key (Pattern.shape p)) t) .empty

theorem Pattern.consume_append (p : Pattern) (xs ys : Path) :
    Pattern.consume p (xs ++ ys) =
      (Pattern.consume p xs).bind (fun rest => Pattern.consume rest ys) := by
  induction xs generalizing p with
  | nil => simp [Pattern.consume]
  | cons x xs ih =>
    cases p with
    | nil => simp [Pattern.consume]
    | cons a p => by_cases h : a.accepts x <;> simp [Pattern.consume, h, ih]

theorem Pattern.consume_matches (p : Pattern) (x : Path) :
    Pattern.consume p x = some [] ↔ Pattern.matches p x = true := by
  induction p generalizing x with
  | nil => cases x <;> simp [Pattern.consume, Pattern.matches]
  | cons a p ih =>
    cases x with
    | nil => simp [Pattern.consume, Pattern.matches]
    | cons y ys => by_cases h : a.accepts y <;> simp [Pattern.consume, Pattern.matches, h, ih]

theorem Pattern.reach_of_matches (hm : Pattern.matches p x = true)
    (hp : scope <+: x) : Pattern.reach p scope = true := by
  obtain ⟨tail, rfl⟩ := hp
  have h := (Pattern.consume_matches _ _).2 hm
  rw [Pattern.consume_append] at h
  cases hscope : Pattern.consume p scope <;> simp_all [Pattern.reach]

end Authz
