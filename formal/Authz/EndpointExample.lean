import Authz.Grants

/-! The fixed parent in the old §1.4 example puts a literal in an ID position. -/
namespace Authz.EndpointExample

def config : ResourceDecl :=
  ⟨"demo.example/Config", "configs", [[.lit "configs", .var "config"]], none⟩

def item (parent : Atom) : ResourceDecl :=
  ⟨"demo.example/Item", "items",
    [[.lit "configs", parent, .lit "items", .var "item"]], none⟩

private def source : PartialSource :=
  { standard := true, failedRequests := false, clientStreaming := false, serverStreaming := false,
    imported := false, explicitRequirements := false }

def getMethod (resource : ResourceDecl) (name : String) : MethodDecl :=
  let info : KeyInfo := ⟨resource.resourceType, "get", .read, false⟩
  let r : Requirement := { key := resource.plural.getD "" ++ ".get", info, patterns := resource.patterns,
                           field := some "name" }
  { name, disposition := .requirements, effect := .readOnly, requirements := [r],
    resourceTarget := some ⟨resource.resourceType, .resource, "name", resource.patterns⟩,
    requestFields := some [("name", "type:" ++ resource.resourceType)], requestShapeKnown := true,
    partialSource := source }

private def declaration : SourceMethod :=
  { serviceIndex := 0, required := false, imported := false, hasAuthorization := true,
    unimplemented := false, standard := true, requirements := none, handlerPolicy := none,
    response := none, importSignature := none }

def descriptor (parent : Atom) : Descriptor :=
  { service := "demo.example", resources := [config, item parent],
    resourceSources := [(config.resourceType, false), ((item parent).resourceType, false)],
    methods := [getMethod config "GetConfig", getMethod (item parent) "GetItem"],
    declaredMethods := [("GetConfig", MethodDeclarations.sources [declaration]), ("GetItem", MethodDeclarations.sources [declaration])],
    guardSources := some [], fieldGuardsEnabled := false, rejectUnhandledFieldGuards := false }

#guard (descriptor (.var "config")).valid

theorem fixed_parent_rejected : (descriptor (.lit "default")).valid = false := by
  cases ok : (descriptor (.lit "default")).valid with
  | false => rfl
  | true =>
    have checked := Descriptor.resource_alternates ok
      (p := [.lit "configs", .lit "default", .lit "items", .var "item"]) (by decide)
    have wrong : Pattern.alternates [.lit "configs", .lit "default", .lit "items", .var "item"] = false := by decide
    simp [wrong] at checked

end Authz.EndpointExample
