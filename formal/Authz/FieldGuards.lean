import Authz.Descriptor

namespace Authz.FieldGuards
open Lean (Json)

def touches (paths : List String) (field : String) :=
  let protectedPath := splitPath field
  paths.any fun p => ((splitPath p).zip protectedPath).all (fun (x,y) => x == "*" || y == "*" || x == y)

def writable (fs : List FieldMeta) (paths : List String) :=
  paths.filter fun p => FieldMeta.writablePath fs (splitPath p)

def populatedLeaves (fs : List FieldMeta) (paths : List String) :=
  paths.filter (fun p => (FieldMeta.atPath fs (splitPath p)).all fun f =>
    !f.message || f.repeatedOrMap || f.realOneof.isSome)

def directWrites (fs : List FieldMeta) (mask populated : Option (List String)) (upsert : Bool) :=
  let leaves := populated.elim (fs.map (·.path)) (populatedLeaves fs)
  let base := mask.elim leaves (fun m => if m.contains "*" then fs.map (·.path) else m)
  writable fs (base ++ (if upsert then leaves else []))

private def selectedArm (written : List String) (fs : List FieldMeta)
    (populated : Option (List String)) (arm : FieldMeta) :=
  arm.realOneof.isSome && touches written arm.path &&
    (populated.isNone || touches (populatedLeaves fs (populated.getD [])) arm.path)

private def sameOneofSibling (f arm : FieldMeta) :=
  f.path != arm.path && f.realOneof == arm.realOneof &&
    (splitPath f.path).dropLast == (splitPath arm.path).dropLast

def effectiveMask (fs : List FieldMeta) (mask populated : Option (List String)) (upsert : Bool) : List String :=
  let written := directWrites fs mask populated upsert
  let selected := fs.filter (selectedArm written fs populated)
  let siblings := fs.filter fun f => selected.any (sameOneofSibling f)
  (writable fs (written ++ siblings.map (·.path))).eraseDups.mergeSort

private theorem mem_effectiveMask {fs mask populated upsert path} :
    path ∈ effectiveMask fs mask populated upsert ↔
      (path ∈ directWrites fs mask populated upsert ∨
        ∃ f ∈ fs, (∃ a ∈ fs, selectedArm (directWrites fs mask populated upsert) fs populated a ∧
          sameOneofSibling f a) ∧ f.path = path) ∧ FieldMeta.writablePath fs (splitPath path) := by
  simp [effectiveMask, writable, List.any_eq_true, and_assoc, or_and_right]

theorem effectiveMask_writable {p fs mask pop upsert}
    (mem : p ∈ effectiveMask fs mask pop upsert) : FieldMeta.writablePath fs (splitPath p) :=
  (mem_effectiveMask.mp mem).2

/-- When population is unknown, an implied mask or a possible create branch
must account for every declared writable field. -/
theorem effectiveMask_unknown_population {fs f mask upsert}
    (field : f ∈ fs) (canWrite : FieldMeta.writablePath fs (splitPath f.path))
    (needsPopulation : mask = none ∨ upsert = true) :
    f.path ∈ effectiveMask fs mask none upsert := by
  apply mem_effectiveMask.mpr
  refine ⟨Or.inl ?_, canWrite⟩
  have declared : f.path ∈ fs.map (·.path) := List.mem_map.mpr ⟨f, field, rfl⟩
  rcases needsPopulation with rfl | rfl
  · simp [directWrites, writable, declared, canWrite]
  · simp [directWrites, writable, declared, canWrite]

theorem populated_repeated_field {fs f paths p}
    (field : FieldMeta.atPath fs (splitPath p) = some f) (collection : f.repeatedOrMap = true)
    (present : p ∈ paths) : p ∈ populatedLeaves fs paths := by
  simp [populatedLeaves, field, collection, present]

theorem empty_optional_message {fs f paths p}
    (field : FieldMeta.atPath fs (splitPath p) = some f)
    (message : f.message = true) (singular : f.repeatedOrMap = false)
    (optional : f.proto3Optional = true) : p ∉ populatedLeaves fs paths := by
  simp [populatedLeaves, field, FieldMeta.realOneof, message, singular, optional]

theorem effectiveMask_strips_output_only {p fs f mask pop upsert i}
    (depth : i < (splitPath p).length) (field : FieldMeta.atPath fs ((splitPath p).take (i+1)) = some f)
    (output : f.outputOnly = true) : p ∉ effectiveMask fs mask pop upsert := by
  intro mem
  have ok := effectiveMask_writable mem
  have blocked : (List.range (splitPath p).length).any (fun j =>
      (FieldMeta.atPath fs ((splitPath p).take (j+1))).any (·.outputOnly)) := by
    exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr depth, by simp [field, output]⟩
  simp [FieldMeta.writablePath, blocked] at ok

theorem effectiveMask_oneof_sibling {fs arm sibling mask pop upsert}
    (ha : arm ∈ fs) (hs : sibling ∈ fs) (group : arm.realOneof.isSome)
    (same : sibling.realOneof = arm.realOneof) (different : sibling.path ≠ arm.path)
    (parent : (splitPath sibling.path).dropLast = (splitPath arm.path).dropLast)
    (writes : touches (directWrites fs mask pop upsert) arm.path)
    (active : pop.isNone || touches (populatedLeaves fs (pop.getD [])) arm.path)
    (writableField : FieldMeta.writablePath fs (splitPath sibling.path)) :
    sibling.path ∈ effectiveMask fs mask pop upsert := by
  exact mem_effectiveMask.mpr ⟨Or.inr ⟨sibling, hs, ⟨arm, ha,
    by simp [selectedArm, group, writes, active], by simp [sameOneofSibling, same, different, parent]⟩, rfl⟩, writableField⟩

private theorem touches_mono {a b : List String} {field} (le : a ⊆ b)
    (hit : touches a field) : touches b field := by
  obtain ⟨p, hp, test⟩ := List.any_eq_true.mp hit
  exact List.any_eq_true.mpr ⟨p, le hp, test⟩

/-- Including fields supplied for the create branch of an upsert preserves every
field the ordinary update could write or clear. -/
theorem effectiveMask_upsert_mono (fs mask pop) :
    effectiveMask fs mask pop false ⊆ effectiveMask fs mask pop true := by
  have incl : directWrites fs mask pop false ⊆ directWrites fs mask pop true := by
    intro x hx
    simp only [directWrites, writable, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      List.mem_filter, List.mem_append] at hx ⊢
    exact ⟨Or.inl hx.1, hx.2⟩
  intro path mem
  obtain ⟨h, writableField⟩ := mem_effectiveMask.mp mem
  apply mem_effectiveMask.mpr
  refine ⟨?_, writableField⟩
  rcases h with direct | ⟨f, hf, ⟨a, ha, selected, sibling⟩, eq⟩
  · exact Or.inl (incl direct)
  · simp only [selectedArm, Bool.and_eq_true] at selected
    exact Or.inr ⟨f, hf, ⟨a, ha, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨selected.1.1, touches_mono incl selected.1.2⟩, selected.2⟩, sibling⟩, eq⟩

private def strings (v : Json) : Option (List String) := (Lean.fromJson? v).toOption

private def writerField (m : MethodDecl) (request : Json) (name : String) (i : Nat) : Option Json :=
  if m.writer?.any (·.perItem) then
    ((request.getObjVal? ("requests[]." ++ name)).toOption.bind (·.getArr?.toOption)).bind (·[i]?)
  else (request.getObjVal? name).toOption

/-- Unknown write sets select every guard; malformed masks are never interpreted
as a request to protect zero fields. An omitted update mask has AIP-161 populated
leaf semantics and differs from a present empty mask. -/
def written (m : MethodDecl) (request : Json) (i : Nat) (upsert : Bool) : Option (List String) := do
  if m.writes == some "update" then
    if m.replacesResource then return effectiveMask m.guardFields (some ["*"]) none upsert
    let own ← writerField m request "update" i
    guard own.getObj?.isOk
    let readPaths (name : String) : Option (Option (List String)) :=
      match own.getObjVal? name with
      | .ok v => (strings v).map some
      | .error _ => some none
    let mask ← readPaths "mask"
    let populated ← readPaths "populated"
    if m.batchLevel.contains "update_mask" then
      if let .ok hoisted := request.getObjVal? "update_mask" then
        let top ← strings hoisted
        return effectiveMask m.guardFields (some ((mask.getD []) ++ top)) populated upsert
    return effectiveMask m.guardFields mask populated upsert
  let supplied ← writerField m request "populated" i
  return writable m.guardFields (populatedLeaves m.guardFields (← strings supplied))

theorem unmasked_update_writes_all {m : MethodDecl} (update : m.writes = some "update")
    (absent : (m.requestFields.getD []).lookup
      (if m.writer?.any (·.perItem) then "requests.update_mask" else "update_mask") = none)
    (request i upsert) : written m request i upsert = some (effectiveMask m.guardFields (some ["*"]) none upsert) := by
  have full : m.replacesResource = true := by
    cases source : m.requestFields with
    | none => simp [MethodDecl.replacesResource, MethodDecl.updateMaskKind, MethodDecl.maskKindAt, source]
    | some fs =>
      simp only [source, Option.getD_some] at absent
      simp [MethodDecl.replacesResource, MethodDecl.updateMaskKind, MethodDecl.maskKindAt, source, absent]
  simp [written, update, full]

/-- Every known write set, including a per-item or hoisted mask, contains only
writable fields. An unknown write set is handled separately by the guard binder. -/
theorem written_writable {m request i upsert paths p}
    (known : written m request i upsert = some paths) (mem : p ∈ paths) :
    FieldMeta.writablePath m.guardFields (splitPath p) := by
  unfold written at known
  split at known
  · split at known
    · cases known
      exact effectiveMask_writable mem
    · iterate 4 obtain ⟨_, _, known⟩ := Option.bind_eq_some_iff.mp known
      dsimp only at known
      split at known
      · split at known
        · obtain ⟨_, _, known⟩ := Option.bind_eq_some_iff.mp known
          cases known
          exact effectiveMask_writable mem
        · cases known
          exact effectiveMask_writable mem
      · cases known
        exact effectiveMask_writable mem
  · iterate 2 obtain ⟨_, _, known⟩ := Option.bind_eq_some_iff.mp known
    cases known
    exact (List.mem_filter.mp mem).2

end Authz.FieldGuards
