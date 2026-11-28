import Authz.Client
import Authz.Query

namespace Authz.GroupedReply
open Query Lean

/-- Local inverses at the JSON library boundary. None of these operations
expands a group, looks up a key set, compares claims, or consults policy. -/
structure CanonicalFields (r : Response) : Prop where
  top : groupedFields r.protoJson true = .ok r.protoJson
  table : wireList r.protoJson "keySets" true = .ok (r.keySets.map toJson)
  entries : wireList r.protoJson "contexts" true = .ok (r.contexts.map WireContext.protoJson)
  key : ∀ ks ∈ r.keySets, keyEntry (toJson ks) true = .ok (ks.id,ks.keys)
  ctx : ∀ ctx ∈ r.contexts, contextFields ctx.protoJson true = .ok ctx.protoJson
  anchor : ∀ ctx ∈ r.contexts, decodedAnchor ctx.protoJson true = some ctx.anchor
  groups : ∀ ctx ∈ r.contexts, wireList ctx.protoJson "claims" true = .ok (ctx.claims.map WireClaim.protoJson)
  form : ∀ ctx ∈ r.contexts, ∀ g ∈ ctx.claims,
    fields g.protoJson true [("keySet","key_set")] ["scope","keySet","kind","holes"] = .ok g.protoJson
  reference : ∀ ctx ∈ r.contexts, ∀ g ∈ ctx.claims, natural (toJson g.keySet) true = some g.keySet
  scope : ∀ ctx ∈ r.contexts, ∀ g ∈ ctx.claims, part (wireScope g.scope) true = some (g.scope.path, some g.scope)
  holes : ∀ ctx ∈ r.contexts, ∀ g ∈ ctx.claims, repeated (α := Json) g.protoJson "holes" true = .ok (g.holes.map wireScope)
  hole : ∀ ctx ∈ r.contexts, ∀ g ∈ ctx.claims, ∀ s ∈ g.holes,
    part (wireScope s) true = some (s.path, some s)

private theorem mappedParts {xs : List Scope}
    (valid : ∀ s ∈ xs, part (wireScope s) true = some (s.path,some s)) :
    (xs.map wireScope).mapM (part · true) = some (xs.map fun s => (s.path,some s)) := by
  induction xs with
  | nil => rfl
  | cons s xs ih =>
    have tail := ih fun x hx => valid x (by simp [hx])
    simp [List.mapM_cons, valid s (by simp), tail]

private theorem canonical_group {r ctx g keys sets profile anchor grouped native out}
    (lex : CanonicalFields r) (site : ctx ∈ r.contexts) (member : g ∈ ctx.claims)
    (parsed : group keys sets profile anchor grouped native true g.protoJson = some out) :
    ∃ selected, sets.lookup g.keySet = some selected ∧
      out = ⟨selected, g.kind, g.scope.path, g.holes.map Scope.path⟩ := by
  have id : g.protoJson.getObjVal? "keySet" = .ok (toJson g.keySet) := by rfl
  have name : g.protoJson.getObjVal? "scope" = .ok (wireScope g.scope) := by rfl
  have noPath : (g.protoJson.getObjVal? "path").isOk = false := by rfl
  have kindValue : g.protoJson.getObjVal? "kind" = .ok (.str (match g.kind with
    | .allow => "ALLOW" | .deny => "DENY" | .conditional => "CONDITIONAL")) := by rfl
  have kindRead : responseKind (.str (match g.kind with
    | .allow => "ALLOW" | .deny => "DENY" | .conditional => "CONDITIONAL")) false = some g.kind := by
    cases g.kind <;> rfl
  obtain ⟨why, hp⟩ : ∃ why, g.protoJson.getObjVal? "path" = .error why := by
    cases h : g.protoJson.getObjVal? "path" with
    | error why => exact ⟨why,rfl⟩
    | ok x => rw [h] at noPath; contradiction
  cases selected : sets.lookup g.keySet with
  | none =>
    simp [group, lex.form ctx site g member, id, lex.reference ctx site g member, selected, bind, Option.bind, Except.toOption] at parsed
  | some values =>
    refine ⟨values, rfl, ?_⟩
    simp [group, lex.form ctx site g member, id, lex.reference ctx site g member, selected,
      name, hp, kindValue, kindRead, lex.scope ctx site g member, lex.holes ctx site g member,
      mappedParts (lex.hole ctx site g member), bind, Option.bind, guard, pure, List.map_map,
      Function.comp_def, Option.or, Except.isOk, Except.toOption] at parsed
    repeat' first | split at parsed | dsimp only at parsed
    all_goals first | contradiction | exact (Option.some.inj parsed).symm

private theorem lookup_member {xs : List (Nat × List String)} {k v}
    (hit : xs.lookup k = some v) : (k,v) ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons pair rest ih =>
    by_cases same : pair.1 = k
    · rcases pair with ⟨id,ks⟩
      subst k
      simp [List.lookup] at hit
      cases hit
      exact List.mem_cons_self
    · simp only [List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm same)] at hit
      exact List.mem_cons_of_mem _ (ih hit)

/-- For any received claim, follow the actual decoder's witnesses back to the
original produced context, group, numeric reference, and exact member key. -/
theorem canonical_claim_in_table {keys r reply ctx c}
    (lex : CanonicalFields r) (rx : receive? keys r.protoJson none true = some reply)
    (inContext : ctx ∈ reply.contexts) (inGroup : c ∈ ctx.claims) : (ctx.anchor,c) ∈ r.ledger := by
  obtain ⟨wire, table, sets, entries, rawCtx, prepared, rawGroups, rawGroup, profile, group,
    hw, ht, fromTable, he, hc, prep, ha, hgs, hg, decoded, expanded⟩ := received_claim_source rx inContext inGroup
  cases (Except.ok.inj (hw.symm.trans lex.top))
  cases (Except.ok.inj (ht.symm.trans lex.table))
  cases (Except.ok.inj (he.symm.trans lex.entries))
  obtain ⟨actual, member, rfl⟩ := List.mem_map.mp hc
  cases (Except.ok.inj (prep.symm.trans (lex.ctx actual member)))
  have atSite := Option.some.inj (ha.symm.trans (lex.anchor actual member))
  rw [atSite] at decoded ⊢
  cases (Except.ok.inj (hgs.symm.trans (lex.groups actual member)))
  obtain ⟨field, present, rfl⟩ := List.mem_map.mp hg
  obtain ⟨values, lookup, rfl⟩ := canonical_group lex member present decoded
  obtain ⟨key, hk, rfl⟩ := List.mem_map.mp expanded
  obtain ⟨rawEntry, rawMem, parse⟩ := fromTable _ (lookup_member lookup)
  obtain ⟨ks, inTable, rfl⟩ := List.mem_map.mp rawMem
  obtain ⟨id, same⟩ := Prod.mk.inj (Except.ok.inj ((lex.key ks inTable).symm.trans parse))
  exact List.mem_flatMap.mpr ⟨actual, member, List.mem_flatMap.mpr ⟨field, present,
    List.mem_flatMap.mpr ⟨ks, List.mem_filter.mpr ⟨inTable, beq_iff_eq.mpr id⟩,
      List.mem_map.mpr ⟨key, same ▸ hk, rfl⟩⟩⟩⟩

end Authz.GroupedReply
