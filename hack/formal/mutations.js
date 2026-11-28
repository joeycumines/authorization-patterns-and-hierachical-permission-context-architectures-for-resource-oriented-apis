'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const os = require('node:os');
const { spawnSync } = require('node:child_process');
const cwd = path.resolve(__dirname, '../../formal');

// Feed isolated source modules to the kernel. Require a diagnostic in the
// intended proof: a missing import or a malformed edit must fail the gate.
const mutants = [
  ['T1', 'Domain', "String.ofList ('a' :: List.replicate ((used.map String.length).sum) 'a')", '"a"', 'freshId_fresh'],
  ['T1', 'Grants', 'd.requirements.filter fun r => g.selects r.info &&', 'd.requirements.filter fun r => true &&', 'expanded_iff'],
  ['T2', 'Grants', '(g.effect == .forbid || Ceiling.permits g.ceiling k) &&', 'Ceiling.permits g.ceiling k &&', 'Grant.forbid_ignores_ceiling'],
  ['T2', 'Policy', "r.effect == .forbid && r.pred.isNone && !r.mayError && r.final", "r.effect == .forbid && r.pred.isNone && r.final", 'final_forbid_blocks'],
  ['T2', 'Policy', '\n  | none => .unresolved', '\n  | none => .error', 'Rule.unknown_fault_fails_closed'],
  ['T2', 'FieldGuards', 'if m.replacesResource then', 'if m.fullReplacement then', 'unmasked_update_writes_all'],
  ['T2', 'Descriptor', 'kind == "childType:" ++ t && m.batchParentType == some t && m.batchLevel.contains "parent"',
    'm.batchParentType.all (· == t)', 'MethodDecl.declared_batch_parent'],
  ['T2', 'Lookup', 'decide opts.mode {faults := observed.getD (fun _ => none)}', 'decide .skipErrors {faults := observed.getD (fun _ => none)}', 'uniform_policy_allow_sound'],
  ['T4', 'Lookup', 'domain.all (patternCellAll resources opts check cell)', 'domain.any (patternCellAll resources opts check cell)', 'all_candidate_cells_at'],
  ['T4', 'Lookup', ' || uniformPolicyDenial d.resourcePatterns rules r.key domain opts', '', 'projecting_denial_precedes_discovery'],
  ['T4', 'Lookup', '    deniedBeforeJoin d.resourcePatterns rules r t.target opts\n  else false', '    false\n  else false', 'lookup_preflight_denial'],
  ['T2', 'Grants', 'g.validSite d && g.validSelectors d', 'g.validSite d', 'invalid_selector_fails_closed'],
  ['T5', 'Request', 'method.writes.isNone && method.itemFilter.isNone &&',
    'method.effect == .readOnly && method.writes.isNone && method.itemFilter.isNone &&', 'readMethods_effect_independent'],
  ['T4', 'Server', '  if phaseDenies d rules opts rs then throw "POLICY"', '  if false then throw "POLICY"', 'phase_denial_precedes_rows'],
  ['T2', 'Server', '{row with faults := opts.faultsOf.elim row.faults (· p)}', 'row', 'unknown_fault_overrides_stale_row'],
  ['T2', 'Server', 'if attributeReadFailed rules r.decl.key t opts then throw "SERVER_FAULT"', 'if attributeReadFailed rules r.decl.key t opts then throw "POLICY"',
    'checkTarget_failed_read'],
  ['T2', 'Server', 'if coveredByParent d rules opts parent r t then .ok [] else checkTarget d rules r t opts',
    'checkTarget d rules r t opts', 'batch_parent_authorizes_without_rows'],
  ['T3', 'Projection', 'if kids.isEmpty || (profile == .grantShaped && !(mergedHoles parent kids).isEmpty)', 'if kids.isEmpty', 'mergeAt_keeps_grant'],
  ['T4', 'Projection', 'if opts.nonprojecting || !pathOk anchor ||', 'if !pathOk anchor ||', 'private_twins'],
  ['T4', 'Disclosure', 'then (resolve p).filter (mayResolve p) else', 'then resolve p else', 'anchor_opacity'],
  ['T4', 'Server', '(r.decl.kind == .resource && !targets.Nodup)', 'false', 'batch_ok_unique_resources'],
  ['T5', 'PolicyStore', 's.nameResolver.rulesAllowed (s.catalog.flatMap (·.patterns)) (s.bindings.map s.effectiveRule) &&',
    'true &&', 'reachable_as_written_rules'],
  ['T5', 'PolicyStore', '!active.isEmpty && active.all fun req =>', '!active.isEmpty && active.any fun req =>', 'readAuthorized_all_targets'],
  ['T5', 'PolicyStore', 'rule.pred.isNone && !rule.mayError && privateCapableAt', '!rule.mayError && privateCapableAt', 'acceptPrivateRule_iff'],
  ['T5', 'PolicyStore', 'rule.pred.isNone && !rule.mayError && privateCapableAt', 'rule.pred.isNone && privateCapableAt', 'acceptPrivateRule_iff'],
  ['T2', 'Policy', 'if rules.any (·.blocks mode facts) then .deny', 'if rules.all (·.blocks mode facts) then .deny',
    'blocking_rule_denies'],
  ['T2', 'Request', '  bind false ++ bind true', '  (bind false ++ bind true).filter (!·.derivedGuard)',
    'canonical_offer_bindings', 'ClientSoundness'],
  ['T2', 'Request', 'let count := requestItemCount request m.itemContainers',
    'let count := (byItem.flatMap (fun r => r.unboundItems ++ r.targets.map Prod.fst)).foldl (fun n i => max n (i+1)) 0',
    'partialRequirements_count'],
  ['T2', 'Client', ' && !c.holes.any (fun h => Domain.nonemptyRegion dom h [])', '',
    'covers_all_candidates', 'ClientSoundness'],
  ['T6', 'Client', 'if anyConflict dom all then', 'if anyConflict dom live then',
    'conflict_at_name', 'ClientSoundness'],
  ['T6', 'Client', '!r.uniqueContexts || r.service.isEmpty', 'r.service.isEmpty',
    'duplicate_context_identity_discard', 'ClientSafety'],
  ['T6', 'Client', 'request.maxProfile == .grantShaped || maxProfile == .grantShaped', 'maxProfile == .grantShaped',
    'dispatch_service_or_ceiling_discard', 'ClientSafety'],
  ['T6', 'Client', 'now < c.expires && c.profile == .grantShaped', 'now < c.expires',
    'scoped_claims_cannot_prove_grant_shaped', 'ClientSafety'],
  ['T6', 'Client', 'else combine ((requirements.flatMap (·.targets)).map fun t => evaluateBinding s keys t now maximum)',
    'else if (requirements.flatMap (·.targets)).all (fun t => (evaluateBinding s keys t now maximum).result == .allow) then .allow else .unloaded',
    'offer_allow_one_snapshot', 'ClientSafety'],
  ['T2', 'Client', 'if positions.contains i then "-" else s', 's',
    'widenName_matches_canonical', 'AliasSoundness'],
  ['T6', 'Client', 'history := frame :: (if reset then [] else s.history)',
    'history := (if reset then [] else s.history) ++ [frame]', 'covering_reply_establishes_floor', 'ClientSafety'],
  ['T3', 'Projection', 'paths.foldl (fun live p => mergeAt profile p live) cells', 'cells', 'mergeCells_nested_same_kind'],
  ['T3', 'Query', '(c.holes.mergeSort nameLE).map (scopeTag v)', 'c.holes.map (scopeTag v)', 'shape_ordered_holes'],
  ['T4', 'Query', 'pack stamp v.profile (((names.map Prod.snd).eraseDups.mergeSort nameLE).map',
    'pack stamp v.profile ((if w.rules.isEmpty then [] else (names.map Prod.snd).eraseDups.mergeSort nameLE).map',
    'response_private_forbid_absent'],
  ['T1', 'Domain', 'pat.length == p.length || (pat[p.length - 1]?).any',
    'p.length <= pat.length || (pat[p.length - 1]?).any', 'universal_permit_singleton', 'Grants'],
  ['T1', 'Grants', '∃ g ∈ sites, g.path <+: x', '∃ g ∈ sites, g.path = x', 'universal_permit_fixed_resource'],
  ['T6', 'Client', 'return { reply with contexts := decoded }',
    'return { reply with profile := .grantShaped, contexts := decoded }', 'received_context_valid'],
  ['T2', 'FieldGuards', 'populated.elim (fs.map (·.path))', 'populated.elim []', 'effectiveMask_unknown_population'],
  ['T5', 'PolicyStore', 'strictDescendant b.scope.path p && ancestors.contains b.scope.path',
    'strictDescendant b.scope.path p', 'PolicyStore.nameableStep_sound'],
  ['T5', 'PolicyStore', 'if candidate.admissible then candidate else s',
    'if candidate.admissible then candidate else {s with bindings := []}', 'rejected_commit_retains_store'],
  ['T6', 'Client', 'changed && s.token.isSome &&', 'changed && s.token.isSome && s.token != some r.token &&',
    'accepted_subject_change_floor', 'SnapshotOrder'],
  ['T6', 'SnapshotOrder', 'floor.epoch < s.revision.epoch', 'floor.epoch != s.revision.epoch', 'served_later'],
  ['T6', 'Client', '!listingSuperseded s keys d f c', 'true', 'usableRegions_no_resurrection', 'ListingOrder'],
  ['T6', 'Client', 'history.find? fun f => !(f.selectContexts keys (reachesScope d scope)).isEmpty',
    'history.reverse.find? fun f => !(f.selectContexts keys (reachesScope d scope)).isEmpty',
    'scope_no_resurrection', 'ClientSafety'],
  ['T2', 'Descriptor', 'd.methods.any (·.disposition == .handlerPolicy) &&',
    'd.methods.any (·.disposition == .handlerPolicy) ||', 'Descriptor.nameless_pure_handler_policy'],
  ['T6', 'Client', 'request.session != s.session || ', '', 'old_session_discard', 'SnapshotOrder']
];

function invoke(command, args, options = {}) {
  const result = spawnSync(command, args, { cwd, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024, ...options });
  if (result.error) throw result.error;
  return result;
}

function declaringName(source, line) {
  const prefix = source.split('\n').slice(0, line).join('\n');
  return [...prefix.matchAll(/^(?:@\[[^\]]+\] )?(?:(?:private|protected) )?(?:theorem|def|structure|inductive) (\S+)/gm)].at(-1)?.[1];
}
function run() {
  const lean = invoke('lake', ['env', 'which', 'lean']);
  const lib = invoke('lake', ['env', 'printenv', 'LEAN_PATH']);
  assert.equal(lean.status, 0, lean.stderr);
  assert.equal(lib.status, 0, lib.stderr);
  for (const [group, mod, before, after, theorem, consumer] of mutants) {
    const original = fs.readFileSync(path.join(cwd, 'Authz', mod + '.lean'), 'utf8');
    assert.equal(original.split(before).length, 2, `stale mutation premise: ${before}`);
    const changed = original.replace(before, after);
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'authz-mutation-'));
    try {
      const env = { ...process.env, LEAN_PATH: [dir, lib.stdout.trim()].join(path.delimiter) };
      let checked = changed;
      if (consumer) {
        const source = path.join(dir, 'Authz', mod + '.lean');
        fs.mkdirSync(path.dirname(source), { recursive: true });
        const built = path.join(cwd, '.lake/build/lib/lean/Authz');
        for (const name of fs.readdirSync(built)) {
          if (!name.startsWith(mod + '.')) fs.symlinkSync(path.join(built, name), path.join(dir, 'Authz', name));
        }
        fs.writeFileSync(source, changed);
        const build = invoke(lean.stdout.trim(), ['-R', dir, '-o', source.replace(/\.lean$/, '.olean'), source], { env });
        assert.equal(build.status, 0, build.stdout + build.stderr);
        checked = fs.readFileSync(path.join(cwd, 'Authz', consumer + '.lean'), 'utf8');
      }
      const result = invoke(lean.stdout.trim(), ['--stdin'], { env, input: checked });
      const output = result.stdout + result.stderr;
      assert.doesNotMatch(output, /object file .* does not exist/, `${group} mutation hit missing olean:\n${output}`);
      const errors = [...output.matchAll(/(?:^|\n)[^\n]*?:(\d+):\d+: error:/g)];
      assert.ok(result.status !== 0 && errors.some(err => declaringName(checked, Number(err[1])) === theorem),
        `${group} mutation did not invalidate ${theorem}\n${output}`);
      console.log(`${group} rejected by ${theorem}`);
    } finally {
      fs.rmSync(dir, { recursive: true, force: true });
    }
  }
}
if (require.main === module) run();
module.exports = { run };
