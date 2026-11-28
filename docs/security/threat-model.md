# Threat Model

- **Specification:** General Authorization Implementation Patterns & Hierarchical Permission-Context Architectures for Resource-Oriented APIs
- **Status:** Living security reference maintained alongside `index.html` and the Lean 4 formal verification suite
- **Deployment status:** Technical specification, embedded JavaScript reference model, and verification suite; the architecture has not been deployed in production, and this repository ships no production authorization server or client SDK
- **Methodology:** W3C Threat Modeling Guide (origin categories and ERTA dispositions), STRIDE (security), LINDDUN (privacy and disclosure), and Trusted Computing Base (TCB) analysis

This document serves two audiences:

1. Security reviewers auditing the specification (`index.html`), embedded JavaScript reference model (`MODEL`), Lean 4 formal proofs, differential test harness, and build pipeline (Layer A).
2. Implementers and deployers building a production authorization service or client from the specification and enforcing its runtime trust boundaries (Layer B).

Any production service built from this specification must independently satisfy the runtime premises in Section 4.3 and the deployer obligations in Section 8.2.

---

## 1. System under analysis

This threat model separates repository artifacts from the specified runtime architecture because they involve distinct trust boundaries, adversaries, and verification evidence.

### 1.1 Layer A: Repository artifacts, reference model, and verification toolchain

- Canonical specification (`index.html`): Single-file specification, interactive archetype explorer, live simulator, Markdown export source (`gmake export-md`), and embedded JavaScript reference model (`MODEL` / `window.AuthzModel`) with embedded regression checks.
- Protobuf extraction, linting, and browser check pipeline: Python 3 extraction of `authz/v1/annotations.proto`, `permission_context.proto`, and `field_guards.proto` from `index.html` into `build/proto/`, comparison against `proto/`, compilation via `protoc`, linting via Google's `api-linter`, JS model checks, headless Chrome loading, and the formal gate (`gmake -j check`, which runs `verify-formal`).
- Formal verification and differential parity suite: Mechanized Lean 4 semantic core and executable oracle (`Authz.Oracle.handle`) under `formal/Authz/`, manifest and heading/theorem index (`formal/sync-manifest.json`), model extractor (`hack/load-model.js`), embedded check runner (`hack/run-checks.js`), verification driver (`hack/formal/verify.js`), and differential parity harness (`hack/formal/verify-cases.js`, `hack/formal/codec.js`, `hack/formal/query-cases.js`, `hack/formal/lookup-cases.js`, `hack/formal/store-cases.js`, `hack/formal/request-cases.js`, `hack/formal-client-cases.js`).
- Build, export, and static hosting artifacts: `Makefile`, exported Markdown files (`build/md/`), `hack/package.json` and `hack/package-lock.json`, and static hosting configuration (all outside the formal verification gate). Local planning ledgers and scratch notes (`blueprint.json`, `scratch/`) are non-authoritative working files outside the specification and formal gate.

### 1.2 Layer B: Specified authorization protocol and runtime architecture

- Protobuf descriptor layer: Method, service, and optional field-guard declarations (`authz/v1/annotations.proto`, `permission_context.proto`, `field_guards.proto`) interpreted from `FileDescriptorSet` or gRPC Server Reflection and versioned by `descriptor_etag`.
- Authoritative server enforcement: gRPC interceptor (`Authz.authorizeRequest`), application handlers enforcing returned residuals (`ITEM_FILTER`, `RESOLVE_WILDCARD`, `PARTIAL_BATCH`, `ATOMIC_BATCH`, `PREDICATE`, `POLICY_EVALUATION`), ancestor-bound multi-collection lookups, atomic commit checks, and uniform AIP `ErrorInfo` responses.
- Policy administration plane and store: Scoped permits and forbids attached to `serviceRoot` or resources (`Authz.GrantSite`), role and group expansion, descendant-rule index, `as-written` name-mode configuration, `Authz.Sight` visibility observations, `Authz.PrivacyBoundary` declarations, and shared global snapshot revisions.
- Advisory permission projection and client evaluation: `QueryPermissionContexts`, grouped ProtoJSON wire serialization and decoding (`Authz.GroupedReply.receive?`), client snapshot cache (`Authz.acceptSnapshot`), local evaluation (`Authz.methodAvailable`, `Authz.offer`, `Authz.offerRequest`, `Authz.offerPartial`, `Authz.evaluate`, `Authz.evaluateScope`, `Authz.usableRegions` in Lean; corresponding embedded JS `MODEL` exports `methodAvailable`, `offer`, `offerDetailed`, `evaluate`, `evaluateScope`, and `usableRegions`), and `min_snapshot_token` freshness ordering.

---

## 2. Stakeholders and adversary profiles

| ID | Layer | Actor / adversary | Capabilities and goals |
| --- | --- | --- | --- |
| `AD-1` | Layer B | Unauthenticated or external caller | Sends arbitrary gRPC/HTTP requests, malformed resource names, or alias probes to gain unauthorized access or enumerate resources. |
| `AD-2` | Layer B | Authenticated tenant caller or delegated agent (including prompt-injected MCP agent) | Holds valid grants in one scope or a restricted credential ceiling; attempts privilege escalation across tenants or operations, probes hidden scopes, rows, or duplicates, or acts on stale client UI/tool state. |
| `AD-3` | Layer B | Misconfigured or malicious policy writer or adapter | Attempts to commit unnameable private rules without a privacy boundary, elevate rule visibility via forged or stale `Sight` observations, or feed stale or inconsistent alias, identity, or fault facts into enforcement or projection. |
| `AD-4` | Layer B | Lagging replica or faulty context producer | Serves stale policy revisions, superseded failover epochs, or malformed or conflicting `QueryPermissionContexts` responses. |
| `AD-5` | Layer A | Browser-side attacker targeting `index.html` readers | Supplies crafted URLs, simulator inputs, or compromised static-hosting assets to execute scripts in a reader's browser. |
| `AD-6` | Layer A | Malicious contributor or build-chain attacker | Attempts to introduce Lean proof escapes (`sorry`, extra axioms, unsafe definitions), desynchronize `index.html` from Lean proofs, or weaken differential assertions so invalid changes pass verification. |

---

## 3. Assets

| ID | Layer | Asset | Security / privacy property | Location |
| --- | --- | --- | --- | --- |
| `AS-1` | Layer B | Authoritative RPC decisions | Integrity (only authorized operations execute; server is sole enforcer) | Server interceptor and application handlers |
| `AS-2` | Layer B | Stored resource data and existence secrecy | Confidentiality and non-detectability (hidden rows, non-members, hidden duplicates, hidden scopes) | Application data store and AIP error replies |
| `AS-3` | Layer B | Policy store, privacy boundaries, and descendant-rule index | Integrity and confidentiality of private rules | Policy administration plane and policy store |
| `AS-4` | Layer B | Protobuf descriptors and method effects | Integrity (method requirements, patterns, `READ_ONLY` vs. `MUTATING`/`DESTRUCTIVE` consent gating) | Descriptor registry, Server Reflection, `descriptor_etag` |
| `AS-5` | Layer B | Delegated credential ceilings | Integrity (permits narrowed; forbids unaffected by ceiling narrowing) | Identity/consent issuer, server resolver, client `methodAvailable`/`offer` |
| `AS-6` | Layer B | Client permission-context soundness | Integrity and bounded freshness (no false `ALLOW` at named snapshot; no rollback across revocations) | Client snapshot cache and evaluator |
| `AS-7` | Layer A | Formal verification and parity claims | Integrity (compiled theorems, axiom footprint, and JS/Lean parity match repository sources) | `formal/Authz/`, `formal/sync-manifest.json`, `hack/formal/`, `formal/README.md` |
| `AS-8` | Layer A | Published specification, reference model, and protobuf contracts | Integrity and reader safety (accurate spec text, safe browser execution, consistent protobuf and Markdown exports) | `index.html`, `proto/`, exported Markdown, build/hosting scripts |

---

## 4. Trust boundaries and Trusted Computing Base (TCB)

### 4.1 Architecture and toolchain boundaries

```text
Layer B: Specified Runtime Architecture
=======================================

[Caller / UI / MCP Host]
   |  (B1: Untrusted RPCs, names, masks, aliases, credentials)
   v
[gRPC Interceptor: authorizeRequest] <---(B5: FileDescriptorSet / Reflection)---> [Descriptor Registry]
   |   |
   |   +--(B6: Advisory QueryPermissionContexts snapshots, tokens, expiry)------> [Client Cache / offerRequest]
   |   |
   |   +--(B4: IdP claims, groups, ownsAlias, canReadNow, faultsOf)-------------> [Identity / Alias / Fault Adapters]
   |   |
   |   +--(B3: Scoped grants, privacy boundaries, Sight, shared revision)-------> [Policy Admin & Store]
   |
   |  (B2: Residuals: ITEM_FILTER, RESOLVE_WILDCARD, PARTIAL_BATCH, ATOMIC_BATCH,
   |       PREDICATE, POLICY_EVALUATION; ancestor binding; commit atomicity; ErrorInfo)
   v
[Application Handler & Data Store]


Layer A: Repository & Verification Toolchain
============================================

[index.html (Spec + JS MODEL + UI + Protobuf blocks)]
   |  (B7: Script extraction, JSON codec, Lean build, axiom/mutation/drift checks)
   +---> hack/load-model.js ---> hack/run-checks.js / hack/formal/verify-cases.js <---> [Lean Oracle]
   |                                                ^                                        ^
   +---> formal/sync-manifest.json -----------------+--> hack/formal/verify.js --------------+--- formal/Authz/
   |
   +--(B8: Protobuf extract/lint, headless Chrome, Markdown export, static hosting)--> [proto/, exports, browser]
```

| Boundary | Layer | Components separated | Security invariant across boundary |
| --- | --- | --- | --- |
| `B1` | Layer B | Untrusted caller <-> Service interceptor | Authorize before validation and existence checks; enforce `Authz.segmentOk`; resolve `indirect` aliases and check `as-written` sites before policy; extract `populated` presence inside the interceptor; fail closed on malformed inputs. |
| `B2` | Layer B | Interceptor <-> Handler & storage | Enforce all returned residuals; bind all ancestor segments on multi-collection and `as-written` lookups (`Authz.storedAsWritten`); pin checks through commit; return identical serialized `ErrorInfo` bytes on opaque denials. |
| `B3` | Layer B | Policy administration <-> Policy store & projector | Restrict `Authz.Sight` and `Authz.PrivacyBoundary` edits to trusted, snapshot-pinned sources; commit boundaries before private rules; forbid rules at or below `as-written` sites; maintain one shared global revision when private rules are enabled. |
| `B4` | Layer B | IdP / alias / fault adapters <-> Server resolver & projector | Bind `ownsAlias`, `canReadNow`, group memberships, and fault observations to the authenticated caller and pinned request snapshot; enforce `faultsOf` precedence; rotate `subject_context_id` on identity-fact changes. |
| `B5` | Layer B | Descriptor source <-> Server & client interpreters | Reconcile validated descriptors (`Authz.Descriptor.valid`) against the live reflected RPC roster; default-deny optional-API `undeclared` RPCs and unreviewed `handler_policy` exits; verify `no_side_effects` against handler writes; update `descriptor_etag` on every semantic edit. |
| `B6` | Layer B | `QueryPermissionContexts` <-> Client / UI / MCP host | Treat contexts strictly as advisory; validate envelopes, key-set ID bounds (`≤ 2147483647`), scopes, holes, expiry, and `min_snapshot_token` ordering; re-authorize every RPC independently on the server. |
| `B7` | Layer A | Repository source <-> Formal verification & parity harness | Enforce manifest SHA-256 freshness, Lean kernel standard-axiom hygiene, escape scanning, differential JS/Lean parity, proof mutations, and embedded-model drift rejection. |
| `B8` | Layer A | Repository source <-> Browser reader, protobuf pipeline & exports | Keep `index.html` free of unsafe DOM execution and unintended external scripts; keep extracted protobuf contracts and Markdown exports synchronized with `index.html`. |

### 4.2 Layer A Trusted Computing Base and limits

Assurance claims produced by `gmake verify-formal` trust:

1. The Lean 4 proof kernel and standard axioms (`Classical.choice`, `Quot.sound`, `propext`), audited across all compiled theorems in `Authz.*` and `Main`.
2. The Lean 4 compiler and runtime executing `Authz.Oracle.handle` during differential parity checks.
3. The Node.js runtime and `hack/load-model.js` (`extractModel`) extracting and running the embedded JS model from `index.html`.
4. The verification harness (`hack/formal/verify.js`, `hack/formal/verify-cases.js`, `hack/formal/codec.js`, and isolated proof mutations) together with `formal/sync-manifest.json`.

Explicit TCB limits in the Layer A harness:

- Manual prose-to-declaration mapping: `sections` and `outsideSemanticCore` in `formal/sync-manifest.json` are curated manually. `hack/formal/verify.js` verifies exhaustive `<h3>` heading coverage and Lean declaration existence, while semantic equivalence between specification prose and Lean definitions requires human review.
- Lexical escape scanning and theorem-only axiom auditing: `hack/formal/verify.js` strips comments, strings, and character literals before scanning Lean sources for literal escape tokens and audits `#print axioms` across all compiled `.thmInfo` declarations in `Authz.*` and `Main`; it does not inspect non-theorem definitions for macro-hidden escapes.
- Narrow `toolchainSha256` coverage: `toolchainSha256` hashes `formal/lean-toolchain` and `formal/lakefile.toml` only. Node.js, npm packages under `hack/`, Python 3, `protoc`, `api-linter`, Chrome, `Makefile`, and static hosting lie outside that hash.
- JS-normalized descriptor inputs in parity tests: `hack/formal/codec.js` builds Lean descriptor inputs from raw declarations combined with JS `MODEL.interpret` outputs. Although `Authz.Descriptor.valid` re-checks derived service identity, source signatures, reflected addresses, effects, and explicit permissions, the parity harness does not parse raw protobuf `FileDescriptorSet` bytes independently.
- Excluded optional-method callbacks: External JS `undeclaredPolicy` callbacks are excluded from Lean differential totals because `Authz.authorizeRequest` always denies `Authz.Disposition.undeclared`.
- JS-only invalid-selector replay: Lean makes a compiled rule with invalid role selectors unrepresentable (`Authz.rulesFromGrants` returns `none`), so embedded request replays over JS rules marked `invalidSelectors` assert the fail-closed JS outcome and are counted as `invalidSelectorReplays` instead of being sent to Lean. Grant expansion and grant-level decisions for the same invalid selectors are compared differentially (`expand`, `grantPolicy`).

### 4.3 Layer B formal theorem premises

The Lean proof suite (also summarized in `formal/README.md`) establishes runtime properties conditioned on these deployment premises:

- Well-formed descriptors (`Authz.Descriptor.WellFormed`): Registered methods, resource patterns, singleton/collection disjointness, batch parent declarations, and field-guard metadata match the live reflected RPC roster.
- Admissible policy stores (`Authz.PolicyStore.admissible`): Policy transactions commit atomically with trusted `Authz.Sight` visibility inputs, pre-committed `Authz.PrivacyBoundary` declarations, valid grant sites, and no rules attached at or below `as-written` sites (`Authz.NameResolver.rulesAllowed`).
- Truthful request-time adapters: Canonical name resolution (`Authz.NameResolver.canonical`), alias authorization (`Authz.Query.World.ownsAlias`, `Authz.Query.World.canReadNow`), row attribute readers (`Authz.ServerOptions.factsOf`), and fault adapters (`Authz.ServerOptions.faultsOf`) reflect the authenticated caller on one pinned snapshot.
- Compliant residual handlers: Methods setting `Authz.ServerOptions.handlerResolvesResiduals` enforce every returned residual (`ITEM_FILTER`, `RESOLVE_WILDCARD`, `PARTIAL_BATCH`, `ATOMIC_BATCH`, `PREDICATE`, `POLICY_EVALUATION`) on the same snapshot before committing writes or disclosing absence.
- Conforming wire, revision, and trace order: Grouped wire replies fit signed 32-bit key-set ID bounds (`keySets.length ≤ 2147483647`), replicas honor `min_snapshot_token` and external authority retirement (`Authz.ConformingReply`), and client listing traces satisfy `Authz.ClientEvent.orderedAfter` so retired tokens are never re-accepted.

---

## 5. Threat catalog

Response dispositions follow the W3C ERTA vocabulary: **Eliminate** (removed by design), **Reduce** (mitigated with residual noted), **Transfer** (assigned to implementer, deployer, or client), and **Accept** (known constraint or trade-off retained with rationale).

### 5.1 Layer B: Target protocol and enforcement threats

W3C origin: in-scope threats addressed by the specification and checked across the Lean proof suite and embedded reference model. Anchors below distinguish kernel-proved theorems from modeled predicates and deployment premises.

| ID | Threat | Category | Boundary | Disposition | Spec & formal anchors |
| --- | --- | --- | --- | --- | --- |
| `TH-01` | Privilege escalation via missing checks, key/class collision, upsert (`allow_missing`), `Expunge`, batch bypass, or ceiling bypass | STRIDE: EoP | `B1`, `B5` | **Eliminate** (Core under valid descriptors, grant sites, and selectors that pass `validateRoleSelectors`) / **Reduce** (extensions) | §3.2–§3.3 (`p3-granularity`, `p3-grants`), §4.2 (`p4-interpretation`), §4.3 (`p4-methods`); predicate `Authz.Descriptor.valid`; theorems `Authz.Descriptor.explicit_permissions_exact`, `Authz.invalid_selector_fails_closed`, `Authz.expanded_policy_exact`, `Authz.Grant.forbid_ignores_ceiling`, `Authz.compiled_grant_ceiling`, `Authz.authorizeRequest_target_sound`, `Authz.batchRequestStatus_item_sound`, `Authz.Rule.unknown_fault_fails_closed` |
| `TH-02` | Path-prefix confusion, singleton/collection collision, fixed-parent bypass, or cross-tenant ID traversal | STRIDE: EoP, InfoDisc | `B1`, `B2` | **Eliminate** (grammar & patterns) / **Transfer** (handler binding) | §1.4 (`p1-invariants`), §3.4 (`p3-hierarchy`), §4.2 (`p4-interpretation`); predicates `Authz.segmentOk`, `Authz.Scope.valid`, `Authz.storedAsWritten`; theorems `Authz.Descriptor.singleton_not_collection`, `Authz.Descriptor.distinct_resources_disjoint`, `Authz.EndpointExample.fixed_parent_rejected` (fixed-parent regression), `Authz.Disclosure.other_collection` (row-filter lemma), `Authz.lookup_nonmember` (handler non-membership) |
| `TH-03` | Existence oracles via absent/hidden rows, inconclusive or multi-match lookups, indirect upserts, wildcard `Get`, `Delete(allow_missing)`, or `Create` collisions | STRIDE: InfoDisc; LINDDUN: Detecting | `B1`, `B2` | **Reduce** (uniform `ErrorInfo`; 1-bit chosen-ID `Create` collision accepted) | §4.3 (`p4-methods`); theorems `Authz.resource_lookup_opacity`, `Authz.inconclusive_lookup_opacity`, `Authz.inconclusive_lookup_diagnostic`, `Authz.denied_match_uses_absent_diagnostic`, `Authz.indirect_upsert_checks_each_parent`, `Authz.direct_upsert_denied_key`, `Authz.lookup_preflight_denial`, `Authz.lookup_denial_before_storage`, `Authz.projecting_denial_precedes_discovery`, `Authz.create_collision_requires_read`, `Authz.Disclosure.hidden_read`, `Authz.Disclosure.hidden_collision_denial_payload` |
| `TH-04` | Private-rule or hidden-scope disclosure via permission contexts, holes, `descendants_omitted`, or batch Step 3 validation | STRIDE: InfoDisc; LINDDUN: Detecting, Disclosure | `B3`, `B6` | **Eliminate** (above declared privacy boundary under admissible stores and a shared global revision) | §3.6 (`p3-claims`), §4.3 (`p4-methods`); theorems `Authz.canName_resource_sound`, `Authz.policy_trace_admissible`, `Authz.admissible_no_private_obstruction`, `Authz.admissible_response_private_twins`, `Authz.reachable_response_private_twins`, `Authz.Query.response_private_twins`, `Authz.Query.response_private_forbid_absent`, `Authz.batchRequestStatus_step3_private` |
| `TH-05` | Unauthorized alias resolution or misattached rules on `as-written` secondary keys in `QueryPermissionContexts` | STRIDE: InfoDisc; LINDDUN: Identifying, Linking | `B4`, `B6` | **Eliminate** (resolver model) / **Transfer** (adapter truth) | §3.4 (`p3-hierarchy`), §4.1 (`p4-proto`); relation `Authz.Query.AuthorizedPath`; theorems `Authz.Query.response_alias_disclosure`, `Authz.Disclosure.anchor_opacity`, `Authz.as_written_query_uses_supplied_name`, `Authz.reachable_as_written_rules` |
| `TH-06` | Silent privilege expansion or consent-gating bypass during API evolution (`READ_ONLY` -> `MUTATING`) | STRIDE: EoP, Tampering | `B5`, `B6` | **Reduce** (diff signal & ETag; release review and consent gating remain host/process controls) | §3.7 (`p3-evolution`: capability diff, `explicit_grant_only`, `descriptor_etag`, AIP-180 effect rule); selector/availability/enforcement definitions `Authz.Grant.selects`, `Authz.methodAvailable` (client availability screening), `Authz.authorizeRequest` (server disposition); `Evolve` regression checks in `index.html` |
| `TH-07` | Cross-snapshot splicing (`MoveWidget`), revocation rollback, expired-claim resurrection, or wire-receipt corruption | STRIDE: Tampering, EoP (advisory layer) | `B6` | **Eliminate** (within checked model under conforming wire, revision, and ordered-trace premises) / **Transfer** (replica fencing and retired-token ordering, `TH-17`) / **Accept** (fixed-revision IdP shifts, `TH-09`) | §3.8 (`p3-caching`), §4.1 (`p4-proto`), §4.4 (`p4-algorithms`); theorems `Authz.offer_allow_one_snapshot`, `Authz.no_resurrected_allow`, `Authz.conflict_survives_expiry`, `Authz.scope_no_resurrection`, `Authz.usableRegions_no_resurrection`, `Authz.accepted_subject_change_floor`, `Authz.revocation_never_rolls_back`, `Authz.GroupedReply.received_context_valid`, `Authz.GroupedReply.canonical_received_envelope`, `Authz.grouped_offer_sound`, `Authz.grouped_reply_respects_maxProfile` |

- Role-selector validation vs. runtime compilation (`TH-01`, `TH-06`): Authoring and CI validation (`validateRoleSelectors`) rejects undeclared resource types and operations the selected type does not declare so misspelled `forbid` rules fail before deployment, and `capabilityDiff` surfaces selector errors against new descriptors. Runtime grant compilation (`Authz.rulesFromGrants`, `Authz.invalid_selector_fails_closed`) fails closed on empty selector lists, malformed selectors, malformed or undeclared resource types, and syntactically invalid operations, while letting well-formed operations not declared for the selected type expand to zero keys so API version evolution does not fail unrelated RPCs for live callers. Deployments that map roles from credentials in code must run `validateRoleSelectors` in CI or startup checks so a misspelled `forbid` never reaches production (§8.2).
- Fault authority semantics (`TH-01`, `TH-03`): Under both `failClosed` and `skipErrors`, an unknown (`none`) fault outcome fails closed (`Authz.Rule.unknown_fault_fails_closed`), and an independent fault adapter overrides stale row observations (`Authz.unknown_fault_overrides_stale_row`). Under `skipErrors`, however, an observed fault (`some true`) on a `forbid` skips that `forbid` (`Authz.LookupExample.joined_fault_witness`), so deployments choosing an error-skipping engine must treat fault reporting as security-critical.
- Conditional boundaries behind the table ratings (`TH-03`, `TH-04`, `TH-07`): Lookup opacity (`TH-03`) compares worlds sharing the descriptor, method, request, rules, ancillary rows, and every `ServerOptions` field except the alias lookup (including authority mode, `factsOf`, `faultsOf`, row failures, ceiling, remaining name-resolver settings, `canName`, and `nonprojecting`). Private-rule non-interference (`TH-04`) depends on pre-committed privacy boundaries and a shared global revision, and the client guarantees behind `TH-07` rest on separate premises: non-resurrection and non-rollback on conforming fenced replies and ordered listing traces, grouped wire-receipt soundness on signed 32-bit key-set ID bounds, and wildcard `List` offer soundness on canonical unbudgeted Scoped Claims reprojection (`Authz.ListFrameSource`). `formal/README.md` summarizes the load-bearing assumptions for each area; each theorem's full premises are in its Lean statement.

### 5.2 Layer B: Specified client/server protocol trade-offs

W3C origin: residual design trade-offs in the advisory client cache protocol, distinct from Layer A reference-API fixture behavior (`TH-18`).

| ID | Threat | Category | Boundary | Disposition | Spec & formal anchors |
| --- | --- | --- | --- | --- | --- |
| `TH-08` | Malformed context in an accepted newer reply discarded while an older `ALLOW` remains live | STRIDE: Tampering / stale advisory evidence | `B6` | **Accept** (bounded advisory staleness) / **Transfer** (client fault handling) | §4.1 (`p4-proto`), §4.4 (`p4-algorithms`); `Authz.GroupedReply.receive?`, `Authz.acceptSnapshot`, JS `acceptNextSnapshot` |
| `TH-09` | Equal `(service, subject_context_id, snapshot_token)` merges frames across IdP or claims changes | STRIDE: EoP (advisory layer) | `B4`, `B6` | **Accept** (documented in §3.8) / **Transfer** (server `subject_context_id` rotation) | §3.8 (`p3-caching`); `Authz.PolicyIdentity`, `Authz.snapshotAction`, `Authz.latestContexts` |

- `TH-08` mechanic: `Authz.GroupedReply.receive?` and JS `acceptNextSnapshot` reject malformed response-wide key tables and duplicate anchors, while skipping an individual malformed context. If a newer reply (`t2`) carries a malformed `DENY` context, the client advances to `t2` with zero decoded contexts for that anchor, leaving a previously accepted `t1` `ALLOW` offered until `t1` expires. Malformed input cannot fabricate a new `ALLOW`, and server enforcement denies immediately and triggers refresh. Production clients may treat any discarded context in an authenticated reply as a producer fault and clear prior offers (§8.2).
- `TH-09` mechanic: `min_snapshot_token` enforces policy-store revision ordering; it does not order changes to identity-provider attributes or group memberships. Two replies sharing `(service, subject_context_id, snapshot_token)` merge in the client cache and can jointly satisfy a multi-target `offer` even if identity facts differed between replies. Server enforcement evaluates every call independently; production servers should rotate `subject_context_id` or hash the canonical claims digest into snapshot identity whenever authenticated authorization inputs change (§8.2).

### 5.3 Layer B: Transferred implementation and deployment threats

W3C origin: runtime integration boundaries transferred to service adopters. Each property holds inside the checked JS and Lean models under its explicit premises; required engineering controls are consolidated in Section 8.2.

| ID | Threat | Category | Boundary | Disposition | Formal boundary & obligation |
| --- | --- | --- | --- | --- | --- |
| `TH-10` | Untrusted, forged, or stale `Sight` visibility inputs or policy-admin writes converting a private group rule into a public rule | STRIDE: InfoDisc, Tampering | `B3` | **Transfer** | `Authz.PolicyStore.commit`, `Authz.Sight`, `Authz.canName_resource_sound`, `Authz.reachable_public_rule_read`; §8.2 (Policy store) |
| `TH-11` | Stale, unsynchronized, or caller-controlled `ownsAlias`, `canReadNow`, or fault-evaluation callbacks | STRIDE: InfoDisc, Spoofing, EoP | `B4` | **Transfer** | `Authz.Query.World` (`ownsAlias`, `canReadNow`), `Authz.ServerOptions.available_sources`, `Authz.unknown_fault_overrides_stale_row`; §8.2 (Adapters) |
| `TH-12` | Misordered privacy-boundary deployment or per-caller/private-dependent revision, expiry, or ETag metadata | STRIDE: InfoDisc; LINDDUN: Detecting | `B3`, `B6` | **Transfer** | `Authz.Query.response_private_twins`, `Authz.Query.distinct_stamps`, `Authz.admissible_response_private_twins`; §8.2 (Policy store) |
| `TH-13` | Permissive optional-API `undeclared` callbacks, mislabeled `handler_policy` or `no_side_effects` annotations, disabled Field Guard checks, or descriptor-to-server drift | STRIDE: EoP, Tampering | `B5` | **Transfer** | `Authz.Descriptor.valid`, `Authz.Disposition.undeclared`, `Authz.Disposition.handlerPolicy`, `Authz.MethodDecl.noSideEffects`, `Authz.Descriptor.rejectUnhandledFieldGuards` (`rejectsUnhandledGuards`), JS `undeclaredPolicy`; §8.2 (Descriptors) |
| `TH-14` | Partial-batch, wildcard-`Get`, or filtered-`Search` handlers ignoring interceptor residuals or bypassing per-item authorization and atomicity | STRIDE: EoP, InfoDisc | `B2` | **Transfer** | `Authz.ServerOptions.handlerResolvesResiduals`, `Authz.authorizeRequest_checked`, `Authz.authorizeRequest_unhandled`, `Authz.authorizeRequest_partial_proceed`, `Authz.method_partial_offer_authorizes`; §8.2 (Handlers) |
| `TH-15` | Untrusted `populated` field-presence inputs, missing field metadata, or unconstrained handler writes under Field Guards | STRIDE: EoP | `B1`, `B2`, `B5` | **Transfer** | `Authz.FieldGuards.effectiveMask`, `Authz.FieldGuards.effectiveMask_unknown_population`, `Authz.FieldGuards.effectiveMask_oneof_sibling`, `Authz.FieldGuards.effectiveMask_strips_output_only`, `Authz.FieldGuards.unmasked_update_writes_all`, `Authz.MethodDecl.guard_covers_upsert_parent`, `Authz.Descriptor.guarded_parents_declared`; §8.2 (Field Guards) |
| `TH-16` | Multi-snapshot lookup races, canonical-name error leaks, or distinguishable storage errors breaking lookup opacity | STRIDE: InfoDisc; LINDDUN: Detecting | `B2` | **Transfer** | `Authz.resource_lookup_opacity`, `Authz.inconclusive_lookup_opacity`, `Authz.lookup_checks_primary_resolution`, `Authz.Disclosure.errorPayload`; §8.2 (Handlers) |
| `TH-17` | Unfenced multi-replica failover or non-monotonic authority retirement rolling back revocations or re-accepting retired tokens | STRIDE: EoP (advisory layer) | `B3`, `B6` | **Transfer** | `Authz.ConformingReply`, `Authz.revocation_never_rolls_back`, `Authz.ClientEvent.orderedAfter`, `Authz.usableRegions_no_resurrection`, `Authz.serveWithMinSnapshot`; §8.2 (Adapters) |

- Descriptor exits (`TH-13`): `Authz.Disposition.handlerPolicy` and optional-API `Authz.Disposition.undeclared` confer no Core declarative permissions. `Authz.MethodDecl.noSideEffects` sets a `handlerPolicy` method's advertised effect to `READ_ONLY` (and permits `read`/`admin` classes on `requirements` methods) without inspecting handler writes. When `Authz.Descriptor.fieldGuardsEnabled` is `false`, standard writers for guarded resources are rejected only when `Authz.Descriptor.rejectUnhandledFieldGuards` activates the `rejectsUnhandledGuards` gate in `Authz.Descriptor.valid`. In the JS reference model, a deployment-supplied `undeclaredPolicy` callback can override default denial on `undeclared` methods.
- Adapter and handler trust inputs (`TH-10`, `TH-14`, `TH-15`): `Authz.PolicyStore.commit` treats each `Authz.Sight` entry as a truthful snapshot-pinned primary read observation; `Authz.authorizeRequest` accepts `handlerResolvesResiduals` as a deployment assertion and transfers per-item authorization, original-index reporting, and all-fail `ABORTED` on `PARTIAL_BATCH` to the handler (`Authz.authorizeRequest_partial_proceed` proves outer authorization plus residual handoff, not item-level enforcement); `Authz.FieldGuards.written` trusts the normalized `populated` and `mask` inputs supplied for the request body (`Authz.FieldGuards.written_writable` proves computed paths are writable, not adapter completeness). Under §4.5’s documented Core-client exception, a client that does not opt into Field Guards ignores field options and may return an advisory `ALLOW` on a guarded write that the server authoritatively denies.

### 5.4 Layer A: Repository, reference-model, and verification-toolchain threats

W3C origin: threats targeting this repository's shipped specification, embedded JS reference model, and verification toolchain.

| ID | Threat | Category | Boundary | Disposition | Artifact & control anchors |
| --- | --- | --- | --- | --- | --- |
| `TH-18` | Exported JS reference evaluators accept envelope-free fixture frames | STRIDE: Tampering, Repudiation (reference API misuse) | `B6`, `B7` | **Accept** (fixture convenience) | `index.html` `MODEL.evaluate`, `MODEL.usableRegions`, `MODEL.offer` (`validStoredSnapshot`, `snapshotEvidence`) |
| `TH-19` | Lean proof escapes, harness weakening, or specification-to-model desynchronization | STRIDE: Tampering, Repudiation | `B7` | **Reduce** (`hack/formal/verify.js` gates) / **Accept** (TCB limits in §4.2) | `formal/sync-manifest.json`, `hack/formal/verify.js`, `hack/formal/codec.js`, `hack/formal/request-cases.js` |
| `TH-20` | Client-side script injection (DOM XSS), compromised static hosting, or build/export tampering | STRIDE: Tampering, InfoDisc | `B7`, `B8` | **Reduce** (static artifact without credentials or external scripts; manual review required) | `index.html`, `Makefile`, `build/proto/` vs. `proto/`, `gmake export-md`, `hack/package-lock.json` |

- `TH-18` (JS reference-API fixture behavior): Envelope-free frame acceptance is specific to the embedded JS reference API in `index.html` and is distinct from the Layer B protocol trade-offs in `TH-08` and `TH-09`. `MODEL.evaluate`, `MODEL.usableRegions`, and `MODEL.offer` accept raw fixture objects lacking `service`, `subject_context_id`, `snapshot_token`, and `expire_time`, treating missing expiry as indefinitely live. Lean's typed client (`Authz.Frame`, `Authz.SnapshotReply`) requires complete envelopes; legacy §4.6 envelope-free fixture replay is isolated in `Authz.RequestOracle.fixtureOffer` (which synthesizes fixture envelopes and skips malformed frames), distinct from `Authz.Oracle.clientState` (which imports complete serialized histories with envelope and serial-order validation). This convenience has no impact on server enforcement and affects only callers that improperly embed the specification's inline JS in production applications.
- `TH-19` (Proof and harness integrity): `gmake verify-formal` enforces manifest SHA-256 freshness, warning-free Lean compilation, lexical escape scanning, kernel-level axiom auditing, differential parity, isolated proof mutations, and embedded-model drift rejection (§7.1). Remaining accepted limits are documented in §4.2.
- `TH-20` (Browser and export pipeline): `index.html` holds no user credentials or backend API keys and loads no external scripts, stylesheets, or iframes (using inline page scripts, a `data:,` favicon, and a generated print document with an inline print trigger). Its `innerHTML` writes render static or enum-derived strings, URL parameters (`format`, `doc`, `raw`) recognize `format=md`, allow-list `doc` against the fixed document list with an `all` fallback, read `raw` only as the boolean `raw=1` (plain Markdown view), render a static toolbar template, and serialize Markdown content through `textContent`, and print blob URLs are revoked via `URL.revokeObjectURL`. `gmake -j check` verifies protobuf extraction, compilation, linting, JS model checks, headless Chrome loading, and `verify-formal`; DOM sinks, Markdown export, `Makefile`, and `hack/package-lock.json` remain outside the formal gate and require direct review (§8.1).

### 5.5 Dependency threats

W3C origin: threats inherited from upstream parsers, libraries, toolchains, and infrastructure.

| ID | Layer | Threat | Category | Boundary | Disposition | Scope & mitigation |
| --- | --- | --- | --- | --- | --- | --- |
| `TH-21` | Layer B | AIP-161 non-standard `FieldMask` parser divergence (backtick map keys and mid-path `*` wildcards) | STRIDE: EoP, Tampering | `B1`, `B5` | **Transfer** | §4.5 (`p4-extensions`): standard protobuf `FieldMask` libraries reject map/wildcard paths; ship matching custom parsers or limit Field Guards to top-level and singular nested fields (§8.2). |
| `TH-22` | Layer A & B | Vulnerabilities or supply-chain compromise in upstream toolchains, protobuf/gRPC libraries, TLS, or IdP stacks | STRIDE: Tampering, Spoofing | `B1`, `B7`, `B8` | **Transfer / Accept** | Layer A hashes `formal/lean-toolchain` and `formal/lakefile.toml` in `toolchainSha256`; `Makefile`, `hack/package-lock.json`, and static hosting lie outside that hash and require direct review (§8.1). Layer B transport and authentication rely on standard TLS and IdP/gRPC stacks. |

---

## 6. Explicitly out of scope

These items define the scope boundary of the specification. Deployments facing these threats require additional controls outside this architecture:

- Timing and response byte-length side channels (§3.6 / `p3-claims`): Formal privacy and lookup-opacity theorems (`Authz.Query.response_private_twins`, `Authz.admissible_response_private_twins`, `Authz.resource_lookup_opacity`, `Authz.inconclusive_lookup_opacity`) cover response content and serialized `ErrorInfo` payloads at the same descriptor service/domain; execution latency and wire byte length are excluded.
- Coarse global revision signal (§3.6 / `p3-claims`): Advancing a shared global `snapshot_token` on a private edit can reveal that some policy change occurred globally (`Authz.Query.distinct_stamps`). Deployments that must hide global edit occurrence require a different protocol.
- One-bit hidden collision inference on caller-chosen `Create` IDs (§4.3 / `p4-methods`): A caller authorized to invoke `Create` under a parent who receives `PERMISSION_DENIED` on a chosen ID can infer a hidden duplicate (`Authz.Disclosure.authorized_create_distinguishes`). Services that cannot accept this 1-bit signal must assign resource IDs on the server.
- Direct child permit revealing a resource name without parent `List` (§3.6 / `p3-claims`): A direct visible permit at a resource site satisfies `Authz.Nameable.direct` even when the caller cannot list its parent. Deployments keeping parent names confidential must declare a parent-level `Authz.PrivacyBoundary` and constrain direct grants.
- Non-hierarchical sharing graphs (§5.1 / `p5-objections`): Coarse scope-level permission contexts target hierarchical resource trees; ad-hoc per-item sharing or dense row-level ABAC requires a relationship-based system (such as Zanzibar, SpiceDB, or OpenFGA).
- Host compromise, network availability, transport encryption, and upstream authentication: Compromised server hosts or root operators, network denial-of-service, TLS configuration, and IdP token issuance or verification lie outside this threat model.

---

## 7. Verification gates and assurance scope (Layer A)

### 7.1 Executable verification commands

Reviewers verify current repository state by running the build and formal gates directly (using GNU Make 4.3+, invoked as `gmake` on macOS):

- Formal verification and parity gate (`gmake verify-formal`): Executes `hack/formal/verify.js` (run `gmake record-formal` after intentional specification or proof edits to refresh `formal/sync-manifest.json`). Enforces:
  1. Manifest SHA-256 freshness: Compares recorded hashes in `formal/sync-manifest.json` against `index.html` (`documentSha256`), the JS model extracted via `hack/load-model.js` (`modelSha256`), the single canonical status/version header (`versionHeaderSha256`, verifying version agreement with `manifest.version`), all Lean sources (`leanSourcesSha256`), and `formal/lean-toolchain` plus `formal/lakefile.toml` (`toolchainSha256`), and confirms `index.html` stays unchanged during the run.
  2. Heading coverage and declaration existence: Verifies that all `<h3 id="p\d+-...">` headings in `index.html` partition exhaustively into `sections` and `outsideSemanticCore` (`p2-catalog`, `p2-matrix`, `p3-simulator`, `p5-bibliography`), checks the manifest's internal theorem-group keys, `#check`s every referenced `Authz.*` declaration in Lean, and asserts §4.2 build-rejection table coverage for singleton/collection collisions and `BatchUpdate` child-request fields. Semantic equivalence between specification prose and mapped Lean declarations remains a manual review check (§4.2).
  3. Warning-free Lean build and escape scanning: Runs `lake --wfail build`, strips nested comments, strings, and character literals across all Lean sources, and rejects `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `partial`, `implemented_by`, `extern`, `csimp`, and `opaque`.
  4. Kernel-level axiom audit: Enumerates all compiled `.thmInfo` declarations across `Authz.*` and `Main` (including private and generated theorems), runs `#print axioms` on each, rejects any axiom outside `propext`, `Classical.choice`, and `Quot.sound`, verifies report count completeness, and confirms every manifest theorem appears in the audited set.
  5. Model checks, differential parity, mutations, and drift rejection: Runs embedded JS checks (`hack/run-checks.js`), compares independent JS and Lean oracle (`Authz.Oracle.handle`) executions (`hack/formal/verify-cases.js`), executes isolated proof mutations verifying each fails at its target without missing `.olean` errors, and injects deliberate drift into a temporary copy of `index.html` (`hack/formal/verify.js --check-source`) to confirm preflight failure on `modelSha256`.
- Specification, protobuf, and browser check pipeline (`npm ci --prefix hack && gmake -j check`): Requires Node.js 18+, npm, Python 3, `protoc`, Google's `api-linter`, and Google Chrome (plus `GOOGLEAPIS_DIR` / `PROTOBUF_INCLUDE` when googleapis or well-known protobuf types are absent locally). Runs JS model checks (`gmake checks`, or `gmake checks-all` for per-check output), extracts `authz/v1/annotations.proto`, `permission_context.proto`, and `field_guards.proto` from `index.html` into `build/proto/`, compares them with `proto/` (updated via `gmake update-protos`), compiles and lints the contracts, opens local `index.html` in headless Chrome, and runs `verify-formal`. Do not run concurrent Lean builds alongside `verify-formal` or `record-formal`.

### 7.2 Checked Lean theorem areas

Every declaration listed below is indexed in `formal/sync-manifest.json` and audited by `gmake verify-formal`. Supporting definitions and premises referenced in Sections 4 and 5 (such as `Authz.Descriptor.valid`, `Authz.Scope.valid`, `Authz.NameResolver`, `Authz.ServerOptions`, and `Authz.Query.World`) are compiled by the warning-free Lean build; only declarations indexed in the manifest are `#check`ed by name.

| Area | Verified property scope | Representative Lean theorems |
| --- | --- | --- |
| Grants and resource names | Hierarchical monotonicity, singleton/collection disjointness, fixed-parent rejection regression, and selector-to-projection equivalence | `Authz.monotone_iff_pointwise_universal`, `Authz.Descriptor.singleton_not_collection`, `Authz.universal_permit_singleton`, `Authz.grant_policy_universal_singleton`, `Authz.EndpointExample.fixed_parent_rejected`, `Authz.expanded_projection_exact` |
| Enforcement, Field Guards, and offers | Authoritative enforcement, descriptor validity, selector validation, ceiling/forbid precedence, fault precedence, writable-path Field Guard soundness, batch item soundness, alias widening, and grouped wire-to-offer soundness (conditional on `ListFrameSource` for wildcard List) | `Authz.Descriptor.explicit_permissions_exact`, `Authz.Descriptor.nameless_pure_handler_policy`, `Authz.invalid_selector_fails_closed`, `Authz.Rule.unknown_fault_fails_closed`, `Authz.ServerOptions.available_sources`, `Authz.authorizeRequest_checked`, `Authz.authorizeRequest_target_sound`, `Authz.authorizeRequest_partial_proceed`, `Authz.batchRequestStatus_item_sound`, `Authz.FieldGuards.effectiveMask_oneof_sibling`, `Authz.method_offer_canonical_allow`, `Authz.grouped_offer_sound`, `Authz.GroupedReply.canonical_fields_of_query`, `Authz.wildcard_list_offer_authorizes` |
| Projection | Projection partitioning, bottom-up cell merging, per-anchor classification consistency, Grant-Shaped preservation, context validity, scope evaluation, and `usableRegions` soundness | `Authz.Domain.nonemptyRegion_iff`, `Authz.partition_total`, `Authz.mergeCells_exact`, `Authz.scoped_projection_total`, `Authz.projection_no_mixed_overlap`, `Authz.grantShaped_publishes_child`, `Authz.Descriptor.projectContext_valid`, `Authz.usableRegions_sound` |
| Disclosure and lookup opacity | Privacy-twin equivalence, alias prefix authorization, lookup opacity (hidden, inconclusive, multi-match, indirect upsert, `Create` collisions), preflight denial ordering, and batch Step 3/4 checks | `Authz.Query.response_private_twins`, `Authz.Query.response_alias_disclosure`, `Authz.resource_lookup_opacity`, `Authz.inconclusive_lookup_opacity`, `Authz.inconclusive_lookup_diagnostic`, `Authz.lookup_preflight_denial`, `Authz.lookup_denial_before_storage`, `Authz.indirect_upsert_checks_each_parent`, `Authz.batchRequestStatus_step3_private`, `Authz.batchRequestStatus_step4_parent`, `Authz.batch_ok_unique_resources` |
| Policy store authoring | Policy-store commit invariants, inductive `Nameable` soundness, effect-independent read discovery, `as-written` rule prohibition, private-obstruction absence, and trace-preserving privacy-twin equivalence | `Authz.policy_trace_admissible`, `Authz.canName_resource_sound`, `Authz.readMethods_effect_independent`, `Authz.reachable_private_rules`, `Authz.reachable_public_rule_read`, `Authz.reachable_as_written_rules`, `Authz.admissible_no_private_obstruction`, `Authz.admissible_response_private_twins`, `Authz.reachable_response_private_twins` |
| Client receipt and snapshot ordering | Client state-machine safety, envelope/profile/session/generation/subject-floor checks, query floor invariance, fixed-state conflict persistence, wire-receipt origin, and ordered-trace listing non-resurrection | `Authz.offer_allow_one_snapshot`, `Authz.no_resurrected_allow`, `Authz.conflict_at_name`, `Authz.conflict_survives_expiry`, `Authz.accepted_subject_change_floor`, `Authz.revocation_never_rolls_back`, `Authz.GroupedReply.received_context_valid`, `Authz.GroupedReply.canonical_claim_in_table`, `Authz.GroupedReply.canonical_received_envelope`, `Authz.grouped_reply_respects_maxProfile`, `Authz.usableRegions_no_resurrection` |

### 7.3 Outside the formal gate

The automated gates in Section 7.1 leave these areas to manual inspection or downstream implementation testing:

- Semantic equivalence between `index.html` prose and mapped Lean definitions (`sections` and `outsideSemanticCore` in `formal/sync-manifest.json`).
- Independent extraction of protobuf descriptors from raw `FileDescriptorSet` bytes (`hack/formal/codec.js` supplies JS-normalized descriptors alongside source metadata).
- External JS `undeclaredPolicy` callbacks (excluded from Lean differential totals because `Authz.authorizeRequest` always denies `undeclared`).
- Browser DOM/UI changes in `index.html`, Markdown export determinism (`gmake export-md`), `Makefile` targets, non-Lean dependency lockfiles under `hack/`, and static hosting configuration (subject to direct review under `TH-20` and `TH-22`).
- Any production authorization service, storage engine, IdP, replica cluster, or client SDK implemented from this specification.

---

## 8. Reviewer audit checklist and deployer obligations

### 8.1 Security reviewer checklist (Layer A)

1. Run `gmake verify-formal` from a clean checkout (without concurrent Lean builds) and confirm exit code `0`, standard-axiom-only output (`Classical.choice`, `Quot.sound`, `propext`), differential parity pass, isolated proof mutation rejections, and embedded-model drift rejection.
2. Run `npm ci --prefix hack && gmake -j check` to verify protobuf extraction from `index.html`, parity with `proto/`, `protoc` compilation, `api-linter` checks, embedded JS model checks, headless Chrome loading, and `verify-formal`.
3. Inspect theorem premises directly in `Authz.method_offer_authorizes`, `Authz.wildcard_list_offer_authorizes`, `Authz.admissible_response_private_twins`, `Authz.resource_lookup_opacity`, `Authz.inconclusive_lookup_opacity`, `Authz.revocation_never_rolls_back`, and `Authz.usableRegions_no_resurrection`, verifying alignment with Sections 4–6 and `formal/README.md`.
4. Review `formal/sync-manifest.json` (`sections` and `outsideSemanticCore`) and `hack/formal/codec.js` against the Layer A TCB limits (`TH-18`, `TH-19`).
5. Re-audit unverified repository artifacts whenever they change (`TH-20`, `TH-22`): confirm `index.html` keeps zero external runtime scripts and static or enum-derived `innerHTML` sinks, and inspect `Makefile` and `hack/package-lock.json`.

### 8.2 Production deployer obligations (Layer B)

- Authoritative enforcement and client caches (`B1`, `B6`; `TH-01`, `TH-07`, `TH-08`, `TH-09`, `TH-18`): Enforce server-side authorization on every RPC; treat permission contexts strictly as advisory hints; require complete validated envelopes in production client evaluators and avoid embedding the `index.html` reference JS exports in production code; treat discarded malformed contexts in authenticated newer replies as producer faults and clear affected offers until a valid snapshot arrives.
- Descriptors and Core exits (`B5`; `TH-01`, `TH-06`, `TH-13`): Reconcile validated descriptors against the live reflected RPC roster; default-deny optional-API `undeclared` methods and unreviewed `handler_policy` exits; verify `no_side_effects` annotations against actual handler writes; update `descriptor_etag` on every semantic change; enable `rejectUnhandledFieldGuards` when serving guarded resource types without the Field Guards extension.
- Handlers, residuals, and lookup opacity (`B2`; `TH-02`, `TH-03`, `TH-14`, `TH-16`): Gate `handlerResolvesResiduals` so only reviewed handlers enforce `ITEM_FILTER`, `RESOLVE_WILDCARD`, `PARTIAL_BATCH`, `ATOMIC_BATCH`, `PREDICATE`, and `POLICY_EVALUATION` residuals on the pinned policy and row snapshot; bind all ancestor segments on multi-collection and `as-written` lookups; pin alias resolution, policy checks, row lookup, collision checks, and commit to one snapshot; never echo canonical names in denials; normalize storage errors and verify paired hidden/absent, inconclusive, multi-match, and duplicate/denied lookups emit identical serialized status bytes.
- Field Guards (`B1`, `B2`, `B5`; `TH-15`, `TH-21`): Derive `populated` inside the trusted interceptor from decoded protobuf presence (falling back to all writable fields when unknown); reject missing field metadata; constrain handler writes to the computed effective mask; declare guards explicitly on custom writers; ship matching custom `FieldMask` parsers on server and opted-in clients when guarding maps or repeated fields, or restrict Field Guards to top-level and singular nested message fields.
- Policy store, role validation, visibility, and privacy boundaries (`B3`; `TH-01`, `TH-04`, `TH-10`, `TH-12`): Run role-selector validation (`validateRoleSelectors`) at policy write time and in CI or startup tests for code-mapped roles so misspelled `forbid` selectors never reach production; restrict `Sight` visibility inputs and `PrivacyBoundary` edits to trusted server paths or derive visibility from authenticated, snapshot-pinned reads; commit privacy boundaries before writing private rules; execute role/membership expansion, visibility checks, `asWrittenTypes` updates, and rule commits atomically; serve projections from committed state under one shared global `snapshot_token` and private-independent expiry and ETag when private rules are enabled.
- Identity, alias, fault, and replica adapters (`B3`, `B4`, `B6`; `TH-05`, `TH-09`, `TH-11`, `TH-17`): Bind `ownsAlias`, `canReadNow`, group memberships, and fault observations to the authenticated caller, exact supplied and canonical names, and the pinned request snapshot (using fenced reads if mappings and policy reside in separate stores); ensure independent fault-adapter unknown outcomes override stale row observations; rotate `subject_context_id` (or hash the canonical claims digest into snapshot identity) whenever authenticated authorization inputs change; enforce epoch fencing and external authority retirement across failover replicas so lagging or superseded replicas return `UNAVAILABLE` for a held `min_snapshot_token` and retired tokens never re-enter client caches.
