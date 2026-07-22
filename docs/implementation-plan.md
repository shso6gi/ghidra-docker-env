# UNKNOWN Taxonomy v2 Implementation Plan

## 1. Status and operating constraints

- Phase 0-9 baseline status: approved and historically completed under the
  recorded phase gates.
- Phase 10 plan / implementation-start status: `GO`. The reviewed Phase-10
  design authorizes implementation to begin at slice 10.0 and proceed in the
  required order; this start approval does not assert that any implementation
  or acceptance gate has already passed.
- Phase 10 completion status: `NO-GO` until slices 10.0 through 10.5, including
  the current-head real-EqBench gates, pass in order and the independent
  read-only completion review reports no unresolved P0/P1 findings.
- Review baseline: repository HEAD `29376ea` at the time this plan was frozen.
- Scope: UNKNOWN/TIMEOUT/ERROR reason taxonomy, lifecycle authority, decision authority, canonical census, legacy compatibility, and migration validation.
- Soundness rule: never reduce UNKNOWN by weakening an equivalence or disequivalence proof gate.
- Git rule: no agent may run `git add`, `git commit`, or `git push` during this work.
- Ownership rule: the main/root agent is the only agent allowed to create, edit, delete, format, or generate workspace files.
- Reviewer rule: the fixed `plan-reviewer` agent is read-only. It independently inspects this plan, the current diff, and test evidence, then returns findings to the main agent without modifying files.
- Existing untracked or unrelated files belong to the user and must not be changed.

## 2. Agent responsibilities

### Main/root agent: sole writer

The main agent owns all implementation activity:

- implement phases in this document in order;
- add or update code and tests;
- run validation;
- create repo-local audit and validation artifacts;
- maintain the progress table;
- maintain the review-response ledger;
- decide how to address reviewer findings;
- re-request review after fixes;
- keep all changes unstaged and uncommitted.

The main agent must not delegate any file-changing task. It may delegate only read-only review to the fixed reviewer.

During implementation, the main agent creates and maintains:

- `docs/implementation-progress.md`
- `docs/review-response-log.md`

Only the main agent may modify those files. Reviewer responses are returned in chat; the main agent records their disposition in the ledger.

### Fixed `plan-reviewer` agent: read-only reviewer

The reviewer must:

- read this complete plan before reviewing;
- inspect the current unstaged diff and relevant surrounding code;
- inspect test commands, logs, manifests, receipts, and census artifacts;
- independently verify claims rather than relying on the main agent's summary;
- prioritize false-EQUIVALENT risk, hidden blockers, authority drift, lifecycle errors, aggregation errors, and missing negative tests;
- report findings ordered by severity with file and line references;
- provide a separate phase-completion and GO/NO-GO judgment;
- return findings only; never edit files.

The reviewer must not:

- call file-editing tools;
- run formatters or generators that modify the workspace;
- request write escalation;
- implement suggested fixes;
- alter progress or review-response files;
- spawn another agent;
- run `git add`, `git commit`, or `git push`.

## 3. Objective and non-goals

### Objective

Replace the current mutable and partially string-derived UNKNOWN reason system with a versioned, typed, auditable authority chain:

```text
Typed producers
  -> sealed append-only EventStream
  -> CauseLifecycleReducer
  -> VerifiedLifecycleProjection
       - CauseLifecycleSnapshot
       - C_active_base
       - Q_open_base
  -> DecisionFinalizer
  -> DecisionReceipt
  -> Outcome Census Join
       - C_active_by_outcome
       - Q_open_by_outcome
  -> Canonical Metrics
```

### Non-goals

- Do not change solver semantics to obtain more EQ results.
- Do not classify timeout as EQ.
- Do not infer semantic cause from diagnostic strings.
- Do not infer replacement or completion from chronology alone.
- Do not make legacy logs authoritative for v2.
- Do not perform a one-shot replacement of all reasons.
- Do not stage, commit, or push changes.

## 4. Problems being corrected

The implementation must remove or isolate these current failure modes:

- registry entries can be silently overwritten;
- producer calls can override registry-owned metadata;
- unknown strings and suffixes can be normalized into registered reasons;
- semantic reason classification parses rendered strings;
- `unknown_reason.py`, `unknown_reason_summary.py`, `debug_trace.py`, and root-blocker reporting select different primary/final reasons;
- final-attempt position can be mistaken for causal authority;
- solver UNKNOWN/TIMEOUT, lifecycle attempts, and semantic blockers are conflated;
- umbrella reasons hide multiple semantic causes;
- internal exceptions can be reported as UNKNOWN;
- current and legacy results can be aggregated without an explicit result-selection manifest.

## 5. Authority and identity contracts

### 5.1 Immutable `ReasonDefinition`

Registry-owned fields:

```text
ReasonDefinition:
  reason_id
  schema_version
  domain
  reason_class
  decision_effect
  allowed_target_kinds
  required_evidence_contract
  allowed_proof_kinds
  terminal_eligibility
  canonicalization_policy_id
  recovery_addressability
```

`recovery_addressability` is one of:

- `REQUIREMENT_REQUIRED`
- `REQUIREMENT_OPTIONAL`
- `NO_PROOF_RECOVERY`

Production occurrence creation cannot override definition metadata.

### 5.2 Semantic-only `CauseIdV2`

```text
CauseIdV2:
  schema_version
  identity_scope: UNARY | RELATIONAL
  reason_id
  canonical_target_key
  missing_semantic_fact
  semantic_proposition_digest
```

The semantic proposition digest includes only semantic identity:

- semantic proposition;
- observation surface;
- active semantic precondition;
- unary or relational target;
- correspondence contract.

It excludes proof and execution strategy:

- satisfaction contract and expression;
- proof requirement and proof kind;
- solver, timeout, normalization, retry, and proof alternatives.

Adding a recovery alternative must not change `cause_id`. A change to the semantic proposition, target, precondition, identity scope, or correspondence contract must change it.

Before/after semantic-cause comparison is keyed by `cause_id`. It must not be keyed by a satisfaction-contract ID, contract version, expression digest, proof kind, or requirement ID.

Unary canonicalization retains binary content identity, function IR identity, semantic object identity, and expression role. Relational canonicalization retains the comparison domain, both semantic objects, relation direction, and correspondence contract. Execution identity is never a semantic cause identity.

### 5.3 `CauseOccurrence`

```text
CauseOccurrence:
  occurrence_id
  cause_id
  reason_id
  target_id
  bound_satisfaction_contract_id
  bound_satisfaction_contract_version
  normalized_expression_digest
  bound_expression_digest
  proof_requirement_ids
  evidence_refs
  evidence_kind
  source_snapshot_fingerprint
  producer_id
  attempt_id
```

Required invariants:

- `CauseOccurrence.reason_id == CauseIdV2.reason_id`;
- target and identity scope match `ReasonDefinition`;
- the bound satisfaction contract is registry-issued;
- occurrence data cannot mutate after observation.

### 5.4 Registry-owned satisfaction contract

Producers cannot construct completion expressions.

```text
SatisfactionContractDefinition:
  schema_version
  contract_definition_id
  contract_version
  requirement_slots
  normalized_expression_template
  normalized_expression_digest
```

Allowed monotone expression nodes:

- `REQUIREMENT_SLOT(name)`
- `ALL_OF(children...)`
- `ANY_OF(children...)`

`NOT` is forbidden. The registry owns the normalized structural expression; it does not claim full Boolean-equivalence canonicalization.

A typed factory creates:

```text
BoundSatisfactionContract:
  contract_definition_id
  contract_version
  normalized_expression_digest
  slot_bindings
  bound_expression_digest
```

Missing slots, extra slots, duplicate bindings, and incompatible requirement kinds are rejected. Contract changes require a version change.

### 5.5 Requirement completion and live frontier

Producers emit proof completion evidence for individual requirements. They never mark an occurrence completed.

```text
RequirementCompletionReceipt:
  cause_id
  occurrence_id
  proof_requirement_id
  bound_satisfaction_contract_id
  bound_satisfaction_contract_version
  bound_expression_digest
  proof_artifact_digest
  applicability_receipt
```

For declared requirements `R`, completed requirements `S`, uncompleted requirements `U = R - S`, and expression `F`:

```text
M_F(S) = inclusion-minimal T subset-of U where F(S union T) is true
L_F(S) = union of all T in M_F(S)
```

`L_F(S)` is the only authority for the open proof frontier. The antichain evaluator:

- returns `{empty-set}` for a satisfied leaf/subexpression;
- unions and minimizes child antichains for `ANY_OF`;
- computes union-products and minimizes them for `ALL_OF`;
- flattens same-operator nesting, sorts children by digest, removes duplicates, and removes non-minimal supersets.

Consumers must not implement their own live-frontier logic.

Proof-backlog comparison is keyed by `(bound_satisfaction_contract_id, bound_satisfaction_contract_version, proof_requirement_id)`. A contract-version change is therefore visible as proof-worklist evolution without manufacturing a new semantic cause.

### 5.6 Frontier resource policy

```text
FrontierEvaluationBudget:
  max_expression_nodes
  max_antichain_sets
  max_requirement_ids
  max_union_operations
```

On budget exhaustion:

- no partial or empty authoritative frontier is returned;
- the occurrence is not satisfied;
- no valid canonical lifecycle snapshot is sealed;
- shadow result is `SHADOW_EVIDENCE_INCOMPLETE`;
- canonical census is `INVALID`;
- after cutover, an `ErrorReceipt` produces final `ERROR`.

### 5.7 Atomic N-to-M transformation

```text
CauseTransformationEvent:
  header
  transformation_kind: REPLACEMENT | REFINEMENT | COALESCENCE
  replaced_occurrence_ids
  replacement_occurrence_ids
  transformation_proof_receipt_id
  recognizing_stage
  source_snapshot_fingerprint
```

Rules:

- old and new sets are non-empty, disjoint, duplicate-free, and in one stream;
- new occurrences are observed before transformation;
- the receipt binds every old/new occurrence ID, cause ID, requirement mapping, and snapshot;
- the transformation is applied atomically;
- intermediate state is never exposed to `DecisionFinalizer`;
- completion state is transferred only when the receipt proves an exact requirement mapping;
- chronology alone never creates a transformation.

## 6. Ordered event stream

All lifecycle, execution, proof, decisive, and error events for one result occurrence share one append-only sequence space.

```text
EventStreamEnvelope:
  schema_version
  stream_id
  result_occurrence_id
  source_snapshot_fingerprint
  first_sequence
  last_sequence
  event_count
  authority_chain_digest
  sealed
```

```text
EventHeader:
  schema_version
  stream_id
  result_occurrence_id
  source_snapshot_fingerprint
  sequence_number
  predecessor_authority_digest
  authority_payload_digest
  event_type
```

Only the central result event recorder assigns sequence numbers and predecessor digests. Producers submit typed event intents. The reducer accepts only sealed streams with continuous sequence numbers, a valid hash chain, one stream ID, and one result occurrence ID.

Diagnostic payload such as paths, timestamps, elapsed time, labels, excerpts, and rendered strings is excluded from authority digests.

### Execution events

Execution events are not reasons:

- `SOLVER_UNKNOWN`
- `SOLVER_TIMEOUT`
- `SOLVER_ERROR`
- `PROCESS_TIMEOUT`
- `CANCELLED`
- `NORMALIZATION_NO_CHANGE`
- `REWRITE_NO_CHANGE`

Solver UNKNOWN/TIMEOUT alone cannot create a semantic reason. Each terminal timeout must reference a live proof requirement.

## 7. Lifecycle projection and verified bundle

The reducer emits outcome-independent base relations.

```text
C_active_base:
  result_occurrence_id
  occurrence_id
  cause_id
  reason_id
  domain
  decision_effect
  target_kind
```

```text
Q_open_base:
  result_occurrence_id
  occurrence_id
  cause_id
  proof_requirement_id
  proof_kind
  semantic_target_digest
```

```text
Blocker_eligibility_base:
  result_occurrence_id
  blocker_occurrence_id
  cause_id: optional until typed
```

Typed-cause coverage is derived from this lifecycle-digest-bound relation. It is never accepted as caller-supplied numerator/denominator counts. Active typed causes must have a matching eligibility row keyed by result and occurrence.

Every `Q_open_base` row has a matching `C_active_base` row and references a declared, incomplete requirement in the live frontier. Its `semantic_target_digest` is derived only by the reducer from the bound registry-owned `ProofRequirement.semantic_target_key`; it is never caller supplied. NULL requirements are forbidden.

These relations are lifecycle authority only. They contain no final outcome, legacy outcome, decision-receipt field, or census-derived field. A cause with no materialized requirement remains in `C_active_base` and contributes no placeholder row to `Q_open_base`.

The finalizer receives one verified authority object, not independent raw lists:

```text
VerifiedLifecycleProjection:
  snapshot
  c_active_base
  q_open_base
  blocker_eligibility_base
  c_active_base_digest
  q_open_base_digest
  blocker_eligibility_base_digest
  semantic_cause_projection_digest
  satisfaction_projection_digest
  lifecycle_projection_digest
```

The snapshot binds both relation digests. Relation rows are canonically sorted before hashing, so physical ordering does not affect the digest. A mismatch invalidates the bundle.

Digest purposes:

- event-stream authority digest: exact run order and tamper detection;
- semantic-cause projection digest: cause taxonomy and semantic lifecycle state;
- satisfaction projection digest: occurrence-to-contract binding, completion state, live frontier, and open requirements;
- composite lifecycle projection digest: complete verified lifecycle artifact.

Changing proof alternatives may change the satisfaction and composite digests, but not `cause_id` or the semantic-cause digest.

## 8. Five-value decision authority

```text
DecisionReceipt.outcome:
  EQUIVALENT
  NOT_EQ
  UNKNOWN
  TIMEOUT
  ERROR
```

`DecisionFinalizer` consumes only:

- verified lifecycle projection;
- decisive proof receipts;
- terminal execution events;
- error receipts.

It cannot read legacy outcome fields, primary reason, legacy summary, or outcome census views.

The dependency boundary is enforced in both directions: the reducer cannot read `DecisionReceipt` or any legacy/candidate outcome, and the finalizer cannot read `C_active_by_outcome`, `Q_open_by_outcome`, or any census aggregate.

Decision rules:

- `EQUIVALENT`: valid EQ closure receipt and no active cause that blocks equivalence/decision.
- `NOT_EQ`: safe decisive counterexample receipt and no active cause that blocks disequivalence/decision.
- `TIMEOUT`: exactly one terminal timeout event references a live requirement; no decisive receipt.
- `UNKNOWN`: one or more active semantic causes; no terminal timeout or error authority.
- `ERROR`: valid internal/tool failure receipt, malformed authority, or conflicting terminal authorities.

Unsupported semantics and incomplete proof remain typed UNKNOWN. Internal invariant violations, invalid pairwise ledger state, malformed v2 authority, and unexpected implementation exceptions become ERROR only at the explicit decision cutover.

## 9. Outcome census and UNKNOWN aggregation

### 9.1 Entry-bound census manifest

```text
CensusEntry:
  result_occurrence_id
  result_kind: V2_NATIVE | LEGACY
  comparison_domain_identity
  binary_content_identities
  function_identities
  event_stream_authority_digest
  lifecycle_projection_digest
  decision_receipt_digest
  result_artifact_digest
```

```text
CensusManifest:
  schema_version
  manifest_id
  census_mode
  repository_commit
  analysis_config_digest
  entries
  manifest_authority_digest
  generated_at
```

`generated_at` is excluded from the authority digest. Entry payloads are canonically sorted and individually bind all identities and digests.

Census modes:

- `V2_CANONICAL`: v2-native entries only; produces canonical metrics.
- `LEGACY_DIAGNOSTIC`: legacy entries only; produces inferred diagnostic metrics.
- `MIGRATION_COMPARISON`: binds paired v1/v2 entries for shadow comparison; never treated as a canonical census.

### 9.2 Outcome join

After `DecisionReceipt` exists, the census builds a decision relation with exactly one row per selected result occurrence and joins outcome onto the base relations:

```text
D_receipt = one validated DecisionReceipt row per CensusManifest result_occurrence_id
C_active_by_outcome = C_active_base JOIN D_receipt by result_occurrence_id
Q_open_by_outcome   = Q_open_base   JOIN D_receipt by result_occurrence_id
```

`D_receipt` is materialized only after finalization. Missing, duplicate, orphaned, or digest-mismatched rows invalidate the entire canonical census. Validation compares manifest and receipt key sets before either join; an inner join must never hide row loss. Legacy outcome fallback is forbidden.

### 9.3 Canonical metrics

Separate metrics are required:

- final decision count by five-value outcome;
- active blocker occurrences from `C_active_base`;
- unique active causes from `C_active_base`;
- affected UNKNOWN results by reason from `C_active_by_outcome`;
- affected TIMEOUT results by reason from `C_active_by_outcome`;
- semantic backlog by reason/cause/domain/decision effect/target kind/final outcome;
- unique open requirements from `Q_open_base`;
- proof backlog by proof kind/cause/final outcome from `Q_open_by_outcome`;
- terminal timeout events;
- observed nonterminal timeout events;
- legacy inferred records, separately.

Primary reason is presentation-only and cannot drive acceptance or regression metrics. Reason totals need not equal UNKNOWN result totals because independent blockers can coexist.

### 9.4 Census invariants

- `count(distinct D_receipt.result_occurrence_id) == len(CensusManifest.entries)`;
- every manifest result occurrence has exactly one `DecisionReceipt`, and no receipt exists outside the manifest;
- decision count sum equals manifest entry count;
- UNKNOWN has at least one `C_active_base` row;
- TIMEOUT has at least one `C_active_base` row, one `Q_open_base` row, and exactly one linked terminal timeout event;
- EQUIVALENT has no active cause blocking equivalence/decision;
- NOT_EQ has no active cause blocking disequivalence/decision;
- every `C_active_by_outcome` row has exactly one matching `D_receipt` row;
- every `Q_open_by_outcome` row has exactly one matching `D_receipt` row and at least one matching `C_active_base` row;
- every open requirement references exactly one matching active occurrence and verified lifecycle bundle;
- relation and receipt digests match the manifest entry.

### 9.5 Coverage

- `v2_native_typed_cause_coverage`: rows with a typed `cause_id` / all rows in lifecycle-bound `Blocker_eligibility_base`.
- `final_blocker_authority_coverage`: UNKNOWN/TIMEOUT results with valid active blocker authority / all UNKNOWN/TIMEOUT results.
- `required_requirement_materialization_coverage`: active `REQUIREMENT_REQUIRED` occurrences with one or more open requirements / all active required occurrences. Gate: `1.0`.
- `optional_requirement_materialization_rate`: active `REQUIREMENT_OPTIONAL` occurrences with one or more open requirements / all active optional occurrences. Observation only; no `1.0` gate.
- `NO_PROOF_RECOVERY` is excluded from materialization denominators.
- Zero denominator is represented as `N/A`, never `0.0` or `1.0`.

The census also reports `active_causes_without_materialized_requirement` as three disjoint counts:

- `required_missing`: active `REQUIREMENT_REQUIRED` occurrences with no `Q_open_base` row; this makes the required coverage gate fail;
- `optional_not_materialized`: active `REQUIREMENT_OPTIONAL` occurrences with no `Q_open_base` row; observation only;
- `no_proof_recovery`: active `NO_PROOF_RECOVERY` occurrences; excluded from both materialization denominators.

The three categories are never collapsed into a NULL requirement row. A satisfied occurrence is not counted as active; therefore a required active occurrence with an empty live frontier is an invariant violation, not successful materialization.

Any invalid artifact, stream, projection, receipt, relation, identity, manifest binding, or decision invariant makes the canonical census `INVALID`. Diagnostic partial counts must be marked non-authoritative and cannot be used for baselines or improvement rates.

## 10. Legacy isolation and dual-write

Production v2 constructors are strict:

- unknown reason ID is rejected;
- metadata override is rejected;
- target/evidence contract violation is rejected;
- suffix normalization is unavailable.

Legacy reading is a separate, lossless path retaining raw ID, raw payload, mapping kind, and mapping certainty. Legacy umbrella reasons are never guessed into concrete v2 causes.

During migration:

- v2 typed events are authoritative;
- legacy umbrella output is a non-authoritative compatibility projection;
- legacy projection never enters the reducer, active set, v2 coverage, or v2 reason count;
- migration comparison reports v2 metrics, legacy counts, mapping coverage, mapping ambiguity, and decision delta separately.

## 11. Implementation phases and gates

### Phase 0: current-HEAD producer/consumer audit

Create under `artifacts/unknown_reason_audit/current-head/`:

- `registry.json`
- `producers.json`
- `consumers.json`
- `decision_projection.json`
- `legacy_aliases.json`
- `census_manifest.json`
- `census.json`
- `overlap_candidates.json`
- `migration_manifest.json`

Audit all 37 reasons, typed/dynamic producers, final/primary consumers, fallback/retry consumers, CLI/batch/resume parsers, proof-backlog consumers, legacy use, tests, current-HEAD representative results, and duplicate stable results. Saved 411 summaries remain a legacy baseline, not current truth.

Gate:

- every reason has producer/consumer/legacy status;
- dynamic string producers are enumerated;
- result selection is manifest-bound;
- current-HEAD representative reruns are included;
- no production behavior changes.

### Phase 1: freeze v2 contracts

Implement the schemas and pure contract tests for:

- immutable reason definitions;
- semantic-only cause identities;
- occurrences and event intents;
- ordered hash-chained stream;
- registry-owned satisfaction contracts and typed binding;
- minimal satisfying extension frontier;
- requirement completion receipts;
- atomic N-to-M transformations;
- base relations and foreign keys;
- verified lifecycle bundle and digests;
- decision matrix;
- entry-bound manifest and census modes;
- canonical metric equations;
- coverage and invalid-census policy;
- frontier resource budget.

Gate: all contract, boundary, mutation, negative, and digest tests pass before Phase 3 work begins. Contract tests must prove that adding only a recovery alternative preserves `cause_id`, while changing the semantic proposition, target, semantic precondition, identity scope, or correspondence contract changes it.

### Phase 2: sealed registry, models, and codecs

Implement:

- duplicate-rejecting registry and recovery registry;
- strict v2 writer/reader;
- lossless legacy reader;
- semantic cause identity factory;
- satisfaction binding factory;
- budgeted antichain evaluator;
- event, receipt, projection, relation, and manifest codecs;
- legacy mapping certainty and compatibility projection.

Gate:

- strict production path cannot use suffix normalization;
- legacy round-trip is lossless;
- v2 and legacy coverage are separate;
- no existing final decision changes.

### Phase 3: outcome-independent shadow reducer

Implement sealed-stream replay and atomically produce:

- `CauseLifecycleSnapshot`
- `C_active_base`
- `Q_open_base`
- `Blocker_eligibility_base`
- `VerifiedLifecycleProjection`
- semantic, satisfaction, relation, and composite digests.

The reducer must not emit or consume outcome, UNKNOWN/TIMEOUT counts, or census outcome views.

Gate tests include:

- sequence duplication/gap/hash mismatch/mixed stream/seal-after-append;
- shuffled physical input with stable sequence;
- no implicit supersession;
- N-to-M transformation atomicity;
- partial completion and `(A OR B) AND C` frontier;
- cause with no materialized requirement;
- one occurrence with multiple requirements but one cause row;
- relation foreign keys;
- relation/snapshot tamper rejection;
- frontier budget fail-closed;
- reducer import/access rejection for `DecisionReceipt`, legacy outcome, candidate outcome, and census views;
- no outcome field in either base relation;
- required-missing, optional-not-materialized, and no-proof-recovery classification without NULL `Q_open_base` rows.

### Phase 4: independent shadow decision and census join

Build two independent projections:

- `LegacyExpectedProjection` from current legacy fields;
- `CandidateDecisionReceipt` only from verified v2 authority.

Candidate code cannot access legacy outcome. Compare:

- outcome;
- decisive authority and proof receipt;
- active cause set;
- terminal execution event;
- retry/fallback projection;
- CLI/batch projection.

Only after `CandidateDecisionReceipt` is sealed does the shadow census build `D_receipt`, validate the one-to-one manifest key set, and create `C_active_by_outcome` and `Q_open_by_outcome`. The finalizer cannot import or consume these joined views.

Classify every comparison as:

- `MATCH`
- `SHADOW_EVIDENCE_INCOMPLETE`
- `MISMATCH_DECISION_AUTHORITY`
- `MISMATCH_LIFECYCLE`
- `MISMATCH_EXECUTION_EVENT`
- `MISMATCH_FALLBACK_POLICY`
- `MISMATCH_LEGACY_AMBIGUITY`

After candidate receipt validation, build outcome views and canonical metric previews. Never count evidence-incomplete cases as matches.

Gate:

- EQ/NOT_EQ decisive authority matches;
- proof receipt digests match;
- UNKNOWN/TIMEOUT/ERROR differences are fully explained;
- authority conflicts never silently become UNKNOWN;
- outcome join cardinality and manifest binding hold;
- missing, duplicate, orphaned, or digest-mismatched decision rows invalidate the shadow census instead of silently shrinking a join;
- semantic before/after comparison uses `cause_id`, while proof-backlog comparison uses satisfaction-contract version plus requirement ID.

### Phase 5: narrow dual-write pilot

Pilot only return/outcome totality requirements plus solver execution events and alternative proof paths.

Required cases:

1. totality query timeout -> final TIMEOUT;
2. solver UNKNOWN -> final UNKNOWN;
3. nonterminal timeout -> fallback UNSAT -> final EQUIVALENT;
4. nonterminal timeout -> another terminal blocker -> final UNKNOWN;
5. residual SAT -> coverage blocker;
6. process timeout with a checkpointed live requirement;
7. `(A OR B) AND C` completion combinations;
8. one-to-two refinement and two-to-one coalescence;
9. one cause with multiple requirements without duplicate cause counting;
10. active semantic cause without a materialized optional requirement;
11. TIMEOUT with no open requirement -> canonical rejection;
12. independent event arrival order with equal semantic projection;
13. invalid manifest entry -> entire canonical census INVALID.

Gate:

- v1 final outcome remains unchanged during pilot;
- attempted requirement identity coverage is `1.0` for solver events;
- lifecycle inference is zero for v2;
- timeout never creates a reason by itself;
- repo-local v1/v2 difference manifest exists.

### Phase 6: domain-by-domain migration

Order:

1. SAT safety and counterexample authority;
2. return coverage and outcome partition;
3. expression, call, effect, memory alias/order;
4. loop, recurrence, and summary;
5. ABI, return width, readonly identity;
6. operational extraction and decompilation.

#### Phase 6 slice 2 contract: return coverage and unary outcome partition

Slice 2 must not infer lifecycle completion from a producer status or from reaching a later stage. The only permitted unary stage lifecycle is:

```text
stage producer returns non-proved
  -> emit one typed OBSERVED cause for that exact stage requirement
  -> stop the stage pipeline and keep C_active/Q_open live

stage producer returns proved
  -> construct and validate the versioned ProofArtifact
  -> bind artifact ID/digest, premise digest, function snapshot,
     outcome-seed digest/revision, exact stage requirement,
     producer version, and encoding version
  -> conditionally exact-COMPLETED an already observed occurrence for that stage
  -> only then execute the next stage
```

A later stage status is never completion authority for an earlier stage. Normal stage progression does not use cause transformation. Slice 2 uses explicit `COMPLETED` followed by an independent `OBSERVED` if the next stage fails. Transformation is reserved for a future same-stage semantic reclassification with its own proof receipt.

The stage/status-to-reason matrix is sealed and reject-by-default. These are the complete reachable producer pairs; anything else invalidates shadow evidence without changing v1:

| Stage | Accepted statuses | Exact typed reason ID projection |
|---|---|---|
| `termination_classification` | `proved`, `unclassified` | none; `outcome_termination_classification_unproven` |
| `cfg_reachability` | `proved`, `incomplete` | none; `outcome_cfg_reachability_unproven` |
| `path_region_completeness` | `proved`, `incomplete` | none; `outcome_path_region_completeness_unproven` |
| `member_classification` | `proved`, `unclassified` | none; `outcome_member_classification_unproven` |
| `same_kind_consistency` | `proved`, `comparison_surface_missing`, `unknown`, `timeout`, `conflict` | none; `outcome_same_kind_comparison_surface_missing`; `outcome_same_kind_consistency_unproven`; the same unproven reason plus timeout event; `outcome_return_value_conflict_witnessed` |
| `cross_kind_disjointness` | `proved`, `unknown`, `timeout`, `overlap` | none; `outcome_cross_kind_disjointness_unproven`; the same unproven reason plus timeout event; `outcome_cross_kind_overlap_witnessed` |
| `residual_totality` | `proved`, `incomplete`, `unknown`, `timeout`, `residual_sat` | none; `outcome_partition_guard_union_incomplete`; `outcome_partition_totality_unproven`; the same unproven reason plus timeout event; `outcome_partition_residual_sat_witnessed` |
| `partition_complete` | `proved`, `unclassified` | none; `outcome_partition_completion_unproven` |

Legacy `outcome_partition_unknown` projects to the applicable typed semantic cause. Legacy `outcome_partition_totality_timeout` projects to `outcome_partition_totality_unproven`; timeout is never encoded in the reason identity. Pair-derived failure after both unary partitions have been proved belongs to a separate relational registry and relational CauseId, not the unary registry.

Solver execution authority is captured at the actual invocation, before status is reduced to a legacy string. Its immutable receipt binds the exact stage `ProofRequirementId`, query digest, solver identity, invocation identity/ordinal, configured budget, elapsed or start/end timing, and observed status. The receipt is held in a stage-local buffer until a non-proved result has produced its exact live cause; it is then appended exactly once, immediately after `CAUSE_OBSERVED`. Event-stream sequence is dependency-safe receipt-materialization order, while invocation identity/ordinal and receipt timing are execution-order authority. This prevents an execution event from preceding its uniquely live requirement. The current event vocabulary materializes only `UNKNOWN`, `TIMEOUT`, and `ERROR`; proved UNSAT/SAT authority belongs to validated proof/counterexample artifacts rather than a synthesized execution event. A timeout remains a nonterminal observation unless the finalizer exactly selects that live-frontier event as terminal. Recovery may complete the semantic requirement while retaining the historical nonterminal timeout receipt.

`conflict`, `overlap`, and `residual_sat` are witnessed causes and require stronger authority than a producer status. At the solver invocation, the implementation captures the SAT query, model/witness, and immutable invocation receipt before legacy status reduction. It then constructs and validates a typed unary outcome witness artifact binding:

- exact stage requirement;
- runtime premise digest and function snapshot;
- outcome-seed digest and revision;
- query digest and model/witness digest;
- solver invocation receipt digest;
- the exact witnessed proposition (return conflict, cross-kind overlap, or residual region satisfiable);
- producer and encoding versions.

Only after that artifact validates may its digest be bound into evidence for the corresponding witnessed cause and `CAUSE_OBSERVED` be appended. A missing, mismatched, or model-free SAT artifact prohibits a witnessed cause; shadow evidence becomes INVALID or conservatively uses the applicable unproven cause while v1 remains unchanged. This unary witness artifact is blocker evidence, not a pairwise disequivalence proof, and must never emit the final-decision `COUNTEREXAMPLE` event. It is separate from buffered `UNKNOWN`/`TIMEOUT`/`ERROR` execution events.

Return coverage uses registry-owned contracts matching the existing proof obligations:

- gap: `ALL_OF(return_partition_extraction, return_guard_coverage)` using requirement IDs that join exactly to the existing `ProofRequirementId` authorities;
- inconclusive: `return_coverage_smt_disambiguation` using its existing exact requirement identity.

`Q_open` is generated only from the live frontier of those bound expressions. Cause identity binds function content identity, function snapshot, outcome-seed digest/revision, stage or proof target, and the missing semantic fact. Pair-side labels, final outcome, raw status text, and result-session identity are excluded; the result session is occurrence authority only.

Exceptional paths are explicit:

- cache hit emits no completion unless a validated dependency-closure receipt proves the cached final artifact covers the exact observed stage requirement in the current session;
- an occurrence from another session is never completed;
- missing outcome seed is a distinct typed semantic-input cause with identity `(function content identity, function snapshot, ("outcome_seed_present", false), missing semantic fact)` and does not fabricate a seed digest;
- missing stage producer is a distinct proof-production/configuration cause whose identity binds the available seed digest/revision, exact stage, and sealed producer-contract identity, and is not a fabricated solver UNKNOWN;
- unknown stage/status combinations fail shadow encoding and leave v1 unchanged.

Slice 2 gates include successful and failing real producer paths, retry completion with exact artifact binding, failed/near-miss completion, solver timeout followed by recovery, exactly-once buffered execution materialization, gap multi-requirement frontier behavior, unary/relational non-merging, same-cause dedup, independent-cause non-merging, cache/seed/producer-missing paths, current-source inventory delta, representative current-HEAD runs, and unchanged legacy decisions. Because slice 2 prohibits normal stage transformation, its transformation gate is a non-use negative test: no stage progression may emit `CAUSE_TRANSFORMED`.

#### Phase 6 slice 3 contract: expression, call, effect, and memory relation

Slice 3 replaces `unresolved_expression` and call/effect uses of `equivalence_blocking_unsafety`. Existing manifest failure strings, `_primary_proof_stage` values, and preflight veto strings are discovery inputs and evidence details only. The encoder first classifies each input by the following sealed, ordered matrix. Exactly one row must match; zero or multiple matches make the shadow entry INVALID. No residual or generic v2 reason is permitted.

| Exact reason ID | Allowed scope and canonical target | Mutually exclusive producer predicate / current failure-source mapping | Registry-owned satisfaction contract and recovery addressability |
|---|---|---|---|
| `expression_semantics_unsupported` | UNARY expression object | recognized expression opcode/semantic class is outside the sealed translator; never an exception | `NO_PROOF_RECOVERY`; C_active only until a future versioned translator contract exists |
| `expression_translation_incomplete` | UNARY supported expression object | supported class, but object-derived operand/type/value translation is incomplete; legacy `unresolved_expression` only after this predicate is proved | `expression_translation` |
| `callsite_identity_extraction_missing` | UNARY function/call site | `pcode_op_identity_missing`, `*_pcode_op_identity_missing` | `callsite_object_identity` |
| `unsupported_call_operation` | UNARY function/call site | `call_operation_kind_unsupported`; distinct from a supported call whose target is unresolved | `NO_PROOF_RECOVERY` |
| `call_target_resolution_unproven` | UNARY function/call site | `call_target_ambiguous`, `call_target_evidence_missing`, `*_call_target*`, `*_target_relation_input_incomplete` | `call_target_resolution` |
| `call_argument_extraction_incomplete` | UNARY function/call site | `argument_evidence_missing`, `argument_coverage_incomplete`, `argument_group_missing`, `argument_groups_ambiguous`, `*_argument_evidence_incomplete` | `call_argument_extraction` |
| `call_invocation_multiplicity_unproven` | UNARY function/call site | `*_call_invocation_multiplicity_unproven` | `call_invocation_multiplicity` |
| `call_output_reaching_definition_unproven` | UNARY function/call output use | `*_call_output_reaching_definition_unproven` | `call_output_reaching_definition` |
| `recursive_call_scc_unproven` | UNARY callee SCC | `recursive_call_scc_unproven`, `*_recursive_callee_summary_unproven` | `recursive_call_scc_summary` |
| `callee_dependency_closure_missing` | UNARY callee/call site | `call_dependency_closure_missing`, `*_callee_dependency_closure_missing`, incomplete nested-call closure | `callee_dependency_closure` |
| `callee_effect_summary_incomplete` | UNARY callee/call site | supported call with incomplete effect summary, control profile, nested-call summary, or total/trap-free scalar-effect evidence | `ALL_OF(callee_control_effect_profile, callee_effect_summary, callee_nested_call_closure)` |
| `callee_return_summary_incomplete` | UNARY callee/call site | missing/incomplete callee return summary, return shape, or return partition | `callee_return_partition` |
| `inline_region_boundary_incomplete` | UNARY inline region | missing single-entry, exit census, or cross-edge census | `ALL_OF(inline_region_single_entry, inline_region_exit_coverage, inline_region_cross_edge_coverage)` |
| `inline_region_semantics_incomplete` | UNARY inline region | missing guard partition, state transformer, return partition, or total/trap/control profile | `ALL_OF(inline_region_guard_partition, inline_region_state_transformer, inline_region_return_partition, inline_region_control_profile)` |
| `effect_observation_coverage_incomplete` | UNARY function effect census | side-local p-code census incomplete or a side-local call/effect fact is missing; one function is named by object identity, not a side label | `effect_observation_coverage` |
| `unsupported_call_effect_semantics` | UNARY call/effect object | supported call operation has an unsupported effect category or unsupported nested effect semantic | `NO_PROOF_RECOVERY` |
| `callsite_correspondence_unproven` | RELATIONAL call/call or call/region obligation | `phase2_requires_paired_call_sites`, incomplete structural correspondence after both unary facts exist | `callsite_correspondence` |
| `effect_endpoint_correspondence_unproven` | RELATIONAL effect coupling | duplicate/uncovered relational endpoints or endpoint coverage mismatch after both unary censuses validate | `effect_endpoint_correspondence` |
| `call_to_region_input_relation_unproven` | RELATIONAL call/region obligation | `call_to_region_input_relation_missing` | `call_to_region_input_relation` |
| `abi_argument_relation_unproven` | RELATIONAL call obligation | parameter alignment, argument arity, or ABI relation missing after unary argument extraction completed | `abi_argument_relation` |
| `pure_call_semantics_unproven` | RELATIONAL call/call or call/region obligation only | eligible obligation lacks a non-effect relational proof; owns only `guard_relation`, `argument_relation`, and `return_relation`; never owns unary callee extraction or any effect/memory requirement | `ALL_OF(ANY_OF(inline_region_semantic_proof, callee_summary_semantic_proof), call_guard_relation, call_argument_relation, call_return_relation)` |
| `call_effect_correspondence_unproven` | RELATIONAL non-memory effect coupling | non-memory observed effects have complete unary censuses/endpoints but semantic effect correspondence is unproved | `call_effect_correspondence` |
| `external_call_coupling_unproven` | RELATIONAL external-call obligation | both unary targets are resolved external calls but nondeterminism/effect coupling is not proved | `external_call_semantic_coupling` |
| `memory_object_identity_unproven` | RELATIONAL memory coupling | observed locations lack a bijective observation-contract-scoped object relation | `memory_object_identity` |
| `memory_alias_relation_unproven` | RELATIONAL memory coupling | object identities exist but alias partitions/overlap relation are incomplete | `memory_alias_relation` |
| `memory_effect_order_extraction_incomplete` | UNARY function memory-effect set | one function lacks a complete object-derived store partial-order/call-order census | `memory_effect_order_extraction` |
| `memory_effect_order_unproven` | RELATIONAL memory coupling | both unary order censuses validate but cross-side order correspondence is unproved | `memory_effect_order_correspondence` |
| `memory_final_state_correspondence_unproven` | RELATIONAL memory coupling | object, alias, and order prerequisites exist but `memory_relation` or `caller_memory_relation` UNSAT proof is missing | `memory_final_state_correspondence` |
| `call_projection_partition_unproven` | RELATIONAL prepared projection | semantic call pairs are empty/filtered but paired outcome/termination coverage proving no active pair is absent | `call_projection_partition` |

The mapping implementation owns a complete table of exact current strings and predicates, not substring fallbacks. The families shown above describe that table; an inventory artifact lists every concrete current value from extraction failures, eligibility blockers, `_primary_proof_stage`, structural coverage, producer failures, and preflight semantic-safety failures with exactly one destination row. In particular, `relational_call_effect_input_incomplete`, `call_effect_preflight_incomplete`, and other catch-all strings are prohibited as canonical v2 inputs; their appearance means the mapping inventory or producer contract is incomplete and therefore INVALID.

`expression_semantics_unsupported` and `unsupported_call_operation/effect_semantics` are active semantic causes without an invented work item. All other rows have the exact contract shown. CauseId includes the declared scope, semantic object identity, source snapshot(s), extraction/observation contract, exact missing proposition, and relational obligation identity where applicable. Raw expression text, `repr`, binary-side labels, result identity, final outcome, manifest readiness, and status text are excluded.

Unary and relational ownership is exclusive. A unary cause is produced before relational obligation construction and cannot contain left/right correspondence. A relational cause requires validated unary object identities and an observation-contract-bound obligation. `pure_call_semantics_unproven` owns the `ANY_OF` contract only at relational scope: `inline_region_semantic_proof` and `callee_summary_semantic_proof` are alternative relational proofs over the same left/right obligation, not unary callee-summary extraction artifacts. The live frontier removes the unused arm after either arm completes.

Requirement ownership follows option A: `pure_call_semantics_unproven` owns only non-effect guard/argument/return requirements. `call_effect_correspondence_unproven` alone owns the non-memory effect requirement. Memory leaf causes alone own object, alias, unary-order-extraction, cross-side-order, and final-state requirements. A producer predicate first separates unary census, relational endpoint, non-effect call semantics, non-memory effect semantics, and memory semantics; it cannot emit two causes for the same missing proposition or bind the same requirement ID into two active occurrences. Multiple memory causes may coexist only when they have distinct missing propositions and distinct requirement IDs.

Slice 3 prohibits provisional parent causes and emits exact leaf causes initially. It emits no `CAUSE_TRANSFORMED` event. This restriction remains until a separate factory-issued semantic-refinement certificate binds old/new semantic proposition digests, recognizing object artifact, source snapshots, schema and producer versions, and a total old-to-new requirement mapping; the current generic transformation receipt is insufficient authority.

Requirement-to-execution assignment is one-to-many safe. A lookup key such as `(obligation_id, stage)` must never select an arbitrary single `Q_open_base` row. Before slice 3 production cutover, the execution context must either (a) bind one solver execution to an explicit tuple of compatible live assignments and prove that the artifact discharges each one independently, or (b) reject the ambiguous assignment and leave every affected requirement open. Silent first/last-row selection is forbidden. The gate includes two live requirements sharing an obligation/stage, exact independent completion, ambiguous refusal, and stable backlog counts.

Existing object-derived authorities are reused, but only according to this allowlist:

| Artifact/receipt | May observe | May complete |
|---|---|---|
| raw source `AnalysisSnapshot`, `ArtifactObjectIdentity`, call/region facts | none directly; raw objects remain discovery inputs until an issuer-owned snapshot/manifest membership wrapper exists | none |
| structural coverage certificate and use-domain coverage mapping | matching unary coverage or relational correspondence cause | none by themselves |
| prepared-surface certificate and projection binding | matching relational cause only | none by themselves |
| verified V2 `InternalSolverProofArtifact` with pinned execution receipt, typed query authority, and live-Q_open assignment | matching relational proof attempt | only its exact declared relational requirement and dependencies; legacy/caller-runner artifacts have no V2 completion capability |
| `ModelBoundRelationalRefutationArtifact` | matching witnessed refutation and Phase 6.1 counterexample handoff | none of the UNKNOWN requirements; may authorize decisive handoff only after applicability/safety validation |
| comparison execution receipt | execution/use evidence for its exact prepared projection | none unless it embeds separately verified proof artifacts; the receipt status alone is insufficient |
| decision lease | run ownership validation only | none |
| cleanup/quiescence receipt | infrastructure validation only | none |
| future no-active-pair certificate | matching prepared projection partition | only `call_projection_partition` after paired return/divergence/termination validation |

Completion requires an allowlisted, factory-issued artifact to validate the exact requirement, source snapshots, semantic object/obligation IDs, observation contract, prepared surface when relevant, stage input and precondition, producer/encoding versions, dependency proof IDs, and solver query/result. `status == proven`, manifest `ready`, absence of a legacy blocker, a lease, cleanup, or a comparison receipt alone never completes a cause.

Production execution receipts are signed only by a deployment-provisioned issuer key. The operational contract must name the key source and owner, active-key selection, minimum key strength, rotation procedure, retained verification-key window, old-receipt verification behavior, startup health check, and revocation response. A missing/default/unknown active key fails production pilot startup closed; it cannot fall back to an ephemeral process key. Rotation tests must verify that newly issued receipts use the new key while receipts issued under retained keys remain verifiable for the declared retention window.

SAT authority is not reused from `InternalSolverProofArtifact.record.status == refuted`. Slice 3 adds a factory-issued `ModelBoundRelationalRefutationArtifact` binding the exact requirement/obligation, source and prepared snapshots, observation contract, query and normalized assertion, premise/stage input/applicability, solver identity/version, budget/timing, raw output digest, SAT model/witness digest, replay result, producer/encoding versions, and dependency proof IDs. The factory receives the raw solver result at invocation time and independently replays the witnessed violation. Missing or mismatched model/output/applicability makes shadow evidence INVALID. A validated refutation does not complete an UNKNOWN requirement; it is passed to the Phase 6.1 counterexample-safety authority, which alone may emit a decisive event.

Common execution authority is moved out of the return/outcome stage matrix into a sealed domain registry keyed by `(domain_contract_id, producer_contract_id, producer_version, proof_stage)`. Production execution accepts only a typed-renderer query authority and an issuer-owned solver configuration; caller-supplied runners are legacy-only and cannot complete V2 requirements. Query authority binds stage, obligation, observation contract, fact identities, stage input, precondition, and execution identity. Its assignment receipt additionally binds result occurrence and the exact proof requirement.

Q_open rows bind `semantic_target_digest` derived by the reducer from the bound satisfaction contract's `ProofRequirement.semantic_target_key`; caller-supplied requirements are not assignment inputs. A live-requirement assignment must join that digest, the current Q_open/C_active occurrence and cause, reason owner, obligation, observation contract, stage, and proof kind. A producer call has one attempt-group identity and synchronized ordinal. Solver receipts bind the group, exact requirement, invocation identity/ordinal, execution identity, query authority, budget/timing, status, and signing-key ID. Production requires a deployment-provisioned signing key; retained key IDs remain verifiable across rotation.

The pinned issuer owns one append-only execution ledger per `(registry version, registry digest, result occurrence)`. All solver results and fixed-model replays append there; replay-in-progress prevents sealing. The sealed full census, not a caller candidate subset or sequence integer, derives the latest event per requirement/stage. A registry-owned `TerminalTimeoutSelectionReceipt` selects exactly one eligible timeout across the final live frontier using registry priority, requirement digest, and event order, and binds the full event-stream digest. Later proved/UNKNOWN/ERROR/receiptless attempts supersede only the same requirement/producer contract.

Semantic and infrastructure failures are disjoint. Structural coverage gaps, unsupported semantics, memory relation gaps, and absence of a semantic no-active-pair proof use the matrix above. Source/prepared/projection identity mismatch, invalid projection consumption, decision-lease conflict, comparison-receipt mismatch, cleanup/quiescence failure, untrusted artifact token, digest mismatch, unknown failure string, or exception makes the pilot entry INVALID and becomes ERROR at Phase 8. Those conditions never create C_active/Q_open rows.

Slice 3 gates include:

- every production site in the current-source inventory classified as exact typed production, legacy-only projection, or diagnostic-only consumer;
- exact boundary tests for every reason ID and near-miss non-merging across function, call site, unary/relational scope, observation contract, alias class, and order relation;
- pairwise-disjoint producer-predicate tests over every current failure input;
- `(result_occurrence_id, proof_requirement_id) -> exactly one active occurrence owner` for all Q_open rows;
- `ANY_OF` frontier tests for inline versus callee-summary proof;
- explicit allowlisted completion and a negative assertion that slice 3 emits no transformation;
- actual solver invocation receipts for UNKNOWN, TIMEOUT, ERROR, SAT refutation, and UNSAT completion;
- cross-obligation/stage/requirement assignment negatives and Q_open semantic-target conservation;
- deployment-key readiness/rotation and issuer-owned ledger/replay-before-seal tests;
- timeout followed by proved, UNKNOWN, ERROR, timeout, and receiptless retry, with receipt array order permutations;
- source/prepared/projection/lease/comparison/cleanup identity mismatch tests asserting INVALID and zero semantic causes;
- default-off and shadow-failure tests proving the v1 decision and production objects are unchanged;
- representative current-HEAD call/effect and memory-order pairs plus a related matrix;
- a repo-local inventory delta, authority manifest, reason/cause/proof-backlog before-after artifact, and fixed-reviewer GO.

Inventory conservation laws are:

```text
current failure strings
  == typed semantic cause inputs
   ⊎ infrastructure INVALID/ERROR inputs
   ⊎ diagnostic-only inputs

unclassified current failure strings == 0
multiply classified current failure strings == 0
canonical semantic rows sourced from infrastructure failures == 0
```

#### Phase 6 slice 4 contract: loop, recurrence, and summary

Slice 4 replaces production uses of `loop_summary_proof_missing`, strategy-derived
`method_b_closure_blocked`, `phi_circular_replacement_unproven`, and the five
`summary_*` umbrella families. A proof strategy name is never a semantic cause.
In particular, Method B is an attempted producer and may appear in evidence, but
not in ReasonId, CauseId, or proof-requirement identity.

The ordered source-to-reason matrix is sealed and exact. Prefix-only or substring
classification is prohibited. Every current source code has one disposition:

| Exact typed reason ID | Scope and target | Exact current source codes | Registry-owned satisfaction contract |
|---|---|---|---|
| `recurrence_proposal_validation_unproven` | UNARY selected recurrence proposal bound to one function snapshot | checker-created quarantined proposal with exact seed/proposal/binding identities | `recurrence_transition_termination_validation` |
| `loop_exact_summary_relation_unproven` | RELATIONAL exact-return/summary-return pair | `counted_loop_summary_expression_proof_missing` | `ALL_OF(loop_exact_term_relation, loop_exact_guard_partition)` |
| `loop_summary_guard_correspondence_unproven` | RELATIONAL loop-summary pair | `loop_summary_guard_mismatch` | `loop_summary_guard_correspondence` |
| `loop_summary_structure_correspondence_unproven` | RELATIONAL loop-summary pair | `loop_summary_shape_mismatch`, `loop_summary_intrinsic_mismatch`, `loop_summary_operand_mismatch`, `exact_key_unavailable`, `exact_key_mismatch` | `loop_summary_structure_correspondence` |
| `loop_summary_semantic_equality_unproven` | RELATIONAL loop-summary pair | `loop_summary_unproven`, `loop_summary_unknown` | `loop_summary_semantic_equality` |
| `summary_return_extraction_incomplete` | UNARY function summary-return extraction | `summary_return_candidate_invalid:no_proposed_returns`, `:no_new_summary_returns`, `:no_valid_candidates` | `summary_return_extraction` |
| `summary_return_value_extraction_incomplete` | UNARY exact summary candidate | `summary_return_candidate_invalid:value_missing` | `summary_return_value_extraction` |
| `summary_recurrence_transition_validation_incomplete` | UNARY exact summary candidate and recurrence transition | `summary_return_candidate_invalid:transition_evidence_missing`, `:transition_evidence_incomplete` | `summary_recurrence_transition_validation` |
| `summary_return_precondition_incomplete` | UNARY exact summary candidate | `summary_precondition_incomplete:summary_applicability_guard_missing` | `summary_return_active_precondition` |
| `summary_effect_model_incomplete` | UNARY exact summary effect surface | `summary_effect_unmodeled:side_effect_provenance_incomplete`, `:effect_region_incomplete`, `:memory_read_unmodeled`, `:memory_write_effects_present` | `summary_effect_model` |
| `phi_cycle_lowering_unproven` | UNARY PHI SCC and replacement target | `phi_circular_replacement_unproven:replacement_obligation_missing` | `phi_cycle_structural_lowering` |
| `summary_return_overlap_feasibility_unproven` | UNARY same-function candidate/exact-return pair | `summary_return_overlap_unproven:overlap_feasibility_unknown` | `summary_return_overlap_feasibility` |
| `summary_return_overlap_input_incomplete` | UNARY same-function candidate/exact-return pair | `summary_return_overlap_unproven:value_comparison_unavailable` | `summary_return_overlap_value_inputs` |
| `summary_return_overlap_value_equality_unproven` | UNARY same-function candidate/exact-return pair | `summary_return_overlap_unproven:value_equality_not_proved` | `summary_return_overlap_value_equality` |
| `summary_return_memory_observation_mismatch` | UNARY same-function candidate/exact-return pair and observation surface | `summary_return_overlap_unproven:memory_read_model_mismatch` | `summary_return_memory_observation_relation` |
| `summary_return_partition_totality_unproven` | UNARY function partition plus residual region | `summary_partition_not_total:active_precondition_not_covered` and the legacy `return_coverage_gap:` spelling of that exact code | `summary_return_partition_totality` |

`summary_return_candidate_invalid:unstable_guard_key`, `:unstable_value_key`,
`:opaque_guard_key`, `:opaque_value_key`, `:loop_summary_identity_missing`,
`:unstable_loop_summary_identity`, and `:unstable_transition_evidence` cannot form
a canonical semantic target. They make the shadow entry INVALID and produce zero
`C_active`/`Q_open` rows. `summary_return_candidate_invalid:return_width_missing`
and `summary_return_overlap_unproven:return_width_mismatch` remain explicit
legacy-only/deferred-slice inputs until slice 5 owns their ABI/width identity; they
must not be projected into a slice 4 cause. Unknown source codes, malformed effect
tuples, `missing_runtime_ref`, `not_loop_contract`, `no_shortcut`, and exception
text are INVALID, not generic loop causes.

Cause identity is object-derived and excludes side labels, strategy names, raw
expression text, result occurrence, status, and final outcome. Unary identities
bind binary content, one function snapshot, exact proposal/candidate/SCC/effect
surface or same-function candidate/exact-return pair, active-precondition and
observation-surface digests, and the missing proposition. The four summary-return
overlap causes are UNARY because both returns belong to one `FunctionReturnAnalysis`;
they never invent a second source snapshot or a cross-binary correspondence.
Relational identities are reserved for loop comparisons performed across the two
binary functions and bind both source snapshots, ordered observation contract,
exact cross-function candidate/summary pair, and missing correspondence
proposition. A result occurrence is lifecycle authority only.

The existing `ValidatedUnaryArtifact` recurrence payload is reusable only through
a new factory-issued `RecurrenceValidationCompletionAuthority`. The factory must
revalidate the exact `RecurrenceSeedCore`, selected
`QuarantinedRecurrenceProposal`, function-recurrence binding digest,
`recurrence_proof_requirement`, semantic closure digest, producer/encoding
versions, and current live Q row. The legacy promotion receipt, cache hit, proposal
selection, or `status == complete` alone has no v2 completion capability.

The legacy-to-v2 join is explicit. The v2 proposal-validation requirement's
semantic target binds the original function snapshot, proposal digest, seed-core
digest, and expected successor-derivation contract version. After the successor
has been prepared, only a factory-issued `RecurrenceRequirementBindingReceipt`
may join that v2 requirement to the exact legacy
`recurrence_proof_requirement(...).to_key()`. The receipt additionally binds the
original source snapshot, the derived successor `analysis_view_identity` and
partition revision, accepted-candidate digest, function-recurrence binding digest,
and semantic-closure digest. `RecurrenceValidationCompletionAuthority` requires
that receipt and exact live-Q membership. The event stream retains the original
comparison source snapshot; a promoted view never becomes event-stream source
authority. Any later relational loop cause binds the original left/right snapshots
and includes the promoted view lineage only in its canonical semantic target.

Method-B covering-case, guard-partition, aggregate-partition, and dual-summary
solver records are discovery evidence only until exact v2 authorities bind the
live requirements above. Two distinct factory-issued completion types are
required:

- `LoopExactTermRelationCompletionAuthority` binds schema version, result and
  cause occurrence, exact live `loop_exact_term_relation` Q row and semantic-target
  digest, original left/right source snapshots, observation contract, ordered
  exact-return/summary-candidate identities, active-precondition digest, normalized
  term-relation proposition, either an object-derived structural proof body or a
  typed query authority plus validated UNSAT receipt, dependency proof IDs,
  producer contract/version, encoding version, and artifact digest.
- `LoopExactGuardPartitionCompletionAuthority` binds the analogous exact live
  `loop_exact_guard_partition` Q row, case-pair/target/snapshot/observation joins,
  normalized guard-partition proposition and coverage body, and depends on the
  exact term-relation completion authority for the same cause occurrence. It may
  be issued only from an object-derived implication/coverage proof or a typed
  guard-miss query with validated UNSAT authority.

The factories reconstruct the case-pair target from immutable return/candidate
objects, reject caller-supplied target strings, revalidate live `C_active/Q_open`,
and issue exact `RequirementCompletionReceipt`s. The registry-owned `ALL_OF`
requires both distinct completions. Aggregate-partition receipts never complete a
pair-local requirement.

Slice 4 uses one immutable registry definition
`LOOP_PRODUCER_STAGE_REGISTRY_V1`. All rows have domain
`loop-recurrence-summary-v2`; the table columns are part of its digest. `S` means
`STRUCTURAL_ONLY`, `S|U` means structural proof or validated solver UNSAT, and `U`
means validated solver UNSAT only.

| Producer contract ID | Version | Proof stage | Proof kind | Capability | Execution issuer | Allowed / terminal-eligible membership status | Terminal priority |
|---|---:|---|---|---|---|---|---:|
| `typed-recurrence-transition-validator-v2` | `2` | `recurrence_transition_termination_validation` | `recurrence_transition_termination_validation` | S | `loop-structural-proof-factory-v1` | `structural_proof` / none | 10 |
| `loop-exact-term-relation-validator-v2` | `2` | `loop_exact_term_relation` | `loop_exact_term_relation` | S\|U | `parallel-solver-runner-v1` | `attempted` / `attempted` | 20 |
| `loop-exact-guard-partition-validator-v2` | `2` | `loop_exact_guard_partition` | `loop_exact_guard_partition` | S\|U | `parallel-solver-runner-v1` | `attempted` / `attempted` | 30 |
| `loop-summary-guard-correspondence-solver-v2` | `2` | `loop_summary_guard_correspondence` | `loop_summary_guard_correspondence` | U | `parallel-solver-runner-v1` | `attempted` / `attempted` | 40 |
| `loop-summary-structure-correspondence-validator-v2` | `2` | `loop_summary_structure_correspondence` | `loop_summary_structure_correspondence` | S\|U | `parallel-solver-runner-v1` | `attempted` / `attempted` | 50 |
| `loop-summary-semantic-equality-solver-v2` | `2` | `loop_summary_semantic_equality` | `loop_summary_semantic_equality` | U | `parallel-solver-runner-v1` | `attempted` / `attempted` | 60 |
| `summary-return-overlap-feasibility-solver-v2` | `2` | `summary_return_overlap_feasibility` | `summary_return_overlap_feasibility` | U | `parallel-solver-runner-v1` | `attempted` / `attempted` | 70 |
| `summary-return-overlap-value-equality-solver-v2` | `2` | `summary_return_overlap_value_equality` | `summary_return_overlap_value_equality` | U | `parallel-solver-runner-v1` | `attempted` / `attempted` | 80 |
| `summary-return-partition-totality-solver-v2` | `2` | `summary_return_partition_totality` | `summary_return_partition_totality` | U | `parallel-solver-runner-v1` | `attempted` / `attempted` | 90 |

The normalized registry digest, including registry ID/version and every displayed
column, is
`59e3fbedc98851c45400a9618c7814f09c2e372d4f9d912e47a4e52921d84654`.
The common `ProducerStageRegistry` projection has digest
`aed45d8bb14646686eefcace9ba0f59856ea48a2b7305d067e875916683c8eb3`.
The full-row digest is reproducible only from this canonical authority payload;
no table-display spelling is hashed:

```text
authority_digest({
  "registry_id": "loop-recurrence-summary-v2",
  "registry_version": 1,
  "rows": tuple(
    (
      producer_contract_id,
      producer_version,
      proof_stage,
      proof_kind,
      capability,                  # exact expanded string below
      execution_issuer_id,
      tuple(sorted(allowed_statuses)),
      tuple(sorted(terminal_eligible_statuses)),
      terminal_priority,
    )
    for row in rows sorted by terminal_priority ascending
  ),
})
```

The canonical capability strings are exactly `STRUCTURAL_ONLY`,
`STRUCTURAL_OR_SOLVER_UNSAT`, and `SOLVER_UNSAT_ONLY`; `S`, `S|U`, and `U` are
display abbreviations only. Producer version is a string (`"2"`), priority is an
integer, status collections are sorted tuples, and none is the empty tuple `()`.
The algorithm is the existing v2 `contracts.authority_digest`, including its
canonical-value normalization and SHA-256 encoding. A registry factory owns
`to_authority_dict()` with exactly this field/tuple schema. A generated fixture
must reconstruct both the full-row and common-projection registries from the same
typed row objects and assert both displayed digests; hand-authored digest literals
alone are not a gate.
Unregistered producer/stage/version tuples and either digest mismatch fail closed.
Structural-only rows prohibit solver receipts. Solver-capable rows require the
common typed query authority, deployment issuer, attempt membership, and complete
result ledger from slices 2/3. Priorities form a total unique order and are the
only timeout-selection priority authority.

Only a validated structural proof or validated UNSAT artifact can complete an
UNKNOWN requirement. SAT never completes one: it requires a model-bound
refutation artifact and Phase 6.1 counterexample-safety handoff. Missing/malformed
model authority is INVALID shadow evidence. UNKNOWN/ERROR remain non-completing
observations. A timeout is a signed execution event tied to the exact live
requirement and never changes ReasonId; only final live-frontier selection can make
it terminal. Raw boolean helpers, caller-visible evidence dictionaries, status
strings, and reordered receipt arrays have no authority.

Slice 3 and slice 4 effect ownership is globally ordered. Slice 3 first owns
function effect census, call/effect endpoints, call/effect correspondence, memory
object/alias/order, and final-state propositions. A slice 4
`summary_effect_model_incomplete` predicate is eligible only for one exact summary
candidate after all applicable slice 3 unary effect facts and endpoint identities
validate; it owns only whether that candidate's transition/applicability model
accounts for its already-identified effect surface. If a slice 3 prerequisite is
missing, only the slice 3 cause is emitted and the slice 4 predicate is false.
Their canonical targets and Q IDs are disjoint. A combined slice3+slice4
conservation gate proves each current effect source matches exactly one owner and
that no missing proposition has two active Q owners.

Accordingly, `summary_effect_unmodeled:effect_summary_missing` is refined to the
slice 3 function-census cause, and
`summary_effect_unmodeled:unsupported_call_effect` to the slice 3 unsupported
call-effect semantic cause. The legacy joined suffix made from a nonempty sorted
subset of `callee_effect_summary_missing`, `effect_order_unavailable`, and
`effect_summary_path_coverage_incomplete` is projection-only. The object-derived
tuple is split before v2 classification: its individual propositions map to slice
3 `callee_effect_summary_incomplete`,
`memory_effect_order_extraction_incomplete`, and
`effect_observation_coverage_incomplete`, respectively. Multiple tuple members
produce independent slice 3 causes/Q rows; duplicate members or noncanonical
order make shadow evidence INVALID. None also emits
`summary_effect_model_incomplete`. This one-to-many refinement is included in the
combined conservation gate and legacy output remains unchanged.

Summary-return blockers are emitted from immutable acceptance inputs, not parsed
from `analysis_notes`. The typed signal factory receives the exact candidate,
function snapshot, active precondition, transition evidence, effect surface,
candidate pair, or residual region required by its source code and derives the
canonical target itself. Notes and legacy reason records are projection-only.
Multiple rejected candidates, PHI SCCs, effect surfaces, and overlap pairs create
independent causes. One candidate with multiple missing propositions creates
independent causes and independently owned requirements; no first/last blocker
selection is permitted.

Slice 4 emits exact `CAUSE_OBSERVED` and artifact-authorized
`REQUIREMENT_COMPLETED` events and emits no `CAUSE_TRANSFORMED`. Successful
recurrence promotion may complete the exact proposal-validation requirement and
then independently expose later relational loop causes; it does not transform or
erase them. Failed promotion preserves the unary cause. Cache reuse requires an
exact current-snapshot dependency-closure receipt. Every issuer-open solver ledger
is finalized before the event recorder is sealed, including exceptions between
execution and proof-batch materialization.

Slice 4 gates include:

- exact table coverage and pairwise-disjoint predicates for every current loop,
  recurrence, summary-candidate, overlap, effect, PHI, and totality source code;
- negatives for each neighboring source code and for all INVALID/deferred inputs;
- same-cause dedup and non-merging across proposals, candidates, SCCs, effects,
  residual regions, candidate pairs, source snapshots, and observation contracts;
- same-function overlap-pair non-merging and negatives proving no cross-side or
  second-source snapshot is fabricated for unary overlap causes;
- combined slice3+slice4 effect-predicate conservation and unique Q ownership;
- exact live-frontier behavior for `ALL_OF(loop_exact_term_relation,
  loop_exact_guard_partition)`; term completion must precede guard completion,
  guard-first issuance is rejected, and physical event/receipt array order after
  both authorities exist does not change the reduced semantic projection;
- recurrence artifact completion through the factory-issued legacy-to-v2 binding
  receipt, with exact original-snapshot/successor-lineage/requirement joins, plus
  stale-cache, wrong-proposal, wrong-function, wrong-successor, wrong-Q, and
  raw-status rejection;
- separate exact-term and guard-partition completion factories, dependency and
  live-Q joins, structural and UNSAT positives, and SAT/raw-dict/aggregate negatives;
- exact full-row registry digest, common-registry projection digest, membership,
  capability, and total terminal priority; UNKNOWN/TIMEOUT/ERROR/
  UNSAT histories through the complete issuer census; SAT model-bound negative
  and counterexample-safety handoff; timeout followed by UNSAT, SAT, UNKNOWN,
  ERROR, another timeout, and receiptless attempt; physical receipt-array order
  permutations with identical semantic projection;
- two identical result-entry payload runs receive distinct occurrence/census
  identities, and execution-before-batch or replay failure leaves no open ledger;
- no strategy name in CauseId/ReasonId/ProofRequirementId and no transformation;
- default-off/shadow-failure preservation of the legacy decision and objects;
- current-source inventory delta, before/after semantic/proof backlog, current-HEAD
  representative loop/recurrence pairs and a related matrix, and fixed-reviewer GO.

#### Phase 6 slice 5 contract: ABI, return width, and readonly identity

Slice 5 owns only ABI/width/readonly semantic insufficiency. It does not own
generic expression lowering, decompilation failures, call/effect/memory ordering,
or solver execution state. A solver `UNKNOWN`, solver deadline, or process deadline
is an execution event and never creates an ABI/width/readonly ReasonId.

The slice replaces the legacy umbrellas `return_width_bridge_missing` and
`readonly_identity_missing`, and takes ownership of the two inputs deliberately
deferred by slice 4:

- `summary_return_candidate_invalid:return_width_missing`;
- `summary_return_overlap_unproven:return_width_mismatch`.

The sealed source-to-cause matrix has eight rows:

| Source condition | Scope and exact semantic target | Typed ReasonId | Proof requirement |
|---|---|---|---|
| an ordinary or summary return member lacks `return_storage_fact`, `payload_width_fact`, or `extension_evidence_fact` | UNARY: binary content, function snapshot, stable return operation/member site, missing-slot code and observation-surface kind; the absent fact is not part of identity | `return_width_provenance_unavailable` | `return_width_provenance` |
| a same-function summary/exact-return overlap has unequal or unjoined widths | UNARY: one function snapshot and exact candidate/exact-return pair | `return_width_relation_unproven` | `same_function_return_width_relation` |
| an exact return member lacks a calling-convention, declared/effective type, or ABI storage descriptor fact | UNARY: function snapshot, stable return operation/member site and missing ABI-slot code | `return_abi_provenance_unavailable` | `return_abi_provenance` |
| two complete unary width/ABI surfaces do not yet determine one common comparison observation | RELATIONAL: both stable return sites, source snapshots and ordered pair-width seed | `return_observation_contract_unproven` | `return_observation_contract` |
| a cross-binary return pair with complete unary facts lacks a calling-convention/storage compatibility theorem | RELATIONAL: both function snapshots, exact return sites, complete ABI artifact IDs and ordered observation contract | `return_abi_relation_unproven` | `return_abi_relation` |
| the return pair lacks proof that ignored/extended high bits preserve the compared observation | RELATIONAL: the same exact pair plus semantic widths, extension modes and compared observation width | `return_high_bit_relation_unproven` | `return_high_bit_relation` |
| one readonly load/reduction operand lacks stable object identity | UNARY: binary content, function snapshot, stable load operation/reduction-member site, role and load width; missing relocation/reference/storage facts are proof inputs, not identity | `readonly_storage_identity_unproven` | `readonly_storage_identity` |
| two ordered, fully identified readonly reduction-role object sets lack a unique proven correspondence | RELATIONAL: both ordered object-set artifact IDs, exact reduction roles, guard/iteration domain and observation contract; no caller-chosen object pairing | `readonly_object_correspondence_unproven` | `readonly_object_correspondence` |

These rows are pairwise disjoint. Missing width provenance is not width mismatch;
same-function overlap is not a cross-binary ABI cause; missing ABI provenance is
not an ABI relation failure; failure to choose an observation width is not a
high-bit theorem; ABI storage compatibility is not a high-bit/value theorem;
unary readonly identity is not relational readonly
correspondence. One return pair may therefore have two active relational causes
(`return_abi_relation_unproven` and `return_high_bit_relation_unproven`), each with
one independently owned requirement. One readonly reduction containing three
unidentified storage objects creates three unary causes, not one pair-level cause.

Cause identity excludes side labels, strategy names, raw pretty-printed types,
chosen proof method, solver status, retry number, result occurrence, and final
outcome. A missing-fact cause binds a stable producer site plus an exact sealed
missing-slot code; it never requires the missing fact itself. A relation cause
binds normalized Ghidra/API-derived type, storage, address-space,
calling-convention, expression-width, observation, and proven object-artifact keys.
Human-readable type names and exception text are diagnostic projection only. A
missing fact is UNKNOWN when its stable return/load site is formable. Only a
missing/unstable site, duplicate site identity, malformed source snapshot, or
unrecognized slot/source code makes the shadow entry INVALID; it must not fall
back to pair identity or a text-derived cause.

The satisfaction contract is registry-owned and atomic for every row above. The
slice must not encode the two legacy return-width actions as one cause with an
`ALL_OF` expression. ABI compatibility and high-bit preservation are distinct
semantic propositions and remain separately countable in `C_active`; their proof
work remains separately countable in `Q_open`.

Semantic observation readiness is independent from proof-producer execution
readiness. When complete prepared seeds establish that ABI compatibility and
high-bit preservation are both missing, both causes and both Q rows are observed
immediately. A missing ABI artifact prevents assignment/execution of the high-bit
producer but never suppresses or completes the high-bit cause/Q. Thus backlog
accounting can be `C=2/Q=2` while only the ABI Q is currently executable.

Completion authority is artifact-specific:

| Requirement | Required completion authority |
|---|---|
| `return_width_provenance` | `ReturnWidthProvenanceArtifact` proves the exact missing slot for one stable return site: positive storage/payload width, or one supported `same_width/zero_extend/sign_extend` flow certificate whose producer/value refs join that site. It binds the live C/Q, source/prepared snapshots, proof body and applicability. |
| `same_function_return_width_relation` | `SameFunctionReturnWidthRelationArtifact` proves, under the active guard, equal observation widths or a total observation-preserving coercion. A coercion body must prove `observe(coerce(v)) == observe(v)` for the full active domain and injectivity/losslessness over compared values; naming a coercion is insufficient. |
| `return_abi_provenance` | `ReturnAbiProvenanceArtifact` proves the exact missing ABI slot for one stable site from Ghidra calling-convention, declared/effective return type and return-storage API objects with provenance and applicability. |
| `return_observation_contract` | `ReturnObservationContractArtifact` proves one positive common observation width, its derivation (`source_declared_return_width` or validated common semantic payload width), projection policy, and semantic applicability to both complete unary surfaces. When projection applicability itself needs a high-bit theorem, completion depends on the exact `ReturnHighBitRelationProofArtifact`; it is not a prerequisite for that proof. |
| `return_abi_relation` | `ReturnAbiRelationArtifact` proves `same_return_abi_family AND abi_related_return_storage AND observation_contract_applicable` from both unary ABI artifacts. It binds normalized compatibility proof body, active guard, exact pair/live C/Q and dependency closure; merely storing ABI facts is insufficient. |
| `return_high_bit_relation` | `ReturnHighBitRelationProofArtifact` proves that the negation of high-bit irrelevance/equality under the active guard and exact observation projection is UNSAT. Structural completion is limited to sealed theorem IDs `same_width_identity_v1`, `validated_zero_extend_projection_v1`, `validated_sign_extend_projection_v1`, and `member_local_high_bits_irrelevant_v1`, each with independently validated premises; generic narrow-producer claims are rejected. |
| `readonly_storage_identity` | `ReadonlyStorageIdentityArtifact` proves that the exact stable load/member site resolves, for every reachable use under its guard, to one immutable object/range with fixed address space, width, endian, readonly block property and symbol/data/reference/relocation provenance. Presence of any one provenance field is insufficient. |
| `readonly_object_correspondence` | `ReadonlyObjectCorrespondenceArtifact` proves a unique total mapping between the two ordered object sets and binds reduction operator, member role/order/multiplicity, count identity, guard implication, iteration domain, load width/endian/address space, exact value observation and finite-witness completeness. Structural or UNSAT proof bodies validate the same theorem. |

`ReturnObservationProjectionSeed` is a typed, immutable, non-completion and
non-proof object built from the two stable return sites and complete unary width
facts. It binds candidate observation width/derivation, both storage/payload
widths, extension modes, projection term schema, guards, source/prepared snapshots
and ordered pair target. It carries no `proved` flag, cannot emit
`REQUIREMENT_COMPLETED`, and is never counted as an artifact. A malformed or
cross-target seed is INVALID. ABI/high-bit query authorities bind this seed rather
than a completed observation contract. After high-bit completion, the observation
contract factory revalidates the seed plus high-bit artifact and may complete the
exact observation-contract Q.

Raw dictionaries, booleans, status strings, legacy completed actions, cache
presence, reaching a later stage, or a final EQ result cannot complete a
requirement. Artifact factories validate fresh immutable inputs and issue exact
artifact IDs/digests. Cache reuse requires current source/prepared snapshot,
registry contract, observation contract, live C/Q identity, producer/encoding
version, applicability predicate, normalized proof body, dependency
closure and requirement identity. SAT never completes a requirement; a
model-bound witnessed refutation is handed to Phase 6.1 counterexample safety.

Readonly target construction is factory-owned. Each side first forms an ordered
set of stable load/reduction-member sites sorted by canonical role and site key.
Missing identities emit exactly one unary cause/Q per site. Duplicate/unstable
site keys are INVALID. After all unary artifacts exist, one relational cause is
formed per exact reduction-role pair over the two ordered sets. The factory
enumerates candidate mappings from role, width, address-space and reduction
constraints. Zero or multiple mappings are semantic UNKNOWN on that same set-level
target; exactly one mapping is stored only inside the completion artifact. A
caller-selected pair is rejected. For L/R set sizes `m/n`, conservation is
`m+n` possible unary site causes before identity completion and exactly one
relational cause per reduction-role pair afterward, never `m*n` guessed causes.

Slice 5 uses the exact immutable registry `ABI_RETURN_WIDTH_READONLY_REGISTRY_V1`
with domain `abi-return-width-readonly-v2`:

| Producer contract ID | Version | Proof stage | Proof kind | Capability | Issuer | Allowed / terminal status | Priority |
|---|---:|---|---|---|---|---|---:|
| `return-width-provenance-validator-v2` | `2` | `return_width_provenance` | `return_width_provenance` | `STRUCTURAL_ONLY` | `abi-width-structural-proof-factory-v1` | `structural_proof` / none | 110 |
| `same-function-return-width-relation-validator-v2` | `2` | `same_function_return_width_relation` | `same_function_return_width_relation` | `STRUCTURAL_ONLY` | `abi-width-structural-proof-factory-v1` | `structural_proof` / none | 120 |
| `return-abi-provenance-validator-v2` | `2` | `return_abi_provenance` | `return_abi_provenance` | `STRUCTURAL_ONLY` | `abi-width-structural-proof-factory-v1` | `structural_proof` / none | 130 |
| `return-observation-contract-validator-v2` | `2` | `return_observation_contract` | `return_observation_contract` | `STRUCTURAL_ONLY` | `abi-width-structural-proof-factory-v1` | `structural_proof` / none | 140 |
| `return-abi-relation-validator-v2` | `2` | `return_abi_relation` | `return_abi_relation` | `STRUCTURAL_ONLY` | `abi-width-structural-proof-factory-v1` | `structural_proof` / none | 150 |
| `return-high-bit-relation-solver-v2` | `2` | `return_high_bit_relation` | `return_high_bit_relation` | `STRUCTURAL_OR_SOLVER_UNSAT` | `parallel-solver-runner-v1` | `attempted` / `attempted` | 160 |
| `readonly-storage-identity-validator-v2` | `2` | `readonly_storage_identity` | `readonly_storage_identity` | `STRUCTURAL_ONLY` | `abi-width-structural-proof-factory-v1` | `structural_proof` / none | 170 |
| `readonly-object-correspondence-validator-v2` | `2` | `readonly_object_correspondence` | `readonly_object_correspondence` | `STRUCTURAL_OR_SOLVER_UNSAT` | `parallel-solver-runner-v1` | `attempted` / `attempted` | 180 |

The full authority payload uses the exact slice-4 tuple schema
`{registry_id, registry_version, rows}` with rows in ascending priority and fields
`(producer_contract_id, producer_version, proof_stage, proof_kind, capability,
execution_issuer_id, sorted allowed statuses, sorted terminal statuses,
terminal_priority)`. Its expected full digest is
`2161081892ca7a9faca9c60c6e93d82e14c008ca219b2d5f33c920d63c5722ab`;
the common `ProducerStageRegistry` projection digest is
`551027e8142ff34fe691aa34351dc3d784cc81a617c748caa57cfcf650495465`.
Both are generated from the same typed rows and fixture-checked before producer
code. Unregistered rows/statuses/issuers, empty status membership, or digest
mismatch is INVALID.

The digest fixture uses these literal values without inference:

```text
registry_id = "abi-return-width-readonly-v2"
registry_version = 1
producer_version = "2"                         # exact string on every row
proof_stage = the displayed Proof stage column  # exact string
proof_kind = the displayed Proof kind column    # exact string; equal to stage in v1
allowed_statuses = sorted tuple from the displayed Allowed value
terminal_eligible_statuses = sorted tuple from the displayed terminal value
none = ()                                       # exact empty tuple
rows = ascending terminal priority
```

The fixture constructs the full payload and common projection from the same eight
typed rows, recomputes both digests, and rejects any displayed-column, tuple/type,
issuer, capability, status, priority or row-order drift.

Same-function width relation and projection-seed construction require all
applicable unary width artifacts. ABI relation execution requires both unary ABI
artifacts plus the exact projection seed. High-bit execution requires the exact
ABI relation plus that seed, never the completed observation contract. Observation
contract completion requires the seed and, only when projection applicability was
blocked, the exact high-bit artifact.

An artifact object is never dependency-completion authority by itself. Assignment
for high-bit or readonly-correspondence execution consumes one immutable verified
PREFIX and must join every dependency artifact digest to the exact live-session
`RequirementCompletionReceipt` that completed its source Q. The join includes
result occurrence, occurrence, cause, requirement, seed/semantic target, source
snapshot, registry and artifact digest. The assignment factory simultaneously
requires exactly one matching `C_active`/`Q_open` row for the requested target and
the complete dependency-closure set. An unobserved, not-yet-completed,
cross-session, stale, extra, duplicated or object-only dependency is INVALID.

Readonly identity recovery uses two distinct factory-owned seeds:

```text
ReadonlyReductionObjectSetSeed
  = ordered base member/site authority, with an exact unresolved-member target set

ResolvedReadonlyObjectSetSeed
  = base seed
    + exact artifacts and live completion receipts for that unresolved set only
    + role-order-preserving replacement by validated storage identity keys
```

Already identified members retain their original authority and require no
invented unary artifact; zero unresolved members therefore require the exact empty
dependency set. Missing, extra, duplicate, wrong-member or stale dependencies are
INVALID. Only the resolved seed may issue the relational correspondence cause,
query or structural completion artifact. After unary completions, a session-owned
promotion finalizer appends the derived relational `CAUSE_OBSERVED` after the
relevant `REQUIREMENT_COMPLETED` events and reaches a deterministic fixed point
before stream seal/decision. It emits no `CAUSE_TRANSFORMED` and never treats an
intermediate prefix as final decision authority.

The two solver-capable proof kinds use factory-only semantic query authorities.
The renderer accepts no caller assertions. From the exact seed and completed
dependency closure it internally renders the negation of the owned theorem:

- high-bit binds observation width, both extension relations, guards and the exact
  completed ABI relation;
- readonly correspondence binds the resolved ordered object sets, candidate
  mapping, totality/uniqueness and all seven correspondence predicates.

Readonly value terms may share one SMT symbol only under independent typed
authority. A parameter load binds the sealed
`binary-equivalence-shared-parameter-memory-v1` contract, the ordered function
pair, one program-independent parameter index, exact term offset/width and
endianness. Owner-specific parameter identities without that contract are
non-formable. Storage, stack and global coordinates are side-local unless a
separate exact content/value-observation correspondence artifact binds the two
binaries; equal space/offset/size or storage names alone never share a symbol.
The `shared_value_authority_rows` are part of the fact-set and theorem digests.
Resolved unary members retain their original role/load member authority and bind
the exact storage proof/applicability, so promotion does not erase renderer facts.

Semantic query identity excludes retry ordinal, solver invocation and result
status; those belong only to assignment/attempt identity. Duplicate semantic
queries collapse, while retries remain distinct issuer-ledger attempts. A solver
completion factory accepts only the exact query authority, live requirement
assignment, issuer-owned execution receipt and validated `UNSAT`, and rechecks the
formula/assertion/declaration, execution, attempt and registry digests. Raw
`UNSAT`/status or a generic query object cannot complete a Q. `SAT` never completes
the slice-5 Q or authorizes `NOT_EQ`; it produces only a model-bound safety handoff
after independent replay validation.

Every attempt is issued from the common sealed registry, assigned to exactly one
live Q, recorded in the complete issuer census, and finalized before stream
sealing. `UNKNOWN`, `ERROR` and receiptless attempts do not complete; `TIMEOUT` is
first a nonterminal observation; a later `UNSAT` records recovered timeout and
completes; `SAT` remains live with the safety handoff. Only after all attempts may
the common priority registry select one terminal timeout. Duplicate/retry order is
canonical, the open ledger is finalized even if execution succeeds before batch
encoding fails, and producer membership status `attempted` is never confused with
the solver result status. Final TIMEOUT requires exactly one terminal timeout
receipt for a live Q; recovered deadlines remain nonterminal diagnostic events.

Parallel receipts are aggregated before lifecycle intents are formed. A
SAT/UNSAT conflict authorizes neither completion nor safety handoff, while every
receipt remains in the census. Multiple UNSAT receipts select exactly one
digest-canonical completion authority; extra UNSAT receipts are census-only.
Only one canonical SAT receipt may create an independently replayed safety
handoff. UNKNOWN/TIMEOUT/ERROR remain nondecisive execution history.

The session finalizer owns the dependency-ready solver scheduler. Production
observation registers the exact high-bit projection seed, readonly promotion
registers the exact resolved seed, and the scheduler forms and executes a query
only after its live dependency closure exists. Non-formable facts or receiptless
execution leave the original C/Q live. Every opened issuer ledger is sealed
before terminal-timeout selection and event-stream sealing.

These dependencies gate assignment/execution only; they never gate observation or
Q materialization of an already derivable missing semantic proposition. Dependency
failure keeps every observed cause/Q live.

Slice 5 emits no `CAUSE_TRANSFORMED`. Successful provenance/ABI/high-bit/readonly
proofs emit exact `REQUIREMENT_COMPLETED`; independently derivable missing
propositions are observed together even when a producer dependency is not ready.
The legacy reason/action records remain
default-off, non-authoritative projections and are never reducer input.

The exact current-source disposition matrix is sealed before wiring:

| Current source/context | V2 disposition |
|---|---|
| `return_width_surface.build_function_return_width_seed` slots `return_storage_fact`, `payload_width_fact`, `extension_evidence_fact`, for ordinary and summary members | one UNARY `return_width_provenance_unavailable` cause/Q per stable site+slot |
| the same seed builder's `calling_convention_fact` slots `calling_convention`, `declared_or_effective_return_type`, `return_storage_descriptor` | one UNARY `return_abi_provenance_unavailable` cause/Q per stable site+slot unless the slot is proven non-applicable by the sealed observation policy |
| `return_width_surface.build_top_level_observation_contract`: `observation_contract/top_level_comparison_contract` | RELATIONAL `return_observation_contract_unproven` |
| the same builder: `pair_width_compatibility/projection_applicability` | observe both RELATIONAL `return_observation_contract_unproven` and `return_high_bit_relation_unproven` with separate Qs over the same projection seed; high-bit completion then authorizes exact observation-contract completion |
| a complete `PairReturnObservationContract` plus two complete `ReturnAbiProvenanceArtifact`s for which `same_return_abi_family` or `abi_related_return_storage` is not proved | RELATIONAL `return_abi_relation_unproven` |
| summary source `summary_return_candidate_invalid:return_width_missing` | exact candidate site plus `return_storage_fact` maps to unary width provenance; unstable candidate site is INVALID |
| summary source `summary_return_overlap_unproven:return_width_mismatch` | UNARY same-function width relation |
| `pairwise_query_executor._run_pair_query` width catch | LEGACY_DIAGNOSTIC only at the catch; V2 rematerializes exact prepared seeds into the rows above; absent/mismatched seeds are INVALID |
| `pairwise_query_executor._check_pair_equality_under_model` and `_check_same_side_case_equality_under_model` catches | diagnostic retry observation only; no new cause because the original pair/member cause owns lifecycle |
| `pairwise_normalization` normalized inequality catch and `loop_template` return-value-proof catch | LEGACY_DIAGNOSTIC plus the same prepared-seed rematerialization; never a strategy-derived V2 cause |
| `monolithic` region/formula bridge catch, terminal monolithic catch, and `formula.builder` canonical-width fallback | successful validated bridge is completion input for the exact existing Q; unresolved prepared seed emits the applicable rows; exception text alone is INVALID |
| checker `ABI_RETRY` catch | LEGACY_DIAGNOSTIC plus prepared-seed rematerialization; retry stage and final outcome are excluded from cause identity |
| `pairwise_services/orchestration_2._solve_canonical_return_observation` pending evidence containing `reason_id/subreason/detail/pair_id/object_target_key` | the dictionary is LEGACY_DIAGNOSTIC only; V2 regenerates stable-site occurrences exclusively from the typed `prepared.blockers`; raw fields never enter the reducer, and absent/malformed prepared authority is INVALID |
| readonly fallbacks `semantic_key_missing`, `semantic_key_unavailable`, `semantic_key_none` | stable sites lacking identity emit unary readonly causes; an unformable/unstable load site is INVALID |
| readonly fallback `semantic_key_mismatch` | after unary identity completion, one ordered set-level relational correspondence cause; before unary completion, only the applicable unary causes |
| `readonly_contract_result_width_mismatch` | the applicable observation-contract/high-bit row derived from prepared width seeds; it is not a readonly identity cause |
| `readonly_contract_mismatch`, `readonly_contract_missing_term_sequence`, `readonly_contract_term_sequence_mismatch` | one ordered set-level readonly correspondence cause when stable sites/roles are formable; otherwise INVALID |
| `readonly_contract_type_mismatch` | not a readonly candidate and INVALID for slice 5; any independently detected loop/expression cause remains owned by its domain |
| `readonly_contract_missing_loop` | slice-4 loop/recurrence ownership only; zero slice-5 C/Q rows |
| `readonly_contract_missing_effect_profile`, `readonly_contract_effects_unproven` | slice-3 effect ownership only; zero slice-5 C/Q rows |
| neighboring loop fallback codes, generic expression/decompiler/call/effect errors, raw exception text, and unknown slot/source codes | owned by their earlier/later slice or INVALID; never coerced into a slice-5 cause |

Every listed catch/function/source code has an exact test row including near-miss
contexts. No catch site directly chooses a V2 ReasonId from exception text.

Slice 5 gates include:

- live current-source inventory of every production/default fallback for the four
  owned legacy source families, with exact source-code and neighboring-code
  classification, including the `orchestration_2` pending-evidence producer, and
  no exception-text catch-all;
- exact registry rows, priority, capability, accepted statuses, issuer ownership,
  full-row digest and common execution-registry projection digest;
- reason-boundary negatives proving all eight semantic rows are disjoint;
- same-cause dedup and non-merging across return members, storage locations,
  semantic widths, ABI/storage descriptors, observation contracts, readonly
  objects, reductions, functions and source snapshots;
- explicit 1:1 cause/Q ownership, including two causes/two Qs for ABI plus high-bit
  insufficiency and N unary causes/N Qs for N unidentified readonly objects;
- proof-artifact positives and raw-status, wrong-target, wrong-width, wrong-ABI,
  wrong-object, wrong-snapshot, stale-cache and missing-dependency negatives;
- UNKNOWN/TIMEOUT/ERROR/UNSAT/SAT, retry, receiptless attempt, recovered timeout and
  terminal timeout histories through the complete issuer ledger;
- no strategy name in semantic IDs, no implicit completion/transformation, and no
  decision-derived active-set or metric authority;
- default-off/shadow-failure preservation of legacy result and production objects;
- independent `C_active` and `Q_open` before/after metrics for each representative,
  with final decision and terminal/nonterminal timeout counts joined afterward;
- current-HEAD representatives covering return-width bridge activation and
  discharge, high-bit near miss, summary return width missing/mismatch, two
  distinct readonly objects, readonly correspondence discharge, and one
  conservative negative; stored structured outputs and source/binary hashes are
  rematerialized by tests;
- related-matrix regression, current source-inventory delta, clean diff check, and
  fixed-reviewer GO before slice 6 starts.

For each slice:

- replace string/umbrella production with typed cause production;
- keep legacy output only as non-authoritative projection;
- add cause boundary and near-miss negative tests;
- test same-cause dedup and independent-cause non-merging;
- test explicit completion and, only where the slice contract permits it, transformation; otherwise assert transformation non-use;
- run representative current-HEAD pairs and related matrix;
- record reason, cause, proof-backlog, and decision before/after.

#### Phase 6 slice 6 contract: operational extraction and decompilation

Slice 6 owns only the availability and execution authority of the function
decompilation artifacts required before semantic extraction begins. It does not
own unsupported P-code/expression semantics, return/outcome extraction after a
valid `HighFunction`, solver execution, or strategy proof gaps. Operational
failure text is diagnostic only and never becomes a reason ID, cause target,
timeout classification, or error kind.

The slice has exactly two semantic causes:

| Structured source state | Scope and exact semantic target | Typed ReasonId | Proof requirement |
|---|---|---|---|
| a looked-up Ghidra `Function` has no completed decompilation artifact for the active decompiler contract | UNARY: binary content identity, program/language/compiler identity, stable function entry/body identity, and decompiler contract digest; mutable prototype/storage is attempt input, not CauseId | `function_decompilation_artifact_unavailable` | `function_decompilation_artifact` |
| a completed, valid decompilation result has no `HighFunction` IR artifact | UNARY: the same function target, decompiler contract and missing IR proposition; occurrence evidence, not CauseId, binds the exact completed decompilation attempt/artifact | `high_function_ir_unavailable` | `high_function_ir_materialization` |

Both contracts are atomic. Cause identity excludes binary side labels, function
display aliases, mutable signature/calling-convention/storage hypotheses,
retry/invocation ordinal, timeout budget, elapsed time, decompilation
attempt/artifact identity, error message, exception text, strategy, result
occurrence and final outcome. The
decompiler contract digest binds the decompiler interface/options version,
analysis mode, simplification style, Ghidra language/compiler specification and
the extraction schema, but not the per-attempt budget. A retry with a different
budget therefore addresses the same semantic cause and requirement.

The function target is factory-owned and must be formable before decompilation.
It is derived from binary content identity plus Ghidra `Function`, entry point,
body/range, program language ID and compiler-spec ID. Prototype, calling
convention, parameters and return storage form a separate immutable
`DecompilationAttemptInputSurface` bound to each attempt/artifact. Signature-
changing reanalysis therefore addresses the same semantic C/Q with a new input
surface; a budget-only retry retains the same input-surface digest. A missing
binary content identity, unstable or
duplicate function entry, malformed program identity, or caller-assembled target
is INVALID; it must not fall back to the requested function name or rendered C.

Decompilation is checkpointable and uses this exact order:

```text
function lookup succeeds and target seed validates
  -> observe function_decompilation_artifact_unavailable C/Q
  -> assign one process attempt to that exact live Q
  -> issue DecompilationInvocationReceipt
  -> persist ACTIVE OperationalCheckpointReceipt
  -> invoke DecompInterface.decompileFunction
  -> issue DecompilationAttemptObservation from flags/getFunction
  -> derive completed-result structural identity only for the completed row
  -> issue immutable DecompilationAttemptReceipt

decompileCompleted == true
  -> issue DecompilationArtifactReceipt
  -> exact-COMPLETED the decompilation Q
  -> observe high_function_ir_unavailable C/Q
  -> call getHighFunction once through HighFunctionObservationCapability
  -> validate that capability against the completed decompilation artifact
  -> issue HighFunctionIRArtifact and exact-COMPLETED that Q, or leave it live

isTimedOut == true
  -> append PROCESS_TIMEOUT bound to the decompilation Q and attempt receipt
  -> keep C/Q live for retry or terminal timeout selection

failedToStart / isCancelled / non-timeout abort / exception
  -> append one sealed ERROR event
  -> never fabricate or complete a semantic requirement
```

The cause is observed before invocation so an outer process deadline can consume
a durable checkpoint referencing one already-live requirement. Before the native
decompiler invocation, the worker persists a factory-issued
`OperationalCheckpointReceipt` using temporary-file write, file `fsync`, atomic
rename and parent-directory `fsync`. It binds the result occurrence, worker
execution identity, worker PID/start-token, stream ID and verified PREFIX digest,
exact C/Q and live-requirement assignment, registry/issuer/decompiler/input-
surface digests, invocation nonce/ordinal, configured deadline policy and worker
signing-key ID/signature. Timing values are diagnostic side data and are excluded
from every authority digest.

Checkpoint lifecycle is a signed compare-and-swap chain with exactly these
states:

```text
ACTIVE -> COMPLETION_READY -> RESOLVED
ACTIVE -> TIMED_OUT_CLAIMED -> TIMED_OUT
```

State transitions bind the prior state digest and invocation nonce. Missing,
torn, stale, duplicate, multiple-active, wrong-PID/start-token, wrong-policy,
signature-invalid and nonmonotonic transition files are rejected. A worker may
not resolve `TIMED_OUT`; exactly one final state exists per invocation.

All continuation publication, continuation re-check and state CAS operations
run under one checkpoint-directory-scoped OS lock shared by worker, supervisor
and recovery resolver. The worker holds it while it persists the continuation
and CASes `ACTIVE -> COMPLETION_READY`; the supervisor holds it while it
re-reads/verifies every durable continuation and CASes
`ACTIVE -> TIMED_OUT_CLAIMED`. If a worker crashes after publishing a valid
continuation but before its CAS, the recovery resolver sees that continuation
under the same lock and claims `COMPLETION_READY`; the timeout branch cannot win
that interval. Lock acquisition identity, state digest and directory identity
are bound to each transition; unlocked or split-directory transitions are
invalid.

`COMPLETION_READY -> RESOLVED` is legal only after a continuation of the worker stream
containing the final `DecompilationAttemptReceipt`, completion artifact plus
`REQUIREMENT_COMPLETED`, or sealed `OperationalErrorArtifact` plus `ERROR` has
been written, file-`fsync`ed, atomically renamed, parent-directory-`fsync`ed and
independently verified. The RESOLVED transition binds that exact continuation
digest and terminal artifact/event IDs. A supervisor may recover this transition
only by issuing a signed `RecoveryResolutionReceipt` over the already durable,
worker-signed continuation; it cannot invent, edit or append worker evidence.
If such a continuation exists, timeout CAS is forbidden. Thus a crash after
continuation durability but before the worker CAS is recovered as RESOLVED,
never misclassified as timeout.

`TIMED_OUT_CLAIMED` binds every deterministic input required for the final
timeout authority: checkpoint/prefix/last-event digests, exact live assignment,
PID/start-token kill disposition, invocation nonce, registry/policy and
supervisor issuer/key ID. The supervisor then writes and `fsync`s the uniquely
derived timeout receipt and terminal segment before CASing to `TIMED_OUT`, whose
transition binds both digests. A crash in this interval is recovered under the
same lock by reissuing byte-identical authority with the retained signing key;
conflicting bytes, unavailable/revoked key or non-reproducible output makes the
canonical census INVALID. Only final `TIMED_OUT`, never the claimed state, is
terminal-selection eligible.

Before the worker is released from its startup barrier, the supervisor persists
a factory-issued signed `SupervisorLaunchReceipt` by the same file/directory
durability protocol. It binds a preallocated result-occurrence ID, immutable
manifest-entry preimage identity (source/binary/function/command/config, but no
future CensusEntry or final-stream digest), execution/invocation nonce, child
PID/start-token, deadline policy, supervisor issuer/key and the empty worker
stream root. The occurrence and manifest preimage are factory inputs to later
events; they never depend on the final decision or final stream, so this launch
authority introduces no census/identity cycle.

The external supervisor owns a separately stored append-only
`SupervisorTerminalSegment`; it never appends to or rewrites the killed worker's
physical file, but the segment is part of the same preallocated logical stream.
After enforcing the configured deadline and killing the exact PID/start-token,
it may complete `ACTIVE -> TIMED_OUT_CLAIMED -> TIMED_OUT` and issue one signed
`SupervisorTimeoutReceipt` plus `PROCESS_TIMEOUT` event. The receipt binds the
checkpoint digest, worker prefix/event-chain digest, exact live Q/assignment,
process invocation and exit/kill disposition, supervisor policy/key, registry
and issuer. It excludes wall-clock/monotonic timestamps and elapsed duration from
identity. A `DurableTimeoutFinalizationBundle` joins the launch receipt, verified
worker PREFIX, checkpoint chain and separately sealed supervisor segment; only
this bundle may let the finalizer issue TIMEOUT when the worker FINAL stream is
absent.

The launch factory preallocates one stream ID and its exact genesis predecessor
constant. Worker events use that stream ID, contiguous sequence numbers starting
at zero, and the previous event authority digest. The supervisor terminal event
uses the same stream ID, sequence `N + 1`, and the worker's last-event authority
digest as its header predecessor; for an empty worker prefix it uses sequence
zero and the fixed genesis predecessor. Its segment receipt additionally binds
the complete worker PREFIX digest, so prefix membership is checked without
misusing that digest as an event predecessor.

The bundle factory issues one `CompositeEventStreamAuthority` by validating this
ordinary single-stream chain through the existing event codec. It rejects mixed
stream IDs, noncontiguous/duplicate sequence, a prefix digest used as header
predecessor, wrong genesis, a worker PREFIX that already contains any terminal
event for the claimed invocation, more than one supervisor terminal event,
broken last-event predecessor, occurrence/manifest/Q mismatch, or either
unsealed input. The validated logical-stream digest is stored as
`CensusEntry.event_stream_authority_digest`; the factory then issues the normal
FINAL `VerifiedLifecycleProjection` over that composite stream and seals C/Q in
the existing reducer. The supervisor `PROCESS_TIMEOUT` is therefore exactly one
canonical terminal event in terminal-event census, and is not counted again as
a side-stream event. Result identity remains the preallocated launch occurrence;
the later CensusEntry binds the composite digest in one direction only.

A deadline before an ACTIVE semantic checkpoint or during a non-decompilation
stage cannot synthesize timeout or semantic C/Q. The supervisor instead issues a
signed `SupervisorOperationalErrorReceipt` from the durable launch receipt and
child exit/kill disposition, appends exactly one ERROR terminal segment using
the same stream ID/sequence/predecessor rules, and forms a
`DurableErrorFinalizationBundle`. The same composite-stream factory joins
the empty or verified nonterminal worker PREFIX with that ERROR and produces the
normal FINAL lifecycle/ERROR authority. Missing/torn/unauthenticated launch
authority, occurrence mismatch, or an unjoinable prefix makes the canonical
census INVALID; it never fabricates ERROR.

The current shell-side `timeout ...; append synthetic JSON` path is prohibited
for canonical v2. It is replaced by a supervisor command started before the
worker and holding a deployment-provisioned supervisor signing key. Shell output
is a projection of the verified finalization bundle only. A kill before an
ACTIVE checkpoint, during a non-decompilation stage, with multiple checkpoints,
or without an authenticated supervisor receipt yields the sealed
`process_deadline_without_checkpoint`/`operational_authority_invalid` ERROR path,
never TIMEOUT. The legacy synthetic JSON remains reader-only input until Phase 8
and is never v2 authority.

A successful ordinary run therefore contains transient OBSERVED/COMPLETED
lifecycle events but has zero final active operational causes. A timeout followed
by a successful retry closes the same Q and remains a nonterminal historical
timeout. A terminal decompiler timeout requires exactly one selected structured
timeout attempt, worker PROCESS_TIMEOUT or supervisor timeout receipt for that
live Q and yields TIMEOUT, not UNKNOWN.

Timeout/error classification uses the structured Ghidra `DecompileResults` API
only. `isTimedOut()`, `failedToStart()`, `isCancelled()`,
`decompileCompleted()`, and `getFunction()` are captured exactly once into the
`DecompilationAttemptObservation` before any legacy status is formed.
`getHighFunction()` is explicitly absent from the invocation, attempt
observation, completed-result structural identity and attempt receipt. Only
after a completed `DecompilationArtifactReceipt` exists may the factory call it
once and issue a `HighFunctionObservationCapability`; that capability is the
sole input object accepted by `HighFunctionIRArtifact` extraction.
`getErrorMessage()` is diagnostic payload only. The accepted flag rows are
sealed and disjoint:

| completed | timed_out | failed_to_start | cancelled | V2 disposition |
|---:|---:|---:|---:|---|
| true | false | false | false | decompilation artifact completion |
| false | true | false | false | live semantic cause plus PROCESS_TIMEOUT |
| false | false | true | false | `decompiler_failed_to_start` ERROR |
| false | false | false | true | `decompiler_cancelled` ERROR |
| false | false | false | false | `decompiler_aborted` ERROR |

Any other combination is `operational_authority_invalid` ERROR. In particular,
substrings such as `timeout`, `cancelled`, `crash`, or `failed` in an error
message have no authority. `HighFunction is None` is a semantic artifact gap only
after the completed row above; a null `HighFunction` on any noncompleted or
contradictory row is INVALID/ERROR rather than the high-function cause.

Non-semantic operational/tool failures use factory-issued
`OperationalErrorArtifact` plus `ErrorEventAuthority`. The sealed error kinds are
`function_lookup_miss`, `function_lookup_exception`,
`decompiler_failed_to_start`, `decompiler_cancelled`, `decompiler_aborted`,
`analysis_exception`, `strategy_exception`, `unexpected_pairwise_state`,
`process_deadline_without_checkpoint`, and `operational_authority_invalid`. Each artifact
binds result occurrence, source/program/function target when available, exact
catch-site contract ID, exception class identity when applicable, structured
attempt receipt when applicable, and producer/encoding version. Exception text,
traceback text and legacy reason records are diagnostic only. Raw strings,
caller-created digests, a legacy `error_message`, or an UNKNOWN reason cannot
issue ERROR authority.

Function lookup is factory-owned and returns one typed `FunctionLookupOutcome`
with status `FOUND`, `MISSING`, or `ERROR`. `FOUND` binds the exact stable
function target seed; `MISSING` binds a complete successful FunctionManager
census and may issue only `function_lookup_miss`; `ERROR` binds the exact lookup
catch-site contract and exception class identity and may issue only
`function_lookup_exception`. `_find_function_by_name` must not swallow an
iteration exception into `None`. Display/error messages are diagnostics, and
identical messages on `MISSING` and `ERROR` must not affect classification.

The result authority is an acyclic issuance DAG:

```text
live-Q assignment
  -> DecompilationInvocationReceipt
  -> DecompilationAttemptObservation
  -> completed-result structural identity (completed row only)
  -> DecompilationAttemptReceipt
  -> DecompilationArtifactReceipt
  -> HighFunctionIRArtifact
```

`DecompilationInvocationReceipt` is fixed before calling Ghidra and binds the
assignment, invocation nonce/ordinal, execution identity, decompiler/input
contract and configured timeout. After the call, the issuer captures the four
structured flags and `DecompileResults.getFunction()` exactly once into a
`DecompilationAttemptObservation` bound to that invocation receipt. It contains
no final attempt-receipt or completion-artifact digest. For the one completed
flag row, the completed-result structural identity is derived only from the
observation/preimage digest, exact target, decompiler contract, attempt input
surface and the observed `getFunction()` identity joined back to the target.

The two completion artifacts are distinct. `DecompilationAttemptReceipt` binds
the invocation receipt, observation, and completed-result identity when present;
noncompleted rows have no such identity. `DecompilationArtifactReceipt` then
binds the exact target, final successful attempt receipt, decompiler contract,
source/program snapshot and that already-derived structural identity. It neither
requires nor claims a `HighFunction`/IR digest; Java/Python object identity,
`repr`, hash code and rendered C are explicitly excluded.

`HighFunctionIRArtifact` additionally binds the exact completed decompilation
artifact and a canonical object-derived IR projection. The projection contains:

- function/entry and prototype storage identity;
- basic blocks in canonical block-index/start order and every directed CFG edge;
- every P-code op in block/`SequenceNumber` order with instruction address,
  order/time, opcode and output/input arity;
- every output/input varnode's address-space identity, offset, size, constant/
  register/unique/address/tied flags and stable high-variable/storage provenance;
- extraction schema and complete block/op/input coverage counts.

The ordered projection content digest, not aggregate block/opcode counts, is IR
identity. Duplicate/unstable block, op, sequence or varnode identity is INVALID.
Cross-session `HighFunctionIRArtifact` cache reuse is prohibited in v1. In-session
reuse is capability-bound to the exact factory-issued object plus target,
source/program snapshot, decompiler/input contract, successful attempt/artifact,
registry and exact live Q. Stale, name-only, census-only, reconstructed or
object-only reuse is rejected.

Process attempts use an append-only issuer ledger independent from solver
ledgers. `DecompilationAttemptReceipt` binds the exact live requirement
assignment, invocation receipt and observation, process invocation
identity/ordinal, configured timeout seconds, decompiler/input contract digest,
structured result flags, completed-result identity when present, active
execution identity and receipt digest. Start/end,
elapsed and wall-clock/monotonic timestamps are diagnostic-only fields stored
outside the authority payload and never affect receipt, attempt, census or
selection digests. Every assigned attempt appears in the sealed census,
including success, timeout, failed-to-start, cancellation, non-timeout abort and
receiptless attempts. Receiptless attempts do not authorize timeout or ERROR
classification; they leave the Q live and make final shadow evidence incomplete
unless an outer checkpointed process timeout or separately sealed error artifact
explains the termination.

Terminal selection is registry-owned and computed from the full sealed process
census after the final lifecycle projection. For each live requirement, the
latest semantically relevant attempt is selected by issuer invocation ordinal
and event-chain order, never by receipt-array or wall-clock order. Only a
structured worker `timed_out` receipt joined to one recorded PROCESS_TIMEOUT, or
one verified `SupervisorTimeoutReceipt` joined through its checkpoint/finalization
bundle, is eligible.
A later successful completion suppresses every older timeout for that Q. A later
structured ERROR has final-decision precedence and no timeout is selected.
UNKNOWN is not a process status; receiptless/cancelled/aborted/failed-to-start
attempts are never terminal-timeout candidates. The selection receipt binds the
registry version/digest and total priority, full census digest, final live-Q
projection digest, worker or supervisor event-stream digest, exact candidate-set
digest and selected attempt/event digests. Duplicate selections, caller subsets,
unsealed ledgers and lifecycle/census mismatches are INVALID. Across all domains,
registry priority plus requirement digest and event order forms one total,
deterministic selection order and at most one terminal timeout.

The immutable registry `OPERATIONAL_EXTRACTION_DECOMPILATION_REGISTRY_V1` has
domain `operational-extraction-decompilation-v2`:

| Producer contract ID | Version | Proof stage / proof kind | Capability | Issuer | Allowed / terminal status | Priority |
|---|---:|---|---|---|---|---:|
| `function-decompilation-artifact-producer-v2` | `2` | `function_decompilation_artifact` | `PROCESS_ARTIFACT_OR_TIMEOUT` | `decompiler-process-runner-v1` | `attempted` / `attempted` | 190 |
| `high-function-ir-validator-v2` | `2` | `high_function_ir_materialization` | `STRUCTURAL_ONLY` | `high-function-ir-proof-factory-v1` | `structural_proof` / none | 200 |

The full registry payload uses the slice-5 tuple schema and is generated from the
same typed rows as the process-registry projection. Exact expected digests are
fixture-generated and inserted before producer wiring; row order, proof kind,
capability, issuer, status tuple, priority, empty terminal tuple and string/int
types are all contract-tested. No generic solver issuer or solver status is
accepted for this domain.

Those two rows are the complete slice-6 *semantic* registry, but secondary
decompilation is authorized by a distinct immutable
`SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY_V1`; it is not forced through a
slice-6 proof-kind equality check. A factory-issued
`SubordinateProcessAssignmentReceipt` joins one exact already-live parent
`LiveRequirementAssignment`, its owning domain/registry row, one adapter row and
the process stage `function_decompilation_artifact`. Parent Q identity and proof
kind remain unchanged; the adapter only authorizes a subordinate process attempt
and never completes the parent by itself. Generic parent-Q, reason-only,
stage-only or caller-built joins are invalid.

| Adapter ID | Exact current source | Parent reason | Parent proof kind | Process capability / terminal eligible | Priority |
|---|---|---|---|---|---:|
| `fresh-callee-parameter-decomp-v1` | `_get_freshest_callee_parameters` through lifecycle broker | `call_argument_extraction_incomplete` | `call_argument_extraction` | `PROCESS_ARTIFACT_OR_TIMEOUT` / yes | 191 |
| `callee-effect-summary-decomp-v1` | `effect_integration._build_effect_summary.summarize_call` | `callee_effect_summary_incomplete` | `callee_effect_summary` | `PROCESS_ARTIFACT_OR_TIMEOUT` / yes | 192 |
| `inline-region-state-decomp-v1` | `call_recovery_1._resolve_local_code_target_expansions` | `inline_region_semantics_incomplete` | `inline_region_state_transformer` | `PROCESS_ARTIFACT_OR_TIMEOUT` / yes | 193 |
| `recurrence-proposal-refresh-decomp-v1` | `session_helpers_3.refresh_structural_recurrence_summary` | `recurrence_proposal_validation_unproven` | `recurrence_transition_termination_validation` | `PROCESS_ARTIFACT_OR_TIMEOUT` / yes | 194 |
| `summary-return-refresh-decomp-v1` | `session_helpers_3.refresh_structural_recurrence_summary` | `summary_return_extraction_incomplete` | `summary_return_extraction` | `PROCESS_ARTIFACT_OR_TIMEOUT` / yes | 195 |
| `summary-transition-refresh-decomp-v1` | `session_helpers_3.refresh_structural_recurrence_summary` | `summary_recurrence_transition_validation_incomplete` | `summary_recurrence_transition_validation` | `PROCESS_ARTIFACT_OR_TIMEOUT` / yes | 196 |

Every row also binds the exact parent domain registry ID/version/digest,
producer-contract membership, adapter issuer
`subordinate-decompilation-assignment-factory-v1`, allowed status `attempted`,
process issuer `decompiler-process-runner-v1`, and total terminal priority. The
literal full/common adapter-registry digests are generated and contract-tested
before wiring. Terminal selection joins the live parent Q through the subordinate
receipt and uses the adapter priority; it does not relabel the parent proof kind
as a slice-6 requirement. A process artifact is input evidence for the owning
slice-3/4 producer; only that domain's separately validated completion artifact
may complete the parent Q.

The exact current-source disposition is:

| Current source/context | V2 disposition |
|---|---|
| `ReturnAnalyzer.analyze_function`: `decompileCompleted()==false` | classify only from the sealed structured flag row; timeout becomes the decompilation cause plus PROCESS_TIMEOUT, other rows become ERROR |
| the same function: completed result with `getHighFunction()==None` | `high_function_ir_unavailable` C/Q |
| `analyzer_services.lifecycle._find_function_by_name` / `analyze_function_by_name` | replace swallowed `None` with typed lookup outcome: complete negative census is `function_lookup_miss`; FunctionManager/catch exception is `function_lookup_exception`; neither emits C/Q |
| `analyze_function_by_name`: analysis exception after FOUND | `analysis_exception` ERROR; no C/Q |
| initial analysis and fresh signature reanalysis in `equivalence.reanalysis` | the same target/attempt/artifact authority; retry stage is excluded from cause identity |
| `analyzer_services.lifecycle._decompile_function`, including `call_recovery_1._get_freshest_callee_parameters` | all semantic uses go through `fresh-callee-parameter-decomp-v1`; the exact `call_argument_extraction_incomplete/call_argument_extraction` Q must be observed and assigned before invocation; no-Q semantic consumption is INVALID |
| `session_helpers_3.refresh_structural_recurrence_summary` | process broker only; before invocation it must select exactly one of the three sealed recurrence/summary adapter rows and its already-live parent Q; ambiguous/no-Q semantic refresh is INVALID; zero slice-6 C/Q |
| `effect_integration._build_effect_summary.summarize_call` direct callee decompilation | process broker only through `callee-effect-summary-decomp-v1`; exact slice-3 `callee_effect_summary_incomplete/callee_effect_summary` Q is required before invocation; zero slice-6 C/Q |
| `call_recovery_1._resolve_local_code_target_expansions` direct containing-function decompilation | process broker only through `inline-region-state-decomp-v1`; exact slice-3 `inline_region_semantics_incomplete/inline_region_state_transformer` Q is required before invocation; zero slice-6 C/Q |
| `validation.phase1_pyghidra_object_probe` and test-only direct decompilation | validation-only, never production stream or canonical census input |
| `pairwise_services.orchestration_2._create_empty_result` / legacy `empty_return_cases` | LEGACY_DIAGNOSTIC only; V2 must use the already-owned slice-2 termination/partition causes, and missing slice-2 authority is INVALID |
| `pairwise_services.orchestration_1` impossible aggregate counts / legacy `unexpected_pairwise_state` | `unexpected_pairwise_state` ERROR; no C/Q |
| monolithic broad exception / legacy `strategy_exception` | `strategy_exception` ERROR; no C/Q; unsupported semantic lowering remains the slice-3 typed cause |
| `eqbench_run_all_32jobs.sh` outer pair timeout and its synthetic JSON helper | reader-only legacy projection; canonical execution uses the authenticated supervisor/finalization bundle, and a kill without one ACTIVE top-level decompilation checkpoint is ERROR |
| solver UNKNOWN/TIMEOUT/ERROR, unsupported expressions, return/summary extraction gaps, loop/call/effect/ABI/readonly gaps | zero slice-6 causes; owned by execution authority or earlier slices |
| legacy `decompilation_failed`, `high_function_missing`, `strategy_exception`, `unexpected_pairwise_state`, and their message/detail fields | LEGACY_DIAGNOSTIC only and never reducer input |

Every production `decompileFunction` call is statically inventoried and must be
inside the pinned process broker. New direct invocations fail the source-inventory
gate. Earlier-domain ownership changes only the semantic Q to which a broker
attempt may be assigned; it never creates a slice-6 semantic cause. The four
semantic secondary paths above may not fall back to DIAGNOSTIC_ONLY merely
because their Q has not yet been emitted: they must materialize the exact parent
C/Q before invoking or fail shadow evidence INVALID. DIAGNOSTIC_ONLY is permitted
only for a source/callsite in a sealed optional-call allowlist and with a
factory-issued `DecisionNonInfluenceCertificate`. The factory accepts no caller
boolean. It rederives a typed dependency/dataflow projection from the pinned
source snapshot and binds its digest, result occurrence, callsite object
identity, broker invocation and allowlist row. The projection must prove all of:
return value is discarded; no returned artifact or fallback is read; no cache,
analysis object or global/instance state is written; no event/reason/requirement/
query producer is reachable; and success/failure control flow rejoins before any
final-decision input. Unresolved/dynamic calls, reflection, alias escape, cache
write, fallback read or source-fingerprint drift make certification impossible
and DIAGNOSTIC_ONLY INVALID. The certificate therefore proves that the returned
artifact, fallback/cache value and failure status are unreachable from every
semantic cause, requirement, solver query and final decision in this result
occurrence. Such a call has no live assignment,
cannot emit PROCESS_TIMEOUT, cannot be terminalized and cannot complete any
requirement. Source-specific postcondition tests prove either exact parent-C/Q
materialization or this non-influence property; absence of both is INVALID.

Slice 6 emits no `CAUSE_TRANSFORMED`. Legacy result fields and decisions remain
default-off and unchanged during dual-write. Shadow failure produces
`SHADOW_EVIDENCE_INCOMPLETE` and cannot mutate v1.

Slice 6 gates include:

- complete current-source inventory for decompilation, high-function, function
  lookup, analysis exception, strategy exception, impossible pairwise state,
  empty-return and outer process-timeout paths, including every production
  `decompileFunction` call and process-broker mode, with exact ownership and no
  message-substring fallback or direct bypass;
- exact two-reason/two-contract registry, digest fixtures, cause boundaries,
  same-cause retry dedup and cross-function/binary/program non-merging;
- pre-invocation checkpoint ordering, success completion, timeout retained Q,
  timeout-then-success recovery, terminal timeout, failed-to-start, cancellation,
  abort, contradictory flags, exception and receiptless attempt histories;
- durable checkpoint atomic-write/fsync and
  ACTIVE/COMPLETION_READY/RESOLVED/TIMED_OUT_CLAIMED/TIMED_OUT CAS tests,
  stale/torn/duplicate/multiple/wrong-process/wrong-policy/signature negatives,
  one-lock continuation/timeout exclusion, recovery-resolution crash window,
  claimed-timeout byte-identical recovery and missing-key INVALID,
  separately sealed same-stream supervisor terminal-segment joins, single-ID/
  contiguous-sequence/last-event-predecessor/genesis negatives, composite FINAL lifecycle/census
  digest and exactly-one terminal-event projection, killed-worker finalization,
  durable launch authority, before-checkpoint/non-decompilation deadline ERROR,
  and missing/torn launch INVALID behavior;
- process-census latest-attempt selection proving later success suppresses older
  timeout, ERROR precedence, receiptless noneligibility, deterministic global
  priority and candidate/census/lifecycle/stream digest binding;
- exact completion-artifact positives and wrong target/program/source/contract,
  stale cache, cross-session, census-only IR collision, reordered block/op/
  varnode projection, forged object/digest and missing-dependency negatives;
- ERROR artifacts for every sealed error kind, with exception/error text proven
  diagnostic-only and no error-derived C/Q;
- typed function lookup FOUND/MISSING/ERROR tests, including identical-message
  miss/exception cases, and changed-signature versus budget-only retry identity;
- acyclic invocation/observation/completed-identity/attempt/artifact digest
  recomputation tests, including a negative that no downstream receipt digest is
  accepted in an upstream preimage;
- completed-only `HighFunctionObservationCapability` tests proving
  `getHighFunction()` and IR identity cannot enter an upstream attempt preimage;
- exact subordinate-adapter registry/digest/membership/priority tests for every
  listed parent reason/proof kind, generic and wrong-parent join negatives, and
  source-by-source postconditions proving parent C/Q precedes every semantic
  secondary call or a sealed allowlist/dataflow-derived non-influence certificate
  makes it truly optional, with discard/state-write/cache/fallback/dynamic-call
  positive and negative projections;
- structured-flag tests proving a completed result whose warning message contains
  `timeout`, `cancelled`, or `failed` still completes, while a non-timeout abort
  whose message contains `timeout` remains abort ERROR;
- explicit proof that `empty_return_cases` remains slice-2-owned and that no
  operational path fabricates solver events, strategy-derived IDs or completion;
- default-off preservation, independent C/Q and outcome-joined metrics,
  TIMEOUT/UNKNOWN/ERROR conservation and canonical census joins;
- current-HEAD real PyGhidra success plus function-lookup-error representatives,
  structured mocked timeout/high-function/error near misses, related analysis and
  reanalysis regressions, current inventory delta, stored hash-bound outputs,
  clean diff check and fixed-reviewer GO.

### Phase 7: stop production umbrella generation

Stop production generation of, at minimum:

- `unknown`
- `solver_unknown_timeout`
- `unresolved_expression`
- `equivalence_blocking_unsafety`
- `sat_unsafety`
- `loop_summary_proof_missing`
- `outcome_partition_unknown`
- strategy-derived `method_b_closure_blocked`

These remain reader-only legacy IDs. Do not replace `solver_unknown_timeout` with new solver-status reason IDs; use a semantic cause plus execution event.

Gate:

- production umbrella generation is zero;
- v2 typed cause coverage is `1.0`;
- legacy inferred count remains separate;
- legacy reader still reads the saved 411 summaries losslessly.

#### Phase 7 authority and inventory contract

Phase 7 does not delete enum values, aliases, or historical decoders. It seals the
following disjoint relations over the reviewed source inventory:

```text
U_retired_refs = all discovered references to a retired reason ID
P_emit   = production sites that can create a reason occurrence or result reason
P_route  = production sites that only route/compare an already-created reason
D_legacy = legacy-only diagnostic projections and aggregate readers
L_decode = lossless legacy decoder declarations and mappings

U_retired_refs = P_emit ⊎ P_route ⊎ D_legacy ⊎ L_decode
```

The union is exact and every pairwise intersection is empty. Every manifest AST
node identity is unique; candidate IDs and classified IDs are equal; row counts
obey the union conservation equation; and every dynamic finite-set site expands
to its exact reviewed member set. `P_emit` is found from constructors, return
values, assignments,
mapping values, dynamic finite reason sets, and indirect constructor arguments;
it is not derived from string search alone. `P_route`, `D_legacy`, and `L_decode`
cannot issue a v2 occurrence, enter `C_active_base`/`Q_open_base`, or influence a
five-value decision. The reviewed manifest binds path, AST node identity, source
fingerprint, finite reason set, relation, and reviewer disposition. Candidate
set equality and rematerialized source fingerprints are hard gates. Both
`P_emit` and `P_route` must contain zero retired-ID members before Phase 8;
`P_route` is not an allowed holding area for obsolete decision logic.

The production constructor surface is split before cutover:

- the strict production constructor rejects all eight retired IDs;
- the lossless legacy decoder preserves the raw ID/payload without calling the
  production constructor;
- a typed result projection may expose only a reason ID already present in the
  verified finalization bundle and binds occurrence ID, cause ID, reason ID,
  result occurrence ID, source snapshots, event/stream digests, semantic and
  lifecycle projection digests, registry ID/version/digest, and projection
  schema;
- a producer may not translate an umbrella into a typed ID by inspecting a
  rendered message, timeout status, strategy name, or fallback position.

The projection is compatibility data, not a second cause issuer. The projection
factory consumes the verified finalization bundle: its sealed event stream and
verified lifecycle projection. It joins exactly one active `CAUSE_OBSERVED`
event by result occurrence ID, occurrence ID, cause ID, and reason ID, and issues
a factory-owned projection receipt only after validating all bound digests and
source snapshots. A directly constructed or codec-reconstructed
`CauseOccurrenceAuthority` is data only and cannot issue projection authority.
The receipt is validated against the issuing factory ledger as well as by value.
Its exact occurrence join is mandatory, and its reason ID must equal the joined
occurrence reason. Missing, inactive, superseded, cross-result, cross-stream,
wrong-source, digest-mismatched, ambiguous, copied, or decoder-only joins fail
closed and cannot fall back to `unknown`.
Production routing that still needs a reason category must use sealed v2
`ReasonDefinition` fields or the typed occurrence; it may not compare a retired
ID.

Each umbrella producer is cut over through its owning Phase 6 domain encoder:

- unresolved expression/call/effect sites use the exact slice 6.3 classified
  cause;
- SAT safety sites use the exact slice 6.1 gate cause;
- outcome sites use the exact slice 6.2 stage/status cause;
- loop/recurrence sites use the exact slice 6.4 classified cause;
- ABI/readonly sites use the exact slice 6.5 classified cause;
- solver/process timeout sites emit only execution events and project a reason
  only from an independently active semantic occurrence;
- internal exceptions use the operational `ERROR` path and never manufacture a
  semantic cause.

For a timeout, no replacement reason is selected from the timeout itself. The
decision finalizer consumes the terminal execution receipt; compatibility
reporting may list independently active semantic causes by their own IDs. A
timeout with no live semantic requirement is INVALID rather than a fabricated
UNKNOWN cause. The terminal timeout receipt must bind the execution's exact,
nonempty, canonically ordered assignment tuple. Every assigned requirement must
join an exact final `Q_open_base` row in the live frontier and that row's matching
active `C_active_base` occurrence/result. Missing, extra, duplicate, inactive,
or reordered assignments invalidate the receipt; the existence of an unrelated
live requirement is insufficient.

Coverage is rooted in producer activation authority, independently of whether a
cause was emitted:

```text
E_discovered = all audited in-scope production branch/attempt activations
E_eligible = expected cause-slot rows whose sealed disposition requires a semantic cause
E_decisive = explicitly decisive activation rows
E_operational_error_no_semantic_cause = explicitly operational ERROR rows
E_legacy = explicitly legacy-only activation rows

E_discovered =
  E_eligible ⊎ E_decisive ⊎ E_operational_error_no_semantic_cause ⊎ E_legacy

E_prod row = (
  activation_id,
  result_occurrence_id,
  domain,
  producer_site_manifest_id,
  producer_source_fingerprint,
  branch_or_attempt_id,
  activation_ledger_id,
  activation_ledger_digest,
  expected_disposition,
  expected_cause_slot_id,
  activation_authority_digest
)
```

Static producer completeness and dynamic activation authority are separate:

```text
S_site = all 24 AST-discovered, reviewed producer wrapper sites
E_discovered = factory-issued wrapper-entry activations actually reached in one run
```

`S_site` proves that every production wrapper is audited; it is not expanded
into per-run `NOT_REACHED` rows. `NOT_REACHED` is not a dynamic disposition and
cannot be caller asserted. Each wrapper records a branch-entry discovery before
encoding its signal. The discovery issuer binds result occurrence, static
manifest digest, site/source fingerprint, exact signal digest, and invocation
ordinal. Only those authorities form the run's expected activation ledger.

`E_prod` is then issued from each discovered branch/attempt authority before
cause emission. Disposition and producer/attempt identity are derived from the
sealed signal/occurrence authority and site contract, never from a caller
selection map or from the absence of an occurrence. Every row binds membership
in an independently sealed dynamic activation ledger by ledger ID and digest.
The expected dynamic ledger may open exactly one runtime census, and exact
expected-to-runtime equality is required over `E_discovered`. Every discovered
activation has exactly one disjoint disposition row. A wrapper entry without
materialized signal intents, an emitted signal without prior discovery, unknown
producer sites, source-fingerprint drift, duplicate activation IDs, or a
disposition inconsistent with the producer contract invalidates the census.

The sealed producer contract declares a reviewed, site-exact finite cause-slot
table. It must never expand all reasons in the site's domain. Each slot binds one
exact reason, target kind, identity scope, and one of these semantics:

- `MANDATORY_CAUSE`: every such slot is required for that activation;
- `ALTERNATIVE_REASON_CHOICE`: exactly one alternative slot is selected from
  the exact factory-issued occurrence before emission.

A multi-cause activation has one `E_eligible` row per mandatory slot plus its
selected alternative, and is never collapsed to activation-level coverage.
Wrong-site reasons fail before stream emission. Slot IDs are unique within the
sealed activation ledger and producer code cannot widen the reviewed table.

```text
T_typed = E_eligible
  JOIN verified finalization bundle
  JOIN exact active factory-owned projection receipt

v2_native_typed_cause_coverage =
  |distinct covered E_eligible expected_cause_slot_id| /
  |E_eligible expected_cause_slot_id|
```

Missing, untyped, ambiguous, retired, inactive, or receiptless emissions remain
in the denominator and are uncovered. Each eligible slot must join exactly one
active projection receipt, and each receipt may cover exactly one eligible slot;
zero or multiple receipts for one slot and one receipt reused across slots are
INVALID. An occurrence may cover a slot only when its producer contract
explicitly binds that activation and slot ID; an occurrence emitted elsewhere
cannot cover it.

Before `CAUSE_OBSERVED`, the canonical runtime activation factory issues one
pre-emission binding receipt over activation/slot/site/source/producer/attempt
and the exact occurrence/cause semantic identity. The verified stream must hold
that same occurrence-authority object in its matching event. Generic recorder
append rejects `CAUSE_OBSERVED`; the finalization factory's dedicated append API
atomically consumes the still-live binding exactly once, appends the event, and
issues an emitted-cause row binding binding-receipt digest, stream/result/source,
sequence and event digest. Reuse on another recorder or finalization factory is
rejected by the activation authority root. A projection issuer
is unique per runtime activation ledger, and occurrence/event reuse is rejected
globally by `(result_occurrence_id, occurrence_id)`, not per activation.

Phase 7 manifest metrics are defined as:

```text
production_umbrella_generation = |P_emit rows whose finite reason set intersects retired IDs|
production_umbrella_routing = |P_route rows whose finite reason set intersects retired IDs|
legacy_inferred_count = count only over D_legacy/L_decode outputs
```

The coverage denominator is `E_eligible`; exclusions exist only as explicit
disjoint disposition rows in the conservation relation above. Zero denominator
is `N/A`, never `1.0`. Completion requires a nonzero denominator and coverage
`1.0` for every activated production domain as well as globally.

The 411-summary legacy baseline has its own sealed, ordered manifest. It contains
exactly 411 entries and preserves duplicate entries and discovery order. Each
entry binds a stable entry ID, ordinal, path, raw byte length, and raw SHA-256.
Validation requires exactly one decoded envelope per manifest entry, stable
ordinal/order, no drop/duplication, raw payload retention, and
`encode(decode(raw_bytes)) == raw_bytes` byte-for-byte. Every decoded envelope is
diagnostic-only. Canonical reducers/census builders reject the envelope type
rather than relying on callers to omit it.

Additional hard gates:

- `production_umbrella_generation == 0` both statically and in representative
  sealed streams/results;
- `production_umbrella_routing == 0` in production decision/routing code;
- the inventory partition and `E_discovered` disposition conservation equations
  hold exactly;
- every typed result projection joins exactly one active occurrence in the
  verified finalization bundle and is owned by the projection factory;
- no retired ID appears in a v2 reason/recovery registry or authoritative event;
- every final TIMEOUT has exactly one terminal timeout receipt and at least one
  exact nonempty assignment tuple whose every member joins a final live
  requirement plus its active cause, but no timeout-derived reason occurrence;
- every final UNKNOWN has at least one active semantic cause and no terminal
  timeout receipt;
- all 411 saved summaries round-trip byte-for-byte through `L_decode`, and their
  ordered envelopes are rejected by canonical v2 metrics;
- the Phase 7 manifest and validation output are source-hash-bound and receive a
  fixed-reviewer GO before Phase 8 starts.

### Phase 8: atomic five-value decision cutover

Cut over together:

- checker and workflow;
- fallback/retry policy;
- result serialization and rendering;
- CLI;
- matrix parser;
- batch/resume logic;
- health, UNKNOWN, and root-blocker summaries;
- shell-side process timeout handling.

`is_equivalent` remains only as a compatibility projection. At this phase:

- `strategy_exception` -> ERROR;
- `unexpected_pairwise_state` -> ERROR;
- terminal solver/process deadline -> TIMEOUT;
- semantic-model insufficiency -> typed UNKNOWN.

Gate:

- `DecisionReceipt` is the sole final-status authority;
- legacy contradiction is a validation error. This is the historical Phase-8
  cutover gate; Phase 10.3 partially supersedes it only for valid,
  non-conflicting UNKNOWN/TIMEOUT candidates under the exhaustive typed
  reconciliation table. Malformed authority, internal failure, legacy ERROR,
  and opposite decisive outcomes remain ERROR;
- retry/fallback matrix is explicit for all five outcomes;
- batch/resume distinguishes UNKNOWN and TIMEOUT;
- EQ/NOT_EQ decisive authority matches the pre-cutover implementation.

### Phase 9: current-HEAD completion evidence

Validation order:

1. registry/model/codec/reducer/finalizer unit tests;
2. reason-boundary and near-miss negative tests;
3. event mutation, replay, digest, transformation, and budget tests;
4. refactor contract;
5. representative real binaries with `./.venv-pyghidra/bin/python`;
6. domain-related matrix;
7. full six-matrix census only when milestone evidence requires it.

Repo-local final evidence:

- `current_head_manifest.json`
- `decision_receipt.json`
- `cause_lifecycle_snapshot.json`
- `query_execution_receipts.json`
- `legacy_coverage.json`
- `reason_before_after.json`
- `decision_transition_matrix.json`
- `validation_run.log`

Completion requires:

- v2 lifecycle inference is zero;
- active set is independent of final-attempt position and physical event-array order;
- implicit replacement/completion is zero;
- serializer, debug trace, and summaries share the verified lifecycle projection;
- semantic cause and proof backlog use separate identities, digests, and metrics;
- UNKNOWN/TIMEOUT canonical metrics are generated only after outcome join;
- `v2_native_typed_cause_coverage == 1.0`;
- `final_blocker_authority_coverage == 1.0`;
- required requirement materialization coverage is `1.0` or `N/A` only for a zero denominator;
- optional requirement materialization rate is reported separately and is not a completion gate;
- required-missing, optional-not-materialized, and no-proof-recovery counts are reported separately;
- production umbrella generation is zero;
- all final TIMEOUT results have a linked terminal timeout receipt;
- internal exceptions and unsupported semantics are distinct;
- EQ/NOT_EQ soundness gates and decisive receipts are unchanged;
- legacy saved summaries remain readable through the legacy diagnostic path.

### Phase 10: post-cutover return-width closure and EqBench runner correction

This phase corrects the current-head `V2_LEGACY_DECISION_CONTRADICTION`
regression without weakening any equivalence, disequivalence, return-width, or
counterexample-safety proof gate. It is one reviewed change unit with ordered
slices; removing the blanket contradiction canary before the typed completion
and C/Q-preservation slices are proven is forbidden.

#### 10.0 Freeze the regression and authority inventory

Before editing production behavior:

1. Save a current-head supervisor-backed reproduction for
   `CLEVER/Comp/Eq/newV/foo B1_B2`, including the source/binary hashes, command,
   human log, canonical result payload, DecisionReceipt, supervisor projection,
   child return code, `C_active_base`, and `Q_open_base`.
2. Record separately:
   - the verified base comparison closure and its exact comparison receipt;
   - every return-width cause observation and proof requirement;
   - every completion artifact and completion receipt;
   - the legacy diagnostic outcome;
   - the pre-reconciliation v2 candidate outcome;
   - the final published outcome.
3. Inventory every production producer of
   `return_width_provenance_unavailable`,
   `return_width_relation_unproven`,
   `return_abi_provenance_unavailable`,
   `return_observation_contract_unproven`,
   `return_high_bit_relation_unproven`, and
   `return_abi_relation_unproven`, including the direct producer in
   `return_width_surface.py` and the pairwise producer in
   `strategies/pairwise_services/orchestration_1.py`.
4. Inventory every production caller of
   `complete_return_width_provenance()`,
   `complete_same_function_return_width_relation()`,
   `complete_return_abi_provenance()`,
   `complete_return_abi_relation()`,
   `complete_return_high_bit_relation()`, and
   `complete_return_observation_contract()`. A unit-test-only caller counts as
   missing production wiring, not coverage.
5. Inventory both seed outcomes at every production adapter:
   `ReturnObservationNeedSeed` when no positive common observation width is
   formable, and `ReturnObservationProjectionSeed` when the exact pair seed has
   a positive projection. Record every `ProjectionNotFormable` transition and
   prove that it cannot silently fall into the projection DAG.
6. Inventory every canonical-result serialization and supervisor persistence
   boundary, including `EquivalenceResult.to_dict()`, result-file writers,
   `SupervisorChildExitReceipt`, supervisor state/checkpoint stores, timeout
   and error bundle stores, and `supervisor-projection.json`. Record which
   boundary currently persists each replay input rather than assuming a digest
   can reconstruct an authority that was never serialized.

The frozen evidence is diagnostic baseline only. Historical pre-cutover logs
and the Phase-8 EqBench dry run are not current-head behavioral evidence.

Gate:

- the reproduction is current-source/current-binary bound;
- the legacy, candidate, and published outcomes are not conflated;
- producer multiplicity and missing production completion edges are explicit;
- no implementation begins from a human-log-only diagnosis.

#### 10.1 Establish one canonical return-observation producer

The canonical semantic owner is the typed ABI/width surface in
`equivalence/v2/abi_width_readonly.py`, reached through one production adapter
at the return-observation contract boundary. Pairwise orchestration may consume
the resulting structured seed/view, but must not independently reconstruct and
emit the same semantic causes.

The canonical adapter has two disjoint, factory-selected paths. Callers cannot
select the path from a reason string or retry state.

```text
pair semantic seed
  -> ReturnObservationNeedSeed
       -> observation-contract C/Q only
       -> no solver candidate and no synthetic projection
       -> UNKNOWN until new positive width authority exists

pair semantic seed
  -> ReturnObservationProjectionSeed
  -> required unary ABI provenance requirements
  -> return ABI relation requirement
  -> high-bit relation requirement
  -> observation contract requirement
```

`ReturnObservationNeedSeed` is the canonical result when declared widths do not
agree, validated payload widths do not agree, required extension evidence is
missing, or `ReturnObservationProjectionSeed.from_pair_seed()` raises
`ProjectionNotFormable`. Its observation-contract cause and requirement remain
live. It cannot create an ABI-relation/high-bit solver candidate and cannot be
completed merely because a later retry rendered a different width string.

If new object-derived positive width authority becomes available in the same
result occurrence, a factory-owned atomic lifecycle transformation must:

1. bind the exact NeedSeed occurrence, live C/Q, new unary width artifacts, and
   resulting ProjectionSeed;
2. complete the NeedSeed observation requirement;
3. observe the ProjectionSeed DAG causes and requirements;
4. record one N-to-M transformation receipt so no gap or double-live semantic
   cause exists.

Without that exact transformation, the NeedSeed path remains UNKNOWN. The
ProjectionSeed path alone may enter the ABI/high-bit completion DAG.

Each semantic cause has one factory-owned occurrence and one live requirement.
The same seed/reason emitted twice, emission from the removed orchestration
path, a different seed under the same occurrence, or a solver candidate without
its canonical cause observation is INVALID. Producer activation/cause-slot
manifests must be refreshed from the surviving site rather than preserving a
deleted site as a compatibility alias.

Deletion in this slice is limited to:

- the duplicate pairwise return-width blocker-emission branch;
- adapters and imports used only by that duplicate branch;
- manifest rows made obsolete by the removed producer, after inventory proves
  that they have no other production consumer.

Do not delete `_run_legacy_check_from_binaries` or the current analysis engine.
It still creates the Ghidra analysis, structured comparison surfaces, and
verified comparison receipts consumed by v2.

Gate:

- exactly one production activation exists per canonical seed/reason;
- NeedSeed and ProjectionSeed activations are disjoint and conserve every
  adapter invocation;
- NeedSeed cannot schedule high-bit work or become EQ without a positive-width
  transformation receipt;
- wrong-site, duplicate, replayed, and seed-drift emissions fail closed;
- pairwise and monolithic/replay consumers either consume the canonical surface
  or retain an explicit conservative fallback;
- no result changes are accepted in this slice solely because a producer was
  removed.

#### 10.2 Complete the typed return-width proof DAG in production

Production must drive the following dependency graph to a fixed point before
candidate finalization:

```text
left/right object-derived width and ABI facts
  -> ReturnWidthProvenanceArtifact(s), when required
  -> SameFunctionReturnWidthRelationArtifact(s), when required
  -> ReturnAbiProvenanceArtifact(s)
  -> ReturnAbiRelationArtifact
  -> return ABI relation REQUIREMENT_COMPLETED
  -> high-bit structural theorem or receipt-bound solver query
       UNSAT -> ReturnHighBitRelationProofArtifact
                -> high-bit REQUIREMENT_COMPLETED
       SAT   -> model-bound refutation
                -> factory-owned CauseTransformed
                   old high-bit C/Q retired
                   new counterexample-safety C/Q observed
                -> safe counterexample proof
                   complete -> NOT_EQ authority
                   incomplete -> retain transformed C/Q
       UNKNOWN/TIMEOUT/ERROR -> keep the exact high-bit C/Q live
  -> ReturnObservationContractArtifact
       identity projection: no fabricated high-bit dependency
       non-identity projection: exact high-bit artifact dependency required
  -> observation-contract REQUIREMENT_COMPLETED
```

`complete_return_width_provenance()`,
`complete_same_function_return_width_relation()`,
`complete_return_abi_provenance()`,
`complete_return_abi_relation()`,
`complete_return_high_bit_relation()`, and
`complete_return_observation_contract()` must be invoked by production code
only with exact factory-issued artifacts bound to the current result,
projection seed, prepared snapshot, active occurrence, and live requirement.
Completion order is dependency order; chronology alone never proves a
dependency. Missing Ghidra facts, unformable projection, SAT without safe
counterexample authority, solver UNKNOWN/TIMEOUT, source drift, or any receipt
join failure leaves the corresponding `C_active_base`/`Q_open_base` rows live.

A receipt-bound SAT result does not complete the high-bit requirement and does
not itself authorize `NOT_EQ`. The SAT lane must use one atomic, factory-owned
N-to-M lifecycle transformation that binds the exact high-bit cause and live
requirement, solver-query receipt, formula digest, SAT model/refutation receipt,
and newly issued counterexample-safety cause/requirement. On commit it emits a
typed `CauseTransformed` receipt, retires the original high-bit C/Q, and makes
the counterexample-safety C/Q live without any gap or double-live interval. If
the transformation cannot validate or commit, the original high-bit C/Q stays
live and no successor cause or decisive authority is published.

Only an exact safe-counterexample proof may complete the transformed C/Q and
issue `NOT_EQ` authority. An incomplete or inconclusive safety proof retains
the transformed C/Q; the eventual DecisionFinalizer, not this transformation,
decides whether the overall result is UNKNOWN, TIMEOUT, or ERROR in the
presence of other terminal authority.

The current `stage_runner.py` behavior that immediately issues and emits
`EQ_CLOSURE` when a strategy returns EQ must be replaced. Before dispatch-frame
cleanup, the stage runner validates the exact comparison receipt/frame/session
join and asks one factory to issue a typed `PendingEqClosureAuthority`. It emits
no `EQ_CLOSURE` event at that point.

The pending authority is an issuer-owned, one-shot lifecycle object and receipt
ledger entry. It binds at least:

```text
result_occurrence_id
execution_identity_digest
comparison_receipt_id and exact receipt authority digest
comparison_session_id, branch_id, generation
dispatch-frame authority digest
base runtime view_id and premise digest
dispatch cleanup/successor binding needed for post-cleanup replay
pending authority nonce and receipt digest
state: PENDING | CONSUMED | DISCARDED
```

Issuance must seal immutable authority sufficient to revalidate the comparison
after the mutable dispatch frame has been cleaned up. Retaining an object
reference to the old frame or reconstructing authority from diagnostic
provenance is insufficient.

After all domain encoders have driven their proof DAGs to a fixed point and a
fresh verified lifecycle projection exists, one terminal pending-authority
finalizer performs exactly one transition:

- consume the exact pending authority through the existing EQ-closure
  issuer/encoder boundary and emit `EQ_CLOSURE` only if the base comparison
  authority revalidates, no blocking C/Q remains, and the verified terminal
  candidate view contains no safe-counterexample candidate, terminal-timeout
  candidate, ERROR authority, or competing decisive authority;
- otherwise issue a typed discard receipt bound to the pre-closure projection
  and terminal candidate view, destroy the one-shot capability, and emit no EQ
  event. Discard is outcome-neutral: it removes only the unpromoted EQ
  capability and never publishes or implies UNKNOWN;
- if replay, cleanup, receipt, view, or ownership validation fails, emit a
  canonical authority ERROR rather than EQ or UNKNOWN.

Before this transition, every timeout-capable encoder must freeze its open
terminal-timeout candidates in a typed resolver ledger included in the
verified terminal candidate view. This preview does not terminalize TIMEOUT,
but prevents pending EQ consumption when the post-seal timeout resolver can
later bind a terminal timeout. Safe-counterexample, ERROR, and other decisive
candidates are likewise exact-type and receipt gated; diagnostic flags do not
participate. The post-seal resolver may bind only candidates in that frozen
ledger; a newly appearing, omitted, replaced, or foreign timeout candidate is
an authority ERROR, never grounds for retaining an already emitted EQ.

`connector.finish()` must preserve this exact order:

```text
close/finalize every domain proof encoder to a fixed point
  -> build and verify a fresh pre-closure lifecycle projection
     plus the frozen terminal candidate view
  -> terminally consume or discard PendingEqClosureAuthority
  -> if consumed, issue and encode the one EQ_CLOSURE event
  -> seal the production stream
  -> resolve and bind terminal timeout candidates against that sealed stream
  -> replay/reduce the sealed stream plus terminalizations
  -> DecisionFinalizer alone chooses EQ/NOT_EQ/UNKNOWN/TIMEOUT/ERROR
  -> build the final DecisionReceipt
```

The pre-closure projection is used only to authorize that one terminal
transition; it is not the published final projection. After an EQ event is
issued, the sealed stream must be replayed again so the final projection and
DecisionReceipt include that exact event. No reducer or candidate builder may
observe an intermediate stream and later reuse it as final authority.
Discarded pending EQ authority is recorded as lifecycle evidence only; it is
not a decision event and is not an input that biases the DecisionFinalizer
toward UNKNOWN.

The session cannot seal while any pending EQ authority is live. Copied, stale,
foreign-session, replayed, already-consumed, already-discarded, or
post-cleanup-unverifiable pending authorities are rejected.

The existing verified base comparison closure is therefore retained as a
nonterminal pending authority while typed requirements remain open. It is
promoted only after a fresh verified projection proves:

```text
C_active_base has no row that blocks equivalence
AND
Q_open_base has no live requirement for such a row
AND
the base comparison receipt still validates against the final runtime view
AND
there is no safe-counterexample candidate
AND
there is no terminal-timeout candidate
AND
there is no ERROR authority
AND
there is no competing decisive authority
```

No caller may synthesize or unconditionally emit a new `EQ_CLOSURE`. If any
consume condition fails, the pending authority is explicitly discarded and no
decisive EQ event is emitted. The sealed stream, terminalizations, completed
counterexample-safety proofs, ERROR receipts, and other decisive authorities
remain intact so the DecisionFinalizer can independently return UNKNOWN,
TIMEOUT, NOT_EQ, or ERROR. A completed proof must close v2 C/Q; removing a
legacy diagnostic string is neither completion authority nor an acceptance
criterion.

Gate:

- unit tests prove every DAG edge and dependency digest;
- completion without a live C/Q row, out-of-order completion, foreign artifact,
  stale projection, copied receipt, and duplicate completion are rejected;
- stage completion emits no immediate EQ event; pending issuance, final
  consumption, and final discard are separately tested;
- dispatch cleanup cannot invalidate a legitimately sealed pending authority,
  while copied/stale/replayed pending authority is rejected;
- session sealing rejects every unconsumed and undiscarded pending authority;
- UNSAT is the only solver status that completes the high-bit requirement;
- SAT atomically transforms the original high-bit C/Q into exact
  counterexample-safety C/Q; successful transformation retires the old cause,
  creates the new cause, and never leaves both live after commit;
- transformation failure leaves only the original high-bit C/Q live, while
  SAT alone can neither complete it nor directly become `NOT_EQ`;
- only completed safe-counterexample proof closes the transformed C/Q and
  issues NOT_EQ; incomplete proof retains the transformed C/Q;
- pending-EQ discard is outcome-neutral, and fixtures prove that terminal
  timeout, safe counterexample, ERROR, and competing decisive candidates
  prevent EQ consumption without being rewritten to UNKNOWN;
- post-seal terminal-timeout binding precedes final replay and decision;
- a provable fixture closes all relevant C/Q before the existing verified base
  closure becomes final EQ;
- an unprovable near-miss retains nonempty blocking C/Q and finishes UNKNOWN;
- no proof gate or observation width is weakened to recover EQ.

#### 10.3 Replace blanket contradiction handling with typed reconciliation

After 10.1 and 10.2 pass, replace the blanket
`decision_delta -> V2_LEGACY_DECISION_CONTRADICTION -> ERROR` canary with an
exact, exhaustively tested reconciliation policy. The v2 candidate
DecisionReceipt and verified lifecycle projection are authoritative; the
legacy outcome is a compatibility diagnostic, except that opposite decisive
outcomes remain a fail-closed migration conflict.

Required policy for results that reach `connector.finish()` without a legacy
ERROR:

| Legacy diagnostic | Valid v2 candidate | Published result |
|---|---|---|
| EQ or NOT_EQ | UNKNOWN | candidate UNKNOWN with its exact C/Q |
| EQ or NOT_EQ | TIMEOUT | candidate TIMEOUT with terminal receipt and live C/Q |
| decisive | same decisive | candidate receipt |
| EQ | NOT_EQ | `DECISIVE_OUTCOME_DISAGREEMENT` ERROR for this phase |
| NOT_EQ | EQ | `DECISIVE_OUTCOME_DISAGREEMENT` ERROR for this phase |
| any | malformed/foreign/tampered authority | ERROR |
| any | canonical internal/strategy exception | ERROR |
| UNKNOWN or TIMEOUT | valid non-conflicting candidate | candidate receipt |

Phase 10 does not introduce a compatibility-only diagnostic ERROR class.
Therefore every legacy `error_message` continues to take the early canonical
ERROR path before `connector.finish()`. Strategy/internal exceptions,
function/decompilation failures, compatibility-shaped errors, and authority
errors cannot be distinguished by prose and cannot be overwritten by candidate
EQ/NOT_EQ/UNKNOWN/TIMEOUT. A future relaxation requires a separately reviewed,
factory-issued, sealed exact error type and receipt; string labels or
`failure_status` aliases are insufficient.

This is a pre-reconciliation boundary, not another candidate-matrix cell:

| Legacy boundary state | Candidate handling | Published result |
|---|---|---|
| ERROR of any legacy class | do not call `connector.finish()` and do not reconcile a candidate | preserve canonical ERROR |

Opposite decisive outcomes may become a typed disagreement UNKNOWN only in a
separately reviewed extension that observes a factory-owned disagreement cause
before final projection and binds a live requirement. This phase must not
fabricate that cause after candidate finalization.

Canonical relations are attached whenever the published result uses a valid
candidate receipt, including UNKNOWN and TIMEOUT. They must not be suppressed
merely because the legacy diagnostic differs. The serialized
`c_active_base`/`q_open_base` must equal the candidate projection; rendering or
compatibility fields cannot replace, clear, or reconstruct them. ERROR caused
by invalid authority must not publish fabricated canonical C/Q.

Only after the table is the sole production reconciliation path may the old
generic contradiction canary and dual-write-only diagnostics with no remaining
consumer be removed. Deletion requires an import/caller/artifact inventory and
negative tests; the legacy analysis body remains in scope and is retained.

This slice explicitly updates the historical Phase-8 expectation rather than
silently changing it. Its implementation/review scope includes:

- `production_boundary.py` and the typed reconciliation policy;
- Phase-8 cutover and production-boundary tests, including the complete legacy
  diagnostic by candidate matrix;
- Phase-8 validation artifact builders/validators and their source maps;
- canonical result/summary fixtures whose expected contradiction ERROR becomes
  a valid UNKNOWN or TIMEOUT;
- negative fixtures that prove legacy ERROR and opposite decisive outcomes
  remain ERROR.

Gate:

- every reachable legacy-by-candidate matrix cell is tested, and the legacy
  ERROR pre-reconciliation bypass is tested separately;
- valid UNKNOWN/TIMEOUT disagreement preserves the exact candidate receipt and
  C/Q digests through JSON, CLI, summary, and replay;
- opposite decisive outcomes remain explicit ERROR rather than silently
  preferring either side;
- every legacy ERROR bypasses candidate reconciliation and remains canonical
  ERROR unless a future exact typed compatibility-error authority is approved;
- malformed receipts, authority drift, and internal exceptions remain ERROR;
- refreshed Phase-8 tests and validation artifacts explicitly encode the
  partially superseded contradiction gate;
- no `V2_LEGACY_DECISION_CONTRADICTION` is emitted for a valid non-conflicting
  candidate.

#### 10.4 Make EqBench runner outcomes and failures structural

The runner must classify a pair from the canonical result payload together
with a verified `supervisor-projection.json`; human `Result:` lines and grep are
diagnostics only. Introduce one structured pair-status projection containing at
least:

```text
canonical_outcome
decision_receipt_digest
result_occurrence_id
result-entry occurrence receipt digest
execution_nonce
stream_id
source_snapshot_fingerprint
launch_receipt_digest
canonical_result_bundle_digest
canonical_result_bundle_kind
supervisor_final_authority_digest
supervisor_authority_kind
semantic_projection_digest
error_kind
child_returncode
supervisor_status
supervisor_projection_digest
classification_valid
```

The current result JSON is not sufficient for this verification. Phase 10.4
must introduce and atomically persist one exact-type
`CanonicalResultFinalizationBundle` containing the material required for
independent replay, not merely its digests:

```text
schema/version and exact bundle authority kind
execution identity and result-entry occurrence receipt
sealed canonical event stream plus its digest
terminalization records and terminal timeout receipt, when present
final VerifiedLifecycleProjection plus its authority/receipt
all decisive EQ or safe-counterexample proof receipts required by the outcome
ErrorReceipt with sealed error_kind for ERROR, including early legacy ERROR
final DecisionReceipt
canonical result payload-preimage digest
CanonicalSemanticResultProjection payload and digest
bundle digest and factory signature/seal
```

Outcome-inapplicable receipt slots are exactly null; omitting a required slot,
supplying an extra conflicting decisive receipt, or storing only a diagnostic
rendering is invalid. The serialized event stream, terminalizations,
projection, and receipts must be sufficient to rerun the reducer and
DecisionFinalizer and reproduce the embedded DecisionReceipt. A digest alone
cannot stand in for missing replay material.

Serialization must avoid a self-referential digest. First create a
schema-versioned canonical result payload preimage that excludes only the
outer bundle locator/digest fields, then bind its digest into the bundle. The
final result envelope stores that unchanged payload plus the bundle locator
and bundle digest. The bundle digest covers the payload-preimage digest and
all replay authorities; validators reject any noncanonical exclusion or
post-bundle payload mutation.

Early legacy ERROR takes no candidate reconciliation path, but it is not exempt
from durable authority. Its originating typed error boundary must issue an
exact `ErrorReceipt`; an error finalization factory seals the available stream,
projection/terminal material, ERROR DecisionReceipt, and that receipt into a
`CanonicalResultFinalizationBundle`. `error_kind` is taken only from the sealed
receipt. Missing typed error authority is itself a fail-closed canonical error
finalization failure and must never be repaired by parsing `error_message`.

The canonical bundle is written atomically alongside the result envelope and
is part of the result-output contract implemented by `result.py` and its
writers. Durable supervisor timeout/error finalizers must also create or adopt
the exact canonical bundle and bind it to their existing supervisor-owned
finalization authority. Cleanup must not remove bundle inputs before the
runner has rematerialized and verified them.

The pair-status projection is issued only after rematerializing and
independently validating the launch receipt, canonical finalization bundle,
result-entry occurrence receipt, exact supervisor final authority, supervisor
projection, and canonical DecisionReceipt. Field presence is not a join. The
verifier requires:

```text
DecisionReceipt.result_occurrence_id
  == result-entry occurrence authority.result_entry_occurrence_id
  == launch receipt.result_occurrence_id

supervisor_projection.launch_receipt_digest
  == verified launch receipt.receipt_digest

supervisor_projection.canonical_result_bundle_digest
  == verified CanonicalResultFinalizationBundle.bundle_digest

canonical result payload.bundle_digest
  == verified CanonicalResultFinalizationBundle.bundle_digest

CanonicalResultFinalizationBundle.canonical_result_payload_preimage_digest
  == independently rebuilt canonical payload-preimage digest

execution_nonce, stream_id, source_snapshot_fingerprint
  == the exact values bound by launch, production execution identity,
     result-entry authority/execution-payload digest, canonical bundle,
     and DecisionReceipt

supervisor_projection.supervisor_final_authority_digest
  == digest of the exact rematerialized supervisor final authority

supervisor_projection.supervisor_authority_kind
  == exact runtime type/receipt kind of that supervisor authority

supervisor_projection.canonical_result_bundle_kind
  == exact runtime type/receipt kind of the rematerialized canonical bundle
```

The result-entry occurrence receipt's execution-payload digest must be
independently reconstructed from the canonical result identity; matching only
its occurrence ID is insufficient. Any missing join, digest drift, duplicate
candidate authority, or self-consistent foreign launch/result pair makes the
pair status invalid.

Supervisor disposition is outcome-aware and exact-type gated:

- normal resolved-child execution accepts only a new exact
  `SupervisorCanonicalResultResolvedReceipt` issued after the supervisor has
  read and verified the child's canonical result envelope and
  `CanonicalResultFinalizationBundle`. It binds the launch receipt digest,
  result occurrence and execution identity, child return code, canonical
  bundle digest, payload-preimage digest, and DecisionReceipt digest. Its
  `child_returncode` must equal `CLI_EXIT_MATRIX[canonical_outcome]`;
- the existing `SupervisorChildExitReceipt` may prove only that a launched
  process exited. Without the new resolved receipt and bound canonical bundle,
  it is never accepted as canonical-result RESOLVED authority, even when the
  child return code is zero;
- durable process TIMEOUT accepts only a rematerialized
  `DurableTimeoutFinalizationBundle` whose terminal timeout receipt, stream,
  assignment, final C/Q, DecisionReceipt, and canonical result bundle all
  join. Signal/kill exit codes are validated under the timeout disposition
  contract and are never compared as ordinary CLI exits;
- durable supervisor ERROR accepts only a rematerialized
  `DurableErrorFinalizationBundle` whose sealed `error_kind`, terminal error
  event, stream, ERROR DecisionReceipt, and canonical result bundle join;
- an authority kind or supervisor status not allowed for the canonical outcome
  is invalid even if its digests are internally self-consistent.

For canonical ERROR, sealed `error_kind` is mandatory and is taken from the
verified ERROR authority/DecisionReceipt join. For every non-ERROR outcome,
`error_kind` is exactly null. `error_message` may be retained as a separate
diagnostic field but is never an authority field or aggregation key.

This slice's implementation scope therefore includes `result.py` and every
canonical result writer/reader, canonical bundle factories and validators,
production-boundary early-error finalization, supervisor factories/stores and
recovery, `process_supervisor_command.py`, supervisor projection schemas, and
runner classification. Updating only the shell runner or projection parser is
insufficient.

`run_pair()` returns nonzero for canonical ERROR, INCOMPLETE/missing canonical
payload, invalid or missing supervisor projection, receipt/projection mismatch,
and unclassifiable output. It returns zero for valid EQ, NOT_EQ, UNKNOWN, and
TIMEOUT. A supervisor exit of zero must not hide a recorded child exit or a
canonical ERROR. The parent `wait -n` path remains the sole increment owner for
`RUN_PAIR_FAILURES`, so background subshells do not attempt to mutate the parent
counter.

At completion the manifest and health summary record counts by canonical
outcome, `error_kind`, child return code, and supervisor status. The script
itself exits nonzero when `RUN_PAIR_FAILURES > 0` after installing its summaries
atomically. Documentation for piped invocation must require `set -o pipefail`
when the caller needs the pipeline exit status.

Remove forced debug mode. Build the CLI argument array without `-d` by default
and add it only when `EQBENCH_DEBUG=1`. Debug selection must not change semantic
arguments or result classification.

Debug equivalence is not tested by removing fields from an already computed
cryptographic digest. Define a separately factory-built, schema-versioned
`CanonicalSemanticResultProjection`. During production, its factory derives
the projection from the already validated final replay inputs before bundle
sealing and stores both its canonical payload and digest in the bundle. During
verification, the validator first validates the complete bundle, then
independently reconstructs this projection and requires an exact payload and
digest match. Its closed normalization schema excludes only enumerated
nonsemantic execution fields (`result_occurrence_id`, execution nonce, stream
ID, process IDs, timestamps, launch/supervisor receipt identities, and outer
bundle/receipt digests). It retains source/binary/function fingerprints,
canonical outcome, normalized C/Q semantic identities, proof-formula and model
semantics, decisive proof kind, terminal outcome semantics, and sealed
`error_kind`. Its own `semantic_projection_digest` is persisted in the bundle
and pair-status projection.

Debug on/off runs may have different full DecisionReceipt and bundle digests;
both full authorities must validate independently. The regression compares
their canonical semantic projection payloads and digests. No verifier may
claim equality by applying an ad hoc field subtraction to either full digest,
and any field not explicitly excluded by the versioned schema remains
semantic.

Gate:

- child 4/supervisor 0/canonical ERROR increments failure count;
- normal resolved-child outcomes reject every child return code that differs
  from `CLI_EXIT_MATRIX`, while durable timeout kill/signal codes use only the
  timeout-specific rule;
- result/entry/launch identity mismatch, foreign self-consistent authority,
  canonical payload/bundle mismatch, missing replay material, supervisor
  final-authority drift, and wrong authority-kind/outcome combinations
  increment failure count;
- bundle-less `SupervisorChildExitReceipt` is never canonical RESOLVED;
- independently replaying the persisted stream plus terminalizations reproduces
  the bundle's projection and DecisionReceipt for EQ, NOT_EQ, UNKNOWN, TIMEOUT,
  ordinary ERROR, and early legacy ERROR;
- canonical ERROR without a sealed `error_kind`, or non-ERROR with a non-null
  `error_kind`, is invalid;
- invalid supervisor projection and missing result payload increment it;
- valid UNKNOWN and TIMEOUT do not count as runner infrastructure failures;
- final script and piped-command exit behavior are tested;
- debug on/off full bundles validate independently and produce identical
  versioned `CanonicalSemanticResultProjection` payloads and digests; full
  authority digests are never compared modulo fields;
- status output includes structured `error_kind` and child return code without
  parsing diagnostic prose.

#### 10.5 Layered regression and EqBench acceptance

Validation order is mandatory:

1. focused unit tests for NeedSeed/ProjectionSeed conservation, unary and
   relational producer uniqueness, proof-DAG completion, high-bit-SAT
   cause transformation, pending-EQ issue/consume/outcome-neutral-discard
   lifecycle, post-seal timeout terminalization, reconciliation, C/Q
   serialization, canonical bundle replay, result-entry/launch/finalization
   joins, supervisor projection, semantic debug projection, and runner failure
   counting;
2. the Phase-8 decision/cutover and Phase-6 ABI/width suites;
3. `compileall`, `env PYTHONPATH=. ./.venv-pyghidra/bin/python
   scripts/function_tracer_pcode/validation/refactor_contract.py`, and
   `git diff --check`;
4. the full unit suite;
5. current-head supervisor-backed real binaries using
   `./.venv-pyghidra/bin/python`;
6. the affected return-width category matrix;
7. full EqBench only after all narrower gates pass.

The real-binary manifest must cover at least:

- narrowed `int` return, same ABI: ARM clang, ARM GCC, MIPS clang, MIPS GCC;
- representative ARM/MIPS cross-ABI pairs;
- a provable high-bit relation that reaches EQ only after complete typed C/Q
  closure;
- an unprovable or SAT near-miss that remains UNKNOWN or follows validated
  counterexample safety, never false EQ;
- a SAT high-bit case whose original C/Q is atomically replaced by
  counterexample-safety C/Q, including both incomplete-UNKNOWN and
  safe-proof-NOT_EQ variants;
- pending EQ combined separately with terminal timeout, safe counterexample,
  ERROR, and competing decisive authority, proving discard is neutral and the
  DecisionFinalizer preserves TIMEOUT/NOT_EQ/ERROR precedence;
- an injected opposite-decisive reconciliation conflict;
- a NeedSeed case with no positive-width transformation that remains UNKNOWN;
- child 4 / supervisor 0 / runner-failure accounting, plus normal-exit,
  durable-timeout, durable-error, early-legacy-error, and bundle-bound resolved
  authority-kind joins;

Use the actual available B IDs discovered from the fixture tree and bind every
selection to source and binary hashes. `CLEVER/Comp/foo B1_B2` is required but
is not sufficient. Run the complete `CLEVER/Comp` function matrix plus at least
one independently selected narrowed-return category before the full census.

Full-EqBench evidence reports outcomes and ERRORs by `error_kind`, function,
ABI/compiler stratum, and pair. Completion does not require hiding legitimate
ERRORs; it requires:

- zero unexpected `V2_LEGACY_DECISION_CONTRADICTION`;
- zero invalid/missing canonical bundles or supervisor projections;
- zero live pending-EQ authorities at session seal, with every pending authority
  exactly consumed or discarded;
- every remaining ERROR explained by typed current-head evidence;
- every canonical outcome independently replayable from its durable
  `CanonicalResultFinalizationBundle`, with resolved supervisor authority bound
  to the exact bundle digest;
- every published UNKNOWN/TIMEOUT retaining valid canonical C/Q and receipts;
- every recovered EQ carrying the original verified base comparison closure
  plus the complete return-width dependency chain;
- no EQ/NOT_EQ soundness regression in the selected matrices or full census;
- repo-local signed JSON publication manifest, receipts, verified pair-status
  census, runner health summary, public verification keys, selected input
  source/binaries, and source hashes sufficient for independent replay. Raw
  `.log` and `.txt` files are diagnostic only and are not canonical completion
  dependencies.

Publication evidence uses the exact target source-file set and content digest
as its canonical source identity. `HEAD`, base commit and dirty-patch hashes may
be retained only as non-canonical history; committing unchanged source and
evidence must not invalidate Phase-9 or Phase-10 reconstruction. Matrix
execution receipts record the normalized executable command and runner's actual
final exit status. A nonzero runner status is signed but is ineligible for a
green completion root. Publication uses an exact path/SHA-256 allowlist; broad
staging of the Phase-10 directory and publication of `.process-authority`, raw
logs, text summaries, or private keys are prohibited. The root, Phase-6 and
Phase-9 validators must pass from a clean checkout containing only the intended
source/evidence files plus the allowlisted Phase-10 artifacts.

EqBench execution authority is scope-typed. `REPRESENTATIVE` evidence may use
filters or a bounded sample count and is permanently ineligible for Phase-10
completion. `FULL_EQBENCH` requires `EQBENCH_MAX_SAMPLES=0`, empty sample and
pair filters, and exact equality with the frozen 147-source / 411-function /
49,320-pair expectation in `validation/eqbench_full_scope.json`. Full execution
uses `REUSE_OR_COMPILE` by default: an existing B1..B16 set is reused only when
a valid `FRESH_COMPILE` build receipt binds the current source SHA-256, compile
script SHA-256 and argv, toolchain executable/version identities, all 16 typed
arch/compiler/optimization axes, and every binary SHA-256. Missing or drifted
authority falls back to a fresh compile; `PREBUILT_ONLY` fails closed instead.
An `ADOPTED_PREBUILT` receipt may support bounded representative evidence but
is permanently ineligible for `FULL_EQBENCH` completion.

Fresh compilation writes exclusively below the run temporary build directory;
it never moves, deletes, or quarantines existing B1..B16 outputs. Only after a
successful compile, 16-axis receipt materialization and validation are the new
binaries installed through per-file temporary names, with the receipt installed
last. A signal or helper failure therefore leaves the prior binaries in place;
an interrupted partial install invalidates the old receipt and forces the next
run to rebuild rather than consuming an unbound mixture. A nonzero compile exit
or missing axis schedules no analysis for that sample and produces a signed
nonzero matrix receipt with typed compile/build-authority counters.

The signed matrix publication manifest persists a normalized typed
`analysis_config`, not only an opaque digest. It includes scope, build policy,
limits and filters, debug/resume/dry-run settings, parallelism, summary level,
all equivalence/decompile/pairwise/process timeout values, kill grace, and the
full-scope expectation digest. Validators recompute `analysis_config_digest`
from this exact projection. The signed executable command records the same
operational settings so a published run can be reconstructed independently.

The publication allowlist names itself, separates normal and force-added exact
paths, and provides a staged-index validator. A publication-only evidence index
must contain exactly the allowlisted artifacts plus the allowlist JSON itself,
with identical SHA-256 content. Ignored EqBench inputs use `git add -f --` only
for the enumerated paths; historical Phase-10 attempts and checkpoints are
rejected as extra staged paths. Code and Phase-5--9 source evidence are staged
and committed separately from this publication-only evidence index; combining
them intentionally fails the exact-index gate.

Phase 10 completion remains `NO-GO` until slices 10.0 through 10.5 pass in order
and an independent read-only completion review reports no unresolved P0/P1
findings. This completion status does not revoke the implementation-start `GO`.
Unit tests or dry-run evidence alone cannot close the phase.

## 12. Progress and review workflow

For every phase:

1. Main agent reads this plan and current progress.
2. Main agent records intended files, tests, and acceptance evidence in `docs/implementation-progress.md`.
3. Main agent implements only a phase whose plan / implementation-start status
   is `GO`, and only the earliest incomplete slice in its required order. For
   Phase 10, the implementation-start `GO` authorizes slice 10.0 immediately;
   passing each slice's local gate authorizes the next slice but does not imply
   Phase-10 completion `GO`.
4. Main agent runs focused tests, then the proportionate broader validation.
5. Main agent records exact commands, results, artifact paths, and known limitations.
6. Main agent requests an independent read-only review from the fixed `plan-reviewer`.
7. Reviewer reads this plan, the current diff, progress, test evidence, and review-response ledger.
8. Reviewer returns findings and a phase GO/NO-GO; it changes no files.
9. Main agent records each finding in `docs/review-response-log.md` as accepted, rejected-with-evidence, deferred-with-gate, or resolved.
10. Main agent fixes accepted blockers and repeats tests/review.
11. Main agent marks the phase complete or advances to a later phase only after
    the completion gate and completion-review `GO` are both satisfied. This
    completion rule does not block work inside an implementation-start-`GO`
    phase under step 3.

Suggested progress states:

- `NOT_STARTED`
- `IN_PROGRESS`
- `IMPLEMENTED_PENDING_TESTS`
- `TESTED_PENDING_REVIEW`
- `CHANGES_REQUESTED`
- `PHASE_GO`
- `BLOCKED`

Review findings are ordered `P0` through `P3`. A phase cannot be `PHASE_GO` with unresolved P0/P1 findings.

## 13. Permanent prohibitions

For the entire goal:

- do not run `git add`;
- do not run `git commit`;
- do not run `git push`;
- do not create or switch branches unless the user separately authorizes it;
- do not let a reviewer or any subagent modify the workspace;
- do not mark a phase complete from chat claims or `/tmp` evidence alone;
- do not treat an INVALID or diagnostic census as canonical evidence;
- do not weaken proof gates to improve counts.
