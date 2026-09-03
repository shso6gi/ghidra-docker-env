"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.pairwise``."""

from __future__ import annotations

import hashlib
from typing import Any
from ...cause_identity import ProofRequirementContract, ProofRequirementId
from ...obligations.model import FunctionProofOutcome
from ...obligations import (
    PairClosureEvidence,
    PairClosureKind,
    PairDisposition,
    PairDispositionLedger,
    PairLedgerBinding,
    CounterexampleSafetyReceipt,
    GuardOverlapGraph,
    GuardUnsatClosureArtifact,
    SolverQueryExecutionReceipt,
    SolverUnsatClosureArtifact,
    StructuralEqualityClosureArtifact,
    StructuralEqualityReceipt,
)
from ...obligations.pair_closure_producers import (
    AggregatePartitionCandidate,
    CountedLoopClosedExpressionCandidate,
    CountedLoopValueRelationCandidate,
    MethodBClosureCandidate,
    ReadonlyIdentityCandidate,
    RuntimeReductionCandidate,
    validate_aggregate_partition_candidate,
    validate_counted_loop_closed_expression_candidate,
    validate_counted_loop_value_candidate,
    validate_method_b_candidate,
    validate_readonly_identity_candidate,
    validate_runtime_reduction_candidate,
)
from .. import pairwise as _pairwise_facade
from ._shared import (
    Condition,
    ConditionSMTOracle,
    ConditionSimplifier,
    CountedLoopSummaryRef,
    Expression,
    ExpressionSafetyChecker,
    ExpressionType,
    Mapping,
    ParameterInfo,
    SolverStatus,
    StorageInfo,
    StrategyResult,
    UnknownReasonId,
    UnknownRecoveryProofKind,
    Z3Solver,
    _MethodBCoveringCaseProof,
    _PendingLoopSummaryPair,
    align_return_value_extension_surfaces,
    build_symbol_replacer,
    build_unknown_recovery_actions,
    expression_smt_bit_width,
    infer_parameter_semantics,
    make_internal_v2_reason_diagnostic,
    make_unknown_reason,
    time,
)


def normalize_analysis_semantic_width(*args, **kwargs):
    """Preserve the documented module-level monkeypatch seam."""
    return _pairwise_facade.normalize_analysis_semantic_width(*args, **kwargs)


def validate_counterexample_across_cases(*args, **kwargs):
    """Preserve the documented module-level monkeypatch seam."""
    return _pairwise_facade.validate_counterexample_across_cases(*args, **kwargs)


def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl_check(
    self,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    save_formula: bool = False
) -> StrategyResult:
    start_time = time.time()
    from ...call_effect_preflight import (
        QueryExecutionRecord,
        consume_prepared_dispatch_frame,
        current_dispatch_depth,
        issue_builtin_comparison_receipt,
        lower_call_projection_for_case_pair,
        projection_binding_evidence_from_query,
    )

    dispatch_frame = None
    if current_dispatch_depth() > 0:
        dispatch_frame = consume_prepared_dispatch_frame(analysis1, analysis2)
        solver_analysis1 = dispatch_frame.prepared.analysis1
        solver_analysis2 = dispatch_frame.prepared.analysis2
    else:
        # Compatibility-only direct strategy invocation.  Production checker
        # dispatch always supplies a certified prepared frame.
        solver_analysis1 = normalize_analysis_semantic_width(
            analysis1,
            infer_parameter_semantics(analysis1),
        )
        solver_analysis2 = normalize_analysis_semantic_width(
            analysis2,
            infer_parameter_semantics(analysis2),
        )
        solver_analysis1, solver_analysis2 = align_return_value_extension_surfaces(
            solver_analysis1,
            solver_analysis2,
        )

    base_ctx = self.formula_builder.build_base_context(
        solver_analysis1,
        solver_analysis2,
    )
    base_ctx["analysis1"] = solver_analysis1
    base_ctx["analysis2"] = solver_analysis2
    if dispatch_frame is not None:
        base_ctx["prepared_surface_digest"] = dispatch_frame.prepared.surface_digest
        base_ctx["normalization_certificate_semantic_id"] = (
            dispatch_frame.prepared.certificate.semantic_id
        )
        base_ctx["observation_contract_digest"] = (
            dispatch_frame.prepared.certificate.observation_contract_digest
        )
    semantic_parameter_sources = self._auxiliary_semantic_parameter_sources(base_ctx)
    safety_checker = ExpressionSafetyChecker(
        solver_runner=self.solver_runner,
        debug_print=self._debug_print,
        per_query_timeout=self.per_query_timeout,
        base_ctx=base_ctx,
    )
    self._active_safety_checker = safety_checker
    sat_unsafety_reasons = self._collect_decisive_sat_unsafety_reasons(
        analysis1,
        analysis2,
    )
    equivalence_blocking_reasons = self._collect_equivalence_blocking_unsafety_reasons(
        analysis1,
        analysis2,
    )
    if dispatch_frame is not None and dispatch_frame.projection.proven:
        covered_blockers = set(dispatch_frame.projection.covered_blockers)
        equivalence_blocking_reasons = [
            reason for reason in equivalence_blocking_reasons
            if reason not in covered_blockers
        ]

    cases1 = self._extract_return_cases(solver_analysis1)
    cases2 = self._extract_return_cases(solver_analysis2)

    self._rewrite_cases_with_parameter_fragments(cases1, base_ctx.get("extra_vars1", []))
    self._rewrite_cases_with_parameter_fragments(cases2, base_ctx.get("extra_vars2", []))
    symbol_replace_fn1 = build_symbol_replacer(
        base_ctx["params1"],
        base_ctx.get("extra_vars1", []),
        float_mode="fp",
    )
    symbol_replace_fn2 = build_symbol_replacer(
        base_ctx["params2"],
        base_ctx.get("extra_vars2", []),
        float_mode="fp",
    )

    if self.debug:
        self._debug_symbol_mapping(base_ctx)

    original_case_count1 = len(cases1)
    original_case_count2 = len(cases2)
    cases1 = self._prune_unreachable_cases(
        cases1,
        base_ctx,
        symbol_replace_fn1,
        label="Case1",
    )
    cases2 = self._prune_unreachable_cases(
        cases2,
        base_ctx,
        symbol_replace_fn2,
        label="Case2",
    )
    coverage_unsafety_reasons = self._collect_return_coverage_unsafety_reasons(
        base_ctx,
        cases1,
        cases2,
        symbol_replace_fn1,
        symbol_replace_fn2,
        analysis1,
        analysis2,
    )
    sat_unsafety_reasons.extend(coverage_unsafety_reasons)
    if "function1:return_coverage_gap" in sat_unsafety_reasons:
        if "return_case_coverage_gap" not in analysis1.analysis_notes:
            analysis1.analysis_notes.append("return_case_coverage_gap")
    if "function2:return_coverage_gap" in sat_unsafety_reasons:
        if "return_case_coverage_gap" not in analysis2.analysis_notes:
            analysis2.analysis_notes.append("return_case_coverage_gap")
    if "function1:return_coverage_inconclusive" in sat_unsafety_reasons:
        if "return_case_coverage_inconclusive" not in analysis1.analysis_notes:
            analysis1.analysis_notes.append("return_case_coverage_inconclusive")
    if "function2:return_coverage_inconclusive" in sat_unsafety_reasons:
        if "return_case_coverage_inconclusive" not in analysis2.analysis_notes:
            analysis2.analysis_notes.append("return_case_coverage_inconclusive")
    total_pairs = len(cases1) * len(cases2)
    active_runtime = getattr(self, "_obligation_runtime_session", None)
    successor_plan = (
        active_runtime.pair_ledger_manager.pending_successor
        if active_runtime is not None else None
    )
    graph_generation = max(
        1, int(getattr(dispatch_frame, "generation", 1) or 1)
    )
    self._guard_overlap_graph = GuardOverlapGraph(
        tuple(getattr(getattr(active_runtime, "current_view", None), "view_id", ()) or ()),
        str(getattr(
            active_runtime,
            "premise_digest",
            hashlib.sha256(b"direct-pairwise-premise").hexdigest(),
        )),
        generation=graph_generation,
    )

    self._debug_print("=" * 60)
    self._debug_print("Pairwise strategy (two-stage check):")
    self._debug_print(
        f"  Function 1: {len(cases1)} return cases"
        + (
            f" (pruned {original_case_count1 - len(cases1)} unreachable)"
            if len(cases1) != original_case_count1
            else ""
        )
    )
    self._debug_print(
        f"  Function 2: {len(cases2)} return cases"
        + (
            f" (pruned {original_case_count2 - len(cases2)} unreachable)"
            if len(cases2) != original_case_count2
            else ""
        )
    )
    self._debug_print(f"  Total pairs to check: {total_pairs}")
    self._debug_print(f"  Per-query timeout (stage1): {self.per_query_timeout}s")
    self._debug_print(f"  Per-query timeout (stage2 hard): {self.per_query_timeout_hard}s")
    self._debug_print("=" * 60)

    if total_pairs == 0:
        self._debug_print("No return cases to check")
        empty_result = self._create_empty_result()
        if dispatch_frame is not None:
            empty_result.comparison_execution_receipt = issue_builtin_comparison_receipt(
                dispatch_frame,
                query_records=(),
                consumed_projection_binding_ids=(),
                disposition_counts={
                    "total": 0,
                    "unsat": 0,
                    "sat": 0,
                    "unknown": 0,
                    "error": 0,
                },
            )
        return empty_result

    unsat_count = 0
    sat_count = 0
    unknown_count = 0
    error_count = 0
    sat_pair_info = None
    sat_safety_receipt = None
    sat_query_execution_receipt = None
    counterexample_raw = None
    last_formula = None
    resolved_pairs: set[tuple[int, int]] = set()
    pending_loop_summary_pairs: list[_PendingLoopSummaryPair] = []
    all_normalization_rules = []
    normalization_stats = {
        "solver_proven_rewrite_attempts": 0,
        "solver_proven_rewrite_successes": 0,
        "solver_proven_rewrite_failures": 0,
        "timeout_fallback_attempts": 0,
        "changed_pairs": 0,
        "no_change_pairs": 0,
        "unsat_results": 0,
        "sat_results": 0,
        "unknown_results": 0,
        "return_width_bridge_missing": 0,
        "exact_query_attempt_cache_hits": 0,
        "exact_query_attempt_cache_misses": 0,
        "width_target_count": 0,
        "width_seed_complete_count": 0,
        "width_seed_incomplete_count": 0,
        "width_unary_proof_attempts": 0,
        "width_unary_proof_cache_hits": 0,
        "width_unary_proof_successes": 0,
        "width_unary_proof_blocked": 0,
        "width_observation_proven": 0,
        "width_observation_blocked": 0,
        "width_binding_receipts": 0,
        "width_binding_blocked": 0,
        "width_canonical_consumer_queries": 0,
        "unary_width_solver_queries": 0,
        "pair_width_projection_queries": 0,
        "pair_width_compatibility_queries": 0,
        "legacy_width_bridge_queries": 0,
    }
    unknown_reasons = []
    self._active_normalization_stats = normalization_stats
    query_execution_records = []

    from ...return_width_pipeline import (
        prepare_function_return_widths,
        prepare_pair_return_observation,
        return_coverage_artifact_ids,
    )
    from ..proof_gates.return_coverage import (
        prepare_unary_return_coverage_for_width,
    )

    prepare_unary_return_coverage_for_width(
        self,
        base_ctx,
        solver_analysis1,
        solver_analysis2,
        symbol_replace_fn1,
        symbol_replace_fn2,
    )

    prepared_widths1 = prepare_function_return_widths(
        solver_analysis1, cases1, normalization_stats
    )
    prepared_widths2 = prepare_function_return_widths(
        solver_analysis2, cases2, normalization_stats
    )
    width_runtime = getattr(self, "_obligation_runtime_session", None)
    width_coverage_ids = return_coverage_artifact_ids(
        width_runtime,
        (
            tuple(getattr(solver_analysis1, "outcome_function_identity")()),
            tuple(getattr(solver_analysis2, "outcome_function_identity")()),
        ),
    )
    base_ctx["return_width_observations_by_pair"] = {}

    # Stage 1 is a real prepass: every logical guard edge is materialized
    # before return-width/value preparation or any legacy value shortcut.
    from ..pairwise_query_executor import (
        execute_guard_overlap,
    )

    runtime = getattr(self, "_obligation_runtime_session", None)
    graph = self._guard_overlap_graph
    ledger_binding = PairLedgerBinding(
        str(getattr(dispatch_frame, "comparison_session_id", "direct-pairwise")),
        str(getattr(dispatch_frame, "branch_id", "pairwise")),
        str(getattr(getattr(dispatch_frame, "prepared", None), "surface_digest", "direct-surface")),
        str(getattr(getattr(dispatch_frame, "projection", None), "projection_id", "direct-projection")),
        int(getattr(dispatch_frame, "generation", 0) or 0),
        tuple(getattr(getattr(runtime, "current_view", None), "view_id", ()) or ()),
        graph.premise_digest,
        graph.generation,
    )
    if (
        runtime is not None
        and runtime.pair_ledger_manager.current is not None
        and runtime.pair_ledger_manager.pending_successor is None
        and (
            runtime.pair_ledger_manager.current.closures
            or runtime.pair_ledger_manager.current.provisional
        )
    ):
        # A repeated direct strategy invocation owns a fresh ledger.  Only the
        # empty successor created by a derived-view transition is reusable.
        runtime.pair_ledger_manager.supersede_current()
    pair_ledger = (
        runtime.open_pair_ledger(ledger_binding, total_pairs)
        if runtime is not None
        else PairDispositionLedger(ledger_binding, total_pairs)
    )
    if dispatch_frame is not None and dispatch_frame.replan_successor_plan is not None:
        composed_plan = (
            runtime.pair_ledger_manager.last_composed_successor
            if runtime is not None else None
        )
        if composed_plan is None:
            raise RuntimeError("pair_replan_successor_composition_missing")
        dispatch_frame.replan_successor_plan = composed_plan
        dispatch_frame.replan_successor_ledger = pair_ledger
        dispatch_frame.successor_ledger_reused = bool(
            composed_plan.accepts(
                pair_ledger.binding, pair_ledger.expected_pairs
            )
            and runtime is not None
            and runtime.pair_ledger_manager.current is pair_ledger
        )
        if not dispatch_frame.successor_ledger_reused:
            raise RuntimeError("pair_replan_successor_binding_failed")
    guard_prepass = {}
    for guard_i, guard_case1 in enumerate(cases1):
        for guard_j, guard_case2 in enumerate(cases2):
            guard_pair_id = f"({guard_i},{guard_j})"
            if dispatch_frame is not None and dispatch_frame.projection.semantic_bindings:
                lowered = lower_call_projection_for_case_pair(
                    dispatch_frame, guard_case1, guard_case2,
                    pair_id=guard_pair_id,
                    render_fn1=symbol_replace_fn1,
                    render_fn2=symbol_replace_fn2,
                )
                if lowered.status != "proven":
                    guard_prepass[(guard_i, guard_j)] = (None, lowered)
                    continue
                base_ctx.setdefault("call_projection_assertions_by_pair", {})[guard_pair_id] = lowered.assertions
                base_ctx.setdefault("call_projection_binding_ids_by_pair", {})[guard_pair_id] = lowered.binding_ids
                base_ctx.setdefault("call_projection_guard_binding_ids_by_pair", {})[guard_pair_id] = lowered.guard_binding_ids
                base_ctx.setdefault("call_projection_assertion_bundles_by_pair", {})[guard_pair_id] = lowered.assertion_bundles
                base_ctx.setdefault("call_projection_binding_digests_by_pair", {})[guard_pair_id] = dict(lowered.binding_assertion_digests)
                base_ctx.setdefault("call_site_return_width_receipts_by_pair", {})[guard_pair_id] = lowered.return_width_receipt_digests
                base_ctx.setdefault("call_site_return_width_receipt_assertions_by_pair", {})[guard_pair_id] = lowered.return_width_receipt_assertion_digests
            else:
                lowered = None
            node = execute_guard_overlap(
                self, base_ctx, guard_case1, guard_case2,
                symbol_replace_fn1, symbol_replace_fn2, guard_pair_id,
            )
            guard_prepass[(guard_i, guard_j)] = (node, lowered)
    normalization_stats["guard_overlap_logical_edges"] = total_pairs
    normalization_stats["guard_overlap_source_logical_edges"] = (
        original_case_count1 * original_case_count2
    )
    normalization_stats["guard_overlap_pruned_unreachable_edges"] = (
        normalization_stats["guard_overlap_source_logical_edges"] - total_pairs
    )
    normalization_stats["guard_overlap_prepass_node_hits"] = 0
    normalization_stats["guard_overlap_unsat_edges"] = sum(
        1 for node, _lowered in guard_prepass.values()
        if node is not None and node.disjoint_artifact is not None
    )
    normalization_stats["guard_overlap_value_candidates"] = (
        total_pairs - normalization_stats["guard_overlap_unsat_edges"]
    )

    for i, case1 in enumerate(cases1):
        for j, case2 in enumerate(cases2):
            pair_id = f"({i},{j})"
            guard_node, prepass_lowered = guard_prepass[(i, j)]
            if guard_node is not None:
                normalization_stats["guard_overlap_prepass_node_hits"] += 1
            if guard_node is None:
                unknown_count += 1
                pair_ledger.record_inconclusive(
                    (i, j), "call_projection_lowering_failed",
                    getattr(prepass_lowered, "evidence_digest", "missing"),
                )
                unknown_reasons.append(make_internal_v2_reason_diagnostic(
                    "call_projection_partition_unproven", stage="CALL_EFFECT_PREFLIGHT",
                    pair_or_case=pair_id,
                    evidence_refs=(getattr(prepass_lowered, "failure_cause", None),),
                    detail="Certified guard projection could not be lowered.",
                ))
                continue
            if guard_node.disjoint_artifact is not None:
                closure = PairClosureEvidence.validated(
                    (i, j), PairClosureKind.GUARD_QUERY, ledger_binding,
                    GuardUnsatClosureArtifact(guard_node.disjoint_artifact),
                    required_binding_uses=tuple(
                        getattr(prepass_lowered, "binding_ids", ()) or ()
                    ),
                    consumed_binding_uses=tuple(
                        getattr(prepass_lowered, "guard_binding_ids", ()) or ()
                    ),
                )
                pair_ledger.close(closure)
                unsat_count += 1
                resolved_pairs.add((i, j))
                continue
            prepared_width_observation = prepare_pair_return_observation(
                solver_analysis1,
                solver_analysis2,
                case1,
                case2,
                prepared_widths1,
                prepared_widths2,
                return_coverage_ids=width_coverage_ids,
                proof_runtime=width_runtime,
                left_query_parameters=base_ctx["params1"],
                right_query_parameters=base_ctx["params2"],
                left_replace_fn=symbol_replace_fn1,
                right_replace_fn=symbol_replace_fn2,
                stats=normalization_stats,
            )
            base_ctx["return_width_observations_by_pair"][pair_id] = (
                prepared_width_observation
            )
            if prepared_width_observation.proven:
                base_ctx.setdefault("return_width_binding_receipts_by_pair", {})[
                    pair_id
                ] = prepared_width_observation.binding_receipt
            call_projection_covers_unresolved = False
            if dispatch_frame is not None and dispatch_frame.projection.semantic_bindings:
                lowered_call_projection = lower_call_projection_for_case_pair(
                    dispatch_frame,
                    case1,
                    case2,
                    pair_id=pair_id,
                    render_fn1=symbol_replace_fn1,
                    render_fn2=symbol_replace_fn2,
                )
                if lowered_call_projection.status != "proven":
                    unknown_count += 1
                    unknown_reasons.append(
                        make_internal_v2_reason_diagnostic(
                            "call_projection_partition_unproven",
                            stage="CALL_EFFECT_PREFLIGHT",
                            pair_or_case=pair_id,
                            evidence_refs=(
                                lowered_call_projection.failure_cause,
                                lowered_call_projection.evidence_digest,
                            ),
                            detail="Certified call projection could not be lowered into this pair query.",
                        )
                    )
                    continue
                base_ctx.setdefault("call_projection_assertions_by_pair", {})[
                    pair_id
                ] = lowered_call_projection.assertions
                base_ctx.setdefault("call_projection_binding_ids_by_pair", {})[
                    pair_id
                ] = lowered_call_projection.binding_ids
                base_ctx.setdefault("call_projection_guard_binding_ids_by_pair", {})[
                    pair_id
                ] = lowered_call_projection.guard_binding_ids
                base_ctx.setdefault("call_projection_assertion_bundles_by_pair", {})[
                    pair_id
                ] = lowered_call_projection.assertion_bundles
                base_ctx.setdefault("call_projection_binding_digests_by_pair", {})[
                    pair_id
                ] = dict(lowered_call_projection.binding_assertion_digests)
                base_ctx.setdefault("call_site_return_width_receipts_by_pair", {})[
                    pair_id
                ] = lowered_call_projection.return_width_receipt_digests
                base_ctx.setdefault(
                    "call_site_return_width_receipt_assertions_by_pair", {}
                )[pair_id] = (
                    lowered_call_projection.return_width_receipt_assertion_digests
                )
                call_projection_covers_unresolved = True
            readonly_contract_assertions = self._readonly_contract_pairwise_extra_assertions(
                case1,
                case2,
                symbol_replace_fn1,
                symbol_replace_fn2,
            )
            if readonly_contract_assertions:
                self._register_pairwise_extra_assertions(
                    base_ctx,
                    pair_id,
                    readonly_contract_assertions,
                )
            else:
                self._clear_pairwise_extra_assertions(base_ctx, pair_id)
            runtime_candidate = RuntimeReductionCandidate.create(
                ledger_binding,
                pair_id,
                (case1.value_expr, case2.value_expr),
                ("equivalent_runtime_reductions", semantic_parameter_sources),
            )
            runtime_relation_artifact = validate_runtime_reduction_candidate(
                self,
                ledger_binding,
                runtime_candidate,
                case1,
                case2,
                semantic_parameter_sources,
            )
            if runtime_relation_artifact is not None:
                pair_ledger.close(PairClosureEvidence.validated(
                    (i, j), PairClosureKind.RECOVERY, ledger_binding,
                    runtime_relation_artifact,
                ))
                unsat_count += 1
                resolved_pairs.add((i, j))
                continue
            closed_expression_candidate = CountedLoopClosedExpressionCandidate.create(
                ledger_binding,
                pair_id,
                (case1.value_expr, case2.value_expr),
                ("counted_loop_summary_closed_expression", "v2"),
            )
            closed_expression_artifact = (
                validate_counted_loop_closed_expression_candidate(
                    self,
                    ledger_binding,
                    closed_expression_candidate,
                    case1,
                    case2,
                    base_ctx,
                )
            )
            if closed_expression_artifact is not None:
                pair_ledger.close(PairClosureEvidence.validated(
                    (i, j), PairClosureKind.RECOVERY, ledger_binding,
                    closed_expression_artifact,
                ))
                unsat_count += 1
                resolved_pairs.add((i, j))
                continue
            case1_has_unresolved = self._case_contains_unresolved_expression(
                case1,
                case2.conditions,
                own_render_fn=symbol_replace_fn1,
                extra_render_fn=symbol_replace_fn2,
                base_ctx=base_ctx,
                query_label=f"{pair_id}:case1",
            )
            case2_has_unresolved = self._case_contains_unresolved_expression(
                case2,
                case1.conditions,
                own_render_fn=symbol_replace_fn2,
                extra_render_fn=symbol_replace_fn1,
                base_ctx=base_ctx,
                query_label=f"{pair_id}:case2",
            )
            if call_projection_covers_unresolved:
                case1_has_unresolved = False
                case2_has_unresolved = False
            if case1_has_unresolved or case2_has_unresolved:
                lowering = self._try_build_unresolved_deferred_call_lowering(
                    base_ctx=base_ctx,
                    case1=case1,
                    case2=case2,
                    pair_id=pair_id,
                )
                object_target_key = None
                completed_proof_evidence = None
                if lowering is None:
                    object_target_key = self._unresolved_expression_object_target_key(
                        base_ctx=base_ctx,
                        case1=case1,
                        case2=case2,
                        pair_id=pair_id,
                    )
                if lowering is None and object_target_key is not None:
                    completed_proof_evidence = (
                        self._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(
                            object_target_key
                        )
                    )
                if lowering is not None:
                    self._register_pairwise_extra_assertions(
                        base_ctx,
                        pair_id,
                        lowering.assertions,
                    )
                    self._debug_print(
                        f"  Pair {pair_id}: unresolved runtime unknown "
                        "lowered with object-derived equality evidence"
                    )
                else:
                    self._clear_pairwise_extra_assertions(base_ctx, pair_id)
                    unknown_count += 1
                    if object_target_key is None:
                        object_target_key = self._unresolved_expression_object_target_key(
                            base_ctx=base_ctx,
                            case1=case1,
                            case2=case2,
                            pair_id=pair_id,
                        )
                    if self._unresolved_expression_target_uses_generic_pending_census(
                        object_target_key
                    ):
                        completed_proof_evidence = (
                            self._unresolved_expression_generic_diagnostic_evidence(
                                object_target_key
                            )
                        )
                    if completed_proof_evidence is None:
                        completed_proof_evidence = (
                            self._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(
                                object_target_key
                            )
                        )
                    if completed_proof_evidence is None:
                        completed_proof_evidence = (
                            self._unresolved_expression_deferred_call_diagnostic_evidence(
                                object_target_key
                            )
                        )
                    if completed_proof_evidence is None:
                        completed_proof_evidence = (
                            self._unresolved_expression_opaque_unknown_diagnostic_evidence(
                                object_target_key
                            )
                        )
                    if completed_proof_evidence is None:
                        completed_proof_evidence = (
                            self._unresolved_expression_generic_diagnostic_evidence(
                                object_target_key
                            )
                        )
                    unknown_reasons.append(
                        make_internal_v2_reason_diagnostic(
                            "expression_translation_incomplete",
                            stage="S_PAIRWISE",
                            pair_or_case=pair_id,
                            evidence_refs=(f"{pair_id}:case1", f"{pair_id}:case2"),
                            recovery_proof_obligations=(
                                self._unresolved_expression_recovery_proof_obligations(object_target_key)
                            ),
                            evidence_kind="unresolved_expression_safety",
                            object_target_key=object_target_key,
                            object_evidence=completed_proof_evidence,
                            action_status=self._unresolved_expression_action_status(
                                object_target_key,
                                completed_proof_evidence,
                            ),
                            detail="pairwise case contains solver-unresolved expression evidence",
                        )
                    )
                    self._debug_print(
                        f"  Pair {pair_id}: unresolved expression detected -> UNKNOWN"
                    )
                    continue
            else:
                if not readonly_contract_assertions:
                    self._clear_pairwise_extra_assertions(base_ctx, pair_id)

            # Loop/readonly recognizers may identify which semantic proof is
            # required, but they no longer close a pair themselves.  A
            # completed proof only authorizes the canonical value query below;
            # the ledger receives authority exclusively from its UNSAT result.
            loop_fallback_reason = self._case_pair_loop_summary_safe_fallback_reason(
                case1, case2
            )
            if loop_fallback_reason is not None:
                v2_loop_blocker_signal = None
                reason_id = self._unknown_reason_id_for_loop_fallback(
                    loop_fallback_reason
                )
                try:
                    from ...v2.loop_recurrence import LoopBlockerProductionSignal
                    from ...v2.production_signals import emit_loop_recurrence_signal

                    v2_loop_blocker_signal = (
                        LoopBlockerProductionSignal.from_loop_fallback(
                            base_ctx.get("analysis1"),
                            base_ctx.get("analysis2"),
                            case1,
                            case2,
                            loop_fallback_reason,
                            observation_contract_id=dispatch_bound_observation_contract_digest(
                                base_ctx, dispatch_frame
                            ),
                        )
                    )
                    emit_loop_recurrence_signal(
                        v2_loop_blocker_signal,
                        producer_site_manifest_id="pairwise-loop-fallback-blocker",
                    )
                except Exception as exc:
                    from ...v2.production_signals import (
                        record_production_pilot_shadow_error,
                    )

                    record_production_pilot_shadow_error(exc)
                try:
                    from ...v2.abi_width_readonly import (
                        AbiWidthReadonlyBlockerSignal,
                        AbiWidthReadonlyDisposition,
                        ReadonlyReductionObjectSetSeed,
                        classify_readonly_source,
                    )
                    from ...v2.production_signals import (
                        emit_abi_width_readonly_signal,
                        register_readonly_promotion,
                    )

                    classification = classify_readonly_source(loop_fallback_reason)
                    if classification.disposition is (
                        AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE
                    ) and classification.reason_ids == (
                        "readonly_storage_identity_unproven",
                    ):
                        readonly_seed = ReadonlyReductionObjectSetSeed.from_analyses_and_cases(
                            base_ctx.get("analysis1"), base_ctx.get("analysis2"),
                            case1, case2,
                        )
                        register_readonly_promotion(readonly_seed)
                        unresolved = (
                            ("left", readonly_seed.left_unresolved_member_indices),
                            ("right", readonly_seed.right_unresolved_member_indices),
                        )
                        if not any(indices for _side, indices in unresolved):
                            raise ValueError(
                                "readonly unary source did not identify an unresolved member"
                            )
                        for side, indices in unresolved:
                            for member_index in indices:
                                emit_abi_width_readonly_signal(
                                    AbiWidthReadonlyBlockerSignal.from_readonly_member(
                                        readonly_seed, side, member_index
                                    ),
                                    producer_site_manifest_id=(
                                        "pairwise-readonly-identity-blocker"
                                    ),
                                )
                    elif classification.disposition is (
                        AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE
                    ) and classification.reason_ids == (
                        "readonly_object_correspondence_unproven",
                    ):
                        readonly_seed = ReadonlyReductionObjectSetSeed.from_analyses_and_cases(
                            base_ctx.get("analysis1"), base_ctx.get("analysis2"),
                            case1, case2,
                        )
                        register_readonly_promotion(readonly_seed)
                        for side, indices in (
                            ("left", readonly_seed.left_unresolved_member_indices),
                            ("right", readonly_seed.right_unresolved_member_indices),
                        ):
                            for member_index in indices:
                                emit_abi_width_readonly_signal(
                                    AbiWidthReadonlyBlockerSignal.from_readonly_member(
                                        readonly_seed, side, member_index
                                    ),
                                    producer_site_manifest_id=(
                                        "pairwise-readonly-correspondence-member"
                                    ),
                                )
                    # Return-observation ABI/width causes are owned exclusively
                    # by return_width_surface.py.  Pairwise fallback classification
                    # remains diagnostic and must not reconstruct the same C/Q.
                except Exception as exc:
                    from ...v2.production_signals import (
                        record_production_pilot_shadow_error,
                    )

                    record_production_pilot_shadow_error(exc)
                object_target_key = None
                evidence_kind = None
                if reason_id == UnknownReasonId.READONLY_IDENTITY_MISSING:
                    object_target_key = self._readonly_identity_object_target_key(
                        base_ctx=base_ctx, case1=case1, case2=case2,
                        pair_id=pair_id,
                    )
                    evidence_kind = "object_storage_identity"
                elif type(reason_id) is str:
                    object_target_key = self._method_b_closure_object_target_key(
                        base_ctx=base_ctx, case1=case1, case2=case2,
                        pair_id=pair_id,
                    )
                reason_factory = (
                    make_internal_v2_reason_diagnostic
                    if type(reason_id) is str
                    else make_unknown_reason
                )
                reason_record = reason_factory(
                    reason_id, stage="S_PAIRWISE", pair_or_case=pair_id,
                    evidence_refs=(loop_fallback_reason,),
                    evidence_kind=evidence_kind,
                    object_target_key=object_target_key,
                    detail=loop_fallback_reason,
                )
                semantic_artifact = None
                if type(reason_id) is str:
                    self._record_completed_method_b_covering_case_proof_if_safe(
                        reason_record,
                        analysis1,
                        case1,
                        case2,
                        v2_blocker_signal=v2_loop_blocker_signal,
                    )
                    if (
                        v2_loop_blocker_signal is not None
                        and loop_fallback_reason
                        == "counted_loop_summary_expression_proof_missing"
                        and self._method_b_covering_case_proof(case1, case2) is None
                    ):
                        try:
                            from ..pairwise_query_executor import (
                                LoopV2QueryNotFormable,
                                RenderedLoopV2SolverQuery,
                                preflight_loop_v2_solver_query,
                            )
                            from ...v2.production_signals import (
                                active_loop_requirement_for_signal,
                                active_production_execution_identity_digest,
                                execute_loop_solver_rendered_query,
                            )

                            v2_requirement = active_loop_requirement_for_signal(
                                v2_loop_blocker_signal,
                                "loop_exact_term_relation",
                            )
                            v2_execution_identity = (
                                active_production_execution_identity_digest()
                            )
                            if (
                                v2_requirement is not None
                                and v2_execution_identity is not None
                            ):
                                loop_query_preflight = preflight_loop_v2_solver_query(
                                    blocker=v2_loop_blocker_signal,
                                    requirement=v2_requirement,
                                    analysis1=base_ctx.get("analysis1"),
                                    analysis2=base_ctx.get("analysis2"),
                                    case1=case1,
                                    case2=case2,
                                    pair_id=pair_id,
                                    execution_identity_digest=v2_execution_identity,
                                )
                                if type(loop_query_preflight) is (
                                    RenderedLoopV2SolverQuery
                                ):
                                    execute_loop_solver_rendered_query(
                                        v2_loop_blocker_signal,
                                        loop_query_preflight,
                                        configured_timeout_ms=max(
                                            1,
                                            int(self.per_query_timeout_hard * 1000),
                                        ),
                                    )
                                elif type(loop_query_preflight) is (
                                    LoopV2QueryNotFormable
                                ):
                                    pass
                                else:
                                    raise TypeError(
                                        "loop v2 query preflight returned an "
                                        "unknown variant"
                                    )
                        except Exception as exc:
                            from ...v2.production_signals import (
                                record_production_pilot_shadow_error,
                            )

                            record_production_pilot_shadow_error(exc)
                    self._record_completed_method_b_dual_summary_solver_proof_if_safe(
                        reason_record, analysis1, case1, case2
                    )
                    completed = tuple(self._completed_recovery_proof_evidence(
                        analysis1, analysis2
                    ))
                    candidate = MethodBClosureCandidate.create(
                        ledger_binding,
                        pair_id,
                        (object_target_key, loop_fallback_reason),
                        completed,
                    )
                    semantic_artifact = validate_method_b_candidate(
                        self,
                        ledger_binding,
                        candidate,
                        reason_record,
                        analysis1,
                        analysis2,
                    )
                elif reason_id == UnknownReasonId.READONLY_IDENTITY_MISSING:
                    self._record_completed_readonly_identity_projection_proof_if_safe(
                        reason_record, analysis1, analysis2, case1, case2
                    )
                    completed = tuple(self._completed_recovery_proof_evidence(
                        analysis1, analysis2
                    ))
                    candidate = ReadonlyIdentityCandidate.create(
                        ledger_binding,
                        pair_id,
                        (object_target_key, loop_fallback_reason),
                        completed,
                    )
                    semantic_artifact = validate_readonly_identity_candidate(
                        self,
                        ledger_binding,
                        candidate,
                        reason_record,
                        analysis1,
                        analysis2,
                    )
                if semantic_artifact is None:
                    candidate = CountedLoopValueRelationCandidate.create(
                        ledger_binding,
                        pair_id,
                        (case1.value_expr, case2.value_expr),
                        ("closed_values_or_semantic_equivalence", loop_fallback_reason),
                    )
                    semantic_artifact = validate_counted_loop_value_candidate(
                        self,
                        ledger_binding,
                        candidate,
                        case1,
                        case2,
                        base_ctx,
                        semantic_parameter_sources,
                    )
                if semantic_artifact is not None:
                    pair_ledger.close(PairClosureEvidence.validated(
                        (i, j), PairClosureKind.RECOVERY, ledger_binding,
                        semantic_artifact,
                    ))
                    unsat_count += 1
                    resolved_pairs.add((i, j))
                    continue
                if self._case_pair_can_defer_loop_summary_proof(
                    case1, case2, loop_fallback_reason
                ):
                    pending_loop_summary_pairs.append(
                        _PendingLoopSummaryPair(
                            i, j, case1, case2, loop_fallback_reason
                        )
                    )
                    continue
                # A deferred proof is work, not closure authority.  Keep the
                # pair provisional and reschedule it after the proof derives a
                # new view.
                _register_loop_pair_replanner(
                    self, pair_id, reason_record, analysis1, analysis2,
                    case1, case2, base_ctx, semantic_parameter_sources,
                )
                unknown_count += 1
                unknown_reasons.append(reason_record)
                continue

            obligation_runtime = getattr(self, "_obligation_runtime_session", None)
            if obligation_runtime is not None:
                def plan_counterexample_safety(
                    pending,
                    *,
                    _base_ctx=base_ctx,
                    _cases1=cases1,
                    _cases2=cases2,
                    _replace1=symbol_replace_fn1,
                    _replace2=symbol_replace_fn2,
                    _pair=(i, j),
                    _pair_id=pair_id,
                    _case1=case1,
                    _case2=case2,
                    _sat_unsafety_reasons=tuple(sat_unsafety_reasons),
                    _analysis1=analysis1,
                    _analysis2=analysis2,
                ):
                    model_sha256 = self._counterexample_model_fingerprint(
                        pending.counterexample_raw
                    ) or "missing-model"
                    requirement = ProofRequirementId.create(
                        "counterexample_safety",
                        (
                            "pair_counterexample",
                            _pair_id,
                            model_sha256,
                            obligation_runtime.current_view.view_id,
                        ),
                        ProofRequirementContract(
                            proposition="SAT model is a safe decisive counterexample",
                            relation_direction="ordered",
                            observation_surface=("return_and_effect", "counterexample_model"),
                            active_precondition=(
                                obligation_runtime.premise_digest,
                                model_sha256,
                            ),
                        ),
                    )

                    def produce_counterexample_safety():
                        raw_model = pending.counterexample_raw
                        if _sat_unsafety_reasons:
                            unsafe_reason = self._make_sat_unsafety_unknown_reason(
                                _sat_unsafety_reasons,
                                _analysis1,
                                _analysis2,
                                case1=_case1,
                                case2=_case2,
                                pair_id=_pair_id,
                                stage="S_PAIRWISE",
                            )
                            if not self._sat_unsafety_resolution_proof_is_complete(
                                unsafe_reason,
                                _analysis1,
                                _analysis2,
                                current_counterexample_raw=raw_model,
                            ):
                                return FunctionProofOutcome.INCONCLUSIVE
                        if not validate_counterexample_across_cases(
                            self,
                            _base_ctx,
                            _cases1,
                            _cases2,
                            _replace1,
                            _replace2,
                            _pair,
                            raw_model,
                        ):
                            return FunctionProofOutcome.INCONCLUSIVE
                        replay_reasons = self._same_function_counterexample_replay_reasons(
                            _analysis1,
                            _analysis2,
                        )
                        if replay_reasons:
                            replay_reason = self._make_sat_unsafety_unknown_reason(
                                replay_reasons,
                                _analysis1,
                                _analysis2,
                                case1=_case1,
                                case2=_case2,
                                pair_id=_pair_id,
                                stage="S_PAIRWISE",
                            )
                            if not self._sat_unsafety_resolution_proof_is_complete(
                                replay_reason,
                                _analysis1,
                                _analysis2,
                                current_counterexample_raw=raw_model,
                            ):
                                return FunctionProofOutcome.INCONCLUSIVE
                        return FunctionProofOutcome.NOT_EQUIVALENT

                    return requirement, "counterexample_safety", produce_counterexample_safety

                obligation_runtime.register_counterexample_safety_replanner(
                    pair_id,
                    plan_counterexample_safety,
                )

            result = self._solve_query_after_guard(
                base_ctx,
                case1,
                case2,
                symbol_replace_fn1,
                symbol_replace_fn2,
                pair_id,
            )

            binding_ids = ()
            query_text = str(result.last_query or "")
            expected_solver_disposition = (
                "unsat" if result.is_equivalent is True
                else "sat" if result.is_equivalent is False
                else "unknown"
            )
            solver_execution_receipt = getattr(
                result, "solver_query_execution_receipt", None
            )
            solver_execution_valid = (
                type(solver_execution_receipt)
                is SolverQueryExecutionReceipt
                and solver_execution_receipt.validates_execution(
                    query=query_text,
                    expected_disposition=expected_solver_disposition,
                    expected_query_label=pair_id,
                    expected_model=(
                        result.counterexample_raw
                        if expected_solver_disposition == "sat"
                        else None
                    ),
                )
            )
            if query_text and solver_execution_valid:
                formula_digest = hashlib.sha256(query_text.encode("utf-8")).hexdigest()
                premise_digest = ledger_binding.premise_digest
                disposition = (
                    "unsat" if result.is_equivalent is True
                    else "sat" if result.is_equivalent is False
                    else "unknown"
                )
                query_binding_evidence = projection_binding_evidence_from_query(
                    query_text
                )
                expected_binding_evidence = dict(
                    base_ctx.get("call_projection_binding_digests_by_pair", {}).get(
                        pair_id,
                        {},
                    )
                )
                binding_ids = tuple(sorted(
                    binding_id
                    for binding_id, assertion_digest in query_binding_evidence.items()
                    if expected_binding_evidence.get(binding_id) == assertion_digest
                ))
                query_execution_records.append(
                    QueryExecutionRecord(
                        query_label=pair_id,
                        premise_digest=premise_digest,
                        formula_digest=formula_digest,
                        disposition=disposition,
                        proof_kind=str(result.pair_stage or "pairwise_solver_query"),
                        projection_binding_ids=binding_ids,
                        return_width_observation_view_digest=getattr(
                            result,
                            "return_width_observation_view_digest",
                            "",
                        ),
                        return_width_binding_receipt_digest=getattr(
                            result,
                            "consumer_binding_receipt_digest",
                            "",
                        ),
                        call_site_return_width_receipt_digests=tuple(
                            (base_ctx.get("call_site_return_width_receipts_by_pair") or {}).get(
                                pair_id, ()
                            )
                        ),
                        call_site_return_width_receipt_assertion_digests=tuple(
                            (
                                base_ctx.get(
                                    "call_site_return_width_receipt_assertions_by_pair"
                                )
                                or {}
                            ).get(pair_id, ())
                        ),
                        canonical_return_width_receipt_digests=(
                            (str(getattr(result, "consumer_binding_receipt_digest", "")),)
                            if getattr(result, "consumer_binding_receipt_digest", "")
                            else ()
                        ),
                        formula_text=query_text,
                    )
                )

            if result.last_query:
                last_formula = result.last_query
            if result.normalization_rules:
                all_normalization_rules.extend(result.normalization_rules)

            if result.is_equivalent is False:
                sat_terminal_query = (
                    result.last_query
                    if isinstance(result.last_query, str)
                    and result.last_query.strip()
                    else None
                )
                if sat_terminal_query is None or not solver_execution_valid:
                    unknown_count += 1
                    unknown_reasons.append(make_unknown_reason(
                        "unexpected_pairwise_state",
                        stage="S_PAIRWISE",
                        pair_or_case=pair_id,
                        evidence_refs=(
                            result.pair_stage or "unknown",
                            (
                                "sat_terminal_query_receipt_missing"
                                if sat_terminal_query is None
                                else "sat_query_execution_receipt_invalid"
                            ),
                        ),
                        detail=(
                            "SAT result is not bound to the exact solver "
                            "execution receipt; counterexample promotion is "
                            "prohibited"
                        ),
                    ))
                    self._debug_print(
                        f"  Pair {pair_id}: SAT downgraded to UNKNOWN because "
                        "the terminal solver query is unavailable"
                    )
                    continue
                analysis_safety_validated = not sat_unsafety_reasons
                if sat_unsafety_reasons:
                    from ...v2.production_signals import (
                        SatCounterexampleEvidenceBinding,
                    )
                    sat_counterexample_binding = SatCounterexampleEvidenceBinding(
                        hashlib.sha256(
                            str(result.last_query or "").encode("utf-8")
                        ).hexdigest(),
                        hashlib.sha256(
                            repr(result.counterexample_raw).encode("utf-8")
                        ).hexdigest(),
                        ledger_binding.premise_digest,
                        (i, j),
                    )
                    sat_unsafety_reason = self._make_sat_unsafety_unknown_reason(
                        sat_unsafety_reasons,
                        analysis1,
                        analysis2,
                        case1=case1,
                        case2=case2,
                        pair_id=pair_id,
                        stage="S_PAIRWISE",
                        counterexample_binding=sat_counterexample_binding,
                    )
                    if not self._sat_unsafety_resolution_proof_is_complete(
                        sat_unsafety_reason,
                        analysis1,
                        analysis2,
                        current_counterexample_raw=result.counterexample_raw,
                    ):
                        unknown_count += 1
                        unknown_reasons.append(sat_unsafety_reason)
                        self._debug_print(
                            "  Pair "
                            f"{pair_id}: SAT downgraded to UNKNOWN due to unsafe analysis "
                            f"summary ({', '.join(sat_unsafety_reasons)})"
                        )
                        continue
                    analysis_safety_validated = True

                self._observe_v2_sat_counterexample_ambiguity((result.pair_stage or "unknown",), analysis1, analysis2, case1=case1, case2=case2, pair_id=pair_id); is_decisive = validate_counterexample_across_cases(
                    self,
                    base_ctx,
                    cases1,
                    cases2,
                    symbol_replace_fn1,
                    symbol_replace_fn2,
                    (i, j),
                    result.counterexample_raw,
                )
                if not is_decisive:
                    unknown_count += 1
                    unknown_reasons.append(
                        self._make_sat_counterexample_ambiguous_unknown_reason(
                            (result.pair_stage or "unknown",),
                            analysis1,
                            analysis2,
                            case1=case1,
                            case2=case2,
                            pair_id=pair_id,
                            stage="S_PAIRWISE",
                        )
                    )
                    self._debug_print(
                        f"  Pair {pair_id}: SAT counterexample was ambiguous -> downgraded to UNKNOWN"
                    )
                    continue
                self._complete_v2_sat_counterexample_ambiguity_if_observed((result.pair_stage or "unknown",), analysis1, analysis2, case1=case1, case2=case2, pair_id=pair_id, counterexample_raw=result.counterexample_raw); global_case_replay_validated = True

                same_function_replay_reasons = self._same_function_counterexample_replay_reasons(
                    analysis1,
                    analysis2,
                )
                same_function_replay_validated = not same_function_replay_reasons
                if same_function_replay_reasons:
                    sat_replay_reason = self._make_sat_unsafety_unknown_reason(
                        same_function_replay_reasons,
                        analysis1,
                        analysis2,
                        case1=case1,
                        case2=case2,
                        pair_id=pair_id,
                        stage="S_PAIRWISE",
                    )
                    if not self._sat_unsafety_resolution_proof_is_complete(
                        sat_replay_reason,
                        analysis1,
                        analysis2,
                        current_counterexample_raw=result.counterexample_raw,
                    ):
                        unknown_count += 1
                        unknown_reasons.append(sat_replay_reason)
                        self._debug_print(
                            "  Pair "
                            f"{pair_id}: SAT downgraded to UNKNOWN until same-function "
                            "counterexample replay is completed"
                        )
                        continue
                    same_function_replay_validated = True

                safety_receipt = CounterexampleSafetyReceipt.from_pairwise_validation(
                    query=sat_terminal_query,
                    model=result.counterexample_raw,
                    premise_digest=ledger_binding.premise_digest,
                    pair_key=(i, j),
                    analysis_safe=analysis_safety_validated,
                    global_case_replay_safe=global_case_replay_validated,
                    same_function_replay_safe=same_function_replay_validated,
                )
                sat_safety_receipt = safety_receipt
                sat_query_execution_receipt = solver_execution_receipt

                sat_count += 1
                sat_pair_info = {
                    "i": i,
                    "j": j,
                    "case1_summary": case1.get_condition_summary(),
                    "case2_summary": case2.get_condition_summary(),
                    "value1": case1.get_value_smt(symbol_replace_fn1),
                    "value2": case2.get_value_smt(symbol_replace_fn2),
                    "pair_stage": result.pair_stage or "unknown",
                    "final_query": sat_terminal_query,
                }
                counterexample_raw = result.counterexample_raw

                self._debug_print(f"  Pair {pair_id}: SAT (NOT EQUIVALENT) - stopping")
                self._debug_print(f"    Case1[{i}]: {sat_pair_info['case1_summary']}")
                self._debug_print(f"    Case2[{j}]: {sat_pair_info['case2_summary']}")
                self._debug_print(f"    Value1: {sat_pair_info['value1'][:60]}...")
                self._debug_print(f"    Value2: {sat_pair_info['value2'][:60]}...")
                break

            if result.is_equivalent is True:
                structural_receipt = getattr(
                    result, "structural_equality_receipt", None
                )
                if (
                    type(structural_receipt) is StructuralEqualityReceipt
                    and structural_receipt.validates(
                        expected_query_label=pair_id
                    )
                ):
                    closure_kind = PairClosureKind.STRUCTURAL_EQUALITY
                    closure_artifact = (
                        StructuralEqualityClosureArtifact.from_validated_result(
                            premise_digest=getattr(
                                runtime,
                                "premise_digest",
                                ledger_binding.premise_digest,
                            ),
                            query_label=pair_id,
                            result=result,
                        )
                    )
                elif solver_execution_valid:
                    closure_kind = PairClosureKind.VALUE_QUERY
                    closure_artifact = (
                        SolverUnsatClosureArtifact.from_validated_result(
                            query_text,
                            getattr(
                                runtime,
                                "premise_digest",
                                ledger_binding.premise_digest,
                            ),
                            pair_id,
                            "value_query",
                            result,
                        )
                    )
                else:
                    unknown_count += 1
                    unknown_reasons.append(make_unknown_reason(
                        "unexpected_pairwise_state",
                        stage="S_PAIRWISE",
                        pair_or_case=pair_id,
                        evidence_refs=(
                            result.pair_stage or "unknown",
                            "unsat_or_structural_authority_missing",
                        ),
                        detail=(
                            "equivalent pair result has neither an exact "
                            "UNSAT execution receipt nor a typed structural "
                            "equality receipt"
                        ),
                    ))
                    self._debug_print(
                        f"  Pair {pair_id}: equivalent result downgraded to "
                        "UNKNOWN because proof authority is unavailable"
                    )
                    continue
                unsat_count += 1
                resolved_pairs.add((i, j))
                pair_ledger.close(PairClosureEvidence.validated(
                    (i, j), closure_kind, ledger_binding,
                    closure_artifact,
                    required_binding_uses=tuple(
                        (base_ctx.get("call_projection_binding_ids_by_pair") or {}).get(
                            pair_id, ()
                        )
                    ),
                    consumed_binding_uses=binding_ids,
                ))
                if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                    self._debug_print(f"  Pair {pair_id}: UNSAT ({unsat_count}/{total_pairs})")
                continue

            if result.blocking_reason == UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value:
                completed_bridge_result = self._solve_canonical_return_observation(
                    base_ctx,
                    case1,
                    case2,
                    symbol_replace_fn1,
                    symbol_replace_fn2,
                    pair_id,
                    object_target_key=getattr(result, "object_target_key", None),
                    blocking_detail=str(result.blocking_detail or ""),
                )
                if completed_bridge_result is not None and completed_bridge_result.is_equivalent is True:
                    unsat_count += 1
                    resolved_pairs.add((i, j))
                    pair_ledger.close(PairClosureEvidence.validated(
                        (i, j), PairClosureKind.RETURN_WIDTH, ledger_binding,
                        SolverUnsatClosureArtifact.from_validated_result(
                            str(completed_bridge_result.last_query or ""),
                            getattr(runtime, "premise_digest", ledger_binding.premise_digest),
                            pair_id, "return_width", completed_bridge_result,
                        ),
                        required_binding_uses=tuple(
                            (base_ctx.get("call_projection_binding_ids_by_pair") or {}).get(
                                pair_id, ()
                            )
                        ),
                        consumed_binding_uses=tuple(
                            (base_ctx.get("call_projection_binding_ids_by_pair") or {}).get(
                                pair_id, ()
                            )
                        ),
                    ))
                    last_formula = completed_bridge_result.last_query or last_formula
                    self._debug_print(
                        f"  Pair {pair_id}: return-width bridge proof -> UNSAT "
                        f"({unsat_count}/{total_pairs})"
                    )
                    continue
                pending_bridge_evidence = getattr(
                    self,
                    "_last_canonical_return_width_pending_evidence",
                    None,
                )
                if pending_bridge_evidence is not None:
                    result.object_evidence = pending_bridge_evidence

            unknown_count += 1
            if result.blocking_reason is not None:
                unknown_reasons.append(
                    make_unknown_reason(
                        result.blocking_reason,
                        stage="S_PAIRWISE",
                        pair_or_case=pair_id,
                        evidence_refs=(
                            result.pair_stage or "unknown", result.blocking_detail
                        ),
                        evidence_kind=getattr(result, "evidence_kind", None),
                        object_target_key=getattr(result, "object_target_key", None),
                        recovery_proof_obligations=getattr(
                            result,
                            "recovery_proof_obligations",
                            None,
                        ),
                        proof_obligation_id=getattr(
                            result, "proof_obligation_id", None
                        ),
                        proof_requirement_ids=getattr(
                            result, "proof_requirement_ids", None
                        ),
                        object_evidence=getattr(result, "object_evidence", None),
                        action_status=getattr(result, "action_status", None),
                        detail=result.blocking_detail,
                    )
                )
            self._debug_print(f"  Pair {pair_id}: final result UNKNOWN/TIMEOUT")

        if sat_count > 0:
            break

    if sat_count == 0 and pending_loop_summary_pairs:
        for pending in pending_loop_summary_pairs:
            pending_pair = (pending.i, pending.j)
            partition_witness = tuple(
                self._resolve_pending_loop_summary_pairs_with_partition_proof(
                    pending_loop_summary_pairs,
                    cases1,
                    cases2,
                    resolved_pairs,
                )
            )
            normalized_partition_witness = tuple(sorted(set(partition_witness)))
            candidate = AggregatePartitionCandidate.create(
                ledger_binding,
                f"({pending.i},{pending.j})",
                (pending_pair, pending.reason),
                normalized_partition_witness,
            )
            aggregate_artifact = validate_aggregate_partition_candidate(
                self,
                ledger_binding,
                candidate,
                pending_pair,
                normalized_partition_witness,
                pending_loop_summary_pairs,
                cases1,
                cases2,
                resolved_pairs,
            )
            if aggregate_artifact is not None:
                pair_ledger.close(PairClosureEvidence.validated(
                    pending_pair, PairClosureKind.AGGREGATE, ledger_binding,
                    aggregate_artifact,
                ))
                unsat_count += 1
                resolved_pairs.add(pending_pair)
                continue
            unknown_count += 1
            try:
                from ...v2.loop_recurrence import LoopBlockerProductionSignal
                from ...v2.production_signals import emit_loop_recurrence_signal

                emit_loop_recurrence_signal(
                    LoopBlockerProductionSignal.from_loop_fallback(
                        analysis1,
                        analysis2,
                        cases1[pending.i],
                        cases2[pending.j],
                        pending.reason,
                        observation_contract_id=dispatch_bound_observation_contract_digest(base_ctx, dispatch_frame),
                    ),
                    producer_site_manifest_id="pairwise-pending-loop-blocker",
                )
            except Exception as exc:
                from ...v2.production_signals import (
                    record_production_pilot_shadow_error,
                )

                record_production_pilot_shadow_error(exc)
            unknown_reasons.append(make_unknown_reason(
                self._unknown_reason_id_for_loop_fallback(pending.reason),
                stage="S_PAIRWISE",
                pair_or_case=f"({pending.i},{pending.j})",
                evidence_refs=(
                    pending.reason,
                    "canonical_solver_required",
                    repr(normalized_partition_witness),
                ),
                detail=pending.reason,
            ))

    elapsed_time = time.time() - start_time
    coverage_unknown_reasons = self._unresolved_return_coverage_unknown_reasons(
        coverage_unsafety_reasons,
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    equivalence_unknown_reasons = self._unresolved_equivalence_blocking_unknown_reasons(
        equivalence_blocking_reasons,
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    blocking_unknown_reasons = coverage_unknown_reasons + equivalence_unknown_reasons
    blocking_reasons_replace_pair_unknowns = (
        self._blocking_unknown_reasons_should_replace_pair_unknowns(
            unknown_reasons,
            coverage_unknown_reasons,
            equivalence_unknown_reasons,
        )
    )

    sat_pair_key = (
        (int(sat_pair_info["i"]), int(sat_pair_info["j"]))
        if sat_pair_info is not None else None
    )
    for ledger_i in range(len(cases1)):
        for ledger_j in range(len(cases2)):
            pair_key = (ledger_i, ledger_j)
            if pair_key in pair_ledger.closures or pair_key in pair_ledger.provisional:
                continue
            if pair_key == sat_pair_key:
                pair_ledger.record_terminal_query(
                    pair_key, PairDisposition.SAT,
                    str((sat_pair_info or {}).get("final_query") or ""), "value_query",
                    safety_receipt=sat_safety_receipt,
                    query_execution_receipt=sat_query_execution_receipt,
                )
            elif sat_count > 0:
                pair_ledger.record_terminal_query(
                    pair_key, PairDisposition.SKIPPED, "", "aggregate",
                )
            else:
                pair_ledger.record_inconclusive(
                    pair_key, "proof_incomplete", tuple(reason.reason_id for reason in unknown_reasons),
                )
    pair_ledger.finalize_inconclusive()
    if runtime is not None:
        terminal_outcomes = runtime.drain_pair_terminal_work()
        if any(
            outcome != FunctionProofOutcome.NOT_EQUIVALENT
            for outcome in terminal_outcomes
        ) and sat_count > 0:
            raise RuntimeError("counterexample safety receipt is not decisive")
    else:
        from ...obligations import RuntimeQuiescenceCertificate
        certificate = RuntimeQuiescenceCertificate(
            ledger_binding.stable_key(), total_pairs, len(pair_ledger.closures),
            0, len(pair_ledger.provisional), ledger_binding.derived_view_id,
            ledger_binding.premise_digest,
        )
        pair_ledger.seal(certificate)
    if dispatch_frame is not None:
        dispatch_frame.pair_disposition_ledger = pair_ledger
        if runtime is None:
            dispatch_frame.pair_quiescence_certificate = certificate
    ledger_counts = pair_ledger.counts()
    unsat_count = int(ledger_counts["unsat"])
    sat_count = int(ledger_counts["sat"])
    unknown_count = int(ledger_counts["unknown"])
    error_count = int(ledger_counts["error"])
    normalization_stats["pair_ledger_sealed"] = int(runtime is None)
    normalization_stats["pair_ledger_skipped_after_terminal"] = int(
        ledger_counts[PairDisposition.SKIPPED.value]
    )

    if sat_count > 0:
        final_is_equiv = False
        self._debug_print("=" * 60)
        self._debug_print("Result: NOT EQUIVALENT (found SAT pair)")
    elif (
        blocking_unknown_reasons
        and unknown_count > 0
        and blocking_reasons_replace_pair_unknowns
    ):
        final_is_equiv = None
        unknown_reasons = blocking_unknown_reasons
        blocking_reasons = coverage_unsafety_reasons + equivalence_blocking_reasons
        self._debug_print("=" * 60)
        self._debug_print(
            "Result: UNKNOWN (equivalence proof is blocked by incomplete analysis: "
            f"{', '.join(blocking_reasons)})"
        )
    elif unknown_count > 0:
        final_is_equiv = None
        if blocking_unknown_reasons:
            unknown_reasons = self._append_blocking_unknown_reasons(
                unknown_reasons,
                blocking_unknown_reasons,
            )
        self._debug_print("=" * 60)
        self._debug_print(f"Result: UNKNOWN (timeout/unknown in {unknown_count} pairs)")
    elif blocking_unknown_reasons:
        final_is_equiv = None
        unknown_reasons = blocking_unknown_reasons
        blocking_reasons = coverage_unsafety_reasons + equivalence_blocking_reasons
        self._debug_print("=" * 60)
        self._debug_print(
            "Result: UNKNOWN (equivalence proof is blocked by incomplete analysis: "
            f"{', '.join(blocking_reasons)})"
        )
    elif unsat_count == total_pairs:
        final_is_equiv = True
        self._debug_print("=" * 60)
        self._debug_print("Result: EQUIVALENT (all pairs UNSAT)")
    else:
        final_is_equiv = None
        error_count = total_pairs - unsat_count - sat_count - unknown_count
        strategy_error_kind = "unexpected_pairwise_state"
        strategy_error_message = f"unexpected pairwise state: errors={error_count}"
        self._debug_print("=" * 60)
        self._debug_print(f"Result: ERROR (unexpected state, errors={error_count})")

    self._debug_print(f"  Total pairs: {total_pairs}")
    self._debug_print(
        f"  UNSAT: {unsat_count}, SAT: {sat_count}, UNKNOWN: {unknown_count}, ERROR: {error_count}"
    )
    self._debug_print(f"  Total time: {elapsed_time:.3f}s")
    self._debug_print("=" * 60)

    self._merge_completed_recovery_proofs_from_solver_analyses(
        analysis1,
        solver_analysis1,
        analysis2,
        solver_analysis2,
    )

    aggregate_result = self._create_aggregate_result(
        final_is_equiv,
        elapsed_time,
        counterexample_raw,
    )

    try:
        consumed_projection_binding_ids = tuple(sorted({
            binding_id
            for record in query_execution_records
            for binding_id in record.projection_binding_ids
        }))
        disposition_counts = {
            "total": total_pairs,
            "unsat": unsat_count,
            "sat": sat_count,
            "unknown": unknown_count,
            "error": error_count,
            "skipped_after_terminal_decision": int(
                ledger_counts[PairDisposition.SKIPPED.value]
            ),
        }
        normalization_stats.update({
            "normalization_unsat_results": normalization_stats["unsat_results"],
            "normalization_sat_results": normalization_stats["sat_results"],
            "normalization_unknown_results": normalization_stats["unknown_results"],
            "unsat_results": unsat_count,
            "sat_results": sat_count,
            "unknown_results": unknown_count,
        })
        if dispatch_frame is not None and runtime is not None:
            dispatch_frame.pending_query_records = tuple(query_execution_records)
            dispatch_frame.pending_consumed_projection_binding_ids = (
                consumed_projection_binding_ids
            )
            dispatch_frame.pending_disposition_counts = dict(disposition_counts)
            comparison_receipt = None
        else:
            comparison_receipt = (
                issue_builtin_comparison_receipt(
                    dispatch_frame,
                    query_records=query_execution_records,
                    consumed_projection_binding_ids=consumed_projection_binding_ids,
                    disposition_counts=disposition_counts,
                )
                if dispatch_frame is not None
                else None
            )
        final_result = StrategyResult(
            is_equivalent=final_is_equiv,
            solver_results=aggregate_result,
            smt_formula=last_formula,
            counterexample_raw=counterexample_raw,
            return_var1="return_1",
            return_var2="return_2",
            constrained_fragments=base_ctx.get("constrained_fragments", []),
            total_pairs=total_pairs,
            unsat_pairs=unsat_count,
            sat_pairs=sat_count,
            unknown_pairs=unknown_count,
            error_pairs=error_count,
            sat_pair_info=sat_pair_info,
            normalization_rules=all_normalization_rules,
            pairwise_debug_stats=normalization_stats,
            unknown_reasons=unknown_reasons,
            error_kind=locals().get("strategy_error_kind"),
            error_message=locals().get("strategy_error_message"),
        )
        final_result.completed_recovery_proof_evidence = [
            {
                "side": side,
                "function_name": getattr(analysis, "function_name", None),
                "binary_name": getattr(analysis, "binary_id", None),
                "binary_id": getattr(analysis, "binary_id", None),
                "evidence": dict(evidence),
            }
            for side, analysis, prepared in (
                ("function1", solver_analysis1, prepared_widths1),
                ("function2", solver_analysis2, prepared_widths2),
            )
            for evidence in prepared.completion_evidence
        ]
        final_result.comparison_execution_receipt = comparison_receipt
        return final_result
    finally:
        self._active_safety_checker = None
        self._active_normalization_stats = None


def _register_loop_pair_replanner(
    strategy,
    pair_id,
    reason_record,
    analysis1,
    analysis2,
    case1,
    case2,
    base_ctx,
    semantic_parameter_sources,
):
    runtime = getattr(strategy, "_obligation_runtime_session", None)
    if runtime is None:
        return

    def replan():
        requirement = ProofRequirementId.create(
            "value_relation",
            ("loop_pair", pair_id, getattr(reason_record, "object_target_key", None)),
            ProofRequirementContract(
                proposition="loop summary value relation",
                observation_surface=("return_and_effect",),
                active_precondition=(runtime.premise_digest, pair_id),
            ),
        )

        def produce():
            complete = strategy._recovery_proof_is_complete(
                reason_record,
                analysis1,
                analysis2,
            )
            if not complete:
                complete = (
                    strategy._case_pair_counted_loop_summaries_match_by_closed_values(
                        case1,
                        case2,
                        base_ctx=base_ctx,
                    )
                    or strategy._counted_loop_values_are_provably_equivalent(
                        case1.value_expr,
                        case2.value_expr,
                        left_case=case1,
                        right_case=case2,
                        semantic_parameter_sources=semantic_parameter_sources,
                    )
                )
            return QueryResult(True if complete else None)

        return requirement, "value_relation", produce

    runtime.register_pair_query_replanner(pair_id, "value_relation", replan)

def _impl__blocking_unknown_reasons_should_replace_pair_unknowns(
    pair_unknown_reasons: Sequence[Any],
    coverage_unknown_reasons: Sequence[Any],
    equivalence_unknown_reasons: Sequence[Any],
) -> bool:
    """Return whether global blockers should replace pair-local reasons."""

    if not pair_unknown_reasons:
        return True
    if not coverage_unknown_reasons and not equivalence_unknown_reasons:
        return False

    replaceable_pair_reasons = {
        "expression_translation_incomplete",
        UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED.value,
        UnknownReasonId.SOLVER_PROVEN_REWRITE_NO_CHANGE.value,
        UnknownReasonId.NORMALIZATION_NO_CHANGE.value,
    }
    pair_reason_ids = {
        getattr(reason, "reason_id", None)
        for reason in pair_unknown_reasons
    }
    return bool(pair_reason_ids) and pair_reason_ids <= replaceable_pair_reasons

def _impl__append_blocking_unknown_reasons(
    cls,
    pair_unknown_reasons: Sequence[Any],
    blocking_unknown_reasons: Sequence[Any],
) -> List[Any]:
    result = list(pair_unknown_reasons)
    seen = {cls._unknown_reason_dedup_key(reason) for reason in result}
    for reason in blocking_unknown_reasons:
        key = cls._unknown_reason_dedup_key(reason)
        if key in seen:
            continue
        result.append(reason)
        seen.add(key)
    return result

def _impl__unknown_reason_dedup_key(reason: Any) -> Tuple[Any, ...]:
    return (
        getattr(reason, "reason_id", None),
        getattr(reason, "stage", None),
        getattr(reason, "pair_or_case", None),
        tuple(getattr(reason, "evidence_refs", ()) or ()),
        getattr(reason, "evidence_kind", None),
        getattr(reason, "proof_obligation_id", None),
    )

def _impl__case_pair_conditions_unsat_under_shared_inputs(
    self,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
    loop_fallback_reason: Optional[str],
) -> bool:
    if loop_fallback_reason != "loop_summary_shape_mismatch":
        return False
    if not case1.conditions or not case2.conditions:
        return False
    query = self._build_condition_only_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )
    result = Z3Solver(timeout=1, debug=False).check_equivalence_direct(query)
    return result.status == SolverStatus.UNSAT

def _impl__fp_denominator_count_identity_matches(
    expr_storage: Optional[tuple],
    expr_index: Optional[tuple],
    proof_storage: Optional[tuple],
    proof_index: Optional[tuple],
) -> bool:
    if expr_storage is not None and proof_storage is not None:
        if expr_storage == proof_storage:
            return True
        if expr_index is None or proof_index is None:
            return False
    if expr_index is not None and proof_index is not None:
        return expr_index == proof_index
    return False

def _impl__fp_denominator_name_fallback_matches_unique_count(
    self,
    expr: Expression,
    parameters: Sequence[Dict[str, Any]],
    accumulator_proof,
) -> bool:
    count_parameter_name = str(getattr(accumulator_proof, "count_parameter_name", "") or "")
    expr_name = str(getattr(expr, "name", "") or "")
    if not count_parameter_name or expr_name != count_parameter_name:
        return False
    matching_parameters = tuple(
        parameter
        for parameter in parameters or ()
        if isinstance(parameter, dict) and str(parameter.get("name") or "") == count_parameter_name
    )
    if len(matching_parameters) != 1:
        return False
    descriptor = matching_parameters[0]
    descriptor_storage = self._parameter_descriptor_storage_identity_key(descriptor)
    descriptor_index = self._parameter_descriptor_index_identity_key(descriptor)
    proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
    proof_index = self._reduction_count_index_identity_key(accumulator_proof)
    if proof_storage is not None and descriptor_storage != proof_storage:
        return False
    if proof_index is not None and descriptor_index != proof_index:
        return False
    return proof_storage is not None or proof_index is not None

def _impl__method_b_covering_case_proof(
    self,
    case1: ReturnCase,
    case2: ReturnCase,
) -> Optional[_MethodBCoveringCaseProof]:
    right_ref = self._method_b_readonly_summary_ref(getattr(case2, "value_expr", None))
    if right_ref is not None:
        proven = self._prove_exact_load_sum_covers_readonly_loop_summary(case1, case2, right_ref)
        if proven is not None:
            proof, adapter = proven
            return _MethodBCoveringCaseProof("left", "right", case1, case2, adapter, proof)
    left_ref = self._method_b_readonly_summary_ref(getattr(case1, "value_expr", None))
    if left_ref is not None:
        proven = self._prove_exact_load_sum_covers_readonly_loop_summary(case2, case1, left_ref)
        if proven is not None:
            proof, adapter = proven
            return _MethodBCoveringCaseProof("right", "left", case2, case1, adapter, proof)
    return None

def _impl__record_completed_method_b_covering_case_proof_if_safe(
    self,
    reason_record,
    analysis: FunctionReturnAnalysis,
    case1: ReturnCase,
    case2: ReturnCase,
    *,
    v2_blocker_signal=None,
) -> None:
    if not self.enable_completed_recovery_proofs:
        return
    from ...v2.loop_recurrence import LOOP_REASON_SPECS

    if reason_record.reason_id not in LOOP_REASON_SPECS:
        return
    object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
    if not isinstance(object_target_key, tuple) or len(object_target_key) != 5:
        return
    covering = self._method_b_covering_case_proof(case1, case2)
    if covering is None:
        return
    proof = covering.exact_proof
    relation = self._normalize_nested_tuple(object_target_key[4])
    if not self._method_b_covering_relation_matches_proof(
        relation,
        exact_side=covering.exact_side,
        summary_side=covering.summary_side,
        proof=proof,
    ):
        return
    v2_term_completion_signal = None
    if v2_blocker_signal is not None:
        try:
            from ...v2.loop_recurrence import (
                LoopExactTermRelationCompletionSignal,
            )
            from ...v2.production_signals import emit_loop_recurrence_signal

            v2_term_completion_signal = (
                LoopExactTermRelationCompletionSignal.from_pairwise_cases(
                    v2_blocker_signal,
                    case1,
                    case2,
                )
            )
            emit_loop_recurrence_signal(
                v2_term_completion_signal,
                producer_site_manifest_id="pairwise-loop-term-completed",
            )
        except Exception as exc:
            from ...v2.production_signals import (
                record_production_pilot_shadow_error,
            )

            record_production_pilot_shadow_error(exc)
    actions = tuple(build_unknown_recovery_actions([reason_record]))
    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, dict)
    ]
    existing_ids = {
        self._normalize_nested_tuple(item.get("proof_obligation_id"))
        for item in records
    }
    changed = self._append_completed_method_b_covering_case_evidence(
        records,
        existing_ids,
        actions,
        reason_id=reason_record.reason_id,
        object_target_key=object_target_key,
        covering=covering,
    )
    count_values = tuple(int(value) for value in (proof.count_values or (proof.count_value,)) if int(value) > 0)
    if self._cases_admit_reduction_count_values(
        covering.exact_case,
        covering.summary_case,
        covering.accumulator_proof,
        count_values,
    ):
        if v2_term_completion_signal is not None:
            try:
                from ...v2.loop_recurrence import (
                    LoopExactGuardPartitionCompletionSignal,
                )
                from ...v2.production_signals import emit_loop_recurrence_signal

                emit_loop_recurrence_signal(
                    LoopExactGuardPartitionCompletionSignal.from_pairwise_cases(
                        v2_term_completion_signal,
                        case1,
                        case2,
                    ),
                    producer_site_manifest_id="pairwise-loop-guard-completed",
                )
            except Exception as exc:
                from ...v2.production_signals import (
                    record_production_pilot_shadow_error,
                )

                record_production_pilot_shadow_error(exc)
        changed = self._append_completed_method_b_guard_partition_evidence(
            records,
            existing_ids,
            actions,
            reason_id=reason_record.reason_id,
            object_target_key=object_target_key,
            covering=covering,
        ) or changed
    if changed:
        analysis.completed_recovery_proof_evidence = tuple(records)

def _impl__append_completed_method_b_covering_case_evidence(
    self,
    records: List[Dict[str, Any]],
    existing_ids: set,
    actions: Sequence[Any],
    *,
    reason_id: str,
    object_target_key: Tuple[Any, ...],
    covering: _MethodBCoveringCaseProof,
) -> bool:
    action = self._method_b_recovery_action(
        actions,
        proof_kind=UnknownRecoveryProofKind.PROOF_BACKED_COVERING_CASE.value,
        proof_stage="method_b_covering_case",
    )
    if action is None:
        return False
    proof_id = self._normalize_nested_tuple(action.proof_obligation_id)
    if proof_id is None or proof_id in existing_ids:
        return False
    proof = covering.exact_proof
    count_values = tuple(int(value) for value in (proof.count_values or (proof.count_value,)) if int(value) > 0)
    records.append(
        {
            "object_derived": True,
            "status": "complete",
            "reason_id": reason_id,
            "proof_kind": action.proof_kind,
            "recovery_proof_kind": action.proof_kind,
            "proof_stage": action.proof_stage,
            "evidence_kind": action.evidence_kind,
            "required_evidence": tuple(action.required_evidence),
            "object_target_key": object_target_key,
            "proof_obligation_id": proof_id,
            "proof_source": "method_b_one_sided_summary_exact_terms",
            "proof_content": {
                "object_derived": True,
                "object_target_key": object_target_key,
                "seed_compensation": "proven",
                "term_sequence": "matched",
                "pure_side_effect_profile": "proven",
                "exact_side": covering.exact_side,
                "summary_side": covering.summary_side,
                "count_value": int(proof.count_value),
                "count_values": count_values,
                "exact_terms": tuple(term.stable_key() for term in proof.exact_terms),
                "expected_terms": tuple(term.stable_key() for term in proof.expected_terms),
                "constant_bias": int(proof.constant_bias),
                "result_size": int(proof.result_size),
                "covering_evidence": proof.evidence,
            },
        }
    )
    existing_ids.add(proof_id)
    return True

def _impl__append_completed_method_b_guard_partition_evidence(
    self,
    records: List[Dict[str, Any]],
    existing_ids: set,
    actions: Sequence[Any],
    *,
    reason_id: str,
    object_target_key: Tuple[Any, ...],
    covering: _MethodBCoveringCaseProof,
) -> bool:
    action = self._method_b_recovery_action(
        actions,
        proof_kind=UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION.value,
        proof_stage="method_b_guard_partition",
    )
    if action is None:
        return False
    proof_id = self._normalize_nested_tuple(action.proof_obligation_id)
    if proof_id is None or proof_id in existing_ids:
        return False
    proof = covering.exact_proof
    count_values = tuple(int(value) for value in (proof.count_values or (proof.count_value,)) if int(value) > 0)
    guard_evidence = (
        "reduction_count_implication"
        if len(count_values) == 1
        else "reduction_count_membership_implication"
    )
    records.append(
        {
            "object_derived": True,
            "status": "complete",
            "reason_id": reason_id,
            "proof_kind": action.proof_kind,
            "recovery_proof_kind": action.proof_kind,
            "proof_stage": action.proof_stage,
            "evidence_kind": action.evidence_kind,
            "required_evidence": tuple(action.required_evidence),
            "object_target_key": object_target_key,
            "proof_obligation_id": proof_id,
            "proof_source": "method_b_reduction_count_guard_partition",
            "proof_content": {
                "object_derived": True,
                "object_target_key": object_target_key,
                "guard_partition": "proven",
                "partition_coverage_proof": "covered",
                "exact_side": covering.exact_side,
                "summary_side": covering.summary_side,
                "count_value": int(proof.count_value),
                "count_values": count_values,
                "guard_evidence": guard_evidence,
            },
        }
    )
    existing_ids.add(proof_id)
    return True

def _impl__method_b_recovery_action(
    actions: Sequence[Any],
    *,
    proof_kind: str,
    proof_stage: str,
):
    return next(
        (
            candidate
            for candidate in actions
            if candidate.proof_stage == proof_stage and candidate.proof_kind == proof_kind
        ),
        None,
    )

def _impl__method_b_covering_relation_matches_proof(
    relation: Any,
    *,
    exact_side: str,
    summary_side: str,
    proof: _ExactReadonlyReductionProof,
) -> bool:
    if not isinstance(relation, tuple) or relation[0] != "method_b_closure_relation":
        return False
    fields = {
        item[0]: item[1]
        for item in relation[1:]
        if isinstance(item, tuple) and len(item) == 2
    }
    if fields.get("kind") != "one_sided_summary":
        return False
    if fields.get("exact_side") != exact_side or fields.get("summary_side") != summary_side:
        return False
    exact_terms = fields.get("exact_terms")
    if not isinstance(exact_terms, tuple) or not exact_terms:
        return False
    if tuple(exact_terms) != tuple(term.stable_key() for term in proof.exact_terms):
        return False
    try:
        exact_constant_bias = int(fields.get("exact_constant_bias"))
    except (TypeError, ValueError):
        return False
    return exact_constant_bias == int(proof.constant_bias)

def _impl__case_pair_comparison_result_size(
    self,
    left_case: Optional[ReturnCase],
    right_case: Optional[ReturnCase],
) -> Optional[int]:
    left_bits = self._case_comparison_bit_width(left_case)
    right_bits = self._case_comparison_bit_width(right_case)
    if left_bits is None or right_bits is None:
        return None
    if left_bits <= 0 or right_bits <= 0 or left_bits % 8 != 0 or right_bits % 8 != 0:
        return None
    if left_bits == right_bits:
        return left_bits // 8
    return None

def _impl__case_comparison_bit_width(self, case: Optional[ReturnCase]) -> Optional[int]:
    if case is None:
        return None
    surface = getattr(case, "comparison_surface", None)
    bits = getattr(surface, "explicit_bit_width", None)
    try:
        if bits is not None and int(bits) > 0:
            return int(bits)
    except (TypeError, ValueError):
        return None
    return None

def _impl__register_storage_identity_components(
    self,
    storage_identity: Optional[tuple],
) -> Optional[Tuple[int, int, int, int, int]]:
    normalized = tuple(storage_identity or ())
    if (
        len(normalized) == 2
        and normalized[0] == "parameter_storage"
        and isinstance(normalized[1], tuple)
    ):
        normalized = tuple(normalized[1])
    if len(normalized) != 6 or normalized[0] != "register_storage":
        return None
    try:
        return (
            int(normalized[1]),
            int(normalized[2]),
            int(normalized[3]),
            int(normalized[4]),
            int(normalized[5]),
        )
    except (TypeError, ValueError):
        return None

def _impl__method_b_closure_object_target_key(
    self,
    *,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    pair_id: str,
) -> Tuple[Any, ...]:
    """Object-derived target key for Method-B covering/guard proof backlog."""

    return (
        "method_b_closure",
        ("pair", pair_id),
        self._method_b_closure_side_object_key(
            "left",
            base_ctx.get("analysis1"),
            case1,
        ),
        self._method_b_closure_side_object_key(
            "right",
            base_ctx.get("analysis2"),
            case2,
        ),
        self._method_b_closure_relation_object_key(case1, case2),
    )

def _impl__method_b_closure_relation_object_key(
    self,
    case1: ReturnCase,
    case2: ReturnCase,
) -> Tuple[Any, ...]:
    left_readonly_ref = self._method_b_readonly_summary_ref(getattr(case1, "value_expr", None))
    right_readonly_ref = self._method_b_readonly_summary_ref(getattr(case2, "value_expr", None))
    left_summary_ref = self._method_b_summary_runtime_ref(getattr(case1, "value_expr", None))
    right_summary_ref = self._method_b_summary_runtime_ref(getattr(case2, "value_expr", None))
    if left_readonly_ref is not None and right_summary_ref is None:
        return self._method_b_one_sided_summary_relation(
            summary_side="left",
            summary_ref=left_readonly_ref,
            exact_side="right",
            exact_case=case2,
        )
    if right_readonly_ref is not None and left_summary_ref is None:
        return self._method_b_one_sided_summary_relation(
            summary_side="right",
            summary_ref=right_readonly_ref,
            exact_side="left",
            exact_case=case1,
        )
    if left_summary_ref is not None and right_summary_ref is not None:
        return (
            "method_b_closure_relation",
            ("kind", "dual_summary"),
            ("left_summary", self._method_b_summary_profile_key(left_summary_ref)),
            ("right_summary", self._method_b_summary_profile_key(right_summary_ref)),
        )
    return ("method_b_closure_relation", ("kind", "missing_method_b_summary"))

def _impl__method_b_one_sided_summary_relation(
    self,
    *,
    summary_side: str,
    summary_ref: ReadonlyReductionRef,
    exact_side: str,
    exact_case: ReturnCase,
) -> Tuple[Any, ...]:
    extracted = self._extract_readonly_reduction_terms_and_bias_from_expression(
        getattr(exact_case, "value_expr", None),
        getattr(exact_case, "parameters", ()) or (),
        getattr(summary_ref, "pointer_base_ref", None),
        program_is_big_endian=getattr(exact_case, "program_is_big_endian", None),
    )
    exact_terms_key: Any = ("exact_terms_unavailable",)
    exact_bias: Any = None
    if extracted is not None:
        exact_terms, exact_bias = extracted
        exact_terms_key = tuple(term.stable_key() for term in exact_terms)
    return (
        "method_b_closure_relation",
        ("kind", "one_sided_summary"),
        ("summary_side", summary_side),
        ("exact_side", exact_side),
        ("summary", self._method_b_summary_profile_key(summary_ref)),
        ("exact_terms", exact_terms_key),
        ("exact_constant_bias", exact_bias),
    )

def _impl__method_b_summary_profile_key(self, summary_ref) -> Tuple[Any, ...]:
    if isinstance(summary_ref, CountedLoopSummaryRef):
        runtime_ref_key = self._counted_loop_summary_runtime_profile_key(summary_ref)
        loop_summary_key = self._counted_loop_summary_loop_profile_key(getattr(summary_ref, "loop_summary", None))
        term_contract = self._counted_loop_summary_contract_key(summary_ref)
        count_identities = self._counted_loop_summary_count_identities(summary_ref)
    else:
        runtime_ref_key = self._semantic_key_or_stable_key_or_none(summary_ref)
        loop_summary_key = self._semantic_key_or_stable_key_or_none(getattr(summary_ref, "loop_summary", None))
        term_contract = self._readonly_reduction_term_sequence_contract_key(
            summary_ref,
            result_size=getattr(summary_ref, "result_size", None),
        )
        term_contract = self._method_b_normalized_term_contract_key(summary_ref, term_contract)
        count_identities = tuple(sorted(self._readonly_count_identity_keys(summary_ref), key=repr))
    return (
        "method_b_summary_profile",
        ("runtime_ref", runtime_ref_key),
        ("loop_summary", loop_summary_key),
        ("term_contract", term_contract),
        ("count_identities", tuple(sorted(count_identities, key=repr))),
    )

def _impl__method_b_value_key_or_none(self, value: Any):
    key = self._semantic_key_or_stable_key_or_none(value)
    if key is not None:
        return self._method_b_key_with_explicit_optional_none(key)
    structural_key = getattr(value, "structural_key", None)
    if callable(structural_key):
        try:
            return self._method_b_key_with_explicit_optional_none(structural_key(budget=256))
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
    return None

def _impl__method_b_key_with_explicit_optional_none(self, value: Any):
    if value is None:
        return ("optional_none",)
    if isinstance(value, tuple):
        return tuple(self._method_b_key_with_explicit_optional_none(item) for item in value)
    if isinstance(value, list):
        return tuple(self._method_b_key_with_explicit_optional_none(item) for item in value)
    return value

def _impl__method_b_normalized_term_contract_key(
    self,
    readonly_ref: ReadonlyReductionRef,
    term_contract: Optional[tuple],
) -> Optional[tuple]:
    if not isinstance(term_contract, tuple) or not term_contract:
        return term_contract
    if term_contract[0] != "loop_summary_method_b" or len(term_contract) < 9:
        return term_contract
    pointer_base = self._semantic_key_or_stable_key_or_none(getattr(readonly_ref, "pointer_base_ref", None))
    count_identities = tuple(sorted(self._readonly_count_identity_keys(readonly_ref), key=repr))
    count_identity = count_identities[0] if count_identities else None
    if pointer_base is None or count_identity is None:
        return term_contract
    term_sequence = term_contract[5]
    if not isinstance(term_sequence, tuple) or len(term_sequence) < 7:
        return term_contract
    try:
        result_size = max(1, int(getattr(readonly_ref, "result_size", 0) or term_sequence[6]))
    except (TypeError, ValueError):
        return term_contract
    return (
        "readonly_reduction_term_sequence_contract",
        str(getattr(readonly_ref, "reduction_kind", None) or "memory_sum"),
        pointer_base,
        count_identity,
        term_contract[3],
        result_size,
        term_sequence[3],
        term_contract[4],
        getattr(readonly_ref, "constant_bias", 0),
        term_sequence[5],
        bool(getattr(readonly_ref, "signed_counter", False)),
        term_contract[6],
        term_contract[7],
        term_contract[8],
    )

def _impl__opaque_unknown_return_object_evidence_from_target(
    self,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    target = self._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 4:
        return None
    sides = []
    opaque_refs: List[Any] = []
    seen_refs = set()
    for side in target[2:4]:
        side_tuple = self._normalize_nested_tuple(side)
        if not isinstance(side_tuple, tuple) or len(side_tuple) < 6:
            return None
        side_label = side_tuple[1]
        function_ref = side_tuple[2]
        return_storage = side_tuple[3]
        partition_member = side_tuple[4]
        unresolved_locations = side_tuple[5]
        side_refs = self._opaque_unknown_refs_from_value(
            (partition_member, unresolved_locations)
        )
        for ref in side_refs:
            key = repr(ref)
            if key not in seen_refs:
                seen_refs.add(key)
                opaque_refs.append(ref)
        sides.append(
            (
                "return_side",
                ("side", side_label),
                ("function_ref", function_ref),
                ("return_storage", return_storage),
                ("return_case_origin", partition_member),
                ("unresolved_locations", unresolved_locations),
                ("opaque_unknown_refs", side_refs),
            )
        )
    if not opaque_refs:
        return None
    return (
        "opaque_unknown_return_object_evidence",
        ("opaque_unknown_refs", tuple(sorted(opaque_refs, key=repr))),
        ("return_sides", tuple(sides)),
        ("return_width_policy", tuple(side[3] for side in target[2:4] if isinstance(side, tuple) and len(side) >= 4)),
        ("evidence_status", "object_evidence_collected"),
    )

def _impl__opaque_unknown_refs_from_value(cls, value: Any) -> Tuple[Any, ...]:
    refs: List[Any] = []
    seen = set()

    def visit(node: Any) -> None:
        normalized = cls._normalize_nested_tuple(node)
        if isinstance(normalized, tuple):
            if (
                len(normalized) == 2
                and normalized[0] in {"runtime_ref", "unknown_runtime_ref"}
                and isinstance(normalized[1], tuple)
                and len(normalized[1]) >= 2
                and normalized[1][0] == "opaque_unknown"
                and normalized[1][1] == "void"
            ):
                key = repr(normalized)
                if key not in seen:
                    seen.add(key)
                    refs.append(normalized)
            for item in normalized:
                visit(item)
        elif isinstance(normalized, list):
            for item in normalized:
                visit(item)
        elif isinstance(normalized, dict):
            for key, item in normalized.items():
                visit(key)
                visit(item)

    visit(value)
    return tuple(sorted(refs, key=repr))

def _impl__pcode_origin_cross_binary_shape_key(origin_key: Any) -> Optional[Tuple[Any, ...]]:
    if not (isinstance(origin_key, tuple) and origin_key and origin_key[0] == "pcode_op"):
        return None
    if (
        len(origin_key) >= 8
        and isinstance(origin_key[2], tuple)
        and len(origin_key[2]) == 3
        and origin_key[2][0] == "function_entry"
        and isinstance(origin_key[3], tuple)
        and len(origin_key[3]) == 3
        and origin_key[3][0] == "seq_target"
    ):
        try:
            relative_target = int(origin_key[3][2]) - int(origin_key[2][2])
            seq_time = int(origin_key[4])
            seq_order = int(origin_key[5])
            local_op_ordinal = int(origin_key[7])
        except (TypeError, ValueError):
            return None
        return (
            "pcode_op_cross_binary_shape",
            ("function_entry_space", origin_key[2][1]),
            ("target_space", origin_key[3][1]),
            ("relative_target_offset", relative_target),
            ("seq_time", seq_time),
            ("seq_order", seq_order),
            ("opcode", origin_key[6]),
            ("local_op_ordinal", local_op_ordinal),
        )
    if len(origin_key) >= 6:
        return (
            "pcode_op_cross_binary_shape",
            ("address_offset", origin_key[1]),
            ("seq_time", origin_key[2]),
            ("seq_order", origin_key[3]),
            ("block_index", origin_key[4]),
            ("mnemonic", origin_key[5]),
        )
    return None

def _impl__collect_summary_parameter_refs(self, *expressions: Any) -> Tuple[Any, ...]:
    refs: List[Tuple[Any, ...]] = []
    seen = set()
    for expr in expressions:
        for parameter in self._collect_parameter_expression_nodes(expr):
            name = str(getattr(parameter, "name", "") or "")
            raw_index = getattr(parameter, "value", None)
            try:
                index = int(raw_index)
            except (TypeError, ValueError):
                index = None
            if not (name.startswith("summary_rec_") or (index is not None and index >= 10000)):
                continue
            item = (
                "summary_parameter",
                ("index", index),
                ("name", name or None),
                ("bit_width", int(expression_smt_bit_width(parameter) or 0) or None),
                ("expression", self._expression_runtime_object_key(parameter)),
            )
            if item in seen:
                continue
            seen.add(item)
            refs.append(item)
    return tuple(sorted(refs, key=repr))

def _impl__collect_parameter_expression_nodes(self, expr: Any) -> Tuple[Any, ...]:
    result: List[Any] = []
    self._collect_parameter_expression_nodes_into(expr, result)
    return tuple(result)

def _impl__collect_parameter_expression_nodes_into(self, expr: Any, result: List[Any]) -> None:
    if expr is None or getattr(expr, "expr_type", None) is None:
        return
    if expr.expr_type == ExpressionType.PARAMETER:
        result.append(expr)
        return
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for condition, value in expr.value:
            if condition is not None:
                self._collect_parameter_expression_nodes_into(condition.expression, result)
            self._collect_parameter_expression_nodes_into(value, result)
        return
    for operand in getattr(expr, "operands", []) or []:
        self._collect_parameter_expression_nodes_into(operand, result)

def _impl__unsupported_ops_include_memory_or_effect(unsupported_ops: set[Any]) -> bool:
    for op in unsupported_ops:
        if not isinstance(op, tuple):
            continue
        rendered = repr(op)
        if any(marker in rendered for marker in ("LOAD", "STORE", "CALL", "INDIRECT", "MULTIEQUAL")):
            return True
    return False

def _impl__unknown_expression_classification_key(self, expr: Any) -> Tuple[str, Tuple[Any, ...]]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    if getattr(runtime_ref, "deferred_call_ref", None) is not None:
        kind = "deferred_call_unknown"
    else:
        raw_kind = getattr(runtime_ref, "kind", None)
        kind = str(raw_kind or "opaque_unknown")
    runtime_key = self._diagnostic_key_or_semantic_key_or_stable_key_or_none(runtime_ref)
    if runtime_key is not None:
        ref_key = ("unknown_runtime_ref", runtime_key)
    else:
        ref_key = ("unknown_expression", self._expression_runtime_object_key(expr))
    return kind, ref_key

def _impl__object_target_contains_void_opaque_unknown(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if (
            len(normalized) >= 2
            and normalized[0] == "opaque_unknown"
            and normalized[1] == "void"
        ):
            return True
        return any(cls._object_target_contains_void_opaque_unknown(item) for item in normalized)
    if isinstance(normalized, list):
        return any(cls._object_target_contains_void_opaque_unknown(item) for item in normalized)
    if isinstance(normalized, dict):
        return any(
            cls._object_target_contains_void_opaque_unknown(key)
            or cls._object_target_contains_void_opaque_unknown(item)
            for key, item in normalized.items()
        )
    return False

def _impl__method_b_closure_side_object_key(
    self,
    side_label: str,
    analysis: Optional[FunctionReturnAnalysis],
    case: ReturnCase,
) -> Tuple[Any, ...]:
    value_expr = getattr(case, "value_expr", None)
    return (
        "method_b_closure_side",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        self._readonly_return_case_partition_member_object_key(case),
        (
            "loop_value",
            self._method_b_loop_value_object_key(value_expr),
        ),
        (
            "guards",
            tuple(
                self._return_condition_object_key(condition)
                for condition in (getattr(case, "conditions", None) or ())
            ),
        ),
    )

def _impl__semantic_key_or_stable_key_or_none(value: Any):
    for name in ("pairwise_semantic_key", "semantic_key", "stable_key"):
        key_fn = getattr(value, name, None)
        if callable(key_fn):
            try:
                key = key_fn()
            except (AttributeError, TypeError, ValueError, RecursionError):
                key = None
            if key is not None:
                return key
    return None

def _impl__diagnostic_key_or_semantic_key_or_stable_key_or_none(value: Any):
    for name in ("diagnostic_key", "pairwise_semantic_key", "semantic_key", "stable_key"):
        key_fn = getattr(value, name, None)
        if callable(key_fn):
            try:
                key = key_fn()
            except (AttributeError, TypeError, ValueError, RecursionError):
                key = None
            if key is not None:
                return key
    return None

def _impl__count_identity_components_compatible(
    self,
    left_storage: Optional[tuple],
    left_index: Optional[tuple],
    right_storage: Optional[tuple],
    right_index: Optional[tuple],
) -> bool:
    if left_storage is not None and right_storage is not None:
        if left_storage == right_storage:
            return True
        return False
    return left_index is not None and right_index is not None and left_index == right_index

def _impl__count_storage_low_projection_compatible(
    self,
    left_storage: tuple,
    right_storage: tuple,
) -> bool:
    left_register = self._register_storage_identity_components(left_storage)
    right_register = self._register_storage_identity_components(right_storage)
    if left_register is None or right_register is None:
        return False
    if left_register[:3] != right_register[:3]:
        return False
    left_low, left_size = int(left_register[3]), int(left_register[4])
    right_low, right_size = int(right_register[3]), int(right_register[4])
    if left_low != right_low:
        return False
    return left_size <= right_size or right_size <= left_size

def _impl__replace_expression_node(
    self,
    expr: Expression,
    target: Expression,
    replacement: Expression,
) -> Expression:
    if expr.equals(target):
        return replacement
    if getattr(expr, "expr_type", None) == ExpressionType.PHI:
        branches = []
        for cond, value in getattr(expr, "value", None) or []:
            new_cond = cond
            if cond is not None and getattr(cond, "expression", None) is not None:
                new_cond = Condition(
                    self._replace_expression_node(cond.expression, target, replacement),
                    getattr(cond, "negated", False),
                )
            branches.append((new_cond, self._replace_expression_node(value, target, replacement)))
        return expr.clone_with(value=branches)
    operands = getattr(expr, "operands", None) or []
    if not operands:
        return expr
    return expr.clone_with(
        operands=[
            self._replace_expression_node(operand, target, replacement)
            for operand in operands
        ]
    )

def _impl__coerce_expression_to_size(
    self,
    expr: Expression,
    target_size: int,
    *,
    signed: bool = False,
) -> Expression:
    target_size = max(1, int(target_size or 0))
    expr_size = int(getattr(expr, "size", 0) or 0)
    if expr_size <= 0:
        expr_bits = int(expression_smt_bit_width(expr) or 0)
        expr_size = max(1, (expr_bits + 7) // 8) if expr_bits > 0 else target_size
    if expr_size == target_size:
        return expr
    if expr_size > target_size:
        narrowed = Expression.binary_op("SUBPIECE", expr, Expression.constant(0, size=4))
        narrowed.size = target_size
        return narrowed
    widened = Expression.unary_op("INT_SEXT" if signed else "INT_ZEXT", expr)
    widened.size = target_size
    return widened

def _impl__expression_prefers_signed_extension(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    data_type = str(getattr(expr, "data_type", "") or "").lower()
    if "unsigned" in data_type or data_type.startswith("u"):
        return False
    if any(token in data_type for token in ("signed", "int", "long", "short", "char")):
        return True
    return False

def _impl__extract_affine_limit_trip_count_candidate(
    self,
    start: Expression,
    limit: Expression,
    step: int,
) -> Optional[Expression]:
    if getattr(limit, "expr_type", None) != ExpressionType.BINARY_OP or getattr(limit, "operator", None) != "INT_ADD":
        return None
    left, right = list(getattr(limit, "operands", ()) or ())
    for maybe_start, maybe_scaled in ((left, right), (right, left)):
        if not self._expressions_same_shape_ignoring_runtime(maybe_start, start):
            continue
        candidate = self._extract_constant_scaled_expression(maybe_scaled, step)
        if candidate is not None:
            return candidate
    return None

def _impl__extract_constant_scaled_expression(self, expr: Expression, factor: int) -> Optional[Expression]:
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP or getattr(expr, "operator", None) != "INT_MULT":
        return None
    left, right = list(getattr(expr, "operands", ()) or ())
    for maybe_const, candidate in ((left, right), (right, left)):
        if getattr(maybe_const, "expr_type", None) != ExpressionType.CONSTANT:
            continue
        try:
            if int(getattr(maybe_const, "value", 0) or 0) == int(factor):
                return candidate
        except (TypeError, ValueError):
            continue
    return None

def _impl__expression_is_zero(self, expr: Expression) -> bool:
    if getattr(expr, "expr_type", None) != ExpressionType.CONSTANT:
        return False
    try:
        return int(getattr(expr, "value", 0) or 0) == 0
    except (TypeError, ValueError):
        return False

def _impl__expression_is_provably_nonnegative_under_conditions(
    self,
    expr: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    width_bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
    if width_bits <= 1:
        return True
    if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
        try:
            raw = int(getattr(expr, "value", 0) or 0) % (1 << width_bits)
            return raw < (1 << (width_bits - 1))
        except Exception:
            return False
    query = self._build_nonnegative_query(expr, conditions, parameters, width_bits)
    if not query:
        return False
    result = Z3Solver(timeout=1, debug=False).check_equivalence_direct(query)
    return result.status == SolverStatus.UNSAT

def _impl__combined_summary_conditions(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
) -> List[Condition]:
    left_conditions = left_case.summary_conditions if left_case.summary_conditions is not None else left_case.conditions
    right_conditions = right_case.summary_conditions if right_case.summary_conditions is not None else right_case.conditions
    return ConditionSimplifier.simplify_conditions_object_centric(
        list(left_conditions or []) + list(right_conditions or [])
    )

def _impl__auxiliary_semantic_parameter_sources(
    self,
    base_ctx: Optional[Mapping[str, Any]],
) -> Tuple[ParameterInfo, ...]:
    if not isinstance(base_ctx, Mapping):
        return ()
    sources: List[ParameterInfo] = []
    for key in ("params1", "params2"):
        for param in base_ctx.get(key, ()) or ():
            if isinstance(param, ParameterInfo):
                sources.append(param)
    return tuple(sources)

def _impl__auxiliary_semantic_hints_by_index(
    self,
    semantic_parameter_sources: Sequence[ParameterInfo],
) -> Dict[int, Tuple[int, str, int]]:
    hints: Dict[int, Tuple[int, str, int]] = {}
    for source in semantic_parameter_sources or ():
        try:
            index = int(getattr(source, "index"))
            bit_width = int(getattr(source, "bit_width"))
            narrow_bits = getattr(source, "semantic_narrow_bits", None)
            narrow_bits = int(narrow_bits) if narrow_bits is not None else None
        except (TypeError, ValueError):
            continue
        signedness = getattr(source, "semantic_signedness", None)
        if bit_width <= 0 or narrow_bits is None or narrow_bits <= 0:
            continue
        if narrow_bits >= bit_width or signedness not in {"signed", "unsigned"}:
            continue
        current = hints.get(index)
        if current is None or bit_width > current[2]:
            hints[index] = (narrow_bits, signedness, bit_width)
    return hints

def _impl__apply_auxiliary_semantic_hint(
    self,
    candidate: Dict[str, Any],
    *,
    size: int,
    semantic_by_index: Mapping[int, Tuple[int, str, int]],
) -> None:
    try:
        index = int(candidate.get("index"))
        bit_width = max(1, int(size)) * 8
    except (TypeError, ValueError):
        return
    hint = semantic_by_index.get(index)
    if hint is None:
        return
    narrow_bits, signedness, source_bit_width = hint
    if source_bit_width != bit_width or narrow_bits >= bit_width:
        return
    candidate["semantic_narrow_bits"] = int(narrow_bits)
    candidate["semantic_signedness"] = signedness

def _impl__build_auxiliary_parameter_infos(
    self,
    symbol_specs: Sequence[Dict[str, Any]],
) -> List[ParameterInfo]:
    infos: List[ParameterInfo] = []
    for spec in sorted(
        symbol_specs or [],
        key=lambda item: (
            self._auxiliary_identity_sort_key(item.get("identity")),
            int(item.get("size", 0) or 0),
        ),
    ):
        aux_name = str(spec.get("aux_name") or "")
        if not aux_name:
            continue
        infos.append(
            ParameterInfo(
                original_name=aux_name,
                smt_name=aux_name,
                bit_width=max(1, int(spec.get("size", 0) or 4)) * 8,
                index=int(spec.get("aux_index", -1) or -1),
                is_signed=bool(spec.get("is_signed", True)),
                semantic_narrow_bits=(
                    int(spec["semantic_narrow_bits"])
                    if spec.get("semantic_narrow_bits") is not None
                    else None
                ),
                semantic_signedness=spec.get("semantic_signedness"),
            )
        )
    return infos

def _impl__auxiliary_identity_sort_key(self, identity) -> Tuple[int, str]:
    if not isinstance(identity, tuple) or not identity:
        return (9, "")
    kind = identity[0]
    if kind == "parameter_index" and len(identity) >= 2:
        try:
            return (0, f"{int(identity[1]):08d}")
        except (TypeError, ValueError):
            return (0, repr(identity[1]))
    if kind == "parameter_storage" and len(identity) >= 2:
        return (1, repr(identity[1]))
    return (8, repr(identity))

def _impl__clone_auxiliary_residue_bias_terms(
    self,
    bias_terms: Sequence[Tuple[int, int, Any]],
    identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
) -> Optional[Tuple[Tuple[int, int, Any], ...]]:
    cloned_terms = []
    for modulus, residue, bias_expr in bias_terms:
        cloned_bias_expr = self._clone_auxiliary_expression_for_smt(
            bias_expr,
            identity_to_spec,
        )
        if cloned_bias_expr is None:
            return None
        cloned_terms.append((int(modulus), int(residue), cloned_bias_expr))
    return tuple(cloned_terms)

def _impl__cases_have_equivalent_summary_conditions(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
) -> bool:
    left_conditions = left_case.summary_conditions if left_case.summary_conditions is not None else left_case.conditions
    right_conditions = right_case.summary_conditions if right_case.summary_conditions is not None else right_case.conditions
    left_normalized = ConditionSimplifier.simplify_conditions_object_centric(list(left_conditions or []))
    right_normalized = ConditionSimplifier.simplify_conditions_object_centric(list(right_conditions or []))
    if not left_normalized and not right_normalized:
        return True
    parameters = list(getattr(left_case, "parameters", None) or []) + list(
        getattr(right_case, "parameters", None) or []
    )
    return self._condition_set_implies(
        left_normalized,
        right_normalized,
        parameters,
    ) and self._condition_set_implies(
        right_normalized,
        left_normalized,
        parameters,
    )

def _impl__cases_have_pair_local_summary_guard_compatibility(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
) -> bool:
    if not self._cases_have_equivalent_summary_conditions(left_case, right_case):
        return False
    return self._case_conditions_cover_runtime_summary_guards(
        left_case,
    ) and self._case_conditions_cover_runtime_summary_guards(right_case)

def _impl__iter_expression_nodes(self, expr: Optional[Expression]):
    if expr is None:
        return
    yield expr
    if getattr(expr, "expr_type", None) == ExpressionType.PHI:
        for condition, value in getattr(expr, "value", None) or ():
            if condition is not None:
                yield from self._iter_expression_nodes(getattr(condition, "expression", None))
            yield from self._iter_expression_nodes(value)
        return
    for operand in getattr(expr, "operands", None) or ():
        yield from self._iter_expression_nodes(operand)

def _impl__condition_delta_region_is_covered_by_cases(
    self,
    domain_conditions: Sequence[Condition],
    excluded_conditions: Sequence[Condition],
    covering_cases: Sequence[ReturnCase],
    domain_case: ReturnCase,
    excluded_case: ReturnCase,
) -> bool:
    excluded_conjunction = Condition.combine_and(list(excluded_conditions or []))
    if excluded_conjunction is None:
        return True

    proof_conditions: List[Condition] = list(domain_conditions or [])
    proof_conditions.append(excluded_conjunction.negate())

    covering_condition = self._case_union_condition(covering_cases)
    if covering_condition is None:
        return self._condition_region_is_unsat_for_cases(
            proof_conditions,
            [domain_case, excluded_case, *list(covering_cases or [])],
        )
    proof_conditions.append(covering_condition.negate())
    return self._condition_region_is_unsat_for_cases(
        proof_conditions,
        [domain_case, excluded_case, *list(covering_cases or [])],
    )

def _impl__case_summary_condition_basis(self, case: ReturnCase) -> List[Condition]:
    return list(case.summary_conditions if case.summary_conditions is not None else case.conditions)

def _impl__case_union_condition(self, cases: Sequence[ReturnCase]) -> Optional[Condition]:
    disjuncts = []
    for case in cases or []:
        case_conditions = list(getattr(case, "conditions", None) or [])
        if not case_conditions:
            return Condition(
                Expression.binary_op(
                    "INT_EQUAL",
                    Expression.constant(1, size=1),
                    Expression.constant(1, size=1),
                )
            )
        conjunction = Condition.combine_and(case_conditions)
        if conjunction is not None:
            disjuncts.append(self._condition_as_bool_expression(conjunction))
    if not disjuncts:
        return None
    union_expr = disjuncts[0]
    for disjunct in disjuncts[1:]:
        union_expr = Expression.binary_op("BOOL_OR", union_expr, disjunct)
    return Condition(union_expr)

def _impl__condition_as_bool_expression(self, condition: Condition) -> Expression:
    if condition.negated:
        return Expression.unary_op("BOOL_NEGATE", condition.expression)
    return condition.expression

def _impl__condition_region_is_unsat_for_cases(
    self,
    conditions: Sequence[Condition],
    cases: Sequence[ReturnCase],
) -> bool:
    parameters: List[Dict[str, Any]] = []
    for case in cases or []:
        parameters.extend(list(getattr(case, "parameters", None) or []))
    identity_conditions = self._conditions_with_object_identity_parameter_symbols(
        conditions,
        parameters,
    )
    solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
    if solver_result is not None:
        return solver_result
    return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)

def _impl__condition_set_implies(
    self,
    premises: Sequence[Condition],
    conclusions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    if not conclusions:
        return True
    for conclusion in conclusions or []:
        implication_conditions = list(premises or []) + [conclusion.negate()]
        identity_conditions = self._conditions_with_object_identity_parameter_symbols(
            implication_conditions,
            parameters,
        )
        solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
        if solver_result is not None:
            if not solver_result:
                return False
            continue
        if not ConditionSimplifier.object_centric_is_contradiction(identity_conditions):
            return False
    return True

def _impl__condition_set_is_unsat(
    self,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    if self._conditions_have_parameter_mask_constant_conflict(list(conditions or ())):
        return True
    identity_conditions = self._conditions_with_object_identity_parameter_symbols(
        list(conditions or []),
        parameters,
    )
    if self._conditions_have_parameter_mask_constant_conflict(identity_conditions):
        return True
    solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
    if solver_result is not None:
        return solver_result
    return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)

def _impl__conditions_have_parameter_mask_constant_conflict(
    self,
    conditions: Sequence[Condition],
) -> bool:
    constants: Dict[Tuple[Any, ...], Tuple[int, int]] = {}
    mask_equalities: List[Tuple[Tuple[Any, ...], int, int, int]] = []
    for condition in conditions or ():
        equality = self._condition_positive_equality_operands(condition)
        if equality is None:
            continue
        left, right = equality
        constant_equality = self._parameter_constant_equality(left, right)
        if constant_equality is None:
            constant_equality = self._parameter_constant_equality(right, left)
        if constant_equality is not None:
            key, value, bits = constant_equality
            previous = constants.get(key)
            if previous is not None and previous != (value, bits):
                return True
            constants[key] = (value, bits)
            continue
        mask_equality = self._parameter_mask_equality(left, right)
        if mask_equality is None:
            mask_equality = self._parameter_mask_equality(right, left)
        if mask_equality is not None:
            mask_equalities.append(mask_equality)
    for key, mask, expected, bits in mask_equalities:
        known = constants.get(key)
        if known is None:
            continue
        known_value, known_bits = known
        width_bits = max(1, int(bits or known_bits or 0))
        width_mask = (1 << width_bits) - 1
        if (known_value & mask & width_mask) != (expected & width_mask):
            return True
    return False

def _impl__condition_positive_equality_operands(
    self,
    condition: Condition,
) -> Optional[Tuple[Expression, Expression]]:
    expr = getattr(condition, "expression", None)
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    operator = getattr(expr, "operator", None)
    negated = bool(getattr(condition, "negated", False))
    if operator == "INT_NOTEQUAL" and negated:
        pass
    elif operator == "INT_EQUAL" and not negated:
        pass
    else:
        return None
    operands = list(getattr(expr, "operands", ()) or ())
    if len(operands) != 2:
        return None
    return operands[0], operands[1]

def _impl__parameter_constant_equality(
    self,
    maybe_param_expr: Expression,
    maybe_const_expr: Expression,
) -> Optional[Tuple[Tuple[Any, ...], int, int]]:
    const_value = self._raw_constant_value(maybe_const_expr)
    if const_value is None:
        return None
    affine = self._parameter_plus_constant_affine(maybe_param_expr)
    if affine is None:
        return None
    key, offset, bits = affine
    width_mask = (1 << max(1, bits)) - 1
    return key, (int(const_value) - int(offset)) & width_mask, bits

def _impl__parameter_mask_equality(
    self,
    maybe_mask_expr: Expression,
    maybe_const_expr: Expression,
) -> Optional[Tuple[Tuple[Any, ...], int, int, int]]:
    const_value = self._raw_constant_value(maybe_const_expr)
    if const_value is None:
        return None
    mask_expr = maybe_mask_expr
    if (
        getattr(mask_expr, "expr_type", None) == ExpressionType.BINARY_OP
        and getattr(mask_expr, "operator", None) == "INT_SUB"
    ):
        operands = list(getattr(mask_expr, "operands", ()) or ())
        if len(operands) != 2:
            return None
        sub_const = self._raw_constant_value(operands[1])
        if sub_const is None:
            return None
        mask_expr = operands[0]
        const_value = int(const_value) + int(sub_const)
    if getattr(mask_expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if getattr(mask_expr, "operator", None) != "INT_AND":
        return None
    operands = list(getattr(mask_expr, "operands", ()) or ())
    if len(operands) != 2:
        return None
    for maybe_mask, maybe_param in ((operands[0], operands[1]), (operands[1], operands[0])):
        mask_value = self._raw_constant_value(maybe_mask)
        key = self._parameter_expression_key(maybe_param)
        if mask_value is None or key is None:
            continue
        bits = max(1, int(getattr(maybe_param, "size", 0) or getattr(mask_expr, "size", 0) or 4) * 8)
        width_mask = (1 << bits) - 1
        return key, int(mask_value) & width_mask, int(const_value) & width_mask, bits
    return None

def _impl__parameter_plus_constant_affine(
    self,
    expr: Expression,
) -> Optional[Tuple[Tuple[Any, ...], int, int]]:
    key = self._parameter_expression_key(expr)
    if key is not None:
        bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
        return key, 0, bits
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    operator = getattr(expr, "operator", None)
    operands = list(getattr(expr, "operands", ()) or ())
    if len(operands) != 2:
        return None
    bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
    width_mask = (1 << bits) - 1
    if operator == "INT_ADD":
        for left, right in ((operands[0], operands[1]), (operands[1], operands[0])):
            affine = self._parameter_plus_constant_affine(left)
            const_value = self._raw_constant_value(right)
            if affine is None or const_value is None:
                continue
            key, offset, affine_bits = affine
            return key, (int(offset) + int(const_value)) & width_mask, max(bits, affine_bits)
    if operator == "INT_SUB":
        affine = self._parameter_plus_constant_affine(operands[0])
        const_value = self._raw_constant_value(operands[1])
        if affine is None or const_value is None:
            return None
        key, offset, affine_bits = affine
        return key, (int(offset) - int(const_value)) & width_mask, max(bits, affine_bits)
    return None

def _impl__parameter_expression_key(self, expr: Expression) -> Optional[Tuple[Any, ...]]:
    if getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
        return None
    return (
        "parameter",
        str(getattr(expr, "name", "") or ""),
        int(getattr(expr, "value", -1) or -1),
        max(1, int(getattr(expr, "size", 0) or 4)),
    )

def _impl__conditions_are_semantically_equivalent(
    self,
    left_condition: Condition,
    right_condition: Condition,
) -> bool:
    if left_condition.equals(right_condition):
        return True
    return self._condition_implies(left_condition, right_condition) and self._condition_implies(
        right_condition,
        left_condition,
    )

def _impl__condition_implies(
    self,
    premise: Condition,
    conclusion: Condition,
) -> bool:
    implication_conditions = [premise, conclusion.negate()]
    solver_result = ConditionSMTOracle.conjunction_is_unsat(implication_conditions)
    if solver_result is not None:
        return solver_result
    return ConditionSimplifier.object_centric_is_contradiction(implication_conditions)

def _impl__storage_info_from_parameter_descriptor(self, parameter: Dict[str, Any]) -> Optional[StorageInfo]:
    storage = parameter.get("storage_info", parameter.get("storage")) if isinstance(parameter, dict) else None
    if isinstance(storage, StorageInfo):
        return storage
    if isinstance(storage, dict):
        try:
            return StorageInfo(**storage)
        except Exception:
            return None
    return None

def _impl__parameter_descriptor_storage_identity_key(self, parameter: Dict[str, Any]) -> Optional[tuple]:
    storage_info = self._storage_info_from_parameter_descriptor(parameter)
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if not callable(storage_key_fn):
        return None
    try:
        storage_key = storage_key_fn()
    except (AttributeError, TypeError, ValueError):
        return None
    if storage_key is None:
        return None
    return ("parameter_storage", tuple(storage_key))

def _impl__parameter_descriptor_index_identity_key(self, parameter: Dict[str, Any]) -> Optional[tuple]:
    if not isinstance(parameter, dict):
        return None
    try:
        index = parameter.get("index")
        if index is not None and int(index) >= 0:
            return ("parameter", int(index))
    except (TypeError, ValueError):
        return None
    return None

def _impl__parameter_descriptor_identity_keys(self, parameter: Dict[str, Any]) -> set[tuple]:
    identities: set[tuple] = set()
    if not isinstance(parameter, dict):
        return identities
    try:
        index = parameter.get("index")
        if index is not None and int(index) >= 0:
            identities.add(("parameter", int(index)))
    except (TypeError, ValueError):
        pass
    storage_info = self._storage_info_from_parameter_descriptor(parameter)
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if callable(storage_key_fn):
        try:
            storage_key = storage_key_fn()
        except (AttributeError, TypeError, ValueError):
            storage_key = None
        if storage_key is not None:
            identities.add(("parameter_storage", tuple(storage_key)))
    return identities

def _impl__parameter_expression_storage_identity_key(self, expr: Expression) -> Optional[tuple]:
    storage_info = getattr(expr, "storage_info", None)
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if not callable(storage_key_fn):
        return None
    try:
        storage_key = storage_key_fn()
    except (AttributeError, TypeError, ValueError):
        return None
    if storage_key is None:
        return None
    return ("parameter_storage", tuple(storage_key))

def _impl__parameter_expression_index_identity_key(self, expr: Expression) -> Optional[tuple]:
    try:
        index = getattr(expr, "value", None)
        if index is not None and int(index) >= 0:
            return ("parameter", int(index))
    except (TypeError, ValueError):
        return None
    return None

def _impl__parameter_expression_identity_keys(self, expr: Expression) -> set[tuple]:
    identities: set[tuple] = set()
    try:
        index = getattr(expr, "value", None)
        if index is not None and int(index) >= 0:
            identities.add(("parameter", int(index)))
    except (TypeError, ValueError):
        pass
    storage_info = getattr(expr, "storage_info", None)
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if callable(storage_key_fn):
        try:
            storage_key = storage_key_fn()
        except (AttributeError, TypeError, ValueError):
            storage_key = None
        if storage_key is not None:
            identities.add(("parameter_storage", tuple(storage_key)))
    return identities

def _impl__solve_affine_equality(
    self,
    left_affine: tuple[int, int],
    right_affine: tuple[int, int],
) -> Optional[int]:
    left_coeff, left_bias = left_affine
    right_coeff, right_bias = right_affine
    coeff_delta = int(left_coeff) - int(right_coeff)
    bias_delta = int(right_bias) - int(left_bias)
    if coeff_delta == 0:
        return None
    if bias_delta % coeff_delta != 0:
        return None
    solved = bias_delta // coeff_delta
    return int(solved) if solved > 0 else None

def _impl__accumulator_proof_supports_count_bit_width(
    self,
    case: ReturnCase,
    accumulator_proof,
    candidate_bits: int,
) -> bool:
    candidate_bits = max(1, int(candidate_bits))
    proof_bits = self._reduction_count_bit_width(accumulator_proof)
    if candidate_bits == proof_bits:
        return True
    if candidate_bits > proof_bits:
        return False
    for expr in self._accumulator_proof_count_surface_expressions(accumulator_proof):
        if self._expression_contains_reduction_count_surface_at_width(
            expr,
            case,
            accumulator_proof,
            candidate_bits,
        ):
            return True
    return False

def _impl__accumulator_proof_count_surface_expressions(self, accumulator_proof):
    limit_expr = getattr(accumulator_proof, "limit_expr", None)
    if limit_expr is not None:
        yield limit_expr
    for condition in tuple(getattr(accumulator_proof, "guard_constraints", ()) or ()):
        expr = getattr(condition, "expression", condition)
        if expr is not None:
            yield expr


def dispatch_bound_observation_contract_digest(base_ctx, dispatch_frame) -> str:
    """Return the observation contract owned by the consumed dispatch frame."""

    if dispatch_frame is None:
        raise ValueError("loop production signal requires a prepared dispatch frame")
    prepared = getattr(dispatch_frame, "prepared", None)
    certificate = getattr(prepared, "certificate", None)
    expected = getattr(certificate, "observation_contract_digest", None)
    actual = base_ctx.get("observation_contract_digest")
    if type(expected) is not str or not expected:
        raise ValueError("dispatch observation contract is incomplete")
    if type(actual) is not str or not actual or actual != expected:
        raise ValueError("base context observation contract differs from dispatch")
    return actual


from ...call_effect_preflight import register_builtin_receipt_executor
from ...obligations.pair_closure_producers import (
    seal_producer_proof_implementations,
)
from . import snapshot_implementations

seal_producer_proof_implementations(snapshot_implementations())
register_builtin_receipt_executor("pairwise", _impl_check)
