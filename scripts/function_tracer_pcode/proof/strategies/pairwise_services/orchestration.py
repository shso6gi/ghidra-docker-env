"""PairwiseStrategy.check orchestration: dispatch, loop pair re-planning, blocking UNKNOWN handling, producer-proof sealing."""

from __future__ import annotations

import hashlib
from typing import Any, Dict, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.proof.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
)
from scripts.function_tracer_pcode.proof.obligations.model import FunctionProofOutcome
from scripts.function_tracer_pcode.proof.obligations import (
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
from scripts.function_tracer_pcode.proof.obligations.pair_closure_producers import (
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
import time
from scripts.function_tracer_pcode.core import Expression, FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.errors import AnalysisLimitation
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
from scripts.function_tracer_pcode.smt.parallel import run_backend_query
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
    ExpressionSafetyChecker,
    QueryResult,
    ReturnCase,
    StrategyResult,
    UnknownReasonId,
    _PendingLoopSummaryPair,
    align_return_value_extension_surfaces,
    build_symbol_replacer,
    infer_parameter_semantics,
    make_internal_v2_reason_diagnostic,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    LEFT as INPUT_LEFT,
    RIGHT as INPUT_RIGHT,
    InputCorrespondenceSet,
    bind_evidence_to_comparison,
    build_input_correspondence_set,
    comparison_authority_digest,
    comparison_is_current,
    comparison_scope,
    current_comparison,
)
from scripts.function_tracer_pcode.proof.call_effect.preflight import (
    register_builtin_receipt_executor,
)
from scripts.function_tracer_pcode.proof.obligations.pair_closure_producers import (
    seal_producer_proof_implementations,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_services import (
    snapshot_implementations,
)






def _pairwise_facade():
    """Late-bound host module: importing it eagerly would cycle through the class bindings."""
    from scripts.function_tracer_pcode.proof.strategies import pairwise
    return pairwise


def normalize_analysis_semantic_width(*args, **kwargs):
    """Preserve the documented module-level monkeypatch seam."""
    return _pairwise_facade().normalize_analysis_semantic_width(*args, **kwargs)


def validate_counterexample_across_cases(*args, **kwargs):
    """Preserve the documented module-level monkeypatch seam."""
    return _pairwise_facade().validate_counterexample_across_cases(*args, **kwargs)


def _extract_cases_under_authorization(strategy, analysis, input_correspondence, side):
    """prepared surface と同じ authorization で case を再 normalize する。

    relation が無い（gate が ``unavailable`` で塞ぐ）ときと空の authorization は
    ``_extract_return_cases`` の既定値（恒等規則だけ）と同じ意味なので、従来どおり
    1 引数で呼ぶ（この method は差し替え可能な seam）。
    """

    authorization = (
        input_correspondence.authorization(side)
        if type(input_correspondence) is InputCorrespondenceSet
        else None
    )
    if authorization is not None and authorization.assumptions:
        return strategy._extract_return_cases(analysis, authorization=authorization)
    return strategy._extract_return_cases(analysis)


def _impl_check(
    self,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    save_formula: bool = False
) -> StrategyResult:
    start_time = time.time()
    from scripts.function_tracer_pcode.proof.call_effect.preflight import (
        QueryExecutionRecord,
        comparison_binding_for_raw_pair,
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
        input_correspondence = dispatch_frame.prepared.input_correspondence
        # Issue #167: この比較で作る authority は frame の比較（raw pair と relation）に
        # 束縛される。範囲がその比較でなければ実行しない。
        if not comparison_is_current(dispatch_frame.comparison_binding):
            raise RuntimeError("comparison_authority_scope_mismatch")
    else:
        # Compatibility-only direct strategy invocation.  Production checker
        # dispatch always supplies a certified prepared frame.  The arguments
        # are the raw pair, so the final relation is built from them first.
        input_correspondence = build_input_correspondence_set(analysis1, analysis2)
        comparison = comparison_binding_for_raw_pair(analysis1, analysis2, input_correspondence)
        if current_comparison() != comparison:
            # この互換呼び出しを、自分の比較（raw pair と relation）として実行し直す。
            with comparison_scope(comparison):
                return _impl_check(self, analysis1, analysis2, save_formula)
        solver_analysis1 = normalize_analysis_semantic_width(
            analysis1,
            infer_parameter_semantics(analysis1),
            authorization=input_correspondence.authorization(INPUT_LEFT),
        )
        solver_analysis2 = normalize_analysis_semantic_width(
            analysis2,
            infer_parameter_semantics(analysis2),
            authorization=input_correspondence.authorization(INPUT_RIGHT),
        )
        solver_analysis1, solver_analysis2 = align_return_value_extension_surfaces(
            solver_analysis1,
            solver_analysis2,
        )

    base_ctx = self.formula_builder.build_base_context(
        solver_analysis1,
        solver_analysis2,
        input_correspondence=input_correspondence,
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
    # Issue #167: EQ も NOT_EQ も、query の premise を決めた最終
    # InputCorrespondence が十分なときだけ確定させる。
    input_correspondence_reasons = self._input_correspondence_unsafety_reasons(
        base_ctx.get("input_correspondence"),
        authority_correspondence=input_correspondence,
    )
    sat_unsafety_reasons.extend(input_correspondence_reasons)
    equivalence_blocking_reasons.extend(input_correspondence_reasons)
    if self.debug and type(input_correspondence) is InputCorrespondenceSet:
        self._debug_print(input_correspondence.diagnostic_line())

    cases1 = _extract_cases_under_authorization(self, solver_analysis1, input_correspondence, INPUT_LEFT)
    cases2 = _extract_cases_under_authorization(self, solver_analysis2, input_correspondence, INPUT_RIGHT)

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
    sat_unsafety_reasons.extend(
        self._sat_decisive_return_coverage_unsafety_reasons(coverage_unsafety_reasons)
    )
    # この比較の観測を raw analysis に書き戻す（比較の identity は変えない、Issue #167）。
    from scripts.function_tracer_pcode.proof.obligations.snapshot import record_comparison_annotation

    if "function1:return_coverage_gap" in sat_unsafety_reasons:
        record_comparison_annotation(analysis1, "return_case_coverage_gap")
    if "function2:return_coverage_gap" in sat_unsafety_reasons:
        record_comparison_annotation(analysis2, "return_case_coverage_gap")
    if "function1:return_coverage_inconclusive" in sat_unsafety_reasons:
        record_comparison_annotation(analysis1, "return_case_coverage_inconclusive")
    if "function2:return_coverage_inconclusive" in sat_unsafety_reasons:
        record_comparison_annotation(analysis2, "return_case_coverage_inconclusive")
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
    # (kind, evidence_refs, case1, case2, pair_id, reason) of SAT candidates whose
    # witness was rejected; retired if a later pair yields a validated witness.
    rejected_witnesses = []
    self._active_normalization_stats = normalization_stats
    query_execution_records = []

    from scripts.function_tracer_pcode.proof.return_width.pipeline import (
        prepare_function_return_widths,
        prepare_pair_return_observation,
        return_coverage_artifact_ids,
    )
    from scripts.function_tracer_pcode.proof.strategies.proof_gates.return_coverage import (
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
    from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    counterexample_replay_targets,
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
        comparison_authority_digest(),
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
                    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
                        LoopBlockerProductionSignal,
                    )
                    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                        emit_loop_recurrence_signal,
                    )

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
                except AnalysisLimitation:
                    # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
                    # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
                    raise
                except Exception as exc:
                    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                        record_production_pilot_shadow_error,
                    )

                    record_production_pilot_shadow_error(exc)
                try:
                    from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
                        AbiWidthReadonlyBlockerSignal,
                        AbiWidthReadonlyDisposition,
                        ReadonlyReductionObjectSetSeed,
                        classify_readonly_source,
                    )
                    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
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
                except AnalysisLimitation:
                    # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
                    # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
                    raise
                except Exception as exc:
                    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
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
                            from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
                                LoopV2QueryNotFormable,
                                RenderedLoopV2SolverQuery,
                                preflight_loop_v2_solver_query,
                            )
                            from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
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
                                    input_correspondence=base_ctx.get("input_correspondence"),
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
                        except AnalysisLimitation:
                            # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
                            # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
                            raise
                        except Exception as exc:
                            from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
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
                        reason_record, analysis1, analysis2, case1, case2,
                        input_correspondence=input_correspondence,
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
                    _sat_unsafety_reasons=tuple(sat_unsafety_reasons)
                    + tuple(self._pair_return_width_unsafety_reasons(base_ctx, pair_id)),
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
                        replay_reasons = self._counterexample_replay_reasons(
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
                pair_sat_unsafety_reasons = list(sat_unsafety_reasons) + list(
                    self._pair_return_width_unsafety_reasons(base_ctx, pair_id)
                )
                analysis_safety_validated = not pair_sat_unsafety_reasons
                if pair_sat_unsafety_reasons:
                    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
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
                        pair_sat_unsafety_reasons,
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
                            f"summary ({', '.join(pair_sat_unsafety_reasons)})"
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
                    ambiguous_reason = self._make_sat_counterexample_ambiguous_unknown_reason(
                        (result.pair_stage or "unknown",),
                        analysis1,
                        analysis2,
                        case1=case1,
                        case2=case2,
                        pair_id=pair_id,
                        stage="S_PAIRWISE",
                    )
                    unknown_reasons.append(ambiguous_reason)
                    rejected_witnesses.append((
                        "ambiguity", (result.pair_stage or "unknown",),
                        case1, case2, pair_id, ambiguous_reason,
                    ))
                    self._debug_print(
                        f"  Pair {pair_id}: SAT counterexample was ambiguous -> downgraded to UNKNOWN"
                    )
                    continue
                self._complete_v2_sat_counterexample_ambiguity_if_observed((result.pair_stage or "unknown",), analysis1, analysis2, case1=case1, case2=case2, pair_id=pair_id, counterexample_raw=result.counterexample_raw); global_case_replay_validated = True

                replay_reasons = self._counterexample_replay_reasons(
                    analysis1,
                    analysis2,
                )
                replay_validated = not replay_reasons
                if replay_reasons and not counterexample_replay_targets(base_ctx):
                    # Closed formula: no symbol to fix, nothing to replay; the
                    # validated SAT query is the complete witness.
                    replay_reasons = ()
                    replay_validated = True
                if replay_reasons:
                    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                        SatCounterexampleEvidenceBinding,
                    )
                    # Bind the replay obligation to this exact witness: the
                    # terminal SAT query, its model, the ledger premise and the
                    # case pair.  The proof recorded below carries the same
                    # binding plus the solver execution receipt digest, so it
                    # cannot discharge any other counterexample (Issue #28).
                    replay_binding = SatCounterexampleEvidenceBinding(
                        hashlib.sha256(sat_terminal_query.encode("utf-8")).hexdigest(),
                        hashlib.sha256(
                            repr(result.counterexample_raw).encode("utf-8")
                        ).hexdigest(),
                        ledger_binding.premise_digest,
                        (i, j),
                    )
                    replay_receipt_digest = getattr(
                        solver_execution_receipt, "authority_digest", None
                    )
                    sat_replay_reason = self._make_sat_unsafety_unknown_reason(
                        replay_reasons,
                        analysis1,
                        analysis2,
                        case1=case1,
                        case2=case2,
                        pair_id=pair_id,
                        stage="S_PAIRWISE",
                        counterexample_binding=replay_binding,
                    )
                    self._record_pairwise_counterexample_replay_proof(
                        sat_replay_reason,
                        analysis1,
                        analysis2,
                        base_ctx=base_ctx,
                        counterexample_raw=result.counterexample_raw,
                        binding=replay_binding,
                        execution_receipt_digest=replay_receipt_digest,
                        pair_id=pair_id,
                    )
                    if not self._sat_unsafety_resolution_proof_is_complete(
                        sat_replay_reason,
                        analysis1,
                        analysis2,
                        current_counterexample_raw=result.counterexample_raw,
                        expected_binding=replay_binding,
                        expected_execution_receipt_digest=replay_receipt_digest,
                    ):
                        unknown_count += 1
                        unknown_reasons.append(sat_replay_reason)
                        rejected_witnesses.append((
                            "replay", tuple(replay_reasons),
                            case1, case2, pair_id, sat_replay_reason,
                        ))
                        self._debug_print(
                            "  Pair "
                            f"{pair_id}: SAT downgraded to UNKNOWN until bound "
                            "counterexample replay is completed"
                        )
                        continue
                    replay_validated = True

                safety_receipt = CounterexampleSafetyReceipt.from_pairwise_validation(
                    query=sat_terminal_query,
                    model=result.counterexample_raw,
                    premise_digest=ledger_binding.premise_digest,
                    pair_key=(i, j),
                    analysis_safe=analysis_safety_validated,
                    global_case_replay_safe=global_case_replay_validated,
                    same_function_replay_safe=replay_validated,
                )
                sat_safety_receipt = safety_receipt
                for kind, refs, r_case1, r_case2, r_pair_id, r_reason in rejected_witnesses:
                    if r_pair_id == pair_id:
                        continue
                    if not self._supersede_rejected_witness_blocker(
                        kind,
                        refs,
                        analysis1,
                        analysis2,
                        case1=r_case1,
                        case2=r_case2,
                        pair_id=r_pair_id,
                        reason_record=r_reason,
                        decisive_binding=safety_receipt,
                    ):
                        # 退けられない blocker（解析の不安全）は UNKNOWN の理由に残す。
                        continue
                    if r_reason in unknown_reasons:
                        unknown_reasons.remove(r_reason)
                    self._debug_print(
                        f"  Pair {r_pair_id}: rejected witness superseded by validated "
                        f"witness of pair {pair_id}"
                    )
                rejected_witnesses = []
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
                from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
                    LoopBlockerProductionSignal,
                )
                from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                    emit_loop_recurrence_signal,
                )

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
            except AnalysisLimitation:
                # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
                # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
                raise
            except Exception as exc:
                from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
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
        from scripts.function_tracer_pcode.proof.obligations import RuntimeQuiescenceCertificate
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
        # 戻り幅の完了証拠はこの比較の solver surface（relation が許可した書き換えの
        # 結果）から作ったので、この比較（raw pair と relation）に束縛する（Issue #167）。
        final_result.completed_recovery_proof_evidence = [
            {
                "side": side,
                "function_name": getattr(analysis, "function_name", None),
                "binary_name": getattr(analysis, "binary_id", None),
                "binary_id": getattr(analysis, "binary_id", None),
                "evidence": bind_evidence_to_comparison(dict(evidence)),
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
    result = run_backend_query(Z3Solver(timeout=1, debug=False), query)
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


# ---- module-level registrations (must follow the definitions above)
seal_producer_proof_implementations(snapshot_implementations())
register_builtin_receipt_executor("pairwise", _impl_check)
