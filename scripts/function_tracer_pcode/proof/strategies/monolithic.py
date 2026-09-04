# -*- coding: utf-8 -*-
"""Monolithic戦略（全条件を一度に検証）"""

import hashlib
import re
import time

from dataclasses import dataclass, field, replace
from typing import Optional, Dict, Any, List, Mapping, Set, Tuple

from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.render_smt import (
    UnknownSmtExtensionWidthError,
    UnsupportedSmtIntrinsicError,
    UnsupportedSmtOperatorError,
)
from scripts.function_tracer_pcode.core.structural import condition_key, expression_provenance_key
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.proof.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.proof.formula.returns import ReturnWidthMismatchError
from scripts.function_tracer_pcode.semantics.normalize import NormalizationSettings
from scripts.function_tracer_pcode.semantics.param_semantics import infer_parameter_semantics
from scripts.function_tracer_pcode.semantics.semantic_width import (
    align_return_value_extension_surfaces,
    normalize_analysis_semantic_width,
)
from scripts.function_tracer_pcode.proof.return_width.pipeline import (
    prepare_function_return_widths,
    prepare_pair_return_observation,
    return_coverage_artifact_ids,
)
from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
    ReturnAbiAuthorityInvalid,
)
from scripts.function_tracer_pcode.proof.query_receipt_authority import (
    canonical_region_query_receipt_digests,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    make_internal_v2_reason_diagnostic,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.proof.monolithic_authority import (
    build_expected_region_query_set as _PINNED_BUILD_EXPECTED_REGION_QUERY_SET,
    create_shared_z3_region_session as _PINNED_CREATE_SHARED_Z3_REGION_SESSION,
    execute_expected_guard_query as _PINNED_EXECUTE_EXPECTED_GUARD_QUERY,
    execute_expected_value_query as _PINNED_EXECUTE_EXPECTED_VALUE_QUERY,
)
from scripts.function_tracer_pcode.proof.strategies.base import CheckStrategy, StrategyResult
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    append_ordered_ite_default_case,
    build_condition_only_query,
    build_pair_query,
    extract_return_cases,
    return_cases_require_relation,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    build_counterexample_model_assertions,
    count_counterexample_model_assertions,
    execute_guard_overlap,
    solve_query_internal,
    validate_counterexample_globally,
)


@dataclass(frozen=True)
class _TypedMonolithicCounterexampleEvidence:
    census: Any
    model_digest: str
    fixed_model_assertion_digest: str
    replay_formula: str = field(repr=False, compare=False)
    legacy_replay_receipt: Any = field(repr=False, compare=False)
    sat_region_id: str = "legacy"
    fixed_model_assertion_count: int = 0

    def __post_init__(self) -> None:
        contract = getattr(self.legacy_replay_receipt, "contract", None)
        if contract is None:
            raise TypeError("monolithic_counterexample_replay_contract_missing")
        formula_digest = hashlib.sha256(
            self.replay_formula.encode("utf-8")
        ).hexdigest()
        if formula_digest != getattr(contract, "formula_digest", None):
            raise ValueError(
                "monolithic_counterexample_replay_formula_mismatch: "
                f"replay={formula_digest}, "
                f"receipt={getattr(contract, 'formula_digest', None)}"
            )
        if self.model_digest != getattr(contract, "model_digest", None):
            raise ValueError("monolithic_counterexample_replay_model_mismatch")
        if (
            self.fixed_model_assertion_digest
            != getattr(contract, "fixed_model_assertion_digest", None)
        ):
            raise ValueError(
                "monolithic_counterexample_fixed_model_assertion_mismatch"
            )
        if (
            getattr(self.census, "census_digest", None)
            != getattr(contract, "census_digest", None)
        ):
            raise ValueError("monolithic_counterexample_replay_census_mismatch")


from scripts.function_tracer_pcode.proof.strategies.monolithic_regions import RegionExecutionMixin
from scripts.function_tracer_pcode.proof.strategies.monolithic_return_width import ReturnWidthObservationMixin
from scripts.function_tracer_pcode.proof.strategies.monolithic_counterexamples import CounterexampleDecisivenessMixin
from scripts.function_tracer_pcode.proof.strategies.monolithic_support import (
    _MonolithicReturnWidthQueryBundle,
    _monolithic_case_identity,
    _MonolithicDecisionExecutionContext,
    _MonolithicRegionPlan,
    _MonolithicRegionExecution,
)


class MonolithicStrategy(RegionExecutionMixin, ReturnWidthObservationMixin, CounterexampleDecisivenessMixin, CheckStrategy):
    """Monolithic戦略（全条件を一度に検証）"""

    def __init__(
        self,
        formula_builder,
        solver_runner,
        debug: bool = False,
        normalization_settings: Optional[NormalizationSettings] = None,
        enable_completed_recovery_proofs: bool = True,
    ):
        super().__init__(
            formula_builder,
            solver_runner,
            debug,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        )
        self.normalization_settings = normalization_settings or NormalizationSettings.safe()
        timeout_candidate = getattr(solver_runner, "timeout", 10) or 10
        try:
            configured_timeout = float(timeout_candidate)
        except (TypeError, ValueError):
            configured_timeout = 10.0
        inherited_region_timeout = getattr(type(self), "per_query_timeout", None)
        region_timeout_candidate = (
            inherited_region_timeout
            if isinstance(inherited_region_timeout, (int, float))
            else configured_timeout
        )
        try:
            configured_region_timeout = int(region_timeout_candidate)
        except (TypeError, ValueError):
            configured_region_timeout = int(configured_timeout)
        self.total_timeout = max(1, int(configured_timeout))
        self.per_query_timeout = max(
            1,
            configured_region_timeout,
        )
        inherited_hard_timeout = getattr(type(self), "per_query_timeout_hard", None)
        self.per_query_timeout_hard = max(
            self.per_query_timeout,
            int(inherited_hard_timeout)
            if isinstance(inherited_hard_timeout, (int, float))
            else self.per_query_timeout,
        )
        self.save_unknown_queries = False
        self.query_mode = "split"
        self.unknown_query_dir = "/tmp"
        from scripts.function_tracer_pcode.proof.obligations import AttemptCache
        self._exact_query_attempt_cache = AttemptCache(max_entries=4096)

    def _build_condition_only_query(self, *args, **kwargs) -> str:
        return build_condition_only_query(*args, **kwargs)

    def _build_pair_query(self, *args, **kwargs) -> str:
        return build_pair_query(*args, **kwargs)

    def _solve_query_internal(self, *args, **kwargs):
        return solve_query_internal(self, *args, **kwargs)

    def _save_unknown_query(self, query: str, pair_id: str, stage: str) -> None:
        del query, pair_id, stage

    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False,
        _build_query_set=_PINNED_BUILD_EXPECTED_REGION_QUERY_SET,
        _create_session=_PINNED_CREATE_SHARED_Z3_REGION_SESSION,
    ) -> StrategyResult:
        """等価性をチェック（monolithic方式）"""
        start_time = time.time()  # ★ これで使える
        from scripts.function_tracer_pcode.proof.call_effect.preflight import (
            QueryExecutionRecord,
            consume_prepared_dispatch_frame,
            current_dispatch_depth,
            issue_builtin_comparison_receipt,
            issue_inconclusive_monolithic_receipts,
            lower_call_projection_for_case_pair,
            projection_binding_evidence_from_query,
        )
        from scripts.function_tracer_pcode.proof.monolithic_authority import (
            freeze_surface,
            reconstruct_canonical_census,
            reconstruct_fallback_census,
            seal_terminal_decision,
        )

        source_analysis1 = analysis1
        source_analysis2 = analysis2
        dispatch_frame = None
        if current_dispatch_depth() > 0:
            dispatch_frame = consume_prepared_dispatch_frame(analysis1, analysis2)
            analysis1 = dispatch_frame.prepared.analysis1
            analysis2 = dispatch_frame.prepared.analysis2
        decision_context = _MonolithicDecisionExecutionContext.create(
            analysis1,
            analysis2,
            decision_surface=(
                "prepared" if dispatch_frame is not None else "legacy_source"
            ),
            prepared_surface_digest=(
                dispatch_frame.prepared.surface_digest
                if dispatch_frame is not None
                else None
            ),
        )
        frozen_surface = None
        canonical_census = None
        if dispatch_frame is not None:
            parent_lease = dispatch_frame.production_branch_authority_lease
            execution_lease = dispatch_frame.monolithic_execution_authority_lease
            frozen_surface = freeze_surface(
                parent_lease,
                execution_lease,
                analysis1,
                analysis2,
                self.normalization_settings,
            )
            canonical_census = reconstruct_canonical_census(frozen_surface)
        call_projection_assertions = ()
        call_projection_binding_ids = ()
        call_width_receipt_digests = ()
        call_width_receipt_assertion_digests = ()
        canonical_width_observation = None
        if dispatch_frame is not None and dispatch_frame.projection.semantic_bindings:
            call_base_ctx = self.formula_builder.build_base_context(analysis1, analysis2)
            call_replace1 = build_symbol_replacer(
                call_base_ctx["params1"],
                call_base_ctx.get("extra_vars1", []),
                float_mode="fp",
            )
            call_replace2 = build_symbol_replacer(
                call_base_ctx["params2"],
                call_base_ctx.get("extra_vars2", []),
                float_mode="fp",
            )
            lowered_call_projection = lower_call_projection_for_case_pair(
                dispatch_frame,
                analysis1,
                analysis2,
                pair_id="monolithic",
                render_fn1=call_replace1,
                render_fn2=call_replace2,
            )
            if lowered_call_projection.status != "proven":
                blocked_result = StrategyResult(
                    is_equivalent=None,
                    solver_results=ParallelResult(results=[]),
                    unknown_reasons=[
                        make_internal_v2_reason_diagnostic(
                            "call_projection_partition_unproven",
                            stage="CALL_EFFECT_PREFLIGHT",
                            evidence_refs=(
                                lowered_call_projection.failure_cause,
                                lowered_call_projection.evidence_digest,
                            ),
                            detail="Certified call projection could not be lowered into the monolithic query.",
                        )
                    ],
                )
                issue_inconclusive_monolithic_receipts(
                    dispatch_frame,
                    frozen_surface,
                    canonical_census,
                    lowered_call_projection.failure_cause,
                )
                blocked_result.comparison_execution_receipt = dispatch_frame.receipt
                return blocked_result
            call_projection_assertions = lowered_call_projection.assertions
            call_projection_binding_ids = lowered_call_projection.binding_ids
            call_width_receipt_digests = (
                lowered_call_projection.return_width_receipt_digests
            )
            call_width_receipt_assertion_digests = (
                lowered_call_projection.return_width_receipt_assertion_digests
            )
        
        try:
            region_execution = None
            production_runner = (
                self.solver_runner.__class__.__module__.endswith(".smt.parallel")
                and self.solver_runner.__class__.__name__ == "ParallelSolverRunner"
            )
            region_plan = (
                _MonolithicRegionPlan(
                    canonical_census.census_digest,
                    canonical_census.expected_region_ids,
                    canonical_census.cases1,
                    canonical_census.cases2,
                    frozen_surface,
                    canonical_census,
                )
                if canonical_census is not None and self.query_mode == "split"
                else self._build_region_plan(analysis1, analysis2)
                if production_runner and self.query_mode == "split" else None
            )
            expected_query_set = None
            region_base_ctx = None
            if region_plan is not None and canonical_census is not None:
                region_base_ctx = dict(
                    self.formula_builder.build_base_context(analysis1, analysis2)
                )
                if call_projection_assertions:
                    region_base_ctx["header_lines"] = [
                        *list(region_base_ctx["header_lines"]),
                        *list(call_projection_assertions),
                    ]
                expected_query_set = _build_query_set(
                    frozen_surface, canonical_census, region_base_ctx
                )
            if region_plan is not None:
                shared_region_session = None
                try:
                    structured_replay_census = (
                        canonical_census
                        if canonical_census is not None
                        else reconstruct_fallback_census(frozen_surface)
                        if frozen_surface is not None
                        else None
                    )
                    if (
                        expected_query_set is not None
                        and production_runner
                    ):
                        shared_region_session = _create_session(
                            expected_query_set, frozen_surface
                        )
                    region_execution = self._execute_region_plan(
                        analysis1,
                        analysis2,
                        plan=region_plan,
                        call_projection_assertions=tuple(call_projection_assertions),
                        call_projection_binding_ids=tuple(call_projection_binding_ids),
                        call_width_receipt_digests=tuple(call_width_receipt_digests),
                        call_width_receipt_assertion_digests=tuple(
                            call_width_receipt_assertion_digests
                        ),
                        QueryExecutionRecord=QueryExecutionRecord,
                        started_at=start_time,
                        base_ctx=region_base_ctx,
                        expected_query_set=expected_query_set,
                        shared_region_session=shared_region_session,
                        replay_frozen_surface=frozen_surface,
                        replay_census=structured_replay_census,
                    )
                except (ReturnWidthMismatchError, TypeError, KeyError, AttributeError) as split_error:
                    # Width bridging has its own proof-backed legacy path below.
                    self._debug_print(
                        f"Monolithic structured split unavailable: {split_error}"
                    )
                    region_execution = None
                finally:
                    shared_region_session = None

            build_kwargs = {}
            if call_projection_assertions:
                build_kwargs["extra_assertions"] = list(call_projection_assertions)
            if region_execution is None:
                # Relation-mode and width-bridge surfaces retain the complete
                # legacy formula; they are never approximated by the splitter.
                try:
                    result = self.formula_builder.build_equivalence_formula_extended(
                        analysis1,
                        analysis2,
                        **build_kwargs,
                    )
                except ReturnWidthMismatchError:
                    canonical_width_observation = (
                        self._canonical_return_width_observation_for_analyses(
                            analysis1, analysis2
                        )
                    )
                    bridge_narrow_bits = (
                        canonical_width_observation.canonical_width
                        if canonical_width_observation is not None
                        else None
                    )
                    if bridge_narrow_bits is None:
                        raise
                    self._debug_print(
                        "Monolithic return-width mismatch bridged by completed pairwise "
                        f"proofs at {bridge_narrow_bits} bits"
                    )
                    bridge_build_kwargs = dict(build_kwargs)
                    bridge_build_kwargs["canonical_return_observation_width"] = bridge_narrow_bits
                    bridge_build_kwargs["extra_assertions"] = list(
                        bridge_build_kwargs.get("extra_assertions", ())
                    ) + list(canonical_width_observation.ordered_markers)
                    result = self.formula_builder.build_equivalence_formula_extended(
                        analysis1,
                        analysis2,
                        **bridge_build_kwargs,
                    )
                    if not all(
                        marker in result.formula
                        for marker in canonical_width_observation.ordered_markers
                    ):
                        raise ValueError("monolithic_canonical_binding_receipt_not_consumed")
                smt_formula = result.formula
                if canonical_width_observation is not None:
                    canonical_width_observation = canonical_width_observation.bind_query(
                        smt_formula
                    )
                    decision_context = decision_context.with_return_width_query_bundle(
                        canonical_width_observation
                    )
                return_var1 = result.return_var1
                return_var2 = result.return_var2
                constrained_fragments = result.constrained_fragments

                if self.debug:
                    print(f"Generated legacy monolithic SMT formula ({len(smt_formula)} bytes)")
                runner_method = (
                    self.solver_runner.run_sequential
                    if self.debug else self.solver_runner.run_parallel
                )
                try:
                    parallel_result = runner_method(
                        smt_formula, timeout=self.total_timeout
                    )
                except TypeError as timeout_error:
                    if "timeout" not in str(timeout_error):
                        raise
                    parallel_result = runner_method(smt_formula)
                counterexample_raw = (
                    parallel_result.get_counterexample() or {}
                    if parallel_result.is_equivalent is False
                    else None
                )
            else:
                smt_formula = region_execution.last_formula
                return_var1 = "return_1"
                return_var2 = "return_2"
                constrained_fragments = []
                parallel_result = region_execution.parallel_result
                counterexample_raw = region_execution.counterexample_raw
                self._debug_print(
                    "Monolithic structured split: "
                    f"{region_execution.disposition_counts.get('closed_regions', 0)}/"
                    f"{region_execution.disposition_counts.get('planned_regions', 0)} regions closed"
                )

            final_is_equivalent = parallel_result.is_equivalent
            global_replay_receipts = []
            counterexample_safety_receipt = None
            typed_counterexample_evidence = None
            unknown_reasons = []
            sat_unsafety_reason = None
            sat_unsafety_resolution_pending = False
            sat_replay_reason = None
            sat_replay_resolution_pending = False
            sat_unsafety_reasons = self._collect_decisive_sat_unsafety_reasons(
                source_analysis1,
                source_analysis2,
            )
            equivalence_blocking_reasons = self._collect_equivalence_blocking_unsafety_reasons(
                source_analysis1,
                source_analysis2,
            )
            if dispatch_frame is not None and dispatch_frame.projection.proven:
                covered_blockers = set(dispatch_frame.projection.covered_blockers)
                equivalence_blocking_reasons = [
                    reason
                    for reason in equivalence_blocking_reasons
                    if reason not in covered_blockers
                ]
            coverage_unsafety_reasons = []
            if final_is_equivalent in {True, False}:
                coverage_unsafety_reasons = self._collect_monolithic_return_coverage_unsafety_reasons(
                    analysis1,
                    analysis2,
                    decision_context,
                )
            sat_unsafety_reasons.extend(
                self._sat_decisive_return_coverage_unsafety_reasons(coverage_unsafety_reasons)
            )
            if (
                final_is_equivalent is False
                and frozen_surface is not None
            ):
                if (
                    region_execution is not None
                    and region_execution.legacy_replay_receipt is not None
                    and region_execution.sat_replay_formula
                    and hashlib.sha256(
                        region_execution.sat_replay_formula.encode("utf-8")
                    ).hexdigest()
                    == getattr(
                        region_execution.legacy_replay_receipt.contract,
                        "formula_digest",
                        None,
                    )
                ):
                    typed_counterexample_evidence = (
                        _TypedMonolithicCounterexampleEvidence(
                            region_execution.sat_replay_census,
                            region_execution.model_digest,
                            region_execution.fixed_model_assertion_digest,
                            region_execution.sat_replay_formula,
                            region_execution.legacy_replay_receipt,
                            region_execution.sat_region_id,
                            count_counterexample_model_assertions(
                                region_base_ctx or dict(
                                    self.formula_builder.build_base_context(
                                        analysis1, analysis2
                                    )
                                ),
                                counterexample_raw,
                            ),
                        )
                    )
                elif region_execution is None and counterexample_raw is not None:
                    try:
                        typed_census = reconstruct_fallback_census(frozen_surface)
                        replay_base_ctx = dict(
                            self.formula_builder.build_base_context(
                                analysis1, analysis2
                            )
                        )
                        model_assertions = tuple(
                            build_counterexample_model_assertions(
                                replay_base_ctx, counterexample_raw
                            )
                        )
                        replay_targets_exist = bool(
                            replay_base_ctx.get("params1")
                            or replay_base_ctx.get("params2")
                            or replay_base_ctx.get("extra_vars1")
                            or replay_base_ctx.get("extra_vars2")
                        )
                        if replay_targets_exist and not model_assertions:
                            raise RuntimeError(
                                "legacy_fixed_model_assertions_missing"
                            )
                        replay_build_kwargs = {
                            "extra_assertions": [
                                *list(call_projection_assertions),
                                *list(model_assertions),
                            ]
                        }
                        if canonical_width_observation is not None:
                            replay_build_kwargs[
                                "canonical_return_observation_width"
                            ] = canonical_width_observation.canonical_width
                            replay_build_kwargs["extra_assertions"].extend(
                                canonical_width_observation.ordered_markers
                            )
                        replay_result = (
                            self.formula_builder.build_equivalence_formula_extended(
                                analysis1, analysis2, **replay_build_kwargs
                            )
                        )
                        replay_formula = replay_result.formula
                        model_digest = hashlib.sha256(
                            repr(counterexample_raw).encode("utf-8")
                        ).hexdigest()
                        fixed_digest = hashlib.sha256(
                            "\n".join(model_assertions).encode("utf-8")
                        ).hexdigest()
                        from scripts.function_tracer_pcode.proof.monolithic_authority import (
                            execute_legacy_violation_replay,
                        )
                        replay_solver_result, legacy_replay_receipt = (
                            execute_legacy_violation_replay(
                                self,
                                frozen_surface,
                                typed_census,
                                formula=replay_formula,
                                model_digest=model_digest,
                                fixed_model_assertion_digest=fixed_digest,
                                timeout=max(1, int(self.per_query_timeout)),
                            )
                        )
                        if replay_solver_result.is_equivalent is not False:
                            raise RuntimeError(
                                "legacy_fixed_model_whole_surface_replay_not_sat"
                            )
                        typed_counterexample_evidence = (
                            _TypedMonolithicCounterexampleEvidence(
                                typed_census,
                                model_digest,
                                fixed_digest,
                                replay_formula,
                                legacy_replay_receipt,
                                "legacy",
                                len(model_assertions),
                            )
                        )
                    except (
                        RuntimeError, ValueError, TypeError, KeyError, AttributeError
                    ) as exc:
                        self._debug_print(
                            "Legacy monolithic fixed-model replay unavailable: "
                            f"{exc}"
                        )
            if final_is_equivalent is True and coverage_unsafety_reasons:
                coverage_unknown_reasons = self._unresolved_return_coverage_unknown_reasons(
                    coverage_unsafety_reasons,
                    analysis1,
                    analysis2,
                    stage="S_MONOLITHIC_FALLBACK",
                )
                if coverage_unknown_reasons:
                    unknown_reasons.extend(coverage_unknown_reasons)
                    self._debug_print(
                        "Monolithic UNSAT downgraded to UNKNOWN due to incomplete return coverage "
                        f"({', '.join(coverage_unsafety_reasons)})"
                    )
                    final_is_equivalent = None
            if final_is_equivalent is True and equivalence_blocking_reasons:
                unresolved_blocking_reasons = self._unresolved_equivalence_blocking_unknown_reasons(
                    equivalence_blocking_reasons,
                    analysis1,
                    analysis2,
                    stage="S_MONOLITHIC_FALLBACK",
                )
                if unresolved_blocking_reasons:
                    unknown_reasons.extend(unresolved_blocking_reasons)
                    self._debug_print(
                        "Monolithic UNSAT downgraded to UNKNOWN due to incomplete effect analysis "
                        f"({', '.join(equivalence_blocking_reasons)})"
                    )
                    final_is_equivalent = None
                else:
                    self._debug_print(
                        "Monolithic UNSAT accepted after completed call-effect summary proof "
                        f"({', '.join(equivalence_blocking_reasons)})"
                    )
            # Evidence binding of the monolithic witness: whole-surface replay
            # formula digest, model digest, replay contract digest and the SAT
            # region.  Every replay/unsafety proof of this witness must carry
            # it and completion verifies it (Issue #39); without typed
            # evidence no proof can be recorded and the SAT stays UNKNOWN.
            sat_counterexample_binding = None
            if final_is_equivalent is False and typed_counterexample_evidence is not None:
                from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                    SatCounterexampleEvidenceBinding,
                )
                sat_counterexample_binding = SatCounterexampleEvidenceBinding(
                    typed_counterexample_evidence.legacy_replay_receipt
                    .contract.formula_digest,
                    typed_counterexample_evidence.model_digest,
                    typed_counterexample_evidence.legacy_replay_receipt
                    .contract.contract_digest,
                    (
                        "monolithic",
                        typed_counterexample_evidence.sat_region_id,
                    ),
                )
            if final_is_equivalent is False and sat_unsafety_reasons:
                sat_unsafety_reason = self._make_sat_unsafety_unknown_reason(
                    sat_unsafety_reasons,
                    analysis1,
                    analysis2,
                    case1=None,
                    case2=None,
                    pair_id="monolithic",
                    stage="S_MONOLITHIC_FALLBACK",
                    counterexample_binding=sat_counterexample_binding,
                )
                # Never consult prior proofs here: this execution's
                # counterexample safety receipt does not exist yet, and a proof
                # from another execution (same formula/model/premise/pair,
                # different receipt) must not discharge the obligation
                # (Issue #39).  Completion happens only after the receipt is
                # issued, with the receipt digest verified.
                sat_unsafety_resolution_pending = True
                self._debug_print(
                    "Monolithic SAT pending typed counterexample safety receipt "
                    f"({', '.join(sat_unsafety_reasons)})"
                )
            counterexample_is_decisive = True
            if final_is_equivalent is False:
                replay_collector = None
                if (
                    typed_counterexample_evidence is not None
                    and frozen_surface is not None
                ):
                    from scripts.function_tracer_pcode.proof.monolithic_authority import (
                        create_global_replay_collector,
                    )
                    global_replay_receipts, replay_collector = create_global_replay_collector(
                        frozen_surface,
                        typed_counterexample_evidence.census,
                        model_digest=typed_counterexample_evidence.model_digest,
                        fixed_model_assertion_digest=(
                            typed_counterexample_evidence.fixed_model_assertion_digest
                        ),
                    )
                    self._monolithic_replay_execution_collector = replay_collector
                try:
                    counterexample_is_decisive = self._dispatch_counterexample_decisiveness(
                        analysis1,
                        analysis2,
                        counterexample_raw,
                        decision_context,
                    )
                finally:
                    self.__dict__.pop(
                        "_monolithic_replay_execution_collector", None
                    )
                if (
                    counterexample_is_decisive
                    and typed_counterexample_evidence is not None
                    and frozen_surface is not None
                ):
                    from scripts.function_tracer_pcode.proof.monolithic_authority import (
                        execute_global_violation_replay,
                    )
                    global_result, global_receipt = execute_global_violation_replay(
                        self,
                        frozen_surface,
                        typed_counterexample_evidence.census,
                        formula=typed_counterexample_evidence.replay_formula,
                        model_digest=typed_counterexample_evidence.model_digest,
                        fixed_model_assertion_digest=(
                            typed_counterexample_evidence.fixed_model_assertion_digest
                        ),
                        timeout=max(1, int(self.per_query_timeout)),
                    )
                    global_replay_receipts.append(global_receipt)
                    counterexample_is_decisive = (
                        global_result.is_equivalent is False
                    )
            if final_is_equivalent is False and not counterexample_is_decisive:
                unknown_reasons.append(
                    self._make_sat_counterexample_ambiguous_unknown_reason(
                        ("monolithic_case_partition_replay",),
                        analysis1,
                        analysis2,
                        case1=None,
                        case2=None,
                        pair_id="monolithic",
                        stage="S_MONOLITHIC_FALLBACK",
                    )
                )
                self._debug_print(
                    "Monolithic SAT downgraded to UNKNOWN after global counterexample validation"
                )
                final_is_equivalent = None
                counterexample_raw = None
            replay_reasons = ()
            if final_is_equivalent is False:
                typed_whole_surface_replay_complete = bool(
                    typed_counterexample_evidence is not None
                    and typed_counterexample_evidence.legacy_replay_receipt.disposition
                    == "sat"
                    and any(
                        receipt.contract.replay_kind
                        == "global_case_validation:whole_surface"
                        and receipt.disposition == "sat"
                        for receipt in global_replay_receipts
                    )
                )
                if not typed_whole_surface_replay_complete:
                    replay_reasons = (
                        self._counterexample_replay_reasons(
                            analysis1,
                            analysis2,
                        )
                    )
                    if replay_reasons:
                        from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
                            counterexample_replay_targets,
                        )
                        try:
                            replay_targets = counterexample_replay_targets(
                                self.formula_builder.build_base_context(analysis1, analysis2)
                            )
                        except Exception:
                            replay_targets = None
                        if replay_targets is not None and not replay_targets:
                            # Closed formula: nothing to replay, the SAT query
                            # itself is the complete witness.
                            replay_reasons = ()
            if final_is_equivalent is False and replay_reasons:
                sat_replay_reason = self._make_sat_unsafety_unknown_reason(
                    replay_reasons,
                    analysis1,
                    analysis2,
                    case1=None,
                    case2=None,
                    pair_id="monolithic",
                    stage="S_MONOLITHIC_FALLBACK",
                    counterexample_binding=sat_counterexample_binding,
                )
                # Same rule as the unsafety obligation: no prior proof is
                # accepted before this execution's receipt exists; the replay
                # proof is recorded and verified (binding + receipt) below.
                sat_replay_resolution_pending = True
                self._debug_print(
                    "Monolithic SAT pending bound counterexample replay proof"
                )
            # A solver UNKNOWN/TIMEOUT remains on the captured execution
            # receipt.  It must never manufacture a semantic reason row.
            
            strategy_result = StrategyResult(
                is_equivalent=final_is_equivalent,
                solver_results=parallel_result,
                smt_formula=smt_formula,  # ★ 修正: save_formula の条件を削除（常に保存）
                counterexample_raw=counterexample_raw,
                return_var1=return_var1,
                return_var2=return_var2,
                constrained_fragments=constrained_fragments,
                total_pairs=(
                    int(region_execution.disposition_counts.get("total", 0))
                    if region_execution is not None else 0
                ),
                unsat_pairs=(
                    int(region_execution.disposition_counts.get("unsat", 0))
                    if region_execution is not None else 0
                ),
                sat_pairs=(
                    int(region_execution.disposition_counts.get("sat", 0))
                    if region_execution is not None else 0
                ),
                unknown_pairs=(
                    int(region_execution.disposition_counts.get("unknown", 0))
                    if region_execution is not None else 0
                ),
                error_pairs=(
                    int(region_execution.disposition_counts.get("error", 0))
                    if region_execution is not None else 0
                ),
                pairwise_debug_stats=(
                    dict(region_execution.debug_stats)
                    if region_execution is not None else {
                        "monolithic_legacy_fallback": 1,
                        "monolithic_legacy_query_bytes": len(smt_formula),
                        "monolithic_legacy_solver_checks": 1,
                    }
                ),
                unknown_reasons=unknown_reasons,
            )
            if dispatch_frame is not None:
                expected_binding_evidence = dict(
                    lowered_call_projection.binding_assertion_digests
                    if call_projection_binding_ids else ()
                )
                if region_execution is not None:
                    query_records = region_execution.query_records
                    disposition_counts = dict(region_execution.disposition_counts)
                    actual_call_projection_binding_ids = tuple(sorted({
                        binding_id
                        for record in query_records
                        for binding_id in record.projection_binding_ids
                    }))
                else:
                    query_digest = hashlib.sha256(
                        smt_formula.encode("utf-8")
                    ).hexdigest()
                    disposition = (
                        "unsat" if parallel_result.is_equivalent is True
                        else "sat" if parallel_result.is_equivalent is False
                        else "unknown"
                    )
                    actual_call_projection_binding_ids = tuple(sorted(
                        binding_id
                        for binding_id, assertion_digest in (
                            projection_binding_evidence_from_query(smt_formula).items()
                        )
                        if expected_binding_evidence.get(binding_id) == assertion_digest
                    ))
                    query_records = (
                        QueryExecutionRecord(
                            query_label="monolithic",
                            premise_digest=query_digest,
                            formula_digest=query_digest,
                            disposition=disposition,
                            proof_kind="monolithic_solver_query",
                            projection_binding_ids=actual_call_projection_binding_ids,
                            formula_text=smt_formula,
                            return_width_observation_view_digest=(
                                canonical_width_observation.view_digest
                                if canonical_width_observation is not None
                                else ""
                            ),
                            return_width_binding_receipt_digest=(
                                canonical_width_observation.binding_digest
                                if canonical_width_observation is not None
                                else ""
                            ),
                            call_site_return_width_receipt_digests=(
                                call_width_receipt_digests
                            ),
                            call_site_return_width_receipt_assertion_digests=(
                                call_width_receipt_assertion_digests
                            ),
                            canonical_return_width_receipt_digests=(
                                canonical_width_observation.ordered_receipt_digests
                                if canonical_width_observation is not None
                                else ()
                            ),
                        ),
                    )
                    disposition_counts = {
                        "total": 1,
                        "unsat": 1 if parallel_result.is_equivalent is True else 0,
                        "sat": 1 if parallel_result.is_equivalent is False else 0,
                        "unknown": 1 if parallel_result.is_equivalent is None else 0,
                        "error": 0,
                    }
                if strategy_result.is_equivalent is False:
                    try:
                        from scripts.function_tracer_pcode.proof.monolithic_authority import (
                            issue_counterexample_safety_decision_receipt,
                            gate_source_artifact_id,
                            issue_gate_artifact_reference,
                        )
                        if (
                            typed_counterexample_evidence is None
                        ):
                            raise RuntimeError(
                                "typed_counterexample_replay_evidence_missing"
                            )
                        runtime = getattr(self, "_obligation_runtime_session", None)
                        coverage_ids = return_coverage_artifact_ids(
                            runtime,
                            (
                                tuple(analysis1.outcome_function_identity()),
                                tuple(analysis2.outcome_function_identity()),
                            ),
                        )
                        width_source = canonical_width_observation or (
                            analysis1,
                            analysis2,
                        )
                        coverage_source = (
                            runtime, coverage_ids, analysis1, analysis2
                        )
                        projection_status = (
                            "proven" if dispatch_frame.projection.required
                            else "not_required"
                        )
                        effect_source = (
                            dispatch_frame.preflight_manifest,
                            dispatch_frame.trusted_proof_artifacts,
                            dispatch_frame.projection,
                        )
                        typed_gate_refs = (
                            issue_gate_artifact_reference(
                                frozen_surface, "coverage",
                                coverage_source,
                                artifact_id=gate_source_artifact_id(
                                    "coverage", coverage_source
                                ),
                                status=("proven" if coverage_ids else "not_required"),
                                census=typed_counterexample_evidence.census,
                            ),
                            issue_gate_artifact_reference(
                                frozen_surface, "effect",
                                effect_source,
                                artifact_id=gate_source_artifact_id(
                                    "effect",
                                    effect_source,
                                ), status=projection_status,
                                census=typed_counterexample_evidence.census,
                            ),
                            issue_gate_artifact_reference(
                                frozen_surface, "projection", dispatch_frame.projection,
                                artifact_id=dispatch_frame.projection.projection_id,
                                status=projection_status,
                                census=typed_counterexample_evidence.census,
                            ),
                            issue_gate_artifact_reference(
                                frozen_surface, "width", width_source,
                                artifact_id=gate_source_artifact_id(
                                    "width", width_source
                                ), status=("proven" if canonical_width_observation
                                           is not None else "not_required"),
                                census=typed_counterexample_evidence.census,
                            ),
                        )
                        counterexample_safety_receipt = (
                            issue_counterexample_safety_decision_receipt(
                                frozen_surface,
                                typed_counterexample_evidence.census,
                                model_digest=typed_counterexample_evidence.model_digest,
                                fixed_model_assertion_digest=(
                                    typed_counterexample_evidence.fixed_model_assertion_digest
                                ),
                                legacy_replay_receipt=(
                                    typed_counterexample_evidence.legacy_replay_receipt
                                ),
                                global_replay_receipts=global_replay_receipts,
                                gate_references=typed_gate_refs,
                            )
                        )
                        dispatch_frame.monolithic_counterexample_safety_receipt = (
                            counterexample_safety_receipt
                        )
                    except (RuntimeError, ValueError, TypeError, AttributeError) as exc:
                        strategy_result.is_equivalent = None
                        strategy_result.counterexample_raw = None
                        counterexample_raw = None
                        unknown_reasons.append(make_internal_v2_reason_diagnostic(
                            "counterexample_analysis_safety_unproven",
                            stage="S_MONOLITHIC_FALLBACK",
                            evidence_refs=(
                                "typed_counterexample_safety_receipt_missing",
                                str(exc),
                            ),
                            detail=(
                                "Typed replay/gate evidence did not authorize "
                                "the monolithic counterexample."
                            ),
                        ))
                        strategy_result.unknown_reasons = unknown_reasons
                pending_reasons = [
                    reason for reason, pending in (
                        (sat_unsafety_reason, sat_unsafety_resolution_pending),
                        (sat_replay_reason, sat_replay_resolution_pending),
                    )
                    if pending and reason is not None
                ]
                if pending_reasons:
                    unresolved = list(pending_reasons)
                    if not (
                        strategy_result.is_equivalent is False
                        and counterexample_safety_receipt is not None
                        and counterexample_raw is not None
                        and sat_counterexample_binding is not None
                    ):
                        self._debug_print(
                            "Monolithic proof recording skipped: "
                            f"sat={strategy_result.is_equivalent is False} "
                            f"receipt={counterexample_safety_receipt is not None} "
                            f"model={counterexample_raw is not None} "
                            f"binding={sat_counterexample_binding is not None}"
                        )
                    if (
                        strategy_result.is_equivalent is False
                        and counterexample_safety_receipt is not None
                        and counterexample_raw is not None
                        and sat_counterexample_binding is not None
                    ):
                        try:
                            receipt_digest = str(counterexample_safety_receipt.receipt_digest)
                            unresolved = []
                            for pending_reason in pending_reasons:
                                self._record_completed_sat_counterexample_replay_proof(
                                    pending_reason,
                                    analysis1,
                                    analysis2,
                                    counterexample_raw=counterexample_raw,
                                    fixed_model_assertion_count=max(
                                        1,
                                        typed_counterexample_evidence.fixed_model_assertion_count,
                                    ),
                                    replay_source=(
                                        "monolithic-counterexample-safety-receipt:"
                                        f"{receipt_digest}"
                                    ),
                                    evidence_binding=sat_counterexample_binding,
                                    execution_receipt_digest=receipt_digest,
                                )
                                if not self._sat_unsafety_resolution_proof_is_complete(
                                    pending_reason,
                                    analysis1,
                                    analysis2,
                                    current_counterexample_raw=counterexample_raw,
                                    expected_binding=sat_counterexample_binding,
                                    expected_execution_receipt_digest=receipt_digest,
                                ):
                                    unresolved.append(pending_reason)
                        except (RuntimeError, ValueError, TypeError, AttributeError):
                            unresolved = list(pending_reasons)
                    sat_unsafety_resolution_pending = sat_unsafety_reason in unresolved
                    sat_replay_resolution_pending = sat_replay_reason in unresolved
                    if unresolved:
                        for pending_reason in unresolved:
                            if pending_reason not in unknown_reasons:
                                unknown_reasons.append(pending_reason)
                        self._debug_print(
                            "Monolithic SAT downgraded to UNKNOWN: bound counterexample "
                            "proof incomplete for "
                            + ", ".join(reason.reason_id for reason in unresolved)
                        )
                        strategy_result.is_equivalent = None
                        strategy_result.counterexample_raw = None
                        counterexample_raw = None
                        counterexample_safety_receipt = None
                        strategy_result.unknown_reasons = unknown_reasons
                proof_bundle = None
                if region_execution is not None and canonical_census is not None:
                    from scripts.function_tracer_pcode.proof.monolithic_authority import (
                        seal_monolithic_proof_bundle,
                        verify_monolithic_proof_bundle,
                    )
                    candidate_outcome_kind = (
                        "eq_closure" if strategy_result.is_equivalent is True
                        else "decisive_counterexample"
                        if strategy_result.is_equivalent is False
                        else "inconclusive_diagnostic"
                    )
                    proof_bundle = seal_monolithic_proof_bundle(
                        frozen_surface,
                        canonical_census,
                        expected_query_set,
                        tuple(getattr(region_execution, "execution_receipts", ()) or ()),
                        tuple(query_records),
                        candidate_outcome_kind,
                        region_execution.session_certificate,
                    )
                    if not verify_monolithic_proof_bundle(proof_bundle):
                        rejected_outcome = strategy_result.is_equivalent
                        strategy_result.is_equivalent = None
                        strategy_result.counterexample_raw = None
                        counterexample_raw = None
                        unknown_reasons.append(make_internal_v2_reason_diagnostic(
                            (
                                "comparison_equivalence_closure_unproven"
                                if rejected_outcome is True
                                else "counterexample_analysis_safety_unproven"
                            ),
                            stage="S_MONOLITHIC_FALLBACK",
                            evidence_refs=("monolithic_proof_bundle_invalid",),
                            detail=(
                                "Independent canonical census/query/execution "
                                "verification rejected monolithic evidence."
                            ),
                        ))
                        strategy_result.unknown_reasons = unknown_reasons
                    dispatch_frame.monolithic_proof_bundle = proof_bundle
                elif (
                    strategy_result.is_equivalent is False
                    and typed_counterexample_evidence is not None
                ):
                    from scripts.function_tracer_pcode.proof.monolithic_authority import (
                        seal_legacy_counterexample_proof_bundle,
                        verify_monolithic_proof_bundle,
                    )
                    whole_surface_receipts = tuple(
                        receipt for receipt in global_replay_receipts
                        if receipt.contract.replay_kind
                        == "global_case_validation:whole_surface"
                    )
                    if len(whole_surface_receipts) == 1:
                        proof_bundle = seal_legacy_counterexample_proof_bundle(
                            frozen_surface,
                            typed_counterexample_evidence.census,
                            typed_counterexample_evidence.legacy_replay_receipt,
                            whole_surface_receipts[0],
                        )
                        if not verify_monolithic_proof_bundle(proof_bundle):
                            raise RuntimeError(
                                "legacy_monolithic_proof_bundle_invalid"
                            )
                        dispatch_frame.monolithic_proof_bundle = proof_bundle
                if (
                    strategy_result.is_equivalent in {True, False}
                    and proof_bundle is None
                    and self.query_mode != "legacy"
                ):
                    rejected_outcome = strategy_result.is_equivalent
                    strategy_result.is_equivalent = None
                    strategy_result.counterexample_raw = None
                    counterexample_raw = None
                    unknown_reasons.append(make_internal_v2_reason_diagnostic(
                        (
                            "comparison_equivalence_closure_unproven"
                            if rejected_outcome is True
                            else "counterexample_analysis_safety_unproven"
                        ),
                        stage="S_MONOLITHIC_FALLBACK",
                        evidence_refs=(
                            "monolithic_structured_proof_bundle_unavailable",
                        ),
                        detail=(
                            "The legacy monolithic solver query did not carry "
                            "canonical region proof-bundle authority."
                        ),
                    ))
                    strategy_result.unknown_reasons = unknown_reasons
                # Seal all decision authority while the prepared frame and its
                # parent/child leases are still active.  Frame close only
                # validates and revokes; it can never issue evidence.
                comparison_receipt = issue_builtin_comparison_receipt(
                    dispatch_frame,
                    query_records=tuple(query_records),
                    consumed_projection_binding_ids=actual_call_projection_binding_ids,
                    disposition_counts=dict(disposition_counts),
                )
                terminal_census = (
                    typed_counterexample_evidence.census
                    if final_is_equivalent is False
                    and typed_counterexample_evidence is not None
                    else canonical_census or reconstruct_fallback_census(
                        frozen_surface
                    )
                )
                gate_refs = (
                    counterexample_safety_receipt.gate_reference_digests
                    if counterexample_safety_receipt is not None
                    else tuple(sorted({
                    hashlib.sha256(str(value).encode("utf-8")).hexdigest()
                    for value in (
                        dispatch_frame.prepared.surface_digest,
                        dispatch_frame.projection.projection_id,
                        decision_context.prepared_surface_digest or "legacy",
                        *(coverage_unsafety_reasons or ("return_coverage_closed",)),
                        *(equivalence_blocking_reasons or ("effect_projection_closed",)),
                        canonical_width_observation.binding_digest
                        if canonical_width_observation is not None else "width_surface_closed",
                    )
                    }))
                )
                reason_digests = tuple(
                    hashlib.sha256(repr(reason).encode("utf-8")).hexdigest()
                    for reason in (unknown_reasons or ("solver_inconclusive",))
                )
                final_is_equivalent = strategy_result.is_equivalent
                if final_is_equivalent is True:
                    outcome_kind = "eq_closure"
                elif final_is_equivalent is False:
                    outcome_kind = "decisive_counterexample"
                else:
                    outcome_kind = "inconclusive_diagnostic"
                safety_digest = (
                    counterexample_safety_receipt.receipt_digest
                    if final_is_equivalent is False
                    and counterexample_safety_receipt is not None else ""
                )
                region_receipt_digests = (
                    canonical_region_query_receipt_digests(query_records)
                )
                terminal_receipt = seal_terminal_decision(
                    parent_lease,
                    execution_lease,
                    frozen_surface,
                    terminal_census,
                    outcome_kind=outcome_kind,
                    comparison_receipt_id=comparison_receipt.receipt_id,
                    region_receipt_digests=region_receipt_digests,
                    sat_region_id=(
                        typed_counterexample_evidence.sat_region_id
                        if final_is_equivalent is False
                        and typed_counterexample_evidence is not None
                        else region_execution.sat_region_id
                        if region_execution else "legacy"
                    ),
                    model_digest=(
                        typed_counterexample_evidence.model_digest
                        if final_is_equivalent is False
                        and typed_counterexample_evidence is not None
                        else hashlib.sha256(repr(counterexample_raw).encode("utf-8")).hexdigest()
                        if final_is_equivalent is False else ""
                    ),
                    fixed_model_assertion_digest=(
                        typed_counterexample_evidence.fixed_model_assertion_digest
                        if final_is_equivalent is False
                        and typed_counterexample_evidence is not None
                        else hashlib.sha256(repr(counterexample_raw).encode("utf-8")).hexdigest()
                        if final_is_equivalent is False else ""
                    ),
                    legacy_replay_receipt_digest=(
                        typed_counterexample_evidence.legacy_replay_receipt.receipt_digest
                        if final_is_equivalent is False
                        and typed_counterexample_evidence is not None
                        else query_records[-1].formula_digest
                        if final_is_equivalent is False else ""
                    ),
                    counterexample_safety_receipt_digest=safety_digest,
                    proof_bundle=proof_bundle,
                    counterexample_safety_receipt=counterexample_safety_receipt,
                    explicit_legacy_validation_control=(
                        self.query_mode == "legacy"
                    ),
                    gate_reference_digests=gate_refs,
                    diagnostic_reason_digests=reason_digests,
                )
                dispatch_frame.monolithic_terminal_receipt = terminal_receipt
                if (
                    terminal_receipt.outcome_kind == "decisive_counterexample"
                    and counterexample_safety_receipt is not None
                ):
                    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                        SafeCounterexampleProductionSignal,
                        complete_observed_sat_safety_for_counterexample,
                        emit_sat_safety_signal,
                    )
                    safe_counterexample_signal = (
                        SafeCounterexampleProductionSignal.from_monolithic_receipt(
                            terminal_receipt,
                        )
                    )
                    complete_observed_sat_safety_for_counterexample(
                        safe_counterexample_signal
                    )
                    emit_sat_safety_signal(
                        safe_counterexample_signal,
                        producer_site_manifest_id=(
                            "safe-counterexample-monolithic-production"
                        ),
                    )
                strategy_result.comparison_execution_receipt = comparison_receipt
            # Fail closed on every path (also without a dispatch frame): an
            # obligation that this execution's receipt did not discharge
            # cannot leave a NOT_EQ behind (Issue #39).
            if strategy_result.is_equivalent is False and (
                sat_unsafety_resolution_pending or sat_replay_resolution_pending
            ):
                for pending_reason, pending in (
                    (sat_unsafety_reason, sat_unsafety_resolution_pending),
                    (sat_replay_reason, sat_replay_resolution_pending),
                ):
                    if pending and pending_reason is not None and pending_reason not in unknown_reasons:
                        unknown_reasons.append(pending_reason)
                self._debug_print(
                    "Monolithic SAT downgraded to UNKNOWN: counterexample proof "
                    "obligation was not discharged by this execution"
                )
                strategy_result.is_equivalent = None
                strategy_result.counterexample_raw = None
                strategy_result.unknown_reasons = unknown_reasons
            return strategy_result
        
        except ReturnWidthMismatchError as e:
            reason_id = getattr(e, "reason_id", "return_width_bridge_missing")
            self._debug_print(f"Monolithic check blocked: {reason_id}: {e}")
            blocked_result = StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[]),
                smt_formula=None,
                counterexample_raw=None,
                return_var1=None,
                return_var2=None,
                constrained_fragments=[],
                pairwise_debug_stats={reason_id: 1},
                unknown_reasons=[
                    make_unknown_reason(
                        reason_id,
                        stage="S_MONOLITHIC_FALLBACK",
                        evidence_refs=(str(e),),
                        object_target_key=(
                            "canonical_return_observation",
                            tuple(analysis1.outcome_function_identity()),
                            tuple(analysis2.outcome_function_identity()),
                            getattr(e, "return_size1", None),
                            getattr(e, "return_size2", None),
                        ),
                        detail=str(e),
                    )
                ],
            )
            if dispatch_frame is not None and dispatch_frame.receipt is None:
                issue_inconclusive_monolithic_receipts(
                    dispatch_frame, frozen_surface, canonical_census, str(e)
                )
                blocked_result.comparison_execution_receipt = dispatch_frame.receipt
            return blocked_result

        except UnknownSmtExtensionWidthError as e:
            message = str(e)
            self._debug_print(
                f"Monolithic check blocked by unknown extension width: {message}"
            )
            blocked_result = StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[]),
                smt_formula=None,
                counterexample_raw=None,
                return_var1=None,
                return_var2=None,
                constrained_fragments=[],
                unknown_reasons=[
                    make_internal_v2_reason_diagnostic(
                        "expression_semantics_unsupported",
                        stage="S_MONOLITHIC_FALLBACK",
                        evidence_refs=("unknown_smt_extension_width",),
                        object_target_key=(
                            "unknown_smt_extension_width",
                            e.operator,
                            e.operand_bits,
                            tuple(analysis1.outcome_function_identity()),
                            tuple(analysis2.outcome_function_identity()),
                        ),
                        detail=message,
                    )
                ],
            )
            if dispatch_frame is not None and dispatch_frame.receipt is None:
                issue_inconclusive_monolithic_receipts(
                    dispatch_frame, frozen_surface, canonical_census, message
                )
                blocked_result.comparison_execution_receipt = dispatch_frame.receipt
            return blocked_result

        except UnsupportedSmtIntrinsicError as e:
            message = str(e)
            self._debug_print(f"Monolithic check blocked by unresolved intrinsic: {message}")
            blocked_result = StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[]),
                smt_formula=None,
                counterexample_raw=None,
                return_var1=None,
                return_var2=None,
                constrained_fragments=[],
                unknown_reasons=[
                    make_internal_v2_reason_diagnostic(
                        "expression_semantics_unsupported",
                        stage="S_MONOLITHIC_FALLBACK",
                        evidence_refs=("unsupported_intrinsic_smt_lowering",),
                        object_target_key=(
                            "unsupported_smt_intrinsic",
                            e.intrinsic_identity,
                            tuple(analysis1.outcome_function_identity()),
                            tuple(analysis2.outcome_function_identity()),
                        ),
                        detail=message,
                    )
                ],
            )
            if dispatch_frame is not None and dispatch_frame.receipt is None:
                issue_inconclusive_monolithic_receipts(
                    dispatch_frame, frozen_surface, canonical_census, message
                )
                blocked_result.comparison_execution_receipt = dispatch_frame.receipt
            return blocked_result

        except UnsupportedSmtOperatorError as e:
            message = str(e)
            self._debug_print(
                f"Monolithic check blocked by unsupported SMT operator: {message}"
            )
            blocked_result = StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[]),
                smt_formula=None,
                counterexample_raw=None,
                return_var1=None,
                return_var2=None,
                constrained_fragments=[],
                unknown_reasons=[
                    make_internal_v2_reason_diagnostic(
                        "expression_semantics_unsupported",
                        stage="S_MONOLITHIC_FALLBACK",
                        evidence_refs=("unsupported_smt_operator",),
                        object_target_key=(
                            "unsupported_smt_operator",
                            e.operator,
                            e.reason,
                            e.operand_bits,
                            e.result_bits,
                            tuple(analysis1.outcome_function_identity()),
                            tuple(analysis2.outcome_function_identity()),
                        ),
                        detail=message,
                    )
                ],
            )
            if dispatch_frame is not None and dispatch_frame.receipt is None:
                issue_inconclusive_monolithic_receipts(
                    dispatch_frame, frozen_surface, canonical_census, message
                )
                blocked_result.comparison_execution_receipt = dispatch_frame.receipt
            return blocked_result

        except ReturnAbiAuthorityInvalid as e:
            self._debug_print(f"Monolithic check has invalid return ABI authority: {e}")
            blocked_result = StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[]),
                smt_formula=None,
                counterexample_raw=None,
                return_var1=None,
                return_var2=None,
                constrained_fragments=[],
                error_pairs=1,
                pairwise_debug_stats={"return_abi_authority_invalid": 1},
                unknown_reasons=[],
                error_kind=e.canonical_error_kind,
                error_message=str(e),
            )
            if dispatch_frame is not None and dispatch_frame.receipt is None:
                issue_inconclusive_monolithic_receipts(
                    dispatch_frame, frozen_surface, canonical_census, str(e)
                )
                blocked_result.comparison_execution_receipt = dispatch_frame.receipt
            return blocked_result

        except Exception as e:
            self._debug_print(f"Exception in monolithic check: {e}")
            if self.debug:
                import traceback
                print(traceback.format_exc())
            
            blocked_result = StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[]),
                smt_formula=None,
                counterexample_raw=None,
                return_var1=None,
                return_var2=None,
                constrained_fragments=[],
                error_pairs=1,
                pairwise_debug_stats={"strategy_exception_error": 1},
                unknown_reasons=[],
                error_kind="strategy_exception",
                error_message=str(e),
            )
            if dispatch_frame is not None and dispatch_frame.receipt is None:
                issue_inconclusive_monolithic_receipts(
                    dispatch_frame, frozen_surface, canonical_census, str(e)
                )
                blocked_result.comparison_execution_receipt = dispatch_frame.receipt
            return blocked_result
from scripts.function_tracer_pcode.proof.call_effect.preflight import (
    register_builtin_receipt_executor,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    register_canonical_guard_strategy_type,
)


# Re-exports kept for callers that import these names from this module.
from scripts.function_tracer_pcode.checker.unknown_reason import UnknownReasonId

register_canonical_guard_strategy_type(MonolithicStrategy)
register_builtin_receipt_executor("monolithic", MonolithicStrategy.check)
