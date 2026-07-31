# -*- coding: utf-8 -*-
"""Monolithic戦略（全条件を一度に検証）"""

import hashlib
import re
import time

from dataclasses import dataclass, field, replace
from typing import Optional, Dict, Any, List, Mapping, Set, Tuple

from ...model import FunctionReturnAnalysis
from ...model.render_smt import (
    UnknownSmtExtensionWidthError,
    UnsupportedSmtIntrinsicError,
)
from ...model.structural import condition_key, expression_provenance_key
from ...smt import ParallelResult
from ..formula.symbol_replace import build_symbol_replacer
from ..formula.returns import ReturnWidthMismatchError
from ..normalize import NormalizationSettings
from ..param_semantics import infer_parameter_semantics
from ..semantic_width import align_return_value_extension_surfaces, normalize_analysis_semantic_width
from ..return_width_pipeline import (
    prepare_function_return_widths,
    prepare_pair_return_observation,
    return_coverage_artifact_ids,
)
from ..query_receipt_authority import (
    canonical_region_query_receipt_digests,
)
from ..unknown_reason import (
    UnknownReasonId,
    make_internal_v2_reason_diagnostic,
    make_unknown_reason,
)
from ..monolithic_authority import (
    build_expected_region_query_set as _PINNED_BUILD_EXPECTED_REGION_QUERY_SET,
    create_shared_z3_region_session as _PINNED_CREATE_SHARED_Z3_REGION_SESSION,
    execute_expected_guard_query as _PINNED_EXECUTE_EXPECTED_GUARD_QUERY,
    execute_expected_value_query as _PINNED_EXECUTE_EXPECTED_VALUE_QUERY,
)
from .base import CheckStrategy, StrategyResult
from .pairwise_query_builder import (
    append_ordered_ite_default_case,
    build_condition_only_query,
    build_pair_query,
    extract_return_cases,
    return_cases_require_relation,
)
from .pairwise_query_executor import (
    build_counterexample_model_assertions,
    count_counterexample_model_assertions,
    execute_guard_overlap,
    solve_query_internal,
    validate_counterexample_globally,
)


@dataclass(frozen=True)
class _MonolithicReturnWidthQueryBundle:
    canonical_width: int
    observations_by_pair: Tuple[Tuple[str, Any], ...]
    left_case_identities: Tuple[Tuple[Any, ...], ...]
    right_case_identities: Tuple[Tuple[Any, ...], ...]
    ordered_receipt_digests: Tuple[str, ...]
    ordered_markers: Tuple[str, ...]
    view_digest: str
    binding_digest: str
    production_query_digest: str = ""
    production_query_text: str = field(default="", repr=False, compare=False)

    @property
    def bundle_digest(self) -> str:
        return hashlib.sha256(repr((
            "monolithic_return_width_query_bundle_v1",
            self.canonical_width,
            tuple(pair_id for pair_id, _ in self.observations_by_pair),
            self.left_case_identities,
            self.right_case_identities,
            self.ordered_receipt_digests,
            self.ordered_markers,
            self.view_digest,
            self.binding_digest,
            self.production_query_digest,
        )).encode("utf-8")).hexdigest()

    def bind_query(self, query: str) -> "_MonolithicReturnWidthQueryBundle":
        query_digest = hashlib.sha256(query.encode("utf-8")).hexdigest()
        markers = tuple(re.findall(
            r"^; canonical_return_width_binding_receipt [0-9a-f]{64}$",
            query,
            flags=re.MULTILINE,
        ))
        if markers != self.ordered_markers:
            raise ValueError("monolithic_canonical_binding_receipt_order_mismatch")
        return replace(
            self,
            production_query_digest=query_digest,
            production_query_text=query,
        )

    def validate(self) -> bool:
        return bool(
            self.production_query_text
            and len(self.production_query_digest) == 64
            and hashlib.sha256(
                self.production_query_text.encode("utf-8")
            ).hexdigest() == self.production_query_digest
            and tuple(re.findall(
                r"^; canonical_return_width_binding_receipt [0-9a-f]{64}$",
                self.production_query_text,
                flags=re.MULTILINE,
            )) == self.ordered_markers
            and tuple(
                observation.binding_receipt.binding_digest
                for _, observation in self.observations_by_pair
            ) == self.ordered_receipt_digests
        )


def _monolithic_case_identity(case: Any) -> Tuple[Any, ...]:
    return (
        "monolithic_return_case_v1",
        int(getattr(case, "index", -1)),
        tuple(int(item) for item in tuple(getattr(case, "source_indices", ()) or ())),
        tuple(expression_provenance_key(getattr(case, "value_expr", None))),
        tuple(condition_key(item) for item in tuple(getattr(case, "conditions", ()) or ())),
    )


@dataclass(frozen=True)
class _MonolithicDecisionExecutionContext:
    decision_surface: str
    analysis_object_ids: tuple[int, int]
    prepared_surface_digest: Optional[str] = None
    return_width_query_bundle: Optional[_MonolithicReturnWidthQueryBundle] = None

    @classmethod
    def create(
        cls,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        *,
        decision_surface: str,
        prepared_surface_digest: Optional[str] = None,
    ) -> "_MonolithicDecisionExecutionContext":
        if decision_surface not in {"prepared", "legacy_source"}:
            raise ValueError("invalid_monolithic_decision_surface")
        if decision_surface == "prepared" and not prepared_surface_digest:
            raise ValueError("prepared_monolithic_surface_digest_missing")
        if decision_surface == "legacy_source" and prepared_surface_digest is not None:
            raise ValueError("legacy_monolithic_surface_has_prepared_digest")
        return cls(
            decision_surface=decision_surface,
            analysis_object_ids=(id(analysis1), id(analysis2)),
            prepared_surface_digest=prepared_surface_digest,
        )

    def assert_bound_to(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> None:
        if self.analysis_object_ids != (id(analysis1), id(analysis2)):
            raise RuntimeError("monolithic_decision_context_analysis_mismatch")

    @property
    def uses_prepared_surface(self) -> bool:
        return self.decision_surface == "prepared"

    def with_return_width_query_bundle(
        self,
        bundle: _MonolithicReturnWidthQueryBundle,
    ) -> "_MonolithicDecisionExecutionContext":
        if not bundle.validate():
            raise ValueError("monolithic_return_width_query_bundle_invalid")
        return replace(self, return_width_query_bundle=bundle)


@dataclass(frozen=True)
class _MonolithicRegionPlan:
    plan_digest: str
    expected_region_ids: Tuple[str, ...]
    cases1: Tuple[Any, ...] = field(repr=False, compare=False)
    cases2: Tuple[Any, ...] = field(repr=False, compare=False)
    frozen_surface: Any = field(default=None, repr=False, compare=False)
    census: Any = field(default=None, repr=False, compare=False)


@dataclass(frozen=True)
class _MonolithicRegionExecution:
    final_is_equivalent: Optional[bool]
    parallel_result: ParallelResult
    counterexample_raw: Optional[Dict[str, Any]]
    last_formula: str
    query_records: Tuple[Any, ...]
    disposition_counts: Mapping[str, int]
    debug_stats: Mapping[str, int]
    plan: _MonolithicRegionPlan
    sat_region_id: str = ""
    model_digest: str = ""
    fixed_model_assertion_digest: str = ""
    legacy_replay_receipt_digest: str = ""
    legacy_replay_receipt: Any = None
    execution_receipts: Tuple[Any, ...] = ()
    expected_query_set: Any = None
    session_certificate: Any = None


class MonolithicStrategy(CheckStrategy):
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
        from ..obligations import AttemptCache
        self._exact_query_attempt_cache = AttemptCache(max_entries=4096)

    def _build_condition_only_query(self, *args, **kwargs) -> str:
        return build_condition_only_query(*args, **kwargs)

    def _build_pair_query(self, *args, **kwargs) -> str:
        return build_pair_query(*args, **kwargs)

    def _solve_query_internal(self, *args, **kwargs):
        return solve_query_internal(self, *args, **kwargs)

    def _save_unknown_query(self, query: str, pair_id: str, stage: str) -> None:
        del query, pair_id, stage

    def _build_region_plan(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        *,
        frozen_surface=None,
        canonical_census=None,
    ) -> Optional[_MonolithicRegionPlan]:
        if canonical_census is not None:
            if frozen_surface is None or not canonical_census.validates(frozen_surface):
                raise RuntimeError("monolithic_canonical_census_invalid")
            return _MonolithicRegionPlan(
                canonical_census.census_digest,
                canonical_census.expected_region_ids,
                canonical_census.cases1,
                canonical_census.cases2,
                frozen_surface,
                canonical_census,
            )
        raw1 = extract_return_cases(
            analysis1, self.normalization_settings, apply_effective_partition=False
        )
        raw2 = extract_return_cases(
            analysis2, self.normalization_settings, apply_effective_partition=False
        )
        if not raw1 or not raw2:
            return None
        if return_cases_require_relation(raw1) or return_cases_require_relation(raw2):
            return None
        cases1 = append_ordered_ite_default_case(
            analysis1, extract_return_cases(analysis1, self.normalization_settings)
        )
        cases2 = append_ordered_ite_default_case(
            analysis2, extract_return_cases(analysis2, self.normalization_settings)
        )
        expected = tuple(
            f"{left.index}:{right.index}"
            for left in cases1
            for right in cases2
        )
        payload = (
            "monolithic_region_plan_v1",
            tuple(analysis1.outcome_function_identity()),
            tuple(analysis2.outcome_function_identity()),
            tuple(_monolithic_case_identity(case) for case in cases1),
            tuple(_monolithic_case_identity(case) for case in cases2),
            expected,
        )
        return _MonolithicRegionPlan(
            hashlib.sha256(repr(payload).encode("utf-8")).hexdigest(),
            expected,
            tuple(cases1),
            tuple(cases2),
        )

    @staticmethod
    def _region_record(
        QueryExecutionRecord,
        *,
        label: str,
        plan_digest: str,
        formula: str,
        disposition: str,
        proof_kind: str,
        projection_binding_ids: Tuple[str, ...],
        call_width_receipt_digests: Tuple[str, ...],
        call_width_receipt_assertion_digests: Tuple[Tuple[str, str], ...],
    ):
        digest = hashlib.sha256(formula.encode("utf-8")).hexdigest()
        return QueryExecutionRecord(
            query_label=label,
            premise_digest=plan_digest,
            formula_digest=digest,
            disposition=disposition,
            proof_kind=proof_kind,
            projection_binding_ids=projection_binding_ids,
            formula_text=formula,
            call_site_return_width_receipt_digests=call_width_receipt_digests,
            call_site_return_width_receipt_assertion_digests=(
                call_width_receipt_assertion_digests
            ),
        )

    def _execute_region_plan(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        *,
        plan: _MonolithicRegionPlan,
        call_projection_assertions: Tuple[str, ...],
        call_projection_binding_ids: Tuple[str, ...],
        call_width_receipt_digests: Tuple[str, ...],
        call_width_receipt_assertion_digests: Tuple[Tuple[str, str], ...],
        QueryExecutionRecord,
        started_at: float,
        base_ctx: Optional[Mapping[str, Any]] = None,
        expected_query_set: Any = None,
        shared_region_session: Any = None,
        _execute_guard=_PINNED_EXECUTE_EXPECTED_GUARD_QUERY,
        _execute_value=_PINNED_EXECUTE_EXPECTED_VALUE_QUERY,
    ) -> _MonolithicRegionExecution:
        base_ctx_was_provided = base_ctx is not None
        base_ctx = dict(
            base_ctx
            if base_ctx is not None
            else self.formula_builder.build_base_context(analysis1, analysis2)
        )
        if call_projection_assertions and not base_ctx_was_provided:
            base_ctx["header_lines"] = [
                *list(base_ctx["header_lines"]),
                *list(call_projection_assertions),
            ]
        replace1 = build_symbol_replacer(
            base_ctx["params1"], base_ctx.get("extra_vars1", []), float_mode="fp"
        )
        replace2 = build_symbol_replacer(
            base_ctx["params2"], base_ctx.get("extra_vars2", []), float_mode="fp"
        )
        records: List[Any] = []
        execution_receipts: List[Any] = []
        terminal_results: List[Any] = []
        region_counts = {"unsat": 0, "sat": 0, "unknown": 0, "error": 0}
        query_bytes = 0
        maximum_query_bytes = 0
        guard_queries = 0
        value_queries = 0
        closed_region_ids: List[str] = []
        last_formula = ""
        counterexample_raw = None
        sat_region_id = ""
        model_digest = ""
        fixed_model_assertion_digest = ""
        legacy_replay_receipt_digest = ""
        legacy_replay_receipt = None
        sliced_assertion_bytes = 0
        shared_prelude_digests: Set[str] = set()
        configured_region_timeout = max(1, int(self.per_query_timeout))

        def remaining_timeout() -> float:
            return self.total_timeout - (time.time() - started_at)

        def disposition(value: Optional[bool]) -> str:
            return "unsat" if value is True else "sat" if value is False else "unknown"

        def projection_ids(formula: str) -> Tuple[str, ...]:
            if not call_projection_binding_ids:
                return ()
            from ..call_effect_preflight import projection_binding_evidence_from_query
            evidence = projection_binding_evidence_from_query(formula)
            return tuple(sorted(
                binding_id for binding_id in call_projection_binding_ids
                if binding_id in evidence
            ))

        for left in plan.cases1:
            for right in plan.cases2:
                region_id = f"{left.index}:{right.index}"
                if remaining_timeout() <= 0:
                    region_counts["unknown"] += 1
                    continue
                query_timeout = max(1, int(min(configured_region_timeout, remaining_timeout())))
                pair_id = f"monolithic-region-{region_id}"
                if plan.census is not None:
                    from ..monolithic_authority import render_expected_region_query
                    rendered_guard = (
                        expected_query_set.query(region_id, "guard")
                        if expected_query_set is not None
                        else render_expected_region_query(
                            plan.frozen_surface, plan.census, base_ctx, region_id, "guard"
                        )
                    )
                    guard_ctx = rendered_guard.render_context
                    guard_expected_formula = rendered_guard.formula
                    guard_premise_digest = rendered_guard.contract.contract_digest
                    sliced_assertion_bytes += rendered_guard.contract.sliced_assertion_bytes
                    shared_prelude_digests.add(rendered_guard.contract.shared_prelude_digest)
                else:
                    rendered_guard = None
                    guard_ctx = base_ctx
                    guard_expected_formula = None
                    guard_premise_digest = plan.plan_digest
                self._active_query_timeout = query_timeout
                try:
                    guard_execution = (
                        _execute_guard(
                            self, rendered_guard, left, right, replace1, replace2,
                            pair_id, shared_region_session,
                        )
                        if rendered_guard is not None
                        else execute_guard_overlap(
                            self, guard_ctx, left, right, replace1, replace2, pair_id
                        )
                    )
                finally:
                    self.__dict__.pop("_active_query_timeout", None)
                if rendered_guard is not None:
                    guard_node, guard_execution_receipt = guard_execution
                    execution_receipts.append(guard_execution_receipt)
                else:
                    guard_node = guard_execution
                guard_result = guard_node.result.raw_result
                guard_formula = str(guard_result.last_query or "")
                if guard_expected_formula is not None and guard_formula != guard_expected_formula:
                    raise RuntimeError("monolithic_guard_render_contract_mismatch")
                guard_disposition = disposition(guard_result.is_equivalent)
                guard_queries += 1
                query_bytes += len(guard_formula)
                maximum_query_bytes = max(maximum_query_bytes, len(guard_formula))
                records.append(self._region_record(
                    QueryExecutionRecord,
                    label=f"monolithic.region:{region_id}:guard",
                    plan_digest=guard_premise_digest,
                    formula=guard_formula,
                    disposition=guard_disposition,
                    proof_kind="monolithic_region_guard",
                    projection_binding_ids=projection_ids(guard_formula),
                    call_width_receipt_digests=call_width_receipt_digests,
                    call_width_receipt_assertion_digests=(
                        call_width_receipt_assertion_digests
                    ),
                ))
                last_formula = guard_formula
                if guard_result.is_equivalent is True:
                    if guard_node.disjoint_artifact is None or not guard_node.disjoint_artifact.validates():
                        region_counts["error"] += 1
                        continue
                    region_counts["unsat"] += 1
                    closed_region_ids.append(region_id)
                    terminal_results.extend(
                        getattr(guard_result.solver_results, "results", ()) or ()
                    )
                    continue
                if remaining_timeout() <= 0:
                    region_counts["unknown"] += 1
                    terminal_results.extend(
                        getattr(guard_result.solver_results, "results", ()) or ()
                    )
                    continue

                if plan.census is not None:
                    rendered_value = (
                        expected_query_set.query(region_id, "value")
                        if expected_query_set is not None
                        else render_expected_region_query(
                            plan.frozen_surface, plan.census, base_ctx, region_id, "value"
                        )
                    )
                    sliced_assertion_bytes += rendered_value.contract.sliced_assertion_bytes
                    shared_prelude_digests.add(rendered_value.contract.shared_prelude_digest)
                    value_formula = rendered_value.formula
                    value_premise_digest = rendered_value.contract.contract_digest
                else:
                    value_formula = build_pair_query(
                        base_ctx, left, right, replace1, replace2, pair_id
                    )
                    value_premise_digest = plan.plan_digest
                query_timeout = max(1, int(min(configured_region_timeout, remaining_timeout())))
                self._active_query_timeout = query_timeout
                try:
                    value_execution = (
                        _execute_value(
                            self, rendered_value, pair_id, shared_region_session
                        )
                        if plan.census is not None
                        else self._solve_query_internal(
                            value_formula, pair_id, stage="monolithic-region-value"
                        )
                    )
                finally:
                    self.__dict__.pop("_active_query_timeout", None)
                if plan.census is not None:
                    value_result, value_execution_receipt = value_execution
                    execution_receipts.append(value_execution_receipt)
                else:
                    value_result = value_execution
                value_disposition = disposition(value_result.is_equivalent)
                value_queries += 1
                query_bytes += len(value_formula)
                maximum_query_bytes = max(maximum_query_bytes, len(value_formula))
                records.append(self._region_record(
                    QueryExecutionRecord,
                    label=f"monolithic.region:{region_id}:value",
                    plan_digest=value_premise_digest,
                    formula=value_formula,
                    disposition=value_disposition,
                    proof_kind="monolithic_region_value_inequality",
                    projection_binding_ids=projection_ids(value_formula),
                    call_width_receipt_digests=call_width_receipt_digests,
                    call_width_receipt_assertion_digests=(
                        call_width_receipt_assertion_digests
                    ),
                ))
                last_formula = value_formula
                terminal_results.extend(
                    getattr(value_result.solver_results, "results", ()) or ()
                )
                if value_result.is_equivalent is True:
                    region_counts["unsat"] += 1
                    closed_region_ids.append(region_id)
                    continue
                if value_result.is_equivalent is None:
                    region_counts["unknown"] += 1
                    continue

                # The final verifier requires a complete canonical region
                # census even after one distinguishing region is found.  A
                # later SAT region is recorded, but the first independently
                # replayed whole-surface witness remains the terminal model.
                if sat_region_id:
                    continue

                # A local SAT is only diagnostic until the same model satisfies
                # the complete frozen-surface violation predicate.
                model_assertions = tuple(build_counterexample_model_assertions(
                    base_ctx, value_result.counterexample_raw
                ))
                model_digest = hashlib.sha256(
                    repr(value_result.counterexample_raw).encode("utf-8")
                ).hexdigest()
                fixed_model_assertion_digest = hashlib.sha256(
                    "\n".join(model_assertions).encode("utf-8")
                ).hexdigest()
                replay_targets_exist = bool(
                    base_ctx.get("params1")
                    or base_ctx.get("params2")
                    or base_ctx.get("extra_vars1")
                    or base_ctx.get("extra_vars2")
                )
                if (replay_targets_exist and not model_assertions) or remaining_timeout() <= 0:
                    region_counts["unknown"] += 1
                    continue
                replay = self.formula_builder.build_equivalence_formula_extended(
                    analysis1,
                    analysis2,
                    extra_assertions=[
                        *list(call_projection_assertions),
                        *list(model_assertions),
                    ],
                )
                replay_formula = replay.formula
                if plan.census is not None:
                    from ..monolithic_authority import execute_legacy_violation_replay
                    replay_result, legacy_replay_receipt = execute_legacy_violation_replay(
                        self,
                        plan.frozen_surface,
                        plan.census,
                        formula=replay_formula,
                        model_digest=model_digest,
                        fixed_model_assertion_digest=fixed_model_assertion_digest,
                        timeout=max(1, int(remaining_timeout())),
                    )
                else:
                    replay_result = (
                        self.solver_runner.run_sequential(
                            replay_formula, timeout=max(1, int(remaining_timeout()))
                        )
                        if self.debug
                        else self.solver_runner.run_parallel(
                            replay_formula, timeout=max(1, int(remaining_timeout()))
                        )
                    )
                replay_disposition = disposition(replay_result.is_equivalent)
                query_bytes += len(replay_formula)
                maximum_query_bytes = max(maximum_query_bytes, len(replay_formula))
                records.append(self._region_record(
                    QueryExecutionRecord,
                    label=f"monolithic.region:{region_id}:global-replay",
                    plan_digest=plan.plan_digest,
                    formula=replay_formula,
                    disposition=replay_disposition,
                    proof_kind="monolithic_global_counterexample_replay",
                    projection_binding_ids=projection_ids(replay_formula),
                    call_width_receipt_digests=call_width_receipt_digests,
                    call_width_receipt_assertion_digests=(
                        call_width_receipt_assertion_digests
                    ),
                ))
                legacy_replay_receipt_digest = (
                    legacy_replay_receipt.receipt_digest
                    if legacy_replay_receipt is not None
                    else records[-1].formula_digest
                )
                last_formula = replay_formula
                terminal_results.extend(getattr(replay_result, "results", ()) or ())
                if replay_result.is_equivalent is False:
                    region_counts["sat"] = 1
                    counterexample_raw = replay_result.get_counterexample() or value_result.counterexample_raw
                    sat_region_id = region_id
                    continue
                region_counts["unknown"] += 1

        planned = len(plan.expected_region_ids)
        all_closed = (
            len(closed_region_ids) == planned
            and tuple(closed_region_ids) == plan.expected_region_ids
        )
        final = False if region_counts["sat"] else True if all_closed else None
        aggregate = ParallelResult(
            results=list(terminal_results),
            is_equivalent=final,
        )
        counts = {
            "total": planned,
            **region_counts,
            "planned_regions": planned,
            "closed_regions": len(closed_region_ids),
        }
        stats = {
            "monolithic_split_planned_regions": planned,
            "monolithic_split_closed_regions": len(closed_region_ids),
            "monolithic_split_guard_queries": guard_queries,
            "monolithic_split_value_queries": value_queries,
            "monolithic_split_query_bytes": query_bytes,
            "monolithic_split_max_query_bytes": maximum_query_bytes,
            "monolithic_split_sliced_assertion_bytes": sliced_assertion_bytes,
            "monolithic_split_shared_preludes": len(shared_prelude_digests),
            "monolithic_split_shared_z3_contexts": (
                1 if shared_region_session is not None else 0
            ),
            "monolithic_split_shared_z3_asts": int(getattr(
                shared_region_session,
                "shared_ast_count", 0,
            )),
            "monolithic_split_shared_z3_checks": int(getattr(
                shared_region_session,
                "check_count", 0,
            )),
        }
        return _MonolithicRegionExecution(
            final,
            aggregate,
            counterexample_raw,
            last_formula,
            tuple(records),
            counts,
            stats,
            plan,
            sat_region_id,
            model_digest,
            fixed_model_assertion_digest,
            legacy_replay_receipt_digest,
            legacy_replay_receipt,
            tuple(execution_receipts),
            expected_query_set,
            getattr(shared_region_session, "certificate", None),
        )

    def _canonical_return_width_observation_for_analyses(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ):
        runtime = getattr(self, "_obligation_runtime_session", None)
        cases1 = extract_return_cases(analysis1, self.normalization_settings)
        cases2 = extract_return_cases(analysis2, self.normalization_settings)
        if not cases1 or not cases2:
            return None
        prepared1 = prepare_function_return_widths(analysis1, cases1)
        prepared2 = prepare_function_return_widths(analysis2, cases2)
        base_ctx = self.formula_builder.build_base_context(analysis1, analysis2)
        replace1 = build_symbol_replacer(
            base_ctx["params1"], base_ctx.get("extra_vars1", []), float_mode="fp"
        )
        replace2 = build_symbol_replacer(
            base_ctx["params2"], base_ctx.get("extra_vars2", []), float_mode="fp"
        )
        from .proof_gates.return_coverage import (
            prepare_unary_return_coverage_for_width,
        )
        prepare_unary_return_coverage_for_width(
            self,
            base_ctx,
            analysis1,
            analysis2,
            replace1,
            replace2,
        )
        coverage_ids = return_coverage_artifact_ids(
            runtime,
            (
                tuple(analysis1.outcome_function_identity()),
                tuple(analysis2.outcome_function_identity()),
            ),
        )
        if not coverage_ids:
            return None
        observations = []
        for left_index, left in enumerate(cases1):
            for right_index, right in enumerate(cases2):
                observations.append((
                    f"({left_index},{right_index})",
                    prepare_pair_return_observation(
                analysis1,
                analysis2,
                left,
                right,
                prepared1,
                prepared2,
                return_coverage_ids=coverage_ids,
                proof_runtime=runtime,
                left_query_parameters=base_ctx["params1"],
                right_query_parameters=base_ctx["params2"],
                left_replace_fn=replace1,
                right_replace_fn=replace2,
                    ),
                ))
        if not observations or not all(item.proven for _, item in observations):
            return None
        widths = {item.view.canonical_comparison_width for _, item in observations}
        if len(widths) != 1:
            return None
        view_digest = hashlib.sha256(
            repr(tuple(item.view.digest for _, item in observations)).encode("utf-8")
        ).hexdigest()
        binding_digest = hashlib.sha256(
            repr(tuple(item.binding_receipt.binding_digest for _, item in observations)).encode("utf-8")
        ).hexdigest()
        markers = tuple(
            f"; canonical_return_width_binding_receipt {item.binding_receipt.binding_digest}"
            for _, item in observations
        )
        return _MonolithicReturnWidthQueryBundle(
            canonical_width=next(iter(widths)),
            observations_by_pair=tuple(observations),
            left_case_identities=tuple(_monolithic_case_identity(item) for item in cases1),
            right_case_identities=tuple(_monolithic_case_identity(item) for item in cases2),
            ordered_receipt_digests=tuple(
                item.binding_receipt.binding_digest for _, item in observations
            ),
            ordered_markers=markers,
            view_digest=view_digest,
            binding_digest=binding_digest,
        )

    def _bind_original_canonical_return_width_replay_observations(
        self,
        decision_context: _MonolithicDecisionExecutionContext,
        base_ctx: Dict[str, Any],
        cases1,
        cases2,
    ) -> bool:
        """Reuse the exact receipt bundle consumed by the production query."""

        if int(base_ctx.get("return_size1", 32)) == int(base_ctx.get("return_size2", 32)):
            return True
        bundle = decision_context.return_width_query_bundle
        if bundle is None or not bundle.validate():
            return False
        if (
            tuple(_monolithic_case_identity(item) for item in cases1)
            != bundle.left_case_identities
            or tuple(_monolithic_case_identity(item) for item in cases2)
            != bundle.right_case_identities
        ):
            return False
        base_ctx["return_width_observations_by_pair"] = dict(
            bundle.observations_by_pair
        )
        base_ctx["canonical_return_replay_authorization"] = {
            "bundle_digest": bundle.bundle_digest,
            "production_query_digest": bundle.production_query_digest,
            "ordered_receipt_digests": bundle.ordered_receipt_digests,
            "binding_projection_order": tuple(
                pair_id for pair_id, _ in bundle.observations_by_pair
            ),
        }
        base_ctx["require_original_canonical_return_query_bundle"] = True
        return bool(bundle.observations_by_pair)

    def _counterexample_is_decisive_across_case_split(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        counterexample_raw: Optional[Dict[str, Any]],
    ) -> bool:
        decision_context = _MonolithicDecisionExecutionContext.create(
            analysis1,
            analysis2,
            decision_surface="legacy_source",
        )
        return self._counterexample_is_decisive_for_surface(
            analysis1,
            analysis2,
            counterexample_raw,
            decision_context,
        )

    def _counterexample_is_decisive_for_surface(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        counterexample_raw: Optional[Dict[str, Any]],
        decision_context: _MonolithicDecisionExecutionContext,
    ) -> bool:
        decision_context.assert_bound_to(analysis1, analysis2)
        self._last_counterexample_replay_fixed_model_assertion_count = 0
        if not counterexample_raw:
            return True

        normalized1, normalized2 = self._build_validation_analyses_for_surface(
            analysis1,
            analysis2,
            decision_context,
        )
        base_ctx = self.formula_builder.build_base_context(normalized1, normalized2)
        self._last_counterexample_replay_fixed_model_assertion_count = (
            count_counterexample_model_assertions(base_ctx, counterexample_raw)
        )
        if decision_context.uses_prepared_surface:
            render_analysis1, render_analysis2 = normalized1, normalized2
        else:
            render_analysis1 = normalize_analysis_semantic_width(
                normalized1,
                infer_parameter_semantics(normalized1),
                base_ctx.get("extra_vars1", []),
            )
            render_analysis2 = normalize_analysis_semantic_width(
                normalized2,
                infer_parameter_semantics(normalized2),
                base_ctx.get("extra_vars2", []),
            )

        cases1 = extract_return_cases(render_analysis1, self.normalization_settings)
        cases2 = extract_return_cases(render_analysis2, self.normalization_settings)
        if not cases1 or not cases2:
            self._debug_print(
                "Monolithic SAT counterexample rejected: no return cases available for validation"
            )
            return False

        replace1 = build_symbol_replacer(
            base_ctx["params1"],
            base_ctx.get("extra_vars1", []),
            float_mode="fp",
        )
        replace2 = build_symbol_replacer(
            base_ctx["params2"],
            base_ctx.get("extra_vars2", []),
            float_mode="fp",
        )
        if not self._bind_original_canonical_return_width_replay_observations(
            decision_context,
            base_ctx,
            cases1,
            cases2,
        ):
            self._debug_print(
                "Monolithic SAT counterexample rejected: canonical return-width receipt "
                "is not applicable to the replay cases"
            )
            return False
        return validate_counterexample_globally(
            self,
            base_ctx,
            cases1,
            cases2,
            replace1,
            replace2,
            counterexample_raw,
        )

    def _dispatch_counterexample_decisiveness(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        counterexample_raw: Optional[Dict[str, Any]],
        decision_context: _MonolithicDecisionExecutionContext,
    ) -> bool:
        """Preserve the legacy override hook without ambient context reads."""

        validator = self._counterexample_is_decisive_across_case_split
        if getattr(validator, "__func__", None) is MonolithicStrategy._counterexample_is_decisive_across_case_split:
            return self._counterexample_is_decisive_for_surface(
                analysis1,
                analysis2,
                counterexample_raw,
                decision_context,
            )
        return validator(analysis1, analysis2, counterexample_raw)
    def _build_validation_analyses(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> tuple[FunctionReturnAnalysis, FunctionReturnAnalysis]:
        decision_context = _MonolithicDecisionExecutionContext.create(
            analysis1,
            analysis2,
            decision_surface="legacy_source",
        )
        return self._build_validation_analyses_for_surface(
            analysis1,
            analysis2,
            decision_context,
        )

    def _build_validation_analyses_for_surface(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        decision_context: _MonolithicDecisionExecutionContext,
    ) -> tuple[FunctionReturnAnalysis, FunctionReturnAnalysis]:
        decision_context.assert_bound_to(analysis1, analysis2)
        if decision_context.uses_prepared_surface:
            # The preflight certificate and comparison receipt are bound to
            # these exact children.  Decision-side validation must not derive
            # an unreceipted normalization/alignment surface.
            return analysis1, analysis2
        hints1 = infer_parameter_semantics(analysis1)
        hints2 = infer_parameter_semantics(analysis2)
        normalized1 = normalize_analysis_semantic_width(analysis1, hints1)
        normalized2 = normalize_analysis_semantic_width(analysis2, hints2)
        return align_return_value_extension_surfaces(
            normalized1,
            normalized2,
        )

    def _collect_monolithic_return_coverage_unsafety_reasons(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        decision_context: _MonolithicDecisionExecutionContext,
    ) -> list[str]:
        decision_context.assert_bound_to(analysis1, analysis2)
        normalized1, normalized2 = self._build_validation_analyses_for_surface(
            analysis1,
            analysis2,
            decision_context,
        )
        preliminary_cases1 = extract_return_cases(normalized1, self.normalization_settings)
        preliminary_cases2 = extract_return_cases(normalized2, self.normalization_settings)
        if self._return_cases_have_object_centric_total_coverage(
            preliminary_cases1
        ) and self._return_cases_have_object_centric_total_coverage(preliminary_cases2):
            return []

        base_ctx = self.formula_builder.build_base_context(normalized1, normalized2)
        if decision_context.uses_prepared_surface:
            render_analysis1, render_analysis2 = normalized1, normalized2
            assert render_analysis1 is analysis1 and render_analysis2 is analysis2
        else:
            render_analysis1 = normalize_analysis_semantic_width(
                normalized1,
                infer_parameter_semantics(normalized1),
                base_ctx.get("extra_vars1", []),
            )
            render_analysis2 = normalize_analysis_semantic_width(
                normalized2,
                infer_parameter_semantics(normalized2),
                base_ctx.get("extra_vars2", []),
            )
            render_analysis1, render_analysis2 = align_return_value_extension_surfaces(
                render_analysis1,
                render_analysis2,
            )
        cases1 = extract_return_cases(render_analysis1, self.normalization_settings)
        cases2 = extract_return_cases(render_analysis2, self.normalization_settings)
        replace1 = build_symbol_replacer(
            base_ctx["params1"],
            base_ctx.get("extra_vars1", []),
            float_mode="fp",
        )
        replace2 = build_symbol_replacer(
            base_ctx["params2"],
            base_ctx.get("extra_vars2", []),
            float_mode="fp",
        )
        reasons = self._collect_return_coverage_unsafety_reasons(
            base_ctx,
            cases1,
            cases2,
            replace1,
            replace2,
            analysis1,
            analysis2,
        )
        self._record_return_coverage_notes(analysis1, analysis2, reasons)
        return reasons

    def _record_return_coverage_notes(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        reasons: list[str],
    ) -> None:
        for label, analysis in (("function1", analysis1), ("function2", analysis2)):
            if f"{label}:return_coverage_gap" in reasons and "return_case_coverage_gap" not in analysis.analysis_notes:
                analysis.analysis_notes.append("return_case_coverage_gap")
            if (
                f"{label}:return_coverage_inconclusive" in reasons
                and "return_case_coverage_inconclusive" not in analysis.analysis_notes
            ):
                analysis.analysis_notes.append("return_case_coverage_inconclusive")
    
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
        from ..call_effect_preflight import (
            QueryExecutionRecord,
            consume_prepared_dispatch_frame,
            current_dispatch_depth,
            issue_builtin_comparison_receipt,
            issue_inconclusive_monolithic_receipts,
            lower_call_projection_for_case_pair,
            projection_binding_evidence_from_query,
        )
        from ..monolithic_authority import (
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
                except ReturnWidthMismatchError as width_mismatch:
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
                    parallel_result.get_counterexample()
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
            unknown_reasons = []
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
            sat_unsafety_reasons.extend(coverage_unsafety_reasons)
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
            if final_is_equivalent is False and sat_unsafety_reasons:
                sat_unsafety_reason = self._make_sat_unsafety_unknown_reason(
                    sat_unsafety_reasons,
                    analysis1,
                    analysis2,
                    case1=None,
                    case2=None,
                    pair_id="monolithic",
                    stage="S_MONOLITHIC_FALLBACK",
                )
                if not self._sat_unsafety_resolution_proof_is_complete(
                    sat_unsafety_reason,
                    analysis1,
                    analysis2,
                    current_counterexample_raw=counterexample_raw,
                ):
                    unknown_reasons.append(sat_unsafety_reason)
                    self._debug_print(
                        "Monolithic SAT downgraded to UNKNOWN due to unsafe analysis summary "
                        f"({', '.join(sat_unsafety_reasons)})"
                    )
                    final_is_equivalent = None
                    counterexample_raw = None
            counterexample_is_decisive = True
            if final_is_equivalent is False:
                replay_collector = None
                if (
                    region_execution is not None
                    and frozen_surface is not None
                    and canonical_census is not None
                ):
                    from ..monolithic_authority import create_global_replay_collector
                    global_replay_receipts, replay_collector = create_global_replay_collector(
                        frozen_surface,
                        canonical_census,
                        model_digest=region_execution.model_digest,
                        fixed_model_assertion_digest=(
                            region_execution.fixed_model_assertion_digest
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
                    and region_execution is not None
                    and frozen_surface is not None
                    and canonical_census is not None
                ):
                    from ..monolithic_authority import execute_global_violation_replay
                    global_result, global_receipt = execute_global_violation_replay(
                        self,
                        frozen_surface,
                        canonical_census,
                        formula=region_execution.last_formula,
                        model_digest=region_execution.model_digest,
                        fixed_model_assertion_digest=(
                            region_execution.fixed_model_assertion_digest
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
            same_function_replay_reasons = ()
            if final_is_equivalent is False:
                typed_whole_surface_replay_complete = bool(
                    region_execution is not None
                    and region_execution.legacy_replay_receipt is not None
                    and region_execution.legacy_replay_receipt.disposition == "sat"
                    and any(
                        receipt.contract.replay_kind
                        == "global_case_validation:whole_surface"
                        and receipt.disposition == "sat"
                        for receipt in global_replay_receipts
                    )
                )
                if not typed_whole_surface_replay_complete:
                    same_function_replay_reasons = (
                        self._same_function_counterexample_replay_reasons(
                            analysis1,
                            analysis2,
                        )
                    )
            if final_is_equivalent is False and same_function_replay_reasons:
                sat_replay_reason = self._make_sat_unsafety_unknown_reason(
                    same_function_replay_reasons,
                    analysis1,
                    analysis2,
                    case1=None,
                    case2=None,
                    pair_id="monolithic",
                    stage="S_MONOLITHIC_FALLBACK",
                )
                if not self._sat_unsafety_resolution_proof_is_complete(
                    sat_replay_reason,
                    analysis1,
                    analysis2,
                    current_counterexample_raw=counterexample_raw,
                ):
                    unknown_reasons.append(sat_replay_reason)
                    self._debug_print(
                        "Monolithic SAT downgraded to UNKNOWN until same-function "
                        "counterexample replay is completed"
                    )
                    final_is_equivalent = None
                    counterexample_raw = None
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
                        from ..monolithic_authority import (
                            issue_counterexample_safety_decision_receipt,
                            gate_source_artifact_id,
                            issue_gate_artifact_reference,
                        )
                        if (
                            region_execution is None
                            or region_execution.legacy_replay_receipt is None
                            or canonical_census is None
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
                            ),
                            issue_gate_artifact_reference(
                                frozen_surface, "effect",
                                effect_source,
                                artifact_id=gate_source_artifact_id(
                                    "effect",
                                    effect_source,
                                ), status=projection_status,
                            ),
                            issue_gate_artifact_reference(
                                frozen_surface, "projection", dispatch_frame.projection,
                                artifact_id=dispatch_frame.projection.projection_id,
                                status=projection_status,
                            ),
                            issue_gate_artifact_reference(
                                frozen_surface, "width", width_source,
                                artifact_id=gate_source_artifact_id(
                                    "width", width_source
                                ), status=("proven" if canonical_width_observation
                                           is not None else "not_required"),
                            ),
                        )
                        counterexample_safety_receipt = (
                            issue_counterexample_safety_decision_receipt(
                                frozen_surface,
                                canonical_census,
                                model_digest=region_execution.model_digest,
                                fixed_model_assertion_digest=(
                                    region_execution.fixed_model_assertion_digest
                                ),
                                legacy_replay_receipt=(
                                    region_execution.legacy_replay_receipt
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
                proof_bundle = None
                if region_execution is not None and canonical_census is not None:
                    from ..monolithic_authority import (
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
                terminal_census = canonical_census or reconstruct_fallback_census(
                    frozen_surface
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
                    sat_region_id=(region_execution.sat_region_id if region_execution else "legacy"),
                    model_digest=(
                        region_execution.model_digest
                        if region_execution is not None
                        else hashlib.sha256(repr(counterexample_raw).encode("utf-8")).hexdigest()
                        if final_is_equivalent is False else ""
                    ),
                    fixed_model_assertion_digest=(
                        region_execution.fixed_model_assertion_digest
                        if region_execution is not None
                        else hashlib.sha256(repr(counterexample_raw).encode("utf-8")).hexdigest()
                        if final_is_equivalent is False else ""
                    ),
                    legacy_replay_receipt_digest=(
                        region_execution.legacy_replay_receipt_digest
                        if region_execution is not None
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
                strategy_result.comparison_execution_receipt = comparison_receipt
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
from ..call_effect_preflight import register_builtin_receipt_executor
from .pairwise_query_executor import register_canonical_guard_strategy_type

register_canonical_guard_strategy_type(MonolithicStrategy)
register_builtin_receipt_executor("monolithic", MonolithicStrategy.check)
