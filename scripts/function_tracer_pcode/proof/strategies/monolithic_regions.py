"""Region-split query planning and execution for the monolithic strategy."""

from __future__ import annotations

import hashlib
import time
from typing import Optional, Any, List, Mapping, Set, Tuple
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.proof.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.proof.monolithic_authority import (
    build_expected_region_query_set as _PINNED_BUILD_EXPECTED_REGION_QUERY_SET,
    create_shared_z3_region_session as _PINNED_CREATE_SHARED_Z3_REGION_SESSION,
    execute_expected_guard_query as _PINNED_EXECUTE_EXPECTED_GUARD_QUERY,
    execute_expected_value_query as _PINNED_EXECUTE_EXPECTED_VALUE_QUERY,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    append_ordered_ite_default_case,
    build_pair_query,
    extract_return_cases,
    return_cases_require_relation,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    build_counterexample_model_assertions,
    execute_guard_overlap,
)
from scripts.function_tracer_pcode.proof.strategies.monolithic_support import (
    _monolithic_case_identity,
    _MonolithicRegionPlan,
    _MonolithicRegionExecution,
)


class RegionExecutionMixin:
    """Region-split query planning and execution for the monolithic strategy."""

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
        input_correspondence: Any,
        base_ctx: Optional[Mapping[str, Any]] = None,
        expected_query_set: Any = None,
        shared_region_session: Any = None,
        replay_frozen_surface: Any = None,
        replay_census: Any = None,
        _execute_guard=_PINNED_EXECUTE_EXPECTED_GUARD_QUERY,
        _execute_value=_PINNED_EXECUTE_EXPECTED_VALUE_QUERY,
    ) -> _MonolithicRegionExecution:
        base_ctx_was_provided = base_ctx is not None
        base_ctx = dict(
            base_ctx
            if base_ctx is not None
            else self.formula_builder.build_base_context(
                analysis1,
                analysis2,
                input_correspondence=input_correspondence,
            )
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
        sat_replay_formula = ""
        sat_replay_census = None
        sat_model_digest = ""
        sat_fixed_model_assertion_digest = ""
        sat_legacy_replay_receipt = None
        sat_legacy_replay_receipt_digest = ""
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
            from scripts.function_tracer_pcode.proof.call_effect.preflight import (
                projection_binding_evidence_from_query,
            )
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
                    from scripts.function_tracer_pcode.proof.monolithic_authority import (
                        render_expected_region_query,
                    )
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
                    input_correspondence=input_correspondence,
                    extra_assertions=[
                        *list(call_projection_assertions),
                        *list(model_assertions),
                    ],
                )
                replay_formula = replay.formula
                authoritative_replay_frozen = (
                    replay_frozen_surface or plan.frozen_surface
                )
                authoritative_replay_census = replay_census or plan.census
                # A receipt is valid only for the formula executed in this
                # iteration.  Never carry a prior region's receipt into a
                # direct-solver replay that lacks canonical surface authority.
                legacy_replay_receipt = None
                if (
                    authoritative_replay_frozen is not None
                    and authoritative_replay_census is not None
                ):
                    from scripts.function_tracer_pcode.proof.monolithic_authority import (
                        execute_legacy_violation_replay,
                    )
                    replay_result, legacy_replay_receipt = execute_legacy_violation_replay(
                        self,
                        authoritative_replay_frozen,
                        authoritative_replay_census,
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
                    sat_replay_formula = replay_formula
                    sat_replay_census = authoritative_replay_census
                    sat_model_digest = model_digest
                    sat_fixed_model_assertion_digest = fixed_model_assertion_digest
                    sat_legacy_replay_receipt = legacy_replay_receipt
                    sat_legacy_replay_receipt_digest = legacy_replay_receipt_digest
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
            final_is_equivalent=final,
            parallel_result=aggregate,
            counterexample_raw=counterexample_raw,
            last_formula=last_formula,
            query_records=tuple(records),
            disposition_counts=counts,
            debug_stats=stats,
            plan=plan,
            sat_region_id=sat_region_id,
            model_digest=sat_model_digest if final is False else model_digest,
            fixed_model_assertion_digest=(
                sat_fixed_model_assertion_digest
                if final is False else fixed_model_assertion_digest
            ),
            legacy_replay_receipt_digest=(
                sat_legacy_replay_receipt_digest
                if final is False else legacy_replay_receipt_digest
            ),
            legacy_replay_receipt=(
                sat_legacy_replay_receipt if final is False else legacy_replay_receipt
            ),
            execution_receipts=tuple(execution_receipts),
            expected_query_set=expected_query_set,
            session_certificate=getattr(shared_region_session, "certificate", None),
            sat_replay_formula=sat_replay_formula,
            sat_replay_census=sat_replay_census,
            input_correspondence=base_ctx.get("input_correspondence"),
            extra_vars1=base_ctx.get("extra_vars1"),
            extra_vars2=base_ctx.get("extra_vars2"),
        )
