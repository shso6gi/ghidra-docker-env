"""Counterexample decisiveness across case splits and surfaces."""

from __future__ import annotations

from typing import Optional, Dict, Any
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
from scripts.function_tracer_pcode.proof.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.semantics.param_semantics import infer_parameter_semantics
from scripts.function_tracer_pcode.semantics.semantic_width import normalize_analysis_semantic_width
from scripts.function_tracer_pcode.proof.monolithic_authority import (
    build_expected_region_query_set as _PINNED_BUILD_EXPECTED_REGION_QUERY_SET,
    create_shared_z3_region_session as _PINNED_CREATE_SHARED_Z3_REGION_SESSION,
    execute_expected_guard_query as _PINNED_EXECUTE_EXPECTED_GUARD_QUERY,
    execute_expected_value_query as _PINNED_EXECUTE_EXPECTED_VALUE_QUERY,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    extract_return_cases,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    count_counterexample_model_assertions,
    validate_counterexample_globally,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    LEFT as INPUT_LEFT,
    RIGHT as INPUT_RIGHT,
    build_input_correspondence_set,
)
from scripts.function_tracer_pcode.proof.strategies.monolithic_support import (
    _MonolithicDecisionExecutionContext,
)


class CounterexampleDecisivenessMixin:
    """Counterexample decisiveness across case splits and surfaces."""

    def _counterexample_is_decisive_across_case_split(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        counterexample_raw: Optional[Dict[str, Any]],
    ) -> bool:
        # 互換経路（raw pair を直接渡す seam）: relation はその raw pair から作る。
        decision_context = _MonolithicDecisionExecutionContext.create(
            analysis1,
            analysis2,
            decision_surface="legacy_source",
            input_correspondence=build_input_correspondence_set(analysis1, analysis2),
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
        base_ctx = self.formula_builder.build_base_context(
            normalized1,
            normalized2,
            input_correspondence=decision_context.input_correspondence,
        )
        self._last_counterexample_replay_fixed_model_assertion_count = (
            count_counterexample_model_assertions(base_ctx, counterexample_raw)
        )
        if decision_context.uses_prepared_surface:
            render_analysis1, render_analysis2 = normalized1, normalized2
        else:
            render_analysis1 = normalize_analysis_semantic_width(
                normalized1,
                infer_parameter_semantics(normalized1),
                authorization=decision_context.authorization(INPUT_LEFT),
            )
            render_analysis2 = normalize_analysis_semantic_width(
                normalized2,
                infer_parameter_semantics(normalized2),
                authorization=decision_context.authorization(INPUT_RIGHT),
            )

        cases1 = extract_return_cases(
            render_analysis1,
            self.normalization_settings,
            authorization=decision_context.authorization(INPUT_LEFT),
        )
        cases2 = extract_return_cases(
            render_analysis2,
            self.normalization_settings,
            authorization=decision_context.authorization(INPUT_RIGHT),
        )
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
        from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy

        if getattr(validator, "__func__", None) is MonolithicStrategy._counterexample_is_decisive_across_case_split:
            return self._counterexample_is_decisive_for_surface(
                analysis1,
                analysis2,
                counterexample_raw,
                decision_context,
            )
        return validator(analysis1, analysis2, counterexample_raw)
