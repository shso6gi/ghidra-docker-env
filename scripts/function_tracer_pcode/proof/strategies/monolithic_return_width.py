"""Canonical return-width observations and return-coverage unsafety for the monolithic strategy."""

from __future__ import annotations

import hashlib
from typing import Dict, Any
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
from scripts.function_tracer_pcode.proof.formula.symbol_replace import build_symbol_replacer
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
from scripts.function_tracer_pcode.proof.monolithic_authority import (
    build_expected_region_query_set as _PINNED_BUILD_EXPECTED_REGION_QUERY_SET,
    create_shared_z3_region_session as _PINNED_CREATE_SHARED_Z3_REGION_SESSION,
    execute_expected_guard_query as _PINNED_EXECUTE_EXPECTED_GUARD_QUERY,
    execute_expected_value_query as _PINNED_EXECUTE_EXPECTED_VALUE_QUERY,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    extract_return_cases,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    LEFT as INPUT_LEFT,
    RIGHT as INPUT_RIGHT,
)
from scripts.function_tracer_pcode.proof.strategies.monolithic_support import (
    _MonolithicReturnWidthQueryBundle,
    _monolithic_case_identity,
    _MonolithicDecisionExecutionContext,
)


class ReturnWidthObservationMixin:
    """Canonical return-width observations and return-coverage unsafety for the monolithic strategy."""

    def _canonical_return_width_observation_for_analyses(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        *,
        input_correspondence,
    ):
        runtime = getattr(self, "_obligation_runtime_session", None)
        cases1 = extract_return_cases(
            analysis1,
            self.normalization_settings,
            authorization=input_correspondence.authorization(INPUT_LEFT),
        )
        cases2 = extract_return_cases(
            analysis2,
            self.normalization_settings,
            authorization=input_correspondence.authorization(INPUT_RIGHT),
        )
        if not cases1 or not cases2:
            return None
        prepared1 = prepare_function_return_widths(analysis1, cases1)
        prepared2 = prepare_function_return_widths(analysis2, cases2)
        base_ctx = self.formula_builder.build_base_context(
            analysis1,
            analysis2,
            input_correspondence=input_correspondence,
        )
        replace1 = build_symbol_replacer(
            base_ctx["params1"], base_ctx.get("extra_vars1", []), float_mode="fp"
        )
        replace2 = build_symbol_replacer(
            base_ctx["params2"], base_ctx.get("extra_vars2", []), float_mode="fp"
        )
        from scripts.function_tracer_pcode.proof.strategies.proof_gates.return_coverage import (
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
        normalized1 = normalize_analysis_semantic_width(
            analysis1, hints1, authorization=decision_context.authorization(INPUT_LEFT)
        )
        normalized2 = normalize_analysis_semantic_width(
            analysis2, hints2, authorization=decision_context.authorization(INPUT_RIGHT)
        )
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
        preliminary_cases1 = extract_return_cases(
            normalized1,
            self.normalization_settings,
            authorization=decision_context.authorization(INPUT_LEFT),
        )
        preliminary_cases2 = extract_return_cases(
            normalized2,
            self.normalization_settings,
            authorization=decision_context.authorization(INPUT_RIGHT),
        )
        if self._return_cases_have_object_centric_total_coverage(
            preliminary_cases1
        ) and self._return_cases_have_object_centric_total_coverage(preliminary_cases2):
            return []

        base_ctx = self.formula_builder.build_base_context(
            normalized1,
            normalized2,
            input_correspondence=decision_context.input_correspondence,
        )
        if decision_context.uses_prepared_surface:
            render_analysis1, render_analysis2 = normalized1, normalized2
            assert render_analysis1 is analysis1 and render_analysis2 is analysis2
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
            render_analysis1, render_analysis2 = align_return_value_extension_surfaces(
                render_analysis1,
                render_analysis2,
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
