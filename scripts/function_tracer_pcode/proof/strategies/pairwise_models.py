# -*- coding: utf-8 -*-
"""Pairwise strategy helper models."""

from typing import Any, Dict, List, Optional

from scripts.function_tracer_pcode.core import Condition, ReturnInfo
from scripts.function_tracer_pcode.core.semantic_freeze import publish_semantic_values
from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.effects.summary import (
    lower_post_state_expression_for_smt_if_needed,
)
from scripts.function_tracer_pcode.proof.formula.returns import (
    coerce_value_to_bitvec_width,
    should_sign_extend_value,
)


class ReturnCase:
    """ReturnInfo から抽出した 1 つの分岐ケース"""

    def __init__(
        self,
        index: int,
        conditions: List[Condition],
        value_expr,
        return_info: ReturnInfo,
        normalized_value_expr=None,
        return_type: Optional[str] = None,
        return_type_obj=None,
        source_indices: Optional[List[int]] = None,
        parameters: Optional[List[Dict]] = None,
        effect_summary=None,
        comparison_surface=None,
        summary_conditions: Optional[List[Condition]] = None,
        program_is_big_endian: Optional[bool] = None,
    ):
        self.index = index
        self.conditions = list(conditions or [])
        self.summary_conditions = list(summary_conditions or self.conditions)
        self.value_expr = value_expr
        self.normalized_value_expr = normalized_value_expr if normalized_value_expr is not None else value_expr
        self.return_info = return_info
        self.return_type = return_type
        self.return_type_obj = return_type_obj
        self.source_indices = source_indices or [index]
        self.parameters = parameters or []
        self.effect_summary = effect_summary
        self.comparison_surface = comparison_surface
        self.program_is_big_endian = program_is_big_endian
        self._conditions_smt_cache: Dict[tuple, List[str]] = {}
        self._value_smt_cache: Dict[tuple, str] = {}
        self._publish_semantic_values()

    def _publish_semantic_values(self) -> None:
        """このケースが抱える意味値を公開する（組み立て・精緻化の完了点）。

        ケースは「この分岐の戻り値と経路条件はこれ」と宣言する carrier で、
        その先は solver と identity しか読まない。公開をこの 1 箇所に置くと、
        値を差し替える経路（`update_conditions` / `replace_value`）を通った
        ものも必ず公開済みになる。
        """

        publish_semantic_values(self)

    def update_conditions(
        self,
        conditions: List[Condition],
        *,
        summary_conditions: Optional[List[Condition]] = None,
    ) -> None:
        self.conditions = list(conditions or [])
        self.summary_conditions = list(summary_conditions or self.conditions)
        self._conditions_smt_cache.clear()
        self._value_smt_cache.clear()
        self._publish_semantic_values()

    def replace_value(self, value_expr, normalized_value_expr=None) -> None:
        """精緻化で戻り値式を差し替える唯一の入口。

        描画済み SMT の cache は値に紐づくので、差し替えたら必ず捨てる。
        呼び手が属性へ直接代入すると、この後始末と公開が抜ける。
        """

        self.value_expr = value_expr
        self.normalized_value_expr = (
            normalized_value_expr if normalized_value_expr is not None else value_expr
        )
        self._value_smt_cache.clear()
        self._publish_semantic_values()

    @staticmethod
    def _coerce_rendered_smt(rendered) -> str:
        if isinstance(rendered, str):
            return rendered
        to_smt = getattr(rendered, "to_smt", None)
        if callable(to_smt):
            return to_smt(float_mode="fp")
        return str(rendered)

    @staticmethod
    def _renderer_cache_key(param_replace_fn) -> tuple:
        if param_replace_fn is None:
            return ("default", None)
        try:
            hash(param_replace_fn)
        except TypeError:
            return ("renderer_repr", repr(param_replace_fn))
        return ("renderer", param_replace_fn)

    def get_conditions_smt(self, param_replace_fn) -> List[str]:
        cache_key = self._renderer_cache_key(param_replace_fn)
        cached = self._conditions_smt_cache.get(cache_key)
        if cached is not None:
            return cached

        rendered_conditions: List[str] = []
        for cond in self.conditions:
            if param_replace_fn is None:
                cond_str = cond.to_smt(float_mode="fp")
            else:
                try:
                    cond_str = param_replace_fn(cond)
                except TypeError:
                    cond_str = param_replace_fn(cond.to_smt(float_mode="fp"))
            rendered_conditions.append(self._coerce_rendered_smt(cond_str))
        self._conditions_smt_cache[cache_key] = rendered_conditions
        return rendered_conditions

    def get_value_smt(
        self,
        param_replace_fn,
        target_bits: Optional[int] = None,
        use_sign_extension: Optional[bool] = None,
    ) -> str:
        if use_sign_extension is None:
            use_sign_extension = self.should_sign_extend_value()
        cache_key = (
            self._renderer_cache_key(param_replace_fn),
            target_bits,
            bool(use_sign_extension),
        )
        result = self._value_smt_cache.get(cache_key)
        if result is not None:
            return result

        rendered_expr = self.value_expr
        if (
            self.effect_summary is not None
            and getattr(self.effect_summary, "effects", None)
        ):
            lowered_expr = lower_post_state_expression_for_smt_if_needed(
                self.value_expr,
                self.conditions,
                self.effect_summary.effects,
                self.parameters,
            )
            if lowered_expr is not None:
                rendered_expr = lowered_expr

        if param_replace_fn is None:
            result = rendered_expr.to_smt(float_mode="fp")
        else:
            try:
                result = param_replace_fn(rendered_expr)
            except TypeError:
                result = param_replace_fn(rendered_expr.to_smt(float_mode="fp"))
            result = self._coerce_rendered_smt(result)
        if target_bits is not None:
            result = coerce_value_to_bitvec_width(
                rendered_expr,
                result,
                target_bits,
                use_sign_extension=bool(use_sign_extension),
            )
        self._value_smt_cache[cache_key] = result
        return result

    def should_sign_extend_value(self) -> bool:
        override = getattr(self.comparison_surface, "use_sign_extension", None)
        if override is not None:
            return bool(override)
        return should_sign_extend_value(
            self.return_type,
            self.value_expr,
            self.conditions,
            return_type_obj=self.return_type_obj,
        )

    def get_condition_summary(self) -> str:
        conditions = self.summary_conditions if self.summary_conditions is not None else self.conditions
        if not conditions:
            return "unconditional"

        cond_strs = []
        for cond in conditions[:3]:
            cond_str = ConditionSimplifier.get_simplified_condition_string(cond)
            if cond_str:
                cond_strs.append(cond_str)

        if not cond_strs:
            return "unconditional"
        summary = " AND ".join(cond_strs)
        if len(self.source_indices) > 1:
            summary = f"{summary} [sources={self.source_indices}]"
        return summary


class QueryResult:
    """1 クエリ分の実行結果"""

    def __init__(
        self,
        is_equivalent: Optional[bool],
        counterexample_raw: Optional[Dict] = None,
        solver_results: Optional[Any] = None,
    ):
        self.is_equivalent = is_equivalent
        self.counterexample_raw = counterexample_raw
        self.solver_results = solver_results
        self.last_query: Optional[str] = None
        self.solver_query_execution_receipt: Optional[Any] = None
        self.structural_equality_receipt: Optional[Any] = None
        self.normalization_rules: List = []
        self.pair_stage: Optional[str] = None
        self.blocking_reason: Optional[str] = None
        self.blocking_detail: Optional[str] = None
        self.evidence_kind: Optional[str] = None
        self.object_target_key = None
        self.proof_obligation_id = None
