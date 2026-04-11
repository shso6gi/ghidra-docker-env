# -*- coding: utf-8 -*-
"""Bounded fallback refinement for unresolved recursive call sites."""

from __future__ import annotations

from typing import Callable, Dict, List, Optional, Sequence, Set, Tuple

from ..model import (
    Condition,
    DeferredCallInfo,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from .condition import ConditionSimplifier
from .effect_summary import substitute_condition, substitute_expression


ExpressionExpansion = Tuple[Expression, List[Condition]]


class BoundedCallRefiner:
    """
    未解決 CALL プレースホルダを、有限回の inlining で保守的に展開する。

    - fuel により無限再帰を防止
    - max_cases により分岐爆発を防止
    - 解けない部分は UNKNOWN のまま保持
    """

    def __init__(
        self,
        analysis_provider: Callable[[str], Optional[FunctionReturnAnalysis]],
        *,
        max_unroll: int = 2,
        max_cases: int = 128,
        debug: bool = False,
    ):
        self.analysis_provider = analysis_provider
        self.max_unroll = max(0, int(max_unroll))
        self.max_cases = max(1, int(max_cases))
        self.debug = debug

    def _debug(self, message: str) -> None:
        if self.debug:
            print(f"[BoundedCallRefiner] {message}")

    def refine_analysis(self, analysis: FunctionReturnAnalysis) -> bool:
        if analysis is None or not analysis.returns or not analysis.deferred_calls or self.max_unroll <= 0:
            return False

        original_signature = self._analysis_signature(analysis.returns)
        refined_returns: List[ReturnInfo] = []

        for ret in analysis.returns:
            refined_returns.extend(self._expand_return_info(ret, analysis, self.max_unroll, set()))
            if len(refined_returns) >= self.max_cases:
                refined_returns = refined_returns[: self.max_cases]
                break

        deduped = self._deduplicate_return_infos(refined_returns)
        if not deduped:
            return False

        analysis.returns = deduped
        analysis.deferred_calls = self._filter_deferred_calls_in_use(analysis)

        changed = original_signature != self._analysis_signature(analysis.returns)
        if changed and "bounded_call_refinement" not in analysis.analysis_notes:
            analysis.analysis_notes.append("bounded_call_refinement")
        return changed

    def _analysis_signature(self, return_infos: Sequence[ReturnInfo]) -> Tuple[Tuple[str, Tuple[str, ...]], ...]:
        signature = []
        for ret in return_infos or []:
            signature.append(
                (
                    ret.value.to_string(),
                    tuple(sorted(cond.to_string() for cond in ret.conditions)),
                )
            )
        return tuple(signature)

    def _expand_return_info(
        self,
        ret: ReturnInfo,
        analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[str],
    ) -> List[ReturnInfo]:
        condition_states = self._expand_conditions(ret.conditions, analysis, fuel, trail)
        value_states = self._expand_expression(ret.value, analysis, fuel, trail)

        results: List[ReturnInfo] = []
        for conds in condition_states:
            for value_expr, extra_conditions in value_states:
                merged_conditions = ConditionSimplifier.simplify_conditions(
                    list(conds) + list(extra_conditions)
                )
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                results.append(
                    ReturnInfo(
                        address=ret.address,
                        value=value_expr,
                        conditions=merged_conditions,
                        branch_index=ret.branch_index,
                    )
                )
                if len(results) >= self.max_cases:
                    return results[: self.max_cases]
        return results

    def _expand_conditions(
        self,
        conditions: Sequence[Condition],
        analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[str],
    ) -> List[List[Condition]]:
        states: List[List[Condition]] = [[]]

        for condition in conditions or []:
            next_states: List[List[Condition]] = []
            expansions = self._expand_expression(condition.expression, analysis, fuel, trail)
            for prefix in states:
                for expr, extra_conditions in expansions:
                    merged = ConditionSimplifier.simplify_conditions(
                        prefix + extra_conditions + [Condition(expr, condition.negated)]
                    )
                    if ConditionSimplifier.is_contradiction(merged):
                        continue
                    next_states.append(merged)
                    if len(next_states) >= self.max_cases:
                        break
                if len(next_states) >= self.max_cases:
                    break
            if not next_states:
                return []
            states = self._deduplicate_condition_sets(next_states)
        return states

    def _expand_expression(
        self,
        expr: Expression,
        analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[str],
    ) -> List[ExpressionExpansion]:
        deferred = self._lookup_deferred_call(expr, analysis)
        if deferred is not None:
            if fuel <= 0 or deferred.placeholder_name in trail:
                return [(expr, [])]
            unfolded = self._expand_deferred_call(deferred, fuel - 1, trail | {deferred.placeholder_name})
            return unfolded or [(expr, [])]

        if expr is None:
            return [(expr, [])]

        if expr.expr_type in {
            ExpressionType.CONSTANT,
            ExpressionType.PARAMETER,
            ExpressionType.VARIABLE,
            ExpressionType.UNKNOWN,
            ExpressionType.LITERAL,
            ExpressionType.PHI,
        }:
            return [(expr, [])]

        if not expr.operands:
            return [(expr, [])]

        states: List[Tuple[List[Expression], List[Condition]]] = [([], [])]
        for operand in expr.operands:
            operand_expansions = self._expand_expression(operand, analysis, fuel, trail)
            next_states: List[Tuple[List[Expression], List[Condition]]] = []
            for built_operands, built_conditions in states:
                for new_operand, extra_conditions in operand_expansions:
                    next_states.append(
                        (
                            built_operands + [new_operand],
                            built_conditions + extra_conditions,
                        )
                    )
                    if len(next_states) >= self.max_cases:
                        break
                if len(next_states) >= self.max_cases:
                    break
            states = next_states
            if not states:
                return [(expr, [])]

        results: List[ExpressionExpansion] = []
        for operands, extra_conditions in states[: self.max_cases]:
            rebuilt = self._clone_expression_with_operands(expr, operands)
            merged_conditions = ConditionSimplifier.simplify_conditions(extra_conditions)
            if ConditionSimplifier.is_contradiction(merged_conditions):
                continue
            results.append((rebuilt, merged_conditions))

        return results or [(expr, [])]

    def _expand_deferred_call(
        self,
        deferred: DeferredCallInfo,
        fuel: int,
        trail: Set[str],
    ) -> List[ExpressionExpansion]:
        callee_analysis = self.analysis_provider(deferred.target_name)
        if callee_analysis is None or not callee_analysis.returns:
            return []

        param_names = [
            name
            for param in callee_analysis.parameters
            for name in [param.get("name")]
            if isinstance(name, str) and name
        ]
        if len(deferred.arguments) < len(param_names):
            self._debug(
                f"Skipped deferred call '{deferred.placeholder_name}': expected "
                f"{len(param_names)} args, got {len(deferred.arguments)}"
            )
            return []

        replacements = dict(zip(param_names, deferred.arguments))
        results: List[ExpressionExpansion] = []

        for ret in callee_analysis.returns:
            substituted_value = substitute_expression(ret.value, replacements)
            substituted_conditions = [
                substitute_condition(cond, replacements)
                for cond in ret.conditions
            ]

            condition_sets = self._expand_conditions(
                substituted_conditions,
                callee_analysis,
                fuel,
                trail,
            )
            value_states = self._expand_expression(
                substituted_value,
                callee_analysis,
                fuel,
                trail,
            )

            for conds in condition_sets or [[]]:
                for value_expr, extra_conditions in value_states:
                    merged_conditions = ConditionSimplifier.simplify_conditions(
                        list(conds) + list(extra_conditions)
                    )
                    if ConditionSimplifier.is_contradiction(merged_conditions):
                        continue
                    results.append((value_expr, merged_conditions))
                    if len(results) >= self.max_cases:
                        return results[: self.max_cases]

        return self._deduplicate_expression_expansions(results)

    def _lookup_deferred_call(
        self,
        expr: Optional[Expression],
        analysis: FunctionReturnAnalysis,
    ) -> Optional[DeferredCallInfo]:
        if expr is None or expr.expr_type != ExpressionType.UNKNOWN:
            return None
        return analysis.deferred_calls.get(expr.name or "")

    def _clone_expression_with_operands(
        self,
        expr: Expression,
        operands: Sequence[Expression],
    ) -> Expression:
        cloned = Expression(
            expr.expr_type,
            value=expr.value,
            operator=expr.operator,
            operands=list(operands),
            size=expr.size,
            name=expr.name,
            data_type=expr.data_type,
            storage_info=expr.storage_info,
            read_order_key=getattr(expr, "read_order_key", None),
        )
        return cloned

    def _deduplicate_condition_sets(
        self,
        condition_sets: Sequence[Sequence[Condition]],
    ) -> List[List[Condition]]:
        seen = set()
        result: List[List[Condition]] = []
        for conditions in condition_sets:
            key = tuple(sorted(cond.to_string() for cond in conditions))
            if key in seen:
                continue
            seen.add(key)
            result.append(list(conditions))
            if len(result) >= self.max_cases:
                break
        return result

    def _deduplicate_expression_expansions(
        self,
        expansions: Sequence[ExpressionExpansion],
    ) -> List[ExpressionExpansion]:
        seen = set()
        result: List[ExpressionExpansion] = []
        for expr, conditions in expansions:
            key = (
                expr.to_string(),
                tuple(sorted(cond.to_string() for cond in conditions)),
            )
            if key in seen:
                continue
            seen.add(key)
            result.append((expr, list(conditions)))
            if len(result) >= self.max_cases:
                break
        return result

    def _deduplicate_return_infos(
        self,
        return_infos: Sequence[ReturnInfo],
    ) -> List[ReturnInfo]:
        seen = set()
        result: List[ReturnInfo] = []
        for ret in return_infos:
            key = (
                ret.address,
                ret.branch_index,
                ret.value.to_string(),
                tuple(sorted(cond.to_string() for cond in ret.conditions)),
            )
            if key in seen:
                continue
            seen.add(key)
            result.append(ret)
            if len(result) >= self.max_cases:
                break
        return result

    def _filter_deferred_calls_in_use(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> Dict[str, DeferredCallInfo]:
        used: Set[str] = set()

        def visit_expression(expr: Optional[Expression]) -> None:
            if expr is None:
                return
            if expr.expr_type == ExpressionType.UNKNOWN and expr.name in analysis.deferred_calls:
                used.add(expr.name)
                return
            if expr.expr_type == ExpressionType.PHI and expr.value:
                for cond, value in expr.value:
                    if cond is not None:
                        visit_expression(cond.expression)
                    visit_expression(value)
                return
            for operand in expr.operands or []:
                visit_expression(operand)

        for ret in analysis.returns:
            visit_expression(ret.value)
            for cond in ret.conditions:
                visit_expression(cond.expression)

        return {
            name: info
            for name, info in analysis.deferred_calls.items()
            if name in used
        }
