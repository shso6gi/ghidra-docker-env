# -*- coding: utf-8 -*-
"""Structural recurrence summaries for simple recursion/loop patterns."""

from __future__ import annotations

from collections import Counter
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from ..model import Condition, Expression, ExpressionType, ReturnInfo
from .condition import ConditionSimplifier, ConditionNormalizer
from .effect_summary import (
    CanonicalLocation,
    _reduce_expression_under_conditions,
    canonicalize_location,
)


def _runtime_expression_signature(expr: Optional[Expression]):
    if expr is None:
        return ("none",)
    return expr.structural_key(
        normalize_commutative=True,
        strip_width_adapters=True,
        collapse_full_masks=True,
        include_memory_read_order=False,
    )


def _runtime_conditions_signature(conditions: Sequence[Condition]):
    return ConditionNormalizer.conditions_signature(conditions)


class StructuralRecurrenceSummarizer:
    """
    Recover conservative closed-form summaries for simple scalar recurrences.

    The current implementation intentionally focuses on a sound, reusable subset:
    single-parameter, unit-step, additive self-recursive functions of the form

      f(n) = base                  when n <= L
      f(n) = f(n - 1) + (a*n + b)  when n > L

    If the pattern cannot be proved from the already recovered return cases and the
    function's direct self-call site, the summarizer declines and the caller falls
    back to the existing path-sensitive analysis.
    """

    _SIGNED_GT_OPS = {"INT_SLESS", "INT_SLESSEQUAL"}

    def __init__(self, tracer, debug: bool = False):
        self.tracer = tracer
        self.debug = debug

    def try_summarize_function(self, function, high_function, analysis) -> Optional[Tuple[List[ReturnInfo], str]]:
        if function is None or high_function is None or analysis is None:
            return None

        if len(getattr(analysis, "parameters", []) or []) == 1:
            summary = self._try_summarize_linear_self_recursion(function, high_function, analysis)
            if summary is not None:
                return summary

        summary = self._try_summarize_branch_accumulator_loop(analysis)
        if summary is not None:
            return summary
        return None

    def _debug(self, message: str) -> None:
        if self.debug:
            print(f"[RecurrenceSummary] {message}")

    def _try_summarize_linear_self_recursion(self, function, high_function, analysis) -> Optional[Tuple[List[ReturnInfo], str]]:
        function_name = function.getName()
        unknown_name = f"call_out_of_scope:{function_name}"
        recursive_returns = [
            ret for ret in (analysis.returns or [])
            if self._expression_contains_unknown_name(ret.value, unknown_name)
        ]
        if len(recursive_returns) != 1:
            self._debug(
                f"Declined '{function_name}': expected exactly one recursive return, found {len(recursive_returns)}"
            )
            return None

        base_returns = [
            ret for ret in (analysis.returns or [])
            if ret not in recursive_returns and self._is_constant_expression(ret.value)
        ]
        if len(base_returns) != 1:
            self._debug(
                f"Declined '{function_name}': expected exactly one constant base return, found {len(base_returns)}"
            )
            return None

        param_info = dict(analysis.parameters[0])
        if not self._parameter_can_be_counter(param_info):
            self._debug(f"Declined '{function_name}': parameter is not a scalar counter candidate")
            return None

        param_expr = self._parameter_expression(param_info)
        param_name = param_expr.name
        if not param_name:
            self._debug(f"Declined '{function_name}': parameter name is unavailable")
            return None
        recursive_ret = recursive_returns[0]
        base_ret = base_returns[0]

        lower_bound = self._infer_lower_bound_from_conditions(recursive_ret.conditions, param_name)
        if lower_bound is None:
            lower_bound = self._infer_lower_bound_from_base_conditions(base_ret.conditions, param_name)
        if lower_bound is None:
            self._debug(f"Declined '{function_name}': could not infer recursion/base split bound")
            return None

        self_call_ops = [
            op for op in self._iter_pcode_ops(high_function)
            if op.getMnemonic() == "CALL"
            and op.getNumInputs() >= 2
            and self.tracer._get_function_name(op.getInput(0)) == function_name
        ]
        if len(self_call_ops) != 1:
            self._debug(
                f"Declined '{function_name}': expected exactly one direct self-call, found {len(self_call_ops)}"
            )
            return None

        call_arg_expr = self.tracer.trace_varnode(self_call_ops[0].getInput(1), use_cache=False)
        step = self._extract_unit_step_from_call_argument(call_arg_expr, param_name)
        if step != -1:
            self._debug(
                f"Declined '{function_name}': recursive call argument is not a unit decrement "
                f"({call_arg_expr.to_string()})"
            )
            return None

        addend_expr = self._extract_addend_expression(recursive_ret.value, unknown_name)
        if addend_expr is None:
            self._debug(
                f"Declined '{function_name}': could not isolate non-recursive addend from "
                f"{recursive_ret.value.to_string()}"
            )
            return None

        affine = self._extract_affine_term(addend_expr, param_name)
        if affine is None:
            self._debug(
                f"Declined '{function_name}': addend is not affine in the counter "
                f"({addend_expr.to_string()})"
            )
            return None
        coeff, bias = affine

        base_value = self._constant_value(base_ret.value)
        if base_value is None:
            self._debug(f"Declined '{function_name}': base value is not a concrete constant")
            return None

        recursive_value = self._build_closed_form(
            param_expr=param_expr,
            lower_bound=lower_bound,
            coeff=coeff,
            bias=bias,
            base_value=base_value,
        )
        if recursive_value is None:
            self._debug(f"Declined '{function_name}': failed to construct closed-form summary")
            return None

        recursive_conditions = self._build_recursive_conditions(param_expr, lower_bound)
        base_conditions = self._build_base_conditions(param_expr, lower_bound)
        if recursive_conditions is None or base_conditions is None:
            self._debug(f"Declined '{function_name}': failed to build guard conditions for summary")
            return None

        summarized_returns = [
            ReturnInfo(
                address=base_ret.address,
                value=Expression.constant(base_value, recursive_value.size or param_expr.size or 4),
                conditions=base_conditions,
                branch_index=base_ret.branch_index,
                pcode_identity=base_ret.pcode_identity,
                pcode_order=base_ret.pcode_order,
                pcode_time=base_ret.pcode_time,
            ),
            ReturnInfo(
                address=recursive_ret.address,
                value=recursive_value,
                conditions=recursive_conditions,
                branch_index=recursive_ret.branch_index,
                pcode_identity=recursive_ret.pcode_identity,
                pcode_order=recursive_ret.pcode_order,
                pcode_time=recursive_ret.pcode_time,
            ),
        ]

        self._debug(
            f"Recovered linear self-recursive summary for '{function_name}' "
            f"(lower_bound={lower_bound}, coeff={coeff}, bias={bias}, base={base_value})"
        )
        return summarized_returns, "linear_self_recursion_summary"

    def _try_summarize_branch_accumulator_loop(
        self,
        analysis,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        if analysis is None or not analysis.returns or len(analysis.parameters or []) < 3:
            self._debug("Declined branch-accumulator summary: insufficient returns/parameters")
            return None
        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is None:
            self._debug("Declined branch-accumulator summary: no effect summary")
            return None

        loop_params = self._infer_loop_parameter_pair(analysis)
        if loop_params is None:
            self._debug("Declined branch-accumulator summary: could not infer loop parameter pair")
            return None
        start_name, limit_name = loop_params

        pointer_param = self._infer_pointer_parameter_name(analysis)
        if not pointer_param:
            self._debug("Declined branch-accumulator summary: could not infer pointer parameter")
            return None

        working_returns = list(analysis.returns)
        null_case = self._find_pointer_null_case(working_returns, pointer_param)
        require_pointer_nonnull = null_case is not None
        base_case = self._find_no_loop_base_case(
            working_returns,
            pointer_param,
            start_name,
            limit_name,
            require_pointer_nonnull=require_pointer_nonnull,
        )
        if base_case is None:
            self._debug(
                "Declined branch-accumulator summary: could not identify no-loop base case "
                f"(pointer={pointer_param}, start={start_name}, limit={limit_name})"
            )
            return None

        step_cases = self._find_one_step_cases(
            working_returns,
            pointer_param,
            start_name,
            limit_name,
            require_pointer_nonnull=require_pointer_nonnull,
        )
        if step_cases is None:
            synthesized = self._synthesize_one_step_cases_from_effects(
                analysis,
                base_case,
                pointer_param,
                start_name,
                limit_name,
                require_pointer_nonnull=require_pointer_nonnull,
            )
            if not synthesized:
                self._debug("Declined branch-accumulator summary: could not synthesize one-step cases from effects")
                return None
            working_returns.extend(synthesized)
            step_cases = self._find_one_step_cases(
                working_returns,
                pointer_param,
                start_name,
                limit_name,
                require_pointer_nonnull=require_pointer_nonnull,
            )
            if step_cases is None:
                self._debug("Declined branch-accumulator summary: synthesized one-step cases still did not match")
                return None

        even_case, odd_case = step_cases
        base_expr = base_case.value
        even_delta = self._extract_additive_delta(even_case.value, base_expr, analysis.parameters or [])
        odd_delta = self._extract_additive_delta(odd_case.value, base_expr, analysis.parameters or [])
        if even_delta is None or odd_delta is None:
            self._debug("Declined branch-accumulator summary: could not isolate additive deltas")
            return None

        even_affine = self._extract_affine_term(even_delta, start_name)
        odd_affine = self._extract_affine_term(odd_delta, start_name)
        if even_affine is None or odd_affine is None:
            self._debug("Declined branch-accumulator summary: one-step deltas are not affine in the loop counter")
            return None

        loop_even_value = self._build_parity_split_loop_value(
            base_expr,
            start_name,
            limit_name,
            even_affine,
            odd_affine,
            start_is_even=True,
        )
        loop_odd_value = self._build_parity_split_loop_value(
            base_expr,
            start_name,
            limit_name,
            even_affine,
            odd_affine,
            start_is_even=False,
        )
        if loop_even_value is None or loop_odd_value is None:
            self._debug("Declined branch-accumulator summary: failed to build closed-form loop values")
            return None

        loop_conditions_common = [
            self._pointer_nonnull_condition(pointer_param, analysis),
            Condition(
                Expression.binary_op(
                    "INT_SLESS",
                    self._param_expr(analysis, start_name),
                    self._param_expr(analysis, limit_name),
                ),
                False,
            ),
        ]
        even_start_cond = Condition(
            Expression.binary_op(
                "INT_EQUAL",
                Expression.binary_op(
                    "INT_AND",
                    self._param_expr(analysis, start_name),
                    Expression.constant(1, self._param_expr(analysis, start_name).size or 4),
                ),
                Expression.constant(0, self._param_expr(analysis, start_name).size or 4),
            ),
            False,
        )
        odd_start_cond = even_start_cond.negate()

        summarized: List[ReturnInfo] = []
        if null_case is not None:
            summarized.append(null_case)
        summarized.append(base_case)
        summarized.append(
            ReturnInfo(
                address=base_case.address,
                value=loop_even_value,
                conditions=ConditionSimplifier.simplify_conditions(loop_conditions_common + [even_start_cond]),
                branch_index=10_100,
                pcode_identity=base_case.pcode_identity,
                pcode_order=base_case.pcode_order,
                pcode_time=base_case.pcode_time,
            )
        )
        summarized.append(
            ReturnInfo(
                address=base_case.address,
                value=loop_odd_value,
                conditions=ConditionSimplifier.simplify_conditions(loop_conditions_common + [odd_start_cond]),
                branch_index=10_101,
                pcode_identity=base_case.pcode_identity,
                pcode_order=base_case.pcode_order,
                pcode_time=base_case.pcode_time,
            )
        )
        self._debug(
            "Recovered counted loop branch-accumulator summary "
            f"(start={start_name}, limit={limit_name}, even={even_affine}, odd={odd_affine})"
        )
        return summarized, "counted_loop_branch_accumulator_summary"

    def _infer_pointer_parameter_name(self, analysis) -> Optional[str]:
        for param in analysis.parameters or []:
            name = str(param.get("name") or "")
            data_type = str(param.get("data_type") or "")
            if name and "*" in data_type:
                return name
        return None

    def _infer_loop_parameter_pair(self, analysis) -> Optional[Tuple[str, str]]:
        candidates: Counter[Tuple[str, str]] = Counter()
        all_conditions: List[Condition] = []
        for ret in analysis.returns or []:
            all_conditions.extend(ret.conditions or [])
        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is not None:
            for effect in effect_summary.effects or []:
                all_conditions.extend(effect.conditions or [])

        for cond in all_conditions:
            pair = self._match_less_parameter_pair(cond)
            if pair is not None:
                candidates[pair] += 1
        if not candidates:
            return None
        return candidates.most_common(1)[0][0]

    def _match_less_parameter_pair(self, condition: Condition) -> Optional[Tuple[str, str]]:
        relation = self._parameter_comparison_relation(condition)
        if relation is None:
            return None
        left_name, relation_name, right_name = relation
        if relation_name == "<":
            return left_name, right_name
        if relation_name == ">":
            return right_name, left_name
        return None

    def _parameter_name_from_expr(self, expr: Optional[Expression]) -> Optional[str]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.PARAMETER and expr.name:
            return expr.name
        normalized = self._normalize_counter_view(expr, getattr(expr, "name", None) or "")
        if normalized is not None and normalized[0].name:
            return normalized[0].name
        return None

    def _param_expr(self, analysis, name: str) -> Expression:
        for param in analysis.parameters or []:
            if param.get("name") != name:
                continue
            return Expression.parameter(
                name,
                index=int(param.get("index", 0)),
                data_type=param.get("data_type"),
                size=int(param.get("size", 4) or 4),
            )
        return Expression.parameter(name, size=4)

    def _find_pointer_null_case(
        self,
        returns: Sequence[ReturnInfo],
        pointer_name: str,
    ) -> Optional[ReturnInfo]:
        for ret in returns:
            if not self._return_is_constant(ret):
                continue
            if any(self._condition_is_pointer_null(cond, pointer_name) for cond in ret.conditions or []):
                return ret
        return None

    def _find_no_loop_base_case(
        self,
        returns: Sequence[ReturnInfo],
        pointer_name: str,
        start_name: str,
        limit_name: str,
        *,
        require_pointer_nonnull: bool,
    ) -> Optional[ReturnInfo]:
        for ret in returns:
            if self._return_is_constant(ret):
                continue
            has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in ret.conditions or [])
            has_not_less = any(self._condition_is_not_less(cond, start_name, limit_name) for cond in ret.conditions or [])
            if has_not_less and (has_nonnull or not require_pointer_nonnull):
                return ret
        return None

    def _find_one_step_cases(
        self,
        returns: Sequence[ReturnInfo],
        pointer_name: str,
        start_name: str,
        limit_name: str,
        *,
        require_pointer_nonnull: bool,
    ) -> Optional[Tuple[ReturnInfo, ReturnInfo]]:
        even_case = None
        odd_case = None
        for ret in returns:
            conditions = ret.conditions or []
            has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in conditions)
            has_loop = any(self._condition_is_less(cond, start_name, limit_name) for cond in conditions)
            has_one_step = any(self._condition_is_step_equality(cond, start_name, limit_name) for cond in conditions)
            if not (has_loop and has_one_step and (has_nonnull or not require_pointer_nonnull)):
                continue
            parity = self._extract_counter_parity(conditions, start_name)
            if parity is True:
                even_case = ret
            elif parity is False:
                odd_case = ret
        if even_case is None or odd_case is None:
            return None
        return even_case, odd_case

    def _synthesize_one_step_cases_from_effects(
        self,
        analysis,
        base_case: ReturnInfo,
        pointer_name: str,
        start_name: str,
        limit_name: str,
        *,
        require_pointer_nonnull: bool,
    ) -> List[ReturnInfo]:
        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is None:
            return []
        coeffs = self._extract_linear_location_coefficients(base_case.value, analysis.parameters or [])
        if not coeffs:
            return []

        grouped: Dict[Tuple[object, ...], List] = {}
        for effect in effect_summary.effects or []:
            conds = ConditionSimplifier.simplify_conditions(effect.conditions or [])
            key = _runtime_conditions_signature(conds)
            grouped.setdefault(key, []).append((conds, effect))

        synthesized: List[ReturnInfo] = []
        for grouped_effects in grouped.values():
            conds = grouped_effects[0][0]
            has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in conds)
            if require_pointer_nonnull and not has_nonnull:
                self._debug(
                    "Skipping effect-derived one-step candidate: missing local pointer-nonnull guard "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue
            if not any(self._condition_is_less(cond, start_name, limit_name) for cond in conds):
                self._debug(
                    "Skipping effect-derived one-step candidate: missing loop-progress guard "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue
            parity = self._extract_counter_parity(conds, start_name)
            if parity is None:
                self._debug(
                    "Skipping effect-derived one-step candidate: could not determine counter parity "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue
            step_eq = Condition(
                Expression.binary_op(
                    "INT_EQUAL",
                    self._param_expr(analysis, limit_name),
                    Expression.binary_op(
                        "INT_ADD",
                        self._param_expr(analysis, start_name),
                        Expression.constant(1, self._param_expr(analysis, start_name).size or 4),
                    ),
                ),
                False,
            )
            step_context = ConditionSimplifier.simplify_conditions(list(conds) + [step_eq])
            if ConditionSimplifier.is_contradiction(step_context):
                self._debug(
                    "Skipping effect-derived one-step candidate: one-step context is contradictory "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue

            delta_terms: List[Expression] = []
            for _conds, effect in grouped_effects:
                coeff = coeffs.get(effect.location)
                if coeff in (None, 0):
                    continue
                delta_expr = self._extract_store_delta_expr(
                    effect,
                    analysis.parameters or [],
                    step_context,
                )
                if delta_expr is None:
                    self._debug(
                        "Aborting effect-derived one-step synthesis: could not isolate store delta "
                        f"for location={effect.location} value={effect.value.to_string()} "
                        f"conditions={[cond.to_string() for cond in step_context]}"
                    )
                    return []
                reduced_delta = _reduce_expression_under_conditions(delta_expr, step_context)
                scaled = self._scale_expression(reduced_delta, coeff)
                if scaled is not None:
                    delta_terms.append(scaled)
            if not delta_terms:
                self._debug(
                    "Skipping effect-derived one-step candidate: no additive delta terms matched "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue

            delta_sum = self._sum_expression_terms(delta_terms)
            if delta_sum is None:
                continue
            value = Expression.binary_op("INT_ADD", base_case.value, delta_sum)
            value.size = base_case.value.size
            synthesized.append(
                ReturnInfo(
                    address=base_case.address,
                    value=value,
                    conditions=step_context,
                    branch_index=9_000 if parity else 9_001,
                    pcode_identity=base_case.pcode_identity,
                    pcode_order=base_case.pcode_order,
                    pcode_time=base_case.pcode_time,
                )
            )
        return synthesized

    def _extract_linear_location_coefficients(
        self,
        expr: Expression,
        parameters: Sequence[dict],
    ) -> Dict[CanonicalLocation, int]:
        coeffs: Dict[CanonicalLocation, int] = {}
        for sign, term in self._flatten_add_terms(expr):
            if term.expr_type == ExpressionType.CONSTANT:
                continue
            if term.expr_type != ExpressionType.MEMORY or not term.operands:
                return {}
            location = canonicalize_location(term.operands[0], parameters, size=term.size)
            if location is None:
                return {}
            coeffs[location] = coeffs.get(location, 0) + sign
        return {loc: coeff for loc, coeff in coeffs.items() if coeff != 0}

    def _extract_store_delta_expr(
        self,
        effect,
        parameters: Sequence[dict],
        conditions: Optional[Sequence[Condition]] = None,
    ) -> Optional[Expression]:
        active_conditions = list(conditions or [])
        reduced_value = _reduce_expression_under_conditions(effect.value, active_conditions)
        current_read = Expression.memory(
            self._address_expr_for_location(effect.location, parameters),
            size=effect.location.size,
        )
        reduced_current_read = _reduce_expression_under_conditions(current_read, active_conditions)
        delta = self._extract_additive_delta(reduced_value, reduced_current_read, parameters)
        if delta is not None:
            return delta
        if reduced_value.equals(reduced_current_read):
            return Expression.constant(0, size=effect.location.size)
        return None

    def _address_expr_for_location(
        self,
        location: CanonicalLocation,
        parameters: Sequence[dict],
    ) -> Expression:
        base_param = None
        for param in parameters:
            if param.get("name") == location.base_param:
                base_param = param
                break
        base_expr = Expression.parameter(
            location.base_param,
            index=int((base_param or {}).get("index", 0)),
            data_type=(base_param or {}).get("data_type"),
            size=int((base_param or {}).get("size", 8) or 8),
        )
        if location.offset == 0:
            return base_expr
        return Expression.binary_op(
            "INT_ADD",
            base_expr,
            Expression.constant(location.offset, size=base_expr.size or 8),
        )

    def _extract_additive_delta(
        self,
        expr: Expression,
        base_expr: Expression,
        parameters: Sequence[dict],
    ) -> Optional[Expression]:
        expr_terms = self._flatten_add_terms(expr)
        base_terms = self._flatten_add_terms(base_expr)
        remaining = list(expr_terms)
        for sign, term in base_terms:
            matched = False
            for index, (cand_sign, cand_term) in enumerate(remaining):
                if cand_sign != sign:
                    continue
                if not self._terms_equivalent(cand_term, term, parameters):
                    continue
                del remaining[index]
                matched = True
                break
            if not matched:
                return None
        return self._sum_expression_terms(
            [self._scale_expression(term, sign) for sign, term in remaining if self._scale_expression(term, sign) is not None]
        )

    def _terms_equivalent(
        self,
        left: Expression,
        right: Expression,
        parameters: Sequence[dict],
    ) -> bool:
        if left.equals(right):
            return True
        if (
            left.expr_type == ExpressionType.MEMORY
            and right.expr_type == ExpressionType.MEMORY
            and left.operands
            and right.operands
        ):
            left_loc = canonicalize_location(left.operands[0], parameters, size=left.size)
            right_loc = canonicalize_location(right.operands[0], parameters, size=right.size)
            if left_loc is not None and right_loc is not None:
                return left_loc == right_loc
        return _runtime_expression_signature(left) == _runtime_expression_signature(right)

    def _flatten_add_terms(
        self,
        expr: Expression,
        sign: int = 1,
    ) -> List[Tuple[int, Expression]]:
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD" and len(expr.operands) == 2:
            return self._flatten_add_terms(expr.operands[0], sign) + self._flatten_add_terms(expr.operands[1], sign)
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_SUB" and len(expr.operands) == 2:
            return self._flatten_add_terms(expr.operands[0], sign) + self._flatten_add_terms(expr.operands[1], -sign)
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_2COMP" and expr.operands:
            return self._flatten_add_terms(expr.operands[0], -sign)
        return [(sign, expr)]

    def _scale_expression(self, expr: Expression, factor: int) -> Optional[Expression]:
        if factor == 0:
            return None
        if factor == 1:
            return expr
        if factor == -1:
            negated = Expression.unary_op("INT_2COMP", expr)
            negated.size = expr.size
            return negated
        return Expression.binary_op(
            "INT_MULT",
            Expression.constant(factor, size=expr.size or 4),
            expr,
        )

    def _sum_expression_terms(
        self,
        terms: Sequence[Optional[Expression]],
    ) -> Optional[Expression]:
        normalized = [term for term in terms if term is not None]
        if not normalized:
            return Expression.constant(0, 4)
        total = normalized[0]
        for term in normalized[1:]:
            total = Expression.binary_op("INT_ADD", total, term)
            total.size = max(total.size, term.size)
        return total

    def _build_parity_split_loop_value(
        self,
        base_expr: Expression,
        start_name: str,
        limit_name: str,
        even_affine: Tuple[int, int],
        odd_affine: Tuple[int, int],
        start_is_even: bool,
    ) -> Optional[Expression]:
        start_expr = self._param_expr_placeholder(start_name, base_expr.size or 4)
        limit_expr = self._param_expr_placeholder(limit_name, base_expr.size or 4)
        size = start_expr.size or 4
        n_expr = Expression.binary_op("INT_SUB", limit_expr, start_expr)
        n_expr.size = size
        one = Expression.constant(1, size)
        two = Expression.constant(2, size)

        if start_is_even:
            n_even = Expression.binary_op("INT_SDIV", Expression.binary_op("INT_ADD", n_expr, one), two)
            n_odd = Expression.binary_op("INT_SDIV", n_expr, two)
            first_even = start_expr
            first_odd = Expression.binary_op("INT_ADD", start_expr, one)
        else:
            n_even = Expression.binary_op("INT_SDIV", n_expr, two)
            n_odd = Expression.binary_op("INT_SDIV", Expression.binary_op("INT_ADD", n_expr, one), two)
            first_even = Expression.binary_op("INT_ADD", start_expr, one)
            first_odd = start_expr
        for item in (n_even, n_odd, first_even, first_odd):
            item.size = size

        sum_even = self._build_arithmetic_progression_sum(first_even, n_even, size)
        sum_odd = self._build_arithmetic_progression_sum(first_odd, n_odd, size)
        contrib_terms: List[Expression] = []
        even_sum_term = self._scale_expression(sum_even, even_affine[0])
        odd_sum_term = self._scale_expression(sum_odd, odd_affine[0])
        if even_sum_term is not None:
            contrib_terms.append(even_sum_term)
        if odd_sum_term is not None:
            contrib_terms.append(odd_sum_term)
        even_count_term = self._scale_expression(n_even, even_affine[1])
        odd_count_term = self._scale_expression(n_odd, odd_affine[1])
        if even_count_term is not None:
            contrib_terms.append(even_count_term)
        if odd_count_term is not None:
            contrib_terms.append(odd_count_term)
        contrib = self._sum_expression_terms(contrib_terms)
        if contrib is None:
            return None
        total = Expression.binary_op("INT_ADD", base_expr, contrib)
        total.size = base_expr.size
        return total

    def _param_expr_placeholder(self, name: str, size: int) -> Expression:
        return Expression.parameter(name, size=size)

    def _build_arithmetic_progression_sum(
        self,
        first_term: Expression,
        count: Expression,
        size: int,
    ) -> Expression:
        one = Expression.constant(1, size)
        count_minus_one = Expression.binary_op("INT_SUB", count, one)
        count_minus_one.size = size
        tail = Expression.binary_op("INT_ADD", first_term, count_minus_one)
        tail.size = size
        pair_sum = Expression.binary_op("INT_ADD", first_term, tail)
        pair_sum.size = size
        product = Expression.binary_op("INT_MULT", count, pair_sum)
        product.size = size
        half = Expression.binary_op("INT_SDIV", product, Expression.constant(2, size))
        half.size = size
        return half

    def _condition_is_pointer_null(self, condition: Condition, pointer_name: str) -> bool:
        return self._match_pointer_equality(condition, pointer_name, expect_zero=True)

    def _condition_is_pointer_nonnull(self, condition: Condition, pointer_name: str) -> bool:
        return self._match_pointer_equality(condition, pointer_name, expect_zero=False)

    def _pointer_nonnull_condition(self, pointer_name: str, analysis) -> Condition:
        ptr_expr = self._param_expr(analysis, pointer_name)
        return Condition(
            Expression.binary_op(
                "INT_NOTEQUAL",
                ptr_expr,
                Expression.constant(0, size=ptr_expr.size or 8),
            ),
            False,
        )

    def _match_pointer_equality(self, condition: Condition, pointer_name: str, expect_zero: bool) -> bool:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return False
        if expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
            return False
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        left_const = self._constant_value(expr.operands[0])
        right_const = self._constant_value(expr.operands[1])
        matches = (
            (left_name == pointer_name and right_const == 0)
            or (right_name == pointer_name and left_const == 0)
        )
        if not matches:
            return False
        is_equal = expr.operator == "INT_EQUAL"
        if condition.negated:
            is_equal = not is_equal
        return is_equal if expect_zero else not is_equal

    def _condition_is_less(self, condition: Condition, start_name: str, limit_name: str) -> bool:
        relation = self._parameter_comparison_relation(condition)
        if relation is None:
            return False
        left_name, relation_name, right_name = relation
        return (
            (left_name == start_name and right_name == limit_name and relation_name == "<")
            or (left_name == limit_name and right_name == start_name and relation_name == ">")
        )

    def _condition_is_not_less(self, condition: Condition, start_name: str, limit_name: str) -> bool:
        relation = self._parameter_comparison_relation(condition)
        if relation is None:
            return False
        left_name, relation_name, right_name = relation
        return (
            (left_name == start_name and right_name == limit_name and relation_name == ">=")
            or (left_name == limit_name and right_name == start_name and relation_name == "<=")
        )

    def _condition_is_step_equality(self, condition: Condition, start_name: str, limit_name: str) -> bool:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_EQUAL" or len(expr.operands) != 2:
            return False
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        if left_name == limit_name and self._expr_is_add_one_of_param(expr.operands[1], start_name):
            return not condition.negated
        if right_name == limit_name and self._expr_is_add_one_of_param(expr.operands[0], start_name):
            return not condition.negated
        return False

    def _expr_is_add_one_of_param(self, expr: Expression, param_name: str) -> bool:
        if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_ADD" or len(expr.operands) != 2:
            return False
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        left_const = self._constant_value(expr.operands[0])
        right_const = self._constant_value(expr.operands[1])
        return (
            (left_name == param_name and right_const == 1)
            or (right_name == param_name and left_const == 1)
        )

    def _extract_counter_parity(
        self,
        conditions: Sequence[Condition],
        counter_name: str,
    ) -> Optional[bool]:
        for condition in conditions or []:
            expr = getattr(condition, "expression", None)
            if (
                expr is None
                or expr.expr_type != ExpressionType.BINARY_OP
                or expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}
                or len(expr.operands) != 2
            ):
                continue
            bitand = None
            parity_const = None
            if self._constant_value(expr.operands[0]) in {0, 1}:
                bitand = expr.operands[1]
                parity_const = self._constant_value(expr.operands[0])
            elif self._constant_value(expr.operands[1]) in {0, 1}:
                bitand = expr.operands[0]
                parity_const = self._constant_value(expr.operands[1])
            if bitand is None or parity_const is None:
                continue
            if bitand.expr_type != ExpressionType.BINARY_OP or bitand.operator != "INT_AND" or len(bitand.operands) != 2:
                continue
            if self._constant_value(bitand.operands[0]) == 1:
                counter_expr = bitand.operands[1]
            elif self._constant_value(bitand.operands[1]) == 1:
                counter_expr = bitand.operands[0]
            else:
                continue
            if self._parameter_name_from_expr(counter_expr) != counter_name:
                continue
            is_equal = expr.operator == "INT_EQUAL"
            if condition.negated:
                is_equal = not is_equal
            is_even = is_equal if parity_const == 0 else not is_equal
            return is_even
        return None

    def _return_is_constant(self, ret: ReturnInfo) -> bool:
        return ret.value is not None and ret.value.expr_type == ExpressionType.CONSTANT

    def _iter_pcode_ops(self, high_function) -> Iterable:
        for basic_block in high_function.getBasicBlocks():
            pcode_iter = basic_block.getIterator()
            while pcode_iter.hasNext():
                yield pcode_iter.next()

    def _parameter_can_be_counter(self, param_info: dict) -> bool:
        data_type = str(param_info.get("data_type") or "").lower()
        size = int(param_info.get("size") or 0)
        if size not in {1, 2, 4, 8}:
            return False
        if not data_type:
            return True
        return any(token in data_type for token in ("int", "long", "short", "char"))

    def _parameter_expression(self, param_info: dict) -> Expression:
        size = int(param_info.get("size") or 4)
        return Expression.parameter(
            param_info.get("name", "param_1"),
            index=int(param_info.get("index", 0)),
            data_type=param_info.get("data_type"),
            size=size,
            storage_info=param_info.get("storage_info"),
        )

    def _expression_contains_unknown_name(self, expr: Optional[Expression], unknown_name: str) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.UNKNOWN:
            expr_name = expr.name or ""
            return expr_name == unknown_name or expr_name.startswith(f"{unknown_name}#")
        if expr.expr_type == ExpressionType.PHI and expr.value:
            return any(
                (cond is not None and self._expression_contains_unknown_name(cond.expression, unknown_name))
                or self._expression_contains_unknown_name(value, unknown_name)
                for cond, value in expr.value
            )
        return any(self._expression_contains_unknown_name(operand, unknown_name) for operand in expr.operands or [])

    def _is_constant_expression(self, expr: Optional[Expression]) -> bool:
        return expr is not None and expr.expr_type == ExpressionType.CONSTANT

    def _constant_value(self, expr: Optional[Expression]) -> Optional[int]:
        if not self._is_constant_expression(expr):
            return None
        assert expr is not None
        return int(expr.value)

    def _raw_constant_value(self, expr: Optional[Expression]) -> Optional[int]:
        if not self._is_constant_expression(expr):
            return None
        assert expr is not None
        return int(expr.value)

    def _signed_constant_value(
        self,
        expr: Optional[Expression],
        bit_width_hint: Optional[int] = None,
    ) -> Optional[int]:
        raw_value = self._raw_constant_value(expr)
        if raw_value is None:
            return None
        assert expr is not None
        bit_width = int(bit_width_hint or ((expr.size or 0) * 8))
        if bit_width <= 0:
            return raw_value
        modulus = 1 << bit_width
        signed = raw_value % modulus
        if signed >= (1 << (bit_width - 1)):
            signed -= modulus
        return signed

    def _extract_addend_expression(self, expr: Expression, unknown_name: str) -> Optional[Expression]:
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        if expr.operator not in {"INT_ADD", "INT_SUB"}:
            return None

        left, right = expr.operands
        if self._expression_contains_unknown_name(left, unknown_name) and not self._expression_contains_unknown_name(right, unknown_name):
            if expr.operator == "INT_ADD":
                return right
            if expr.operator == "INT_SUB":
                return Expression.unary_op("INT_2COMP", right)
        if self._expression_contains_unknown_name(right, unknown_name) and not self._expression_contains_unknown_name(left, unknown_name):
            if expr.operator == "INT_ADD":
                return left
        return None

    def _extract_unit_step_from_call_argument(self, expr: Expression, param_name: str) -> Optional[int]:
        bit_width_hint = self._infer_counter_bit_width(expr, param_name)
        affine = self._extract_affine_term(expr, param_name, bit_width_hint=bit_width_hint)
        if affine is None:
            return None
        coeff, bias = affine
        if coeff != 1:
            return None
        if bias in {-1, 1}:
            return bias
        return None

    def _extract_affine_term(
        self,
        expr: Expression,
        param_name: str,
        bit_width_hint: Optional[int] = None,
    ) -> Optional[Tuple[int, int]]:
        normalized_counter = self._normalize_counter_view(expr, param_name)
        if normalized_counter is not None:
            return 1, 0
        if expr.expr_type == ExpressionType.CONSTANT:
            signed_value = self._signed_constant_value(expr, bit_width_hint=bit_width_hint)
            if signed_value is None:
                return None
            return 0, signed_value
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"} and len(expr.operands) == 1:
            operand = self._extract_affine_term(
                expr.operands[0],
                param_name,
                bit_width_hint=bit_width_hint,
            )
            if operand is None:
                return None
            coeff, bias = operand
            return -coeff, -bias
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None

        node_bit_width = bit_width_hint or self._infer_counter_bit_width(expr, param_name)
        left = self._extract_affine_term(expr.operands[0], param_name, bit_width_hint=node_bit_width)
        right = self._extract_affine_term(expr.operands[1], param_name, bit_width_hint=node_bit_width)

        if expr.operator == "INT_ADD" and left is not None and right is not None:
            return left[0] + right[0], left[1] + right[1]
        if expr.operator == "INT_SUB" and left is not None and right is not None:
            return left[0] - right[0], left[1] - right[1]
        if expr.operator == "INT_MULT":
            left_const = self._signed_constant_value(expr.operands[0], bit_width_hint=node_bit_width)
            right_const = self._signed_constant_value(expr.operands[1], bit_width_hint=node_bit_width)
            if left_const is not None and right is not None:
                return left_const * right[0], left_const * right[1]
            if right_const is not None and left is not None:
                return right_const * left[0], right_const * left[1]
        return None

    def _normalize_counter_view(
        self,
        expr: Optional[Expression],
        param_name: str,
    ) -> Optional[Tuple[Expression, Optional[int]]]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.PARAMETER and expr.name == param_name:
            return expr, (expr.size * 8) if expr.size else None
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_ZEXT", "INT_SEXT"} and len(expr.operands) == 1:
            return self._normalize_counter_view(expr.operands[0], param_name)
        if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_AND" or len(expr.operands) != 2:
            return None

        left_counter = self._normalize_counter_view(expr.operands[0], param_name)
        right_counter = self._normalize_counter_view(expr.operands[1], param_name)
        left_const = self._raw_constant_value(expr.operands[0])
        right_const = self._raw_constant_value(expr.operands[1])

        if left_counter is not None and right_const is not None:
            mask_bits = self._bit_width_from_low_bit_mask(right_const)
            if mask_bits is not None:
                return left_counter[0], mask_bits
        if right_counter is not None and left_const is not None:
            mask_bits = self._bit_width_from_low_bit_mask(left_const)
            if mask_bits is not None:
                return right_counter[0], mask_bits
        return None

    def _infer_counter_bit_width(self, expr: Optional[Expression], param_name: str) -> Optional[int]:
        normalized = self._normalize_counter_view(expr, param_name)
        if normalized is not None:
            return normalized[1]
        if expr is None:
            return None
        for operand in expr.operands or []:
            operand_bit_width = self._infer_counter_bit_width(operand, param_name)
            if operand_bit_width is not None:
                return operand_bit_width
        return None

    def _bit_width_from_low_bit_mask(self, value: int) -> Optional[int]:
        if value <= 0:
            return None
        if (value & (value + 1)) != 0:
            return None
        bit_width = value.bit_length()
        if bit_width < 8 or bit_width % 8 != 0:
            return None
        return bit_width

    def _infer_lower_bound_from_conditions(self, conditions: Sequence[Condition], param_name: str) -> Optional[int]:
        lower_bounds: List[int] = []
        for condition in conditions or []:
            relation = self._condition_relation(condition, param_name)
            if relation is None:
                continue
            relation_name, constant = relation
            if relation_name == ">":
                lower_bounds.append(constant)
            elif relation_name == ">=":
                lower_bounds.append(constant - 1)
        if not lower_bounds:
            return None
        return max(lower_bounds)

    def _infer_lower_bound_from_base_conditions(self, conditions: Sequence[Condition], param_name: str) -> Optional[int]:
        upper_bounds: List[int] = []
        for condition in conditions or []:
            relation = self._condition_relation(condition, param_name)
            if relation is None:
                continue
            relation_name, constant = relation
            if relation_name == "<=":
                upper_bounds.append(constant)
            elif relation_name == "<":
                upper_bounds.append(constant - 1)
        if not upper_bounds:
            return None
        return min(upper_bounds)

    def _condition_relation(self, condition: Condition, param_name: str) -> Optional[Tuple[str, int]]:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        left, right = expr.operands
        right_const = self._constant_value(right)
        left_const = self._constant_value(left)

        op = expr.operator
        relation: Optional[str] = None

        if self._is_condition_counter_view(left, param_name) and right_const is not None:
            relation = self._comparison_to_relation(op, swapped=False)
            constant = right_const
        elif self._is_condition_counter_view(right, param_name) and left_const is not None:
            relation = self._comparison_to_relation(op, swapped=True)
            constant = left_const
        else:
            return None

        if relation is None:
            return None
        if condition.negated:
            relation = self._negate_relation(relation)
            if relation is None:
                return None
        return relation, constant

    def _parameter_comparison_relation(self, condition: Condition) -> Optional[Tuple[str, str, str]]:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        relation = self._comparison_to_relation(expr.operator, swapped=False)
        if relation is None:
            return None
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        if not left_name or not right_name or left_name == right_name:
            return None
        if condition.negated:
            relation = self._negate_relation(relation)
            if relation is None:
                return None
        return left_name, relation, right_name

    def _is_condition_counter_view(self, expr: Optional[Expression], param_name: str) -> bool:
        if expr is None:
            return False
        if self._normalize_counter_view(expr, param_name) is not None:
            return True
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "PIECE" and len(expr.operands) == 2:
            return self._normalize_counter_view(expr.operands[1], param_name) is not None
        if expr.expr_type != ExpressionType.BINARY_OP or expr.operator not in {"INT_OR", "INT_ADD"} or len(expr.operands) != 2:
            return False
        left, right = expr.operands
        return self._matches_shifted_high_reconstruction(left, right, param_name) or self._matches_shifted_high_reconstruction(right, left, param_name)

    def _matches_shifted_high_reconstruction(
        self,
        high_expr: Optional[Expression],
        low_expr: Optional[Expression],
        param_name: str,
    ) -> bool:
        low_counter = self._normalize_counter_view(low_expr, param_name)
        if low_counter is None:
            return False
        if high_expr is None:
            return False
        if high_expr.expr_type != ExpressionType.BINARY_OP or high_expr.operator != "INT_LEFT" or len(high_expr.operands) != 2:
            return False
        shift_bits = self._raw_constant_value(high_expr.operands[1])
        if shift_bits is None:
            return False
        low_bits = low_counter[1]
        if low_bits is None:
            return False
        return shift_bits == low_bits

    def _comparison_to_relation(self, operator: str, swapped: bool) -> Optional[str]:
        mapping = {
            "INT_SLESS": "<",
            "INT_SLESSEQUAL": "<=",
            "INT_LESS": "<",
            "INT_LESSEQUAL": "<=",
        }
        relation = mapping.get(operator)
        if relation is None:
            return None
        if not swapped:
            return relation
        if relation == "<":
            return ">"
        if relation == "<=":
            return ">="
        return None

    def _negate_relation(self, relation: str) -> Optional[str]:
        return {
            "<": ">=",
            "<=": ">",
            ">": "<=",
            ">=": "<",
        }.get(relation)

    def _build_closed_form(
        self,
        param_expr: Expression,
        lower_bound: int,
        coeff: int,
        bias: int,
        base_value: int,
    ) -> Optional[Expression]:
        size = param_expr.size or 4
        wide_size = self._summary_working_size(size)
        lower_const = Expression.constant(lower_bound, size)
        wide_param = self._zero_extend_bitpattern(param_expr, wide_size)
        wide_lower = self._zero_extend_bitpattern(lower_const, wide_size)
        shift_amount = Expression.constant(1, wide_size)

        triangular_n = self._triangular(wide_param, wide_size, shift_amount)
        if lower_bound == 0:
            triangular_delta = triangular_n
        else:
            triangular_lower = self._triangular(wide_lower, wide_size, shift_amount)
            triangular_delta = Expression.binary_op("INT_SUB", triangular_n, triangular_lower)
            triangular_delta.size = wide_size

        term_exprs: List[Expression] = []
        coeff_term = self._scale_term(triangular_delta, coeff, wide_size)
        if coeff_term is not None:
            term_exprs.append(coeff_term)
        if bias != 0:
            distance = Expression.binary_op("INT_SUB", wide_param, wide_lower)
            distance.size = wide_size
            bias_term = self._scale_term(distance, bias, wide_size)
            if bias_term is not None:
                term_exprs.append(bias_term)

        total = self._sum_terms(term_exprs, base_value, size, wide_size)
        return self._truncate_to_width(total, size)

    def _triangular(self, expr: Expression, size: int, shift_amount: Expression) -> Expression:
        one = Expression.constant(1, size)
        incremented = Expression.binary_op("INT_ADD", expr, one)
        incremented.size = size
        product = Expression.binary_op("INT_MULT", expr, incremented)
        product.size = size
        tri = Expression.binary_op("INT_RIGHT", product, shift_amount)
        tri.size = size
        return tri

    def _summary_working_size(self, narrow_size: int) -> int:
        narrow_bits = max(8, narrow_size * 8)
        wide_bits = max(64, narrow_bits * 2)
        return max(narrow_size, (wide_bits + 7) // 8)

    def _zero_extend_bitpattern(self, expr: Expression, target_size: int) -> Expression:
        source_size = expr.size or 0
        if source_size <= 0 or source_size >= target_size:
            copied = expr
            copied.size = max(source_size, target_size)
            if source_size > target_size:
                return self._truncate_to_width(copied, target_size)
            return copied
        widened = Expression.unary_op("INT_ZEXT", expr)
        widened.size = target_size
        return widened

    def _truncate_to_width(self, expr: Expression, target_size: int) -> Expression:
        if (expr.size or 0) <= target_size:
            expr.size = target_size
            return expr
        truncated = Expression.binary_op("SUBPIECE", expr, Expression.constant(0, 4))
        truncated.size = target_size
        return truncated

    def _scale_term(
        self,
        expr: Expression,
        factor: int,
        wide_size: int,
    ) -> Optional[Expression]:
        if factor == 0:
            return None
        if factor == 1:
            expr.size = wide_size
            return expr
        if factor == -1:
            negated = Expression.unary_op("INT_2COMP", expr)
            negated.size = wide_size
            return negated
        factor_const = self._zero_extend_bitpattern(Expression.constant(factor, expr.size or wide_size), wide_size)
        scaled = Expression.binary_op("INT_MULT", factor_const, expr)
        scaled.size = wide_size
        return scaled

    def _sum_terms(
        self,
        term_exprs: Sequence[Expression],
        base_value: int,
        size: int,
        wide_size: int,
    ) -> Expression:
        total: Optional[Expression] = None
        if base_value != 0:
            total = self._zero_extend_bitpattern(Expression.constant(base_value, size), wide_size)
        for term in term_exprs:
            if total is None:
                total = term
                continue
            total = Expression.binary_op("INT_ADD", total, term)
            total.size = wide_size
        if total is None:
            total = self._zero_extend_bitpattern(Expression.constant(0, size), wide_size)
        total.size = wide_size
        return total

    def _build_recursive_conditions(self, param_expr: Expression, lower_bound: int) -> Optional[List[Condition]]:
        size = param_expr.size or 4
        lower_const = Expression.constant(lower_bound, size)
        cond_expr = Expression.binary_op("INT_SLESS", lower_const, param_expr)
        return [Condition(cond_expr, False)]

    def _build_base_conditions(self, param_expr: Expression, lower_bound: int) -> Optional[List[Condition]]:
        size = param_expr.size or 4
        lower_const = Expression.constant(lower_bound, size)
        cond_expr = Expression.binary_op("INT_SLESSEQUAL", param_expr, lower_const)
        return [Condition(cond_expr, False)]
