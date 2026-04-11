# -*- coding: utf-8 -*-
"""Structural recurrence summaries for simple recursion/loop patterns."""

from __future__ import annotations

from typing import Iterable, List, Optional, Sequence, Tuple

from ..model import Condition, Expression, ExpressionType, ReturnInfo


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
        if len(getattr(analysis, "parameters", []) or []) != 1:
            return None

        summary = self._try_summarize_linear_self_recursion(function, high_function, analysis)
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
            ),
            ReturnInfo(
                address=recursive_ret.address,
                value=recursive_value,
                conditions=recursive_conditions,
                branch_index=recursive_ret.branch_index,
            ),
        ]

        self._debug(
            f"Recovered linear self-recursive summary for '{function_name}' "
            f"(lower_bound={lower_bound}, coeff={coeff}, bias={bias}, base={base_value})"
        )
        return summarized_returns, "linear_self_recursion_summary"

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
