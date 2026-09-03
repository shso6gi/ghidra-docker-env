"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence.summarizer``."""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    Condition,
    ConditionSimplifier,
    Expression,
    ExpressionType,
    ReturnInfo,
    _reduce_expression_under_conditions,
    _runtime_conditions_signature,
    eval_constant_raw,
    is_integral_data_type,
)

def _impl__synthesize_one_step_cases_from_effects(
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
        conds = ConditionSimplifier.simplify_conditions_object_centric(effect.conditions or [])
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
        step_context = ConditionSimplifier.simplify_conditions_object_centric(list(conds) + [step_eq])
        if ConditionSimplifier.object_centric_is_contradiction(step_context):
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
                pcode_op_ref=getattr(base_case, "pcode_op_ref", None),
                return_value_pcode_op_refs=tuple(
                    getattr(base_case, "return_value_pcode_op_refs", ()) or ()
                ),
            )
        )
    return synthesized

def _impl__extract_store_delta_expr(
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

def _impl__extract_additive_delta(
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

def _impl__flatten_add_terms(
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

def _impl__build_parity_split_loop_value(
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

def _impl__param_expr_placeholder(self, name: str, size: int) -> Expression:
    return Expression.parameter(name, size=size)

def _impl__expr_is_add_one_of_param(self, expr: Expression, param_name: str) -> bool:
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

def _impl__extract_counter_parity(
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

def _impl__iter_pcode_ops(self, high_function) -> Iterable:
    for basic_block in high_function.getBasicBlocks():
        pcode_iter = basic_block.getIterator()
        while pcode_iter.hasNext():
            yield pcode_iter.next()

def _impl__parameter_can_be_counter(self, param_info: dict) -> bool:
    size = int(param_info.get("size") or 0)
    if size not in {1, 2, 4, 8}:
        return False
    data_type_obj = param_info.get("data_type_obj")
    if data_type_obj is None:
        return True
    return is_integral_data_type(
        data_type_obj,
        param_info.get("data_type"),
        program=getattr(self.tracer, "program", None),
    )

def _impl__is_direct_self_call(self, op, function_name: str) -> bool:
    resolver = getattr(self.tracer, "resolve_call_target_ref", None)
    if not callable(resolver):
        return False
    target_ref = resolver(
        op.getInput(0),
        allow_containing=True,
        allow_code_address=False,
    )
    return bool(target_ref is not None and target_ref.function_name == function_name)

def _impl__constant_value(self, expr: Optional[Expression]) -> Optional[int]:
    raw = self._raw_constant_value(expr)
    if raw is None:
        return None
    return raw

def _impl__raw_constant_value(self, expr: Optional[Expression]) -> Optional[int]:
    if expr is None:
        return None
    if expr.expr_type == ExpressionType.CONSTANT:
        return int(expr.value)
    evaluated = eval_constant_raw(expr)
    if evaluated is None:
        return None
    return int(evaluated[0])

def _impl__signed_constant_value(
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

def _impl__extract_unit_step_from_call_argument(self, expr: Expression, param_name: str) -> Optional[int]:
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

def _impl__normalize_counter_view(
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
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "SUBPIECE" and len(expr.operands) == 2:
        source, offset = expr.operands
        offset_value = self._raw_constant_value(offset)
        if offset_value == 0:
            source_counter = self._normalize_counter_view(source, param_name)
            if source_counter is not None:
                expr_bits = (expr.size * 8) if expr.size else None
                if expr_bits is not None and expr_bits > 0:
                    return source_counter[0], expr_bits
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

def _impl__infer_counter_bit_width(self, expr: Optional[Expression], param_name: str) -> Optional[int]:
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

def _impl__bit_width_from_low_bit_mask(self, value: int) -> Optional[int]:
    if value <= 0:
        return None
    if (value & (value + 1)) != 0:
        return None
    bit_width = value.bit_length()
    if bit_width < 8 or bit_width % 8 != 0:
        return None
    return bit_width

def _impl__parameter_comparison_relation(self, condition: Condition) -> Optional[Tuple[str, str, str]]:
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

def _impl__matches_shifted_high_reconstruction(
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

def _impl__comparison_to_relation(self, operator: str, swapped: bool) -> Optional[str]:
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

def _impl__negate_relation(self, relation: str) -> Optional[str]:
    return {
        "<": ">=",
        "<=": ">",
        ">": "<=",
        ">=": "<",
    }.get(relation)

def _impl__build_closed_form(
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

def _impl__triangular(self, expr: Expression, size: int, shift_amount: Expression) -> Expression:
    one = Expression.constant(1, size)
    incremented = Expression.binary_op("INT_ADD", expr, one)
    incremented.size = size
    product = Expression.binary_op("INT_MULT", expr, incremented)
    product.size = size
    tri = Expression.binary_op("INT_RIGHT", product, shift_amount)
    tri.size = size
    return tri

def _impl__zero_extend_bitpattern(self, expr: Expression, target_size: int) -> Expression:
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

def _impl__truncate_to_width(self, expr: Expression, target_size: int) -> Expression:
    if (expr.size or 0) <= target_size:
        expr.size = target_size
        return expr
    truncated = Expression.binary_op("SUBPIECE", expr, Expression.constant(0, 4))
    truncated.size = target_size
    return truncated

def _impl__scale_term(
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

def _impl__sum_terms(
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
