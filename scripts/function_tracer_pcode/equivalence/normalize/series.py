# -*- coding: utf-8 -*-
"""Safe canonicalization for simple arithmetic-series closed forms."""

from typing import Optional, Tuple

from ...model import Expression, ExpressionType, expression_key_or_identity
from .context import NormalizationContext


def normalize_series_patterns(
    expr: Expression,
    context: NormalizationContext,
) -> Expression:
    """Canonicalize only series shapes that are exact in bit-vector arithmetic."""
    canonical = _match_exact_triangular_phi(expr)
    if canonical is expr:
        return expr

    context.record_rule(
        rule_name="SERIES_CANONICALIZATION",
        before_expr=expr.to_smt(),
        after_expr=canonical.to_smt(),
        reason="Canonicalized equivalent arithmetic-series closed form",
    )
    return canonical


def _match_base_plus_square(expr: Expression) -> Tuple[Optional[Expression], Optional[Expression]]:
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_ADD" or len(expr.operands) != 2:
        return None, None
    left, right = expr.operands
    if _match_square(left) is not None:
        return right, left
    if _match_square(right) is not None:
        return left, right
    return None, None


def _match_square(expr: Expression) -> Optional[Expression]:
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_MULT" or len(expr.operands) != 2:
        return None
    left, right = expr.operands
    if _same_nonconstant_expr(left, right):
        return left
    return None


def _match_half_product(expr: Expression, target_size: int) -> Optional[Tuple[Expression, Expression]]:
    phi_operands = _match_exact_triangular_phi_operands(expr)
    if phi_operands is not None:
        return phi_operands

    inner = expr
    if (
        inner.expr_type == ExpressionType.BINARY_OP
        and inner.operator == "SUBPIECE"
        and len(inner.operands) == 2
        and inner.operands[1].expr_type == ExpressionType.CONSTANT
        and int(inner.operands[1].value) == 0
    ):
        inner = inner.operands[0]

    if inner.expr_type != ExpressionType.BINARY_OP or inner.operator != "INT_RIGHT" or len(inner.operands) != 2:
        return None
    shift = inner.operands[1]
    if shift.expr_type != ExpressionType.CONSTANT or int(shift.value) != 1:
        return None

    mult = inner.operands[0]
    if mult.expr_type != ExpressionType.BINARY_OP or mult.operator != "INT_MULT" or len(mult.operands) != 2:
        return None

    left = _strip_zero_extend(mult.operands[0], target_size)
    right = _strip_zero_extend(mult.operands[1], target_size)
    if left is None or right is None:
        return None
    return left, right


def _match_exact_triangular_phi(expr: Expression) -> Expression:
    phi_operands = _match_exact_triangular_phi_operands(expr)
    if phi_operands is None:
        return expr

    left, right = phi_operands
    return _build_half_product(left, right, expr.size or left.size or right.size or 4)


def _match_exact_triangular_phi_operands(expr: Expression) -> Optional[Tuple[Expression, Expression]]:
    if expr.expr_type != ExpressionType.PHI or not expr.value or len(expr.value) != 2:
        return None

    branches = expr.value
    even_condition, even_value = branches[0]
    odd_condition, odd_value = branches[1]
    if even_condition is None or odd_condition is None:
        return None
    if not _same_condition_expression(even_condition.expression, odd_condition.expression):
        return None
    if even_condition.negated == odd_condition.negated:
        return None
    if even_condition.negated:
        even_value, odd_value = odd_value, even_value

    parity_base = _match_parity_zero_condition(even_condition.expression)
    if parity_base is None:
        return None

    if not _matches_exact_triangular_even_value(even_value, parity_base):
        return None
    if not _matches_exact_triangular_odd_value(odd_value, parity_base):
        return None

    one = Expression.constant(1, parity_base.size or expr.size or 4)
    base_minus_one = Expression.binary_op("INT_SUB", _clone_expression(parity_base), one)
    base_minus_one.size = parity_base.size or expr.size or 4
    return _clone_expression(parity_base), _clone_expression(base_minus_one)


def _strip_zero_extend(expr: Expression, target_size: int) -> Optional[Expression]:
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_ZEXT", "INT_SEXT"} and expr.operands:
        inner = expr.operands[0]
        if target_size <= 0 or (inner.size and inner.size <= target_size):
            return inner
    return expr


def _build_half_product(left: Expression, right: Expression, target_size: int) -> Expression:
    wide_size = max(8, target_size * 2)
    wide_left = Expression.unary_op("INT_ZEXT", left)
    wide_left.size = wide_size
    wide_right = Expression.unary_op("INT_ZEXT", right)
    wide_right.size = wide_size
    product = Expression.binary_op("INT_MULT", wide_left, wide_right)
    product.size = wide_size
    shift_amount = Expression.constant(1, wide_size)
    shifted = Expression.binary_op("INT_RIGHT", product, shift_amount)
    shifted.size = wide_size
    if wide_size == target_size:
        return shifted
    truncated = Expression.binary_op("SUBPIECE", shifted, Expression.constant(0, 4))
    truncated.size = target_size
    return truncated


def _match_var_plus_const(expr: Expression) -> Optional[Tuple[Expression, int]]:
    if expr.expr_type != ExpressionType.CONSTANT and expr.expr_type not in {ExpressionType.BINARY_OP, ExpressionType.UNARY_OP}:
        return expr, 0

    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None

    left, right = expr.operands
    if expr.operator == "INT_ADD":
        left_const = _signed_const_value(left)
        right_const = _signed_const_value(right)
        if left_const is not None:
            return _accumulate_bias(right, left_const)
        if right_const is not None:
            return _accumulate_bias(left, right_const)
    if expr.operator == "INT_SUB" and right.expr_type == ExpressionType.CONSTANT:
        return _accumulate_bias(left, -int(right.value))
    return None


def _with_bias(expr: Expression, bias: int) -> Optional[Tuple[Expression, int]]:
    if expr.expr_type != ExpressionType.CONSTANT:
        return expr, bias
    return None


def _accumulate_bias(expr: Expression, bias: int) -> Optional[Tuple[Expression, int]]:
    nested = _match_var_plus_const(expr)
    if nested is None:
        return _with_bias(expr, bias)
    return nested[0], nested[1] + bias


def _same_nonconstant_expr(left: Expression, right: Expression) -> bool:
    left = _strip_series_wrapper(left)
    right = _strip_series_wrapper(right)
    left_key = expression_key_or_identity(left, normalize_commutative=True)
    right_key = expression_key_or_identity(right, normalize_commutative=True)
    return left_key == right_key


def _same_condition_expression(left: Expression, right: Expression) -> bool:
    return _same_nonconstant_expr(left, right)


def _clone_expression(expr: Expression) -> Expression:
    return Expression(
        expr_type=expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=[_clone_expression(op) for op in expr.operands],
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
    )


def _matches_exact_triangular_even_value(expr: Expression, base_expr: Expression) -> bool:
    expr = _strip_series_wrapper(expr)
    base_expr = _strip_series_wrapper(base_expr)
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_MULT" or len(expr.operands) != 2:
        return False
    left, right = expr.operands
    return (
        (_is_shift_right_by_one_of(left, base_expr) and _is_expr_minus_one(right, base_expr))
        or (_is_shift_right_by_one_of(right, base_expr) and _is_expr_minus_one(left, base_expr))
    )


def _matches_exact_triangular_odd_value(expr: Expression, base_expr: Expression) -> bool:
    expr = _strip_series_wrapper(expr)
    base_expr = _strip_series_wrapper(base_expr)
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_MULT" or len(expr.operands) != 2:
        return False
    left, right = expr.operands
    return (
        (_same_nonconstant_expr(left, base_expr) and _is_shift_right_by_one_of_minus_one(right, base_expr))
        or (_same_nonconstant_expr(right, base_expr) and _is_shift_right_by_one_of_minus_one(left, base_expr))
    )


def _is_shift_right_by_one_of(expr: Expression, base_expr: Expression) -> bool:
    expr = _strip_series_wrapper(expr)
    base_expr = _strip_series_wrapper(base_expr)
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_RIGHT" or len(expr.operands) != 2:
        return False
    shift = expr.operands[1]
    return _same_nonconstant_expr(expr.operands[0], base_expr) and _is_one_constant(shift)


def _is_shift_right_by_one_of_minus_one(expr: Expression, base_expr: Expression) -> bool:
    expr = _strip_series_wrapper(expr)
    base_expr = _strip_series_wrapper(base_expr)
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_RIGHT" or len(expr.operands) != 2:
        return False
    shift = expr.operands[1]
    return _is_expr_minus_one(expr.operands[0], base_expr) and _is_one_constant(shift)


def _is_expr_minus_one(expr: Expression, base_expr: Expression) -> bool:
    expr = _strip_series_wrapper(expr)
    base_expr = _strip_series_wrapper(base_expr)
    bias = _match_relative_const(expr, base_expr)
    if bias == -1:
        return True

    expr_origin = _match_expr_plus_const(expr)
    base_origin = _match_expr_plus_const(base_expr)
    if expr_origin is None or base_origin is None:
        return False

    expr_base, expr_bias = expr_origin
    base_base, base_bias = base_origin
    return _same_nonconstant_expr(expr_base, base_base) and expr_bias == base_bias - 1


def _match_expr_plus_const(expr: Expression) -> Optional[Tuple[Expression, int]]:
    expr = _strip_series_wrapper(expr)
    if expr.expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
        return expr, 0

    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        const_value = _signed_const_value(expr)
        if const_value is None:
            return expr, 0
        return None

    left, right = expr.operands
    if expr.operator == "INT_ADD":
        left_const = _signed_const_value(left)
        right_const = _signed_const_value(right)
        if left_const is not None:
            return _accumulate_expr_bias(right, left_const)
        if right_const is not None:
            return _accumulate_expr_bias(left, right_const)
    if expr.operator == "INT_SUB":
        right_const = _signed_const_value(right)
        if right_const is not None:
            return _accumulate_expr_bias(left, -right_const)
    return expr, 0


def _accumulate_expr_bias(expr: Expression, bias: int) -> Optional[Tuple[Expression, int]]:
    nested = _match_expr_plus_const(expr)
    if nested is None:
        return None
    return nested[0], nested[1] + bias


def _match_relative_const(expr: Expression, base_expr: Expression) -> Optional[int]:
    expr = _strip_series_wrapper(expr)
    base_expr = _strip_series_wrapper(base_expr)
    if _same_nonconstant_expr(expr, base_expr):
        return 0

    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None

    left, right = expr.operands
    if expr.operator == "INT_ADD":
        left_const = _signed_const_value(left)
        if left_const is not None:
            right_bias = _match_relative_const(right, base_expr)
            if right_bias is not None:
                return right_bias + left_const
        right_const = _signed_const_value(right)
        if right_const is not None:
            left_bias = _match_relative_const(left, base_expr)
            if left_bias is not None:
                return left_bias + right_const
    if expr.operator == "INT_SUB":
        right_const = _signed_const_value(right)
        if right_const is not None:
            left_bias = _match_relative_const(left, base_expr)
            if left_bias is not None:
                return left_bias - right_const
    return None


def _match_parity_zero_condition(expr: Expression) -> Optional[Expression]:
    expr = _strip_series_wrapper(expr)
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_EQUAL" or len(expr.operands) != 2:
        return None
    left, right = expr.operands
    if _is_zero_constant(left):
        return _match_parity_expr(right)
    if _is_zero_constant(right):
        return _match_parity_expr(left)
    return None


def _match_parity_expr(expr: Expression) -> Optional[Expression]:
    expr = _strip_series_wrapper(expr)
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_AND" or len(expr.operands) != 2:
        return None
    left, right = expr.operands
    if _is_one_constant(left):
        return right
    if _is_one_constant(right):
        return left
    return None


def _is_zero_constant(expr: Expression) -> bool:
    value = _basic_const_value(expr)
    return value == 0


def _is_one_constant(expr: Expression) -> bool:
    value = _basic_const_value(expr)
    return value == 1


def _flatten_add_terms(expr: Expression, sign: int = 1) -> list[tuple[int, Expression]]:
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD" and len(expr.operands) == 2:
        return _flatten_add_terms(expr.operands[0], sign) + _flatten_add_terms(expr.operands[1], sign)
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_SUB" and len(expr.operands) == 2:
        return _flatten_add_terms(expr.operands[0], sign) + _flatten_add_terms(expr.operands[1], -sign)
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"} and expr.operands:
        return _flatten_add_terms(expr.operands[0], -sign)
    return [(sign, expr)]


def _sum_terms(terms: list[tuple[int, Expression]]) -> Optional[Expression]:
    result: Optional[Expression] = None
    for sign, expr in terms:
        term_expr = _apply_sign(expr, sign)
        if term_expr is None:
            continue
        if result is None:
            result = term_expr
            continue
        combined = Expression.binary_op("INT_ADD", result, term_expr)
        combined.size = max(result.size or 0, term_expr.size or 0, 4)
        result = combined
    return result


def _apply_sign(expr: Expression, sign: int) -> Optional[Expression]:
    if sign == 1:
        return expr
    if sign == -1:
        negated = Expression.unary_op("INT_2COMP", expr)
        negated.size = expr.size
        return negated
    return None


def _match_affine_coeff_bias(expr: Expression, base_expr: Expression) -> Optional[Tuple[int, int]]:
    expr = _strip_series_wrapper(expr)
    base_expr = _strip_series_wrapper(base_expr)
    if _same_nonconstant_expr(expr, base_expr):
        return 1, 0

    const_value = _signed_const_value(expr)
    if const_value is not None:
        return 0, const_value

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left, right = expr.operands
        if expr.operator == "INT_ADD":
            left_affine = _match_affine_coeff_bias(left, base_expr)
            right_affine = _match_affine_coeff_bias(right, base_expr)
            if left_affine is None or right_affine is None:
                return None
            return left_affine[0] + right_affine[0], left_affine[1] + right_affine[1]
        if expr.operator == "INT_SUB":
            left_affine = _match_affine_coeff_bias(left, base_expr)
            right_affine = _match_affine_coeff_bias(right, base_expr)
            if left_affine is None or right_affine is None:
                return None
            return left_affine[0] - right_affine[0], left_affine[1] - right_affine[1]
        if expr.operator == "INT_MULT":
            left_const = _signed_const_value(left)
            right_const = _signed_const_value(right)
            if left_const is not None:
                right_affine = _match_affine_coeff_bias(right, base_expr)
                if right_affine is None:
                    return None
                return left_const * right_affine[0], left_const * right_affine[1]
            if right_const is not None:
                left_affine = _match_affine_coeff_bias(left, base_expr)
                if left_affine is None:
                    return None
                return right_const * left_affine[0], right_const * left_affine[1]

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"} and expr.operands:
        affine = _match_affine_coeff_bias(expr.operands[0], base_expr)
        if affine is None:
            return None
        return -affine[0], -affine[1]

    return None


def _build_triangular(base_expr: Expression, target_size: int) -> Expression:
    incremented = Expression.binary_op("INT_ADD", _clone_expression(base_expr), Expression.constant(1, base_expr.size or target_size))
    incremented.size = base_expr.size or target_size
    return _build_half_product(base_expr, incremented, target_size)


def _signed_const_value(expr: Expression) -> Optional[int]:
    expr = _strip_series_wrapper(expr)
    return _basic_const_value(expr)


def _basic_const_value(expr: Expression) -> Optional[int]:
    if expr.expr_type == ExpressionType.CONSTANT:
        value = int(expr.value)
        bit_width = expr.get_bit_width()
        if bit_width > 0:
            modulus = 1 << bit_width
            sign_bit = 1 << (bit_width - 1)
            value %= modulus
            if value & sign_bit:
                value -= modulus
        return value
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        if expr.operator == "INT_2COMP":
            inner = _basic_const_value(expr.operands[0])
            if inner is not None:
                return -inner
        if expr.operator in {"INT_ZEXT", "INT_SEXT"}:
            return _basic_const_value(expr.operands[0])
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left_value = _basic_const_value(expr.operands[0])
        right_value = _basic_const_value(expr.operands[1])
        if expr.operator == "INT_ADD" and left_value is not None and right_value is not None:
            return left_value + right_value
        if expr.operator == "INT_SUB" and left_value is not None and right_value is not None:
            return left_value - right_value
        if expr.operator == "INT_MULT" and left_value is not None and right_value is not None:
            return left_value * right_value
        if expr.operator in {"INT_RIGHT", "INT_SRIGHT"} and left_value is not None and right_value is not None:
            if right_value < 0:
                return None
            return left_value >> right_value
        if expr.operator == "INT_AND" and left_value is not None and right_value is not None:
            return left_value & right_value
    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "SUBPIECE"
        and len(expr.operands) == 2
        and expr.operands[1].expr_type == ExpressionType.CONSTANT
        and int(expr.operands[1].value) == 0
    ):
        return _basic_const_value(expr.operands[0])
    return None


def _strip_series_wrapper(expr: Expression) -> Expression:
    current = expr
    while True:
        next_expr = _strip_series_wrapper_once(current)
        if next_expr is current:
            return current
        current = next_expr


def _strip_series_wrapper_once(expr: Expression) -> Expression:
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        if expr.operator in {"INT_ZEXT", "INT_SEXT"}:
            return expr.operands[0]
        return expr

    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return expr

    left, right = expr.operands
    if expr.operator == "SUBPIECE" and right.expr_type == ExpressionType.CONSTANT and int(right.value) == 0:
        return left
    if expr.operator == "INT_ADD":
        if _is_zero_constant(left):
            return right
        if _is_zero_constant(right):
            return left
    if expr.operator == "INT_SUB" and _is_zero_constant(right):
        return left
    return expr
