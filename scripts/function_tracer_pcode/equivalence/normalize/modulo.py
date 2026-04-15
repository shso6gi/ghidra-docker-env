# -*- coding: utf-8 -*-
"""Safe modulo canonicalization rules."""

from ...model import Expression, ExpressionType, expression_key_or_identity
from .context import NormalizationContext


SIGNED_DIV_OPS = frozenset({"INT_SDIV", "SDIV", "//"})
UNSIGNED_DIV_OPS = frozenset({"INT_DIV", "DIV", "/"})
ALL_DIV_OPS = SIGNED_DIV_OPS | UNSIGNED_DIV_OPS
MULT_OPS = frozenset({"INT_MULT", "MULT", "*"})
SUB_OPS = frozenset({"INT_SUB", "SUB", "-"})


def normalize_modulo_patterns(
    expr: Expression,
    context: NormalizationContext,
) -> Expression:
    """
    剰余の展開形式を剰余演算に正規化する。

    適用するのは bit-vector 恒等式として安全な変形のみ:
    - a - ((a / b) * b) -> a % b
    """
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator not in SUB_OPS:
        return expr

    if len(expr.operands) != 2:
        return expr

    lhs = expr.operands[0]
    rhs = expr.operands[1]
    if rhs.expr_type != ExpressionType.BINARY_OP or rhs.operator not in MULT_OPS:
        return expr

    div_expr, multiplier = _extract_div_and_multiplier(rhs)
    if div_expr is None or multiplier is None or len(div_expr.operands) != 2:
        return expr

    dividend = div_expr.operands[0]
    divisor = div_expr.operands[1]
    if not _same_expr(lhs, dividend):
        return expr
    if not _same_expr(multiplier, divisor):
        return expr

    mod_op = "INT_SREM" if div_expr.operator in SIGNED_DIV_OPS else "INT_REM"
    rewritten = Expression.binary_op(mod_op, lhs, multiplier)
    rewritten.size = expr.size
    context.record_rule(
        rule_name="MODULO_CANONICALIZATION",
        before_expr=expr.to_smt(),
        after_expr=rewritten.to_smt(),
        reason="Canonicalized remainder expansion to modulo operator",
    )
    return rewritten


def _extract_div_and_multiplier(mult_expr: Expression):
    for index, operand in enumerate(mult_expr.operands):
        if operand.expr_type == ExpressionType.BINARY_OP and operand.operator in ALL_DIV_OPS:
            return operand, mult_expr.operands[1 - index]
    return None, None


def _same_expr(lhs: Expression, rhs: Expression) -> bool:
    lhs_key = expression_key_or_identity(lhs, normalize_commutative=True)
    rhs_key = expression_key_or_identity(rhs, normalize_commutative=True)
    return lhs_key == rhs_key
