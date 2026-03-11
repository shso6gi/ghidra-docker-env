# -*- coding: utf-8 -*-
"""Safe arithmetic canonicalization rules."""

from ...model import Expression, ExpressionType
from .context import NormalizationContext


def normalize_arithmetic(
    expr: Expression,
    context: NormalizationContext,
) -> Expression:
    """
    加算・減算の安全な正規形化を行う

    適用するのは bit-vector 上で常に成り立つ変形のみ:
    - x - y -> x + (-y)
    - x + 0 -> x
    - 0 + x -> x
    - 加算木の平坦化と順序正規化
    """
    if expr.expr_type != ExpressionType.BINARY_OP:
        return expr

    expr_before = expr

    if expr.operator == "INT_SUB":
        expr = _rewrite_sub_as_add_neg(expr)

    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD":
        expr = _canonicalize_add(expr)

    if expr is not expr_before:
        context.record_rule(
            rule_name="ARITHMETIC_CANONICALIZATION",
            before_expr=expr_before.to_smt(),
            after_expr=expr.to_smt(),
            reason="Canonicalized add/sub using modulo-safe bit-vector identities",
        )

    return expr


def _rewrite_sub_as_add_neg(expr: Expression) -> Expression:
    if len(expr.operands) != 2:
        return expr

    left, right = expr.operands
    neg_right = Expression.unary_op("INT_2COMP", right)
    neg_right.size = right.size

    rewritten = Expression.binary_op("INT_ADD", left, neg_right)
    rewritten.size = expr.size
    return rewritten


def _canonicalize_add(expr: Expression) -> Expression:
    terms = _collect_add_terms(expr)
    original_terms = list(terms)

    terms = [term for term in terms if not _is_zero_constant(term)]
    if not terms:
        zero = Expression.constant(0, size=expr.size or 0)
        zero.size = expr.size
        return zero

    if len(terms) == 1:
        only = terms[0]
        return Expression(
            expr_type=only.expr_type,
            value=only.value,
            operator=only.operator,
            operands=only.operands,
            size=only.size or expr.size,
            name=only.name,
            data_type=only.data_type,
            storage_info=only.storage_info,
        )

    sorted_terms = sorted(terms, key=_term_sort_key)
    if sorted_terms == original_terms and len(sorted_terms) == 2:
        return expr

    rebuilt = _build_add_tree(sorted_terms)
    rebuilt.size = expr.size
    return rebuilt


def _collect_add_terms(expr: Expression):
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD" and len(expr.operands) == 2:
        return _collect_add_terms(expr.operands[0]) + _collect_add_terms(expr.operands[1])
    return [expr]


def _build_add_tree(terms):
    current = terms[0]
    for term in terms[1:]:
        current = Expression.binary_op("INT_ADD", current, term)
    return current


def _is_zero_constant(expr: Expression) -> bool:
    return expr.expr_type == ExpressionType.CONSTANT and expr.value == 0


def _term_sort_key(expr: Expression):
    if expr.expr_type == ExpressionType.CONSTANT:
        return (0, expr.get_bit_width(), int(expr.value))
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        return (1, expr.name or "", expr.get_bit_width())
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_2COMP":
        inner = expr.operands[0] if expr.operands else Expression.unknown("missing")
        return (2, _term_sort_key(inner))
    return (3, expr.to_smt())
