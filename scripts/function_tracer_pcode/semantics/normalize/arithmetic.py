# -*- coding: utf-8 -*-
"""Safe arithmetic canonicalization rules."""

from scripts.function_tracer_pcode.core import Expression, ExpressionType
from scripts.function_tracer_pcode.semantics.normalize.context import NormalizationContext
from scripts.function_tracer_pcode.core.render_smt import render_expression_smt_evidence


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
    - x * 0 -> 0
    - 0 * x -> 0
    - x * 1 -> x
    - 1 * x -> x
    - 加算木の平坦化と順序正規化
    """
    if expr.expr_type != ExpressionType.BINARY_OP:
        return expr

    expr_before = expr

    if expr.operator == "INT_SUB":
        expr = _rewrite_sub_as_add_neg(expr)

    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD":
        expr = _canonicalize_add(expr)
    elif expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_MULT":
        expr = _simplify_mult_identities(expr)

    if expr is not expr_before:
        context.record_rule(
            rule_name="ARITHMETIC_CANONICALIZATION",
            before_expr=render_expression_smt_evidence(expr_before),
            after_expr=render_expression_smt_evidence(expr),
            reason="Canonicalized add/sub using modulo-safe bit-vector identities",
        )

    return expr


def _rewrite_sub_as_add_neg(expr: Expression) -> Expression:
    if len(expr.operands) != 2:
        return expr

    left, right = expr.operands
    neg_right = Expression.unary_op("INT_2COMP", right)
    neg_right.size = right.size

    rewritten = expr.clone_with(
        operator="INT_ADD",
        operands=[left, neg_right],
        size=expr.size,
    )
    return rewritten


def _canonicalize_add(expr: Expression) -> Expression:
    # Issue #298: 宣言の大きさの違う加算を平らにすると、狭い加算の桁あふれ（wrap）を失い、
    # 項を 1 つにすると伸ばし方の分からない狭い値に置き換わる。全ての項と入れ子の加算が
    # 同じ大きさのときだけ並べ替える
    width = int(expr.size or 0)
    terms = _collect_add_terms(expr, width)
    if width <= 0 or any(int(term.size or 0) != width for term in terms):
        return expr
    original_terms = list(terms)

    terms = [term for term in terms if not _is_zero_constant(term)]
    if not terms:
        zero = Expression.constant(0, size=expr.size or 0)
        zero.size = expr.size
        return zero

    if len(terms) == 1:
        return terms[0]

    sorted_terms = sorted(terms, key=_term_sort_key)
    if sorted_terms == original_terms and len(sorted_terms) == 2:
        return expr

    rebuilt = _build_add_tree(sorted_terms)
    rebuilt.size = expr.size
    return rebuilt


def _collect_add_terms(expr: Expression, width: int):
    """同じ大きさ（``width`` byte）の入れ子の加算だけを平らにした項。"""
    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_ADD"
        and len(expr.operands) == 2
        and int(expr.size or 0) == width
    ):
        return _collect_add_terms(expr.operands[0], width) + _collect_add_terms(expr.operands[1], width)
    return [expr]


def _build_add_tree(terms):
    current = terms[0]
    for term in terms[1:]:
        current = Expression.binary_op("INT_ADD", current, term)
    return current


def _constant_value(expr: Expression):
    from scripts.function_tracer_pcode.core.render_smt.widths import constant_value_at_width

    return constant_value_at_width(expr)


def _is_zero_constant(expr: Expression) -> bool:
    return _constant_value(expr) == 0


def _is_one_constant(expr: Expression) -> bool:
    return _constant_value(expr) == 1


def _simplify_mult_identities(expr: Expression) -> Expression:
    if len(expr.operands) != 2:
        return expr

    left, right = expr.operands
    if _is_zero_constant(left) or _is_zero_constant(right):
        zero = Expression.constant(0, size=expr.size or max(left.size, right.size))
        zero.size = expr.size or zero.size
        return zero
    # Issue #298: 残す被演算子が乗算と同じ大きさのときだけ外す（大きさを付け替えると、狭い値を
    # 広い値と読み替える）
    width = int(expr.size or 0)
    if _is_one_constant(left) and width > 0 and int(right.size or 0) == width:
        return right
    if _is_one_constant(right) and width > 0 and int(left.size or 0) == width:
        return left
    return expr


def _term_sort_key(expr: Expression):
    if expr.expr_type == ExpressionType.CONSTANT:
        return (0, expr.get_bit_width(), int(expr.value))
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        return (1, expr.name or "", expr.get_bit_width())
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_2COMP":
        inner = expr.operands[0] if expr.operands else Expression.unknown("missing")
        return (2, _term_sort_key(inner))
    from scripts.function_tracer_pcode.core import expression_key_or_identity

    return (3, expression_key_or_identity(expr, normalize_commutative=True))
