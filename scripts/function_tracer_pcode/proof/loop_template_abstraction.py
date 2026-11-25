# -*- coding: utf-8 -*-
"""Exact algebraic template abstraction for loop-derived closed forms.

This layer is intentionally conservative:
- it only proves equality when both expressions can be reduced to the same
  modulo-2^N polynomial over canonical atoms;
- otherwise it abstains and lets later fallbacks continue.

The abstraction is exact for the supported ring operators (add/sub/neg/mul)
because bit-vectors with those operators form a commutative ring modulo 2^N.
Recognized exact arithmetic-series forms are reduced to a canonical
"tri(base) + affine(base)" representation before comparison.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from scripts.function_tracer_pcode.core import (
    Expression,
    ExpressionType,
    StructuralKey,
    expression_key_or_identity,
)
from scripts.function_tracer_pcode.semantics.normalize import (
    NormalizationContext,
    NormalizationSettings,
    normalize_expression,
)
from scripts.function_tracer_pcode.semantics.normalize.series import (
    _match_expr_plus_const,
    _match_half_product,
    _same_nonconstant_expr,
)


MAX_TEMPLATE_TERMS = 256
SAFE_NORMALIZATION_SETTINGS = NormalizationSettings.safe()


@dataclass(frozen=True, order=True)
class TemplateAtom:
    kind: str
    key: object

    def render(self) -> str:
        return f"{self.kind}:{repr(self.key)}"


@dataclass
class TemplateBuildResult:
    width_bits: int
    terms: Dict[Tuple[TemplateAtom, ...], int]

    def is_zero(self) -> bool:
        return not self.terms

    def summary(self) -> str:
        if not self.terms:
            return "0"

        pieces: List[str] = []
        for monomial, coeff in sorted(self.terms.items(), key=lambda item: (len(item[0]), [atom.render() for atom in item[0]])):
            atom_part = " * ".join(atom.render() for atom in monomial) if monomial else "1"
            pieces.append(f"{coeff}*{atom_part}")
        return " + ".join(pieces)


def prove_template_equivalence(
    expr1: Expression,
    expr2: Expression,
    *,
    target_bits: int,
    debug: bool = False,
) -> Tuple[bool, str]:
    """Try to prove equality via exact algebraic template abstraction."""
    normalized1 = normalize_expression(expr1, NormalizationContext(settings=SAFE_NORMALIZATION_SETTINGS))
    normalized2 = normalize_expression(expr2, NormalizationContext(settings=SAFE_NORMALIZATION_SETTINGS))

    poly1 = _build_template(normalized1, target_bits)
    poly2 = _build_template(normalized2, target_bits)
    if poly1 is None or poly2 is None:
        reason = "template abstraction aborted"
        if debug:
            details = []
            if poly1 is None:
                details.append("expr1")
            if poly2 is None:
                details.append("expr2")
            reason = f"{reason}: {', '.join(details)}"
        return False, reason

    if poly1.terms == poly2.terms:
        return True, f"template match: {poly1.summary()}"

    if debug:
        return (
            False,
            "template mismatch: "
            f"left={poly1.summary()} | right={poly2.summary()}",
        )
    return False, "template mismatch"


def _build_template(expr: Expression, width_bits: int) -> Optional[TemplateBuildResult]:
    modulus = 1 << width_bits

    def const_poly(value: int) -> TemplateBuildResult:
        normalized = value % modulus
        if normalized == 0:
            return TemplateBuildResult(width_bits, {})
        return TemplateBuildResult(width_bits, {tuple(): normalized})

    def atom_poly(atom: TemplateAtom) -> TemplateBuildResult:
        return TemplateBuildResult(width_bits, {(atom,): 1})

    def add_poly(left: TemplateBuildResult, right: TemplateBuildResult) -> Optional[TemplateBuildResult]:
        merged: Dict[Tuple[TemplateAtom, ...], int] = dict(left.terms)
        for monomial, coeff in right.terms.items():
            merged[monomial] = (merged.get(monomial, 0) + coeff) % modulus
            if merged[monomial] == 0:
                merged.pop(monomial)
        if len(merged) > MAX_TEMPLATE_TERMS:
            return None
        return TemplateBuildResult(width_bits, merged)

    def neg_poly(poly: TemplateBuildResult) -> TemplateBuildResult:
        if not poly.terms:
            return poly
        return TemplateBuildResult(
            width_bits,
            {
                monomial: (-coeff) % modulus
                for monomial, coeff in poly.terms.items()
                if ((-coeff) % modulus) != 0
            },
        )

    def mul_poly(left: TemplateBuildResult, right: TemplateBuildResult) -> Optional[TemplateBuildResult]:
        if not left.terms or not right.terms:
            return TemplateBuildResult(width_bits, {})

        products: Dict[Tuple[TemplateAtom, ...], int] = {}
        for left_monomial, left_coeff in left.terms.items():
            for right_monomial, right_coeff in right.terms.items():
                monomial = tuple(sorted(left_monomial + right_monomial))
                coeff = (left_coeff * right_coeff) % modulus
                products[monomial] = (products.get(monomial, 0) + coeff) % modulus
                if products[monomial] == 0:
                    products.pop(monomial)
                if len(products) > MAX_TEMPLATE_TERMS:
                    return None
        return TemplateBuildResult(width_bits, products)

    def build(expr_node: Expression) -> Optional[TemplateBuildResult]:
        adapted = _strip_width_adapter(expr_node, width_bits)
        if adapted is not expr_node:
            return build(adapted)

        const_value = _const_value_for_template(expr_node, width_bits)
        if const_value is not None:
            return const_poly(const_value)

        tri_poly = _build_triangular_poly(expr_node, width_bits, const_poly, atom_poly, add_poly, mul_poly)
        if tri_poly is not None:
            return tri_poly

        canonical = normalize_expression(
            _normalize_expression_for_width(expr_node, width_bits),
            NormalizationContext(settings=SAFE_NORMALIZATION_SETTINGS),
        )
        if not _same_expression_key(canonical, expr_node):
            return build(canonical)

        if expr_node.expr_type == ExpressionType.CONSTANT:
            return const_poly(int(expr_node.value))

        if expr_node.expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE, ExpressionType.LITERAL}:
            return atom_poly(_symbol_atom(expr_node, width_bits))

        if expr_node.expr_type == ExpressionType.UNARY_OP and expr_node.operands:
            operand = build(expr_node.operands[0])
            if operand is None:
                return None
            if expr_node.operator in {"INT_2COMP", "INT_NEGATE"}:
                return neg_poly(operand)
            return atom_poly(_generic_atom(expr_node, width_bits))

        if expr_node.expr_type == ExpressionType.BINARY_OP and len(expr_node.operands) == 2:
            left_expr, right_expr = expr_node.operands
            left = build(left_expr)
            right = build(right_expr)
            if left is None or right is None:
                return None

            if expr_node.operator == "INT_ADD":
                return add_poly(left, right)
            if expr_node.operator == "INT_SUB":
                return add_poly(left, neg_poly(right))
            if expr_node.operator == "INT_MULT":
                return mul_poly(left, right)
            return atom_poly(_generic_atom(expr_node, width_bits))

        if expr_node.expr_type == ExpressionType.PHI:
            return atom_poly(_generic_atom(expr_node, width_bits))

        return atom_poly(_generic_atom(expr_node, width_bits))

    return build(expr)


def _build_triangular_poly(
    expr: Expression,
    width_bits: int,
    const_poly,
    atom_poly,
    add_poly,
    mul_poly,
) -> Optional[TemplateBuildResult]:
    operands = _match_half_product(expr, target_size=max(expr.size or 0, width_bits // 8))
    if operands is None:
        return None

    left, right = operands
    left_const = _const_value_for_template(left, width_bits)
    right_const = _const_value_for_template(right, width_bits)
    if left_const is not None and right_const is not None:
        return const_poly((left_const * right_const) >> 1)

    left_affine = _match_expr_plus_const(left)
    right_affine = _match_expr_plus_const(right)
    if left_affine is None or right_affine is None:
        return atom_poly(_half_product_atom(left, right, width_bits))

    left_base, left_bias = left_affine
    right_base, right_bias = right_affine
    if not _same_nonconstant_expr(left_base, right_base):
        return atom_poly(_half_product_atom(left, right, width_bits))

    lower_bias = min(left_bias, right_bias)
    upper_bias = max(left_bias, right_bias)
    if upper_bias - lower_bias != 1:
        return atom_poly(_half_product_atom(left, right, width_bits))

    base_atom = _symbol_atom(left_base, width_bits)
    tri_atom = TemplateAtom("tri", base_atom.key)
    tri_poly = atom_poly(tri_atom)

    if lower_bias == 0:
        return tri_poly

    # Adjacent half-products shifted away from the canonical tri(base) shape are
    # not exact under bit-vector wraparound, so keep them as opaque atoms.
    return atom_poly(_half_product_atom(left, right, width_bits))


def _const_value_for_template(expr: Expression, width_bits: int) -> Optional[int]:
    modulus = 1 << width_bits

    if expr.expr_type == ExpressionType.CONSTANT:
        return int(expr.value) % modulus

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        inner = _const_value_for_template(expr.operands[0], width_bits)
        if inner is None:
            return None
        if expr.operator in {"INT_ZEXT", "INT_SEXT"}:
            # 拡張は被演算子の幅の値を伸ばす（SEXT は最上位 bit で埋める）
            operand_bits = int(expr.operands[0].get_bit_width() or 0)
            if 0 < operand_bits < width_bits:
                inner %= 1 << operand_bits
                if expr.operator == "INT_SEXT" and inner >> (operand_bits - 1):
                    inner = (inner - (1 << operand_bits)) % modulus
            return inner
        if expr.operator in {"INT_2COMP", "INT_NEGATE"}:
            return (-inner) % modulus
        return None

    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None

    left = _const_value_for_template(expr.operands[0], width_bits)
    right = _const_value_for_template(expr.operands[1], width_bits)
    if left is None or right is None:
        return None

    if expr.operator == "INT_ADD":
        return (left + right) % modulus
    if expr.operator == "INT_SUB":
        return (left - right) % modulus
    if expr.operator == "INT_MULT":
        return (left * right) % modulus
    if expr.operator in {"INT_RIGHT", "INT_SRIGHT"}:
        return left >> right if right >= 0 else None
    if expr.operator == "INT_AND":
        return left & right
    if expr.operator == "SUBPIECE" and right == 0:
        return left % modulus
    if expr.operator == "PIECE":
        low_bits = expr.operands[1].get_bit_width()
        return ((left << low_bits) | right) % modulus
    return None


def _strip_width_adapter(expr: Expression, target_bits: int) -> Expression:
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        # Issue #298: 拡張は、被演算子が目標の幅以上なら 2^target_bits の剰余で見えない（外してよい）。
        # 被演算子が狭いと ZEXT と SEXT の値が違うので外さない（外すと両者と、伸ばし方の分からない
        # 狭い値が同じ atom になる）
        if (
            expr.operator in {"INT_ZEXT", "INT_SEXT"}
            and expr.operands[0].get_bit_width() >= target_bits
        ):
            return expr.operands[0]
        return expr

    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return expr

    left, right = expr.operands
    if (
        expr.operator == "SUBPIECE"
        and right.expr_type == ExpressionType.CONSTANT
    ):
        byte_offset = int(right.value)
        if byte_offset == 0:
            return left
        if (
            left.expr_type == ExpressionType.BINARY_OP
            and left.operator == "PIECE"
            and len(left.operands) == 2
        ):
            high, low = left.operands
            if not high.size or not low.size:
                return expr
            low_size = low.size
            if byte_offset >= low_size:
                high_offset = byte_offset - low_size
                if high_offset == 0:
                    return high
                if high_offset > 0 and high_offset < high.size:
                    truncated = Expression.binary_op(
                        "SUBPIECE",
                        high,
                        Expression.constant(high_offset, size=4),
                    )
                    truncated.size = expr.size or max(1, target_bits // 8)
                    return truncated

    if expr.operator == "PIECE":
        low_bits = right.get_bit_width()
        if low_bits >= target_bits:
            return right

    if expr.operator in {"INT_RIGHT", "INT_SRIGHT"} and right.expr_type == ExpressionType.CONSTANT:
        shift_bits = int(right.value)
        if (
            left.expr_type == ExpressionType.BINARY_OP
            and left.operator == "PIECE"
            and len(left.operands) == 2
        ):
            high, low = left.operands
            if not high.size or not low.size:
                return expr
            low_bits = low.size * 8
            if shift_bits >= low_bits and shift_bits % 8 == 0:
                remaining_bits = shift_bits - low_bits
                if remaining_bits == 0:
                    return high
                shifted_high = Expression.binary_op(
                    expr.operator,
                    high,
                    Expression.constant(remaining_bits, size=right.size or 4),
                )
                shifted_high.size = expr.size or high.size
                return shifted_high

    return expr


def _symbol_atom(expr: Expression, width_bits: int) -> TemplateAtom:
    return TemplateAtom("sym", _expr_key(expr, width_bits))


def _half_product_atom(left: Expression, right: Expression, width_bits: int) -> TemplateAtom:
    left_key = _expr_key(left, width_bits)
    right_key = _expr_key(right, width_bits)
    if right_key < left_key:
        left_key, right_key = right_key, left_key
    return TemplateAtom("half", (left_key, right_key))


def _generic_atom(expr: Expression, width_bits: int) -> TemplateAtom:
    return TemplateAtom("expr", _expr_key(expr, width_bits))


def _expr_key(expr: Expression, width_bits: int) -> StructuralKey:
    normalized = normalize_expression(
        _normalize_expression_for_width(expr, width_bits),
        NormalizationContext(settings=SAFE_NORMALIZATION_SETTINGS),
    )
    # Issue #298 / #246: 拡張は ``_normalize_expression_for_width`` が目標の幅で見えないものだけを
    # 外す。key で全ての拡張を外す（lossy）と、ZEXT と SEXT（と伸ばし方の分からない狭い値）が同じ
    # atom になる
    return expression_key_or_identity(
        normalized,
        normalize_commutative=True,
        strip_width_adapters=False,
        collapse_full_masks=True,
        include_memory_read_order=False,
    )


def _normalize_expression_for_width(expr: Expression, width_bits: int) -> Expression:
    stripped = _strip_width_adapter(expr, width_bits)
    if stripped is not expr:
        return _normalize_expression_for_width(stripped, width_bits)

    if expr.expr_type == ExpressionType.CONSTANT:
        target_size = max(1, width_bits // 8)
        if expr.size != target_size:
            return Expression.constant(int(expr.value), size=target_size)
        return expr

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand = _normalize_expression_for_width(expr.operands[0], width_bits)
        if expr.operator in {"INT_2COMP", "INT_NEGATE"} and operand.expr_type == ExpressionType.CONSTANT:
            return Expression.constant(-int(operand.value), size=max(1, width_bits // 8))
        rebuilt = Expression.unary_op(expr.operator, operand)
        rebuilt.size = expr.size
        rebuilt.value = expr.value
        rebuilt.name = expr.name
        rebuilt.data_type = expr.data_type
        rebuilt.data_type_obj = getattr(expr, "data_type_obj", None)
        rebuilt.storage_info = expr.storage_info
        rebuilt.read_order_key = expr.read_order_key
        return rebuilt

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left = _normalize_expression_for_width(expr.operands[0], width_bits)
        right = _normalize_expression_for_width(expr.operands[1], width_bits)
        if expr.operator == "INT_ADD":
            if _is_zero_constant_for_width(left):
                return right
            if _is_zero_constant_for_width(right):
                return left
        if expr.operator == "INT_SUB" and _is_zero_constant_for_width(right):
            return left
        rebuilt = Expression.binary_op(expr.operator, left, right)
        rebuilt.size = expr.size
        rebuilt.value = expr.value
        rebuilt.name = expr.name
        rebuilt.data_type = expr.data_type
        rebuilt.data_type_obj = getattr(expr, "data_type_obj", None)
        rebuilt.storage_info = expr.storage_info
        rebuilt.read_order_key = expr.read_order_key
        second_strip = _strip_width_adapter(rebuilt, width_bits)
        if second_strip is not rebuilt:
            return _normalize_expression_for_width(second_strip, width_bits)
        collapsed = _collapse_affine_additive_constants(rebuilt, width_bits)
        if collapsed is not rebuilt and not _same_expression_key(collapsed, rebuilt):
            return _normalize_expression_for_width(collapsed, width_bits)
        return rebuilt

    return expr


def _is_zero_constant_for_width(expr: Expression) -> bool:
    return expr.expr_type == ExpressionType.CONSTANT and int(expr.value) == 0


def _collapse_affine_additive_constants(expr: Expression, width_bits: int) -> Expression:
    extracted = _extract_affine_base_and_const(expr)
    if extracted is None:
        return expr
    base_expr, const_value = extracted
    const_value %= 1 << width_bits
    target_size = max(1, width_bits // 8)
    if base_expr is None:
        return Expression.constant(const_value, size=target_size)
    if const_value == 0:
        return base_expr
    rebuilt = Expression.binary_op("INT_ADD", base_expr, Expression.constant(const_value, size=target_size))
    rebuilt.size = max(base_expr.size, target_size)
    return rebuilt


def _extract_affine_base_and_const(expr: Expression) -> Optional[Tuple[Optional[Expression], int]]:
    if expr.expr_type == ExpressionType.CONSTANT:
        return None, int(expr.value)

    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return expr, 0

    if expr.operator not in {"INT_ADD", "INT_SUB"}:
        return expr, 0

    left = _extract_affine_base_and_const(expr.operands[0])
    right = _extract_affine_base_and_const(expr.operands[1])
    if left is None or right is None:
        return None

    left_base, left_const = left
    right_base, right_const = right
    if expr.operator == "INT_SUB":
        right_const = -right_const
        if right_base is not None:
            return None

    if left_base is None:
        return right_base, left_const + right_const
    if right_base is None:
        return left_base, left_const + right_const
    if _same_expression_key(left_base, right_base):
        doubled = Expression.binary_op("INT_ADD", left_base, right_base)
        doubled.size = max(left_base.size, right_base.size, 4)
        return doubled, left_const + right_const
    return None


def _same_expression_key(left: Expression, right: Expression) -> bool:
    return expression_key_or_identity(left, normalize_commutative=True) == expression_key_or_identity(
        right,
        normalize_commutative=True,
    )
