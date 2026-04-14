# -*- coding: utf-8 -*-
"""Pairwise fallback with exact loop-template abstraction."""

from __future__ import annotations

from typing import Any, Dict, Iterable
from copy import deepcopy

from ..loop_template_abstraction import prove_template_equivalence
from ..normalize.context import NormalizationContext
from ..normalize.core import normalize_expression
from ...model import Condition, Expression, ExpressionType
from .pairwise import PairwiseStrategy
from .pairwise_models import QueryResult, ReturnCase


class LoopTemplatePairwiseStrategy(PairwiseStrategy):
    """A heavier but exact pairwise fallback for loop-derived closed forms.

    This strategy preserves the existing pairwise control-flow reasoning and
    SMT-based condition checks, but replaces unresolved value comparisons with an
    exact algebraic template proof when possible.
    """

    def _try_normalization_equivalence(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str,
    ) -> QueryResult:
        base_result = super()._try_normalization_equivalence(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )
        if base_result.is_equivalent is not None:
            return base_result

        target_bits = min(
            int(base_ctx.get("return_size1", case1.value_expr.get_bit_width()) or 0),
            int(base_ctx.get("return_size2", case2.value_expr.get_bit_width()) or 0),
        )
        if target_bits <= 0:
            return base_result

        template_value1, template_value2 = _normalize_values_under_exact_conditions(
            case1.value_expr,
            case2.value_expr,
            list(case1.conditions) + list(case2.conditions),
        )
        proved, reason = prove_template_equivalence(
            template_value1,
            template_value2,
            target_bits=target_bits,
            debug=self.debug,
        )
        if not proved:
            if self.debug:
                self._debug_print(
                    f"    Loop-template abstraction did not prove equivalence for pair {pair_id}: {reason}"
                )
            return base_result

        self._debug_print(
            f"    Loop-template abstraction proved pair {pair_id} equivalent: {reason}"
        )
        result = QueryResult(is_equivalent=True)
        result.last_query = base_result.last_query
        result.normalization_rules = list(base_result.normalization_rules)
        return result


def _normalize_values_under_exact_conditions(
    value1: Expression,
    value2: Expression,
    conditions: Iterable[Condition],
) -> tuple[Expression, Expression]:
    replacements = _extract_exact_constant_replacements(conditions)
    if not replacements:
        return value1, value2

    normalized1 = normalize_expression(
        _substitute_exact_replacements(value1, replacements),
        NormalizationContext(),
    )
    normalized2 = normalize_expression(
        _substitute_exact_replacements(value2, replacements),
        NormalizationContext(),
    )
    return normalized1, normalized2


def _extract_exact_constant_replacements(
    conditions: Iterable[Condition],
) -> dict[str, Expression]:
    replacements: dict[str, Expression] = {}
    conflicts: set[str] = set()
    for condition in conditions:
        if condition is None or condition.negated:
            continue
        expr = condition.expression
        if (
            expr.expr_type != ExpressionType.BINARY_OP
            or expr.operator != "INT_EQUAL"
            or len(expr.operands) != 2
        ):
            continue

        left, right = expr.operands
        symbol = _extract_replacement_symbol(left)
        constant = _extract_replacement_constant(right)
        if symbol is None or constant is None:
            symbol = _extract_replacement_symbol(right)
            constant = _extract_replacement_constant(left)
        if symbol is None or constant is None:
            continue

        existing = replacements.get(symbol)
        if existing is not None and existing.to_smt() != constant.to_smt():
            conflicts.add(symbol)
            replacements.pop(symbol, None)
            continue
        if symbol not in conflicts:
            replacements[symbol] = constant

    return replacements


def _extract_replacement_symbol(expr: Expression) -> str | None:
    current = expr
    while current.expr_type == ExpressionType.UNARY_OP and current.operands:
        if current.operator not in {"INT_ZEXT", "INT_SEXT"}:
            break
        current = current.operands[0]

    if (
        current.expr_type == ExpressionType.BINARY_OP
        and current.operator == "SUBPIECE"
        and len(current.operands) == 2
        and current.operands[1].expr_type == ExpressionType.CONSTANT
        and int(current.operands[1].value) == 0
    ):
        current = current.operands[0]

    if current.expr_type not in {
        ExpressionType.PARAMETER,
        ExpressionType.VARIABLE,
        ExpressionType.LITERAL,
    }:
        return None
    return current.name


def _extract_replacement_constant(expr: Expression) -> Expression | None:
    value = _const_value(expr)
    if value is None:
        return None
    return Expression.constant(value, size=expr.size or 4)


def _substitute_exact_replacements(
    expr: Expression,
    replacements: dict[str, Expression],
) -> Expression:
    if expr.expr_type in {
        ExpressionType.PARAMETER,
        ExpressionType.VARIABLE,
        ExpressionType.LITERAL,
    }:
        replacement = replacements.get(expr.name)
        if replacement is None:
            return expr
        cloned = deepcopy(replacement)
        if expr.size and cloned.size != expr.size:
            cloned.size = expr.size
        return cloned

    if expr.expr_type == ExpressionType.PHI and expr.value:
        rebuilt_branches = []
        for condition, value in expr.value:
            rebuilt_branches.append(
                (
                    Condition(
                        _substitute_exact_replacements(condition.expression, replacements),
                        condition.negated,
                    ),
                    _substitute_exact_replacements(value, replacements),
                )
            )
        rebuilt = Expression.phi(rebuilt_branches)
        rebuilt.size = expr.size
        rebuilt.name = expr.name
        rebuilt.data_type = expr.data_type
        rebuilt.storage_info = expr.storage_info
        rebuilt.read_order_key = expr.read_order_key
        return rebuilt

    if not expr.operands:
        return expr

    rebuilt = Expression(
        expr_type=expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=[
            _substitute_exact_replacements(operand, replacements)
            for operand in expr.operands
        ],
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
    )
    return rebuilt


def _const_value(expr: Expression) -> int | None:
    if expr.expr_type == ExpressionType.CONSTANT:
        return int(expr.value)

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        inner = _const_value(expr.operands[0])
        if inner is None:
            return None
        if expr.operator in {"INT_ZEXT", "INT_SEXT"}:
            return inner
        if expr.operator in {"INT_2COMP", "INT_NEGATE"}:
            return -inner
        return None

    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None

    left = _const_value(expr.operands[0])
    right = _const_value(expr.operands[1])
    if left is None or right is None:
        return None

    if expr.operator == "INT_ADD":
        return left + right
    if expr.operator == "INT_SUB":
        return left - right
    if expr.operator == "INT_MULT":
        return left * right
    if expr.operator in {"INT_RIGHT", "INT_SRIGHT"}:
        return left >> right if right >= 0 else None
    if expr.operator == "INT_AND":
        return left & right
    if expr.operator == "SUBPIECE" and right == 0:
        return left
    return None
