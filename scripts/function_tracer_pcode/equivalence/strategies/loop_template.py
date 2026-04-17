# -*- coding: utf-8 -*-
"""Pairwise fallback with exact loop-template abstraction."""

from __future__ import annotations

from typing import Any, Dict, Iterable
from copy import deepcopy

from ..loop_template_abstraction import prove_template_equivalence
from ..normalize.context import NormalizationContext
from ..normalize.core import normalize_expression
from ..normalize.facts import extract_sign_facts
from ...model import Condition, Expression, ExpressionType, expression_key_or_identity
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
    replacements, expr_replacements = _extract_exact_constant_replacements(conditions)
    sign_facts = extract_sign_facts(list(conditions), debug=False)
    norm_context = NormalizationContext(
        nonneg_vars=set(sign_facts.nonneg_vars),
        pos_vars=set(sign_facts.pos_vars),
        neg_vars=set(sign_facts.neg_vars),
        nonzero_vars=set(sign_facts.nonzero_vars),
        nonneg_exprs=set(sign_facts.nonneg_exprs),
        pos_exprs=set(sign_facts.pos_exprs),
        neg_exprs=set(sign_facts.neg_exprs),
        nonzero_exprs=set(sign_facts.nonzero_exprs),
        upper_bounds=dict(sign_facts.upper_bounds),
    )
    if not replacements and not expr_replacements:
        return (
            normalize_expression(value1, norm_context),
            normalize_expression(value2, norm_context),
        )

    normalized1 = normalize_expression(
        _substitute_exact_replacements(value1, replacements, expr_replacements),
        norm_context,
    )
    normalized2 = normalize_expression(
        _substitute_exact_replacements(value2, replacements, expr_replacements),
        norm_context,
    )
    return normalized1, normalized2


def _extract_exact_constant_replacements(
    conditions: Iterable[Condition],
) -> tuple[dict[str, Expression], dict[tuple, Expression]]:
    replacements: dict[str, Expression] = {}
    expr_replacements: dict[tuple, Expression] = {}
    conflicts: set[str] = set()
    expr_conflicts: set[tuple] = set()
    expr_fact_exprs: dict[tuple, Expression] = {}

    normalized_conditions = [
        _normalize_exact_fact_condition(condition) for condition in conditions
    ]

    for condition in normalized_conditions:
        if condition is None:
            continue
        for fact_expr, constant in _extract_expr_constant_facts(condition.expression):
            expr_key = _expr_key(fact_expr)
            if expr_key is None:
                continue
            existing = expr_replacements.get(expr_key)
            if existing is not None and expression_key_or_identity(existing) != expression_key_or_identity(constant):
                expr_conflicts.add(expr_key)
                expr_replacements.pop(expr_key, None)
                expr_fact_exprs.pop(expr_key, None)
                continue
            if expr_key not in expr_conflicts:
                expr_replacements[expr_key] = constant
                expr_fact_exprs[expr_key] = fact_expr

    changed = True
    while changed:
        changed = False
        for expr_key, constant in list(expr_replacements.items()):
            fact_expr = expr_fact_exprs.get(expr_key)
            if fact_expr is None:
                continue
            symbol = _extract_replacement_symbol(fact_expr)
            if symbol is not None and symbol not in conflicts:
                existing = replacements.get(symbol)
                if existing is None:
                    replacements[symbol] = constant
                    changed = True
                elif expression_key_or_identity(existing) != expression_key_or_identity(constant):
                    conflicts.add(symbol)
                    replacements.pop(symbol, None)
                    changed = True

        for condition in normalized_conditions:
            if condition is None:
                continue
            derived = _derive_symbol_replacement_from_condition(
                condition.expression,
                replacements,
                expr_replacements,
            )
            if derived is None:
                continue
            symbol, constant = derived
            if symbol in conflicts:
                continue
            existing = replacements.get(symbol)
            if existing is None:
                replacements[symbol] = constant
                changed = True
                continue
            if expression_key_or_identity(existing) != expression_key_or_identity(constant):
                conflicts.add(symbol)
                replacements.pop(symbol, None)
                changed = True

    for conflict in conflicts:
        replacements.pop(conflict, None)

    return replacements, expr_replacements


def _normalize_exact_fact_condition(condition: Condition | None) -> Condition | None:
    if condition is None:
        return None
    if not condition.negated:
        return condition

    expr = condition.expression
    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and len(expr.operands) == 2
    ):
        if expr.operator == "INT_NOTEQUAL":
            rewritten = Expression.binary_op("INT_EQUAL", expr.operands[0], expr.operands[1])
            rewritten.size = expr.size
            return Condition(rewritten, False)
        if expr.operator == "INT_EQUAL":
            rewritten = Expression.binary_op("INT_NOTEQUAL", expr.operands[0], expr.operands[1])
            rewritten.size = expr.size
            return Condition(rewritten, False)

    return condition


def _extract_expr_constant_facts(
    expr: Expression,
) -> list[tuple[Expression, Expression]]:
    if (
        expr.expr_type != ExpressionType.BINARY_OP
        or expr.operator != "INT_EQUAL"
        or len(expr.operands) != 2
    ):
        return []

    left, right = expr.operands
    facts: list[tuple[Expression, Expression]] = []
    facts.extend(_extract_side_equals_constant(left, right))
    facts.extend(_extract_side_equals_constant(right, left))
    return facts


def _extract_side_equals_constant(
    side: Expression,
    other: Expression,
) -> list[tuple[Expression, Expression]]:
    constant = _extract_replacement_constant(other)
    if constant is None:
        return []

    facts: list[tuple[Expression, Expression]] = [(side, constant)]
    if (
        side.expr_type == ExpressionType.BINARY_OP
        and len(side.operands) == 2
        and side.operator in {"INT_ADD", "INT_SUB"}
    ):
        left, right = side.operands
        right_const = _extract_replacement_constant(right)
        left_const = _extract_replacement_constant(left)
        if side.operator == "INT_ADD":
            if right_const is not None:
                facts.append((left, Expression.constant(int(constant.value) - int(right_const.value), size=constant.size)))
            if left_const is not None:
                facts.append((right, Expression.constant(int(constant.value) - int(left_const.value), size=constant.size)))
        if side.operator == "INT_SUB":
            if right_const is not None:
                facts.append((left, Expression.constant(int(constant.value) + int(right_const.value), size=constant.size)))
            if left_const is not None:
                facts.append((right, Expression.constant(int(left_const.value) - int(constant.value), size=constant.size)))
    return facts


def _derive_symbol_replacement_from_condition(
    expr: Expression,
    replacements: dict[str, Expression],
    expr_replacements: dict[tuple, Expression],
) -> tuple[str, Expression] | None:
    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_EQUAL"
        and len(expr.operands) == 2
    ):
        left, right = expr.operands
        left_symbol = _extract_replacement_symbol(left)
        right_symbol = _extract_replacement_symbol(right)
        left_known = _lookup_known_constant(left, replacements, expr_replacements)
        right_known = _lookup_known_constant(right, replacements, expr_replacements)
        if left_symbol is not None and right_known is not None:
            return left_symbol, right_known
        if right_symbol is not None and left_known is not None:
            return right_symbol, left_known
    for fact_expr, constant in _extract_expr_constant_facts(expr):
        derived = _derive_symbol_replacement_from_fact(
            fact_expr,
            constant,
            replacements,
            expr_replacements,
        )
        if derived is not None:
            return derived
    return None


def _derive_symbol_replacement_from_fact(
    fact_expr: Expression,
    constant: Expression,
    replacements: dict[str, Expression],
    expr_replacements: dict[tuple, Expression],
) -> tuple[str, Expression] | None:
    if (
        fact_expr.expr_type != ExpressionType.BINARY_OP
        or len(fact_expr.operands) != 2
        or fact_expr.operator not in {"INT_ADD", "INT_SUB"}
    ):
        return None

    left, right = fact_expr.operands
    left_symbol = _extract_replacement_symbol(left)
    right_symbol = _extract_replacement_symbol(right)
    left_known = _lookup_known_constant(left, replacements, expr_replacements)
    right_known = _lookup_known_constant(right, replacements, expr_replacements)

    if fact_expr.operator == "INT_SUB":
        if left_symbol is not None and right_known is not None:
            return (
                left_symbol,
                Expression.constant(
                    int(constant.value) + int(right_known.value),
                    size=constant.size or right_known.size or 4,
                ),
            )
        if right_symbol is not None and left_known is not None:
            return (
                right_symbol,
                Expression.constant(
                    int(left_known.value) - int(constant.value),
                    size=left_known.size or constant.size or 4,
                ),
            )

    if fact_expr.operator == "INT_ADD":
        if left_symbol is not None and right_known is not None:
            return (
                left_symbol,
                Expression.constant(
                    int(constant.value) - int(right_known.value),
                    size=constant.size or right_known.size or 4,
                ),
            )
        if right_symbol is not None and left_known is not None:
            return (
                right_symbol,
                Expression.constant(
                    int(constant.value) - int(left_known.value),
                    size=constant.size or left_known.size or 4,
                ),
            )
    return None


def _lookup_known_constant(
    expr: Expression,
    replacements: dict[str, Expression],
    expr_replacements: dict[tuple, Expression],
) -> Expression | None:
    symbol = _extract_replacement_symbol(expr)
    if symbol is not None:
        replacement = replacements.get(symbol)
        if replacement is not None:
            return replacement
    expr_key = _expr_key(expr)
    if expr_key is None:
        return None
    return expr_replacements.get(expr_key)


def _expr_key(expr: Expression) -> tuple | None:
    try:
        normalized = normalize_expression(expr, NormalizationContext())
        return expression_key_or_identity(
            normalized,
            normalize_commutative=True,
            strip_width_adapters=True,
            collapse_full_masks=True,
        )
    except Exception:
        try:
            return expression_key_or_identity(
                expr,
                normalize_commutative=True,
                strip_width_adapters=True,
                collapse_full_masks=True,
            )
        except Exception:
            return None


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
    expr_replacements: dict[tuple, Expression],
) -> Expression:
    expr_key = _expr_key(expr)
    if expr_key is not None:
        replacement = expr_replacements.get(expr_key)
        if replacement is not None:
            cloned = deepcopy(replacement)
            if expr.size and cloned.size != expr.size:
                cloned.size = expr.size
            return cloned

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
                        _substitute_exact_replacements(
                            condition.expression,
                            replacements,
                            expr_replacements,
                        ),
                        condition.negated,
                    ),
                    _substitute_exact_replacements(
                        value,
                        replacements,
                        expr_replacements,
                    ),
                )
            )
        rebuilt = Expression.phi(rebuilt_branches)
        rebuilt.size = expr.size
        rebuilt.name = expr.name
        rebuilt.data_type = expr.data_type
        rebuilt.data_type_obj = getattr(expr, "data_type_obj", None)
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
            _substitute_exact_replacements(
                operand,
                replacements,
                expr_replacements,
            )
            for operand in expr.operands
        ],
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        opcode=getattr(expr, "opcode", None),
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
        runtime_ref=getattr(expr, "runtime_ref", None),
    )
    rebuilt_key = _expr_key(rebuilt)
    if rebuilt_key is not None:
        replacement = expr_replacements.get(rebuilt_key)
        if replacement is not None:
            cloned = deepcopy(replacement)
            if rebuilt.size and cloned.size != rebuilt.size:
                cloned.size = rebuilt.size
            return cloned
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
