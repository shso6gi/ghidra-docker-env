"""Equivalence under conditions, alias representatives, boolean simplification and parameter equalities."""

from __future__ import annotations

from typing import Dict, FrozenSet, List, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    expression_key_safe,
)
from scripts.function_tracer_pcode.analysis.effects._shared import (
    ConditionSimplifier,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _additive_signature,
    _apply_condition_parameter_replacements,
    _clone_expression_with_operands,
    _expression_matches_value_under_conditions,
    _expression_truth_value,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
    _extract_positive_param_equality_pair,
    _flatten_location_addition,
    _location_sort_key,
    _parameter_base_ref_matches_descriptor,
    _parameter_like_identity,
    _reduce_expression_under_conditions,
    _runtime_expression_signature,
    _strip_materialized_post_state_value_refs,
    locations_match,
    subtract_implied_conditions,
)


def _impl__expression_matches_value_under_conditions(
    expr: Expression,
    value: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> bool:
    reduced_expr = _reduce_expression_under_conditions(expr, conditions)
    reduced_value = _reduce_expression_under_conditions(value, conditions)
    if _expressions_equivalent_under_conditions(reduced_expr, reduced_value, conditions, parameters):
        return True
    if reduced_value.expr_type != ExpressionType.PHI or not reduced_value.value:
        return False
    for cond, branch_value in reduced_value.value:
        combined = list(conditions)
        if cond is not None:
            combined.append(cond)
        if ConditionSimplifier.object_centric_is_contradiction(combined):
            continue
        if _expression_matches_value_under_conditions(reduced_expr, branch_value, combined, parameters):
            return True
    return False


def _impl__expressions_equivalent(left: Optional[Expression], right: Optional[Expression]) -> bool:
    if left is right:
        return True
    if left is None or right is None:
        return False
    left_key = expression_key_safe(left, include_memory_read_order=True)
    right_key = expression_key_safe(right, include_memory_read_order=True)
    if left_key is None or right_key is None:
        return False
    return left_key == right_key


def _impl__additive_signature(expr: Optional[Expression]) -> Optional[Tuple[int, Tuple[Tuple[object, int], ...], int]]:
    if expr is None:
        return None

    bit_width = int(getattr(expr, "size", 0) or 0)
    modulus = 1 << bit_width if bit_width > 0 else None
    term_counts: Dict[object, int] = {}
    const_value = 0

    def visit(node: Expression, sign: int) -> bool:
        nonlocal const_value, bit_width, modulus
        if node is None:
            return False
        node_bits = int(getattr(node, "size", 0) or 0)
        if node_bits > bit_width:
            bit_width = node_bits
            modulus = 1 << bit_width if bit_width > 0 else None

        if node.expr_type == ExpressionType.CONSTANT:
            value = int(node.value)
            const_value = const_value + (sign * value)
            if modulus is not None:
                const_value %= modulus
            return True

        if node.expr_type == ExpressionType.UNARY_OP and node.operands:
            if node.operator in {"INT_2COMP", "INT_NEGATE"}:
                return visit(node.operands[0], -sign)
            return False

        if node.expr_type == ExpressionType.BINARY_OP and len(node.operands) == 2:
            if node.operator == "INT_ADD":
                return visit(node.operands[0], sign) and visit(node.operands[1], sign)
            if node.operator == "INT_SUB":
                return visit(node.operands[0], sign) and visit(node.operands[1], -sign)

        key = _runtime_expression_signature(node)
        term_counts[key] = term_counts.get(key, 0) + sign
        if term_counts[key] == 0:
            term_counts.pop(key, None)
        return True

    if not visit(expr, 1):
        return None

    if modulus is not None:
        const_value %= modulus
    terms = tuple(sorted((key, coeff) for key, coeff in term_counts.items() if coeff))
    return const_value, terms, bit_width


def _impl__expressions_equivalent_under_conditions(
    left: Optional[Expression],
    right: Optional[Expression],
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> bool:
    if _expressions_equivalent(left, right):
        return True

    left_unwrapped = _strip_materialized_post_state_value_refs(left)
    right_unwrapped = _strip_materialized_post_state_value_refs(right)
    if left_unwrapped is not left or right_unwrapped is not right:
        if _expressions_equivalent(left_unwrapped, right_unwrapped):
            return True

    left_rewritten = _apply_condition_parameter_replacements(left_unwrapped, conditions, parameters)
    right_rewritten = _apply_condition_parameter_replacements(right_unwrapped, conditions, parameters)
    if _expressions_equivalent(left_rewritten, right_rewritten):
        return True

    left_sig = _additive_signature(left_rewritten)
    right_sig = _additive_signature(right_rewritten)
    if left_sig is None or right_sig is None:
        return False
    return left_sig == right_sig


def _impl__build_alias_representative_map(
    locations: Sequence[CanonicalLocation],
    conditions: Sequence[Condition],
) -> Dict[CanonicalLocation, CanonicalLocation]:
    groups: List[List[CanonicalLocation]] = []
    for location in sorted(set(locations), key=_location_sort_key):
        placed = False
        for group in groups:
            head = group[0]
            if head.size != location.size:
                continue
            if locations_match(location, head, conditions):
                group.append(location)
                placed = True
                break
        if not placed:
            groups.append([location])

    representatives: Dict[CanonicalLocation, CanonicalLocation] = {}
    for group in groups:
        representative = min(group, key=_location_sort_key)
        for member in group:
            representatives[member] = representative
    return representatives


def _impl__resolve_alias_representative(
    location: CanonicalLocation,
    alias_representatives: Dict[CanonicalLocation, CanonicalLocation],
    conditions: Sequence[Condition],
) -> Optional[CanonicalLocation]:
    representative = alias_representatives.get(location)
    if representative is not None:
        return representative
    for candidate, candidate_rep in alias_representatives.items():
        if candidate.size != location.size:
            continue
        if locations_match(location, candidate, conditions):
            return candidate_rep
    return None


def _impl__reduce_expression_under_conditions(
    expr: Expression,
    conditions: Sequence[Condition],
) -> Expression:
    if expr is None:
        return expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is None:
                continue
            combined = list(conditions) + [cond]
            if ConditionSimplifier.is_contradiction(combined):
                continue
            if not subtract_implied_conditions([cond], conditions):
                return _reduce_expression_under_conditions(value, combined)

        surviving = []
        for cond, value in expr.value:
            combined = list(conditions)
            if cond is not None:
                combined.append(cond)
            if ConditionSimplifier.is_contradiction(combined):
                continue
            reduced_value = _reduce_expression_under_conditions(value, combined)
            surviving.append((cond, reduced_value))

        if not surviving:
            return expr
        if len(surviving) == 1:
            return surviving[0][1]

        rebuilt = Expression.phi(surviving)
        rebuilt.size = expr.size
        return rebuilt

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.INTRINSIC, ExpressionType.MEMORY):
        new_operands = [_reduce_expression_under_conditions(op, conditions) for op in expr.operands]
        return _clone_expression_with_operands(expr, new_operands) if not all(
            new is old for new, old in zip(new_operands, expr.operands)
        ) else expr

    return expr


def _impl_subtract_implied_conditions(
    effect_conditions: Sequence[Condition],
    return_conditions: Sequence[Condition],
) -> List[Condition]:
    context_basis = ConditionSimplifier.simplify_conditions_object_centric(
        list(return_conditions or [])
    )
    residual: List[Condition] = []
    for condition in ConditionSimplifier.simplify_conditions_object_centric(
        list(effect_conditions or [])
    ):
        if any(condition.equals(existing) for existing in context_basis):
            continue
        if ConditionSimplifier.object_centric_is_contradiction(
            context_basis + [condition.negate()]
        ):
            continue
        residual.append(condition)
    return residual


def _impl__simplify_boolean_binary_expression(
    operator: str,
    left: Expression,
    right: Expression,
) -> Optional[Expression]:
    left_truth = _expression_truth_value(left)
    right_truth = _expression_truth_value(right)

    if operator == "BOOL_AND":
        if left_truth is False or right_truth is False:
            return Expression.constant(0, size=1)
        if left_truth is True:
            return right
        if right_truth is True:
            return left
        return None

    if operator == "BOOL_OR":
        if left_truth is True or right_truth is True:
            return Expression.constant(1, size=1)
        if left_truth is False:
            return right
        if right_truth is False:
            return left
        return None

    if operator == "BOOL_XOR":
        if left_truth is not None and right_truth is not None:
            return Expression.constant(1 if left_truth ^ right_truth else 0, size=1)
        if left_truth is False:
            return right
        if right_truth is False:
            return left
        if left_truth is True:
            return Expression.unary_op("BOOL_NEGATE", right)
        if right_truth is True:
            return Expression.unary_op("BOOL_NEGATE", left)

    return None


def _impl__collect_param_equalities(
    conditions: Sequence[Condition],
) -> Set[FrozenSet[Tuple[object, ...]]]:
    equalities: Set[FrozenSet[Tuple[object, ...]]] = set()
    for condition in conditions:
        pair = _extract_positive_param_equality_pair(condition)
        if pair is not None:
            equalities.add(pair)
    return equalities


def _impl__extract_positive_param_equality_pair(
    condition: Optional[Condition],
) -> Optional[FrozenSet[Tuple[object, ...]]]:
    if condition is None:
        return None

    expr = condition.expression
    negated = bool(condition.negated)
    while (
        expr is not None
        and expr.expr_type == ExpressionType.UNARY_OP
        and expr.operator == "BOOL_NEGATE"
        and expr.operands
    ):
        negated = not negated
        expr = expr.operands[0]

    if (
        expr is None
        or expr.expr_type != ExpressionType.BINARY_OP
        or len(expr.operands) != 2
        or expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}
    ):
        return None

    is_positive = (expr.operator == "INT_EQUAL" and not negated) or (
        expr.operator == "INT_NOTEQUAL" and negated
    )
    if not is_positive:
        return None

    left_key = _parameter_like_identity(expr.operands[0])
    right_key = _parameter_like_identity(expr.operands[1])
    if left_key is None or right_key is None:
        return None
    return frozenset((left_key, right_key))


def _impl__flatten_param_addition(
    expr: Expression,
    parameters: Sequence[Dict],
) -> Tuple[Optional[int], List[LocationBaseRef]]:
    const_total, bases = _flatten_location_addition(expr, parameters)
    if const_total is None:
        return None, []
    if not all(
        base.is_parameter()
        and any(_parameter_base_ref_matches_descriptor(base, param) for param in parameters)
        for base in bases
    ):
        return None, []
    return const_total, bases


def _impl__has_overlapping_guards(matched: Sequence[Tuple[int, List[Condition], Expression]]) -> bool:
    for i in range(len(matched)):
        for j in range(i + 1, len(matched)):
            residual_i = list(matched[i][1])
            residual_j = list(matched[j][1])
            if not residual_i or not residual_j:
                return True
            if not ConditionSimplifier.is_contradiction(residual_i + residual_j):
                return True
    return False


def _impl__all_residual_guards_empty(matched: Sequence[Tuple[int, List[Condition], Expression]]) -> bool:
    return all(not list(residual) for _order, residual, _value in matched)
