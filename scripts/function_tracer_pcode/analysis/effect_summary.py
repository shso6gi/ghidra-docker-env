# -*- coding: utf-8 -*-
"""Simple parameter-derived memory effect summaries."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Set, Tuple

from ..model import Condition, Expression, ExpressionType
from .condition import ConditionSimplifier
from .condition.normalizer import ConditionNormalizer


@dataclass(frozen=True)
class CanonicalLocation:
    base_param: str
    offset: int
    size: int


@dataclass
class StoreEffect:
    location: CanonicalLocation
    value: Expression
    conditions: List[Condition]
    order_key: int


@dataclass
class EffectSummary:
    parameter_names: List[str]
    effects: List[StoreEffect]
    synthetic_expr: Optional[Expression] = None
    has_unsupported_call: bool = False


def summarize_store_effects(
    block_infos: Iterable,
    tracer,
    condition_tracker,
    parameters: Sequence[Dict],
    direct_call_summary: Optional[Callable[[str, Sequence[Expression]], Optional["EffectSummary"]]] = None,
    debug: bool = False,
) -> EffectSummary:
    parameter_names = [param.get("name") for param in parameters if param.get("name")]
    effects: List[StoreEffect] = []
    has_unsupported_call = False

    for block_info in block_infos:
        path_sets = condition_tracker.get_all_valid_paths_to_block(block_info)
        if not path_sets:
            path_sets = [[]]

        for op in block_info.pcode_ops:
            mnemonic = op.getMnemonic()

            if mnemonic == "STORE" and op.getNumInputs() >= 3:
                addr_expr = tracer.trace_varnode(op.getInput(1), use_cache=False)
                value_expr = tracer.trace_varnode(op.getInput(2), use_cache=False)
                location = canonicalize_param_location(addr_expr, parameters, size=op.getInput(2).getSize())
                if location is None:
                    continue
                for path_conditions in path_sets:
                    simplified = ConditionSimplifier.simplify_conditions(path_conditions)
                    effects.append(
                        StoreEffect(
                            location=location,
                            value=value_expr,
                            conditions=simplified,
                            order_key=_get_order_key(op),
                        )
                    )
                continue

            if mnemonic not in {"CALL", "CALLIND"} or direct_call_summary is None or op.getNumInputs() < 1:
                continue

            target_name = _resolve_call_target_name(tracer, op)
            if not target_name:
                has_unsupported_call = True
                continue
            args = [
                tracer.trace_varnode(op.getInput(i), use_cache=False)
                for i in range(1, op.getNumInputs())
            ]
            callee_summary = direct_call_summary(target_name, args)
            if callee_summary is None or not is_call_effect_summary_allowed(callee_summary):
                has_unsupported_call = True
                continue

            for effect in callee_summary.effects:
                substituted_location = substitute_location(effect.location, callee_summary.parameter_names, args, parameters)
                if substituted_location is None:
                    continue
                substituted_value = substitute_expression(effect.value, dict(zip(callee_summary.parameter_names, args)))
                substituted_conditions = [
                    substitute_condition(cond, dict(zip(callee_summary.parameter_names, args)))
                    for cond in effect.conditions
                ]
                for path_conditions in path_sets:
                    merged_conditions = ConditionSimplifier.simplify_conditions(
                        list(path_conditions) + substituted_conditions
                    )
                    effects.append(
                        StoreEffect(
                            location=substituted_location,
                            value=substituted_value,
                            conditions=merged_conditions,
                            order_key=_get_order_key(op),
                        )
                    )

    synthetic_expr = build_void_effect_summary_expr(effects)
    if debug:
        print(
            f"[EffectSummary] collected {len(effects)} effects "
            f"for params={parameter_names}"
        )
    return EffectSummary(
        parameter_names=parameter_names,
        effects=effects,
        synthetic_expr=synthetic_expr,
        has_unsupported_call=has_unsupported_call,
    )


def _resolve_call_target_name(tracer, op) -> Optional[str]:
    if op.getNumInputs() < 1:
        return None

    target_varnode = op.getInput(0)
    mnemonic = op.getMnemonic()
    if mnemonic == "CALL":
        target_name = tracer._get_function_name(target_varnode)
        return None if target_name == "UNKNOWN_FUNC" else target_name

    if mnemonic != "CALLIND":
        return None

    target_name = tracer._get_function_name(target_varnode)
    if target_name != "UNKNOWN_FUNC":
        return target_name

    traced_target = tracer.trace_varnode(target_varnode, use_cache=False)
    if traced_target.expr_type != ExpressionType.CONSTANT or not isinstance(traced_target.value, int):
        return None

    try:
        default_space = tracer.program.getAddressFactory().getDefaultAddressSpace()
        addr = default_space.getAddress(traced_target.value)
        func = tracer.program.getFunctionManager().getFunctionAt(addr)
        if func:
            return func.getName()
    except Exception:
        return None

    return None


def is_call_effect_summary_allowed(summary: EffectSummary) -> bool:
    if summary is None:
        return False
    if summary.has_unsupported_call:
        return False
    if not summary.effects:
        return False

    for effect in summary.effects:
        if not _expression_is_call_scope_safe(effect.value):
            return False
        for condition in effect.conditions:
            if not _expression_is_call_scope_safe(condition.expression):
                return False

    if summary.synthetic_expr is not None and not _expression_is_call_scope_safe(summary.synthetic_expr):
        return False
    if _summary_has_interdependent_writes(summary):
        return False

    return True


def _expression_is_call_scope_safe(expr: Optional[Expression]) -> bool:
    if expr is None:
        return True

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type in (expr_kind.CALL, expr_kind.UNKNOWN):
        return False

    if expr_type == expr_kind.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and not _expression_is_call_scope_safe(cond.expression):
                return False
            if not _expression_is_call_scope_safe(value):
                return False
        return True

    for operand in getattr(expr, "operands", []) or []:
        if not _expression_is_call_scope_safe(operand):
            return False

    return True


def _summary_has_interdependent_writes(summary: EffectSummary) -> bool:
    if summary is None or len(summary.effects) <= 1:
        return False

    params = [{"name": name} for name in summary.parameter_names]
    for index, effect in enumerate(summary.effects):
        for other_index, other in enumerate(summary.effects):
            if index == other_index:
                continue
            if effect.location == other.location:
                continue
            if _expression_reads_location(effect.value, other.location, effect.conditions, params):
                return True
    return False


def canonicalize_param_location(
    addr_expr: Expression,
    parameters: Sequence[Dict],
    size: int = 4,
) -> Optional[CanonicalLocation]:
    const_total, bases = _flatten_param_addition(addr_expr)
    if const_total is None or len(bases) != 1:
        return None

    base_name = bases[0]
    if not any(param.get("name") == base_name for param in parameters):
        return None

    return CanonicalLocation(base_param=base_name, offset=const_total, size=size)


def substitute_location(
    location: CanonicalLocation,
    callee_params: Sequence[str],
    call_args: Sequence[Expression],
    caller_params: Sequence[Dict],
) -> Optional[CanonicalLocation]:
    arg_map = dict(zip(callee_params, call_args))
    actual_addr = arg_map.get(location.base_param)
    if actual_addr is None:
        return None
    caller_location = canonicalize_param_location(actual_addr, caller_params, size=location.size)
    if caller_location is None:
        return None
    return CanonicalLocation(
        base_param=caller_location.base_param,
        offset=caller_location.offset + location.offset,
        size=location.size,
    )


def rewrite_loads_from_effects(
    expr: Expression,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
    blocked_locations: Optional[Sequence[CanonicalLocation]] = None,
) -> Expression:
    if expr is None:
        return expr

    active_blocked_locations = list(blocked_locations or [])

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = rewrite_loads_from_effects(
            expr.operands[0],
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
            blocked_locations=active_blocked_locations,
        )
        location = canonicalize_param_location(rewritten_addr, parameters, size=expr.size)
        candidate = Expression.memory(rewritten_addr, expr.size)
        if location is None:
            return candidate
        if _matches_existing_effect_value(
            candidate,
            location,
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
        ):
            return candidate

        for blocked_location in active_blocked_locations:
            if blocked_location.size != expr.size:
                continue
            if locations_match(location, blocked_location, return_conditions):
                return candidate

        matched = []
        for effect in effects:
            if max_order_key is not None and effect.order_key >= max_order_key:
                continue
            if effect.location.size != expr.size:
                continue
            if ConditionSimplifier.is_contradiction(list(return_conditions) + list(effect.conditions)):
                continue
            if not locations_match(location, effect.location, list(return_conditions) + effect.conditions):
                continue
            residual = subtract_implied_conditions(effect.conditions, return_conditions)
            matched.append((effect.order_key, residual, effect.value))

        if not matched:
            return candidate

        if _has_overlapping_guards(matched):
            return candidate

        matched.sort(key=lambda item: item[0], reverse=True)
        branches = []
        for effect_order, residual, value in matched:
            if residual:
                cond = Condition.combine_and(residual)
                branches.append(
                    (
                        cond,
                        rewrite_loads_from_effects(
                            value,
                            return_conditions,
                            effects,
                            parameters,
                            max_order_key=effect_order,
                            blocked_locations=active_blocked_locations + [location],
                        ),
                    )
                )
            else:
                return rewrite_loads_from_effects(
                    value,
                    return_conditions,
                    effects,
                    parameters,
                    max_order_key=effect_order,
                    blocked_locations=active_blocked_locations + [location],
                )

        branches.append((None, candidate))
        resolved = Expression.phi(branches)
        resolved.size = expr.size
        return resolved

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL):
        expr_location = canonicalize_expr_read_location(expr, parameters)
        if expr_location is not None and _matches_existing_effect_value(
            expr,
            expr_location,
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
        ):
            return expr
        new_operands = [
            rewrite_loads_from_effects(
                op,
                return_conditions,
                effects,
                parameters,
                max_order_key=max_order_key,
                blocked_locations=active_blocked_locations,
            )
            for op in expr.operands
        ]
        if all(new is old for new, old in zip(new_operands, expr.operands)):
            return expr
        rebuilt = Expression(
            expr_type=expr.expr_type,
            value=expr.value,
            operator=expr.operator,
            operands=new_operands,
            size=expr.size,
            name=expr.name,
            data_type=expr.data_type,
            storage_info=expr.storage_info,
        )
        return rebuilt

    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        changed = False
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = rewrite_loads_from_effects(
                value,
                combined_conditions,
                effects,
                parameters,
                max_order_key=max_order_key,
                blocked_locations=active_blocked_locations,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr


def _matches_existing_effect_value(
    expr: Expression,
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
) -> bool:
    for effect in effects:
        if max_order_key is not None and effect.order_key >= max_order_key:
            continue
        if ConditionSimplifier.is_contradiction(list(return_conditions) + list(effect.conditions)):
            continue
        if not locations_match(location, effect.location, return_conditions):
            continue
        if not _expression_reads_location(expr, location, return_conditions, parameters):
            continue
        if _expressions_equivalent(expr, effect.value):
            return True
    return False


def canonicalize_expr_read_location(expr: Expression, parameters: Sequence[Dict]) -> Optional[CanonicalLocation]:
    if expr is None:
        return None
    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        return canonicalize_param_location(expr.operands[0], parameters, size=expr.size)
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left = canonicalize_expr_read_location(expr.operands[0], parameters)
        right = canonicalize_expr_read_location(expr.operands[1], parameters)
        if left is None:
            return right
        if right is None:
            return left
        if left == right:
            return left
        return None
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        return canonicalize_expr_read_location(expr.operands[0], parameters)
    return None


def _expression_reads_location(
    expr: Optional[Expression],
    location: CanonicalLocation,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        read_location = canonicalize_param_location(expr.operands[0], parameters, size=expr.size)
        if read_location is None:
            return False
        return locations_match(read_location, location, conditions)
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            combined = list(conditions)
            if cond is not None:
                combined.append(cond)
            if _expression_reads_location(value, location, combined, parameters):
                return True
        return False
    for operand in getattr(expr, "operands", []) or []:
        if _expression_reads_location(operand, location, conditions, parameters):
            return True
    return False


def _expressions_equivalent(left: Optional[Expression], right: Optional[Expression]) -> bool:
    if left is right:
        return True
    if left is None or right is None:
        return False
    if left.expr_type != right.expr_type:
        return False
    if left.expr_type == ExpressionType.CONSTANT:
        return left.value == right.value and left.size == right.size
    if left.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE, ExpressionType.UNKNOWN, ExpressionType.CALL):
        return (
            left.name == right.name
            and left.value == right.value
            and left.size == right.size
        )
    if left.expr_type == ExpressionType.MEMORY:
        return left.size == right.size and _expressions_equivalent(left.operands[0], right.operands[0])
    if left.expr_type == ExpressionType.UNARY_OP:
        return (
            left.operator == right.operator
            and left.size == right.size
            and len(left.operands) == len(right.operands)
            and all(_expressions_equivalent(lop, rop) for lop, rop in zip(left.operands, right.operands))
        )
    if left.expr_type == ExpressionType.BINARY_OP:
        if left.operator != right.operator or left.size != right.size:
            return False
        if len(left.operands) != 2 or len(right.operands) != 2:
            return False
        left_pair = (left.operands[0], left.operands[1])
        right_pair = (right.operands[0], right.operands[1])
        if all(_expressions_equivalent(lop, rop) for lop, rop in zip(left_pair, right_pair)):
            return True
        if left.operator in {
            "INT_ADD",
            "INT_MULT",
            "INT_AND",
            "INT_OR",
            "INT_XOR",
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
            "INT_EQUAL",
            "INT_NOTEQUAL",
        }:
            return _expressions_equivalent(left.operands[0], right.operands[1]) and _expressions_equivalent(
                left.operands[1], right.operands[0]
            )
        return False
    if left.expr_type == ExpressionType.PHI:
        if left.size != right.size or not left.value or not right.value or len(left.value) != len(right.value):
            return False
        for (left_cond, left_value), (right_cond, right_value) in zip(left.value, right.value):
            if left_cond is None or right_cond is None:
                if left_cond is not right_cond:
                    return False
            else:
                if left_cond.negated != right_cond.negated:
                    return False
                if not _expressions_equivalent(left_cond.expression, right_cond.expression):
                    return False
            if not _expressions_equivalent(left_value, right_value):
                return False
        return True
    return (
        left.operator == right.operator
        and left.name == right.name
        and left.value == right.value
        and left.size == right.size
        and len(left.operands) == len(right.operands)
        and all(_expressions_equivalent(lop, rop) for lop, rop in zip(left.operands, right.operands))
    )


def build_void_effect_summary_expr(effects: Sequence[StoreEffect]) -> Optional[Expression]:
    groups: Dict[CanonicalLocation, List[StoreEffect]] = {}
    for effect in effects:
        groups.setdefault(effect.location, []).append(effect)

    if not groups:
        return None

    summary_parts: List[Expression] = []
    for location in sorted(groups.keys(), key=lambda loc: (loc.base_param, loc.offset, loc.size)):
        loc_effects = sorted(groups[location], key=lambda effect: effect.order_key, reverse=True)
        value_branches = []
        flag_branches = []
        for effect in loc_effects:
            cond = Condition.combine_and(effect.conditions)
            value_branches.append((cond, effect.value))
            flag_branches.append((cond, Expression.constant(1, 1)))
        value_branches.append((None, Expression.constant(0, max(1, location.size))))
        flag_branches.append((None, Expression.constant(0, 1)))
        value_expr = Expression.phi(value_branches)
        value_expr.size = max(1, location.size)
        flag_expr = Expression.phi(flag_branches)
        flag_expr.size = 1
        summary_parts.append(_concat(flag_expr, value_expr))

    result = summary_parts[0]
    for part in summary_parts[1:]:
        result = _concat(result, part)
    return result


def locations_match(
    left: CanonicalLocation,
    right: CanonicalLocation,
    conditions: Sequence[Condition],
) -> bool:
    if left.offset != right.offset:
        return False
    if left.base_param == right.base_param:
        return True
    equalities = _collect_param_equalities(conditions)
    return frozenset((left.base_param, right.base_param)) in equalities


def subtract_implied_conditions(
    effect_conditions: Sequence[Condition],
    return_conditions: Sequence[Condition],
) -> List[Condition]:
    implied = {
        ConditionNormalizer.normalize_for_contradiction(cond)
        for cond in return_conditions
    }
    residual = []
    for cond in effect_conditions:
        if ConditionNormalizer.normalize_for_contradiction(cond) not in implied:
            residual.append(cond)
    return residual


def substitute_condition(condition: Condition, replacements: Dict[str, Expression]) -> Condition:
    return Condition(substitute_expression(condition.expression, replacements), condition.negated)


def substitute_expression(expr: Expression, replacements: Dict[str, Expression]) -> Expression:
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE) and expr.name in replacements:
        return replacements[expr.name]

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.MEMORY):
        new_operands = [substitute_expression(op, replacements) for op in expr.operands]
        if all(new is old for new, old in zip(new_operands, expr.operands)):
            return expr
        rebuilt = Expression(
            expr_type=expr.expr_type,
            value=expr.value,
            operator=expr.operator,
            operands=new_operands,
            size=expr.size,
            name=expr.name,
            data_type=expr.data_type,
            storage_info=expr.storage_info,
        )
        return rebuilt

    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        changed = False
        for cond, value in expr.value:
            new_cond = substitute_condition(cond, replacements) if cond is not None else None
            new_value = substitute_expression(value, replacements)
            branches.append((new_cond, new_value))
            changed = changed or (new_cond is not cond or new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr


def _collect_param_equalities(conditions: Sequence[Condition]) -> Set[frozenset]:
    equalities: Set[frozenset] = set()
    for condition in conditions:
        left, op, right, is_positive = ConditionNormalizer.normalize(condition)
        if is_positive and op == "INT_EQUAL" and left and right:
            equalities.add(frozenset((left, right)))
    return equalities


def _flatten_param_addition(expr: Expression) -> Tuple[Optional[int], List[str]]:
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE) and expr.name:
        return 0, [expr.name]

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_ZEXT", "INT_SEXT"} and expr.operands:
        return _flatten_param_addition(expr.operands[0])

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "SUBPIECE"
        and len(expr.operands) == 2
    ):
        source, offset = expr.operands
        if offset.expr_type == ExpressionType.CONSTANT and offset.value == 0:
            return _flatten_param_addition(source)

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_ADD"
        and len(expr.operands) == 2
    ):
        left_const, left_bases = _flatten_param_addition(expr.operands[0])
        right_const, right_bases = _flatten_param_addition(expr.operands[1])
        if left_const is None or right_const is None:
            return None, []
        return left_const + right_const, left_bases + right_bases

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_MULT"
        and len(expr.operands) == 2
    ):
        left_const = _constant_factor(expr.operands[0])
        right_const = _constant_factor(expr.operands[1])
        if left_const == 1:
            return _flatten_param_addition(expr.operands[1])
        if right_const == 1:
            return _flatten_param_addition(expr.operands[0])

    if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
        return expr.value, []

    return None, []


def _constant_factor(expr: Expression) -> Optional[int]:
    if expr.expr_type != ExpressionType.CONSTANT or not isinstance(expr.value, int):
        return None
    return int(expr.value)


def _concat(left: Expression, right: Expression) -> Expression:
    result = Expression.binary_op("PIECE", left, right)
    result.size = (left.size or 0) + (right.size or 0)
    return result


def _has_overlapping_guards(matched: Sequence[Tuple[int, List[Condition], Expression]]) -> bool:
    for i in range(len(matched)):
        for j in range(i + 1, len(matched)):
            residual_i = list(matched[i][1])
            residual_j = list(matched[j][1])
            if not residual_i or not residual_j:
                return True
            if not ConditionSimplifier.is_contradiction(residual_i + residual_j):
                return True
    return False


def _get_order_key(op) -> int:
    seq = op.getSeqnum()
    if seq is None:
        return 0
    target = seq.getTarget()
    return (target.getOffset() << 8) | seq.getOrder()
