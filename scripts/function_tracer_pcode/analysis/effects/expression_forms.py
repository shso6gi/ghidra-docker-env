"""Expression structure helpers: keys, cloning, iteration, variants, ordering."""

from __future__ import annotations

from typing import Any, Dict, Iterator, List, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.effects._shared import (
    CanonicalLocation,
    Condition,
    ConditionSimplifier,
    EffectOrderUnavailable,
    EffectSummary,
    Expression,
    ExpressionType,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    _MAX_CALL_ARGUMENT_VARIANTS,
    expression_key_or_identity,
    expression_provenance_key,
    product,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _all_non_none_expressions,
    _clone_expression_tree,
    _clone_expression_with_operands,
    _enumerate_expression_variants,
    _expression_declares_pointer_type,
    _expression_is_call_scope_safe,
    _expression_location_ref,
    _expression_observed_read_ref,
    _expression_reads_location,
    _get_order_key,
    _is_test_order_mock,
    _iter_expression_nodes,
    _parameter_descriptor_from_expression,
    _parameter_descriptor_is_address_sized_unknown,
    _reduce_expression_under_conditions,
    _runtime_conditions_signature,
    _runtime_expression_signature,
)


def _impl__stable_target_expression_key(expr: Optional[Expression]) -> Optional[Tuple[object, ...]]:
    if expr is None:
        return None
    return expression_provenance_key(expr)


def _impl__condition_evidence_key(condition: Condition) -> Tuple[object, ...]:
    try:
        structural_key = condition.structural_key()
    except Exception:
        structural_key = None
    if structural_key is not None:
        return ("condition", bool(getattr(condition, "negated", False)), structural_key)
    expression = getattr(condition, "expression", None)
    return (
        "condition",
        bool(getattr(condition, "negated", False)),
        expression_provenance_key(expression) if expression is not None else None,
    )


def _impl__runtime_expression_signature(expr: Optional[Expression]):
    if expr is None:
        return ("none",)
    return expression_key_or_identity(
        expr,
        include_memory_read_order=False,
        include_semantic_runtime_refs=False,
    )


def _impl__runtime_conditions_signature(conditions: Sequence[Condition]):
    return ConditionSimplifier.object_centric_conditions_signature(conditions)


def _impl__encode_signed_token(value: int) -> str:
    try:
        numeric = int(value)
    except Exception:
        numeric = 0
    if numeric < 0:
        return f"n{abs(numeric)}"
    return f"p{numeric}"


def _impl__all_non_none_expressions(
    operands: Sequence[Optional[Expression]],
) -> Optional[List[Expression]]:
    normalized: List[Expression] = []
    for operand in operands:
        if operand is None:
            return None
        normalized.append(operand)
    return normalized


def _impl__clone_expression_with_operands(
    expr: Expression,
    operands: Sequence[Expression],
) -> Expression:
    return Expression(
        expr_type=expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=list(operands),
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
    )


def _impl__rebuild_expression_from_optional_operands(
    expr: Expression,
    rewritten_operands: Sequence[Optional[Expression]],
    *,
    fallback: Optional[Expression] = None,
) -> Optional[Expression]:
    if all(new is old for new, old in zip(rewritten_operands, expr.operands)):
        return expr
    new_operands = _all_non_none_expressions(rewritten_operands)
    if new_operands is None:
        return fallback
    return _clone_expression_with_operands(expr, new_operands)


def _impl__expression_observed_read_ref(expr: Optional[Expression]) -> Optional[ObservedMemoryReadRef]:
    if expr is None:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, ObservedMemoryReadRef):
        return runtime_ref
    return None


def _impl__expression_observed_order_key(expr: Optional[Expression]) -> Optional[int]:
    if expr is None:
        return None
    read_order_key = getattr(expr, "read_order_key", None)
    if read_order_key is not None:
        return int(read_order_key)
    observed_ref = _expression_observed_read_ref(expr)
    if observed_ref is not None and observed_ref.order_key is not None:
        return int(observed_ref.order_key)
    return None


def _impl__merge_memory_runtime_ref(
    runtime_ref: Any,
    runtime_location: Optional[CanonicalLocation],
    runtime_snapshot: Optional[PostStateSnapshotRef] = None,
) -> Any:
    if isinstance(runtime_ref, ObservedMemoryReadRef):
        if (
            (runtime_location is None or runtime_ref.location == runtime_location)
            and runtime_snapshot == runtime_ref.snapshot_ref
        ):
            return runtime_ref
        return runtime_ref.with_location(runtime_location, snapshot_ref=runtime_snapshot)
    if isinstance(runtime_ref, PostStateReadRef):
        location = runtime_location if runtime_location is not None else runtime_ref.location
        snapshot = runtime_snapshot if runtime_snapshot is not None else runtime_ref.snapshot_ref
        if location == runtime_ref.location and snapshot == runtime_ref.snapshot_ref:
            return runtime_ref
        return runtime_ref.with_location(location).with_snapshot(snapshot)
    if runtime_location is not None and runtime_snapshot is not None:
        return PostStateReadRef(
            location=runtime_location,
            snapshot_ref=runtime_snapshot,
        )
    if runtime_location is not None:
        return runtime_location
    return runtime_ref


def _impl__iter_expression_nodes(
    expr: Optional[Expression],
    *,
    include_phi_conditions: bool = True,
) -> Iterator[Expression]:
    if expr is None:
        return

    pending: List[Expression] = [expr]
    while pending:
        current = pending.pop()
        if current is None:
            continue
        yield current
        if current.expr_type == ExpressionType.PHI and current.value:
            for cond, value in reversed(current.value):
                if value is not None:
                    pending.append(value)
                if include_phi_conditions and cond is not None and cond.expression is not None:
                    pending.append(cond.expression)
            continue
        operands = getattr(current, "operands", None) or []
        pending.extend(reversed([operand for operand in operands if operand is not None]))


def _impl__expression_contains_value_reads(expr: Optional[Expression]) -> bool:
    for node in _iter_expression_nodes(expr):
        if _expression_location_ref(node) is not None:
            return True
        if node.expr_type == ExpressionType.MEMORY and node.operands:
            return True
    return False


def _impl__expression_contains_phi(expr: Optional[Expression]) -> bool:
    for node in _iter_expression_nodes(expr, include_phi_conditions=False):
        if node.expr_type == ExpressionType.PHI:
            return True
    return False


def _impl__expression_node_count(expr: Optional[Expression]) -> int:
    return sum(1 for _ in _iter_expression_nodes(expr))


def _impl__expression_is_wide_unknown_or_undefined(expr: Expression) -> bool:
    if expr.expr_type not in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
        return False
    descriptor = _parameter_descriptor_from_expression(expr)
    if not _parameter_descriptor_is_address_sized_unknown(descriptor):
        return False
    try:
        expr_size = int(getattr(expr, "size", 0) or 0)
    except Exception:
        expr_size = 0
    return expr_size > 4


def _impl__expression_is_non_address_sized_scalar_value(expr: Expression) -> bool:
    if _expression_declares_pointer_type(expr):
        return False
    try:
        expr_size = int(getattr(expr, "size", 0) or 0)
    except Exception:
        expr_size = 0
    return 0 < expr_size <= 4


def _impl__enumerate_expression_variants(
    expr: Optional[Expression],
    *,
    limit: int = _MAX_CALL_ARGUMENT_VARIANTS,
) -> List[Tuple[List[Condition], Expression]]:
    if expr is None:
        return []

    if expr.expr_type == ExpressionType.PHI and expr.value:
        resolved: List[Tuple[List[Condition], Expression]] = []
        seen = set()
        for cond, value in expr.value:
            for branch_conditions, branch_value in _enumerate_expression_variants(value, limit=limit):
                merged_conditions = list(branch_conditions)
                if cond is not None:
                    merged_conditions.insert(0, cond)
                simplified = ConditionSimplifier.simplify_conditions(merged_conditions)
                if ConditionSimplifier.is_contradiction(simplified):
                    continue
                key = (
                    _runtime_conditions_signature(simplified),
                    _runtime_expression_signature(branch_value),
                )
                if key in seen:
                    continue
                seen.add(key)
                resolved.append((simplified, branch_value))
                if len(resolved) >= limit:
                    break
            if len(resolved) >= limit:
                break
        return resolved or [([], expr)]

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.INTRINSIC, ExpressionType.MEMORY):
        operand_variants = [
            _enumerate_expression_variants(operand, limit=limit)
            for operand in expr.operands
        ]
        if operand_variants and any(len(variants) > 1 or variants[0][0] for variants in operand_variants):
            resolved = []
            seen = set()
            for variant_tuple in product(*operand_variants):
                merged_conditions: List[Condition] = []
                merged_operands: List[Expression] = []
                for branch_conditions, branch_expr in variant_tuple:
                    merged_conditions.extend(branch_conditions)
                    merged_operands.append(branch_expr)
                simplified = ConditionSimplifier.simplify_conditions(merged_conditions)
                if ConditionSimplifier.is_contradiction(simplified):
                    continue
                rebuilt = _clone_expression_with_operands(expr, merged_operands)
                key = (
                    _runtime_conditions_signature(simplified),
                    _runtime_expression_signature(rebuilt),
                )
                if key in seen:
                    continue
                seen.add(key)
                resolved.append((simplified, rebuilt))
                if len(resolved) >= limit:
                    break
            return resolved or [([], expr)]

    return [([], expr)]


def _impl__reduce_conditions_under_context(
    conditions: Sequence[Condition],
    context_conditions: Sequence[Condition],
) -> List[Condition]:
    reduced: List[Condition] = []
    for cond in conditions or []:
        reduced_expr = _reduce_expression_under_conditions(
            cond.expression,
            list(context_conditions),
        )
        reduced.append(Condition(reduced_expr, cond.negated))
    return ConditionSimplifier.simplify_conditions(reduced)


def _impl__mask_to_expr_width(expr: Expression, value: int) -> int:
    bit_width = max(1, expr.get_bit_width())
    return value & ((1 << bit_width) - 1)


def _impl__expression_bit_width(expr: Optional[Expression]) -> int:
    if expr is None:
        return 0
    try:
        width = int(expr.get_bit_width() or 0)
    except Exception:
        width = 0
    if width > 0:
        return width
    try:
        size = int(getattr(expr, "size", 0) or 0)
    except Exception:
        size = 0
    return max(0, size * 8)


def _impl__clone_expression_tree(expr: Optional[Expression]) -> Optional[Expression]:
    if expr is None:
        return None
    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        for cond, value in expr.value:
            cloned_cond = None
            if cond is not None:
                cloned_expression = _clone_expression_tree(cond.expression)
                cloned_cond = None if cloned_expression is None else Condition(cloned_expression, cond.negated)
            branches.append((cloned_cond, _clone_expression_tree(value)))
        cloned = Expression.phi(branches)
        cloned.size = expr.size
        cloned.data_type = expr.data_type
        cloned.data_type_obj = getattr(expr, "data_type_obj", None)
        cloned.storage_info = getattr(expr, "storage_info", None)
        cloned.read_order_key = getattr(expr, "read_order_key", None)
        cloned.runtime_ref = getattr(expr, "runtime_ref", None)
        cloned.opcode = getattr(expr, "opcode", None)
        return cloned
    return expr.clone_with(
        operands=[_clone_expression_tree(op) for op in (expr.operands or [])]
    )


def _impl__expression_is_call_scope_safe(expr: Optional[Expression]) -> bool:
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


def _impl__summary_has_interdependent_writes(summary: EffectSummary) -> bool:
    if summary is None or len(summary.effects) <= 1:
        return False

    params = [{"name": name, "index": index} for index, name in enumerate(summary.parameter_names)]
    for index, effect in enumerate(summary.effects):
        for other_index, other in enumerate(summary.effects):
            if index == other_index:
                continue
            if effect.location == other.location:
                continue
            if _expression_reads_location(effect.value, other.location, effect.conditions, params):
                return True
    return False


def _impl__strongly_connected_components(
    graph: Dict[CanonicalLocation, Set[CanonicalLocation]]
) -> List[List[CanonicalLocation]]:
    index = 0
    stack: List[CanonicalLocation] = []
    indices: Dict[CanonicalLocation, int] = {}
    lowlinks: Dict[CanonicalLocation, int] = {}
    on_stack: Set[CanonicalLocation] = set()
    components: List[List[CanonicalLocation]] = []

    def strongconnect(node: CanonicalLocation) -> None:
        nonlocal index
        indices[node] = index
        lowlinks[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)

        for succ in graph.get(node, set()):
            if succ not in indices:
                strongconnect(succ)
                lowlinks[node] = min(lowlinks[node], lowlinks[succ])
            elif succ in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[succ])

        if lowlinks[node] != indices[node]:
            return

        component: List[CanonicalLocation] = []
        while stack:
            member = stack.pop()
            on_stack.discard(member)
            component.append(member)
            if member == node:
                break
        components.append(component)

    for node in graph:
        if node not in indices:
            strongconnect(node)

    return components


def _impl__concat(left: Expression, right: Expression) -> Expression:
    result = Expression.binary_op("PIECE", left, right)
    result.size = (left.size or 0) + (right.size or 0)
    return result


def _impl__get_order_key(op) -> int:
    try:
        seq = op.getSeqnum()
    except Exception as exc:
        if _is_test_order_mock(op):
            return 0
        raise EffectOrderUnavailable("pcode op sequence number is unavailable") from exc
    if seq is None:
        if _is_test_order_mock(op):
            return 0
        raise EffectOrderUnavailable("pcode op sequence number is unavailable")
    try:
        target = seq.getTarget()
        return (int(target.getOffset()) << 8) | int(seq.getOrder())
    except Exception as exc:
        if _is_test_order_mock(op):
            return 0
        raise EffectOrderUnavailable("pcode op target/order is unavailable") from exc


def _impl__try_get_order_key(op, *, default: Optional[int] = None) -> Optional[int]:
    try:
        return _get_order_key(op)
    except EffectOrderUnavailable:
        return default


def _impl__is_test_order_mock(op) -> bool:
    module_name = str(getattr(type(op), "__module__", "") or "")
    return (
        module_name.startswith("test_")
        or ".tests." in module_name
        or module_name.endswith(".tests")
    )
