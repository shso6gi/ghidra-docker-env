# -*- coding: utf-8 -*-
"""Object-centric JumpTable-based switch recovery helpers."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Any, Callable, Iterable, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.structural import expression_key_safe
from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier

_INDIRECT_DISPATCH_MNEMONICS = {"BRANCHIND", "CALLIND"}
_VALUE_PASSTHROUGH_UNARY_OPS = {"INT_ZEXT", "INT_SEXT", "CAST", "COPY"}


@dataclass(frozen=True)
class JumpTableLoadSpec:
    base_address: int
    entry_size: int
    entry_count: int


@dataclass(frozen=True)
class SwitchDispatchCase:
    label_value: Optional[int]
    target_address: int
    conditions: Tuple[Condition, ...]
    is_default: bool = False


@dataclass(frozen=True)
class SwitchDispatchPath:
    base_conditions: Tuple[Condition, ...]
    selector: Expression
    target_expression: Expression
    cases: Tuple[SwitchDispatchCase, ...]


@dataclass(frozen=True)
class SwitchDispatchSummary:
    block_info: Any
    dispatch_op: Any
    dispatch_mnemonic: str
    switch_address: Optional[str]
    labels: Tuple[int, ...]
    target_addresses: Tuple[int, ...]
    load_specs: Tuple[JumpTableLoadSpec, ...]
    paths: Tuple[SwitchDispatchPath, ...]


def build_switch_dispatch_summaries(
    *,
    tracer,
    condition_tracker,
    parameters: Sequence[dict],
    concretize_readonly_loads: Callable[[Optional[Expression], List[Condition], Sequence[dict]], Optional[Expression]],
    read_memory_value: Optional[Callable[[int, int], Optional[int]]] = None,
    max_cases: int = 128,
    debug: bool = False,
    debug_print: Optional[Callable[[str], None]] = None,
) -> List[SwitchDispatchSummary]:
    """Recover switch dispatch summaries from Ghidra JumpTable objects."""

    high_function = getattr(tracer, "high_function", None)
    if high_function is None:
        return []

    get_jump_tables = getattr(high_function, "getJumpTables", None)
    if callable(get_jump_tables):
        try:
            jump_tables = list(get_jump_tables() or [])
        except Exception:
            jump_tables = []
    else:
        jump_tables = []

    block_by_index = getattr(condition_tracker, "block_by_index", None) or {}
    dispatch_candidates = [
        (block_info, dispatch_op)
        for block_info in block_by_index.values()
        for dispatch_op in _iter_indirect_dispatch_ops(block_info)
    ]
    if not dispatch_candidates:
        return []

    summaries: List[SwitchDispatchSummary] = []
    matched_dispatch_ids = set()
    for jump_table in jump_tables:
        dispatch_binding = _match_jump_table_dispatch(jump_table, dispatch_candidates)
        if dispatch_binding is None:
            continue

        block_info, dispatch_op = dispatch_binding
        matched_dispatch_ids.add(id(dispatch_op))
        load_specs = _extract_load_specs(jump_table)
        label_values = tuple(_extract_int_values(getattr(jump_table, "getLabelValues", None)))
        target_addresses = tuple(_extract_address_offsets(getattr(jump_table, "getCases", None)))
        if not target_addresses or not label_values:
            continue

        raw_paths = None
        get_paths = getattr(condition_tracker, "get_all_valid_block_paths_to_block", None)
        if callable(get_paths):
            try:
                raw_paths = get_paths(block_info)
            except Exception:
                raw_paths = None
        path_entries = _coerce_block_path_entries(raw_paths)
        if not path_entries:
            path_entries = [([block_info], [])]

        raw_target_expr = None
        try:
            if dispatch_op.getNumInputs() >= 1:
                raw_target_expr = tracer.trace_varnode(dispatch_op.getInput(0), use_cache=False)
        except Exception:
            raw_target_expr = None
        if raw_target_expr is None:
            continue

        path_summaries: List[SwitchDispatchPath] = []
        path_failed = False
        for _block_path, base_conditions in path_entries:
            simplified_base = ConditionSimplifier.simplify_conditions(list(base_conditions))
            if ConditionSimplifier.is_contradiction(simplified_base):
                continue

            target_expression = concretize_readonly_loads(
                raw_target_expr,
                list(simplified_base),
                parameters,
            )
            if target_expression is None:
                path_failed = True
                break

            selector = _recover_selector_from_target_expression(
                target_expression,
                load_specs,
                tracer,
            )
            if selector is None:
                path_failed = True
                break

            selector = ConditionSimplifier.reduce_expression_under_conditions(
                selector,
                simplified_base,
            )
            cases = _build_dispatch_cases(
                selector=selector,
                base_conditions=simplified_base,
                labels=label_values,
                target_addresses=target_addresses,
            )
            if not cases:
                path_failed = True
                break

            path_summaries.append(
                SwitchDispatchPath(
                    base_conditions=tuple(simplified_base),
                    selector=selector,
                    target_expression=target_expression,
                    cases=tuple(cases),
                )
            )

        if path_failed or not path_summaries:
            if debug and debug_print is not None:
                try:
                    switch_addr = jump_table.getSwitchAddress()
                except Exception:
                    switch_addr = None
                debug_print(
                    "JumpTable-based switch recovery skipped: failed to recover selector "
                    f"for {switch_addr}"
                )
            continue

        summaries.append(
            SwitchDispatchSummary(
                block_info=block_info,
                dispatch_op=dispatch_op,
                dispatch_mnemonic=str(getattr(dispatch_op, "getMnemonic", lambda: "INDIRECT")()),
                switch_address=_address_to_string(getattr(jump_table, "getSwitchAddress", lambda: None)()),
                labels=label_values,
                target_addresses=target_addresses,
                load_specs=tuple(load_specs),
                paths=tuple(path_summaries),
            )
        )

    if read_memory_value is not None:
        for block_info, dispatch_op in dispatch_candidates:
            if id(dispatch_op) in matched_dispatch_ids:
                continue
            synthetic_summary = _build_synthetic_dispatch_summary(
                block_info=block_info,
                dispatch_op=dispatch_op,
                tracer=tracer,
                condition_tracker=condition_tracker,
                parameters=parameters,
                concretize_readonly_loads=concretize_readonly_loads,
                read_memory_value=read_memory_value,
                max_cases=max_cases,
            )
            if synthetic_summary is not None:
                summaries.append(synthetic_summary)

    return summaries


def _iter_indirect_dispatch_ops(block_info) -> Iterable[Any]:
    for pcode_op in reversed(list(getattr(block_info, "pcode_ops", []) or [])):
        try:
            mnemonic = str(pcode_op.getMnemonic())
        except Exception:
            continue
        if mnemonic in _INDIRECT_DISPATCH_MNEMONICS:
            yield pcode_op


def _match_jump_table_dispatch(
    jump_table,
    dispatch_candidates: Sequence[Tuple[Any, Any]],
) -> Optional[Tuple[Any, Any]]:
    switch_address = None
    try:
        switch_address = jump_table.getSwitchAddress()
    except Exception:
        switch_address = None
    switch_key = _address_identity(switch_address)
    if switch_key is None:
        return None

    for block_info, dispatch_op in dispatch_candidates:
        seq = getattr(dispatch_op, "getSeqnum", lambda: None)()
        target = getattr(seq, "getTarget", lambda: None)() if seq is not None else None
        if _address_identity(target) == switch_key:
            return block_info, dispatch_op
    return None


def _extract_load_specs(jump_table) -> List[JumpTableLoadSpec]:
    get_load_tables = getattr(jump_table, "getLoadTables", None)
    if not callable(get_load_tables):
        return []

    specs: List[JumpTableLoadSpec] = []
    for load_table in list(get_load_tables() or []):
        try:
            address = load_table.getAddress()
            base_offset = _address_offset(address)
            entry_size = int(load_table.getSize())
            entry_count = int(load_table.getNum())
        except Exception:
            continue
        if base_offset is None or entry_size <= 0 or entry_count <= 0:
            continue
        specs.append(
            JumpTableLoadSpec(
                base_address=base_offset,
                entry_size=entry_size,
                entry_count=entry_count,
            )
        )
    return specs


def _extract_int_values(getter) -> List[int]:
    if not callable(getter):
        return []
    values: List[int] = []
    try:
        raw_values = list(getter() or [])
    except Exception:
        return values
    for value in raw_values:
        try:
            values.append(int(value))
        except Exception:
            continue
    return values


def _extract_address_offsets(getter) -> List[int]:
    if not callable(getter):
        return []
    values: List[int] = []
    try:
        raw_values = list(getter() or [])
    except Exception:
        return values
    for address in raw_values:
        address_value = _address_offset(address)
        if address_value is None:
            continue
        values.append(address_value)
    return values


def _build_dispatch_cases(
    *,
    selector: Expression,
    base_conditions: Sequence[Condition],
    labels: Sequence[int],
    target_addresses: Sequence[int],
) -> List[SwitchDispatchCase]:
    paired_count = min(len(labels), len(target_addresses))
    if paired_count <= 0:
        return []

    selector_size = max(1, int(getattr(selector, "size", 0) or 0))
    built_cases: List[SwitchDispatchCase] = []

    for label_value, target_address in zip(labels[:paired_count], target_addresses[:paired_count]):
        case_guard = Condition(
            Expression.binary_op(
                "INT_EQUAL",
                _clone_expression(selector),
                Expression.constant(int(label_value), selector_size),
            ),
            False,
        )
        merged_conditions = ConditionSimplifier.simplify_conditions(
            list(base_conditions) + [case_guard]
        )
        if ConditionSimplifier.is_contradiction(merged_conditions):
            continue
        built_cases.append(
            SwitchDispatchCase(
                label_value=int(label_value),
                target_address=int(target_address),
                conditions=tuple(merged_conditions),
            )
        )

    extra_targets = list(target_addresses[paired_count:])
    if len(extra_targets) == 1 and labels:
        default_conditions = list(base_conditions)
        for label_value in labels[:paired_count]:
            default_conditions.append(
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        _clone_expression(selector),
                        Expression.constant(int(label_value), selector_size),
                    ),
                    False,
                )
            )
        simplified_default = ConditionSimplifier.simplify_conditions(default_conditions)
        if not ConditionSimplifier.is_contradiction(simplified_default):
            built_cases.append(
                SwitchDispatchCase(
                    label_value=None,
                    target_address=int(extra_targets[0]),
                    conditions=tuple(simplified_default),
                    is_default=True,
                )
            )

    return built_cases


def _recover_selector_from_target_expression(
    target_expression: Expression,
    load_specs: Sequence[JumpTableLoadSpec],
    tracer,
) -> Optional[Expression]:
    memory_nodes = _find_memory_nodes(target_expression)
    for memory_node in memory_nodes:
        address_expr = memory_node.operands[0] if memory_node.operands else None
        if address_expr is None:
            continue
        for load_spec in load_specs:
            selector = _recover_selector_from_load_address(
                address_expr,
                load_spec,
                tracer,
            )
            if selector is not None:
                return _normalize_selector_expression(selector)

    direct_selector = _recover_direct_selector_from_dispatch_input(
        target_expression,
        tracer,
    )
    if direct_selector is not None:
        return _normalize_selector_expression(direct_selector)
    return None


def _find_memory_nodes(expr: Optional[Expression]) -> List[Expression]:
    if expr is None:
        return []

    found: List[Expression] = []
    if expr.expr_type == ExpressionType.MEMORY:
        found.append(expr)
    for operand in getattr(expr, "operands", []) or []:
        found.extend(_find_memory_nodes(operand))
    return found


def _recover_selector_from_load_address(
    address_expr: Expression,
    load_spec: JumpTableLoadSpec,
    tracer,
) -> Optional[Expression]:
    constant_base, delta_expr = _split_address_base_delta(address_expr, tracer)
    if constant_base is None or delta_expr is None:
        return None

    delta_constant, delta_terms = _flatten_additive_expression(delta_expr, tracer)
    base_adjustment = constant_base + delta_constant - int(load_spec.base_address)

    if base_adjustment < 0:
        return None
    if load_spec.entry_size > 1 and base_adjustment % int(load_spec.entry_size) != 0:
        return None

    selector_term: Optional[Expression] = None
    for term in delta_terms:
        scaled_selector = _strip_known_unary_wrappers(term)
        recovered = _strip_scale_factor(
            scaled_selector,
            int(load_spec.entry_size),
            tracer,
        )
        if recovered is None:
            return None
        if selector_term is not None:
            return None
        selector_term = recovered

    if selector_term is None:
        return None

    if selector_term.expr_type == ExpressionType.BINARY_OP and selector_term.operator == "SUBPIECE":
        selector_term = _normalize_subpiece_to_zext(selector_term)

    return selector_term


def _recover_direct_selector_from_dispatch_input(
    target_expression: Expression,
    tracer,
) -> Optional[Expression]:
    if _resolve_concrete_address_offset(target_expression, tracer) is not None:
        return None
    if target_expression.expr_type == ExpressionType.UNKNOWN:
        return None
    if (
        target_expression.expr_type == ExpressionType.INTRINSIC
        and getattr(target_expression, "name", None) in {"PTRADD", "PTRSUB"}
    ):
        return None
    return target_expression


def _normalize_selector_expression(selector: Expression) -> Expression:
    if selector.expr_type == ExpressionType.BINARY_OP and selector.operator == "SUBPIECE":
        return _normalize_subpiece_to_zext(selector)
    return selector


def _build_synthetic_dispatch_summary(
    *,
    block_info,
    dispatch_op,
    tracer,
    condition_tracker,
    parameters: Sequence[dict],
    concretize_readonly_loads: Callable[[Optional[Expression], List[Condition], Sequence[dict]], Optional[Expression]],
    read_memory_value: Callable[[int, int], Optional[int]],
    max_cases: int,
) -> Optional[SwitchDispatchSummary]:
    raw_target_expr = None
    try:
        if dispatch_op.getNumInputs() >= 1:
            raw_target_expr = tracer.trace_varnode(dispatch_op.getInput(0), use_cache=False)
    except Exception:
        raw_target_expr = None
    if raw_target_expr is None:
        return None

    raw_paths = None
    get_paths = getattr(condition_tracker, "get_all_valid_block_paths_to_block", None)
    if callable(get_paths):
        try:
            raw_paths = get_paths(block_info)
        except Exception:
            raw_paths = None
    path_entries = _coerce_block_path_entries(raw_paths)
    if not path_entries:
        path_entries = [([block_info], [])]

    path_summaries: List[SwitchDispatchPath] = []
    top_level_targets: List[int] = []
    top_level_labels: List[int] = []
    for _block_path, base_conditions in path_entries:
        simplified_base = ConditionSimplifier.simplify_conditions(list(base_conditions))
        if ConditionSimplifier.is_contradiction(simplified_base):
            continue

        target_expression = concretize_readonly_loads(
            raw_target_expr,
            list(simplified_base),
            parameters,
        )
        if target_expression is None:
            return None

        selector = _recover_selector_from_target_expression(
            target_expression,
            (),
            tracer,
        )
        if selector is None:
            inferred_raw = _infer_selector_and_memory_plan(raw_target_expr, tracer)
            selector = inferred_raw[0] if inferred_raw is not None else None
        if selector is None:
            return None
        selector = ConditionSimplifier.reduce_expression_under_conditions(
            _normalize_selector_expression(selector),
            simplified_base,
        )

        direct_cases = _expand_expression_cases(
            target_expression,
            simplified_base,
            max_cases=max_cases,
        )
        if direct_cases:
            cases: List[SwitchDispatchCase] = []
            for case_expr, case_conditions in direct_cases:
                target_address = _resolve_concrete_address_offset(case_expr, tracer)
                if target_address is None:
                    continue
                target_address = _canonicalize_program_address_offset(target_address, tracer)
                label_value = _extract_label_value_for_selector(selector, case_conditions)
                if label_value is None:
                    continue
                cases.append(
                    SwitchDispatchCase(
                        label_value=int(label_value),
                        target_address=int(target_address),
                        conditions=tuple(case_conditions),
                    )
                )
                if int(label_value) not in top_level_labels:
                    top_level_labels.append(int(label_value))
                    top_level_targets.append(int(target_address))

            if cases:
                path_summaries.append(
                    SwitchDispatchPath(
                        base_conditions=tuple(simplified_base),
                        selector=selector,
                        target_expression=target_expression,
                        cases=tuple(sorted(cases, key=lambda case: int(case.label_value if case.label_value is not None else -1))),
                    )
                )
                continue

        inferred = _infer_selector_and_memory_plan(raw_target_expr, tracer)
        if inferred is None:
            return None
        selector, memory_node, table_base, entry_size = inferred
        selector = ConditionSimplifier.reduce_expression_under_conditions(
            _normalize_selector_expression(selector),
            simplified_base,
        )
        label_values = _enumerate_selector_values(
            selector,
            simplified_base,
            max_cases=max_cases,
        )
        if not label_values:
            return None

        cases: List[SwitchDispatchCase] = []
        for label_value in label_values:
            load_address = int(table_base) + int(label_value) * int(entry_size)
            loaded_value = read_memory_value(
                load_address,
                max(1, int(getattr(memory_node, "size", 0) or entry_size)),
            )
            if loaded_value is None:
                return None

            target_address = _materialize_target_address_from_memory_load(
                raw_target_expr,
                memory_node,
                int(loaded_value),
                tracer,
            )
            if target_address is None:
                return None
            target_address = _canonicalize_program_address_offset(target_address, tracer)

            merged_conditions = ConditionSimplifier.simplify_conditions(
                list(simplified_base)
                + [
                    Condition(
                        Expression.binary_op(
                            "INT_EQUAL",
                            _clone_expression(selector),
                            Expression.constant(
                                int(label_value),
                                max(1, int(getattr(selector, "size", 0) or 0)),
                            ),
                        ),
                        False,
                    )
                ]
            )
            if ConditionSimplifier.is_contradiction(merged_conditions):
                continue
            cases.append(
                SwitchDispatchCase(
                    label_value=int(label_value),
                    target_address=int(target_address),
                    conditions=tuple(merged_conditions),
                )
            )
            if int(label_value) not in top_level_labels:
                top_level_labels.append(int(label_value))
                top_level_targets.append(int(target_address))

        if not cases:
            return None

        path_summaries.append(
            SwitchDispatchPath(
                base_conditions=tuple(simplified_base),
                selector=selector,
                target_expression=target_expression,
                cases=tuple(cases),
            )
        )

    if not path_summaries:
        return None

    return SwitchDispatchSummary(
        block_info=block_info,
        dispatch_op=dispatch_op,
        dispatch_mnemonic=str(getattr(dispatch_op, "getMnemonic", lambda: "INDIRECT")()),
        switch_address=_address_to_string(getattr(getattr(dispatch_op, "getSeqnum", lambda: None)(), "getTarget", lambda: None)()),
        labels=tuple(top_level_labels),
        target_addresses=tuple(top_level_targets),
        load_specs=tuple(),
        paths=tuple(path_summaries),
    )


def _infer_selector_and_memory_plan(
    target_expression: Expression,
    tracer,
) -> Optional[Tuple[Expression, Expression, int, int]]:
    for memory_node in _find_memory_nodes(target_expression):
        address_expr = memory_node.operands[0] if memory_node.operands else None
        if address_expr is None:
            continue
        constant_base, delta_expr = _split_address_base_delta(address_expr, tracer)
        if constant_base is None or delta_expr is None:
            continue
        delta_constant, delta_terms = _flatten_additive_expression(delta_expr, tracer)
        if len(delta_terms) != 1:
            continue
        selector_expr, entry_size = _infer_selector_scale(delta_terms[0], tracer)
        if selector_expr is None or entry_size <= 0:
            continue
        table_base = int(constant_base) + int(delta_constant)
        return selector_expr, memory_node, table_base, entry_size
    return None


def _infer_selector_scale(
    term: Expression,
    tracer,
) -> Tuple[Optional[Expression], int]:
    expr = _strip_known_unary_wrappers(term)

    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_MULT" and len(expr.operands) == 2:
        left_const = _resolve_concrete_address_offset(expr.operands[0], tracer)
        right_const = _resolve_concrete_address_offset(expr.operands[1], tracer)
        if left_const is not None:
            return expr.operands[1], int(left_const)
        if right_const is not None:
            return expr.operands[0], int(right_const)
        return None, 0

    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_LEFT" and len(expr.operands) == 2:
        shift_amount = _resolve_concrete_address_offset(expr.operands[1], tracer)
        if shift_amount is None:
            return None, 0
        return expr.operands[0], 1 << int(shift_amount)

    return expr, 1


def _enumerate_selector_values(
    selector: Expression,
    base_conditions: Sequence[Condition],
    *,
    max_cases: int,
) -> List[int]:
    selector_key = expression_key_safe(selector)
    if selector_key is None:
        return []

    eq_values: List[int] = []
    ne_values: set[int] = set()
    lower_bound: Optional[int] = None
    lower_inclusive = True
    upper_bound: Optional[int] = None
    upper_inclusive = True
    saw_unsigned_fact = False

    for condition in base_conditions:
        fact = ConditionSimplifier.extract_scalar_constraint(condition)
        if fact is None:
            continue
        if expression_key_safe(fact.expr) != selector_key:
            continue

        if fact.kind == "eq" and fact.raw_value is not None:
            eq_values.append(int(fact.raw_value))
            continue
        if fact.kind == "ne" and fact.raw_value is not None:
            ne_values.add(int(fact.raw_value))
            continue
        if fact.kind == "lower" and fact.value is not None:
            candidate = int(fact.value)
            if lower_bound is None or candidate > lower_bound or (
                candidate == lower_bound and fact.inclusive and not lower_inclusive
            ):
                lower_bound = candidate
                lower_inclusive = bool(fact.inclusive)
            saw_unsigned_fact = saw_unsigned_fact or not fact.signed
            continue
        if fact.kind == "upper" and fact.value is not None:
            candidate = int(fact.value)
            if upper_bound is None or candidate < upper_bound or (
                candidate == upper_bound and fact.inclusive and not upper_inclusive
            ):
                upper_bound = candidate
                upper_inclusive = bool(fact.inclusive)
            saw_unsigned_fact = saw_unsigned_fact or not fact.signed

    if eq_values:
        ordered = []
        for value in sorted(set(eq_values)):
            if value in ne_values:
                continue
            ordered.append(int(value))
        return ordered[:max_cases]

    if upper_bound is None:
        return []

    effective_lower = lower_bound
    if effective_lower is None and saw_unsigned_fact:
        effective_lower = 0
        lower_inclusive = True
    if effective_lower is None:
        return []

    start = int(effective_lower) + (0 if lower_inclusive else 1)
    stop = int(upper_bound) + (1 if upper_inclusive else 0)
    if stop < start:
        return []
    if stop - start > max_cases:
        return []

    return [value for value in range(start, stop) if value not in ne_values]


def _materialize_target_address_from_memory_load(
    target_expression: Expression,
    memory_node: Expression,
    loaded_value: int,
    tracer,
) -> Optional[int]:
    replacement = Expression.constant(
        int(loaded_value),
        size=max(1, int(getattr(memory_node, "size", 0) or 0)),
    )
    rebuilt = _replace_expression_node(target_expression, memory_node, replacement)
    return _resolve_concrete_address_offset(rebuilt, tracer)


def _canonicalize_program_address_offset(value: int, tracer) -> int:
    normalized = int(value)
    program = getattr(tracer, "program", None)
    pointer_bits = None
    if program is not None:
        get_pointer_size = getattr(program, "getDefaultPointerSize", None)
        if callable(get_pointer_size):
            try:
                pointer_bits = int(get_pointer_size()) * 8
            except Exception:
                pointer_bits = None
    if pointer_bits is None or pointer_bits <= 0 or pointer_bits > 128:
        return normalized
    mask = (1 << pointer_bits) - 1
    return normalized & mask


def _expand_expression_cases(
    expr: Expression,
    base_conditions: Sequence[Condition],
    *,
    max_cases: int,
) -> List[Tuple[Expression, List[Condition]]]:
    simplified_base = ConditionSimplifier.simplify_conditions(list(base_conditions))
    if ConditionSimplifier.is_contradiction(simplified_base):
        return []

    if expr.expr_type == ExpressionType.PHI and expr.value:
        expanded: List[Tuple[Expression, List[Condition]]] = []
        prior_guards: List[Condition] = []
        for cond, value in expr.value:
            branch_conditions = list(simplified_base)
            for prior in prior_guards:
                branch_conditions.append(prior.negate())
            if cond is not None:
                branch_conditions.append(cond)
                prior_guards.append(cond)
            branch_conditions = ConditionSimplifier.simplify_conditions(branch_conditions)
            if ConditionSimplifier.is_contradiction(branch_conditions):
                continue
            expanded.extend(
                _expand_expression_cases(
                    value,
                    branch_conditions,
                    max_cases=max_cases,
                )
            )
            if len(expanded) > max_cases:
                return []
        return expanded

    operands = list(getattr(expr, "operands", []) or [])
    if not operands:
        return [(expr, simplified_base)]

    operand_case_lists: List[List[Tuple[Expression, List[Condition]]]] = []
    for operand in operands:
        operand_cases = _expand_expression_cases(
            operand,
            simplified_base,
            max_cases=max_cases,
        )
        operand_case_lists.append(operand_cases or [(operand, simplified_base)])

    expanded: List[Tuple[Expression, List[Condition]]] = []
    for case_combination in product(*operand_case_lists):
        rebuilt_operands: List[Expression] = []
        combined_conditions = list(simplified_base)
        for operand_value, operand_conditions in case_combination:
            residual_conditions = ConditionSimplifier.subtract_implied_conditions(
                operand_conditions,
                simplified_base,
            )
            combined_conditions.extend(residual_conditions)
            rebuilt_operands.append(operand_value)
        combined_conditions = ConditionSimplifier.simplify_conditions(combined_conditions)
        if ConditionSimplifier.is_contradiction(combined_conditions):
            continue
        expanded.append((expr.clone_with(operands=rebuilt_operands), combined_conditions))
        if len(expanded) > max_cases:
            return []
    return expanded


def _extract_label_value_for_selector(
    selector: Expression,
    conditions: Sequence[Condition],
) -> Optional[int]:
    selector_key = expression_key_safe(selector)
    if selector_key is None:
        return None
    for condition in conditions:
        fact = ConditionSimplifier.extract_scalar_constraint(condition)
        if fact is None or fact.kind != "eq" or fact.raw_value is None:
            continue
        if expression_key_safe(fact.expr) != selector_key:
            continue
        return int(fact.raw_value)
    return None


def _replace_expression_node(
    expr: Expression,
    needle: Expression,
    replacement: Expression,
) -> Expression:
    if expr is needle:
        return replacement
    if not getattr(expr, "operands", None):
        return expr
    return expr.clone_with(
        operands=[
            _replace_expression_node(operand, needle, replacement)
            for operand in expr.operands
        ]
    )


def _split_address_base_delta(
    expr: Expression,
    tracer,
) -> Tuple[Optional[int], Optional[Expression]]:
    constant_part, terms = _flatten_additive_expression(expr, tracer)
    if not terms:
        return None, None
    if len(terms) == 1:
        return constant_part, terms[0]
    return constant_part, _combine_add_terms(terms)


def _flatten_additive_expression(
    expr: Optional[Expression],
    tracer,
) -> Tuple[int, List[Expression]]:
    if expr is None:
        return 0, []

    concrete_value = _resolve_concrete_address_offset(expr, tracer)
    if concrete_value is not None:
        return int(concrete_value), []

    expr = _strip_known_unary_wrappers(expr)

    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD":
        left_const, left_terms = _flatten_additive_expression(expr.operands[0], tracer)
        right_const, right_terms = _flatten_additive_expression(expr.operands[1], tracer)
        return left_const + right_const, left_terms + right_terms

    if expr.expr_type == ExpressionType.INTRINSIC and getattr(expr, "name", None) == "PTRSUB" and len(expr.operands) == 2:
        base_const, base_terms = _flatten_additive_expression(expr.operands[0], tracer)
        offset_const, offset_terms = _flatten_additive_expression(expr.operands[1], tracer)
        if offset_terms:
            return 0, [expr]
        return base_const + offset_const, base_terms

    if expr.expr_type == ExpressionType.INTRINSIC and getattr(expr, "name", None) == "PTRADD" and len(expr.operands) == 3:
        base_const, base_terms = _flatten_additive_expression(expr.operands[0], tracer)
        elem_size = _resolve_concrete_address_offset(expr.operands[2], tracer)
        if elem_size is None:
            return 0, [expr]
        index_expr = _strip_known_unary_wrappers(expr.operands[1])
        scaled_index = _apply_scale(index_expr, int(elem_size))
        return base_const, base_terms + [scaled_index]

    return 0, [expr]


def _strip_scale_factor(
    expr: Expression,
    entry_size: int,
    tracer,
) -> Optional[Expression]:
    expr = _strip_known_unary_wrappers(expr)
    if entry_size <= 1:
        return expr

    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_MULT" and len(expr.operands) == 2:
        left_const = _resolve_concrete_address_offset(expr.operands[0], tracer)
        right_const = _resolve_concrete_address_offset(expr.operands[1], tracer)
        if left_const == entry_size:
            return expr.operands[1]
        if right_const == entry_size:
            return expr.operands[0]
        return None

    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_LEFT" and len(expr.operands) == 2:
        shift_amount = _resolve_concrete_address_offset(expr.operands[1], tracer)
        if shift_amount is None:
            return None
        if (1 << int(shift_amount)) == entry_size:
            return expr.operands[0]
        return None

    return None


def _strip_known_unary_wrappers(expr: Expression) -> Expression:
    current = expr
    while (
        current.expr_type == ExpressionType.UNARY_OP
        and current.operator in _VALUE_PASSTHROUGH_UNARY_OPS
        and current.operands
    ):
        current = current.operands[0]
    return current


def _normalize_subpiece_to_zext(expr: Expression) -> Expression:
    if len(expr.operands) != 2:
        return expr
    source, offset = expr.operands
    offset_value = getattr(offset, "value", None)
    if (
        offset.expr_type == ExpressionType.CONSTANT
        and isinstance(offset_value, int)
        and int(offset_value) == 0
    ):
        normalized = Expression.unary_op("INT_ZEXT", _clone_expression(source))
        normalized.size = max(1, int(getattr(expr, "size", 0) or 0), int(getattr(source, "size", 0) or 0))
        return normalized
    return expr


def _apply_scale(expr: Expression, scale: int) -> Expression:
    if scale == 1:
        return expr
    return Expression.binary_op(
        "INT_MULT",
        _clone_expression(expr),
        Expression.constant(int(scale), max(1, int(getattr(expr, "size", 0) or 0))),
    )


def _combine_add_terms(terms: Sequence[Expression]) -> Expression:
    iterator = iter(terms)
    combined = _clone_expression(next(iterator))
    for term in iterator:
        combined = Expression.binary_op("INT_ADD", combined, _clone_expression(term))
    return combined


def _clone_expression(expr: Expression) -> Expression:
    return expr.clone_with(operands=[_clone_expression(op) for op in expr.operands])


def _resolve_concrete_address_offset(expr: Optional[Expression], tracer) -> Optional[int]:
    resolver = getattr(tracer, "_resolve_concrete_address_offset", None)
    if callable(resolver):
        try:
            value = resolver(expr)
        except Exception:
            value = None
        if value is not None:
            try:
                return int(value)
            except Exception:
                return None

    if expr is None:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if runtime_ref is not None and hasattr(runtime_ref, "has_concrete_address") and runtime_ref.has_concrete_address():
        address_offset = getattr(runtime_ref, "address_offset", None)
        if address_offset is not None:
            return int(address_offset)
    if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
        return int(expr.value)
    return None


def _coerce_block_path_entries(
    path_entries,
) -> Optional[List[Tuple[List[Any], List[Condition]]]]:
    if not isinstance(path_entries, (list, tuple)):
        return None

    normalized: List[Tuple[List[Any], List[Condition]]] = []
    for entry in path_entries:
        if not isinstance(entry, (list, tuple)) or len(entry) != 2:
            return None
        block_path, conditions = entry
        if not isinstance(block_path, (list, tuple)):
            return None
        if not isinstance(conditions, (list, tuple)):
            return None
        normalized.append((list(block_path), list(conditions)))
    return normalized


def _address_identity(address) -> Optional[Tuple[Optional[int], Optional[int], Optional[str]]]:
    if address is None:
        return None
    offset = _address_offset(address)
    address_space = None
    try:
        address_space = address.getAddressSpace()
    except Exception:
        address_space = None
    try:
        space_id = int(address_space.getSpaceID()) if address_space is not None else None
    except Exception:
        space_id = None
    return (space_id, offset, _address_to_string(address))


def _address_offset(address) -> Optional[int]:
    if address is None:
        return None
    try:
        return int(address.getOffset())
    except Exception:
        return None


def _address_to_string(address) -> Optional[str]:
    if address is None:
        return None
    try:
        return str(address)
    except Exception:
        return None
