"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence_summary``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    ExpressionType,
    LoopSideEffectProfileRef,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__collect_state_transition_loop_phi_ops(
    self,
    loop_blocks: Sequence[object],
    preferred_phi_ops: Sequence[object],
) -> Tuple[object, ...]:
    result = []
    seen = set()

    def add(phi_op) -> None:
        key = id(phi_op)
        if key not in seen:
            seen.add(key)
            result.append(phi_op)

    for phi_op in preferred_phi_ops or ():
        add(phi_op)
    for block in loop_blocks or ():
        for op in self._iter_block_ops(block):
            if (
                getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL"
                and getattr(op, "getOutput", lambda: None)() is not None
            ):
                add(op)
    return tuple(result)

def _impl__normalize_state_transition_state_guard(
    self,
    state_guard: Optional[Expression],
    state_placeholder: Expression,
) -> Optional[Expression]:
    guard = self._canonicalize_expression(state_guard)
    if guard is None:
        return None
    placeholder_key = state_placeholder.structural_key()

    def is_placeholder(value: Optional[Expression]) -> bool:
        if value is None:
            return False
        try:
            return value.structural_key() == placeholder_key
        except (AttributeError, TypeError, ValueError, RecursionError):
            return False

    if (
        guard.expr_type == ExpressionType.UNARY_OP
        and guard.operator == "BOOL_NEGATE"
        and len(guard.operands) == 1
    ):
        inner = self._canonicalize_expression(guard.operands[0])
        if (
            inner.expr_type == ExpressionType.BINARY_OP
            and inner.operator == "INT_SLESS"
            and len(inner.operands) == 2
            and is_placeholder(inner.operands[0])
            and self._raw_constant_value(inner.operands[1]) == 1
        ):
            return self._positive_state_guard_expression(state_placeholder)
    if (
        guard.expr_type == ExpressionType.BINARY_OP
        and guard.operator == "INT_SLESSEQUAL"
        and len(guard.operands) == 2
        and self._raw_constant_value(guard.operands[0]) == 1
        and is_placeholder(guard.operands[1])
    ):
        return self._positive_state_guard_expression(state_placeholder)
    return guard

def _impl__extract_multiplicative_accumulator_transition(
    self,
    expr: Expression,
    accumulator_placeholder: Expression,
) -> Optional[Expression]:
    expr = self._canonicalize_expression(expr)
    if expr is None:
        return None
    multiplier = self._multiplicative_accumulator_delta_multiplier(
        expr,
        accumulator_placeholder,
    )
    if multiplier is None or int(multiplier) in {0, 1}:
        return None
    return expr

def _impl__state_transition_model_priority(
    self,
    model: StateTransitionLoopModel,
) -> Tuple[int, int, int]:
    return (
        1 if self._varnode_reaches_return(model.accumulator_phi_output) else 0,
        len(model.loop_blocks),
        max(1, int(getattr(model.state_phi_output, "getSize", lambda: 0)() or 0)),
    )

def _impl__collect_state_transition_loop_blocks(
    self,
    *,
    header_block,
    body_block,
    exit_block,
    backedge_indices: Sequence[int],
) -> Tuple[object, ...]:
    header_key = self._block_key(header_block)
    exit_key = self._block_key(exit_block)
    blocks_by_key: Dict[object, object] = {}

    def add(block) -> None:
        key = self._block_key(block)
        if key is not None and key != exit_key and key not in blocks_by_key:
            blocks_by_key[key] = block

    add(header_block)
    add(body_block)
    in_size = int(getattr(header_block, "getInSize", lambda: 0)() or 0)
    stack = []
    for index in backedge_indices:
        if index < in_size:
            predecessor = header_block.getIn(index)
            add(predecessor)
            stack.append(predecessor)
    while stack:
        current = stack.pop()
        current_key = self._block_key(current)
        if current_key == header_key:
            continue
        for predecessor in self._collect_block_predecessors(current):
            predecessor_key = self._block_key(predecessor)
            if predecessor_key in {None, exit_key}:
                continue
            if not self._can_reach_block(body_block, predecessor) and predecessor_key != header_key:
                continue
            if predecessor_key not in blocks_by_key:
                blocks_by_key[predecessor_key] = predecessor
                stack.append(predecessor)
    return tuple(blocks_by_key.values())

def _impl__build_state_transition_loop_side_effect_profile(
    self,
    *,
    loop_blocks: Sequence[object],
) -> LoopSideEffectProfileRef:
    memory_reads = False
    memory_writes = False
    calls = False
    escapes = False
    conditional_guards = False
    for block in loop_blocks or ():
        for op in self._iter_block_ops(block):
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic == "LOAD":
                memory_reads = True
            elif mnemonic == "STORE":
                memory_writes = True
            elif mnemonic in {"CALL", "CALLIND"}:
                calls = True
                escapes = True
            elif mnemonic == "BRANCHIND":
                escapes = True
            elif mnemonic == "CBRANCH":
                conditional_guards = True
    return LoopSideEffectProfileRef(
        profile=self._loop_effect_profile_name(
            memory_reads=memory_reads,
            memory_writes=memory_writes,
            calls=calls,
            escapes=escapes,
            conditional_guards=conditional_guards,
        ),
        memory_reads=memory_reads,
        memory_writes=memory_writes,
        calls=calls,
        escapes=escapes,
        conditional_guards=conditional_guards,
        effect_count=0,
        guard_count=1 if conditional_guards else 0,
    )
