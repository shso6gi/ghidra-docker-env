"""Loop side-effect profiles and safe accessors over Ghidra P-code objects."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    Condition,
    ExpressionType,
    LoopBodyEffectRef,
    LoopSideEffectProfileRef,
    canonicalize_location,
)


def _impl__loop_effect_profile_name(
    self,
    *,
    memory_reads: bool,
    memory_writes: bool,
    calls: bool,
    escapes: bool,
    conditional_guards: bool,
) -> str:
    if calls or escapes:
        return "effect_unknown"
    if memory_writes:
        return "effect_aware"
    if conditional_guards:
        return "pure_conditional"
    if memory_reads:
        return "pure_memory_read"
    return "pure"


def _impl__build_loop_side_effect_profile(
    self,
    *,
    analysis=None,
    high_function=None,
    loop_blocks: Optional[Sequence[object]] = None,
    ignored_branch_ops: Optional[Sequence[object]] = None,
    block_guard_conditions: Optional[Dict[object, Sequence[Condition]]] = None,
    block_guard_info: Optional[Dict[object, Dict[str, Any]]] = None,
    memory_reads: bool = False,
) -> LoopSideEffectProfileRef:
    descriptors: List[LoopBodyEffectRef] = []
    context_descriptors: List[LoopBodyEffectRef] = []
    has_memory_reads = bool(memory_reads)
    has_memory_writes = False
    has_calls = False
    has_escapes = False
    has_conditional_guards = False
    has_context_memory_writes = False
    has_context_calls = False
    has_context_escapes = False
    has_context_conditional_guards = False

    effect_summary = getattr(analysis, "effect_summary", None) if analysis is not None else None
    for effect in getattr(effect_summary, "effects", None) or []:
        has_context_memory_writes = True
        effect_conditions = tuple(getattr(effect, "conditions", None) or ())
        if effect_conditions:
            has_context_conditional_guards = True
        context_descriptors.append(
            LoopBodyEffectRef(
                kind="memory_write",
                source="function_effect_summary",
                scope="function",
                location=getattr(effect, "location", None),
                value_expr=getattr(effect, "value", None),
                guard_constraints=effect_conditions,
                order_key=getattr(effect, "order_key", None),
            )
        )
    if getattr(effect_summary, "has_unsupported_call", False):
        has_context_calls = True
        has_context_escapes = True
        context_descriptors.append(
            LoopBodyEffectRef(
                kind="unsupported_call",
                source="function_effect_summary",
                scope="function",
            )
        )
    if getattr(analysis, "incomplete_control_flow", False):
        has_context_escapes = True
        context_descriptors.append(
            LoopBodyEffectRef(
                kind="incomplete_control_flow",
                source="function_analysis",
                scope="function",
            )
        )

    ignored_ids = {id(op) for op in (ignored_branch_ops or ()) if op is not None}
    pcode_scope = "loop" if loop_blocks is not None else "function"
    if loop_blocks is None and high_function is not None:
        loop_blocks = list(self._iter_basic_blocks(high_function))
    for block in loop_blocks or ():
        for op in self._iter_block_ops(block):
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic == "LOAD":
                if pcode_scope == "loop":
                    has_memory_reads = True
                continue
            if mnemonic == "STORE":
                block_key = self._block_key(block)
                guard_info = (block_guard_info or {}).get(block_key, {})
                guard_conditions = tuple(
                    guard_info.get(
                        "common",
                        (block_guard_conditions or {}).get(block_key, ()),
                    )
                )
                path_condition_sets = tuple(
                    tuple(path_conditions or ())
                    for path_conditions in guard_info.get("paths", ())
                )
                store_effect = self._store_effect_ref_for_op(
                    op,
                    scope=pcode_scope,
                    guard_constraints=guard_conditions,
                    path_condition_sets=path_condition_sets,
                    guard_paths_incomplete=bool(guard_info.get("incomplete", False)),
                )
                if pcode_scope == "loop":
                    has_memory_writes = True
                    descriptors.append(store_effect)
                else:
                    has_context_memory_writes = True
                    context_descriptors.append(store_effect)
                continue
            if mnemonic in {"CALL", "CALLIND"}:
                call_effect = LoopBodyEffectRef(
                    kind="call",
                    source="pcode_scan",
                    scope=pcode_scope,
                    target_ref=self._call_target_ref_for_op(op),
                    order_key=self._pcode_op_order_key(op),
                )
                if pcode_scope == "loop":
                    has_calls = True
                    has_escapes = True
                    descriptors.append(call_effect)
                else:
                    has_context_calls = True
                    has_context_escapes = True
                    context_descriptors.append(call_effect)
                continue
            if mnemonic == "BRANCHIND":
                escape_effect = LoopBodyEffectRef(
                    kind="escape",
                    source="pcode_scan",
                    scope=pcode_scope,
                    order_key=self._pcode_op_order_key(op),
                )
                if pcode_scope == "loop":
                    has_escapes = True
                    descriptors.append(escape_effect)
                else:
                    has_context_escapes = True
                    context_descriptors.append(escape_effect)
                continue
            if mnemonic == "CBRANCH" and id(op) not in ignored_ids:
                condition = self._condition_for_cbranch_op(op)
                guard_effect = LoopBodyEffectRef(
                    kind="conditional_guard",
                    source="pcode_scan",
                    scope=pcode_scope,
                    guard_constraints=(condition,) if condition is not None else (),
                    order_key=self._pcode_op_order_key(op),
                )
                if pcode_scope == "loop":
                    has_conditional_guards = True
                    descriptors.append(guard_effect)
                else:
                    has_context_conditional_guards = True
                    context_descriptors.append(guard_effect)

    guard_count = sum(1 for effect in descriptors if effect.kind == "conditional_guard")
    profile = self._loop_effect_profile_name(
        memory_reads=has_memory_reads,
        memory_writes=has_memory_writes,
        calls=has_calls,
        escapes=has_escapes,
        conditional_guards=has_conditional_guards,
    )
    return LoopSideEffectProfileRef(
        profile=profile,
        memory_reads=has_memory_reads,
        memory_writes=has_memory_writes,
        calls=has_calls,
        escapes=has_escapes,
        conditional_guards=has_conditional_guards,
        context_memory_writes=has_context_memory_writes,
        context_calls=has_context_calls,
        context_escapes=has_context_escapes,
        context_conditional_guards=has_context_conditional_guards,
        effect_count=len(descriptors),
        guard_count=guard_count,
        effect_descriptors=tuple(descriptors),
        context_descriptors=tuple(context_descriptors),
    )


def _impl__store_effect_ref_for_op(
    self,
    op,
    *,
    scope: str,
    guard_constraints: Sequence[Condition] = (),
    path_condition_sets: Sequence[Sequence[Condition]] = (),
    guard_paths_incomplete: bool = False,
) -> LoopBodyEffectRef:
    address_space = None
    address_expr = None
    value_expr = None
    unkeyable_reasons: List[str] = []
    input_count = self._safe_pcode_input_count(op)
    if input_count >= 3:
        address_space = self._store_address_space_ref_for_op(op)
        try:
            address_expr = self._build_pcode_expression(op.getInput(1), placeholders={})
        except RecursionError:
            address_expr = None
        try:
            value_expr = self._build_pcode_expression(op.getInput(2), placeholders={})
        except RecursionError:
            value_expr = None
    if address_space is None:
        unkeyable_reasons.append("store_address_space_unresolved")
    if address_expr is None or self._expression_is_unresolved(address_expr):
        address_expr = None
        unkeyable_reasons.append("store_address_unresolved")
    if value_expr is None or self._expression_is_unresolved(value_expr):
        value_expr = None
        unkeyable_reasons.append("store_value_unresolved")
    if guard_paths_incomplete:
        unkeyable_reasons.append("store_guard_paths_incomplete")
    return LoopBodyEffectRef(
        kind="memory_write",
        source="pcode_scan",
        scope=scope,
        address_space=address_space,
        location=address_expr,
        value_expr=value_expr,
        guard_constraints=tuple(guard_constraints or ()),
        path_condition_sets=tuple(
            tuple(path_conditions or ())
            for path_conditions in (path_condition_sets or ())
        ),
        guard_paths_incomplete=bool(guard_paths_incomplete),
        order_key=self._pcode_op_order_key(op),
        keyable=not unkeyable_reasons,
        unkeyable_reason=";".join(unkeyable_reasons) if unkeyable_reasons else None,
    )


def _impl__safe_call(self, obj, method_name: str):
    method = getattr(obj, method_name, None)
    if not callable(method):
        return None
    try:
        return method()
    except (AttributeError, TypeError, ValueError, RuntimeError):
        return None


def _impl__safe_bool_call(self, obj, method_name: str) -> Optional[bool]:
    value = self._safe_call(obj, method_name)
    if value is None:
        return None
    return bool(value)


def _impl__safe_int(self, value) -> Optional[int]:
    if value is None:
        return None
    try:
        return int(value)
    except (TypeError, ValueError, OverflowError):
        return None


def _impl__call_target_ref_for_op(self, op):
    if op is None or self._safe_pcode_input_count(op) < 1:
        return None
    resolver = getattr(self.tracer, "resolve_call_target_ref", None)
    if not callable(resolver):
        return None
    try:
        return resolver(op.getInput(0))
    except (AttributeError, TypeError, ValueError, RecursionError):
        return None


def _impl__safe_pcode_input_count(self, op) -> int:
    try:
        value = getattr(op, "getNumInputs", lambda: 0)()
        if not isinstance(value, (int, float, str, bytes)):
            return 0
        return int(value or 0)
    except Exception:
        return 0


def _impl__varnode_def_is_multiequal(self, varnode) -> bool:
    if varnode is None:
        return False
    definition = getattr(varnode, "getDef", lambda: None)()
    return getattr(definition, "getMnemonic", lambda: None)() == "MULTIEQUAL"


def _impl__safe_pcode_input_varnode(self, op, index: int):
    try:
        return op.getInput(int(index))
    except Exception:
        return None


def _impl__parameter_bases_memory_reads(
    self,
    analysis,
    param: dict,
) -> bool:
    for ret in analysis.returns or []:
        for node in self._iter_expression_nodes(ret.value):
            if node.expr_type == ExpressionType.MEMORY and node.operands:
                location = canonicalize_location(
                    node.operands[0],
                    analysis.parameters or [],
                    size=max(1, int(getattr(node, "size", 0) or 0) or 1),
                )
                if location is not None and location.base_ref.matches_parameter(param):
                    return True
            if node.expr_type == ExpressionType.INTRINSIC and getattr(node, "name", None) == "PTRADD":
                base_name = self._parameter_name_from_expr(node.operands[0] if node.operands else None)
                if base_name and base_name == param.get("name"):
                    return True
    return False
