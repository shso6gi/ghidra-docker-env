"""Block-path reasoning around call sites: path ops, MULTIEQUAL inputs and live-in argument recovery."""

from __future__ import annotations

from typing import Dict, Iterator, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core import Condition, Expression, StorageInfo
from scripts.function_tracer_pcode.analysis.effects._shared import (
    CallArgumentWidthEvidence,
    ConditionSimplifier,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _coerce_storage_info,
    _find_block_info_for_pcode_op,
    _parameter_declared_semantic_size_bytes,
    _parameter_expression_from_descriptor,
    _parameter_semantic_size_bytes,
    _path_writes_storage,
    _pcode_op_ref_key_from_tracker,
    _reduce_expression_under_conditions,
    _resolve_call_argument_expression,
    _resolve_live_in_parameter_descriptor_for_call_storage,
    _storage_identity_key,
    _try_get_order_key,
)


def _impl__find_block_info_for_pcode_op(condition_tracker, pcode_op):
    if condition_tracker is None or pcode_op is None:
        return None
    block_index = getattr(condition_tracker, "block_by_index", None)
    if not isinstance(block_index, dict):
        return None
    target_key = _pcode_op_ref_key_from_tracker(condition_tracker, pcode_op)
    for block_info in block_index.values():
        try:
            pcode_ops = getattr(block_info, "pcode_ops", None) or []
            if any(
                candidate is pcode_op
                or (
                    target_key is not None
                    and _pcode_op_ref_key_from_tracker(condition_tracker, candidate) == target_key
                )
                for candidate in pcode_ops
            ):
                return block_info
        except Exception:
            continue
    return None


def _impl__pcode_op_ref_key_from_tracker(condition_tracker, pcode_op) -> Optional[Tuple[object, ...]]:
    tracer = getattr(condition_tracker, "tracer", None)
    make_ref = getattr(tracer, "_make_pcode_op_ref", None)
    if not callable(make_ref):
        return None
    try:
        ref = make_ref(pcode_op)
    except Exception:
        return None
    stable_key = getattr(ref, "stable_key", None)
    if not callable(stable_key):
        return None
    try:
        return stable_key()
    except Exception:
        return None


def _impl__iter_path_ops_before_call(path_blocks, call_op) -> Iterator[object]:
    call_order = _try_get_order_key(call_op)
    if call_order is None:
        return
    for block_info in path_blocks or []:
        for op in getattr(block_info, "pcode_ops", None) or []:
            if op is call_op:
                return
            op_order = _try_get_order_key(op)
            if op_order is None or op_order >= call_order:
                continue
            yield op


def _impl__compatible_call_block_paths(
    call_op,
    condition_tracker,
    current_conditions: Optional[Sequence[Condition]],
) -> Optional[List[Tuple[List[object], List[Condition]]]]:
    if condition_tracker is None:
        return None
    call_block = _find_block_info_for_pcode_op(condition_tracker, call_op)
    if call_block is None:
        return None
    get_paths = getattr(condition_tracker, "get_all_valid_block_paths_to_block", None)
    if not callable(get_paths):
        return None

    compatible: List[Tuple[List[object], List[Condition]]] = []
    try:
        path_results = list(get_paths(call_block) or [])
    except Exception:
        return None
    if not path_results:
        return None

    for blocks, path_conditions in path_results:
        merged = ConditionSimplifier.simplify_conditions(
            list(path_conditions or []) + list(current_conditions or []),
        )
        if ConditionSimplifier.is_contradiction(merged):
            continue
        compatible.append((list(blocks or []), list(path_conditions or [])))
    return compatible


def _impl__resolve_multiequal_input_for_path(
    op,
    path_blocks,
    tracer,
    caller_parameters: Sequence[Dict],
    current_conditions: Optional[Sequence[Condition]],
) -> Optional[Expression]:
    if op is None or getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
        return None
    if not path_blocks:
        return None

    op_block = None
    for idx, block_info in enumerate(path_blocks):
        try:
            if any(candidate is op for candidate in (getattr(block_info, "pcode_ops", None) or [])):
                op_block = (idx, block_info)
                break
        except Exception:
            continue
    if op_block is None:
        return None

    path_index, block_info = op_block
    if path_index <= 0:
        return None
    predecessor = path_blocks[path_index - 1]
    ghidra_block = getattr(block_info, "block", None)
    if ghidra_block is None:
        return None

    try:
        in_size = int(ghidra_block.getInSize())
    except Exception:
        return None

    predecessor_block = getattr(predecessor, "block", predecessor)
    for input_index in range(min(int(op.getNumInputs()), in_size)):
        try:
            incoming = ghidra_block.getIn(input_index)
        except Exception:
            incoming = None
        if incoming is None:
            continue
        incoming_index = getattr(incoming, "getIndex", lambda: None)()
        predecessor_index = getattr(predecessor_block, "getIndex", lambda: None)()
        if incoming is not predecessor_block and incoming_index != predecessor_index:
            continue
        try:
            input_varnode = op.getInput(input_index)
        except Exception:
            return None
        expr = _resolve_call_argument_expression(input_varnode, tracer, caller_parameters)
        reduced = _reduce_expression_under_conditions(
            expr,
            list(current_conditions or []),
        )
        return reduced if reduced is not None else expr

    return None


def _impl__recover_unmodified_live_in_argument(
    ops: Sequence[object],
    target_storage: StorageInfo,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_param: Dict,
) -> Optional[Expression]:
    if _path_writes_storage(ops, target_storage, tracer):
        return None
    declared_target_size = _parameter_declared_semantic_size_bytes(callee_param)
    target_size = declared_target_size or _parameter_semantic_size_bytes(callee_param)
    descriptor = _resolve_live_in_parameter_descriptor_for_call_storage(
        caller_parameters,
        target_storage,
        required_size_bytes=declared_target_size,
        allow_register_fragment_extension=declared_target_size is None,
    )
    if descriptor is None:
        return None
    try:
        source_size = int(_parameter_semantic_size_bytes(descriptor) or descriptor.get("size") or 0)
    except Exception:
        source_size = 0
    try:
        target_size = int(target_size or callee_param.get("size") or target_storage.size or source_size or 0)
    except Exception:
        target_size = source_size
    source_size = source_size if source_size > 0 else target_size
    expr = _parameter_expression_from_descriptor(descriptor, size=source_size or None)
    if expr is None:
        return None
    if target_size > source_size:
        if declared_target_size is not None:
            return None
        source_storage = _coerce_storage_info(descriptor.get("storage"))
        expr = expr.clone_with(
            call_argument_width_evidence=CallArgumentWidthEvidence(
                source_bits=max(1, int(source_size or 0)) * 8,
                target_bits=max(
                    max(1, int(target_size or 0)) * 8,
                    int(getattr(target_storage, "size_bits", 0) or 0),
                ),
                source_storage_key=_storage_identity_key(source_storage),
                target_storage_key=_storage_identity_key(target_storage),
            )
        )
    return expr
