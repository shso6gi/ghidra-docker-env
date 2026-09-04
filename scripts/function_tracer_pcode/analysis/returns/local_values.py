"""Local varnode / alias expression evaluation and lookup."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple, cast
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.core.structural import StructuralKey, expression_key_safe
from scripts.function_tracer_pcode.analysis.returns._shared import (
    AnalysisFailure,
    ConditionNormalizer,
    ConditionSMTOracle,
    ConditionSimplifier,
    EffectSummary,
    PcodeTracer,
    _expressions_equivalent,
    _iter_expression_nodes,
)
from scripts.function_tracer_pcode.analysis.returns._api import StructuralRecurrenceSummarizer
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    eval_constant_raw,
)
from typing import Any, Optional, Set, Tuple


def _impl__local_varnode_key(self, varnode) -> Tuple[str, int, int]:
    try:
        addr = varnode.getAddress()
        return (addr.getAddressSpace().getName(), int(varnode.getOffset()), int(varnode.getSize()))
    except Exception:
        return ("synthetic", id(varnode), int(getattr(varnode, "getSize", lambda: 0)()))


def _impl__evaluate_local_varnode_expression(
    self,
    varnode,
    tracer,
    local_values: Dict[Tuple[str, int, int], Expression],
    local_storages: Dict[Tuple[str, int, int], Any],
    local_memory: Dict[Tuple[StructuralKey, int], Expression],
    visiting: Optional[Set[int]] = None,
) -> Expression:
    if varnode is None:
        return Expression.unknown("local_none")

    key = self._local_varnode_key(varnode)
    cached = local_values.get(key)
    if cached is not None:
        return cached

    aliased = self._lookup_local_alias_expression(varnode, tracer, local_values, local_storages)
    if aliased is not None:
        local_values[key] = aliased
        return aliased

    is_constant = getattr(varnode, "isConstant", None)
    if callable(is_constant) and is_constant():
        return Expression.constant(varnode.getOffset(), varnode.getSize())

    if visiting is None:
        visiting = set()
    marker = id(varnode)
    if marker in visiting:
        return Expression.unknown("local_cycle")
    visiting.add(marker)
    try:
        get_def = getattr(varnode, "getDef", None)
        def_op = get_def() if callable(get_def) else None
        if def_op is not None:
            evaluated = self._evaluate_local_pcode_expression(
                def_op,
                tracer,
                local_values,
                local_storages,
                local_memory,
                visiting,
            )
            if evaluated is not None:
                local_values[key] = evaluated
                return evaluated
    finally:
        visiting.discard(marker)

    return tracer.trace_varnode(varnode, use_cache=False)


def _impl__evaluate_local_pcode_expression(
    self,
    pcode_op,
    tracer,
    local_values: Dict[Tuple[str, int, int], Expression],
    local_storages: Dict[Tuple[str, int, int], Any],
    local_memory: Dict[Tuple[StructuralKey, int], Expression],
    visiting: Optional[Set[int]] = None,
) -> Optional[Expression]:
    mnemonic = pcode_op.getMnemonic()

    def _input(index: int) -> Expression:
        return self._evaluate_local_varnode_expression(
            pcode_op.getInput(index),
            tracer,
            local_values,
            local_storages,
            local_memory,
            visiting,
        )

    if mnemonic in {"COPY", "CAST"} and pcode_op.getNumInputs() >= 1:
        expr = _input(0)
        output = pcode_op.getOutput()
        if output is not None:
            expr = self._clone_expression(expr)
            expr.size = output.getSize()
        return expr

    binary_ops = {
        "INT_ADD", "INT_SUB", "INT_MULT", "INT_DIV", "INT_SDIV",
        "INT_REM", "INT_SREM", "INT_AND", "INT_OR", "INT_XOR",
        "INT_LEFT", "INT_RIGHT", "INT_SRIGHT",
        "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_SLESS",
        "INT_LESSEQUAL", "INT_SLESSEQUAL",
        "FLOAT_ADD", "FLOAT_SUB", "FLOAT_MULT", "FLOAT_DIV",
        "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL",
        "BOOL_AND", "BOOL_OR", "BOOL_XOR", "PIECE", "SUBPIECE",
        "PTRADD", "PTRSUB",
    }
    if mnemonic in binary_ops and pcode_op.getNumInputs() >= 2:
        if mnemonic == "PTRADD" and pcode_op.getNumInputs() >= 3:
            base = _input(0)
            index = _input(1)
            element_size = _input(2)
            return Expression.binary_op(
                "INT_ADD",
                base,
                Expression.binary_op("INT_MULT", index, element_size),
            )
        return Expression.binary_op(mnemonic, _input(0), _input(1))

    unary_ops = {
        "INT_NEGATE", "INT_2COMP", "BOOL_NEGATE", "INT_ZEXT", "INT_SEXT",
        "FLOAT_NEG", "FLOAT_ABS", "FLOAT_SQRT",
        "TRUNC", "FLOAT_FLOAT2FLOAT", "FLOAT_INT2FLOAT", "FLOAT_CEIL", "FLOAT_FLOOR",
        "POPCOUNT", "LZCOUNT",
    }
    if mnemonic in unary_ops and pcode_op.getNumInputs() >= 1:
        expr = Expression.unary_op(mnemonic, _input(0))
        output = pcode_op.getOutput()
        if output is not None:
            expr.size = output.getSize()
        return expr

    if mnemonic == "LOAD" and pcode_op.getNumInputs() >= 2:
        output = pcode_op.getOutput()
        size = output.getSize() if output is not None else 4
        addr_expr = _input(1)
        cached = local_memory.get(self._local_memory_key(addr_expr, size))
        if cached is not None:
            return cached
        return Expression.memory(addr_expr, size)

    return None


def _impl__lookup_local_alias_expression(
    self,
    varnode,
    tracer,
    local_values: Dict[Tuple[str, int, int], Expression],
    local_storages: Dict[Tuple[str, int, int], Any],
) -> Optional[Expression]:
    try:
        target_storage = tracer._get_storage_info_from_varnode(varnode)
    except Exception:
        return None
    if target_storage is None or not getattr(target_storage, "is_register", False):
        return None

    for key, candidate_storage in local_storages.items():
        if candidate_storage is None:
            continue
        try:
            same_base = candidate_storage.shares_base_register_with(target_storage)
            overlaps = candidate_storage.bit_range_overlaps_with(target_storage)
        except Exception:
            continue
        if not same_base or not overlaps:
            continue
        candidate_expr = local_values.get(key)
        if candidate_expr is None:
            continue
        aliased = self._clone_expression(candidate_expr)
        aliased.size = target_storage.size
        self._debug_print(
            "Local alias resolution: "
            f"{getattr(candidate_storage, 'register_name', None)} -> "
            f"{getattr(target_storage, 'register_name', None)} as {aliased.to_string()}"
        )
        return aliased
    return None


def _impl__lookup_local_expression_for_storage(
    self,
    target_storage: Optional[StorageInfo],
    local_values: Dict[Tuple[str, int, int], Expression],
    local_storages: Dict[Tuple[str, int, int], Any],
) -> Optional[Expression]:
    if target_storage is None or not getattr(target_storage, "is_register", False):
        return None

    best_expr: Optional[Expression] = None
    best_score: Optional[Tuple[int, int, int, int]] = None

    for key, candidate_storage in local_storages.items():
        if candidate_storage is None:
            continue
        try:
            same_base = candidate_storage.shares_base_register_with(target_storage)
            overlaps = candidate_storage.bit_range_overlaps_with(target_storage)
        except Exception:
            continue
        if not same_base or not overlaps:
            continue

        candidate_expr = local_values.get(key)
        if candidate_expr is None:
            continue

        candidate_size = int(getattr(candidate_storage, "size", 0) or 0)
        target_size = int(getattr(target_storage, "size", 0) or 0)
        candidate_offset = int(getattr(candidate_storage, "bit_offset_in_base", 0) or 0)
        target_offset = int(getattr(target_storage, "bit_offset_in_base", 0) or 0)
        score = (
            1 if candidate_offset == target_offset else 0,
            1 if candidate_size == target_size else 0,
            min(candidate_size, target_size),
            -abs(candidate_offset - target_offset),
        )
        if best_score is not None and score <= best_score:
            continue

        aliased = self._clone_expression(candidate_expr)
        aliased.size = max(1, target_size or getattr(aliased, "size", 0) or 0)
        best_expr = aliased
        best_score = score

    return best_expr
