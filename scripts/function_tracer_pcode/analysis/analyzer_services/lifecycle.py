"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.analyzer``."""

from __future__ import annotations

from typing import Any, Optional, Tuple
from ._shared import (
    ANALYSIS_STATUS_ANALYSIS_EXCEPTION,
    ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
    AnalysisFailure,
    Condition,
    ConditionTracker,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
)

def _impl__program_is_big_endian(self) -> Optional[bool]:
    language_getter = getattr(self.program, "getLanguage", None)
    if not callable(language_getter):
        return None
    try:
        language = language_getter()
        is_big_endian = getattr(language, "isBigEndian", None)
        if callable(is_big_endian):
            return bool(is_big_endian())
    except Exception:
        return None
    return None

def _impl__program_identity(self) -> Optional[int]:
    try:
        getter = getattr(self.program, "getUniqueProgramID", None)
        if callable(getter):
            return int(getter())
    except Exception:
        return None
    return None

def _impl__get_decompiler(self):
    if self._decompiler is None:
        from ghidra.app.decompiler import DecompInterface # type: ignore[import]
        self._decompiler = DecompInterface()
        self._decompiler.openProgram(self.program)
    return self._decompiler

def _impl__program_transaction(self, description: str):
    start_transaction = getattr(self.program, "startTransaction", None)
    end_transaction = getattr(self.program, "endTransaction", None)
    if not callable(start_transaction) or not callable(end_transaction):
        yield
        return

    tx_id = start_transaction(description)
    try:
        yield
        end_transaction(tx_id, True)
    except Exception:
        end_transaction(tx_id, False)
        raise

def _impl__decompose_comparison_condition(
    self,
    condition: Condition,
) -> Optional[Tuple[bool, str, Expression, Expression]]:
    """条件を比較式 `(negated, op, left, right)` に展開。"""
    expr = condition.expression
    negated = bool(condition.negated)
    while expr is not None and expr.expr_type == ExpressionType.UNARY_OP:
        if expr.operator == "BOOL_NEGATE":
            negated = not negated
            expr = expr.operands[0] if expr.operands else None
            continue
        break
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) < 2:
        return None
    return (
        negated,
        expr.operator or "",
        expr.operands[0],
        expr.operands[1],
    )

def _impl__program_userop_name(self, userop_id: Optional[int]) -> Optional[str]:
    if userop_id is None:
        return None
    language = getattr(self.program, "getLanguage", lambda: None)()
    get_name = getattr(language, "getUserDefinedOpName", None)
    if not callable(get_name):
        return None
    try:
        name = get_name(int(userop_id))
    except Exception:
        return None
    return str(name) if name else None

def _impl__find_block_info_for_program_offset(
    self,
    condition_tracker: ConditionTracker,
    address_value: int,
):
    block_by_index = getattr(condition_tracker, "block_by_index", None) or {}
    for block_info in block_by_index.values():
        block = getattr(block_info, "block", None)
        if block is None:
            continue
        start_offset = self._address_offset_for_block_endpoint(getattr(block, "getStart", lambda: None)())
        stop_offset = self._address_offset_for_block_endpoint(getattr(block, "getStop", lambda: None)())
        if start_offset is None:
            continue
        if stop_offset is None:
            stop_offset = start_offset
        lo = min(start_offset, stop_offset)
        hi = max(start_offset, stop_offset)
        if lo <= int(address_value) <= hi:
            return block_info
    return None

def _impl__decompile_function(self, function, timeout: int = 60):
    try:
        from ..decompilation_broker import (
            LIFECYCLE_HELPER_SOURCE_CONTRACT,
            decompile_function,
        )
        results = decompile_function(
            self, function, timeout, None,
            source_contract_id=LIFECYCLE_HELPER_SOURCE_CONTRACT,
            semantic_owner="subordinate",
        )
        if not results.decompileCompleted():
            return None
        return results
    except Exception:
        return None

def _impl__resolve_function_from_program_offset(self, address_value: int):
    if self.program is None or address_value < 0:
        return None
    try:
        address_factory = self.program.getAddressFactory()
        if address_factory is None:
            return None
        default_space = address_factory.getDefaultAddressSpace()
        if default_space is None:
            return None
        address = default_space.getAddress(address_value)
    except Exception:
        return None
    return self._resolve_function_from_address(address)

def _impl_analyze_function_by_name(self, function_name: str, timeout: int = 60) -> Optional[FunctionReturnAnalysis]:
    self._last_function_lookup_error = None
    self._last_analysis_failure = None
    function = self._find_function_by_name(function_name)
    if function is None:
        message = f"Function '{function_name}' not found"
        self._last_function_lookup_error = message
        self._last_analysis_failure = AnalysisFailure(
            status=ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
            message=message,
            function_name=function_name,
        )
        self._debug_print(self._last_function_lookup_error)
        return None
    try:
        return self.analyze_function(function, timeout)
    except Exception as exc:
        self._last_analysis_failure = AnalysisFailure(
            status=ANALYSIS_STATUS_ANALYSIS_EXCEPTION,
            message=str(exc),
            function_name=function_name,
        )
        raise

def _impl__find_function_by_name(self, function_name: str):
    if not function_name:
        return None
    function_manager = self._get_function_manager()
    if function_manager is None:
        return None
    try:
        for func in function_manager.getFunctions(True):
            if func.getName() == function_name:
                return func
    except Exception:
        return None
    return None
