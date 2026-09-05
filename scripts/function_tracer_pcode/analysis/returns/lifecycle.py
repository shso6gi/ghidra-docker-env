"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.returns.analyzer``."""

from __future__ import annotations

from contextlib import contextmanager
from typing import Any, Callable, Dict, List, Optional, Set, Tuple
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.analysis.returns._shared import (
    ANALYSIS_STATUS_ANALYSIS_EXCEPTION,
    ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
    AnalysisFailure,
    ConditionTracker,
)
from scripts.function_tracer_pcode.analysis.returns._shared import ConditionNormalizer, EffectSummary
from scripts.function_tracer_pcode.analysis.returns._api import PcodeTracer
from scripts.function_tracer_pcode.analysis.returns.debug_reporter import DebugReporter


def decompose_comparison_condition(condition: Condition) -> Optional[Tuple[bool, str, Expression, Expression]]:
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


def _impl__decompose_comparison_condition(self, condition: Condition):
    return decompose_comparison_condition(condition)


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


def _impl__current_function_entry_address(self):
    if self._current_function_entry_address_value is not None:
        return self._current_function_entry_address_value
    prototype = self._current_function_prototype
    for getter_name in ("getFunction", "getFunctionDefinition"):
        getter = getattr(prototype, getter_name, None)
        if not callable(getter):
            continue
        try:
            function = getter()
        except Exception:
            function = None
        entry_getter = getattr(function, "getEntryPoint", None)
        if callable(entry_getter):
            try:
                return entry_getter()
            except Exception:
                return None
    return None


def function_entry_address(function):
    entry_getter = getattr(function, "getEntryPoint", None)
    if not callable(entry_getter):
        return None
    try:
        return entry_getter()
    except Exception:
        return None


def _impl__function_entry_address(function):
    return function_entry_address(function)


def _impl__analysis_context(
    self,
    parameters: List[Dict],
    effect_summary: Optional[EffectSummary],
    function_prototype=None,
    function_entry_address=None,
):
    """Temporarily bind per-analysis state and restore the parent context on exit."""
    previous_parameters = self._current_parameters
    previous_effect_summary = self._current_effect_summary
    previous_deferred_calls = self._current_deferred_calls
    previous_function_prototype = self._current_function_prototype
    previous_function_entry_address = self._current_function_entry_address_value
    previous_noreturn_observations = self._current_noreturn_terminal_observations
    self._current_parameters = parameters
    self._current_effect_summary = effect_summary
    self._current_deferred_calls = {}
    self._current_function_prototype = function_prototype
    self._current_function_entry_address_value = function_entry_address
    self._current_noreturn_terminal_observations = []
    try:
        yield
    finally:
        self._current_parameters = previous_parameters
        self._current_effect_summary = previous_effect_summary
        self._current_deferred_calls = previous_deferred_calls
        self._current_function_prototype = previous_function_prototype
        self._current_function_entry_address_value = previous_function_entry_address
        self._current_noreturn_terminal_observations = previous_noreturn_observations


def collect_java_or_python_iterable(value) -> Tuple[Tuple[Any, ...], bool]:
    if value is None:
        return (), False
    has_next = getattr(value, "hasNext", None)
    next_item = getattr(value, "next", None)
    items: List[Any] = []
    if callable(has_next) and callable(next_item):
        while True:
            try:
                has_item = has_next()
                if not isinstance(has_item, bool):
                    return tuple(items), False
                if not has_item:
                    break
                items.append(next_item())
            except Exception:
                return tuple(items), False
        return tuple(items), True
    try:
        iterator = iter(value)
    except TypeError:
        return (), False
    try:
        for item in iterator:
            items.append(item)
    except Exception:
        return tuple(items), False
    return tuple(items), True


def _impl__collect_java_or_python_iterable(value):
    return collect_java_or_python_iterable(value)


def function_cache_key(function) -> Optional[Tuple[Any, ...]]:
    if function is None:
        return None
    try:
        return (str(function.getEntryPoint()),)
    except Exception:
        return None


def _impl__function_cache_key(self, function):
    return function_cache_key(function)


def _impl__analysis_scope_key(
    self,
    target,
    bound_parameter_values: Optional[Dict[int, Expression]] = None,
    bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
) -> Tuple[Any, ...]:
    target_ref = self._coerce_runtime_target_ref(target)
    if target_ref is None and target is not None:
        try:
            if hasattr(target, "getEntryPoint"):
                target_ref = CallTargetRef.from_function(target)
        except Exception:
            target_ref = None
    target_key = (
        self._target_active_key(target_ref)
        if target_ref is not None
        else self._function_cache_key(target)
    ) or ("unknown_target",)
    normalized_bound_parameter_values = self._normalize_bound_parameter_values(
        bound_parameter_values,
    )
    bound_signature = tuple(
        (
            int(index),
            ConditionNormalizer.expression_signature(
                expr,
                include_memory_read_order=False,
            ),
        )
        for index, expr in sorted(normalized_bound_parameter_values.items())
    )
    normalized_bound_parameter_storage_values = self._normalize_bound_parameter_storage_values(
        bound_parameter_storage_values,
    )
    storage_bound_signature = tuple(
        (
            tuple(key),
            ConditionNormalizer.expression_signature(
                expr,
                include_memory_read_order=False,
            ),
        )
        for key, expr in sorted(
            normalized_bound_parameter_storage_values.items(),
            key=lambda item: repr(item[0]),
        )
    )
    return ("analysis_scope", target_key, bound_signature, storage_bound_signature)


def _impl__extend_active_functions(
    self,
    active_functions: Optional[Set[Tuple[Any, ...]]],
    target_ref: Optional[CallTargetRef],
) -> Set[Tuple[Any, ...]]:
    scoped = set(active_functions or set())
    active_key = self._target_active_key(target_ref)
    if active_key is not None:
        scoped.add(active_key)
    return scoped


class ProgramAccessService:
    """ReturnAnalyzer から切り出した program / decompiler アクセス（lifecycle family B 群）の collaborator。

    facade 状態は program / binary id / debug フラグを supplier で読む。decompiler の遅延生成と破棄は
    ``decompiler_value`` supplier と ``set_decompiler`` setter を通し、**所有権は ReturnAnalyzer に残す**
    （既存の ``analyzer._decompiler`` seam と ``dispose()`` のリソース所有を変えない）。
    デバッグ出力は ``DebugReporter`` 直接依存。broker の decompile は facade 経由の
    ``decompile_with_broker`` callable（broker は analyzer を第 1 引数に取る）。
    未抽出 family（control_recovery）が所有する ``address_offset_for_block_endpoint`` は facade 経由 callable。
    """

    def __init__(
        self,
        *,
        debug_reporter: DebugReporter,
        address_offset_for_block_endpoint: Callable[..., Any],
        decompile_with_broker: Callable[..., Any],
        program_value: Callable[..., Any],
        binary_id_value: Callable[..., Any],
        debug_flag: Callable[..., Any],
        decompiler_value: Callable[..., Any],
        set_decompiler: Callable[..., Any],
    ) -> None:
        self.debug_reporter = debug_reporter
        self.address_offset_for_block_endpoint = address_offset_for_block_endpoint
        self.decompile_with_broker = decompile_with_broker
        self.program_value = program_value
        self.binary_id_value = binary_id_value
        self.debug_flag = debug_flag
        self.decompiler_value = decompiler_value
        self.set_decompiler = set_decompiler

    def program_is_big_endian(self) -> Optional[bool]:
        language_getter = getattr(self.program_value(), "getLanguage", None)
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

    def program_identity(self) -> Optional[int]:
        try:
            getter = getattr(self.program_value(), "getUniqueProgramID", None)
            if callable(getter):
                return int(getter())
        except Exception:
            return None
        return None

    def get_decompiler(self):
        decompiler = self.decompiler_value()
        if decompiler is None:
            from ghidra.app.decompiler import DecompInterface # type: ignore[import]
            decompiler = DecompInterface()
            # 旧実装と同じ順序: openProgram() より前に facade へ保存する。openProgram() が例外を投げても
            # instance は facade に残り、後続の dispose() で回収できる。
            self.set_decompiler(decompiler)
            decompiler.openProgram(self.program_value())
        return decompiler

    @contextmanager
    def program_transaction(self, description: str):
        start_transaction = getattr(self.program_value(), "startTransaction", None)
        end_transaction = getattr(self.program_value(), "endTransaction", None)
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

    def program_userop_name(self, userop_id: Optional[int]) -> Optional[str]:
        if userop_id is None:
            return None
        language = getattr(self.program_value(), "getLanguage", lambda: None)()
        get_name = getattr(language, "getUserDefinedOpName", None)
        if not callable(get_name):
            return None
        try:
            name = get_name(int(userop_id))
        except Exception:
            return None
        return str(name) if name else None

    def find_block_info_for_program_offset(
        self,
        condition_tracker: ConditionTracker,
        address_value: int,
    ):
        block_by_index = getattr(condition_tracker, "block_by_index", None) or {}
        for block_info in block_by_index.values():
            block = getattr(block_info, "block", None)
            if block is None:
                continue
            start_offset = self.address_offset_for_block_endpoint(getattr(block, "getStart", lambda: None)())
            stop_offset = self.address_offset_for_block_endpoint(getattr(block, "getStop", lambda: None)())
            if start_offset is None:
                continue
            if stop_offset is None:
                stop_offset = start_offset
            lo = min(start_offset, stop_offset)
            hi = max(start_offset, stop_offset)
            if lo <= int(address_value) <= hi:
                return block_info
        return None

    def decompile_function(self, function, timeout: int = 60):
        try:
            from scripts.function_tracer_pcode.ghidra.decompilation_broker import LIFECYCLE_HELPER_SOURCE_CONTRACT
            # broker は analyzer（facade）を第 1 引数に取るため、facade 経由の callable で呼ぶ
            results = self.decompile_with_broker(
                function, timeout, None,
                source_contract_id=LIFECYCLE_HELPER_SOURCE_CONTRACT,
                semantic_owner="subordinate",
            )
            if not results.decompileCompleted():
                return None
            return results
        except Exception:
            return None

    def resolve_function_from_program_offset(self, address_value: int):
        if self.program_value() is None or address_value < 0:
            return None
        try:
            address_factory = self.program_value().getAddressFactory()
            if address_factory is None:
                return None
            default_space = address_factory.getDefaultAddressSpace()
            if default_space is None:
                return None
            address = default_space.getAddress(address_value)
        except Exception:
            return None
        return self.resolve_function_from_address(address)

    def find_function_by_name(self, function_name: str):
        if not function_name:
            return None
        function_manager = self.get_function_manager()
        if function_manager is None:
            return None
        try:
            for func in function_manager.getFunctions(True):
                if func.getName() == function_name:
                    return func
        except Exception:
            return None
        return None

    def dispose(self):
        decompiler = self.decompiler_value()
        if decompiler is not None:
            try:
                decompiler.dispose()
            except Exception as exc:
                exc_text = str(exc).lower()
                if "jvm is not running" not in exc_text and "java virtual machine is not running" not in exc_text:
                    raise
            finally:
                self.set_decompiler(None)

    def make_tracer(
        self,
        high_function,
        *,
        bound_parameter_values: Optional[Dict[int, Expression]] = None,
        bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
    ) -> PcodeTracer:
        try:
            return PcodeTracer(
                self.program_value(),
                high_function,
                debug=self.debug_flag(),
                bound_parameter_values=bound_parameter_values,
                bound_parameter_storage_values=bound_parameter_storage_values,
                binary_id=self.binary_id_value(),
            )
        except TypeError:
            return PcodeTracer(
                self.program_value(),
                high_function,
                debug=self.debug_flag(),
            )

    def get_instruction_with_fallback(self, addr):
        listing = self.program_value().getListing()
        instruction = listing.getInstructionAt(addr)
        if instruction is not None:
            return instruction

        containing_instruction = getattr(listing, "getInstructionContaining", None)
        if callable(containing_instruction):
            instruction = containing_instruction(addr)
            if instruction is not None:
                return instruction

        if self.attempt_disassemble_at(addr):
            instruction = listing.getInstructionAt(addr)
            if instruction is not None:
                return instruction
            if callable(containing_instruction):
                instruction = containing_instruction(addr)
                if instruction is not None:
                    return instruction

        return None

    def attempt_disassemble_at(self, addr) -> bool:
        try:
            from ghidra.app.cmd.disassemble import DisassembleCommand  # type: ignore[import]
        except Exception:
            self.debug_reporter.debug_print(f"Local target disassembly unavailable at {addr}: import failed")
            return False

        try:
            command = DisassembleCommand(addr, None, True)
        except TypeError:
            try:
                command = DisassembleCommand(addr, None)
            except Exception as exc:
                self.debug_reporter.debug_print(f"Local target disassembly setup failed at {addr}: {exc}")
                return False
        except Exception as exc:
            self.debug_reporter.debug_print(f"Local target disassembly setup failed at {addr}: {exc}")
            return False

        try:
            with self.program_transaction(f"Disassemble local target {addr}"):
                applied = command.applyTo(self.program_value())
        except Exception as exc:
            self.debug_reporter.debug_print(f"Local target disassembly failed at {addr}: {exc}")
            return False

        if applied:
            self.debug_reporter.debug_print(f"Local target disassembly materialized instructions at {addr}")
        else:
            self.debug_reporter.debug_print(f"Local target disassembly produced no instructions at {addr}")
        return bool(applied)

    def get_function_manager(self):
        if self.program_value() is None:
            return None
        try:
            return self.program_value().getFunctionManager()
        except Exception:
            return None

    def resolve_function_from_address(self, address):
        if address is None:
            return None
        try:
            function_manager = self.get_function_manager()
            if function_manager is None:
                return None
            get_function_at = getattr(function_manager, "getFunctionAt", None)
            if callable(get_function_at):
                function = get_function_at(address)
                if function is not None:
                    return function
            get_referenced_function = getattr(function_manager, "getReferencedFunction", None)
            if callable(get_referenced_function):
                function = get_referenced_function(address)
                if function is not None:
                    return function
        except Exception:
            return None
        return None



def _impl_get_last_function_lookup_error(self) -> Optional[str]:
    return self._last_function_lookup_error


def _impl_get_last_analysis_failure(self) -> Optional[AnalysisFailure]:
    return self._last_analysis_failure


def _impl_get_last_analysis_failure_status(self) -> Optional[str]:
    failure = self._last_analysis_failure
    return failure.status if failure is not None else None
