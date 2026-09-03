# -*- coding: utf-8 -*-
"""P-codeトレースロジック"""

from __future__ import annotations
from dataclasses import dataclass
import inspect
from typing import Callable, Dict, List, Optional, Sequence, Set, Tuple, Any, TYPE_CHECKING
from ..model import (
    CanonicalLocation,
    Expression,
    ExpressionType,
    Condition,
    StorageInfo,
    CallTargetRef,
    UnknownValueRef,
    AddressValueRef,
    LocationBaseRef,
    ObservedMemoryReadRef,
    PcodeOpRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
)
from ..model.intrinsics import resolve_pcode_intrinsic
from ..model.signature import get_data_type_display_name, is_unsigned_data_type
from ..config.settings import MAX_TRACE_DEPTH
from .debug.unknown_trace import (
    UnknownTracker, UnknownEvent, UnknownReason,
    VarnodeInfo, PcodeOpInfo
)

if TYPE_CHECKING:
    from .phi_resolver import PhiHandler


def _callable_accepts_positional_args(fn: Callable, count: int) -> bool:
    try:
        signature = inspect.signature(fn)
    except (TypeError, ValueError):
        return True
    positional_count = 0
    for param in signature.parameters.values():
        if param.kind == inspect.Parameter.VAR_POSITIONAL:
            return True
        if param.kind in {
            inspect.Parameter.POSITIONAL_ONLY,
            inspect.Parameter.POSITIONAL_OR_KEYWORD,
        }:
            positional_count += 1
    return positional_count >= count


class VarnodeKey:
    """Varnodeを識別するためのキー"""
    
    def __init__(self, space_id: Optional[int], space_name: str, offset: int, size: int):
        self.space_id = space_id
        self.space_name = space_name
        self.offset = offset
        self.size = size
    
    def __hash__(self):
        return hash((self.space_id, self.space_name, self.offset, self.size))
    
    def __eq__(self, other):
        if not isinstance(other, VarnodeKey):
            return False
        return (self.space_id == other.space_id and
                self.space_name == other.space_name and
                self.offset == other.offset and 
                self.size == other.size)
    
    def __repr__(self):
        return f"VarnodeKey({self.space_id},{self.space_name},0x{self.offset:x},{self.size})"
    
    @classmethod
    def from_varnode(cls, varnode) -> 'VarnodeKey':
        """GhidraのVarnodeからキーを作成"""
        addr = varnode.getAddress()
        space = addr.getAddressSpace()
        return cls(
            space_id=int(space.getSpaceID()) if space is not None else None,
            space_name=str(space.getName()) if space is not None else "unknown",
            offset=varnode.getOffset(),
            size=varnode.getSize()
        )


@dataclass(frozen=True)
class ParameterStorageDescriptor:
    """Storage-backed parameter identity collected from Ghidra objects."""

    name: str
    index: int
    size_bytes: int
    is_signed: bool
    data_type: Optional[str]
    data_type_obj: Any
    storage_info: Optional[StorageInfo]


class PcodeTracer:
    """
    P-codeのデータフロー解析とトレースを行うクラス
    """
    
    def __init__(
        self,
        program,
        high_function,
        debug: bool = False,
        *,
        bound_parameter_values: Optional[Dict[int, Expression]] = None,
        bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
        binary_id: Optional[str] = None,
    ):
        self.program = program
        self.high_function = high_function
        self.debug = debug
        self._function_binary_id = binary_id
        self.record_deferred_call: Optional[
            Callable[[Any, List[Expression], Optional[Expression], Optional[PcodeOpRef]], Any]
        ] = None
        self._debug_message_limit = 4000
        self._debug_message_count = 0
        self._debug_suppressed = False
        
        # トレース済みのキャッシュ（一意なキー -> Expression）
        self._trace_cache: Dict[Tuple[Any, ...], Expression] = {}
        
        # トレース中のスタック（循環検出用）
        self._trace_stack: Set[Tuple[Any, ...]] = set()
        
        # Unknown発生追跡
        self.unknown_tracker = UnknownTracker()
        if debug:
            self.unknown_tracker.enable()
        
        # PHI handler（analyzerから設定される）
        self.phi_handler: Optional['PhiHandler'] = None
        self.condition_tracker = None
        self._parameter_descriptors: List[ParameterStorageDescriptor] = []
        self._bound_parameter_values: Dict[int, Expression] = {
            int(index): self._clone_expression(expr)
            for index, expr in (bound_parameter_values or {}).items()
            if expr is not None
        }
        self._bound_parameter_storage_values: Dict[Tuple[Any, ...], Expression] = {
            tuple(key): self._clone_expression(expr)
            for key, expr in (bound_parameter_storage_values or {}).items()
            if key is not None and expr is not None
        }
        (
            self._function_program_id,
            self._function_entry_space,
            self._function_entry_offset,
        ) = self._resolve_current_function_scope()
        self._parameter_descriptors = self._collect_parameter_descriptors()
        
        self._collect_debug_info()

    def _resolve_callother_userop_name(self, pcode_op: Any) -> Optional[str]:
        if pcode_op is None:
            return None
        try:
            if pcode_op.getNumInputs() < 1:
                return None
            userop_id = int(pcode_op.getInput(0).getOffset())
        except Exception:
            return None
        language = getattr(self.program, "getLanguage", lambda: None)()
        get_name = getattr(language, "getUserDefinedOpName", None)
        if callable(get_name):
            try:
                name = get_name(userop_id)
            except Exception:
                name = None
            if name:
                return str(name)
        return None

    def _get_op_order_key(self, pcode_op) -> Optional[int]:
        """Return a comparable intra-address P-code op order, if available.

        This is intentionally narrower than ``PcodeOpRef.stable_key()``. Memory
        read ordering and live-in checks need a monotonic integer order for
        comparisons, not a structural identity tuple.
        """
        if pcode_op is None:
            return None
        seqnum = getattr(pcode_op, "getSeqnum", lambda: None)()
        if seqnum is not None:
            order = getattr(seqnum, "getOrder", lambda: None)()
            coerced = self._coerce_op_order_value(order)
            if coerced is not None:
                return coerced
        order = getattr(pcode_op, "getOrder", lambda: None)()
        return self._coerce_op_order_value(order)

    @staticmethod
    def _coerce_op_order_value(value) -> Optional[int]:
        if value is None:
            return None
        try:
            return int(value)
        except (TypeError, ValueError):
            return None

    def _record_deferred_call(
        self,
        target_ref: CallTargetRef,
        args: List[Expression],
        call_target_expr: Optional[Expression],
        pcode_op_ref: Optional[PcodeOpRef],
    ):
        if self.record_deferred_call is None:
            return None
        if _callable_accepts_positional_args(self.record_deferred_call, 4):
            return self.record_deferred_call(target_ref, args, call_target_expr, pcode_op_ref)
        return self.record_deferred_call(target_ref, args, call_target_expr)

    def _clone_expression(self, expr: Optional[Expression]) -> Optional[Expression]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.PHI and expr.value:
            cloned_branches = []
            for cond, value in expr.value:
                cloned_cond = None
                if cond is not None:
                    cloned_cond = Condition(
                        self._clone_expression(cond.expression),
                        cond.negated,
                    )
                cloned_branches.append((cloned_cond, self._clone_expression(value)))
            cloned = Expression.phi(cloned_branches)
            cloned.size = expr.size
            cloned.data_type = expr.data_type
            cloned.data_type_obj = getattr(expr, "data_type_obj", None)
            cloned.storage_info = getattr(expr, "storage_info", None)
            cloned.read_order_key = getattr(expr, "read_order_key", None)
            cloned.runtime_ref = getattr(expr, "runtime_ref", None)
            cloned.opcode = getattr(expr, "opcode", None)
            return cloned

        cloned = Expression(
            expr.expr_type,
            value=expr.value,
            operator=expr.operator,
            operands=[
                self._clone_expression(operand)
                for operand in (expr.operands or [])
            ],
            size=expr.size,
            name=expr.name,
            data_type=expr.data_type,
            data_type_obj=getattr(expr, "data_type_obj", None),
            storage_info=getattr(expr, "storage_info", None),
            read_order_key=getattr(expr, "read_order_key", None),
            runtime_ref=getattr(expr, "runtime_ref", None),
            opcode=getattr(expr, "opcode", None),
        )
        return cloned

    def _coerce_descriptor_signedness(
        self,
        data_type_obj: Any,
        display_name: Optional[str],
    ) -> bool:
        try:
            return not is_unsigned_data_type(
                data_type_obj,
                display_name,
                program=self.program,
            )
        except Exception:
            return True

    def _resolve_current_function_scope(self) -> Tuple[Optional[int], Optional[str], Optional[int]]:
        program_id = None
        entry_space = None
        entry_offset = None

        try:
            if self.program is not None and hasattr(self.program, "getUniqueProgramID"):
                program_id = int(self.program.getUniqueProgramID())
        except Exception:
            program_id = None

        function = getattr(self.high_function, "getFunction", lambda: None)()
        try:
            if function is not None and hasattr(function, "getEntryPoint"):
                entry_point = function.getEntryPoint()
                if entry_point is not None:
                    try:
                        entry_space = entry_point.getAddressSpace().getName()
                    except Exception:
                        entry_space = None
                    entry_offset = int(entry_point.getOffset())
        except Exception:
            entry_space = None
            entry_offset = None

        return program_id, entry_space, entry_offset

    def get_parameter_owner_scope(self) -> Dict[str, Optional[int]]:
        return {
            "owner_program_id": self._function_program_id,
            "owner_entry_offset": self._function_entry_offset,
        }

    def _make_parameter_location_ref(
        self,
        name: Optional[str],
        *,
        index: Optional[int] = None,
    ) -> LocationBaseRef:
        return LocationBaseRef.parameter(
            name or None,
            index=index,
            owner_program_id=self._function_program_id,
            owner_entry_offset=self._function_entry_offset,
        )

    def _make_storage_location_ref(
        self,
        storage_info: Optional[StorageInfo],
    ) -> Optional[LocationBaseRef]:
        storage_key = self._storage_identity_key(storage_info)
        if storage_info is None or storage_key is None:
            return None
        return LocationBaseRef.storage(
            space_id=storage_info.space_id,
            space_name=storage_info.space_name or ("register" if storage_info.is_register else "mem"),
            offset=int(storage_info.offset or getattr(storage_info, "base_register_offset", 0) or 0),
            size=max(1, int(storage_info.size or storage_info.register_size or 1)),
            storage_identity_key=storage_key,
        )

    def _make_parameter_or_storage_location_ref(
        self,
        name: Optional[str],
        *,
        index: Optional[int] = None,
        storage_info: Optional[StorageInfo] = None,
    ) -> LocationBaseRef:
        try:
            normalized_index = int(index) if index is not None else None
        except Exception:
            normalized_index = None
        if normalized_index is None or normalized_index < 0:
            storage_ref = self._make_storage_location_ref(storage_info)
            if storage_ref is not None:
                return storage_ref
        return self._make_parameter_location_ref(name, index=normalized_index)

    def _get_storage_info_from_variable_storage(self, variable_storage) -> Optional[StorageInfo]:
        if variable_storage is None:
            return None
        get_varnodes = getattr(variable_storage, "getVarnodes", None)
        if callable(get_varnodes):
            try:
                for varnode in get_varnodes():
                    if varnode is None:
                        continue
                    storage = self._get_storage_info_from_varnode(varnode)
                    if storage is not None:
                        return storage
            except Exception:
                pass
        get_registers = getattr(variable_storage, "getRegisters", None)
        if callable(get_registers):
            try:
                registers = list(get_registers() or [])
            except Exception:
                registers = []
            if registers:
                reg = registers[0]
                try:
                    base_reg = reg.getBaseRegister() or reg
                except Exception:
                    base_reg = reg
                try:
                    storage = StorageInfo(
                        is_register=True,
                        space_name="register",
                        offset=int(reg.getOffset()),
                        size=int(reg.getNumBytes()),
                        size_bits=int(reg.getBitLength()),
                        register_offset=int(reg.getOffset()),
                        register_size=int(reg.getNumBytes()),
                        register_size_bits=int(reg.getBitLength()),
                        register_name=reg.getName(),
                        base_register_name=base_reg.getName(),
                        base_register_offset=int(base_reg.getOffset()),
                        base_register_size=max(1, int(base_reg.getBitLength()) // 8),
                        base_register_size_bits=int(base_reg.getBitLength()),
                        bit_offset_in_base=max(
                            0,
                            (int(reg.getOffset()) - int(base_reg.getOffset())) * 8,
                        ),
                    )
                    return storage
                except Exception:
                    return None
        return None

    def _collect_parameter_descriptors(self) -> List[ParameterStorageDescriptor]:
        descriptors: Dict[int, ParameterStorageDescriptor] = {}
        local_map = getattr(self.high_function, "getLocalSymbolMap", lambda: None)()
        if local_map is not None:
            try:
                symbols = list(local_map.getSymbols() or [])
            except Exception:
                symbols = []
            for symbol in symbols:
                try:
                    if not symbol.isParameter():
                        continue
                    index = int(symbol.getCategoryIndex())
                except Exception:
                    continue
                try:
                    data_type_obj = symbol.getDataType() if symbol.getDataType() else None
                except Exception:
                    data_type_obj = None
                display_name = get_data_type_display_name(data_type_obj)
                high_var = getattr(symbol, "getHighVariable", lambda: None)()
                representative = getattr(high_var, "getRepresentative", lambda: None)() if high_var is not None else None
                storage_info = (
                    self._get_storage_info_from_varnode(representative)
                    if representative is not None
                    else None
                )
                if storage_info is None:
                    try:
                        storage_info = self._get_storage_info_from_variable_storage(symbol.getStorage())
                    except Exception:
                        storage_info = None
                size_bytes = 0
                try:
                    size_bytes = int(symbol.getSize())
                except Exception:
                    size_bytes = 0
                if size_bytes <= 0 and data_type_obj is not None:
                    try:
                        size_bytes = int(data_type_obj.getLength())
                    except Exception:
                        size_bytes = 0
                if size_bytes <= 0 and storage_info is not None:
                    size_bytes = max(1, int(storage_info.size or 0))
                descriptors[index] = ParameterStorageDescriptor(
                    name=str(symbol.getName()),
                    index=index,
                    size_bytes=max(1, size_bytes or 1),
                    is_signed=self._coerce_descriptor_signedness(data_type_obj, display_name),
                    data_type=display_name,
                    data_type_obj=data_type_obj,
                    storage_info=storage_info,
                )
        return [descriptors[index] for index in sorted(descriptors)]

    def _storage_contains(self, outer: StorageInfo, inner: StorageInfo) -> bool:
        if not outer.shares_base_register_with(inner):
            return False
        outer_low = int(getattr(outer, "bit_offset_in_base", 0) or 0)
        outer_high = outer_low + int(getattr(outer, "size_bits", 0) or 0)
        inner_low = int(getattr(inner, "bit_offset_in_base", 0) or 0)
        inner_high = inner_low + int(getattr(inner, "size_bits", 0) or 0)
        if outer_high <= outer_low or inner_high <= inner_low:
            return False
        return outer_low <= inner_low and inner_high <= outer_high

    def _coerce_expression_width(
        self,
        expr: Expression,
        source_storage: Optional[StorageInfo],
        target_storage: Optional[StorageInfo],
        *,
        is_signed: bool,
    ) -> Expression:
        if source_storage is None or target_storage is None:
            cloned = self._clone_expression(expr)
            return cloned if cloned is not None else Expression.unknown("coerce_missing_storage")

        source_bits = int(getattr(source_storage, "size_bits", 0) or 0)
        target_bits = int(getattr(target_storage, "size_bits", 0) or 0)
        if source_bits <= 0 or target_bits <= 0:
            cloned = self._clone_expression(expr)
            return cloned if cloned is not None else Expression.unknown("coerce_missing_bits")

        cloned = self._clone_expression(expr)
        if cloned is None:
            return Expression.unknown("coerce_missing_expr")

        source_low = int(getattr(source_storage, "bit_offset_in_base", 0) or 0)
        target_low = int(getattr(target_storage, "bit_offset_in_base", 0) or 0)

        if source_bits == target_bits and source_low == target_low:
            cloned.size = max(1, target_bits // 8)
            cloned.storage_info = target_storage
            return cloned

        if self._storage_contains(source_storage, target_storage):
            byte_offset = max(0, (target_low - source_low) // 8)
            offset_expr = Expression.constant(byte_offset, size=max(1, cloned.size or 1))
            narrowed = Expression.binary_op("SUBPIECE", cloned, offset_expr)
            narrowed.size = max(1, target_bits // 8)
            narrowed.storage_info = target_storage
            return narrowed

        if self._storage_contains(target_storage, source_storage):
            op = "INT_SEXT" if is_signed else "INT_ZEXT"
            widened = Expression.unary_op(op, cloned)
            widened.size = max(1, target_bits // 8)
            widened.storage_info = target_storage
            return widened

        cloned.size = max(1, target_bits // 8)
        cloned.storage_info = target_storage
        return cloned

    def _coerce_bound_argument_to_parameter(
        self,
        expr: Expression,
        descriptor: ParameterStorageDescriptor,
    ) -> Expression:
        cloned = self._clone_expression(expr)
        if cloned is None:
            return Expression.unknown("bound_arg_missing")

        target_bits = max(1, int(descriptor.size_bytes) * 8)
        source_bits = max(1, int(getattr(cloned, "size", 0) or 0) * 8)
        if source_bits == target_bits:
            cloned.size = max(1, target_bits // 8)
            return cloned

        if source_bits > target_bits:
            narrowed = Expression.binary_op(
                "SUBPIECE",
                cloned,
                Expression.constant(0, size=max(1, cloned.size or 1)),
            )
            narrowed.size = max(1, target_bits // 8)
            return narrowed

        op = "INT_SEXT" if descriptor.is_signed else "INT_ZEXT"
        widened = Expression.unary_op(op, cloned)
        widened.size = max(1, target_bits // 8)
        return widened

    def _resolve_storage_backed_parameter_expression(
        self,
        storage_info: Optional[StorageInfo],
    ) -> Optional[Expression]:
        if storage_info is None or not getattr(storage_info, "is_register", False):
            return None

        best_descriptor: Optional[ParameterStorageDescriptor] = None
        best_score: Optional[Tuple[int, int, int]] = None
        for descriptor in self._parameter_descriptors:
            descriptor_storage = descriptor.storage_info
            if descriptor_storage is None or not getattr(descriptor_storage, "is_register", False):
                continue
            if not descriptor_storage.shares_base_register_with(storage_info):
                continue

            exact = int(descriptor_storage.register_identity_key() == storage_info.register_identity_key())
            contains_target = int(self._storage_contains(descriptor_storage, storage_info))
            contains_descriptor = int(self._storage_contains(storage_info, descriptor_storage))
            if exact == 0 and contains_target == 0 and contains_descriptor == 0:
                continue
            score = (
                exact,
                contains_target,
                -abs(
                    int(getattr(descriptor_storage, "size_bits", 0) or 0)
                    - int(getattr(storage_info, "size_bits", 0) or 0)
                ),
            )
            if best_score is not None and score <= best_score:
                continue
            best_descriptor = descriptor
            best_score = score

        if best_descriptor is None:
            return None

        source_expr = (
            self._bound_parameter_values.get(best_descriptor.index)
            if best_descriptor.index >= 0
            else None
        )
        storage_key = self._storage_identity_key(best_descriptor.storage_info)
        if source_expr is None and storage_key is not None:
            source_expr = self._bound_parameter_storage_values.get(storage_key)
        if source_expr is None:
            source_expr = Expression.parameter(
                best_descriptor.name,
                best_descriptor.index,
                best_descriptor.data_type,
                best_descriptor.data_type_obj,
                best_descriptor.size_bytes,
                storage_info=best_descriptor.storage_info,
                runtime_ref=self._make_parameter_or_storage_location_ref(
                    best_descriptor.name,
                    index=best_descriptor.index,
                    storage_info=best_descriptor.storage_info,
                ),
            )
        else:
            source_expr = self._coerce_bound_argument_to_parameter(
                source_expr,
                best_descriptor,
            )

        resolved = self._coerce_expression_width(
            source_expr,
            best_descriptor.storage_info,
            storage_info,
            is_signed=best_descriptor.is_signed,
        )
        resolved.runtime_ref = self._make_parameter_or_storage_location_ref(
            best_descriptor.name,
            index=best_descriptor.index,
            storage_info=best_descriptor.storage_info,
        )
        return resolved

    def _resolve_bound_parameter_expression(
        self,
        *,
        name: str,
        index: int,
        data_type: Optional[str],
        data_type_obj,
        size_bytes: int,
        storage_info: Optional[StorageInfo],
    ) -> Optional[Expression]:
        source_expr = self._bound_parameter_values.get(index) if index >= 0 else None
        storage_key = self._storage_identity_key(storage_info)
        if source_expr is None and storage_key is not None:
            source_expr = self._bound_parameter_storage_values.get(storage_key)
        if source_expr is None:
            return None

        descriptor = None
        if index >= 0:
            descriptor = next(
                (
                    candidate
                    for candidate in self._parameter_descriptors
                    if int(candidate.index) == int(index)
                ),
                None,
            )
        if descriptor is None and storage_key is not None:
            descriptor = next(
                (
                    candidate
                    for candidate in self._parameter_descriptors
                    if self._storage_identity_key(candidate.storage_info) == storage_key
                ),
                None,
            )
        if descriptor is None:
            descriptor = ParameterStorageDescriptor(
                name=name,
                index=index,
                size_bytes=max(1, int(size_bytes or 1)),
                is_signed=self._coerce_descriptor_signedness(data_type_obj, data_type),
                data_type=data_type,
                data_type_obj=data_type_obj,
                storage_info=storage_info,
            )

        resolved = self._coerce_bound_argument_to_parameter(source_expr, descriptor)
        resolved.storage_info = storage_info
        resolved.runtime_ref = self._make_parameter_or_storage_location_ref(
            name,
            index=index,
            storage_info=storage_info,
        )
        return resolved

    def _storage_identity_key(self, storage_info: Optional[StorageInfo]) -> Optional[Tuple[Any, ...]]:
        if storage_info is None:
            return None
        try:
            key = storage_info.storage_identity_key()
        except Exception:
            key = None
        return tuple(key) if key is not None else None

    def _recover_call_argument_expressions(
        self,
        pcode_op,
        depth: int,
        use_cache: bool,
        target_ref: Optional[CallTargetRef] = None,
    ) -> List[Expression]:
        recovered: List[Expression] = []
        if pcode_op is None:
            return recovered
        for index in range(1, pcode_op.getNumInputs()):
            try:
                recovered.append(
                    self.trace_varnode(pcode_op.getInput(index), depth + 1, use_cache)
                )
            except Exception:
                recovered.append(Expression.unknown(f"call_arg_{index}_unknown"))
        if recovered:
            return recovered
        return self._recover_implicit_call_argument_expressions(
            pcode_op,
            target_ref,
        )

    def _recover_implicit_call_argument_expressions(
        self,
        pcode_op,
        target_ref: Optional[CallTargetRef],
    ) -> List[Expression]:
        """Recover omitted ABI-register call arguments through path-covered evidence."""

        target_function = self._resolve_call_target_function(target_ref)
        if target_function is None:
            if self._debug_available():
                self._debug_print("  [CallArgRecovery] no target function for implicit CALL args")
            return []
        parameters = self._call_target_parameters(target_function)
        if not parameters:
            if self._debug_available():
                self._debug_print("  [CallArgRecovery] target function has no parameter objects")
            return []

        shared_recovered = self._recover_implicit_call_arguments_with_effect_model(
            pcode_op,
            parameters,
        )
        if len(shared_recovered) >= len(parameters):
            if self._debug_available():
                self._debug_print(
                    "  [CallArgRecovery] recovered implicit CALL args via shared effect model: "
                    + ", ".join(arg.to_string() for arg in shared_recovered[: len(parameters)])
                )
            return shared_recovered[: len(parameters)]
        if self._debug_available():
            self._debug_print(
                "  [CallArgRecovery] shared effect-model recovery did not cover all params "
                f"(got={len(shared_recovered)}, expected={len(parameters)})"
            )
        return []

    def _recover_implicit_call_arguments_with_effect_model(
        self,
        pcode_op,
        parameters: Sequence[Any],
    ) -> List[Expression]:
        caller_parameters = self._caller_parameter_dicts_for_call_recovery()
        callee_parameters = [
            descriptor
            for parameter in parameters
            for descriptor in [self._call_parameter_descriptor(parameter)]
            if descriptor is not None
        ]
        if not caller_parameters or len(callee_parameters) != len(parameters):
            return []
        try:
            from .effect_summary import _recover_call_argument_expressions as recover_call_args

            recovered = recover_call_args(
                pcode_op,
                self,
                caller_parameters,
                callee_parameters,
                [],
                condition_tracker=getattr(self, "condition_tracker", None),
            )
        except Exception:
            return []
        return list(recovered or [])

    def _caller_parameter_dicts_for_call_recovery(self) -> List[Dict[str, Any]]:
        result: List[Dict[str, Any]] = []
        for descriptor in self._parameter_descriptors:
            result.append(
                {
                    "name": descriptor.name,
                    "index": descriptor.index,
                    "size": descriptor.size_bytes,
                    "data_type": descriptor.data_type,
                    "data_type_obj": descriptor.data_type_obj,
                    "is_signed": descriptor.is_signed,
                    "storage": descriptor.storage_info,
                    "storage_info": descriptor.storage_info,
                }
            )
        return result

    def _call_parameter_descriptor(self, parameter) -> Optional[Dict[str, Any]]:
        storage_info = self._call_parameter_storage_info(parameter)
        if storage_info is None:
            return None
        name = ""
        for accessor in ("getName", "getNameString"):
            getter = getattr(parameter, accessor, None)
            if not callable(getter):
                continue
            try:
                name = str(getter() or "")
            except Exception:
                name = ""
            if name:
                break
        index = -1
        for accessor in ("getOrdinal", "getIndex"):
            getter = getattr(parameter, accessor, None)
            if not callable(getter):
                continue
            try:
                index = int(getter())
            except Exception:
                index = -1
            if index >= 0:
                break
        size_bytes = 0
        for accessor in ("getLength", "getSize"):
            getter = getattr(parameter, accessor, None)
            if not callable(getter):
                continue
            try:
                size_bytes = int(getter())
            except Exception:
                size_bytes = 0
            if size_bytes > 0:
                break
        if size_bytes <= 0:
            size_bytes = max(1, int(getattr(storage_info, "size", 0) or 0))
        data_type_obj = None
        try:
            data_type_obj = parameter.getDataType()
        except Exception:
            data_type_obj = None
        data_type = get_data_type_display_name(data_type_obj)
        return {
            "name": name or f"param_{index + 1 if index >= 0 else len(name)}",
            "index": index,
            "size": max(1, int(size_bytes)),
            "data_type": data_type,
            "data_type_obj": data_type_obj,
            "is_signed": self._coerce_descriptor_signedness(data_type_obj, data_type),
            "storage": storage_info,
            "storage_info": storage_info,
        }

    def _resolve_call_target_function(
        self,
        target_ref: Optional[CallTargetRef],
    ):
        function_obj = getattr(target_ref, "function_obj", None)
        if function_obj is not None:
            return function_obj
        address_offset = getattr(target_ref, "entry_offset", None)
        if address_offset is None:
            address_offset = getattr(target_ref, "address_offset", None)
        if address_offset is None or self.program is None:
            return None
        try:
            address_factory = self.program.getAddressFactory()
            default_space = address_factory.getDefaultAddressSpace()
            address = default_space.getAddress(int(address_offset))
            function_manager = self.program.getFunctionManager()
            return function_manager.getFunctionAt(address)
        except Exception:
            return None

    def _call_target_parameters(self, target_function) -> List[Any]:
        get_parameters = getattr(target_function, "getParameters", None)
        if callable(get_parameters):
            try:
                return list(get_parameters() or [])
            except Exception:
                return []
        return []

    def _call_parameter_storage_info(self, parameter) -> Optional[StorageInfo]:
        storage = None
        for accessor in ("getVariableStorage", "getStorage"):
            getter = getattr(parameter, accessor, None)
            if not callable(getter):
                continue
            try:
                storage = getter()
            except Exception:
                storage = None
            if storage is not None:
                break
        return self._get_storage_info_from_variable_storage(storage)

    def _call_storage_is_unmodified_before_call(
        self,
        storage_info: StorageInfo,
        call_op,
    ) -> bool:
        call_key = self._pcode_sequence_sort_key(call_op)
        if call_key is None:
            return False
        for op in self._iter_high_pcode_ops():
            if self._same_pcode_op(op, call_op):
                return True
            op_key = self._pcode_sequence_sort_key(op)
            if op_key is None or op_key >= call_key:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is None:
                continue
            output_storage = self._get_storage_info_from_varnode(output)
            if output_storage is None:
                continue
            if self._storage_ranges_overlap(storage_info, output_storage):
                return False
        return True

    def _iter_high_pcode_ops(self):
        blocks = getattr(self.high_function, "getBasicBlocks", lambda: [])()
        for block in blocks or []:
            iterator = getattr(block, "getIterator", lambda: None)()
            if iterator is None:
                continue
            while iterator.hasNext():
                yield iterator.next()

    def _pcode_sequence_sort_key(self, pcode_op) -> Optional[Tuple[int, int, int]]:
        try:
            seq = pcode_op.getSeqnum()
        except Exception:
            seq = None
        if seq is None:
            return None
        try:
            target = seq.getTarget()
            address_offset = int(target.getOffset())
        except Exception:
            return None
        try:
            seq_time = int(seq.getTime())
        except Exception:
            seq_time = 0
        try:
            seq_order = int(seq.getOrder())
        except Exception:
            seq_order = 0
        return (address_offset, seq_time, seq_order)

    def _same_pcode_op(self, left, right) -> bool:
        if left is right:
            return True
        left_ref = self._make_pcode_op_ref(left)
        right_ref = self._make_pcode_op_ref(right)
        return (
            left_ref is not None
            and right_ref is not None
            and left_ref.stable_key() == right_ref.stable_key()
        )

    def _storage_ranges_overlap(
        self,
        left: StorageInfo,
        right: StorageInfo,
    ) -> bool:
        if not left.is_register or not right.is_register:
            return False
        if not left.shares_base_register_with(right):
            return False
        left_low = int(getattr(left, "bit_offset_in_base", 0) or 0)
        left_high = left_low + int(getattr(left, "size_bits", 0) or 0)
        right_low = int(getattr(right, "bit_offset_in_base", 0) or 0)
        right_high = right_low + int(getattr(right, "size_bits", 0) or 0)
        return left_high > right_low and right_high > left_low

    def _recover_call_target_expression(
        self,
        pcode_op,
        depth: int,
        use_cache: bool,
    ) -> Optional[Expression]:
        if pcode_op is None or pcode_op.getNumInputs() < 1:
            return None
        try:
            return self.trace_varnode(pcode_op.getInput(0), depth + 1, use_cache)
        except Exception:
            return None

    def _resolve_call_target_ref_from_expression(
        self,
        expr: Optional[Expression],
        *,
        allow_containing: bool = True,
        allow_code_address: bool = True,
    ) -> Optional[CallTargetRef]:
        if expr is None or expr.expr_type != ExpressionType.CONSTANT:
            return None
        try:
            address_value = int(expr.value)
        except (TypeError, ValueError):
            return None
        if address_value < 0 or self.program is None:
            return None

        try:
            address_factory = self.program.getAddressFactory()
            default_space = address_factory.getDefaultAddressSpace()
            address = default_space.getAddress(address_value)
        except Exception:
            address = None
        if address is None:
            return None

        try:
            function_manager = self.program.getFunctionManager()
        except Exception:
            function_manager = None
        if function_manager is not None:
            for accessor in ("getFunctionAt", "getReferencedFunction"):
                getter = getattr(function_manager, accessor, None)
                if callable(getter):
                    try:
                        function = getter(address)
                    except Exception:
                        function = None
                    if function is not None:
                        return CallTargetRef.from_function(function)
            if allow_containing:
                getter = getattr(function_manager, "getFunctionContaining", None)
                if callable(getter):
                    try:
                        function = getter(address)
                    except Exception:
                        function = None
                    if function is not None:
                        return CallTargetRef.from_function(function)

        if not allow_code_address:
            return None
        return CallTargetRef.from_code_address(address_value)

    def _resolve_call_target_ref_from_op(
        self,
        pcode_op,
        depth: int,
        use_cache: bool,
        *,
        allow_containing: bool = True,
        allow_code_address: bool = True,
    ) -> CallTargetRef:
        try:
            target_varnode = pcode_op.getInput(0)
        except Exception:
            target_varnode = None
        direct_ref = self.resolve_call_target_ref(
            target_varnode,
            allow_containing=allow_containing,
            allow_code_address=allow_code_address,
        ) if target_varnode is not None else None
        if direct_ref is not None and not direct_ref.is_unknown():
            return direct_ref

        target_expr = self._recover_call_target_expression(
            pcode_op,
            depth,
            use_cache,
        )
        expr_ref = self._resolve_call_target_ref_from_expression(
            target_expr,
            allow_containing=allow_containing,
            allow_code_address=allow_code_address,
        )
        if expr_ref is not None:
            return expr_ref
        return direct_ref or CallTargetRef.unknown()

    def _build_unresolved_call_unknown(
        self,
        pcode_op,
        depth: int,
        use_cache: bool,
        *,
        reason: str,
        target_ref: CallTargetRef,
    ) -> Expression:
        target_label = target_ref.display_name()
        runtime_ref = None
        display_name = None

        if self.record_deferred_call is not None:
            deferred_args = self._recover_call_argument_expressions(
                pcode_op,
                depth,
                use_cache,
                target_ref,
            )
            deferred_target_expr = self._recover_call_target_expression(
                pcode_op,
                depth,
                use_cache,
            )
            recorded = self._record_deferred_call(
                target_ref,
                deferred_args,
                deferred_target_expr,
                self._make_pcode_op_ref(pcode_op),
            )
            if isinstance(recorded, str):
                display_name = recorded
            else:
                runtime_ref = recorded
                if hasattr(recorded, "display_name"):
                    display_name = recorded.display_name()

        if runtime_ref is None:
            runtime_ref = UnknownValueRef.out_of_scope_call(
                reason=reason,
                target_ref=target_ref,
                display_hint=target_label,
            )
        if display_name is None:
            display_name = runtime_ref.display_name() if hasattr(runtime_ref, "display_name") else f"{reason}:{target_label}"

        return Expression.unknown(display_name, runtime_ref=runtime_ref)

    def _debug_print(self, msg: str) -> None:
        if not self.debug:
            return
        if self._debug_message_count >= self._debug_message_limit:
            if not self._debug_suppressed:
                print(
                    f"[PcodeTracer] debug output suppressed after "
                    f"{self._debug_message_limit} messages"
                )
                self._debug_suppressed = True
            return
        self._debug_message_count += 1
        print(msg)

    def _debug_available(self) -> bool:
        return self.debug and self._debug_message_count < self._debug_message_limit

    def _make_address_runtime_ref(
        self,
        *,
        display_name: Optional[str] = None,
        symbol: Any = None,
        high_var: Any = None,
    ) -> Optional[AddressValueRef]:
        def _build_runtime_ref(address, source: str) -> Optional[AddressValueRef]:
            try:
                offset = int(address.getOffset())
            except Exception:
                return None
            if offset < 0:
                return None

            space_name = None
            space_id = None
            try:
                space = address.getAddressSpace()
                if space is not None:
                    space_name = space.getName()
                    space_id = int(space.getSpaceID())
            except Exception:
                space_name = None
                space_id = None

            symbol_name = None
            if symbol is not None:
                try:
                    symbol_name = symbol.getName()
                except Exception:
                    symbol_name = None
            if not symbol_name:
                symbol_name = self._lookup_symbol_name_for_address(address)

            block_name = None
            is_initialized = None
            can_read = None
            can_write = None
            can_execute = None
            is_volatile = None
            try:
                memory = self.program.getMemory()
                block = memory.getBlock(address) if memory is not None else None
                if block is not None:
                    block_name = block.getName()
                    is_initialized = bool(block.isInitialized())
                    can_read = bool(block.isRead())
                    can_write = bool(block.isWrite())
                    can_execute = bool(block.isExecute())
                    is_volatile = bool(block.isVolatile())
            except Exception:
                pass

            return AddressValueRef(
                address_offset=offset,
                source=source,
                display_hint=display_name,
                program_id=(
                    int(self.program.getUniqueProgramID())
                    if self.program is not None and hasattr(self.program, "getUniqueProgramID")
                    else None
                ),
                space_id=space_id,
                space_name=space_name,
                symbol_name=symbol_name,
                block_name=block_name,
                is_initialized=is_initialized,
                can_read=can_read,
                can_write=can_write,
                can_execute=can_execute,
                is_volatile=is_volatile,
            )

        representative = None
        if high_var is not None:
            try:
                representative = high_var.getRepresentative()
            except Exception:
                representative = None

        probes = (
            (symbol, "getAddress", "symbol_address"),
            (high_var, "getAddress", "high_var_address"),
            (high_var, "getPCAddress", "high_var_pc_address"),
            (representative, "getAddress", "high_var_representative_address"),
            (representative, "getPCAddress", "high_var_representative_pc_address"),
        )
        probe_failures = []
        for owner, method_name, source in probes:
            if owner is None:
                continue
            getter = getattr(owner, method_name, None)
            if not callable(getter):
                probe_failures.append(f"{source}=missing_method")
                continue
            try:
                address = getter()
            except Exception as exc:
                probe_failures.append(f"{source}=error:{type(exc).__name__}")
                continue
            if address is None:
                probe_failures.append(f"{source}=none")
                continue
            runtime_ref = _build_runtime_ref(address, source)
            if runtime_ref is not None:
                return runtime_ref
            probe_failures.append(f"{source}=bad_offset")
        if self.debug and display_name:
            self._debug_print(
                "[PcodeTracer] failed to build AddressValueRef "
                f"name={display_name} probes={probe_failures}"
            )
        return None

    def _make_address_runtime_ref_for_offset(
        self,
        offset: int,
        *,
        display_name: Optional[str] = None,
        require_ghidra_evidence: bool = True,
    ) -> Optional[AddressValueRef]:
        if self.program is None:
            return None
        try:
            offset = int(offset)
        except Exception:
            return None
        if offset < 0:
            return None

        try:
            address_factory = self.program.getAddressFactory()
            default_space = (
                address_factory.getDefaultAddressSpace()
                if address_factory is not None and hasattr(address_factory, "getDefaultAddressSpace")
                else None
            )
            address = default_space.getAddress(offset) if default_space is not None else None
        except Exception:
            address = None
        if address is None:
            return None

        try:
            memory = self.program.getMemory()
            block = memory.getBlock(address) if memory is not None else None
        except Exception:
            block = None

        has_symbol = bool(self._lookup_symbol_name_for_address(address))
        has_data = False
        try:
            listing = self.program.getListing()
        except Exception:
            listing = None
        if listing is not None:
            for getter_name in ("getDataAt", "getDataContaining"):
                getter = getattr(listing, getter_name, None)
                if not callable(getter):
                    continue
                try:
                    if getter(address) is not None:
                        has_data = True
                        break
                except Exception:
                    continue

        has_reference = False
        try:
            reference_manager = self.program.getReferenceManager()
        except Exception:
            reference_manager = None
        if reference_manager is not None:
            for getter_name in ("getReferencesFrom", "getReferencesTo"):
                getter = getattr(reference_manager, getter_name, None)
                if not callable(getter):
                    continue
                try:
                    refs = getter(address)
                except Exception:
                    refs = None
                if refs is None:
                    continue
                if hasattr(refs, "hasNext"):
                    try:
                        has_reference = bool(refs.hasNext())
                    except Exception:
                        has_reference = False
                else:
                    try:
                        has_reference = bool(list(refs))
                    except Exception:
                        has_reference = False
                if has_reference:
                    break

        is_readonly_block = False
        if block is not None:
            try:
                is_readonly_block = bool(
                    block.isInitialized()
                    and block.isRead()
                    and not block.isWrite()
                    and not block.isVolatile()
                )
            except Exception:
                is_readonly_block = False

        if require_ghidra_evidence and not (has_symbol or has_data or has_reference or is_readonly_block):
            return None

        return AddressValueRef(
            address_offset=offset,
            source="constant_offset",
            display_hint=display_name,
            program_id=(
                int(self.program.getUniqueProgramID())
                if self.program is not None and hasattr(self.program, "getUniqueProgramID")
                else None
            ),
            space_id=(
                int(address.getAddressSpace().getSpaceID())
                if address is not None and address.getAddressSpace() is not None
                else None
            ),
            space_name=(
                address.getAddressSpace().getName()
                if address is not None and address.getAddressSpace() is not None
                else None
            ),
            symbol_name=self._lookup_symbol_name_for_address(address),
            block_name=block.getName() if block is not None else None,
            is_initialized=bool(block.isInitialized()) if block is not None else None,
            can_read=bool(block.isRead()) if block is not None else None,
            can_write=bool(block.isWrite()) if block is not None else None,
            can_execute=bool(block.isExecute()) if block is not None else None,
            is_volatile=bool(block.isVolatile()) if block is not None else None,
        )

    def _resolve_concrete_address_offset(self, expr: Optional[Expression]) -> Optional[int]:
        runtime_ref = getattr(expr, "runtime_ref", None)
        if isinstance(runtime_ref, AddressValueRef) and runtime_ref.has_concrete_address():
            return int(runtime_ref.address_offset)

        if expr is None or getattr(expr, "expr_type", None) is None:
            return None

        expr_kind = expr.expr_type.__class__
        if expr.expr_type == expr_kind.CONSTANT and isinstance(expr.value, int):
            return int(expr.value)

        if expr.expr_type == expr_kind.BINARY_OP and expr.operator == "INT_ADD" and len(expr.operands) == 2:
            left_value = self._resolve_concrete_address_offset(expr.operands[0])
            right_value = self._resolve_concrete_address_offset(expr.operands[1])
            if left_value is None or right_value is None:
                return None
            return left_value + right_value

        if expr.expr_type == expr_kind.BINARY_OP and expr.operator == "INT_MULT" and len(expr.operands) == 2:
            left_value = self._resolve_concrete_address_offset(expr.operands[0])
            right_value = self._resolve_concrete_address_offset(expr.operands[1])
            if left_value is None or right_value is None:
                return None
            return left_value * right_value

        if expr.expr_type != expr_kind.INTRINSIC:
            return None

        mnemonic = getattr(expr, "name", None) or ""
        opcode = getattr(expr, "opcode", None)
        operands = getattr(expr, "operands", None) or []

        if (opcode == PTRSUB_OPCODE or mnemonic == "PTRSUB") and len(operands) == 2:
            base_value = self._resolve_concrete_address_offset(operands[0])
            offset_value = self._resolve_concrete_address_offset(operands[1])
            if base_value is None or offset_value is None:
                return None
            return base_value + offset_value

        if (opcode == PTRADD_OPCODE or mnemonic == "PTRADD") and len(operands) == 3:
            base_value = self._resolve_concrete_address_offset(operands[0])
            index_value = self._resolve_concrete_address_offset(operands[1])
            elem_value = self._resolve_concrete_address_offset(operands[2])
            if base_value is None or index_value is None or elem_value is None:
                return None
            return base_value + index_value * elem_value

        return None

    def _derive_pointer_runtime_ref(
        self,
        expr: Expression,
        *,
        display_name: Optional[str] = None,
    ) -> Optional[AddressValueRef]:
        concrete_offset = self._resolve_concrete_address_offset(expr)
        if concrete_offset is None:
            return None
        return self._make_address_runtime_ref_for_offset(
            concrete_offset,
            display_name=display_name,
        )

    def _canonical_location_for_varnode(
        self,
        varnode,
        value_size: int,
    ) -> Optional[CanonicalLocation]:
        if varnode is None or value_size <= 0:
            return None

        storage_info = None
        try:
            storage_info = self._get_storage_info_from_varnode(varnode)
        except Exception:
            storage_info = None

        if storage_info is None:
            try:
                addr = varnode.getAddress()
                if addr is not None:
                    space = addr.getAddressSpace()
                    if space is not None:
                        space_name = space.getName()
                        size = max(1, int(value_size or varnode.getSize() or 0))
                        if space_name == "stack":
                            storage_info = StorageInfo(
                                is_register=False,
                                space_name="stack",
                                offset=int(varnode.getOffset()),
                                size=size,
                                size_bits=size * 8,
                            )
                        elif space_name == "register":
                            storage_info = StorageInfo(
                                is_register=True,
                                space_name="register",
                                offset=int(varnode.getOffset()),
                                size=size,
                                size_bits=size * 8,
                            )
            except Exception:
                storage_info = None

        if storage_info is None:
            return None

        size = max(1, int(value_size or getattr(storage_info, "size", 0) or 0))
        if not storage_info.is_register and (
            storage_info.space_name == "stack"
            or bool(getattr(storage_info, "is_stack_pointer", False))
        ):
            return CanonicalLocation(
                base_ref=LocationBaseRef.stack_frame(),
                offset=int(storage_info.offset),
                size=size,
            )

        return CanonicalLocation(
            base_ref=LocationBaseRef.storage(
                space_id=storage_info.space_id,
                space_name=storage_info.space_name or ("register" if storage_info.is_register else "mem"),
                offset=int(
                    storage_info.base_register_offset
                    if storage_info.is_register
                    else storage_info.offset
                ),
                size=max(
                    1,
                    int(
                        storage_info.base_register_size
                        if storage_info.is_register
                        else storage_info.size
                    ) or size,
                ),
                storage_identity_key=storage_info.storage_identity_key(),
                display_hint=storage_info.register_name if storage_info.is_register else None,
            ),
            offset=0,
            size=size,
        )

    def _symbolic_post_state_read_for_output_varnode(
        self,
        varnode,
        output_size: int,
    ) -> Optional[Expression]:
        location = self._canonical_location_for_varnode(varnode, output_size)
        if location is None:
            return None
        if not self._varnode_supports_symbolic_post_state_promotion(varnode, location):
            return None
        snapshot_ref = PostStateSnapshotRef.function_return()
        runtime_ref = PostStateReadRef(
            location=location,
            snapshot_ref=snapshot_ref,
        )
        return Expression.variable(
            f"poststate_{abs(int(location.offset))}_{int(location.size)}",
            size=max(1, int(output_size or location.size)),
            runtime_ref=runtime_ref,
        )

    def _varnode_supports_symbolic_post_state_promotion(
        self,
        varnode,
        location: Optional[CanonicalLocation],
    ) -> bool:
        if varnode is None or location is None:
            return False

        base_ref = getattr(location, "base_ref", None)
        if base_ref is None:
            return False
        if base_ref.is_stack_frame():
            return True
        if base_ref.is_storage() and str(getattr(base_ref, "storage_space", "") or "").lower() == "register":
            return True

        try:
            addr = varnode.getAddress()
        except Exception:
            addr = None
        if addr is None or self.program is None:
            return False

        try:
            memory = self.program.getMemory()
        except Exception:
            memory = None
        if memory is None:
            return False

        try:
            block = memory.getBlock(addr)
        except Exception:
            block = None
        if block is None:
            return False

        try:
            return bool(block.isWrite()) and not bool(block.isVolatile())
        except Exception:
            return False

    def _lookup_symbol_name_for_address(self, address) -> Optional[str]:
        if address is None:
            return None

        try:
            symbol_table = self.program.getSymbolTable()
        except Exception:
            symbol_table = None
        if symbol_table is not None:
            try:
                primary_symbol = symbol_table.getPrimarySymbol(address)
            except Exception:
                primary_symbol = None
            if primary_symbol is not None:
                try:
                    name = primary_symbol.getName()
                except Exception:
                    name = None
                if name:
                    return name

        try:
            listing = self.program.getListing()
        except Exception:
            listing = None
        if listing is None:
            return None

        for getter_name in ("getDataAt", "getDataContaining"):
            getter = getattr(listing, getter_name, None)
            if not callable(getter):
                continue
            try:
                data = getter(address)
            except Exception:
                data = None
            if data is None:
                continue
            primary_symbol_getter = getattr(data, "getPrimarySymbol", None)
            if callable(primary_symbol_getter):
                try:
                    data_symbol = primary_symbol_getter()
                except Exception:
                    data_symbol = None
                if data_symbol is not None:
                    try:
                        name = data_symbol.getName()
                    except Exception:
                        name = None
                    if name:
                        return name
        return None
    
    def _get_op_key(self, pcode_op) -> Tuple[Any, ...]:
        """PcodeOpの一意なキーを生成（同一seqnumの異なるopを区別）"""
        seq = pcode_op.getSeqnum()
        if seq:
            target = seq.getTarget()
            time = getattr(seq, "getTime", lambda: None)()
            order = seq.getOrder()
            obj_id = id(pcode_op)
            target_offset = None
            if target is not None:
                get_offset = getattr(target, "getOffset", None)
                if callable(get_offset):
                    try:
                        target_offset = int(get_offset())
                    except Exception:
                        target_offset = None
            return (
                "pcode_op_instance",
                target_offset,
                None if time is None else int(time),
                None if order is None else int(order),
                obj_id,
            )
        obj_id = id(pcode_op)
        return (
            "pcode_op_instance",
            None,
            None,
            None,
            pcode_op.hashCode(),
            pcode_op.getMnemonic(),
            obj_id,
        )

    def _make_pcode_op_ref(self, pcode_op) -> Optional[PcodeOpRef]:
        return PcodeOpRef.from_pcode_op(
            pcode_op,
            binary_id=self._function_binary_id,
            program_uid=self._function_program_id,
            function_entry_space=self._function_entry_space,
            function_entry_offset=self._function_entry_offset,
        )
    
    def _collect_debug_info(self):
        """デバッグ用の情報を収集"""
        if self.debug:
            self._debug_print("\n" + "=" * 60)
            self._debug_print("DEBUG: PcodeTracer Initialization")
            self._debug_print("=" * 60)
            
            local_map = self.high_function.getLocalSymbolMap()
            if local_map:
                self._debug_print("\nLocal Symbols:")
                for sym in local_map.getSymbols():
                    if not self._debug_available():
                        break
                    self._debug_print(
                        f"  - {sym.getName()}: type={sym.getDataType()}, "
                        f"isParam={sym.isParameter()}, storage={sym.getStorage()}"
                    )
                    
                    high_var = sym.getHighVariable()
                    if high_var:
                        rep = high_var.getRepresentative()
                        if rep:
                            self._debug_print(
                                f"    Representative Varnode: {rep}, "
                                f"addr={rep.getAddress()}, size={rep.getSize()}"
                            )
            self._debug_print("=" * 60 + "\n")
    
    def clear_cache(self):
        """キャッシュをクリア"""
        self._trace_cache.clear()
        self._trace_stack.clear()

    def emit_unknown_event(self, reason, varnode=None, def_op=None,
                           depth=0, note=None, context="tracer"):
        """Unknown発生イベントを記録"""
        event = UnknownEvent(
            reason=UnknownReason.from_string(reason),
            reason_str=reason, depth=depth,
            varnode=VarnodeInfo.from_varnode(varnode),
            def_op=PcodeOpInfo.from_pcodeop(def_op),
            note=note, context=context
        )
        self.unknown_tracker.record(event)
        if self.debug:
            self._debug_print(event.format_detail(indent=depth))
    
    def _get_storage_info_from_varnode(self, varnode) -> Optional[StorageInfo]:
        """VarnodeからStorageInfoを作成"""
        if varnode is None:
            return None
        
        try:
            addr = varnode.getAddress()
            space = addr.getAddressSpace()
            
            storage_info = StorageInfo(
                is_register=space.isRegisterSpace(),
                space_name=space.getName(),
                space_id=int(space.getSpaceID()),
                offset=varnode.getOffset(),
                size=varnode.getSize(),
                size_bits=varnode.getSize() * 8
            )
            
            if space.isRegisterSpace():
                # レジスタ情報を取得
                reg = self.program.getRegister(addr, varnode.getSize())
                if reg:
                    storage_info.register_name = reg.getName()
                    storage_info.register_offset = reg.getOffset()
                    storage_info.register_size = reg.getNumBytes()
                    storage_info.register_size_bits = reg.getBitLength()
                    
                    # 親レジスタ情報
                    base_reg = reg.getBaseRegister()
                    if base_reg:
                        storage_info.base_register_name = base_reg.getName()
                        storage_info.base_register_offset = base_reg.getOffset()
                        storage_info.base_register_size = base_reg.getBitLength() // 8
                        storage_info.base_register_size_bits = base_reg.getBitLength()
                        
                        # 親レジスタ内でのビットオフセットを計算
                        # reg.getOffset()はレジスタのバイトオフセット
                        # base_reg.getOffset()は親レジスタのバイトオフセット
                        byte_offset_in_base = reg.getOffset() - base_reg.getOffset()
                        storage_info.bit_offset_in_base = byte_offset_in_base * 8
                    else:
                        # 親レジスタがない場合は自身が親
                        storage_info.base_register_name = reg.getName()
                        storage_info.base_register_offset = reg.getOffset()
                        storage_info.base_register_size = reg.getBitLength() // 8
                        storage_info.base_register_size_bits = reg.getBitLength()
                        storage_info.bit_offset_in_base = 0
                    try:
                        storage_info.is_frame_pointer = bool(reg.isDefaultFramePointer())
                    except Exception:
                        storage_info.is_frame_pointer = False
                    try:
                        compiler_spec = self.program.getCompilerSpec()
                        stack_pointer = compiler_spec.getStackPointer() if compiler_spec is not None else None
                    except Exception:
                        stack_pointer = None
                    try:
                        reg_base = reg.getBaseRegister() if reg is not None else None
                        stack_base = stack_pointer.getBaseRegister() if stack_pointer is not None else None
                        storage_info.is_stack_pointer = (
                            reg_base is not None
                            and stack_base is not None
                            and reg_base.getOffset() == stack_base.getOffset()
                        )
                    except Exception:
                        storage_info.is_stack_pointer = False
            
            return storage_info
        except Exception as e:
            if self.debug:
                self._debug_print(f"  [Warning] Failed to get storage info: {e}")
            return None
    
    def trace_varnode(self, varnode, depth: int = 0, use_cache: bool = True) -> Expression:
        """
        Varnodeを逆順にトレースして式を構築
        
        Args:
            varnode: トレース対象のVarnode
            depth: 現在のトレース深度
            use_cache: キャッシュを使用するか
        
        Returns:
            Expression: 展開された式
        """
        if varnode is None:
            self.emit_unknown_event(reason="null", depth=depth,
                                    note="Null varnode passed to trace_varnode")
            return Expression.unknown("null")
        
        if depth > MAX_TRACE_DEPTH:
            self.emit_unknown_event(reason="max_depth_exceeded", varnode=varnode,
                                    depth=depth, note=f"Exceeded {MAX_TRACE_DEPTH}")
            return Expression.unknown("max_depth_exceeded")
        
        if self._debug_available():
            self._debug_print_varnode(varnode, depth)
        
        return self._trace_varnode_internal(varnode, depth, use_cache)
    
    def _debug_print_varnode(self, varnode, depth: int):
        """Varnodeのデバッグ情報を出力"""
        if not self._debug_available():
            return
        indent = "  " * depth
        self._debug_print(f"\n{indent}DEBUG trace_varnode (depth={depth}):")
        self._debug_print(f"{indent}  varnode: {varnode}")
        self._debug_print(f"{indent}  address: {varnode.getAddress()}")
        self._debug_print(f"{indent}  size: {varnode.getSize()}")
        self._debug_print(f"{indent}  isConstant: {varnode.isConstant()}")
        self._debug_print(f"{indent}  isRegister: {varnode.isRegister()}")
        self._debug_print(f"{indent}  isUnique: {varnode.isUnique()}")
        self._debug_print(f"{indent}  isAddress: {varnode.isAddress()}")
        self._debug_print(f"{indent}  isInput: {varnode.isInput()}")
        
        def_op = varnode.getDef()
        self._debug_print(f"{indent}  getDef(): {def_op}")
        if def_op:
            self._debug_print(f"{indent}    def mnemonic: {def_op.getMnemonic()}")
            self._debug_print(f"{indent}    def seqnum: {def_op.getSeqnum()}")
        
        high_var = varnode.getHigh()
        self._debug_print(f"{indent}  getHigh(): {high_var}")
        if high_var:
            self._debug_print(f"{indent}    high name: {high_var.getName()}")
            self._debug_print(f"{indent}    high type: {type(high_var).__name__}")
            symbol = high_var.getSymbol()
            self._debug_print(f"{indent}    symbol: {symbol}")
            if symbol:
                self._debug_print(f"{indent}      symbol name: {symbol.getName()}")
                self._debug_print(f"{indent}      isParameter: {symbol.isParameter()}")
        
        # ストレージ情報を出力
        storage_info = self._get_storage_info_from_varnode(varnode)
        if storage_info:
            self._debug_print(f"{indent}  storage_info:")
            self._debug_print(f"{indent}    is_register: {storage_info.is_register}")
            self._debug_print(f"{indent}    register_name: {storage_info.register_name}")
            self._debug_print(f"{indent}    base_register_name: {storage_info.base_register_name}")
            self._debug_print(f"{indent}    bit_offset_in_base: {storage_info.bit_offset_in_base}")
            self._debug_print(f"{indent}    size_bits: {storage_info.size_bits}")
    
    def _trace_varnode_internal(self, varnode, depth: int, use_cache: bool = True) -> Expression:
        """Varnodeトレースの内部処理"""
        
        # 1. 定数かどうかチェック（最優先）
        if varnode.isConstant():
            value = varnode.getOffset()
            if self._debug_available():
                self._debug_print(f"  -> Constant: 0x{value:x}")
            return Expression.constant(
                value,
                varnode.getSize(),
                runtime_ref=self._make_address_runtime_ref_for_offset(value),
            )
        
        # ストレージ情報を取得
        storage_info = self._get_storage_info_from_varnode(varnode)
        
        # 2. 定義元のPcodeOpを取得
        def_op = varnode.getDef()
        
        if def_op is not None:
            if self._debug_available():
                self._debug_print(f"  -> Has def: {def_op.getMnemonic()}")
            return self._trace_pcode_op(def_op, depth + 1, use_cache)
        
        # 3. 定義がない場合は、入力変数
        if self._debug_available():
            self._debug_print("  -> No def, checking high variable")
        
        high_var = varnode.getHigh()
        if high_var:
            symbol = high_var.getSymbol()
            if symbol:
                sym_name = symbol.getName()
                
                if symbol.isParameter():
                    param_idx = -1
                    try:
                        param_idx = symbol.getCategoryIndex()
                    except:
                        pass
                    dtype_obj = symbol.getDataType() if symbol.getDataType() else None
                    dtype = str(dtype_obj) if dtype_obj else None
                    
                    if self._debug_available():
                        self._debug_print(f"  -> Parameter: {sym_name} (index={param_idx})")

                    bound_expr = self._resolve_bound_parameter_expression(
                        name=sym_name,
                        index=param_idx,
                        data_type=dtype,
                        data_type_obj=dtype_obj,
                        size_bytes=varnode.getSize(),
                        storage_info=storage_info,
                    )
                    if bound_expr is not None:
                        if self._debug_available():
                            self._debug_print(
                                "  -> Bound parameter argument: "
                                f"{bound_expr.to_string()}"
                            )
                        return bound_expr
                    
                    return Expression.parameter(
                        sym_name, param_idx, dtype, dtype_obj, varnode.getSize(),
                        storage_info=storage_info,
                        runtime_ref=self._make_parameter_location_ref(
                            sym_name,
                            index=param_idx,
                        ),
                    )
                else:
                    dtype_obj = symbol.getDataType() if symbol.getDataType() else None
                    dtype = str(dtype_obj) if dtype_obj else None
                    runtime_ref = self._make_address_runtime_ref(
                        display_name=sym_name,
                        symbol=symbol,
                        high_var=high_var,
                    )
                    
                    if self._debug_available():
                        self._debug_print(f"  -> Variable (from symbol): {sym_name}")

                    if (
                        isinstance(runtime_ref, AddressValueRef)
                        and runtime_ref.has_concrete_address()
                        and varnode.isAddress()
                    ):
                        if self._debug_available():
                            self._debug_print(
                                "  -> Address-backed symbol; treating as concrete address object"
                            )
                        return Expression.constant(
                            runtime_ref.address_offset,
                            varnode.getSize(),
                            runtime_ref=runtime_ref,
                        )
                    
                    return Expression.variable(
                        sym_name, dtype, dtype_obj, varnode.getSize(),
                        storage_info=storage_info,
                        runtime_ref=runtime_ref,
                    )
            
            name = high_var.getName()
            if name and name != "UNNAMED":
                runtime_ref = self._make_address_runtime_ref(
                    display_name=name,
                    high_var=high_var,
                )
                if self._debug_available():
                    self._debug_print(f"  -> Variable (from high name): {name}")
                if (
                    isinstance(runtime_ref, AddressValueRef)
                    and runtime_ref.has_concrete_address()
                    and varnode.isAddress()
                ):
                    if self._debug_available():
                        self._debug_print(
                            "  -> Address-backed high variable; treating as concrete address object"
                        )
                    return Expression.constant(
                        runtime_ref.address_offset,
                        varnode.getSize(),
                        runtime_ref=runtime_ref,
                    )
                return Expression.variable(
                    name, size=varnode.getSize(),
                    storage_info=storage_info,
                    runtime_ref=runtime_ref,
                )

        storage_backed_param = self._resolve_storage_backed_parameter_expression(
            storage_info,
        )
        if storage_backed_param is not None:
            if self._debug_available():
                self._debug_print(
                    "  -> Parameter (storage-backed fallback): "
                    f"{storage_backed_param.to_string()}"
                )
            return storage_backed_param
        
        # 4. レジスタの場合（入力変数として扱う）
        if varnode.isRegister():
            reg = self.program.getRegister(varnode.getAddress(), varnode.getSize())
            if reg:
                reg_name = reg.getName()
                if self._debug_available():
                    self._debug_print(f"  -> Register (input): {reg_name}")
                    self._debug_print(f"     isInput: {varnode.isInput()}")
                    self._debug_print(f"     storage_info: {storage_info}")
                
                # 入力varnodeの場合は変数として扱う
                return Expression.variable(
                    reg_name, size=varnode.getSize(),
                    storage_info=storage_info
                )
        
        # 5. アドレス空間の変数（メモリ）
        if varnode.isAddress():
            addr = varnode.getAddress()
            runtime_ref = self._make_address_runtime_ref(
                display_name=str(addr) if addr is not None else None,
                high_var=high_var,
            )
            if self._debug_available():
                self._debug_print(f"  -> Memory address: {addr}")
            return Expression.constant(
                addr.getOffset(),
                varnode.getSize(),
                runtime_ref=runtime_ref,
            )
        
        # 6. ユニーク変数
        if varnode.isUnique():
            offset = varnode.getOffset()
            if self._debug_available():
                self._debug_print(f"  -> Unique (untraced): 0x{offset:x}")
            return Expression.unknown(f"unique_0x{offset:x}")
        
        # 7. 不明
        if self._debug_available():
            self._debug_print("  -> Unknown")
        
        key = VarnodeKey.from_varnode(varnode)
        return Expression.unknown(f"untraced_{key.space_name}_0x{key.offset:x}")
    
    def _trace_pcode_op(self, pcode_op, depth: int, use_cache: bool = True) -> Expression:
        """PcodeOpをトレースして式を構築"""
        op_key = self._get_op_key(pcode_op)
        
        # キャッシュチェック
        if use_cache and op_key in self._trace_cache:
            if self._debug_available():
                self._debug_print(f"  -> Cache hit for {pcode_op.getMnemonic()} (key={op_key})")
            return self._trace_cache[op_key]
        
        # 循環検出
        if op_key in self._trace_stack:
            if self._debug_available():
                self._debug_print(f"  -> Circular reference detected (key={op_key})")
            self.emit_unknown_event(reason="circular_reference", def_op=pcode_op,
                                    depth=depth, note=f"Key {op_key} already in stack")
            return Expression.unknown("circular_reference")
        
        self._trace_stack.add(op_key)
        
        try:
            result = self._trace_pcode_op_internal(pcode_op, depth, use_cache)
            if use_cache:
                self._trace_cache[op_key] = result
            return result
        finally:
            self._trace_stack.discard(op_key)
    
    def _trace_pcode_op_internal(self, pcode_op, depth: int, use_cache: bool = True) -> Expression:
        """PcodeOpトレースの内部処理"""
        mnemonic = pcode_op.getMnemonic()
        
        if self._debug_available():
            indent = "  " * depth
            self._debug_print(f"\n{indent}DEBUG trace_pcode_op (depth={depth}):")
            self._debug_print(f"{indent}  mnemonic: {mnemonic}")
            self._debug_print(f"{indent}  num_inputs: {pcode_op.getNumInputs()}")
            self._debug_print(f"{indent}  key: {self._get_op_key(pcode_op)}")
        
        inputs = []
        for i in range(pcode_op.getNumInputs()):
            input_varnode = pcode_op.getInput(i)
            inputs.append(input_varnode)
        
        # COPY
        if mnemonic == "COPY":
            if inputs:
                return self.trace_varnode(inputs[0], depth, use_cache)
            return Expression.unknown("copy_no_input")
        
        # 二項演算
        binary_ops = {
            "INT_ADD", "INT_SUB", "INT_MULT", "INT_DIV", "INT_SDIV",
            "INT_REM", "INT_SREM", "INT_AND", "INT_OR", "INT_XOR",
            "INT_LEFT", "INT_RIGHT", "INT_SRIGHT",
            "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_SLESS",
            "INT_LESSEQUAL", "INT_SLESSEQUAL",
            "FLOAT_ADD", "FLOAT_SUB", "FLOAT_MULT", "FLOAT_DIV",
            "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL",
            "BOOL_AND", "BOOL_OR", "BOOL_XOR",
        }
        
        if mnemonic in binary_ops:
            if len(inputs) >= 2:
                left = self.trace_varnode(inputs[0], depth, use_cache)
                right = self.trace_varnode(inputs[1], depth, use_cache)
                return Expression.binary_op(mnemonic, left, right)
            return Expression.unknown(f"{mnemonic}_insufficient_inputs")
        
        # 単項演算
        unary_ops = {
            "INT_NEGATE", "INT_2COMP", "BOOL_NEGATE", "INT_ZEXT", "INT_SEXT",
            "FLOAT_NEG", "FLOAT_ABS", "FLOAT_SQRT",
            "TRUNC", "FLOAT_FLOAT2FLOAT", "FLOAT_INT2FLOAT", "FLOAT_CEIL", "FLOAT_FLOOR",
            "POPCOUNT", "LZCOUNT",
        }
        
        if mnemonic in unary_ops:
            if inputs:
                operand = self.trace_varnode(inputs[0], depth, use_cache)
                result = Expression.unary_op(mnemonic, operand)
                # 出力サイズを取得（INT_ZEXT/INT_SEXTなどで重要）
                output = pcode_op.getOutput()
                if output:
                    result.size = output.getSize()
                return result
            return Expression.unknown(f"{mnemonic}_no_input")
        
        # CALL
        if mnemonic == "CALL":
            if inputs:
                target_ref = self._resolve_call_target_ref_from_op(
                    pcode_op,
                    depth,
                    use_cache,
                    allow_containing=True,
                    allow_code_address=True,
                )
                func_name = target_ref.display_name()
                self.emit_unknown_event(
                    reason="call_out_of_scope",
                    varnode=pcode_op.getOutput(),
                    def_op=pcode_op,
                    depth=depth,
                    note=f"CALL target={func_name}",
                )
                return self._build_unresolved_call_unknown(
                    pcode_op,
                    depth,
                    use_cache,
                    reason="call_out_of_scope",
                    target_ref=target_ref,
                )
            return Expression.unknown("call_no_target")

        # CALLIND
        if mnemonic == "CALLIND":
            if inputs:
                target_ref = self._resolve_call_target_ref_from_op(
                    pcode_op,
                    depth,
                    use_cache,
                    allow_containing=True,
                    allow_code_address=True,
                )
                target_name = target_ref.display_name()
                self.emit_unknown_event(
                    reason="callind_out_of_scope",
                    varnode=pcode_op.getOutput(),
                    def_op=pcode_op,
                    depth=depth,
                    note=f"CALLIND target={target_name}",
                )
                return self._build_unresolved_call_unknown(
                    pcode_op,
                    depth,
                    use_cache,
                    reason="callind_out_of_scope",
                    target_ref=target_ref,
                )
            return Expression.unknown("callind_no_target")
        
        # LOAD
        if mnemonic == "LOAD":
            if len(inputs) >= 2:
                addr = self.trace_varnode(inputs[1], depth, use_cache)
                output = pcode_op.getOutput()
                size = output.getSize() if output else 4
                order_key = self._get_op_order_key(pcode_op)
                return Expression.memory(
                    addr,
                    size,
                    read_order_key=order_key,
                    runtime_ref=ObservedMemoryReadRef(
                        order_key=order_key,
                        pcode_op_ref=self._make_pcode_op_ref(pcode_op),
                    ),
                )
            return Expression.unknown("load_insufficient_inputs")
        
        # STORE
        if mnemonic == "STORE":
            return Expression.unknown("store_no_output")
        
        # MULTIEQUAL - PhiHandlerで展開
        if mnemonic == "MULTIEQUAL":
            if self._debug_available():
                self._debug_print(f"\n{' ' * depth}  MULTIEQUAL detected - expanding via PhiHandler")
            
            if self.phi_handler is None:
                self.emit_unknown_event(
                    reason="phi_no_handler", varnode=pcode_op.getOutput(),
                    def_op=pcode_op, depth=depth, note="phi_handler is None"
                )
                if self.debug:
                    raise RuntimeError("phi_handler is None")
                return Expression.unknown("phi_no_handler_CRITICAL")
            
            try:
                phi_branches = self.phi_handler.resolve_multiequal(pcode_op, depth)
                
                if not phi_branches:
                    self.emit_unknown_event(
                        reason="phi_no_branches", varnode=pcode_op.getOutput(),
                        def_op=pcode_op, depth=depth,
                        note="PhiHandler returned empty"
                    )
                    return Expression.unknown("phi_no_branches")
                
                if len(phi_branches) == 1:
                    return phi_branches[0].value
                
                # 複数分岐 → PHI式構築
                branches = []
                for pb in phi_branches:
                    all_conds = pb.get_all_conditions()
                    if all_conds:
                        combined_cond = Condition.combine_and(all_conds)
                        branches.append((combined_cond, pb.value))
                    else:
                        branches.append((None, pb.value))
                
                output = pcode_op.getOutput()
                phi_expr = Expression.phi(branches)
                phi_expr.size = output.getSize() if output else 0
                return phi_expr
            
            except Exception as e:
                if self.debug:
                    import traceback as tb
                    tb.print_exc()
                self.emit_unknown_event(
                    reason="phi_expansion_error", varnode=pcode_op.getOutput(),
                    def_op=pcode_op, depth=depth, note=str(e)
                )
                if self.debug:
                    raise
                return Expression.unknown(f"phi_error:{str(e)[:50]}")
        
        # CAST
        if mnemonic == "CAST":
            if inputs:
                return self.trace_varnode(inputs[0], depth, use_cache)
            return Expression.unknown("cast_no_input")
        
        # PTRADD
        if mnemonic == "PTRADD":
            if len(inputs) >= 3:
                base = self.trace_varnode(inputs[0], depth, use_cache)
                index = self.trace_varnode(inputs[1], depth, use_cache)
                element_size = self.trace_varnode(inputs[2], depth, use_cache)
                output = pcode_op.getOutput()
                output_size = output.getSize() if output else max(
                    base.size if base is not None else 0,
                    index.size if index is not None else 0,
                    element_size.size if element_size is not None else 0,
                )
                intrinsic = Expression.intrinsic(
                    "PTRADD",
                    [base, index, element_size],
                    size=output_size,
                    opcode=PTRADD_OPCODE,
                )
                runtime_ref = self._derive_pointer_runtime_ref(intrinsic)
                if runtime_ref is not None:
                    intrinsic = intrinsic.clone_with(runtime_ref=runtime_ref)
                return intrinsic
            return Expression.unknown("ptradd_insufficient_inputs")

        # PTRSUB
        if mnemonic == "PTRSUB":
            if len(inputs) >= 2:
                base = self.trace_varnode(inputs[0], depth, use_cache)
                offset = self.trace_varnode(inputs[1], depth, use_cache)
                output = pcode_op.getOutput()
                output_size = output.getSize() if output else max(
                    base.size if base is not None else 0,
                    offset.size if offset is not None else 0,
                )
                intrinsic = Expression.intrinsic(
                    "PTRSUB",
                    [base, offset],
                    size=output_size,
                    opcode=PTRSUB_OPCODE,
                )
                runtime_ref = self._derive_pointer_runtime_ref(intrinsic)
                if runtime_ref is not None:
                    intrinsic = intrinsic.clone_with(runtime_ref=runtime_ref)
                return intrinsic
            return Expression.unknown("ptrsub_insufficient_inputs")

        if mnemonic == "CALLOTHER":
            userop_name = self._resolve_callother_userop_name(pcode_op)
            if userop_name:
                intrinsic_spec = resolve_pcode_intrinsic(mnemonic=userop_name)
                if intrinsic_spec is not None and len(inputs) >= 1:
                    operands = [
                        self.trace_varnode(inp, depth, use_cache)
                        for inp in inputs[1:]
                    ]
                    output = pcode_op.getOutput()
                    output_size = output.getSize() if output is not None else 0
                    return Expression.intrinsic(
                        intrinsic_spec.mnemonic,
                        operands,
                        size=output_size,
                        opcode=intrinsic_spec.opcode,
                    )

        # PIECE - サイズ情報を保持
        if mnemonic == "PIECE":
            if len(inputs) >= 2:
                high = self.trace_varnode(inputs[0], depth, use_cache)
                low = self.trace_varnode(inputs[1], depth, use_cache)
                # サイズを取得
                output = pcode_op.getOutput()
                output_size = output.getSize() if output else (high.size + low.size)
                expr = Expression.binary_op("PIECE", high, low)
                expr.size = output_size
                return expr
            return Expression.unknown("piece_insufficient_inputs")
        
        # SUBPIECE - サイズ情報を保持
        if mnemonic == "SUBPIECE":
            if len(inputs) >= 2:
                source = self.trace_varnode(inputs[0], depth, use_cache)
                offset = self.trace_varnode(inputs[1], depth, use_cache)
                # 出力サイズを取得
                output = pcode_op.getOutput()
                output_size = output.getSize() if output else 4
                expr = Expression.binary_op("SUBPIECE", source, offset)
                expr.size = output_size
                return expr
            return Expression.unknown("subpiece_insufficient_inputs")
        
        # その他
        if self._debug_available():
            self._debug_print(f"  -> Unhandled opcode: {mnemonic}")

        if mnemonic == "INDIRECT":
            output = pcode_op.getOutput()
            output_size = output.getSize() if output is not None else 0
            output_location = (
                self._canonical_location_for_varnode(output, output_size)
                if output is not None
                else None
            )
            input_location = None
            if inputs:
                try:
                    input_location = self._canonical_location_for_varnode(
                        inputs[0],
                        inputs[0].getSize(),
                    )
                except Exception:
                    input_location = None
            if (
                output is not None
                and output_location is not None
                and input_location is not None
                and output_location == input_location
            ):
                promoted = self._symbolic_post_state_read_for_output_varnode(
                    output,
                    output_size,
                )
                if promoted is not None:
                    return promoted
            base_expr = self.trace_varnode(inputs[0], depth, use_cache) if inputs else None
            if (
                base_expr is not None
                and base_expr.expr_type == ExpressionType.CONSTANT
                and int(getattr(base_expr, "value", 1)) == 0
                and output is not None
            ):
                promoted = self._symbolic_post_state_read_for_output_varnode(
                    output,
                    output_size,
                )
                if promoted is not None:
                    return promoted

        if inputs:
            traced_inputs = [self.trace_varnode(inp, depth, use_cache) for inp in inputs]
            if len(traced_inputs) == 1:
                return Expression.unary_op(mnemonic, traced_inputs[0])
            elif len(traced_inputs) == 2:
                return Expression.binary_op(mnemonic, traced_inputs[0], traced_inputs[1])
            else:
                output = pcode_op.getOutput()
                output_size = output.getSize() if output is not None else 0
                return Expression.intrinsic(
                    mnemonic,
                    traced_inputs,
                    size=output_size,
                    opcode=getattr(pcode_op, "getOpcode", lambda: None)(),
                )

        return Expression.unknown(f"unhandled_{mnemonic}")

    def resolve_call_target_ref(
        self,
        addr_varnode,
        *,
        allow_containing: bool = True,
        allow_code_address: bool = True,
    ) -> Optional[CallTargetRef]:
        """CALL/CALLIND の target を object ベースで解決する。"""
        if addr_varnode is None or self.program is None:
            return None

        address = None
        try:
            if addr_varnode.isConstant():
                address = addr_varnode.getAddress()
            else:
                candidate = addr_varnode.getAddress()
                space = candidate.getAddressSpace() if candidate else None
                if space and not (
                    space.isRegisterSpace()
                    or space.isUniqueSpace()
                    or space.isConstantSpace()
                ):
                    address = candidate
        except Exception:
            address = None

        if address is None:
            return None

        try:
            function_manager = self.program.getFunctionManager()
            if function_manager is not None:
                get_function_at = getattr(function_manager, "getFunctionAt", None)
                if callable(get_function_at):
                    func = get_function_at(address)
                    if func is not None:
                        return CallTargetRef.from_function(func)
                get_referenced_function = getattr(function_manager, "getReferencedFunction", None)
                if callable(get_referenced_function):
                    func = get_referenced_function(address)
                    if func is not None:
                        return CallTargetRef.from_function(func)
                if allow_containing:
                    get_function_containing = getattr(function_manager, "getFunctionContaining", None)
                    if callable(get_function_containing):
                        func = get_function_containing(address)
                        if func is not None:
                            return CallTargetRef.from_function(func)
        except Exception:
            pass

        if not allow_code_address:
            return None

        try:
            return CallTargetRef.from_code_address(int(address.getOffset()))
        except Exception:
            return None

    def _get_function_name(self, addr_varnode) -> str:
        """関数アドレスから関数名を取得"""
        target_ref = self.resolve_call_target_ref(
            addr_varnode,
            allow_containing=True,
            allow_code_address=True,
        )
        if target_ref is None:
            return "UNKNOWN_FUNC"
        return target_ref.display_name()
    
    def get_all_pcode_ops(self) -> List[Any]:
        """全てのPcodeOpをリストで取得"""
        ops = []
        basic_blocks = self.high_function.getBasicBlocks()
        
        for bb in basic_blocks:
            pcode_iter = bb.getIterator()
            while pcode_iter.hasNext():
                ops.append(pcode_iter.next())
        
        return ops
    
    def find_return_ops(self) -> List[Any]:
        """RETURNオペレーションを全て取得"""
        returns = []
        
        for pcode_op in self.get_all_pcode_ops():
            if pcode_op.getMnemonic() == "RETURN":
                returns.append(pcode_op)
        
        return returns
