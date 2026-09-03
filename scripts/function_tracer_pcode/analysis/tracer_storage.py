"""Parameter and storage descriptors, bound-parameter expressions and width coercion."""

from __future__ import annotations

from typing import Dict, List, Optional, Tuple, Any
from scripts.function_tracer_pcode.core import Expression, StorageInfo, LocationBaseRef
from scripts.function_tracer_pcode.core.signature import (
    get_data_type_display_name,
    is_unsigned_data_type,
)
from scripts.function_tracer_pcode.analysis.tracer_support import ParameterStorageDescriptor


class ParameterStorageMixin:
    """Parameter and storage descriptors, bound-parameter expressions and width coercion."""

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
