"""Address / pointer runtime references, canonical locations and symbolic post-state reads."""

from __future__ import annotations

from typing import Optional, Any
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    Expression,
    StorageInfo,
    AddressValueRef,
    LocationBaseRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
)


class AddressRefMixin:
    """Address / pointer runtime references, canonical locations and symbolic post-state reads."""

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
