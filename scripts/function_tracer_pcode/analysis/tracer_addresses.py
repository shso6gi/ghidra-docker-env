"""Address / pointer runtime references, canonical locations and symbolic post-state reads."""

from __future__ import annotations

from typing import Optional, Any
from scripts.function_tracer_pcode.core.signature import is_composite_data_type, is_pointer_data_type
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

    def _global_object_value_expression(
        self,
        varnode,
        runtime_ref: AddressValueRef,
        *,
        display_name: Optional[str],
        data_type: Optional[str],
        data_type_obj: Any,
        storage_info: Any,
    ) -> Expression:
        """Value of an input ``ram`` varnode that names a global object.

        A varnode whose address is a global and that has no defining op is a
        *read* of that global.  For a scalar (numeric / pointer / undefined)
        type the value is the memory contents at that address, so emit a
        memory load of the concrete address: the memory resolver concretises
        it when the block is read-only (``.rodata`` constants) and it stays a
        symbolic read of ``mem`` otherwise.  Arrays, structures and unions are
        used as address bases (PTRADD/PTRSUB), so those keep the address
        object semantics (Issue #30).
        """
        size = varnode.getSize()
        if is_composite_data_type(data_type_obj, data_type):
            if self._debug_available():
                self._debug_print(
                    "  -> Address-backed composite symbol; treating as concrete address object"
                )
            return Expression.constant(
                runtime_ref.address_offset, size, runtime_ref=runtime_ref,
            )
        if runtime_ref.is_readonly_memory():
            image_value = self._read_program_memory_value(runtime_ref.address_offset, size)
            if image_value is not None:
                if self._debug_available():
                    self._debug_print(
                        f"  -> Global scalar read {display_name or ''}@0x{runtime_ref.address_offset:x}: "
                        f"read-only image constant 0x{image_value:x}"
                    )
                # A read-only pointer slot (GOT entry, relocated pointer table)
                # yields the address of another object.  Keep that object's
                # identity on the constant so a STORE/LOAD through the pointer
                # canonicalises to the named global instead of a bare number.
                if is_pointer_data_type(data_type_obj, data_type):
                    target_ref = self._make_address_runtime_ref_for_offset(
                        image_value,
                        require_ghidra_evidence=True,
                    )
                    if target_ref is not None and target_ref.global_object_identity() is not None:
                        return Expression.constant(image_value, size, runtime_ref=target_ref)
                return Expression.constant(image_value, size)
        pointer_size = 8
        try:
            pointer_size = int(self.program.getDefaultPointerSize()) or 8
        except Exception:
            pointer_size = 8
        if self._debug_available():
            self._debug_print(
                f"  -> Global scalar read {display_name or ''}@0x{runtime_ref.address_offset:x}: "
                "memory load of the concrete address"
            )
        address_expr = Expression.constant(
            runtime_ref.address_offset, pointer_size, runtime_ref=runtime_ref,
        )
        return Expression.memory(address_expr, size)

    def _read_program_memory_value(self, address_value: int, size_bytes: int) -> Optional[int]:
        """Unsigned integer at ``address_value`` from the program image, or None."""
        if address_value < 0 or size_bytes <= 0:
            return None
        try:
            memory = self.program.getMemory()
            default_space = self.program.getAddressFactory().getDefaultAddressSpace()
            address = default_space.getAddress(address_value)
            if address is None:
                return None
            raw = [int(memory.getByte(address.add(offset))) & 0xFF for offset in range(size_bytes)]
            ordered = raw if self.program.getLanguage().isBigEndian() else list(reversed(raw))
            value = 0
            for byte in ordered:
                value = (value << 8) | byte
            return value
        except Exception:
            return None

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

            object_symbol_name, object_base_offset, object_size = self._global_object_facts(address)
            return AddressValueRef(
                address_offset=offset,
                source=source,
                display_hint=display_name,
                object_symbol_name=object_symbol_name,
                object_base_offset=object_base_offset,
                object_size=object_size,
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

        object_symbol_name, object_base_offset, object_size = self._global_object_facts(address)
        return AddressValueRef(
            address_offset=offset,
            source="constant_offset",
            display_hint=display_name,
            object_symbol_name=object_symbol_name,
            object_base_offset=object_base_offset,
            object_size=object_size,
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

    def _global_object_facts(self, address):
        """``(symbol_name, base_offset, size)`` of the named data object at ``address``.

        The object is the Ghidra data item containing the address; its name is
        the non-dynamic primary symbol at the item start (imported ELF object
        symbols such as ``count``).  Ghidra's synthesised names (``DAT_``,
        ``PTR_``, offcut ``h[4]``) are dynamic and never used as identity.
        Returns ``(None, None, None)`` when there is no such object.
        """

        if address is None or self.program is None:
            return None, None, None
        try:
            listing = self.program.getListing()
            symbol_table = self.program.getSymbolTable()
        except Exception:
            return None, None, None
        if listing is None or symbol_table is None:
            return None, None, None
        data = None
        getter = getattr(listing, "getDataContaining", None)
        if callable(getter):
            try:
                data = getter(address)
            except Exception:
                data = None
        if data is None:
            return None, None, None
        try:
            base_address = data.getAddress()
            length = int(data.getLength())
        except Exception:
            return None, None, None
        if base_address is None or length <= 0:
            return None, None, None
        try:
            symbol = symbol_table.getPrimarySymbol(base_address)
        except Exception:
            symbol = None
        if symbol is None:
            return None, None, None
        try:
            if bool(symbol.isDynamic()):
                return None, None, None
            name = symbol.getName()
        except Exception:
            return None, None, None
        if not name or not str(name).strip():
            return None, None, None
        try:
            base_offset = int(base_address.getOffset())
        except Exception:
            return None, None, None
        return str(name).strip(), base_offset, length

    def ram_varnode_write_class(self, varnode) -> Optional[str]:
        """Classify a ``ram``-space varnode as a write target.

        ``"global"`` for a writable, non-volatile named data object,
        ``"readonly"`` for read-only memory (GOT slots, ``.rodata``),
        ``"unresolved"`` for writable memory without a stable object identity
        (stripped symbol, volatile block, no data item) and ``None`` when the
        varnode is not an addressable ``ram`` location at all.
        """

        if varnode is None:
            return None
        try:
            if not varnode.isAddress():
                return None
            address = varnode.getAddress()
            space = address.getAddressSpace()
            space_name = space.getName() if space is not None else None
        except Exception:
            return None
        if space_name in {None, "stack", "register", "unique", "const"}:
            return None
        # Only a real memory space (Ghidra ``AddressSpace.isMemorySpace``) can
        # hold an observable object; overlay / hash / external / OTHER spaces
        # are not classified by name alone.
        is_memory = getattr(space, "isMemorySpace", None)
        if callable(is_memory):
            try:
                if not bool(is_memory()):
                    return None
            except Exception:
                return None
        runtime_ref = self._make_address_runtime_ref_for_offset(
            int(address.getOffset()),
            require_ghidra_evidence=False,
        )
        if runtime_ref is None:
            return "unresolved"
        if runtime_ref.is_readonly_memory():
            return "readonly"
        if runtime_ref.can_write is False and runtime_ref.is_volatile is False:
            return "readonly"
        if runtime_ref.global_object_identity() is not None:
            return "global"
        return "unresolved"

    def global_object_location_for_varnode(self, varnode) -> Optional[CanonicalLocation]:
        """Canonical global location of a writable ``ram`` varnode, or ``None``."""

        if self.ram_varnode_write_class(varnode) != "global":
            return None
        try:
            address = varnode.getAddress()
            size = int(varnode.getSize())
        except Exception:
            return None
        runtime_ref = self._make_address_runtime_ref_for_offset(
            int(address.getOffset()),
            require_ghidra_evidence=False,
        )
        identity = runtime_ref.global_object_identity() if runtime_ref is not None else None
        if identity is None:
            return None
        symbol_name, object_size, offset = identity
        if offset + max(1, size) > object_size:
            return None
        return CanonicalLocation(
            base_ref=LocationBaseRef.global_object(
                symbol_name,
                object_size,
                space_name=runtime_ref.space_name,
            ),
            offset=int(offset),
            size=max(1, size),
        )

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
