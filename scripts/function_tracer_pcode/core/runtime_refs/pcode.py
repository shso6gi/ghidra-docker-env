"""P-code op / block references and their ordinal signatures."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple


_MAX_PARENT_PCODE_OP_SCAN = 10000


def _coerce_nonnegative_int(value: Any) -> Optional[int]:
    if value is None or isinstance(value, bool):
        return None
    try:
        coerced = int(value)
    except (TypeError, ValueError):
        return None
    return coerced if coerced >= 0 else None


def _coerce_optional_text(value: Any) -> Optional[str]:
    if value is None:
        return None
    text = str(value)
    return text if text else None


def _coerce_opcode(value: Any) -> Optional[Any]:
    if value is None or isinstance(value, bool):
        return None
    try:
        return int(value)
    except (TypeError, ValueError):
        return str(value)


def _address_components(address: Any) -> Tuple[Optional[str], Optional[int]]:
    if address is None:
        return None, None
    space_name = None
    try:
        space = address.getAddressSpace()
    except Exception:
        space = None
    if space is not None:
        try:
            space_name = space.getName()
        except Exception:
            space_name = None
    try:
        offset = address.getOffset()
    except Exception:
        offset = None
    return _coerce_optional_text(space_name), _coerce_nonnegative_int(offset)


def _pcode_op_ordinal_signature(pcode_op: Any) -> Tuple[Any, ...]:
    target_space = None
    target_offset = None
    seq_time = None
    seq_order = None
    try:
        seq = pcode_op.getSeqnum()
    except Exception:
        seq = None
    if seq is not None:
        try:
            target_space, target_offset = _address_components(seq.getTarget())
        except Exception:
            target_space, target_offset = None, None
        try:
            seq_time = _coerce_nonnegative_int(seq.getTime())
        except Exception:
            seq_time = None
        try:
            seq_order = _coerce_nonnegative_int(seq.getOrder())
        except Exception:
            seq_order = None
    try:
        opcode = _coerce_opcode(pcode_op.getOpcode())
    except Exception:
        opcode = None
    try:
        mnemonic = _coerce_optional_text(pcode_op.getMnemonic())
    except Exception:
        mnemonic = None
    return (target_space, target_offset, seq_time, seq_order, opcode, mnemonic)


def _local_op_ordinal_from_parent(pcode_op: Any) -> Optional[int]:
    try:
        parent = pcode_op.getParent()
    except Exception:
        parent = None
    if parent is None:
        return None
    iterator = getattr(parent, "getIterator", lambda: None)()
    if iterator is None:
        return None
    target_signature = _pcode_op_ordinal_signature(pcode_op)
    ordinal = 0
    while ordinal < _MAX_PARENT_PCODE_OP_SCAN:
        try:
            has_next = iterator.hasNext()
        except Exception:
            return None
        if not isinstance(has_next, bool):
            return None
        if not has_next:
            return None
        try:
            candidate = iterator.next()
        except Exception:
            return None
        if candidate is pcode_op or candidate == pcode_op:
            return ordinal
        if _pcode_op_ordinal_signature(candidate) == target_signature:
            return ordinal
        ordinal += 1
    return None


@dataclass(frozen=True)
class PcodeOpRef:
    """Stable identity for a concrete Ghidra P-code operation."""

    address_offset: Optional[int] = None
    seq_time: Optional[int] = None
    seq_order: Optional[int] = None
    block_index: Optional[int] = None
    mnemonic: Optional[str] = None
    input_sizes: Tuple[int, ...] = ()
    output_size: Optional[int] = None
    binary_id: Optional[Any] = None
    function_entry_space: Optional[str] = None
    function_entry_offset: Optional[int] = None
    target_space: Optional[str] = None
    target_offset: Optional[int] = None
    opcode: Optional[Any] = None
    local_op_ordinal: Optional[int] = None
    program_uid: Optional[int] = None

    def __post_init__(self) -> None:
        normalized_input_sizes = []
        for size in tuple(self.input_sizes or ()):
            try:
                int_size = int(size)
            except (TypeError, ValueError):
                continue
            if int_size > 0:
                normalized_input_sizes.append(int_size)
        object.__setattr__(self, "input_sizes", tuple(normalized_input_sizes))
        try:
            output_size = int(self.output_size) if self.output_size is not None else None
        except (TypeError, ValueError):
            output_size = None
        object.__setattr__(self, "output_size", output_size if output_size and output_size > 0 else None)
        object.__setattr__(self, "address_offset", _coerce_nonnegative_int(self.address_offset))
        object.__setattr__(self, "seq_time", _coerce_nonnegative_int(self.seq_time))
        object.__setattr__(self, "seq_order", _coerce_nonnegative_int(self.seq_order))
        object.__setattr__(self, "block_index", _coerce_nonnegative_int(self.block_index))
        object.__setattr__(
            self,
            "function_entry_offset",
            _coerce_nonnegative_int(self.function_entry_offset),
        )
        normalized_target_offset = _coerce_nonnegative_int(self.target_offset)
        if normalized_target_offset is None:
            normalized_target_offset = self.address_offset
        object.__setattr__(self, "target_offset", normalized_target_offset)
        object.__setattr__(self, "local_op_ordinal", _coerce_nonnegative_int(self.local_op_ordinal))
        object.__setattr__(self, "function_entry_space", _coerce_optional_text(self.function_entry_space))
        object.__setattr__(self, "target_space", _coerce_optional_text(self.target_space))
        object.__setattr__(self, "mnemonic", _coerce_optional_text(self.mnemonic))
        object.__setattr__(self, "opcode", _coerce_opcode(self.opcode))
        object.__setattr__(self, "program_uid", _coerce_nonnegative_int(self.program_uid))

    def input_size(self, index: int = 0) -> Optional[int]:
        try:
            return self.input_sizes[int(index)]
        except (IndexError, TypeError, ValueError):
            return None

    @classmethod
    def from_pcode_op(
        cls,
        pcode_op: Any,
        *,
        binary_id: Optional[Any] = None,
        program_uid: Optional[int] = None,
        function_entry: Any = None,
        function_entry_space: Optional[str] = None,
        function_entry_offset: Optional[int] = None,
        local_op_ordinal: Optional[int] = None,
    ) -> Optional["PcodeOpRef"]:
        """Build a stable, object-derived reference for a concrete Ghidra P-code op."""
        if pcode_op is None:
            return None

        address_offset = None
        target_space = None
        seq_time = None
        seq_order = None
        block_index = None
        mnemonic = None
        input_sizes = []
        output_size = None
        opcode = None

        try:
            mnemonic = pcode_op.getMnemonic()
        except Exception:
            mnemonic = None
        try:
            opcode = pcode_op.getOpcode()
        except Exception:
            opcode = None

        try:
            seq = pcode_op.getSeqnum()
        except Exception:
            seq = None
        if seq is not None:
            try:
                target = seq.getTarget()
                target_space, address_offset = _address_components(target)
            except Exception:
                address_offset = None
            try:
                time = getattr(seq, "getTime", lambda: None)()
                seq_time = None if time is None else int(time)
            except Exception:
                seq_time = None
            try:
                order = seq.getOrder()
                seq_order = None if order is None else int(order)
            except Exception:
                seq_order = None

        try:
            parent = pcode_op.getParent()
        except Exception:
            parent = None
        if parent is not None:
            try:
                block_index = int(parent.getIndex())
            except Exception:
                block_index = None
        if local_op_ordinal is None:
            local_op_ordinal = _local_op_ordinal_from_parent(pcode_op)

        try:
            num_inputs = int(pcode_op.getNumInputs())
        except Exception:
            num_inputs = 0
        for input_index in range(max(0, num_inputs)):
            try:
                input_varnode = pcode_op.getInput(input_index)
                input_size = int(input_varnode.getSize())
            except Exception:
                continue
            if input_size > 0:
                input_sizes.append(input_size)

        try:
            output_varnode = pcode_op.getOutput()
            output_size = int(output_varnode.getSize()) if output_varnode is not None else None
        except Exception:
            output_size = None

        return cls(
            address_offset=address_offset,
            seq_time=seq_time,
            seq_order=seq_order,
            block_index=block_index,
            mnemonic=mnemonic,
            input_sizes=tuple(input_sizes),
            output_size=output_size,
            binary_id=binary_id,
            program_uid=program_uid,
            function_entry_space=(
                function_entry_space
                if function_entry_space is not None
                else _address_components(function_entry)[0]
            ),
            function_entry_offset=(
                function_entry_offset
                if function_entry_offset is not None
                else _address_components(function_entry)[1]
            ),
            target_space=target_space,
            target_offset=address_offset,
            opcode=opcode,
            local_op_ordinal=local_op_ordinal,
        )

    def stable_key(self) -> Tuple[Any, ...]:
        if self._has_full_identity_context():
            return (
                "pcode_op",
                self.binary_id,
                (
                    "function_entry",
                    self.function_entry_space,
                    int(self.function_entry_offset),
                ),
                (
                    "seq_target",
                    self.target_space,
                    int(self.target_offset),
                ),
                int(self.seq_time),
                int(self.seq_order),
                self.opcode,
                int(self.local_op_ordinal),
            )
        return (
            "pcode_op",
            None if self.address_offset is None else int(self.address_offset),
            None if self.seq_time is None else int(self.seq_time),
            None if self.seq_order is None else int(self.seq_order),
            None if self.block_index is None else int(self.block_index),
            self.mnemonic,
        )

    def _has_full_identity_context(self) -> bool:
        return (
            self.binary_id is not None
            and self.function_entry_space is not None
            and self.function_entry_offset is not None
            and self.target_space is not None
            and self.target_offset is not None
            and self.seq_time is not None
            and self.seq_order is not None
            and self.opcode is not None
            and self.local_op_ordinal is not None
        )

    def to_dict(self) -> Dict[str, Any]:
        result = {
            "kind": "pcode_op",
            "address_offset": self.address_offset,
            "seq_time": self.seq_time,
            "seq_order": self.seq_order,
            "block_index": self.block_index,
            "mnemonic": self.mnemonic,
            "input_sizes": list(self.input_sizes),
            "output_size": self.output_size,
        }
        if self.binary_id is not None:
            result["binary_id"] = self.binary_id
        if self.program_uid is not None:
            result["program_uid"] = self.program_uid
        if self.function_entry_space is not None:
            result["function_entry_space"] = self.function_entry_space
        if self.function_entry_offset is not None:
            result["function_entry_offset"] = self.function_entry_offset
        if self.target_space is not None:
            result["target_space"] = self.target_space
        if self.target_offset is not None:
            result["target_offset"] = self.target_offset
        if self.opcode is not None:
            result["opcode"] = self.opcode
        if self.local_op_ordinal is not None:
            result["local_op_ordinal"] = self.local_op_ordinal
        return result


@dataclass(frozen=True)
class PcodeBlockRef:
    """Stable identity for a concrete Ghidra decompiler basic block."""

    block_index: Optional[int] = None
    start_address_offset: Optional[int] = None
    binary_id: Optional[Any] = None
    function_entry_space: Optional[str] = None
    function_entry_offset: Optional[int] = None

    def stable_key(self) -> Tuple[Any, ...]:
        if (
            self.binary_id is not None
            and self.function_entry_space is not None
            and self.function_entry_offset is not None
        ):
            return (
                "pcode_block",
                self.binary_id,
                (
                    "function_entry",
                    self.function_entry_space,
                    int(self.function_entry_offset),
                ),
                None if self.block_index is None else int(self.block_index),
                None if self.start_address_offset is None else int(self.start_address_offset),
            )
        return (
            "pcode_block",
            None if self.block_index is None else int(self.block_index),
            None if self.start_address_offset is None else int(self.start_address_offset),
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "pcode_block",
            "block_index": self.block_index,
            "start_address_offset": self.start_address_offset,
            "binary_id": self.binary_id,
            "function_entry_space": self.function_entry_space,
            "function_entry_offset": self.function_entry_offset,
        }
