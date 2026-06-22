# -*- coding: utf-8 -*-
"""Runtime object references carried through expression analysis."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Dict, Optional, Sequence, Tuple

from .call_target import CallTargetRef, coerce_call_target_ref

_MAX_PARENT_PCODE_OP_SCAN = 10000


@dataclass(frozen=True)
class AddressValueRef:
    """Structured constant-address identity for runtime analysis."""

    address_offset: int
    source: str = "ghidra_object"
    display_hint: Optional[str] = None
    program_id: Optional[int] = None
    space_id: Optional[int] = None
    space_name: Optional[str] = None
    symbol_name: Optional[str] = None
    block_name: Optional[str] = None
    is_initialized: Optional[bool] = None
    can_read: Optional[bool] = None
    can_write: Optional[bool] = None
    can_execute: Optional[bool] = None
    is_volatile: Optional[bool] = None

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        return (
            "address",
            self.program_id,
            self.space_id,
            int(self.address_offset),
        )

    def has_concrete_address(self) -> bool:
        return int(self.address_offset) >= 0

    def is_readonly_memory(self) -> bool:
        return bool(
            self.has_concrete_address()
            and self.is_initialized
            and self.can_read
            and not self.can_write
            and not self.is_volatile
        )

    def display_name(self) -> str:
        return self.display_hint or f"ADDR_{int(self.address_offset):x}"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "address",
            "address_offset": int(self.address_offset),
            "source": self.source,
            "display_name": self.display_name(),
            "program_id": self.program_id,
            "space_id": self.space_id,
            "space_name": self.space_name,
            "symbol_name": self.symbol_name,
            "block_name": self.block_name,
            "is_initialized": self.is_initialized,
            "can_read": self.can_read,
            "can_write": self.can_write,
            "can_execute": self.can_execute,
            "is_volatile": self.is_volatile,
            "is_readonly_memory": self.is_readonly_memory(),
        }


@dataclass(frozen=True)
class LocationBaseRef:
    """Structured identity for the root of a canonical memory location."""

    kind: str
    parameter_name: Optional[str] = None
    parameter_index: Optional[int] = None
    owner_program_id: Optional[int] = None
    owner_entry_offset: Optional[int] = None
    storage_space_id: Optional[int] = None
    storage_space: Optional[str] = None
    storage_offset: Optional[int] = None
    storage_size: Optional[int] = None
    storage_identity_key: Optional[Tuple[Any, ...]] = None
    display_hint: Optional[str] = None

    def __post_init__(self) -> None:
        if self.kind not in {"parameter", "stack_frame", "storage"}:
            raise ValueError(f"Unsupported location base kind: {self.kind}")
        if self.kind == "parameter":
            normalized_index = None
            if self.parameter_index is not None:
                try:
                    candidate = int(self.parameter_index)
                except Exception:
                    candidate = None
                if candidate is not None and candidate >= 0:
                    normalized_index = candidate
            if normalized_index != self.parameter_index:
                object.__setattr__(self, "parameter_index", normalized_index)

    @classmethod
    def parameter(
        cls,
        name: str,
        *,
        index: Optional[int] = None,
        owner_program_id: Optional[int] = None,
        owner_entry_offset: Optional[int] = None,
    ) -> "LocationBaseRef":
        return cls(
            kind="parameter",
            parameter_name=name or None,
            parameter_index=index,
            owner_program_id=owner_program_id,
            owner_entry_offset=owner_entry_offset,
            display_hint=name or None,
        )

    @classmethod
    def stack_frame(cls) -> "LocationBaseRef":
        return cls(kind="stack_frame", display_hint="stackframe")

    @classmethod
    def storage(
        cls,
        *,
        space_id: Optional[int] = None,
        space_name: Optional[str],
        offset: int,
        size: int,
        storage_identity_key: Optional[Tuple[Any, ...]] = None,
        display_hint: Optional[str] = None,
    ) -> "LocationBaseRef":
        return cls(
            kind="storage",
            storage_space_id=space_id,
            storage_space=space_name or None,
            storage_offset=int(offset),
            storage_size=max(1, int(size or 0)),
            storage_identity_key=tuple(storage_identity_key) if storage_identity_key is not None else None,
            display_hint=display_hint,
        )

    def is_parameter(self) -> bool:
        return self.kind == "parameter"

    def is_stack_frame(self) -> bool:
        return self.kind == "stack_frame"

    def is_storage(self) -> bool:
        return self.kind == "storage"

    def __hash__(self) -> int:
        return hash(self.stable_key())

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, LocationBaseRef):
            return False
        if self.kind != other.kind:
            return False
        if self.is_parameter():
            if self.parameter_index is not None and other.parameter_index is not None:
                if (
                    self.owner_program_id is not None
                    or self.owner_entry_offset is not None
                    or other.owner_program_id is not None
                    or other.owner_entry_offset is not None
                ):
                    return (
                        self.owner_program_id == other.owner_program_id
                        and self.owner_entry_offset == other.owner_entry_offset
                        and int(self.parameter_index) == int(other.parameter_index)
                    )
                return int(self.parameter_index) == int(other.parameter_index)
            return False
        if self.is_stack_frame():
            return True
        if self.storage_identity_key is not None or other.storage_identity_key is not None:
            return (
                self.storage_identity_key is not None
                and other.storage_identity_key is not None
                and self.storage_identity_key == other.storage_identity_key
            )
        return (
            self.storage_space_id == other.storage_space_id
            and int(self.storage_offset or 0) == int(other.storage_offset or 0)
            and int(self.storage_size or 0) == int(other.storage_size or 0)
        )

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        if self.is_parameter():
            if self.parameter_index is not None:
                if self.owner_program_id is not None or self.owner_entry_offset is not None:
                    return (
                        "parameter",
                        self.owner_program_id,
                        self.owner_entry_offset,
                        int(self.parameter_index),
                    )
                return ("parameter", int(self.parameter_index))
            return (
                "parameter",
                self.owner_program_id,
                self.owner_entry_offset,
                None,
                self.parameter_name,
            )
        if self.is_stack_frame():
            return ("stack_frame",)
        if self.storage_identity_key is not None:
            return ("storage_identity", self.storage_identity_key)
        return (
            "storage",
            self.storage_space_id,
            self.storage_space,
            int(self.storage_offset or 0),
            int(self.storage_size or 0),
        )

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        """Program-independent identity for comparing function-local locations.

        ``stable_key`` intentionally distinguishes the same parameter position in
        different Ghidra functions.  Loop equivalence, however, compares two
        functions under an explicit parameter correspondence, so a parameter
        base is identified by argument position rather than by the owning
        program/function object.  Storage-backed locations remain concrete.
        """

        if self.is_parameter():
            if self.parameter_index is not None:
                return ("parameter", int(self.parameter_index))
            return None
        if self.is_stack_frame():
            return ("stack_frame",)
        if self.storage_identity_key is not None:
            return ("storage_identity", self.storage_identity_key)
        return (
            "storage",
            self.storage_space_id,
            self.storage_space,
            int(self.storage_offset or 0),
            int(self.storage_size or 0),
        )

    def display_name(self) -> str:
        if self.display_hint:
            return self.display_hint
        if self.is_parameter():
            return self.parameter_name or "param"
        if self.is_stack_frame():
            return "stackframe"
        space = self.storage_space or "mem"
        return f"{space}@{int(self.storage_offset or 0)}:{int(self.storage_size or 0)}"

    def matches_parameter(self, param: Dict[str, Any]) -> bool:
        if not self.is_parameter():
            return False
        try:
            param_index = param.get("index")
            if self.parameter_index is not None and param_index is not None:
                if self.owner_program_id is not None or self.owner_entry_offset is not None:
                    return (
                        int(param_index) == int(self.parameter_index)
                        and param.get("owner_program_id") == self.owner_program_id
                        and param.get("owner_entry_offset") == self.owner_entry_offset
                    )
                return int(param_index) == int(self.parameter_index)
        except Exception:
            pass
        return False

    def to_dict(self) -> Dict[str, Any]:
        result: Dict[str, Any] = {
            "kind": self.kind,
            "display_name": self.display_name(),
        }
        if self.parameter_name is not None:
            result["parameter_name"] = self.parameter_name
        if self.parameter_index is not None:
            result["parameter_index"] = self.parameter_index
        if self.owner_program_id is not None:
            result["owner_program_id"] = self.owner_program_id
        if self.owner_entry_offset is not None:
            result["owner_entry_offset"] = self.owner_entry_offset
        if self.storage_space is not None:
            result["storage_space"] = self.storage_space
        if self.storage_space_id is not None:
            result["storage_space_id"] = self.storage_space_id
        if self.storage_offset is not None:
            result["storage_offset"] = self.storage_offset
        if self.storage_size is not None:
            result["storage_size"] = self.storage_size
        if self.storage_identity_key is not None:
            result["storage_identity_key"] = self.storage_identity_key
        return result


@dataclass(frozen=True)
class LocationStep:
    kind: str
    value: int

    def __post_init__(self) -> None:
        if self.kind not in {"offset", "deref"}:
            raise ValueError(f"Unsupported location step kind: {self.kind}")

    def stable_key(self) -> Tuple[str, int]:
        return (self.kind, int(self.value))

    def to_dict(self) -> Dict[str, Any]:
        return {"kind": self.kind, "value": int(self.value)}


@dataclass(frozen=True, init=False)
class CanonicalLocation:
    base_ref: LocationBaseRef
    offset: int
    size: int
    steps: Tuple[LocationStep, ...] = ()

    def __init__(
        self,
        base_param: Optional[str] = None,
        offset: int = 0,
        size: int = 0,
        steps: Tuple[LocationStep, ...] = (),
        base_ref: Optional[LocationBaseRef] = None,
    ) -> None:
        normalized_base = base_ref
        if normalized_base is None:
            if base_param in {"stackframe", "__locbase__stackframe"}:
                normalized_base = LocationBaseRef.stack_frame()
            else:
                normalized_base = LocationBaseRef.parameter(base_param or "param")
        object.__setattr__(self, "base_ref", normalized_base)
        object.__setattr__(self, "offset", int(offset))
        object.__setattr__(self, "size", int(size))
        object.__setattr__(self, "steps", tuple(steps))

    @property
    def base_param(self) -> str:
        return self.base_ref.display_name()

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.base_ref.stable_key(),
            tuple(step.stable_key() for step in self.steps),
            int(self.offset),
            int(self.size),
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "base_ref": self.base_ref.to_dict(),
            "offset": int(self.offset),
            "size": int(self.size),
            "steps": [step.to_dict() for step in self.steps],
        }


@dataclass(frozen=True)
class PostStateValueRef:
    """Structured identity for a fully materialized final object-state value."""

    location: CanonicalLocation
    snapshot_ref: Optional["PostStateSnapshotRef"] = None
    source: str = "effect_summary"
    state_kind: str = "materialized_final_value"

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "post_state_value",
            self.location.stable_key(),
            self.snapshot_ref.stable_key() if self.snapshot_ref is not None else None,
            self.source,
            self.state_kind,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "post_state_value",
            "location": self.location.to_dict(),
            "snapshot_ref": self.snapshot_ref.to_dict() if self.snapshot_ref is not None else None,
            "source": self.source,
            "state_kind": self.state_kind,
        }


@dataclass(frozen=True)
class PostStateSnapshotRef:
    """Structured identity for a shared post-state memory snapshot."""

    scope: str = "function_return"
    source: str = "effect_summary"
    epoch: str = "post_effects"
    pcode_op_ref: Optional["PcodeOpRef"] = None

    @classmethod
    def function_return(cls) -> "PostStateSnapshotRef":
        return cls()

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "post_state_snapshot",
            self.scope,
            self.source,
            self.epoch,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "post_state_snapshot",
            "scope": self.scope,
            "source": self.source,
            "epoch": self.epoch,
            "pcode_op_ref": self.pcode_op_ref.to_dict() if self.pcode_op_ref is not None else None,
        }


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

    def stable_key(self) -> Tuple[Any, ...]:
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
        }


@dataclass(frozen=True)
class LoopVariableIdentityRef:
    """Object-derived identity for a synthetic loop placeholder variable."""

    role: str
    varnode_key: Tuple[Any, ...]
    binder_ordinal: int = 0

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return None

    def binder_key(self) -> Tuple[Any, ...]:
        return (
            "loop_variable_binder",
            self.role,
            int(self.binder_ordinal),
        )

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        if not self.varnode_key:
            return None
        return (
            "loop_variable_identity",
            self.role,
            int(self.binder_ordinal),
            self.varnode_key,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "loop_variable_identity",
            "role": self.role,
            "binder_ordinal": int(self.binder_ordinal),
            "varnode_key": self.varnode_key,
        }


@dataclass(frozen=True)
class _LoopVariableBindingContext:
    """Per-summary alpha-renaming context for loop placeholder variables."""

    stable_to_binder: Dict[Tuple[Any, ...], Tuple[Any, ...]]

    def semantic_key_for(self, ref: LoopVariableIdentityRef) -> Optional[Tuple[Any, ...]]:
        stable_key = ref.stable_key()
        if stable_key is None:
            return None
        binder_key = self.stable_to_binder.get(stable_key)
        if binder_key is None:
            return None
        return ("loop_bound_variable", binder_key)


@dataclass(frozen=True)
class PostStateReadRef:
    """Structured identity for a symbolic read from a shared post-state snapshot."""

    location: CanonicalLocation
    snapshot_ref: Optional[PostStateSnapshotRef] = None
    source: str = "effect_summary"
    state_kind: str = "symbolic_post_state_read"

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "post_state_read",
            self.location.stable_key(),
            self.snapshot_ref.stable_key() if self.snapshot_ref is not None else None,
            self.source,
            self.state_kind,
        )

    def with_location(self, location: CanonicalLocation) -> "PostStateReadRef":
        return PostStateReadRef(
            location=location,
            snapshot_ref=self.snapshot_ref,
            source=self.source,
            state_kind=self.state_kind,
        )

    def with_snapshot(self, snapshot_ref: Optional[PostStateSnapshotRef]) -> "PostStateReadRef":
        return PostStateReadRef(
            location=self.location,
            snapshot_ref=snapshot_ref,
            source=self.source,
            state_kind=self.state_kind,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "post_state_read",
            "location": self.location.to_dict(),
            "snapshot_ref": self.snapshot_ref.to_dict() if self.snapshot_ref is not None else None,
            "source": self.source,
            "state_kind": self.state_kind,
        }


@dataclass(frozen=True)
class DeferredCallRef:
    """Structured identity for a deferred call site."""

    caller_program_id: Optional[int] = None
    caller_entry_offset: Optional[int] = None
    pcode_op_ref: Optional[PcodeOpRef] = None
    target_ref: Optional[CallTargetRef] = None
    sequence: Optional[int] = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "target_ref", coerce_call_target_ref(self.target_ref))

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "deferred_call_site",
            self.caller_program_id,
            self.caller_entry_offset,
            self.pcode_op_ref.stable_key() if self.pcode_op_ref is not None else None,
            self.target_ref.stable_key() if self.target_ref is not None else None,
            self.sequence,
        )

    def display_name(self) -> str:
        target_name = self.target_ref.display_name() if self.target_ref is not None else "unknown"
        if self.pcode_op_ref is not None and self.pcode_op_ref.address_offset is not None:
            return f"{target_name}@0x{int(self.pcode_op_ref.address_offset):x}"
        return target_name

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "deferred_call_site",
            "caller_program_id": self.caller_program_id,
            "caller_entry_offset": self.caller_entry_offset,
            "pcode_op_ref": self.pcode_op_ref.to_dict() if self.pcode_op_ref is not None else None,
            "target_ref": self.target_ref.to_dict() if self.target_ref is not None else None,
            "sequence": self.sequence,
            "display_name": self.display_name(),
        }


@dataclass(frozen=True)
class ObservedMemoryReadRef:
    """Structured provenance for an observed LOAD-derived memory read."""

    order_key: Optional[int] = None
    location: Optional[CanonicalLocation] = None
    snapshot_ref: Optional[PostStateSnapshotRef] = None
    pcode_op_ref: Optional[PcodeOpRef] = None
    source: str = "ghidra_load"

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "observed_memory_read",
            None if self.order_key is None else int(self.order_key),
            self.location.stable_key() if self.location is not None else None,
            self.snapshot_ref.stable_key() if self.snapshot_ref is not None else None,
            self.pcode_op_ref.stable_key() if self.pcode_op_ref is not None else None,
            self.source,
        )

    def with_location(
        self,
        location: Optional[CanonicalLocation],
        *,
        snapshot_ref: Optional[PostStateSnapshotRef] = None,
    ) -> "ObservedMemoryReadRef":
        return ObservedMemoryReadRef(
            order_key=self.order_key,
            location=location,
            snapshot_ref=self.snapshot_ref if snapshot_ref is None else snapshot_ref,
            pcode_op_ref=self.pcode_op_ref,
            source=self.source,
        )

    def with_snapshot(
        self,
        snapshot_ref: Optional[PostStateSnapshotRef],
    ) -> "ObservedMemoryReadRef":
        return ObservedMemoryReadRef(
            order_key=self.order_key,
            location=self.location,
            snapshot_ref=snapshot_ref,
            pcode_op_ref=self.pcode_op_ref,
            source=self.source,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "observed_memory_read",
            "order_key": self.order_key,
            "location": self.location.to_dict() if self.location is not None else None,
            "snapshot_ref": self.snapshot_ref.to_dict() if self.snapshot_ref is not None else None,
            "pcode_op_ref": self.pcode_op_ref.to_dict() if self.pcode_op_ref is not None else None,
            "source": self.source,
        }


def _loop_object_key(value: Any) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return ("none",)
    if isinstance(value, bool):
        return ("bool", bool(value))
    if isinstance(value, int):
        return ("int", int(value))
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, tuple):
        item_keys = tuple(_loop_object_key(item) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("tuple", item_keys)
    if isinstance(value, list):
        item_keys = tuple(_loop_object_key(item) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("list", item_keys)
    if isinstance(value, dict):
        items = []
        for key, item in value.items():
            key_key = _loop_object_key(key)
            item_key = _loop_object_key(item)
            if key_key is None or item_key is None:
                return None
            items.append((key_key, item_key))
        items.sort()
        return ("dict", tuple(items))
    structural_key = getattr(value, "structural_key", None)
    if callable(structural_key):
        try:
            return ("structural", structural_key())
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is None:
            return None
        return ("stable", key)
    return None


def _loop_variable_binding_context_from_values(
    *values: Any,
) -> Optional[_LoopVariableBindingContext]:
    stable_to_binder: Dict[Tuple[Any, ...], Tuple[Any, ...]] = {}
    binder_to_stable: Dict[Tuple[Any, ...], Tuple[Any, ...]] = {}
    seen: set[int] = set()

    def visit(item: Any) -> bool:
        if item is None:
            return True
        item_id = id(item)
        if item_id in seen:
            return True
        seen.add(item_id)

        ref = item if isinstance(item, LoopVariableIdentityRef) else getattr(item, "runtime_ref", None)
        if isinstance(ref, LoopVariableIdentityRef):
            stable_key = ref.stable_key()
            binder_key = ref.binder_key()
            if stable_key is None:
                return False
            existing_stable = binder_to_stable.get(binder_key)
            if existing_stable is not None and existing_stable != stable_key:
                return False
            existing_binder = stable_to_binder.get(stable_key)
            if existing_binder is not None and existing_binder != binder_key:
                return False
            binder_to_stable[binder_key] = stable_key
            stable_to_binder[stable_key] = binder_key

        expr_type = getattr(getattr(item, "expr_type", None), "name", None)
        if expr_type == "PHI":
            for cond, branch_value in getattr(item, "value", None) or ():
                if cond is not None and not visit(cond):
                    return False
                if not visit(branch_value):
                    return False
            return True

        condition_expr = getattr(item, "expression", None)
        if condition_expr is not None and not visit(condition_expr):
            return False

        for operand in getattr(item, "operands", None) or ():
            if not visit(operand):
                return False

        if isinstance(item, dict):
            for key, dict_value in item.items():
                if not visit(key) or not visit(dict_value):
                    return False
        elif isinstance(item, (tuple, list)):
            for child in item:
                if not visit(child):
                    return False
        return True

    for value in values:
        if not visit(value):
            return None
    return _LoopVariableBindingContext(stable_to_binder=stable_to_binder)


def _loop_object_semantic_key(
    value: Any,
    loop_variable_context: Optional[_LoopVariableBindingContext] = None,
) -> Optional[Tuple[Any, ...]]:
    """Semantic key for proof-oriented loop comparison.

    This intentionally differs from ``_loop_object_key`` for objects whose
    stable identity contains Ghidra ownership metadata.  The key is still fully
    object-centric: it walks expression/runtime objects and never depends on
    rendered strings.
    """

    if value is None:
        return ("none",)
    if isinstance(value, bool):
        return ("bool", bool(value))
    if isinstance(value, int):
        return ("int", int(value))
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, tuple):
        item_keys = tuple(_loop_object_semantic_key(item, loop_variable_context) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("tuple", item_keys)
    if isinstance(value, list):
        item_keys = tuple(_loop_object_semantic_key(item, loop_variable_context) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("list", item_keys)
    if isinstance(value, dict):
        items = []
        for key, item in value.items():
            key_key = _loop_object_semantic_key(key, loop_variable_context)
            item_key = _loop_object_semantic_key(item, loop_variable_context)
            if key_key is None or item_key is None:
                return None
            items.append((key_key, item_key))
        items.sort()
        return ("dict", tuple(items))

    if isinstance(value, LoopVariableIdentityRef):
        if loop_variable_context is None:
            return None
        return loop_variable_context.semantic_key_for(value)

    expr_key = _loop_expression_semantic_key(value, loop_variable_context)
    if expr_key is not None:
        return ("expression", expr_key)

    semantic_key = getattr(value, "semantic_key", None)
    if callable(semantic_key):
        try:
            key = semantic_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is not None:
            return ("semantic", key)
        if isinstance(value, LocationBaseRef):
            return None

    storage_identity_key = getattr(value, "storage_identity_key", None)
    if callable(storage_identity_key):
        try:
            key = storage_identity_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is None:
            return None
        return ("storage_identity", key)

    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is None:
            return None
        return ("stable", key)
    return None


def _loop_expression_semantic_key(
    value: Any,
    loop_variable_context: Optional[_LoopVariableBindingContext] = None,
) -> Optional[Tuple[Any, ...]]:
    expr_type = getattr(value, "expr_type", None)
    expr_type_name = getattr(expr_type, "name", None)
    if expr_type_name is None:
        return None

    size = int(getattr(value, "size", 0) or 0)
    if expr_type_name == "CONSTANT":
        try:
            return ("const", int(getattr(value, "value")), size)
        except (TypeError, ValueError):
            return None
    if expr_type_name == "PARAMETER":
        index = getattr(value, "value", None)
        try:
            if index is not None and int(index) >= 0:
                return ("parameter", int(index), size)
        except (TypeError, ValueError):
            pass
        storage = getattr(value, "storage_info", None)
        storage_key = _loop_object_semantic_key(storage, loop_variable_context) if storage is not None else None
        if storage is not None:
            if storage_key is None:
                return None
            return ("parameter_storage", size, storage_key)
        return None
    if expr_type_name == "VARIABLE":
        storage = getattr(value, "storage_info", None)
        storage_key = _loop_object_semantic_key(storage, loop_variable_context) if storage is not None else None
        if storage is not None:
            if storage_key is None:
                return None
            return ("variable_storage", size, storage_key)
        runtime_ref = getattr(value, "runtime_ref", None)
        runtime_key = _loop_object_semantic_key(runtime_ref, loop_variable_context) if runtime_ref is not None else None
        if runtime_ref is not None:
            if runtime_key is None:
                return None
            return ("variable_runtime", size, runtime_key)
        return None
    if expr_type_name in {"UNARY_OP", "BINARY_OP", "INTRINSIC", "CALL"}:
        operand_keys = tuple(
            _loop_object_semantic_key(operand, loop_variable_context)
            for operand in (getattr(value, "operands", None) or ())
        )
        if any(operand_key is None for operand_key in operand_keys):
            return None
        return (
            expr_type_name.lower(),
            getattr(value, "operator", None) or getattr(value, "name", None) or "",
            None if getattr(value, "opcode", None) is None else int(getattr(value, "opcode")),
            size,
            operand_keys,
        )
    if expr_type_name == "MEMORY":
        operands = getattr(value, "operands", None) or ()
        if not operands:
            return None
        address_key = _loop_object_semantic_key(operands[0], loop_variable_context)
        runtime_key = _loop_object_semantic_key(getattr(value, "runtime_ref", None), loop_variable_context)
        if address_key is None:
            return None
        return ("memory", size, address_key, runtime_key)
    if expr_type_name == "PHI":
        branches = []
        for condition, branch_value in getattr(value, "value", None) or ():
            if condition is None:
                condition_key = ("none",)
            else:
                condition_expr = getattr(condition, "expression", None)
                condition_key = (
                    "condition",
                    _loop_object_semantic_key(condition_expr, loop_variable_context),
                    bool(getattr(condition, "negated", False)),
                )
                if condition_key[1] is None:
                    return None
            value_key = _loop_object_semantic_key(branch_value, loop_variable_context)
            if value_key is None:
                return None
            branches.append((condition_key, value_key))
        return ("phi", size, tuple(branches))
    if expr_type_name == "UNKNOWN":
        runtime_key = _loop_object_semantic_key(getattr(value, "runtime_ref", None), loop_variable_context)
        if runtime_key is not None:
            return ("unknown", size, runtime_key)
        return None
    return None


def _loop_object_to_dict(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, tuple):
        return [_loop_object_to_dict(item) for item in value]
    if isinstance(value, list):
        return [_loop_object_to_dict(item) for item in value]
    if isinstance(value, dict):
        return {str(key): _loop_object_to_dict(item) for key, item in value.items()}
    to_dict = getattr(value, "to_dict", None)
    if callable(to_dict):
        try:
            return to_dict()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return {
                "type": f"{type(value).__module__}.{type(value).__qualname__}",
                "unserializable": True,
            }
    return {
        "type": f"{type(value).__module__}.{type(value).__qualname__}",
        "unkeyable": True,
    }


@dataclass(frozen=True)
class LoopBodyEffectRef:
    """Object-centric descriptor for one loop-body effect or guard."""

    kind: str
    source: str = "loop_body"
    scope: str = "loop"
    address_space: Any = None
    location: Any = None
    value_expr: Any = None
    guard_constraints: Tuple[Any, ...] = ()
    path_condition_sets: Tuple[Tuple[Any, ...], ...] = ()
    guard_paths_incomplete: bool = False
    target_ref: Any = None
    order_key: Optional[int] = None
    keyable: bool = True
    unkeyable_reason: Optional[str] = None

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        if not self.keyable:
            return None
        if self.guard_paths_incomplete:
            return None
        if (
            self.kind == "memory_write"
            and self.source == "pcode_scan"
            and self.scope == "loop"
            and (self.address_space is None or self.location is None or self.value_expr is None)
        ):
            return None
        address_space_key = _loop_object_key(self.address_space)
        location_key = _loop_object_key(self.location)
        value_key = _loop_object_key(self.value_expr)
        guard_keys = tuple(_loop_object_key(guard) for guard in self.guard_constraints)
        path_keys = tuple(
            tuple(_loop_object_key(condition) for condition in path_conditions)
            for path_conditions in self.path_condition_sets
        )
        target_key = _loop_object_key(self.target_ref)
        if (
            address_space_key is None
            or location_key is None
            or value_key is None
            or target_key is None
            or any(guard_key is None for guard_key in guard_keys)
            or any(any(condition_key is None for condition_key in path_key) for path_key in path_keys)
        ):
            return None
        return (
            "loop_body_effect",
            self.kind,
            self.source,
            self.scope,
            address_space_key,
            location_key,
            value_key,
            guard_keys,
            path_keys,
            bool(self.guard_paths_incomplete),
            target_key,
            None if self.order_key is None else int(self.order_key),
            bool(self.keyable),
        )

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        if not self.keyable or self.guard_paths_incomplete:
            return None
        address_space_key = _loop_object_semantic_key(self.address_space)
        location_key = _loop_object_semantic_key(self.location)
        value_key = _loop_object_semantic_key(self.value_expr)
        guard_keys = tuple(_loop_object_semantic_key(guard) for guard in self.guard_constraints)
        path_keys = tuple(
            tuple(_loop_object_semantic_key(condition) for condition in path_conditions)
            for path_conditions in self.path_condition_sets
        )
        target_key = _loop_object_semantic_key(self.target_ref)
        if (
            address_space_key is None
            or location_key is None
            or value_key is None
            or target_key is None
            or any(guard_key is None for guard_key in guard_keys)
            or any(any(condition_key is None for condition_key in path_key) for path_key in path_keys)
        ):
            return None
        return (
            "loop_body_effect",
            self.kind,
            self.source,
            self.scope,
            address_space_key,
            location_key,
            value_key,
            guard_keys,
            path_keys,
            bool(self.guard_paths_incomplete),
            target_key,
            None if self.order_key is None else int(self.order_key),
            bool(self.keyable),
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "loop_body_effect",
            "effect_kind": self.kind,
            "source": self.source,
            "scope": self.scope,
            "address_space": _loop_object_to_dict(self.address_space),
            "location": _loop_object_to_dict(self.location),
            "value_expr": _loop_object_to_dict(self.value_expr),
            "guard_constraints": [
                _loop_object_to_dict(guard)
                for guard in self.guard_constraints
            ],
            "path_condition_sets": [
                [
                    _loop_object_to_dict(condition)
                    for condition in path_conditions
                ]
                for path_conditions in self.path_condition_sets
            ],
            "guard_paths_incomplete": bool(self.guard_paths_incomplete),
            "target_ref": _loop_object_to_dict(self.target_ref),
            "order_key": self.order_key,
            "keyable": bool(self.keyable),
            "unkeyable_reason": self.unkeyable_reason,
        }


@dataclass(frozen=True)
class LoopSideEffectProfileRef:
    """Object-centric side-effect profile for a loop summary."""

    profile: str = "pure"
    memory_reads: bool = False
    memory_writes: bool = False
    calls: bool = False
    escapes: bool = False
    conditional_guards: bool = False
    context_memory_writes: bool = False
    context_calls: bool = False
    context_escapes: bool = False
    context_conditional_guards: bool = False
    effect_count: int = 0
    guard_count: int = 0
    effect_descriptors: Tuple[LoopBodyEffectRef, ...] = ()
    context_descriptors: Tuple[LoopBodyEffectRef, ...] = ()

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        effect_keys = tuple(effect.stable_key() for effect in self.effect_descriptors)
        context_effect_keys = tuple(effect.stable_key() for effect in self.context_descriptors)
        if any(effect_key is None for effect_key in effect_keys):
            return None
        if any(effect_key is None for effect_key in context_effect_keys):
            return None
        return (
            "loop_side_effect_profile",
            self.profile,
            bool(self.memory_reads),
            bool(self.memory_writes),
            bool(self.calls),
            bool(self.escapes),
            bool(self.conditional_guards),
            bool(self.context_memory_writes),
            bool(self.context_calls),
            bool(self.context_escapes),
            bool(self.context_conditional_guards),
            int(self.effect_count),
            int(self.guard_count),
            effect_keys,
            context_effect_keys,
        )

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        effect_keys = tuple(effect.semantic_key() for effect in self.effect_descriptors)
        context_effect_keys = tuple(effect.semantic_key() for effect in self.context_descriptors)
        if any(effect_key is None for effect_key in effect_keys):
            return None
        if any(effect_key is None for effect_key in context_effect_keys):
            return None
        return (
            "loop_side_effect_profile",
            self.profile,
            bool(self.memory_reads),
            bool(self.memory_writes),
            bool(self.calls),
            bool(self.escapes),
            bool(self.conditional_guards),
            bool(self.context_memory_writes),
            bool(self.context_calls),
            bool(self.context_escapes),
            bool(self.context_conditional_guards),
            int(self.effect_count),
            int(self.guard_count),
            effect_keys,
            context_effect_keys,
        )

    def requires_effect_proof(self) -> bool:
        profile = (self.profile or "").lower()
        effect_descriptors = tuple(self.effect_descriptors or ())
        context_descriptors = tuple(self.context_descriptors or ())

        def _descriptor_requires_effect_proof(effect: LoopBodyEffectRef) -> bool:
            return getattr(effect, "kind", None) != "conditional_guard"

        if profile not in {"pure", "pure_memory_read", "pure_conditional"}:
            return True
        return bool(
            self.memory_writes
            or self.calls
            or self.escapes
            or self.context_memory_writes
            or self.context_calls
            or self.context_escapes
            or any(_descriptor_requires_effect_proof(effect) for effect in effect_descriptors)
            or any(_descriptor_requires_effect_proof(effect) for effect in context_descriptors)
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "loop_side_effect_profile",
            "profile": self.profile,
            "memory_reads": bool(self.memory_reads),
            "memory_writes": bool(self.memory_writes),
            "calls": bool(self.calls),
            "escapes": bool(self.escapes),
            "conditional_guards": bool(self.conditional_guards),
            "context_memory_writes": bool(self.context_memory_writes),
            "context_calls": bool(self.context_calls),
            "context_escapes": bool(self.context_escapes),
            "context_conditional_guards": bool(self.context_conditional_guards),
            "effect_count": int(self.effect_count),
            "guard_count": int(self.guard_count),
            "effect_descriptors": [
                effect.to_dict()
                for effect in self.effect_descriptors
            ],
            "context_descriptors": [
                effect.to_dict()
                for effect in self.context_descriptors
            ],
        }


@dataclass(frozen=True)
class LoopTermDescriptorRef:
    """Object-centric descriptor for the per-iteration term of a loop summary."""

    kind: str
    reduction_kind: str = "sum"
    location_base_ref: Optional[LocationBaseRef] = None
    start_offset: int = 0
    stride: int = 0
    element_size: int = 0
    result_size: int = 0
    residue_cases: Tuple[Tuple[int, int, int, int], ...] = ()
    residue_bias_terms: Tuple[Tuple[int, int, Any], ...] = ()
    lane_terms: Tuple[Tuple[int, int], ...] = ()

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        residue_bias_keys = tuple(
            (
                int(modulus),
                int(residue),
                _loop_object_key(bias_expr),
            )
            for modulus, residue, bias_expr in self.residue_bias_terms
        )
        if any(key[2] is None for key in residue_bias_keys):
            return None
        return (
            "loop_term_descriptor",
            self.kind,
            self.reduction_kind,
            self.location_base_ref.stable_key() if self.location_base_ref is not None else None,
            int(self.start_offset),
            int(self.stride),
            int(self.element_size),
            max(1, int(self.result_size or 0)),
            tuple(
                (
                    int(modulus),
                    int(residue),
                    int(coeff),
                    int(bias),
                )
                for modulus, residue, coeff, bias in self.residue_cases
            ),
            residue_bias_keys,
            tuple((int(offset), max(1, int(size or 0))) for offset, size in self.lane_terms),
        )

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        location_key = self.location_base_ref.semantic_key() if self.location_base_ref is not None else None
        if self.location_base_ref is not None and location_key is None:
            return None
        residue_bias_keys = tuple(
            (
                int(modulus),
                int(residue),
                _loop_object_semantic_key(bias_expr),
            )
            for modulus, residue, bias_expr in self.residue_bias_terms
        )
        if any(key[2] is None for key in residue_bias_keys):
            return None
        return (
            "loop_term_descriptor",
            self.kind,
            self.reduction_kind,
            location_key,
            int(self.start_offset),
            int(self.stride),
            int(self.element_size),
            max(1, int(self.result_size or 0)),
            tuple(
                (
                    int(modulus),
                    int(residue),
                    int(coeff),
                    int(bias),
                )
                for modulus, residue, coeff, bias in self.residue_cases
            ),
            residue_bias_keys,
            tuple((int(offset), max(1, int(size or 0))) for offset, size in self.lane_terms),
        )

    def to_dict(self) -> Dict[str, Any]:
        result: Dict[str, Any] = {
            "kind": "loop_term_descriptor",
            "term_kind": self.kind,
            "reduction_kind": self.reduction_kind,
            "start_offset": int(self.start_offset),
            "stride": int(self.stride),
            "element_size": int(self.element_size),
            "result_size": max(1, int(self.result_size or 0)),
            "residue_cases": [
                {
                    "modulus": int(modulus),
                    "residue": int(residue),
                    "coeff": int(coeff),
                    "bias": int(bias),
                }
                for modulus, residue, coeff, bias in self.residue_cases
            ],
            "residue_bias_terms": [
                {
                    "modulus": int(modulus),
                    "residue": int(residue),
                    "bias_expr": getattr(bias_expr, "to_dict", lambda: repr(bias_expr))(),
                }
                for modulus, residue, bias_expr in self.residue_bias_terms
            ],
            "lane_terms": [
                {
                    "byte_offset": int(offset),
                    "access_size": max(1, int(size or 0)),
                }
                for offset, size in self.lane_terms
            ],
        }
        if self.location_base_ref is not None:
            result["location_base_ref"] = self.location_base_ref.to_dict()
        return result


@dataclass(frozen=True)
class LoopCaseRef:
    """Path-sensitive loop-body case used by Method-B loop summaries."""

    path_conditions: Tuple[Any, ...] = ()
    body_effect: Any = None
    term_expr: Any = None
    case_kind: str = "body_term"
    source: str = "recurrence_summary"

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        path_keys = tuple(_loop_object_key(condition) for condition in self.path_conditions)
        body_effect_key = _loop_object_key(self.body_effect)
        term_key = _loop_object_key(self.term_expr)
        if (
            any(path_key is None for path_key in path_keys)
            or body_effect_key is None
            or term_key is None
        ):
            return None
        return (
            "loop_case",
            self.case_kind,
            path_keys,
            body_effect_key,
            term_key,
            self.source,
        )

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        path_keys = tuple(_loop_object_semantic_key(condition) for condition in self.path_conditions)
        body_effect_key = _loop_object_semantic_key(self.body_effect)
        term_key = _loop_object_semantic_key(self.term_expr)
        if (
            any(path_key is None for path_key in path_keys)
            or body_effect_key is None
            or term_key is None
        ):
            return None
        return (
            "loop_case",
            self.case_kind,
            path_keys,
            body_effect_key,
            term_key,
            self.source,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "loop_case",
            "case_kind": self.case_kind,
            "path_conditions": [
                _loop_object_to_dict(condition)
                for condition in self.path_conditions
            ],
            "body_effect": _loop_object_to_dict(self.body_effect),
            "term_expr": _loop_object_to_dict(self.term_expr),
            "source": self.source,
        }


def _bias_key(value: int, result_size: int) -> Tuple[int, int]:
    bits = max(1, int(result_size or 0)) * 8
    return bits, int(value) % (1 << bits)


def _normalize_storage_identity_key(value: Optional[Tuple[Any, ...]]) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return None
    return tuple(value)


def _count_parameter_semantic_identity(
    *,
    count_parameter_index: Optional[int],
    count_parameter_storage_identity_key: Optional[Tuple[Any, ...]],
) -> Optional[Tuple[Any, ...]]:
    identities = _count_parameter_semantic_identities(
        count_parameter_index=count_parameter_index,
        count_parameter_storage_identity_key=count_parameter_storage_identity_key,
    )
    return identities[0] if identities else None


def _count_parameter_semantic_identities(
    *,
    count_parameter_index: Optional[int],
    count_parameter_storage_identity_key: Optional[Tuple[Any, ...]],
) -> Tuple[Tuple[Any, ...], ...]:
    identities = []
    storage_key = _normalize_storage_identity_key(count_parameter_storage_identity_key)
    if storage_key is not None:
        identities.append(("parameter_storage", storage_key))
    if count_parameter_index is not None:
        try:
            index = int(count_parameter_index)
        except (TypeError, ValueError):
            index = -1
        if index >= 0:
            identities.append(("parameter", index))
    return tuple(identities)


@dataclass(frozen=True)
class LoopSummaryRef:
    """Unified semantic loop summary shared by all recurrence summaries.

    ``witnesses`` are evidence keyed by the original count/limit surface, not
    proof obligations by themselves. A witness may describe a count value outside
    ``guard_constraints``; consumers must check guard reachability before using
    witnesses to prove equivalence.
    """

    start_expr: Any
    limit_expr: Any
    step_expr: Any
    term_descriptor: LoopTermDescriptorRef
    seed_terms: Tuple[Any, ...] = ()
    seed_term_count: Optional[int] = None
    witnesses: Tuple[Any, ...] = ()
    side_effect_profile: LoopSideEffectProfileRef = LoopSideEffectProfileRef()
    guard_constraints: Tuple[Any, ...] = ()
    cases: Tuple[LoopCaseRef, ...] = ()
    loop_var_unit: str = "element_index"
    source: str = "recurrence_summary"
    constant_bias: int = 0

    def __post_init__(self) -> None:
        result_size = int(getattr(self.term_descriptor, "result_size", 0) or 0)
        if result_size <= 0 and int(self.constant_bias) != 0:
            raise ValueError("LoopSummaryRef.constant_bias requires a positive term result_size")
        result_size = max(1, result_size)
        object.__setattr__(self, "constant_bias", _bias_key(int(self.constant_bias), result_size)[1])

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        start_key = _loop_object_key(self.start_expr)
        limit_key = _loop_object_key(self.limit_expr)
        step_key = _loop_object_key(self.step_expr)
        seed_terms = tuple(self.seed_terms or ())
        seed_term_count = getattr(self, "seed_term_count", None)
        if seed_terms:
            seed_keys = tuple(_loop_object_key(term) for term in seed_terms)
        elif seed_term_count is not None:
            if int(seed_term_count) < 0:
                return None
            seed_keys = (("seed_term_count", int(seed_term_count)),)
        else:
            seed_keys = ()
        witness_keys = tuple(_loop_object_key(witness) for witness in self.witnesses)
        guard_keys = tuple(_loop_object_key(guard) for guard in self.guard_constraints)
        case_keys = tuple(case.stable_key() for case in self.cases)
        term_descriptor_key = self.term_descriptor.stable_key()
        side_effect_key = self.side_effect_profile.stable_key()
        if (
            start_key is None
            or limit_key is None
            or step_key is None
            or term_descriptor_key is None
            or any(seed_key is None for seed_key in seed_keys)
            or any(witness_key is None for witness_key in witness_keys)
            or any(guard_key is None for guard_key in guard_keys)
            or any(case_key is None for case_key in case_keys)
            or side_effect_key is None
        ):
            return None
        return (
            "loop_summary",
            self.loop_var_unit,
            start_key,
            limit_key,
            step_key,
            term_descriptor_key,
            seed_keys,
            witness_keys,
            side_effect_key,
            guard_keys,
            case_keys,
            self.source,
            _bias_key(int(self.constant_bias), getattr(self.term_descriptor, "result_size", 0)),
        )

    def requires_effect_proof(self) -> bool:
        return self.side_effect_profile.requires_effect_proof()

    def requires_path_proof(self) -> bool:
        counted_update_cases = []
        for case in tuple(self.cases or ()):
            if getattr(case, "source", None) == "counted_loop_update_case":
                counted_update_cases.append(case)
                continue
            if getattr(case, "body_effect", None) is not None:
                return True
            if getattr(case, "term_expr", None) is not None:
                return True
        if counted_update_cases and not self._counted_loop_update_cases_are_descriptor_covered(counted_update_cases):
            return True
        return False

    def _counted_loop_update_cases_are_descriptor_covered(self, cases: Sequence[Any]) -> bool:
        if not cases:
            return True
        if getattr(self.term_descriptor, "kind", None) != "affine_residue":
            return False
        residue_cases = tuple(getattr(self.term_descriptor, "residue_cases", ()) or ())
        if not residue_cases:
            return False
        for case in cases:
            if getattr(case, "case_kind", None) != "accumulator_delta":
                return False
            body_effect = getattr(case, "body_effect", None)
            if getattr(body_effect, "kind", None) != "accumulator_update":
                return False
            if getattr(case, "term_expr", None) is None:
                return False
        residue_keys = []
        for residue_case in residue_cases:
            if len(residue_case) < 4:
                return False
            try:
                modulus = int(residue_case[0])
                residue = int(residue_case[1])
            except (TypeError, ValueError):
                return False
            if modulus <= 0 or residue < 0 or residue >= modulus:
                return False
            residue_keys.append((modulus, residue))
        if len(residue_keys) == 1:
            return residue_keys[0] == (1, 0) and len(cases) == 1
        moduli = {modulus for modulus, _residue in residue_keys}
        if len(moduli) != 1:
            return False
        modulus = moduli.pop()
        if len(cases) != modulus:
            return False
        return {residue for _modulus, residue in residue_keys} == set(range(modulus))

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        if self.requires_effect_proof() or self.requires_path_proof():
            return None
        return loop_summary_method_b_key(self)

    def pairwise_exact_key(self) -> Optional[Tuple[Any, ...]]:
        if self.requires_effect_proof() or self.requires_path_proof():
            return None
        return self.stable_key()

    def pairwise_semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return self.semantic_key()

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "loop_summary",
            "loop_var_unit": self.loop_var_unit,
            "start_expr": _loop_object_to_dict(self.start_expr),
            "limit_expr": _loop_object_to_dict(self.limit_expr),
            "step_expr": _loop_object_to_dict(self.step_expr),
            "term_descriptor": self.term_descriptor.to_dict(),
            "seed_terms": [_loop_object_to_dict(term) for term in self.seed_terms],
            "seed_term_count": None if self.seed_term_count is None else int(self.seed_term_count),
            "witnesses": [_loop_object_to_dict(witness) for witness in self.witnesses],
            "side_effect_profile": self.side_effect_profile.to_dict(),
            "guard_constraints": [_loop_object_to_dict(guard) for guard in self.guard_constraints],
            "cases": [case.to_dict() for case in self.cases],
            "source": self.source,
            "constant_bias": int(self.constant_bias),
        }


@dataclass(frozen=True)
class LoopSummaryComparisonResult:
    """Tri-state result for the future Method-B loop-summary comparator."""

    status: str
    reason: Optional[str] = None

    def __post_init__(self) -> None:
        if self.status not in {"equivalent", "different", "incompatible", "unknown"}:
            raise ValueError(f"Unsupported loop summary comparison status: {self.status}")

    def is_equivalent(self) -> Optional[bool]:
        if self.status == "equivalent":
            return True
        if self.status == "different":
            return False
        return None

    def blocks_shortcut(self) -> bool:
        return self.status in {"different", "incompatible"}

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "loop_summary_comparison_result",
            "status": self.status,
            "reason": self.reason,
        }


def compare_loop_summaries(
    left: Optional[LoopSummaryRef],
    right: Optional[LoopSummaryRef],
) -> LoopSummaryComparisonResult:
    """Compare Method-B loop summaries.

    The full seed/tail, guard-aware, and SMT-backed proof is intentionally still
    non-decisive. We can, however, safely reject summaries whose loop-body
    effect surfaces are already structurally different.
    """

    if left is None or right is None:
        return LoopSummaryComparisonResult("unknown", "missing loop summary")
    left_method_b_key = loop_summary_method_b_key(left)
    right_method_b_key = loop_summary_method_b_key(right)
    if left_method_b_key is not None and right_method_b_key is not None:
        if left_method_b_key == right_method_b_key:
            return LoopSummaryComparisonResult("equivalent", "loop summaries match by semantic seed compensation")
    left_profile = getattr(left, "side_effect_profile", None)
    right_profile = getattr(right, "side_effect_profile", None)
    if left_profile is not None and right_profile is not None:
        left_shape = (
            left_profile.profile,
            bool(left_profile.memory_reads),
            bool(left_profile.memory_writes),
            bool(left_profile.calls),
            bool(left_profile.escapes),
            bool(left_profile.conditional_guards),
            int(left_profile.effect_count),
            int(left_profile.guard_count),
        )
        right_shape = (
            right_profile.profile,
            bool(right_profile.memory_reads),
            bool(right_profile.memory_writes),
            bool(right_profile.calls),
            bool(right_profile.escapes),
            bool(right_profile.conditional_guards),
            int(right_profile.effect_count),
            int(right_profile.guard_count),
        )
        if left_shape != right_shape:
            return LoopSummaryComparisonResult("incompatible", "loop side-effect profiles differ")
        left_effect_key = left_profile.stable_key()
        right_effect_key = right_profile.stable_key()
        if left_effect_key is not None and right_effect_key is not None and left_effect_key != right_effect_key:
            return LoopSummaryComparisonResult("incompatible", "loop body effects differ")
    left_cases = tuple(getattr(left, "cases", ()) or ())
    right_cases = tuple(getattr(right, "cases", ()) or ())
    if len(left_cases) != len(right_cases):
        return LoopSummaryComparisonResult("incompatible", "loop case counts differ")
    if left_cases or right_cases:
        left_case_keys = tuple(case.stable_key() for case in left_cases)
        right_case_keys = tuple(case.stable_key() for case in right_cases)
        if any(case_key is None for case_key in left_case_keys + right_case_keys):
            return LoopSummaryComparisonResult("incompatible", "loop cases are unkeyable")
        if left_case_keys != right_case_keys:
            return LoopSummaryComparisonResult("incompatible", "loop cases differ")
    left_semantic_key = left.pairwise_semantic_key()
    right_semantic_key = right.pairwise_semantic_key()
    if left_semantic_key is not None and right_semantic_key is not None:
        if left_semantic_key == right_semantic_key:
            return LoopSummaryComparisonResult("equivalent", "loop summaries match by semantic key")
    return LoopSummaryComparisonResult("unknown", "loop summary comparator is not implemented")


def loop_summary_method_b_key(summary: Optional[LoopSummaryRef]) -> Optional[Tuple[Any, ...]]:
    """Canonical Method-B key for pure loop summaries.

    The key normalizes a suffix loop whose ``seed_terms`` exactly cover the
    omitted prefix back to the earliest represented start.  This is not a broad
    semantic proof; it is a deterministic object-centric identity for the
    current pure, path-insensitive loop-summary subset.
    """

    if summary is None:
        return None
    seed_terms_for_binding = tuple(getattr(summary, "seed_terms", ()) or ())
    binding_context = _loop_variable_binding_context_from_values(
        getattr(summary, "start_expr", None),
        getattr(summary, "limit_expr", None),
        getattr(summary, "step_expr", None),
        seed_terms_for_binding,
        tuple(getattr(summary, "witnesses", ()) or ()),
        tuple(getattr(summary, "guard_constraints", ()) or ()),
    )
    if binding_context is None:
        return None
    requires_effect_proof = getattr(summary, "requires_effect_proof", None)
    if callable(requires_effect_proof) and requires_effect_proof():
        return None
    requires_path_proof = getattr(summary, "requires_path_proof", None)
    if callable(requires_path_proof) and requires_path_proof():
        return None
    start_value = _loop_summary_int_constant(getattr(summary, "start_expr", None))
    step_value = _loop_summary_int_constant(getattr(summary, "step_expr", None))
    if start_value is None or step_value is None or step_value <= 0:
        return None

    term_descriptor = getattr(summary, "term_descriptor", None)
    if term_descriptor is None:
        return None
    if (
        getattr(term_descriptor, "kind", None) == "memory_load"
        and getattr(term_descriptor, "location_base_ref", None) is None
    ):
        return None
    term_key = _loop_summary_term_descriptor_semantic_key(
        term_descriptor,
        loop_var_unit=getattr(summary, "loop_var_unit", None),
    )
    if getattr(term_descriptor, "kind", None) == "memory_load" and term_key is None:
        return None
    loop_var_unit_key = getattr(summary, "loop_var_unit", None)
    if term_key is not None and len(term_key) > 0 and term_key[0] == "scalar_memory_term_sequence":
        loop_var_unit_key = "scalar_element_index"
    limit_key = _loop_summary_limit_semantic_key(
        getattr(summary, "limit_expr", None),
        binding_context,
    )
    side_effect_key = summary.side_effect_profile.semantic_key()
    if limit_key is None or side_effect_key is None:
        return None

    canonical_start = int(start_value)
    remaining_seed_terms = list(getattr(summary, "seed_terms", ()) or ())
    if not remaining_seed_terms:
        seed_term_count = getattr(summary, "seed_term_count", None)
        if (
            seed_term_count is not None
            and int(seed_term_count) >= 0
            and int(seed_term_count) == int(canonical_start)
            and int(step_value) == 1
        ):
            canonical_start = int(canonical_start) - int(seed_term_count)
            remaining_seed_terms = []

    while remaining_seed_terms:
        previous_index = canonical_start - int(step_value)
        expected_term = _loop_summary_term_at_index(summary, previous_index)
        if expected_term is None:
            break
        expected_key = _loop_object_semantic_key(expected_term, binding_context)
        actual_key = _loop_object_semantic_key(remaining_seed_terms[-1], binding_context)
        if expected_key is None or actual_key is None or expected_key != actual_key:
            break
        remaining_seed_terms.pop()
        canonical_start = previous_index

    seed_keys = tuple(_loop_object_semantic_key(term, binding_context) for term in remaining_seed_terms)
    if any(seed_key is None for seed_key in seed_keys):
        return None
    return (
        "loop_summary_method_b",
        loop_var_unit_key,
        int(canonical_start),
        limit_key,
        int(step_value),
        term_key,
        seed_keys,
        _bias_key(
            int(getattr(summary, "constant_bias", 0) or 0),
            getattr(term_descriptor, "result_size", 0),
        ),
        side_effect_key,
    )


def loop_summary_method_b_key_at_result_size(
    summary: Optional[LoopSummaryRef],
    result_size: int,
) -> Optional[Tuple[Any, ...]]:
    """Projected Method-B key for comparing a wider sum at a narrower width."""

    if summary is None:
        return None
    try:
        target_result_size = max(1, int(result_size))
    except (TypeError, ValueError):
        return None
    term_descriptor = getattr(summary, "term_descriptor", None)
    if term_descriptor is None:
        return None
    original_result_size = max(1, int(getattr(term_descriptor, "result_size", 0) or 0))
    if target_result_size > original_result_size:
        return None
    if target_result_size == original_result_size:
        return loop_summary_method_b_key(summary)
    if getattr(term_descriptor, "kind", None) != "memory_load":
        return None
    if getattr(term_descriptor, "reduction_kind", "sum") not in {"sum", "memory_sum"}:
        return None

    lane_terms = tuple(getattr(term_descriptor, "lane_terms", ()) or ())
    if lane_terms:
        try:
            if any(max(1, int(size or 0)) != target_result_size for _offset, size in lane_terms):
                return None
        except (TypeError, ValueError):
            return None
    else:
        try:
            element_size = max(1, int(getattr(term_descriptor, "element_size", 0) or 0))
        except (TypeError, ValueError):
            return None
        if element_size != target_result_size:
            return None

    projected_descriptor = replace(term_descriptor, result_size=target_result_size)
    projected_summary = replace(
        summary,
        term_descriptor=projected_descriptor,
        constant_bias=_bias_key(int(getattr(summary, "constant_bias", 0) or 0), target_result_size)[1],
    )
    return loop_summary_method_b_key(projected_summary)


def _loop_summary_int_constant(value: Any) -> Optional[int]:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return int(value)
    expr_type = getattr(value, "expr_type", None)
    if getattr(expr_type, "name", None) == "CONSTANT":
        try:
            return int(getattr(value, "value"))
        except (TypeError, ValueError):
            return None
    return None


def _loop_summary_limit_semantic_key(
    value: Any,
    loop_variable_context: Optional[_LoopVariableBindingContext] = None,
) -> Optional[Tuple[Any, ...]]:
    expr_type = getattr(value, "expr_type", None)
    if getattr(expr_type, "name", None) == "PARAMETER":
        index = getattr(value, "value", None)
        try:
            if index is not None and int(index) >= 0:
                return ("loop_limit_parameter", int(index))
        except (TypeError, ValueError):
            pass
        storage = getattr(value, "storage_info", None)
        storage_key = _loop_object_semantic_key(storage, loop_variable_context) if storage is not None else None
        if storage is not None:
            if storage_key is None:
                return None
            return ("loop_limit_parameter_storage", storage_key)
        return None
    return _loop_object_semantic_key(value, loop_variable_context)


def _loop_summary_term_descriptor_semantic_key(
    term_descriptor: LoopTermDescriptorRef,
    *,
    loop_var_unit: Optional[str] = None,
) -> Optional[Tuple[Any, ...]]:
    scalar_key = _loop_summary_scalar_memory_term_key(
        term_descriptor,
        loop_var_unit=loop_var_unit,
    )
    if scalar_key is not None:
        return scalar_key
    return term_descriptor.semantic_key()


def _loop_summary_scalar_memory_term_key(
    term_descriptor: LoopTermDescriptorRef,
    *,
    loop_var_unit: Optional[str] = None,
) -> Optional[Tuple[Any, ...]]:
    if getattr(term_descriptor, "kind", None) != "memory_load":
        return None
    location_base_ref = getattr(term_descriptor, "location_base_ref", None)
    if location_base_ref is None:
        return None
    reduction_kind = getattr(term_descriptor, "reduction_kind", "sum")
    result_size = max(1, int(getattr(term_descriptor, "result_size", 0) or 0))
    start_offset = int(getattr(term_descriptor, "start_offset", 0) or 0)
    lane_terms = tuple(getattr(term_descriptor, "lane_terms", ()) or ())
    if not lane_terms:
        element_size = int(getattr(term_descriptor, "element_size", 0) or 0)
        stride = int(getattr(term_descriptor, "stride", 0) or 0)
        if element_size <= 0 or stride <= 0 or element_size != result_size:
            return None
        location_key = location_base_ref.semantic_key()
        if location_key is None:
            return None
        return (
            "scalar_memory_term_sequence",
            reduction_kind,
            location_key,
            start_offset,
            stride,
            element_size,
            result_size,
        )
    if loop_var_unit != "scalar_element_index":
        return None

    normalized_lanes = sorted(
        (int(offset), max(1, int(size or 0)))
        for offset, size in lane_terms
    )
    access_sizes = {size for _, size in normalized_lanes}
    if len(access_sizes) != 1:
        return None
    access_size = next(iter(access_sizes))
    if access_size != result_size:
        return None
    offsets = [offset for offset, _ in normalized_lanes]
    if len(set(offsets)) != len(offsets):
        return None
    if len(offsets) == 1:
        scalar_stride = access_size
    else:
        deltas = [right - left for left, right in zip(offsets, offsets[1:])]
        if any(delta <= 0 for delta in deltas):
            return None
        scalar_stride = deltas[0]
        if any(delta != scalar_stride for delta in deltas):
            return None
    if scalar_stride != access_size:
        return None
    descriptor_stride = int(getattr(term_descriptor, "stride", 0) or 0)
    if descriptor_stride != scalar_stride * len(offsets):
        return None
    expected_offsets = [offsets[0] + index * scalar_stride for index in range(len(offsets))]
    if offsets != expected_offsets:
        return None
    location_key = location_base_ref.semantic_key()
    if location_key is None:
        return None
    return (
        "scalar_memory_term_sequence",
        reduction_kind,
        location_key,
        start_offset + offsets[0],
        scalar_stride,
        access_size,
        result_size,
    )


def _loop_summary_term_at_index(summary: LoopSummaryRef, index: int) -> Optional[Any]:
    term_descriptor = getattr(summary, "term_descriptor", None)
    if term_descriptor is None:
        return None
    if getattr(term_descriptor, "kind", None) != "memory_load":
        return None
    scalar_key = _loop_summary_scalar_memory_term_key(
        term_descriptor,
        loop_var_unit=getattr(summary, "loop_var_unit", None),
    )
    if scalar_key is not None:
        start_offset = int(scalar_key[3])
        stride = int(scalar_key[4])
        access_size = int(scalar_key[5])
        return ReadonlyReductionTermRef(
            byte_offset=start_offset + int(index) * stride,
            access_size=access_size,
        )
    element_size = int(getattr(term_descriptor, "element_size", 0) or 0)
    stride = int(getattr(term_descriptor, "stride", 0) or 0)
    if element_size <= 0 or stride <= 0:
        return None
    start_offset = int(getattr(term_descriptor, "start_offset", 0) or 0)
    return ReadonlyReductionTermRef(
        byte_offset=start_offset + int(index) * stride,
        access_size=element_size,
    )


@dataclass(frozen=True)
class ReadonlyReductionTermRef:
    """Object-centric description of one scalar term in a memory reduction."""

    byte_offset: int
    access_size: int

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "readonly_reduction_term",
            int(self.byte_offset),
            max(1, int(self.access_size or 0)),
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "readonly_reduction_term",
            "byte_offset": int(self.byte_offset),
            "access_size": max(1, int(self.access_size or 0)),
        }


@dataclass(frozen=True)
class ReadonlyReductionWitness:
    """Concrete count-parameter witness for a readonly reduction."""

    exact_count: int
    terms: Tuple[ReadonlyReductionTermRef, ...]
    count_semantics: str = "count_parameter"

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "readonly_reduction_witness",
            self.count_semantics,
            int(self.exact_count),
            tuple(term.stable_key() for term in self.terms),
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "readonly_reduction_witness",
            "count_semantics": self.count_semantics,
            "exact_count": int(self.exact_count),
            "terms": [term.to_dict() for term in self.terms],
        }


@dataclass(frozen=True)
class ReductionAccumulatorProof:
    """Object-centric proof that a loop accumulator is a readonly reduction.

    This is intentionally richer than the runtime summaries it can lower to.
    Runtime refs describe what can be compared today; this proof records the
    Ghidra/SMT-relevant evidence used to justify that lowering, including PHI
    roles, CFG anchors, seed terms, lane terms, exact return witnesses, and
    constant bias.  Consumers should preserve this object when future lowerings
    need more detail than ``READONLY_SUM(base, count)`` can currently express.
    """

    reduction_kind: str
    pointer_base_ref: LocationBaseRef
    count_parameter_name: str
    count_parameter_index: Optional[int]
    limit_expr: Any
    result_size: int
    stride: int
    element_size: int
    count_parameter_storage_identity_key: Optional[Tuple[Any, ...]] = None
    start_offset: int = 0
    start_index: int = 0
    index_step: int = 1
    index_scale: int = 0
    signed_counter: bool = True
    seed_terms: Tuple[ReadonlyReductionTermRef, ...] = ()
    seed_term_count: Optional[int] = None
    lane_terms: Tuple[Tuple[int, int], ...] = ()
    loop_body_witnesses: Tuple[ReadonlyReductionWitness, ...] = ()
    exact_return_witnesses: Tuple[ReadonlyReductionWitness, ...] = ()
    guard_constraints: Tuple[Any, ...] = ()
    side_effect_profile: LoopSideEffectProfileRef = LoopSideEffectProfileRef(
        profile="pure_memory_read",
        memory_reads=True,
    )
    constant_bias: int = 0
    induction_phi_ref: Optional[PcodeOpRef] = None
    accumulator_phi_ref: Optional[PcodeOpRef] = None
    update_op_ref: Optional[PcodeOpRef] = None
    load_op_refs: Tuple[PcodeOpRef, ...] = ()
    return_op_refs: Tuple[PcodeOpRef, ...] = ()
    return_value_op_refs: Tuple[PcodeOpRef, ...] = ()
    entry_block_ref: Optional[PcodeBlockRef] = None
    backedge_block_ref: Optional[PcodeBlockRef] = None
    return_region_value_proven: bool = False
    source: str = "recurrence_summary"

    def __post_init__(self) -> None:
        if int(self.stride) <= 0:
            raise ValueError("ReductionAccumulatorProof requires a positive stride")
        if int(self.element_size) <= 0:
            raise ValueError("ReductionAccumulatorProof requires a positive element_size")
        if int(self.result_size) <= 0:
            raise ValueError("ReductionAccumulatorProof requires a positive result_size")
        if int(self.index_step) <= 0:
            raise ValueError("ReductionAccumulatorProof requires a positive index_step")
        if self.seed_term_count is not None and int(self.seed_term_count) < 0:
            raise ValueError("ReductionAccumulatorProof requires a non-negative seed_term_count")
        if self.count_parameter_storage_identity_key is not None:
            object.__setattr__(
                self,
                "count_parameter_storage_identity_key",
                _normalize_storage_identity_key(self.count_parameter_storage_identity_key),
            )
        object.__setattr__(self, "constant_bias", _bias_key(int(self.constant_bias), int(self.result_size))[1])
        lane_terms = tuple(
            sorted((int(offset), max(1, int(size or 0))) for offset, size in (self.lane_terms or ()))
        )
        if lane_terms:
            start_offset = int(self.start_offset)
            min_offset = min(offset for offset, _size in lane_terms)
            if start_offset != 0 and min_offset == start_offset:
                lane_terms = tuple((offset - start_offset, size) for offset, size in lane_terms)
            object.__setattr__(self, "lane_terms", lane_terms)
        return_op_refs = tuple(
            sorted(
                (ref for ref in (self.return_op_refs or ()) if isinstance(ref, PcodeOpRef)),
                key=lambda ref: repr(ref.stable_key()),
            )
        )
        object.__setattr__(self, "return_op_refs", return_op_refs)
        return_value_op_refs = tuple(
            sorted(
                (ref for ref in (self.return_value_op_refs or ()) if isinstance(ref, PcodeOpRef)),
                key=lambda ref: repr(ref.stable_key()),
            )
        )
        object.__setattr__(self, "return_value_op_refs", return_value_op_refs)

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        limit_key = _loop_object_key(self.limit_expr)
        guard_keys = tuple(_loop_object_key(guard) for guard in self.guard_constraints)
        side_effect_key = self.side_effect_profile.stable_key()
        if limit_key is None or side_effect_key is None or any(key is None for key in guard_keys):
            return None
        return (
            "reduction_accumulator_proof",
            self.reduction_kind,
            self.pointer_base_ref.stable_key(),
            self.count_parameter_name,
            None if self.count_parameter_index is None else int(self.count_parameter_index),
            self.count_parameter_storage_identity_key,
            limit_key,
            max(1, int(self.result_size)),
            int(self.stride),
            int(self.element_size),
            int(self.start_offset),
            int(self.start_index),
            int(self.index_step),
            int(self.index_scale or self.stride),
            bool(self.signed_counter),
            tuple(term.stable_key() for term in self.seed_terms)
            if tuple(self.seed_terms or ())
            else (
                (("seed_term_count", int(self.seed_term_count)),)
                if self.seed_term_count is not None
                else ()
            ),
            tuple((int(offset), max(1, int(size or 0))) for offset, size in self.lane_terms),
            tuple(witness.stable_key() for witness in self.loop_body_witnesses),
            tuple(witness.stable_key() for witness in self.exact_return_witnesses),
            guard_keys,
            side_effect_key,
            int(self.constant_bias),
            self.induction_phi_ref.stable_key() if self.induction_phi_ref is not None else None,
            self.accumulator_phi_ref.stable_key() if self.accumulator_phi_ref is not None else None,
            self.update_op_ref.stable_key() if self.update_op_ref is not None else None,
            tuple(ref.stable_key() for ref in self.load_op_refs),
            tuple(ref.stable_key() for ref in self.return_op_refs),
            tuple(ref.stable_key() for ref in self.return_value_op_refs),
            self.entry_block_ref.stable_key() if self.entry_block_ref is not None else None,
            self.backedge_block_ref.stable_key() if self.backedge_block_ref is not None else None,
            bool(self.return_region_value_proven),
            self.source,
        )

    def readonly_term_sequence_specificity_score(self) -> int:
        """Relative precision of the proven readonly term-sequence contract.

        A higher score means the proof carries more object-level information
        about non-zero starts, explicit seed terms, or scalarized vector lanes.
        This is used only as an ordering tiebreaker between overlapping
        readonly summaries that target the same base/count reduction surface.
        """

        try:
            start_index = max(0, int(self.start_index))
        except (TypeError, ValueError):
            start_index = 0
        seed_terms = tuple(self.seed_terms or ())
        seed_term_count = self.seed_term_count
        try:
            implicit_seed_count = 0 if seed_term_count is None else max(0, int(seed_term_count))
        except (TypeError, ValueError):
            implicit_seed_count = 0
        lane_terms = tuple(self.lane_terms or ())
        return int(start_index) + len(seed_terms) + int(implicit_seed_count) + len(lane_terms)

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return self.readonly_term_sequence_contract_key()

    def readonly_term_sequence_contract_key(
        self,
        *,
        result_size: Optional[int] = None,
    ) -> Optional[Tuple[Any, ...]]:
        """Semantic contract for a readonly scalar memory-term reduction.

        The contract is deliberately proof-centric rather than surface-centric:
        it is derived from the accumulator proof's base object, limit object,
        scalarized term geometry, explicit seed terms, and side-effect profile.
        A path-sensitive ``LoopSummaryRef`` may still be comparable through this
        contract when the accumulator proof proves the readonly term sequence;
        loops with writes, calls, escapes, or conditional side effects remain
        proof-required and do not get a shortcut here.
        """

        target_result_size = self._readonly_contract_result_size(result_size)
        if target_result_size is None:
            return None
        if self.side_effect_profile.requires_effect_proof():
            return None
        pointer_key = self.pointer_base_ref.semantic_key()
        count_identity = self.count_parameter_semantic_identity()
        if count_identity is None:
            return None
        limit_key = _loop_summary_limit_semantic_key(self.limit_expr)
        if limit_key is None:
            count_storage_key = _normalize_storage_identity_key(
                self.count_parameter_storage_identity_key
            )
            if count_storage_key is None:
                return None
            limit_key = ("loop_limit_count_storage_identity", count_storage_key)
        side_effect_key = self.side_effect_profile.semantic_key()
        if pointer_key is None or limit_key is None or side_effect_key is None:
            return None
        geometry = self._readonly_contract_scalar_geometry(target_result_size)
        if geometry is None:
            return None
        term_start_offset, scalar_stride = geometry
        seed_terms = self._readonly_contract_seed_terms(
            target_result_size=target_result_size,
            term_start_offset=term_start_offset,
            scalar_stride=scalar_stride,
        )
        if seed_terms is None:
            return None
        canonical_start, remaining_seed_terms = self._readonly_contract_canonical_start_and_seed_terms(
            seed_terms=seed_terms,
            target_result_size=target_result_size,
            term_start_offset=term_start_offset,
            scalar_stride=scalar_stride,
        )
        seed_keys = tuple(term.stable_key() for term in remaining_seed_terms)
        return (
            "readonly_reduction_term_sequence_contract",
            self.reduction_kind,
            pointer_key,
            count_identity,
            limit_key,
            max(1, int(target_result_size)),
            int(canonical_start),
            int(self.index_step),
            int(term_start_offset),
            int(scalar_stride),
            bool(self.signed_counter),
            seed_keys,
            _bias_key(int(self.constant_bias), target_result_size),
            side_effect_key,
        )

    def _readonly_contract_result_size(self, result_size: Optional[int]) -> Optional[int]:
        proof_result_size = max(1, int(self.result_size or 0))
        try:
            target_result_size = proof_result_size if result_size is None else max(1, int(result_size))
        except (TypeError, ValueError):
            return None
        if target_result_size > proof_result_size:
            return None
        if target_result_size < proof_result_size and self.reduction_kind not in {"sum", "memory_sum"}:
            return None
        return target_result_size

    def count_parameter_semantic_identity(self) -> Optional[Tuple[Any, ...]]:
        return _count_parameter_semantic_identity(
            count_parameter_index=self.count_parameter_index,
            count_parameter_storage_identity_key=self.count_parameter_storage_identity_key,
        )

    def count_parameter_semantic_identities(self) -> Tuple[Tuple[Any, ...], ...]:
        return _count_parameter_semantic_identities(
            count_parameter_index=self.count_parameter_index,
            count_parameter_storage_identity_key=self.count_parameter_storage_identity_key,
        )

    def _readonly_contract_scalar_geometry(
        self,
        target_result_size: int,
    ) -> Optional[Tuple[int, int]]:
        target_result_size = max(1, int(target_result_size))
        start_index = int(self.start_index)
        if start_index < 0:
            return None
        index_scale = int(self.index_scale or self.stride)
        if index_scale <= 0:
            return None
        lane_terms = tuple(self.lane_terms or ())
        if lane_terms:
            scalar_lanes = self._readonly_contract_scalar_lane_terms(target_result_size)
            if not scalar_lanes:
                return None
            first_lane_offset = int(scalar_lanes[0][0])
            scalar_stride = target_result_size
            term_start_offset = int(self.start_offset) + first_lane_offset - start_index * scalar_stride
            return term_start_offset, scalar_stride
        if max(1, int(self.element_size or 0)) != target_result_size:
            return None
        term_start_offset = int(self.start_offset) - start_index * index_scale
        return term_start_offset, index_scale

    def _readonly_contract_scalar_lane_terms(
        self,
        target_result_size: int,
    ) -> Tuple[Tuple[int, int], ...]:
        target_result_size = max(1, int(target_result_size))
        normalized_lanes = tuple(
            sorted((int(offset), max(1, int(size or 0))) for offset, size in (self.lane_terms or ()))
        )
        if not normalized_lanes:
            return ()
        if int(self.index_step) != 1:
            return ()
        if not all(size == target_result_size for _offset, size in normalized_lanes):
            return ()
        offsets = [offset for offset, _size in normalized_lanes]
        expected_offsets = [offsets[0] + index * target_result_size for index in range(len(offsets))]
        if offsets != expected_offsets:
            return ()
        if int(self.index_scale or self.stride) != target_result_size * len(offsets):
            return ()
        return normalized_lanes

    def _readonly_contract_seed_terms(
        self,
        *,
        target_result_size: int,
        term_start_offset: int,
        scalar_stride: int,
    ) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        target_result_size = max(1, int(target_result_size))
        explicit_seed_terms = tuple(self.seed_terms or ())
        if explicit_seed_terms:
            normalized_terms = []
            for term in explicit_seed_terms:
                if max(1, int(getattr(term, "access_size", 0) or 0)) != target_result_size:
                    return None
                normalized_terms.append(
                    ReadonlyReductionTermRef(
                        byte_offset=int(getattr(term, "byte_offset")),
                        access_size=target_result_size,
                    )
                )
            return tuple(normalized_terms)
        seed_term_count = self.seed_term_count
        if seed_term_count is None:
            return ()
        try:
            seed_count = int(seed_term_count)
        except (TypeError, ValueError):
            return None
        if seed_count < 0 or seed_count > int(self.start_index):
            return None
        return tuple(
            ReadonlyReductionTermRef(
                byte_offset=int(term_start_offset) + index * int(scalar_stride),
                access_size=target_result_size,
            )
            for index in range(seed_count)
        )

    def _readonly_contract_canonical_start_and_seed_terms(
        self,
        *,
        seed_terms: Tuple[ReadonlyReductionTermRef, ...],
        target_result_size: int,
        term_start_offset: int,
        scalar_stride: int,
    ) -> Tuple[int, Tuple[ReadonlyReductionTermRef, ...]]:
        canonical_start = int(self.start_index)
        index_step = int(self.index_step)
        remaining_seed_terms = sorted(
            tuple(seed_terms or ()),
            key=lambda term: (int(term.byte_offset), int(term.access_size)),
        )
        while remaining_seed_terms:
            previous_index = canonical_start - index_step
            if previous_index < 0:
                break
            expected_term = ReadonlyReductionTermRef(
                byte_offset=int(term_start_offset) + previous_index * int(scalar_stride),
                access_size=max(1, int(target_result_size)),
            )
            expected_key = expected_term.stable_key()
            matching_index = None
            for index, term in enumerate(remaining_seed_terms):
                if term.stable_key() == expected_key:
                    matching_index = index
                    break
            if matching_index is None:
                break
            remaining_seed_terms.pop(matching_index)
            canonical_start = previous_index
        return canonical_start, tuple(remaining_seed_terms)

    def trip_count_for_count_value(self, count_value: int) -> Optional[int]:
        if int(count_value) <= 0:
            return None
        start_index = int(self.start_index)
        index_step = int(self.index_step)
        if index_step <= 0:
            return None
        if int(count_value) <= start_index:
            return 0
        distance = int(count_value) - start_index
        return (distance + index_step - 1) // index_step

    def loop_body_terms_for_count_value(self, count_value: int) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        trip_count = self.trip_count_for_count_value(count_value)
        if trip_count is None:
            return None
        access_size = max(1, int(self.result_size))
        lane_terms = self._scalar_lane_terms(require_witness_prefix=False)
        if lane_terms:
            lane_count = len(lane_terms)
            if lane_count <= 0:
                return None
            stride = int(self.index_scale or self.stride)
            return tuple(
                ReadonlyReductionTermRef(
                    byte_offset=int(self.start_offset)
                    + (scalar_index // lane_count) * stride
                    + lane_terms[scalar_index % lane_count][0],
                    access_size=access_size,
                )
                for scalar_index in range(trip_count)
            )
        if int(self.element_size) != access_size:
            return None
        return tuple(
            ReadonlyReductionTermRef(
                byte_offset=int(self.start_offset) + index * int(self.stride),
                access_size=access_size,
            )
            for index in range(trip_count)
        )

    def full_terms_for_count_value(self, count_value: int) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        seed_terms = self.seed_terms_for_count_value(count_value)
        if seed_terms is None:
            return None
        if not tuple(self.seed_terms or ()) and self.seed_term_count is not None:
            try:
                if int(count_value) >= int(self.start_index):
                    full_seed_terms = self._materialized_seed_prefix_terms()
                    if full_seed_terms is None:
                        return None
                    seed_terms = full_seed_terms
            except (TypeError, ValueError):
                return None
        loop_terms = self.loop_body_terms_for_count_value(count_value)
        if loop_terms is None:
            return self._prefix_terms_from_exact_return_witnesses(count_value)
        return tuple(seed_terms) + tuple(loop_terms)

    def _prefix_terms_from_exact_return_witnesses(
        self,
        count_value: int,
    ) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        """Materialize a small prefix from stronger exact-return evidence.

        Some optimized shapes prove the broad READONLY_SUM contract but only
        retain exact return witnesses for selected counts, e.g. count=1,3,4.
        If a larger exact witness is a contiguous scalar prefix, every smaller
        prefix is also object-centrically determined.  This deliberately refuses
        non-prefix or non-scalar witnesses; it does not infer arbitrary loop
        behavior from a sparse sample.
        """

        try:
            count_value = int(count_value)
        except (TypeError, ValueError):
            return None
        if count_value <= 0:
            return None
        access_size = max(1, int(self.result_size))
        expected_prefix = tuple(
            ReadonlyReductionTermRef(
                byte_offset=index * access_size,
                access_size=access_size,
            )
            for index in range(count_value)
        )
        expected_prefix_key = tuple(term.stable_key() for term in expected_prefix)
        for witness in sorted(
            tuple(self.exact_return_witnesses or ()),
            key=lambda item: int(getattr(item, "exact_count", 0) or 0),
        ):
            exact_count = int(getattr(witness, "exact_count", 0) or 0)
            terms = tuple(getattr(witness, "terms", ()) or ())
            if exact_count < count_value or len(terms) < exact_count:
                continue
            expected_witness = tuple(
                ReadonlyReductionTermRef(
                    byte_offset=index * access_size,
                    access_size=access_size,
                )
                for index in range(exact_count)
            )
            if tuple(term.stable_key() for term in terms[:exact_count]) != tuple(
                term.stable_key() for term in expected_witness
            ):
                continue
            candidate = tuple(terms[:count_value])
            if tuple(term.stable_key() for term in candidate) == expected_prefix_key:
                return candidate
        return None

    def seed_terms_for_count_value(self, count_value: int) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        seed_terms = tuple(self.seed_terms or ())
        if not seed_terms:
            seed_term_count = self.seed_term_count
            if seed_term_count is not None:
                count_value = int(count_value)
                if count_value <= 0:
                    return None
                start_index = int(self.start_index)
                if start_index <= 0:
                    return ()
                seed_term_count_value = int(seed_term_count)
                if seed_term_count_value < 0 or seed_term_count_value > start_index:
                    return None
                index_scale = int(self.index_scale or self.stride)
                if index_scale <= 0:
                    return None
                if count_value >= start_index:
                    return ()
                term_start_offset = int(self.start_offset) - int(self.start_index) * index_scale
                selected_count = min(int(count_value), seed_term_count_value)
                return tuple(
                    ReadonlyReductionTermRef(
                        byte_offset=int(term_start_offset) + index * index_scale,
                        access_size=max(1, int(self.result_size)),
                    )
                    for index in range(selected_count)
                )
            return ()
        count_value = int(count_value)
        if count_value <= 0:
            return None
        start_index = int(self.start_index)
        if count_value >= start_index:
            return seed_terms
        index_scale = int(self.index_scale or self.stride)
        if index_scale <= 0:
            return None
        term_start_offset = int(self.start_offset) - int(self.start_index) * index_scale
        selected = []
        for term in seed_terms:
            byte_offset = int(term.byte_offset)
            logical_delta = byte_offset - term_start_offset
            if logical_delta < 0 or logical_delta % index_scale != 0:
                return None
            logical_index = logical_delta // index_scale
            if logical_index < count_value:
                selected.append(term)
        return tuple(selected)

    def _materialized_seed_prefix_terms(self) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        seed_terms = tuple(self.seed_terms or ())
        if seed_terms:
            return seed_terms
        seed_term_count = self.seed_term_count
        if seed_term_count is None:
            return ()
        start_index = int(self.start_index)
        if start_index <= 0:
            return ()
        seed_term_count_value = int(seed_term_count)
        if seed_term_count_value < 0 or seed_term_count_value > start_index:
            return None
        index_scale = int(self.index_scale or self.stride)
        if index_scale <= 0:
            return None
        term_start_offset = int(self.start_offset) - int(self.start_index) * index_scale
        return tuple(
            ReadonlyReductionTermRef(
                byte_offset=int(term_start_offset) + index * index_scale,
                access_size=max(1, int(self.result_size)),
            )
            for index in range(seed_term_count_value)
        )

    def _readonly_lowering_failure_reason(self) -> Optional[str]:
        if self.side_effect_profile.requires_effect_proof():
            return "side_effects_not_representable"
        return None

    def _build_loop_summary_ref(
        self,
        *,
        loop_var_unit_override: Optional[str] = None,
        canonicalize_scalar_iteration: bool = False,
    ) -> Optional["LoopSummaryRef"]:
        if self._readonly_lowering_failure_reason() is not None:
            return None
        stride = int(self.stride)
        element_size = int(self.element_size)
        index_scale = int(self.index_scale or stride)
        if stride <= 0 or element_size <= 0 or index_scale <= 0:
            return None
        lane_terms = tuple(self.lane_terms or ())
        if canonicalize_scalar_iteration:
            scalar_lane_terms = self._scalar_lane_terms(require_witness_prefix=False)
            if scalar_lane_terms:
                access_size = max(1, int(self.result_size))
                stride = access_size
                element_size = access_size
                index_scale = access_size
                lane_terms = ()
                term_start_offset = int(self.start_offset) - int(self.start_index) * access_size
            else:
                term_start_offset = int(self.start_offset) - int(self.start_index) * index_scale
        else:
            term_start_offset = int(self.start_offset) - int(self.start_index) * index_scale
        return LoopSummaryRef(
            start_expr=_loop_int_expr(int(self.start_index), self.limit_expr),
            limit_expr=self.limit_expr,
            step_expr=_loop_int_expr(int(self.index_step), self.limit_expr),
            term_descriptor=LoopTermDescriptorRef(
                kind="memory_load",
                reduction_kind="sum",
                location_base_ref=self.pointer_base_ref,
                start_offset=term_start_offset,
                stride=index_scale,
                element_size=element_size,
                result_size=max(1, int(self.result_size)),
                lane_terms=lane_terms,
            ),
            seed_terms=tuple(self.seed_terms or ()),
            seed_term_count=None
            if self.seed_term_count is None
            else int(self.seed_term_count),
            witnesses=tuple(self.loop_body_witnesses or ()),
            side_effect_profile=self.side_effect_profile,
            guard_constraints=tuple(self.guard_constraints or ()),
            loop_var_unit=loop_var_unit_override or self.loop_var_unit(),
            source=self.source,
            constant_bias=int(self.constant_bias),
        )

    def lower_to_loop_summary_ref(self) -> Optional["LoopSummaryRef"]:
        return self._build_loop_summary_ref()

    def to_loop_summary_ref(self) -> Optional["LoopSummaryRef"]:
        return self.lower_to_loop_summary_ref()

    def _pairwise_loop_summary_ref(self) -> Optional["LoopSummaryRef"]:
        return self._build_loop_summary_ref(
            loop_var_unit_override=self._pairwise_loop_var_unit(),
            canonicalize_scalar_iteration=True,
        )

    def with_runtime_evidence(
        self,
        *,
        limit_expr: Any,
        result_size: int,
        loop_body_witnesses: Tuple[ReadonlyReductionWitness, ...],
        exact_return_witnesses: Tuple[ReadonlyReductionWitness, ...],
        guard_constraints: Tuple[Any, ...],
        signed_counter: bool,
    ) -> "ReductionAccumulatorProof":
        normalized_result_size = max(1, int(result_size or 0))
        lane_terms = tuple(self.lane_terms or ())
        if not lane_terms:
            lane_terms = self._infer_lane_terms_from_witnesses(
                access_size=normalized_result_size,
                witnesses=tuple(loop_body_witnesses or ()),
            )
        return replace(
            self,
            limit_expr=limit_expr,
            result_size=normalized_result_size,
            lane_terms=lane_terms,
            loop_body_witnesses=tuple(loop_body_witnesses or ()),
            exact_return_witnesses=tuple(exact_return_witnesses or ()),
            guard_constraints=tuple(guard_constraints or ()),
            signed_counter=bool(signed_counter),
        )._normalize_scalar_prefix_from_exact_witnesses()._complete_seed_prefix_from_exact_witnesses()

    def _normalize_scalar_prefix_from_exact_witnesses(self) -> "ReductionAccumulatorProof":
        access_size = max(1, int(self.result_size))
        current_start = max(0, int(self.start_index or 0))
        if (
            access_size <= 0
            or current_start <= 0
            or (
                int(self.stride) == access_size
                and int(self.element_size) == access_size
                and int(self.index_scale or self.stride) == access_size
                and int(self.start_offset) == 0
                and int(self.start_index) == 0
            )
        ):
            return self
        exact_witnesses = {
            int(witness.exact_count): tuple(witness.terms)
            for witness in self.exact_return_witnesses or ()
            if int(getattr(witness, "exact_count", 0) or 0) > 0
        }
        if not exact_witnesses:
            return self
        matching_counts = []
        for count_value, terms in exact_witnesses.items():
            expected_terms = tuple(
                ReadonlyReductionTermRef(
                    byte_offset=index * access_size,
                    access_size=access_size,
                )
                for index in range(count_value)
            )
            if tuple(term.stable_key() for term in terms) == tuple(
                term.stable_key() for term in expected_terms
            ):
                matching_counts.append(int(count_value))
        if not matching_counts:
            return self
        matching_counts = sorted(set(matching_counts))
        prefix_len = 0
        while (prefix_len + 1) in matching_counts:
            prefix_len += 1
        if prefix_len < max(1, current_start):
            return self
        if int(self.start_offset) != current_start * access_size:
            return self
        return replace(
            self,
            stride=access_size,
            element_size=access_size,
            start_offset=0,
            start_index=0,
            index_step=1,
            index_scale=access_size,
            seed_terms=(),
            seed_term_count=None,
            lane_terms=(),
        )

    def _infer_lane_terms_from_witnesses(
        self,
        *,
        access_size: int,
        witnesses: Tuple[ReadonlyReductionWitness, ...],
    ) -> Tuple[Tuple[int, int], ...]:
        stride = int(self.index_scale or self.stride)
        element_size = int(self.element_size)
        if (
            stride <= 0
            or access_size <= 0
            or stride % access_size != 0
            or element_size <= access_size
            or int(self.start_index) != 0
            or int(self.index_step) != 1
        ):
            return ()
        lane_count = stride // access_size
        if lane_count <= 1:
            return ()
        witnesses_by_count = {int(witness.exact_count): tuple(witness.terms) for witness in witnesses or ()}
        for count in range(1, lane_count + 1):
            terms = witnesses_by_count.get(count)
            expected = tuple(
                ReadonlyReductionTermRef(
                    byte_offset=int(self.start_offset) + index * access_size,
                    access_size=access_size,
                )
                for index in range(count)
            )
            if terms is None or tuple(term.stable_key() for term in terms) != tuple(
                term.stable_key() for term in expected
            ):
                return ()
        return tuple((index * access_size, access_size) for index in range(lane_count))

    def lower_to_readonly_reduction(self) -> Optional["ReadonlyReductionLowering"]:
        loop_summary = self.lower_to_loop_summary_ref()
        if loop_summary is None:
            return None
        readonly_ref = ReadonlyReductionRef(
            reduction_kind=self.reduction_kind,
            pointer_base_ref=self.pointer_base_ref,
            count_parameter_name=self.count_parameter_name,
            count_parameter_index=self.count_parameter_index,
            count_parameter_storage_identity_key=self.count_parameter_storage_identity_key,
            stride=int(self.stride),
            element_size=int(self.element_size),
            result_size=max(1, int(self.result_size)),
            start_offset=int(self.start_offset),
            signed_counter=bool(self.signed_counter),
            source=self.source,
            semantic_witnesses=tuple(self.loop_body_witnesses or ()),
            loop_summary=loop_summary,
            accumulator_proof=self,
            constant_bias=int(self.constant_bias),
        )
        return ReadonlyReductionLowering(
            proof=self,
            loop_summary=loop_summary,
            readonly_reduction=readonly_ref,
        )

    def lower_to_readonly_reduction_ref(self) -> Optional["ReadonlyReductionRef"]:
        lowering = self.lower_to_readonly_reduction()
        return lowering.readonly_reduction if lowering is not None else None

    def to_readonly_reduction_ref(self) -> Optional["ReadonlyReductionRef"]:
        return self.lower_to_readonly_reduction_ref()

    def loop_var_unit(self) -> str:
        return "scalar_element_index" if self._scalar_lane_terms(require_witness_prefix=True) else "element_index"

    def _pairwise_loop_var_unit(self) -> str:
        return "scalar_element_index" if self._scalar_lane_terms(require_witness_prefix=False) else self.loop_var_unit()

    def _scalar_lane_terms(
        self,
        *,
        require_witness_prefix: bool,
    ) -> Tuple[Tuple[int, int], ...]:
        normalized_lanes = tuple(
            sorted((int(offset), max(1, int(size or 0))) for offset, size in (self.lane_terms or ()))
        )
        if not normalized_lanes:
            return ()
        access_size = max(1, int(self.result_size))
        offsets = [offset for offset, _size in normalized_lanes]
        expected_offsets = [index * access_size for index in range(len(offsets))]
        if not all(size == access_size for _offset, size in normalized_lanes):
            return ()
        if offsets != expected_offsets:
            return ()
        if int(self.index_scale or self.stride) != access_size * len(offsets):
            return ()
        if int(self.index_step) != 1:
            return ()
        if require_witness_prefix:
            if int(self.start_index) != 0:
                return ()
            witnesses_by_count = {
                int(witness.exact_count): tuple(witness.terms)
                for witness in self.loop_body_witnesses or ()
            }
            for count in range(1, len(offsets)):
                terms = witnesses_by_count.get(count)
                expected = tuple(
                    ReadonlyReductionTermRef(
                        byte_offset=int(self.start_offset) + index * access_size,
                        access_size=access_size,
                    )
                    for index in range(count)
                )
                if terms is None or tuple(term.stable_key() for term in terms) != tuple(
                    term.stable_key() for term in expected
                ):
                    return ()
        return normalized_lanes

    def _complete_seed_prefix_from_exact_witnesses(self) -> "ReductionAccumulatorProof":
        if tuple(self.seed_terms or ()) or self.seed_term_count is not None:
            return self
        if int(self.start_index or 0) not in {0}:
            return self
        scalar_lane_terms = self._scalar_lane_terms(require_witness_prefix=False)
        if not scalar_lane_terms:
            return self
        access_size = max(1, int(self.result_size))
        first_body_offset = int(self.start_offset) + int(scalar_lane_terms[0][0])
        if first_body_offset <= 0 or first_body_offset % access_size != 0:
            return self
        candidate_start_index = first_body_offset // access_size
        if candidate_start_index <= 0:
            return self
        exact_witnesses = {
            int(witness.exact_count): tuple(witness.terms)
            for witness in self.exact_return_witnesses or ()
        }
        for count_value in range(1, candidate_start_index + 1):
            witness_terms = exact_witnesses.get(count_value)
            if witness_terms is None:
                return self
            expected_terms = tuple(
                ReadonlyReductionTermRef(
                    byte_offset=index * access_size,
                    access_size=access_size,
                )
                for index in range(count_value)
            )
            if tuple(term.stable_key() for term in witness_terms) != tuple(
                term.stable_key() for term in expected_terms
            ):
                return self
        seed_terms = tuple(
            ReadonlyReductionTermRef(
                byte_offset=index * access_size,
                access_size=access_size,
            )
            for index in range(candidate_start_index)
        )
        return replace(
            self,
            start_index=int(candidate_start_index),
            seed_terms=seed_terms,
            seed_term_count=None,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "reduction_accumulator_proof",
            "reduction_kind": self.reduction_kind,
            "pointer_base_ref": self.pointer_base_ref.to_dict(),
            "count_parameter_name": self.count_parameter_name,
            "count_parameter_index": self.count_parameter_index,
            "count_parameter_storage_identity_key": self.count_parameter_storage_identity_key,
            "result_size": max(1, int(self.result_size)),
            "stride": int(self.stride),
            "element_size": int(self.element_size),
            "start_offset": int(self.start_offset),
            "start_index": int(self.start_index),
            "index_step": int(self.index_step),
            "index_scale": int(self.index_scale or self.stride),
            "signed_counter": bool(self.signed_counter),
            "seed_terms": [term.to_dict() for term in self.seed_terms],
            "seed_term_count": None if self.seed_term_count is None else int(self.seed_term_count),
            "lane_terms": [
                {"byte_offset": int(offset), "access_size": max(1, int(size or 0))}
                for offset, size in self.lane_terms
            ],
            "loop_body_witnesses": [witness.to_dict() for witness in self.loop_body_witnesses],
            "exact_return_witnesses": [witness.to_dict() for witness in self.exact_return_witnesses],
            "guard_constraints": [_loop_object_to_dict(guard) for guard in self.guard_constraints],
            "side_effect_profile": self.side_effect_profile.to_dict(),
            "constant_bias": int(self.constant_bias),
            "induction_phi_ref": self.induction_phi_ref.to_dict() if self.induction_phi_ref is not None else None,
            "accumulator_phi_ref": self.accumulator_phi_ref.to_dict() if self.accumulator_phi_ref is not None else None,
            "update_op_ref": self.update_op_ref.to_dict() if self.update_op_ref is not None else None,
            "load_op_refs": [ref.to_dict() for ref in self.load_op_refs],
            "return_op_refs": [ref.to_dict() for ref in self.return_op_refs],
            "return_value_op_refs": [ref.to_dict() for ref in self.return_value_op_refs],
            "entry_block_ref": self.entry_block_ref.to_dict() if self.entry_block_ref is not None else None,
            "backedge_block_ref": self.backedge_block_ref.to_dict() if self.backedge_block_ref is not None else None,
            "return_region_value_proven": bool(self.return_region_value_proven),
            "source": self.source,
        }


def _loop_int_expr(value: int, like_expr: Any) -> Any:
    expression_cls = getattr(like_expr, "__class__", None)
    constant = getattr(expression_cls, "constant", None)
    if callable(constant):
        size = max(1, int(getattr(like_expr, "size", 0) or 4))
        return constant(int(value), size=size)
    return int(value)


@dataclass(frozen=True)
class ReadonlyReductionRef:
    """Structured identity for a readonly pointer-reduction summary."""

    reduction_kind: str
    pointer_base_ref: LocationBaseRef
    count_parameter_name: str
    count_parameter_index: Optional[int] = None
    count_parameter_storage_identity_key: Optional[Tuple[Any, ...]] = None
    stride: int = 0
    element_size: int = 0
    result_size: int = 0
    start_offset: int = 0
    signed_counter: bool = True
    source: str = "recurrence_summary"
    semantic_witnesses: Tuple[ReadonlyReductionWitness, ...] = ()
    loop_summary: Optional[LoopSummaryRef] = None
    accumulator_proof: Optional[ReductionAccumulatorProof] = None
    constant_bias: int = 0

    def __post_init__(self) -> None:
        result_size = max(1, int(self.result_size or 0))
        ref_bias = _bias_key(int(self.constant_bias), result_size)[1]
        loop_summary = self.loop_summary
        accumulator_proof = self.accumulator_proof
        if self.count_parameter_storage_identity_key is not None:
            object.__setattr__(
                self,
                "count_parameter_storage_identity_key",
                _normalize_storage_identity_key(self.count_parameter_storage_identity_key),
            )
        source_biases = []
        if loop_summary is not None:
            summary_result_size_raw = int(
                getattr(getattr(loop_summary, "term_descriptor", None), "result_size", 0) or 0
            )
            if summary_result_size_raw > 0 and summary_result_size_raw != result_size:
                raise ValueError("ReadonlyReductionRef.result_size must match loop_summary term result_size")
            if summary_result_size_raw <= 0 and int(getattr(loop_summary, "constant_bias", 0) or 0) != 0:
                raise ValueError("ReadonlyReductionRef cannot align biased loop_summary without term result_size")
            summary_result_size = result_size if summary_result_size_raw <= 0 else summary_result_size_raw
            summary_bias = _bias_key(
                int(getattr(loop_summary, "constant_bias", 0) or 0),
                summary_result_size,
            )[1]
            source_biases.append(("loop_summary.constant_bias", summary_bias))
        if accumulator_proof is not None:
            proof_result_size = max(1, int(getattr(accumulator_proof, "result_size", 0) or 0))
            if proof_result_size != result_size:
                raise ValueError("ReadonlyReductionRef.result_size must match accumulator_proof.result_size")
            proof_bias = _bias_key(
                int(getattr(accumulator_proof, "constant_bias", 0) or 0),
                proof_result_size,
            )[1]
            source_biases.append(("accumulator_proof.constant_bias", proof_bias))
        nonzero_source_biases = [bias for _name, bias in source_biases if bias != 0]
        if ref_bias == 0 and nonzero_source_biases:
            ref_bias = nonzero_source_biases[0]
        for name, source_bias in source_biases:
            if ref_bias != source_bias:
                raise ValueError(f"ReadonlyReductionRef.constant_bias must match {name}")
        object.__setattr__(self, "constant_bias", ref_bias)

    def stable_key(self) -> Tuple[Any, ...]:
        loop_summary_key = self.loop_summary.stable_key() if self.loop_summary is not None else None
        proof_key = self.accumulator_proof.stable_key() if self.accumulator_proof is not None else None
        return (
            "readonly_reduction",
            self.reduction_kind,
            self.pointer_base_ref.stable_key(),
            self.count_parameter_name,
            None if self.count_parameter_index is None else int(self.count_parameter_index),
            self.count_parameter_storage_identity_key,
            int(self.stride),
            int(self.element_size),
            int(self.result_size),
            int(self.start_offset),
            bool(self.signed_counter),
            self.source,
            loop_summary_key,
            proof_key,
            _bias_key(int(self.constant_bias), self.result_size),
        )

    def display_name(self) -> str:
        return (
            f"{self.reduction_kind}("
            f"{self.pointer_base_ref.display_name()},"
            f"{self.count_parameter_name},"
            f"stride={int(self.stride)},"
            f"elem={int(self.element_size)},"
            f"bias={int(self.constant_bias)})"
        )

    def readonly_term_sequence_contract_key(
        self,
        *,
        result_size: Optional[int] = None,
    ) -> Optional[Tuple[Any, ...]]:
        ref_result_size = max(1, int(self.result_size or 0))
        try:
            target_result_size = ref_result_size if result_size is None else max(1, int(result_size))
        except (TypeError, ValueError):
            return None
        if target_result_size > ref_result_size:
            return None
        if self.accumulator_proof is not None:
            proof_key_fn = getattr(self.accumulator_proof, "readonly_term_sequence_contract_key", None)
            if callable(proof_key_fn):
                try:
                    proof_key = proof_key_fn(result_size=target_result_size)
                except (AttributeError, TypeError, ValueError):
                    proof_key = None
                if proof_key is not None:
                    return proof_key
        if self.loop_summary is not None:
            if result_size is not None and target_result_size != ref_result_size:
                return loop_summary_method_b_key_at_result_size(
                    self.loop_summary,
                    target_result_size,
                )
            loop_key_fn = getattr(self.loop_summary, "pairwise_semantic_key", None)
            if callable(loop_key_fn):
                try:
                    loop_key = loop_key_fn()
                except (AttributeError, TypeError, ValueError):
                    loop_key = None
                if loop_key is not None:
                    return loop_key
        return None

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        proof_key = (
            self.readonly_term_sequence_contract_key()
            if self.accumulator_proof is not None
            else None
        )
        if proof_key is not None:
            pointer_identity = self.pointer_base_ref.semantic_key()
            count_identity = self.count_parameter_semantic_identity()
            if pointer_identity is None or count_identity is None:
                return None
            return (
                "readonly_reduction_proof_semantic",
                self.reduction_kind,
                pointer_identity,
                count_identity,
                max(1, int(self.result_size or 0)),
                _bias_key(int(self.constant_bias), self.result_size),
                proof_key,
            )
        if self.loop_summary is not None:
            loop_key = self.loop_summary.semantic_key()
            if loop_key is None:
                return None
            pointer_identity = self.pointer_base_ref.semantic_key()
            count_identity = self.count_parameter_semantic_identity()
            if pointer_identity is None or count_identity is None:
                return None
            return (
                "readonly_reduction_loop_semantic",
                self.reduction_kind,
                pointer_identity,
                count_identity,
                max(1, int(self.result_size or 0)),
                _bias_key(int(self.constant_bias), self.result_size),
                loop_key,
            )
        witness_prefix = self._semantic_witness_prefix(required_prefix=3, cap=3)
        if witness_prefix is None:
            return None
        pointer_identity = self.pointer_base_ref.semantic_key()
        count_identity = self.count_parameter_semantic_identity()
        if pointer_identity is None or count_identity is None:
            return None
        return (
            "readonly_reduction_semantic",
            self.reduction_kind,
            pointer_identity,
            count_identity,
            max(1, int(self.result_size or 0)),
            int(self.start_offset),
            _bias_key(int(self.constant_bias), self.result_size),
            tuple(witness.stable_key() for witness in witness_prefix),
        )

    def count_parameter_semantic_identity(self) -> Optional[Tuple[Any, ...]]:
        return _count_parameter_semantic_identity(
            count_parameter_index=self.count_parameter_index,
            count_parameter_storage_identity_key=self.count_parameter_storage_identity_key,
        )

    def count_parameter_semantic_identities(self) -> Tuple[Tuple[Any, ...], ...]:
        return _count_parameter_semantic_identities(
            count_parameter_index=self.count_parameter_index,
            count_parameter_storage_identity_key=self.count_parameter_storage_identity_key,
        )

    def _count_parameter_semantic_identity(self) -> Optional[Tuple[Any, ...]]:
        return self.count_parameter_semantic_identity()

    def readonly_term_sequence_specificity_score(self) -> int:
        """Relative precision of this readonly reduction contract."""

        if self.accumulator_proof is not None:
            score_fn = getattr(
                self.accumulator_proof,
                "readonly_term_sequence_specificity_score",
                None,
            )
            if callable(score_fn):
                try:
                    return max(0, int(score_fn()))
                except (TypeError, ValueError):
                    return 0
        witness_counts = {
            int(witness.exact_count)
            for witness in (self.semantic_witnesses or ())
            if getattr(witness, "exact_count", None) is not None
        }
        return len(witness_counts)

    def _semantic_witness_prefix(
        self,
        *,
        required_prefix: int,
        cap: Optional[int] = None,
    ) -> Optional[Tuple[ReadonlyReductionWitness, ...]]:
        if not self.semantic_witnesses:
            return None
        witnesses_by_count = {
            int(witness.exact_count): witness
            for witness in self.semantic_witnesses
            if int(getattr(witness, "exact_count", 0) or 0) > 0
        }
        prefix = []
        next_count = 1
        while next_count in witnesses_by_count:
            prefix.append(witnesses_by_count[next_count])
            if cap is not None and len(prefix) >= int(cap):
                break
            next_count += 1
        if len(prefix) < max(1, int(required_prefix or 0)):
            return None
        return tuple(prefix)

    def pairwise_exact_key(self) -> Optional[Tuple[Any, ...]]:
        if self.loop_summary is not None and self.loop_summary.pairwise_exact_key() is None:
            return None
        return self.stable_key()

    def pairwise_semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return self.semantic_key()

    def pairwise_requires_guard_equivalence(self) -> bool:
        return False

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "readonly_reduction",
            "reduction_kind": self.reduction_kind,
            "pointer_base_ref": self.pointer_base_ref.to_dict(),
            "count_parameter_name": self.count_parameter_name,
            "count_parameter_index": self.count_parameter_index,
            "count_parameter_storage_identity_key": self.count_parameter_storage_identity_key,
            "stride": int(self.stride),
            "element_size": int(self.element_size),
            "result_size": int(self.result_size),
            "start_offset": int(self.start_offset),
            "signed_counter": bool(self.signed_counter),
            "source": self.source,
            "semantic_witnesses": [witness.to_dict() for witness in self.semantic_witnesses],
            "loop_summary": self.loop_summary.to_dict() if self.loop_summary is not None else None,
            "accumulator_proof": self.accumulator_proof.to_dict() if self.accumulator_proof is not None else None,
            "constant_bias": int(self.constant_bias),
            "display_name": self.display_name(),
        }


@dataclass(frozen=True)
class ReadonlyReductionLowering:
    """Materialized readonly lowering produced from a reduction proof."""

    proof: ReductionAccumulatorProof
    loop_summary: LoopSummaryRef
    readonly_reduction: ReadonlyReductionRef
    lowering_kind: str = "readonly_reduction"

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        proof_key = self.proof.stable_key()
        loop_key = self.loop_summary.stable_key()
        readonly_key = self.readonly_reduction.stable_key()
        if proof_key is None or loop_key is None:
            return None
        return (
            "readonly_reduction_lowering",
            self.lowering_kind,
            proof_key,
            loop_key,
            readonly_key,
        )

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        proof_key = self.proof.semantic_key()
        loop_key = self.loop_summary.semantic_key()
        readonly_key = self.readonly_reduction.semantic_key()
        if proof_key is None or loop_key is None or readonly_key is None:
            return None
        return (
            "readonly_reduction_lowering_semantic",
            self.lowering_kind,
            proof_key,
            loop_key,
            readonly_key,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "readonly_reduction_lowering",
            "lowering_kind": self.lowering_kind,
            "proof": self.proof.to_dict(),
            "loop_summary": self.loop_summary.to_dict(),
            "readonly_reduction": self.readonly_reduction.to_dict(),
        }


@dataclass(frozen=True)
class CountedLoopSummaryRef:
    """Structured identity for a counted scalar loop summary."""

    induction_step: int
    result_size: int
    signed_loop: bool
    residue_cases: Tuple[Tuple[int, int, int, int], ...]
    residue_bias_terms: Tuple[Tuple[int, int, Any], ...] = ()
    source: str = "recurrence_summary"
    loop_summary: Optional[LoopSummaryRef] = None

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        loop_summary_key = self.loop_summary.stable_key() if self.loop_summary is not None else None
        residue_bias_keys = tuple(
            (
                int(modulus),
                int(residue),
                _loop_object_key(bias_expr),
            )
            for modulus, residue, bias_expr in self.residue_bias_terms
        )
        if any(key[2] is None for key in residue_bias_keys):
            return None
        return (
            "counted_loop_summary",
            int(self.induction_step),
            max(1, int(self.result_size or 0)),
            bool(self.signed_loop),
            tuple(
                (
                    int(modulus),
                    int(residue),
                    int(coeff),
                    int(bias),
                )
                for modulus, residue, coeff, bias in self.residue_cases
            ),
            residue_bias_keys,
            self.source,
            loop_summary_key,
        )

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        residue_bias_keys = tuple(
            (
                int(modulus),
                int(residue),
                _loop_object_semantic_key(bias_expr),
            )
            for modulus, residue, bias_expr in self.residue_bias_terms
        )
        if any(key[2] is None for key in residue_bias_keys):
            return None
        if self.loop_summary is not None:
            loop_key = self.loop_summary.semantic_key()
            if loop_key is None:
                return None
            return (
                "counted_loop_summary_loop_semantic",
                int(self.induction_step),
                max(1, int(self.result_size or 0)),
                bool(self.signed_loop),
                tuple(
                    (
                        int(modulus),
                        int(residue),
                        int(coeff),
                        int(bias),
                    )
                    for modulus, residue, coeff, bias in self.residue_cases
                ),
                residue_bias_keys,
                loop_key,
            )
        return (
            "counted_loop_summary_semantic",
            int(self.induction_step),
            max(1, int(self.result_size or 0)),
            bool(self.signed_loop),
            tuple(
                (
                    int(modulus),
                    int(residue),
                    int(coeff),
                    int(bias),
                )
                for modulus, residue, coeff, bias in self.residue_cases
            ),
            residue_bias_keys,
        )

    def pairwise_exact_key(self) -> Optional[Tuple[Any, ...]]:
        if self.loop_summary is not None and self.loop_summary.pairwise_exact_key() is None:
            return None
        return self.stable_key()

    def pairwise_semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return self.semantic_key()

    def pairwise_requires_guard_equivalence(self) -> bool:
        return True

    def display_name(self) -> str:
        return (
            f"counted_loop(step={int(self.induction_step)},"
            f"signed={bool(self.signed_loop)},"
            f"cases={len(self.residue_cases)})"
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "counted_loop_summary",
            "induction_step": int(self.induction_step),
            "result_size": max(1, int(self.result_size or 0)),
            "signed_loop": bool(self.signed_loop),
            "residue_cases": [
                {
                    "modulus": int(modulus),
                    "residue": int(residue),
                    "coeff": int(coeff),
                    "bias": int(bias),
                }
                for modulus, residue, coeff, bias in self.residue_cases
            ],
            "residue_bias_terms": [
                {
                    "modulus": int(modulus),
                    "residue": int(residue),
                    "bias_expr": getattr(bias_expr, "to_dict", lambda: repr(bias_expr))(),
                }
                for modulus, residue, bias_expr in self.residue_bias_terms
            ],
            "source": self.source,
            "loop_summary": self.loop_summary.to_dict() if self.loop_summary is not None else None,
            "display_name": self.display_name(),
        }


@dataclass(frozen=True)
class StateTransitionLoopSummaryRef:
    """Object-centric summary for loops whose trip count is driven by state transitions.

    The summary describes the transition system, not a source-level loop name.
    Two summaries can share an SMT function only when their guard/update surface
    and side-effect profile are structurally/semantically identical.
    """

    state_guard: Any
    transition_expr: Any
    result_size: int
    state_size: int
    accumulator_init: Any = None
    accumulator_delta: Any = None
    transition_cases: Any = None
    side_effect_profile: LoopSideEffectProfileRef = LoopSideEffectProfileRef()
    source: str = "state_transition_loop_summary"

    def __post_init__(self) -> None:
        object.__setattr__(self, "result_size", max(1, int(self.result_size or 0)))
        object.__setattr__(self, "state_size", max(1, int(self.state_size or 0)))

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        guard_key = _loop_object_key(self.state_guard)
        transition_key = _loop_object_key(
            self.transition_cases if self.transition_cases is not None else self.transition_expr
        )
        init_key = _loop_object_key(self.accumulator_init)
        delta_key = _loop_object_key(self.accumulator_delta)
        side_effect_key = self.side_effect_profile.stable_key()
        if (
            guard_key is None
            or transition_key is None
            or init_key is None
            or delta_key is None
            or side_effect_key is None
        ):
            return None
        return (
            "state_transition_loop_summary",
            guard_key,
            transition_key,
            init_key,
            delta_key,
            side_effect_key,
            int(self.state_size),
            int(self.result_size),
            self.source,
        )

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        binding_context = _loop_variable_binding_context_from_values(
            self.state_guard,
            self.transition_cases if self.transition_cases is not None else self.transition_expr,
            self.accumulator_init,
            self.accumulator_delta,
        )
        if binding_context is None:
            return None
        guard_key = _loop_object_semantic_key(self.state_guard, binding_context)
        transition_key = _loop_object_semantic_key(
            self.transition_cases if self.transition_cases is not None else self.transition_expr,
            binding_context,
        )
        init_key = _loop_object_semantic_key(self.accumulator_init, binding_context)
        delta_key = _loop_object_semantic_key(self.accumulator_delta, binding_context)
        side_effect_key = self._scalar_side_effect_semantic_key(binding_context)
        if (
            guard_key is None
            or transition_key is None
            or init_key is None
            or delta_key is None
            or side_effect_key is None
        ):
            return None
        return (
            "state_transition_loop_summary",
            guard_key,
            transition_key,
            init_key,
            delta_key,
            side_effect_key,
            int(self.state_size),
            int(self.result_size),
            self.source,
        )

    def _scalar_side_effect_semantic_key(
        self,
        binding_context: Optional[_LoopVariableBindingContext] = None,
    ) -> Optional[Tuple[Any, ...]]:
        """Semantic effect key for state-transition summaries.

        Branch guards are part of ``state_guard`` and ``transition_cases`` for this
        summary kind, so CFG-local guard counts must not split otherwise identical
        transition systems.  Non-scalar effects still participate in the key.
        """

        effect_keys = tuple(
            _loop_object_semantic_key(effect, binding_context)
            for effect in getattr(self.side_effect_profile, "effect_descriptors", ()) or ()
        )
        context_keys = tuple(
            _loop_object_semantic_key(effect, binding_context)
            for effect in getattr(self.side_effect_profile, "context_descriptors", ()) or ()
        )
        if any(effect_key is None for effect_key in effect_keys + context_keys):
            return None
        return (
            "state_transition_scalar_effect_profile",
            bool(getattr(self.side_effect_profile, "memory_reads", False)),
            bool(getattr(self.side_effect_profile, "memory_writes", False)),
            bool(getattr(self.side_effect_profile, "calls", False)),
            bool(getattr(self.side_effect_profile, "escapes", False)),
            bool(getattr(self.side_effect_profile, "context_memory_writes", False)),
            bool(getattr(self.side_effect_profile, "context_calls", False)),
            bool(getattr(self.side_effect_profile, "context_escapes", False)),
            effect_keys,
            context_keys,
        )

    def display_name(self) -> str:
        return f"state_transition_loop(state={int(self.state_size)},result={int(self.result_size)})"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "state_transition_loop_summary",
            "state_guard": _loop_object_to_dict(self.state_guard),
            "transition_expr": _loop_object_to_dict(self.transition_expr),
            "transition_cases": _loop_object_to_dict(self.transition_cases),
            "accumulator_init": _loop_object_to_dict(self.accumulator_init),
            "accumulator_delta": _loop_object_to_dict(self.accumulator_delta),
            "side_effect_profile": self.side_effect_profile.to_dict(),
            "state_size": int(self.state_size),
            "result_size": int(self.result_size),
            "source": self.source,
            "display_name": self.display_name(),
        }


def _runtime_ref_stable_key_or_repr(value: Any) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return None
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            key = None
        if key is not None:
            return ("stable", key)
    return ("repr", type(value).__module__, type(value).__qualname__, repr(value))


@dataclass(frozen=True)
class UnknownValueRef:
    """Structured identity for UNKNOWN expressions used at runtime."""

    kind: str
    reason: Optional[str] = None
    target_ref: Optional[CallTargetRef] = None
    deferred_call_ref: Optional[DeferredCallRef] = None
    origin_kind: Optional[str] = None
    origin_ref: Optional[Any] = None
    display_hint: Optional[str] = None

    def __post_init__(self) -> None:
        normalized_target = coerce_call_target_ref(self.target_ref)
        object.__setattr__(self, "target_ref", normalized_target)
        deferred_call_ref = getattr(self, "deferred_call_ref", None)
        if isinstance(deferred_call_ref, DeferredCallRef):
            object.__setattr__(self, "deferred_call_ref", deferred_call_ref)

    @classmethod
    def deferred_call(
        cls,
        *,
        deferred_call_ref: Optional[DeferredCallRef] = None,
        target_ref=None,
        placeholder_name: Optional[str] = None,
        sequence: Optional[int] = None,
        deferred_key: Optional[Tuple[Any, ...]] = None,
    ) -> "UnknownValueRef":
        normalized = coerce_call_target_ref(target_ref) or CallTargetRef.unknown()
        normalized_ref = deferred_call_ref
        if normalized_ref is None:
            normalized_ref = DeferredCallRef(
                target_ref=normalized,
                sequence=sequence,
            )
        display_hint = placeholder_name or normalized_ref.display_name()
        return cls(
            kind="deferred_call",
            reason="call_out_of_scope",
            target_ref=normalized,
            deferred_call_ref=normalized_ref,
            display_hint=display_hint,
        )

    @classmethod
    def out_of_scope_call(
        cls,
        *,
        reason: str,
        target_ref=None,
        display_hint: Optional[str] = None,
    ) -> "UnknownValueRef":
        normalized = coerce_call_target_ref(target_ref)
        return cls(
            kind="call_target",
            reason=reason,
            target_ref=normalized,
            display_hint=display_hint,
        )

    @classmethod
    def budget_exceeded(
        cls,
        *,
        operation: Optional[str] = None,
    ) -> "UnknownValueRef":
        reason = f"{operation}_budget_exceeded" if operation else "budget_exceeded"
        return cls(
            kind="budget_exceeded",
            reason=reason,
            display_hint=reason,
        )

    @classmethod
    def opaque(
        cls,
        *,
        reason: Optional[str] = None,
        display_hint: Optional[str] = None,
        origin_kind: Optional[str] = None,
        origin_ref: Optional[Any] = None,
    ) -> "UnknownValueRef":
        normalized_reason = reason or "unknown"
        return cls(
            kind="opaque_unknown",
            reason=normalized_reason,
            origin_kind=origin_kind,
            origin_ref=origin_ref,
            display_hint=display_hint or normalized_reason,
        )

    @classmethod
    def phi_circular(
        cls,
        *,
        pcode_op_ref: Optional[Any] = None,
        display_hint: str = "phi_circular",
    ) -> "UnknownValueRef":
        return cls.opaque(
            reason="phi_circular",
            display_hint=display_hint,
            origin_kind="multiequal_pcode_op",
            origin_ref=pcode_op_ref,
        )

    def stable_key(self) -> Tuple[Any, ...]:
        target_key = self.target_ref.stable_key() if self.target_ref is not None else None
        return (
            self.kind,
            self.reason,
            target_key,
            self.deferred_call_ref.stable_key() if self.deferred_call_ref is not None else None,
        )

    def diagnostic_key(self) -> Tuple[Any, ...]:
        key = self.stable_key()
        if self.origin_kind is None and self.origin_ref is None:
            return key
        return key + (
            self.origin_kind,
            _runtime_ref_stable_key_or_repr(self.origin_ref),
        )

    def display_name(self) -> str:
        if self.display_hint:
            return self.display_hint
        if self.deferred_call_ref is not None:
            return self.deferred_call_ref.display_name()
        if self.target_ref is not None:
            return self.target_ref.display_name()
        return self.reason or "unknown"

    def to_dict(self) -> Dict[str, Any]:
        result: Dict[str, Any] = {
            "kind": self.kind,
            "display_name": self.display_name(),
        }
        if self.reason is not None:
            result["reason"] = self.reason
        if self.deferred_call_ref is not None:
            result["deferred_call_ref"] = self.deferred_call_ref.to_dict()
        if self.target_ref is not None:
            result["target_ref"] = self.target_ref.to_dict()
        if self.origin_kind is not None:
            result["origin_kind"] = self.origin_kind
        if self.origin_ref is not None:
            to_dict = getattr(self.origin_ref, "to_dict", None)
            if callable(to_dict):
                result["origin_ref"] = to_dict()
            else:
                result["origin_ref"] = _runtime_ref_stable_key_or_repr(self.origin_ref)
        return result
