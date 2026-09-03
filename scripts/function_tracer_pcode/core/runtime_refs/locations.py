"""Address, storage and canonical location references plus post-state snapshot/read references."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple
from scripts.function_tracer_pcode.core.runtime_refs.pcode import (
    PcodeOpRef,
)


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


# Sibling modules reference each other at call time; import them last to avoid cycles.
