"""Address, storage and canonical location references plus post-state snapshot/read references."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple
from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_entry, runtime_ref_key, runtime_ref_record
from scripts.function_tracer_pcode.core.json_encoding import (as_list, builtin_str, each, inline, is_json_record, mapping_of, materialize, nested, raw)
from scripts.function_tracer_pcode.core.live_values import as_bool, as_int, exact_scalar, exact_tree, scalar_int, scalar_text, str_value, is_kind, method_of
from scripts.function_tracer_pcode.core.runtime_refs.pcode import (
    PcodeOpRef,
)


@dataclass(frozen=True)
@runtime_ref_record
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
    # Data object that contains the address (Ghidra ``Listing.getDataContaining``
    # plus the non-dynamic primary symbol at its start).  ``None`` when the
    # address is not covered by a named data object.
    object_symbol_name: Optional[str] = None
    object_base_offset: Optional[int] = None
    object_size: Optional[int] = None

    @runtime_ref_key(proven=True)
    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        return (
            "address",
            self.program_id,
            self.space_id,
            int(self.address_offset),
        )

    def has_concrete_address(self) -> bool:
        return as_int(self.address_offset) >= 0

    def global_object_identity(self) -> Optional[Tuple[str, int, int]]:
        """``(symbol_name, object_size, offset_in_object)`` of a writable global.

        The identity is program-independent: it names the data object by its
        imported symbol, so the same source-level global compiled by different
        compilers / ISAs canonicalises to the same location.  ``None`` when the
        address is not inside a named data object of a writable, non-volatile
        memory block (read-only data keeps the readonly-image semantics and
        volatile memory is never treated as a plain object).
        """

        if not self.has_concrete_address():
            return None
        if not self.object_symbol_name or self.object_base_offset is None:
            return None
        if self.can_write is not True or self.is_volatile is not False:
            return None
        size = int(self.object_size or 0)
        if size <= 0:
            return None
        offset = int(self.address_offset) - int(self.object_base_offset)
        if offset < 0 or offset >= size:
            return None
        return (str(self.object_symbol_name), size, offset)

    def is_readonly_memory(self) -> bool:
        # field の真偽は owner の API で読む（`bool(...)` と同じ値）
        return (
            self.has_concrete_address()
            and as_bool(self.is_initialized)
            and as_bool(self.can_read)
            and not as_bool(self.can_write)
            and not as_bool(self.is_volatile)
        )

    def display_name(self) -> str:
        hint = self.display_hint
        if as_bool(hint):
            return hint
        return f"ADDR_{as_int(self.address_offset):x}"

    def json_items(self):
        yield "kind", "address"
        yield "address_offset", as_int(self.address_offset)
        yield "source", self.source
        yield "display_name", self.display_name()
        yield "program_id", self.program_id
        yield "space_id", self.space_id
        yield "space_name", self.space_name
        yield "symbol_name", self.symbol_name
        yield "block_name", self.block_name
        yield "is_initialized", self.is_initialized
        yield "can_read", self.can_read
        yield "can_write", self.can_write
        yield "can_execute", self.can_execute
        yield "is_volatile", self.is_volatile
        yield "is_readonly_memory", self.is_readonly_memory()
        yield "object_symbol_name", self.object_symbol_name
        yield "object_base_offset", self.object_base_offset
        yield "object_size", self.object_size

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


def _kind_text(kind: Any) -> Any:
    """`kind` の field の基底型の文字列（文字列でなければ `NOT_PLAIN`。`==` を live な値に当てない）。"""

    if type(kind) is str:
        return kind
    return str_value(kind)


def _int_or_zero(value: Any) -> int:
    """`int(value or 0)` と同じ値（真偽と整数化は owner の API で読む）。"""

    if type(value) is int:
        return value
    if value is None or not as_bool(value):
        return 0
    return as_int(value)


@dataclass(frozen=True)
@runtime_ref_record
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
        if self.kind not in {"parameter", "stack_frame", "storage", "global"}:
            raise ValueError(f"Unsupported location base kind: {self.kind}")
        if self.storage_identity_key is not None:
            # key は `==`・hash・文字列化で読む: list のまま受理した値の葉も基底型の値にする（Issue #242）
            object.__setattr__(self, "storage_identity_key", exact_tree(self.storage_identity_key))
        if self.kind == "global":
            # 構築中の key は list のこともある（owner は exact な tuple だけを写す）: 要素は基底型の値で比べる
            if not self.storage_identity_key or exact_scalar(self.storage_identity_key[0]) != "global_object":
                raise ValueError("global location base requires a global_object identity key")
        if self.kind == "parameter":
            normalized_index = None
            if self.parameter_index is not None:
                try:
                    candidate = scalar_int(self.parameter_index)
                except Exception:
                    candidate = None
                if candidate is not None and candidate >= 0:
                    normalized_index = candidate
            if normalized_index != self.parameter_index:
                object.__setattr__(self, "parameter_index", normalized_index)

    @classmethod
    @runtime_ref_entry
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
    @runtime_ref_entry
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
            storage_offset=scalar_int(offset),
            storage_size=max(1, scalar_int(exact_scalar(size) or 0)),
            storage_identity_key=tuple(storage_identity_key) if storage_identity_key is not None else None,
            display_hint=display_hint,
        )

    @classmethod
    @runtime_ref_entry
    def global_object(
        cls,
        symbol_name: str,
        size: int,
        *,
        space_name: Optional[str] = None,
    ) -> "LocationBaseRef":
        """Base of a writable global / static data object named by its symbol.

        The identity is the imported symbol name and the object size, never
        the absolute address, so the same source global compiled into two
        different binaries canonicalises to the same base (Issue #104).
        """

        name = scalar_text(exact_scalar(symbol_name) or "").strip()
        if not name:
            raise ValueError("global location base requires a symbol name")
        object_size = max(1, scalar_int(exact_scalar(size) or 0))
        return cls(
            kind="global",
            storage_space=space_name or None,
            storage_offset=0,
            storage_size=object_size,
            storage_identity_key=("global_object", name, object_size),
            display_hint=name,
        )

    def is_parameter(self) -> bool:
        return _kind_text(self.kind) == "parameter"

    def is_stack_frame(self) -> bool:
        return _kind_text(self.kind) == "stack_frame"

    def is_storage(self) -> bool:
        return _kind_text(self.kind) == "storage"

    def is_global(self) -> bool:
        return _kind_text(self.kind) == "global"

    @property
    def global_symbol_name(self) -> Optional[str]:
        if not self.is_global() or not self.storage_identity_key:
            return None
        return str(self.storage_identity_key[1])

    def __hash__(self) -> int:
        return hash(self.stable_key())

    def __eq__(self, other: object) -> bool:
        if not is_kind(other, LocationBaseRef):
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

    @runtime_ref_key(proven=True)
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

    @runtime_ref_key(proven=True)
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
        hint = self.display_hint
        if as_bool(hint):
            return hint
        if self.is_parameter():
            name = self.parameter_name
            return name if as_bool(name) else "param"
        if self.is_stack_frame():
            return "stackframe"
        space = self.storage_space
        if not as_bool(space):
            space = "mem"
        return f"{builtin_str(space)}@{_int_or_zero(self.storage_offset)}:{_int_or_zero(self.storage_size)}"

    def matches_parameter(self, param: Dict[str, Any]) -> bool:
        if not self.is_parameter():
            return False
        try:
            # `param` は呼び出し元の dict: 値は基底型の値で読む（Issue #242）
            param_index = exact_scalar(method_of(param, "get")("index"))
            if self.parameter_index is not None and param_index is not None:
                if self.owner_program_id is not None or self.owner_entry_offset is not None:
                    return (
                        scalar_int(param_index) == int(self.parameter_index)
                        and exact_tree(method_of(param, "get")("owner_program_id")) == self.owner_program_id
                        and exact_tree(method_of(param, "get")("owner_entry_offset")) == self.owner_entry_offset
                    )
                return scalar_int(param_index) == int(self.parameter_index)
        except Exception:
            pass
        return False

    def json_items(self):
        yield "kind", self.kind
        yield "display_name", self.display_name()
        if self.parameter_name is not None:
            yield "parameter_name", self.parameter_name
        if self.parameter_index is not None:
            yield "parameter_index", self.parameter_index
        if self.owner_program_id is not None:
            yield "owner_program_id", self.owner_program_id
        if self.owner_entry_offset is not None:
            yield "owner_entry_offset", self.owner_entry_offset
        if self.storage_space is not None:
            yield "storage_space", self.storage_space
        if self.storage_space_id is not None:
            yield "storage_space_id", self.storage_space_id
        if self.storage_offset is not None:
            yield "storage_offset", self.storage_offset
        if self.storage_size is not None:
            yield "storage_size", self.storage_size
        if self.storage_identity_key is not None:
            yield "storage_identity_key", self.storage_identity_key

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class LocationStep:
    kind: str
    value: int

    def __post_init__(self) -> None:
        if self.kind not in {"offset", "deref"}:
            raise ValueError(f"Unsupported location step kind: {self.kind}")

    @runtime_ref_key(proven=True)
    def stable_key(self) -> Tuple[str, int]:
        return (self.kind, int(self.value))

    def json_items(self):
        yield "kind", self.kind
        yield "value", as_int(self.value)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True, init=False)
@runtime_ref_record
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
        # scalar の subclass は基底型の値にしてから整数にする（subclass の `__int__` を呼ばない。Issue #242）
        object.__setattr__(self, "offset", scalar_int(offset))
        object.__setattr__(self, "size", scalar_int(size))
        object.__setattr__(self, "steps", tuple(steps))

    @property
    def base_param(self) -> str:
        return exact_scalar(self.base_ref.display_name())  # 代わりの型の method の結果の葉を写す

    @runtime_ref_key
    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.base_ref.stable_key(),
            tuple(method_of(step, "stable_key")() for step in self.steps),
            int(self.offset),
            int(self.size),
        )

    def json_items(self):
        yield "base_ref", self.base_ref
        yield "offset", as_int(self.offset)
        yield "size", as_int(self.size)
        yield "steps", each(self.steps)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class PostStateValueRef:
    """Structured identity for a fully materialized final object-state value."""

    location: CanonicalLocation
    snapshot_ref: Optional["PostStateSnapshotRef"] = None
    source: str = "effect_summary"
    state_kind: str = "materialized_final_value"

    @runtime_ref_key
    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "post_state_value",
            self.location.stable_key(),
            self.snapshot_ref.stable_key() if self.snapshot_ref is not None else None,
            self.source,
            self.state_kind,
        )

    def json_items(self):
        yield "kind", "post_state_value"
        yield "location", self.location
        yield "snapshot_ref", self.snapshot_ref if self.snapshot_ref is not None else None
        yield "source", self.source
        yield "state_kind", self.state_kind

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class PostStateSnapshotRef:
    """Structured identity for a shared post-state memory snapshot."""

    scope: str = "function_return"
    source: str = "effect_summary"
    epoch: str = "post_effects"
    pcode_op_ref: Optional["PcodeOpRef"] = None

    @classmethod
    def function_return(cls) -> "PostStateSnapshotRef":
        return cls()

    @runtime_ref_key(proven=True)
    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "post_state_snapshot",
            self.scope,
            self.source,
            self.epoch,
        )

    def json_items(self):
        yield "kind", "post_state_snapshot"
        yield "scope", self.scope
        yield "source", self.source
        yield "epoch", self.epoch
        yield "pcode_op_ref", self.pcode_op_ref if self.pcode_op_ref is not None else None

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class PostStateReadRef:
    """Structured identity for a symbolic read from a shared post-state snapshot."""

    location: CanonicalLocation
    snapshot_ref: Optional[PostStateSnapshotRef] = None
    source: str = "effect_summary"
    state_kind: str = "symbolic_post_state_read"

    @runtime_ref_key
    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "post_state_read",
            self.location.stable_key(),
            self.snapshot_ref.stable_key() if self.snapshot_ref is not None else None,
            self.source,
            self.state_kind,
        )

    @runtime_ref_entry
    def with_location(self, location: CanonicalLocation) -> "PostStateReadRef":
        return PostStateReadRef(
            location=location,
            snapshot_ref=self.snapshot_ref,
            source=self.source,
            state_kind=self.state_kind,
        )

    @runtime_ref_entry
    def with_snapshot(self, snapshot_ref: Optional[PostStateSnapshotRef]) -> "PostStateReadRef":
        return PostStateReadRef(
            location=self.location,
            snapshot_ref=snapshot_ref,
            source=self.source,
            state_kind=self.state_kind,
        )

    def json_items(self):
        yield "kind", "post_state_read"
        yield "location", self.location
        yield "snapshot_ref", self.snapshot_ref if self.snapshot_ref is not None else None
        yield "source", self.source
        yield "state_kind", self.state_kind

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class ObservedMemoryReadRef:
    """Structured provenance for an observed LOAD-derived memory read."""

    order_key: Optional[int] = None
    location: Optional[CanonicalLocation] = None
    snapshot_ref: Optional[PostStateSnapshotRef] = None
    pcode_op_ref: Optional[PcodeOpRef] = None
    source: str = "ghidra_load"

    @runtime_ref_key
    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "observed_memory_read",
            None if self.order_key is None else int(self.order_key),
            self.location.stable_key() if self.location is not None else None,
            self.snapshot_ref.stable_key() if self.snapshot_ref is not None else None,
            self.pcode_op_ref.stable_key() if self.pcode_op_ref is not None else None,
            self.source,
        )

    @runtime_ref_entry
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

    @runtime_ref_entry
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

    def json_items(self):
        yield "kind", "observed_memory_read"
        yield "order_key", self.order_key
        yield "location", self.location if self.location is not None else None
        yield "snapshot_ref", self.snapshot_ref if self.snapshot_ref is not None else None
        yield "pcode_op_ref", self.pcode_op_ref if self.pcode_op_ref is not None else None
        yield "source", self.source

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


# Sibling modules reference each other at call time; import them last to avoid cycles.
