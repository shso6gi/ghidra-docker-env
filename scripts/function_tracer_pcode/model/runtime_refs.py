# -*- coding: utf-8 -*-
"""Runtime object references carried through expression analysis."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple

from .call_target import CallTargetRef, coerce_call_target_ref


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

    def stable_key(self) -> Tuple[Any, ...]:
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
    display_hint: Optional[str] = None

    def __post_init__(self) -> None:
        if self.kind not in {"parameter", "stack_frame", "storage"}:
            raise ValueError(f"Unsupported location base kind: {self.kind}")

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
        display_hint: Optional[str] = None,
    ) -> "LocationBaseRef":
        return cls(
            kind="storage",
            storage_space_id=space_id,
            storage_space=space_name or None,
            storage_offset=int(offset),
            storage_size=max(1, int(size or 0)),
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
        return (
            self.storage_space_id == other.storage_space_id
            and int(self.storage_offset or 0) == int(other.storage_offset or 0)
            and int(self.storage_size or 0) == int(other.storage_size or 0)
        )

    def stable_key(self) -> Tuple[Any, ...]:
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
            return ("parameter", None)
        if self.is_stack_frame():
            return ("stack_frame",)
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
class PcodeOpRef:
    """Stable identity for a concrete Ghidra P-code operation."""

    address_offset: Optional[int] = None
    seq_time: Optional[int] = None
    seq_order: Optional[int] = None
    block_index: Optional[int] = None
    mnemonic: Optional[str] = None

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "pcode_op",
            None if self.address_offset is None else int(self.address_offset),
            None if self.seq_time is None else int(self.seq_time),
            None if self.seq_order is None else int(self.seq_order),
            None if self.block_index is None else int(self.block_index),
            self.mnemonic,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "pcode_op",
            "address_offset": self.address_offset,
            "seq_time": self.seq_time,
            "seq_order": self.seq_order,
            "block_index": self.block_index,
            "mnemonic": self.mnemonic,
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


@dataclass(frozen=True)
class ReadonlyReductionTermRef:
    """Object-centric description of one scalar term in a readonly reduction."""

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
    """Exact-count witness for a readonly reduction."""

    exact_count: int
    terms: Tuple[ReadonlyReductionTermRef, ...]

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "readonly_reduction_witness",
            int(self.exact_count),
            tuple(term.stable_key() for term in self.terms),
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "readonly_reduction_witness",
            "exact_count": int(self.exact_count),
            "terms": [term.to_dict() for term in self.terms],
        }


@dataclass(frozen=True)
class ReadonlyReductionRef:
    """Structured identity for a readonly pointer-reduction summary."""

    reduction_kind: str
    pointer_base_ref: LocationBaseRef
    count_parameter_name: str
    count_parameter_index: Optional[int] = None
    stride: int = 0
    element_size: int = 0
    result_size: int = 0
    start_offset: int = 0
    signed_counter: bool = True
    source: str = "recurrence_summary"
    semantic_witnesses: Tuple[ReadonlyReductionWitness, ...] = ()

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "readonly_reduction",
            self.reduction_kind,
            self.pointer_base_ref.stable_key(),
            self.count_parameter_name,
            None if self.count_parameter_index is None else int(self.count_parameter_index),
            int(self.stride),
            int(self.element_size),
            int(self.result_size),
            int(self.start_offset),
            bool(self.signed_counter),
            self.source,
        )

    def display_name(self) -> str:
        return (
            f"{self.reduction_kind}("
            f"{self.pointer_base_ref.display_name()},"
            f"{self.count_parameter_name},"
            f"stride={int(self.stride)},"
            f"elem={int(self.element_size)})"
        )

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        witness_prefix = self._semantic_witness_prefix(required_prefix=3, cap=3)
        if witness_prefix is None:
            return None
        pointer_identity = (
            ("parameter", int(self.pointer_base_ref.parameter_index))
            if self.pointer_base_ref.is_parameter() and self.pointer_base_ref.parameter_index is not None
            else self.pointer_base_ref.stable_key()
        )
        count_identity = (
            ("parameter", int(self.count_parameter_index))
            if self.count_parameter_index is not None
            else ("parameter_name", self.count_parameter_name)
        )
        return (
            "readonly_reduction_semantic",
            self.reduction_kind,
            pointer_identity,
            count_identity,
            max(1, int(self.result_size or 0)),
            int(self.start_offset),
            tuple(witness.stable_key() for witness in witness_prefix),
        )

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

    def pairwise_exact_key(self) -> Tuple[Any, ...]:
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
            "stride": int(self.stride),
            "element_size": int(self.element_size),
            "result_size": int(self.result_size),
            "start_offset": int(self.start_offset),
            "signed_counter": bool(self.signed_counter),
            "source": self.source,
            "semantic_witnesses": [witness.to_dict() for witness in self.semantic_witnesses],
            "display_name": self.display_name(),
        }


@dataclass(frozen=True)
class CountedLoopSummaryRef:
    """Structured identity for a counted scalar loop summary."""

    induction_step: int
    result_size: int
    signed_loop: bool
    residue_cases: Tuple[Tuple[int, int, int, int], ...]
    source: str = "recurrence_summary"

    def stable_key(self) -> Tuple[Any, ...]:
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
            self.source,
        )

    def semantic_key(self) -> Tuple[Any, ...]:
        return (
            "counted_loop_summary_semantic",
            int(self.induction_step),
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
        )

    def pairwise_exact_key(self) -> Tuple[Any, ...]:
        return self.stable_key()

    def pairwise_semantic_key(self) -> Tuple[Any, ...]:
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
            "source": self.source,
            "display_name": self.display_name(),
        }


@dataclass(frozen=True)
class UnknownValueRef:
    """Structured identity for UNKNOWN expressions used at runtime."""

    kind: str
    reason: Optional[str] = None
    target_ref: Optional[CallTargetRef] = None
    deferred_call_ref: Optional[DeferredCallRef] = None
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
    ) -> "UnknownValueRef":
        normalized_reason = reason or "unknown"
        return cls(
            kind="opaque_unknown",
            reason=normalized_reason,
            display_hint=display_hint or normalized_reason,
        )

    def stable_key(self) -> Tuple[Any, ...]:
        target_key = self.target_ref.stable_key() if self.target_ref is not None else None
        return (
            self.kind,
            self.reason,
            target_key,
            self.deferred_call_ref.stable_key() if self.deferred_call_ref is not None else None,
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
        return result
