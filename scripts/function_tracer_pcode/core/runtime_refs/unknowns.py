"""Deferred-call and unknown-value references."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple
from scripts.function_tracer_pcode.core.call_target import CallTargetRef, coerce_call_target_ref
from scripts.function_tracer_pcode.core.runtime_refs.pcode import (
    PcodeOpRef,
)


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
        origin_kind: Optional[str] = None,
        origin_ref: Optional[Any] = None,
    ) -> "UnknownValueRef":
        reason = f"{operation}_budget_exceeded" if operation else "budget_exceeded"
        return cls(
            kind="budget_exceeded",
            reason=reason,
            origin_kind=origin_kind,
            origin_ref=origin_ref,
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
        origin_key = None
        stable_key = getattr(self.origin_ref, "stable_key", None)
        if callable(stable_key):
            try:
                candidate_key = stable_key()
            except (AttributeError, TypeError, ValueError, RecursionError):
                candidate_key = None
            if candidate_key is not None:
                origin_key = ("stable", candidate_key)
        return (
            self.kind,
            self.reason,
            target_key,
            self.deferred_call_ref.stable_key() if self.deferred_call_ref is not None else None,
            self.origin_kind,
            origin_key,
        )

    def diagnostic_key(self) -> Tuple[Any, ...]:
        key = self.stable_key()
        if self.origin_kind is None and self.origin_ref is None:
            return key
        return key + (("diagnostic_origin", _runtime_ref_stable_key_or_repr(self.origin_ref)),)

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


# Sibling modules reference each other at call time; import them last to avoid cycles.
