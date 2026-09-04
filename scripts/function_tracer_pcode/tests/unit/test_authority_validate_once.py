"""Issue #14: sealed authority objects validate once per process and
canonical_value keeps its exact output with the primitive fast path."""
import enum
import gc
import types
from dataclasses import dataclass

from scripts.function_tracer_pcode.authority import contracts
from types import MappingProxyType

import pytest

from scripts.function_tracer_pcode.authority.contracts import (
    VALIDATED_ONCE,
    ValidatedOnceRegistry,
    assert_deep_immutable,
    authority_digest,
    canonical_value,
    freeze_authority_value,
)


# ---- canonical_value: identical output to the previous implementation ----

def _reference_canonical_value(value):
    from dataclasses import fields, is_dataclass
    from typing import Mapping

    if isinstance(value, enum.Enum):
        return value.value
    if hasattr(value, "to_authority_dict"):
        return _reference_canonical_value(value.to_authority_dict())
    if is_dataclass(value):
        return tuple((f.name, _reference_canonical_value(getattr(value, f.name))) for f in fields(value))
    if isinstance(value, Mapping):
        return tuple((str(k), _reference_canonical_value(v)) for k, v in sorted(value.items(), key=lambda i: str(i[0])))
    if isinstance(value, (list, tuple)):
        return tuple(_reference_canonical_value(c) for c in value)
    if isinstance(value, (set, frozenset)):
        return tuple(sorted([_reference_canonical_value(c) for c in value], key=authority_digest))
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    raise TypeError(type(value).__name__)


class _Colour(str, enum.Enum):
    RED = "red"


class _Level(enum.IntEnum):
    HIGH = 3


@dataclass(frozen=True)
class _Row:
    name: str
    level: _Level
    tags: tuple


class _WithAuthorityDict:
    def to_authority_dict(self):
        return {"kind": _Colour.RED, "n": 1}


class _StrSubclass(str):
    pass


def test_canonical_value_matches_reference_on_nested_values():
    sample = {
        "b": [1, 2.5, True, None, "s", _StrSubclass("sub")],
        "a": _Row("r", _Level.HIGH, (_Colour.RED, {"z": 0, "y": frozenset({3, 1})})),
        3: types.MappingProxyType({"k": _WithAuthorityDict()}),
        "e": {(1, "x"), (0, "y")},
    }
    assert canonical_value(sample) == _reference_canonical_value(sample)
    assert authority_digest(sample) == authority_digest(_reference_canonical_value(sample))
    # Enums are not short-circuited by the primitive fast path.
    assert canonical_value(_Colour.RED) == "red"
    assert canonical_value(_Level.HIGH) == 3
    assert canonical_value(True) is True


# ---- validated-once registry ----

@dataclass(frozen=True)
class _Sealed:
    digest: str


def test_registry_marks_identity_and_forgets_collected_objects():
    registry = ValidatedOnceRegistry()
    obj = _Sealed("a")
    assert not registry.is_validated(obj)
    registry.mark(obj)
    assert registry.is_validated(obj)
    # An equal but distinct object is not considered validated.
    assert not registry.is_validated(_Sealed("a"))
    key = id(obj)
    del obj
    gc.collect()
    assert key not in registry._refs
    # Objects that cannot be weakly referenced are simply not cached.
    registry.mark(("tuple",))
    assert not registry.is_validated(("tuple",))


def test_validate_runs_once_per_sealed_object(monkeypatch):
    from scripts.function_tracer_pcode.authority.lifecycle import stream as stream_mod
    from scripts.function_tracer_pcode.authority.lifecycle.stream import EventRecorder

    recorder = EventRecorder(
        stream_id="stream-1",
        result_occurrence_id="occ-1",
        source_snapshot_fingerprint="fp-1",
    )
    from scripts.function_tracer_pcode.authority.lifecycle.stream import SealedEventStream

    # seal() validates (and memoises) the object it returns; take a fresh
    # object with the same content so the first validate() below is real work.
    sealed = _seal_minimal_stream(recorder)
    sealed = SealedEventStream(sealed.envelope, sealed.events)
    assert not VALIDATED_ONCE.is_validated(sealed)

    calls = {"n": 0}
    real = stream_mod.authority_digest

    def counting(value):
        calls["n"] += 1
        return real(value)

    monkeypatch.setattr(stream_mod, "authority_digest", counting)
    sealed.validate()
    first = calls["n"]
    assert first > 0
    sealed.validate()
    sealed.validate()
    assert calls["n"] == first          # memoised: no re-digesting
    assert VALIDATED_ONCE.is_validated(sealed)

    # A structurally equal but new stream object is validated on its own.
    other = SealedEventStream(sealed.envelope, sealed.events)
    assert other is not sealed and other == sealed
    calls["n"] = 0
    other.validate()
    assert calls["n"] > 0


def _seal_minimal_stream(recorder):
    """Record one typed CAUSE_OBSERVED event and seal (fixture shared with the
    phase-2 stream tests)."""
    from scripts.function_tracer_pcode.authority.lifecycle.stream import EventIntent, EventType
    from scripts.function_tracer_pcode.authority.lifecycle.stream import CauseObservedEventAuthority
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase2 import (
        _occurrence_authority,
    )

    recorder.append(EventIntent(
        EventType.CAUSE_OBSERVED,
        CauseObservedEventAuthority(_occurrence_authority()),
    ))
    return recorder.seal()


# ---- deep immutability of sealed authority content ----

def test_freeze_keeps_digest_and_makes_containers_immutable():
    raw = {"b": [1, {"c": {2, 3}}], "a": ("x", [4])}
    frozen = freeze_authority_value(raw)
    assert isinstance(frozen, MappingProxyType)
    assert isinstance(frozen["b"], tuple) and isinstance(frozen["b"][1]["c"], frozenset)
    assert authority_digest(frozen) == authority_digest(raw)
    assert_deep_immutable(frozen)
    with pytest.raises(TypeError):
        frozen["a"] = "tampered"
    # mutating the original afterwards does not reach the frozen copy
    raw["b"].append(99)
    assert len(frozen["b"]) == 2


def test_registry_refuses_objects_with_nested_mutable_containers():
    @dataclass(frozen=True)
    class _Holder:
        payload: object

    registry = ValidatedOnceRegistry()
    leaky = _Holder({"k": "v"})
    assert registry.mark(leaky) is False
    assert not registry.is_validated(leaky)
    with pytest.raises(TypeError, match=r"\$\.payload"):
        assert_deep_immutable(leaky)
    tight = _Holder(freeze_authority_value({"k": "v"}))
    assert registry.mark(tight) is True


def _receipt_bound_solver_intent():
    """A SOLVER_UNKNOWN intent whose payload carries a Mapping field, built
    from a real outcome-stage execution receipt (phase-6 fixture)."""
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        EventIntent,
        EventType,
        ReceiptBoundSolverExecutionEventAuthority,
        outcome_stage_requirement_id,
    )
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_return_outcome import (
        _execution_receipt,
    )

    receipt = dict(_execution_receipt("same_kind_consistency", "unknown").to_authority_dict())
    payload = ReceiptBoundSolverExecutionEventAuthority(
        outcome_stage_requirement_id(receipt), receipt, False
    )
    return EventIntent(EventType.SOLVER_UNKNOWN, payload), receipt


def test_sealed_stream_content_cannot_be_changed_after_seal():
    from scripts.function_tracer_pcode.authority.lifecycle.stream import EventRecorder

    intent, receipt = _receipt_bound_solver_intent()
    recorder = EventRecorder(
        stream_id="stream-1", result_occurrence_id="occ-1", source_snapshot_fingerprint="fp-1",
    )
    recorder.append(intent)
    sealed = recorder.seal()
    assert VALIDATED_ONCE.is_validated(sealed)          # the cache engaged
    payload = sealed.events[0].authority_payload
    authority = payload.execution_receipt_authority
    assert isinstance(authority, MappingProxyType)
    # The caller's dict is not the recorded object: tampering with it is inert.
    receipt["query_digest"] = "tampered"
    sealed.validate()
    assert authority["query_digest"] != "tampered"
    # The recorded content itself cannot be changed at all.
    with pytest.raises(TypeError):
        authority["query_digest"] = "tampered"
    with pytest.raises(TypeError):
        authority["x"] = "tampered"
    sealed.validate()


def test_immutable_primitive_subclasses_are_accepted():
    # JPype's JInt / JString are int / str subclasses (immutable); canonical
    # target keys carry them in production streams.
    class _JInt(int):
        pass

    @dataclass(frozen=True)
    class _Key:
        parts: tuple

    key = _Key((_JInt(3), "x", 2.5, True, None))
    assert_deep_immutable(key)
    registry = ValidatedOnceRegistry()
    assert registry.mark(key) is True


# ---- mapping keys must be deep-immutable too ----

class _MutableKey:
    """Hashable (by identity) but mutable: a valid dict key whose content
    can change after sealing."""

    def __init__(self, tag):
        self.tag = tag

    def __hash__(self):
        return id(self)

    def __eq__(self, other):
        return self is other


def test_mapping_with_string_keys_is_cacheable():
    @dataclass(frozen=True)
    class _Holder:
        payload: object

    frozen = freeze_authority_value({"b": 1, "a": ("x", 2)})
    assert_deep_immutable(frozen)
    # (a bare mappingproxy cannot be weakly referenced; sealed objects are
    # frozen dataclasses holding it)
    assert ValidatedOnceRegistry().mark(_Holder(frozen)) is True


def test_mapping_with_mutable_object_key_is_rejected_and_not_cached():
    mutable_key = _MutableKey("k")
    proxy = MappingProxyType({mutable_key: "v"})
    with pytest.raises(TypeError, match=r"\$\.<key>"):
        assert_deep_immutable(proxy)

    @dataclass(frozen=True)
    class _Holder:
        payload: object

    holder = _Holder(proxy)
    registry = ValidatedOnceRegistry()
    assert registry.mark(holder) is False
    assert not registry.is_validated(holder)
    # freeze_authority_value keeps keys as they are (no key rewriting), so the
    # object stays uncacheable rather than silently changing meaning.
    refrozen = freeze_authority_value({mutable_key: "v"})
    assert list(refrozen)[0] is mutable_key


def test_key_check_keeps_existing_digests():
    receipt = {"query_digest": "q", "elapsed_ms": 3, "nested": {"k": [1, 2]}}
    expected = authority_digest(receipt)
    frozen = freeze_authority_value(receipt)
    assert_deep_immutable(frozen)
    assert authority_digest(frozen) == expected


# ---- primitive subclasses: keys must be exact str, values are digest-stable ----

class _MutableIntKey(int):
    """An int subclass whose str() depends on mutable state: as a mapping key
    it would change the canonical key representation after sealing."""

    def __new__(cls, value, label):
        obj = int.__new__(cls, value)
        obj.label = label
        return obj

    def __str__(self):
        return self.label

    __repr__ = __str__


def test_int_subclass_key_with_mutable_str_is_rejected_and_not_cached():
    key = _MutableIntKey(1, "before")
    proxy = MappingProxyType({key: "v"})
    with pytest.raises(TypeError, match=r"exact str at \$\.<key>"):
        assert_deep_immutable(proxy)

    @dataclass(frozen=True)
    class _Holder:
        payload: object

    assert ValidatedOnceRegistry().mark(_Holder(proxy)) is False
    # The threat that motivates the rule: canonical keys go through str(key).
    before = authority_digest(proxy)
    key.label = "after"
    assert authority_digest(proxy) != before


def test_primitive_subclass_values_are_digest_stable_and_accepted():
    # As a *value* the same object is harmless: json canonicalisation uses the
    # base int data, so mutating its label cannot change the digest.
    value = _MutableIntKey(7, "before")
    frozen = freeze_authority_value({"k": value})
    assert_deep_immutable(frozen)
    before = authority_digest(frozen)
    value.label = "after"
    assert authority_digest(frozen) == before
    assert authority_digest(frozen) == authority_digest({"k": 7})

    class _Str(str):
        def __str__(self):
            return "overridden"

    frozen_str = freeze_authority_value({"k": _Str("raw")})
    assert_deep_immutable(frozen_str)
    assert authority_digest(frozen_str) == authority_digest({"k": "raw"})


def test_enum_values_must_be_deep_immutable():
    class _Good(enum.Enum):
        A = "a"

    class _Bad(enum.Enum):
        A = {"mutable": True}

    assert_deep_immutable(_Good.A)
    with pytest.raises(TypeError, match=r"\$\.value"):
        assert_deep_immutable(_Bad.A)
