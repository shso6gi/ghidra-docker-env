# -*- coding: utf-8 -*-
"""Proof-owned premises for conditional (assumption-dependent) equivalence.

An ``AssumptionPremise`` is a *semantic proof premise*, not an authority
object: it records what a conditional proof was allowed to assume, in a form
that is deterministic, canonical and deeply immutable.  The authority layer
imports this module downward and binds premises into its own conditional
receipts (``authority.decision.conditional``); this module must never import
authority, so it carries no digest, signature or decision policy.

The contract is shared with the counterexample work of Issue #18: a new
``AssumptionKind`` is added by the PR that first produces premises of that
kind, together with the payload keys that kind requires.  Nothing here makes
a premise true -- discharging or refusing a premise is the job of the proof
that depends on it.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum
from typing import Any, Iterable, Mapping, Sequence, Tuple


CONDITIONAL_ASSUMPTION_SCHEMA_VERSION = 1


class AssumptionKind(str, Enum):
    """The kinds of premise a conditional proof may depend on."""

    # Issue #20: the callee behaves like the catalog specification of its
    # canonical symbol (same value semantics, no observable memory write,
    # normal return).  Being an external symbol is *not* itself evidence for
    # this; the premise is what the proof assumes on top of that evidence.
    EXTERNAL_CALLEE_SPEC = "EXTERNAL_CALLEE_SPEC"


# Payload leaves are exact primitives.  Subclasses (JPype ``JInt`` /
# ``JString``, ``IntEnum`` members, ...) are rejected at construction rather
# than normalized, because a premise built from a live runtime object would
# not be reproducible from the serialized receipt.
_LEAF_TYPES = (bool, int, float, str)


def _normalized_leaf(value: Any, path: str) -> Any:
    if value is None:
        return None
    if type(value) is float:
        if not math.isfinite(value):
            raise ValueError(f"assumption payload float must be finite at {path}")
        return value
    if type(value) in _LEAF_TYPES:
        return value
    if isinstance(value, _LEAF_TYPES):
        raise TypeError(
            f"assumption payload leaf must be an exact primitive at {path}: "
            f"{type(value).__name__}"
        )
    raise TypeError(
        f"assumption payload carries an unsupported value at {path}: "
        f"{type(value).__name__}"
    )


def _normalized_payload_value(value: Any, path: str) -> Any:
    if isinstance(value, Mapping):
        return _normalized_payload(value, path)
    if isinstance(value, (list, tuple)):
        return tuple(
            _normalized_payload_value(item, f"{path}[{index}]")
            for index, item in enumerate(value)
        )
    return _normalized_leaf(value, path)


def _normalized_payload(value: Any, path: str = "$") -> Tuple[Tuple[str, Any], ...]:
    """Return one payload level as a key-sorted tuple of ``(name, value)``."""
    if isinstance(value, Mapping):
        items: Sequence[Tuple[Any, Any]] = tuple(value.items())
    elif isinstance(value, (list, tuple)):
        items = tuple(value)
    else:
        raise TypeError(
            f"assumption payload must be a mapping or a sequence of pairs at {path}: "
            f"{type(value).__name__}"
        )
    normalized = []
    for item in items:
        if not isinstance(item, (list, tuple)) or len(item) != 2:
            raise TypeError(f"assumption payload entry must be a (name, value) pair at {path}")
        name, child = item
        if type(name) is not str or not name:
            raise TypeError(f"assumption payload name must be a non-empty exact str at {path}")
        normalized.append((name, _normalized_payload_value(child, f"{path}.{name}")))
    names = [name for name, _child in normalized]
    if len(set(names)) != len(names):
        raise ValueError(f"assumption payload repeats a name at {path}")
    return tuple(sorted(normalized, key=lambda pair: pair[0]))


@dataclass(frozen=True)
class AssumptionPremise:
    """One explicit premise a conditional proof depends on.

    ``subject`` names what the premise is about (a canonical callee symbol,
    for example) and ``payload`` carries the premise content as a key-sorted
    tuple of pairs.  Construction normalizes mappings and sequences into that
    canonical form and rejects anything that is not deeply immutable, so the
    authority layer's ``assert_deep_immutable`` holds by construction and two
    premises built from equal facts compare and serialize identically.
    """

    kind: AssumptionKind
    subject: str
    payload: Tuple[Tuple[str, Any], ...] = ()
    schema_version: int = CONDITIONAL_ASSUMPTION_SCHEMA_VERSION

    def __post_init__(self) -> None:
        if type(self.kind) is not AssumptionKind:
            object.__setattr__(self, "kind", AssumptionKind(self.kind))
        if type(self.subject) is not str or not self.subject:
            raise TypeError("assumption subject must be a non-empty exact str")
        if type(self.schema_version) is not int:
            raise TypeError("assumption schema version must be an exact int")
        if self.schema_version != CONDITIONAL_ASSUMPTION_SCHEMA_VERSION:
            raise ValueError(
                f"unsupported assumption schema version: {self.schema_version}"
            )
        object.__setattr__(self, "payload", _normalized_payload(self.payload))

    def premise_key(self) -> Tuple[Any, ...]:
        """Return the canonical identity of this premise as a nested tuple.

        Ordering and digesting a set of premises is the authority layer's
        policy; this key exists so the proof layer can compare and de-duplicate
        premises without depending on it.
        """
        return (self.schema_version, self.kind.value, self.subject, self.payload)

    def payload_value(self, name: str, default: Any = None) -> Any:
        for key, value in self.payload:
            if key == name:
                return value
        return default


def normalize_assumption_premises(
    premises: Iterable[AssumptionPremise],
) -> Tuple[AssumptionPremise, ...]:
    """De-duplicate an assumption set, keeping first-seen order.

    A conditional proof depends on its whole assumption set (no minimization),
    so this only removes exact repeats; it never drops a distinct premise.
    """
    seen = set()
    unique = []
    for premise in premises:
        if type(premise) is not AssumptionPremise:
            raise TypeError(
                f"assumption sets carry AssumptionPremise only: {type(premise).__name__}"
            )
        key = premise.premise_key()
        if key in seen:
            continue
        seen.add(key)
        unique.append(premise)
    return tuple(unique)
