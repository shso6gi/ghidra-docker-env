"""Dependency-neutral canonical authority for executed comparison queries."""

from __future__ import annotations

import hashlib
from typing import Any, Iterable, Tuple


def canonical_region_query_receipt_digest(record: Any) -> str:
    """Return the digest sealed by a monolithic terminal receipt."""

    validate = getattr(record, "validate", None)
    if not callable(validate) or not validate():
        raise ValueError("canonical region query receipt is invalid")
    fields = (
        record.query_label,
        record.premise_digest,
        record.formula_digest,
        record.disposition,
    )
    if any(type(value) is not str or not value for value in fields):
        raise ValueError("canonical region query receipt is incomplete")
    return hashlib.sha256(repr(fields).encode("utf-8")).hexdigest()


def canonical_region_query_receipt_digests(
    records: Iterable[Any],
) -> Tuple[str, ...]:
    """Preserve execution order while digesting the exact query records."""

    return tuple(
        canonical_region_query_receipt_digest(record)
        for record in tuple(records)
    )
