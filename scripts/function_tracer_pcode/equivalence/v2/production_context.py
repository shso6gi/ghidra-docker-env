"""Leaf context authority shared by production signal scopes and issuers."""

from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
from typing import Any, Dict, Iterator, Optional, Tuple


_ACTIVE_SESSION: ContextVar[Optional[Any]] = ContextVar(
    "unknown_taxonomy_v2_active_production_pilot_session", default=None
)

_COMPARISON_RECEIPT_AUTHORITIES: Dict[str, Tuple[Any, Any, Any]] = {}


def active_production_pilot_session() -> Optional[Any]:
    return _ACTIVE_SESSION.get()


def register_comparison_receipt_authority(
    receipt_id: str, frame: Any, receipt: Any, production_session: Any,
) -> None:
    """Record exact objects only after the built-in issuer installs its receipt."""

    if (
        type(receipt_id) is not str
        or not receipt_id
        or getattr(receipt, "receipt_id", None) != receipt_id
        or getattr(frame, "authoritative_receipt", None) is not receipt
        or getattr(frame, "receipt", None) is not receipt
    ):
        raise ValueError("comparison receipt authority registration is invalid")
    _COMPARISON_RECEIPT_AUTHORITIES[receipt_id] = (
        frame, receipt, production_session,
    )


def comparison_receipt_authority(receipt: Any, frame: Any) -> Optional[Tuple[Any, Any, Any]]:
    authority = _COMPARISON_RECEIPT_AUTHORITIES.get(
        getattr(receipt, "receipt_id", "")
    )
    if (
        authority is None
        or authority[0] is not frame
        or authority[1] is not receipt
        or getattr(frame, "authoritative_receipt", None) is not receipt
        or getattr(frame, "receipt", None) is not receipt
    ):
        return None
    return authority


@contextmanager
def production_pilot_session_scope(session: Any) -> Iterator[None]:
    token = _ACTIVE_SESSION.set(session)
    try:
        yield
    finally:
        _ACTIVE_SESSION.reset(token)
