"""Dependency-neutral typed input for an inconclusive base comparison."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Mapping

from ..query_receipt_authority import (
    canonical_region_query_receipt_digest,
    canonical_region_query_receipt_digests,
)
from .contracts import authority_digest, canonical_value


def query_execution_record_projection(record: Any) -> Mapping[str, Any]:
    """Serialize the exact typed query record used by comparison authority."""

    if not callable(getattr(record, "validate", None)) or not record.validate():
        raise ValueError("comparison query record is not valid")
    return {
        "query_label": record.query_label,
        "premise_digest": record.premise_digest,
        "formula_digest": record.formula_digest,
        "disposition": record.disposition,
        "proof_kind": record.proof_kind,
        "projection_binding_ids": list(record.projection_binding_ids),
        "return_width_observation_view_digest": (
            record.return_width_observation_view_digest
        ),
        "return_width_binding_receipt_digest": (
            record.return_width_binding_receipt_digest
        ),
        "canonical_return_width_receipt_digests": list(
            record.canonical_return_width_receipt_digests
        ),
        "formula_text": record.formula_text,
        "region_receipt_digest": canonical_region_query_receipt_digest(record),
        "validated": True,
    }


@dataclass(frozen=True)
class InconclusiveComparisonAuthority:
    """Capability-backed join across exact comparison and terminal receipts."""

    comparison_receipt_id: str
    terminal_receipt_digest: str
    terminal_region_receipt_digests: tuple[str, ...]
    query_receipt_digests: tuple[str, ...]
    binding_digest: str
    schema_version: str = "inconclusive_comparison_authority_v2"
    _dispatch_frame: Any = field(
        default=None, repr=False, compare=False
    )
    _comparison_receipt: Any = field(
        default=None, repr=False, compare=False
    )
    _terminal_receipt: Any = field(
        default=None, repr=False, compare=False
    )
    _query_projections: tuple[Mapping[str, Any], ...] = field(
        default=(), repr=False, compare=False
    )

    @classmethod
    def issue(
        cls, dispatch_frame: Any,
    ) -> "InconclusiveComparisonAuthority":
        if dispatch_frame is None:
            raise TypeError(
                "inconclusive comparison authority requires exact frame"
            )
        comparison = dispatch_frame.receipt
        terminal = dispatch_frame.monolithic_terminal_receipt
        if (
            comparison is None
            or terminal is None
            or not callable(getattr(comparison, "is_trusted_for", None))
            or not callable(getattr(terminal, "validates", None))
            or not comparison.is_trusted_for(dispatch_frame)
            or not terminal.validates()
            or terminal.outcome_kind != "inconclusive_diagnostic"
            or terminal.comparison_receipt_id != comparison.receipt_id
        ):
            raise ValueError(
                "inconclusive comparison receipt join is not canonical"
            )
        query_projections = tuple(
            query_execution_record_projection(record)
            for record in comparison.query_records
        )
        terminal_region_receipt_digests = tuple(
            terminal.region_receipt_digests
        )
        query_region_receipt_digests = (
            canonical_region_query_receipt_digests(
                comparison.query_records
            )
        )
        if terminal_region_receipt_digests != query_region_receipt_digests:
            raise ValueError(
                "terminal and comparison query receipt sets differ"
            )
        query_receipt_digests = tuple(
            authority_digest(row) for row in query_projections
        )
        payload = {
            "schema_version": "inconclusive_comparison_authority_v2",
            "comparison_receipt_id": comparison.receipt_id,
            "terminal_receipt_digest": terminal.receipt_digest,
            "terminal_region_receipt_digests": (
                terminal_region_receipt_digests
            ),
            "query_receipt_digests": query_receipt_digests,
        }
        return cls(
            comparison_receipt_id=comparison.receipt_id,
            terminal_receipt_digest=terminal.receipt_digest,
            terminal_region_receipt_digests=(
                terminal_region_receipt_digests
            ),
            query_receipt_digests=query_receipt_digests,
            binding_digest=authority_digest(payload),
            _dispatch_frame=dispatch_frame,
            _comparison_receipt=comparison,
            _terminal_receipt=terminal,
            _query_projections=query_projections,
        )

    def validates(self) -> bool:
        comparison = self._comparison_receipt
        terminal = self._terminal_receipt
        if (
            comparison is None
            or terminal is None
            or not callable(getattr(comparison, "is_trusted_for", None))
            or not callable(getattr(terminal, "validates", None))
            or not comparison.is_trusted_for(self._dispatch_frame)
            or not terminal.validates()
            or terminal.outcome_kind != "inconclusive_diagnostic"
            or terminal.comparison_receipt_id != comparison.receipt_id
            or self.comparison_receipt_id != comparison.receipt_id
            or self.terminal_receipt_digest != terminal.receipt_digest
            or self.terminal_region_receipt_digests
            != tuple(terminal.region_receipt_digests)
            or self.terminal_region_receipt_digests
            != canonical_region_query_receipt_digests(
                comparison.query_records
            )
            or self._query_projections != tuple(
                query_execution_record_projection(record)
                for record in comparison.query_records
            )
            or self.query_receipt_digests != tuple(
                authority_digest(row) for row in self._query_projections
            )
        ):
            return False
        payload = {
            "schema_version": self.schema_version,
            "comparison_receipt_id": self.comparison_receipt_id,
            "terminal_receipt_digest": self.terminal_receipt_digest,
            "terminal_region_receipt_digests": (
                self.terminal_region_receipt_digests
            ),
            "query_receipt_digests": self.query_receipt_digests,
        }
        return bool(
            self.schema_version
            == "inconclusive_comparison_authority_v2"
            and authority_digest(payload) == self.binding_digest
        )

    def matches_provenance(self, provenance: Mapping[str, Any]) -> bool:
        terminal = provenance.get("monolithic_terminal_receipt")
        queries = tuple(
            provenance.get("query_execution_receipts", ()) or ()
        )
        return bool(
            self.validates()
            and provenance.get("comparison_receipt_id")
            == self.comparison_receipt_id
            and isinstance(terminal, Mapping)
            and terminal.get("validated") is True
            and terminal.get("receipt_digest")
            == self.terminal_receipt_digest
            and terminal.get("comparison_receipt_id")
            == self.comparison_receipt_id
            and terminal.get("outcome_kind")
            == "inconclusive_diagnostic"
            and tuple(terminal.get("region_receipt_digests", ()) or ())
            == self.terminal_region_receipt_digests
            and queries == self._query_projections
        )


@dataclass(frozen=True)
class ComparisonClosureProductionSignal:
    """Typed proof backlog for a receipt-bound inconclusive comparison."""

    comparison_receipt_id: str
    terminal_receipt_digest: str
    branch_id: str
    runtime_premise_digest: str
    runtime_view_id: Any
    query_receipt_digests: tuple[str, ...]
    producer_id: str = "comparison-closure-producer-v1"

    def __post_init__(self) -> None:
        for value in (
            self.comparison_receipt_id, self.terminal_receipt_digest,
            self.branch_id, self.runtime_premise_digest, self.producer_id,
        ):
            if type(value) is not str or not value:
                raise TypeError("comparison closure signal authority is incomplete")
        object.__setattr__(self, "runtime_view_id", canonical_value(self.runtime_view_id))
        object.__setattr__(self, "query_receipt_digests", tuple(self.query_receipt_digests))
        if any(type(item) is not str or not item for item in self.query_receipt_digests):
            raise TypeError("comparison closure query authority is incomplete")
