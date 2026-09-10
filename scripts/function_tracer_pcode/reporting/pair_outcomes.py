# -*- coding: utf-8 -*-
"""Load canonical pair outcomes from an EqBench/NeqBench result tree.

Only ``*.pair-status.json`` files are read; the signature material they carry
is not verified here (``result_summary`` does that), because the transition
table and the soundness gate are measurement aids, not authorities.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterator, Optional, Tuple

PAIR_STATUS_SUFFIX = ".pair-status.json"
OUTCOME_MISSING = "MISSING"
# A pair-status file that carries no canonical outcome (authority invalid,
# truncated JSON, ...). Identity is then recovered from the file path.
OUTCOME_INVALID = "INVALID"
OUTCOME_ORDER = (
    "EQUIVALENT", "NOT_EQ", "UNKNOWN", "TIMEOUT", "ERROR", OUTCOME_INVALID, OUTCOME_MISSING,
)

LABEL_EQ = "Eq"
LABEL_NEQ = "Neq"
LABEL_UNLABELLED = "unlabelled"

PairKey = Tuple[str, str, str, str]


@dataclass(frozen=True)
class PairOutcome:
    sample_identity: str
    function_name: str
    left_binary_id: str
    right_binary_id: str
    outcome: str
    status_path: str
    # Issue #20: the assumption-dependent column, reported separately from
    # ``outcome``.  ``None`` whenever the pair carries no conditional decision,
    # which is every pair until the conditional lane is activated.
    conditional_outcome: Optional[str] = None

    @property
    def key(self) -> PairKey:
        return (
            self.sample_identity,
            self.function_name,
            self.left_binary_id,
            self.right_binary_id,
        )

    @property
    def pair_id(self) -> str:
        return f"{self.left_binary_id}_{self.right_binary_id}"

    @property
    def label(self) -> str:
        return benchmark_label(self.sample_identity)


def benchmark_label(sample_identity: str) -> str:
    """Return the dataset label encoded in the sample path (``Eq``/``Neq``)."""
    parts = sample_identity.split("/")
    if LABEL_EQ in parts:
        return LABEL_EQ
    if LABEL_NEQ in parts:
        return LABEL_NEQ
    return LABEL_UNLABELLED


def identity_from_status_path(root: Path, status_path: Path) -> Tuple[str, str, str, str]:
    """Recover ``(sample, function, left, right)`` from
    ``<root>/<sample...>/<function>/<function>_<left>_<right>.pair-status.json``."""
    relative = status_path.relative_to(root)
    if len(relative.parts) < 3:
        raise ValueError(f"pair status path too short to carry an identity: {status_path}")
    function_name = relative.parts[-2]
    sample_identity = "/".join(relative.parts[:-2])
    name = relative.name[: -len(PAIR_STATUS_SUFFIX)]
    prefix = f"{function_name}_"
    if not name.startswith(prefix):
        raise ValueError(f"pair status name does not start with its function: {status_path}")
    pair_id = name[len(prefix):]
    if "_O_" in pair_id:
        left, right = pair_id.split("_O_", 1)
        right = f"O_{right}"
    else:
        parts = pair_id.split("_")
        if len(parts) != 2:
            raise ValueError(f"unrecognised pair id in status name: {status_path}")
        left, right = parts
    if not (sample_identity and left and right):
        raise ValueError(f"incomplete identity in status path: {status_path}")
    return sample_identity, function_name, left, right


def iter_pair_outcomes(root: Path) -> Iterator[PairOutcome]:
    for status_path in sorted(root.rglob(f"*{PAIR_STATUS_SUFFIX}")):
        try:
            payload = json.loads(status_path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            payload = {}
        if not isinstance(payload, dict):
            payload = {}
        target = payload.get("pair_execution_target") or {}
        outcome = payload.get("canonical_outcome")
        identity = (
            target.get("sample_identity"),
            target.get("function_name"),
            target.get("left_binary_id"),
            target.get("right_binary_id"),
        )
        if not all(isinstance(value, str) and value for value in identity):
            identity = identity_from_status_path(root, status_path)
        if not (isinstance(outcome, str) and outcome):
            outcome = OUTCOME_INVALID
        conditional = payload.get("conditional_outcome")
        if not (isinstance(conditional, str) and conditional):
            conditional = None
        yield PairOutcome(
            *identity,
            outcome,
            status_path=str(status_path),
            conditional_outcome=conditional,
        )


def load_pair_outcomes(root: Path) -> Dict[PairKey, PairOutcome]:
    outcomes: Dict[PairKey, PairOutcome] = {}
    for record in iter_pair_outcomes(root):
        if record.key in outcomes:
            raise ValueError(
                f"duplicate pair status for {record.key}: "
                f"{outcomes[record.key].status_path} and {record.status_path}"
            )
        outcomes[record.key] = record
    return outcomes
