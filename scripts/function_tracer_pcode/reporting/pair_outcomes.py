# -*- coding: utf-8 -*-
"""Load canonical pair outcomes from an EqBench/NeqBench result tree.

Only ``*.pair-status.json`` files are read; the signature material they carry
is not verified here (``result_summary`` does that), because the transition
table and the soundness gate are measurement aids, not authorities.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterator, Mapping, Optional, Sequence, Tuple

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

#: A run tree may hold one half per benchmark set; a subset run has both.
HALF_EQ = "eq"
HALF_NEQ = "neq"
HALVES = (HALF_EQ, HALF_NEQ)

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")

PairKey = Tuple[str, str, str, str]


def normalized_sha256(value: Any) -> Optional[str]:
    """The lower-case 64 hex digits of ``value``, or ``None`` if it is not one.

    Empty, short, non-string and non-hex values are all "not a digest": a
    reader must never conclude "the two sides are the same binary" from two
    values that merely compare equal (``""`` == ``""``).
    """

    if not isinstance(value, str):
        return None
    candidate = value.strip().lower()
    return candidate if _SHA256_RE.match(candidate) else None


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
    # Issue #15 PR-15-B.  The signed execution target names the two binaries
    # this pair actually ran on; the gate needs them to tell an identical-input
    # pair from any other, and it must not re-derive them from a path.
    left_binary_sha256: Optional[str] = None
    right_binary_sha256: Optional[str] = None
    # The pair log next to the status file, where the result JSON lives.
    log_path: Optional[str] = None
    # ``eq`` / ``neq`` when the status sits under one of a run's halves, else
    # ``None``.  A per-half manifest and ground truth is chosen with this, so a
    # pair is never read against the other half's settings.
    half: Optional[str] = None
    # The pair's own conditional receipt, exactly as the signed status carries
    # it.  Kept unparsed here; the gate validates it through the authority
    # codec rather than trusting these fields.
    conditional_decision_receipt: Optional[Mapping[str, Any]] = None
    # What binds a result JSON (and a conditional receipt) to *this* pair.
    result_occurrence_id: Optional[str] = None
    decision_receipt_digest: Optional[str] = None

    @property
    def identical_input(self) -> bool:
        """Did this pair run on two byte-identical binaries?

        True only when both sides carry a well-formed sha256 and the two are
        the same digest.  A missing or malformed digest is never "identical".
        """

        left = normalized_sha256(self.left_binary_sha256)
        right = normalized_sha256(self.right_binary_sha256)
        return left is not None and left == right

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
        receipt = payload.get("conditional_decision_receipt")
        if not isinstance(receipt, dict):
            receipt = None
        yield PairOutcome(
            *identity,
            outcome,
            status_path=str(status_path),
            conditional_outcome=conditional,
            left_binary_sha256=_target_text(target, "left_binary_sha256"),
            right_binary_sha256=_target_text(target, "right_binary_sha256"),
            log_path=str(_log_path_for(status_path)),
            half=_half_of(root, status_path),
            conditional_decision_receipt=receipt,
            result_occurrence_id=_payload_text(payload, "result_occurrence_id"),
            decision_receipt_digest=_payload_text(payload, "decision_receipt_digest"),
        )


def _payload_text(payload: Any, field: str) -> Optional[str]:
    value = payload.get(field) if isinstance(payload, Mapping) else None
    return value if isinstance(value, str) and value else None


def _target_text(target: Any, field: str) -> Optional[str]:
    value = target.get(field) if isinstance(target, Mapping) else None
    return value if isinstance(value, str) and value else None


def _log_path_for(status_path: Path) -> Path:
    """The pair log the runner wrote next to this status file."""

    return status_path.with_name(
        status_path.name[: -len(PAIR_STATUS_SUFFIX)] + ".log"
    )


def _half_of(root: Path, status_path: Path) -> Optional[str]:
    """``eq``/``neq`` when the status lives under one of a run's halves.

    The half decides which ``run_manifest.txt`` and which ground truth apply,
    so it is read from the path relative to the root that was scanned and is
    never guessed from the sample identity.
    """

    try:
        parts = status_path.relative_to(root).parts
    except ValueError:
        return None
    return parts[0] if parts and parts[0] in HALVES else None


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


def comparison_tree_pair_count(root: Path) -> int:
    """Number of pairs a transition/gate report would read from ``root``.

    Raises ``ValueError`` for the trees the reader itself refuses (an identity
    that is recoverable from neither the payload nor the path, two statuses for
    the same pair).  Callers that want to know *before* producing results
    whether a tree can serve as the ``--before`` side ask here, so the rule
    stays this module's and is never restated by a caller.
    """
    return len(load_pair_outcomes(root))


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--validate-comparison-tree", type=Path, required=True, metavar="ROOT",
        help=(
            "exit 0 and print the pair count when ROOT can be loaded as the "
            "before/after side of a transition report and holds at least one "
            "pair; exit 1 with the reason otherwise"
        ),
    )
    args = parser.parse_args(argv)
    root = args.validate_comparison_tree
    if not root.is_dir():
        print(f"error: not a directory: {root}", file=sys.stderr)
        return 1
    try:
        pairs = comparison_tree_pair_count(root)
    except ValueError as exc:
        print(f"error: not loadable as a result tree: {root}: {exc}", file=sys.stderr)
        return 1
    if pairs == 0:
        print(f"error: no pair status under: {root}", file=sys.stderr)
        return 1
    print(pairs)
    return 0


if __name__ == "__main__":
    sys.exit(main())
