# -*- coding: utf-8 -*-
"""Shared soundness gate over finished EqBench / NeqBench result trees.

Usage::

    python3 -m scripts.function_tracer_pcode.reporting.soundness_gate \
        logs/EqBench/subset_current/eq logs/EqBench/subset_current/neq [--json gate.json]

What makes the gate FAIL (Issue #15 PR-15-B; this replaces the label-only rule
the gate used before):

A0  a *verified* unconditional ground-truth violation -- the function-level
    relation that ``function_diff_manifest.json`` records for this exact
    ``(sample, function)`` is ``CONFIRMED_EQ`` and the pair was judged
    ``NOT_EQ``, or it is ``CONFIRMED_NOT_EQ`` and the pair was judged
    ``EQUIVALENT``.  **Eq samples are looked up too**: the dataset directory a
    sample lives in is not by itself a verified relation, so a ``NOT_EQ`` on an
    ``Eq`` sample whose function the manifest cannot classify is an
    investigation row, not a violation.
A0c the same contradiction read against the assumption-dependent column, and
    only when every premise of that pair's conditional receipt is recorded as
    ``verified`` in ``scripts/eqbench/ground_truth_conditional_compatibility.json``.
    A premise that is unverified, not applicable or absent leaves the row an
    investigation (A0u), because a reviewed relation says nothing about what
    holds once a callee is merely *assumed* to meet a specification.
A   an identical-input pair -- both sides of the signed execution target carry
    the same sha256 -- whose identity evidence confirms one and the same
    function on both sides, judged ``NOT_EQ``.  This holds in every mode; byte
    identity is not a matter of configuration.
B   a fast-path acceptance failure: with the fast path ``on``, an applicable
    identical pair that was not accepted, or one whose disposition cannot be
    read at all (``unverifiable``).
C   a configuration or integrity failure: an analysis config that names the v3
    schema without a usable ``identical_fast_path``, a conditional column that
    does not hold together, an unreadable ground truth, or broken compatibility
    metadata.

UNKNOWN / TIMEOUT / ERROR / INVALID decide nothing and never violate anything.
Dataset-label mismatches, unregistered ground truth, ``UNKNOWN`` verdicts and
unverified assumption compatibility are counted and reported, but they do not
fail the gate: they are work items, not proofs of unsoundness.

The gate reads only finished artifacts (pair statuses, the run manifest, the
ground-truth manifest and the result JSON in each pair log).  It never runs
Ghidra, never opens a fixture, and never changes a pair's outcome.  Exit 0 on
PASS, 1 on a violation, 2 when the trees hold no pair status at all.

``benchmark_validation_gate`` keeps its own classification and its own verdict;
the two gates are not mixed and neither reads the other's result.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.reporting.pair_outcomes import (
    LABEL_EQ,
    LABEL_NEQ,
    LABEL_UNLABELLED,
    OUTCOME_ORDER,
    PairOutcome,
    iter_pair_outcomes,
    normalized_sha256,
)

EXIT_PASS = 0
EXIT_VIOLATION = 1
EXIT_EMPTY = 2

GATE_SCHEMA = "soundness-gate-v2"

OUTCOME_EQ = "EQUIVALENT"
OUTCOME_NOT_EQ = "NOT_EQ"
DECISIVE_OUTCOMES = (OUTCOME_EQ, OUTCOME_NOT_EQ)

TRUTH_EQ = "CONFIRMED_EQ"
TRUTH_NOT_EQ = "CONFIRMED_NOT_EQ"

#: The outcome a reviewed relation forbids.
FORBIDDEN_BY_TRUTH = {TRUTH_EQ: OUTCOME_NOT_EQ, TRUTH_NOT_EQ: OUTCOME_EQ}
#: The outcome the dataset directory *suggests* is wrong.  Never a violation on
#: its own -- only the input to an investigation row.
MISMATCHED_BY_LABEL = {LABEL_EQ: OUTCOME_NOT_EQ, LABEL_NEQ: OUTCOME_EQ}

RUN_MANIFEST_FILE = "run_manifest.txt"
GROUND_TRUTH_FILE = "function_diff_manifest.json"
ANALYSIS_CONFIG_SCHEMA_KEY = "analysis_config_schema"
IDENTICAL_FAST_PATH_KEY = "identical_fast_path"
ANALYSIS_CONFIG_V3_SCHEMA = "eqbench-analysis-config-v3"

MODE_ON = "on"
MODE_OFF = "off"
#: A run that recorded neither the schema nor the flag.  The fast path is not
#: guessed from anything else, and gate B is simply not evaluated.
MODE_LEGACY_UNKNOWN = "legacy_unknown"
MODE_INVALID = "invalid"

#: The identity observation a PR-15-A or later checker writes for a pair whose
#: two inputs carry the same sha256.
IDENTITY_EVIDENCE_KEY = "identical_function_identity_evidence"
IDENTITY_EVIDENCE_SCHEMA = "identical_function_identity_evidence_v1"
DISPOSITION_KEY = "identical_fast_path_disposition"

RESULT_JSON_BEGIN = "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
RESULT_JSON_END = "=== EQUIVALENCE_RESULT_JSON_END ==="

COMPATIBILITY_SCHEMA = "ground-truth-conditional-compatibility-v1"
COMPATIBILITY_VERIFIED = "verified"
COMPATIBILITY_UNVERIFIED = "unverified"
COMPATIBILITY_NOT_APPLICABLE = "not_applicable"
COMPATIBILITY_UNKNOWN = "unknown"
COMPATIBILITY_STATUSES = frozenset({
    COMPATIBILITY_VERIFIED, COMPATIBILITY_UNVERIFIED, COMPATIBILITY_NOT_APPLICABLE,
})
COMPATIBILITY_ANY_SUBJECT = "*"
DEFAULT_COMPATIBILITY_PATH = (
    Path(__file__).resolve().parents[2]
    / "eqbench"
    / "ground_truth_conditional_compatibility.json"
)

# Identity dispositions, as the checker writes them.
IDENTITY_CONFIRMED = "confirmed_same_function"
IDENTITY_UNVERIFIED = "same_function_unverified"


# ---------------------------------------------------------------------------
# conditional compatibility metadata
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ConditionalCompatibility:
    """Which reviewed relations are known to survive which premises."""

    path: Optional[str]
    sha256: Optional[str]
    entries: Mapping[Tuple[str, str, str, str], str]

    def status(self, sample: str, function: str, kind: str, subject: str) -> str:
        """``verified`` / ``unverified`` / ``not_applicable`` / ``unknown``.

        An exact ``(sample, function, kind, subject)`` entry wins; a ``*``
        subject entry covers the rest of that kind; anything else is
        ``unknown``.  ``unknown`` is never treated as permission.
        """

        exact = self.entries.get((sample, function, kind, subject))
        if exact is not None:
            return exact
        any_subject = self.entries.get(
            (sample, function, kind, COMPATIBILITY_ANY_SUBJECT)
        )
        return any_subject if any_subject is not None else COMPATIBILITY_UNKNOWN


EMPTY_COMPATIBILITY = ConditionalCompatibility(path=None, sha256=None, entries={})


def load_conditional_compatibility(path: Path) -> ConditionalCompatibility:
    """Read the evaluation-side compatibility metadata, or raise ``ValueError``.

    Every field is checked: a file the gate cannot fully understand must fail
    the gate (C5) rather than silently contribute zero verified entries, which
    would look exactly like "nothing is verified" and hide the breakage.
    """

    raw = Path(path).read_bytes()
    try:
        payload = json.loads(raw.decode("utf-8"))
    except (UnicodeError, ValueError) as exc:
        raise ValueError(f"conditional compatibility metadata is not JSON: {path}") from exc
    if not isinstance(payload, Mapping) or payload.get("schema") != COMPATIBILITY_SCHEMA:
        raise ValueError(f"unexpected conditional compatibility schema in {path}")
    rows = payload.get("entries")
    if not isinstance(rows, list):
        raise ValueError(f"conditional compatibility metadata has no entries: {path}")
    entries: Dict[Tuple[str, str, str, str], str] = {}
    for row in rows:
        if not isinstance(row, Mapping):
            raise ValueError(f"conditional compatibility entry is not an object: {path}")
        key_fields = ("sample", "function", "assumption_kind", "subject")
        for name in (*key_fields, "status"):
            if not isinstance(row.get(name), str) or not row[name]:
                raise ValueError(
                    f"conditional compatibility entry lacks {name}: {path}"
                )
        if row["status"] not in COMPATIBILITY_STATUSES:
            raise ValueError(
                f"conditional compatibility entry has an unknown status: {path}"
            )
        key = tuple(row[name] for name in key_fields)
        if key in entries:
            raise ValueError(f"duplicate conditional compatibility entry: {key}")
        entries[key] = row["status"]
    return ConditionalCompatibility(
        path=str(path),
        sha256=hashlib.sha256(raw).hexdigest(),
        entries=entries,
    )


# ---------------------------------------------------------------------------
# run configuration (mode)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RunMode:
    mode: str
    detail: str
    manifest_path: Optional[str] = None


def _read_key_values(path: Path) -> Mapping[str, str]:
    fields: Dict[str, str] = {}
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            fields[key.strip()] = value.strip()
    return fields


def resolve_run_mode(manifest_path: Path) -> RunMode:
    """Read one run manifest's fast-path mode, or say why it cannot be read.

    A run predating the flag names neither key and stays ``legacy_unknown`` --
    it is not assumed to be ``off``.  A run that names the v3 config schema must
    carry a usable flag, because the schema is what promises the digest
    separates the two modes.
    """

    if not manifest_path.is_file():
        return RunMode(MODE_LEGACY_UNKNOWN, "run_manifest_absent")
    try:
        fields = _read_key_values(manifest_path)
    except OSError as exc:
        return RunMode(MODE_INVALID, f"run_manifest_unreadable: {exc}",
                       str(manifest_path))
    schema = fields.get(ANALYSIS_CONFIG_SCHEMA_KEY)
    flag = fields.get(IDENTICAL_FAST_PATH_KEY)
    if schema is not None:
        if schema != ANALYSIS_CONFIG_V3_SCHEMA:
            return RunMode(
                MODE_INVALID, f"unknown_analysis_config_schema: {schema}",
                str(manifest_path),
            )
        if flag not in ("0", "1"):
            return RunMode(
                MODE_INVALID,
                f"identical_fast_path_invalid: {flag!r}",
                str(manifest_path),
            )
        return RunMode(MODE_ON if flag == "1" else MODE_OFF, "analysis_config_v3",
                       str(manifest_path))
    if flag is None:
        return RunMode(MODE_LEGACY_UNKNOWN, "no_fast_path_field", str(manifest_path))
    if flag not in ("0", "1"):
        return RunMode(
            MODE_INVALID, f"identical_fast_path_invalid: {flag!r}", str(manifest_path),
        )
    return RunMode(MODE_ON if flag == "1" else MODE_OFF, "fast_path_field_only",
                   str(manifest_path))


# ---------------------------------------------------------------------------
# per-root / per-half scopes
# ---------------------------------------------------------------------------


@dataclass(frozen=True, eq=False)
class Scope:
    """One root, or one half of one root: its own manifest and ground truth.

    Compared by identity (``eq=False``): it carries a loaded manifest, and two
    scopes are "the same scope" only when they are the same object.
    """

    root: str
    half: Optional[str]
    directory: Path
    mode: RunMode
    manifest: Optional[Any]
    ground_truth: str

    @property
    def name(self) -> str:
        return self.root if self.half is None else f"{self.root}/{self.half}"


def _load_ground_truth(directory: Path) -> Tuple[Optional[Any], str]:
    """This scope's own ``function_diff_manifest.json``, or ``(None, reason)``."""

    from scripts.function_tracer_pcode.reporting.benchmark_validation_gate import (
        FunctionDiffManifest,
    )

    path = directory / GROUND_TRUTH_FILE
    if not path.is_file():
        return None, "absent"
    try:
        return FunctionDiffManifest.load(path), str(path)
    except (OSError, ValueError) as exc:
        return None, f"unreadable: {exc}"


def _build_scope(root: Path, half: Optional[str]) -> Scope:
    directory = root if half is None else root / half
    manifest, ground_truth = _load_ground_truth(directory)
    return Scope(
        root=str(root),
        half=half,
        directory=directory,
        mode=resolve_run_mode(directory / RUN_MANIFEST_FILE),
        manifest=manifest,
        ground_truth=ground_truth,
    )


class _ScopeResolver:
    """A root with its own run manifest speaks for itself; else each half does.

    A tree is never read against another tree's manifest or another half's
    ground truth, so a subset run holding both halves cannot have its Eq pairs
    judged by the Neq ground truth.  Scopes are built only for the halves that
    actually hold a pair, so an unused directory never reports a mode.
    """

    def __init__(self, root: Path) -> None:
        self._root = root
        self._root_level = (root / RUN_MANIFEST_FILE).is_file()
        self._scopes: Dict[Optional[str], Scope] = {}

    def for_half(self, half: Optional[str]) -> Scope:
        key = None if self._root_level else half
        if key not in self._scopes:
            self._scopes[key] = _build_scope(self._root, key)
        return self._scopes[key]

    @property
    def scopes(self) -> Tuple[Scope, ...]:
        return tuple(self._scopes.values())


# ---------------------------------------------------------------------------
# result JSON, bound to its own pair
# ---------------------------------------------------------------------------


def read_result_payload(record: PairOutcome) -> Tuple[Optional[Mapping[str, Any]], str]:
    """The pair log's last result JSON, or ``(None, reason)``.

    The payload is returned only when it is bound to *this* pair: same result
    occurrence, same decision receipt digest, same function on both sides, same
    two input binaries and the same final outcome.  A log that belongs to
    another pair (a copied file, a stale rerun) is refused rather than read.
    """

    if not record.log_path:
        return None, "log_path_unknown"
    path = Path(record.log_path)
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None, "log_absent"
    blocks: List[str] = []
    index = 0
    while True:
        begin = text.find(RESULT_JSON_BEGIN, index)
        if begin < 0:
            break
        end = text.find(RESULT_JSON_END, begin)
        if end < 0:
            break
        blocks.append(text[begin + len(RESULT_JSON_BEGIN):end])
        index = end + len(RESULT_JSON_END)
    if not blocks:
        return None, "result_json_absent"
    try:
        payload = json.loads(blocks[-1])
    except ValueError:
        return None, "result_json_malformed"
    if not isinstance(payload, Mapping):
        return None, "result_json_malformed"
    receipt = payload.get("decision_receipt")
    receipt = receipt if isinstance(receipt, Mapping) else {}
    if (
        record.result_occurrence_id is None
        or receipt.get("result_occurrence_id") != record.result_occurrence_id
        or record.decision_receipt_digest is None
        or receipt.get("receipt_digest") != record.decision_receipt_digest
    ):
        return None, "result_json_occurrence_mismatch"
    if not (
        payload.get("function1_name")
        == payload.get("function2_name")
        == record.function_name
    ):
        return None, "result_json_function_mismatch"
    for side, expected in (
        ("binary1_content_identity", record.left_binary_sha256),
        ("binary2_content_identity", record.right_binary_sha256),
    ):
        identity = payload.get(side)
        digest = (
            identity[1]
            if isinstance(identity, (list, tuple)) and len(identity) == 2
            else None
        )
        if (
            normalized_sha256(digest) is None
            or normalized_sha256(digest) != normalized_sha256(expected)
        ):
            return None, "result_json_binary_mismatch"
    if payload.get("final_outcome") != record.outcome:
        return None, "result_json_outcome_mismatch"
    return payload, "ok"


def _identity_evidence_verdict(
    record: PairOutcome, payload: Optional[Mapping[str, Any]],
) -> Tuple[str, str]:
    """Is this identical-input pair *confirmed* to be one and the same function?

    The evidence is the checker's own observation of both Programs.  It is
    accepted only when both sides observed the same single function and each
    side's executable digest is the digest of that side's input binary.
    """

    if payload is None:
        return IDENTITY_UNVERIFIED, "result_json_unusable"
    evidence = payload.get(IDENTITY_EVIDENCE_KEY)
    if not isinstance(evidence, Mapping):
        return IDENTITY_UNVERIFIED, "identity_evidence_absent"
    if evidence.get("schema") != IDENTITY_EVIDENCE_SCHEMA:
        return IDENTITY_UNVERIFIED, "identity_evidence_schema_unknown"
    left, right = evidence.get("left"), evidence.get("right")
    if not isinstance(left, Mapping) or not isinstance(right, Mapping):
        return IDENTITY_UNVERIFIED, "identity_evidence_incomplete"
    if left != right:
        return IDENTITY_UNVERIFIED, "identity_evidence_differs"
    for side, expected in ((left, record.left_binary_sha256), (right, record.right_binary_sha256)):
        observed = normalized_sha256(side.get("executable_sha256"))
        if observed is None or observed != normalized_sha256(expected):
            return IDENTITY_UNVERIFIED, "identity_evidence_sha_mismatch"
        if side.get("function_name") != record.function_name:
            return IDENTITY_UNVERIFIED, "identity_evidence_function_mismatch"
        if side.get("match_count") != 1:
            return IDENTITY_UNVERIFIED, "identity_evidence_match_count"
    return IDENTITY_CONFIRMED, "ok"


# ---------------------------------------------------------------------------
# conditional column integrity + compatibility
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ConditionalView:
    present: bool
    outcome: Optional[str] = None
    integrity_error: Optional[str] = None
    premises: Tuple[Tuple[str, str], ...] = ()
    compatibility: Tuple[Tuple[str, str, str], ...] = ()

    @property
    def decisive(self) -> bool:
        """A decisive column, and one this reader was able to verify.

        A receipt that did not hold together is already a gate C violation; it
        must not also be read as a decision about the pair.
        """

        return self.integrity_error is None and self.outcome in DECISIVE_OUTCOMES

    @property
    def all_premises_verified(self) -> bool:
        return bool(self.compatibility) and all(
            status == COMPATIBILITY_VERIFIED for _kind, _subject, status in self.compatibility
        )


def _conditional_view(
    record: PairOutcome, compatibility: ConditionalCompatibility,
) -> ConditionalView:
    """Re-check the conditional column through the authority's own codec.

    Nothing here is a weaker restatement of the authority's rules: the receipt
    is rebuilt with ``conditional_decision_receipt_from_payload`` (which
    revalidates the digest, the canonical assumption set and every premise
    kind) and joined to this pair's own unconditional decision.
    """

    from scripts.function_tracer_pcode.authority.contracts import Outcome
    from scripts.function_tracer_pcode.authority.decision.conditional import (
        assumption_dependencies_digest,
        assumption_set_from_payload,
        conditional_decision_receipt_from_payload,
        validate_conditional_decision_join,
    )

    payload = record.conditional_decision_receipt
    if record.conditional_outcome is None and payload is None:
        return ConditionalView(present=False)
    if record.conditional_outcome is None or payload is None:
        return ConditionalView(
            present=True, integrity_error="conditional_column_half_written",
        )
    if record.outcome != "UNKNOWN":
        return ConditionalView(
            present=True,
            outcome=record.conditional_outcome,
            integrity_error="conditional_column_on_a_decided_pair",
        )
    try:
        receipt = conditional_decision_receipt_from_payload(payload)
        validate_conditional_decision_join(
            receipt,
            result_occurrence_id=record.result_occurrence_id,
            unconditional_outcome=Outcome(record.outcome),
            unconditional_receipt_digest=record.decision_receipt_digest,
        )
        if receipt.conditional_outcome.value != record.conditional_outcome:
            raise ValueError("conditional outcome contradicts its receipt")
        premises = assumption_set_from_payload(payload["assumption_set"])
        if assumption_dependencies_digest(premises) != receipt.assumption_set_digest:
            raise ValueError("assumption dependencies digest mismatch")
    except (TypeError, ValueError, KeyError) as exc:
        return ConditionalView(
            present=True,
            outcome=record.conditional_outcome,
            integrity_error=f"{type(exc).__name__}: {exc}",
        )
    observed = tuple(
        (premise.kind.value, premise.subject) for premise in receipt.assumption_set
    )
    return ConditionalView(
        present=True,
        outcome=record.conditional_outcome,
        premises=observed,
        compatibility=tuple(
            (
                kind,
                subject,
                compatibility.status(
                    record.sample_identity, record.function_name, kind, subject
                ),
            )
            for kind, subject in observed
        ),
    )


# ---------------------------------------------------------------------------
# classification
# ---------------------------------------------------------------------------


def _row(record: PairOutcome, scope: Scope, **extra: Any) -> Dict[str, Any]:
    row = {
        "sample_identity": record.sample_identity,
        "function_name": record.function_name,
        "pair_id": record.pair_id,
        "label": record.label,
        "outcome": record.outcome,
        "scope": scope.name,
        "mode": scope.mode.mode,
        "status_path": record.status_path,
    }
    row.update(extra)
    return row


@dataclass
class _Accumulator:
    unconditional_verified_violations: List[Dict[str, Any]] = field(default_factory=list)
    conditional_verified_violations: List[Dict[str, Any]] = field(default_factory=list)
    verified_rows: List[Dict[str, Any]] = field(default_factory=list)
    compatibility_unknown_rows: List[Dict[str, Any]] = field(default_factory=list)
    dataset_label_mismatch_rows: List[Dict[str, Any]] = field(default_factory=list)
    ground_truth_unverified_rows: List[Dict[str, Any]] = field(default_factory=list)
    manifest_lookup_error_rows: List[Dict[str, Any]] = field(default_factory=list)
    identical_rows: List[Dict[str, Any]] = field(default_factory=list)
    identical_soundness_violations: List[Dict[str, Any]] = field(default_factory=list)
    fast_path_violations: List[Dict[str, Any]] = field(default_factory=list)
    fast_path_not_applicable_rows: List[Dict[str, Any]] = field(default_factory=list)
    identity_unverified_rows: List[Dict[str, Any]] = field(default_factory=list)
    oracle_rows: List[Dict[str, Any]] = field(default_factory=list)
    config_integrity_violations: List[Dict[str, Any]] = field(default_factory=list)


def _classify_ground_truth(
    record: PairOutcome, scope: Scope, conditional: ConditionalView, acc: _Accumulator,
) -> None:
    """A0 / A0c / A0u / B0: what a *verified* relation says about this pair."""

    if scope.manifest is None:
        fact, reason = None, scope.ground_truth
    else:
        fact, reason = scope.manifest.lookup(
            record.sample_identity, record.function_name
        )
    truth = fact.semantic_ground_truth if fact is not None else None
    verified = truth in FORBIDDEN_BY_TRUTH

    for column, outcome in (
        ("unconditional", record.outcome),
        ("conditional", conditional.outcome if conditional.decisive else None),
    ):
        if outcome not in DECISIVE_OUTCOMES:
            continue
        if verified and FORBIDDEN_BY_TRUTH[truth] == outcome:
            row = _row(
                record, scope, column=column, column_outcome=outcome,
                ground_truth=truth,
                ground_truth_evidence=fact.ground_truth_evidence,
            )
            if column == "unconditional":
                acc.unconditional_verified_violations.append(row)
            elif conditional.all_premises_verified:
                acc.conditional_verified_violations.append({
                    **row, "assumption_compatibility": list(conditional.compatibility),
                })
            else:
                acc.compatibility_unknown_rows.append({
                    **row,
                    "assumption_compatibility": list(conditional.compatibility),
                    "detail": "a reviewed relation is contradicted only under"
                              " premises whose compatibility is not verified",
                })
            continue
        if verified:
            acc.verified_rows.append(
                _row(record, scope, column=column, column_outcome=outcome,
                     ground_truth=truth, consistent=True)
            )
            continue
        # Not verified for this function: the dataset directory may still
        # disagree with the decision, which is an investigation, not a proof.
        if MISMATCHED_BY_LABEL.get(record.label) == outcome:
            acc.dataset_label_mismatch_rows.append(
                _row(record, scope, column=column, column_outcome=outcome,
                     lookup=reason, ground_truth=truth)
            )
        if fact is None:
            acc.manifest_lookup_error_rows.append(
                _row(record, scope, column=column, column_outcome=outcome, lookup=reason)
            )
        else:
            acc.ground_truth_unverified_rows.append(
                _row(record, scope, column=column, column_outcome=outcome,
                     ground_truth=truth)
            )


def _classify_identical_input(
    record: PairOutcome, scope: Scope, acc: _Accumulator,
) -> None:
    """A / B: byte-identical inputs, and whether the fast path accepted them."""

    if not record.identical_input:
        return
    payload, payload_reason = read_result_payload(record)
    identity, identity_reason = _identity_evidence_verdict(record, payload)
    disposition = payload.get(DISPOSITION_KEY) if isinstance(payload, Mapping) else None
    disposition = disposition if isinstance(disposition, Mapping) else None
    row = _row(
        record, scope, identity=identity, identity_detail=identity_reason,
        result_json=payload_reason,
        disposition=dict(disposition) if disposition is not None else None,
    )
    acc.identical_rows.append(row)

    # A: independent of the mode.  Byte identity is not configuration.
    if identity == IDENTITY_CONFIRMED and record.outcome == OUTCOME_NOT_EQ:
        acc.identical_soundness_violations.append(row)
    if identity != IDENTITY_CONFIRMED:
        acc.identity_unverified_rows.append(row)

    # B: only a run that says it had the fast path on can fail to accept.
    if scope.mode.mode == MODE_OFF:
        if disposition is not None and disposition.get("applied") is True:
            # The run manifest and the results disagree about what was run.
            # Neither can then be believed, so this fails closed rather than
            # being filed as an oracle row.
            acc.config_integrity_violations.append({
                **row, "kind": "fast_path_applied_in_an_off_run",
                "detail": "run_manifest says off, the result says applied",
            })
        acc.oracle_rows.append(row)
        return
    if scope.mode.mode != MODE_ON:
        return
    if disposition is None:
        acc.fast_path_violations.append({**row, "violation_kind": "unverifiable"})
        return
    if disposition.get("applicable") is not True:
        acc.fast_path_not_applicable_rows.append(row)
        return
    if disposition.get("applied") is not True:
        acc.fast_path_violations.append({**row, "violation_kind": "not_applied"})
    elif record.outcome != OUTCOME_EQ:
        acc.fast_path_violations.append({**row, "violation_kind": "not_equivalent"})


# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class GateReport:
    records: Tuple[PairOutcome, ...]
    scopes: Tuple[Scope, ...]
    accumulator: _Accumulator
    compatibility: ConditionalCompatibility = EMPTY_COMPATIBILITY

    @property
    def counts(self) -> Counter:
        return Counter((record.label, record.outcome) for record in self.records)

    @property
    def mode_by_scope(self) -> Dict[str, Dict[str, Any]]:
        return {
            scope.name: {
                "mode": scope.mode.mode,
                "detail": scope.mode.detail,
                "run_manifest": scope.mode.manifest_path,
                "ground_truth": scope.ground_truth,
            }
            for scope in self.scopes
        }

    @property
    def counts_by_mode(self) -> Dict[str, int]:
        counts: Counter = Counter()
        for row in self.accumulator.identical_rows:
            counts[row["mode"]] += 1
        return dict(sorted(counts.items()))

    @property
    def passed(self) -> bool:
        acc = self.accumulator
        return bool(self.records) and not (
            acc.unconditional_verified_violations
            or acc.conditional_verified_violations
            or acc.identical_soundness_violations
            or acc.fast_path_violations
            or acc.config_integrity_violations
        )

    @property
    def exit_code(self) -> int:
        if not self.records:
            return EXIT_EMPTY
        return EXIT_PASS if self.passed else EXIT_VIOLATION

    def as_dict(self) -> Dict[str, Any]:
        acc = self.accumulator
        return {
            "schema": GATE_SCHEMA,
            "pairs": len(self.records),
            "passed": self.passed,
            "exit_code": self.exit_code,
            "roots": sorted({scope.root for scope in self.scopes}),
            "mode_by_root": self.mode_by_scope,
            "metadata": {
                "compatibility_file": self.compatibility.path,
                "compatibility_sha256": self.compatibility.sha256,
            },
            "counts": [
                {"label": label, "outcome": outcome, "count": count}
                for (label, outcome), count in sorted(self.counts.items())
            ],
            "verified_ground_truth": {
                "unconditional_violations": acc.unconditional_verified_violations,
                "conditional_violations": acc.conditional_verified_violations,
                "rows": acc.verified_rows,
            },
            "conditional_compatibility": {
                "unknown_rows": acc.compatibility_unknown_rows,
            },
            "dataset_label": {
                "mismatch_rows": acc.dataset_label_mismatch_rows,
                "unverified_rows": acc.ground_truth_unverified_rows,
                "lookup_error_rows": acc.manifest_lookup_error_rows,
            },
            "identical_input": {
                "rows": acc.identical_rows,
                "soundness_violations": acc.identical_soundness_violations,
                "fast_path_violations": acc.fast_path_violations,
                "not_applicable_rows": acc.fast_path_not_applicable_rows,
                "unverified_rows": acc.identity_unverified_rows,
                "oracle_rows": acc.oracle_rows,
                "counts_by_mode": self.counts_by_mode,
            },
            "config_integrity": {"violations": acc.config_integrity_violations},
        }


def build_gate_report(
    roots: Sequence[Path], *, compatibility_path: Optional[Path] = None,
) -> GateReport:
    acc = _Accumulator()
    compatibility = EMPTY_COMPATIBILITY
    path = DEFAULT_COMPATIBILITY_PATH if compatibility_path is None else compatibility_path
    try:
        compatibility = load_conditional_compatibility(path)
    except (OSError, ValueError) as exc:
        acc.config_integrity_violations.append({
            "kind": "conditional_compatibility_unreadable",
            "detail": f"{path}: {exc}",
        })

    records: List[PairOutcome] = []
    scopes: List[Scope] = []
    for root in roots:
        resolver = _ScopeResolver(Path(root))
        for record in iter_pair_outcomes(Path(root)):
            records.append(record)
            scope = resolver.for_half(record.half)
            conditional = _conditional_view(record, compatibility)
            if conditional.integrity_error is not None:
                acc.config_integrity_violations.append(
                    _row(record, scope, kind="conditional_column_invalid",
                         detail=conditional.integrity_error)
                )
            _classify_ground_truth(record, scope, conditional, acc)
            _classify_identical_input(record, scope, acc)
        for scope in resolver.scopes:
            scopes.append(scope)
            if scope.mode.mode == MODE_INVALID:
                acc.config_integrity_violations.append({
                    "kind": "analysis_config_invalid",
                    "scope": scope.name,
                    "detail": scope.mode.detail,
                })
            if scope.manifest is None and scope.ground_truth.startswith("unreadable"):
                acc.config_integrity_violations.append({
                    "kind": "ground_truth_unreadable",
                    "scope": scope.name,
                    "detail": scope.ground_truth,
                })
    return GateReport(
        records=tuple(records),
        scopes=tuple(scopes),
        accumulator=acc,
        compatibility=compatibility,
    )


def _format_counts(report: GateReport) -> List[str]:
    counts = report.counts
    labels = [
        label for label in (LABEL_EQ, LABEL_NEQ, LABEL_UNLABELLED)
        if any(key[0] == label for key in counts)
    ]
    outcomes = [name for name in OUTCOME_ORDER if any(key[1] == name for key in counts)]
    outcomes.extend(sorted({key[1] for key in counts} - set(OUTCOME_ORDER)))
    if not labels:
        return []
    width = max([len("label")] + [len(name) for name in outcomes + labels])
    lines = ["Outcomes by benchmark label:"]
    lines.append("label".ljust(width) + "".join(name.rjust(width + 2) for name in outcomes))
    for label in labels:
        lines.append(
            label.ljust(width)
            + "".join(
                str(counts.get((label, outcome), 0)).rjust(width + 2)
                for outcome in outcomes
            )
        )
    return lines + [""]


#: The row fields worth printing, most specific first.  A row carries only
#: some of them, and a scope-level row carries none of the pair fields.
_ROW_DETAIL_FIELDS = (
    "detail", "violation_kind", "kind", "lookup", "identity_detail", "ground_truth",
)


def _format_rows(title: str, rows: Sequence[Mapping[str, Any]]) -> List[str]:
    if not rows:
        return []
    lines = [f"{title} ({len(rows)}):"]
    for row in rows:
        identity = " ".join(
            str(row[name]) for name in ("sample_identity", "function_name", "pair_id")
            if row.get(name)
        ) or str(row.get("scope", ""))
        outcome = row.get("column_outcome") or row.get("outcome") or ""
        detail = next(
            (str(row[name]) for name in _ROW_DETAIL_FIELDS if row.get(name)), "",
        )
        lines.append(f"  {identity}: {outcome} {detail}".rstrip())
    return lines + [""]


def format_gate_report(report: GateReport) -> str:
    acc = report.accumulator
    lines = [f"Pairs checked: {len(report.records)}", ""]
    lines.extend(_format_counts(report))
    lines.append("Run mode by scope:")
    for name, info in report.mode_by_scope.items():
        lines.append(f"  {name}: {info['mode']} ({info['detail']})")
    lines.append("")
    if report.compatibility.path is not None:
        lines.append(
            f"Conditional compatibility: {report.compatibility.path} "
            f"sha256={report.compatibility.sha256}"
        )
        lines.append("")
    lines.extend(_format_rows(
        "Verified ground-truth violations (unconditional)",
        acc.unconditional_verified_violations,
    ))
    lines.extend(_format_rows(
        "Verified ground-truth violations (conditional, every premise verified)",
        acc.conditional_verified_violations,
    ))
    lines.extend(_format_rows(
        "Identical-input same-function violations", acc.identical_soundness_violations,
    ))
    lines.extend(_format_rows("Fast-path acceptance violations", acc.fast_path_violations))
    lines.extend(_format_rows("Config / integrity violations", acc.config_integrity_violations))
    lines.append(
        "Identical-input pairs: "
        f"{len(acc.identical_rows)} (by mode: {report.counts_by_mode}; "
        f"oracle {len(acc.oracle_rows)}, identity unverified "
        f"{len(acc.identity_unverified_rows)}, fast path not applicable "
        f"{len(acc.fast_path_not_applicable_rows)})"
    )
    lines.append(
        "Investigation (not violations): dataset-label mismatch "
        f"{len(acc.dataset_label_mismatch_rows)}, ground truth unverified "
        f"{len(acc.ground_truth_unverified_rows)}, manifest lookup errors "
        f"{len(acc.manifest_lookup_error_rows)}, conditional compatibility unknown "
        f"{len(acc.compatibility_unknown_rows)}"
    )
    lines.append("")
    if not report.records:
        lines.append("GATE: EMPTY (no pair status found)")
    elif report.passed:
        lines.append("GATE: PASS")
    else:
        lines.append(
            "GATE: FAIL ("
            f"{len(acc.unconditional_verified_violations)} verified ground truth, "
            f"{len(acc.conditional_verified_violations)} conditional, "
            f"{len(acc.identical_soundness_violations)} identical same-function, "
            f"{len(acc.fast_path_violations)} fast path, "
            f"{len(acc.config_integrity_violations)} config/integrity)"
        )
    return "\n".join(lines) + "\n"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("roots", nargs="+", type=Path, help="result trees to check")
    parser.add_argument(
        "--json", type=Path, default=None, help="write the report as JSON to this path",
    )
    parser.add_argument(
        "--conditional-compatibility", type=Path, default=None,
        help=(
            "ground-truth conditional compatibility metadata "
            f"(default: {DEFAULT_COMPATIBILITY_PATH})"
        ),
    )
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    for root in args.roots:
        if not root.is_dir():
            print(f"error: not a directory: {root}", file=sys.stderr)
            return EXIT_EMPTY
    report = build_gate_report(
        args.roots, compatibility_path=args.conditional_compatibility,
    )
    if args.json is not None:
        args.json.write_text(
            json.dumps(report.as_dict(), indent=1, default=str) + "\n", encoding="utf-8",
        )
    sys.stdout.write(format_gate_report(report))
    return report.exit_code


if __name__ == "__main__":
    sys.exit(main())
