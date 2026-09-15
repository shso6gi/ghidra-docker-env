# -*- coding: utf-8 -*-
"""Issue #15 PR-15-B: the shared soundness gate decides on verified relations.

The gate used to read the dataset directory alone: an ``Eq`` sample judged
``NOT_EQ`` was a soundness violation whatever the manifest said, and a ``Neq``
sample judged ``EQUIVALENT`` likewise.  That conflates "the benchmark filed
these two sources apart" with "these two functions are known to differ".

v2 fixes the authority of each verdict:

* a violation needs a **function-level** reviewed relation, looked up for the
  pair's own ``(sample, function)`` -- for ``Eq`` samples too;
* a contradiction in the assumption-dependent column counts only when every
  premise of that pair's receipt is recorded as compatible with the relation;
* everything else -- an unregistered function, an ``UNKNOWN`` verdict, a
  dataset-label mismatch, an unverified premise -- is an investigation row and
  never flips the verdict;
* identical inputs (gate A) and fast-path acceptance (gate B) and the run's own
  configuration (gate C) are judged independently of all of that.

These tests fix that contract.  Nothing here hand-writes a conditional receipt:
every conditional column comes from a real ``ConditionalDecisionReceipt``
issued against a real unconditional ``UNKNOWN`` decision.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.contracts import (
    Outcome,
    VerifiedLifecycleProjection,
)
from scripts.function_tracer_pcode.authority.decision.conditional import (
    ConditionalDecisiveProofKind,
    ConditionalDecisiveProofReceipt,
    ConditionalFinalizationAuthority,
    canonical_assumption_dependencies,
    conditional_decision_receipt_payload,
    finalize_conditional_decision,
)
from scripts.function_tracer_pcode.proof.assumptions import (
    AssumptionKind,
    AssumptionPremise,
)
from scripts.function_tracer_pcode.reporting import soundness_gate

from scripts.function_tracer_pcode.tests.unit.test_conditional_signed_pair_status import (
    _unknown_pilot,
)

EQ = "airy/Sign/Eq/newV"
NEQ = "raytrace/sphere/Neq/newV-oldV"
SHA_A = "a" * 64
SHA_B = "b" * 64
COMPAT_KIND = "EXTERNAL_CALLEE_SPEC"


# ---------------------------------------------------------------------------
# a run tree, written the way the runners write one
# ---------------------------------------------------------------------------


def write_pair_status(
    root: Path,
    sample: str,
    function: str,
    left: str,
    right: str,
    outcome: str,
    *,
    left_sha: str = SHA_A,
    right_sha: str = SHA_B,
    occurrence: str = "production-pilot-test",
    receipt_digest: str = "d" * 64,
    conditional=None,
) -> Path:
    path = root / sample / function / f"{function}_{left}_{right}.pair-status.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "canonical_outcome": outcome,
        "result_occurrence_id": occurrence,
        "decision_receipt_digest": receipt_digest,
        "pair_execution_target": {
            "sample_identity": sample,
            "function_name": function,
            "left_binary_id": left,
            "right_binary_id": right,
            "left_binary_sha256": left_sha,
            "right_binary_sha256": right_sha,
        },
    }
    if conditional is not None:
        payload["conditional_outcome"] = conditional["conditional_outcome"]
        payload["conditional_decision_receipt"] = conditional
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def write_result_json(
    root: Path,
    sample: str,
    function: str,
    left: str,
    right: str,
    outcome: str,
    *,
    left_sha: str = SHA_A,
    right_sha: str = SHA_B,
    occurrence: str = "production-pilot-test",
    receipt_digest: str = "d" * 64,
    evidence=None,
    disposition=None,
    function_names=None,
) -> Path:
    name1, name2 = function_names or (function, function)
    payload = {
        "function1_name": name1,
        "function2_name": name2,
        "binary1_content_identity": ["sha256", left_sha],
        "binary2_content_identity": ["sha256", right_sha],
        "final_outcome": outcome,
        "decision_receipt": {
            "result_occurrence_id": occurrence,
            "receipt_digest": receipt_digest,
            "outcome": outcome,
        },
    }
    if evidence is not None:
        payload["identical_function_identity_evidence"] = evidence
    if disposition is not None:
        payload["identical_fast_path_disposition"] = disposition
    path = root / sample / function / f"{function}_{left}_{right}.log"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "noise\n"
        f"{soundness_gate.RESULT_JSON_BEGIN}\n{json.dumps(payload)}\n"
        f"{soundness_gate.RESULT_JSON_END}\n",
        encoding="utf-8",
    )
    return path


def identity_evidence(
    *, sha: str = SHA_A, function: str = "snippet", match_count: int = 1,
):
    side = {
        "executable_sha256": sha,
        "function_name": function,
        "language_id": "AARCH64:LE:64:v8A",
        "compiler_spec_id": "default",
        "image_base": 0x100000,
        "entry": ["ram", 0x100000],
        "body_range": [["ram", 0x100000], ["ram", 0x100020]],
        "match_count": match_count,
    }
    return {
        "schema": soundness_gate.IDENTITY_EVIDENCE_SCHEMA,
        "left": side,
        "right": dict(side),
    }


def write_run_manifest(directory: Path, **fields) -> Path:
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / soundness_gate.RUN_MANIFEST_FILE
    path.write_text(
        "".join(f"{key}={value}\n" for key, value in fields.items()), encoding="utf-8",
    )
    return path


def write_ground_truth(directory: Path, facts, *, evidence="witness input 1 -> 2 / 0") -> Path:
    """``{sample: {function: verdict}}`` as the runner's manifest writes it."""

    directory.mkdir(parents=True, exist_ok=True)
    path = directory / soundness_gate.GROUND_TRUTH_FILE
    path.write_text(
        json.dumps({
            "schema": "eqbench-function-diff-manifest-v1",
            "samples": {
                sample: {
                    "parse_status": "ok",
                    "functions": {
                        function: {
                            "source_relation": "SOURCE_CHANGED",
                            "source_impact": "DIRECTLY_CHANGED",
                            "semantic_ground_truth": verdict,
                            "ground_truth_evidence": evidence,
                        }
                        for function, verdict in functions.items()
                    },
                }
                for sample, functions in facts.items()
            },
        }),
        encoding="utf-8",
    )
    return path


VERIFIED_FIELDS = {
    "evidence": "native run of the witness input with the callee's catalog value",
    "verified_by": "reviewer",
    "verified_at": "2026-09-15T00:00:00Z",
}
UNVERIFIED_FIELDS = {"evidence": "none", "verified_by": None, "verified_at": None}


def compatibility_entry(sample, function, kind, subject, status, **overrides):
    """One entry with exactly the fields its status requires."""

    row = {
        "sample": sample, "function": function,
        "assumption_kind": kind, "subject": subject, "status": status,
        **(VERIFIED_FIELDS if status == "verified" else UNVERIFIED_FIELDS),
    }
    row.update(overrides)
    return {name: value for name, value in row.items() if value is not _DROP}


class _Drop:
    pass


_DROP = _Drop()


def write_compatibility(path: Path, entries, **file_overrides) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema": soundness_gate.COMPATIBILITY_SCHEMA,
        "entries": [
            compatibility_entry(*entry) if isinstance(entry, tuple) else entry
            for entry in entries
        ],
    }
    payload.update(file_overrides)
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def build(roots, compatibility=None):
    return soundness_gate.build_gate_report(
        [Path(root) for root in roots], compatibility_path=compatibility,
    )


@pytest.fixture
def empty_compatibility(tmp_path_factory):
    """No entry is verified -- the state the repository actually ships."""

    return write_compatibility(
        tmp_path_factory.mktemp("compat") / "none.json", [],
    )


# ---------------------------------------------------------------------------
# real conditional receipts
# ---------------------------------------------------------------------------


_PILOTS = {}


def conditional_column(case: str, outcome: Outcome, subjects=("log",)):
    """A real conditional receipt for one real unconditional UNKNOWN pair.

    Returns ``(receipt payload, result_occurrence_id, unconditional digest)``.
    """

    if case not in _PILOTS:
        _PILOTS[case] = _unknown_pilot(case)
    _session, _evidence, decision = _PILOTS[case]
    result_id = decision.result_occurrence_id
    projection = VerifiedLifecycleProjection.seal(
        result_occurrence_id=result_id,
        snapshot_digest=f"conditional-snapshot-{case}",
        c_active_base=(), q_open_base=(), blocker_eligibility_base=(),
        satisfaction_projection={"live": ()},
    )
    premises = canonical_assumption_dependencies(tuple(
        AssumptionPremise(
            kind=AssumptionKind.EXTERNAL_CALLEE_SPEC, subject=subject,
            payload={"canonical_symbol": subject, "no_observable_memory_write": True},
        )
        for subject in subjects
    ))
    proof = ConditionalDecisiveProofReceipt.create(
        result_occurrence_id=result_id,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        proof_kind=(
            ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE
            if outcome is Outcome.EQUIVALENT
            else ConditionalDecisiveProofKind.CONDITIONAL_SAFE_COUNTEREXAMPLE
        ),
        proof_artifact_digest=f"conditional-proof-{case}",
        assumption_dependencies=premises,
    )
    receipt = finalize_conditional_decision(ConditionalFinalizationAuthority(
        result_id, decision, projection, premises,
        conditional_decisive_proof_receipts=(proof,),
    ))
    assert receipt.conditional_outcome is outcome
    return (
        conditional_decision_receipt_payload(receipt),
        result_id,
        decision.receipt_digest,
    )


def write_conditional_pair(
    root: Path, sample: str, function: str, case: str, outcome: Outcome,
    *, subjects=("log",), unconditional: str = "UNKNOWN",
):
    payload, result_id, digest = conditional_column(case, outcome, subjects)
    write_pair_status(
        root, sample, function, "B1", "B2", unconditional,
        occurrence=result_id, receipt_digest=digest, conditional=payload,
    )
    return payload


# ---------------------------------------------------------------------------
# A0: verified unconditional ground truth (matrix rows 1-9)
# ---------------------------------------------------------------------------


def test_an_eq_sample_not_eq_is_a_violation_only_when_the_lookup_confirms_it(
    tmp_path, empty_compatibility,
):
    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "NOT_EQ")
    write_ground_truth(tmp_path, {EQ: {"snippet": "CONFIRMED_EQ"}})

    report = build([tmp_path], empty_compatibility)

    violations = report.accumulator.unconditional_verified_violations
    assert [(row["pair_id"], row["ground_truth"]) for row in violations] == [
        ("B1_B2", "CONFIRMED_EQ"),
    ]
    assert report.passed is False
    assert report.exit_code == soundness_gate.EXIT_VIOLATION


@pytest.mark.parametrize("facts,lookup", [
    pytest.param({"other/sample/Eq/newV": {"snippet": "CONFIRMED_EQ"}},
                 "sample_not_in_manifest", id="sample-missing"),
    pytest.param({EQ: {"other": "CONFIRMED_EQ"}},
                 "function_not_in_manifest", id="function-missing"),
    pytest.param(None, "absent", id="no-manifest"),
])
def test_an_unregistered_eq_function_is_an_investigation_not_a_violation(
    tmp_path, empty_compatibility, facts, lookup,
):
    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "NOT_EQ")
    if facts is not None:
        write_ground_truth(tmp_path, facts)

    report = build([tmp_path], empty_compatibility)
    acc = report.accumulator

    assert acc.unconditional_verified_violations == []
    assert [row["lookup"] for row in acc.dataset_label_mismatch_rows] == [lookup]
    assert [row["lookup"] for row in acc.manifest_lookup_error_rows] == [lookup]
    assert report.passed is True


def test_an_unknown_verdict_is_not_a_verified_relation(tmp_path, empty_compatibility):
    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "NOT_EQ")
    write_ground_truth(tmp_path, {EQ: {"snippet": "UNKNOWN"}})

    report = build([tmp_path], empty_compatibility)
    acc = report.accumulator

    assert acc.unconditional_verified_violations == []
    assert len(acc.dataset_label_mismatch_rows) == 1
    assert [row["ground_truth"] for row in acc.ground_truth_unverified_rows] == ["UNKNOWN"]
    assert acc.manifest_lookup_error_rows == []
    assert report.passed is True


@pytest.mark.parametrize("outcome,verdict", [
    ("EQUIVALENT", "CONFIRMED_NOT_EQ"),
    ("NOT_EQ", "CONFIRMED_EQ"),
])
def test_a_neq_pair_violates_its_own_reviewed_relation_in_both_directions(
    tmp_path, empty_compatibility, outcome, verdict,
):
    write_pair_status(tmp_path, NEQ, "SphereConstructor", "N_B1", "O_B2", outcome)
    write_ground_truth(tmp_path, {NEQ: {"SphereConstructor": verdict}})

    report = build([tmp_path], empty_compatibility)

    assert len(report.accumulator.unconditional_verified_violations) == 1
    assert report.passed is False


def test_an_unmapped_neq_equivalent_is_an_investigation_here(
    tmp_path, empty_compatibility,
):
    """``benchmark_validation_gate`` fails closed on this; the shared gate does not.

    The two gates answer different questions and the runner requires both.
    """

    write_pair_status(tmp_path, NEQ, "SphereConstructor", "N_B1", "O_B2", "EQUIVALENT")
    write_ground_truth(tmp_path, {NEQ: {"SphereConstructor": "UNKNOWN"}})

    report = build([tmp_path], empty_compatibility)

    assert report.accumulator.unconditional_verified_violations == []
    assert len(report.accumulator.dataset_label_mismatch_rows) == 1
    assert report.passed is True


# ---------------------------------------------------------------------------
# A0c / A0u: the conditional column (matrix rows 10-13, 16)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("verdict,conditional,case", [
    ("CONFIRMED_NOT_EQ", Outcome.EQUIVALENT, "cond-eq"),
    ("CONFIRMED_EQ", Outcome.NOT_EQ, "cond-not-eq"),
])
def test_a_conditional_contradiction_counts_only_with_every_premise_verified(
    tmp_path, verdict, conditional, case,
):
    write_conditional_pair(tmp_path, NEQ, "SphereConstructor", case, conditional)
    write_ground_truth(tmp_path, {NEQ: {"SphereConstructor": verdict}})
    compat = write_compatibility(
        tmp_path / "compat.json",
        [(NEQ, "SphereConstructor", COMPAT_KIND, "log", "verified")],
    )

    report = build([tmp_path], compat)
    acc = report.accumulator

    assert acc.unconditional_verified_violations == []
    assert len(acc.conditional_verified_violations) == 1
    row = acc.conditional_verified_violations[0]
    assert row["column"] == "conditional"
    assert row["column_outcome"] == conditional.value
    assert row["assumption_compatibility"] == [(COMPAT_KIND, "log", "verified")]
    assert report.passed is False


@pytest.mark.parametrize("status", ["unverified", "not_applicable", None])
def test_an_unverified_premise_leaves_the_contradiction_an_investigation(
    tmp_path, status,
):
    write_conditional_pair(
        tmp_path, NEQ, "SphereConstructor", f"cond-unver-{status}", Outcome.EQUIVALENT,
    )
    write_ground_truth(tmp_path, {NEQ: {"SphereConstructor": "CONFIRMED_NOT_EQ"}})
    entries = (
        [] if status is None
        else [(NEQ, "SphereConstructor", COMPAT_KIND, "log", status)]
    )
    compat = write_compatibility(tmp_path / "compat.json", entries)

    report = build([tmp_path], compat)
    acc = report.accumulator

    assert acc.conditional_verified_violations == []
    assert len(acc.compatibility_unknown_rows) == 1
    observed = acc.compatibility_unknown_rows[0]["assumption_compatibility"]
    assert observed == [(COMPAT_KIND, "log", status or "unknown")]
    assert report.passed is True


def test_one_verified_premise_among_several_is_not_enough(tmp_path):
    write_conditional_pair(
        tmp_path, NEQ, "SphereConstructor", "cond-multi", Outcome.EQUIVALENT,
        subjects=("log", "sin"),
    )
    write_ground_truth(tmp_path, {NEQ: {"SphereConstructor": "CONFIRMED_NOT_EQ"}})
    compat = write_compatibility(
        tmp_path / "compat.json",
        [(NEQ, "SphereConstructor", COMPAT_KIND, "log", "verified")],
    )

    report = build([tmp_path], compat)
    acc = report.accumulator

    assert acc.conditional_verified_violations == []
    assert len(acc.compatibility_unknown_rows) == 1
    assert sorted(acc.compatibility_unknown_rows[0]["assumption_compatibility"]) == [
        (COMPAT_KIND, "log", "verified"),
        (COMPAT_KIND, "sin", "unknown"),
    ]
    assert report.passed is True


def test_a_subject_wildcard_covers_a_premise_the_table_does_not_name(tmp_path):
    write_conditional_pair(
        tmp_path, NEQ, "SphereConstructor", "cond-wildcard", Outcome.EQUIVALENT,
        subjects=("sqrtf",),
    )
    write_ground_truth(tmp_path, {NEQ: {"SphereConstructor": "CONFIRMED_NOT_EQ"}})
    compat = write_compatibility(
        tmp_path / "compat.json",
        [(NEQ, "SphereConstructor", COMPAT_KIND, "*", "verified")],
    )

    report = build([tmp_path], compat)

    assert len(report.accumulator.conditional_verified_violations) == 1


def test_an_unregistered_relation_keeps_a_conditional_decision_an_investigation(
    tmp_path,
):
    write_conditional_pair(
        tmp_path, NEQ, "SphereConstructor", "cond-unregistered", Outcome.EQUIVALENT,
    )
    write_ground_truth(tmp_path, {NEQ: {"SphereConstructor": "UNKNOWN"}})
    compat = write_compatibility(
        tmp_path / "compat.json",
        [(NEQ, "SphereConstructor", COMPAT_KIND, "*", "verified")],
    )

    report = build([tmp_path], compat)
    acc = report.accumulator

    assert acc.conditional_verified_violations == []
    assert acc.compatibility_unknown_rows == []
    assert len(acc.dataset_label_mismatch_rows) == 1
    assert report.passed is True


# ---------------------------------------------------------------------------
# C: configuration and integrity (matrix rows 14, 15, 17, 19, 20, 27)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("break_receipt", [
    pytest.param(lambda r: {**r, "assumption_set": []}, id="empty-assumption-set"),
    pytest.param(lambda r: {**r, "assumption_set_digest": "0" * 64}, id="set-digest"),
    pytest.param(lambda r: {**r, "receipt_digest": "0" * 64}, id="receipt-digest"),
    pytest.param(
        lambda r: {
            **r,
            "assumption_set": [
                {**r["assumption_set"][0], "kind": "NO_SUCH_ASSUMPTION_KIND"}
            ],
        },
        id="unknown-kind",
    ),
    pytest.param(lambda r: {k: v for k, v in r.items() if k != "authority_input_digest"},
                 id="missing-field"),
])
def test_a_malformed_conditional_receipt_fails_the_gate_closed(
    tmp_path, empty_compatibility, break_receipt,
):
    payload, result_id, digest = conditional_column("cond-malformed", Outcome.EQUIVALENT)
    write_pair_status(
        tmp_path, NEQ, "SphereConstructor", "B1", "B2", "UNKNOWN",
        occurrence=result_id, receipt_digest=digest,
        conditional={**break_receipt(payload),
                     "conditional_outcome": payload["conditional_outcome"]},
    )
    write_ground_truth(tmp_path, {NEQ: {"SphereConstructor": "CONFIRMED_NOT_EQ"}})

    report = build([tmp_path], empty_compatibility)

    assert len(report.accumulator.config_integrity_violations) == 1
    assert report.accumulator.config_integrity_violations[0]["kind"] == (
        "conditional_column_invalid"
    )
    assert report.passed is False


def test_a_malformed_conditional_column_is_not_also_read_as_a_decision(tmp_path):
    """A receipt that did not hold together says nothing about the pair.

    It is a gate C violation; it must not additionally become a conditional
    ground-truth violation, however permissive the compatibility table is.
    """

    payload, result_id, digest = conditional_column("cond-not-a-column", Outcome.EQUIVALENT)
    write_pair_status(
        tmp_path, NEQ, "SphereConstructor", "B1", "B2", "UNKNOWN",
        occurrence=result_id, receipt_digest=digest,
        conditional={**payload, "receipt_digest": "0" * 64},
    )
    write_ground_truth(tmp_path, {NEQ: {"SphereConstructor": "CONFIRMED_NOT_EQ"}})
    compat = write_compatibility(
        tmp_path / "compat.json",
        [(NEQ, "SphereConstructor", COMPAT_KIND, "*", "verified")],
    )

    report = build([tmp_path], compat)
    acc = report.accumulator

    assert len(acc.config_integrity_violations) == 1
    assert acc.conditional_verified_violations == []
    assert acc.compatibility_unknown_rows == []
    assert report.passed is False


def test_a_conditional_receipt_from_another_pair_is_refused(
    tmp_path, empty_compatibility,
):
    payload, _result_id, _digest = conditional_column("cond-foreign", Outcome.EQUIVALENT)
    write_pair_status(
        tmp_path, NEQ, "SphereConstructor", "B1", "B2", "UNKNOWN",
        occurrence="production-pilot-someone-else", receipt_digest="e" * 64,
        conditional=payload,
    )

    report = build([tmp_path], empty_compatibility)

    assert len(report.accumulator.config_integrity_violations) == 1
    assert report.passed is False


def test_a_conditional_column_on_a_decided_pair_is_an_integrity_failure(
    tmp_path, empty_compatibility,
):
    payload, result_id, digest = conditional_column("cond-decided", Outcome.EQUIVALENT)
    write_pair_status(
        tmp_path, NEQ, "SphereConstructor", "B1", "B2", "NOT_EQ",
        occurrence=result_id, receipt_digest=digest, conditional=payload,
    )

    report = build([tmp_path], empty_compatibility)

    assert [row["detail"] for row in report.accumulator.config_integrity_violations] == [
        "conditional_column_on_a_decided_pair",
    ]
    assert report.passed is False


@pytest.mark.parametrize("evidence", [None, "", "   "])
def test_a_reviewed_relation_without_its_evidence_fails_the_gate(
    tmp_path, empty_compatibility, evidence,
):
    """A relation is an authority claim, and a claim needs what was checked.

    Without the evidence column the entry cannot be called verified -- but
    silently demoting it to an investigation would hide a violation, so the
    broken artifact fails the gate instead.
    """

    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "NOT_EQ")
    write_ground_truth(tmp_path, {EQ: {"snippet": "CONFIRMED_EQ"}}, evidence=evidence)

    report = build([tmp_path], empty_compatibility)
    acc = report.accumulator

    assert [row["kind"] for row in acc.config_integrity_violations] == [
        "ground_truth_without_evidence",
    ]
    assert acc.unconditional_verified_violations == []
    assert report.passed is False


def test_a_verdict_this_gate_cannot_read_fails_the_gate(tmp_path, empty_compatibility):
    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "NOT_EQ")
    write_ground_truth(tmp_path, {EQ: {"snippet": "CONFIRMED-EQ"}})

    report = build([tmp_path], empty_compatibility)

    assert [row["kind"] for row in report.accumulator.config_integrity_violations] == [
        "ground_truth_verdict_unknown",
    ]
    assert report.passed is False


def test_an_unverified_verdict_needs_no_evidence(tmp_path, empty_compatibility):
    """``UNKNOWN`` asserts nothing, so it carries no evidence and breaks nothing."""

    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "NOT_EQ")
    write_ground_truth(tmp_path, {EQ: {"snippet": "UNKNOWN"}}, evidence=None)

    report = build([tmp_path], empty_compatibility)

    assert report.accumulator.config_integrity_violations == []
    assert len(report.accumulator.dataset_label_mismatch_rows) == 1
    assert report.passed is True


def test_an_unreadable_ground_truth_fails_the_gate(tmp_path, empty_compatibility):
    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "EQUIVALENT")
    (tmp_path / soundness_gate.GROUND_TRUTH_FILE).write_text("{", encoding="utf-8")

    report = build([tmp_path], empty_compatibility)

    assert [row["kind"] for row in report.accumulator.config_integrity_violations] == [
        "ground_truth_unreadable",
    ]
    assert report.passed is False


# ---------------------------------------------------------------------------
# the compatibility metadata is the only thing that can authorize A0c
# ---------------------------------------------------------------------------


def test_the_shipped_metadata_loads_and_verifies_nothing_yet():
    """The file in the repository must satisfy the contract it is read under."""

    loaded = soundness_gate.load_conditional_compatibility(
        soundness_gate.DEFAULT_COMPATIBILITY_PATH
    )
    assert loaded.entries
    assert loaded.verified_entry_count == 0


@pytest.mark.parametrize("overrides,match", [
    pytest.param({"evidence": _DROP}, "entry fields", id="no-evidence-field"),
    pytest.param({"evidence": ""}, "non-empty evidence", id="empty-evidence"),
    pytest.param({"evidence": "none"}, "needs real evidence", id="evidence-says-none"),
    pytest.param({"evidence": "NONE"}, "needs real evidence", id="evidence-says-none-caps"),
    pytest.param({"verified_by": None}, "non-empty verified_by", id="no-verifier"),
    pytest.param({"verified_by": ""}, "non-empty verified_by", id="empty-verifier"),
    pytest.param({"verified_at": None}, "non-empty verified_at", id="no-timestamp"),
    pytest.param({"verified_at": "yesterday"}, "not a UTC instant", id="prose-timestamp"),
    pytest.param({"verified_at": "2026-13-01T00:00:00Z"}, "not a UTC instant",
                 id="impossible-timestamp"),
    pytest.param({"verified_at": "2026-09-15"}, "not a UTC instant", id="date-only"),
])
def test_a_verified_entry_without_its_evidence_and_verifier_is_refused(
    tmp_path, overrides, match,
):
    """"verified" is an authority claim; without evidence it is only a word.

    This file is the only thing that can turn a conditional contradiction into
    a soundness violation, so an entry that cannot say what was checked, by
    whom and when must not be readable at all.
    """

    path = write_compatibility(tmp_path / "c.json", [
        compatibility_entry(NEQ, "SphereConstructor", COMPAT_KIND, "log", "verified",
                            **overrides),
    ])
    with pytest.raises(ValueError, match=match):
        soundness_gate.load_conditional_compatibility(path)


@pytest.mark.parametrize("status", ["unverified", "not_applicable"])
@pytest.mark.parametrize("overrides", [
    pytest.param({"verified_by": "reviewer"}, id="verifier"),
    pytest.param({"verified_at": "2026-09-15T00:00:00Z"}, id="timestamp"),
])
def test_only_a_verified_entry_may_name_a_verifier(tmp_path, status, overrides):
    path = write_compatibility(tmp_path / "c.json", [
        compatibility_entry(NEQ, "SphereConstructor", COMPAT_KIND, "log", status,
                            **overrides),
    ])
    with pytest.raises(ValueError, match="only a verified"):
        soundness_gate.load_conditional_compatibility(path)


@pytest.mark.parametrize("entries,file_overrides,match", [
    pytest.param([{"sample": NEQ, "function": "f", "assumption_kind": COMPAT_KIND,
                   "subject": "*", "status": "unverified", "evidence": "none",
                   "verified_by": None, "verified_at": None, "extra": 1}],
                 {}, "entry fields", id="unknown-entry-field"),
    pytest.param([{"sample": NEQ, "function": "f", "assumption_kind": COMPAT_KIND,
                   "subject": "*", "status": "unverified"}],
                 {}, "entry fields", id="missing-required-fields"),
    pytest.param([], {"extra": 1}, "file fields", id="unknown-file-field"),
    pytest.param([(NEQ, "f", COMPAT_KIND, "*", "maybe")], {}, "unknown status",
                 id="unknown-status"),
    pytest.param([(NEQ, "f", COMPAT_KIND, "*", "unverified"),
                  (NEQ, "f", COMPAT_KIND, "*", "verified")], {}, "duplicate",
                 id="duplicate-key"),
])
def test_metadata_the_gate_cannot_fully_understand_is_refused(
    tmp_path, entries, file_overrides, match,
):
    path = write_compatibility(tmp_path / "c.json", entries, **file_overrides)
    with pytest.raises(ValueError, match=match):
        soundness_gate.load_conditional_compatibility(path)


def test_an_unreadable_metadata_file_cannot_authorize_a_conditional_violation(
    tmp_path,
):
    """Fail-closed twice: gate C fails, and nothing counts as verified.

    The entry below would make the contradiction a violation if the file were
    accepted; because one of its siblings is malformed the whole file is
    refused, so the row stays an investigation and the run fails on C instead.
    """

    write_conditional_pair(
        tmp_path, NEQ, "SphereConstructor", "cond-broken-metadata", Outcome.EQUIVALENT,
    )
    write_ground_truth(tmp_path, {NEQ: {"SphereConstructor": "CONFIRMED_NOT_EQ"}})
    compat = write_compatibility(tmp_path / "c.json", [
        compatibility_entry(NEQ, "SphereConstructor", COMPAT_KIND, "log", "verified"),
        compatibility_entry(NEQ, "other", COMPAT_KIND, "*", "verified", evidence="none"),
    ])

    report = build([tmp_path], compat)
    acc = report.accumulator

    assert [row["kind"] for row in acc.config_integrity_violations] == [
        "conditional_compatibility_unreadable",
    ]
    assert acc.conditional_verified_violations == []
    assert len(acc.compatibility_unknown_rows) == 1
    # The metadata block says the file was not used at all, so the 0 below
    # cannot be read as "the file was read and verifies nothing".
    assert report.as_dict()["metadata"] == {
        "compatibility_file": None,
        "compatibility_sha256": None,
        "compatibility_verified_entries": 0,
    }
    assert report.passed is False


def test_the_report_says_how_many_entries_could_authorize_a_violation(tmp_path):
    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "EQUIVALENT")
    compat = write_compatibility(tmp_path / "c.json", [
        compatibility_entry(NEQ, "SphereConstructor", COMPAT_KIND, "log", "verified"),
        compatibility_entry(NEQ, "SphereConstructor", COMPAT_KIND, "sin", "unverified"),
    ])

    payload = build([tmp_path], compat).as_dict()

    assert payload["metadata"]["compatibility_verified_entries"] == 1


def test_broken_compatibility_metadata_fails_the_gate(tmp_path):
    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "EQUIVALENT")
    broken = tmp_path / "broken.json"
    broken.write_text(json.dumps({"schema": "something-else"}), encoding="utf-8")

    report = build([tmp_path], broken)

    assert [row["kind"] for row in report.accumulator.config_integrity_violations] == [
        "conditional_compatibility_unreadable",
    ]
    assert report.passed is False


@pytest.mark.parametrize("fields,mode", [
    pytest.param({}, "legacy_unknown", id="legacy"),
    pytest.param({"identical_fast_path": "1"}, "on", id="flag-only-on"),
    pytest.param({"identical_fast_path": "0"}, "off", id="flag-only-off"),
    pytest.param(
        {"analysis_config_schema": "eqbench-analysis-config-v3",
         "identical_fast_path": "1"}, "on", id="v3-on",
    ),
    pytest.param(
        {"analysis_config_schema": "eqbench-analysis-config-v3",
         "identical_fast_path": "0"}, "off", id="v3-off",
    ),
    pytest.param(
        {"analysis_config_schema": "eqbench-analysis-config-v3"}, "invalid",
        id="v3-without-flag",
    ),
    pytest.param(
        {"analysis_config_schema": "eqbench-analysis-config-v3",
         "identical_fast_path": "yes"}, "invalid", id="v3-bad-value",
    ),
    pytest.param({"identical_fast_path": "yes"}, "invalid", id="flag-bad-value"),
    pytest.param({"analysis_config_schema": "eqbench-analysis-config-v2",
                  "identical_fast_path": "1"}, "invalid", id="unknown-schema"),
])
def test_the_run_mode_comes_from_the_manifest_and_is_never_guessed(
    tmp_path, empty_compatibility, fields, mode,
):
    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "EQUIVALENT")
    write_run_manifest(tmp_path, run_kind="test", **fields)

    report = build([tmp_path], empty_compatibility)

    assert [info["mode"] for info in report.mode_by_scope.values()] == [mode]
    assert report.passed is (mode != "invalid")
    assert (report.exit_code == soundness_gate.EXIT_PASS) is report.passed


def test_an_empty_tree_is_not_a_pass(tmp_path, empty_compatibility):
    (tmp_path / "empty").mkdir()
    report = build([tmp_path / "empty"], empty_compatibility)
    assert report.passed is False
    assert report.exit_code == soundness_gate.EXIT_EMPTY


# ---------------------------------------------------------------------------
# A / B: identical inputs (matrix rows 18, 21-25)
# ---------------------------------------------------------------------------


def _identical_pair(
    root: Path, outcome: str, *, evidence=None, disposition=None, with_log=True,
    left="B2", right="B3",
):
    write_pair_status(
        root, EQ, "snippet", left, right, outcome,
        left_sha=SHA_A, right_sha=SHA_A,
    )
    if with_log:
        write_result_json(
            root, EQ, "snippet", left, right, outcome,
            left_sha=SHA_A, right_sha=SHA_A,
            evidence=evidence, disposition=disposition,
        )
    write_ground_truth(root, {EQ: {"snippet": "CONFIRMED_EQ"}})


@pytest.mark.parametrize("fields", [
    pytest.param({}, id="legacy"),
    pytest.param({"identical_fast_path": "0",
                  "analysis_config_schema": "eqbench-analysis-config-v3"}, id="off"),
])
def test_a_confirmed_same_function_pair_judged_not_eq_violates_in_every_mode(
    tmp_path, empty_compatibility, fields,
):
    _identical_pair(tmp_path, "NOT_EQ", evidence=identity_evidence(sha=SHA_A))
    write_run_manifest(tmp_path, run_kind="test", **fields)

    report = build([tmp_path], empty_compatibility)
    acc = report.accumulator

    assert len(acc.identical_soundness_violations) == 1
    assert acc.identical_soundness_violations[0]["identity"] == "confirmed_same_function"
    assert acc.fast_path_violations == []
    assert report.passed is False


@pytest.mark.parametrize("evidence,detail", [
    pytest.param(None, "identity_evidence_absent", id="absent"),
    pytest.param(
        {"schema": "identical_function_identity_evidence_v1",
         "left": identity_evidence()["left"]},
        "identity_evidence_incomplete", id="one-sided",
    ),
    pytest.param(
        {**identity_evidence(), "right": {**identity_evidence()["right"],
                                          "image_base": 0x200000}},
        "identity_evidence_differs", id="differs",
    ),
    pytest.param(identity_evidence(sha=SHA_B), "identity_evidence_sha_mismatch",
                 id="foreign-sha"),
    pytest.param(identity_evidence(function="other"),
                 "identity_evidence_function_mismatch", id="other-function"),
    pytest.param(identity_evidence(match_count=2), "identity_evidence_match_count",
                 id="ambiguous-name"),
])
def test_identical_inputs_without_confirmed_identity_are_not_a_violation(
    tmp_path, empty_compatibility, evidence, detail,
):
    """Byte-identical inputs alone do not prove the same function was compared."""

    _identical_pair(tmp_path, "NOT_EQ", evidence=evidence)

    report = build([tmp_path], empty_compatibility)
    acc = report.accumulator

    assert acc.identical_soundness_violations == []
    assert [row["identity_detail"] for row in acc.identity_unverified_rows] == [detail]
    # The Eq relation is registered, so the NOT_EQ is still an A0 violation --
    # gate A simply is not the reason.
    assert len(acc.unconditional_verified_violations) == 1


def test_two_empty_digests_are_not_identical_inputs(tmp_path, empty_compatibility):
    write_pair_status(
        tmp_path, EQ, "snippet", "B1", "B2", "UNKNOWN", left_sha="", right_sha="",
    )
    report = build([tmp_path], empty_compatibility)
    assert report.accumulator.identical_rows == []


def test_with_the_fast_path_on_an_applicable_pair_must_be_accepted(
    tmp_path, empty_compatibility,
):
    _identical_pair(
        tmp_path, "UNKNOWN", evidence=identity_evidence(),
        disposition={"applicable": True, "applied": False, "reason": "disabled"},
    )
    write_run_manifest(
        tmp_path, analysis_config_schema="eqbench-analysis-config-v3",
        identical_fast_path="1",
    )

    report = build([tmp_path], empty_compatibility)

    assert [row["violation_kind"] for row in report.accumulator.fast_path_violations] == [
        "not_applied",
    ]
    assert report.passed is False


def test_an_applied_fast_path_that_did_not_decide_is_a_violation(
    tmp_path, empty_compatibility,
):
    _identical_pair(
        tmp_path, "UNKNOWN", evidence=identity_evidence(),
        disposition={"applicable": True, "applied": True, "reason": "applied"},
    )
    write_run_manifest(
        tmp_path, analysis_config_schema="eqbench-analysis-config-v3",
        identical_fast_path="1",
    )

    report = build([tmp_path], empty_compatibility)

    assert [row["violation_kind"] for row in report.accumulator.fast_path_violations] == [
        "not_equivalent",
    ]


def test_an_accepted_fast_path_pair_passes(tmp_path, empty_compatibility):
    _identical_pair(
        tmp_path, "EQUIVALENT", evidence=identity_evidence(),
        disposition={"applicable": True, "applied": True, "reason": "applied"},
    )
    write_run_manifest(
        tmp_path, analysis_config_schema="eqbench-analysis-config-v3",
        identical_fast_path="1",
    )

    report = build([tmp_path], empty_compatibility)

    assert report.accumulator.fast_path_violations == []
    assert report.accumulator.identity_unverified_rows == []
    assert report.counts_by_mode == {"on": 1}
    assert report.passed is True


@pytest.mark.parametrize("with_log,detail", [
    pytest.param(False, "log_absent", id="no-log"),
    pytest.param(True, "result_json_occurrence_mismatch", id="foreign-json"),
])
def test_an_unreadable_disposition_fails_the_gate_when_the_fast_path_is_on(
    tmp_path, empty_compatibility, with_log, detail,
):
    _identical_pair(tmp_path, "UNKNOWN", with_log=with_log)
    if with_log:
        # A log that belongs to another pair: the binding check refuses it.
        write_result_json(
            tmp_path, EQ, "snippet", "B2", "B3", "UNKNOWN",
            left_sha=SHA_A, right_sha=SHA_A, occurrence="production-pilot-other",
            evidence=identity_evidence(),
            disposition={"applicable": True, "applied": True, "reason": "applied"},
        )
    write_run_manifest(
        tmp_path, analysis_config_schema="eqbench-analysis-config-v3",
        identical_fast_path="1",
    )

    report = build([tmp_path], empty_compatibility)
    acc = report.accumulator

    assert [row["violation_kind"] for row in acc.fast_path_violations] == ["unverifiable"]
    assert acc.identical_rows[0]["result_json"] == detail
    assert report.passed is False


@pytest.mark.parametrize("fields,mode", [
    pytest.param({}, "legacy_unknown", id="legacy"),
    pytest.param({"identical_fast_path": "0",
                  "analysis_config_schema": "eqbench-analysis-config-v3"},
                 "off", id="off"),
])
def test_a_timeout_pair_is_never_reported_as_a_confirmed_same_function(
    tmp_path, empty_compatibility, fields, mode,
):
    """A pair the runner killed left no result JSON, so there is nothing to confirm.

    The identity is not reconstructed from the sha alone and not guessed from
    the pair's siblings: byte-identical inputs say the two *files* are the
    same, not that the checker resolved one and the same function in both.  An
    oracle run must therefore report such a pair as unverified, and gate A must
    stay silent about it.
    """

    _identical_pair(tmp_path, "TIMEOUT", with_log=False)
    write_run_manifest(tmp_path, run_kind="test", **fields)

    report = build([tmp_path], empty_compatibility)
    acc = report.accumulator

    assert len(acc.identical_rows) == 1
    row = acc.identical_rows[0]
    assert row["identity"] == "same_function_unverified"
    assert (row["identity_detail"], row["result_json"]) == (
        "result_json_unusable", "log_absent",
    )
    assert acc.identity_unverified_rows == [row]
    assert acc.identical_soundness_violations == []
    assert acc.fast_path_violations == []
    assert acc.oracle_rows == ([row] if mode == "off" else [])
    assert report.counts_by_mode == {mode: 1}
    assert report.passed is True


def test_the_same_timeout_pair_fails_gate_b_when_the_fast_path_is_on(
    tmp_path, empty_compatibility,
):
    """With the fast path on, "we cannot check" is a failure, not a pass."""

    _identical_pair(tmp_path, "TIMEOUT", with_log=False)
    write_run_manifest(
        tmp_path, analysis_config_schema="eqbench-analysis-config-v3",
        identical_fast_path="1",
    )

    report = build([tmp_path], empty_compatibility)

    assert [row["violation_kind"] for row in report.accumulator.fast_path_violations] == [
        "unverifiable",
    ]
    assert report.accumulator.identical_soundness_violations == []
    assert report.passed is False


def test_a_not_applicable_disposition_is_reported_not_failed(
    tmp_path, empty_compatibility,
):
    _identical_pair(
        tmp_path, "UNKNOWN",
        disposition={"applicable": False, "applied": False,
                     "reason": "binary_id_unavailable"},
    )
    write_run_manifest(
        tmp_path, analysis_config_schema="eqbench-analysis-config-v3",
        identical_fast_path="1",
    )

    report = build([tmp_path], empty_compatibility)
    acc = report.accumulator

    assert acc.fast_path_violations == []
    assert len(acc.fast_path_not_applicable_rows) == 1
    assert report.passed is True


def test_an_off_run_whose_results_applied_the_fast_path_fails_closed(
    tmp_path, empty_compatibility,
):
    """The manifest and the results must agree about which mode was run.

    If they do not, neither can be believed: the run is not an oracle and its
    outcomes are not the feature's either.
    """

    _identical_pair(
        tmp_path, "EQUIVALENT", evidence=identity_evidence(),
        disposition={"applicable": True, "applied": True, "reason": "applied"},
    )
    write_run_manifest(
        tmp_path, analysis_config_schema="eqbench-analysis-config-v3",
        identical_fast_path="0",
    )

    report = build([tmp_path], empty_compatibility)

    assert [row["kind"] for row in report.accumulator.config_integrity_violations] == [
        "fast_path_applied_in_an_off_run",
    ]
    assert report.passed is False


@pytest.mark.parametrize("fields", [
    pytest.param({}, id="legacy"),
    pytest.param({"identical_fast_path": "0",
                  "analysis_config_schema": "eqbench-analysis-config-v3"}, id="off"),
])
def test_gate_b_is_not_evaluated_outside_an_on_run(
    tmp_path, empty_compatibility, fields,
):
    _identical_pair(tmp_path, "UNKNOWN", evidence=identity_evidence())
    write_run_manifest(tmp_path, run_kind="test", **fields)

    report = build([tmp_path], empty_compatibility)
    acc = report.accumulator

    assert acc.fast_path_violations == []
    off = fields.get("identical_fast_path") == "0"
    assert len(acc.oracle_rows) == (1 if off else 0)
    assert report.counts_by_mode == {"off" if off else "legacy_unknown": 1}
    assert report.passed is True


# ---------------------------------------------------------------------------
# halves, roots and the report as a whole (matrix rows 26, 27)
# ---------------------------------------------------------------------------


def test_each_half_is_read_against_its_own_manifest_and_ground_truth(
    tmp_path, empty_compatibility,
):
    root = tmp_path / "subset"
    eq, neq = root / "eq", root / "neq"
    write_pair_status(eq, EQ, "snippet", "B1", "B2", "NOT_EQ")
    write_pair_status(neq, NEQ, "SphereConstructor", "N_B1", "O_B2", "EQUIVALENT")
    # Only the Eq half registers its relation; the Neq half's manifest knows
    # nothing about SphereConstructor, so its EQUIVALENT stays an investigation.
    write_ground_truth(eq, {EQ: {"snippet": "CONFIRMED_EQ"}})
    write_ground_truth(neq, {"other/sample/Neq/newV-oldV": {"f": "CONFIRMED_NOT_EQ"}})
    write_run_manifest(eq, analysis_config_schema="eqbench-analysis-config-v3",
                       identical_fast_path="1")
    write_run_manifest(neq, identical_fast_path="0")

    report = build([root], empty_compatibility)
    acc = report.accumulator

    assert {name.rsplit("/", 1)[-1]: info["mode"]
            for name, info in report.mode_by_scope.items()} == {"eq": "on", "neq": "off"}
    assert [row["pair_id"] for row in acc.unconditional_verified_violations] == ["B1_B2"]
    assert len(acc.dataset_label_mismatch_rows) == 1
    assert report.passed is False


def test_two_roots_keep_their_own_manifests(tmp_path, empty_compatibility):
    first, second = tmp_path / "first", tmp_path / "second"
    write_pair_status(first, EQ, "snippet", "B1", "B2", "NOT_EQ")
    write_pair_status(second, EQ, "snippet", "B1", "B2", "NOT_EQ")
    write_ground_truth(first, {EQ: {"snippet": "CONFIRMED_EQ"}})

    report = build([first, second], empty_compatibility)
    acc = report.accumulator

    assert len(report.records) == 2
    assert len(acc.unconditional_verified_violations) == 1
    assert acc.unconditional_verified_violations[0]["scope"] == str(first)
    assert [row["lookup"] for row in acc.manifest_lookup_error_rows] == ["absent"]


def test_the_report_names_the_compatibility_file_it_used(tmp_path):
    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "EQUIVALENT")
    compat = write_compatibility(
        tmp_path / "compat.json",
        [(EQ, "snippet", COMPAT_KIND, "*", "unverified")],
    )

    report = build([tmp_path], compat)
    payload = report.as_dict()

    assert payload["schema"] == "soundness-gate-v2"
    assert payload["metadata"]["compatibility_file"] == str(compat)
    assert len(payload["metadata"]["compatibility_sha256"]) == 64
    # The keys a label-only gate used to publish are gone for good.
    assert "violations" not in payload
    assert "violation_rows" not in payload


def test_the_cli_exit_code_follows_the_verdict(tmp_path, empty_compatibility, capsys):
    out = tmp_path / "gate.json"
    write_pair_status(tmp_path, EQ, "snippet", "B1", "B2", "EQUIVALENT")
    write_ground_truth(tmp_path, {EQ: {"snippet": "CONFIRMED_EQ"}})
    argv = [str(tmp_path), "--json", str(out),
            "--conditional-compatibility", str(empty_compatibility)]

    assert soundness_gate.main(argv) == soundness_gate.EXIT_PASS
    assert json.loads(out.read_text(encoding="utf-8"))["passed"] is True
    assert "GATE: PASS" in capsys.readouterr().out

    write_pair_status(tmp_path, EQ, "snippet", "B3", "B4", "NOT_EQ")
    assert soundness_gate.main(argv) == soundness_gate.EXIT_VIOLATION
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["passed"] is False
    assert payload["exit_code"] == soundness_gate.EXIT_VIOLATION
    assert payload["verified_ground_truth"]["unconditional_violations"][0]["pair_id"] == (
        "B3_B4"
    )
    assert soundness_gate.main([str(tmp_path / "missing")]) == soundness_gate.EXIT_EMPTY
