# -*- coding: utf-8 -*-
"""Issue #123 / PR-123-B: `outcome_transition` の 3 軸と reason 集合比較。

固定するのは次の独立性と fail-closed 性:

* 正解確認軸は benchmark ground truth だけを根拠にし、`source_relation` /
  `source_impact` を正解の代用にしない。Neq の NOT_EQ で ground truth が
  `UNKNOWN` のものは `unconfirmed` のまま残す。
* 遷移軸は「正解が確認できた決定」だけを `capability_improvement` に数え、
  確認できていない決定は `decided_but_unconfirmed` として別に数える。
* gate 軸は独立で、`ok` は正解確認の根拠にならない。
* reason 集合は payload を読めた pair だけを比較し、読めない pair は
  `incomparable` として別建て（一致に数えない）。
* 既存の既定出力・`--fail-on-change` の意味を変えない。
"""

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.contracts import (
    CLI_EXIT_CODE_BY_OUTCOME,
    Outcome,
    authority_digest,
)
from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
    PAIR_STATUS_PUBLIC_KEY_FILE,
    generate_pair_status_keypair,
    seal_pair_status,
)
from scripts.function_tracer_pcode.reporting import outcome_transition as ot
from scripts.function_tracer_pcode.reporting.benchmark_validation_gate import (
    FunctionDiffManifest,
)
from scripts.function_tracer_pcode.reporting.execution_receipt import (
    MATRIX_PUBLICATION_SCHEMA,
)
from scripts.function_tracer_pcode.reporting.pair_outcomes import load_pair_outcomes

EQ_SAMPLE = "CLEVER/LoopSub/Eq/new"
NEQ_SAMPLE = "CLEVER/LoopSub/Neq/new-old"
DIGEST = "a" * 64


def write_pair(tree: Path, sample, function, left, right, outcome, *,
               reasons=None, payload=True, supervisor_status="RESOLVED") -> str:
    """One pair status.  ``supervisor_status`` is how the pair *ended*.

    It is written explicitly rather than derived from ``outcome``, because the
    two say different things: a canonical ``ERROR`` can come from a pair the
    supervisor resolved (the run holds its result) or from one that ended in
    the durable ERROR state (it never produced one).
    """

    directory = tree / sample / function
    directory.mkdir(parents=True, exist_ok=True)
    name = f"{function}_{left}_{right}"
    body = {
        "canonical_outcome": outcome,
        "pair_execution_target": {
            "sample_identity": sample, "function_name": function,
            "left_binary_id": left, "right_binary_id": right,
        },
    }
    if supervisor_status is not None:
        body["supervisor_status"] = supervisor_status
    (directory / f"{name}.pair-status.json").write_text(
        json.dumps(body), encoding="utf-8",
    )
    log = directory / f"{name}.log"
    if payload:
        body = json.dumps({
            "unknown_reasons": [{"reason_id": value} for value in (reasons or ())],
            "diagnostics": {},
        })
        log.write_text(
            "=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n"
            f"{body}\n=== EQUIVALENCE_RESULT_JSON_END ===\n",
            encoding="utf-8",
        )
    else:
        log.write_text("no result payload\n", encoding="utf-8")
    return f"{sample}/{function}/{name}.pair-status.json"


# ---------------------------------------------------------------------------
# Issue #15 PR-15-B: pair statuses that are *sealed* by the real authority.
#
# A missing result payload can be excused only by an ending the pair-status
# authority confirms, so a fixture that merely writes ``supervisor_status`` as
# a string would test nothing: it would be exactly the unverified file the
# contract is there to refuse.  These helpers seal a real signed status with
# ``seal_pair_status`` and drop the verification key in the tree, so an
# "authority-valid" fixture is one the authority actually validated.
# ---------------------------------------------------------------------------

RESOLVED_KIND = "SupervisorCanonicalResultResolvedReceipt"


def _pair_target(sample, function, left, right):
    target = {
        "schema": "eqbench-pair-execution-target-v1",
        "authority_kind": "PairExecutionTargetReceipt",
        "sample_identity": sample, "output_sample_relative_path": sample,
        "function_name": function, "left_binary_id": left,
        "right_binary_id": right, "source_path": "source.c",
        "source_sha256": DIGEST, "left_binary_path": "left.bin",
        "left_binary_sha256": DIGEST, "right_binary_path": "right.bin",
        "right_binary_sha256": DIGEST, "analysis_source_digest": DIGEST,
        "analysis_config_digest": DIGEST,
    }
    return {**target, "target_digest": authority_digest(target)}


def _status_body(sample, function, left, right, outcome, supervisor_status):
    body = {
        "authority_kind": RESOLVED_KIND,
        "supervisor_authority_kind": RESOLVED_KIND,
        "supervisor_final_authority_digest": DIGEST,
        "launch_receipt_digest": DIGEST,
        "canonical_outcome": outcome,
        "decision_receipt_digest": DIGEST,
        "result_occurrence_id": "production-pilot-fixture",
        "result_entry_occurrence_receipt_digest": DIGEST,
        "execution_identity_digest": DIGEST,
        "execution_nonce": "fixture-nonce",
        "stream_id": "stream-production-pilot-fixture",
        "source_snapshot_fingerprint": DIGEST,
        "canonical_result_bundle_digest": DIGEST,
        "canonical_result_bundle_kind": "CanonicalResultFinalizationBundle",
        "canonical_result_payload_preimage_digest": DIGEST,
        "semantic_projection_digest": DIGEST,
        "error_kind": "checker_error" if outcome == "ERROR" else None,
        "child_returncode": CLI_EXIT_CODE_BY_OUTCOME[Outcome(outcome)],
        "supervisor_status": supervisor_status,
        "supervisor_projection_digest": DIGEST,
        "classification_valid": True,
        "pair_execution_target": _pair_target(sample, function, left, right),
    }
    if supervisor_status != "RESOLVED":
        kind = f"Durable{supervisor_status.title()}FinalizationBundle"
        body.update({
            "authority_kind": kind,
            "supervisor_authority_kind": kind,
            "finalization_bundle_digest": DIGEST,
            "event_stream_authority_digest": DIGEST,
            "child_exit_disposition": "EXITED_143_AFTER_SIGTERM",
            "child_returncode_observation_kind": "LIVE_PROCESS_WAIT",
            "child_returncode": 143,
        })
    return body


def write_sealed_pair(
    tree: Path, sample, function, left, right, outcome, *,
    supervisor_status="RESOLVED", reasons=None, payload=True, corrupt=None,
) -> Path:
    """One pair status sealed by the authority, optionally corrupted after sealing."""

    private_key = tree / "pair-status-signing.key"
    public_key = tree / PAIR_STATUS_PUBLIC_KEY_FILE
    tree.mkdir(parents=True, exist_ok=True)
    if not public_key.is_file():
        generate_pair_status_keypair(private_key, public_key)
    body = _status_body(sample, function, left, right, outcome, supervisor_status)
    sealed = seal_pair_status(
        body, private_key_path=private_key, public_key_path=public_key,
    )
    if corrupt is not None:
        sealed = corrupt(dict(sealed))
    directory = tree / sample / function
    directory.mkdir(parents=True, exist_ok=True)
    name = f"{function}_{left}_{right}"
    path = directory / f"{name}.pair-status.json"
    path.write_text(json.dumps(sealed), encoding="utf-8")
    log = directory / f"{name}.log"
    if payload:
        log.write_text(
            "=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n"
            + json.dumps({
                "unknown_reasons": [{"reason_id": v} for v in (reasons or ())],
                "diagnostics": {},
            })
            + "\n=== EQUIVALENCE_RESULT_JSON_END ===\n",
            encoding="utf-8",
        )
    else:
        log.write_text("no result payload\n", encoding="utf-8")
    return path


def ground_truth(entries) -> FunctionDiffManifest:
    return FunctionDiffManifest(samples={
        sample: {
            "parse_status": "ok",
            "functions": {
                name: {
                    "source_relation": relation,
                    "source_impact": impact,
                    "semantic_ground_truth": truth,
                    "ground_truth_evidence": "reviewed",
                },
            },
        }
        for sample, name, relation, impact, truth in entries
    })


def write_publication_manifest(tree: Path, expected, skipped=(), *, schema=None) -> None:
    tree.mkdir(parents=True, exist_ok=True)
    (tree / ot.PUBLICATION_MANIFEST_FILE).write_text(
        json.dumps({
            "schema": MATRIX_PUBLICATION_SCHEMA if schema is None else schema,
            "expected_pair_status_paths": list(expected),
            "verified_skipped_pair_status_paths": list(skipped),
        }),
        encoding="utf-8",
    )


def write_runtime_receipt(tree: Path, sample, function, left, right, seconds, **override):
    directory = tree / sample / function / ot.RUNTIME_METRICS_DIR
    directory.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema": "eqbench-pair-progress-receipt-v1",
        "function_name": function, "left_binary_id": left, "right_binary_id": right,
        "elapsed_seconds": seconds, "state": "COMPLETED",
    }
    payload.update(override)
    (directory / f"{function}_{left}_{right}{ot.RUNTIME_METRICS_SUFFIX}").write_text(
        json.dumps(payload), encoding="utf-8",
    )


def one(tree: Path, sample, function, left, right, outcome, **kwargs):
    write_pair(tree, sample, function, left, right, outcome, **kwargs)
    return load_pair_outcomes(tree)[(sample, function, left, right)]


# ---------------------------------------------------------------------------
# A. correctness axis
# ---------------------------------------------------------------------------


def test_correctness_axis_uses_ground_truth_only(tmp_path):
    """Neq の決定は reviewed ground truth だけが確定できる。"""
    manifest = ground_truth([
        (NEQ_SAMPLE, "confirmed_neq", "changed", "MAY_AFFECT", "CONFIRMED_NOT_EQ"),
        (NEQ_SAMPLE + "/eq", "confirmed_eq", "changed", "MAY_AFFECT", "CONFIRMED_EQ"),
        (NEQ_SAMPLE + "/unk", "unknown_truth", "changed", "MAY_AFFECT", "UNKNOWN"),
    ])
    cases = (
        (NEQ_SAMPLE, "confirmed_neq", "NOT_EQ", ot.CORRECTNESS_CONSISTENT),
        (NEQ_SAMPLE, "confirmed_neq", "EQUIVALENT", ot.CORRECTNESS_CONTRADICTED),
        (NEQ_SAMPLE + "/eq", "confirmed_eq", "EQUIVALENT", ot.CORRECTNESS_CONSISTENT),
        (NEQ_SAMPLE + "/eq", "confirmed_eq", "NOT_EQ", ot.CORRECTNESS_CONTRADICTED),
        (NEQ_SAMPLE + "/unk", "unknown_truth", "NOT_EQ", ot.CORRECTNESS_UNCONFIRMED),
        (NEQ_SAMPLE + "/unk", "unknown_truth", "EQUIVALENT", ot.CORRECTNESS_UNCONFIRMED),
    )
    for index, (sample, function, outcome, expected) in enumerate(cases):
        record = one(tmp_path / f"t{index}", sample, function, "N_B1", "O_B1", outcome)
        assert ot.correctness_axis(record, manifest) == expected, (sample, outcome)


def test_unconfirmed_ground_truth_is_never_counted_as_confirmed(tmp_path):
    """ground truth UNKNOWN の Neq NOT_EQ を「正解」に数えない。"""
    manifest = ground_truth([(NEQ_SAMPLE, "g", "changed", "MAY_AFFECT", "UNKNOWN")])
    record = one(tmp_path, NEQ_SAMPLE, "g", "N_B1", "O_B1", "NOT_EQ")

    assert ot.correctness_axis(record, manifest) == ot.CORRECTNESS_UNCONFIRMED


def test_source_relation_is_not_used_as_ground_truth(tmp_path):
    """source が変わった / 同一というだけでは意味的な正解にしない。"""
    changed = ground_truth([(NEQ_SAMPLE, "g", "changed", "MAY_AFFECT", "UNKNOWN")])
    identical = ground_truth([
        (NEQ_SAMPLE, "g", "source-identical", "NO_KNOWN_SOURCE_IMPACT", "UNKNOWN"),
    ])
    not_eq = one(tmp_path / "a", NEQ_SAMPLE, "g", "N_B1", "O_B1", "NOT_EQ")
    equivalent = one(tmp_path / "b", NEQ_SAMPLE, "g", "N_B1", "O_B1", "EQUIVALENT")

    assert ot.correctness_axis(not_eq, changed) == ot.CORRECTNESS_UNCONFIRMED
    assert ot.correctness_axis(equivalent, identical) == ot.CORRECTNESS_UNCONFIRMED


def test_missing_manifest_leaves_neq_decisions_unconfirmed(tmp_path):
    record = one(tmp_path, NEQ_SAMPLE, "g", "N_B1", "O_B1", "NOT_EQ")
    assert ot.correctness_axis(record, None) == ot.CORRECTNESS_UNCONFIRMED


def test_eq_label_is_its_own_ground_truth(tmp_path):
    """Eq sample は両側が同一 source なので label が正解そのもの。"""
    good = one(tmp_path / "a", EQ_SAMPLE, "f", "B1", "B2", "EQUIVALENT")
    bad = one(tmp_path / "b", EQ_SAMPLE, "f", "B1", "B2", "NOT_EQ")

    assert ot.correctness_axis(good, None) == ot.CORRECTNESS_CONSISTENT
    assert ot.correctness_axis(bad, None) == ot.CORRECTNESS_CONTRADICTED


def test_non_decisive_outcomes_have_nothing_to_confirm(tmp_path):
    for index, outcome in enumerate(("UNKNOWN", "TIMEOUT", "ERROR")):
        record = one(tmp_path / f"t{index}", EQ_SAMPLE, "f", "B1", "B2", outcome)
        assert ot.correctness_axis(record, None) == ot.CORRECTNESS_NOT_APPLICABLE


# ---------------------------------------------------------------------------
# B. transition axis
# ---------------------------------------------------------------------------


def test_transition_axis_counts_improvement_only_when_confirmed_consistent():
    confirmed = ot.classify_transition(
        "UNKNOWN", "NOT_EQ", ot.CORRECTNESS_NOT_APPLICABLE, ot.CORRECTNESS_CONSISTENT,
    )
    unconfirmed = ot.classify_transition(
        "UNKNOWN", "NOT_EQ", ot.CORRECTNESS_NOT_APPLICABLE, ot.CORRECTNESS_UNCONFIRMED,
    )

    assert confirmed == (ot.TRANSITION_IMPROVEMENT, ())
    assert unconfirmed[0] == ot.TRANSITION_OTHER
    assert ot.TRANSITION_NOTE_DECIDED_BUT_UNCONFIRMED in unconfirmed[1]


def test_decided_but_unconfirmed_is_a_separate_bucket(tmp_path):
    """改善の counter へ混ぜず、独立に数える。"""
    before, after = tmp_path / "before", tmp_path / "after"
    write_pair(before, NEQ_SAMPLE, "g", "N_B1", "O_B1", "UNKNOWN")
    write_pair(after, NEQ_SAMPLE, "g", "N_B1", "O_B1", "NOT_EQ")
    manifest = ground_truth([(NEQ_SAMPLE, "g", "changed", "MAY_AFFECT", "UNKNOWN")])

    report = ot.build_axes(
        load_pair_outcomes(before), load_pair_outcomes(after),
        before_manifest=manifest, after_manifest=manifest,
    )

    assert report.transition_counts()[ot.TRANSITION_IMPROVEMENT] == 0
    assert report.transition_notes()[ot.TRANSITION_NOTE_DECIDED_BUT_UNCONFIRMED] == 1
    assert report.correctness_counts("after")[ot.CORRECTNESS_UNCONFIRMED] == 1


def test_a_contradicted_decision_is_a_regression_not_an_improvement():
    assert ot.classify_transition(
        "UNKNOWN", "NOT_EQ", ot.CORRECTNESS_NOT_APPLICABLE, ot.CORRECTNESS_CONTRADICTED,
    ) == (ot.TRANSITION_REGRESSION, ())


def test_eq_label_not_eq_is_regression_and_violation(tmp_path):
    """Eq sample の NOT_EQ は遷移軸で退行、gate 軸で violation。"""
    before, after = tmp_path / "before", tmp_path / "after"
    write_pair(before, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")
    write_pair(after, EQ_SAMPLE, "f", "B1", "B2", "NOT_EQ")

    report = ot.build_axes(load_pair_outcomes(before), load_pair_outcomes(after))

    assert report.transition_counts()[ot.TRANSITION_REGRESSION] == 1
    assert report.correctness_counts("after")[ot.CORRECTNESS_CONTRADICTED] == 1
    assert report.gate_counts("after")[ot.GATE_VIOLATION] == 1


def test_losing_a_decision_is_a_regression():
    assert ot.classify_transition(
        "EQUIVALENT", "UNKNOWN", ot.CORRECTNESS_CONSISTENT, ot.CORRECTNESS_NOT_APPLICABLE,
    ) == (ot.TRANSITION_REGRESSION, ())


def test_non_decisive_kind_change_is_a_classification_change():
    assert ot.classify_transition(
        "TIMEOUT", "UNKNOWN", ot.CORRECTNESS_NOT_APPLICABLE, ot.CORRECTNESS_NOT_APPLICABLE,
    ) == (ot.TRANSITION_CLASSIFICATION_CHANGE, ())


def test_a_reason_set_change_is_a_classification_change_only_when_compared():
    same = ot.classify_transition(
        "UNKNOWN", "UNKNOWN", ot.CORRECTNESS_NOT_APPLICABLE, ot.CORRECTNESS_NOT_APPLICABLE,
        reason_set_changed=False,
    )
    changed = ot.classify_transition(
        "UNKNOWN", "UNKNOWN", ot.CORRECTNESS_NOT_APPLICABLE, ot.CORRECTNESS_NOT_APPLICABLE,
        reason_set_changed=True,
    )
    not_compared = ot.classify_transition(
        "UNKNOWN", "UNKNOWN", ot.CORRECTNESS_NOT_APPLICABLE, ot.CORRECTNESS_NOT_APPLICABLE,
    )

    assert same == (ot.TRANSITION_OTHER, (ot.TRANSITION_NOTE_UNCHANGED,))
    assert changed[0] == ot.TRANSITION_CLASSIFICATION_CHANGE
    assert not_compared == (ot.TRANSITION_OTHER, (ot.TRANSITION_NOTE_UNCHANGED,))


def test_a_pair_missing_on_one_side_is_reported_not_counted_as_unchanged(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    write_pair(before, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")
    after.mkdir()
    write_pair(after, EQ_SAMPLE, "f", "B1", "B9", "UNKNOWN")

    report = ot.build_axes(load_pair_outcomes(before), load_pair_outcomes(after))

    assert report.transition_notes()[ot.TRANSITION_NOTE_MISSING] == 2
    assert report.transition_notes()[ot.TRANSITION_NOTE_UNCHANGED] == 0


def test_axes_report_says_when_reason_sets_were_not_compared(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    for tree in (before, after):
        write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")

    text = "\n".join(ot.format_axes(
        ot.build_axes(load_pair_outcomes(before), load_pair_outcomes(after))
    ))

    assert "--reason-sets is off" in text


# ---------------------------------------------------------------------------
# C. gate axis independence
# ---------------------------------------------------------------------------


def test_gate_axis_is_independent_of_correctness(tmp_path):
    """gate `ok` は正解確認にならない（同じ pair が unconfirmed のまま）。"""
    manifest = ground_truth([
        (NEQ_SAMPLE, "g", "source-identical", "NO_KNOWN_SOURCE_IMPACT", "UNKNOWN"),
    ])
    record = one(tmp_path, NEQ_SAMPLE, "g", "N_B1", "O_B1", "EQUIVALENT")

    assert ot.gate_axis(record, manifest) == ot.GATE_OK
    assert ot.correctness_axis(record, manifest) == ot.CORRECTNESS_UNCONFIRMED


def test_gate_not_applicable_is_not_a_correctness_claim(tmp_path):
    """Neq NOT_EQ は gate では not_applicable、正解軸では unconfirmed。"""
    manifest = ground_truth([(NEQ_SAMPLE, "g", "changed", "MAY_AFFECT", "UNKNOWN")])
    record = one(tmp_path, NEQ_SAMPLE, "g", "N_B1", "O_B1", "NOT_EQ")

    assert ot.gate_axis(record, manifest) == ot.GATE_NOT_APPLICABLE
    assert ot.correctness_axis(record, manifest) == ot.CORRECTNESS_UNCONFIRMED


def test_the_three_axes_are_reported_separately(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    for tree in (before, after):
        write_pair(tree, NEQ_SAMPLE, "g", "N_B1", "O_B1", "NOT_EQ")
    manifest = ground_truth([(NEQ_SAMPLE, "g", "changed", "MAY_AFFECT", "UNKNOWN")])

    payload = ot.build_axes(
        load_pair_outcomes(before), load_pair_outcomes(after),
        before_manifest=manifest, after_manifest=manifest,
    ).as_dict()

    assert set(payload) >= {"correctness", "transition", "gate"}
    assert payload["correctness"]["after"][ot.CORRECTNESS_UNCONFIRMED] == 1
    assert payload["gate"]["after"][ot.GATE_NOT_APPLICABLE] == 1
    assert payload["transition"][ot.TRANSITION_IMPROVEMENT] == 0


# ---------------------------------------------------------------------------
# reason set comparison
# ---------------------------------------------------------------------------


def test_reason_set_comparison_separates_comparable_mismatch_and_incomparable(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    write_pair(before, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", reasons=("a", "b"))
    write_pair(after, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", reasons=("b", "a"))
    write_pair(before, EQ_SAMPLE, "f", "B1", "B9", "UNKNOWN", reasons=("a",))
    write_pair(after, EQ_SAMPLE, "f", "B1", "B9", "UNKNOWN", reasons=("c",))
    write_pair(before, EQ_SAMPLE, "f", "B3", "B4", "TIMEOUT", payload=False,
               supervisor_status="TIMEOUT")
    write_pair(after, EQ_SAMPLE, "f", "B3", "B4", "TIMEOUT", payload=False,
               supervisor_status="TIMEOUT")
    write_pair(before, EQ_SAMPLE, "f", "B5", "B6", "UNKNOWN", reasons=("a",))
    write_pair(after, EQ_SAMPLE, "f", "B5", "B6", "EQUIVALENT", reasons=())

    report = ot.build_reason_sets(load_pair_outcomes(before), load_pair_outcomes(after))

    counts = report.counts()
    assert counts["pairs"] == 4
    assert counts["comparable"] == 3
    assert counts["incomparable"] == 1
    assert counts["reason_set_mismatch"] == 2
    assert counts["outcome_mismatch"] == 1
    assert report.incomparable_sides_agree is True


def test_a_pair_without_a_payload_is_never_counted_as_a_match(tmp_path):
    """payload 無しを「reason 集合が一致」に数えない。"""
    before, after = tmp_path / "before", tmp_path / "after"
    for tree in (before, after):
        write_sealed_pair(tree, EQ_SAMPLE, "f", "B1", "B2", outcome="TIMEOUT",
                          supervisor_status="TIMEOUT", payload=False)

    report = ot.build_reason_sets(load_pair_outcomes(before), load_pair_outcomes(after))

    assert report.counts() == {
        "pairs": 1, "comparable": 0, "incomparable": 1,
        "outcome_mismatch": 0, "reason_set_mismatch": 0, "payload_loss": 0,
    }
    assert report.rows[0].detail == ot.REASON_DETAIL_NO_PAYLOAD_BOTH


def test_an_empty_reason_set_is_not_the_same_as_an_unreadable_one(tmp_path):
    empty = tmp_path / "empty"
    unreadable = tmp_path / "unreadable"
    record_empty = one(empty, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", reasons=())
    record_none = one(unreadable, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", payload=False)

    assert ot.final_reason_set(record_empty) == ()
    assert ot.final_reason_set(record_none) is None


def test_losing_a_payload_on_one_side_only_is_visible(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    write_pair(before, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", reasons=("a",))
    write_pair(after, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", payload=False)

    report = ot.build_reason_sets(load_pair_outcomes(before), load_pair_outcomes(after))

    assert report.counts()["incomparable"] == 1
    assert report.rows[0].detail == ot.REASON_DETAIL_NO_PAYLOAD_AFTER
    assert report.incomparable_sides_agree is False
    assert report.counts()["payload_loss"] == 1


def test_a_decided_pair_that_lost_its_payload_is_a_payload_loss(tmp_path):
    """Issue #15 PR-15-B: separate "we could not look" from "there was nothing".

    A pair the checker decided emitted a result payload, so its absence on one
    side means the run lost something it produced.  That must stay visible as
    its own count instead of being absorbed into the generic incomparable
    bucket, because a before/after comparison is only as good as what it could
    actually compare.
    """

    before, after = tmp_path / "before", tmp_path / "after"
    write_pair(before, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", reasons=("a",))
    write_pair(after, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", payload=False)

    report = ot.build_reason_sets(load_pair_outcomes(before), load_pair_outcomes(after))

    assert report.counts()["payload_loss"] == 1
    assert report.payload_losses == report.incomparable
    assert report.rows[0].as_dict()["payload_loss"] is True


# ---------------------------------------------------------------------------
# What excuses a missing result payload: an ending the authority confirms.
# ---------------------------------------------------------------------------


def _sealed_reason_sets(tmp_path, *, before_spec, after_spec):
    before, after = tmp_path / "before", tmp_path / "after"
    for tree, spec in ((before, before_spec), (after, after_spec)):
        write_sealed_pair(tree, EQ_SAMPLE, "f", "B1", "B2", **spec)
    return ot.build_reason_sets(load_pair_outcomes(before), load_pair_outcomes(after))


@pytest.mark.parametrize("outcome,supervisor_status", [
    pytest.param("TIMEOUT", "TIMEOUT", id="killed-at-the-deadline"),
    pytest.param("ERROR", "ERROR", id="durable-failure"),
])
def test_an_authority_valid_durable_ending_owes_no_payload(
    tmp_path, outcome, supervisor_status,
):
    """Neither ending reached a canonical result, so neither owes a payload.

    A pair killed at the deadline may or may not have flushed the JSON first --
    a matter of milliseconds, on which two runs of the same commit legitimately
    disagree -- and a durable failure never produced one at all.
    """

    report = _sealed_reason_sets(
        tmp_path,
        before_spec=dict(outcome=outcome, supervisor_status=supervisor_status,
                         reasons=("a",)),
        after_spec=dict(outcome=outcome, supervisor_status=supervisor_status,
                        payload=False),
    )

    assert report.counts()["incomparable"] == 1
    assert report.counts()["payload_loss"] == 0
    # ... and it is still not counted as a match.
    assert report.counts()["comparable"] == 0
    assert report.counts()["reason_set_mismatch"] == 0


def test_an_error_the_supervisor_resolved_owes_its_payload(tmp_path):
    """The canonical outcome cannot tell the two ERROR endings apart.

    A pair the supervisor RESOLVED holds the child's canonical result, so its
    payload going missing is a real loss -- and reading ``ERROR`` alone would
    have excused exactly that.
    """

    report = _sealed_reason_sets(
        tmp_path,
        before_spec=dict(outcome="ERROR", supervisor_status="RESOLVED", reasons=("a",)),
        after_spec=dict(outcome="ERROR", supervisor_status="RESOLVED", payload=False),
    )

    assert report.counts()["payload_loss"] == 1
    assert report.rows[0].detail == ot.REASON_DETAIL_NO_PAYLOAD_AFTER
    assert report.rows[0].as_dict()["after_finalization"] == "resolved"


def test_a_resolved_error_with_payloads_on_both_sides_is_comparable(tmp_path):
    report = _sealed_reason_sets(
        tmp_path,
        before_spec=dict(outcome="ERROR", supervisor_status="RESOLVED", reasons=("a",)),
        after_spec=dict(outcome="ERROR", supervisor_status="RESOLVED", reasons=("a",)),
    )

    assert report.counts()["comparable"] == 1
    assert report.counts()["payload_loss"] == 0
    assert report.counts()["reason_set_mismatch"] == 0


def _drop(field):
    return lambda sealed: {k: v for k, v in sealed.items() if k != field}


def _set(**fields):
    return lambda sealed: {**sealed, **fields}


@pytest.mark.parametrize("spec,why", [
    # A status whose ending contradicts its own outcome is not a durable
    # ending, it is a broken file claiming one.  It cannot be sealed (see
    # below), so it can only reach a run tree as an edited file.
    pytest.param(dict(outcome="TIMEOUT", supervisor_status="TIMEOUT",
                      corrupt=_set(canonical_outcome="UNKNOWN")),
                 "status/outcome join", id="timeout-state-unknown-outcome"),
    pytest.param(dict(outcome="ERROR", supervisor_status="ERROR",
                      corrupt=_set(canonical_outcome="TIMEOUT")),
                 "status/outcome join", id="error-state-timeout-outcome"),
    # The durable authority fields are what a durable ending is made of.
    pytest.param(dict(outcome="TIMEOUT", supervisor_status="TIMEOUT",
                      corrupt=_drop("finalization_bundle_digest")),
                 "missing durable field", id="missing-durable-field"),
    pytest.param(dict(outcome="TIMEOUT", supervisor_status="TIMEOUT",
                      corrupt=_set(event_stream_authority_digest="")),
                 "empty durable field", id="empty-durable-field"),
    pytest.param(dict(outcome="TIMEOUT", supervisor_status="TIMEOUT",
                      corrupt=_set(authority_kind="SupervisorCanonicalResultResolvedReceipt")),
                 "authority kind", id="wrong-authority-kind"),
    pytest.param(dict(outcome="TIMEOUT", supervisor_status="TIMEOUT",
                      corrupt=_set(supervisor_authority_kind="DurableErrorFinalizationBundle")),
                 "supervisor kind", id="wrong-supervisor-kind"),
    pytest.param(dict(outcome="TIMEOUT", supervisor_status="TIMEOUT",
                      corrupt=_set(child_returncode=7)),
                 "child exit join", id="child-exit-join"),
    pytest.param(dict(outcome="TIMEOUT", supervisor_status="TIMEOUT",
                      corrupt=_set(child_exit_disposition="SOMETHING_ELSE")),
                 "child disposition", id="child-disposition"),
    pytest.param(dict(outcome="TIMEOUT", supervisor_status="TIMEOUT",
                      corrupt=_drop("supervisor_status")),
                 "no ending at all", id="missing-supervisor-status"),
    pytest.param(dict(outcome="TIMEOUT", supervisor_status="TIMEOUT",
                      corrupt=_set(supervisor_status="KILLED")),
                 "unknown ending", id="unknown-supervisor-status"),
    pytest.param(dict(outcome="TIMEOUT", supervisor_status="TIMEOUT",
                      corrupt=_set(pair_status_signature="A" * 88)),
                 "broken seal", id="broken-signature"),
])
def test_a_claimed_durable_ending_the_authority_refuses_excuses_nothing(
    tmp_path, spec, why,
):
    """Only an ending the authority *confirms* can excuse a missing payload.

    Each of these is a file that says ``TIMEOUT``/``ERROR`` somewhere while
    failing the contract that makes such a status mean anything -- the seal,
    the durable authority fields, the authority kinds, the child-exit join.
    Taking the claim at face value would let a broken artifact hide a lost
    result, so the payload stays counted as lost.
    """

    before, after = tmp_path / "before", tmp_path / "after"
    write_sealed_pair(before, EQ_SAMPLE, "f", "B1", "B2", outcome=spec["outcome"],
                      supervisor_status=spec["supervisor_status"], reasons=("a",))
    write_sealed_pair(after, EQ_SAMPLE, "f", "B1", "B2", payload=False, **spec)
    # The before side is a genuine durable ending, so only the after side is
    # in question: the count below is about the corrupted file alone.

    report = ot.build_reason_sets(load_pair_outcomes(before), load_pair_outcomes(after))

    assert report.counts()["payload_loss"] == 1, why
    assert report.rows[0].as_dict()["after_finalization"] == "unverified"


@pytest.mark.parametrize("outcome,supervisor_status", [
    pytest.param("UNKNOWN", "ERROR", id="error-state-unknown-outcome"),
    pytest.param("ERROR", "TIMEOUT", id="timeout-state-error-outcome"),
])
def test_the_authority_refuses_to_seal_a_contradictory_ending(
    tmp_path, outcome, supervisor_status,
):
    """A durable ending must agree with the outcome, so these cannot be sealed.

    This is why the reporting side can treat "sealed and validated" as the
    whole question: a contradictory combination has no legitimate form, and a
    file carrying one is an edited file, covered by the case above.
    """

    with pytest.raises(ValueError, match="status/outcome join"):
        write_sealed_pair(tmp_path / "tree", EQ_SAMPLE, "f", "B1", "B2",
                          outcome=outcome, supervisor_status=supervisor_status)


def test_a_status_without_a_verification_key_is_not_verified(tmp_path):
    """The seal is only evidence when it can be checked."""

    before, after = tmp_path / "before", tmp_path / "after"
    write_sealed_pair(before, EQ_SAMPLE, "f", "B1", "B2", outcome="TIMEOUT",
                      supervisor_status="TIMEOUT", reasons=("a",))
    write_sealed_pair(after, EQ_SAMPLE, "f", "B1", "B2", outcome="TIMEOUT",
                      supervisor_status="TIMEOUT", payload=False)
    (after / PAIR_STATUS_PUBLIC_KEY_FILE).unlink()

    report = ot.build_reason_sets(load_pair_outcomes(before), load_pair_outcomes(after))

    assert report.counts()["payload_loss"] == 1


def test_a_pair_missing_on_one_side_is_not_a_lost_payload(tmp_path):
    """No status on that side at all is a missing pair, not a missing result."""

    before, after = tmp_path / "before", tmp_path / "after"
    write_pair(before, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", reasons=("a",))
    after.mkdir(parents=True, exist_ok=True)
    write_pair(after, EQ_SAMPLE, "f", "B9", "B9", "UNKNOWN", reasons=("a",))

    report = ot.build_reason_sets(load_pair_outcomes(before), load_pair_outcomes(after))

    assert report.counts()["payload_loss"] == 0
    assert {row.detail for row in report.incomparable} == {ot.REASON_DETAIL_MISSING}


def test_a_comparable_pair_is_never_a_payload_loss(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    for tree in (before, after):
        write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", reasons=("a",))

    report = ot.build_reason_sets(load_pair_outcomes(before), load_pair_outcomes(after))

    assert report.counts() == {
        "pairs": 1, "comparable": 1, "incomparable": 0,
        "outcome_mismatch": 0, "reason_set_mismatch": 0, "payload_loss": 0,
    }


def test_only_the_last_result_payload_of_a_log_is_used(tmp_path):
    """retry で payload が複数出ても最終の reason 集合を使う。"""
    tree = tmp_path / "tree"
    write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", reasons=("first",))
    log = tree / EQ_SAMPLE / "f" / "f_B1_B2.log"
    body = json.dumps({"unknown_reasons": [{"reason_id": "last"}], "diagnostics": {}})
    with log.open("a", encoding="utf-8") as stream:
        stream.write(
            "=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n"
            f"{body}\n=== EQUIVALENCE_RESULT_JSON_END ===\n"
        )

    record = load_pair_outcomes(tree)[(EQ_SAMPLE, "f", "B1", "B2")]
    assert ot.final_reason_set(record) == ("last",)


# ---------------------------------------------------------------------------
# --manifest completeness
# ---------------------------------------------------------------------------


def test_manifest_completeness_reports_missing_and_unexpected_pairs(tmp_path):
    tree = tmp_path / "tree"
    kept = write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")
    extra = write_pair(tree, EQ_SAMPLE, "f", "B5", "B6", "UNKNOWN")
    write_publication_manifest(tree, [kept, f"{EQ_SAMPLE}/f/f_B9_B9.pair-status.json"])

    part = ot.tree_completeness(tree)

    assert part.status == ot.COMPLETENESS_PARTIAL
    assert part.pairs_missing == (f"{EQ_SAMPLE}/f/f_B9_B9.pair-status.json",)
    assert part.pairs_unexpected == (extra,)


def test_manifest_completeness_is_unknown_without_a_manifest(tmp_path):
    tree = tmp_path / "tree"
    write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")

    part = ot.tree_completeness(tree)

    assert part.status == ot.COMPLETENESS_UNKNOWN
    assert part.pairs_expected == 0


def test_manifest_of_an_unexpected_schema_is_not_complete(tmp_path):
    tree = tmp_path / "tree"
    kept = write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")
    write_publication_manifest(tree, [kept], schema="something-else-v9")

    assert ot.tree_completeness(tree).status == ot.COMPLETENESS_UNKNOWN


def test_reused_pairs_keep_a_tree_from_being_complete(tmp_path):
    tree = tmp_path / "tree"
    kept = write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")
    write_publication_manifest(tree, [kept], skipped=[kept])

    part = ot.tree_completeness(tree)

    assert part.status == ot.COMPLETENESS_PARTIAL
    assert part.pairs_verified_skipped == 1


def test_combined_completeness_fails_closed(tmp_path):
    complete = ot.TreeCompleteness("a", ot.COMPLETENESS_COMPLETE, "", 1, 1, (), (), 0)
    partial = ot.TreeCompleteness("b", ot.COMPLETENESS_PARTIAL, "x", 1, 0, ("p",), (), 0)
    unknown = ot.TreeCompleteness("c", ot.COMPLETENESS_UNKNOWN, "y", 0, 0, (), (), 0)

    assert ot.combine_completeness((complete, complete))[0] == ot.COMPLETENESS_COMPLETE
    assert ot.combine_completeness((complete, partial))[0] == ot.COMPLETENESS_PARTIAL
    assert ot.combine_completeness((complete, partial, unknown))[0] == ot.COMPLETENESS_UNKNOWN
    assert ot.combine_completeness(())[0] == ot.COMPLETENESS_UNKNOWN


# ---------------------------------------------------------------------------
# --runtime-metrics
# ---------------------------------------------------------------------------


def test_runtime_metrics_reports_partial_coverage_rather_than_assuming_zero(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    for tree in (before, after):
        write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")
        write_pair(tree, EQ_SAMPLE, "f", "B3", "B4", "UNKNOWN")
    write_runtime_receipt(before, EQ_SAMPLE, "f", "B1", "B2", 10.0)
    write_runtime_receipt(after, EQ_SAMPLE, "f", "B1", "B2", 4.0)

    keys = sorted(set(load_pair_outcomes(before)) | set(load_pair_outcomes(after)))
    report = ot.build_runtime_metrics(before, after, keys)

    assert report.pairs == 2
    assert len(report.deltas) == 1
    assert report.complete is False
    assert report.faster == 1 and report.slower == 0
    assert report.median_delta() == pytest.approx(-6.0)


def test_runtime_metrics_with_no_receipts_is_not_a_zero_delta(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    for tree in (before, after):
        write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")

    keys = sorted(load_pair_outcomes(after))
    report = ot.build_runtime_metrics(before, after, keys)

    assert report.complete is False
    assert report.median_delta() is None
    assert "coverage complete: False" in "\n".join(ot.format_runtime_metrics(report))


def test_a_receipt_whose_identity_disagrees_with_its_path_is_dropped(tmp_path):
    tree = tmp_path / "tree"
    write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")
    write_runtime_receipt(tree, EQ_SAMPLE, "f", "B1", "B2", 1.0, function_name="other")

    elapsed, unusable = ot.load_runtime_metrics(tree)

    assert elapsed == {} and unusable == 1


def test_runtime_metrics_never_change_the_exit_code(tmp_path):
    """時間差だけでは fail させない（`--fail-on-change` の意味を動かさない）。"""
    before, after = tmp_path / "before", tmp_path / "after"
    for tree in (before, after):
        write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")
    write_runtime_receipt(before, EQ_SAMPLE, "f", "B1", "B2", 10.0)
    write_runtime_receipt(after, EQ_SAMPLE, "f", "B1", "B2", 900.0)

    assert ot.main([
        "--before", str(before), "--after", str(after),
        "--runtime-metrics", "--fail-on-change",
    ]) == 0


# ---------------------------------------------------------------------------
# backward compatibility
# ---------------------------------------------------------------------------


def test_default_output_and_json_are_unchanged_by_the_new_sections(tmp_path, capsys):
    before, after = tmp_path / "before", tmp_path / "after"
    for tree in (before, after):
        write_pair(tree, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", reasons=("a",))
        write_publication_manifest(tree, [f"{EQ_SAMPLE}/f/f_B1_B2.pair-status.json"])
    plain, opted_in = tmp_path / "plain.json", tmp_path / "opted.json"

    assert ot.main([
        "--before", str(before), "--after", str(after), "--json", str(plain),
    ]) == 0
    plain_text = capsys.readouterr().out
    assert ot.main([
        "--before", str(before), "--after", str(after), "--json", str(opted_in),
        "--axes", "--reason-sets", "--manifest", "--runtime-metrics",
    ]) == 0
    opted_text = capsys.readouterr().out

    plain_payload = json.loads(plain.read_text(encoding="utf-8"))
    opted_payload = json.loads(opted_in.read_text(encoding="utf-8"))
    # 既定の出力・JSON は完全に据え置き、新 section は付け足しにとどまる。
    assert opted_text.startswith(plain_text)
    assert set(plain_payload) == {"pairs", "changed", "outcomes", "matrix", "rows"}
    assert all(plain_payload[key] == opted_payload[key] for key in plain_payload)
    assert set(opted_payload) - set(plain_payload) == {
        "axes", "reason_sets", "completeness", "runtime_metrics",
    }


def test_fail_on_change_keeps_its_meaning_with_the_new_sections(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    write_pair(before, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", reasons=("a",))
    write_pair(after, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN", reasons=("b",))

    # reason 集合だけが変わった pair は、従来どおり outcome の変化ではない。
    assert ot.main([
        "--before", str(before), "--after", str(after),
        "--reason-sets", "--axes", "--fail-on-change",
    ]) == 0

    write_pair(after, EQ_SAMPLE, "f", "B1", "B2", "EQUIVALENT", reasons=("b",))
    assert ot.main([
        "--before", str(before), "--after", str(after),
        "--reason-sets", "--axes", "--fail-on-change",
    ]) == 2


def test_losing_a_contradicted_decision_is_not_reported_as_a_regression(tmp_path):
    """正解に反する決定が消えたのを「退行」と数えない（改善にも数えない）。"""
    before, after = tmp_path / "before", tmp_path / "after"
    write_pair(before, EQ_SAMPLE, "f", "B1", "B2", "NOT_EQ")
    write_pair(after, EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")

    report = ot.build_axes(load_pair_outcomes(before), load_pair_outcomes(after))

    assert report.transition_counts()[ot.TRANSITION_REGRESSION] == 0
    assert report.transition_counts()[ot.TRANSITION_IMPROVEMENT] == 0
    assert report.transition_notes()[ot.TRANSITION_NOTE_LOST_CONTRADICTED] == 1
    # 消えた側が違反だった事実は正解軸に残る。
    assert report.correctness_counts("before")[ot.CORRECTNESS_CONTRADICTED] == 1


def test_the_unconfirmed_note_is_not_used_for_a_contradicted_decision():
    """`decided_but_unconfirmed` は「確認できなかった」だけに付く名前。"""
    both_wrong = ot.classify_transition(
        "EQUIVALENT", "NOT_EQ", ot.CORRECTNESS_CONTRADICTED, ot.CORRECTNESS_CONTRADICTED,
    )
    unconfirmed = ot.classify_transition(
        "EQUIVALENT", "NOT_EQ", ot.CORRECTNESS_UNCONFIRMED, ot.CORRECTNESS_UNCONFIRMED,
    )

    assert both_wrong == (ot.TRANSITION_OTHER, ())
    assert unconfirmed == (
        ot.TRANSITION_OTHER, (ot.TRANSITION_NOTE_DECIDED_BUT_UNCONFIRMED,),
    )


def test_ground_truth_manifest_override_is_used_for_both_sides(tmp_path):
    """tree 直下に manifest が無くても、明示した ground truth で正解軸を出せる。"""
    before, after = tmp_path / "before", tmp_path / "after"
    for tree in (before, after):
        write_pair(tree, NEQ_SAMPLE, "g", "N_B1", "O_B1", "NOT_EQ")
    manifest_path = tmp_path / "function_diff_manifest.json"
    manifest_path.write_text(json.dumps({
        "schema": "eqbench-function-diff-manifest-v1",
        "samples": {NEQ_SAMPLE: {"parse_status": "ok", "functions": {"g": {
            "source_relation": "changed", "source_impact": "MAY_AFFECT",
            "semantic_ground_truth": "CONFIRMED_NOT_EQ",
            "ground_truth_evidence": "reviewed",
        }}}},
    }), encoding="utf-8")

    without = ot.build_report_sections(before, after, axes=True)[1]["axes"]
    with_override = ot.build_report_sections(
        before, after, axes=True, ground_truth_manifest=manifest_path,
    )[1]["axes"]

    assert without.after_ground_truth == ot.GROUND_TRUTH_ABSENT
    assert without.correctness_counts("after")[ot.CORRECTNESS_UNCONFIRMED] == 1
    assert with_override.after_ground_truth == str(manifest_path)
    assert with_override.correctness_counts("after")[ot.CORRECTNESS_CONSISTENT] == 1
    assert with_override.correctness_counts("before")[ot.CORRECTNESS_CONSISTENT] == 1
