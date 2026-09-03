import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import outcome_transition, soundness_gate
from scripts.function_tracer_pcode.reporting.pair_outcomes import (
    OUTCOME_INVALID,
    OUTCOME_MISSING,
    benchmark_label,
    identity_from_status_path,
    load_pair_outcomes,
)


def write_pair_status(root: Path, sample: str, function: str, left: str, right: str, outcome: str) -> Path:
    path = root / sample / function / f"{function}_{left}_{right}.pair-status.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "canonical_outcome": outcome,
                "pair_execution_target": {
                    "sample_identity": sample,
                    "function_name": function,
                    "left_binary_id": left,
                    "right_binary_id": right,
                },
            }
        ),
        encoding="utf-8",
    )
    return path


def test_benchmark_label_reads_dataset_directory_only():
    assert benchmark_label("CLEVER/LoopSub/Eq/new") == "Eq"
    assert benchmark_label("raytrace/sphere/Neq/newV-oldV") == "Neq"
    assert benchmark_label("Neqish/Eqish/other") == "unlabelled"


def test_load_pair_outcomes_rejects_duplicate_status(tmp_path: Path):
    write_pair_status(tmp_path, "a/b/Eq/newV", "f", "B1", "B2", "UNKNOWN")
    dup = tmp_path / "copy" / "f" / "f_B1_B2.pair-status.json"
    dup.parent.mkdir(parents=True)
    dup.write_text((tmp_path / "a/b/Eq/newV/f/f_B1_B2.pair-status.json").read_text(), encoding="utf-8")
    with pytest.raises(ValueError, match="duplicate pair status"):
        load_pair_outcomes(tmp_path)


def test_invalid_pair_status_recovers_identity_from_path(tmp_path: Path):
    invalid = tmp_path / "a/b/Neq/newV-oldV/h/h_N_B2_O_B4.pair-status.json"
    invalid.parent.mkdir(parents=True)
    invalid.write_text(json.dumps({"classification_valid": False, "error_kind": "X"}), encoding="utf-8")
    truncated = tmp_path / "a/b/Eq/newV/f/f_B1_B9.pair-status.json"
    truncated.parent.mkdir(parents=True)
    truncated.write_text("{\"canonical_outcome\": \"UNK", encoding="utf-8")

    records = load_pair_outcomes(tmp_path)

    assert records[("a/b/Neq/newV-oldV", "h", "N_B2", "O_B4")].outcome == OUTCOME_INVALID
    assert records[("a/b/Eq/newV", "f", "B1", "B9")].outcome == OUTCOME_INVALID
    assert soundness_gate.build_gate_report([tmp_path]).violations == ()
    with pytest.raises(ValueError, match="unrecognised pair id"):
        identity_from_status_path(tmp_path, tmp_path / "a/b/Eq/newV/f/f_B1_B2_B3.pair-status.json")


def test_transition_matrix_counts_changed_and_missing_pairs(tmp_path: Path):
    before, after = tmp_path / "before", tmp_path / "after"
    write_pair_status(before, "a/b/Eq/newV", "f", "B1", "B2", "UNKNOWN")
    write_pair_status(after, "a/b/Eq/newV", "f", "B1", "B2", "EQUIVALENT")
    write_pair_status(before, "a/b/Eq/newV", "f", "B1", "B9", "TIMEOUT")
    write_pair_status(after, "a/b/Eq/newV", "f", "B1", "B9", "TIMEOUT")
    write_pair_status(before, "a/b/Eq/newV", "g", "B1", "B2", "ERROR")
    write_pair_status(after, "c/d/Neq/newV-oldV", "h", "N_B1", "O_B1", "NOT_EQ")

    report = outcome_transition.build_transition(load_pair_outcomes(before), load_pair_outcomes(after))

    assert report.matrix == {
        ("UNKNOWN", "EQUIVALENT"): 1,
        ("TIMEOUT", "TIMEOUT"): 1,
        ("ERROR", OUTCOME_MISSING): 1,
        (OUTCOME_MISSING, "NOT_EQ"): 1,
    }
    assert [(r.function_name, r.pair_id, r.before, r.after) for r in report.changed_rows] == [
        ("f", "B1_B2", "UNKNOWN", "EQUIVALENT"),
        ("g", "B1_B2", "ERROR", OUTCOME_MISSING),
        ("h", "N_B1_O_B1", OUTCOME_MISSING, "NOT_EQ"),
    ]
    text = outcome_transition.format_transition(report, changed_only=True)
    assert "Pairs compared: 4 (changed: 3)" in text
    assert "* a/b/Eq/newV f B1_B2: UNKNOWN -> EQUIVALENT" in text
    assert "f B1_B9" not in text


def test_transition_cli_writes_json_and_fails_on_change_only_when_asked(tmp_path: Path, capsys):
    before, after = tmp_path / "before", tmp_path / "after"
    write_pair_status(before, "a/b/Eq/newV", "f", "B1", "B2", "UNKNOWN")
    write_pair_status(after, "a/b/Eq/newV", "f", "B1", "B2", "UNKNOWN")
    out = tmp_path / "t.json"

    assert outcome_transition.main(["--before", str(before), "--after", str(after), "--json", str(out), "--fail-on-change"]) == 0
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["pairs"] == 1 and payload["changed"] == 0
    assert payload["matrix"] == [{"before": "UNKNOWN", "after": "UNKNOWN", "count": 1}]

    write_pair_status(after, "a/b/Eq/newV", "f", "B1", "B2", "EQUIVALENT")
    assert outcome_transition.main(["--before", str(before), "--after", str(after)]) == 0
    assert outcome_transition.main(["--before", str(before), "--after", str(after), "--fail-on-change"]) == 2
    assert outcome_transition.main(["--before", str(before), "--after", str(tmp_path / "nope")]) == 1
    assert "not a directory" in capsys.readouterr().err


def test_soundness_gate_flags_neq_equivalent_and_eq_not_eq_only(tmp_path: Path):
    eq, neq = tmp_path / "eq", tmp_path / "neq"
    write_pair_status(eq, "a/b/Eq/newV", "f", "B1", "B2", "EQUIVALENT")
    write_pair_status(eq, "a/b/Eq/newV", "f", "B1", "B9", "UNKNOWN")
    write_pair_status(eq, "a/b/Eq/newV", "f", "B3", "B11", "NOT_EQ")
    write_pair_status(neq, "c/d/Neq/newV-oldV", "h", "N_B1", "O_B1", "NOT_EQ")
    write_pair_status(neq, "c/d/Neq/newV-oldV", "h", "N_B2", "O_B4", "EQUIVALENT")
    write_pair_status(neq, "c/d/Neq/newV-oldV", "h", "N_B5", "O_B7", "TIMEOUT")
    write_pair_status(neq, "c/d/Neq/newV-oldV", "h", "N_B9", "O_B9", "ERROR")

    report = soundness_gate.build_gate_report([eq, neq])

    assert [(r.label, r.function_name, r.pair_id, r.outcome) for r in report.violations] == [
        ("Eq", "f", "B3_B11", "NOT_EQ"),
        ("Neq", "h", "N_B2_O_B4", "EQUIVALENT"),
    ]
    assert not report.passed
    text = soundness_gate.format_gate_report(report)
    assert "GATE: FAIL (2 violations)" in text
    assert "Neq sample judged EQUIVALENT: c/d/Neq/newV-oldV h N_B2_O_B4" in text


def test_soundness_gate_cli_exit_codes(tmp_path: Path):
    eq = tmp_path / "eq"
    write_pair_status(eq, "a/b/Eq/newV", "f", "B1", "B2", "EQUIVALENT")
    write_pair_status(eq, "a/b/Eq/newV", "f", "B1", "B9", "UNKNOWN")
    empty = tmp_path / "empty"
    empty.mkdir()
    out = tmp_path / "gate.json"

    assert soundness_gate.main([str(eq), "--json", str(out)]) == soundness_gate.EXIT_PASS
    assert json.loads(out.read_text(encoding="utf-8"))["passed"] is True
    assert soundness_gate.main([str(empty)]) == soundness_gate.EXIT_EMPTY
    assert soundness_gate.main([str(tmp_path / "missing")]) == soundness_gate.EXIT_EMPTY

    write_pair_status(eq, "a/b/Eq/newV", "f", "B3", "B11", "NOT_EQ")
    assert soundness_gate.main([str(eq), "--json", str(out)]) == soundness_gate.EXIT_VIOLATION
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["violations"] == 1 and payload["violation_rows"][0]["pair_id"] == "B3_B11"


def test_subset_manifest_is_consistent_with_full_scope():
    reporting = Path(__file__).resolve().parents[2] / "reporting"
    manifest = json.loads((reporting / "eqbench_subset.json").read_text(encoding="utf-8"))
    scope = json.loads((reporting / "eqbench_full_scope.json").read_text(encoding="utf-8"))

    assert manifest["schema"] == "eqbench-measurement-subset-v1"
    assert manifest["observed_baseline"]["non_authoritative"] is True
    assert manifest["run_settings"]["PARALLEL_JOBS"] == 20
    assert manifest["run_settings"]["EQBENCH_RESOURCE_ADMISSION"] == 0
    assert len(manifest["eq"]["sources"]) == len(set(manifest["eq"]["sources"]))
    assert len(manifest["neq"]["sources"]) == len(set(manifest["neq"]["sources"]))
    assert all(benchmark_label(s) == "Eq" for s in manifest["eq"]["sources"])
    assert all(benchmark_label(s) == "Neq" for s in manifest["neq"]["sources"])
    full_sources = {p[: -len(".c")] for p in scope["expected_functions"]}
    assert set(manifest["eq"]["sources"]) <= full_sources
    ids = set(scope["expected_binary_ids"])
    for pair_id in manifest["eq"]["pair_ids"]:
        left, right = pair_id.split("_")
        assert left in ids and right in ids and left != right
    for pair_id in manifest["neq"]["pair_ids"]:
        assert pair_id.startswith("N_B") and "_O_B" in pair_id
    for row in manifest["observed_baseline"]["eq"]:
        assert row["sample_identity"] in manifest["eq"]["sources"]
        assert row["pair_id"] in manifest["eq"]["pair_ids"]
    for row in manifest["observed_baseline"]["neq"]:
        assert row["sample_identity"] in manifest["neq"]["sources"]
        assert row["pair_id"] in manifest["neq"]["pair_ids"]
