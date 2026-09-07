"""reporting.benchmark_validation_gate (Issue #104 runner benchmark gate)."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import benchmark_validation_gate as gate
from scripts.function_tracer_pcode.reporting import run_health_summary
from scripts.function_tracer_pcode.reporting.result_summary import (
    BENCHMARK_VALIDATION_KEY,
    format_run_health_summary,
)

REPO_ROOT = Path(__file__).resolve().parents[4]


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


def _entry(relation: str, impact: str, truth: str = "UNKNOWN", evidence=None) -> dict:
    return {
        "source_relation": relation,
        "source_impact": impact,
        "impact_details": [],
        "semantic_ground_truth": truth,
        "ground_truth_evidence": evidence,
    }


NEQ = "fam/prog/Neq/newV-oldV"
EQ = "fam/prog/Eq/newV"


def _manifest(tmp_path: Path) -> Path:
    payload = {
        "schema": gate.MANIFEST_SCHEMA,
        "samples": {
            NEQ: {
                "lane": "Neq",
                "parse_status": "ok",
                "functions": {
                    "confirmed": _entry("SOURCE_CHANGED", "DIRECTLY_CHANGED", "CONFIRMED_NOT_EQ", "cex"),
                    "changed": _entry("SOURCE_CHANGED", "DIRECTLY_CHANGED"),
                    "caller": _entry("SOURCE_IDENTICAL", "CALLS_CHANGED_CALLEE"),
                    "identical": _entry("SOURCE_IDENTICAL", "NO_KNOWN_SOURCE_IMPACT"),
                    "reviewed_eq": _entry("SOURCE_CHANGED", "DIRECTLY_CHANGED", "CONFIRMED_EQ", "proof"),
                },
            },
            "fam/broken/Neq/newV-oldV": {"lane": "Neq", "parse_status": "failed", "functions": {}},
            EQ: {
                "lane": "Eq",
                "parse_status": "ok",
                "functions": {"f": _entry("SOURCE_IDENTICAL", "NO_KNOWN_SOURCE_IMPACT", "CONFIRMED_EQ", "eq")},
            },
        },
    }
    path = tmp_path / "function_diff_manifest.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def _kinds(report: gate.GateReport) -> dict:
    return {
        (c.record.sample_identity, c.record.function_name, c.record.pair_id): c.kind
        for c in report.classified
    }


def test_classification_matrix(tmp_path):
    root = tmp_path / "results"
    write_pair_status(root, EQ, "f", "B1", "B2", "NOT_EQ")
    write_pair_status(root, EQ, "f", "B1", "B3", "EQUIVALENT")
    write_pair_status(root, EQ, "f", "B1", "B4", "UNKNOWN")
    write_pair_status(root, NEQ, "confirmed", "N_B1", "O_B1", "EQUIVALENT")
    write_pair_status(root, NEQ, "confirmed", "N_B2", "O_B2", "NOT_EQ")
    write_pair_status(root, NEQ, "changed", "N_B1", "O_B1", "EQUIVALENT")
    write_pair_status(root, NEQ, "caller", "N_B1", "O_B1", "EQUIVALENT")
    write_pair_status(root, NEQ, "identical", "N_B1", "O_B1", "EQUIVALENT")
    write_pair_status(root, NEQ, "identical", "N_B2", "O_B2", "NOT_EQ")
    write_pair_status(root, NEQ, "reviewed_eq", "N_B1", "O_B1", "EQUIVALENT")
    write_pair_status(root, NEQ, "unlisted", "N_B1", "O_B1", "EQUIVALENT")
    write_pair_status(root, NEQ, "unlisted", "N_B2", "O_B2", "NOT_EQ")
    write_pair_status(root, "fam/broken/Neq/newV-oldV", "f", "N_B1", "O_B1", "EQUIVALENT")
    write_pair_status(root, "fam/missing/Neq/newV-oldV", "f", "N_B1", "O_B1", "EQUIVALENT")
    write_pair_status(root, "fam/missing/Neq/newV-oldV", "f", "N_B2", "O_B2", "TIMEOUT")
    write_pair_status(root, "fam/prog/other/newV", "f", "B1", "B2", "EQUIVALENT")

    manifest = gate.FunctionDiffManifest.load(_manifest(tmp_path))
    report = gate.build_gate_report([root], manifest, manifest_path="m.json")
    kinds = _kinds(report)
    assert kinds[(EQ, "f", "B1_B2")] == gate.KIND_EQ_NOT_EQ
    assert kinds[(EQ, "f", "B1_B3")] == gate.KIND_NOT_APPLICABLE
    assert kinds[(EQ, "f", "B1_B4")] == gate.KIND_NOT_APPLICABLE
    assert kinds[(NEQ, "confirmed", "N_B1_O_B1")] == gate.KIND_NEQ_CONFIRMED_NOT_EQ_EQUIVALENT
    assert kinds[(NEQ, "confirmed", "N_B2_O_B2")] == gate.KIND_NOT_APPLICABLE
    assert kinds[(NEQ, "changed", "N_B1_O_B1")] == gate.KIND_SUSPICIOUS_EQ
    assert kinds[(NEQ, "caller", "N_B1_O_B1")] == gate.KIND_SUSPICIOUS_EQ
    assert kinds[(NEQ, "identical", "N_B1_O_B1")] == gate.KIND_BENIGN_EQ_NO_IMPACT
    assert kinds[(NEQ, "identical", "N_B2_O_B2")] == gate.KIND_SUSPICIOUS_NOT_EQ
    assert kinds[(NEQ, "reviewed_eq", "N_B1_O_B1")] == gate.KIND_BENIGN_EQ_CONFIRMED
    assert kinds[(NEQ, "unlisted", "N_B1_O_B1")] == gate.KIND_NEQ_EQUIVALENT_UNMAPPED
    assert kinds[(NEQ, "unlisted", "N_B2_O_B2")] == gate.KIND_NOT_APPLICABLE
    assert kinds[("fam/broken/Neq/newV-oldV", "f", "N_B1_O_B1")] == gate.KIND_NEQ_EQUIVALENT_UNMAPPED
    assert kinds[("fam/missing/Neq/newV-oldV", "f", "N_B1_O_B1")] == gate.KIND_NEQ_EQUIVALENT_UNMAPPED
    assert kinds[("fam/missing/Neq/newV-oldV", "f", "N_B2_O_B2")] == gate.KIND_NOT_APPLICABLE
    unlabelled = [c for c in report.classified if c.record.sample_identity == "fam/prog/other/newV"]
    assert [c.kind for c in unlabelled] == [gate.KIND_NOT_APPLICABLE]

    assert report.status == gate.GATE_STATUS_FAIL
    section = report.health_section()
    assert section["hard_violations"] == {
        gate.KIND_EQ_NOT_EQ: 1,
        gate.KIND_NEQ_CONFIRMED_NOT_EQ_EQUIVALENT: 1,
        gate.KIND_NEQ_EQUIVALENT_UNMAPPED: 3,
    }
    assert section["suspicious"] == {gate.KIND_SUSPICIOUS_EQ: 2, gate.KIND_SUSPICIOUS_NOT_EQ: 1}
    assert section["benign"] == {gate.KIND_BENIGN_EQ_NO_IMPACT: 1, gate.KIND_BENIGN_EQ_CONFIRMED: 1}
    assert section["outcomes_by_label"]["Eq"] == {"EQUIVALENT": 1, "NOT_EQ": 1, "UNKNOWN": 1}
    text = gate.format_gate_report(report)
    assert "GATE: FAIL (5 hard violations, 3 suspicious)" in text
    assert "soundness_violations: eq_not_eq=1 neq_equivalent=1 neq_equivalent_unmapped=3" in text
    rows = report.as_dict()["rows"]
    assert {row["kind"] for row in rows} == set(gate.HARD_VIOLATION_KINDS + gate.SUSPICIOUS_KINDS)


def test_suspicious_only_passes_unless_requested(tmp_path):
    root = tmp_path / "results"
    write_pair_status(root, NEQ, "changed", "N_B1", "O_B1", "EQUIVALENT")
    write_pair_status(root, NEQ, "identical", "N_B1", "O_B1", "EQUIVALENT")
    manifest = gate.FunctionDiffManifest.load(_manifest(tmp_path))
    report = gate.build_gate_report([root], manifest)
    assert report.status == gate.GATE_STATUS_PASS
    assert report.exit_code == gate.EXIT_PASS
    strict = gate.build_gate_report([root], manifest, fail_on_suspicious=True)
    assert strict.status == gate.GATE_STATUS_FAIL
    assert strict.exit_code == gate.EXIT_VIOLATION


def test_without_manifest_every_neq_equivalent_is_unmapped(tmp_path):
    root = tmp_path / "results"
    write_pair_status(root, NEQ, "identical", "N_B1", "O_B1", "EQUIVALENT")
    report = gate.build_gate_report([root], None)
    assert [c.kind for c in report.classified] == [gate.KIND_NEQ_EQUIVALENT_UNMAPPED]
    assert report.status == gate.GATE_STATUS_FAIL


def test_empty_tree_is_not_a_pass(tmp_path):
    root = tmp_path / "results"
    root.mkdir()
    report = gate.build_gate_report([root], gate.FunctionDiffManifest.load(_manifest(tmp_path)))
    assert report.status == gate.GATE_STATUS_EMPTY
    assert report.exit_code == gate.EXIT_EMPTY


def test_manifest_schema_is_checked(tmp_path):
    path = tmp_path / "m.json"
    path.write_text(json.dumps({"schema": "other", "samples": {}}), encoding="utf-8")
    with pytest.raises(ValueError, match="schema"):
        gate.FunctionDiffManifest.load(path)


def test_cli_merges_health_summary_and_exit_codes(tmp_path):
    root = tmp_path / "results"
    write_pair_status(root, NEQ, "identical", "N_B1", "O_B1", "EQUIVALENT")
    write_pair_status(root, NEQ, "changed", "N_B1", "O_B1", "EQUIVALENT")
    health_json = root / "run_health_summary.json"
    health_json.write_text(
        json.dumps({"total_results": 2, "final_result_counts": {"EQ": 2}, "unknown_units": 0}),
        encoding="utf-8",
    )
    health_text = root / "run_health_summary.txt"
    report_json = root / "benchmark_validation_gate.json"
    argv = [
        str(root), "--manifest", str(_manifest(tmp_path)), "--json", str(report_json),
        "--health-summary-json", str(health_json), "--health-summary-text", str(health_text),
    ]
    assert gate.main(argv) == gate.EXIT_PASS
    merged = json.loads(health_json.read_text())
    assert merged["total_results"] == 2  # existing keys preserved
    assert merged[BENCHMARK_VALIDATION_KEY]["gate"] == "PASS"
    assert merged[BENCHMARK_VALIDATION_KEY]["suspicious"][gate.KIND_SUSPICIOUS_EQ] == 1
    text = health_text.read_text()
    assert "soundness_violations: eq_not_eq=0 neq_equivalent=0 neq_equivalent_unmapped=0" in text
    assert f"{gate.KIND_SUSPICIOUS_EQ}: 1" in text
    assert "benchmark_gate: PASS (pairs=2)" in text
    assert text.strip() == format_run_health_summary(merged).strip()
    assert json.loads(report_json.read_text())["gate"] == "PASS"

    assert gate.main(argv + ["--fail-on-suspicious"]) == gate.EXIT_VIOLATION
    assert json.loads(health_json.read_text())[BENCHMARK_VALIDATION_KEY]["gate"] == "FAIL"

    write_pair_status(root, EQ, "f", "B1", "B2", "NOT_EQ")
    assert gate.main(argv) == gate.EXIT_VIOLATION
    assert gate.main([str(tmp_path / "nope")]) == gate.EXIT_EMPTY
    assert gate.main([str(root), "--manifest", str(tmp_path / "missing.json")]) == gate.EXIT_EMPTY


def test_offline_health_summary_keeps_gate_section_when_json_reused(tmp_path):
    health = {
        "total_results": 1,
        "final_result_counts": {"EQ": 1},
        BENCHMARK_VALIDATION_KEY: {
            "gate": "PASS", "pairs": 1,
            "hard_violations": {"eq_not_eq": 0, "neq_confirmed_not_eq_equivalent": 0, "neq_equivalent_unmapped": 0},
            "suspicious": {}, "benign": {},
        },
    }
    text_path = tmp_path / "health.txt"
    json_path = tmp_path / "health.json"
    run_health_summary.write_health_outputs(health, output_json=json_path, output_text=text_path)
    assert "benchmark_gate: PASS (pairs=1)" in text_path.read_text()
    assert json.loads(json_path.read_text())[BENCHMARK_VALIDATION_KEY]["gate"] == "PASS"


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash required")
def test_bash_runner_helper_builds_manifest_runs_gate_and_sets_status(tmp_path):
    bench = tmp_path / "bench"
    neq = bench / "fam/prog/Neq"
    neq.mkdir(parents=True)
    (neq / "oldV.c").write_text("int changed(int x) { return x; }\nint same(int x) { return 1; }\n")
    (neq / "newV.c").write_text("int changed(int x) { return x + 1; }\nint same(int x) { return 1; }\n")
    out = tmp_path / "out"
    write_pair_status(out, NEQ, "same", "N_B1", "O_B1", "EQUIVALENT")
    write_pair_status(out, NEQ, "changed", "N_B1", "O_B1", "NOT_EQ")
    (out / "run_health_summary.json").write_text(json.dumps({"total_results": 2}), encoding="utf-8")

    def run(env_extra: dict) -> tuple[int, str, dict]:
        env = dict(os.environ, PYTHON_BIN=sys.executable, **env_extra)
        result = subprocess.run(
            [
                "bash", "-euo", "pipefail", "-c",
                'source scripts/validation_matrix_common.sh; '
                'validation_run_benchmark_gate "$1" "$2" "$3"; '
                'echo "STATUS=$VALIDATION_BENCHMARK_GATE_STATUS FAILURES=$VALIDATION_BENCHMARK_GATE_FAILURES"',
                "bash", str(out), str(bench), str(REPO_ROOT),
            ],
            cwd=REPO_ROOT, env=env, check=False, text=True, capture_output=True,
        )
        health = json.loads((out / "run_health_summary.json").read_text())
        return result.returncode, result.stdout + result.stderr, health

    code, output, health = run({})
    assert code == 0, output
    assert "STATUS=PASS FAILURES=0" in output
    assert (out / "function_diff_manifest.json").is_file()
    assert (out / "benchmark_validation_gate.json").is_file()
    assert (out / "benchmark_validation_gate.txt").is_file()
    assert health["total_results"] == 2
    assert health[BENCHMARK_VALIDATION_KEY]["benign"][gate.KIND_BENIGN_EQ_NO_IMPACT] == 1
    assert "benchmark_gate: PASS" in (out / "run_health_summary.txt").read_text()

    write_pair_status(out, NEQ, "changed", "N_B2", "O_B2", "EQUIVALENT")
    code, output, health = run({"EQBENCH_BENCHMARK_GATE_FAIL_ON_SUSPICIOUS": "1"})
    assert code == 0, output  # the helper never aborts the runner; it reports
    assert "STATUS=FAIL FAILURES=1" in output
    assert health[BENCHMARK_VALIDATION_KEY]["gate"] == "FAIL"

    code, output, _ = run({"EQBENCH_BENCHMARK_GATE": "0"})
    assert code == 0 and "STATUS=SKIPPED FAILURES=0" in output

    code, output, _ = run({"EQBENCH_BENCHMARK_GATE": "1"})
    assert "STATUS=PASS FAILURES=0" in output  # suspicious only counts by default

    shutil.rmtree(bench)
    bench.mkdir()
    code, output, _ = run({})
    assert code == 0, output
    # An empty benchmark tree yields an empty manifest: the Neq EQUIVALENT is unmapped.
    assert "STATUS=FAIL FAILURES=1" in output
