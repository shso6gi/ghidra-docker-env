from __future__ import annotations

import ast
import copy
import json
from pathlib import Path
import subprocess

import pytest

from scripts.function_tracer_pcode.validation.phase7_legacy_baseline import (
    decode_and_validate_phase7_legacy_baseline,
)
from scripts.function_tracer_pcode.validation.result_summary import (
    classify_canonical_log_text,
    classify_log_text,
)


BASELINE_COMMIT = "635637c10746f7b7436bec6e3d898ef16e91c546"
PHASE9 = "artifacts/unknown_taxonomy_v2/phase9"


def _root() -> Path:
    return Path(__file__).resolve().parents[4]


def _current_json(relative: str):
    return json.loads((_root() / relative).read_text(encoding="utf-8"))


def _baseline_json(relative: str):
    raw = subprocess.check_output(
        ["git", "show", f"{BASELINE_COMMIT}:{relative}"], cwd=_root(), text=True
    )
    return json.loads(raw)


def _semantic_phase9_projection(source):
    payload = copy.deepcopy(source)
    payload.pop("artifact_digest", None)
    binding = payload.get("all_five_source_bound_authority")
    if isinstance(binding, dict):
        binding.pop("phase8_artifact_digest", None)
        binding.pop("phase8_artifact_sha256", None)
    decisive = payload.get("eq_not_eq_decisive_receipts_unchanged_authority")
    if isinstance(decisive, dict):
        decisive.pop("phase8_artifact_digest", None)
        decisive.pop("phase8_artifact_sha256", None)
    internal_error = payload.get("internal_error_authority")
    if isinstance(internal_error, dict):
        internal_error.pop("phase8_artifact_digest", None)
    return payload


def _semantic_cleanup_projection(source):
    """Drop only identities reissued by a current authority materialization."""

    reissued_fields = {
        "artifact_digest",
        "occurrence_id",
        "proof_requirement_id",
        "receipt_digest",
        "execution_event_digest",
        "lifecycle_projection_digest",
        "premise_digest",
        "authority_input_digest",
        "focused_junit_sha256",
        "focused_test_source_sha256",
        "phase7_artifact_digest",
        "terminal_timeout_receipt_digest",
        # Exact query-authority join identities added after the cleanup
        # baseline.  They strengthen receipt binding without changing the
        # preserved decision, cause, requirement, or aggregate semantics.
        "region_receipt_digest",
        "projection_binding_ids",
    }

    def project(value):
        if isinstance(value, dict):
            return {
                key: project(item)
                for key, item in value.items()
                if key not in reissued_fields
            }
        if isinstance(value, list):
            return [project(item) for item in value]
        return value

    return project(copy.deepcopy(source))


def test_cleanup_preserves_decisions_causes_requirements_and_aggregates():
    exact_paths = (
        f"{PHASE9}/cause_lifecycle_snapshot.json",
        f"{PHASE9}/query_execution_receipts.json",
        f"{PHASE9}/legacy_coverage.json",
    )
    for relative in exact_paths:
        assert _semantic_cleanup_projection(
            _current_json(relative)
        ) == _semantic_cleanup_projection(_baseline_json(relative))

    bound_paths = (
        f"{PHASE9}/decision_receipt.json",
        f"{PHASE9}/decision_transition_matrix.json",
        f"{PHASE9}/reason_before_after.json",
    )
    for relative in bound_paths:
        assert _semantic_cleanup_projection(_semantic_phase9_projection(
            _current_json(relative)
        )) == _semantic_cleanup_projection(_semantic_phase9_projection(
            _baseline_json(relative)
        ))


def test_cleanup_preserves_unknown_timeout_conservation():
    decision = _current_json(f"{PHASE9}/decision_receipt.json")
    receipts = decision["receipts"]
    assert [item["outcome"] for item in receipts] == ["UNKNOWN", "TIMEOUT"]

    lifecycle = _current_json(f"{PHASE9}/cause_lifecycle_snapshot.json")
    for outcome in ("unknown", "timeout"):
        relation = lifecycle[outcome]
        causes = {
            (row["result_occurrence_id"], row["occurrence_id"], row["cause_id"])
            for row in relation["c_active"]
        }
        assert causes
        assert all("final_outcome" not in row for row in relation["c_active"])
        assert all("final_outcome" not in row for row in relation["q_open"])
        assert all(
            (row["result_occurrence_id"], row["occurrence_id"], row["cause_id"])
            in causes
            for row in relation["q_open"]
        )

    executions = _current_json(f"{PHASE9}/query_execution_receipts.json")
    assert executions["terminal_timeout_receipt_count"] == 1
    assert executions["final_timeout_result_count"] == 1


def test_cleanup_removes_only_dead_migration_exports_and_synthetic_timeout_writer():
    package_init = _root() / "scripts/function_tracer_pcode/equivalence/v2/__init__.py"
    tree = ast.parse(package_init.read_text(encoding="utf-8"))
    assert not any(
        isinstance(node, ast.ImportFrom)
        and any(alias.name == "*" for alias in node.names)
        for node in ast.walk(tree)
    )

    shell = (_root() / "scripts/validation_matrix_common.sh").read_text(
        encoding="utf-8"
    )
    assert "validation_append_pair_process_timeout_payload" not in shell
    assert '"is_timeout": true' not in shell


def test_cleanup_keeps_lossless_legacy_reading_but_not_legacy_decision_authority():
    manifest = _current_json(
        "artifacts/unknown_taxonomy_v2/phase7/legacy-baseline-manifest.json"
    )
    saved_summaries = tuple(
        (
            _root()
            / "logs/EqBench/all_eq_matrix_current"
        ).rglob("results_summary.txt")
    )
    if len(saved_summaries) != 411:
        pytest.skip(
            "requires the external 411-summary legacy diagnostic fixture"
        )
    decoded = decode_and_validate_phase7_legacy_baseline(_root(), manifest)
    assert len(decoded) == 411

    legacy_timeout = "\n".join((
        "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
        '{"is_equivalent":null,"is_timeout":true}',
        "=== EQUIVALENCE_RESULT_JSON_END ===",
    ))
    assert classify_log_text(legacy_timeout, matrix_context=True) == "TIMEOUT"
    assert classify_canonical_log_text(legacy_timeout, matrix_context=True) == "INCOMPLETE"
