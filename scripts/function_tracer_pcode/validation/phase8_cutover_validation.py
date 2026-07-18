"""Build and validate source-bound Phase 8 five-value cutover evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
from typing import Any, Mapping
from xml.etree import ElementTree

from ..equivalence.v2.contracts import Outcome, authority_digest
from ..equivalence.v2.phase8_cutover import (
    BATCH_RESUME_MATRIX,
    CLI_EXIT_MATRIX,
    RETRY_FALLBACK_MATRIX,
    rematerialize_process_timeout_decision,
)


VALIDATION_KIND = "unknown-taxonomy-v2-phase8-five-value-cutover-v1"

SOURCE_PATHS = (
    "Eq_new.sh",
    "eqbench_run_all_32jobs.sh",
    "scripts/validation_matrix_common.sh",
    "scripts/function_tracer_pcode/cli/commands/equivalence.py",
    "scripts/function_tracer_pcode/equivalence/checker.py",
    "scripts/function_tracer_pcode/equivalence/call_effect_preflight.py",
    "scripts/function_tracer_pcode/equivalence/result.py",
    "scripts/function_tracer_pcode/equivalence/obligations/stage_runner.py",
    "scripts/function_tracer_pcode/equivalence/strategies/monolithic.py",
    "scripts/function_tracer_pcode/equivalence/strategies/pairwise_services/orchestration_1.py",
    "scripts/function_tracer_pcode/equivalence/v2/phase8_cutover.py",
    "scripts/function_tracer_pcode/equivalence/v2/production_boundary.py",
    "scripts/function_tracer_pcode/equivalence/v2/production_context.py",
    "scripts/function_tracer_pcode/equivalence/v2/production_signals.py",
    "scripts/function_tracer_pcode/validation/result_summary.py",
    "scripts/function_tracer_pcode/validation/unknown_reason_summary.py",
    "scripts/function_tracer_pcode/validation/root_blocker_summary.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase8_cutover.py",
    "scripts/function_tracer_pcode/validation/phase8_cutover_validation.py",
)

WORKFLOW_TEST_PATHS = (
    "scripts/function_tracer_pcode/tests/unit/test_sat_decisiveness_recovery.py",
    "scripts/function_tracer_pcode/tests/unit/test_phase_retry_gates_flow.py",
    "scripts/function_tracer_pcode/tests/unit/test_phase_retry_gates_parametrized.py",
    "scripts/function_tracer_pcode/tests/unit/test_phase_retry_gates_retry_disabled.py",
    "scripts/function_tracer_pcode/tests/unit/test_selective_reanalysis.py",
    "scripts/function_tracer_pcode/tests/unit/test_debug_trace_integration_basics.py",
    "scripts/function_tracer_pcode/tests/unit/test_debug_trace_integration_pairwise.py",
    "scripts/function_tracer_pcode/tests/unit/test_debug_trace_integration_phase4.py",
    "scripts/function_tracer_pcode/tests/unit/test_yaml_golden_cases.py",
    "scripts/function_tracer_pcode/tests/unit/test_validation_result_summary.py",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _passing_junit(
    path: Path, *, minimum: int, required_names: tuple[str, ...] = (),
) -> Mapping[str, Any]:
    root = ElementTree.parse(path).getroot()
    suites = tuple(root.iter("testsuite"))
    cases = tuple(root.iter("testcase"))
    tests = sum(int(suite.attrib.get("tests", "0")) for suite in suites)
    if (
        tests != len(cases)
        or tests < minimum
        or any(int(suite.attrib.get("errors", "0")) for suite in suites)
        or any(int(suite.attrib.get("failures", "0")) for suite in suites)
        or any(int(suite.attrib.get("skipped", "0")) for suite in suites)
    ):
        raise ValueError("Phase 8 JUnit is not a complete passing run")
    names = {case.attrib.get("name", "") for case in cases}
    if any(name not in names for name in required_names):
        raise ValueError("Phase 8 JUnit lacks a required authority test")
    return {"test_count": tests, "test_names": names}


def _eqbench_dry_run_evidence(root: Path) -> Mapping[str, Any]:
    stored = root / "artifacts/unknown_taxonomy_v2/phase8/eqbench-dry-run"
    manifest = stored / "run_manifest.txt"
    sources = stored / "dry_run_sources.txt"
    if "dry_run=1" not in manifest.read_text(encoding="utf-8"):
        raise ValueError("stored EqBench evidence is not a dry run")
    if len(sources.read_text(encoding="utf-8").splitlines()) != 1:
        raise ValueError("stored EqBench dry run did not select exactly one sample")
    import tempfile

    with tempfile.TemporaryDirectory() as temporary:
        rerun = Path(temporary) / "output"
        environment = dict(os.environ)
        environment.update({
            "DRY_RUN": "1",
            "EQBENCH_MAX_SAMPLES": "1",
            "OUTPUT_BASE_DIR": str(rerun),
            "EQBENCH_TMPDIR": str(Path(temporary) / "tmp"),
        })
        completed = subprocess.run(
            ["./eqbench_run_all_32jobs.sh"], cwd=root, env=environment,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            check=True,
        )
        if (rerun / "dry_run_sources.txt").read_bytes() != sources.read_bytes():
            raise ValueError("EqBench dry-run source selection drifted")
    return {
        "command": "DRY_RUN=1 EQBENCH_MAX_SAMPLES=1 ./eqbench_run_all_32jobs.sh",
        "exit_code": completed.returncode,
        "run_manifest_sha256": _sha256(manifest),
        "dry_run_sources_sha256": _sha256(sources),
        "selected_source_count": 1,
    }


def _timeout_receipt(root: Path) -> Mapping[str, Any]:
    payload = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/real-process-timeout.json"
    )).read_text(encoding="utf-8"))
    durable = payload["durable_store"]
    import tempfile

    with tempfile.TemporaryDirectory() as temporary:
        store_root = Path(temporary) / "store"
        directory = store_root / durable["execution_nonce"]
        directory.mkdir(parents=True)
        for name, content in durable["files"].items():
            (directory / name).write_text(content, encoding="utf-8")
        supervisor_key = Path(temporary) / "supervisor.key"
        worker_key = Path(temporary) / "worker.key"
        supervisor_key.write_bytes(bytes.fromhex(durable["supervisor_signing_key_hex"]))
        worker_key.write_bytes(bytes.fromhex(durable["worker_signing_key_hex"]))
        receipt = rematerialize_process_timeout_decision(
            checkpoint_root=store_root,
            execution_nonce=durable["execution_nonce"],
            supervisor_signing_key_id=durable["supervisor_signing_key_id"],
            supervisor_signing_key_file=supervisor_key,
            worker_signing_key_id=durable["worker_signing_key_id"],
            worker_signing_key_file=worker_key,
        )
    if receipt.outcome is not Outcome.TIMEOUT:
        raise ValueError("durable process authority did not finalize as TIMEOUT")
    if receipt.receipt_digest != payload["decision_receipt"]["receipt_digest"]:
        raise ValueError("durable TIMEOUT DecisionReceipt drifted")
    return {
        "outcome": receipt.outcome.value,
        "receipt_digest": receipt.receipt_digest,
        "terminal_timeout_event_count": payload["terminal_timeout_event_count"],
        "active_cause_count": payload["active_cause_count"],
        "open_requirement_count": payload["open_requirement_count"],
    }


def build_phase8_cutover_validation(repo_root: Path) -> Mapping[str, Any]:
    root = Path(repo_root).resolve()
    junit = root / "artifacts/unknown_taxonomy_v2/phase8/phase8-focused-validation.xml"
    focused = _passing_junit(
        junit,
        minimum=23,
        required_names=(
            "test_serialized_legacy_contradiction_is_rejected",
            "test_timeout_requires_terminal_receipt_not_solver_row_heuristic",
            "test_serialized_lifecycle_relations_remain_base_relations_without_outcome",
            "test_process_timeout_is_rematerialized_from_durable_terminal_bundle",
            "test_eq_cutover_is_bound_to_audited_comparison_receipt_signal",
            "test_cli_startup_error_emits_canonical_error_and_exit_four",
            "test_cli_no_solver_emits_canonical_error_and_exit_four",
            "test_cli_missing_function_emits_canonical_error_and_exit_four",
            "test_canonical_summary_drops_receiptless_unknown_payload_metrics",
            "test_canonical_summary_keeps_only_final_receipt_bound_payload",
            "test_canonical_summary_mode_never_uses_legacy_timeout_heuristics",
        ),
    )
    workflow_junit = root / (
        "artifacts/unknown_taxonomy_v2/phase8/phase8-workflow-regression.xml"
    )
    workflow = _passing_junit(workflow_junit, minimum=162)
    phase7_junit = root / (
        "artifacts/unknown_taxonomy_v2/phase7/phase7-cross-slice-validation.xml"
    )
    phase7 = _passing_junit(
        phase7_junit,
        minimum=508,
        required_names=(
            "test_canonical_census_is_all_or_nothing_and_never_returns_partial_metrics",
            "test_census_rejects_timeout_stream_mismatch_and_missing_required_materialization",
            "test_shadow_census_join_is_post_receipt_and_all_or_nothing",
        ),
    )
    subprocess.run(
        ["bash", "-n", "Eq_new.sh", "eqbench_run_all_32jobs.sh",
         "scripts/validation_matrix_common.sh"],
        cwd=root, check=True,
    )
    producer_manifest_path = root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )
    producer_manifest = json.loads(producer_manifest_path.read_text(encoding="utf-8"))
    site_ids = {row["producer_site_manifest_id"] for row in producer_manifest["sites"]}
    if producer_manifest["site_count"] != 25 or (
        "obligation-stage-final-eq-closure" not in site_ids
    ):
        raise ValueError("Phase 8 decisive EQ producer site is not audited")
    phase7_cutover = root / "artifacts/unknown_taxonomy_v2/phase7/cutover-validation.json"
    real_sat = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/real-sat-unknown.json"
    )).read_text(encoding="utf-8"))
    relation_rows = tuple(real_sat["c_active_rows"]) + tuple(real_sat["q_open_rows"])
    if any("final_outcome" in row for row in relation_rows):
        raise ValueError("base lifecycle relation contains final outcome")
    body = {
        "validation_kind": VALIDATION_KIND,
        "repository_commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip(),
        "source_files": tuple({"path": path, "sha256": _sha256(root / path)}
                              for path in SOURCE_PATHS),
        "policy": {
            "retry_fallback": {outcome.value: RETRY_FALLBACK_MATRIX[outcome]
                               for outcome in Outcome},
            "batch_resume": {outcome.value: BATCH_RESUME_MATRIX[outcome]
                             for outcome in Outcome},
            "cli_exit": {outcome.value: CLI_EXIT_MATRIX[outcome]
                         for outcome in Outcome},
        },
        "gates": {
            "decision_receipt_only_final_status": {
                "junit": junit.relative_to(root).as_posix(),
                "test_family": "test_decision_receipt_is_only_serialized_status_authority",
                "outcome_case_count": sum(
                    name.startswith("test_decision_receipt_is_only_serialized_status_authority[")
                    for name in focused["test_names"]
                ),
            },
            "legacy_contradiction_is_error": {
                "test": "test_serialized_legacy_contradiction_is_rejected"
            },
            "unknown_timeout_policy_distinct": (
                RETRY_FALLBACK_MATRIX[Outcome.UNKNOWN]
                != RETRY_FALLBACK_MATRIX[Outcome.TIMEOUT]
                and BATCH_RESUME_MATRIX[Outcome.UNKNOWN]
                != BATCH_RESUME_MATRIX[Outcome.TIMEOUT]
            ),
            "base_relations_exclude_final_outcome": {
                "checked_row_count": len(relation_rows),
                "test": "test_serialized_lifecycle_relations_remain_base_relations_without_outcome",
            },
            "canonical_census_uses_manifest_receipt_stream_join": {
                "junit": phase7_junit.relative_to(root).as_posix(),
                "test_count": phase7["test_count"],
                "required_test_count": 3,
            },
            "shell_syntax_valid": {
                "files": ("Eq_new.sh", "eqbench_run_all_32jobs.sh",
                          "scripts/validation_matrix_common.sh"),
            },
        },
        "producer_manifest": {
            "path": producer_manifest_path.relative_to(root).as_posix(),
            "sha256": _sha256(producer_manifest_path),
            "manifest_digest": producer_manifest["manifest_digest"],
            "site_count": producer_manifest["site_count"],
        },
        "phase7_cutover": {
            "path": phase7_cutover.relative_to(root).as_posix(),
            "sha256": _sha256(phase7_cutover),
        },
        "durable_process_timeout": _timeout_receipt(root),
        "focused_junit": {
            "path": junit.relative_to(root).as_posix(),
            "sha256": _sha256(junit),
            "test_count": focused["test_count"],
        },
        "workflow_regression_junit": {
            "path": workflow_junit.relative_to(root).as_posix(),
            "sha256": _sha256(workflow_junit),
            "test_count": workflow["test_count"],
            "source_files": tuple({"path": path, "sha256": _sha256(root / path)}
                                  for path in WORKFLOW_TEST_PATHS),
        },
        "eqbench_dry_run": _eqbench_dry_run_evidence(root),
    }
    return {**body, "artifact_digest": authority_digest(body)}


def validate_phase8_cutover_validation(
    repo_root: Path, payload: Mapping[str, Any],
) -> None:
    expected = json.loads(json.dumps(build_phase8_cutover_validation(repo_root)))
    if payload != expected:
        raise ValueError("Phase 8 cutover validation artifact drifted")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--output", required=True)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    output = Path(args.output)
    if args.validate:
        validate_phase8_cutover_validation(
            Path(args.repo_root), json.loads(output.read_text(encoding="utf-8"))
        )
    else:
        payload = build_phase8_cutover_validation(Path(args.repo_root))
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n",
                          encoding="utf-8")
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
