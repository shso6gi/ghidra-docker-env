from pathlib import Path
import shutil

import pytest

from scripts.function_tracer_pcode.equivalence.v2.census_contract import (
    ActiveOccurrenceMaterialization,
    materialization_metrics,
)
from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    QOpenBaseRow,
    RecoveryAddressability,
)
from scripts.function_tracer_pcode.validation.phase9_completion_validation import (
    build_phase9_evidence,
    validate_phase9_evidence,
)


def test_phase9_current_head_evidence_is_complete_and_source_bound():
    root = Path(__file__).resolve().parents[4]
    validate_phase9_evidence(root)
    evidence = build_phase9_evidence(root)

    assert evidence["legacy_coverage.json"]["v2_native_typed_cause_coverage"] == 1.0
    assert evidence["legacy_coverage.json"]["final_blocker_authority_coverage"] == 1.0
    assert evidence["query_execution_receipts.json"]["terminal_timeout_receipt_count"] == 1
    replay = evidence["cause_lifecycle_snapshot.json"]["lifecycle_replay_authority"]
    assert replay["lifecycle_inference_count"] == 0
    assert replay["implicit_replacement_or_completion_count"] == 0


def test_phase9_keeps_semantic_causes_proof_backlog_and_outcome_join_separate():
    root = Path(__file__).resolve().parents[4]
    snapshot = build_phase9_evidence(root)["cause_lifecycle_snapshot.json"]
    for outcome in ("unknown", "timeout"):
        assert all("final_outcome" not in row for row in snapshot[outcome]["c_active"])
        assert all("final_outcome" not in row for row in snapshot[outcome]["q_open"])
    assert snapshot["semantic_cause_and_proof_backlog_are_separate"] is True


def test_phase9_closeout_root_rejects_validation_log_tampering(tmp_path):
    root = Path(__file__).resolve().parents[4]
    copied = tmp_path / "phase9"
    shutil.copytree(root / "artifacts/unknown_taxonomy_v2/phase9", copied)
    (copied / "validation_run.log").write_text("tampered\n", encoding="utf-8")

    with pytest.raises(ValueError, match="validation_run.log drifted"):
        validate_phase9_evidence(root, evidence_directory=copied)
    receipt_copy = tmp_path / "phase9-receipt-tamper"
    shutil.copytree(root / "artifacts/unknown_taxonomy_v2/phase9", receipt_copy)
    receipt_path = receipt_copy / "query_execution_receipts.json"
    receipt_path.write_text(
        receipt_path.read_text(encoding="utf-8").replace(
            '"terminal_timeout_receipt_count": 1',
            '"terminal_timeout_receipt_count": 2',
        ),
        encoding="utf-8",
    )
    with pytest.raises(ValueError, match="query_execution_receipts.json"):
        validate_phase9_evidence(root, evidence_directory=receipt_copy)


def test_phase9_materialization_metrics_classify_registry_addressability():
    active = (
        ActiveOccurrenceMaterialization(
            "result", "required", "cause-required",
            RecoveryAddressability.REQUIREMENT_REQUIRED,
        ),
        ActiveOccurrenceMaterialization(
            "result", "optional", "cause-optional",
            RecoveryAddressability.REQUIREMENT_OPTIONAL,
        ),
        ActiveOccurrenceMaterialization(
            "result", "no-proof", "cause-no-proof",
            RecoveryAddressability.NO_PROOF_RECOVERY,
        ),
    )
    requirement = QOpenBaseRow(
        "result", "required", "cause-required", "requirement", "proof", "target"
    )

    metrics = materialization_metrics(active, (requirement,))

    assert metrics["required_requirement_materialization_coverage"] == 1.0
    assert metrics["optional_requirement_materialization_rate"] == 0.0
    assert metrics["active_causes_without_materialized_requirement"] == {
        "required_missing": 0,
        "optional_not_materialized": 1,
        "no_proof_recovery": 1,
    }
    forbidden = QOpenBaseRow(
        "result", "no-proof", "cause-no-proof", "forbidden", "proof", "target"
    )
    with pytest.raises(ValueError, match="NO_PROOF_RECOVERY"):
        materialization_metrics(active, (requirement, forbidden))


def test_phase9_binds_all_five_receipt_cases_to_phase8_authority():
    root = Path(__file__).resolve().parents[4]
    evidence = build_phase9_evidence(root)
    binding = evidence["decision_receipt.json"]["all_five_source_bound_authority"]

    assert binding["outcome_case_count"] == 5
    assert len(binding["phase8_artifact_digest"]) == 64
    assert len(binding["focused_junit_sha256"]) == 64
    assert len(binding["focused_test_source_sha256"]) == 64


def test_phase9_refactor_replacement_is_current_contract_green():
    root = Path(__file__).resolve().parents[4]
    replacement = build_phase9_evidence(root)["validation_run.json"][
        "refactor_replacement_contract"
    ]

    assert replacement["contract_kind"] == "phase10-refactor-contract-green-v1"
    assert replacement["exit_code"] == 0
    assert tuple(replacement["stdout_lines"]) == ("refactor contract: ok",)
    assert replacement["stderr"] == ""
    assert replacement["public_symbol_deltas"] == ()
    assert replacement["private_import_count_delta"] == 0
    assert replacement["added_private_imports"] == ()
    assert replacement["removed_private_imports"] == ()
    assert replacement["exact_failures"] == ()
    assert replacement["new_dependency_cycle_module_counts"] == ()
    assert replacement["review_disposition"] == "contract_green"
    assert replacement["blanket_baseline_regeneration"] is False
