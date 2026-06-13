# -*- coding: utf-8 -*-

import hashlib
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.validation import phase3_lane_index
from scripts.function_tracer_pcode.validation.phase3_post_fix_gate_index import (
    DEFAULT_PHASE3_POST_FIX_GATE_SPECS,
    Phase3PostFixGateSpec,
    build_phase3_post_fix_gate_index,
    phase3_post_fix_gate_index_text_summary,
    validate_phase3_post_fix_gate_index,
)


def _validator(manifest):
    if manifest.get("ready") is not True:
        raise ValueError("gate is not ready")


def _spec(lane_number: int, lane_id: str) -> Phase3PostFixGateSpec:
    return Phase3PostFixGateSpec(
        lane_number=lane_number,
        lane_id=lane_id,
        gate_relpath=f"logs/{lane_id}/gate.json",
        manifest_kind=f"{lane_id}_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
    )


def _write_gate(
    repo: Path,
    spec: Phase3PostFixGateSpec,
    *,
    ready=True,
    summary_failed=None,
    summary_failed_kinds=None,
    post_fix_status="pending_proof",
    manifest_kind=None,
    artifact_role="derived_audit_post_fix_gate",
    baseline_id="observed-v0@0a53352",
    baseline_git_head=phase3_lane_index.BASELINE_GIT_HEAD,
    omit_pending_obligations=False,
    pending_obligation_updates=None,
    include_required_completion_actions=True,
    omit_required_completion_actions=False,
    required_action_updates=None,
    extra_unresolved_observations=None,
) -> None:
    path = repo / spec.gate_relpath
    path.parent.mkdir(parents=True, exist_ok=True)
    entry = {
        "id": f"{spec.lane_id}-entry",
        "function": "function_one",
        "binary_pair": "B1_B2",
        "post_fix_status": post_fix_status,
    }
    obligation = None
    if not omit_pending_obligations and post_fix_status in {"pending_proof", "pending_retry"}:
        obligation = {
            "reason_id": "reason_one",
            "proof_kind": "proof_kind_one",
            "proof_stage": "proof_stage_one",
            "evidence_kind": "evidence_kind_one",
            "required_evidence": ["evidence_kind_one"],
            "proof_obligation_id": ["proof", spec.lane_id, "proof_stage_one"],
            "completed_evidence_present": False,
            "status": "pending_evidence" if post_fix_status == "pending_proof" else "pending_retry",
        }
        obligation.update(pending_obligation_updates or {})
        if post_fix_status == "pending_proof":
            entry["pending_proof_obligations"] = [obligation]
        else:
            entry["pending_retry_obligations"] = [obligation]
    if (
        include_required_completion_actions
        and not omit_required_completion_actions
        and obligation is not None
    ):
        required_action = {
            key: obligation[key]
            for key in (
                "reason_id",
                "proof_kind",
                "proof_stage",
                "evidence_kind",
                "required_evidence",
                "proof_obligation_id",
            )
        }
        required_action.update(required_action_updates or {})
        entry["required_completion_actions"] = [required_action]
    payload = {
        "manifest_version": 1,
        "manifest_kind": manifest_kind or spec.manifest_kind,
        "artifact_role": artifact_role,
        "baseline_id": baseline_id,
        "baseline_git_head": baseline_git_head,
        spec.ready_key: ready,
        "post_fix_regression_gate": {
            "summary": {
                "failed": (
                    summary_failed
                    if summary_failed is not None
                    else (0 if ready else 1)
                ),
                "failed_kinds": (
                    summary_failed_kinds
                    if summary_failed_kinds is not None
                    else ([] if ready else ["unit_failure"])
                ),
            }
        },
        "entries": [entry],
    }
    if extra_unresolved_observations is not None:
        payload["extra_current_unresolved_expression_observations"] = list(
            extra_unresolved_observations
        )
        payload["post_fix_summary"] = {
            "extra_current_unresolved_expression_count": len(extra_unresolved_observations)
        }
    path.write_text(json.dumps(payload, sort_keys=True))


def _retired_transfer_action():
    return {
        "evidence_kind": "transfer_evidence",
        "object_target_key": ["transfer", "object"],
        "pair_or_case": "<missing>",
        "proof_obligation_id": ["transfer", "proof"],
        "required_evidence": ["transfer_evidence"],
        "stage": "S_PAIRWISE",
        "tuple": [
            "proof_action",
            "return_coverage_gap",
            "blocks_equivalence",
            "function",
            "return_coverage_completion",
            "return_guard_coverage",
            "pending_proof",
        ],
    }


def _actions_sha256(actions):
    return hashlib.sha256(
        json.dumps(actions, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def test_default_lane6_required_completion_action_hashes_are_current():
    lane6 = next(
        spec
        for spec in DEFAULT_PHASE3_POST_FIX_GATE_SPECS
        if spec.lane_id == "phase3_unresolved_expression_lane6"
    )

    assert lane6.expected_entry_count == 3
    assert lane6.expected_post_fix_status_counts == {"pending_proof": 3}
    assert lane6.expected_post_fix_obligation_counts == {
        "pending_proof_entry_count": 3,
        "pending_proof_obligation_count": 24,
        "pending_retry_entry_count": 0,
        "pending_retry_obligation_count": 0,
    }
    assert list(lane6.expected_required_completion_action_hashes) == [
        {
            "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
            "required_completion_actions_sha256": (
                "27312a6f83dc29b3fdb787cac2b283fed98a934dd0bc2feaa8283522eca2783f"
            ),
        },
        {
            "id": "representative-unresolved-expression-is-even-deferred-call-return-current-transition",
            "required_completion_actions_sha256": (
                "c25c782c296a181d96a80f43260a29b03758700625fbdbb6662ea028fddeff8a"
            ),
        },
        {
            "id": "representative-unresolved-expression-is-odd-opaque-void-return-current-transition",
            "required_completion_actions_sha256": (
                "c41aa1f18262cb9c63cf66337635b2e0e1b5d69688320f93a5a2273254f47a5a"
            ),
        },
    ]


def test_phase3_post_fix_gate_index_accepts_ready_gates(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"), _spec(2, "lane_two"))
    for spec in specs:
        _write_gate(repo, spec)

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is True
    assert manifest["summary"]["failed"] == 0
    assert [gate["lane_id"] for gate in manifest["gates"]] == ["lane_one", "lane_two"]
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_accepts_semantic_proof_required_obligation(tmp_path):
    repo = tmp_path / "repo"
    spec = _spec(6, "phase3_unresolved_expression_lane6")
    _write_gate(
        repo,
        spec,
        post_fix_status="pending_proof",
        pending_obligation_updates={
            "object_evidence_status": "object_evidence_collected",
            "semantic_proof_status": "pending_semantic_proof",
            "status": "semantic_proof_required",
        },
        required_action_updates={
            "object_evidence_status": "object_evidence_collected",
            "semantic_proof_status": "pending_semantic_proof",
        },
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is True
    assert summary["pending_proof_invalid_obligations"] == []
    assert summary["pending_proof_invalid_required_actions"] == []
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_summarizes_extra_unresolved_expression_observations(tmp_path):
    repo = tmp_path / "repo"
    spec = _spec(6, "phase3_unresolved_expression_lane6")
    _write_gate(
        repo,
        spec,
        extra_unresolved_observations=[
            {
                "category": "function_call",
                "function": "fc_is_even",
                "binary_pair": "B11_B12",
                "unresolved_expression_reason_record_count": 3,
            }
        ],
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    summary = manifest["gates"][0]["extra_current_unresolved_expression_summary"]
    assert summary == {
        "count": 1,
        "observed_count": 1,
        "identities": [
            {
                "category": "function_call",
                "function": "fc_is_even",
                "binary_pair": "B11_B12",
                "unresolved_expression_reason_record_count": 3,
            }
        ],
    }
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_non_mapping_manifest(tmp_path):
    with pytest.raises(ValueError, match="manifest must be an object"):
        validate_phase3_post_fix_gate_index(["not", "an", "object"], repo_root=tmp_path)


def test_phase3_post_fix_gate_index_rejects_empty_gate_specs(tmp_path):
    repo = tmp_path / "repo"

    with pytest.raises(ValueError, match="gate_specs"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(),
        )


@pytest.mark.parametrize(
    ("first", "second", "match"),
    (
        (_spec(1, "lane_one"), _spec(1, "lane_two"), "lane_number"),
        (_spec(1, "lane_one"), _spec(2, "lane_one"), "lane_id"),
        (
            _spec(1, "lane_one"),
            Phase3PostFixGateSpec(
                lane_number=2,
                lane_id="lane_two",
                gate_relpath="logs/lane_one/gate.json",
                manifest_kind="lane_two_post_fix_gate",
                ready_key="ready",
                validator=_validator,
                expected_entry_count=1,
                allowed_post_fix_statuses=("pending_proof",),
            ),
            "gate_relpath",
        ),
    ),
)
def test_phase3_post_fix_gate_index_rejects_duplicate_gate_specs(
    tmp_path,
    first,
    second,
    match,
):
    repo = tmp_path / "repo"
    _write_gate(repo, first)
    _write_gate(repo, second)

    with pytest.raises(ValueError, match=match):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(first, second),
        )


def test_phase3_post_fix_gate_index_rejects_explicit_empty_gate_specs_on_validate(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    with pytest.raises(ValueError, match="gate_specs"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=())


def test_phase3_post_fix_gate_index_summarizes_post_fix_status_counts(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"), _spec(2, "lane_two"))
    _write_gate(repo, specs[0], post_fix_status="pending_proof")
    _write_gate(repo, specs[1], post_fix_status="completed_recovery")

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["post_fix_status_counts"] == {
        "completed_recovery": 1,
        "pending_proof": 1,
    }
    assert manifest["gates"][0]["post_fix_status_counts"] == {"pending_proof": 1}
    assert manifest["gates"][1]["post_fix_status_counts"] == {"completed_recovery": 1}
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_text_summary_includes_lane_status_and_obligations(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"), _spec(2, "lane_two"))
    _write_gate(repo, specs[0], post_fix_status="pending_proof")
    _write_gate(repo, specs[1], post_fix_status="completed_recovery")

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    text = phase3_post_fix_gate_index_text_summary(manifest)

    assert "ready=True failed_checks=0" in text
    assert "post_fix_status_counts={completed_recovery:1, pending_proof:1}" in text
    assert "lane1 lane_one: ready=True entries=1 statuses={pending_proof:1}" in text
    assert "lane2 lane_two: ready=True entries=1 statuses={completed_recovery:1}" in text
    assert "pending_proof_obligation_count:1" in text


def test_phase3_post_fix_gate_index_accepts_expected_status_distribution(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"completed_recovery": 1, "pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"].append(
        {
            "id": "lane_one-completed",
            "function": "function_one",
            "binary_pair": "B1_B2",
            "post_fix_status": "completed_recovery",
        }
    )
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is True
    assert manifest["expected_post_fix_status_counts"] == {
        "completed_recovery": 1,
        "pending_proof": 1,
    }
    assert manifest["gates"][0]["expected_post_fix_status_counts"] == {
        "completed_recovery": 1,
        "pending_proof": 1,
    }
    assert manifest["gates"][0]["post_fix_status_counts"] == {
        "completed_recovery": 1,
        "pending_proof": 1,
    }
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_allowed_status_distribution_drift(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"completed_recovery": 1, "pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    second_entry = dict(gate["entries"][0])
    second_entry["id"] = "lane_one-second-pending-proof"
    gate["entries"].append(second_entry)
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["post_fix_status_counts"] == {"pending_proof": 2}
    assert "phase3_post_fix_gate_status_counts_expected" in manifest["summary"]["failed_kinds"]
    assert (
        "phase3_post_fix_gate_status_counts_global_expected"
        in manifest["summary"]["failed_kinds"]
    )
    with pytest.raises(ValueError, match="phase3_post_fix_gate_status_counts_expected"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_tampered_expected_status_counts(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    manifest["expected_post_fix_status_counts"] = {}

    with pytest.raises(ValueError, match="expected_post_fix_status_counts"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_bool_summary_failed_count(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["summary"]["failed"] = False

    with pytest.raises(ValueError, match="summary_failed_count"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


@pytest.mark.parametrize("bad_count", (None, True, -1, 0))
def test_phase3_post_fix_gate_index_rejects_invalid_expected_entry_count_spec(
    tmp_path,
    bad_count,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=bad_count,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_entry_count"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


@pytest.mark.parametrize(
    "bad_statuses",
    (
        (),
        ("pending_proof", "pending_proof"),
        ("",),
        ("   ",),
        ("<missing>",),
    ),
)
def test_phase3_post_fix_gate_index_rejects_invalid_allowed_status_spec(
    tmp_path,
    bad_statuses,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=bad_statuses,
        expected_post_fix_status_counts={"pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="allowed_post_fix_statuses"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


@pytest.mark.parametrize("bad_count", (True, -1, 0))
def test_phase3_post_fix_gate_index_rejects_invalid_expected_status_count_spec(
    tmp_path,
    bad_count,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": bad_count},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_status_counts"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_non_mapping_expected_status_counts_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts=["pending_proof"],
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_status_counts"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_expected_status_outside_allowed_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("completed_recovery",),
        expected_post_fix_status_counts={"pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="completed_recovery")

    with pytest.raises(ValueError, match="expected_post_fix_status_counts"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_expected_status_count_total_drift_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_status_counts"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_unknown_expected_obligation_count_key_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_obligation_counts={"pending_proof_obligation_typo": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_obligation_counts"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_non_mapping_expected_obligation_counts_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_obligation_counts=["pending_proof_obligation_count"],
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_obligation_counts"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


@pytest.mark.parametrize("bad_count", (True, -1))
def test_phase3_post_fix_gate_index_rejects_invalid_expected_entry_state_count_spec(
    tmp_path,
    bad_count,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": bad_count,
                "pending_retry_obligation_count": 0,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_states"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_non_sequence_expected_entry_identities_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_identities={"id": "lane_one-entry"},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_identities"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_non_mapping_expected_entry_identity_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_identities=("not-an-entry-object",),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_identities"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_duplicate_expected_entry_identity_ids_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 2},
        expected_post_fix_entry_identities=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
            },
            {
                "id": "lane_one-entry",
                "function": "function_two",
                "binary_pair": "B3_B4",
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_identities"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_partial_expected_entry_identities_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 2},
        expected_post_fix_entry_identities=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_identities"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_non_sequence_expected_entry_states_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_states={"id": "lane_one-entry"},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_states"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_non_mapping_expected_entry_state_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_states=("not-an-entry-object",),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_states"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_partial_expected_entry_states_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"completed_recovery": 1, "pending_proof": 1},
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_states"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_expected_identity_state_mismatch_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_identities=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
            },
        ),
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_two",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_identities"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_expected_state_status_count_mismatch_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"completed_recovery": 1, "pending_proof": 1},
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
            },
            {
                "id": "lane_one-second-entry",
                "function": "function_two",
                "binary_pair": "B3_B4",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_status_counts"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_expected_state_obligation_count_mismatch_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 1,
            "pending_proof_obligation_count": 2,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_obligation_counts"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_non_pending_state_with_pending_obligations_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("completed_recovery",),
        expected_post_fix_status_counts={"completed_recovery": 1},
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "completed_recovery",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="completed_recovery")

    with pytest.raises(ValueError, match="expected_post_fix_entry_states"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_pending_state_without_obligation_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_retry",),
        expected_post_fix_status_counts={"pending_retry": 1},
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_retry",
                "pending_proof_obligation_count": 0,
                "pending_retry_obligation_count": 0,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_retry")

    with pytest.raises(ValueError, match="expected_post_fix_entry_states"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_duplicate_expected_entry_state_ids_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("completed_recovery", "pending_proof"),
        expected_post_fix_status_counts={"completed_recovery": 1, "pending_proof": 1},
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
            },
            {
                "id": "lane_one-entry",
                "function": "function_two",
                "binary_pair": "B3_B4",
                "post_fix_status": "completed_recovery",
                "pending_proof_obligation_count": 0,
                "pending_retry_obligation_count": 0,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_states"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_expected_entry_state_status_outside_allowed_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("completed_recovery",),
        expected_post_fix_status_counts={"completed_recovery": 1},
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="completed_recovery")

    with pytest.raises(ValueError, match="expected_post_fix_entry_states"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_missing_expected_entry_identity_field_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_identities=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_identities"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_missing_expected_entry_state_field_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_entry_states"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_invalid_expected_required_action_hash_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": "lane_one-entry",
                "required_completion_actions_sha256": "not-a-sha256",
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_required_completion_action_hashes"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_invalid_summary_source_spec(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_summary_source="unknown_source",
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_summary_source"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_expected_required_action_hash_state_mismatch_spec(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": "lane_one-other-entry",
                "required_completion_actions_sha256": _actions_sha256([]),
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_required_completion_action_hashes"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_accepts_expected_entry_identities(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_identities=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"][0]["function"] = "function_one"
    gate["entries"][0]["binary_pair"] = "B1_B2"
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is True
    assert manifest["gates"][0]["post_fix_entry_identities"] == [
        {
            "id": "lane_one-entry",
            "function": "function_one",
            "binary_pair": "B1_B2",
        },
    ]
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_entry_identity_drift(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_identities=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"][0]["function"] = "function_two"
    gate["entries"][0]["binary_pair"] = "B1_B2"
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert "phase3_post_fix_gate_entry_identities_expected" in manifest["summary"][
        "failed_kinds"
    ]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_entry_identities_expected"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_accepts_expected_entry_states(tmp_path):
    repo = tmp_path / "repo"
    expected_states = (
        {
            "id": "lane_one-entry",
            "function": "function_one",
            "binary_pair": "B1_B2",
            "post_fix_status": "completed_recovery",
            "pending_proof_obligation_count": 0,
            "pending_retry_obligation_count": 0,
            "required_completion_action_count": 0,
        },
        {
            "id": "lane_one-retired",
            "function": "function_two",
            "binary_pair": "B3_B4",
            "post_fix_status": "retired_to_return_coverage_gap",
            "pending_proof_obligation_count": 0,
            "pending_retry_obligation_count": 0,
            "required_completion_action_count": 0,
        },
    )
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("completed_recovery", "retired_to_return_coverage_gap"),
        expected_post_fix_status_counts={
            "completed_recovery": 1,
            "retired_to_return_coverage_gap": 1,
        },
        expected_post_fix_entry_identities=tuple(
            {
                "id": state["id"],
                "function": state["function"],
                "binary_pair": state["binary_pair"],
            }
            for state in expected_states
        ),
        expected_post_fix_entry_states=expected_states,
    )
    _write_gate(repo, spec, post_fix_status="completed_recovery")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"][0]["function"] = "function_one"
    gate["entries"][0]["binary_pair"] = "B1_B2"
    gate["entries"].append(
        {
            "id": "lane_one-retired",
            "function": "function_two",
            "binary_pair": "B3_B4",
            "post_fix_status": "retired_to_return_coverage_gap",
        }
    )
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is True
    assert manifest["gates"][0]["post_fix_entry_states"] == list(expected_states)
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_entry_state_drift_with_same_status_counts(
    tmp_path,
):
    repo = tmp_path / "repo"
    expected_states = (
        {
            "id": "lane_one-entry",
            "function": "function_one",
            "binary_pair": "B1_B2",
            "post_fix_status": "completed_recovery",
            "pending_proof_obligation_count": 0,
            "pending_retry_obligation_count": 0,
            "required_completion_action_count": 0,
        },
        {
            "id": "lane_one-retired",
            "function": "function_two",
            "binary_pair": "B3_B4",
            "post_fix_status": "retired_to_return_coverage_gap",
            "pending_proof_obligation_count": 0,
            "pending_retry_obligation_count": 0,
            "required_completion_action_count": 0,
        },
    )
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("completed_recovery", "retired_to_return_coverage_gap"),
        expected_post_fix_status_counts={
            "completed_recovery": 1,
            "retired_to_return_coverage_gap": 1,
        },
        expected_post_fix_entry_identities=tuple(
            {
                "id": state["id"],
                "function": state["function"],
                "binary_pair": state["binary_pair"],
            }
            for state in expected_states
        ),
        expected_post_fix_entry_states=expected_states,
    )
    _write_gate(repo, spec, post_fix_status="retired_to_return_coverage_gap")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"][0]["function"] = "function_one"
    gate["entries"][0]["binary_pair"] = "B1_B2"
    gate["entries"].append(
        {
            "id": "lane_one-retired",
            "function": "function_two",
            "binary_pair": "B3_B4",
            "post_fix_status": "completed_recovery",
        }
    )
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["post_fix_status_counts"] == {
        "completed_recovery": 1,
        "retired_to_return_coverage_gap": 1,
    }
    assert "phase3_post_fix_gate_entry_states_expected" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_entry_states_expected"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_required_action_count_drift_with_clean_gate_checks(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("retired_to_return_coverage_gap",),
        expected_post_fix_status_counts={"retired_to_return_coverage_gap": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "retired_to_return_coverage_gap",
                "pending_proof_obligation_count": 0,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 1,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="retired_to_return_coverage_gap")

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["post_fix_summary"] == {"failed": 0, "failed_kinds": []}
    assert manifest["gates"][0]["post_fix_entry_states"][0][
        "required_completion_action_count"
    ] == 0
    assert "phase3_post_fix_gate_entry_states_expected" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_entry_states_expected"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_required_action_content_drift_with_same_count(
    tmp_path,
):
    repo = tmp_path / "repo"
    expected_action = _retired_transfer_action()
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("retired_to_return_coverage_gap",),
        expected_post_fix_status_counts={"retired_to_return_coverage_gap": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "retired_to_return_coverage_gap",
                "pending_proof_obligation_count": 0,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 1,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": "lane_one-entry",
                "required_completion_actions_sha256": _actions_sha256([expected_action]),
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="retired_to_return_coverage_gap")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    changed_action = dict(expected_action)
    changed_action["stage"] = "S_CHANGED_BUT_STILL_CONCRETE"
    gate["entries"][0]["required_completion_actions"] = [changed_action]
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["retired_invalid_required_actions"] == []
    assert manifest["gates"][0]["post_fix_entry_states"][0][
        "required_completion_action_count"
    ] == 1
    assert "phase3_post_fix_gate_required_action_hashes_expected" in manifest["summary"][
        "failed_kinds"
    ]
    with pytest.raises(
        ValueError,
        match="phase3_post_fix_gate_required_action_hashes_expected",
    ):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_non_pending_entry_with_pending_fields(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("completed_recovery",),
        expected_post_fix_status_counts={"completed_recovery": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    entry = gate["entries"][0]
    entry["post_fix_status"] = "completed_recovery"
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["non_pending_entries_with_pending_obligations"] == [
        {
            "entry_id": "lane_one-entry",
            "post_fix_status": "completed_recovery",
            "pending_fields": ["pending_proof_obligations"],
        }
    ]
    assert summary["entries_with_unexpected_required_actions"] == [
        {
            "entry_id": "lane_one-entry",
            "post_fix_status": "completed_recovery",
        }
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_allows_retired_entry_transfer_actions(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("retired_to_return_coverage_gap",),
        expected_post_fix_status_counts={"retired_to_return_coverage_gap": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    entry = gate["entries"][0]
    entry["post_fix_status"] = "retired_to_return_coverage_gap"
    entry.pop("pending_proof_obligations")
    entry["required_completion_actions"] = [_retired_transfer_action()]
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is True
    assert summary["non_pending_entries_with_pending_obligations"] == []
    assert summary["entries_with_unexpected_required_actions"] == []
    assert summary["retired_invalid_required_actions"] == []
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_malformed_retired_transfer_action(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("retired_to_return_coverage_gap",),
        expected_post_fix_status_counts={"retired_to_return_coverage_gap": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    entry = gate["entries"][0]
    entry["post_fix_status"] = "retired_to_return_coverage_gap"
    entry.pop("pending_proof_obligations")
    entry["required_completion_actions"] = [{"evidence_kind": "transfer_evidence"}]
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["retired_invalid_required_actions"] == [
        {
            "entry_id": "lane_one-entry",
            "post_fix_status": "retired_to_return_coverage_gap",
            "required_action_index": 0,
        }
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


@pytest.mark.parametrize(
    "action_updates",
    (
        {"tuple": ["not_proof_action", "reason", "effect", "scope", "proof", "stage", "status"]},
        {"tuple": ["proof_action", "reason", "effect", "scope", "proof", "stage", 1]},
        {"proof_obligation_id": []},
        {"proof_obligation_id": 0},
        {"object_target_key": []},
        {"object_target_key": 0},
        {"required_evidence": ["transfer_evidence", "transfer_evidence"]},
    ),
)
def test_phase3_post_fix_gate_index_rejects_invalid_retired_transfer_action_shape(
    tmp_path,
    action_updates,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("retired_to_return_coverage_gap",),
        expected_post_fix_status_counts={"retired_to_return_coverage_gap": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    entry = gate["entries"][0]
    action = _retired_transfer_action()
    action.update(action_updates)
    entry["post_fix_status"] = "retired_to_return_coverage_gap"
    entry.pop("pending_proof_obligations")
    entry["required_completion_actions"] = [action]
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["retired_invalid_required_actions"] == [
        {
            "entry_id": "lane_one-entry",
            "post_fix_status": "retired_to_return_coverage_gap",
            "required_action_index": 0,
        }
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_duplicate_retired_transfer_action_id(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("retired_to_return_coverage_gap",),
        expected_post_fix_status_counts={"retired_to_return_coverage_gap": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    entry = gate["entries"][0]
    action = _retired_transfer_action()
    entry["post_fix_status"] = "retired_to_return_coverage_gap"
    entry.pop("pending_proof_obligations")
    entry["required_completion_actions"] = [action, dict(action)]
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["retired_invalid_required_actions"] == []
    assert summary["retired_duplicate_required_action_ids"] == [
        {
            "entry_id": "lane_one-entry",
            "post_fix_status": "retired_to_return_coverage_gap",
            "duplicate_proof_obligation_ids": ['["transfer","proof"]'],
        }
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_duplicate_retired_transfer_action_id_across_entries(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("retired_to_return_coverage_gap",),
        expected_post_fix_status_counts={"retired_to_return_coverage_gap": 2},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 0,
            "pending_proof_obligation_count": 0,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    first_entry = gate["entries"][0]
    first_entry["post_fix_status"] = "retired_to_return_coverage_gap"
    first_entry.pop("pending_proof_obligations")
    first_entry["required_completion_actions"] = [_retired_transfer_action()]
    second_entry = json.loads(json.dumps(first_entry))
    second_entry["id"] = "lane_one-second-entry"
    gate["entries"].append(second_entry)
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["retired_duplicate_required_action_ids"] == []
    assert summary["retired_duplicate_required_action_ids_across_entries"] == [
        {
            "proof_obligation_id": '["transfer","proof"]',
            "refs": [
                {
                    "entry_id": "lane_one-entry",
                    "post_fix_status": "retired_to_return_coverage_gap",
                },
                {
                    "entry_id": "lane_one-second-entry",
                    "post_fix_status": "retired_to_return_coverage_gap",
                },
            ],
        }
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


@pytest.mark.parametrize(
    ("post_fix_status", "extra_field", "extra_obligation_status"),
    (
        ("pending_proof", "pending_retry_obligations", "pending_retry"),
        ("pending_retry", "pending_proof_obligations", "pending_evidence"),
    ),
)
def test_phase3_post_fix_gate_index_rejects_pending_entry_with_wrong_pending_field(
    tmp_path,
    post_fix_status,
    extra_field,
    extra_obligation_status,
):
    repo = tmp_path / "repo"
    obligation_field = (
        "pending_proof_obligations"
        if post_fix_status == "pending_proof"
        else "pending_retry_obligations"
    )
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=(post_fix_status,),
        expected_post_fix_status_counts={post_fix_status: 1},
    )
    _write_gate(repo, spec, post_fix_status=post_fix_status)
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    entry = gate["entries"][0]
    extra_obligation = dict(entry[obligation_field][0])
    extra_obligation["status"] = extra_obligation_status
    entry[extra_field] = [extra_obligation]
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["entries_with_unexpected_pending_obligations"] == [
        {
            "entry_id": "lane_one-entry",
            "post_fix_status": post_fix_status,
            "pending_fields": [extra_field],
        }
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_accepts_expected_obligation_counts(tmp_path):
    repo = tmp_path / "repo"
    expected_obligations = {
        "pending_proof_entry_count": 1,
        "pending_proof_obligation_count": 1,
        "pending_retry_entry_count": 0,
        "pending_retry_obligation_count": 0,
    }
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_obligation_counts=expected_obligations,
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is True
    assert manifest["expected_post_fix_obligation_counts"] == expected_obligations
    assert manifest["post_fix_obligation_counts"] == expected_obligations
    assert manifest["gates"][0]["expected_post_fix_obligation_counts"] == expected_obligations
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_accepts_pending_proof_to_proof_complete_progress(
    tmp_path,
):
    repo = tmp_path / "repo"
    pending_action = {
        "reason_id": "reason_one",
        "proof_kind": "proof_kind_one",
        "proof_stage": "proof_stage_one",
        "evidence_kind": "evidence_kind_one",
        "required_evidence": ["evidence_kind_one"],
        "proof_obligation_id": ["proof", "lane_one", "proof_stage_one"],
    }
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof", "proof_complete"),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 1,
            "pending_proof_obligation_count": 1,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 1,
            },
        ),
        expected_required_completion_action_hashes=(
            {
                "id": "lane_one-entry",
                "required_completion_actions_sha256": _actions_sha256([pending_action]),
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="proof_complete")

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is True
    assert manifest["expected_post_fix_status_counts"] == {"pending_proof": 1}
    assert manifest["post_fix_status_counts"] == {"proof_complete": 1}
    assert manifest["post_fix_obligation_counts"] == {
        "pending_proof_entry_count": 0,
        "pending_proof_obligation_count": 0,
        "pending_retry_entry_count": 0,
        "pending_retry_obligation_count": 0,
    }
    assert manifest["gates"][0]["post_fix_entry_states"] == [
        {
            "id": "lane_one-entry",
            "function": "function_one",
            "binary_pair": "B1_B2",
            "post_fix_status": "proof_complete",
            "pending_proof_obligation_count": 0,
            "pending_retry_obligation_count": 0,
            "required_completion_action_count": 0,
        }
    ]
    validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_proof_complete_without_allowed_progress(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_entry_states=(
            {
                "id": "lane_one-entry",
                "function": "function_one",
                "binary_pair": "B1_B2",
                "post_fix_status": "pending_proof",
                "pending_proof_obligation_count": 1,
                "pending_retry_obligation_count": 0,
                "required_completion_action_count": 1,
            },
        ),
    )
    _write_gate(repo, spec, post_fix_status="proof_complete")

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert "phase3_post_fix_gate_status_allowed" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_status_allowed"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_obligation_count_drift(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 1,
            "pending_proof_obligation_count": 1,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    entry = gate["entries"][0]
    extra_obligation = dict(entry["pending_proof_obligations"][0])
    extra_obligation["proof_stage"] = "proof_stage_two"
    extra_obligation["proof_obligation_id"] = ["proof", spec.lane_id, "proof_stage_two"]
    entry["pending_proof_obligations"].append(extra_obligation)
    entry["required_completion_actions"].append(
        {
            key: extra_obligation[key]
            for key in (
                "reason_id",
                "proof_kind",
                "proof_stage",
                "evidence_kind",
                "required_evidence",
                "proof_obligation_id",
            )
        }
    )
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["post_fix_obligation_summary"][
        "pending_proof_required_action_mismatches"
    ] == []
    assert "phase3_post_fix_gate_obligation_counts_expected" in manifest["summary"]["failed_kinds"]
    assert (
        "phase3_post_fix_gate_obligation_counts_global_expected"
        in manifest["summary"]["failed_kinds"]
    )
    with pytest.raises(ValueError, match="phase3_post_fix_gate_obligation_counts_expected"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_tampered_expected_obligation_counts(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 1,
            "pending_proof_obligation_count": 1,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    manifest["expected_post_fix_obligation_counts"] = {}

    with pytest.raises(ValueError, match="expected_post_fix_obligation_counts"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_tampered_obligation_counts(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 1,
            "pending_proof_obligation_count": 1,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    manifest["post_fix_obligation_counts"] = {
        "pending_proof_entry_count": 1,
        "pending_proof_obligation_count": 999,
        "pending_retry_entry_count": 0,
        "pending_retry_obligation_count": 0,
    }

    with pytest.raises(ValueError, match="post_fix_obligation_counts"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_bool_status_counts(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    manifest["post_fix_status_counts"] = {"pending_proof": True}

    with pytest.raises(ValueError, match="post_fix_status_counts"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_bool_gate_status_counts(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    manifest["gates"][0]["post_fix_status_counts"] = {"pending_proof": True}

    with pytest.raises(ValueError, match="derived_failed_kinds"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_negative_gate_status_counts(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    manifest["gates"][0]["post_fix_status_counts"] = {"pending_proof": -1}

    with pytest.raises(ValueError, match="derived_failed_kinds"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_bool_obligation_counts(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 1,
            "pending_proof_obligation_count": 1,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    manifest["post_fix_obligation_counts"] = {
        "pending_proof_entry_count": True,
        "pending_proof_obligation_count": True,
        "pending_retry_entry_count": 0,
        "pending_retry_obligation_count": 0,
    }

    with pytest.raises(ValueError, match="post_fix_obligation_counts"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


@pytest.mark.parametrize("bad_count", (True, -1))
def test_phase3_post_fix_gate_index_rejects_invalid_expected_obligation_count_spec(
    tmp_path,
    bad_count,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": bad_count,
            "pending_proof_obligation_count": 1,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")

    with pytest.raises(ValueError, match="expected_post_fix_obligation_counts"):
        build_phase3_post_fix_gate_index(
            repo_root=repo,
            output_dir=tmp_path / "out",
            gate_specs=(spec,),
        )


def test_phase3_post_fix_gate_index_rejects_negative_gate_obligation_summary_count(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 1},
        expected_post_fix_obligation_counts={
            "pending_proof_entry_count": 1,
            "pending_proof_obligation_count": 1,
            "pending_retry_entry_count": 0,
            "pending_retry_obligation_count": 0,
        },
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    manifest["gates"][0]["post_fix_obligation_summary"][
        "pending_proof_obligation_count"
    ] = -1

    with pytest.raises(ValueError, match="derived_failed_kinds"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_tampered_status_counts(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], post_fix_status="pending_proof")
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["post_fix_status_counts"] = {}

    with pytest.raises(ValueError, match="post_fix_status_counts"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_missing_gate(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert "phase3_post_fix_gate_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_non_mapping_gate_payload(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    path = repo / specs[0].gate_relpath
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(["not", "a", "gate"]))

    index_path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(index_path.read_text())
    gate = manifest["gates"][0]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert gate["status"] == "invalid_payload"
    assert gate["validator_status"] == "failed"
    assert "gate payload must be an object" in gate["validator_error"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_records_validator_exception(tmp_path):
    def exploding_validator(_manifest):
        raise RuntimeError("validator crashed")

    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=exploding_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
    )
    _write_gate(repo, spec)

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    gate = manifest["gates"][0]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert gate["validator_status"] == "failed"
    assert gate["validator_error"] == "RuntimeError: validator crashed"
    assert "phase3_post_fix_gate_validator" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_validator"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


@pytest.mark.parametrize("summary_failed", (False, -1))
def test_phase3_post_fix_gate_index_rejects_malformed_gate_summary_failed_count(
    tmp_path,
    summary_failed,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], summary_failed=summary_failed, summary_failed_kinds=[])

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert "phase3_post_fix_gate_summary_clean" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_summary_clean"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_malformed_gate_summary_failed_kinds(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["post_fix_regression_gate"]["summary"]["failed_kinds"] = "not-a-list"
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert "phase3_post_fix_gate_summary_clean" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_summary_clean"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_recomputes_nested_regression_gate_summary(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["post_fix_regression_gate"]["summary"] = {
        "total": 1,
        "passed": 1,
        "failed": 0,
        "failed_kinds": [],
    }
    gate["post_fix_regression_gate"]["checks"] = [
        {"kind": "hidden_nested_failure", "status": "failed"}
    ]
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    materialized_gate = manifest["gates"][0]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert materialized_gate["validator_status"] == "passed"
    assert materialized_gate["post_fix_summary"] == {
        "total": 1,
        "passed": 0,
        "failed": 1,
        "failed_kinds": ["hidden_nested_failure"],
    }
    assert "phase3_post_fix_gate_summary_consistent" in manifest["summary"][
        "failed_kinds"
    ]
    assert "phase3_post_fix_gate_summary_clean" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_summary_consistent"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_missing_gate_summary_even_when_ready(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate.pop("post_fix_regression_gate")
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["ready_value"] is True
    assert "phase3_post_fix_gate_summary_clean" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_summary_clean"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_wrong_gate_summary_source(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate.pop("post_fix_regression_gate")
    gate["checks"] = []
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["post_fix_summary_source"] == "top_level_checks"
    assert "phase3_post_fix_gate_summary_source" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_summary_source"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_empty_top_level_summary_checks(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_summary_source="top_level_checks",
    )
    _write_gate(repo, spec)
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    gate.pop("post_fix_regression_gate")
    gate["checks"] = []
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert "phase3_post_fix_gate_summary_checks_present" in manifest["summary"][
        "failed_kinds"
    ]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_summary_checks_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_invalid_top_level_summary_check(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_summary_source="top_level_checks",
    )
    _write_gate(repo, spec)
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    gate.pop("post_fix_regression_gate")
    gate["checks"] = [
        {"kind": "valid_check", "status": "ok"},
        {"kind": "invalid_check", "status": "unknown"},
    ]
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["post_fix_summary_invalid_checks"] == [
        {"check_index": 1, "field": "status", "value": "unknown"}
    ]
    assert "phase3_post_fix_gate_summary_checks_valid" in manifest["summary"][
        "failed_kinds"
    ]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_summary_checks_valid"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_invalid_nested_summary_check(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["post_fix_regression_gate"] = {
        "summary": {"total": 2, "passed": 1, "failed": 0, "failed_kinds": []},
        "checks": [
            {"kind": "valid_check", "status": "ok"},
            {"kind": "invalid_check", "status": "unknown"},
        ],
    }
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["post_fix_summary_invalid_checks"] == [
        {"check_index": 1, "field": "status", "value": "unknown"}
    ]
    assert "phase3_post_fix_gate_summary_checks_valid" in manifest["summary"][
        "failed_kinds"
    ]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_summary_checks_valid"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_recomputes_tampered_ready_value(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["gates"][0]["ready_value"] = False

    with pytest.raises(ValueError, match="derived_failed_kinds"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_hidden_check_list(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["checks"] = []
    manifest["summary"] = {
        "total": 0,
        "failed": 0,
        "failed_kinds": [],
        "failed_kind_counts": {},
        "failed_lanes": [],
        "failed_index_kinds": [],
    }

    with pytest.raises(ValueError, match="derived_checks"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_tampered_summary_counts(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["summary"]["total"] = 0

    with pytest.raises(ValueError, match="summary_consistency"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_deleted_gate_after_index_build(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    (repo / specs[0].gate_relpath).unlink()

    with pytest.raises(ValueError, match="materialized_gates"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_missing_materialized_context(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest.pop("repo_root")

    with pytest.raises(ValueError, match="materialized_context_missing"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_gate_baseline_head_drift(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], baseline_git_head="wrong-head")

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert "phase3_post_fix_gate_baseline_git_head" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_baseline_git_head"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_gate_summary_failure(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        summary_failed=1,
        summary_failed_kinds=["hidden_post_fix_failure"],
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert "phase3_post_fix_gate_summary_clean" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_summary_clean"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_hidden_gate_entries(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"] = []
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["entry_count"] == 0
    assert "phase3_post_fix_gate_entry_count" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_entry_count"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_entries_without_status(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"] = [{}]
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["entry_count"] == 1
    assert manifest["gates"][0]["post_fix_status_counts"] == {}
    assert "phase3_post_fix_gate_status_count_complete" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_status_count_complete"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_entry_without_concrete_id(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"][0].pop("id")
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["post_fix_invalid_entry_ids"] == [
        {"entry_index": 0, "entry_id": "<missing>"}
    ]
    assert "phase3_post_fix_gate_entry_ids_concrete" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_entry_ids_concrete"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_entry_with_whitespace_id(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"][0]["id"] = "   "
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["post_fix_invalid_entry_ids"] == [
        {"entry_index": 0, "entry_id": "   "}
    ]
    assert "phase3_post_fix_gate_entry_ids_concrete" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_entry_ids_concrete"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_duplicate_entry_ids(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 2},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    second_entry = json.loads(json.dumps(gate["entries"][0]))
    second_entry["pending_proof_obligations"][0]["proof_obligation_id"] = [
        "proof",
        "lane_one",
        "second",
    ]
    second_entry["required_completion_actions"][0]["proof_obligation_id"] = [
        "proof",
        "lane_one",
        "second",
    ]
    gate["entries"].append(second_entry)
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["gates"][0]["post_fix_duplicate_entry_ids"] == ["lane_one-entry"]
    assert "phase3_post_fix_gate_entry_ids_unique" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_entry_ids_unique"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


@pytest.mark.parametrize(
    ("field_name", "expected_value"),
    (
        ("function", "<missing>"),
        ("binary_pair", "<missing>"),
        ("post_fix_status", "<missing>"),
    ),
)
def test_phase3_post_fix_gate_index_rejects_entry_without_concrete_metadata(
    tmp_path,
    field_name,
    expected_value,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"][0].pop(field_name)
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert {
        "entry_index": 0,
        "entry_id": "lane_one-entry",
        "field": field_name,
        "value": expected_value,
    } in manifest["gates"][0]["post_fix_invalid_entry_metadata"]
    assert "phase3_post_fix_gate_entry_metadata_concrete" in manifest["summary"][
        "failed_kinds"
    ]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_entry_metadata_concrete"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_whitespace_entry_metadata(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"][0]["function"] = "   "
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert {
        "entry_index": 0,
        "entry_id": "lane_one-entry",
        "field": "function",
        "value": "   ",
    } in manifest["gates"][0]["post_fix_invalid_entry_metadata"]
    assert "phase3_post_fix_gate_entry_metadata_concrete" in manifest["summary"][
        "failed_kinds"
    ]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_entry_metadata_concrete"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_unexpected_post_fix_status(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], post_fix_status="forged_ready")

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert manifest["post_fix_status_counts"] == {"forged_ready": 1}
    assert "phase3_post_fix_gate_status_allowed" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_status_allowed"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_pending_proof_without_obligations(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], post_fix_status="pending_proof", omit_pending_obligations=True)

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    gate = manifest["gates"][0]
    assert gate["post_fix_obligation_summary"]["pending_proof_entry_count"] == 1
    assert gate["post_fix_obligation_summary"]["pending_proof_obligation_count"] == 0
    assert gate["post_fix_obligation_summary"]["pending_proof_entries_missing_obligations"] == [
        "lane_one-entry"
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_pending_retry_without_obligations(tmp_path):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=9,
        lane_id="lane_retry",
        gate_relpath="logs/lane_retry/gate.json",
        manifest_kind="lane_retry_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=1,
        allowed_post_fix_statuses=("pending_retry",),
    )
    _write_gate(repo, spec, post_fix_status="pending_retry", omit_pending_obligations=True)

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    gate = manifest["gates"][0]
    assert gate["post_fix_obligation_summary"]["pending_retry_entry_count"] == 1
    assert gate["post_fix_obligation_summary"]["pending_retry_obligation_count"] == 0
    assert gate["post_fix_obligation_summary"]["pending_retry_entries_missing_obligations"] == [
        "lane_retry-entry"
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_malformed_pending_obligation(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        pending_obligation_updates={"proof_obligation_id": ["proof", "<missing>"]},
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    invalid = manifest["gates"][0]["post_fix_obligation_summary"]["pending_proof_invalid_obligations"]
    assert invalid == [{"entry_id": "lane_one-entry", "obligation_index": 0}]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_scalar_pending_obligation_proof_id(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        pending_obligation_updates={"proof_obligation_id": 0},
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["pending_proof_invalid_obligations"] == [
        {"entry_id": "lane_one-entry", "obligation_index": 0}
    ]
    assert summary["pending_proof_invalid_required_actions"] == [
        {"entry_id": "lane_one-entry", "required_action_index": 0}
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_duplicate_pending_obligation_required_evidence(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        pending_obligation_updates={
            "required_evidence": ["evidence_kind_one", "evidence_kind_one"]
        },
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["pending_proof_invalid_obligations"] == [
        {"entry_id": "lane_one-entry", "obligation_index": 0}
    ]
    assert summary["pending_proof_invalid_required_actions"] == [
        {"entry_id": "lane_one-entry", "required_action_index": 0}
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_scalar_pending_obligation_required_evidence(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        pending_obligation_updates={"required_evidence": 0},
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["pending_proof_invalid_obligations"] == [
        {"entry_id": "lane_one-entry", "obligation_index": 0}
    ]
    assert summary["pending_proof_invalid_required_actions"] == [
        {"entry_id": "lane_one-entry", "required_action_index": 0}
    ]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_duplicate_pending_obligation(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], post_fix_status="pending_proof")
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"][0]["pending_proof_obligations"].append(
        dict(gate["entries"][0]["pending_proof_obligations"][0])
    )
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert len(summary["pending_proof_duplicate_obligations"]) == 1
    assert summary["pending_proof_duplicate_obligations"][0]["entry_id"] == "lane_one-entry"
    assert summary["pending_proof_required_action_mismatches"] == []
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_duplicate_proof_obligation_id(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], post_fix_status="pending_proof")
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    entry = gate["entries"][0]
    second_obligation = dict(entry["pending_proof_obligations"][0])
    second_obligation["proof_stage"] = "proof_stage_two"
    second_obligation["evidence_kind"] = "evidence_kind_two"
    second_obligation["required_evidence"] = ["evidence_kind_two"]
    entry["pending_proof_obligations"].append(second_obligation)
    entry["required_completion_actions"].append(
        {
            key: second_obligation[key]
            for key in (
                "reason_id",
                "proof_kind",
                "proof_stage",
                "evidence_kind",
                "required_evidence",
                "proof_obligation_id",
            )
        }
    )
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["pending_proof_duplicate_obligations"] == []
    assert len(summary["pending_proof_duplicate_obligation_ids"]) == 1
    assert len(summary["pending_proof_duplicate_required_action_ids"]) == 1
    assert summary["pending_proof_required_action_mismatches"] == []
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_duplicate_proof_obligation_id_across_entries(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("pending_proof",),
        expected_post_fix_status_counts={"pending_proof": 2},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    first_entry = gate["entries"][0]
    second_entry = {
        "id": "lane_one-second-entry",
        "post_fix_status": "pending_proof",
        "pending_proof_obligations": [
            dict(first_entry["pending_proof_obligations"][0])
        ],
        "required_completion_actions": [
            dict(first_entry["required_completion_actions"][0])
        ],
    }
    gate["entries"].append(second_entry)
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["pending_proof_duplicate_obligation_ids"] == []
    assert len(summary["pending_proof_duplicate_obligation_ids_across_entries"]) == 1
    assert summary["pending_proof_duplicate_obligation_ids_across_entries"][0][
        "entry_ids"
    ] == ["lane_one-entry", "lane_one-second-entry"]
    assert len(summary["pending_proof_duplicate_required_action_ids_across_entries"]) == 1
    assert summary["pending_proof_required_action_mismatches"] == []
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_duplicate_proof_obligation_id_across_statuses(
    tmp_path,
):
    repo = tmp_path / "repo"
    spec = Phase3PostFixGateSpec(
        lane_number=1,
        lane_id="lane_one",
        gate_relpath="logs/lane_one/gate.json",
        manifest_kind="lane_one_post_fix_gate",
        ready_key="ready",
        validator=_validator,
        expected_entry_count=2,
        allowed_post_fix_statuses=("pending_proof", "pending_retry"),
        expected_post_fix_status_counts={"pending_proof": 1, "pending_retry": 1},
    )
    _write_gate(repo, spec, post_fix_status="pending_proof")
    gate_path = repo / spec.gate_relpath
    gate = json.loads(gate_path.read_text())
    first_entry = gate["entries"][0]
    retry_obligation = dict(first_entry["pending_proof_obligations"][0])
    retry_obligation["status"] = "pending_retry"
    retry_entry = {
        "id": "lane_one-retry-entry",
        "post_fix_status": "pending_retry",
        "pending_retry_obligations": [retry_obligation],
        "required_completion_actions": [
            {
                key: retry_obligation[key]
                for key in (
                    "reason_id",
                    "proof_kind",
                    "proof_stage",
                    "evidence_kind",
                    "required_evidence",
                    "proof_obligation_id",
                )
            }
        ],
    }
    gate["entries"].append(retry_entry)
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=(spec,),
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["pending_proof_duplicate_obligation_ids_across_entries"] == []
    assert summary["pending_retry_duplicate_obligation_ids_across_entries"] == []
    assert len(summary["duplicate_obligation_ids_across_statuses"]) == 1
    assert len(summary["duplicate_required_action_ids_across_statuses"]) == 1
    assert summary["pending_proof_required_action_mismatches"] == []
    assert summary["pending_retry_required_action_mismatches"] == []
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=(spec,))


def test_phase3_post_fix_gate_index_rejects_pending_obligation_required_action_mismatch(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        include_required_completion_actions=True,
        required_action_updates={"proof_obligation_id": ["proof", "lane_one", "different"]},
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    mismatches = manifest["gates"][0]["post_fix_obligation_summary"][
        "pending_proof_required_action_mismatches"
    ]
    assert len(mismatches) == 1
    assert mismatches[0]["entry_id"] == "lane_one-entry"
    assert mismatches[0]["missing_required_actions"]
    assert mismatches[0]["unexpected_obligations"]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_scalar_required_action_proof_id(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        include_required_completion_actions=True,
        required_action_updates={"proof_obligation_id": 0},
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["pending_proof_invalid_required_actions"] == [
        {"entry_id": "lane_one-entry", "required_action_index": 0}
    ]
    assert summary["pending_proof_required_action_mismatches"]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_duplicate_required_action_required_evidence(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        include_required_completion_actions=True,
        required_action_updates={
            "required_evidence": ["evidence_kind_one", "evidence_kind_one"]
        },
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["pending_proof_invalid_required_actions"] == [
        {"entry_id": "lane_one-entry", "required_action_index": 0}
    ]
    assert summary["pending_proof_required_action_mismatches"]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_scalar_required_action_required_evidence(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        include_required_completion_actions=True,
        required_action_updates={"required_evidence": 0},
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["pending_proof_invalid_required_actions"] == [
        {"entry_id": "lane_one-entry", "required_action_index": 0}
    ]
    assert summary["pending_proof_required_action_mismatches"]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_pending_obligation_without_required_actions(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(
        repo,
        specs[0],
        post_fix_status="pending_proof",
        omit_required_completion_actions=True,
    )

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())

    assert manifest["phase3_post_fix_gates_ready"] is False
    missing = manifest["gates"][0]["post_fix_obligation_summary"][
        "pending_proof_entries_missing_required_actions"
    ]
    assert missing == ["lane_one-entry"]
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_malformed_required_completion_action(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], post_fix_status="pending_proof")
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"][0]["required_completion_actions"].append("not-a-required-action")
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert summary["pending_proof_invalid_required_actions"] == [
        {
            "entry_id": "lane_one-entry",
            "required_action_index": 1,
        }
    ]
    assert summary["pending_proof_required_action_mismatches"] == []
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_duplicate_required_completion_action(
    tmp_path,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0], post_fix_status="pending_proof")
    gate_path = repo / specs[0].gate_relpath
    gate = json.loads(gate_path.read_text())
    gate["entries"][0]["required_completion_actions"].append(
        dict(gate["entries"][0]["required_completion_actions"][0])
    )
    gate_path.write_text(json.dumps(gate, sort_keys=True))

    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    summary = manifest["gates"][0]["post_fix_obligation_summary"]

    assert manifest["phase3_post_fix_gates_ready"] is False
    assert len(summary["pending_proof_duplicate_required_actions"]) == 1
    assert summary["pending_proof_duplicate_required_actions"][0]["entry_id"] == "lane_one-entry"
    assert summary["pending_proof_required_action_mismatches"] == []
    assert "phase3_post_fix_gate_pending_obligations_present" in manifest["summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase3_post_fix_gate_pending_obligations_present"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


def test_phase3_post_fix_gate_index_rejects_manifest_repo_root_drift(tmp_path):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    manifest["repo_root"] = str(tmp_path / "forged-repo")

    with pytest.raises(ValueError, match="repo_root"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)


@pytest.mark.parametrize(
    "created_at",
    (
        None,
        "",
        "<missing>",
        "not-a-timestamp",
        "2026-01-01T00:00:00",
    ),
)
def test_phase3_post_fix_gate_index_rejects_invalid_manifest_created_at(
    tmp_path,
    created_at,
):
    repo = tmp_path / "repo"
    specs = (_spec(1, "lane_one"),)
    _write_gate(repo, specs[0])
    path = build_phase3_post_fix_gate_index(
        repo_root=repo,
        output_dir=tmp_path / "out",
        gate_specs=specs,
    )
    manifest = json.loads(path.read_text())
    if created_at is None:
        manifest.pop("created_at")
    else:
        manifest["created_at"] = created_at

    with pytest.raises(ValueError, match="created_at"):
        validate_phase3_post_fix_gate_index(manifest, repo_root=repo, gate_specs=specs)
