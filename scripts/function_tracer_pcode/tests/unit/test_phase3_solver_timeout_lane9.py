# -*- coding: utf-8 -*-

import hashlib
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownReasonId,
    build_unknown_recovery_actions,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.validation.phase3_solver_timeout_lane9 import (
    build_phase3_solver_timeout_lane9_manifest,
    build_phase3_solver_timeout_lane9_post_fix_gate,
    validate_phase3_solver_timeout_lane9_manifest,
    validate_phase3_solver_timeout_lane9_post_fix_gate,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


LEFT_BINARY_NAME = "function_call_test-arm64-gcc-O3"
RIGHT_BINARY_NAME = "function_call_test-mips64-clang-O0"
QUERY_HASH = hashlib.sha256(b"(check-sat)").hexdigest()


def _sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_artifact_manifest(root: Path) -> None:
    root.mkdir(parents=True)
    (root / "artifact_manifest.json").write_text(
        json.dumps(
            {
                "baseline_id": "observed-v0@0a53352",
                "git_head": "0a53352cf3c9528abfb654906ed7b963474bedc5",
            }
        )
    )


def _return_case(binary_id: str, entry: int, address: str):
    return [
        "return_case",
        0,
        address,
        [
            "pcode_op",
            binary_id,
            ["function_entry", "ram", entry],
            ["seq_target", "ram", entry + 20],
            12,
            1,
            10,
            1,
        ],
        f"{address}:t12",
        1,
        ["expression", ["const", ["int", 1], 8]],
        [
            [
                "return_guard",
                True,
                ["condition", ["const", ["int", 1], 1], True],
                ["expression", ["const", ["int", 1], 1]],
            ]
        ],
    ]


def _side(side: str, binary_id: str, entry: int, address: str):
    return [
        "solver_timeout_side",
        side,
        ["function_ref", ["function", binary_id, entry]],
        ["return_storage", "return_value", 64, None, "long"],
        ["return_partition", [_return_case(binary_id, entry, address)]],
        [
            "guard_disjunction",
            [
                [
                    0,
                    [
                        [
                            "return_guard",
                            True,
                            ["condition", ["const", ["int", 1], 1], True],
                            ["expression", ["const", ["int", 1], 1]],
                        ]
                    ],
                ]
            ],
        ],
    ]


def _target(pair="B8_B9"):
    return [
        "solver_timeout",
        ["pair", pair],
        ["stage", "S_MONOLITHIC_FALLBACK"],
        ["query_hash", QUERY_HASH],
        ["timeout_budget_seconds", 10],
        ["solver_options", ["solver", "Z3"], ["timeout_seconds", 10]],
        _side("left", "B8", 1051028, "001009a8"),
        _side("right", "B9", 4198400, "00401000"),
    ]


def _timeout_reason(target=None):
    kwargs = {
        "stage": "S_MONOLITHIC_FALLBACK",
        "evidence_refs": ("monolithic_query_timeout",),
        "evidence_kind": "query_hash",
        "detail": "monolithic solver query timed out",
    }
    if target is not None:
        kwargs["object_target_key"] = target
    return make_unknown_reason(UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT, **kwargs)


def _action_payload(action):
    return action if isinstance(action, dict) else action.to_dict()


def _completed_evidence(action):
    target = action["object_target_key"]
    return [
        {
            "evidence": {
                "reason_id": action["reason_id"],
                "proof_stage": action["proof_stage"],
                "proof_kind": action["proof_kind"],
                "evidence_kind": action["evidence_kind"],
                "required_evidence": action["required_evidence"],
                "status": "complete",
                "object_derived": True,
                "object_target_key": target,
                "proof_obligation_id": action["proof_obligation_id"],
                "proof_content": {
                    "object_derived": True,
                    "object_target_key": target,
                    "query_hash": "complete",
                    "timeout_budget": "complete",
                    "solver_options": "complete",
                    "normalized_query": "complete",
                },
            }
        }
    ]


def _payload(*, reasons, actions=None, is_equivalent=None, is_timeout=True, completed_evidence=None):
    raw_reasons = [reason.to_dict() for reason in reasons]
    raw_actions = [
        _action_payload(action)
        for action in (actions if actions is not None else build_unknown_recovery_actions(reasons))
    ]
    return {
        "function1_name": "fc_long_branch_dispatch",
        "function2_name": "fc_long_branch_dispatch",
        "binary1_name": LEFT_BINARY_NAME,
        "binary2_name": RIGHT_BINARY_NAME,
        "is_equivalent": is_equivalent,
        "is_timeout": is_timeout,
        "error_message": None,
        "debug_trace": {
            "final_result": is_equivalent,
            "attempts": [
                {
                    "attempt_id": 0,
                    "phase": "P0_BASE",
                    "result": is_equivalent,
                    "transition_reason": "UNKNOWN",
                    "unknown_reasons": raw_reasons,
                }
            ],
        },
        "unknown_reasons": raw_reasons,
        "unknown_recovery_actions": raw_actions,
        "completed_recovery_proof_evidence": list(completed_evidence or ()),
    }


def _write_log(root: Path, payload: dict) -> Path:
    path = root / "fc_long_branch_dispatch" / "fc_long_branch_dispatch_B8_B9.log"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            [
                "Result: TIMEOUT" if payload.get("is_timeout") else "Result: UNKNOWN",
                RESULT_JSON_BEGIN,
                json.dumps(payload, indent=2, sort_keys=True),
                RESULT_JSON_END,
                "",
            ]
        )
    )
    return path


def _setup_logs(tmp_path: Path, *, current_payload: dict):
    raw_dir = tmp_path / "raw"
    _write_artifact_manifest(raw_dir)
    baseline_root = raw_dir / "logs" / "function_call"
    current_root = tmp_path / "current"
    _write_log(baseline_root, _payload(reasons=[_timeout_reason()]))
    _write_log(current_root, current_payload)
    return raw_dir, baseline_root, current_root


def test_phase3_solver_timeout_lane9_manifest_and_post_fix_gate_ready(tmp_path):
    current_payload = _payload(reasons=[_timeout_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_solver_timeout_lane9_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane9_ready"] is True
    validate_phase3_solver_timeout_lane9_manifest(manifest)
    tampered_manifest = json.loads(json.dumps(manifest))
    tampered_manifest["readiness"]["failure_kinds"] = ["hidden_lane9_failure"]
    with pytest.raises(ValueError, match="hidden_lane9_failure"):
        validate_phase3_solver_timeout_lane9_manifest(tampered_manifest)

    entry = manifest["entries"][0]
    assert len(entry["target_object_keys"]) == 1
    assert entry["target_object_keys"][0][1] == ["pair", "B8_B9"]
    assert len(entry["required_completion_actions"]) == 1
    assert entry["required_completion_actions"][0]["proof_obligation_id"]

    post_fix_path = build_phase3_solver_timeout_lane9_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane9_post_fix_ready"] is True
    assert gate["entries"][0]["post_fix_status"] == "pending_retry"
    assert gate["entries"][0]["pending_retry_obligations"] == [
        {
            "reason_id": "solver_unknown_timeout",
            "proof_kind": "solver_retry_or_normalization",
            "proof_stage": "solver_timeout_retry",
            "evidence_kind": "query_hash",
            "required_evidence": [
                "query_hash",
                "timeout_budget",
                "solver_options",
                "normalized_query",
            ],
            "proof_obligation_id": entry["required_completion_actions"][0]["proof_obligation_id"],
            "completed_evidence_present": False,
            "status": "pending_retry",
        }
    ]
    validate_phase3_solver_timeout_lane9_post_fix_gate(gate)
    tampered_gate = json.loads(json.dumps(gate))
    tampered_gate["post_fix_regression_gate"]["summary"]["failed_kinds"] = ["hidden_lane9_post_fix_failure"]
    with pytest.raises(ValueError, match="hidden_lane9_post_fix_failure"):
        validate_phase3_solver_timeout_lane9_post_fix_gate(tampered_gate)
    tampered_pre_fix = json.loads(pre_fix_path.read_text())
    tampered_pre_fix["readiness"]["failure_kinds"] = ["hidden_lane9_pre_fix_manifest_failure"]
    tampered_pre_fix_path = pre_fix_path.with_name(
        "tampered_solver_timeout_lane9_representatives.json"
    )
    tampered_pre_fix_path.write_text(json.dumps(tampered_pre_fix))
    tampered_pre_fix_gate_path = build_phase3_solver_timeout_lane9_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate-tampered-pre-fix",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=tampered_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(tampered_pre_fix_path),
    )
    tampered_pre_fix_gate = json.loads(tampered_pre_fix_gate_path.read_text())
    assert tampered_pre_fix_gate["phase3_lane9_post_fix_ready"] is False
    assert (
        "phase3_pre_fix_manifest_ready"
        in tampered_pre_fix_gate["post_fix_regression_gate"]["summary"]["failed_kinds"]
    )
    ready_check = next(
        check
        for check in tampered_pre_fix_gate["post_fix_regression_gate"]["checks"]
        if check["kind"] == "phase3_pre_fix_manifest_ready"
    )
    assert ready_check["status"] == "failed"
    assert "hidden_lane9_pre_fix_manifest_failure" in ready_check["error"]
    with pytest.raises(ValueError, match="phase3_pre_fix_manifest_ready"):
        validate_phase3_solver_timeout_lane9_post_fix_gate(tampered_pre_fix_gate)


def test_phase3_solver_timeout_lane9_manifest_rejects_missing_concrete_pair(tmp_path):
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[_timeout_reason(_target(pair=None))]),
    )

    pre_fix_path = build_phase3_solver_timeout_lane9_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane9_ready"] is False
    assert "solver_timeout_current_targets_present" in manifest["readiness"]["failure_kinds"]
    with pytest.raises(ValueError, match="solver_timeout_current_targets_present"):
        validate_phase3_solver_timeout_lane9_manifest(manifest)


def test_phase3_solver_timeout_lane9_manifest_rejects_missing_raw_proof_id(tmp_path):
    reason = _timeout_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    actions[0]["proof_obligation_id"] = None
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )

    pre_fix_path = build_phase3_solver_timeout_lane9_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane9_ready"] is False
    assert "solver_timeout_current_actions_complete" in manifest["readiness"]["failure_kinds"]


def test_phase3_solver_timeout_lane9_manifest_accepts_multiple_solver_names(tmp_path):
    target = _target()
    target[5] = ["solver_options", ["solvers", ["CVC5", "Yices2"]], ["timeout_seconds", 10]]
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[_timeout_reason(target)]),
    )

    pre_fix_path = build_phase3_solver_timeout_lane9_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane9_ready"] is True
    assert manifest["entries"][0]["target_object_keys"][0][5] == [
        "solver_options",
        ["solvers", ["CVC5", "Yices2"]],
        ["timeout_seconds", 10],
    ]


@pytest.mark.parametrize(
    "solver_info",
    [
        ["solver", "unknown_solver"],
        ["solver", "UNKNOWN_SOLVER"],
        ["solver", "no_solver_result"],
        ["solvers", ["CVC5", "unknown_solver"]],
    ],
)
def test_phase3_solver_timeout_lane9_manifest_rejects_placeholder_solver_names(tmp_path, solver_info):
    target = _target()
    target[5] = ["solver_options", solver_info, ["timeout_seconds", 10]]
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[_timeout_reason(target)]),
    )

    pre_fix_path = build_phase3_solver_timeout_lane9_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane9_ready"] is False
    assert "solver_timeout_current_targets_present" in manifest["readiness"]["failure_kinds"]


def test_phase3_solver_timeout_lane9_post_fix_gate_accepts_completed_recovery_with_proof(tmp_path):
    reason = _timeout_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )
    pre_fix_path = build_phase3_solver_timeout_lane9_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    completed_root = tmp_path / "completed"
    _write_log(
        completed_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            is_timeout=False,
            completed_evidence=_completed_evidence(actions[0]),
        ),
    )
    post_fix_path = build_phase3_solver_timeout_lane9_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": completed_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane9_post_fix_ready"] is True
    assert gate["entries"][0]["post_fix_status"] == "completed_recovery"
    validate_phase3_solver_timeout_lane9_post_fix_gate(gate)


def test_phase3_solver_timeout_lane9_post_fix_gate_rejects_unknown_without_expected_movement(tmp_path):
    reason = _timeout_reason(_target())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )
    pre_fix_path = build_phase3_solver_timeout_lane9_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    unknown_root = tmp_path / "unknown"
    _write_log(
        unknown_root,
        _payload(
            reasons=[reason],
            is_equivalent=None,
            is_timeout=False,
        ),
    )
    post_fix_path = build_phase3_solver_timeout_lane9_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": unknown_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane9_post_fix_ready"] is False
    entry = gate["entries"][0]
    assert entry["post_fix_status"] == "failed"
    assert entry["post_fix_failures"][0]["kind"] == "solver_timeout_pending_retry_requires_timeout_final_result"
    assert entry["post_fix_failures"][0]["current_result"] == "UNKNOWN"
    with pytest.raises(ValueError, match="solver_timeout_post_fix_expected_movement"):
        validate_phase3_solver_timeout_lane9_post_fix_gate(gate)


def test_phase3_solver_timeout_lane9_post_fix_gate_rejects_eq_without_completed_proof(tmp_path):
    reason = _timeout_reason(_target())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )
    pre_fix_path = build_phase3_solver_timeout_lane9_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    eq_root = tmp_path / "eq"
    _write_log(eq_root, _payload(reasons=[], actions=[], is_equivalent=True, is_timeout=False))
    post_fix_path = build_phase3_solver_timeout_lane9_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": eq_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane9_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    with pytest.raises(ValueError, match="solver_timeout_post_fix_expected_movement"):
        validate_phase3_solver_timeout_lane9_post_fix_gate(gate)
