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
from scripts.function_tracer_pcode.validation.phase3_method_b_closure_lane4 import (
    build_phase3_method_b_closure_lane4_manifest,
    build_phase3_method_b_closure_lane4_post_fix_gate,
    main as phase3_method_b_closure_lane4_main,
    validate_phase3_method_b_closure_lane4_manifest,
    validate_phase3_method_b_closure_lane4_post_fix_gate,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


LEFT_BINARY_NAME = "loop_method_b_test-mips64-clang-O1"
RIGHT_BINARY_NAME = "loop_method_b_test-mips64-gcc-O0"


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


def _pcode_ref(binary_id: str):
    return [
        "pcode_op",
        binary_id,
        ["function_entry", "ram", 1052592 if binary_id == "B10" else 4831846228],
        ["seq_target", "ram", 1052644 if binary_id == "B10" else 4831846344],
        40,
        1,
        "RETURN",
        0,
    ]


def _guard(count_index: int):
    return [
        "return_guard",
        True,
        ["condition", ["parameter", "n", ["int", count_index], 4]],
        ["expression", ["parameter", "n", ["int", count_index], 4]],
    ]


def _return_case(binary_id: str, address: str, count_index: int):
    return [
        "readonly_return_case_partition_member",
        0,
        [0],
        [
            "return_case",
            0,
            address,
            _pcode_ref(binary_id),
            f"{address}:return",
            1,
        ],
        ["comparison_surface", "return_value", 32, None],
        ["value", ["expression", ["parameter", "sum", ["int", count_index], 4]]],
        ["guards", [_guard(count_index)]],
    ]


def _runtime_ref(binary_id: str, count_index: int):
    return [
        "readonly_reduction_proof_semantic",
        "memory_sum",
        ["parameter", 0],
        ["parameter_storage", ["register_storage", -1, 12756, 64, 0 if binary_id == "B10" else 32, 64 if binary_id == "B10" else 32]],
        4,
        [32, 0],
        [
            "readonly_reduction_term_sequence_contract",
            "memory_sum",
            ["parameter", 0],
            ["parameter_storage", ["register_storage", -1, 12756, 64, 0 if binary_id == "B10" else 32, 64 if binary_id == "B10" else 32]],
            ["loop_limit_parameter", count_index],
            4,
            0,
            2,
            0,
            4,
            True,
            [],
            [32, 0],
            ["loop_side_effect_profile", "pure_memory_read", True, False, False, False, False, False, False, False, False, 0, 0, [], []],
        ],
    ]


def _loop_summary(binary_id: str, step: int):
    return [
        "loop_summary_method_b",
        "scalar_element_index",
        0,
        ["loop_limit_parameter", 1],
        step,
        [
            "scalar_memory_term_sequence",
            "sum",
            ["parameter", 0],
            0,
            4,
            4,
            4,
        ],
        [],
        [32, 0],
        ["loop_side_effect_profile", "pure_memory_read", True, False, False, False, False, False, False, False, False, 0, 0, [], []],
    ]


def _loop_value(binary_id: str, count_index: int, *, has_loop: bool):
    runtime = _runtime_ref(binary_id, count_index) if has_loop else None
    loop = _loop_summary(binary_id, 2 if binary_id == "B13" else 1) if has_loop else None
    expression_key = ["expression", ["parameter", "sum", ["int", count_index], 4]]
    if has_loop:
        expression_key = ["runtime_ref", runtime]
    return [
        "loop_value",
        [
            "method_b_loop_value",
            runtime,
            loop,
            expression_key,
        ],
    ]


def _side(side: str, binary_id: str, address: str, count_index: int, *, has_loop: bool):
    return [
        "method_b_closure_side",
        side,
        ["function_ref", ["function", binary_id, 1052592 if binary_id == "B10" else 4831846228]],
        _return_case(binary_id, address, count_index),
        _loop_value(binary_id, count_index, has_loop=has_loop),
        ["guards", [_guard(count_index)]],
    ]


def _target():
    return [
        "method_b_closure",
        ["pair", "(4,0)"],
        _side("left", "B10", "00100fe4", 1, has_loop=False),
        _side("right", "B13", "120001fc8", 1, has_loop=True),
    ]


def _method_b_reason(target=None):
    kwargs = {
        "evidence_refs": ("loop_summary_unproven",),
        "stage": "S_PAIRWISE",
        "pair_or_case": "(4,0)",
    }
    if target is not None:
        kwargs["object_target_key"] = target
    return make_unknown_reason(UnknownReasonId.METHOD_B_CLOSURE_BLOCKED, **kwargs)


def _action_payload(action):
    return action if isinstance(action, dict) else action.to_dict()


def _payload(*, reasons, actions=None, is_equivalent=None, completed_evidence=None):
    raw_reasons = [reason.to_dict() for reason in reasons]
    raw_actions = [
        _action_payload(action)
        for action in (actions if actions is not None else build_unknown_recovery_actions(reasons))
    ]
    return {
        "function1_name": "lmb_sum_even_index_step2",
        "function2_name": "lmb_sum_even_index_step2",
        "binary1_name": LEFT_BINARY_NAME,
        "binary2_name": RIGHT_BINARY_NAME,
        "is_equivalent": is_equivalent,
        "is_timeout": False,
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
    path = root / "lmb_sum_even_index_step2" / "lmb_sum_even_index_step2_B10_B13.log"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            [
                "Result: UNKNOWN",
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
    baseline_root = raw_dir / "logs" / "loop"
    current_root = tmp_path / "current"
    _write_log(baseline_root, _payload(reasons=[_method_b_reason()]))
    _write_log(current_root, current_payload)
    return raw_dir, baseline_root, current_root


def _completed_evidence(actions, *, include_proof_content=True):
    records = []
    for action in actions:
        evidence = {
            "reason_id": action["reason_id"],
            "proof_stage": action["proof_stage"],
            "proof_kind": action["proof_kind"],
            "evidence_kind": action["evidence_kind"],
            "required_evidence": action["required_evidence"],
            "status": "complete",
            "object_derived": True,
            "object_target_key": action["object_target_key"],
            "proof_obligation_id": action["proof_obligation_id"],
        }
        if include_proof_content:
            proof_content = {
                "object_derived": True,
                "object_target_key": action["object_target_key"],
            }
            if action["proof_stage"] == "method_b_covering_case":
                proof_content.update(
                    {
                        "seed_compensation": "proven",
                        "term_sequence": "proven",
                        "pure_side_effect_profile": "proven",
                    }
                )
            else:
                proof_content.update(
                    {
                        "guard_partition": "proven",
                        "partition_coverage_proof": "proven",
                    }
                )
            evidence["proof_content"] = proof_content
        records.append({"evidence": evidence})
    return records


def test_phase3_method_b_closure_lane4_manifest_and_post_fix_gate_ready(tmp_path):
    current_payload = _payload(reasons=[_method_b_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_method_b_closure_lane4_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane4_ready"] is True
    validate_phase3_method_b_closure_lane4_manifest(manifest)

    entry = manifest["entries"][0]
    assert len(entry["target_object_keys"]) == 1
    assert {action["proof_stage"] for action in entry["required_completion_actions"]} == {
        "method_b_covering_case",
        "method_b_guard_partition",
    }
    assert all(action["proof_obligation_id"] for action in entry["required_completion_actions"])

    post_fix_path = build_phase3_method_b_closure_lane4_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane4_post_fix_ready"] is True
    assert gate["entries"][0]["post_fix_status"] == "pending_proof"
    validate_phase3_method_b_closure_lane4_post_fix_gate(gate)


def test_phase3_method_b_closure_lane4_manifest_rejects_nested_diagnostic_reason(tmp_path):
    target = _target()
    target[2][4][1][3] = ["expression", ["reason", "loop_summary_unproven"]]
    current_payload = _payload(reasons=[_method_b_reason(target)])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_method_b_closure_lane4_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane4_ready"] is False
    with pytest.raises(ValueError, match="method_b_closure_current_targets_present"):
        validate_phase3_method_b_closure_lane4_manifest(manifest)


def test_phase3_method_b_closure_lane4_manifest_rejects_raw_expression_payload(tmp_path):
    target = _target()
    target[2][4][1][3] = ["expression", ["binary", "INT_ADD", 4, "raw-left", ["const", ["int", 1], 4]]]
    current_payload = _payload(reasons=[_method_b_reason(target)])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_method_b_closure_lane4_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane4_ready"] is False
    with pytest.raises(ValueError, match="method_b_closure_current_targets_present"):
        validate_phase3_method_b_closure_lane4_manifest(manifest)


def test_phase3_method_b_closure_lane4_manifest_rejects_malformed_proof_id(tmp_path):
    reason = _method_b_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    actions[0]["proof_obligation_id"] = ["wrong", "proof"]
    current_payload = _payload(reasons=[reason], actions=actions)
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_method_b_closure_lane4_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane4_ready"] is False
    with pytest.raises(ValueError, match="method_b_closure_current_actions_complete"):
        validate_phase3_method_b_closure_lane4_manifest(manifest)


def test_phase3_method_b_closure_lane4_manifest_rejects_malformed_action_tuple(tmp_path):
    reason = _method_b_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    actions[0]["decision_effect"] = "retryable"
    actions[0]["reason_scope"] = "pair"
    actions[0]["aggregation_unit"] = "function"
    actions[0]["stage"] = "S_WRONG"
    current_payload = _payload(reasons=[reason], actions=actions)
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_method_b_closure_lane4_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane4_ready"] is False
    with pytest.raises(ValueError, match="method_b_closure_current_actions_complete"):
        validate_phase3_method_b_closure_lane4_manifest(manifest)


def test_phase3_method_b_closure_lane4_post_fix_requires_manifest_sha256(tmp_path):
    current_payload = _payload(reasons=[_method_b_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_method_b_closure_lane4_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )

    post_fix_path = build_phase3_method_b_closure_lane4_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane4_post_fix_ready"] is False
    with pytest.raises(ValueError, match="phase3_pre_fix_manifest_sha256_required"):
        validate_phase3_method_b_closure_lane4_post_fix_gate(gate)


def test_phase3_method_b_closure_lane4_post_fix_rejects_eq_without_completed_proofs(tmp_path):
    reason = _method_b_reason(_target())
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=_payload(reasons=[reason]))
    pre_fix_path = build_phase3_method_b_closure_lane4_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    _write_log(current_root, _payload(reasons=[], actions=[], is_equivalent=True))

    post_fix_path = build_phase3_method_b_closure_lane4_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane4_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    with pytest.raises(ValueError, match="method_b_closure_post_fix_expected_movement"):
        validate_phase3_method_b_closure_lane4_post_fix_gate(gate)


def test_phase3_method_b_closure_lane4_post_fix_accepts_eq_with_completed_proofs(tmp_path):
    reason = _method_b_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )
    pre_fix_path = build_phase3_method_b_closure_lane4_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=_completed_evidence(actions),
        ),
    )

    post_fix_path = build_phase3_method_b_closure_lane4_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane4_post_fix_ready"] is True
    assert gate["entries"][0]["post_fix_status"] == "completed_recovery"
    validate_phase3_method_b_closure_lane4_post_fix_gate(gate)


def test_phase3_method_b_closure_lane4_post_fix_rejects_eq_with_one_completed_proof(tmp_path):
    reason = _method_b_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )
    pre_fix_path = build_phase3_method_b_closure_lane4_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=_completed_evidence(actions[:1]),
        ),
    )

    post_fix_path = build_phase3_method_b_closure_lane4_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane4_post_fix_ready"] is False
    with pytest.raises(ValueError, match="method_b_closure_post_fix_expected_movement"):
        validate_phase3_method_b_closure_lane4_post_fix_gate(gate)


def test_phase3_method_b_closure_lane4_post_fix_rejects_metadata_only_completed_proofs(tmp_path):
    reason = _method_b_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )
    pre_fix_path = build_phase3_method_b_closure_lane4_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=_completed_evidence(actions, include_proof_content=False),
        ),
    )

    post_fix_path = build_phase3_method_b_closure_lane4_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane4_post_fix_ready"] is False
    with pytest.raises(ValueError, match="method_b_closure_post_fix_expected_movement"):
        validate_phase3_method_b_closure_lane4_post_fix_gate(gate)


def test_phase3_method_b_closure_lane4_post_fix_cli_requires_sha(capsys):
    with pytest.raises(SystemExit):
        phase3_method_b_closure_lane4_main(
            [
                "--gate-stage",
                "post-fix",
                "--baseline-raw-dir",
                "unused",
                "--output-dir",
                "unused",
            ]
        )
    assert "--phase3-manifest-sha256 is required" in capsys.readouterr().err
