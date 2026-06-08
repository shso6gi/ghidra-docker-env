# -*- coding: utf-8 -*-

import hashlib
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownReasonId,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.validation.phase3_return_width_bridge_lane2 import (
    build_phase3_return_width_bridge_lane2_manifest,
    build_phase3_return_width_bridge_lane2_post_fix_gate,
    main as phase3_return_width_bridge_lane2_main,
    validate_phase3_return_width_bridge_lane2_manifest,
    validate_phase3_return_width_bridge_lane2_post_fix_gate,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


LEFT_BINARY_NAME = "function_call_test-mips64-clang-O1"
RIGHT_BINARY_NAME = "function_call_test-mips64-gcc-O0"


def _pcode_ref(binary_id: str, function_entry: int, seq_target: int, *, seq_time: int = 40):
    return [
        "pcode_op",
        binary_id,
        ["function_entry", "ram", function_entry],
        ["seq_target", "ram", seq_target],
        seq_time,
        1,
        10,
        1,
    ]


def _return_case_partition_member(
    *,
    binary_id: str,
    function_entry: int,
    seq_target: int,
    address: str,
    return_width: int,
    case_index: int = 0,
):
    return [
        "return_case_partition_member",
        case_index,
        [case_index],
        [
            "return_case",
            case_index,
            address,
            _pcode_ref(binary_id, function_entry, seq_target),
            f"{address}:t40",
            1,
            ["expression", ["const", ["int", 1], return_width // 8]],
            [
                [
                    "return_guard",
                    True,
                    ["condition", ["const", ["int", 1], 1], True],
                    ["expression", ["const", ["int", 1], 1]],
                ]
            ],
        ],
        ["comparison_surface", "return_value", return_width, None],
        ["value", ["expression", ["const", ["int", 1], return_width // 8]]],
    ]


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


def _target(label: str = "case0"):
    return [
        "return_width_bridge",
        ["pair", label],
        ["return_widths", 32, 64],
        [
            "return_width_side",
            "left",
            ["function_ref", ["function", "B10", 1052592]],
            ["return_size", 32],
            ["return_storage", "return_value", 32, None, "int"],
            _return_case_partition_member(
                binary_id="B10",
                function_entry=1052592,
                seq_target=1052644,
                address="00100fe4",
                return_width=32,
            ),
        ],
        [
            "return_width_side",
            "right",
            ["function_ref", ["function", "B13", 4831846228]],
            ["return_size", 64],
            ["return_storage", "return_value", 64, None, "long"],
            _return_case_partition_member(
                binary_id="B13",
                function_entry=4831846228,
                seq_target=4831846344,
                address="120001fc8",
                return_width=64,
            ),
        ],
    ]


def _weak_target(label: str = "case0"):
    return [
        "return_width_bridge",
        ["pair", label],
        ["return_widths", 32, 64],
        ["return_width_side", "left", ["function_ref", ["function", "B10", 1052592]]],
        ["return_width_side", "right", ["function_ref", ["function", "B13", 4831846228]]],
    ]


def _weak_target_with_return_case_only(label: str = "case0"):
    return [
        "return_width_bridge",
        ["pair", label],
        ["return_widths", 32, 64],
        [
            "return_width_side",
            "left",
            ["return_case_partition_member", 0, [0], ["return_case", 0, "00100fe4"]],
        ],
        [
            "return_width_side",
            "right",
            ["return_case_partition_member", 0, [0], ["return_case", 0, "120001fc8"]],
        ],
    ]


def _target_with_return_size_mismatch(label: str = "case0"):
    target = json.loads(json.dumps(_target(label)))
    target[3][3] = ["return_size", 64]
    return target


def _target_with_function_ref(label: str, function_ref):
    target = json.loads(json.dumps(_target(label)))
    target[3][2] = ["function_ref", function_ref]
    return target


def _target_with_pair(pair_value):
    target = json.loads(json.dumps(_target("case0")))
    target[1] = ["pair", pair_value]
    return target


def _target_with_extra_missing_diagnostic():
    target = json.loads(json.dumps(_target("case0")))
    target.append(["diagnostic", "<missing>"])
    return target


def _target_with_return_case_member(label: str, return_case_member):
    target = json.loads(json.dumps(_target(label)))
    target[3][5] = return_case_member
    return target


def _valid_left_return_case_member():
    return _return_case_partition_member(
        binary_id="B10",
        function_entry=1052592,
        seq_target=1052644,
        address="00100fe4",
        return_width=32,
    )


def _return_case_member_with_guards(guards):
    member = _valid_left_return_case_member()
    member[3][7] = guards
    return member


def _return_case_member_with_return_value(return_value):
    member = _valid_left_return_case_member()
    member[3][6] = return_value
    return member


def _return_case_member_with_value_evidence(value_evidence):
    member = _valid_left_return_case_member()
    member[5] = value_evidence
    return member


def _return_case_member_with_comparison_surface(comparison_surface):
    member = _valid_left_return_case_member()
    member[4] = comparison_surface
    return member


def _return_case_member_with_guard_condition(condition):
    member = _valid_left_return_case_member()
    member[3][7][0][2] = condition
    return member


def _return_case_member_with_guard_expression(expression):
    member = _valid_left_return_case_member()
    member[3][7][0][3] = expression
    return member


def _width_reason(target=None):
    kwargs = {}
    if target is not None:
        kwargs["object_target_key"] = target
    return make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING, **kwargs)


def _action_payload(action):
    return action if isinstance(action, dict) else action.to_dict()


def _completed_proof_content(action):
    target = action["object_target_key"]
    widths = target[2]
    left = target[3]
    right = target[4]
    left_function_ref = left[2]
    right_function_ref = right[2]
    left_return_storage = left[4]
    right_return_storage = right[4]
    narrow_width = min(widths[1], widths[2])
    wide_width = max(widths[1], widths[2])
    if action["proof_kind"] == "abi_relation_proof":
        return {
            "calling_convention": {
                "object_derived": True,
                "left_function_ref": left_function_ref,
                "right_function_ref": right_function_ref,
                "relation": "same_return_abi_family",
            },
            "return_storage": {
                "object_derived": True,
                "left_return_storage": left_return_storage,
                "right_return_storage": right_return_storage,
                "relation": "abi_related_return_storage",
            },
            "narrow_return_width": {
                "object_derived": True,
                "narrow_width": narrow_width,
                "proven": True,
            },
        }
    if action["proof_kind"] == "high_bit_proof":
        return {
            "producer_width": {
                "object_derived": True,
                "left_width": widths[1],
                "right_width": widths[2],
            },
            "extension_semantics": {
                "object_derived": True,
                "left_extension": "narrow_return",
                "right_extension": "abi_return_extension",
                "relation": "compatible_under_narrow_width",
            },
            "high_bits_irrelevant_or_equal": {
                "object_derived": True,
                "narrow_width": narrow_width,
                "wide_width": wide_width,
                "proof": "high_bits_do_not_affect_compared_return",
                "proven": True,
            },
        }
    return {}


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
            evidence["proof_content"] = _completed_proof_content(action)
        records.append(
            {
                "evidence": {
                    **evidence,
                }
            }
        )
    return records


def _payload(*, reasons, actions=None, is_equivalent=None, completed_evidence=None):
    raw_reasons = [reason.to_dict() for reason in reasons]
    raw_actions = [
        _action_payload(action)
        for action in (actions if actions is not None else build_unknown_recovery_actions(reasons))
    ]
    return {
        "function1_name": "fc_apply_indirect",
        "function2_name": "fc_apply_indirect",
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
    path = root / "fc_apply_indirect" / "fc_apply_indirect_B10_B13.log"
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
    baseline_root = raw_dir / "logs" / "function_call"
    current_root = tmp_path / "current"
    _write_log(baseline_root, _payload(reasons=[_width_reason()]))
    _write_log(current_root, current_payload)
    return raw_dir, baseline_root, current_root


def test_phase3_return_width_bridge_lane2_manifest_and_post_fix_gate_ready(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is True
    validate_phase3_return_width_bridge_lane2_manifest(manifest)
    tampered_manifest = json.loads(json.dumps(manifest))
    tampered_manifest["readiness"]["failure_kinds"] = ["hidden_lane2_failure"]
    with pytest.raises(ValueError, match="hidden_lane2_failure"):
        validate_phase3_return_width_bridge_lane2_manifest(tampered_manifest)

    entry = manifest["entries"][0]
    assert len(entry["target_object_keys"]) == 1
    assert {action["proof_stage"] for action in entry["required_completion_actions"]} == {
        "abi_relation",
        "high_bit_relation",
    }
    assert all(action["proof_obligation_id"] for action in entry["required_completion_actions"])

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is True
    assert gate["entries"][0]["post_fix_status"] == "pending_proof"
    obligations = gate["entries"][0]["pending_proof_obligations"]
    assert {obligation["proof_stage"] for obligation in obligations} == {
        "abi_relation",
        "high_bit_relation",
    }
    assert all(
        obligation["reason_id"] == "return_width_bridge_missing"
        and obligation["completed_evidence_present"] is False
        and obligation["status"] == "pending_evidence"
        and obligation["proof_obligation_id"]
        for obligation in obligations
    )
    validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)
    tampered_gate = json.loads(json.dumps(gate))
    tampered_gate["post_fix_regression_gate"]["summary"]["failed_kinds"] = ["hidden_lane2_post_fix_failure"]
    with pytest.raises(ValueError, match="hidden_lane2_post_fix_failure"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(tampered_gate)
    tampered_pre_fix = json.loads(pre_fix_path.read_text())
    tampered_pre_fix["readiness"]["failure_kinds"] = ["hidden_lane2_pre_fix_manifest_failure"]
    tampered_pre_fix_path = pre_fix_path.with_name(
        "tampered_return_width_bridge_lane2_representatives.json"
    )
    tampered_pre_fix_path.write_text(json.dumps(tampered_pre_fix))
    tampered_pre_fix_gate_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate-tampered-pre-fix",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=tampered_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(tampered_pre_fix_path),
    )
    tampered_pre_fix_gate = json.loads(tampered_pre_fix_gate_path.read_text())
    assert tampered_pre_fix_gate["phase3_lane2_post_fix_ready"] is False
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
    assert "hidden_lane2_pre_fix_manifest_failure" in ready_check["error"]
    with pytest.raises(ValueError, match="phase3_pre_fix_manifest_ready"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(tampered_pre_fix_gate)


def test_phase3_return_width_bridge_lane2_manifest_rejects_missing_high_bit_action(tmp_path):
    reason = _width_reason(_target())
    actions = [
        action
        for action in build_unknown_recovery_actions([reason])
        if action.proof_stage != "high_bit_relation"
    ]
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_actions_complete" in manifest["readiness"]["failure_kinds"]
    with pytest.raises(ValueError, match="return_width_bridge_current_actions_complete"):
        validate_phase3_return_width_bridge_lane2_manifest(manifest)


def test_phase3_return_width_bridge_lane2_manifest_rejects_malformed_proof_id(tmp_path):
    reason = _width_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    actions[0]["proof_obligation_id"] = ["not", "the", "full", "key"]
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_actions_complete" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_manifest_rejects_wrong_action_metadata(tmp_path):
    reason = _width_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    actions[0]["evidence_kind"] = "not_expected_evidence"
    actions[0]["required_evidence"] = ["wrong"]
    actions[0]["status"] = "unexpected_status"
    actions[0]["proof_obligation_id"] = build_proof_obligation_id(
        actions[0]["reason_id"],
        actions[0]["proof_stage"],
        actions[0]["proof_kind"],
        actions[0]["evidence_kind"],
        actions[0]["object_target_key"],
    )
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_actions_complete" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_manifest_rejects_weak_object_target(tmp_path):
    reason = _width_reason(_weak_target())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_manifest_rejects_return_case_only_target(tmp_path):
    reason = _width_reason(_weak_target_with_return_case_only())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_manifest_rejects_side_return_size_mismatch(tmp_path):
    reason = _width_reason(_target_with_return_size_mismatch())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


@pytest.mark.parametrize(
    "function_ref",
    [
        ["function", None, 1052592],
        ["function", "", 1052592],
        ["function", "<missing>", 1052592],
        ["function", "B10", None],
        ["function", "B10", True],
        ["function", "123", 1052592],
        ["entry_point", "B10", 1052592],
    ],
)
def test_phase3_return_width_bridge_lane2_manifest_rejects_weak_function_ref(
    tmp_path,
    function_ref,
):
    reason = _width_reason(_target_with_function_ref("case0", function_ref))
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


@pytest.mark.parametrize("pair_value", [[], 0, "", "<missing>"])
def test_phase3_return_width_bridge_lane2_manifest_rejects_weak_pair_tag(tmp_path, pair_value):
    reason = _width_reason(_target_with_pair(pair_value))
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_manifest_rejects_missing_sentinel_in_target(
    tmp_path,
):
    reason = _width_reason(_target_with_extra_missing_diagnostic())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


@pytest.mark.parametrize(
    "return_case_member",
    [
        ["return_case_partition_member"],
        ["return_case_partition_member", None, [], None],
        [
            "return_case_partition_member",
            0,
            [],
            [
                "return_case",
                0,
                "00100fe4",
                _pcode_ref("B10", 1052592, 1052644),
                "00100fe4:t40",
                1,
                ["expression", ["const", ["int", 1], 4]],
                [],
            ],
            ["comparison_surface", "return_value", 32, None],
            ["value", ["expression", ["const", ["int", 1], 4]]],
        ],
        [
            "return_case_partition_member",
            0,
            [0],
            ["return_case", None, None],
            ["comparison_surface", "return_value", 32, None],
            ["value", ["expression", ["const", ["int", 1], 4]]],
        ],
        [
            "return_case_partition_member",
            0,
            [0],
            [
                "return_case",
                0,
                "00100fe4",
                ["pcode_op", "B10"],
                "00100fe4:t40",
                1,
                ["expression", ["const", ["int", 1], 4]],
                [],
            ],
            ["comparison_surface", "return_value", 32, None],
            ["value", ["expression", ["const", ["int", 1], 4]]],
        ],
        [
            "return_case_partition_member",
            0,
            [0],
            [
                "return_case",
                0,
                "00100fe4",
                _pcode_ref("B10", 1052592, 1052644),
                "00100fe4:t40",
                1,
                ["expression", ["const", ["int", 1], 4]],
                [],
            ],
            ["comparison_surface", "return_value", 64, None],
            ["value", ["expression", ["const", ["int", 1], 4]]],
        ],
        [
            "return_case_partition_member",
            0,
            [0],
            [
                "return_case",
                0,
                "00100fe4",
                _pcode_ref("B10", 1052592, 1052644),
                "00100fe4:t40",
                1,
                ["expression", ["const", ["int", 1], 4]],
                [],
            ],
            ["comparison_surface", "return_value", 32, None],
            ["value", None],
        ],
        _return_case_member_with_guards([]),
        _return_case_member_with_return_value("raw-prose-ish-return-value"),
        _return_case_member_with_return_value(["expression", "raw-prose-ish-return-value"]),
        _return_case_member_with_return_value(
            ["expression", ["const", "raw-prose-ish-return-value", 4]]
        ),
        _return_case_member_with_return_value(
            ["expression", ["const", ["bytes", "raw-prose-ish"], 4]]
        ),
        _return_case_member_with_return_value(
            [
                "expression",
                [
                    "memory",
                    32,
                    ["const", ["int", 1], 8],
                    ["read_order", "raw-prose-ish-order"],
                ],
            ]
        ),
        _return_case_member_with_return_value(
            [
                "expression",
                [
                    "memory",
                    32,
                    ["const", ["int", 1], 8],
                    ["read_order", None],
                ],
            ]
        ),
        _return_case_member_with_return_value(
            ["expression", ["call", "raw-prose-ish-callee", 4, []]]
        ),
        _return_case_member_with_return_value(
            [
                "expression",
                [
                    "call",
                    ["unknown_indirect_target", "raw-prose-ish-callee"],
                    4,
                    [],
                ],
            ]
        ),
        _return_case_member_with_return_value(
            [
                "expression",
                [
                    "call",
                    [
                        "unknown_indirect_target",
                        ["typed_target_expression", ["expression", ["parameter", "fp", ["int", 0], 8]]],
                        ["provenance", "raw-prose-ish-provenance"],
                    ],
                    4,
                    [],
                ],
            ]
        ),
        _return_case_member_with_return_value(
            ["expression", ["call", ["call_target", "raw-prose-ish-callee"], 4, []]]
        ),
        _return_case_member_with_return_value(
            [
                "expression",
                [
                    "call",
                    ["external_symbol", "raw-prose-ish-lib", "raw-prose-ish-name"],
                    4,
                    [],
                ],
            ]
        ),
        _return_case_member_with_return_value(
            ["expression", ["call", ["import_stub", "raw-prose-ish-import"], 4, []]]
        ),
        _return_case_member_with_return_value(
            ["expression", ["call", ["thunk", "raw-prose-ish-thunk"], 4, []]]
        ),
        _return_case_member_with_return_value(
            ["expression", ["raw-prose-ish-node", "raw-prose-ish-return-value"]]
        ),
        _return_case_member_with_value_evidence(["value", "raw-prose-ish-value-evidence"]),
        _return_case_member_with_value_evidence(
            ["value", ["expression", "raw-prose-ish-value-evidence"]]
        ),
        _return_case_member_with_value_evidence(
            ["value", ["expression", ["const", "raw-prose-ish-value-evidence", 4]]]
        ),
        _return_case_member_with_value_evidence(
            ["value", ["expression", ["raw-prose-ish-node", "raw-prose-ish-value-evidence"]]]
        ),
        _return_case_member_with_comparison_surface(["comparison_surface", "memory_effect", 32, None]),
        _return_case_member_with_guard_condition("raw-prose-ish-guard-condition"),
        _return_case_member_with_guard_condition(["condition", "raw-prose-ish-guard-condition"]),
        _return_case_member_with_guard_condition(
            ["condition", ["const", "raw-prose-ish-guard-condition", 1], True]
        ),
        _return_case_member_with_guard_condition(
            ["condition", ["raw-prose-ish-node", "raw-prose-ish-guard-condition"], True]
        ),
        _return_case_member_with_guard_expression("raw-prose-ish-guard-expression"),
        _return_case_member_with_guard_expression(["expression", "raw-prose-ish-guard-expression"]),
        _return_case_member_with_guard_expression(
            ["expression", ["const", "raw-prose-ish-guard-expression", 1]]
        ),
        _return_case_member_with_guard_expression(
            ["expression", ["raw-prose-ish-node", "raw-prose-ish-guard-expression"]]
        ),
    ],
)
def test_phase3_return_width_bridge_lane2_manifest_rejects_weak_return_case_member(
    tmp_path,
    return_case_member,
):
    reason = _width_reason(_target_with_return_case_member("case0", return_case_member))
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_post_fix_requires_manifest_sha256(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    failed = gate["post_fix_regression_gate"]["summary"]["failed_kinds"]
    assert "phase3_pre_fix_manifest_sha256_required" in failed
    with pytest.raises(ValueError, match="phase3_pre_fix_manifest_sha256_required"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_without_completed_proof(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    _write_log(current_root, _payload(reasons=[], actions=[], is_equivalent=True))

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert gate["entries"][0]["post_fix_failures"][0]["kind"] == "return_width_bridge_completed_proof_required"
    with pytest.raises(ValueError, match="return_width_bridge_post_fix_expected_movement"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_post_fix_accepts_eq_with_completed_proof(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=_completed_evidence(required_actions),
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is True
    assert gate["entries"][0]["post_fix_status"] == "completed_recovery"
    validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_metadata_only_completed_proof(
    tmp_path,
):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=_completed_evidence(
                required_actions,
                include_proof_content=False,
            ),
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert {
        failure["kind"] for failure in gate["entries"][0]["post_fix_failures"]
    } == {"return_width_bridge_completed_proof_required"}


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_missing_required_evidence(
    tmp_path,
):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    completed_evidence = _completed_evidence(required_actions)
    completed_evidence[0]["evidence"].pop("required_evidence")
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=completed_evidence,
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert any(
        failure["kind"] == "return_width_bridge_completed_proof_required"
        and failure["proof_stage"] == "abi_relation"
        for failure in gate["entries"][0]["post_fix_failures"]
    )


@pytest.mark.parametrize(
    "mutation",
    [
        "bogus_calling_convention_relation",
        "bogus_extension_relation",
        "bogus_high_bit_proof_label",
        "nested_high_bit_active_blocker",
    ],
)
def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_bogus_proof_content(
    tmp_path,
    mutation,
):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    completed_evidence = _completed_evidence(required_actions)
    if mutation == "bogus_calling_convention_relation":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "abi_relation_proof":
                evidence["proof_content"]["calling_convention"]["relation"] = (
                    "definitely_not_an_abi_proof"
                )
    elif mutation == "bogus_high_bit_proof_label":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "high_bit_proof":
                evidence["proof_content"]["high_bits_irrelevant_or_equal"]["proof"] = (
                    "bogus_proof_label"
                )
    elif mutation == "bogus_extension_relation":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "high_bit_proof":
                evidence["proof_content"]["extension_semantics"]["relation"] = (
                    "definitely_not_an_extension_proof"
                )
    elif mutation == "nested_high_bit_active_blocker":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "high_bit_proof":
                evidence["proof_content"]["high_bits_irrelevant_or_equal"][
                    "active_unsafety_reasons"
                ] = ["sat_unsafety"]
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=completed_evidence,
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert {
        failure["kind"] for failure in gate["entries"][0]["post_fix_failures"]
    } == {"return_width_bridge_completed_proof_required"}


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_planned_action_backlog(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=required_actions,
            is_equivalent=True,
            completed_evidence=_completed_evidence(required_actions),
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert any(
        failure["kind"] == "return_width_bridge_pending_proof_action_still_active"
        for failure in gate["entries"][0]["post_fix_failures"]
    )


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_unknown_action_status(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    stale_actions = json.loads(json.dumps(required_actions))
    stale_actions[0]["status"] = "unexpected_status"
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=stale_actions,
            is_equivalent=True,
            completed_evidence=_completed_evidence(required_actions),
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert any(
        failure["kind"] == "return_width_bridge_pending_proof_action_still_active"
        for failure in gate["entries"][0]["post_fix_failures"]
    )


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_partial_completed_proof(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = [
        action
        for action in pre_fix["entries"][0]["required_completion_actions"]
        if action["proof_stage"] != "high_bit_relation"
    ]
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=_completed_evidence(required_actions),
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    failures = gate["entries"][0]["post_fix_failures"]
    assert any(
        failure["kind"] == "return_width_bridge_completed_proof_required"
        and failure["proof_stage"] == "high_bit_relation"
        for failure in failures
    )
    with pytest.raises(ValueError, match="return_width_bridge_post_fix_expected_movement"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_post_fix_cli_requires_sha(capsys):
    with pytest.raises(SystemExit):
        phase3_return_width_bridge_lane2_main(
            [
                "--gate-stage",
                "post-fix",
                "--baseline-raw-dir",
                "raw",
                "--output-dir",
                "out",
                "--current-log-root",
                "function_call=current",
                "--baseline-log-root",
                "function_call=baseline",
            ]
        )
    captured = capsys.readouterr()
    assert "--phase3-manifest-sha256 is required" in captured.err
