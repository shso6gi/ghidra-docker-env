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
from scripts.function_tracer_pcode.validation.phase3_readonly_identity_lane3 import (
    build_phase3_readonly_identity_lane3_manifest,
    build_phase3_readonly_identity_lane3_post_fix_gate,
    main as phase3_readonly_identity_lane3_main,
    validate_phase3_readonly_identity_lane3_manifest,
    validate_phase3_readonly_identity_lane3_post_fix_gate,
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


def _readonly_ref(binary_id: str, count_index: int):
    return [
        "readonly_reduction_ref",
        "memory_sum",
        [
            "semantic_key",
            [
                "readonly_sum",
                ["binary", binary_id],
                ["base", ["parameter", 0]],
                ["count", ["parameter", count_index]],
            ],
        ],
        ["pointer_base_identity", ["parameter", 0]],
        [
            "count_identities",
            [
                ["parameter", count_index],
                ["storage", ["register", f"a{count_index}", 8]],
            ],
        ],
        [
            "term_contract",
            [
                "affine_readonly_sum",
                ["stride", 4],
                ["element_size", 4],
                ["result_size", 4],
            ],
        ],
        ["result_size", 4],
        ["stride", 4],
        ["element_size", 4],
        ["start_offset", 0],
        ["constant_bias", 0],
    ]


def _return_case(binary_id: str, address: str, count_index: int):
    ref = _readonly_ref(binary_id, count_index)
    return [
        "readonly_return_case_partition_member",
        0,
        [0],
        [
            "return_case",
            0,
            address,
            [
                "pcode_op",
                binary_id,
                ["function_entry", "ram", 1052592 if binary_id == "B10" else 4831846228],
                ["seq_target", "ram", 1052644 if binary_id == "B10" else 4831846344],
                40,
                1,
                "RETURN",
                0,
            ],
            f"{address}:return",
            1,
        ],
        ["comparison_surface", "return_value", 32, None],
        ["value", ["readonly_value", ref]],
        [
            "guards",
            [
                [
                    "return_guard",
                    True,
                    ["condition", ["parameter", "n", ["int", count_index], 8]],
                    ["expression", ["parameter", "n", ["int", count_index], 8]],
                ]
            ],
        ],
    ]


def _side(side: str, binary_id: str, address: str, count_index: int):
    ref = _readonly_ref(binary_id, count_index)
    return [
        "readonly_identity_side",
        side,
        ["function_ref", ["function", binary_id, 1052592 if binary_id == "B10" else 4831846228]],
        _return_case(binary_id, address, count_index),
        ref,
        [
            "guards",
            [
                [
                    "return_guard",
                    True,
                    ["condition", ["parameter", "n", ["int", count_index], 8]],
                    ["expression", ["parameter", "n", ["int", count_index], 8]],
                ]
            ],
        ],
        ["value", ["readonly_value", ref]],
    ]


def _target_without_relation():
    return [
        "readonly_identity",
        ["pair", "(0,0)"],
        _side("left", "B10", "00100fe4", 1),
        _side("right", "B13", "120001fc8", 2),
    ]


def _target():
    target = _target_without_relation()
    target.append(
        [
            "readonly_identity_relation",
            ["shared_count_identities", [["parameter", 1]]],
            [
                "count_storage_relation",
                [
                    "same_register_base_projection",
                    ["base", [-1, 12756, 64]],
                    ["left_bits", 0, 64],
                    ["right_bits", 32, 32],
                    ["projection", "left_contains_right"],
                ],
            ],
        ]
    )
    return target


def _readonly_reason(target=None):
    kwargs = {
        "evidence_kind": "object_storage_identity",
        "evidence_refs": ("object_storage_identity",),
        "stage": "S_PAIRWISE",
        "pair_or_case": "(0,0)",
    }
    if target is not None:
        kwargs["object_target_key"] = target
    return make_unknown_reason(UnknownReasonId.READONLY_IDENTITY_MISSING, **kwargs)


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
    _write_log(baseline_root, _payload(reasons=[_readonly_reason()]))
    _write_log(current_root, current_payload)
    return raw_dir, baseline_root, current_root


def _completed_evidence(actions, *, include_proof_content=True, proof_content_overrides=None):
    records = []
    for action in actions:
        storage_relation = action["object_target_key"][4][2][1]
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
                "left_side": action["object_target_key"][2],
                "right_side": action["object_target_key"][3],
                "object_storage_identity": "matched",
                "count_identity": "matched",
                "guard_implication": "proven",
                "finite_witness": "checked",
                "storage_relation": storage_relation,
                "parameter_extension": {
                    "object_derived": True,
                    "status": "proven",
                    "relation": "same_register_base_projection_semantic_extension",
                    "projection_relation": storage_relation,
                    "wide_side": "left",
                    "narrow_side": "right",
                    "parameter_index": 1,
                    "signedness": "signed",
                    "narrow_bits": 32,
                    "wide_bits": 64,
                    "extension": "sign_extend",
                    "proof_source": "param_semantic_hint",
                },
            }
            proof_content.update(proof_content_overrides or {})
            evidence["proof_content"] = proof_content
        records.append({"evidence": evidence})
    return records


def test_phase3_readonly_identity_lane3_manifest_and_post_fix_gate_ready(tmp_path):
    current_payload = _payload(reasons=[_readonly_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane3_ready"] is True
    validate_phase3_readonly_identity_lane3_manifest(manifest)
    tampered_manifest = json.loads(json.dumps(manifest))
    tampered_manifest["readiness"]["failure_kinds"] = ["hidden_lane3_failure"]
    with pytest.raises(ValueError, match="hidden_lane3_failure"):
        validate_phase3_readonly_identity_lane3_manifest(tampered_manifest)

    entry = manifest["entries"][0]
    assert len(entry["target_object_keys"]) == 1
    assert {action["proof_stage"] for action in entry["required_completion_actions"]} == {
        "readonly_operand_identity",
    }
    assert entry["required_completion_actions"][0]["tuple"] == [
        "proof_action",
        "readonly_identity_missing",
        "blocks_equivalence",
        "expression",
        "storage_backed_identity_propagation",
        "readonly_operand_identity",
        "planned",
    ]
    assert entry["required_completion_actions"][0]["decision_effect"] == "blocks_equivalence"
    assert entry["required_completion_actions"][0]["reason_scope"] == "expression"
    assert entry["required_completion_actions"][0]["aggregation_unit"] == "pair"
    assert entry["required_completion_actions"][0]["stage"] == "S_PAIRWISE"
    assert all(action["proof_obligation_id"] for action in entry["required_completion_actions"])

    post_fix_path = build_phase3_readonly_identity_lane3_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane3_post_fix_ready"] is True
    assert gate["entries"][0]["post_fix_status"] == "pending_proof"
    assert gate["entries"][0]["pending_proof_obligations"] == [
        {
            "reason_id": "readonly_identity_missing",
            "proof_kind": "storage_backed_identity_propagation",
            "proof_stage": "readonly_operand_identity",
            "evidence_kind": "object_storage_identity",
            "required_evidence": [
                "object_storage_identity",
                "count_identity",
                "guard_implication",
                "finite_witness",
            ],
            "proof_obligation_id": entry["required_completion_actions"][0]["proof_obligation_id"],
            "completed_evidence_present": False,
            "status": "pending_evidence",
        }
    ]
    validate_phase3_readonly_identity_lane3_post_fix_gate(gate)
    tampered_gate = json.loads(json.dumps(gate))
    tampered_gate["post_fix_regression_gate"]["summary"]["failed_kinds"] = ["hidden_lane3_post_fix_failure"]
    with pytest.raises(ValueError, match="hidden_lane3_post_fix_failure"):
        validate_phase3_readonly_identity_lane3_post_fix_gate(tampered_gate)
    tampered_pre_fix = json.loads(pre_fix_path.read_text())
    tampered_pre_fix["readiness"]["failure_kinds"] = ["hidden_lane3_pre_fix_manifest_failure"]
    tampered_pre_fix_path = pre_fix_path.with_name(
        "tampered_readonly_identity_lane3_representatives.json"
    )
    tampered_pre_fix_path.write_text(json.dumps(tampered_pre_fix))
    tampered_pre_fix_gate_path = build_phase3_readonly_identity_lane3_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate-tampered-pre-fix",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=tampered_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(tampered_pre_fix_path),
    )
    tampered_pre_fix_gate = json.loads(tampered_pre_fix_gate_path.read_text())
    assert tampered_pre_fix_gate["phase3_lane3_post_fix_ready"] is False
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
    assert "hidden_lane3_pre_fix_manifest_failure" in ready_check["error"]
    with pytest.raises(ValueError, match="phase3_pre_fix_manifest_ready"):
        validate_phase3_readonly_identity_lane3_post_fix_gate(tampered_pre_fix_gate)


def test_phase3_readonly_identity_lane3_accepts_storage_projection_relation(tmp_path):
    current_payload = _payload(reasons=[_readonly_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    validate_phase3_readonly_identity_lane3_manifest(manifest)
    relation = manifest["entries"][0]["target_object_keys"][0][4]

    assert relation[0] == "readonly_identity_relation"
    assert relation[1] == ["shared_count_identities", [["parameter", 1]]]
    assert relation[2][1][0] == "same_register_base_projection"


def test_phase3_readonly_identity_lane3_rejects_relationless_target(tmp_path):
    current_payload = _payload(reasons=[_readonly_reason(_target_without_relation())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())

    with pytest.raises(ValueError, match="readonly_identity_current_targets_present"):
        validate_phase3_readonly_identity_lane3_manifest(manifest)


def test_phase3_readonly_identity_lane3_manifest_rejects_diagnostic_reason_in_target(tmp_path):
    target = _target()
    target.append(["reason", "readonly_contract_mismatch"])
    current_payload = _payload(reasons=[_readonly_reason(target)])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane3_ready"] is False
    with pytest.raises(ValueError, match="readonly_identity_current_targets_present"):
        validate_phase3_readonly_identity_lane3_manifest(manifest)


def test_phase3_readonly_identity_lane3_manifest_rejects_malformed_proof_id(tmp_path):
    reason = _readonly_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    actions[0]["proof_obligation_id"] = ["wrong", "proof"]
    current_payload = _payload(reasons=[reason], actions=actions)
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane3_ready"] is False
    with pytest.raises(ValueError, match="readonly_identity_current_actions_complete"):
        validate_phase3_readonly_identity_lane3_manifest(manifest)


def test_phase3_readonly_identity_lane3_manifest_rejects_malformed_action_tuple(tmp_path):
    reason = _readonly_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    actions[0]["decision_effect"] = "retryable"
    actions[0]["reason_scope"] = "pair"
    actions[0]["aggregation_unit"] = "function"
    actions[0]["stage"] = "S_WRONG"
    current_payload = _payload(reasons=[reason], actions=actions)
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane3_ready"] is False
    assert manifest["entries"][0]["required_completion_actions"] == []
    with pytest.raises(ValueError, match="readonly_identity_current_actions_complete"):
        validate_phase3_readonly_identity_lane3_manifest(manifest)


def test_phase3_readonly_identity_lane3_manifest_rejects_raw_semantic_key_payload(tmp_path):
    target = _target()
    target[2][4][2] = ["semantic_key", "raw-prose-ish-semantic-key"]
    current_payload = _payload(reasons=[_readonly_reason(target)])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane3_ready"] is False
    with pytest.raises(ValueError, match="readonly_identity_current_targets_present"):
        validate_phase3_readonly_identity_lane3_manifest(manifest)


@pytest.mark.parametrize(
    ("path", "bad_value"),
    [
        ((2, 4, 2), ["semantic_key", ["raw-prose-ish-semantic-key"]]),
        ((2, 4, 3), ["pointer_base_identity", ["raw-prose-ish-pointer-base"]]),
        ((2, 4, 5), ["term_contract", ["raw-prose-ish-term-contract"]]),
    ],
)
def test_phase3_readonly_identity_lane3_manifest_rejects_text_only_readonly_payloads(
    tmp_path,
    path,
    bad_value,
):
    target = _target()
    cursor = target
    for index in path[:-1]:
        cursor = cursor[index]
    cursor[path[-1]] = bad_value
    current_payload = _payload(reasons=[_readonly_reason(target)])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane3_ready"] is False
    with pytest.raises(ValueError, match="readonly_identity_current_targets_present"):
        validate_phase3_readonly_identity_lane3_manifest(manifest)


@pytest.mark.parametrize(
    "bad_witnesses",
    [
        [["raw-prose-ish-witness"]],
        [["readonly_reduction_witness", "count_parameter", 2, [["raw-prose-ish-term"]]]],
        [["readonly_reduction_witness", "count_parameter", 2, [["readonly_reduction_term", 0, 0]]]],
    ],
)
def test_phase3_readonly_identity_lane3_manifest_rejects_malformed_semantic_witnesses(
    tmp_path,
    bad_witnesses,
):
    target = _target()
    target[2][4].append(["semantic_witnesses", bad_witnesses])
    current_payload = _payload(reasons=[_readonly_reason(target)])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane3_ready"] is False
    with pytest.raises(ValueError, match="readonly_identity_current_targets_present"):
        validate_phase3_readonly_identity_lane3_manifest(manifest)


def test_phase3_readonly_identity_lane3_manifest_rejects_nested_diagnostic_reason(tmp_path):
    target = _target()
    target[2][4][2] = ["semantic_key", ["reason", "readonly_contract_mismatch"]]
    current_payload = _payload(reasons=[_readonly_reason(target)])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane3_ready"] is False
    with pytest.raises(ValueError, match="readonly_identity_current_targets_present"):
        validate_phase3_readonly_identity_lane3_manifest(manifest)


@pytest.mark.parametrize("opcode", ["", "<missing>"])
def test_phase3_readonly_identity_lane3_manifest_rejects_missing_pcode_opcode(tmp_path, opcode):
    target = _target()
    target[2][3][3][3][6] = opcode
    current_payload = _payload(reasons=[_readonly_reason(target)])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane3_ready"] is False
    with pytest.raises(ValueError, match="readonly_identity_current_targets_present"):
        validate_phase3_readonly_identity_lane3_manifest(manifest)


def test_phase3_readonly_identity_lane3_manifest_rejects_weak_return_case_pcode_ref(tmp_path):
    target = _target()
    target[2][3][3][3] = ["raw-prose-ish-pcode-ref"]
    current_payload = _payload(reasons=[_readonly_reason(target)])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane3_ready"] is False
    with pytest.raises(ValueError, match="readonly_identity_current_targets_present"):
        validate_phase3_readonly_identity_lane3_manifest(manifest)


def test_phase3_readonly_identity_lane3_post_fix_requires_manifest_sha256(tmp_path):
    current_payload = _payload(reasons=[_readonly_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )

    post_fix_path = build_phase3_readonly_identity_lane3_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane3_post_fix_ready"] is False
    with pytest.raises(ValueError, match="phase3_pre_fix_manifest_sha256_required"):
        validate_phase3_readonly_identity_lane3_post_fix_gate(gate)


def test_phase3_readonly_identity_lane3_post_fix_rejects_eq_without_completed_proof(tmp_path):
    reason = _readonly_reason(_target())
    unknown_payload = _payload(reasons=[reason])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=unknown_payload)
    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    _write_log(current_root, _payload(reasons=[], actions=[], is_equivalent=True))

    post_fix_path = build_phase3_readonly_identity_lane3_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane3_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    with pytest.raises(ValueError, match="readonly_identity_post_fix_expected_movement"):
        validate_phase3_readonly_identity_lane3_post_fix_gate(gate)


def test_phase3_readonly_identity_lane3_post_fix_accepts_eq_with_completed_proof(tmp_path):
    reason = _readonly_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    unknown_payload = _payload(reasons=[reason], actions=actions)
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=unknown_payload)
    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
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

    post_fix_path = build_phase3_readonly_identity_lane3_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane3_post_fix_ready"] is True
    assert gate["entries"][0]["post_fix_status"] == "completed_recovery"
    validate_phase3_readonly_identity_lane3_post_fix_gate(gate)


def test_phase3_readonly_identity_lane3_post_fix_rejects_eq_with_active_sat_unsafety(tmp_path):
    reason = _readonly_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    unknown_payload = _payload(reasons=[reason], actions=actions)
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=unknown_payload)
    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
    )
    _write_log(
        current_root,
        _payload(
            reasons=[make_unknown_reason(UnknownReasonId.SAT_UNSAFETY)],
            actions=[],
            is_equivalent=True,
            completed_evidence=_completed_evidence(actions),
        ),
    )

    post_fix_path = build_phase3_readonly_identity_lane3_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane3_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    failures = gate["entries"][0]["post_fix_failures"]
    assert any(
        failure["kind"] == "readonly_identity_active_reason_not_cleared"
        and failure["active_reason_ids"] == ["sat_unsafety"]
        for failure in failures
    )
    with pytest.raises(ValueError, match="readonly_identity_post_fix_expected_movement"):
        validate_phase3_readonly_identity_lane3_post_fix_gate(gate)


def test_phase3_readonly_identity_lane3_post_fix_rejects_metadata_only_completed_proof(tmp_path):
    reason = _readonly_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    unknown_payload = _payload(reasons=[reason], actions=actions)
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=unknown_payload)
    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
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

    post_fix_path = build_phase3_readonly_identity_lane3_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane3_post_fix_ready"] is False
    with pytest.raises(ValueError, match="readonly_identity_post_fix_expected_movement"):
        validate_phase3_readonly_identity_lane3_post_fix_gate(gate)


def test_phase3_readonly_identity_lane3_post_fix_rejects_projection_without_extension_proof(tmp_path):
    reason = _readonly_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    unknown_payload = _payload(reasons=[reason], actions=actions)
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=unknown_payload)
    pre_fix_path = build_phase3_readonly_identity_lane3_manifest(
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
            completed_evidence=_completed_evidence(
                actions,
                proof_content_overrides={"parameter_extension": None},
            ),
        ),
    )

    post_fix_path = build_phase3_readonly_identity_lane3_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"loop": current_root},
        baseline_log_roots={"loop": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane3_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    with pytest.raises(ValueError, match="readonly_identity_post_fix_expected_movement"):
        validate_phase3_readonly_identity_lane3_post_fix_gate(gate)


def test_phase3_readonly_identity_lane3_post_fix_cli_requires_sha(capsys):
    with pytest.raises(SystemExit):
        phase3_readonly_identity_lane3_main(
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
