# -*- coding: utf-8 -*-

import hashlib
import json
from pathlib import Path
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    FunctionReturnAnalysis,
    PcodeOpRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.validation.phase3_solver_rewrite_proof_lane8 import (
    ACTIVE_SOLVER_REWRITE_PROOF_EXPECTED_MOVEMENTS,
    REWRITE_RECHECK_ACTION_TUPLE,
    REWRITE_RECHECK_EVIDENCE_KIND,
    REWRITE_RECHECK_STAGE,
    SOLVER_PROOF_KIND,
    SOLVER_REASON_TUPLE,
    SOLVER_RETRY_ACTION_TUPLE,
    SOLVER_RETRY_EVIDENCE_KIND,
    SOLVER_RETRY_STAGE,
    build_phase3_solver_rewrite_proof_lane8_manifest,
    build_phase3_solver_rewrite_proof_lane8_post_fix_gate,
    validate_phase3_solver_rewrite_proof_lane8_manifest,
    validate_phase3_solver_rewrite_proof_lane8_post_fix_gate,
    _action_has_expected_id,
    _action_matches_lane_definition,
    _object_target_key_is_specific_solver_rewrite_proof,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


LEFT_BINARY_NAME = "function_call_test-arm64-gcc-O3"
RIGHT_BINARY_NAME = "function_call_test-mips64-clang-O1"


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


def _param(name: str, index: int = 0, size: int = 4):
    return {
        "name": name,
        "index": index,
        "size": size,
        "data_type": "int",
        "is_signed": True,
    }


def _pcode(binary_id: str, offset: int, mnemonic: str = "RETURN") -> PcodeOpRef:
    return PcodeOpRef(
        address_offset=offset,
        seq_time=offset,
        seq_order=1,
        block_index=0,
        mnemonic=mnemonic,
        input_sizes=(4,),
        output_size=4,
        binary_id=binary_id,
        function_entry_space="ram",
        function_entry_offset=offset - 0x20,
        target_space="ram",
        target_offset=offset,
        opcode=62,
        local_op_ordinal=0,
    )


def _case(binary_id: str, entry: int, index: int, value: Expression):
    x = Expression.parameter("x", 0, size=4)
    ret = ReturnInfo(
        address=hex(entry + 0x20),
        value=value,
        conditions=[
            Condition(
                Expression.binary_op("INT_EQUAL", x, Expression.constant(index, 4)),
                False,
            )
        ],
        pcode_identity=f"{binary_id}:return:{index}",
        pcode_order=index,
        pcode_time=entry + 0x20,
        pcode_op_ref=_pcode(binary_id, entry + 0x20),
    )
    analysis = FunctionReturnAnalysis(
        function_name="fc_recursive_sum",
        entry_point=hex(entry),
        parameters=[_param("x")],
        returns=[ret],
        return_type="int",
        binary_id=binary_id,
    )
    case = ReturnCase(
        index=index,
        conditions=ret.conditions,
        value_expr=ret.value,
        return_info=ret,
        return_type="int",
        parameters=analysis.parameters,
        source_indices=[index],
        comparison_surface=analysis.get_comparison_surface(),
    )
    return analysis, case


def _solver_rewrite_proof_target():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_original = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("x", 0, size=4),
        Expression.constant(1, 4),
    )
    left_rewritten = Expression.binary_op(
        "INT_ADD",
        Expression.constant(1, 4),
        Expression.parameter("x", 0, size=4),
    )
    right_value = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("x", 0, size=4),
        Expression.constant(1, 4),
    )
    left_analysis, left_case = _case("B8", 0x1000, 0, left_original)
    right_analysis, right_case = _case("B10", 0x2000, 1, right_value)
    return strategy._solver_rewrite_proof_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,1)",
        rewrite_side="left",
        original_expr=left_original,
        rewritten_expr=left_rewritten,
        rewrite_label="rewrite-proof-2",
    )


def _sat_unsafety_reason():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _case("B8", 0x1000, 1, Expression.constant(1, 4))
    right_analysis, right_case = _case("B10", 0x2000, 1, Expression.constant(0, 4))
    return strategy._make_sat_unsafety_unknown_reason(
        ("function1:incomplete_control_flow", "function2:return_coverage_gap"),
        left_analysis,
        right_analysis,
        case1=left_case,
        case2=right_case,
        pair_id="(1,1)",
        stage="S_PAIRWISE",
    )


def _proof_failed_reason(target=None):
    kwargs = {
        "stage": "S_PAIRWISE",
        "pair_or_case": "(0,1)",
        "evidence_refs": ("rewrite-proof-2", "solver-proven rewrite proof did not prove equivalence"),
        "detail": "solver-proven rewrite proof did not prove equivalence",
    }
    if target is not None:
        kwargs["object_target_key"] = target
    return make_unknown_reason("solver_proven_rewrite_proof_failed", **kwargs)


def _action_payload(action):
    return action if isinstance(action, dict) else action.to_dict()


def _payload(*, reasons, actions=None, is_equivalent=None):
    raw_reasons = [reason.to_dict() for reason in reasons]
    raw_actions = [
        _action_payload(action)
        for action in (actions if actions is not None else build_unknown_recovery_actions(reasons))
    ]
    return {
        "function1_name": "fc_recursive_sum",
        "function2_name": "fc_recursive_sum",
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
    }


def _write_log(root: Path, payload: dict) -> Path:
    path = root / "fc_recursive_sum" / "fc_recursive_sum_B8_B10.log"
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


def _active_solver_rewrite_representatives():
    return (
        {
            "id": "representative-solver-rewrite-proof-failed-recursive-sum-arm64-mips64",
            "category": "function_call",
            "function": "fc_recursive_sum",
            "binary_pair": "B8_B10",
            "expected_observed_binary1_name": LEFT_BINARY_NAME,
            "expected_observed_binary2_name": RIGHT_BINARY_NAME,
            "required_reason_ids": ["solver_proven_rewrite_proof_failed"],
            "role": "active solver rewrite proof backlog fixture",
            "expected_movements": [dict(movement) for movement in ACTIVE_SOLVER_REWRITE_PROOF_EXPECTED_MOVEMENTS],
        },
    )


def _setup_logs(tmp_path: Path, *, current_payload: dict):
    raw_dir = tmp_path / "raw"
    _write_artifact_manifest(raw_dir)
    baseline_root = raw_dir / "logs" / "function_call"
    current_root = tmp_path / "current"
    _write_log(baseline_root, _payload(reasons=[_proof_failed_reason()]))
    _write_log(current_root, current_payload)
    return raw_dir, baseline_root, current_root


def test_solver_rewrite_proof_target_is_object_specific():
    target = _solver_rewrite_proof_target()

    assert target[0] == "solver_rewrite_proof"
    assert _object_target_key_is_specific_solver_rewrite_proof(target)


def test_solver_rewrite_proof_target_rejects_log_prose_expression():
    target = list(_solver_rewrite_proof_target())
    target[6] = ("original_expression", ("reason", "solver rewrite proof prose"))

    assert not _object_target_key_is_specific_solver_rewrite_proof(tuple(target))


def test_solver_rewrite_proof_action_requires_full_tuple_and_proof_id():
    target = _solver_rewrite_proof_target()
    rewrite_action = {
        "tuple": list(REWRITE_RECHECK_ACTION_TUPLE),
        "reason_id": "solver_proven_rewrite_proof_failed",
        "stage": "S_PAIRWISE",
        "pair_or_case": "(0,1)",
        "proof_kind": SOLVER_PROOF_KIND,
        "proof_stage": REWRITE_RECHECK_STAGE,
        "status": "planned",
        "required_evidence": [
            "rewrite_before_expr",
            "rewrite_after_expr",
            "proof_counterexample_or_solver_trace",
        ],
        "evidence_kind": REWRITE_RECHECK_EVIDENCE_KIND,
        "object_target_key": target,
        "proof_obligation_id": build_proof_obligation_id(
            "solver_proven_rewrite_proof_failed",
            REWRITE_RECHECK_STAGE,
            SOLVER_PROOF_KIND,
            REWRITE_RECHECK_EVIDENCE_KIND,
            target,
        ),
    }
    solver_action = {
        **rewrite_action,
        "tuple": list(SOLVER_RETRY_ACTION_TUPLE),
        "proof_stage": SOLVER_RETRY_STAGE,
        "required_evidence": ["normalized_query", "solver_options", "query_hash"],
        "evidence_kind": SOLVER_RETRY_EVIDENCE_KIND,
        "proof_obligation_id": build_proof_obligation_id(
            "solver_proven_rewrite_proof_failed",
            SOLVER_RETRY_STAGE,
            SOLVER_PROOF_KIND,
            SOLVER_RETRY_EVIDENCE_KIND,
            target,
        ),
    }

    assert _action_matches_lane_definition(rewrite_action)
    assert _action_has_expected_id(rewrite_action)
    assert _action_matches_lane_definition(solver_action)
    assert _action_has_expected_id(solver_action)

    wrong_id = dict(solver_action)
    wrong_id["proof_obligation_id"] = ("not", "the", "full", "key")
    assert not _action_has_expected_id(wrong_id)


def test_solver_rewrite_proof_reason_tuple_stays_count_compatible():
    assert SOLVER_REASON_TUPLE == (
        "reason_record",
        "solver_proven_rewrite_proof_failed",
        "retryable",
        "pair",
        "solver_retry_or_normalization",
        "<missing>",
        "<missing>",
    )
    assert REWRITE_RECHECK_ACTION_TUPLE == (
        "proof_action",
        "solver_proven_rewrite_proof_failed",
        "retryable",
        "pair",
        "solver_retry_or_normalization",
        "rewrite_proof_recheck",
        "planned",
    )
    assert SOLVER_RETRY_ACTION_TUPLE == (
        "proof_action",
        "solver_proven_rewrite_proof_failed",
        "retryable",
        "pair",
        "solver_retry_or_normalization",
        "solver_retry",
        "planned",
    )


def test_phase3_solver_rewrite_proof_lane8_active_manifest_ready(tmp_path):
    reason = _proof_failed_reason(_solver_rewrite_proof_target())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_solver_rewrite_proof_lane8_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        representatives=_active_solver_rewrite_representatives(),
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane8_ready"] is True
    validate_phase3_solver_rewrite_proof_lane8_manifest(manifest)

    entry = manifest["entries"][0]
    assert len(entry["target_object_keys"]) == 1
    assert entry["target_object_keys"][0][1] == ["pair", "(0,1)"]
    assert len(entry["required_completion_actions"]) == 2
    assert all(action["proof_obligation_id"] for action in entry["required_completion_actions"])


def test_phase3_solver_rewrite_proof_lane8_default_accepts_sat_unsafety_reclassification(tmp_path):
    sat_reason = _sat_unsafety_reason()
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(
            reasons=[
                sat_reason,
                make_unknown_reason(
                    "unresolved_expression",
                    stage="S_PAIRWISE",
                    pair_or_case="(1,2)",
                ),
            ]
        ),
    )

    pre_fix_path = build_phase3_solver_rewrite_proof_lane8_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane8_ready"] is True
    entry = manifest["entries"][0]
    assert entry["target_object_keys"] == []
    assert entry["required_completion_actions"] == []
    assert len(entry["accepted_current_reclassification_targets"]) == 1
    assert len(entry["accepted_current_reclassification_actions"]) == 1
    validate_phase3_solver_rewrite_proof_lane8_manifest(manifest)

    post_fix_path = build_phase3_solver_rewrite_proof_lane8_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane8_post_fix_ready"] is True
    assert gate["entries"][0]["post_fix_status"] == "retired_to_sat_unsafety"
    validate_phase3_solver_rewrite_proof_lane8_post_fix_gate(gate)


def test_phase3_solver_rewrite_proof_lane8_default_rejects_sat_reclassification_without_target(tmp_path):
    sat_reason = make_unknown_reason(
        "sat_unsafety",
        decision_effect="blocks_disequivalence",
        reason_scope="pair",
        recovery_proof_kind="sat_unsafety_resolution",
        proof_stage="sat_counterexample_safety",
        action_status="pending_proof",
        stage="S_PAIRWISE",
        pair_or_case="(1,1)",
    )
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[sat_reason]),
    )

    pre_fix_path = build_phase3_solver_rewrite_proof_lane8_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane8_ready"] is False
    assert "solver_rewrite_proof_accepted_reclassification_targets_present" in manifest["readiness"]["failed_kinds"]


def test_phase3_solver_rewrite_proof_lane8_manifest_rejects_missing_raw_proof_id(tmp_path):
    reason = _proof_failed_reason(_solver_rewrite_proof_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    actions[0]["proof_obligation_id"] = None
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )

    pre_fix_path = build_phase3_solver_rewrite_proof_lane8_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        representatives=_active_solver_rewrite_representatives(),
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane8_ready"] is False
    assert "solver_rewrite_proof_current_actions_complete" in manifest["readiness"]["failed_kinds"]


def test_phase3_solver_rewrite_proof_lane8_manifest_rejects_missing_current_target(tmp_path):
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[_proof_failed_reason()]),
    )

    pre_fix_path = build_phase3_solver_rewrite_proof_lane8_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        representatives=_active_solver_rewrite_representatives(),
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane8_ready"] is False
    assert "solver_rewrite_proof_current_targets_present" in manifest["readiness"]["failed_kinds"]
    with pytest.raises(ValueError, match="solver_rewrite_proof_current_targets_present"):
        validate_phase3_solver_rewrite_proof_lane8_manifest(manifest)
