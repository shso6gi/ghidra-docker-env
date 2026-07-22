# -*- coding: utf-8 -*-

from pathlib import Path
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownReasonId,
    UnknownRecoveryProofKind,
    build_unknown_recovery_actions,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.model import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    DeferredCallRef,
    Expression,
    FunctionReturnAnalysis,
    UnknownValueRef,
    PcodeOpRef,
    ReturnInfo,
    expression_provenance_key,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import _global_reason_tuple_from_action
from scripts.function_tracer_pcode.validation.phase3_sat_unsafety_lane5 import (
    SAT_ACTION_TUPLE,
    SAT_EVIDENCE_KIND,
    SAT_PROOF_KIND,
    SAT_PROOF_STAGE,
    SAT_REQUIRED_EVIDENCE,
    _observation,
    _object_target_key_is_specific_sat_unsafety,
    _pending_proof_obligations,
    _post_fix_checks,
    _post_fix_status,
    _proof_action_has_expected_id,
    _proof_action_matches_lane_definition,
    validate_phase3_sat_unsafety_lane5_manifest,
    validate_phase3_sat_unsafety_lane5_post_fix_gate,
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
        input_sizes=(8, 4),
        output_size=4,
        binary_id=binary_id,
        function_entry_space="ram",
        function_entry_offset=offset - 0x20,
        target_space="ram",
        target_offset=offset,
        opcode=62,
        local_op_ordinal=0,
    )


def _case(binary_id: str, entry: int, index: int) -> tuple[FunctionReturnAnalysis, ReturnCase]:
    x = Expression.parameter("x", 0, size=4)
    ret = ReturnInfo(
        address=hex(entry + 0x20),
        value=Expression.constant(index, 4),
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
        function_name="fc_is_even",
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


def _sat_reason():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1, case1 = _case("B10", 0x1000, 0)
    analysis2, case2 = _case("B9", 0x2000, 1)
    return strategy._make_sat_unsafety_unknown_reason(
        ("function1:incomplete_control_flow", "function2:return_coverage_gap"),
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id="(0,1)",
        stage="S_PAIRWISE",
    )


def _completed_sat_replay_evidence(action, **counterexample_overrides):
    object_target_key = action["object_target_key"]
    replay = {
        "status": "replayed",
        "replay_source": "counterexample_model_replay",
        "fixed_model_assertion_count": 2,
        "counterexample_symbol_keys": (("sym", "x"),),
        "counterexample_model_sha256": "0" * 64,
    }
    replay.update(counterexample_overrides)
    return {
        "object_derived": True,
        "status": "complete",
        "reason_id": action["reason_id"],
        "proof_kind": SAT_PROOF_KIND,
        "proof_stage": SAT_PROOF_STAGE,
        "evidence_kind": SAT_EVIDENCE_KIND,
        "object_target_key": object_target_key,
        "proof_obligation_id": action["proof_obligation_id"],
        "proof_content": {
            "object_derived": True,
            "object_target_key": object_target_key,
            "counterexample_replay": replay,
            "active_unsafety_discharge": {
                "status": "discharged",
                "discharged_unsafety_count": 1,
            },
            "coverage_effect_safety": {
                "status": "complete",
                "coverage_gap_count": 0,
                "unsupported_effect_count": 0,
            },
        },
    }


def _analysis_with_deferred_call_program_id(program_id: int) -> tuple[FunctionReturnAnalysis, ReturnCase]:
    binary_id = "B10"
    entry = 0x1000
    pcode_ref = _pcode(binary_id, entry + 0x20, "CALLIND")
    target_ref = CallTargetRef.from_name("callee", program_id=program_id, entry_offset=0x1200)
    deferred_ref = DeferredCallRef(
        caller_program_id=program_id,
        caller_entry_offset=entry,
        pcode_op_ref=pcode_ref,
        target_ref=target_ref,
        sequence=3,
    )
    deferred = DeferredCallInfo(
        placeholder_name="indirect",
        target_ref=target_ref,
        arguments=[Expression.parameter("arg0", 0, size=4)],
        call_target_expr=Expression.parameter("fp", 1, size=8),
        deferred_call_ref=deferred_ref,
        call_argument_recovery_status="inconclusive",
    )
    return_value = Expression.constant(0, 4)
    ret = ReturnInfo(
        address=hex(entry + 0x30),
        value=return_value,
        conditions=[Condition(Expression.parameter("x", 0, size=4), False)],
        pcode_identity=f"{binary_id}:return:0",
        pcode_order=0,
        pcode_time=entry + 0x30,
        pcode_op_ref=_pcode(binary_id, entry + 0x30),
    )
    analysis = FunctionReturnAnalysis(
        function_name="fc_is_even",
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name("fc_is_even", program_id=program_id, entry_offset=entry),
        parameters=[_param("x")],
        returns=[ret],
        return_type="int",
        binary_id=binary_id,
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    case = ReturnCase(
        index=0,
        conditions=ret.conditions,
        value_expr=ret.value,
        return_info=ret,
        return_type="int",
        parameters=analysis.parameters,
        source_indices=[0],
        comparison_surface=analysis.get_comparison_surface(),
    )
    return analysis, case


def _nested_contains(value, needle) -> bool:
    if value == needle:
        return True
    if isinstance(value, (tuple, list)):
        return any(_nested_contains(item, needle) for item in value)
    if isinstance(value, dict):
        return any(_nested_contains(key, needle) or _nested_contains(item, needle) for key, item in value.items())
    return False


def test_sat_unsafety_target_is_specific_and_action_uses_full_proof_id():
    reason = _sat_reason()
    action = build_unknown_recovery_actions([reason])[0]

    assert reason.object_target_key[0] == "counterexample_safety_gate"
    assert _object_target_key_is_specific_sat_unsafety(reason.object_target_key)
    assert action.proof_kind == SAT_PROOF_KIND
    assert action.proof_stage == SAT_PROOF_STAGE
    assert action.evidence_kind == SAT_EVIDENCE_KIND
    assert action.required_evidence == SAT_REQUIRED_EVIDENCE
    assert action.proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert _global_reason_tuple_from_action(action) == (
        SAT_ACTION_TUPLE[0],
        "counterexample_analysis_safety_unproven",
        SAT_ACTION_TUPLE[2],
        "query",
        *SAT_ACTION_TUPLE[4:],
    )
    action_dict = action.to_dict()
    assert _proof_action_matches_lane_definition(action_dict)
    assert _proof_action_has_expected_id(action_dict)


def test_sat_unsafety_manifest_validator_rejects_ready_without_readiness():
    manifest = {
        "manifest_kind": "phase3_sat_unsafety_lane5_representatives",
        "phase3_lane5_ready": True,
    }

    with pytest.raises(ValueError, match="sat_unsafety_readiness_missing"):
        validate_phase3_sat_unsafety_lane5_manifest(manifest)


def test_sat_unsafety_manifest_validator_rejects_hidden_failed_kind():
    manifest = {
        "manifest_kind": "phase3_sat_unsafety_lane5_representatives",
        "phase3_lane5_ready": True,
        "readiness": {
            "ready": True,
            "failed_checks": [],
            "failed_kinds": ["hidden_sat_unsafety_failure"],
            "checks": [],
        },
    }

    with pytest.raises(ValueError, match="hidden_sat_unsafety_failure"):
        validate_phase3_sat_unsafety_lane5_manifest(manifest)


def test_sat_unsafety_post_fix_gate_validator_rejects_ready_without_checks():
    manifest = {
        "manifest_kind": "phase3_sat_unsafety_lane5_post_fix_gate",
        "phase3_lane5_post_fix_ready": True,
    }

    with pytest.raises(ValueError, match="sat_unsafety_post_fix_checks_missing"):
        validate_phase3_sat_unsafety_lane5_post_fix_gate(manifest)


def test_sat_unsafety_post_fix_checks_reject_tampered_pre_fix_manifest_ready():
    manifest = {
        "manifest_kind": "phase3_sat_unsafety_lane5_representatives",
        "phase3_lane5_ready": True,
        "readiness": {
            "ready": True,
            "failed_checks": [],
            "failed_kinds": ["hidden_sat_unsafety_pre_fix_failure"],
            "checks": [],
        },
        "entries": [],
    }

    checks = _post_fix_checks(
        baseline_manifest={"baseline_id": "observed-v0@0a53352"},
        phase3_manifest=manifest,
        phase3_manifest_path=Path("sat_unsafety_lane5_representatives.json"),
        actual_phase3_sha256="a" * 64,
        expected_phase3_sha256="a" * 64,
        entries=(),
    )

    ready_check = next(check for check in checks if check["kind"] == "phase3_pre_fix_manifest_ready")
    assert ready_check["status"] == "failed"
    assert "hidden_sat_unsafety_pre_fix_failure" in ready_check["error"]


def test_sat_unsafety_target_normalizes_ghidra_program_ids_out_of_deferred_calls():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_a, case_a = _analysis_with_deferred_call_program_id(3732166838612569888)
    left_b, case_b = _analysis_with_deferred_call_program_id(3732174609056778976)
    right, right_case = _case("B9", 0x2000, 1)

    reason_a = strategy._make_sat_unsafety_unknown_reason(
        ("function1:effect_call_argument_evidence_incomplete",),
        left_a,
        right,
        case1=case_a,
        case2=right_case,
        pair_id="(0,1)",
        stage="S_PAIRWISE",
    )
    reason_b = strategy._make_sat_unsafety_unknown_reason(
        ("function1:effect_call_argument_evidence_incomplete",),
        left_b,
        right,
        case1=case_b,
        case2=right_case,
        pair_id="(0,1)",
        stage="S_PAIRWISE",
    )

    assert reason_a.object_target_key == reason_b.object_target_key
    assert reason_a.proof_obligation_id == reason_b.proof_obligation_id
    assert not _nested_contains(reason_a.object_target_key, 3732166838612569888)
    assert not _nested_contains(reason_a.object_target_key, 3732174609056778976)
    assert _object_target_key_is_specific_sat_unsafety(reason_a.object_target_key)


def test_sat_unsafety_artifact_key_rewrites_atom_encoded_runtime_ref_program_ids():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    program_id = 3732174609056778976
    analysis, _case = _analysis_with_deferred_call_program_id(program_id)
    deferred = next(iter(analysis.deferred_calls.values()))
    runtime_expr = Expression.unknown(
        "indirect",
        runtime_ref=UnknownValueRef.deferred_call(
            deferred_call_ref=deferred.deferred_call_ref,
            target_ref=deferred.target_ref,
            placeholder_name="indirect",
        ),
    )

    normalized = strategy._artifact_stable_key_for_analysis(
        ("typed_target_expression", expression_provenance_key(runtime_expr)),
        analysis,
    )

    assert not _nested_contains(normalized, program_id)
    assert _nested_contains(normalized, "B10")


def test_sat_unsafety_target_rejects_nested_diagnostic_reason():
    reason = _sat_reason()
    target = list(reason.object_target_key)
    active = list(target[4])
    active[1] = tuple(active[1]) + (("reason", "sat diagnostic prose"),)
    target[4] = tuple(active)

    assert not _object_target_key_is_specific_sat_unsafety(tuple(target))


def test_sat_unsafety_action_rejects_weak_proof_id_target():
    reason = _sat_reason()
    action = build_unknown_recovery_actions([reason])[0].to_dict()
    action["object_target_key"] = ("sat_unsafety", ("pair", "(0,1)"))

    assert not _proof_action_has_expected_id(action)


def test_sat_unsafety_pending_proof_obligations_materialize_required_evidence():
    action = build_unknown_recovery_actions([_sat_reason()])[0].to_dict()
    entry = {
        "required_completion_actions": [action],
        "current_observation": {
            "completed_recovery_proof_evidence": [],
        },
    }

    obligations = _pending_proof_obligations(entry)
    assert len(obligations) == 1
    assert obligations[0]["reason_id"] == (
        "counterexample_analysis_safety_unproven"
    )
    assert obligations[0]["proof_kind"] == SAT_PROOF_KIND
    assert obligations[0]["proof_stage"] == SAT_PROOF_STAGE
    assert obligations[0]["evidence_kind"] == SAT_EVIDENCE_KIND
    assert obligations[0]["required_evidence"] == list(SAT_REQUIRED_EVIDENCE)
    assert obligations[0]["proof_obligation_id"]
    assert obligations[0]["completed_evidence_present"] is False
    assert obligations[0]["status"] == "pending_evidence"


def test_sat_unsafety_post_fix_accepts_completed_replay_with_model_fingerprint():
    action = build_unknown_recovery_actions([_sat_reason()])[0].to_dict()
    entry = {
        "id": "representative-sat-unsafety-is-even-guard",
        "function": "fc_is_even",
        "binary_pair": "B9_B10",
        "required_completion_actions": [action],
        "current_observation": {
            "final_result": "NOT_EQ",
            "observed_reason_ids": [],
            "decision_gated_by_pending_proof": False,
            "proof_actions": [],
            "completed_recovery_proof_evidence": [
                _completed_sat_replay_evidence(action),
            ],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "completed_recovery"
    assert failures == ()


@pytest.mark.parametrize(
    "override",
    [
        {"counterexample_model_sha256": None},
        {"counterexample_model_sha256": "a" * 63},
        {"counterexample_model_sha256": "A" * 64},
        {"fixed_model_assertion_count": 0},
        {"counterexample_symbol_keys": ()},
    ],
)
def test_sat_unsafety_post_fix_rejects_completed_replay_without_fixed_model_fingerprint(override):
    action = build_unknown_recovery_actions([_sat_reason()])[0].to_dict()
    entry = {
        "id": "representative-sat-unsafety-is-even-guard",
        "function": "fc_is_even",
        "binary_pair": "B9_B10",
        "required_completion_actions": [action],
        "current_observation": {
            "final_result": "NOT_EQ",
            "observed_reason_ids": [],
            "decision_gated_by_pending_proof": False,
            "proof_actions": [],
            "completed_recovery_proof_evidence": [
                _completed_sat_replay_evidence(action, **override),
            ],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "failed"
    assert "sat_unsafety_completed_proof_required" in {failure["kind"] for failure in failures}


def test_sat_unsafety_post_fix_accepts_current_sat_action_when_target_details_change():
    reason = _sat_reason()
    action = build_unknown_recovery_actions([reason])[0].to_dict()
    action["raw_object_target_key_present"] = True
    action["raw_proof_obligation_id_present"] = True
    entry = {
        "id": "representative-sat-unsafety-is-even-guard",
        "function": "fc_is_even",
        "binary_pair": "B9_B10",
        "target_object_keys": [("sat_unsafety", ("pair", "frozen-target"))],
        "required_completion_actions": [
            {"reason_id": "sat_unsafety", "object_target_key": ("sat_unsafety", ("pair", "frozen-action"))}
        ],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "pending_proof"
    assert failures == ()


def test_sat_unsafety_post_fix_rejects_current_sat_target_without_action():
    reason = _sat_reason()
    entry = {
        "id": "representative-sat-unsafety-is-even-guard",
        "function": "fc_is_even",
        "binary_pair": "B9_B10",
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "failed"
    assert {failure["kind"] for failure in failures} >= {
        "sat_unsafety_current_actions_present",
        "sat_unsafety_current_actions_complete",
    }


def test_sat_unsafety_observation_supplements_registered_unresolved_actions():
    sat_reason = _sat_reason()
    sat_action = build_unknown_recovery_actions([sat_reason])[0]
    unresolved_reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind="unresolved_expression_safety",
        object_target_key=(
            "unresolved_expression",
            ("pair", "B9_B10"),
            ("expression", ("parameter", "x", ("int", 0), 4)),
        ),
    )
    record = {
        "payload": {
            "is_equivalent": None,
            "is_timeout": False,
            "function1_name": "fc_is_even",
            "function2_name": "fc_is_even",
            "binary1_name": "function_call_test-mips64-clang-O0",
            "binary2_name": "function_call_test-mips64-clang-O1",
            "unknown_reasons": [sat_reason.to_dict(), unresolved_reason.to_dict()],
            "unknown_recovery_actions": [sat_action.to_dict()],
        },
        "relative_log_path": "fc_is_even/fc_is_even_B9_B10.log",
        "log_sha256": "0" * 64,
    }

    observation = _observation({}, record)
    actions = observation["proof_actions"]

    assert [action["reason_id"] for action in actions].count(
        "counterexample_analysis_safety_unproven"
    ) == 1
    assert [action["reason_id"] for action in actions].count("unresolved_expression") == 2
    assert {
        action["proof_stage"]
        for action in actions
        if action["reason_id"] == "unresolved_expression"
    } == {"typed_expression_lowering", "type_normalization"}
    assert all(
        action["proof_obligation_id"]
        for action in actions
        if action["reason_id"] == "unresolved_expression"
    )
    assert all(
        action["raw_object_target_key_present"] is False
        for action in actions
        if action["reason_id"] == "unresolved_expression"
    )
