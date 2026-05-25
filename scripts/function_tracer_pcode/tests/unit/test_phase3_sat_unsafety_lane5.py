# -*- coding: utf-8 -*-

from unittest.mock import Mock

from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownRecoveryProofKind,
    build_unknown_recovery_actions,
)
from scripts.function_tracer_pcode.model import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    DeferredCallRef,
    Expression,
    FunctionReturnAnalysis,
    PcodeOpRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import _global_reason_tuple_from_action
from scripts.function_tracer_pcode.validation.phase3_sat_unsafety_lane5 import (
    SAT_ACTION_TUPLE,
    SAT_EVIDENCE_KIND,
    SAT_PROOF_KIND,
    SAT_PROOF_STAGE,
    SAT_REQUIRED_EVIDENCE,
    _object_target_key_is_specific_sat_unsafety,
    _proof_action_has_expected_id,
    _proof_action_matches_lane_definition,
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

    assert reason.object_target_key[0] == "sat_unsafety"
    assert _object_target_key_is_specific_sat_unsafety(reason.object_target_key)
    assert action.proof_kind == SAT_PROOF_KIND
    assert action.proof_stage == SAT_PROOF_STAGE
    assert action.evidence_kind == SAT_EVIDENCE_KIND
    assert action.required_evidence == SAT_REQUIRED_EVIDENCE
    assert action.proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert _global_reason_tuple_from_action(action) == SAT_ACTION_TUPLE
    action_dict = action.to_dict()
    assert _proof_action_matches_lane_definition(action_dict)
    assert _proof_action_has_expected_id(action_dict)


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
