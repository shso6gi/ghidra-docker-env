# -*- coding: utf-8 -*-

from unittest.mock import Mock

from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.unknown_reason import build_proof_obligation_id
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    FunctionReturnAnalysis,
    PcodeOpRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.validation.phase3_solver_rewrite_lane7 import (
    SOLVER_ACTION_TUPLE,
    SOLVER_EVIDENCE_KIND,
    SOLVER_PROOF_KIND,
    SOLVER_PROOF_STAGE,
    SOLVER_REASON_TUPLE,
    _action_has_expected_id,
    _action_matches_lane_definition,
    _object_target_key_is_specific_solver_rewrite_candidate,
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
        function_name="lmb_sum_prefix_loop",
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


def _solver_target():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _case(
        "B12",
        0x1000,
        0,
        Expression.binary_op(
            "INT_ADD",
            Expression.parameter("x", 0, size=4),
            Expression.constant(1, 4),
        ),
    )
    right_analysis, right_case = _case(
        "B16",
        0x2000,
        1,
        Expression.binary_op(
            "INT_ADD",
            Expression.parameter("x", 0, size=4),
            Expression.constant(1, 4),
        ),
    )
    return strategy._solver_rewrite_candidate_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,1)",
    )


def test_solver_rewrite_target_is_object_specific():
    target = _solver_target()

    assert target[0] == "solver_rewrite_candidate"
    assert _object_target_key_is_specific_solver_rewrite_candidate(target)


def test_solver_rewrite_target_rejects_nested_diagnostic_reason():
    target = list(_solver_target())
    left = list(target[3])
    left[5] = ("typed_expression_key", ("reason", "solver rewrite prose"))
    target[3] = tuple(left)

    assert not _object_target_key_is_specific_solver_rewrite_candidate(tuple(target))


def test_solver_rewrite_target_rejects_missing_typed_expression_key():
    target = list(_solver_target())
    right = list(target[4])
    right[5] = ("typed_expression_key", None)
    target[4] = tuple(right)

    assert not _object_target_key_is_specific_solver_rewrite_candidate(tuple(target))


def test_solver_rewrite_target_rejects_missing_guard_opcode():
    target = list(_solver_target())
    left = list(target[3])
    member = list(left[4])
    return_case = list(member[3])
    guard = list(return_case[7][0])
    guard[2] = ("condition", ("raw-prose-ish",), False)
    return_case[7] = (tuple(guard),)
    member[3] = tuple(return_case)
    left[4] = tuple(member)
    target[3] = tuple(left)

    assert not _object_target_key_is_specific_solver_rewrite_candidate(tuple(target))


def test_solver_rewrite_action_requires_full_tuple_and_proof_id():
    target = _solver_target()
    proof_id = build_proof_obligation_id(
        "solver_proven_rewrite_no_change",
        SOLVER_PROOF_STAGE,
        SOLVER_PROOF_KIND,
        SOLVER_EVIDENCE_KIND,
        target,
    )
    action = {
        "tuple": list(SOLVER_ACTION_TUPLE),
        "reason_id": "solver_proven_rewrite_no_change",
        "stage": "S_PAIRWISE",
        "pair_or_case": "(0,1)",
        "proof_kind": SOLVER_PROOF_KIND,
        "proof_stage": SOLVER_PROOF_STAGE,
        "status": "planned",
        "required_evidence": [
            "pre_normalized_query",
            "rewrite_candidate",
            "typed_expression_key",
        ],
        "evidence_kind": SOLVER_EVIDENCE_KIND,
        "object_target_key": target,
        "proof_obligation_id": proof_id,
    }

    assert _action_matches_lane_definition(action)
    assert _action_has_expected_id(action)

    weakened = dict(action)
    weakened["tuple"] = list(SOLVER_ACTION_TUPLE[:-1]) + ["pending_proof"]
    assert not _action_matches_lane_definition(weakened)

    wrong_id = dict(action)
    wrong_id["proof_obligation_id"] = ("not", "the", "full", "key")
    assert not _action_has_expected_id(wrong_id)


def test_solver_rewrite_reason_tuple_stays_count_compatible():
    assert SOLVER_REASON_TUPLE == (
        "reason_record",
        "solver_proven_rewrite_no_change",
        "retryable",
        "pair",
        "solver_retry_or_normalization",
        "rewrite_candidate_generation",
        "<missing>",
    )
    assert SOLVER_ACTION_TUPLE == (
        "proof_action",
        "solver_proven_rewrite_no_change",
        "retryable",
        "pair",
        "solver_retry_or_normalization",
        "rewrite_candidate_generation",
        "planned",
    )
