# -*- coding: utf-8 -*-

from copy import deepcopy
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
    DEFAULT_REPRESENTATIVES,
    RETURN_COVERAGE_RECLASSIFIED_GUARD_ACTION_TUPLE,
    RETURN_COVERAGE_RECLASSIFIED_PARTITION_ACTION_TUPLE,
    RETURN_COVERAGE_RECLASSIFIED_REASON_TUPLE,
    SOLVER_ACTION_TUPLE,
    SOLVER_EVIDENCE_KIND,
    SOLVER_PROOF_KIND,
    SOLVER_PROOF_STAGE,
    SOLVER_REASON_TUPLE,
    _action_has_expected_id,
    _action_matches_lane_definition,
    _object_target_key_is_specific_solver_rewrite_candidate,
    _post_fix_status,
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


def _return_coverage_target():
    pcode = (
        "pcode_op",
        "B12",
        ("function_entry", "ram", 0x1000),
        ("seq_target", "ram", 0x1020),
        1,
        0,
        62,
        0,
    )
    case = (
        "return_case",
        0,
        "00101020",
        pcode,
        "00101020:t1",
        0,
        ("expression", ("const", ("int", 0), 4)),
        (),
    )
    return (
        "return_coverage",
        "function1",
        ("function_ref", ("function", "B12", 0x1000)),
        "return_coverage_gap",
        ("return_storage", "return_value", 32, None, "int"),
        ("return_partition", (case,)),
        ("guard_disjunction", ((0, ()),)),
    )


def _return_coverage_action(stage: str):
    target = _return_coverage_target()
    evidence_kind = (
        "missing_return_guard"
        if stage == "return_partition_extraction"
        else "case_guard_disjunction"
    )
    required_evidence = (
        ["missing_return_guard", "tail_or_default_return_value", "return_storage"]
        if stage == "return_partition_extraction"
        else ["case_guard_disjunction", "path_feasibility", "function_precondition"]
    )
    return {
        "tuple": list(
            RETURN_COVERAGE_RECLASSIFIED_PARTITION_ACTION_TUPLE
            if stage == "return_partition_extraction"
            else RETURN_COVERAGE_RECLASSIFIED_GUARD_ACTION_TUPLE
        ),
        "reason_id": "return_coverage_gap",
        "stage": "S_PAIRWISE",
        "pair_or_case": None,
        "proof_kind": "return_coverage_completion",
        "proof_stage": stage,
        "status": "pending_proof",
        "required_evidence": required_evidence,
        "evidence_refs": ["function1:return_coverage_gap"],
        "evidence_kind": evidence_kind,
        "object_target_key": target,
        "proof_obligation_id": build_proof_obligation_id(
            "return_coverage_gap",
            stage,
            "return_coverage_completion",
            evidence_kind,
            target,
        ),
        "raw_object_target_key_present": True,
        "raw_proof_obligation_id_present": True,
    }


def _post_fix_reclassified_entry():
    target = _return_coverage_target()
    partition_action = _return_coverage_action("return_partition_extraction")
    guard_action = _return_coverage_action("return_guard_coverage")
    entry = dict(DEFAULT_REPRESENTATIVES[0])
    entry.update({
        "current_observation": {
            "final_result": "UNKNOWN",
            "observed_reason_ids": ["return_coverage_gap"],
            "reason_record_tuples": [list(RETURN_COVERAGE_RECLASSIFIED_REASON_TUPLE)],
            "proof_action_tuples": [
                list(RETURN_COVERAGE_RECLASSIFIED_PARTITION_ACTION_TUPLE),
                list(RETURN_COVERAGE_RECLASSIFIED_GUARD_ACTION_TUPLE),
            ],
            "reason_records": [
                {
                    "tuple": list(RETURN_COVERAGE_RECLASSIFIED_REASON_TUPLE),
                    "reason_id": "return_coverage_gap",
                    "evidence_refs": ["function1:return_coverage_gap"],
                    "object_target_key": target,
                    "proof_obligation_id": None,
                }
            ],
            "proof_actions": [partition_action, guard_action],
        },
    })
    return entry


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


def test_solver_rewrite_post_fix_accepts_explicit_return_coverage_reclassification():
    status, failures = _post_fix_status(_post_fix_reclassified_entry())

    assert status == "retired_to_return_coverage_gap"
    assert failures == ()


def test_solver_rewrite_post_fix_reclassification_requires_both_return_coverage_actions():
    entry = _post_fix_reclassified_entry()
    entry["current_observation"]["proof_action_tuples"] = [
        list(RETURN_COVERAGE_RECLASSIFIED_PARTITION_ACTION_TUPLE)
    ]
    entry["current_observation"]["proof_actions"] = [
        _return_coverage_action("return_partition_extraction")
    ]

    status, failures = _post_fix_status(entry)

    assert status == "failed"
    assert any(
        failure.get("kind") == "solver_rewrite_accepted_reclassification_tuple_missing"
        for failure in failures
    )


def test_solver_rewrite_post_fix_reclassification_requires_action_evidence_kind_and_required_evidence():
    entry = _post_fix_reclassified_entry()
    action = dict(entry["current_observation"]["proof_actions"][0])
    action["evidence_kind"] = "wrong_return_coverage_evidence"
    action["required_evidence"] = ["wrong_return_coverage_evidence"]
    action["proof_obligation_id"] = build_proof_obligation_id(
        "return_coverage_gap",
        action["proof_stage"],
        action["proof_kind"],
        action["evidence_kind"],
        action["object_target_key"],
    )
    entry["current_observation"]["proof_actions"][0] = action

    status, failures = _post_fix_status(entry)

    assert status == "failed"
    assert any(
        failure.get("kind") == "solver_rewrite_accepted_reclassification_action_evidence_kind"
        for failure in failures
    )
    assert any(
        failure.get("kind") == "solver_rewrite_accepted_reclassification_action_required_evidence"
        for failure in failures
    )


def test_solver_rewrite_post_fix_reclassification_freezes_expected_evidence_kind():
    entry = deepcopy(_post_fix_reclassified_entry())
    wrong_kind = "wrong_return_coverage_evidence"
    for movement in entry["accepted_post_fix_reclassification"]["accepted_movements"]:
        if movement["id"] == "solver-rewrite-retired-to-return-coverage-partition-action":
            movement["expected_evidence_kind"] = wrong_kind
            break
    else:
        raise AssertionError("partition reclassification action definition not found")
    action = entry["current_observation"]["proof_actions"][0]
    action["evidence_kind"] = wrong_kind
    action["proof_obligation_id"] = build_proof_obligation_id(
        "return_coverage_gap",
        action["proof_stage"],
        action["proof_kind"],
        wrong_kind,
        action["object_target_key"],
    )

    status, failures = _post_fix_status(entry)

    assert status == "failed"
    assert any(
        failure.get("kind") == "solver_rewrite_accepted_reclassification_definition"
        for failure in failures
    )


def test_solver_rewrite_post_fix_reclassification_requires_expected_evidence_refs():
    entry = _post_fix_reclassified_entry()
    entry["current_observation"]["reason_records"][0]["evidence_refs"] = [
        "wrong:return_coverage_gap"
    ]
    entry["current_observation"]["proof_actions"] = [
        {**action, "evidence_refs": ["wrong:return_coverage_gap"]}
        for action in entry["current_observation"]["proof_actions"]
    ]

    status, failures = _post_fix_status(entry)

    assert status == "failed"
    assert any(
        failure.get("kind") == "solver_rewrite_accepted_reclassification_record_evidence_refs"
        for failure in failures
    )
    assert any(
        failure.get("kind") == "solver_rewrite_accepted_reclassification_action_evidence_refs"
        for failure in failures
    )


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
