# -*- coding: utf-8 -*-

from unittest.mock import Mock

from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    PcodeOpRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.validation.phase3_unresolved_expression_lane6 import (
    UNRESOLVED_EVIDENCE_KIND,
    UNRESOLVED_REASON_TUPLE,
    _object_target_key_is_specific_unresolved_expression,
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


def _unresolved_target():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _case(
        "B10",
        0x1000,
        0,
        Expression(ExpressionType.UNKNOWN, name="unresolved_call_value", size=4),
    )
    right_analysis, right_case = _case("B15", 0x2000, 1, Expression.constant(1, 4))
    return strategy._unresolved_expression_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,1)",
    )


def _nested_contains(value, needle) -> bool:
    if value == needle:
        return True
    if isinstance(value, (tuple, list)):
        return any(_nested_contains(item, needle) for item in value)
    if isinstance(value, dict):
        return any(_nested_contains(key, needle) or _nested_contains(item, needle) for key, item in value.items())
    return False


def test_unresolved_expression_target_is_object_specific():
    target = _unresolved_target()

    assert target[0] == "unresolved_expression"
    assert _object_target_key_is_specific_unresolved_expression(target)
    assert _nested_contains(target, "unresolved_call_value")
    assert not _nested_contains(target, ("reason", "unresolved_expression"))


def test_unresolved_expression_target_rejects_nested_diagnostic_reason():
    target = list(_unresolved_target())
    left = list(target[2])
    locations = list(left[5])
    locations[1] = tuple(locations[1]) + (("reason", "raw diagnostic"),)
    left[5] = tuple(locations)
    target[2] = tuple(left)

    assert not _object_target_key_is_specific_unresolved_expression(tuple(target))


def test_unresolved_expression_target_rejects_missing_unresolved_locations():
    target = list(_unresolved_target())
    for side_index in (2, 3):
        side = list(target[side_index])
        side[5] = ("unresolved_locations", ())
        target[side_index] = tuple(side)

    assert not _object_target_key_is_specific_unresolved_expression(tuple(target))


def test_unresolved_expression_target_rejects_weak_unknown_payload():
    target = list(_unresolved_target())
    left = list(target[2])
    locations = list(left[5])
    first_location = list(locations[1][0])
    first_location[2] = ("expression", ("unknown", "", ("none",), 4))
    locations[1] = (tuple(first_location),)
    left[5] = tuple(locations)
    target[2] = tuple(left)

    assert not _object_target_key_is_specific_unresolved_expression(tuple(target))


def test_unresolved_expression_target_rejects_missing_pcode_opcode():
    target = list(_unresolved_target())
    left = list(target[2])
    member = list(left[4])
    return_case = list(member[3])
    pcode_ref = list(return_case[3])
    pcode_ref[6] = "<missing>"
    return_case[3] = tuple(pcode_ref)
    member[3] = tuple(return_case)
    left[4] = tuple(member)
    target[2] = tuple(left)

    assert not _object_target_key_is_specific_unresolved_expression(tuple(target))


def test_unresolved_expression_target_rejects_raw_call_callee_expression():
    target = list(_unresolved_target())
    left = list(target[2])
    member = list(left[4])
    return_case = list(member[3])
    raw_call = ("expression", ("call", "raw-prose-ish-callee", 4, ()))
    return_case[6] = raw_call
    member[3] = tuple(return_case)
    member[5] = ("value", raw_call)
    left[4] = tuple(member)
    target[2] = tuple(left)

    assert not _object_target_key_is_specific_unresolved_expression(tuple(target))


def test_unresolved_expression_target_accepts_nested_unknown_guard_expression():
    target = list(_unresolved_target())
    right = list(target[3])
    member = list(right[4])
    return_case = list(member[3])
    guard = list(return_case[7][0])
    guard[2] = (
        "condition",
        (
            "binary",
            "INT_NOTEQUAL",
            1,
            (
                "unknown",
                "phi_circular",
                ("none", ""),
                0,
                (
                    "runtime_ref",
                    (
                        "stable_runtime_ref",
                        ("tuple", (("str", "opaque_unknown"), ("str", "phi_circular"))),
                    ),
                ),
            ),
            ("const", ("int", 0), 1),
        ),
        False,
    )
    guard[3] = (
        "expression",
        (
            "binary",
            "INT_NOTEQUAL",
            1,
            (
                "unknown",
                "phi_circular",
                ("none", ""),
                0,
                (
                    "runtime_ref",
                    (
                        "stable_runtime_ref",
                        ("tuple", (("str", "opaque_unknown"), ("str", "phi_circular"))),
                    ),
                ),
            ),
            ("const", ("int", 0), 1),
        ),
    )
    return_case[7] = (tuple(guard),)
    member[3] = tuple(return_case)
    right[4] = tuple(member)
    right[5] = (
        "unresolved_locations",
        (
            (
                "unresolved_location",
                "guard_condition",
                0,
                False,
                tuple(guard),
            ),
        ),
    )
    target[3] = tuple(right)

    assert _object_target_key_is_specific_unresolved_expression(tuple(target))


def test_unresolved_expression_reason_tuple_stays_count_compatible():
    assert UNRESOLVED_REASON_TUPLE == (
        "reason_record",
        "unresolved_expression",
        "blocks_decision",
        "expression",
        "none",
        "<missing>",
        "<missing>",
    )
    assert UNRESOLVED_EVIDENCE_KIND == "unresolved_expression_safety"
