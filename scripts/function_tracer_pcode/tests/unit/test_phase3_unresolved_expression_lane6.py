# -*- coding: utf-8 -*-

from pathlib import Path
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownReasonId,
    build_unknown_recovery_actions,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    PcodeOpRef,
    ReturnInfo,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.validation.phase3_unresolved_expression_lane6 import (
    UNRESOLVED_DEFERRED_CALL_PROOF_STAGES,
    UNRESOLVED_EVIDENCE_KIND,
    UNRESOLVED_GENERIC_PROOF_STAGES,
    UNRESOLVED_OPAQUE_VOID_PROOF_STAGES,
    UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES,
    UNRESOLVED_PROOF_KIND,
    _extra_current_unresolved_expression_observations_from_records,
    _expression_shape_is_specific,
    _timeout_transition_readiness,
    UNRESOLVED_REASON_TUPLE,
    _object_target_key_is_specific_unresolved_expression,
    _pending_proof_obligations,
    _post_fix_checks,
    _post_fix_status,
    _required_completion_actions,
    _unresolved_expression_proof_actions_complete,
    validate_phase3_unresolved_expression_lane6_manifest,
    validate_phase3_unresolved_expression_lane6_post_fix_gate,
    validate_phase3_unresolved_expression_timeout_transition_audit,
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


def _phi_runtime_key(binary_id: str = "B12", offset: int = 0x2040):
    return (
        "opaque_unknown",
        "phi_circular",
        None,
        None,
        "multiequal_pcode_op",
        ("stable", _pcode(binary_id, offset, mnemonic="MULTIEQUAL").stable_key()),
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


def _originated_phi_target():
    target = list(_unresolved_target())
    right = list(target[3])
    right[5] = (
        "unresolved_locations",
        (
            (
                "unresolved_location",
                "guard_condition",
                0,
                False,
                (
                    "unresolved_classification",
                    ("location_scope", "guard_condition"),
                    ("unresolved_kinds", ("opaque_unknown",)),
                    (
                        "unknown_refs",
                        (
                            (
                                "unknown_runtime_ref",
                                _phi_runtime_key(),
                            ),
                        ),
                    ),
                    ("unsupported_ops", ()),
                ),
                ("return_guard", False, ("condition", ("const", ("int", 1), 1), False), ("expression", ("const", ("int", 1), 1))),
            ),
        ),
    )
    target[3] = tuple(right)
    return tuple(target)


def _deferred_call_runtime_ref(binary_id: str = "B10", entry: int = 0x3000):
    return (
        "runtime_ref",
        (
            "deferred_call",
            "call_out_of_scope",
            ("function", binary_id, entry),
            (
                "deferred_call_site",
                ("function_ref", ("function", binary_id, entry + 0x20)),
                _pcode(binary_id, entry + 0x40, mnemonic="CALL").stable_key(),
                ("function", binary_id, entry),
                ("argument",),
                0,
            ),
        ),
    )


def _deferred_call_target():
    target = list(_unresolved_target())
    left = list(target[2])
    member = list(left[4])
    return_case = list(member[3])
    deferred_ref = _deferred_call_runtime_ref("B10", 0x3000)
    return_case[6] = deferred_ref
    member[3] = tuple(return_case)
    member[5] = ("value", deferred_ref)
    left[4] = tuple(member)
    left[5] = (
        "unresolved_locations",
        (
            (
                "unresolved_location",
                "return_value",
                (
                    "unresolved_classification",
                    ("location_scope", "return_value"),
                    ("unresolved_kinds", ("deferred_call_unknown",)),
                    ("unknown_refs", (("unknown_runtime_ref", deferred_ref[1]),)),
                    ("unsupported_ops", ()),
                ),
                deferred_ref,
                (
                    "typed_lowering_evidence",
                    ("location_scope", "return_value"),
                    ("expression_kind", "UNKNOWN"),
                    ("expression_bits", 32),
                    ("typed_expression_key", deferred_ref),
                    ("contains_unsupported_smt_ops", False),
                    ("lowering_status", "blocked_unknown_expression"),
                ),
            ),
        ),
    )
    target[2] = tuple(left)
    return tuple(target)


def _opaque_void_runtime_ref():
    return (
        "runtime_ref",
        (
            "opaque_unknown",
            "void",
            None,
            None,
        ),
    )


def _opaque_void_target():
    target = list(_unresolved_target())
    left = list(target[2])
    member = list(left[4])
    return_case = list(member[3])
    opaque_ref = _opaque_void_runtime_ref()
    return_case[6] = opaque_ref
    member[3] = tuple(return_case)
    member[5] = ("value", opaque_ref)
    left[4] = tuple(member)
    left[5] = (
        "unresolved_locations",
        (
            (
                "unresolved_location",
                "return_value",
                (
                    "unresolved_classification",
                    ("location_scope", "return_value"),
                    ("unresolved_kinds", ("opaque_unknown",)),
                    ("unknown_refs", (("unknown_runtime_ref", opaque_ref[1]),)),
                    ("unsupported_ops", ()),
                ),
                opaque_ref,
                (
                    "typed_lowering_evidence",
                    ("location_scope", "return_value"),
                    ("expression_kind", "UNKNOWN"),
                    ("expression_bits", 32),
                    ("typed_expression_key", opaque_ref),
                    ("contains_unsupported_smt_ops", False),
                    ("lowering_status", "blocked_unknown_expression"),
                ),
            ),
        ),
    )
    target[2] = tuple(left)
    return tuple(target)


def _phi_circular_unknown(binary_id: str, entry: int) -> Expression:
    pcode_ref = PcodeOpRef(
        address_offset=entry + 0x20,
        seq_time=98,
        seq_order=0,
        block_index=0,
        mnemonic="MULTIEQUAL",
        input_sizes=(4, 4),
        output_size=4,
        binary_id=binary_id,
        function_entry_space="ram",
        function_entry_offset=entry,
        target_space="ram",
        target_offset=entry + 0x20,
        opcode=60,
        local_op_ordinal=0,
    )
    return Expression.unknown(
        "phi_circular",
        runtime_ref=UnknownValueRef.phi_circular(pcode_op_ref=pcode_ref),
    ).clone_with(size=4)


def _phi_guard_case(binary_id: str, entry: int, index: int):
    summary_value = Expression.parameter(f"summary_rec_{10000 + index}", 10000 + index, size=4)
    phi_unknown = _phi_circular_unknown(binary_id, entry)
    guard = Condition(
        Expression.binary_op(
            "INT_SLESS",
            Expression.unary_op("INT_2COMP", phi_unknown),
            Expression.constant(0, 4),
        ),
        False,
    )
    ret = ReturnInfo(
        address=hex(entry + 0x20),
        value=summary_value,
        conditions=[guard],
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


def _actual_phi_guard_target():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _phi_guard_case("B11", 0x1000, 0)
    right_analysis, right_case = _phi_guard_case("B12", 0x2000, 1)
    return strategy._unresolved_expression_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,1)",
    )


def _replace_first_tuple(value, tag, replacement_fn):
    if isinstance(value, tuple):
        if value and value[0] == tag:
            return replacement_fn(value), True
        changed = False
        items = []
        for item in value:
            new_item, item_changed = _replace_first_tuple(item, tag, replacement_fn)
            changed = changed or item_changed
            items.append(new_item)
            if item_changed:
                items.extend(value[len(items):])
                break
        return tuple(items), changed
    if isinstance(value, list):
        changed = False
        items = []
        for item in value:
            new_item, item_changed = _replace_first_tuple(item, tag, replacement_fn)
            changed = changed or item_changed
            items.append(new_item)
            if item_changed:
                items.extend(value[len(items):])
                break
        return items, changed
    if isinstance(value, dict):
        result = {}
        changed = False
        for key, item in value.items():
            if changed:
                result[key] = item
                continue
            new_item, item_changed = _replace_first_tuple(item, tag, replacement_fn)
            changed = changed or item_changed
            result[key] = new_item
        return result, changed
    return value, False


def _find_tuples(value, tag):
    found = []
    if isinstance(value, tuple):
        if value and value[0] == tag:
            found.append(value)
        for item in value:
            found.extend(_find_tuples(item, tag))
    elif isinstance(value, list):
        for item in value:
            found.extend(_find_tuples(item, tag))
    elif isinstance(value, dict):
        for item in value.values():
            found.extend(_find_tuples(item, tag))
    return found


def _with_typed_lowering_evidence(target):
    def visit(value):
        if isinstance(value, tuple):
            if value and value[0] == "unresolved_location":
                if value and isinstance(value[-1], tuple) and value[-1][0] == "typed_lowering_evidence":
                    return tuple(visit(item) for item in value)
                scope = value[1]
                evidence = (
                    "typed_lowering_evidence",
                    ("location_scope", scope),
                    ("expression_kind", "BINARY_OP"),
                    ("expression_bits", 1),
                    ("typed_expression_key", ("expression", ("const", ("int", 1), 1))),
                    ("contains_unsupported_smt_ops", False),
                    ("lowering_status", "blocked_nested_unresolved_expression"),
                )
                return tuple(visit(item) for item in value) + (evidence,)
            return tuple(visit(item) for item in value)
        if isinstance(value, list):
            return [visit(item) for item in value]
        if isinstance(value, dict):
            return {key: visit(item) for key, item in value.items()}
        return value

    return visit(target)


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
    assert _nested_contains(target, "unresolved_classification")
    assert _nested_contains(target, "opaque_unknown")
    assert _nested_contains(target, "unknown_expression")
    assert _nested_contains(target, "unresolved_call_value")
    assert _nested_contains(target, "typed_lowering_evidence")
    assert _nested_contains(target, "blocked_unknown_expression")
    assert not _nested_contains(target, ("reason", "unresolved_expression"))


def test_unresolved_expression_manifest_validator_rejects_ready_without_readiness():
    manifest = {
        "manifest_kind": "phase3_unresolved_expression_lane6_representatives",
        "phase3_lane6_ready": True,
    }

    with pytest.raises(ValueError, match="unresolved_expression_readiness_missing"):
        validate_phase3_unresolved_expression_lane6_manifest(manifest)


def test_unresolved_expression_manifest_validator_rejects_hidden_failed_kind():
    manifest = {
        "manifest_kind": "phase3_unresolved_expression_lane6_representatives",
        "phase3_lane6_ready": True,
        "readiness": {
            "ready": True,
            "failed_checks": [],
            "failed_kinds": ["hidden_unresolved_expression_failure"],
            "checks": [],
        },
    }

    with pytest.raises(ValueError, match="hidden_unresolved_expression_failure"):
        validate_phase3_unresolved_expression_lane6_manifest(manifest)


def test_unresolved_expression_post_fix_gate_validator_rejects_ready_without_checks():
    manifest = {
        "manifest_kind": "phase3_unresolved_expression_lane6_post_fix_gate",
        "phase3_lane6_post_fix_ready": True,
    }

    with pytest.raises(ValueError, match="unresolved_expression_post_fix_checks_missing"):
        validate_phase3_unresolved_expression_lane6_post_fix_gate(manifest)


def test_unresolved_expression_timeout_transition_audit_accepts_frozen_unknown_to_timeout():
    entry = {
        "id": "representative-recursive-sum-b10-b11-unresolved-to-timeout",
        "category": "function_call",
        "function": "fc_recursive_sum",
        "binary_pair": "B10_B11",
        "expected_observed_binary1_name": "function_call_test-mips64-clang-O1",
        "expected_observed_binary2_name": "function_call_test-mips64-clang-O2",
        "expected_baseline_result": "UNKNOWN",
        "expected_current_result": "TIMEOUT",
        "expected_baseline_reason_ids": ["sat_unsafety", "unresolved_expression"],
        "expected_current_reason_ids": ["solver_unknown_timeout"],
        "baseline_observation": {
            "log_status": "present",
            "final_result": "UNKNOWN",
            "observed_reason_ids": ["sat_unsafety", "unresolved_expression"],
        },
        "current_observation": {
            "log_status": "present",
            "final_result": "TIMEOUT",
            "observed_binary1_name": "function_call_test-mips64-clang-O1",
            "observed_binary2_name": "function_call_test-mips64-clang-O2",
            "observed_reason_ids": ["solver_unknown_timeout"],
        },
    }

    readiness = _timeout_transition_readiness([entry])

    assert readiness["ready"] is True
    assert readiness["failed_kinds"] == []


def test_unresolved_expression_timeout_transition_audit_rejects_reason_drift():
    entry = {
        "id": "representative-recursive-sum-b10-b11-unresolved-to-timeout",
        "category": "function_call",
        "function": "fc_recursive_sum",
        "binary_pair": "B10_B11",
        "expected_observed_binary1_name": "function_call_test-mips64-clang-O1",
        "expected_observed_binary2_name": "function_call_test-mips64-clang-O2",
        "expected_baseline_result": "UNKNOWN",
        "expected_current_result": "TIMEOUT",
        "expected_baseline_reason_ids": ["sat_unsafety", "unresolved_expression"],
        "expected_current_reason_ids": ["solver_unknown_timeout"],
        "baseline_observation": {
            "log_status": "present",
            "final_result": "UNKNOWN",
            "observed_reason_ids": ["sat_unsafety", "unresolved_expression"],
        },
        "current_observation": {
            "log_status": "present",
            "final_result": "TIMEOUT",
            "observed_binary1_name": "function_call_test-mips64-clang-O1",
            "observed_binary2_name": "function_call_test-mips64-clang-O2",
            "observed_reason_ids": ["solver_unknown_timeout", "unresolved_expression"],
        },
    }

    readiness = _timeout_transition_readiness([entry])

    assert readiness["ready"] is False
    assert "timeout_transition_current_reasons" in readiness["failed_kinds"]


def test_unresolved_expression_timeout_transition_validator_rejects_failed_ready_flag():
    manifest = {
        "manifest_kind": "phase3_unresolved_expression_timeout_transition_representatives",
        "phase3_lane6_timeout_transition_ready": False,
        "readiness": {
            "ready": False,
            "failed_checks": [],
            "failed_kinds": ["timeout_transition_current_reasons"],
        },
    }

    with pytest.raises(ValueError, match="unresolved_expression_timeout_transition"):
        validate_phase3_unresolved_expression_timeout_transition_audit(manifest)


def test_unresolved_expression_post_fix_checks_reject_tampered_pre_fix_manifest_ready():
    manifest = {
        "manifest_kind": "phase3_unresolved_expression_lane6_representatives",
        "phase3_lane6_ready": True,
        "readiness": {
            "ready": True,
            "failed_checks": [],
            "failed_kinds": ["hidden_unresolved_expression_pre_fix_failure"],
            "checks": [],
        },
        "entries": [],
    }

    checks = _post_fix_checks(
        baseline_manifest={"baseline_id": "observed-v0@0a53352"},
        phase3_manifest=manifest,
        phase3_manifest_path=Path("unresolved_expression_lane6_representatives.json"),
        actual_phase3_sha256="a" * 64,
        expected_phase3_sha256="a" * 64,
        entries=(),
    )

    ready_check = next(check for check in checks if check["kind"] == "phase3_pre_fix_manifest_ready")
    assert ready_check["status"] == "failed"
    assert "hidden_unresolved_expression_pre_fix_failure" in ready_check["error"]


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
    first_location[3] = ("expression", ("unknown", "", ("none",), 4))
    locations[1] = (tuple(first_location),)
    left[5] = tuple(locations)
    target[2] = tuple(left)

    assert not _object_target_key_is_specific_unresolved_expression(tuple(target))


def test_unresolved_expression_target_rejects_missing_location_classification():
    target = list(_unresolved_target())
    left = list(target[2])
    locations = list(left[5])
    first_location = list(locations[1][0])
    first_location.pop(2)
    locations[1] = (tuple(first_location),)
    left[5] = tuple(locations)
    target[2] = tuple(left)

    assert not _object_target_key_is_specific_unresolved_expression(tuple(target))


def test_unresolved_expression_target_rejects_empty_location_classification():
    target = list(_unresolved_target())
    left = list(target[2])
    locations = list(left[5])
    first_location = list(locations[1][0])
    first_location[2] = (
        "unresolved_classification",
        ("location_scope", "return_value"),
        ("unresolved_kinds", ()),
        ("unknown_refs", ()),
        ("unsupported_ops", ()),
    )
    locations[1] = (tuple(first_location),)
    left[5] = tuple(locations)
    target[2] = tuple(left)

    assert not _object_target_key_is_specific_unresolved_expression(tuple(target))


def test_unresolved_expression_target_rejects_malformed_typed_lowering_evidence():
    target = list(_unresolved_target())
    left = list(target[2])
    locations = list(left[5])
    first_location = list(locations[1][0])
    typed_evidence = list(first_location[4])
    typed_evidence[3] = ("expression_bits", "<missing>")
    first_location[4] = tuple(typed_evidence)
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
                (
                    "unresolved_classification",
                    ("location_scope", "guard_condition"),
                    ("unresolved_kinds", ("opaque_unknown",)),
                    (
                        "unknown_refs",
                        (
                            (
                                "unknown_runtime_ref",
                                _phi_runtime_key(),
                            ),
                        ),
                    ),
                    ("unsupported_ops", ()),
                ),
                tuple(guard),
            ),
        ),
    )
    target[3] = tuple(right)

    assert _object_target_key_is_specific_unresolved_expression(tuple(target))


def test_unresolved_expression_target_rejects_coarse_phi_circular_runtime_ref():
    target = list(_unresolved_target())
    right = list(target[3])
    right[5] = (
        "unresolved_locations",
        (
            (
                "unresolved_location",
                "guard_condition",
                0,
                False,
                (
                    "unresolved_classification",
                    ("location_scope", "guard_condition"),
                    ("unresolved_kinds", ("opaque_unknown",)),
                    (
                        "unknown_refs",
                        (
                            (
                                "unknown_runtime_ref",
                                ("opaque_unknown", "phi_circular", None, None),
                            ),
                        ),
                    ),
                    ("unsupported_ops", ()),
                ),
                ("return_guard", False, ("condition", ("const", ("int", 1), 1), False), ("expression", ("const", ("int", 1), 1))),
            ),
        ),
    )
    target[3] = tuple(right)

    assert not _object_target_key_is_specific_unresolved_expression(tuple(target))


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


def test_unresolved_expression_post_fix_status_moves_to_pending_proof_when_actions_exist():
    target = _unresolved_target()
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "pending_proof"
    assert failures == ()
    assert [action.proof_stage for action in actions] == list(UNRESOLVED_GENERIC_PROOF_STAGES)
    assert all(action.proof_obligation_id for action in actions)
    obligations = _pending_proof_obligations(entry)
    assert {obligation["proof_stage"] for obligation in obligations} == set(UNRESOLVED_GENERIC_PROOF_STAGES)
    assert all(obligation["reason_id"] == "unresolved_expression" for obligation in obligations)
    assert all(obligation["proof_kind"] == UNRESOLVED_PROOF_KIND for obligation in obligations)
    assert all(obligation["proof_obligation_id"] for obligation in obligations)
    assert all(obligation["completed_evidence_present"] is False for obligation in obligations)
    assert all(obligation["status"] == "pending_evidence" for obligation in obligations)
    required_actions = _required_completion_actions(entry)
    assert {action["proof_stage"] for action in required_actions} == set(UNRESOLVED_GENERIC_PROOF_STAGES)
    assert {
        repr(action["proof_obligation_id"])
        for action in required_actions
    } == {
        repr(obligation["proof_obligation_id"])
        for obligation in obligations
    }
    assert all(action["required_evidence"] for action in required_actions)


def test_unresolved_expression_post_fix_keeps_phi_circular_typed_lowering_without_relation_evidence_pending():
    frozen_target = _originated_phi_target()
    current_target = _with_typed_lowering_evidence(frozen_target)
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=current_target,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(current_target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [frozen_target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "pending_object_evidence"
    assert failures == ()
    assert _pending_proof_obligations(entry) == ()


def test_phi_circular_guard_target_carries_object_detail_proof_evidence():
    target = _actual_phi_guard_target()

    assert _object_target_key_is_specific_unresolved_expression(target)
    assert _nested_contains(target, "typed_lowering_evidence")
    assert _nested_contains(target, "phi_circular_evidence")
    assert _nested_contains(target, "phi_origin")
    assert _nested_contains(target, "summary_parameter")
    assert _nested_contains(target, ("relation_status", "pending_guard_summary_relation_proof"))
    assert _nested_contains(target, "guard_condition_key")


def test_phi_circular_guard_target_accepts_empty_summary_binding_when_no_parameter_binding_exists():
    target = _actual_phi_guard_target()

    def drop_summary_refs(evidence):
        return tuple(
            ("summary_parameter_refs", ())
            if isinstance(item, tuple) and item and item[0] == "summary_parameter_refs"
            else item
            for item in evidence
        )

    tampered, changed = _replace_first_tuple(target, "phi_circular_evidence", drop_summary_refs)

    assert changed
    assert _object_target_key_is_specific_unresolved_expression(tampered)


def test_phi_circular_guard_target_rejects_malformed_summary_binding_evidence():
    target = _actual_phi_guard_target()

    def break_summary_refs(evidence):
        return tuple(
            ("summary_parameter_refs", ("raw-summary-binding",))
            if isinstance(item, tuple) and item and item[0] == "summary_parameter_refs"
            else item
            for item in evidence
        )

    tampered, changed = _replace_first_tuple(target, "phi_circular_evidence", break_summary_refs)

    assert changed
    assert not _object_target_key_is_specific_unresolved_expression(tampered)


def test_phi_circular_guard_target_rejects_missing_origin_pcode_evidence():
    target = _actual_phi_guard_target()

    def drop_pcode_origin(origin):
        updated = list(origin)
        updated[3] = ("pcode_op_ref", "<missing>")
        return tuple(updated)

    tampered, changed = _replace_first_tuple(target, "phi_origin", drop_pcode_origin)

    assert changed
    assert not _object_target_key_is_specific_unresolved_expression(tampered)


def test_unresolved_expression_phi_circular_target_uses_dedicated_proof_stages():
    target = _originated_phi_target()
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    assert [action.proof_stage for action in actions] == list(UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES)
    assert all("guard" in " ".join(action.required_evidence) for action in actions)
    assert all("pair_lowering_diagnostic" in action.required_evidence for action in actions)
    assert all(action.proof_kind == UNRESOLVED_PROOF_KIND for action in actions)


def test_phi_circular_target_records_guard_literals_and_pair_diagnostic():
    target = _actual_phi_guard_target()

    phi_evidence = _find_tuples(target, "phi_circular_evidence")
    assert phi_evidence
    assert any(
        item[0] == "guard_condition_literals" and item[1]
        for evidence in phi_evidence
        for item in evidence
        if isinstance(item, tuple)
    )
    diagnostics = _find_tuples(target, "pair_lowering_diagnostic")
    assert len(diagnostics) == 1
    diagnostic = diagnostics[0]
    assert ("candidate_kind", "phi_circular_guard_summary_relation") in diagnostic
    assert ("status", "value_shape_mismatch") in diagnostic
    assert (
        "unknown_count_relation",
        (
            "unknown_count_relation",
            ("relation", "equal"),
            ("left_count", 1),
            ("right_count", 1),
        ),
    ) in diagnostic
    assert (
        "value_shape_relation",
        (
            "value_shape_relation",
            ("relation", "summary_parameter_shift"),
            ("left_kind", "parameter"),
            ("right_kind", "parameter"),
            ("left_summary_parameter_index", 10000),
            ("right_summary_parameter_index", 10001),
            ("left_constant_value", None),
            ("right_constant_value", None),
        ),
    ) in diagnostic
    assert any(item[0] == "left_guard_literals" and item[1] for item in diagnostic)
    assert any(item[0] == "right_guard_literals" and item[1] for item in diagnostic)


def test_phi_circular_guard_literal_preserves_parameter_index_zero():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    _analysis, case = _phi_guard_case("B11", 0x1000, 0)
    original_guard = case.conditions[0].expression
    case.conditions[0].expression = Expression.binary_op(
        "BOOL_AND",
        original_guard,
        Expression.binary_op(
            "INT_EQUAL",
            Expression.parameter("param_1", 0, size=4),
            Expression.constant(0, 4),
        ),
    )

    literals = strategy._phi_circular_case_condition_literals(case)

    assert literals
    assert any(
        isinstance(literal, tuple)
        and len(literal) == 3
        and literal[0] == "guard_literal"
        and _expression_shape_is_specific(literal[2])
        and ("parameter", "param_1", 0, 32) in _find_tuples(literal[2], "parameter")
        for literal in literals
    )


def test_phi_circular_pair_diagnostic_rejects_malformed_value_shape_relation():
    target = _actual_phi_guard_target()

    def break_relation(diagnostic):
        return tuple(
            ("value_shape_relation", ("value_shape_relation", ("relation", "raw-diagnostic")))
            if isinstance(item, tuple) and item and item[0] == "value_shape_relation"
            else item
            for item in diagnostic
        )

    tampered, changed = _replace_first_tuple(target, "pair_lowering_diagnostic", break_relation)

    assert changed
    assert not _object_target_key_is_specific_unresolved_expression(tampered)


def test_phi_circular_pair_diagnostic_does_not_change_target_identity():
    current_target = _actual_phi_guard_target()
    frozen_target = tuple(
        item for item in current_target if not (isinstance(item, tuple) and item and item[0] == "pair_lowering_diagnostic")
    )
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=current_target,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(current_target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [frozen_target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    assert len(frozen_target) == 4
    assert len(current_target) == 5
    status, failures = _post_fix_status(entry)

    assert status == "pending_proof"
    assert failures == ()


def test_phi_circular_full_shape_match_diagnostic_evidence_keeps_gate_pending():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _phi_guard_case("B11", 0x1000, 0)
    right_analysis, right_case = _phi_guard_case("B12", 0x2000, 0)
    target = strategy._unresolved_expression_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )
    evidence = strategy._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(target)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        object_evidence=evidence,
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-full-shape",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    assert evidence is not None
    assert evidence[0] == "unresolved_expression_diagnostic_evidence"
    assert _nested_contains(evidence, "proof_query_plan")
    assert {action.status for action in actions} == {UnknownRecoveryActionStatus.PENDING_PROOF.value}
    assert all(action.object_evidence == evidence for action in actions)
    status, failures = _post_fix_status(entry)
    required_actions = _required_completion_actions(entry)
    pending_obligations = _pending_proof_obligations(entry)

    assert status == "pending_proof"
    assert failures == ()
    assert {action["object_evidence_status"] for action in required_actions} == {
        "object_evidence_collected"
    }
    assert {obligation["status"] for obligation in pending_obligations} == {
        "semantic_proof_required"
    }
    assert {obligation["object_evidence_status"] for obligation in pending_obligations} == {
        "object_evidence_collected"
    }


def test_phi_circular_shape_mismatch_does_not_build_completed_proof_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _phi_guard_case("B11", 0x1000, 0)
    right_analysis, right_case = _phi_guard_case("B12", 0x2000, 1)
    base_ctx = {"analysis1": left_analysis, "analysis2": right_analysis}
    target = strategy._unresolved_expression_object_target_key(
        base_ctx=base_ctx,
        case1=left_case,
        case2=right_case,
        pair_id="(0,1)",
    )
    evidence = strategy._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(target)

    assert evidence is None


def test_phi_circular_full_shape_match_rejects_completed_action_without_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _phi_guard_case("B11", 0x1000, 0)
    right_analysis, right_case = _phi_guard_case("B12", 0x2000, 0)
    target = strategy._unresolved_expression_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        action_status=UnknownRecoveryActionStatus.PROOF_COMPLETE,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-full-shape",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "failed"
    assert [failure["kind"] for failure in failures] == [
        "unresolved_expression_completed_proof_evidence_invalid"
    ]


def test_phi_circular_full_shape_match_rejects_completed_action_with_diagnostic_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _phi_guard_case("B11", 0x1000, 0)
    right_analysis, right_case = _phi_guard_case("B12", 0x2000, 0)
    target = strategy._unresolved_expression_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )
    evidence = strategy._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(target)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        object_evidence=evidence,
        action_status=UnknownRecoveryActionStatus.PROOF_COMPLETE,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-full-shape",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert evidence is not None
    assert status == "failed"
    assert [failure["kind"] for failure in failures] == [
        "unresolved_expression_completed_proof_evidence_invalid"
    ]


def test_phi_circular_pending_diagnostic_missing_stage_evidence_stays_pending_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _phi_guard_case("B11", 0x1000, 0)
    right_analysis, right_case = _phi_guard_case("B12", 0x2000, 0)
    target = strategy._unresolved_expression_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )
    evidence = strategy._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(target)
    fields = {
        item[0]: item[1]
        for item in evidence[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    weakened_evidence = tuple(
        item for item in evidence if not (isinstance(item, tuple) and item[0] == "stage_evidence")
    )
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        object_evidence=weakened_evidence,
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-full-shape",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)
    required_actions = _required_completion_actions(entry)
    pending_obligations = _pending_proof_obligations(entry)

    assert fields["stage_evidence"]
    assert status == "pending_proof"
    assert failures == ()
    assert {action["object_evidence_status"] for action in required_actions} == {
        "object_evidence_invalid"
    }
    assert {obligation["status"] for obligation in pending_obligations} == {
        "pending_evidence"
    }


def test_phi_circular_pending_diagnostic_missing_query_plan_stays_pending_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _phi_guard_case("B11", 0x1000, 0)
    right_analysis, right_case = _phi_guard_case("B12", 0x2000, 0)
    target = strategy._unresolved_expression_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )
    evidence = strategy._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(target)

    def drop_query_plan(value):
        return tuple(
            item
            for item in value
            if not (isinstance(item, tuple) and item and item[0] == "proof_query_plan")
        )

    weakened_evidence, changed = _replace_first_tuple(
        evidence,
        "unresolved_expression_stage_evidence",
        drop_query_plan,
    )
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        object_evidence=weakened_evidence,
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-full-shape",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)
    required_actions = _required_completion_actions(entry)

    assert changed is True
    assert status == "pending_proof"
    assert failures == ()
    assert {action["object_evidence_status"] for action in required_actions} == {
        "object_evidence_collected",
        "object_evidence_invalid",
    }


def test_phi_circular_pending_diagnostic_query_without_object_content_stays_pending_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _phi_guard_case("B11", 0x1000, 0)
    right_analysis, right_case = _phi_guard_case("B12", 0x2000, 0)
    target = strategy._unresolved_expression_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )
    evidence = strategy._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(target)

    def drop_query_object_content(value):
        fields = {
            item[0]: item[1]
            for item in value[1:]
            if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
        }
        if fields.get("query_stage") != "phi_circular_guard_condition_lowering":
            return value
        return tuple(
            item
            for item in value
            if not (
                isinstance(item, tuple)
                and item
                and item[0] == "guard_transition_relation"
            )
        )

    weakened_evidence, changed = _replace_first_tuple(
        evidence,
        "semantic_recurrence_query",
        drop_query_object_content,
    )
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        object_evidence=weakened_evidence,
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-full-shape",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)
    required_actions = _required_completion_actions(entry)

    assert changed is True
    assert status == "pending_proof"
    assert failures == ()
    assert {action["object_evidence_status"] for action in required_actions} == {
        "object_evidence_collected",
        "object_evidence_invalid",
    }


def test_phi_circular_full_shape_match_rejects_stale_completed_proof_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _phi_guard_case("B11", 0x1000, 0)
    right_analysis, right_case = _phi_guard_case("B12", 0x2000, 0)
    target = strategy._unresolved_expression_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )
    diagnostic = next(
        item
        for item in target
        if isinstance(item, tuple) and item and item[0] == "pair_lowering_diagnostic"
    )
    stale_evidence = (
        "completed_unresolved_expression_proof",
        ("object_derived", True),
        ("status", "complete"),
        ("proof_rule", "phi_circular_full_shape_match"),
        (
            "completed_stages",
            (
                "phi_circular_guard_condition_lowering",
                "recursive_summary_guard_equivalence",
            ),
        ),
        ("object_target_key", target),
        ("pair_lowering_diagnostic", diagnostic),
    )
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        object_evidence=stale_evidence,
        action_status=UnknownRecoveryActionStatus.PROOF_COMPLETE,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-full-shape",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "failed"
    assert [failure["kind"] for failure in failures] == [
        "unresolved_expression_completed_proof_evidence_invalid"
    ]


def test_phi_circular_semantic_recurrence_completed_proof_gate_accepts_query_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _phi_guard_case("B11", 0x1000, 0)
    right_analysis, right_case = _phi_guard_case("B12", 0x2000, 0)
    target = strategy._unresolved_expression_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )
    diagnostic_evidence = strategy._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(target)
    fields = {
        item[0]: item[1]
        for item in diagnostic_evidence[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    stage_fields_by_name = {
        stage_fields["proof_stage"]: stage_fields
        for stage_evidence in fields["stage_evidence"]
        for stage_fields in (
            {
                item[0]: item[1]
                for item in stage_evidence[1:]
                if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
            },
        )
    }
    guard_stage_fields = stage_fields_by_name["phi_circular_guard_condition_lowering"]
    recurrence_stage_fields = stage_fields_by_name["recursive_summary_guard_equivalence"]
    completed_stages = (
        "phi_circular_guard_condition_lowering",
        "recursive_summary_guard_equivalence",
    )
    semantic_proof = (
        "semantic_recurrence_proof",
        ("proof_rule", "phi_circular_semantic_recurrence_proof"),
        ("status", "complete"),
        ("completed_stages", completed_stages),
        ("object_target_key", target),
        ("pair_lowering_diagnostic", fields["pair_lowering_diagnostic"]),
        (
            "proof_queries",
            (
                (
                    "semantic_recurrence_query",
                    ("query_id", "guard-transition-query"),
                    ("query_stage", "phi_circular_guard_condition_lowering"),
                    ("solver_result", "unsat"),
                    ("query_status", "proven"),
                    ("guard_transition_relation", guard_stage_fields["guard_transition_relation"]),
                ),
                (
                    "semantic_recurrence_query",
                    ("query_id", "summary-recurrence-query"),
                    ("query_stage", "recursive_summary_guard_equivalence"),
                    ("solver_result", "unsat"),
                    ("query_status", "proven"),
                    (
                        "summary_parameter_binding",
                        recurrence_stage_fields["summary_parameter_binding"],
                    ),
                    ("recurrence_relation", recurrence_stage_fields["recurrence_relation"]),
                ),
            ),
        ),
    )
    completed_evidence = (
        "completed_unresolved_expression_proof",
        ("object_derived", True),
        ("status", "complete"),
        ("proof_rule", "phi_circular_semantic_recurrence_proof"),
        ("completed_stages", completed_stages),
        ("object_target_key", target),
        ("pair_lowering_diagnostic", fields["pair_lowering_diagnostic"]),
        ("stage_evidence", fields["stage_evidence"]),
        ("semantic_recurrence_proof", semantic_proof),
    )
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        object_evidence=completed_evidence,
        action_status=UnknownRecoveryActionStatus.PROOF_COMPLETE,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-full-shape",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "proof_complete"
    assert failures == ()


def test_phi_circular_semantic_recurrence_completed_proof_rejects_missing_queries():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_analysis, left_case = _phi_guard_case("B11", 0x1000, 0)
    right_analysis, right_case = _phi_guard_case("B12", 0x2000, 0)
    target = strategy._unresolved_expression_object_target_key(
        base_ctx={"analysis1": left_analysis, "analysis2": right_analysis},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )
    diagnostic_evidence = strategy._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(target)
    fields = {
        item[0]: item[1]
        for item in diagnostic_evidence[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    completed_stages = (
        "phi_circular_guard_condition_lowering",
        "recursive_summary_guard_equivalence",
    )
    incomplete_semantic_proof = (
        "semantic_recurrence_proof",
        ("proof_rule", "phi_circular_semantic_recurrence_proof"),
        ("status", "complete"),
        ("completed_stages", completed_stages),
        ("object_target_key", target),
        ("pair_lowering_diagnostic", fields["pair_lowering_diagnostic"]),
        ("proof_queries", ()),
    )
    completed_evidence = (
        "completed_unresolved_expression_proof",
        ("object_derived", True),
        ("status", "complete"),
        ("proof_rule", "phi_circular_semantic_recurrence_proof"),
        ("completed_stages", completed_stages),
        ("object_target_key", target),
        ("pair_lowering_diagnostic", fields["pair_lowering_diagnostic"]),
        ("stage_evidence", fields["stage_evidence"]),
        ("semantic_recurrence_proof", incomplete_semantic_proof),
    )
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        object_evidence=completed_evidence,
        action_status=UnknownRecoveryActionStatus.PROOF_COMPLETE,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-full-shape",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "failed"
    assert [failure["kind"] for failure in failures] == [
        "unresolved_expression_completed_proof_evidence_invalid"
    ]


def test_unresolved_expression_post_fix_accepts_phi_circular_pending_proof_actions_with_relation_evidence():
    target = _actual_phi_guard_target()
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "pending_proof"
    assert failures == ()
    assert {action["proof_stage"] for action in _required_completion_actions(entry)} == set(
        UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES
    )


def test_unresolved_expression_post_fix_rejects_phi_circular_actions_missing_value_relation():
    target = _actual_phi_guard_target()
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    action_dicts = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    for action in action_dicts:
        if action.get("proof_stage") == "recursive_summary_guard_equivalence":
            action["required_evidence"] = [
                item for item in action.get("required_evidence", ()) if item != "value_shape_relation"
            ]
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": action_dicts,
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "pending_object_evidence"
    assert failures == ()
    assert not _unresolved_expression_proof_actions_complete(entry, [target])


def test_unresolved_expression_post_fix_rejects_phi_circular_actions_without_relation_evidence():
    target = _originated_phi_target()
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "pending_object_evidence"
    assert failures == ()
    assert _required_completion_actions(entry) == ()


def test_unresolved_expression_deferred_call_target_uses_dedicated_proof_stages():
    target = _deferred_call_target()
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])

    assert _object_target_key_is_specific_unresolved_expression(target)
    assert [action.proof_stage for action in actions] == list(UNRESOLVED_DEFERRED_CALL_PROOF_STAGES)
    assert all(action.proof_kind == UNRESOLVED_PROOF_KIND for action in actions)
    assert all("deferred" in " ".join(action.required_evidence) or "return" in " ".join(action.required_evidence) for action in actions)


def test_unresolved_expression_post_fix_accepts_deferred_call_pending_proof_actions():
    target = _deferred_call_target()
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "function": "fc_is_even",
        "binary_pair": "B10_B13",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "pending_proof"
    assert failures == ()
    assert {action["proof_stage"] for action in _required_completion_actions(entry)} == set(
        UNRESOLVED_DEFERRED_CALL_PROOF_STAGES
    )


def test_unresolved_expression_opaque_void_target_uses_dedicated_proof_stages():
    target = _opaque_void_target()
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])

    assert _object_target_key_is_specific_unresolved_expression(target)
    assert [action.proof_stage for action in actions] == list(UNRESOLVED_OPAQUE_VOID_PROOF_STAGES)
    assert all(action.proof_kind == UNRESOLVED_PROOF_KIND for action in actions)
    assert all("opaque" in " ".join(action.required_evidence) or "return" in " ".join(action.required_evidence) for action in actions)


def test_unresolved_expression_post_fix_accepts_opaque_void_pending_proof_actions():
    target = _opaque_void_target()
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
        recovery_proof_obligations=strategy._unresolved_expression_recovery_proof_obligations(target),
    )
    actions = build_unknown_recovery_actions([reason])
    entry = {
        "id": "representative-unresolved-expression-is-odd-opaque-void-return-current-transition",
        "function": "fc_is_odd",
        "binary_pair": "B1_B2",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "pending_proof"
    assert failures == ()
    assert {action["proof_stage"] for action in _required_completion_actions(entry)} == set(
        UNRESOLVED_OPAQUE_VOID_PROOF_STAGES
    )


def test_unresolved_expression_post_fix_status_keeps_object_evidence_pending_without_actions():
    target = _unresolved_target()
    reason = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
    )
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "reason_records": [reason.to_dict()],
            "proof_actions": [],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "pending_object_evidence"
    assert failures == ()


def test_unresolved_expression_post_fix_status_accepts_target_cleared_under_other_unknown():
    target = _unresolved_target()
    blocker = make_unknown_reason(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind="call_effect_summary",
    )
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "observed_reason_ids": ["equivalence_blocking_unsafety"],
            "reason_records": [blocker.to_dict()],
            "proof_actions": [],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "resolved_under_other_conservative_unknown"
    assert failures == ()


def test_unresolved_expression_post_fix_status_rejects_target_cleared_without_reason():
    target = _unresolved_target()
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "observed_reason_ids": [],
            "reason_records": [],
            "proof_actions": [],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "failed"
    assert [failure["kind"] for failure in failures] == ["unresolved_expression_target_set_changed"]


def test_unresolved_expression_post_fix_status_rejects_target_cleared_with_stale_unresolved_action():
    target = _unresolved_target()
    blocker = make_unknown_reason(
        UnknownReasonId.RETURN_COVERAGE_GAP,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_refs=("function1:return_coverage_gap",),
    )
    unresolved = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
    )
    actions = build_unknown_recovery_actions([unresolved])
    entry = {
        "id": "representative-unresolved-expression-is-even-recursive-summary-current-transition",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "target_object_keys": [target],
        "current_observation": {
            "final_result": "UNKNOWN",
            "observed_reason_ids": ["return_coverage_gap"],
            "reason_records": [blocker.to_dict()],
            "proof_actions": [action.to_dict() for action in actions],
        },
    }

    status, failures = _post_fix_status(entry)

    assert status == "failed"
    assert [failure["kind"] for failure in failures] == ["unresolved_expression_target_set_changed"]


def test_extra_current_unresolved_expression_observations_exclude_manifest_entries():
    target = _unresolved_target()
    unresolved = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
    )
    gap = make_unknown_reason(
        UnknownReasonId.RETURN_COVERAGE_GAP,
        stage="S_PAIRWISE",
        evidence_refs=("function1:return_coverage_gap",),
    )
    records = {
        ("function_call", "fc_is_even", "B11_B12"): {
            "relative_log_path": "fc_is_even/fc_is_even_B11_B12.log",
            "payload": {
                "is_equivalent": None,
                "unknown_reasons": [unresolved.to_dict()],
            },
        },
        ("function_call", "fc_is_even", "B10_B15"): {
            "relative_log_path": "fc_is_even/fc_is_even_B10_B15.log",
            "payload": {
                "is_equivalent": None,
                "unknown_reasons": [unresolved.to_dict(), gap.to_dict()],
            },
        },
        ("function_call", "fc_is_even", "B1_B2"): {
            "relative_log_path": "fc_is_even/fc_is_even_B1_B2.log",
            "payload": {
                "is_equivalent": None,
                "unknown_reasons": [gap.to_dict()],
            },
        },
    }

    observations = _extra_current_unresolved_expression_observations_from_records(
        records,
        manifest_keys=(("function_call", "fc_is_even", "B11_B12"),),
    )

    assert observations == (
        {
            "category": "function_call",
            "function": "fc_is_even",
            "binary_pair": "B10_B15",
            "log_path": "fc_is_even/fc_is_even_B10_B15.log",
            "final_result": "UNKNOWN",
            "unresolved_expression_reason_record_count": 1,
            "observed_reason_ids": ["return_coverage_gap", "unresolved_expression"],
            "proof_action_object_evidence_status_counts": {
                "pending_evidence": 2,
            },
            "pair_lowering_diagnostic_status_counts": {},
            "pair_lowering_diagnostic_relation_counts": {},
        },
    )


def test_extra_current_unresolved_expression_observations_report_pair_diagnostic_statuses():
    target = _actual_phi_guard_target()
    unresolved = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_EXPRESSION,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_kind=UNRESOLVED_EVIDENCE_KIND,
        object_target_key=target,
    )
    records = {
        ("function_call", "fc_is_even", "B11_B12"): {
            "relative_log_path": "fc_is_even/fc_is_even_B11_B12.log",
            "payload": {
                "is_equivalent": None,
                "unknown_reasons": [unresolved.to_dict()],
            },
        },
    }

    observations = _extra_current_unresolved_expression_observations_from_records(
        records,
        manifest_keys=(),
    )

    assert observations[0]["pair_lowering_diagnostic_status_counts"] == {
        "value_shape_mismatch": 1,
    }
    assert observations[0]["proof_action_object_evidence_status_counts"] == {
        "pending_evidence": 2,
    }
    assert observations[0]["pair_lowering_diagnostic_relation_counts"] == {
        "phi_origin_shape_relation:exact_match": 1,
        "unknown_count_relation:equal": 1,
        "value_shape_relation:summary_parameter_shift": 1,
    }
