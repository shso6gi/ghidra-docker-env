# -*- coding: utf-8 -*-

from pathlib import Path
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
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
)
from scripts.function_tracer_pcode.validation.phase3_unresolved_expression_lane6 import (
    UNRESOLVED_EVIDENCE_KIND,
    UNRESOLVED_GENERIC_PROOF_STAGES,
    UNRESOLVED_PHI_CIRCULAR_PROOF_STAGES,
    UNRESOLVED_PROOF_KIND,
    _extra_current_unresolved_expression_observations_from_records,
    UNRESOLVED_REASON_TUPLE,
    _object_target_key_is_specific_unresolved_expression,
    _pending_proof_obligations,
    _post_fix_checks,
    _post_fix_status,
    _required_completion_actions,
    validate_phase3_unresolved_expression_lane6_manifest,
    validate_phase3_unresolved_expression_lane6_post_fix_gate,
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
    assert all(action.proof_kind == UNRESOLVED_PROOF_KIND for action in actions)


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
        },
    )
