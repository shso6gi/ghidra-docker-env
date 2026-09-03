# -*- coding: utf-8 -*-

from types import MethodType
from unittest.mock import Mock

from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker, StageID
from scripts.function_tracer_pcode.proof.recursive_abstraction import abstract_recursive_calls
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.proof.return_width.surface import (
    ExtensionKind,
    ExtensionEvidenceSource,
    FunctionReturnWidthSeed,
    FunctionReturnWidthTargetId,
    GuardRegionFact,
    GuardRegionTargetId,
    build_pair_return_observation_seed,
)
from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
    assess_return_abi_pair,
)
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.analysis.returns import parameters as session_helpers_1
from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    Expression,
    ExpressionType,
    ReturnInfo,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis, create_mock_result


class _AbiTestSpace:
    def getName(self):
        return "register"


class _AbiTestAddress:
    def getAddressSpace(self):
        return _AbiTestSpace()

    def getOffset(self):
        return 0


class _AbiTestVarnode:
    def getAddress(self):
        return _AbiTestAddress()

    def getSize(self):
        return 8


class _AbiTestStorage:
    def getVarnodes(self):
        return [_AbiTestVarnode()]


class _AbiTestPrototype:
    def getModelName(self):
        return "default"

    def getReturnStorage(self):
        return _AbiTestStorage()


class _AbiTestReturnType:
    def getPathName(self):
        return "/int"

    def getLength(self):
        return 8


def _production_return_abi_facts():
    return session_helpers_1._sealed_return_abi_facts(
        _AbiTestPrototype(), _AbiTestReturnType(), "int"
    )


def _production_width_seed(analysis, side):
    member = ("return-member", side)
    guard_target = GuardRegionTargetId(member, (("guard-slot", side),))
    target = FunctionReturnWidthTargetId(
        analysis.outcome_function_identity(), member, guard_target
    )
    return FunctionReturnWidthSeed(
        target,
        GuardRegionFact("complete", (("guard", side),)),
        64,
        64,
        ("storage", side, 64),
        ("payload", side, 64),
        ("return_type_provenance", ("declared_return_type_width", 64)),
        ExtensionEvidenceSource(
            ExtensionKind.SAME_WIDTH.value,
            ("storage-value", side),
            ("payload-value", side),
            (("producer", side),),
            "certified_flow",
        ),
    )


def _param(name: str = "n", index: int = 0, size: int = 4):
    return Expression.parameter(name, index=index, data_type="int", size=size)


def _const(value: int, size: int = 4):
    return Expression.constant(value, size=size)


def _external_sqrt_target():
    return CallTargetRef.from_name("sqrt", is_external=True, library_name="libm")


def _self_recursive_target(function_name: str):
    synthetic_program_id = sum(ord(ch) for ch in function_name) & 0xFFFFFFFF
    return CallTargetRef.from_name(
        function_name,
        program_id=synthetic_program_id,
        entry_offset=0x00401000,
    )


def _deferred_unknown(info: DeferredCallInfo):
    return Expression.unknown(info.placeholder_name, runtime_ref=info.unknown_ref)


def _analysis_with_deferred_value(
    function_name: str,
    info: DeferredCallInfo,
    *,
    parameters=None,
    condition=None,
    value_size: int = 8,
):
    conditions = [] if condition is None else [condition]
    value = Expression.unknown(
        info.placeholder_name,
        runtime_ref=info.unknown_ref,
    )
    value.size = value_size
    return create_mock_analysis(
        function_name,
        parameters=parameters or [{"name": "x", "index": 0, "data_type": "double", "size": 8}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=value,
                conditions=conditions,
            )
        ],
    )


def test_recursive_abstraction_rewrites_matching_self_recursive_placeholders_to_shared_params():
    n1 = _param("n", 0)
    n2 = _param("m", 0)
    placeholder1 = "call_out_of_scope:left#0"
    placeholder2 = "call_out_of_scope:right#0"
    info1 = DeferredCallInfo(
        placeholder1,
        _self_recursive_target("left"),
        [Expression.binary_op("INT_SUB", n1, _const(1))],
        sequence=0,
    )
    info2 = DeferredCallInfo(
        placeholder2,
        _self_recursive_target("right"),
        [Expression.binary_op("INT_SUB", n2, _const(1))],
        sequence=0,
    )

    analysis1 = create_mock_analysis(
        "left",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op("INT_ADD", _deferred_unknown(info1), _const(1)),
                conditions=[],
            )
        ],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[{"name": "m", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x2000",
                value=Expression.binary_op("INT_ADD", _deferred_unknown(info2), _const(1)),
                conditions=[],
            )
        ],
    )
    analysis1.deferred_calls = {
        placeholder1: info1
    }
    analysis2.deferred_calls = {
        placeholder2: info2
    }

    result = abstract_recursive_calls(analysis1, analysis2, debug=False)

    assert result.applied is True
    assert len(result.matches) == 1
    left_expr = result.analysis1.returns[0].value.to_string()
    right_expr = result.analysis2.returns[0].value.to_string()
    assert "summary_rec_" in left_expr
    assert left_expr == right_expr
    assert any(param.get("synthetic_recursive_summary") for param in result.analysis1.parameters)
    assert any(param.get("synthetic_recursive_summary") for param in result.analysis2.parameters)


def test_recursive_abstraction_rejects_name_only_self_target_even_when_display_name_matches():
    n1 = _param("n", 0)
    n2 = _param("m", 0)
    placeholder1 = "call_out_of_scope:left#0"
    placeholder2 = "call_out_of_scope:right#0"
    info1 = DeferredCallInfo(
        placeholder1,
        CallTargetRef.from_name("left"),
        [Expression.binary_op("INT_SUB", n1, _const(1))],
        sequence=0,
    )
    info2 = DeferredCallInfo(
        placeholder2,
        CallTargetRef.from_name("right"),
        [Expression.binary_op("INT_SUB", n2, _const(1))],
        sequence=0,
    )
    analysis1 = create_mock_analysis(
        "left",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(info1), conditions=[])],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[{"name": "m", "index": 0, "data_type": "int", "size": 4}],
        returns=[ReturnInfo(address="0x2000", value=_deferred_unknown(info2), conditions=[])],
    )
    analysis1.deferred_calls = {placeholder1: info1}
    analysis2.deferred_calls = {placeholder2: info2}

    result = abstract_recursive_calls(analysis1, analysis2, debug=False)

    assert result.applied is False
    assert result.matches == []


def test_recursive_abstraction_matches_structurally_equivalent_arguments_without_string_keys():
    n1 = _param("n", 0)
    n2 = _param("m", 0)
    placeholder1 = "call_out_of_scope:left#0"
    placeholder2 = "call_out_of_scope:right#0"
    info1 = DeferredCallInfo(
        placeholder1,
        _self_recursive_target("left"),
        [Expression.binary_op("INT_ADD", n1, _const(1))],
        sequence=0,
    )
    info2 = DeferredCallInfo(
        placeholder2,
        _self_recursive_target("right"),
        [Expression.binary_op("INT_ADD", _const(1), n2)],
        sequence=0,
    )

    analysis1 = create_mock_analysis(
        "left",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_deferred_unknown(info1),
                conditions=[],
            )
        ],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[{"name": "m", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x2000",
                value=_deferred_unknown(info2),
                conditions=[],
            )
        ],
    )
    analysis1.deferred_calls = {
        placeholder1: info1
    }
    analysis2.deferred_calls = {
        placeholder2: info2
    }

    result = abstract_recursive_calls(analysis1, analysis2, debug=False)

    assert result.applied is True
    assert len(result.matches) == 1
    left_value = result.analysis1.returns[0].value
    right_value = result.analysis2.returns[0].value
    assert left_value.expr_type == ExpressionType.PARAMETER
    assert right_value.expr_type == ExpressionType.PARAMETER
    assert left_value.name == right_value.name


def test_recursive_abstraction_rejects_unknown_targets_via_call_target_expression():
    callback1 = _param("callback", 0, size=8)
    callback2 = _param("fn", 0, size=8)
    placeholder1 = "call_out_of_scope:left#0"
    placeholder2 = "call_out_of_scope:right#0"
    info1 = DeferredCallInfo(
        placeholder1,
        CallTargetRef.unknown(),
        [_param("lhs", 1), _param("rhs", 2)],
        call_target_expr=callback1,
        sequence=0,
    )
    info2 = DeferredCallInfo(
        placeholder2,
        CallTargetRef.unknown(),
        [_param("a", 1), _param("b", 2)],
        call_target_expr=callback2,
        sequence=0,
    )

    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "callback", "index": 0, "data_type": "void *", "size": 8},
            {"name": "lhs", "index": 1, "data_type": "int", "size": 4},
            {"name": "rhs", "index": 2, "data_type": "int", "size": 4},
        ],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(info1), conditions=[])],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "fn", "index": 0, "data_type": "void *", "size": 8},
            {"name": "a", "index": 1, "data_type": "int", "size": 4},
            {"name": "b", "index": 2, "data_type": "int", "size": 4},
        ],
        returns=[ReturnInfo(address="0x2000", value=_deferred_unknown(info2), conditions=[])],
    )
    analysis1.deferred_calls = {placeholder1: info1}
    analysis2.deferred_calls = {placeholder2: info2}

    result = abstract_recursive_calls(analysis1, analysis2, debug=False)

    assert result.applied is False
    assert result.matches == []


def test_recursive_abstraction_rewrites_deferred_unknowns_inside_return_guards_only():
    n1 = _param("n", 0)
    n2 = _param("m", 0)
    placeholder1 = "call_out_of_scope:left#0"
    placeholder2 = "call_out_of_scope:right#0"
    info1 = DeferredCallInfo(
        placeholder1,
        _self_recursive_target("left"),
        [Expression.binary_op("INT_SUB", n1, _const(1))],
        sequence=0,
    )
    info2 = DeferredCallInfo(
        placeholder2,
        _self_recursive_target("right"),
        [Expression.binary_op("INT_SUB", n2, _const(1))],
        sequence=0,
    )
    deferred_guard1 = Condition(
        Expression.binary_op("INT_NOTEQUAL", _deferred_unknown(info1), _const(0)),
    )
    deferred_guard2 = Condition(
        Expression.binary_op("INT_NOTEQUAL", _deferred_unknown(info2), _const(0)),
    )
    opaque_guard = Condition(Expression.unknown("phi_circular"))

    analysis1 = create_mock_analysis(
        "left",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(1),
                conditions=[deferred_guard1, opaque_guard],
            )
        ],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[{"name": "m", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x2000",
                value=_const(1),
                conditions=[deferred_guard2, opaque_guard],
            )
        ],
    )
    analysis1.deferred_calls = {placeholder1: info1}
    analysis2.deferred_calls = {placeholder2: info2}

    result = abstract_recursive_calls(analysis1, analysis2, debug=False)

    assert result.applied is True
    left_conditions = result.analysis1.returns[0].conditions
    right_conditions = result.analysis2.returns[0].conditions
    assert "summary_rec_" in left_conditions[0].expression.to_string()
    assert left_conditions[0].expression.to_string() == right_conditions[0].expression.to_string()
    assert left_conditions[1].expression.expr_type == ExpressionType.UNKNOWN
    assert left_conditions[1].expression.name == "phi_circular"


def test_recursive_abstraction_debug_reports_empty_deferred_calls(capsys):
    analysis1 = create_mock_analysis("left")
    analysis2 = create_mock_analysis("right")

    result = abstract_recursive_calls(analysis1, analysis2, debug=True)

    assert result.applied is False
    output = capsys.readouterr().out
    assert "no compatible deferred-call matches" in output
    assert "left_deferred_calls=0 right_deferred_calls=0" in output


def test_recursive_abstraction_debug_reports_argument_mismatch_for_shared_target(capsys):
    n1 = _param("n", 0)
    n2 = _param("m", 0)
    callback1 = _param("callback", 1, size=8)
    callback2 = _param("fn", 1, size=8)
    placeholder1 = "call_out_of_scope:left#0"
    placeholder2 = "call_out_of_scope:right#0"
    info1 = DeferredCallInfo(
        placeholder1,
        CallTargetRef.unknown(),
        [Expression.binary_op("INT_SUB", n1, _const(1))],
        call_target_expr=callback1,
        sequence=0,
    )
    info2 = DeferredCallInfo(
        placeholder2,
        CallTargetRef.unknown(),
        [Expression.binary_op("INT_SUB", n2, _const(2))],
        call_target_expr=callback2,
        sequence=0,
    )

    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "n", "index": 0, "data_type": "int", "size": 4},
            {"name": "callback", "index": 1, "data_type": "void *", "size": 8},
        ],
        returns=[ReturnInfo(address="0x1000", value=_deferred_unknown(info1), conditions=[])],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "m", "index": 0, "data_type": "int", "size": 4},
            {"name": "fn", "index": 1, "data_type": "void *", "size": 8},
        ],
        returns=[ReturnInfo(address="0x2000", value=_deferred_unknown(info2), conditions=[])],
    )
    analysis1.deferred_calls = {placeholder1: info1}
    analysis2.deferred_calls = {placeholder2: info2}

    result = abstract_recursive_calls(analysis1, analysis2, debug=True)

    assert result.applied is False
    output = capsys.readouterr().out
    assert "shared_targets=0" in output


def test_deferred_call_abstraction_rewrites_matching_sqrt_returns_to_summary_call_params():
    x1 = _param("x", 0, size=8)
    x2 = _param("y", 0, size=8)
    info1 = DeferredCallInfo(
        "sqrt@0x1000",
        CallTargetRef.from_name("sqrt", is_external=True, library_name="libm"),
        [x1],
        sequence=0,
    )
    info2 = DeferredCallInfo(
        "sqrt@0x2000",
        CallTargetRef.from_name("sqrt", is_external=True, library_name="libm"),
        [x2],
        sequence=0,
    )
    analysis1 = _analysis_with_deferred_value("left", info1)
    analysis2 = _analysis_with_deferred_value("right", info2)
    analysis1.return_abi_facts = _production_return_abi_facts()
    analysis2.return_abi_facts = _production_return_abi_facts()
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(
        analysis1,
        analysis2,
        assume_fp_non_nan=True,
        debug=False,
    )

    assert result.applied is True
    assert len(result.matches) == 1
    assert result.matches[0].summary_name.startswith("summary_call_")
    left_value = result.analysis1.returns[0].value
    right_value = result.analysis2.returns[0].value
    assert left_value.expr_type == ExpressionType.PARAMETER
    assert right_value.expr_type == ExpressionType.PARAMETER
    assert left_value.name == right_value.name
    assert any(param.get("synthetic_pure_call_summary") for param in result.analysis1.parameters)
    assert result.analysis1.return_abi_facts == analysis1.return_abi_facts
    assert result.analysis2.return_abi_facts == analysis2.return_abi_facts
    assert result.analysis1.return_abi_facts is not analysis1.return_abi_facts
    assert result.analysis2.return_abi_facts is not analysis2.return_abi_facts
    left_width = _production_width_seed(result.analysis1, "left")
    right_width = _production_width_seed(result.analysis2, "right")
    abi_assessment = assess_return_abi_pair(
        result.analysis1,
        result.analysis2,
        left_width,
        right_width,
        build_pair_return_observation_seed(left_width, right_width),
    )
    assert not abi_assessment.left_seed.malformed_slots
    assert not abi_assessment.right_seed.malformed_slots
    evidence = result.matches[0].match_evidence["left"]
    assert evidence["effect_class"] == "pure_return"
    assert evidence["domain_policy"]["fp_non_nan"] is True
    assert evidence["abi_return_width_bits"] == 64
    assert evidence["abi_return_type_policy"] == "fp64"
    assert evidence["callee_identity_policy"]["status"] == "external_library_function"


def test_deferred_call_abstraction_requires_fp_non_nan_domain_for_sqrt():
    info1 = DeferredCallInfo("sqrt@0x1000", _external_sqrt_target(), [_param("x", 0, size=8)], sequence=0)
    info2 = DeferredCallInfo("sqrt@0x2000", _external_sqrt_target(), [_param("y", 0, size=8)], sequence=0)
    analysis1 = _analysis_with_deferred_value("left", info1)
    analysis2 = _analysis_with_deferred_value("right", info2)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=False)

    assert result.applied is False


def test_deferred_call_abstraction_rejects_name_only_sqrt_without_library_provenance():
    info1 = DeferredCallInfo("sqrt@0x1000", CallTargetRef.from_name("sqrt"), [_param("x", 0, size=8)], sequence=0)
    info2 = DeferredCallInfo("sqrt@0x2000", CallTargetRef.from_name("sqrt"), [_param("y", 0, size=8)], sequence=0)
    analysis1 = _analysis_with_deferred_value("left", info1)
    analysis2 = _analysis_with_deferred_value("right", info2)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=True)

    assert result.applied is False
    assert info1.effect_class == "unknown_effect"


def test_deferred_call_abstraction_rejects_external_sqrt_without_library_scope():
    info1 = DeferredCallInfo("sqrt@0x1000", CallTargetRef.from_name("sqrt", is_external=True), [_param("x", 0, size=8)], sequence=0)
    info2 = DeferredCallInfo("sqrt@0x2000", CallTargetRef.from_name("sqrt", is_external=True), [_param("y", 0, size=8)], sequence=0)
    analysis1 = _analysis_with_deferred_value("left", info1)
    analysis2 = _analysis_with_deferred_value("right", info2)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=True)

    assert result.applied is False
    assert info1.effect_class == "unknown_effect"


def test_deferred_call_abstraction_rejects_forced_pure_external_sqrt_without_library_scope():
    info1 = DeferredCallInfo(
        "sqrt@0x1000",
        CallTargetRef.from_name("sqrt", is_external=True),
        [_param("x", 0, size=8)],
        sequence=0,
        effect_class="pure_return",
    )
    info2 = DeferredCallInfo(
        "sqrt@0x2000",
        CallTargetRef.from_name("sqrt", is_external=True),
        [_param("y", 0, size=8)],
        sequence=0,
        effect_class="pure_return",
    )
    analysis1 = _analysis_with_deferred_value("left", info1)
    analysis2 = _analysis_with_deferred_value("right", info2)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=True)

    assert result.applied is False


def test_deferred_call_abstraction_rejects_sqrt_when_errno_or_fenv_is_observed():
    info1 = DeferredCallInfo("sqrt@0x1000", _external_sqrt_target(), [_param("x", 0, size=8)], sequence=0)
    info2 = DeferredCallInfo("sqrt@0x2000", _external_sqrt_target(), [_param("y", 0, size=8)], sequence=0)
    analysis1 = _analysis_with_deferred_value("left", info1)
    analysis2 = _analysis_with_deferred_value("right", info2)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    errno_result = abstract_recursive_calls(
        analysis1,
        analysis2,
        assume_fp_non_nan=True,
        observes_errno=True,
    )
    fenv_result = abstract_recursive_calls(
        analysis1,
        analysis2,
        assume_fp_non_nan=True,
        observes_fenv=True,
    )

    assert errno_result.applied is False
    assert fenv_result.applied is False


def test_deferred_call_abstraction_rejects_local_sqrt_replacement_target():
    target = CallTargetRef.from_name("sqrt", entry_offset=0x5000, is_external=False)
    info1 = DeferredCallInfo("sqrt@0x1000", target, [_param("x", 0, size=8)], sequence=0)
    info2 = DeferredCallInfo("sqrt@0x2000", target, [_param("y", 0, size=8)], sequence=0)
    analysis1 = _analysis_with_deferred_value("left", info1)
    analysis2 = _analysis_with_deferred_value("right", info2)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=True)

    assert result.applied is False
    assert info1.effect_class == "unknown_effect"


def test_deferred_call_abstraction_allows_external_sqrt_thunk_target():
    target = CallTargetRef.from_name(
        "sqrt",
        entry_offset=0x5000,
        is_external=False,
        is_thunk=True,
        thunked_is_external=True,
        thunked_library_name="libm",
    )
    info1 = DeferredCallInfo("sqrt@0x1000", target, [_param("x", 0, size=8)], sequence=0)
    info2 = DeferredCallInfo("sqrt@0x2000", target, [_param("y", 0, size=8)], sequence=0)
    analysis1 = _analysis_with_deferred_value("left", info1)
    analysis2 = _analysis_with_deferred_value("right", info2)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=True)

    assert result.applied is True
    assert result.matches[0].match_evidence["left"]["callee_identity_policy"]["status"] == "external_library_thunk"


def test_deferred_call_abstraction_rejects_sqrt_different_same_typed_parameter_ordinal():
    info1 = DeferredCallInfo("sqrt@0x1000", _external_sqrt_target(), [_param("x", 0, size=8)], sequence=0)
    info2 = DeferredCallInfo("sqrt@0x2000", _external_sqrt_target(), [_param("y", 1, size=8)], sequence=0)
    parameters = [
        {"name": "x", "index": 0, "data_type": "double", "size": 8},
        {"name": "y", "index": 1, "data_type": "double", "size": 8},
    ]
    analysis1 = _analysis_with_deferred_value("left", info1, parameters=parameters)
    analysis2 = _analysis_with_deferred_value("right", info2, parameters=parameters)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=True)

    assert result.applied is False


def test_deferred_call_abstraction_uses_policy_width_for_unknown_sqrt_usage_width():
    info1 = DeferredCallInfo("sqrt@0x1000", _external_sqrt_target(), [_param("x", 0, size=8)], sequence=0)
    info2 = DeferredCallInfo("sqrt@0x2000", _external_sqrt_target(), [_param("y", 0, size=8)], sequence=0)
    analysis1 = _analysis_with_deferred_value("left", info1, value_size=0)
    analysis2 = _analysis_with_deferred_value("right", info2, value_size=0)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=True)

    assert result.applied is True
    assert result.matches[0].summary_size == 8
    assert result.analysis1.returns[0].value.size == 8


def test_deferred_call_abstraction_rejects_side_effecting_printf():
    info1 = DeferredCallInfo("printf@0x1000", CallTargetRef.from_name("printf"), [_param("fmt", 0, size=8)], sequence=0)
    info2 = DeferredCallInfo("printf@0x2000", CallTargetRef.from_name("printf"), [_param("fmt2", 0, size=8)], sequence=0)
    analysis1 = _analysis_with_deferred_value("left", info1, value_size=4)
    analysis2 = _analysis_with_deferred_value("right", info2, value_size=4)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=True)

    assert result.applied is False
    assert info1.effect_class == "side_effecting"


def test_deferred_call_abstraction_rejects_sqrt_abi_width_mismatch():
    info1 = DeferredCallInfo("sqrt@0x1000", _external_sqrt_target(), [_param("x", 0, size=8)], sequence=0)
    info2 = DeferredCallInfo("sqrt@0x2000", _external_sqrt_target(), [_param("y", 0, size=8)], sequence=0)
    analysis1 = _analysis_with_deferred_value("left", info1, value_size=8)
    analysis2 = _analysis_with_deferred_value("right", info2, value_size=4)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=True)

    assert result.applied is False


def test_deferred_call_abstraction_rejects_sqrt_guard_mismatch():
    guard1 = Condition(Expression.binary_op("INT_EQUAL", _param("flag", 1), _const(1)))
    guard2 = Condition(Expression.binary_op("INT_EQUAL", _param("flag", 1), _const(2)))
    info1 = DeferredCallInfo("sqrt@0x1000", _external_sqrt_target(), [_param("x", 0, size=8)], sequence=0)
    info2 = DeferredCallInfo("sqrt@0x2000", _external_sqrt_target(), [_param("y", 0, size=8)], sequence=0)
    analysis1 = _analysis_with_deferred_value("left", info1, condition=guard1)
    analysis2 = _analysis_with_deferred_value("right", info2, condition=guard2)
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}
    analysis2.deferred_calls = {info2.deferred_call_ref.stable_key(): info2}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=True)

    assert result.applied is False


def test_deferred_call_abstraction_rejects_one_sided_deferred_call():
    info1 = DeferredCallInfo("sqrt@0x1000", _external_sqrt_target(), [_param("x", 0, size=8)], sequence=0)
    analysis1 = _analysis_with_deferred_value("left", info1)
    analysis2 = create_mock_analysis(
        "right",
        parameters=[{"name": "y", "index": 0, "data_type": "double", "size": 8}],
        returns=[ReturnInfo(address="0x2000", value=_param("y", 0, size=8), conditions=[])],
    )
    analysis1.deferred_calls = {info1.deferred_call_ref.stable_key(): info1}

    result = abstract_recursive_calls(analysis1, analysis2, assume_fp_non_nan=True)

    assert result.applied is False


def test_checker_uses_recursive_abstraction_stage_after_pairwise_unknown():
    checker = EquivalenceChecker(debug=False)
    analysis1 = create_mock_analysis("left")
    analysis2 = create_mock_analysis("right")

    pairwise_unknown = create_mock_result(None)
    pairwise_unknown.stage_path = []
    pairwise_unknown.type_fix_result = TypeFixResult()
    abstract_equiv = create_mock_result(True)
    abstract_equiv.stage_path = []
    abstract_equiv.type_fix_result = TypeFixResult()

    calls = []

    def fake_check(self, a1, a2, *args, force_strategy=None, **kwargs):
        calls.append((a1, a2, force_strategy))
        if len(calls) == 1:
            return pairwise_unknown
        return abstract_equiv

    checker.check = MethodType(fake_check, checker)

    def fake_recursive_stage(*args, **kwargs):
        return abstract_equiv

    checker._run_recursive_abstraction_stage = Mock(side_effect=fake_recursive_stage)

    result = checker._run_stage_plan(
        analysis1,
        analysis2,
        "bin1",
        "bin2",
        False,
        type_fix_result=TypeFixResult(),
        retry_count=0,
        original_signature1=None,
        original_signature2=None,
    )

    assert result is abstract_equiv
    checker._run_recursive_abstraction_stage.assert_called_once()
    assert StageID.S_ABSTRACT_RECURSIVE_SUMMARY.value in result.stage_path


def test_checker_skips_recursive_abstraction_stage_when_no_match_exists():
    checker = EquivalenceChecker(debug=False)
    analysis1 = create_mock_analysis("left")
    analysis2 = create_mock_analysis("right")

    pairwise_unknown = create_mock_result(None)
    pairwise_unknown.stage_path = []
    pairwise_unknown.type_fix_result = TypeFixResult()
    monolithic_unknown = create_mock_result(None)
    monolithic_unknown.stage_path = []
    monolithic_unknown.type_fix_result = TypeFixResult()

    sequence = [pairwise_unknown, monolithic_unknown]

    def fake_check(self, a1, a2, *args, force_strategy=None, **kwargs):
        return sequence.pop(0)

    checker.check = MethodType(fake_check, checker)
    checker._run_recursive_abstraction_stage = Mock(return_value=None)

    result = checker._run_stage_plan(
        analysis1,
        analysis2,
        "bin1",
        "bin2",
        False,
        type_fix_result=TypeFixResult(),
        retry_count=0,
        original_signature1=None,
        original_signature2=None,
    )

    assert result is monolithic_unknown
    assert StageID.S_ABSTRACT_RECURSIVE_SUMMARY.value not in result.stage_path
    assert result.stage_path == [
        StageID.S_PAIRWISE.value,
        StageID.S_MONOLITHIC_FALLBACK.value,
    ]
