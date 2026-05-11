# -*- coding: utf-8 -*-

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.equivalence.formula.types import ExtraVariableInfo
from scripts.function_tracer_pcode.equivalence.formula.variable import (
    ExtensionType,
    ExtraVariableAnalysis,
    ParameterFragmentInfo,
    VariableClassification,
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    FunctionReturnAnalysis,
    LocationBaseRef,
    READONLY_SUM_OPCODE,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReturnInfo,
)


def _param(name: str) -> Expression:
    index = -1
    if name.startswith("param_") and name[6:].isdigit():
        index = int(name[6:]) - 1
    return Expression.parameter(name, index=index, size=4, data_type="int")


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size=size)


def _binary(op: str, left: Expression, right: Expression) -> Expression:
    return Expression.binary_op(op, left, right)


def _fragment_var(name: str) -> Expression:
    return Expression.variable(name, size=4)


def _wide_param(fragment_name: str, param_name: str) -> Expression:
    return _binary(
        "INT_OR",
        _binary("INT_LEFT", _fragment_var(fragment_name), _const(32, size=8)),
        _param(param_name),
    )


def _readonly_sum_value(
    name: str,
    *,
    stride: int,
    element_size: int,
    signed_counter: bool = True,
    semantic_witnesses=(),
) -> Expression:
    return Expression.intrinsic(
        "READONLY_SUM",
        [Expression.parameter(name, index=0, size=8), Expression.parameter("param_2", index=1, size=4)],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=LocationBaseRef.parameter(name, index=0),
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=stride,
            element_size=element_size,
            result_size=4,
            signed_counter=signed_counter,
            semantic_witnesses=tuple(semantic_witnesses),
        ),
        opcode=READONLY_SUM_OPCODE,
    )


def _fragment_info(fragment_name: str, parent_name: str, parent_index: int) -> ExtraVariableInfo:
    fragment_info = ParameterFragmentInfo(
        fragment_name=fragment_name,
        fragment_bit_width=32,
        parent_param_name=parent_name,
        parent_param_index=parent_index,
        parent_param_bit_width=32,
        extension_type=ExtensionType.SIGN_EXTEND,
        bit_offset_in_base=0,
        bit_length=32,
        base_register_name=f"a{parent_index}",
        base_register_size_bits=64,
    )
    analysis = ExtraVariableAnalysis(
        name=fragment_name,
        bit_width=32,
        classification=VariableClassification.PARAMETER_FRAGMENT,
        fragment_info=fragment_info,
        reason="test fragment",
    )
    return ExtraVariableInfo(
        original_name=fragment_name,
        smt_name=f"{fragment_name}_2",
        bit_width=32,
        analysis=analysis,
    )


def test_pairwise_rewrites_mips64_parameter_fragments_before_contradiction_check():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    selector_is_zero = _binary(
        "INT_EQUAL",
        _binary("INT_SLESS", _param("param_2"), _param("param_1")),
        _const(0),
    )
    cutoff = _binary(
        "INT_ADD",
        _binary("INT_MULT", _param("param_2"), _const(3)),
        _const(1),
    )

    case1 = ReturnCase(
        index=1,
        conditions=[
            Condition(_binary("INT_SLESSEQUAL", cutoff, _param("param_3"))),
            Condition(selector_is_zero),
        ],
        value_expr=_const(0),
        return_info=ReturnInfo(address="0x1", value=_const(0), conditions=[], branch_index=1),
        return_type="int",
    )

    wide_cutoff = Expression.unary_op("INT_SEXT", cutoff)
    wide_cutoff.size = 8
    case2 = ReturnCase(
        index=2,
        conditions=[
            Condition(
                _binary(
                    "INT_SLESSEQUAL",
                    _wide_param("in_a0_hi", "param_1"),
                    _wide_param("in_a1_hi", "param_2"),
                )
            ),
            Condition(
                _binary(
                    "INT_SLESS",
                    _wide_param("in_a2_hi", "param_3"),
                    wide_cutoff,
                )
            ),
        ],
        value_expr=_const(1),
        return_info=ReturnInfo(address="0x2", value=_const(1), conditions=[], branch_index=2),
        return_type="int",
    )

    strategy._rewrite_cases_with_parameter_fragments(
        [case2],
        [
            _fragment_info("in_a0_hi", "param_1", 0),
            _fragment_info("in_a1_hi", "param_2", 1),
            _fragment_info("in_a2_hi", "param_3", 2),
        ],
    )

    for cond in case2.conditions:
        assert "in_a" not in cond.to_string()
    assert case2.conditions[0].to_string() == "(int(param_1) <= int(param_2))"
    assert case2.conditions[1].to_string() == "(int(param_3) < int(((param_2 * 3) + 1)))"


def test_pairwise_check_normalizes_fragment_backed_nonzero_before_case_pruning():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    analysis1 = FunctionReturnAnalysis(
        function_name="fc_widen_then_bias_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1001",
                value=_const(0),
                conditions=[
                    Condition(_binary("INT_NOTEQUAL", _param("param_2"), _const(0)), negated=True)
                ],
            )
        ],
        return_type="int",
    )

    analysis2 = FunctionReturnAnalysis(
        function_name="fc_widen_then_bias_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1002",
                value=_const(1),
                conditions=[
                    Condition(
                        _binary(
                            "INT_NOTEQUAL",
                            _wide_param("in_a1_hi", "param_2"),
                            _const(0, size=8),
                        )
                    )
                ],
            )
        ],
        return_type="long",
    )

    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [_fragment_info("in_a1_hi", "param_2", 1)],
    }

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    assert "return_case_coverage_inconclusive" in analysis1.analysis_notes
    assert "return_case_coverage_inconclusive" in analysis2.analysis_notes
    strategy.solver_runner.run_sequential.assert_not_called()


def test_pairwise_extracts_cases_from_solver_view_consistently():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    raw_left = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "data_type": "int", "size": 8, "index": 0, "is_signed": True}],
        returns=[ReturnInfo(address="0x1001", value=_const(0), conditions=[])],
        return_type="int",
    )
    raw_right = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "data_type": "int", "size": 8, "index": 0, "is_signed": True}],
        returns=[ReturnInfo(address="0x1002", value=_const(1), conditions=[])],
        return_type="int",
    )
    solver_left = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "data_type": "int", "size": 4, "index": 0, "is_signed": True}],
        returns=[ReturnInfo(address="0x1001", value=_const(0), conditions=[])],
        return_type="int",
    )
    solver_right = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "data_type": "int", "size": 4, "index": 0, "is_signed": True}],
        returns=[ReturnInfo(address="0x1002", value=_const(1), conditions=[])],
        return_type="int",
    )

    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    with patch(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.normalize_analysis_semantic_width",
        side_effect=[solver_left, solver_right],
    ), patch.object(strategy, "_extract_return_cases", side_effect=[[], []]) as extract_cases:
        result = strategy.check(raw_left, raw_right)

    assert result.is_equivalent is None
    assert result.total_pairs == 0
    assert extract_cases.call_args_list[0].args[0] is solver_left
    assert extract_cases.call_args_list[1].args[0] is solver_right


def test_pairwise_short_circuits_semantically_equal_readonly_reductions():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "long", "size": 8, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": True},
        ],
        returns=[ReturnInfo(address="0x1001", value=_readonly_sum_value("param_1", stride=4, element_size=4), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "undefined8 *", "size": 8, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "uint", "size": 4, "index": 1, "is_signed": True},
        ],
        returns=[ReturnInfo(address="0x1002", value=_readonly_sum_value("param_1", stride=4, element_size=4), conditions=[])],
        return_type="int",
    )

    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_pairwise_does_not_short_circuit_different_readonly_reduction_shapes():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left = _readonly_sum_value("param_1", stride=4, element_size=4, signed_counter=True)
    right = _readonly_sum_value("param_1", stride=16, element_size=8, signed_counter=False)

    assert strategy._readonly_reduction_values_equivalent(left, right) is False


def test_pairwise_short_circuits_semantically_equal_readonly_reductions_via_witnesses():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_witnesses = (
        ReadonlyReductionWitness(
            exact_count=1,
            terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
        ),
        ReadonlyReductionWitness(
            exact_count=2,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ),
        ),
        ReadonlyReductionWitness(
            exact_count=3,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        ),
        ReadonlyReductionWitness(
            exact_count=4,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                ReadonlyReductionTermRef(byte_offset=12, access_size=4),
            ),
        ),
    )
    right_witnesses = left_witnesses[:3]
    left = _readonly_sum_value(
        "param_1",
        stride=4,
        element_size=4,
        signed_counter=True,
        semantic_witnesses=left_witnesses,
    )
    right = _readonly_sum_value(
        "param_1",
        stride=16,
        element_size=8,
        signed_counter=False,
        semantic_witnesses=right_witnesses,
    )

    assert strategy._readonly_reduction_values_equivalent(left, right) is True
