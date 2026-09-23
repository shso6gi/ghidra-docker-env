# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import echo_input_correspondence
from unittest.mock import Mock, patch
from scripts.function_tracer_pcode.smt import ParallelSolverRunner

from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    build_input_correspondence_set,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.core import (
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


def _solver_runner():
    runner = ParallelSolverRunner(timeout=5)
    runner.run_sequential = Mock(wraps=runner.run_sequential)
    return runner


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


def test_pairwise_keeps_mips64_parameter_fragments_uncollapsed():
    """``(in_a0_hi << 32) | param_1`` を ``sext(param_1)`` へ畳まない（Issue #167）。

    修正前は pairwise の case 前処理が fragment の ``is_signed`` ラベルだけで
    畳んでいた（normalizer と同じ規則の複製）。上位断片が同じ引数の sign 拡張で
    あることは信頼済み IEE が無ければ言えないので、式はそのまま残る。
    """
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), _solver_runner(), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "int", "size": 4, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x2",
                value=_const(1),
                conditions=[
                    Condition(
                        _binary(
                            "INT_SLESSEQUAL",
                            _wide_param("in_a0_hi", "param_1"),
                            _wide_param("in_a1_hi", "param_2"),
                        )
                    )
                ],
            )
        ],
        return_type="int",
    )

    cases = strategy._extract_return_cases(analysis)

    assert "in_a0_hi" in cases[0].conditions[0].to_string()
    assert "in_a1_hi" in cases[0].conditions[0].to_string()
    assert not hasattr(strategy, "_rewrite_cases_with_parameter_fragments")


def test_pairwise_fragment_backed_pair_is_gated_by_input_correspondence():
    """断片付き parameter の pair は、入力対応が不十分なので決着させない（Issue #167）。

    修正前は断片を ``sext(param_2)`` と仮定して case を刈り、UNSAT にしていた。
    修正後は ``in_a1_hi`` が自由な入力として残る。右側は param_2 の register を
    別名で読む（構造的な断片）ので、最終 relation は不十分で、SAT も UNSAT も
    確定に使わない。
    """
    strategy = PairwiseStrategy(FormulaBuilder(debug=False), _solver_runner(), debug=False)

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
        return_type="int",
    )

    correspondence = build_input_correspondence_set(analysis1, analysis2)
    assert not correspondence.decisive_sufficient
    assert any("structural_fragment:in_a1_hi" in ref for ref in correspondence.insufficiency_evidence())

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert any(
        "input_correspondence" in ref
        for reason in result.unknown_reasons
        for ref in (getattr(reason, "evidence_refs", None) or ())
    )


def test_pairwise_extracts_cases_from_solver_view_consistently():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), _solver_runner(), debug=False)

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
        "scripts.function_tracer_pcode.proof.strategies.pairwise.normalize_analysis_semantic_width",
        side_effect=[solver_left, solver_right],
    ), patch.object(strategy, "_extract_return_cases", side_effect=[[], []]) as extract_cases:
        result = strategy.check(raw_left, raw_right)

    assert result.is_equivalent is None
    assert result.total_pairs == 0
    assert extract_cases.call_args_list[0].args[0] is solver_left
    assert extract_cases.call_args_list[1].args[0] is solver_right


def test_pairwise_short_circuits_semantically_equal_readonly_reductions():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), _solver_runner(), debug=False)

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
    strategy.solver_runner.run_sequential.assert_called()


def test_pairwise_does_not_short_circuit_different_readonly_reduction_shapes():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), _solver_runner(), debug=False)
    left = _readonly_sum_value("param_1", stride=4, element_size=4, signed_counter=True)
    right = _readonly_sum_value("param_1", stride=16, element_size=8, signed_counter=False)

    assert strategy._readonly_reduction_values_equivalent(left, right) is False


def test_pairwise_short_circuits_semantically_equal_readonly_reductions_via_witnesses():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), _solver_runner(), debug=False)
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
