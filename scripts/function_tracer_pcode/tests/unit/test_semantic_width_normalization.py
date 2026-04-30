# -*- coding: utf-8 -*-
"""Semantic-width normalization regressions."""

from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.formula.types import ExtraVariableInfo
from scripts.function_tracer_pcode.equivalence.formula.variable import (
    ExtensionType,
    ExtraVariableAnalysis,
    ParameterFragmentInfo,
    VariableClassification,
)
from scripts.function_tracer_pcode.equivalence.semantic_width import (
    normalize_analysis_semantic_width,
)
from scripts.function_tracer_pcode.equivalence.param_semantics import ParameterSemanticHint
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
    lower_post_state_expression_for_smt_if_needed,
    post_state_read_expression_for_location,
)
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    LocationBaseRef,
    ReturnInfo,
)


def _param(name: str, size: int) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=size)


def _const(value: int, size: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _binary(op: str, left: Expression, right: Expression, size: int) -> Expression:
    return Expression(
        ExpressionType.BINARY_OP,
        operator=op,
        operands=[left, right],
        size=size,
    )


def _unary(op: str, operand: Expression, size: int) -> Expression:
    return Expression(
        ExpressionType.UNARY_OP,
        operator=op,
        operands=[operand],
        size=size,
    )


def _subpiece(expr: Expression, size: int, offset: int = 0) -> Expression:
    return Expression(
        ExpressionType.BINARY_OP,
        operator="SUBPIECE",
        operands=[expr, _const(offset, 8)],
        size=size,
    )


def _var(name: str, size: int) -> Expression:
    return Expression(ExpressionType.VARIABLE, name=name, size=size)


def _wide_param(fragment_name: str, param_name: str) -> Expression:
    return _binary(
        "INT_OR",
        _binary("INT_LEFT", _var(fragment_name, 4), _const(32, 8), 8),
        _param(param_name, 4),
        8,
    )


def _mem_addr(addr: Expression, size: int = 4) -> Expression:
    return Expression(ExpressionType.MEMORY, operands=[addr], size=size)


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


def test_normalize_analysis_collapses_widened_signed_division_back_to_32bit():
    widened_div = _binary(
        "INT_SDIV",
        _unary("INT_SEXT", _param("param_1", 4), 8),
        _unary("INT_SEXT", _param("param_2", 4), 8),
        8,
    )
    widened_value = _unary(
        "INT_SEXT",
        _binary(
            "INT_ADD",
            _subpiece(widened_div, 4),
            _param("param_3", 4),
            4,
        ),
        8,
    )
    analysis = FunctionReturnAnalysis(
        function_name="fc_widen_then_bias_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "int", "size": 4, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": True},
            {"name": "param_3", "data_type": "int", "size": 4, "index": 2, "is_signed": True},
        ],
        returns=[ReturnInfo(address="0x1000", conditions=[], value=widened_value)],
        return_type="long",
    )

    normalized = normalize_analysis_semantic_width(analysis)
    value_smt = normalized.returns[0].value.to_smt()

    assert "(bvsdiv param_1 param_2)" in value_smt
    assert "((_ extract 31 0) (bvsdiv ((_ sign_extend 32) param_1) ((_ sign_extend 32) param_2)))" not in value_smt


def test_normalize_analysis_rewrites_raw_wide_xor_of_semantically_narrow_params():
    analysis = FunctionReturnAnalysis(
        function_name="fc_wide_xor_wrapper_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "long", "size": 8, "index": 0, "is_signed": False},
            {"name": "param_2", "data_type": "long", "size": 8, "index": 1, "is_signed": True},
            {"name": "param_3", "data_type": "long", "size": 8, "index": 2, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[Condition(_binary("INT_NOTEQUAL", _binary("INT_AND", _param("param_1", 8), _const(1, 8), 8), _const(0, 8), 1))],
                value=_binary("INT_XOR", _param("param_2", 8), _param("param_3", 8), 8),
            )
        ],
        return_type="long",
    )

    normalized = normalize_analysis_semantic_width(
        analysis,
        hints={
            1: ParameterSemanticHint(32, "signed"),
            2: ParameterSemanticHint(32, "signed"),
        },
    )

    value = normalized.returns[0].value
    assert value.operator == "INT_XOR"
    assert value.size == 4
    assert value.operands[0].operator == "SUBPIECE"
    assert value.operands[1].operator == "SUBPIECE"


def test_normalize_analysis_collapses_fragment_backed_widening_patterns():
    wide_div = _binary(
        "INT_SDIV",
        _wide_param("in_a0_hi", "param_1"),
        _wide_param("in_a1_hi", "param_2"),
        8,
    )
    widened_value = _unary(
        "INT_SEXT",
        _binary(
            "INT_ADD",
            _subpiece(wide_div, 4),
            _param("param_3", 4),
            4,
        ),
        8,
    )
    analysis = FunctionReturnAnalysis(
        function_name="fc_widen_then_bias_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "int", "size": 4, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": True},
            {"name": "param_3", "data_type": "int", "size": 4, "index": 2, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    Condition(
                        _binary(
                            "INT_NOTEQUAL",
                            _wide_param("in_a1_hi", "param_2"),
                            _const(0, 8),
                            1,
                        )
                    )
                ],
                value=widened_value,
            )
        ],
        return_type="long",
    )

    normalized = normalize_analysis_semantic_width(
        analysis,
        fragment_infos=[
            _fragment_info("in_a0_hi", "param_1", 0),
            _fragment_info("in_a1_hi", "param_2", 1),
        ],
    )
    value_smt = normalized.returns[0].value.to_smt()
    cond_smt = normalized.returns[0].conditions[0].to_smt()

    assert "in_a0_hi" not in value_smt
    assert "in_a1_hi" not in value_smt
    assert "(bvsdiv param_1 param_2)" in value_smt
    assert "((_ sign_extend 32) param_2)" not in cond_smt
    assert "(distinct param_2 (_ bv0 32))" in cond_smt


def test_normalize_analysis_deduplicates_wide_nonzero_and_masked_nonzero_conditions():
    masked = _binary("INT_AND", _param("param_1", 8), _const(0xFFFFFFFF, 8), 8)
    analysis = FunctionReturnAnalysis(
        function_name="wide_guard_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "ulong", "size": 8, "index": 0, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    Condition(_binary("INT_NOTEQUAL", _param("param_1", 8), _const(0, 8), 1)),
                    Condition(_binary("INT_NOTEQUAL", masked, _const(0, 8), 1)),
                ],
                value=masked,
            )
        ],
        return_type="long",
    )

    normalized = normalize_analysis_semantic_width(analysis)

    assert len(normalized.returns[0].conditions) == 1
    cond_smt = normalized.returns[0].conditions[0].to_smt()
    assert "(_ bv0 32)" in cond_smt
    assert "param_1" in cond_smt


def test_formula_builder_applies_semantic_width_normalization_before_lowering():
    builder = FormulaBuilder(debug=False)
    widened_analysis = FunctionReturnAnalysis(
        function_name="fc_widen_then_bias_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "int", "size": 4, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": True},
            {"name": "param_3", "data_type": "int", "size": 4, "index": 2, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[Condition(_binary("INT_NOTEQUAL", _unary("INT_SEXT", _param("param_2", 4), 8), _const(0, 8), 1))],
                value=_unary(
                    "INT_SEXT",
                    _binary(
                        "INT_ADD",
                        _subpiece(
                            _binary(
                                "INT_SDIV",
                                _unary("INT_SEXT", _param("param_1", 4), 8),
                                _unary("INT_SEXT", _param("param_2", 4), 8),
                                8,
                            ),
                            4,
                        ),
                        _param("param_3", 4),
                        4,
                    ),
                    8,
                ),
            )
        ],
        return_type="long",
    )
    narrow_analysis = FunctionReturnAnalysis(
        function_name="fc_widen_then_bias_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "int", "size": 4, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": True},
            {"name": "param_3", "data_type": "int", "size": 4, "index": 2, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[Condition(_binary("INT_NOTEQUAL", _param("param_2", 4), _const(0, 4), 1))],
                value=_binary("INT_ADD", _binary("INT_SDIV", _param("param_1", 4), _param("param_2", 4), 4), _param("param_3", 4), 4),
            )
        ],
        return_type="int",
    )

    formula = builder.build_equivalence_formula_extended(narrow_analysis, widened_analysis).formula

    assert "(bvsdiv param_1_2 param_2_2)" in formula
    assert "((_ extract 31 0) (bvsdiv ((_ sign_extend 32) param_1_2) ((_ sign_extend 32) param_2_2)))" not in formula
    assert "(distinct param_2_2 (_ bv0 32))" in formula


def test_normalize_analysis_rewrites_effect_summary_for_fragment_backed_pointer_reads():
    params = [
        {"name": "param_1", "data_type": "int *", "size": 4, "index": 0, "is_signed": True},
        {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": False},
        {"name": "param_3", "data_type": "int", "size": 4, "index": 2, "is_signed": False},
    ]
    loc0 = CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=0, size=4)
    loc4 = CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=4, size=4)
    symbolic_sum = _binary(
        "INT_ADD",
        post_state_read_expression_for_location(loc0, params, symbolic=True),
        post_state_read_expression_for_location(loc4, params, symbolic=True),
        4,
    )
    analysis = FunctionReturnAnalysis(
        function_name="lr_loop_with_side_effect",
        entry_point="0x1000",
        parameters=params,
        returns=[ReturnInfo(address="0x1000", conditions=[], value=symbolic_sum)],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["param_1", "param_2", "param_3"],
            effects=[
                StoreEffect(
                    location=loc0,
                    value=_mem_addr(_wide_param("in_a0_hi", "param_1")),
                    conditions=[],
                    order_key=1,
                ),
                StoreEffect(
                    location=loc4,
                    value=_mem_addr(
                        _binary(
                            "INT_ADD",
                            _wide_param("in_a0_hi", "param_1"),
                            _const(4, 8),
                            8,
                        )
                    ),
                    conditions=[],
                    order_key=2,
                ),
            ],
        ),
    )

    normalized = normalize_analysis_semantic_width(
        analysis,
        fragment_infos=[_fragment_info("in_a0_hi", "param_1", 0)],
    )
    lowered = lower_post_state_expression_for_smt_if_needed(
        normalized.returns[0].value,
        normalized.returns[0].conditions,
        normalized.effect_summary.effects,
        normalized.parameters,
    )

    assert lowered is not None
    lowered_smt = lowered.to_smt()
    assert (
        "((_ sign_extend 32) param_1)" in lowered_smt
        or "((_ zero_extend 32) param_1)" in lowered_smt
    )
    assert "(bvadd (_ bv4 64) param_1)" not in lowered_smt
    assert "in_a0_hi" not in lowered_smt


def test_normalize_analysis_synchronizes_parameter_expr_widths_with_declared_metadata():
    mismatched_ptr = _param("param_1", 8)
    analysis = FunctionReturnAnalysis(
        function_name="lr_loop_with_side_effect",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "int *", "size": 4, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "uint", "size": 4, "index": 1, "is_signed": False},
            {"name": "param_3", "data_type": "uint", "size": 4, "index": 2, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    Condition(_binary("INT_NOTEQUAL", mismatched_ptr, _const(0, 8), 1))
                ],
                value=_binary(
                    "INT_ADD",
                    _mem_addr(mismatched_ptr),
                    _mem_addr(_binary("INT_ADD", mismatched_ptr, _const(4, 8), 8)),
                    4,
                ),
            )
        ],
        return_type="int",
    )

    normalized = normalize_analysis_semantic_width(analysis)
    cond_smt = normalized.returns[0].conditions[0].to_smt()
    value_smt = normalized.returns[0].value.to_smt()

    assert "(distinct param_1 (_ bv0 32))" in cond_smt
    assert "(select mem32 param_1)" not in value_smt
    assert "(bvadd (_ bv4 64) param_1)" not in value_smt
    assert "((_ zero_extend 32) param_1)" in value_smt


def test_formula_builder_handles_mips64_abi_param_width_mismatch_in_return_exprs():
    builder = FormulaBuilder(debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="lr_loop_with_side_effect",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "int *", "size": 4, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "uint", "size": 4, "index": 1, "is_signed": False},
            {"name": "param_3", "data_type": "uint", "size": 4, "index": 2, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[Condition(_binary("INT_NOTEQUAL", _param("param_1", 4), _const(0, 4), 1))],
                value=_binary(
                    "INT_ADD",
                    _mem_addr(_param("param_1", 4)),
                    _mem_addr(_binary("INT_ADD", _param("param_1", 4), _const(4, 8), 8)),
                    4,
                ),
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="lr_loop_with_side_effect",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "int *", "size": 4, "index": 0, "is_signed": True},
            {"name": "param_2", "data_type": "uint", "size": 4, "index": 1, "is_signed": False},
            {"name": "param_3", "data_type": "uint", "size": 4, "index": 2, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x1001",
                conditions=[Condition(_binary("INT_NOTEQUAL", _param("param_1", 8), _const(0, 8), 1))],
                value=_binary(
                    "INT_ADD",
                    _mem_addr(_param("param_1", 8)),
                    _mem_addr(_binary("INT_ADD", _param("param_1", 8), _const(4, 8), 8)),
                    4,
                ),
            )
        ],
        return_type="int",
    )

    formula = builder.build_equivalence_formula_extended(analysis1, analysis2).formula

    assert "(declare-const param_1_2 (_ BitVec 32))" in formula
    assert "(select mem32 param_1_2)" not in formula
    assert "(bvadd (_ bv4 64) param_1_2)" not in formula
    assert "((_ zero_extend 32) param_1_2)" in formula


def test_normalize_analysis_rewrites_unsigned_guard_to_signed_when_hint_is_explicit():
    count = _param("count", 4)
    analysis = FunctionReturnAnalysis(
        function_name="signed_count_tail_like",
        entry_point="0x4000",
        parameters=[
            {"name": "count", "data_type": "uint", "size": 4, "index": 0, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x4000",
                conditions=[Condition(_binary("INT_LESS", _const(3, 4), count, 1))],
                value=_const(1, 4),
            )
        ],
        return_type="int",
    )

    normalized = normalize_analysis_semantic_width(
        analysis,
        hints={0: ParameterSemanticHint(32, "signed", signedness_source="explicit")},
    )
    cond_smt = normalized.returns[0].conditions[0].to_smt()

    assert "(bvslt (_ bv3 32) count)" in cond_smt
    assert "(bvult (_ bv3 32) count)" not in cond_smt
