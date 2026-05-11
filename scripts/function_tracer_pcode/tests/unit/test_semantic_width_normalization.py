# -*- coding: utf-8 -*-
"""Semantic-width normalization regressions."""

from dataclasses import replace

from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.formula.types import ExtraVariableInfo
from scripts.function_tracer_pcode.equivalence.formula.variable import (
    ExtensionType,
    ExtraVariableAnalysis,
    ParameterFragmentInfo,
    VariableClassification,
)
from scripts.function_tracer_pcode.equivalence.semantic_width import (
    align_return_value_extension_surfaces,
    normalize_analysis_semantic_width,
    return_extension_surface_diagnostic_metadata,
    return_extension_surface_evidence_key,
)
from scripts.function_tracer_pcode.equivalence.param_semantics import (
    ParameterSemanticHint,
    infer_parameter_semantics,
)
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
    lower_post_state_expression_for_smt_if_needed,
    post_state_read_expression_for_location,
)
from scripts.function_tracer_pcode.model import (
    Condition,
    ComparisonSurface,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    LocationBaseRef,
    PcodeOpRef,
    ReductionAccumulatorProof,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReturnInfo,
    StorageInfo,
)


def _param(name: str, size: int, *, index: int | None = None, storage_info=None) -> Expression:
    if index is None:
        if name.startswith("param_") and name[6:].isdigit():
            index = int(name[6:]) - 1
        elif name == "count":
            index = 0
        else:
            index = -1
    return Expression(
        ExpressionType.PARAMETER,
        name=name,
        value=index,
        size=size,
        storage_info=storage_info,
    )


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


def _readonly_sum_expr(
    result_size: int,
    proof_result_size: int | None = None,
    return_value_mnemonics: tuple[str, ...] = (),
    return_value_input_size: int | None = None,
    return_value_output_size: int | None = None,
    include_return_value_output_size: bool = True,
    element_size: int = 4,
) -> Expression:
    pointer = Expression.parameter("base", index=0, data_type="int *", size=8)
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    proven_result_size = proof_result_size or result_size
    extension_input_size = max(1, int(return_value_input_size or 4))
    extension_output_size = max(1, int(return_value_output_size or result_size))
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count,
        result_size=proven_result_size,
        stride=element_size,
        element_size=element_size,
        start_offset=12,
        start_index=3,
        index_scale=element_size,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=element_size),
            ReadonlyReductionTermRef(byte_offset=element_size * 2, access_size=element_size),
        ),
        return_value_op_refs=tuple(
            PcodeOpRef(
                address_offset=0x5000 + index,
                seq_time=index,
                seq_order=0,
                mnemonic=mnemonic,
                input_sizes=(extension_input_size,),
                output_size=extension_output_size if include_return_value_output_size else None,
            )
            for index, mnemonic in enumerate(return_value_mnemonics)
        ),
        return_region_value_proven=True,
    )
    runtime_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        stride=element_size,
        element_size=element_size,
        result_size=proof.result_size,
        start_offset=12,
        accumulator_proof=proof,
    )
    return Expression.intrinsic(
        "READONLY_SUM",
        [pointer, count],
        size=result_size,
        runtime_ref=runtime_ref,
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


def test_normalize_analysis_does_not_apply_semantic_width_hint_by_no_index_name():
    count = Expression(ExpressionType.PARAMETER, name="count", size=8)
    analysis = FunctionReturnAnalysis(
        function_name="name_only_count_hint_like",
        entry_point="0x1000",
        parameters=[
            {"name": "count", "data_type": "long", "size": 8, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[],
                value=_binary("INT_XOR", count, count, 8),
            )
        ],
        return_type="long",
    )

    normalized = normalize_analysis_semantic_width(
        analysis,
        hints={0: ParameterSemanticHint(32, "signed")},
    )

    value = normalized.returns[0].value
    assert value.operator == "INT_XOR"
    assert value.size == 8
    assert all(getattr(operand, "operator", None) != "SUBPIECE" for operand in value.operands)


def test_normalize_analysis_does_not_rebind_name_inferred_hint_to_indexed_parameter():
    count = Expression(ExpressionType.PARAMETER, name="count", size=8)
    masked = _binary("INT_AND", count, _const(0xFFFFFFFF, 8), 8)
    analysis = FunctionReturnAnalysis(
        function_name="name_inferred_hint_should_not_gain_index_identity",
        entry_point="0x1000",
        parameters=[
            {"name": "count", "data_type": "long", "size": 8, "index": 0, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[],
                value=_binary("INT_XOR", masked, masked, 8),
            )
        ],
        return_type="long",
    )

    normalized = normalize_analysis_semantic_width(analysis)

    value = normalized.returns[0].value
    assert value.operator == "INT_XOR"
    assert value.size == 8
    assert all(getattr(operand, "operator", None) == "INT_AND" for operand in value.operands)


def test_normalize_analysis_applies_semantic_width_hint_by_parameter_storage_identity():
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a0",
        base_register_name="a0",
        size=8,
        size_bits=64,
    )
    left = Expression.parameter("stale_count", size=8, storage_info=storage)
    right = Expression.parameter("stale_count", size=8, storage_info=storage)
    analysis = FunctionReturnAnalysis(
        function_name="storage_backed_count_hint_like",
        entry_point="0x1000",
        parameters=[
            {
                "name": "count",
                "data_type": "long",
                "size": 8,
                "index": 0,
                "is_signed": True,
                "storage": storage,
            },
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[],
                value=_binary("INT_XOR", left, right, 8),
            )
        ],
        return_type="long",
    )

    normalized = normalize_analysis_semantic_width(
        analysis,
        hints={0: ParameterSemanticHint(32, "signed")},
    )

    value = normalized.returns[0].value
    assert value.operator == "INT_XOR"
    assert value.size == 4
    assert value.operands[0].operator == "SUBPIECE"
    assert value.operands[1].operator == "SUBPIECE"


def test_normalize_analysis_applies_semantic_width_hint_from_serialized_parameter_storage():
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a0",
        base_register_name="a0",
        size=8,
        size_bits=64,
    )
    left = Expression.parameter("stale_count", size=8, storage_info=storage)
    right = Expression.parameter("stale_count", size=8, storage_info=storage)
    analysis = FunctionReturnAnalysis(
        function_name="serialized_storage_backed_count_hint_like",
        entry_point="0x1000",
        parameters=[
            {
                "name": "count",
                "data_type": "long",
                "size": 8,
                "index": 0,
                "is_signed": True,
                "storage": storage.to_dict(),
            },
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[],
                value=_binary("INT_XOR", left, right, 8),
            )
        ],
        return_type="long",
    )

    normalized = normalize_analysis_semantic_width(
        analysis,
        hints={0: ParameterSemanticHint(32, "signed")},
    )

    value = normalized.returns[0].value
    assert value.operator == "INT_XOR"
    assert value.size == 4
    assert value.operands[0].operator == "SUBPIECE"
    assert value.operands[1].operator == "SUBPIECE"


def test_normalize_analysis_keeps_inferred_storage_hints_when_index_hints_are_passed():
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a0",
        base_register_name="a0",
        size=8,
        size_bits=64,
    )
    masked = _binary(
        "INT_AND",
        Expression.parameter("stale_count", size=8, storage_info=storage),
        _const(0xFFFFFFFF, 8),
        8,
    )
    plain = Expression.parameter("stale_count", size=8, storage_info=storage)
    analysis = FunctionReturnAnalysis(
        function_name="storage_only_hint_even_with_by_index_callers",
        entry_point="0x1000",
        parameters=[
            {
                "name": "count",
                "data_type": "long",
                "size": 8,
                "is_signed": True,
                "storage": storage,
            },
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[],
                value=_binary("INT_XOR", masked, plain, 8),
            )
        ],
        return_type="long",
    )

    by_index_hints = infer_parameter_semantics(analysis)
    assert by_index_hints == {}

    normalized = normalize_analysis_semantic_width(analysis, hints=by_index_hints)

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


def test_readonly_reduction_contract_does_not_locally_narrow_wide_return_surface():
    analysis = FunctionReturnAnalysis(
        function_name="wide_readonly_sum",
        entry_point="0x5000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x5000", value=_const(4294966996, 8)),
            ReturnInfo(address="0x5004", value=_readonly_sum_expr(4)),
            ReturnInfo(address="0x5008", value=_readonly_sum_expr(8, proof_result_size=8)),
        ],
        return_type="ulong",
    )

    normalized = normalize_analysis_semantic_width(analysis)
    surface = normalized.get_comparison_surface()

    assert surface.explicit_bit_width == 64
    assert "source" not in surface.evidence


def test_readonly_reduction_contract_keeps_wide_surface_when_constant_has_high_bits():
    analysis = FunctionReturnAnalysis(
        function_name="wide_constant_readonly_sum",
        entry_point="0x5000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x5000", value=_const(0x1_0000_0001, 8)),
            ReturnInfo(address="0x5008", value=_readonly_sum_expr(8, proof_result_size=8)),
        ],
        return_type="ulong",
    )

    normalized = normalize_analysis_semantic_width(analysis)

    assert normalized.get_comparison_surface().explicit_bit_width == 64


def test_return_extension_surface_alignment_rejects_64bit_high_bit_difference():
    left = FunctionReturnAnalysis(
        function_name="wide_extension_readonly_sum",
        entry_point="0x5000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x5000", value=_const(4294966996, 8)),
            ReturnInfo(
                address="0x5008",
                value=_readonly_sum_expr(8, proof_result_size=8, return_value_mnemonics=("INT_ZEXT",)),
            ),
        ],
        return_type="ulong",
    )
    right = FunctionReturnAnalysis(
        function_name="narrow_readonly_sum",
        entry_point="0x6000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x6000", value=_const(0xFFFFFFFFFFFFFED4, 8)),
            ReturnInfo(address="0x6008", value=_readonly_sum_expr(4)),
        ],
        return_type="ulong",
    )

    aligned_left, aligned_right = align_return_value_extension_surfaces(left, right)

    left_surface = aligned_left.get_comparison_surface()
    right_surface = aligned_right.get_comparison_surface()
    assert left_surface.explicit_bit_width == 64
    assert right_surface.explicit_bit_width == 64
    assert "source" not in left_surface.evidence
    assert "source" not in right_surface.evidence


def test_return_extension_surface_alignment_refuses_mixed_zext_sext_evidence():
    left = FunctionReturnAnalysis(
        function_name="wide_zext_readonly_sum",
        entry_point="0x5000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x5000", value=_const(4294966996, 8)),
            ReturnInfo(
                address="0x5008",
                value=_readonly_sum_expr(8, proof_result_size=8, return_value_mnemonics=("INT_ZEXT",)),
            ),
        ],
        return_type="ulong",
    )
    right = FunctionReturnAnalysis(
        function_name="wide_sext_readonly_sum",
        entry_point="0x6000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x6000", value=_const(0xFFFFFFFFFFFFFED4, 8)),
            ReturnInfo(
                address="0x6008",
                value=_readonly_sum_expr(8, proof_result_size=8, return_value_mnemonics=("INT_SEXT",)),
            ),
        ],
        return_type="ulong",
    )

    aligned_left, aligned_right = align_return_value_extension_surfaces(left, right)

    assert aligned_left.get_comparison_surface().explicit_bit_width == 64
    assert aligned_right.get_comparison_surface().explicit_bit_width == 64


def test_return_extension_surface_metadata_is_diagnostic_not_semantic_key():
    valid_surface = ComparisonSurface(
        kind="return_value",
        explicit_bit_width=32,
        use_sign_extension=False,
        evidence={
            "source": "cross_side_return_extension_surface",
            "extension_surface_bit_width": 32,
            "return_width_sign_artifact": True,
            "extension_surface_coercion": "equal_width_or_object_proven_extract",
            "extension_surface_extension_kind": "INT_ZEXT",
            "extension_surface_source_bit_widths": (32,),
        },
    )
    stale_surface = replace(
        valid_surface,
        evidence={
            **valid_surface.evidence,
            "extension_surface_source_bit_widths": "32",
        },
    )
    detached_surface = replace(
        valid_surface,
        explicit_bit_width=64,
    )

    assert return_extension_surface_evidence_key(valid_surface) is None
    assert return_extension_surface_evidence_key(stale_surface) is None
    assert return_extension_surface_evidence_key(detached_surface) is None
    assert return_extension_surface_diagnostic_metadata(valid_surface) == {
        "source": "cross_side_return_extension_surface",
        "surface_bits": 32,
        "coercion": "equal_width_or_object_proven_extract",
        "extension_kind": "INT_ZEXT",
        "source_widths": (32,),
        "return_width_sign_artifact": True,
    }
    assert return_extension_surface_diagnostic_metadata(stale_surface) is None
    assert return_extension_surface_diagnostic_metadata(detached_surface) is None


def test_return_extension_surface_alignment_refuses_wide_readonly_without_extension_op():
    left = FunctionReturnAnalysis(
        function_name="true_wide_readonly_sum",
        entry_point="0x5000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x5000", value=_const(4294966996, 8)),
            ReturnInfo(address="0x5008", value=_readonly_sum_expr(8, proof_result_size=8)),
        ],
        return_type="ulong",
    )
    right = FunctionReturnAnalysis(
        function_name="narrow_readonly_sum",
        entry_point="0x6000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x6000", value=_const(0xFFFFFFFFFFFFFED4, 8)),
            ReturnInfo(address="0x6008", value=_readonly_sum_expr(4)),
        ],
        return_type="ulong",
    )

    aligned_left, aligned_right = align_return_value_extension_surfaces(left, right)

    assert aligned_left.get_comparison_surface().explicit_bit_width == 64
    assert aligned_right.get_comparison_surface().explicit_bit_width == 64


def test_return_extension_surface_alignment_refuses_sub32_value_without_extension_proof():
    left = FunctionReturnAnalysis(
        function_name="sub32_value",
        entry_point="0x5000",
        parameters=[{"name": "narrow", "data_type": "short", "size": 2, "index": 0}],
        returns=[
            ReturnInfo(address="0x5000", value=_const(4294966996, 8)),
            ReturnInfo(address="0x5004", value=Expression.parameter("narrow", index=0, data_type="short", size=2)),
        ],
        return_type="ulong",
    )
    right = FunctionReturnAnalysis(
        function_name="narrow_readonly_sum",
        entry_point="0x6000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x6000", value=_const(0xFFFFFFFFFFFFFED4, 8)),
            ReturnInfo(address="0x6008", value=_readonly_sum_expr(4)),
        ],
        return_type="ulong",
    )

    aligned_left, aligned_right = align_return_value_extension_surfaces(left, right)

    assert aligned_left.get_comparison_surface().explicit_bit_width == 64
    assert aligned_right.get_comparison_surface().explicit_bit_width == 64


def test_return_extension_surface_alignment_uses_actual_readonly_extension_source_width():
    left = FunctionReturnAnalysis(
        function_name="wide_readonly_sum_32bit_accumulator_16bit_loads",
        entry_point="0x5000",
        parameters=[
            {"name": "base", "data_type": "short *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(
                address="0x5008",
                value=_readonly_sum_expr(
                    8,
                    proof_result_size=4,
                    return_value_mnemonics=("INT_ZEXT",),
                    return_value_input_size=4,
                    element_size=2,
                ),
            ),
        ],
        return_type="ulong",
    )
    right = FunctionReturnAnalysis(
        function_name="narrow_16bit_readonly_sum",
        entry_point="0x6000",
        parameters=[
            {"name": "base", "data_type": "short *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x6008", value=_readonly_sum_expr(2, proof_result_size=2, element_size=2)),
        ],
        return_type="ulong",
    )

    aligned_left, aligned_right = align_return_value_extension_surfaces(left, right)

    assert aligned_left.get_comparison_surface().explicit_bit_width == 64
    assert aligned_right.get_comparison_surface().explicit_bit_width == 16
    assert "source" not in aligned_left.get_comparison_surface().evidence


def test_return_extension_surface_alignment_requires_readonly_extension_output_width():
    left = FunctionReturnAnalysis(
        function_name="wide_readonly_missing_output_width",
        entry_point="0x5000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(
                address="0x5008",
                value=_readonly_sum_expr(
                    8,
                    proof_result_size=8,
                    return_value_mnemonics=("INT_ZEXT",),
                    return_value_input_size=4,
                    include_return_value_output_size=False,
                ),
            ),
        ],
        return_type="ulong",
    )
    right = FunctionReturnAnalysis(
        function_name="narrow_readonly_sum",
        entry_point="0x6000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x6008", value=_readonly_sum_expr(4)),
        ],
        return_type="ulong",
    )

    aligned_left, aligned_right = align_return_value_extension_surfaces(left, right)

    assert aligned_left.get_comparison_surface().explicit_bit_width == 64
    assert aligned_right.get_comparison_surface().explicit_bit_width == 32
    assert "source" not in aligned_left.get_comparison_surface().evidence


def test_return_extension_surface_alignment_rejects_same_width_readonly_extension_op():
    left = FunctionReturnAnalysis(
        function_name="wide_readonly_same_width_zext",
        entry_point="0x5000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(
                address="0x5008",
                value=_readonly_sum_expr(
                    8,
                    proof_result_size=8,
                    return_value_mnemonics=("INT_ZEXT",),
                    return_value_input_size=4,
                    return_value_output_size=4,
                ),
            ),
        ],
        return_type="ulong",
    )
    right = FunctionReturnAnalysis(
        function_name="narrow_readonly_sum",
        entry_point="0x6000",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0},
            {"name": "count", "data_type": "int", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x6008", value=_readonly_sum_expr(4)),
        ],
        return_type="ulong",
    )

    aligned_left, aligned_right = align_return_value_extension_surfaces(left, right)

    assert aligned_left.get_comparison_surface().explicit_bit_width == 64
    assert aligned_right.get_comparison_surface().explicit_bit_width == 32
    assert "source" not in aligned_left.get_comparison_surface().evidence


def test_normalize_analysis_parameter_metadata_uses_index_before_unique_stale_name():
    stale_name_param = Expression.parameter("count", index=1, data_type="long", size=8)
    analysis = FunctionReturnAnalysis(
        function_name="semantic_width_index_wins",
        entry_point="0x7000",
        parameters=[
            {"name": "count", "index": 0, "size": 8, "data_type": "long"},
            {"name": "actual_count", "index": 1, "size": 4, "data_type": "int"},
        ],
        returns=[ReturnInfo(address="0x7000", value=stale_name_param, conditions=[])],
        return_type="int",
    )

    normalized = normalize_analysis_semantic_width(analysis)
    rewritten_param = normalized.returns[0].value

    assert rewritten_param.value == 1
    assert rewritten_param.size == 4
    assert rewritten_param.data_type == "int"


def test_normalize_analysis_parameter_metadata_does_not_infer_index_from_position():
    stale_index_param = Expression.parameter("stale_count", index=1, data_type="short", size=2)
    analysis = FunctionReturnAnalysis(
        function_name="semantic_width_no_positional_index",
        entry_point="0x7000",
        parameters=[
            {"name": "base", "size": 8, "data_type": "int *"},
            {"name": "count", "size": 4, "data_type": "int"},
        ],
        returns=[ReturnInfo(address="0x7000", value=stale_index_param, conditions=[])],
        return_type="int",
    )

    normalized = normalize_analysis_semantic_width(analysis)
    rewritten_param = normalized.returns[0].value

    assert rewritten_param.value == 1
    assert rewritten_param.name == "stale_count"
    assert rewritten_param.size == 2
    assert rewritten_param.data_type == "short"


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
