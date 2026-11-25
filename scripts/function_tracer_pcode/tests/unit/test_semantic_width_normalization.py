# -*- coding: utf-8 -*-
"""Semantic-width normalization regressions."""

from dataclasses import replace

from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.semantics.semantic_width import (
    align_return_value_extension_surfaces,
    normalize_analysis_semantic_width,
)
from scripts.function_tracer_pcode.semantics.param_semantics import (
    ParameterSemanticHint,
    infer_parameter_semantics,
)
from scripts.function_tracer_pcode.analysis.effects.summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
)
from scripts.function_tracer_pcode.core import (
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
from scripts.function_tracer_pcode.proof.formula.input_correspondence import build_input_correspondence_set
from scripts.function_tracer_pcode.core.render_smt import SMT_SEMANTICS_REFUSALS
from scripts.function_tracer_pcode.core.semantic_snapshot import traverse_semantic_graph
import pytest


def _leaf_names(expr):
    """式の graph の PARAMETER / VARIABLE の名前（描画に依らない構造の確認用）。"""
    return {
        getattr(node, "name", None)
        for node in traverse_semantic_graph(expr).entry_order
        if getattr(getattr(node, "expr_type", None), "name", None) in {"PARAMETER", "VARIABLE"}
    }


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


def test_normalize_analysis_keeps_widened_signed_division_at_the_wide_width():
    """Issue #167: 除算・剰余の狭めは有効な規則ではない。

    ``SUBPIECE(sdiv(sext(a), sext(b)), 0) == sdiv(a, b)`` は幅に依らない恒等式だが、
    production 幅（64→32）で実 lowering の certificate が得られない（z3 が決着しない、
    ``tests/fixtures/issue167/README.md``）。未証明の規則は有効にしないので、広い除算を
    そのまま描く（意味は元式と同じ）。周囲の ring 演算の狭めは恒等規則なので残る。
    """
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

    assert "(bvsdiv param_1 param_2)" not in value_smt
    assert "((_ extract 31 0) (bvsdiv ((_ sign_extend 32) param_1) ((_ sign_extend 32) param_2)))" in value_smt


def test_normalize_analysis_keeps_wide_xor_at_full_width_despite_narrow_hints():
    """64 bit の XOR を 32 bit へ裸で狭めない（Issue #167, v5 §4.6）。

    修正前は hint だけで ``p2 ^ p3``（64 bit）を ``low32(p2) ^ low32(p3)``（32 bit）へ
    書き換えていた。式の sort が変わり、全幅の値も保存しない。hint は
    ``SUBPIECE(p2 ^ p3, 0)`` のように下位 bit だけを読む文脈でだけ効く。
    """
    wide_xor = _binary("INT_XOR", _param("param_2", 8), _param("param_3", 8), 8)
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
                value=wide_xor,
            ),
            ReturnInfo(address="0x1004", conditions=[], value=_subpiece(wide_xor, 4)),
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

    wide = normalized.returns[0].value
    assert wide.operator == "INT_XOR"
    assert wide.size == 8
    assert all(operand.expr_type == ExpressionType.PARAMETER for operand in wide.operands)
    low = normalized.returns[1].value
    assert low.operator == "INT_XOR"
    assert low.size == 4
    assert [operand.operator for operand in low.operands] == ["SUBPIECE", "SUBPIECE"]


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
                # 下位 32 bit だけを読む文脈（恒等規則の対象）で hint の解決を見る。
                value=_subpiece(_binary("INT_XOR", left, right, 8), 4),
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
                # 下位 32 bit だけを読む文脈（恒等規則の対象）で hint の解決を見る。
                value=_subpiece(_binary("INT_XOR", left, right, 8), 4),
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
                # mask の use が storage 単位の hint を作る。値は下位 32 bit だけを読む
                # 文脈（恒等規則の対象）に置く。
                conditions=[Condition(_binary("INT_NOTEQUAL", masked, _const(0, 8), 1))],
                value=_subpiece(_binary("INT_XOR", plain, plain, 8), 4),
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


def test_normalize_analysis_keeps_fragment_backed_widening_patterns():
    """``(in_a0_hi << 32) | param_1`` を ``sext(param_1)`` へ畳まない（Issue #167）。

    修正前は fragment の ``is_signed`` ラベルだけで畳み、SDIV まで 32 bit へ狭めて
    いた。上位断片が同じ引数の拡張であることは信頼済み IEE が無ければ言えない
    （独立した上位 bit では値が変わる）ので、式を保つ。
    """
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

    normalized = normalize_analysis_semantic_width(analysis)
    value = normalized.returns[0].value
    cond = normalized.returns[0].conditions[0].expression

    # 断片の形を保つ（sext へ畳まない）
    assert {"in_a0_hi", "in_a1_hi"} <= _leaf_names(value)
    assert "in_a1_hi" in _leaf_names(cond)
    # Issue #298: ``(hi << 32) | lo`` の lo（32 bit）を 64 bit の INT_OR でどう伸ばすかは式に無いので、
    # 描画は推測せず拒否する（以前は宣言の符号で伸ばし方を選んでいた）
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        value.to_smt()
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        normalized.returns[0].conditions[0].to_smt()


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

    formula = builder.build_equivalence_formula_extended(narrow_analysis, widened_analysis, input_correspondence=build_input_correspondence_set(narrow_analysis, widened_analysis)).formula

    # 除算の狭めは無効（上の test を参照）。広い除算のまま lowering する。
    assert "(bvsdiv param_1_2 param_2_2)" not in formula
    assert "((_ extract 31 0) (bvsdiv ((_ sign_extend 32) param_1_2) ((_ sign_extend 32) param_2_2)))" in formula
    assert "(distinct param_2_2 (_ bv0 32))" in formula


def test_normalize_analysis_keeps_fragment_backed_pointer_reads_unassumed():
    """store 値の pointer ``(in_a0_hi << 32) | param_1`` を ``ext(param_1)`` と仮定しない。

    修正前は fragment tag から ``sext(param_1)`` へ畳んでいた（Issue #167）。
    """
    params = [
        {"name": "param_1", "data_type": "int *", "size": 4, "index": 0, "is_signed": True},
        {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": False},
        {"name": "param_3", "data_type": "int", "size": 4, "index": 2, "is_signed": False},
    ]
    loc0 = CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=0, size=4)
    effect_value = _mem_addr(_wide_param("in_a0_hi", "param_1"))
    analysis = FunctionReturnAnalysis(
        function_name="lr_loop_with_side_effect",
        entry_point="0x1000",
        parameters=params,
        returns=[ReturnInfo(address="0x1000", conditions=[], value=_const(0, 4))],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["param_1", "param_2", "param_3"],
            effects=[StoreEffect(location=loc0, value=effect_value, conditions=[], order_key=1)],
        ),
    )

    normalized = normalize_analysis_semantic_width(analysis)
    stored = normalized.effect_summary.effects[0].value

    # 断片の形を保つ（ext(param_1) と仮定しない）
    assert {"in_a0_hi", "param_1"} <= _leaf_names(stored)
    # Issue #298: lo の伸ばし方が式に無いので、描画は推測せず拒否する
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        stored.to_smt()


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

    assert "(distinct param_1 (_ bv0 32))" in cond_smt
    # Issue #298: 32 bit の pointer の引数を 64 bit の番地の加算でどう伸ばすか（ABI によって zero /
    # sign のどちらもある）は式に無いので、描画は推測せず拒否する（以前は zero 拡張していた）
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        normalized.returns[0].value.to_smt()


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

    # Issue #298: 32 bit の pointer の引数を 64 bit の番地の加算で伸ばす形は、伸ばし方（ABI によって
    # zero / sign）が式に無いので、式を作らず拒否する（以前は zero 拡張を推測していた）
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        builder.build_equivalence_formula_extended(
            analysis1, analysis2, input_correspondence=build_input_correspondence_set(analysis1, analysis2),
        )


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


def test_return_extension_surface_alignment_accepts_high_zero_piece_to_64bit_surface():
    low_value = _param("param_1", 8, index=0)
    wide_zero_piece = _binary("PIECE", _const(0, 8), low_value, 16)
    left = FunctionReturnAnalysis(
        function_name="wide_zero_piece_return",
        entry_point="0x5000",
        parameters=[{"name": "param_1", "data_type": "double", "size": 8, "index": 0}],
        returns=[
            ReturnInfo(address="0x5000", value=wide_zero_piece),
            ReturnInfo(address="0x5004", value=_binary("PIECE", _const(0, 8), _unary("FLOAT_NEG", low_value, 8), 16)),
        ],
        return_type="undefined1[16]",
    )
    right = FunctionReturnAnalysis(
        function_name="narrow_double_return",
        entry_point="0x6000",
        parameters=[{"name": "param_1", "data_type": "double", "size": 8, "index": 0}],
        returns=[
            ReturnInfo(address="0x6000", value=low_value),
            ReturnInfo(address="0x6004", value=_unary("FLOAT_NEG", low_value, 8)),
        ],
        return_type="double",
    )

    aligned_left, aligned_right = align_return_value_extension_surfaces(left, right)

    left_surface = aligned_left.get_comparison_surface()
    right_surface = aligned_right.get_comparison_surface()
    assert left_surface.explicit_bit_width == 64
    assert right_surface.explicit_bit_width == 64
    assert left_surface.evidence["source"] == "cross_side_return_extension_surface"
    assert left_surface.evidence["extension_surface_extension_kind"] == "INT_ZEXT"
    assert left_surface.evidence["extension_surface_source_bit_widths"] == (64,)


def test_return_extension_surface_alignment_rejects_nonzero_high_piece():
    low_value = _param("param_1", 8, index=0)
    left = FunctionReturnAnalysis(
        function_name="wide_nonzero_piece_return",
        entry_point="0x5000",
        parameters=[{"name": "param_1", "data_type": "double", "size": 8, "index": 0}],
        returns=[ReturnInfo(address="0x5000", value=_binary("PIECE", _const(1, 8), low_value, 16))],
        return_type="undefined1[16]",
    )
    right = FunctionReturnAnalysis(
        function_name="narrow_double_return",
        entry_point="0x6000",
        parameters=[{"name": "param_1", "data_type": "double", "size": 8, "index": 0}],
        returns=[ReturnInfo(address="0x6000", value=low_value)],
        return_type="double",
    )

    aligned_left, aligned_right = align_return_value_extension_surfaces(left, right)

    assert aligned_left.get_comparison_surface().explicit_bit_width == 128
    assert aligned_right.get_comparison_surface().explicit_bit_width == 64
    assert "source" not in aligned_left.get_comparison_surface().evidence


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


def test_normalize_analysis_keeps_unsigned_guard_unsigned_despite_explicit_signed_hint():
    """unsigned 比較を signed 比較へ変えない（Issue #167, v5 §4.6）。

    修正前は explicit signed hint だけで ``3 <u count`` を ``3 <s count`` にしていた。
    ``count = 0x80000000`` で結果が変わる（sign 拡張の前提があっても同じ）。
    """
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

    assert "(bvult (_ bv3 32) count)" in cond_smt
    assert "bvslt" not in cond_smt


