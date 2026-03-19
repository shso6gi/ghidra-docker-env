# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.memory_resolver import (
    collect_memory_bit_widths_from_analysis,
    concretize_readonly_loads,
)
from scripts.function_tracer_pcode.equivalence.arch.mips64 import MIPS64Handler
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.model import Condition, Expression, FunctionReturnAnalysis, ReturnInfo


def _param(name: str, size: int = 4, is_signed: bool = True, index: int = 0):
    return {"name": name, "size": size, "is_signed": is_signed, "index": index}


def test_formula_builder_declares_memory_arrays_for_memory_returns():
    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x0",
        parameters=[_param("p", size=8)],
        returns=[
            ReturnInfo(
                address="0x1",
                conditions=[],
                value=Expression.memory(Expression.parameter("p", 0, size=8), size=4),
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x0",
        parameters=[_param("q", size=8)],
        returns=[
            ReturnInfo(
                address="0x2",
                conditions=[],
                value=Expression.memory(Expression.parameter("q", 0, size=8), size=4),
            )
        ],
        return_type="int",
    )

    builder = FormulaBuilder(debug=False, exclude_ub=False)
    formula = builder.build_equivalence_formula_extended(analysis1, analysis2).formula

    assert "(declare-const mem32 (Array (_ BitVec 64) (_ BitVec 32)))" in formula
    assert "(select mem32 p_1)" in formula
    assert "(select mem32 q_2)" in formula
    assert collect_memory_bit_widths_from_analysis(analysis1) == [32]


def test_mips64_handler_detects_spurious_same_pattern_extension_violation():
    handler = MIPS64Handler(debug=False)
    counterexample = {"param_1_1": 0x400000000002, "param_1_2": 0x400000000002}
    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x0",
        parameters=[{"name": "param_1", "data_type": "long", "size": 8, "is_signed": True}],
        returns=[],
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x0",
        parameters=[{"name": "param_1", "data_type": "long", "size": 8, "is_signed": True}],
        returns=[],
    )

    handler._analyze_parameter_usage = lambda analysis: {"param_1": ("signed", 32)}

    constraints = handler.detect_spurious_counterexample(
        counterexample,
        analysis1,
        analysis2,
        is_mips64_1=True,
        is_mips64_2=True,
    )

    assert constraints == {"param_1_1": ("signed", 32), "param_1_2": ("signed", 32)}


def test_memory_resolver_concretizes_small_readonly_jump_table():
    param = Expression.parameter("param_1", 0, size=8)
    index_expr = Expression.unary_op(
        "INT_SEXT",
        Expression.binary_op("SUBPIECE", param, Expression.constant(0, 4)),
    )
    index_expr.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.variable("PTR_00112058", size=8),
        Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_MULT", index_expr, Expression.constant(4, 8)),
            Expression.constant(5024, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", param, Expression.constant(4, 8)),
        False,
    )

    table = {
        0x00112058 + 5024 + 0: 1,
        0x00112058 + 5024 + 4: 1,
        0x00112058 + 5024 + 8: 2,
        0x00112058 + 5024 + 12: 2,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=8, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [1, 1, 2, 2]


def test_memory_resolver_concretizes_jump_table_when_additive_index_is_wrapped_by_mul_one():
    param = Expression.parameter("param_1", 0, size=8)
    subpiece = Expression.binary_op("SUBPIECE", param, Expression.constant(0, 4))
    subpiece.size = 4
    index_expr = Expression.unary_op("INT_SEXT", subpiece)
    index_expr.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.variable("PTR_00112058", size=8),
        Expression.binary_op(
            "INT_MULT",
            Expression.constant(1, 8),
            Expression.binary_op(
                "INT_ADD",
                Expression.constant(5024, 8),
                Expression.binary_op("INT_MULT", index_expr, Expression.constant(4, 8)),
            ),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", param, Expression.constant(4, 8)),
        False,
    )

    table = {
        0x00112058 + 5024 + 0: 1,
        0x00112058 + 5024 + 4: 1,
        0x00112058 + 5024 + 8: 2,
        0x00112058 + 5024 + 12: 2,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=8, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [1, 1, 2, 2]


def test_memory_resolver_concretizes_mips_pic_jump_table_using_image_base_fallback():
    param = Expression.parameter("param_1", 0, size=8)
    subpiece = Expression.binary_op("SUBPIECE", param, Expression.constant(0, 4))
    subpiece.size = 4
    index_expr = Expression.unary_op("INT_SEXT", subpiece)
    index_expr.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.variable("PTR_00112058", size=8),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op(
                "INT_ADD",
                Expression.binary_op("INT_MULT", index_expr, Expression.constant(4, 8)),
                Expression.constant(0x13A0, 8),
            ),
            Expression.constant(1, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", param, Expression.constant(4, 8)),
        False,
    )

    image_base = 0x00100000
    table = {
        image_base + 0x13A0 + 0: 1,
        image_base + 0x13A0 + 4: 1,
        image_base + 0x13A0 + 8: 2,
        image_base + 0x13A0 + 12: 2,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=8, is_signed=False)],
        lambda addr, size: table.get(addr),
        image_base=image_base,
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [1, 1, 2, 2]


def test_memory_resolver_accepts_unsigned_lessequal_range_conditions():
    param = Expression.parameter("param_1", 0, size=4)
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.constant(0, 8), Expression.constant(0x1009EC, 8)),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op("INT_MULT", Expression.unary_op("INT_ZEXT", param), Expression.constant(1, 8)),
            Expression.constant(4, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESSEQUAL", param, Expression.constant(5, 4)),
        False,
    )

    table = {
        0x1009EC + 0: 5,
        0x1009EC + 4: 7,
        0x1009EC + 8: 11,
        0x1009EC + 12: 13,
        0x1009EC + 16: 17,
        0x1009EC + 20: 19,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=4, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [5, 7, 11, 13, 17, 19]


def test_memory_resolver_accepts_negated_less_condition_as_upper_bound():
    param = Expression.parameter("param_1", 0, size=4)
    index = Expression.unary_op("INT_ZEXT", param)
    index.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.constant(0, 8), Expression.constant(0x1009EC, 8)),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op("INT_MULT", index, Expression.constant(1, 8)),
            Expression.constant(4, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", Expression.constant(5, 4), param),
        True,
    )

    table = {
        0x1009EC + 0: 5,
        0x1009EC + 4: 7,
        0x1009EC + 8: 11,
        0x1009EC + 12: 13,
        0x1009EC + 16: 17,
        0x1009EC + 20: 19,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=4, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [5, 7, 11, 13, 17, 19]


def test_memory_resolver_concretizes_mips_got_base_symbol_with_address_suffix():
    param = Expression.parameter("param_1", 0, size=8)
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.variable("PTR___DT_MIPS_BASE_ADDRESS_120011050", size=8),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op(
                "INT_ADD",
                Expression.binary_op("INT_MULT", param, Expression.constant(4, 8)),
                Expression.constant(0xF00, 8),
            ),
            Expression.constant(1, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", param, Expression.constant(6, 8)),
        False,
    )

    got_slot = 0x120011050
    image_base = 0x120000000
    table = {
        got_slot: image_base,
        image_base + 0xF00 + 0: 5,
        image_base + 0xF00 + 4: 7,
        image_base + 0xF00 + 8: 11,
        image_base + 0xF00 + 12: 13,
        image_base + 0xF00 + 16: 17,
        image_base + 0xF00 + 20: 19,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=8, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [5, 7, 11, 13, 17, 19]
