# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.memory_resolver import (
    collect_memory_bit_widths_from_analysis,
    concretize_readonly_loads,
)
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    LocationStep,
    StoreEffect,
    _resolve_call_target_name,
    _resolve_parameter_name,
    _storage_matches_parameter,
    subtract_implied_conditions,
    is_call_effect_summary_allowed,
    build_void_effect_summary_expr,
    canonicalize_location,
    canonicalize_param_location,
    canonicalize_post_state_subexpressions,
    collapse_post_state_expr_to_canonical_memory,
    collapse_pruned_post_state_memory_leaf_to_canonical_memory,
    memory_expression_for_location,
    normalize_post_state_expression,
    rewrite_loads_from_effects,
    rewrite_location_read_from_effects,
    rewrite_observed_loads_from_effects,
    summarize_store_effects,
    substitute_condition,
    substitute_location,
    _choose_effect_substitution_args,
    _recover_call_argument_expressions,
    _recover_call_argument_from_storage,
    _resolve_call_argument_expression,
    _normalize_call_argument_expression,
    EffectSummary,
)
from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.phi_resolver import ExpandedBranch as PhiExpandedBranch, PhiHandler
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixer, TypeFixerConfig
from scripts.function_tracer_pcode.equivalence.arch.mips64 import MIPS64Handler
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.model import Condition, Expression, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.model.storage import StorageInfo
from scripts.function_tracer_pcode.transform.expander import ExpressionExpander, ExpandedValue


def _param(
    name: str,
    size: int = 4,
    is_signed: bool = True,
    index: int = 0,
    storage=None,
):
    result = {"name": name, "size": size, "is_signed": is_signed, "index": index}
    if storage is not None:
        result["storage"] = storage
    return result


def _reg_storage(base_name: str, size_bytes: int = 8, register_name: str = None):
    register_name = register_name or base_name
    return {
        "is_register": True,
        "space_name": "register",
        "offset": 0,
        "size": size_bytes,
        "size_bits": size_bytes * 8,
        "register_name": register_name,
        "base_register_name": base_name,
        "base_register_offset": 0,
        "base_register_size": size_bytes,
        "base_register_size_bits": size_bytes * 8,
        "bit_offset_in_base": 0,
    }


def _stack_storage(offset: int, size_bytes: int = 4):
    return {
        "is_register": False,
        "space_name": "stack",
        "offset": offset,
        "size": size_bytes,
        "size_bits": size_bytes * 8,
    }


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


def test_memory_resolver_concretizes_direct_readonly_pointer_slot():
    load_expr = Expression.memory(
        Expression.variable("PTR_ptr_op_add_00113090", size=8),
        size=8,
    )

    table = {
        0x00113090: 0x401120,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [],
        [],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "CONSTANT"
    assert resolved.value == 0x401120


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


def test_memory_resolver_accepts_cast_wrapped_parameter_range_conditions():
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
    widened_param = Expression.unary_op("INT_ZEXT", param)
    widened_param.size = 8
    cond = Condition(
        Expression.binary_op("INT_LESS", widened_param, Expression.constant(4, 8)),
        False,
    )

    table = {
        0x1009EC + 0: 5,
        0x1009EC + 4: 7,
        0x1009EC + 8: 11,
        0x1009EC + 12: 13,
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
    assert values == [5, 7, 11, 13]


def test_memory_resolver_accepts_cast_then_zext_parameter_range_conditions():
    param = Expression.parameter("param_1", 0, size=4)
    cast_param = Expression.unary_op("CAST", param)
    cast_param.size = 4
    index = Expression.unary_op("INT_ZEXT", cast_param)
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
        Expression.binary_op("INT_LESS", index, Expression.constant(4, 8)),
        False,
    )

    table = {
        0x1009EC + 0: 5,
        0x1009EC + 4: 7,
        0x1009EC + 8: 11,
        0x1009EC + 12: 13,
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
    assert values == [5, 7, 11, 13]


def test_memory_resolver_accepts_cast_then_zext_for_signed_parameter_indices():
    param = Expression.parameter("param_1", 0, size=4)
    cast_param = Expression.unary_op("CAST", param)
    cast_param.size = 4
    index = Expression.unary_op("INT_ZEXT", cast_param)
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
        Expression.binary_op("INT_LESS", index, Expression.constant(4, 8)),
        False,
    )

    table = {
        0x1009EC + 0: 5,
        0x1009EC + 4: 7,
        0x1009EC + 8: 11,
        0x1009EC + 12: 13,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=4, is_signed=True)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [5, 7, 11, 13]


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


def test_memory_resolver_splits_load_of_phi_address_into_phi_of_loads():
    base = Expression.parameter("param_1", 0, size=8)
    addr_phi = Expression.phi(
        [
            (
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.parameter("pick_right", 1, size=4),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
                Expression.binary_op("INT_ADD", base, Expression.constant(4, 8)),
            ),
            (None, base),
        ]
    )
    addr_phi.size = 8
    load_expr = Expression.memory(addr_phi, size=4)

    resolved = concretize_readonly_loads(
        load_expr,
        [],
        [_param("param_1", size=8, is_signed=False), _param("pick_right", size=4)],
        lambda addr, size: None,
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    assert resolved.value[0][1].expr_type.name == "MEMORY"
    assert resolved.value[1][1].expr_type.name == "MEMORY"


def test_memory_resolver_splits_bool_scaled_offset_load_into_two_loads():
    base = Expression.parameter("param_1", 0, size=8)
    cond_expr = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.parameter("pick_right", 1, size=4),
        Expression.constant(0, 4),
    )
    addr_expr = Expression.binary_op(
        "INT_ADD",
        base,
        Expression.binary_op("INT_MULT", cond_expr, Expression.constant(4, 8)),
    )
    load_expr = Expression.memory(addr_expr, size=4)

    resolved = concretize_readonly_loads(
        load_expr,
        [],
        [_param("param_1", size=8, is_signed=False), _param("pick_right", size=4)],
        lambda addr, size: None,
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    first_addr = resolved.value[0][1].operands[0]
    second_addr = resolved.value[1][1].operands[0]
    assert first_addr.to_string() == "(param_1 + 4)"
    assert second_addr.to_string() == "param_1"


def test_effect_summary_rewrites_load_from_prior_store_under_same_path():
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    original = Expression.binary_op(
        "INT_ADD",
        Expression.memory(ptr, size=4),
        Expression.constant(0xFFFFFFFF, 4),
    )
    effect = StoreEffect(
        location=CanonicalLocation("ptr", 0, 4),
        value=Expression.binary_op("INT_ADD", value, Expression.constant(3, 4)),
        conditions=[
            Condition(
                Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
                False,
            )
        ],
        order_key=1,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        effect.conditions,
        [effect],
        [_param("ptr", size=8, is_signed=False), _param("value", size=4, index=1)],
    )

    assert rewritten.to_string() == "((value + 3) + 4294967295)"


def test_effect_summary_builds_synthetic_expr_for_void_writes():
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    positive = Condition(
        Expression.binary_op("INT_SLESS", Expression.constant(0, 4), value),
        False,
    )
    non_positive = positive.negate()
    effects = [
        StoreEffect(
            location=CanonicalLocation("ptr", 0, 4),
            value=value,
            conditions=[positive],
            order_key=2,
        ),
        StoreEffect(
            location=CanonicalLocation("ptr", 0, 4),
            value=Expression.unary_op("INT_2COMP", value),
            conditions=[non_positive],
            order_key=1,
        ),
    ]

    summary = build_void_effect_summary_expr(effects)

    assert summary is not None
    assert summary.expr_type.name == "BINARY_OP"
    assert summary.operator == "PIECE"


def test_effect_summary_accepts_variable_based_parameter_addresses():
    addr_expr = Expression.variable("ptr", size=8)

    location = canonicalize_param_location(
        addr_expr,
        [_param("ptr", size=8, is_signed=False)],
        size=4,
    )

    assert location == CanonicalLocation("ptr", 0, 4)


def test_effect_summary_accepts_variable_plus_constant_parameter_addresses():
    addr_expr = Expression.binary_op(
        "INT_ADD",
        Expression.variable("box", size=8),
        Expression.constant(4, 8),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("box", size=8, is_signed=False)],
        size=4,
    )

    assert location == CanonicalLocation("box", 4, 4)


def test_effect_summary_accepts_register_alias_parameter_addresses():
    addr_expr = Expression.variable(
        "saved_arg",
        size=8,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            register_name="A0",
            base_register_name="A0",
            size=8,
            size_bits=64,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=0,
        ),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("param_1", size=8, is_signed=False, storage=_reg_storage("A0"))],
        size=4,
    )

    assert location == CanonicalLocation("param_1", 0, 4)


def test_effect_summary_accepts_double_indirect_parameter_addresses():
    addr_expr = Expression.memory(
        Expression.parameter("slot", 0, size=8),
        size=8,
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("slot", size=8, is_signed=False)],
        size=4,
    )

    assert location == CanonicalLocation(
        "slot",
        0,
        4,
        steps=(LocationStep("deref", 8),),
    )


def test_memory_expression_for_location_reconstructs_double_indirect_location():
    expr = memory_expression_for_location(
        CanonicalLocation(
            "slot",
            0,
            4,
            steps=(LocationStep("deref", 8),),
        ),
        [_param("slot", size=8, is_signed=False)],
    )

    assert expr is not None
    assert expr.to_string() == "MEM[MEM[slot]]"


def test_substitute_location_accepts_register_alias_call_arguments():
    call_args = [
        Expression.variable(
            "arg_a",
            size=8,
            storage_info=StorageInfo(
                is_register=True,
                space_name="register",
                register_name="A0",
                base_register_name="A0",
                size=8,
                size_bits=64,
                base_register_size=8,
                base_register_size_bits=64,
                bit_offset_in_base=0,
            ),
        ),
        Expression.variable(
            "arg_b",
            size=8,
            storage_info=StorageInfo(
                is_register=True,
                space_name="register",
                register_name="A1",
                base_register_name="A1",
                size=8,
                size_bits=64,
                base_register_size=8,
                base_register_size_bits=64,
                bit_offset_in_base=0,
            ),
        ),
    ]

    substituted = substitute_location(
        CanonicalLocation("a", 0, 4),
        ["a", "b"],
        call_args,
        [
            _param("param_1", size=8, is_signed=False, storage=_reg_storage("A0")),
            _param("param_2", size=8, is_signed=False, index=1, storage=_reg_storage("A1")),
        ],
    )

    assert substituted == CanonicalLocation("param_1", 0, 4)


def test_substitute_location_accepts_stack_local_call_arguments():
    caller_params = [_param("param_1", size=8, is_signed=False)]
    local_out = Expression.variable(
        "local_out",
        size=8,
        storage_info=StorageInfo(**_stack_storage(24, size_bytes=4)),
    )

    substituted = substitute_location(
        CanonicalLocation("out", 0, 4),
        ["in", "out"],
        [Expression.parameter("param_1", 0, size=8), local_out],
        caller_params,
    )

    assert substituted == canonicalize_location(local_out, caller_params, size=4)


def test_canonicalize_location_accepts_stack_pointer_relative_address_expression():
    params = [_param("param_1", size=8, is_signed=False)]
    sp = Expression.variable(
        "sp",
        size=8,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            register_name="sp",
            base_register_name="sp",
            size=8,
            size_bits=64,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=0,
        ),
    )
    addr_expr = Expression.binary_op("INT_ADD", sp, Expression.constant(-0x1C, 8))

    location = canonicalize_location(addr_expr, params, size=4)

    assert location == CanonicalLocation("__locbase__stackframe", -0x1C, 4)


def test_substitute_condition_simplifies_stack_local_nonnull_guard():
    params = [_param("param_1", size=8, is_signed=False)]
    sp = Expression.variable(
        "sp",
        size=8,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            register_name="sp",
            base_register_name="sp",
            size=8,
            size_bits=64,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=0,
        ),
    )
    local_addr = Expression.binary_op("INT_ADD", sp, Expression.constant(-0x1C, 8))
    guard = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.parameter("out", 1, size=8),
            Expression.constant(0, 8),
        ),
        False,
    )

    substituted = substitute_condition(
        guard,
        {"out": local_addr},
        params,
    )

    assert substituted.expression.expr_type.name == "CONSTANT"
    assert substituted.expression.value == 1


def test_effect_summary_rewrites_stack_local_post_state_reads_in_arithmetic_expression():
    a = Expression.parameter("a", 0, size=4)
    b = Expression.parameter("b", 1, size=4)
    sum_slot = Expression.variable(
        "sum_slot",
        size=4,
        storage_info=StorageInfo(**_stack_storage(24, size_bytes=4)),
    )
    diff_slot = Expression.variable(
        "diff_slot",
        size=4,
        storage_info=StorageInfo(**_stack_storage(28, size_bytes=4)),
    )
    sum_location = canonicalize_location(sum_slot, [_param("a", size=4), _param("b", size=4, index=1)], size=4)
    diff_location = canonicalize_location(diff_slot, [_param("a", size=4), _param("b", size=4, index=1)], size=4)

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_MULT", memory_expression_for_location(sum_location, []), Expression.constant(4, 4)),
        memory_expression_for_location(diff_location, []),
    )

    rewritten = rewrite_loads_from_effects(
        expr,
        [],
        [
            StoreEffect(
                location=sum_location,
                value=Expression.binary_op("INT_ADD", a, b),
                conditions=[],
                order_key=1,
            ),
            StoreEffect(
                location=diff_location,
                value=Expression.binary_op("INT_SUB", a, b),
                conditions=[],
                order_key=2,
            ),
        ],
        [_param("a", size=4), _param("b", size=4, index=1)],
    )

    assert rewritten.to_string() == "(((a + b) * 4) + (a - b))"


def test_rewrite_location_read_from_effects_drops_stack_local_nonnull_phi_guard():
    params = [_param("a", size=4), _param("b", size=4, index=1)]
    location = CanonicalLocation("__locbase__stackframe", -0x1C, 4)
    raw_guard = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.parameter("out", 2, size=8),
            Expression.constant(0, 8),
        ),
        False,
    )
    cond = substitute_condition(
        raw_guard,
        {
            "out": Expression.binary_op(
                "INT_ADD",
                Expression.variable(
                    "sp",
                    size=8,
                    storage_info=StorageInfo(
                        is_register=True,
                        space_name="register",
                        register_name="sp",
                        base_register_name="sp",
                        size=8,
                        size_bits=64,
                        base_register_size=8,
                        base_register_size_bits=64,
                        bit_offset_in_base=0,
                    ),
                ),
                Expression.constant(-0x1C, 8),
            ),
        },
        params,
    )

    rewritten = rewrite_location_read_from_effects(
        location,
        Expression.constant(0, 4),
        [],
        [
            StoreEffect(
                location=location,
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("a", 0, size=4),
                    Expression.parameter("b", 1, size=4),
                ),
                conditions=[cond],
                order_key=1,
            ),
        ],
        params,
    )

    assert rewritten.to_string() == "(a + b)"


def test_return_analyzer_normalizes_synthetic_post_state_reads_via_effect_summary():
    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("param_1", size=4, is_signed=False, index=0),
        _param("param_2", size=4, is_signed=False, index=1),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("__locbase__stackframe", -32, 4),
                value=Expression.binary_op(
                    "INT_SUB",
                    Expression.parameter("param_1", 0, size=4),
                    Expression.parameter("param_2", 1, size=4),
                ),
                conditions=[],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("__locbase__stackframe", -28, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("param_1", 0, size=4),
                    Expression.parameter("param_2", 1, size=4),
                ),
                conditions=[],
                order_key=2,
            ),
        ],
    )

    expr = Expression.binary_op(
        "INT_ADD",
        memory_expression_for_location(CanonicalLocation("__locbase__stackframe", -32, 4), []),
        Expression.binary_op(
            "INT_MULT",
            memory_expression_for_location(CanonicalLocation("__locbase__stackframe", -28, 4), []),
            Expression.constant(4, 4),
        ),
    )

    normalized = analyzer._normalize_expanded_return_value(expr, [])

    assert "__locread__" not in normalized.to_string()
    assert normalized.to_string() == "((param_1 - param_2) + ((param_1 + param_2) * 4))"


def test_effect_summary_falls_back_to_pre_state_value_for_unwritten_stack_local_read():
    params = [_param("guard", size=8, is_signed=False)]
    slot_expr = Expression.variable(
        "local_guard",
        size=8,
        storage_info=StorageInfo(**_stack_storage(8, size_bytes=8)),
    )
    location = canonicalize_location(slot_expr, params, size=8)
    fallback = Expression.variable("guard_before_call", size=8)

    rewritten = rewrite_location_read_from_effects(
        location,
        fallback,
        [],
        [
            StoreEffect(
                location=CanonicalLocation("guard", 0, 8),
                value=Expression.constant(1, 8),
                conditions=[],
                order_key=1,
            )
        ],
        params,
    )

    assert rewritten.to_string() == "guard_before_call"


def test_recover_call_argument_from_storage_prefers_exact_register_match_for_pointer_arg():
    class FakeAddress:
        def __init__(self, offset, space_name="register"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset, "ram")
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage, size=8):
            self.storage = storage
            self._size = size

        def getSize(self):
            return self._size

        def getAddress(self):
            return FakeAddress(self.storage.offset, self.storage.space_name)

        def getOffset(self):
            return self.storage.offset

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeOp:
        def __init__(self, output, offset, order):
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getOutput(self):
            return self._output

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeTracer:
        def __init__(self, traced_values, ops):
            self._traced_values = traced_values
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return self._traced_values[varnode]

    partial_output = FakeVarnode(
        StorageInfo(
            is_register=True,
            space_name="register",
            offset=0,
            size=4,
            size_bits=32,
            register_name="a2_lo",
            base_register_name="a2",
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=0,
        ),
        size=4,
    )
    exact_output = FakeVarnode(StorageInfo(**_reg_storage("a2")), size=8)
    tracer = FakeTracer(
        {
            partial_output: Expression.parameter("param_1", 0, size=4),
            exact_output: Expression.binary_op(
                "INT_ADD",
                Expression.variable(
                    "sp",
                    size=8,
                    storage_info=StorageInfo(
                        is_register=True,
                        space_name="register",
                        register_name="sp",
                        base_register_name="sp",
                        size=8,
                        size_bits=64,
                        base_register_size=8,
                        base_register_size_bits=64,
                        bit_offset_in_base=0,
                    ),
                ),
                Expression.constant(-0x30, 8),
            ),
        },
        [
            FakeOp(partial_output, 0x1000, 1),
            FakeOp(exact_output, 0x1000, 2),
        ],
    )
    call_op = FakeOp(None, 0x1000, 3)

    recovered = _recover_call_argument_from_storage(
        call_op,
        tracer,
        [_param("param_1", size=4, is_signed=False, index=0)],
        {"storage": _reg_storage("a2"), "size": 8},
    )

    assert recovered is not None
    assert recovered.to_string() == "(sp + (-48))"


def test_recover_call_argument_from_storage_prefers_pointer_compatible_candidate_over_later_scalar_copy():
    class FakeAddress:
        def __init__(self, offset, space_name="register"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset, "ram")
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage, size=8):
            self.storage = storage
            self._size = size

        def getSize(self):
            return self._size

        def getAddress(self):
            return FakeAddress(self.storage.offset, self.storage.space_name)

        def getOffset(self):
            return self.storage.offset

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeOp:
        def __init__(self, output, offset, order):
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getOutput(self):
            return self._output

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeTracer:
        def __init__(self, traced_values, ops):
            self._traced_values = traced_values
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return self._traced_values[varnode]

    pointer_output = FakeVarnode(StorageInfo(**_reg_storage("a2")), size=8)
    scalar_output = FakeVarnode(StorageInfo(**_reg_storage("a2")), size=8)
    local_addr = Expression.binary_op(
        "INT_ADD",
        Expression.variable(
            "sp",
            size=8,
            storage_info=StorageInfo(
                is_register=True,
                space_name="register",
                register_name="sp",
                base_register_name="sp",
                size=8,
                size_bits=64,
                base_register_size=8,
                base_register_size_bits=64,
                bit_offset_in_base=0,
            ),
        ),
        Expression.constant(-0x30, 8),
    )
    tracer = FakeTracer(
        {
            pointer_output: local_addr,
            scalar_output: Expression.parameter("param_1", 0, size=4),
        },
        [
            FakeOp(pointer_output, 0x1000, 1),
            FakeOp(scalar_output, 0x1000, 2),
        ],
    )
    call_op = FakeOp(None, 0x1000, 3)

    recovered = _recover_call_argument_from_storage(
        call_op,
        tracer,
        [_param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0_lo", size_bytes=4, register_name="a0_lo"))],
        {"storage": _reg_storage("a2"), "size": 8, "data_type": "int *"},
    )

    assert recovered is not None
    assert recovered.to_string() == "(sp + (-48))"


def test_storage_matches_parameter_rejects_superset_register_alias():
    expr_storage = StorageInfo(**_reg_storage("a0", size_bytes=8, register_name="a0"))
    param_storage = StorageInfo(
        is_register=True,
        space_name="register",
        offset=36,
        size=4,
        size_bits=32,
        register_name="a0_lo",
        base_register_name="a0",
        base_register_offset=0,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=32,
    )

    assert _storage_matches_parameter(expr_storage, param_storage) is False
    assert _storage_matches_parameter(param_storage, param_storage) is True


def test_resolve_parameter_name_rejects_full_register_when_only_fragment_param_exists():
    params = [
        _param(
            "param_1",
            size=4,
            is_signed=False,
            index=0,
            storage={
                **_reg_storage("a0", size_bytes=4, register_name="a0_lo"),
                "offset": 36,
                "bit_offset_in_base": 32,
                "base_register_size": 8,
                "base_register_size_bits": 64,
            },
        )
    ]

    full_reg_expr = Expression.variable(
        "a0",
        size=8,
        storage_info=StorageInfo(**_reg_storage("a0", size_bytes=8, register_name="a0")),
    )
    fragment_expr = Expression.variable(
        "a0_lo",
        size=4,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            offset=36,
            size=4,
            size_bits=32,
            register_name="a0_lo",
            base_register_name="a0",
            base_register_offset=0,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=32,
        ),
    )

    assert _resolve_parameter_name(full_reg_expr, params) is None
    assert _resolve_parameter_name(fragment_expr, params) == "param_1"


def test_expression_expander_infers_stack_location_for_indirect_output_without_tracer_storage():
    class FakeAddress:
        def __init__(self, offset, space_name="stack"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeVarnode:
        def getAddress(self):
            return FakeAddress(-0x30, "stack")

        def getOffset(self):
            return -0x30

        def getSize(self):
            return 4

        def getHigh(self):
            return None

    class FakeTracer:
        def __init__(self):
            self.program = object()

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    expander = ExpressionExpander(
        tracer=FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=EffectSummary(parameter_names=["param_1"], effects=[]),
        parameters=[_param("param_1", size=4, is_signed=False, index=0)],
    )

    location = expander._infer_indirect_output_location(FakeVarnode(), 4)

    assert location == CanonicalLocation("__locbase__stackframe", -0x30, 4)


def test_recover_call_argument_expressions_prefers_explicit_stack_local_address_over_storage_guess():
    class FakeAddress:
        def __init__(self, offset, space_name="register"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset, "ram")
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage=None, size=8):
            self.storage = storage
            self._size = size

        def getSize(self):
            return self._size

        def getAddress(self):
            if self.storage is None:
                return None
            return FakeAddress(self.storage.offset, self.storage.space_name)

        def getOffset(self):
            return 0 if self.storage is None else self.storage.offset

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeOp:
        def __init__(self, output):
            self._output = output
            self._seqnum = FakeSeqnum(0x1000, 3)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return self._output

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return 0

    class FakeTracer:
        def __init__(self, ops):
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=8)

    misleading_output = FakeVarnode(StorageInfo(**_reg_storage("a2")), size=8)
    tracer = FakeTracer([FakeOp(misleading_output)])
    call_op = FakeOp(None)
    local_addr = Expression.binary_op(
        "INT_ADD",
        Expression.variable(
            "sp",
            size=8,
            storage_info=StorageInfo(
                is_register=True,
                space_name="register",
                register_name="sp",
                base_register_name="sp",
                size=8,
                size_bits=64,
                base_register_size=8,
                base_register_size_bits=64,
                bit_offset_in_base=0,
            ),
        ),
        Expression.constant(-0x30, 8),
    )

    recovered = _recover_call_argument_expressions(
        call_op,
        tracer,
        [
            _param("param_1", size=4, is_signed=False, index=0),
            _param("param_2", size=4, is_signed=False, index=1),
        ],
        [
            {"name": "param_1", "size": 4, "storage": _reg_storage("a0_lo", size_bytes=4, register_name="a0_lo")},
            {"name": "param_2", "size": 4, "storage": _reg_storage("a1_lo", size_bytes=4, register_name="a1_lo")},
            {"name": "param_3", "size": 8, "storage": _reg_storage("a2")},
        ],
        [
            Expression.parameter("param_1", 0, size=4),
            Expression.parameter("param_2", 1, size=4),
            local_addr,
        ],
    )

    assert recovered[2].to_string() == "(sp + (-48))"


def test_recover_call_argument_expressions_preserves_explicit_phi_function_pointer():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeOp:
        def __init__(self):
            self._seqnum = FakeSeqnum(0x1000, 3)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 0

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=8)

    call_op = FakeOp()
    explicit_target = Expression.phi(
        [
            (
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression.parameter("selector", 0, size=4),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
                Expression.binary_op(
                    "INT_ADD",
                    Expression.constant(0, 8),
                    Expression.constant(0x100814, 8),
                ),
            ),
            (
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.parameter("selector", 0, size=4),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
                Expression.binary_op(
                    "INT_ADD",
                    Expression.constant(0, 8),
                    Expression.constant(0x10081C, 8),
                ),
            ),
        ]
    )

    recovered = _recover_call_argument_expressions(
        call_op,
        FakeTracer(),
        [
            _param("param_1", size=8, is_signed=False, index=0, storage=_reg_storage("x0")),
        ],
        [
            {"name": "param_1", "size": 8, "data_type": "code *", "storage": _reg_storage("x0")},
        ],
        [explicit_target],
    )

    assert len(recovered) == 1
    assert recovered[0].expr_type.name == "PHI"
    assert recovered[0].to_string() == explicit_target.to_string()


def test_recover_call_argument_expressions_selects_callee_aligned_explicit_subsequence():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeCallOp:
        def __init__(self):
            self._seqnum = FakeSeqnum(0x2000, 10)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 0

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    recovered = _recover_call_argument_expressions(
        FakeCallOp(),
        FakeTracer(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            _param("lhs", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("rhs", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            Expression.binary_op(
                "INT_SUB",
                Expression.parameter("param_1", 0, size=4),
                Expression.parameter("param_2", 1, size=4),
            ),
            Expression.parameter("param_1", 0, size=4),
            Expression.parameter("param_2", 1, size=4),
            Expression.constant(1, 4),
        ],
    )

    assert [arg.to_string() for arg in recovered] == ["param_1", "param_2", "1"]


def test_recover_call_argument_expressions_prefers_right_aligned_visible_args_over_hidden_prefix():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeCallOp:
        def __init__(self):
            self._seqnum = FakeSeqnum(0x3000, 10)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 0

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    recovered = _recover_call_argument_expressions(
        FakeCallOp(),
        FakeTracer(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            _param("value", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        [
            Expression.parameter("param_3", 2, size=4),
            Expression.parameter("param_3", 2, size=4),
            Expression.constant(0xFFFFFFFD, 8),
        ],
    )

    assert [arg.to_string() for arg in recovered] == ["param_3", "4294967293"]


def test_resolve_call_argument_expression_recovers_parameter_from_storage_alias():
    class FakeVarnode:
        def getSize(self):
            return 8

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeTracer:
        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.variable("tmp_arg", size=8)

        def _get_storage_info_from_varnode(self, _varnode):
            return StorageInfo(
                is_register=True,
                space_name="register",
                register_name="A0",
                base_register_name="A0",
                size=8,
                size_bits=64,
                base_register_size=8,
                base_register_size_bits=64,
                bit_offset_in_base=0,
            )

    resolved = _resolve_call_argument_expression(
        FakeVarnode(),
        FakeTracer(),
        [_param("param_1", size=8, is_signed=False, storage=_reg_storage("A0"))],
    )

    assert resolved.expr_type.name == "PARAMETER"
    assert resolved.name == "param_1"


def test_resolve_call_argument_expression_does_not_relabel_call_defined_register_as_parameter():
    class FakeSymbol:
        def __init__(self, name: str):
            self._name = name

        def getName(self):
            return self._name

        def isParameter(self):
            return True

    class FakeHigh:
        def __init__(self, name: str, symbol=None):
            self._name = name
            self._symbol = symbol

        def getName(self):
            return self._name

        def getSymbol(self):
            return self._symbol

    class FakeCallOp:
        def getMnemonic(self):
            return "CALL"

    class FakeVarnode:
        def __init__(self, def_op=None, high=None):
            self._def_op = def_op
            self._high = high

        def getSize(self):
            return 4

        def getDef(self):
            return self._def_op

        def getHigh(self):
            return self._high

    call_defined = FakeVarnode(
        def_op=FakeCallOp(),
        high=FakeHigh("param_1", FakeSymbol("param_1")),
    )

    class FakeTracer:
        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.variable(
                "w0",
                size=4,
                storage_info=StorageInfo(**_reg_storage("a0", size_bytes=4, register_name="a0")),
            )

        def _get_storage_info_from_varnode(self, _varnode):
            return StorageInfo(**_reg_storage("a0", size_bytes=4, register_name="a0"))

    resolved = _resolve_call_argument_expression(
        call_defined,
        FakeTracer(),
        [_param("param_1", size=4, is_signed=False, storage=_reg_storage("a0", size_bytes=4, register_name="a0"))],
    )

    assert resolved.expr_type.name == "VARIABLE"
    assert resolved.name == "w0"


def test_normalize_call_argument_expression_falls_back_to_positional_parameter():
    unresolved = Expression.variable("opaque_arg", size=8)

    normalized = _normalize_call_argument_expression(
        unresolved,
        1,
        [
            _param("param_1", size=8, is_signed=False, index=0),
            _param("param_2", size=8, is_signed=False, index=1),
        ],
    )

    assert normalized.expr_type.name == "PARAMETER"
    assert normalized.name == "param_2"


def test_choose_effect_substitution_args_retries_with_positional_parameters():
    chosen = _choose_effect_substitution_args(
        CanonicalLocation("a", 0, 4),
        ["a", "b"],
        [Expression.variable("opaque0", size=8), Expression.variable("opaque1", size=8)],
        [
            _param("param_1", size=8, is_signed=False, index=0),
            _param("param_2", size=8, is_signed=False, index=1),
        ],
    )

    assert chosen[0].expr_type.name == "PARAMETER"
    assert chosen[0].name == "param_1"
    assert chosen[1].expr_type.name == "PARAMETER"
    assert chosen[1].name == "param_2"


def test_summarize_store_effects_recovers_argumentless_call_via_matching_parameter_storage():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def getAddress(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._target = FakeVarnode()
            self._seqnum = FakeSeqnum(0x401000, 1)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._target

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def __init__(self, op):
            self._op = op

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    call_op = FakeCallOp()
    captured_args = {}

    def _direct_call_summary(_name, args):
        captured_args["args"] = list(args)
        return EffectSummary(
            parameter_names=["a", "b"],
            effects=[
                StoreEffect(
                    location=CanonicalLocation("a", 0, 4),
                    value=Expression.memory(Expression.parameter("b", 1, size=8), size=4),
                    conditions=[],
                    order_key=1,
                ),
                StoreEffect(
                    location=CanonicalLocation("b", 0, 4),
                    value=Expression.memory(Expression.parameter("a", 0, size=8), size=4),
                    conditions=[],
                    order_key=1,
                ),
            ],
        )

    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(call_op),
        FakeConditionTracker(),
        [
            _param("param_1", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("param_2", size=8, is_signed=False, index=1, storage=_reg_storage("x1", register_name="x1")),
        ],
        direct_call_summary=_direct_call_summary,
        resolve_callee_parameters=lambda _name: [
            _param("a", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("b", size=8, is_signed=False, index=1, storage=_reg_storage("x1", register_name="x1")),
        ],
        debug=False,
    )

    assert [arg.name for arg in captured_args["args"]] == ["param_1", "param_2"]
    assert len(summary.effects) == 2
    assert summary.effects[0].location == CanonicalLocation("param_1", 0, 4)
    assert summary.effects[0].value.to_string() == "MEM[param_2]"
    assert summary.effects[1].location == CanonicalLocation("param_2", 0, 4)
    assert summary.effects[1].value.to_string() == "MEM[param_1]"


def test_summarize_store_effects_substitutes_stack_pointer_relative_out_parameter_locations():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key):
            self.key = key

        def getSize(self):
            return 8

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target"),
                FakeVarnode("arg0"),
                FakeVarnode("out0"),
            ]
            self._seqnum = FakeSeqnum(0x401100, 3)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    sp = Expression.variable(
        "sp",
        size=8,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            register_name="sp",
            base_register_name="sp",
            size=8,
            size_bits=64,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=0,
        ),
    )

    class FakeTracer:
        def __init__(self, op):
            self._op = op

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "arg0":
                return Expression.parameter("param_1", 0, size=8)
            if varnode.key == "out0":
                return Expression.binary_op("INT_ADD", sp, Expression.constant(-0x1C, 8))
            return Expression.constant(0x401100, 8)

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(call_op),
        FakeConditionTracker(),
        [_param("param_1", size=8, is_signed=False, index=0)],
        direct_call_summary=lambda _name, _args: EffectSummary(
            parameter_names=["value", "out"],
            effects=[
                StoreEffect(
                    location=CanonicalLocation("out", 0, 4),
                    value=Expression.parameter("value", 0, size=4),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
        resolve_callee_parameters=lambda _name: [
            _param("value", size=8, is_signed=False, index=0),
            _param("out", size=8, is_signed=False, index=1),
        ],
        debug=False,
    )

    assert len(summary.effects) == 1
    assert summary.effects[0].location == CanonicalLocation("__locbase__stackframe", -0x1C, 4)
    assert summary.effects[0].value.expr_type.name == "PARAMETER"
    assert summary.effects[0].value.name == "param_1"


def test_expression_expander_stabilizes_parameter_like_call_arg_from_original_input():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return "ram"

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeSymbol:
        def __init__(self, name: str, is_parameter: bool):
            self._name = name
            self._is_parameter = is_parameter

        def getName(self):
            return self._name

        def isParameter(self):
            return self._is_parameter

    class FakeHigh:
        def __init__(self, name: str, symbol=None):
            self._name = name
            self._symbol = symbol

        def getName(self):
            return self._name

        def getSymbol(self):
            return self._symbol

    class FakeVarnode:
        def __init__(self, name, size=4, def_op=None, high=None):
            self.name = name
            self._size = size
            self._def_op = def_op
            self._high = high

        def getDef(self):
            return self._def_op

        def getSize(self):
            return self._size

        def getHigh(self):
            return self._high

    class FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class FakeCopyOp:
        def __init__(self, source):
            self._source = source

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            return self._source if index == 0 else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._inputs = inputs
            self._output = FakeOutput(4)
            self._seqnum = FakeSeqnum(0x401020, 10)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    target_varnode = FakeVarnode("callee_addr", size=8)
    source_param3 = FakeVarnode(
        "param3_src",
        size=4,
        high=FakeHigh("param_3", FakeSymbol("param_3", True)),
    )
    copied_first_arg = FakeVarnode(
        "copied_first_arg",
        size=4,
        def_op=FakeCopyOp(source_param3),
        high=FakeHigh("tmp_w0"),
    )
    bias_varnode = FakeVarnode("bias", size=4)
    call_op = FakeCallOp([target_varnode, copied_first_arg, bias_varnode])

    class FakeTracer:
        debug = False

        def _get_function_name(self, _varnode):
            return "fc_bias"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return Expression.constant(0x401000, 8)
            if varnode is copied_first_arg:
                return Expression.variable(
                    "w0",
                    size=4,
                    storage_info=StorageInfo(**_reg_storage("a0", size_bytes=4, register_name="a0")),
                )
            if varnode is bias_varnode:
                return Expression.constant(0xFFFFFFFD, 4)
            raise AssertionError(f"unexpected trace: {varnode}")

        def emit_unknown_event(self, **kwargs):
            raise AssertionError(f"call should have been resolved: {kwargs}")

        def _trace_pcode_op(self, *_args, **_kwargs):
            raise AssertionError("recursive tracing fallback should not run")

        def get_all_pcode_ops(self):
            return [call_op]

        def _get_storage_info_from_varnode(self, varnode):
            if varnode is copied_first_arg:
                return StorageInfo(**_reg_storage("a0", size_bytes=4, register_name="a0"))
            if varnode is source_param3:
                return StorageInfo(**_reg_storage("a2", size_bytes=4, register_name="a2"))
            return None

    captured = {}

    def resolve_call(function_name, args):
        captured["target"] = function_name
        captured["args"] = list(args)
        return [ExpandedValue(Expression.constant(1, 4), [])]

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=resolve_call,
        parameters=[
            _param("param_1", size=4, index=0, storage=_reg_storage("a0", size_bytes=4, register_name="a0")),
            _param("param_3", size=4, index=2, storage=_reg_storage("a2", size_bytes=4, register_name="a2")),
        ],
        resolve_callee_parameters=lambda _name: [
            _param("value", size=4, index=0, storage=_reg_storage("a0", size_bytes=4, register_name="a0")),
            _param("bias", size=4, index=1, storage=_reg_storage("a1", size_bytes=4, register_name="a1")),
        ],
    )
    expander._expand_input_varnode = lambda varnode, _conds, _depth: {
        copied_first_arg: [ExpandedValue(Expression.parameter("param_1", 0, size=4), [])],
        bias_varnode: [ExpandedValue(Expression.constant(0xFFFFFFFD, 4), [])],
    }[varnode]

    expanded = expander._expand_call_operation(call_op, [], depth=0, output_size=4)

    assert len(expanded) == 1
    assert captured["target"] == "fc_bias"
    assert [arg.to_string() for arg in captured["args"]] == ["param_3", "4294967293"]


def test_summarize_store_effects_recovers_direct_call_store_values_from_call_expander():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size, def_op=None):
            self.key = key
            self._size = size
            self._def_op = def_op

        def getSize(self):
            return self._size

        def getDef(self):
            return self._def_op

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]
            self._seqnum = FakeSeqnum(0x401180, 2)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeStoreOp:
        def __init__(self, call_op):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                FakeVarnode("value", 4, def_op=call_op),
            ]
            self._seqnum = FakeSeqnum(0x401190, 3)

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, *ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def _get_function_name(self, varnode):
            if getattr(varnode, "key", None) == "target":
                return "fc_add"
            return "UNKNOWN_FUNC"

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "addr":
                return Expression.parameter("slot", 0, size=8)
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 1, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 2, size=4)
            if varnode.key == "value":
                return Expression.unknown("call_out_of_scope:fc_add")
            return Expression.constant(0, max(1, varnode.getSize()))

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(FakeStoreOp(call_op))],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("slot", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("lhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
            _param("rhs", size=4, index=2, storage=_reg_storage("x2", size_bytes=4, register_name="w2")),
        ],
        direct_call_expander=lambda _name, args: [
            ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])
        ],
        resolve_callee_parameters=lambda _name: [
            _param("a", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("b", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )

    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    assert summary.effects[0].location == CanonicalLocation("slot", 0, 4)
    assert summary.effects[0].value.to_string() == "(lhs + rhs)"


def test_summarize_store_effects_keeps_effect_free_value_calls_from_poisoning_summary():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size, def_op=None):
            self.key = key
            self._size = size
            self._def_op = def_op

        def getSize(self):
            return self._size

        def getDef(self):
            return self._def_op

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]
            self._output = FakeVarnode("ret", 4, def_op=self)
            self._seqnum = FakeSeqnum(0x401180, 2)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    class FakeStoreOp:
        def __init__(self, call_op):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                call_op.getOutput(),
            ]
            self._seqnum = FakeSeqnum(0x401190, 3)

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, *ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def _get_function_name(self, varnode):
            if getattr(varnode, "key", None) == "target":
                return "fc_add"
            return "UNKNOWN_FUNC"

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "addr":
                return Expression.parameter("slot", 0, size=8)
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 1, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 2, size=4)
            if varnode.key == "ret":
                return Expression.unknown("call_out_of_scope:fc_add")
            return Expression.constant(0, max(1, varnode.getSize()))

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op, FakeStoreOp(call_op))],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("slot", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("lhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
            _param("rhs", size=4, index=2, storage=_reg_storage("x2", size_bytes=4, register_name="w2")),
        ],
        direct_call_summary=lambda _name, _args: EffectSummary(
            parameter_names=["a", "b"],
            effects=[],
            has_unsupported_call=False,
        ),
        direct_call_expander=lambda _name, args: [
            ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])
        ],
        resolve_callee_parameters=lambda _name: [
            _param("a", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("b", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )

    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    assert summary.effects[0].location == CanonicalLocation("slot", 0, 4)
    assert summary.effects[0].value.to_string() == "(lhs + rhs)"


def test_expression_expander_keeps_concrete_call_arg_when_canonical_candidate_is_unresolved_phi():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return "ram"

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeHigh:
        def __init__(self, name: str):
            self._name = name

        def getName(self):
            return self._name

        def getSymbol(self):
            return None

    class FakeVarnode:
        def __init__(self, name, size=4, def_op=None, high=None):
            self.name = name
            self._size = size
            self._def_op = def_op
            self._high = high

        def getDef(self):
            return self._def_op

        def getSize(self):
            return self._size

        def getHigh(self):
            return self._high

    class FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class FakeAddOp:
        def __init__(self):
            self._inputs = []

        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeCallOp:
        def __init__(self, inputs):
            self._inputs = inputs
            self._output = FakeOutput(4)
            self._seqnum = FakeSeqnum(0x401040, 12)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    target_varnode = FakeVarnode("callee_addr", size=8)
    unstable_source = FakeVarnode(
        "unstable_arg",
        size=4,
        def_op=FakeAddOp(),
        high=FakeHigh("tmp_w0"),
    )
    call_op = FakeCallOp([target_varnode, unstable_source])

    unresolved_phi = Expression.phi(
        [
            (
                Condition(Expression.binary_op("INT_EQUAL", Expression.parameter("param_1", 0, size=4), Expression.constant(0, 4))),
                Expression.unknown("call_out_of_scope:fc_wrap_add_then_bias"),
            ),
            (
                Condition(Expression.binary_op("INT_NOTEQUAL", Expression.parameter("param_1", 0, size=4), Expression.constant(0, 4))),
                Expression.unknown("call_out_of_scope:fc_bias"),
            ),
        ]
    )

    class FakeTracer:
        debug = False

        def _get_function_name(self, _varnode):
            return "fc_scale"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return Expression.constant(0x401000, 8)
            if varnode is unstable_source:
                return unresolved_phi
            raise AssertionError(f"unexpected trace: {varnode}")

        def emit_unknown_event(self, **kwargs):
            raise AssertionError(f"call should have been resolved: {kwargs}")

        def _trace_pcode_op(self, *_args, **_kwargs):
            raise AssertionError("recursive tracing fallback should not run")

        def get_all_pcode_ops(self):
            return [call_op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    captured = {}

    def resolve_call(function_name, args):
        captured["target"] = function_name
        captured["args"] = list(args)
        return [ExpandedValue(Expression.constant(1, 4), [])]

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=resolve_call,
        parameters=[
            _param("param_1", size=4, index=0, storage=_reg_storage("a0", size_bytes=4, register_name="a0")),
        ],
        resolve_callee_parameters=lambda _name: [
            _param("value", size=4, index=0, storage=_reg_storage("a0", size_bytes=4, register_name="a0")),
        ],
    )
    expander._expand_input_varnode = lambda varnode, _conds, _depth: {
        unstable_source: [ExpandedValue(Expression.parameter("param_1", 0, size=4), [])],
    }[varnode]

    expanded = expander._expand_call_operation(call_op, [], depth=0, output_size=4)

    assert len(expanded) == 1
    assert captured["target"] == "fc_scale"
    assert [arg.to_string() for arg in captured["args"]] == ["param_1"]


def test_summarize_store_effects_uses_callee_aligned_subset_for_hidden_call_operands():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size=4, storage=None):
            self.key = key
            self._size = size
            self.storage = storage

        def getSize(self):
            return self._size

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", size=8),
                FakeVarnode("hidden", size=4),
                FakeVarnode("lhs", size=4),
                FakeVarnode("rhs", size=4),
                FakeVarnode("bias", size=4),
            ]
            self._seqnum = FakeSeqnum(0x401100, 10)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def __init__(self, op):
            self._op = op

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "hidden":
                return Expression.binary_op(
                    "INT_SUB",
                    Expression.parameter("param_1", 0, size=4),
                    Expression.parameter("param_2", 1, size=4),
                )
            if varnode.key == "lhs":
                return Expression.parameter("param_1", 0, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("param_2", 1, size=4)
            if varnode.key == "bias":
                return Expression.constant(1, 4)
            return Expression.constant(0x401100, 8)

    captured_args = {}
    call_op = FakeCallOp()

    def _direct_call_summary(_name, args):
        captured_args["args"] = list(args)
        return EffectSummary(parameter_names=["lhs", "rhs", "bias"], effects=[])

    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(call_op),
        FakeConditionTracker(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        direct_call_summary=_direct_call_summary,
        resolve_callee_parameters=lambda _name: [
            _param("lhs", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("rhs", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert [arg.to_string() for arg in captured_args["args"]] == ["param_1", "param_2", "1"]


def test_summarize_store_effects_captures_double_indirect_parameter_store():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeStoreOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                FakeVarnode("value", 4),
            ]
            self._seqnum = FakeSeqnum(0x401200, 7)

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "addr":
                return Expression.memory(Expression.parameter("slot", 0, size=8), size=8)
            if varnode.key == "value":
                return Expression.parameter("value", 1, size=4)
            return Expression.constant(0, 4)

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeStoreOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("slot", size=8, is_signed=False, index=0),
            _param("value", size=4, index=1),
        ],
        debug=False,
    )

    assert len(summary.effects) == 1
    assert summary.effects[0].location == CanonicalLocation(
        "slot",
        0,
        4,
        steps=(LocationStep("deref", 8),),
    )
    assert summary.effects[0].value.to_string() == "value"


def test_effect_summary_accepts_mul_by_one_wrapped_parameter_addresses():
    addr_expr = Expression.binary_op(
        "INT_MULT",
        Expression.constant(1, 8),
        Expression.binary_op(
            "INT_ADD",
            Expression.variable("box", size=8),
            Expression.constant(4, 8),
        ),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("box", size=8, is_signed=False)],
        size=4,
    )

    assert location == CanonicalLocation("box", 4, 4)


def test_effect_summary_accepts_subpiece_lower_parameter_addresses():
    ptr = Expression.parameter("ptr", 0, size=8)
    addr_expr = Expression.unary_op(
        "INT_ZEXT",
        Expression.binary_op("SUBPIECE", ptr, Expression.constant(0, 4)),
    )
    addr_expr.size = 8

    location = canonicalize_param_location(
        addr_expr,
        [_param("ptr", size=8, is_signed=False)],
        size=4,
    )

    assert location == CanonicalLocation("ptr", 0, 4)


def test_effect_summary_accepts_ptradd_style_constant_offsets():
    ptr = Expression.parameter("ptr", 0, size=8)
    addr_expr = Expression.binary_op(
        "INT_ADD",
        ptr,
        Expression.binary_op(
            "INT_MULT",
            Expression.constant(1, 8),
            Expression.constant(4, 8),
        ),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("ptr", size=8, is_signed=False)],
        size=4,
    )

    assert location == CanonicalLocation("ptr", 4, 4)


def test_normalize_post_state_expression_composes_same_location_increment_effects():
    ptr = Expression.parameter("ptr", 0, size=8)
    field = Expression.binary_op(
        "INT_ADD",
        ptr,
        Expression.binary_op(
            "INT_MULT",
            Expression.constant(1, 8),
            Expression.constant(4, 8),
        ),
    )
    field_load = Expression.memory(field, size=4)
    expr = Expression.binary_op("INT_ADD", field_load, Expression.constant(7, 4))
    effects = [
        StoreEffect(
            location=CanonicalLocation("ptr", 4, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(field, size=4), Expression.constant(1, 4)),
            conditions=[],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("ptr", 4, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(field, size=4), Expression.constant(1, 4)),
            conditions=[],
            order_key=2,
        ),
    ]

    normalized = normalize_post_state_expression(
        expr,
        [],
        effects,
        [_param("ptr", size=8, is_signed=False)],
        prefer_canonical_post_state=False,
    )

    assert normalized is not None
    assert normalized.to_string() == "(((MEM[(ptr + 4)] + 1) + 1) + 7)"


def test_effect_summary_keeps_load_when_multiple_writes_overlap():
    ptr = Expression.parameter("ptr", 0, size=8)
    original = Expression.memory(ptr, size=4)
    effects = [
        StoreEffect(
            location=CanonicalLocation("ptr", 0, 4),
            value=Expression.constant(1, 4),
            conditions=[],
            order_key=2,
        ),
        StoreEffect(
            location=CanonicalLocation("ptr", 0, 4),
            value=Expression.constant(2, 4),
            conditions=[],
            order_key=1,
        ),
    ]

    rewritten = rewrite_loads_from_effects(
        original,
        [],
        effects,
        [_param("ptr", size=8, is_signed=False)],
    )

    assert rewritten.expr_type.name == "MEMORY"


def test_effect_summary_skips_effects_that_contradict_return_conditions():
    ptr = Expression.parameter("ptr", 0, size=8)
    flag = Expression.parameter("flag", 1, size=4)
    original = Expression.memory(ptr, size=4)
    positive = Condition(
        Expression.binary_op("INT_NOTEQUAL", flag, Expression.constant(0, 4)),
        False,
    )
    negative = positive.negate()
    effects = [
        StoreEffect(
            location=CanonicalLocation("ptr", 0, 4),
            value=Expression.parameter("v_true", 2, size=4),
            conditions=[positive],
            order_key=2,
        ),
        StoreEffect(
            location=CanonicalLocation("ptr", 0, 4),
            value=Expression.parameter("v_false", 3, size=4),
            conditions=[negative],
            order_key=1,
        ),
    ]

    rewritten = rewrite_loads_from_effects(
        original,
        [positive],
        effects,
        [
            _param("ptr", size=8, is_signed=False),
            _param("flag", size=4, index=1),
            _param("v_true", size=4, index=2),
            _param("v_false", size=4, index=3),
        ],
    )

    assert rewritten.to_string() == "v_true"


def test_effect_summary_does_not_reapply_self_referential_store():
    box = Expression.parameter("box", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    right_addr = Expression.binary_op("INT_ADD", box, Expression.constant(4, 8))
    original = Expression.binary_op("INT_ADD", Expression.memory(right_addr, size=4), delta)
    effect = StoreEffect(
        location=CanonicalLocation("box", 4, 4),
        value=Expression.binary_op("INT_ADD", Expression.memory(right_addr, size=4), delta),
        conditions=[],
        order_key=3,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [],
        [effect],
        [_param("box", size=8, is_signed=False), _param("delta", size=4, index=1)],
    )

    assert rewritten.to_string() == "(MEM[(box + 4)] + delta)"


def test_effect_summary_does_not_reapply_commuted_self_referential_store():
    box = Expression.parameter("box", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    right_addr = Expression.binary_op("INT_ADD", box, Expression.constant(4, 8))
    original = Expression.binary_op("INT_ADD", delta, Expression.memory(right_addr, size=4))
    effect = StoreEffect(
        location=CanonicalLocation("box", 4, 4),
        value=Expression.binary_op("INT_ADD", Expression.memory(right_addr, size=4), delta),
        conditions=[],
        order_key=3,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [],
        [effect],
        [_param("box", size=8, is_signed=False), _param("delta", size=4, index=1)],
    )

    assert rewritten.to_string() == "(delta + MEM[(box + 4)])"


def test_call_effect_summary_policy_accepts_interdependent_swap_writes():
    summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(Expression.parameter("b", 1, size=8), size=4),
                conditions=[],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(Expression.parameter("a", 0, size=8), size=4),
                conditions=[],
                order_key=2,
            ),
        ],
    )

    assert is_call_effect_summary_allowed(summary)


def test_effect_summary_rewrites_swap_branch_using_pre_store_values():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    original = Expression.binary_op("INT_SUB", Expression.memory(a, size=4), Expression.memory(b, size=4))
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    rewritten = rewrite_loads_from_effects(
        original,
        [swap_taken],
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert rewritten.to_string() == "(MEM[b] - MEM[a])"


def test_effect_summary_rewrites_observed_post_call_loads_into_phi_difference():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    original = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=10,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=11,
        ),
    ]

    rewritten = rewrite_observed_loads_from_effects(
        original,
        [nonnull_a, nonnull_b],
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert rewritten.to_string() == "(PHI(MEM[b] if (MEM[b] < MEM[a]), MEM[a]) - PHI(MEM[a] if (MEM[b] < MEM[a]), MEM[b]))"


def test_effect_summary_collapses_post_state_phi_to_canonical_memory_location():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    post_swap_b = Expression.phi(
        [
            (swap_taken, Expression.memory(a, size=4)),
            (None, Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effects = [
        StoreEffect(
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        post_swap_b,
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"


def test_expression_expander_collapses_nested_multiequal_matching_effect_post_state():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    post_swap_b = Expression.phi(
        [
            (swap_taken, Expression.memory(a, size=4)),
            (None, Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeMultiequalOp:
        def getMnemonic(self):
            return "MULTIEQUAL"

    class FakeVarnode:
        def __init__(self, def_op):
            self._def_op = def_op

        def getSize(self):
            return 4

        def getDef(self):
            return self._def_op

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return post_swap_b

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    expanded = expander._expand_input_varnode(
        FakeVarnode(FakeMultiequalOp()),
        [],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "MEM[b]"


def test_effect_summary_collapses_post_state_phi_with_explicit_complementary_guards():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    post_swap_b = Expression.phi(
        [
            (swap_taken, Expression.memory(a, size=4)),
            (no_swap, Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effects = [
        StoreEffect(
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        post_swap_b,
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
        return_conditions=[swap_taken],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"


def test_effect_summary_collapses_pruned_post_state_memory_leaf_to_canonical_location():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    collapsed = collapse_pruned_post_state_memory_leaf_to_canonical_memory(
        Expression.memory(a, size=4),
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
        return_conditions=[swap_taken],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"


def test_expression_expander_collapses_nested_multiequal_using_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    post_swap_b = Expression.phi(
        [
            (swap_taken, Expression.memory(a, size=4)),
            (no_swap, Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeMultiequalOp:
        def getMnemonic(self):
            return "MULTIEQUAL"

    class FakeVarnode:
        def __init__(self, def_op):
            self._def_op = def_op

        def getSize(self):
            return 4

        def getDef(self):
            return self._def_op

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return post_swap_b

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    expanded = expander._expand_input_varnode(
        FakeVarnode(FakeMultiequalOp()),
        [swap_taken],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "MEM[b]"


def test_expression_expander_canonicalizes_top_level_phi_input_using_effects():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull = Condition.combine_and(
        [
            Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False),
            Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False),
        ]
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.phi(
            [
                (Condition.combine_and([nonnull, swap_taken]), Expression.memory(a, size=4)),
                (Condition.combine_and([nonnull, no_swap]), Expression.memory(b, size=4)),
            ]
        ),
    )
    expr.operands[1].size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        def trace_varnode(self, _varnode, depth=0, use_cache=False):
            return expr

        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return expr

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    conds = [
        Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False),
        Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False),
        swap_taken,
    ]
    canonicalized = expander._trace_and_canonicalize_input_value(object(), conds, 0)

    assert canonicalized is not None
    assert canonicalized.to_string() == "(MEM[a] - MEM[b])"


def test_expression_expander_canonicalizes_multiequal_branch_memory_leaf_using_effects():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        def trace_varnode(self, _varnode, depth=0, use_cache=False):
            return Expression.memory(a, size=4)

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._trace_and_canonicalize_input_value(object(), [swap_taken], 0)

    assert canonicalized is not None
    assert canonicalized.to_string() == "MEM[b]"


def test_effect_summary_treats_composite_guard_as_implied_by_split_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    composite = Condition.combine_and([nonnull_a, nonnull_b, swap_taken])

    residual = subtract_implied_conditions([composite], [nonnull_a, nonnull_b, swap_taken])

    assert residual == []


def test_effect_summary_treats_composite_guard_as_implied_by_grouped_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    nonnull = Condition.combine_and([nonnull_a, nonnull_b])
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    composite = Condition.combine_and([nonnull, swap_taken])

    residual = subtract_implied_conditions([composite], [nonnull, swap_taken])

    assert residual == []


def test_canonicalize_post_state_subexpressions_handles_composite_guard_without_self_subtraction():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.phi(
            [
                (Condition.combine_and([nonnull_a, nonnull_b, swap_taken]), Expression.memory(a, size=4)),
                (Condition.combine_and([nonnull_a, nonnull_b, no_swap]), Expression.memory(b, size=4)),
            ]
        ),
    )
    expr.operands[1].size = 4
    effects = [
        StoreEffect(
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    normalized = canonicalize_post_state_subexpressions(
        expr,
        [nonnull_a, nonnull_b, swap_taken],
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert normalized.to_string() == "(MEM[a] - MEM[b])"


def test_expression_expander_collapses_nested_multiequal_with_grouped_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    nonnull = Condition.combine_and([nonnull_a, nonnull_b])
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    post_swap_b = Expression.phi(
        [
            (Condition.combine_and([nonnull, swap_taken]), Expression.memory(a, size=4)),
            (Condition.combine_and([nonnull, no_swap]), Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeMultiequalOp:
        def getMnemonic(self):
            return "MULTIEQUAL"

    class FakeVarnode:
        def __init__(self, def_op):
            self._def_op = def_op

        def getSize(self):
            return 4

        def getDef(self):
            return self._def_op

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return post_swap_b

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    expanded = expander._expand_input_varnode(
        FakeVarnode(FakeMultiequalOp()),
        [nonnull, swap_taken],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "MEM[b]"


def test_normalize_post_state_expression_collapses_effect_rewritten_branch_value():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=8)
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 8)),
        False,
    )
    negate_nonzero = negate_zero.negate()
    effects = [
        StoreEffect(
            location=CanonicalLocation("value", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
            conditions=[negate_zero],
            order_key=5,
        ),
        StoreEffect(
            location=CanonicalLocation("value", 0, 4),
            value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
            conditions=[negate_nonzero],
            order_key=5,
        ),
    ]

    rewritten = rewrite_observed_loads_from_effects(
        Expression.memory(value, size=4, read_order_key=9),
        [negate_zero],
        effects,
        [
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )
    normalized = normalize_post_state_expression(
        rewritten,
        [negate_zero],
        effects,
        [
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )

    assert rewritten.to_string() == "(MEM[value] + delta)"
    assert normalized.to_string() == "MEM[value]"


def test_normalize_post_state_expression_rewrites_double_indirect_post_state_load():
    slot = Expression.parameter("slot", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    slot_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", slot, Expression.constant(0, 8)),
        False,
    )
    inner_nonnull = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.memory(slot, size=8),
            Expression.constant(0, 8),
        ),
        False,
    )
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(Expression.memory(slot, size=8), size=4),
        Expression.constant(1, 4),
    )

    normalized = normalize_post_state_expression(
        expr,
        [slot_nonnull, inner_nonnull],
        [
            StoreEffect(
                location=CanonicalLocation(
                    "slot",
                    0,
                    4,
                    steps=(LocationStep("deref", 8),),
                ),
                value=value,
                conditions=[slot_nonnull, inner_nonnull],
                order_key=5,
            ),
        ],
        [
            _param("slot", size=8, is_signed=False),
            _param("value", size=4, index=1),
        ],
    )

    assert normalized.to_string() == "(value + 1)"


def test_normalize_post_state_expression_collapses_ordered_alias_updates_to_post_state_memory():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", dst, src),
        False,
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation("dst", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
            conditions=[dst_nonnull, src_nonnull],
            order_key=10,
        ),
        StoreEffect(
            location=CanonicalLocation("src", 0, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(src, size=4),
                Expression.constant(4294967295, 4),
            ),
            conditions=[dst_nonnull, src_nonnull],
            order_key=20,
        ),
    ]
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        Expression.constant(4294967295, 4),
    )
    params = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    conditions = [dst_nonnull, src_nonnull, alias_cond]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        expr,
        effects,
        params,
        return_conditions=conditions,
    )
    normalized = normalize_post_state_expression(
        expr,
        conditions,
        effects,
        params,
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[dst]"
    assert normalized.to_string() == "MEM[dst]"


def test_normalize_post_state_expression_keeps_ordered_alias_update_when_alias_not_implied():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation("dst", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
            conditions=[dst_nonnull, src_nonnull],
            order_key=10,
        ),
        StoreEffect(
            location=CanonicalLocation("src", 0, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(src, size=4),
                Expression.constant(4294967295, 4),
            ),
            conditions=[dst_nonnull, src_nonnull],
            order_key=20,
        ),
    ]
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        Expression.constant(4294967295, 4),
    )
    params = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    conditions = [dst_nonnull, src_nonnull]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        expr,
        effects,
        params,
        return_conditions=conditions,
    )
    normalized = normalize_post_state_expression(
        expr,
        conditions,
        effects,
        params,
    )

    assert collapsed is None
    assert normalized.to_string() == "(MEM[dst] + 4294967295)"


def test_normalize_post_state_expression_stays_conservative_when_guards_do_not_match():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=8)
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 8)),
        False,
    )
    other_guard = Condition(
        Expression.binary_op("INT_NOTEQUAL", negate, Expression.constant(1, 8)),
        False,
    )
    expr = Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta)

    normalized = normalize_post_state_expression(
        expr,
        [negate_zero],
        [
            StoreEffect(
                location=CanonicalLocation("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[other_guard],
                order_key=5,
            ),
        ],
        [
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )

    assert normalized.to_string() == "(MEM[value] + delta)"


def test_normalize_post_state_expression_replays_definite_simple_store_then_read():
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(ptr, size=4),
        Expression.constant(4294967295, 4),
    )

    normalized = normalize_post_state_expression(
        expr,
        [ptr_nonnull],
        [
            StoreEffect(
                location=CanonicalLocation("ptr", 0, 4),
                value=Expression.binary_op("INT_ADD", value, Expression.constant(3, 4)),
                conditions=[ptr_nonnull],
                order_key=5,
            ),
        ],
        [
            _param("ptr", size=8, is_signed=False),
            _param("value", size=4, is_signed=True, index=1),
        ],
    )

    assert normalized.to_string() == "((value + 3) + 4294967295)"


def test_normalize_post_state_expression_rewrites_wide_param_store_then_read_per_branch():
    param_1 = Expression.parameter("param_1", 0, size=8)
    param_2 = Expression.parameter("param_2", 1, size=8)
    param_3 = Expression.parameter("param_3", 2, size=4)
    param_4 = Expression.parameter("param_4", 3, size=8)
    param_4_zero = Condition(
        Expression.binary_op("INT_EQUAL", param_4, Expression.constant(0, 8)),
        False,
    )
    param_4_nonzero = param_4_zero.negate()
    param_2_lo = Expression.binary_op("SUBPIECE", param_2, Expression.constant(0, 4))
    param_2_lo.size = 4
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(param_1, size=4),
        param_2_lo,
    )

    normalized_zero = normalize_post_state_expression(
        expr,
        [param_4_zero],
        [
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op(
                            "INT_MULT",
                            param_2_lo,
                            Expression.constant(2, 4),
                        ),
                        Expression.constant(11, 4),
                    ),
                    param_3,
                ),
                conditions=[param_4_zero],
                order_key=5,
            ),
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.binary_op("INT_XOR", param_2_lo, param_3),
                conditions=[param_4_nonzero],
                order_key=5,
            ),
        ],
        [
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=8, is_signed=False, index=1),
            _param("param_3", size=4, index=2),
            _param("param_4", size=8, is_signed=False, index=3),
        ],
    )
    normalized_nonzero = normalize_post_state_expression(
        expr,
        [param_4_nonzero],
        [
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op(
                            "INT_MULT",
                            param_2_lo,
                            Expression.constant(2, 4),
                        ),
                        Expression.constant(11, 4),
                    ),
                    param_3,
                ),
                conditions=[param_4_zero],
                order_key=5,
            ),
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.binary_op("INT_XOR", param_2_lo, param_3),
                conditions=[param_4_nonzero],
                order_key=5,
            ),
        ],
        [
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=8, is_signed=False, index=1),
            _param("param_3", size=4, index=2),
            _param("param_4", size=8, is_signed=False, index=3),
        ],
    )

    assert normalized_zero.to_string() == (
        "(((((param_2 & 4294967295) * 2) + 11) + param_3) - (param_2 & 4294967295))"
    )
    assert normalized_nonzero.to_string() == (
        "(((param_2 & 4294967295) ^ param_3) - (param_2 & 4294967295))"
    )


def test_expression_expander_prefers_canonical_post_state_memory_after_observed_load_rewrite():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=8)
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 8)),
        False,
    )
    negate_nonzero = negate_zero.negate()

    effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[negate_zero],
                order_key=5,
            ),
            StoreEffect(
                location=CanonicalLocation("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[negate_nonzero],
                order_key=5,
            ),
        ],
    )

    expander = ExpressionExpander(
        tracer=None,
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        Expression.memory(value, size=4, read_order_key=9),
        [negate_zero],
    )

    assert canonicalized.to_string() == "MEM[value]"


def test_expression_expander_collapses_nested_multiequal_after_phi_handler_prunes_to_memory_leaf():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeMultiequalOp:
        def getMnemonic(self):
            return "MULTIEQUAL"

    class FakeVarnode:
        def __init__(self, def_op):
            self._def_op = def_op

        def getSize(self):
            return 4

        def getDef(self):
            return self._def_op

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return Expression.memory(a, size=4)

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    expanded = expander._expand_input_varnode(
        FakeVarnode(FakeMultiequalOp()),
        [swap_taken],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "MEM[b]"


def test_expression_expander_uses_multiequal_canonical_location_per_branch():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = swap_taken.negate()
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    pred_no_swap = object()
    pred_swap = object()

    class FakeInputVarnode:
        def __init__(self, expr):
            self.expr = expr

        def getDef(self):
            return None

    class FakeParent:
        def getInSize(self):
            return 2

        def getIn(self, index):
            return [pred_no_swap, pred_swap][index]

    class FakeMultiequalOp:
        def getParent(self):
            return FakeParent()

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            return [
                FakeInputVarnode(Expression.memory(b, size=4)),
                FakeInputVarnode(Expression.memory(a, size=4)),
            ][index]

    class FakeBlockInfo:
        def __init__(self, index):
            self.index = index

    class FakeConditionTracker:
        def get_block_by_hash(self, block):
            if block is pred_no_swap:
                return FakeBlockInfo(3)
            if block is pred_swap:
                return FakeBlockInfo(4)
            return None

        def get_all_valid_paths_to_block(self, target_block):
            return [[]]

    class FakeTracer:
        def trace_varnode(self, varnode, depth=0, use_cache=False):
            return varnode.expr

        def _get_op_key(self, _op):
            return "fake-multiequal"

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=FakeConditionTracker(),
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )
    expander._get_edge_condition = lambda block_info, _parent: no_swap if block_info.index == 3 else swap_taken

    expanded = expander._expand_multiequal_internal(
        FakeMultiequalOp(),
        [],
        depth=0,
    )

    observed = {
        (ev.value.to_string(), tuple(cond.to_string() for cond in ev.conditions))
        for ev in expanded
    }
    assert observed == {
        ("MEM[b]", (no_swap.to_string(),)),
        ("MEM[a]", (swap_taken.to_string(),)),
    }


def test_return_analyzer_keeps_canonical_post_state_return_unchanged():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )
    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = effect_summary
    analyzer._current_parameters = [
        _param("a", size=8, is_signed=False),
        _param("b", size=8, is_signed=False, index=1),
    ]
    normalized = analyzer._normalize_expanded_return_value(
        Expression.binary_op("INT_SUB", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        [swap_taken],
    )

    assert normalized.to_string() == "(MEM[b] - MEM[a])"


def test_return_analyzer_reduces_phi_bearing_expanded_return_without_recanonicalizing():
    a = Expression.parameter("param_1", 0, size=8)
    b = Expression.parameter("param_2", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    composite_less = Condition.combine_and([nonnull_a, nonnull_b, swap_taken])
    composite_not_less = Condition.combine_and([nonnull_a, nonnull_b, swap_taken.negate()])
    value = Expression.binary_op(
        "INT_SUB",
        Expression.phi(
            [
                (composite_less, Expression.memory(b, size=4)),
                (composite_not_less, Expression.memory(a, size=4)),
            ]
        ),
        Expression.phi(
            [
                (composite_less, Expression.memory(a, size=4)),
                (composite_not_less, Expression.memory(b, size=4)),
            ]
        ),
    )
    value.operands[0].size = 4
    value.operands[1].size = 4
    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("param_2", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]

    normalized_less = analyzer._normalize_expanded_return_value(
        value,
        [nonnull_a, nonnull_b, swap_taken],
    )
    normalized_not_less = analyzer._normalize_expanded_return_value(
        value,
        [nonnull_a, nonnull_b, swap_taken.negate()],
    )

    assert normalized_less.to_string() == "(MEM[param_2] - MEM[param_1])"
    assert normalized_not_less.to_string() == "(MEM[param_1] - MEM[param_2])"


def test_return_analyzer_prefers_definite_branch_store_value_over_canonical_post_state_memory():
    param_1 = Expression.parameter("param_1", 0, size=8)
    param_2 = Expression.parameter("param_2", 1, size=8)
    param_3 = Expression.parameter("param_3", 2, size=4)
    param_4 = Expression.parameter("param_4", 3, size=8)
    param_4_zero = Condition(
        Expression.binary_op("INT_EQUAL", param_4, Expression.constant(0, 8)),
        False,
    )
    param_4_nonzero = param_4_zero.negate()
    param_2_lo = Expression.binary_op("SUBPIECE", param_2, Expression.constant(0, 4))
    param_2_lo.size = 4
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(param_1, size=4),
        param_2_lo,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3", "param_4"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op(
                            "INT_MULT",
                            param_2_lo,
                            Expression.constant(2, 4),
                        ),
                        Expression.constant(11, 4),
                    ),
                    param_3,
                ),
                conditions=[param_4_zero],
                order_key=5,
            ),
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.binary_op("INT_XOR", param_2_lo, param_3),
                conditions=[param_4_nonzero],
                order_key=5,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
        _param("param_3", size=4, index=2),
        _param("param_4", size=8, is_signed=False, index=3),
    ]

    normalized_zero = analyzer._normalize_expanded_return_value(
        expr,
        [param_4_zero],
    )
    normalized_nonzero = analyzer._normalize_expanded_return_value(
        expr,
        [param_4_nonzero],
    )

    assert normalized_zero.to_string() == (
        "(((((param_2 & 4294967295) * 2) + 11) + param_3) - (param_2 & 4294967295))"
    )
    assert normalized_nonzero.to_string() == (
        "(((param_2 & 4294967295) ^ param_3) - (param_2 & 4294967295))"
    )


def test_return_analyzer_canonicalizes_partially_replayed_post_state_before_reapplying_effects():
    stats = Expression.parameter("param_1", 0, size=8)
    a = Expression.parameter("param_2", 1, size=4)
    b = Expression.parameter("param_3", 2, size=4)
    delta = Expression.parameter("param_4", 3, size=4)
    nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", stats, Expression.constant(0, 8)),
        False,
    )
    count_addr = Expression.binary_op("INT_ADD", stats, Expression.constant(4, 8))
    partially_replayed = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_ADD", a, b),
            delta,
        ),
        Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_ADD", Expression.memory(count_addr, size=4), Expression.constant(1, 4)),
            Expression.constant(1, 4),
        ),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3", "param_4"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.binary_op("INT_ADD", a, b),
                conditions=[nonnull],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("param_1", 4, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(count_addr, size=4), Expression.constant(1, 4)),
                conditions=[nonnull],
                order_key=2,
            ),
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(stats, size=4), delta),
                conditions=[nonnull],
                order_key=3,
            ),
            StoreEffect(
                location=CanonicalLocation("param_1", 4, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(count_addr, size=4), Expression.constant(1, 4)),
                conditions=[nonnull],
                order_key=4,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
        _param("param_4", size=4, index=3),
    ]

    normalized = analyzer._normalize_expanded_return_value(partially_replayed, [nonnull])

    assert normalized.to_string() == "(((param_2 + param_3) + param_4) + ((MEM[(param_1 + 4)] + 1) + 1))"


def test_expression_expander_reduces_full_operation_trace_under_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.phi(
            [
                (no_swap, Expression.memory(a, size=4)),
                (swap_taken, Expression.memory(b, size=4)),
            ]
        ),
        Expression.phi(
            [
                (no_swap, Expression.memory(b, size=4)),
                (swap_taken, Expression.memory(a, size=4)),
            ]
        ),
    )
    expr.operands[0].size = 4
    expr.operands[1].size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return expr

    class FakeOp:
        def getMnemonic(self):
            return "INT_SUB"

        def getOutput(self):
            class Out:
                def getSize(self):
                    return 4
            return Out()

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    direct = expander._trace_operation_expression(FakeOp(), [no_swap], 0, output_size=4)

    assert direct is not None
    assert direct.to_string() == "(MEM[a] - MEM[b])"


def test_expression_expander_rewrites_observed_loads_before_post_state_canonicalization_duplicate_path():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [nonnull_a, nonnull_b],
    )

    assert canonicalized.to_string() == "(MEM[a] - MEM[b])"


def test_phi_handler_merge_preserves_same_value_with_distinct_conditions():
    a = Expression.parameter("a", 0, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)),
        False,
    )
    no_swap = swap_taken.negate()

    class FakeTracer:
        debug = False

    handler = PhiHandler(FakeTracer(), condition_tracker=None)
    merged = handler._merge_branches(
        [
            PhiExpandedBranch([swap_taken], Expression.memory(a, size=4)),
            PhiExpandedBranch([no_swap], Expression.memory(a, size=4)),
        ]
    )

    assert len(merged) == 2


def test_expression_expander_infers_multiequal_location_by_branch_match():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = swap_taken.negate()
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        debug = False

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    inferred = expander._infer_multiequal_canonical_location(
        [
            ExpandedValue(Expression.memory(a, size=4), [swap_taken]),
            ExpandedValue(Expression.memory(b, size=4), [no_swap]),
        ],
        depth=0,
    )

    assert inferred == CanonicalLocation("b", 0, 4)


def test_expression_expander_infers_multiequal_location_by_identical_observed_load():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = swap_taken.negate()
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        debug = False

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    inferred = expander._infer_multiequal_canonical_location(
        [
            ExpandedValue(Expression.memory(a, size=4), [swap_taken]),
            ExpandedValue(Expression.memory(a, size=4), [no_swap]),
        ],
        depth=0,
    )

    assert inferred == CanonicalLocation("a", 0, 4)


def test_expression_expander_reduces_full_operation_trace_under_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.phi(
            [
                (no_swap, Expression.memory(a, size=4)),
                (swap_taken, Expression.memory(b, size=4)),
            ]
        ),
        Expression.phi(
            [
                (no_swap, Expression.memory(b, size=4)),
                (swap_taken, Expression.memory(a, size=4)),
            ]
        ),
    )
    expr.operands[0].size = 4
    expr.operands[1].size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return expr

    class FakeOp:
        def getMnemonic(self):
            return "INT_SUB"

        def getOutput(self):
            class Out:
                def getSize(self):
                    return 4
            return Out()

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    direct = expander._trace_operation_expression(FakeOp(), [no_swap], 0, output_size=4)

    assert direct is not None
    assert direct.to_string() == "(MEM[a] - MEM[b])"


def test_expression_expander_rewrites_observed_loads_before_post_state_canonicalization():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [nonnull_a, nonnull_b],
    )

    assert canonicalized.to_string() == "(MEM[a] - MEM[b])"


def test_expression_expander_keeps_canonical_memory_without_read_order_key_unchanged():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )
    canonical = Expression.binary_op(
        "INT_SUB",
        Expression.memory(b, size=4),
        Expression.memory(a, size=4),
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        canonical,
        [swap_taken],
    )

    assert canonicalized.to_string() == "(MEM[b] - MEM[a])"


def test_expression_expander_expands_observed_load_phi_difference_into_cases():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return traced

    class FakeOp:
        def getMnemonic(self):
            return "INT_SUB"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            class In:
                def getDef(self):
                    return None
            return In()

        def getOutput(self):
            class Out:
                def getSize(self):
                    return 4
            return Out()

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    expanded = expander._expand_input_operation(
        FakeOp(),
        [nonnull_a, nonnull_b],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "(MEM[a] - MEM[b])"
    cond_text = " ".join(cond.to_string() for cond in expanded[0].conditions)
    assert "(a != 0)" in cond_text
    assert "(b != 0)" in cond_text


def test_canonicalize_post_state_subexpressions_rewrites_phi_operand_to_memory_location():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.phi(
            [
                (swap_taken, Expression.memory(a, size=4)),
                (None, Expression.memory(b, size=4)),
            ]
        ),
    )
    expr.operands[1].size = 4
    effects = [
        StoreEffect(
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    normalized = canonicalize_post_state_subexpressions(
        expr,
        [swap_taken],
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert normalized.to_string() == "(MEM[a] - MEM[b])"


def test_effect_summary_does_not_reapply_alias_equivalent_store_inside_rhs():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", dst, src),
        False,
    )
    original = Expression.memory(src, size=4)
    effect = StoreEffect(
        location=CanonicalLocation("dst", 0, 4),
        value=Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        conditions=[alias_cond],
        order_key=4,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [alias_cond],
        [effect],
        [
            _param("dst", size=8, is_signed=False),
            _param("src", size=8, is_signed=False, index=1),
            _param("delta", size=4, index=2),
        ],
    )

    assert rewritten.to_string() == "(MEM[dst] + delta)"


def test_effect_summary_does_not_reapply_when_expr_matches_phi_branch_value():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    choose_src = Expression.parameter("choose_src", 2, size=4)
    choose_true = Condition(
        Expression.binary_op("INT_NOTEQUAL", choose_src, Expression.constant(0, 4)),
        False,
    )
    choose_false = choose_true.negate()
    original = Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), Expression.constant(1, 4))
    effect = StoreEffect(
        location=CanonicalLocation("dst", 0, 4),
        value=Expression.phi(
            [
                (choose_true, Expression.memory(src, size=4)),
                (None, Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), Expression.constant(1, 4))),
            ]
        ),
        conditions=[],
        order_key=3,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [choose_false],
        [effect],
        [
            _param("dst", size=8, is_signed=False),
            _param("src", size=8, is_signed=False, index=1),
            _param("choose_src", size=4, index=2),
        ],
    )

    assert rewritten.to_string() == "(MEM[dst] + 1)"


def test_effect_summary_does_not_reapply_when_expr_matches_true_phi_branch_value():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    choose_src = Expression.parameter("choose_src", 2, size=4)
    choose_true = Condition(
        Expression.binary_op("INT_NOTEQUAL", choose_src, Expression.constant(0, 4)),
        False,
    )
    original = Expression.memory(src, size=4)
    effect = StoreEffect(
        location=CanonicalLocation("dst", 0, 4),
        value=Expression.phi(
            [
                (choose_true, Expression.memory(src, size=4)),
                (None, Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), Expression.constant(1, 4))),
            ]
        ),
        conditions=[],
        order_key=3,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [choose_true],
        [effect],
        [
            _param("dst", size=8, is_signed=False),
            _param("src", size=8, is_signed=False, index=1),
            _param("choose_src", size=4, index=2),
        ],
    )

    assert rewritten.to_string() == "MEM[src]"


def test_effect_summary_resolves_callind_target_from_traced_constant():
    class FakeVarnode:
        def __init__(self, is_constant=False):
            self._is_constant = is_constant

        def isConstant(self):
            return self._is_constant

    class FakeAddressSpace:
        def getAddress(self, value):
            return value

    class FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return FakeAddressSpace()

    class FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class FakeFunctionManager:
        def getFunctionAt(self, addr):
            if addr == 0x401000:
                return FakeFunction("callee")
            return None

    class FakeProgram:
        def getAddressFactory(self):
            return FakeAddressFactory()

        def getFunctionManager(self):
            return FakeFunctionManager()

    class FakeTracer:
        def __init__(self):
            self.program = FakeProgram()

        def _get_function_name(self, _addr_varnode):
            return "UNKNOWN_FUNC"

        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.constant(0x401000, 8)

    class FakeOp:
        def __init__(self):
            self._input = FakeVarnode(is_constant=False)

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input

        def getMnemonic(self):
            return "CALLIND"

    assert _resolve_call_target_name(FakeTracer(), FakeOp()) == "callee"


def test_effect_summary_resolves_call_target_from_traced_constant():
    class FakeVarnode:
        def __init__(self, is_constant=False):
            self._is_constant = is_constant

        def isConstant(self):
            return self._is_constant

    class FakeAddressSpace:
        def getAddress(self, value):
            return value

    class FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return FakeAddressSpace()

    class FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class FakeFunctionManager:
        def getFunctionAt(self, addr):
            if addr == 0x401000:
                return FakeFunction("callee")
            return None

        def getFunctionContaining(self, addr):
            return self.getFunctionAt(addr)

    class FakeProgram:
        def getAddressFactory(self):
            return FakeAddressFactory()

        def getFunctionManager(self):
            return FakeFunctionManager()

    class FakeTracer:
        def __init__(self):
            self.program = FakeProgram()

        def _get_function_name(self, _addr_varnode):
            return "UNKNOWN_FUNC"

        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.constant(0x401000, 8)

    class FakeOp:
        def __init__(self):
            self._input = FakeVarnode(is_constant=False)

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input

        def getMnemonic(self):
            return "CALL"

    assert _resolve_call_target_name(FakeTracer(), FakeOp()) == "callee"


def test_effect_summary_prefers_traced_constant_over_synthetic_fun_name():
    class FakeVarnode:
        def __init__(self, is_constant=False):
            self._is_constant = is_constant

        def isConstant(self):
            return self._is_constant

    class FakeAddressSpace:
        def getAddress(self, value):
            return value

    class FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return FakeAddressSpace()

    class FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class FakeFunctionManager:
        def getFunctionAt(self, addr):
            if addr == 0x401000:
                return FakeFunction("callee")
            return None

        def getFunctionContaining(self, addr):
            return self.getFunctionAt(addr)

    class FakeProgram:
        def getAddressFactory(self):
            return FakeAddressFactory()

        def getFunctionManager(self):
            return FakeFunctionManager()

    class FakeTracer:
        def __init__(self):
            self.program = FakeProgram()

        def _get_function_name(self, _addr_varnode):
            return "FUN_401000"

        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.constant(0x401000, 8)

    class FakeOp:
        def __init__(self):
            self._input = FakeVarnode(is_constant=False)

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input

        def getMnemonic(self):
            return "CALL"

    assert _resolve_call_target_name(FakeTracer(), FakeOp()) == "callee"


def test_call_effect_summary_policy_accepts_simple_param_store_summary():
    summary = EffectSummary(
        parameter_names=["ptr", "value"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("ptr", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(Expression.parameter("ptr", 0, size=8), size=4),
                    Expression.parameter("value", 1, size=4),
                ),
                conditions=[],
                order_key=1,
            )
        ],
    )

    assert is_call_effect_summary_allowed(summary)


def test_call_effect_summary_policy_rejects_nested_call_values():
    summary = EffectSummary(
        parameter_names=["ptr"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("ptr", 0, 4),
                value=Expression.call("callee", [Expression.parameter("ptr", 0, size=8)]),
                conditions=[],
                order_key=1,
            )
        ],
    )

    assert not is_call_effect_summary_allowed(summary)


def test_call_effect_summary_policy_rejects_unsupported_nested_calls():
    summary = EffectSummary(
        parameter_names=["ptr"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("ptr", 0, 4),
                value=Expression.constant(1, 4),
                conditions=[],
                order_key=1,
            )
        ],
        has_unsupported_call=True,
    )

    assert not is_call_effect_summary_allowed(summary)


def test_expander_combines_load_inputs_into_memory_expression():
    tracer = type("Tracer", (), {"debug": False})()
    expander = ExpressionExpander(tracer, condition_tracker=None, debug=False)

    result = expander._combine_input_expansions_with_conditions(
        "LOAD",
        [
            [ExpandedValue(Expression.constant(0x1B1, 4), [])],
            [ExpandedValue(Expression.parameter("ptr", 0, size=8), [])],
        ],
        [],
        0,
        output_size=4,
    )

    assert len(result) == 1
    assert result[0].value.expr_type.name == "MEMORY"
    assert result[0].value.to_string() == "MEM[ptr]"


def test_expander_resolves_indirect_stack_slot_read_via_effect_summary():
    class FakeOutputVarnode:
        def getHigh(self):
            return None

    class FakeTracer:
        debug = False

        def _get_storage_info_from_varnode(self, _varnode):
            return StorageInfo(**_stack_storage(-0x1C, size_bytes=4))

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=EffectSummary(
            parameter_names=["a", "b"],
            effects=[
                StoreEffect(
                    location=CanonicalLocation("__locbase__stackframe", -0x1C, 4),
                    value=Expression.binary_op(
                        "INT_ADD",
                        Expression.parameter("a", 0, size=4),
                        Expression.parameter("b", 1, size=4),
                    ),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
        parameters=[
            _param("a", size=4, is_signed=False, index=0),
            _param("b", size=4, is_signed=False, index=1),
        ],
    )

    result = expander._combine_input_expansions_with_conditions(
        "INDIRECT",
        [
            [ExpandedValue(Expression.constant(0, 4), [])],
            [ExpandedValue(Expression.constant(0x28, 4), [])],
        ],
        [],
        0,
        output_size=4,
        output_varnode=FakeOutputVarnode(),
    )

    assert len(result) == 1
    assert result[0].value.to_string() == "(a + b)"


def test_type_fixer_does_not_pattern_fix_pointer_types():
    fixer = object.__new__(TypeFixer)
    fixer.config = TypeFixerConfig()
    fixer.debug = False

    assert fixer._should_fix_type("undefined4")
    assert not fixer._should_fix_type("undefined4 *")


def test_return_analyzer_find_function_by_name_resolves_fun_address_via_containing():
    class _FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class _FakeFunctionManager:
        def __init__(self, containing):
            self._containing = containing

        def getFunctions(self, _forward):
            return []

        def getFunctionAt(self, _addr):
            return None

        def getFunctionContaining(self, _addr):
            return self._containing

    class _FakeAddressSpace:
        def getAddress(self, value):
            return value

    class _FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return _FakeAddressSpace()

    class _FakeProgram:
        def __init__(self, containing):
            self._manager = _FakeFunctionManager(containing)
            self._factory = _FakeAddressFactory()

        def getFunctionManager(self):
            return self._manager

        def getAddressFactory(self):
            return self._factory

    analyzer = ReturnAnalyzer(_FakeProgram(_FakeFunction("mem_void_write_if_needed")), debug=False)

    resolved = analyzer._find_function_by_name("FUN_120001514")

    assert resolved is not None
    assert resolved.getName() == "mem_void_write_if_needed"


def test_tracer_get_function_name_accepts_ram_address_varnode():
    class _FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class _FakeFunctionManager:
        def __init__(self, containing):
            self._containing = containing

        def getFunctionAt(self, _addr):
            return None

        def getFunctionContaining(self, _addr):
            return self._containing

    class _FakeProgram:
        def __init__(self, containing):
            self._manager = _FakeFunctionManager(containing)

        def getFunctionManager(self):
            return self._manager

    class _FakeSpace:
        def isRegisterSpace(self):
            return False

        def isUniqueSpace(self):
            return False

        def isConstantSpace(self):
            return False

    class _FakeAddress:
        def __init__(self, offset):
            self._offset = offset
            self._space = _FakeSpace()

        def getAddressSpace(self):
            return self._space

        def getOffset(self):
            return self._offset

    class _FakeVarnode:
        def __init__(self, offset):
            self._address = _FakeAddress(offset)

        def isConstant(self):
            return False

        def getAddress(self):
            return self._address

    tracer = object.__new__(PcodeTracer)
    tracer.program = _FakeProgram(_FakeFunction("mem_void_write_if_needed"))

    resolved = tracer._get_function_name(_FakeVarnode(0x120001514))

    assert resolved == "mem_void_write_if_needed"
