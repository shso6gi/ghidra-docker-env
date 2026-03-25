# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.memory_resolver import (
    collect_memory_bit_widths_from_analysis,
    concretize_readonly_loads,
)
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    StoreEffect,
    _resolve_call_target_name,
    is_call_effect_summary_allowed,
    build_void_effect_summary_expr,
    canonicalize_param_location,
    rewrite_loads_from_effects,
    substitute_location,
    EffectSummary,
)
from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
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
