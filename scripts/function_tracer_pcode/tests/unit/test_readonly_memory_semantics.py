# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.memory_resolver import concretize_readonly_loads
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.normalize import (
    NormalizationContext,
    normalize_expression,
)
from scripts.function_tracer_pcode.model import (
    AddressValueRef,
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
    ReturnInfo,
)


def _param(name: str, *, size: int, is_signed: bool) -> dict:
    return {
        "name": name,
        "size": size,
        "is_signed": is_signed,
    }


def test_memory_resolver_concretizes_structured_mips_pic_readonly_jump_table() -> None:
    param = Expression.parameter("param_1", 0, size=8)
    subpiece = Expression.binary_op("SUBPIECE", param, Expression.constant(0, 4))
    subpiece.size = 4
    index_expr = Expression.unary_op("INT_SEXT", subpiece)
    index_expr.size = 8
    anchor_ref = AddressValueRef(
        address_offset=0x00112058,
        source="unit_test",
        display_hint="mips_pic_anchor",
        space_name="ram",
        symbol_name="lookup_anchor",
        block_name=".rodata",
        is_initialized=True,
        can_read=True,
        can_write=False,
        can_execute=False,
        is_volatile=False,
    )
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.variable("mips_pic_anchor", size=8, runtime_ref=anchor_ref),
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

    assert resolved.expr_type == ExpressionType.PHI
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [1, 1, 2, 2]


def test_memory_resolver_concretizes_intrinsic_ptrsub_ptradd_with_constant_address_object() -> None:
    index = Expression.parameter("index", 0, size=4)
    widened_index = Expression.unary_op("INT_ZEXT", index)
    widened_index.size = 8
    anchor_ref = AddressValueRef(
        address_offset=0x00112008,
        source="unit_test",
        display_hint="mips_pic_ptr_anchor",
        space_name="ram",
        symbol_name="PTR_lookup_table",
        block_name=".rodata",
        is_initialized=True,
        can_read=True,
        can_write=False,
        can_execute=False,
        is_volatile=False,
    )
    anchor_expr = Expression.constant(
        anchor_ref.address_offset,
        size=8,
        runtime_ref=anchor_ref,
    )
    base_expr = Expression.intrinsic(
        "PTRSUB",
        [Expression.constant(0, 8), anchor_expr],
        size=8,
        opcode=PTRSUB_OPCODE,
    )
    address_expr = Expression.intrinsic(
        "PTRADD",
        [base_expr, widened_index, Expression.constant(4, 8)],
        size=8,
        opcode=PTRADD_OPCODE,
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", index, Expression.constant(4, 4)),
        False,
    )
    table = {
        0x00112008: 11,
        0x0011200C: 13,
        0x00112010: 17,
        0x00112014: 19,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("index", size=4, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type == ExpressionType.PHI
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [11, 13, 17, 19]


def test_memory_resolver_concretizes_intrinsic_ptrsub_got_anchor_via_image_relative_pointee() -> None:
    index = Expression.parameter("index", 0, size=4)
    widened_index = Expression.unary_op("INT_ZEXT", index)
    widened_index.size = 8
    got_anchor_ref = AddressValueRef(
        address_offset=0x120013E20,
        source="unit_test",
        display_hint="mips_got_anchor",
        space_name="ram",
        symbol_name="PTR_table_slot",
        block_name=".got",
        is_initialized=True,
        can_read=True,
        can_write=False,
        can_execute=False,
        is_volatile=False,
    )
    got_anchor_expr = Expression.constant(
        got_anchor_ref.address_offset,
        size=8,
        runtime_ref=got_anchor_ref,
    )
    base_expr = Expression.intrinsic(
        "PTRSUB",
        [Expression.constant(0, 8), got_anchor_expr],
        size=8,
        opcode=PTRSUB_OPCODE,
    )
    address_expr = Expression.intrinsic(
        "PTRADD",
        [base_expr, widened_index, Expression.constant(4, 8)],
        size=8,
        opcode=PTRADD_OPCODE,
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", index, Expression.constant(4, 4)),
        False,
    )
    image_base = 0x00100000
    table_base = image_base + 0x13A0
    table = {
        got_anchor_ref.address_offset: 0x13A0,
        table_base + 0: 5,
        table_base + 4: 5,
        table_base + 8: 7,
        table_base + 12: 11,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("index", size=4, is_signed=False)],
        lambda addr, size: table.get(addr),
        image_base=image_base,
        debug=False,
    )

    assert resolved.expr_type == ExpressionType.PHI
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [5, 5, 7, 11]


def test_normalize_expression_preserves_phi_fallback_branch_without_condition() -> None:
    param = Expression.parameter("param_1", 0, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", param, Expression.constant(6, 4)),
        False,
    )
    phi = Expression.phi(
        [
            (cond, Expression.constant(5, 4)),
            (None, Expression.variable("fallback_load", size=4)),
        ]
    )
    phi.size = 4

    normalized = normalize_expression(phi, NormalizationContext())

    assert normalized.expr_type == ExpressionType.PHI
    assert len(normalized.value) == 2
    assert normalized.value[0][0] is not None
    assert normalized.value[1][0] is None
    assert normalized.value[1][1].expr_type == ExpressionType.VARIABLE


def test_memory_address_smt_uses_structured_runtime_address_symbol() -> None:
    runtime_ref = AddressValueRef(
        address_offset=0x00112058,
        source="unit_test",
        display_hint="structured_anchor",
        space_name="ram",
        symbol_name="lookup_anchor",
        block_name=".rodata",
        is_initialized=True,
        can_read=True,
        can_write=False,
        can_execute=False,
        is_volatile=False,
    )
    expr = Expression.memory(
        Expression.variable("structured_anchor", size=8, runtime_ref=runtime_ref),
        size=4,
    )

    assert expr.to_smt() == "(select mem32 (_ bv1122392 64))"


def test_formula_builder_skips_concrete_address_anchor_extra_vars() -> None:
    anchor_ref = AddressValueRef(
        address_offset=0x00112058,
        source="unit_test",
        display_hint="lookup_anchor",
        space_name="ram",
        symbol_name="PTR_00112058",
        block_name=".rodata",
        is_initialized=True,
        can_read=True,
        can_write=False,
        can_execute=False,
        is_volatile=False,
    )
    index = Expression.parameter("param_1", 0, size=4)
    widened_index = Expression.unary_op("INT_ZEXT", index)
    widened_index.size = 8
    load_expr = Expression.memory(
        Expression.binary_op(
            "INT_ADD",
            Expression.variable("lookup_anchor", size=8, runtime_ref=anchor_ref),
            Expression.binary_op(
                "INT_MULT",
                widened_index,
                Expression.constant(4, 8),
            ),
        ),
        size=4,
    )

    analysis = FunctionReturnAnalysis(
        function_name="mem_rodata_lookup_like",
        entry_point="0x1000",
        parameters=[_param("param_1", size=4, is_signed=False)],
        returns=[ReturnInfo(address="0x1004", value=load_expr, conditions=[])],
        return_type="int",
    )

    result = FormulaBuilder(debug=False).build_equivalence_formula_extended(
        analysis,
        analysis,
    )

    assert "lookup_anchor_1" not in result.formula
    assert "lookup_anchor_2" not in result.formula
    assert "Extra variables for mem_rodata_lookup_like" not in result.formula
    assert "(_ bv1122392 64)" in result.formula
