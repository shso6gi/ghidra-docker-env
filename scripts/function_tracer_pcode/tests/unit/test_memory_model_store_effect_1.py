from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *

def test_summarize_store_effects_marks_real_op_unknown_order_incomplete():
    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        pass

    class FakeStoreOp:
        __module__ = "ghidra.program.model.pcode"

        def getMnemonic(self):
            return "STORE"

        def getSeqnum(self):
            raise RuntimeError("seqnum unavailable")

    class FakeBlockInfo:
        pcode_ops = [FakeStoreOp()]

    summary = summarize_store_effects(
        [FakeBlockInfo()],
        FakeTracer(),
        FakeConditionTracker(),
        [_param("dst", index=0, size=8)],
    )

    assert summary.effects == []
    assert summary.incomplete_reasons == ("effect_order_unavailable",)

def test_normalize_expression_preserves_memory_identity_metadata():
    location = _loc("trace", 0, 4)
    traced_load = Expression.memory(
        Expression.parameter("trace", 0, size=8),
        size=4,
        read_order_key=42,
        runtime_ref=location,
    )
    expr = Expression.binary_op("INT_ADD", traced_load, Expression.constant(1, 4))

    normalized = normalize_expression(expr)
    normalized_memory = next(
        operand for operand in normalized.operands if operand.expr_type == ExpressionType.MEMORY
    )

    assert normalized_memory.read_order_key == 42
    assert getattr(normalized_memory, "runtime_ref", None) == location

def test_concretize_readonly_loads_preserves_unresolved_memory_identity_metadata():
    location = _loc("trace", 0, 4)
    expr = Expression.memory(
        Expression.parameter("trace", 0, size=8),
        size=4,
        read_order_key=17,
        runtime_ref=location,
    )

    rewritten = concretize_readonly_loads(
        expr,
        [],
        [_param("trace", size=8, is_signed=False)],
        lambda *_args: None,
    )

    assert rewritten.read_order_key == 17
    assert getattr(rewritten, "runtime_ref", None) == location

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

def test_memory_resolver_concretizes_small_readonly_jump_table():
    param = Expression.parameter("param_1", 0, size=8)
    index_expr = Expression.unary_op(
        "INT_SEXT",
        Expression.binary_op("SUBPIECE", param, Expression.constant(0, 4)),
    )
    index_expr.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        _addr_var("PTR_00112058", 0x00112058, size=8),
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

def test_memory_resolver_concretizes_direct_readonly_scalar_symbol_in_value_position():
    expr = Expression.binary_op(
        "INT_ADD",
        _addr_var("DAT_00113090", 0x00113090, size=8),
        Expression.constant(1, 8),
    )

    table = {
        0x00113090: 0x401120,
    }

    resolved = concretize_readonly_loads(
        expr,
        [],
        [],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "BINARY_OP"
    assert resolved.operands[0].expr_type.name == "CONSTANT"
    assert resolved.operands[0].value == 0x401120
    assert resolved.operands[1].expr_type.name == "CONSTANT"
    assert resolved.operands[1].value == 1

def test_memory_resolver_does_not_concretize_plain_integer_constant_in_value_position():
    expr = Expression.binary_op(
        "INT_XOR",
        Expression.parameter("param_1", index=0, size=8),
        Expression.constant(0x00113090, 8),
    )

    resolved = concretize_readonly_loads(
        expr,
        [],
        [],
        lambda _addr, _size: 0x8000000000000000,
        debug=False,
    )

    assert resolved.operands[1].expr_type.name == "CONSTANT"
    assert resolved.operands[1].value == 0x00113090

def test_memory_resolver_concretizes_direct_unknown_symbol_when_readable():
    expr = Expression.binary_op(
        "INT_ADD",
        _addr_var("UNK_00113090", 0x00113090, size=8),
        Expression.constant(1, 8),
    )

    table = {
        0x00113090: 0x401120,
    }

    resolved = concretize_readonly_loads(
        expr,
        [],
        [],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "BINARY_OP"
    assert resolved.operands[0].expr_type.name == "CONSTANT"
    assert resolved.operands[0].value == 0x401120
    assert resolved.operands[1].expr_type.name == "CONSTANT"
    assert resolved.operands[1].value == 1

def test_memory_resolver_concretizes_jump_table_when_additive_index_is_wrapped_by_mul_one():
    param = Expression.parameter("param_1", 0, size=8)
    subpiece = Expression.binary_op("SUBPIECE", param, Expression.constant(0, 4))
    subpiece.size = 4
    index_expr = Expression.unary_op("INT_SEXT", subpiece)
    index_expr.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        _addr_var("PTR_00112058", 0x00112058, size=8),
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
        _addr_var("PTR_00112058", 0x00112058, size=8),
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
        location=_loc("ptr", 0, 4),
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
            location=_loc("ptr", 0, 4),
            value=value,
            conditions=[positive],
            order_key=2,
        ),
        StoreEffect(
            location=_loc("ptr", 0, 4),
            value=Expression.unary_op("INT_2COMP", value),
            conditions=[non_positive],
            order_key=1,
        ),
    ]

    summary = build_void_effect_summary_expr(effects)

    assert summary is not None
    assert summary.expr_type.name == "BINARY_OP"
    assert summary.operator == "PIECE"

def test_effect_summary_falls_back_to_pre_state_value_for_unwritten_stack_local_read():
    params = [_param("guard", size=8, is_signed=False)]
    slot_expr = Expression.variable(
        "local_guard",
        size=8,
        storage_info=StorageInfo(**_stack_storage(8, size_bytes=8)),
    )
    location = canonicalize_location(slot_expr, params, size=8)
    assert location is not None
    fallback = Expression.variable("guard_before_call", size=8)

    rewritten = rewrite_location_read_from_effects(
        location,
        fallback,
        [],
        [
            StoreEffect(
                location=_loc("guard", 0, 8),
                value=Expression.constant(1, 8),
                conditions=[],
                order_key=1,
            )
        ],
        params,
    )

    assert rewritten.to_string() == "guard_before_call"

def test_effect_summary_does_not_synthesize_parameter_refs_from_names():
    summary = EffectSummary(parameter_names=["param_1"], effects=[])
    assert summary.parameter_refs == []

def test_choose_effect_substitution_args_does_not_invent_positional_parameters():
    args = [Expression.variable("opaque0", size=8), Expression.variable("opaque1", size=8)]

    chosen = _choose_effect_substitution_args(
        _loc("a", 0, 4),
        ["a", "b"],
        args,
        [
            _param("param_1", size=8, is_signed=False, index=0),
            _param("param_2", size=8, is_signed=False, index=1),
        ],
    )

    assert chosen is args

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
    assert summary.effects[0].location == _loc(
        "slot",
        0,
        4,
        steps=(LocationStep("deref", 8),),
    )
    assert summary.effects[0].value.to_string() == "value"

def test_summarize_store_effects_marks_store_block_incomplete_when_paths_unavailable():
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

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return []

    class FakeTracer:
        def trace_varnode(self, _varnode, use_cache=False):
            raise AssertionError("path-incomplete store blocks must not be scanned")

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeStoreOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [_param("slot", size=8, is_signed=False, index=0)],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ("effect_summary_path_coverage_incomplete",)

def test_summarize_store_effects_ignores_proven_unreachable_effect_block():
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

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete_unreachable"
        condition_paths = []

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def trace_varnode(self, _varnode, use_cache=False):
            raise AssertionError("unreachable effect blocks must not be scanned")

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeStoreOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [_param("slot", size=8, is_signed=False, index=0)],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is False
    assert summary.incomplete_reasons == ()

def test_summarize_store_effects_resolves_path_conditioned_indirect_targets():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallIndOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]

        def getMnemonic(self):
            return "CALLIND"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    mode_is_zero = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.parameter("mode", 0, size=4),
            Expression.constant(0, 4),
        )
    )
    mode_is_one = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.parameter("mode", 0, size=4),
            Expression.constant(1, 4),
        )
    )

    class FakeTracer:
        program = None

        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 1, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 2, size=4)
            return Expression.phi(
                [
                    (mode_is_zero, Expression.constant(0x1000, 8)),
                    (mode_is_one, Expression.constant(0x2000, 8)),
                ]
            )

    seen_targets = []

    def direct_call_summary(target_ref, args):
        seen_targets.append((target_ref.stable_key(), tuple(arg.name for arg in args)))
        return EffectSummary(
            parameter_names=["lhs", "rhs"],
            effects=[],
            has_unsupported_call=False,
        )

    call_op = FakeCallIndOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("mode", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0")),
            _param("lhs", size=4, index=1, storage=_reg_storage("w1", size_bytes=4, register_name="w1")),
            _param("rhs", size=4, index=2, storage=_reg_storage("w2", size_bytes=4, register_name="w2")),
        ],
        direct_call_summary=direct_call_summary,
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0")),
            _param("rhs", size=4, index=1, storage=_reg_storage("w1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is False
    assert summary.incomplete_reasons == ()
    assert sorted(target for target, _args in seen_targets) == [
        ("code_address", None, 0x1000),
        ("code_address", None, 0x2000),
    ]
    assert all(args == ("lhs", "rhs") for _target, args in seen_targets)

def test_summarize_store_effects_falls_back_to_pathless_target_identity(monkeypatch):
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallIndOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("dst", 8),
            ]

        def getMnemonic(self):
            return "CALLIND"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    path_cond = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.parameter("selector", 0, size=4),
            Expression.constant(1, 4),
        )
    )
    target_cond = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.parameter("selector", 0, size=4),
            Expression.constant(0, 4),
        )
    )

    class FakeCoverage:
        status = "complete"
        condition_paths = [[path_cond]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        program = None

        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "dst":
                return Expression.parameter("dst", 1, size=8)
            return Expression.unknown("target_requires_pathless_fallback")

    seen_condition_lengths = []

    def fake_resolve_call_targets(_tracer, _op, **kwargs):
        conditions = list(kwargs.get("conditions") or ())
        seen_condition_lengths.append(len(conditions))
        if conditions:
            return []
        return [(CallTargetRef.from_code_address(0x401000), [target_cond])]

    monkeypatch.setattr(
        effect_summary_module,
        "resolve_call_targets",
        fake_resolve_call_targets,
    )

    def direct_call_summary(_target_ref, _args):
        return EffectSummary(
            parameter_names=["dst"],
            parameter_refs=[LocationBaseRef.parameter("dst", index=0)],
            effects=[
                StoreEffect(
                    location=_loc("dst", 0, 4),
                    value=Expression.constant(1, 4),
                    conditions=[],
                    order_key=1,
                )
            ],
            has_unsupported_call=False,
        )

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallIndOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("selector", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0")),
            _param("dst", size=8, index=1, storage=_reg_storage("x1", size_bytes=8, register_name="x1")),
        ],
        direct_call_summary=direct_call_summary,
        resolve_callee_parameters=lambda _target_ref: [
            _param("dst", size=8, index=0, storage=_reg_storage("x0", size_bytes=8, register_name="x0")),
        ],
        debug=False,
    )

    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    assert seen_condition_lengths == [1, 0]
    condition_texts = [cond.to_string() for cond in summary.effects[0].conditions]
    assert "(selector == 1)" in condition_texts

def test_summarize_store_effects_keeps_constant_actual_missing_summary_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("literal", 8),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("missing_uintptr_helper")

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "literal":
                return Expression.constant(0x1234, size=8)
            return Expression.constant(0, max(1, varnode.getSize()))

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("ptr", size=8, index=0, storage=_reg_storage("x0", register_name="x0"), data_type="int *"),
        ],
        direct_call_summary=lambda _target_ref, _args: None,
        resolve_callee_parameters=lambda _target_ref: [
            _param("as_int", size=8, index=0, storage=_reg_storage("x0", register_name="x0"), data_type="ulong"),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()

def test_effect_summary_path_coverage_note_is_sat_unsafe():
    analysis = FunctionReturnAnalysis(
        function_name="path_incomplete_store",
        entry_point="0x5000",
        parameters=[],
        returns=[
            ReturnInfo(
                address="0x5000",
                value=Expression.constant(0, 4),
                conditions=[],
            )
        ],
        effect_summary=EffectSummary(
            parameter_names=[],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=("effect_summary_path_coverage_incomplete",),
        ),
    )

    reasons = analysis.get_decisive_sat_unsafety_reasons()
    assert "effect_summary_path_coverage_incomplete" in reasons
    assert "unsupported_call_effect_summary" in reasons

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

    assert location == _loc("ptr", 4, 4)

def test_effect_summary_keeps_load_when_multiple_writes_overlap():
    ptr = Expression.parameter("ptr", 0, size=8)
    original = Expression.memory(ptr, size=4)
    effects = [
        StoreEffect(
            location=_loc("ptr", 0, 4),
            value=Expression.constant(1, 4),
            conditions=[],
            order_key=2,
        ),
        StoreEffect(
            location=_loc("ptr", 0, 4),
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
            location=_loc("ptr", 0, 4),
            value=Expression.parameter("v_true", 2, size=4),
            conditions=[positive],
            order_key=2,
        ),
        StoreEffect(
            location=_loc("ptr", 0, 4),
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
        location=_loc("box", 4, 4),
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
        location=_loc("box", 4, 4),
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
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
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
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
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
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
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
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
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

def test_expression_expander_canonicalizes_direct_traced_memory_leaf_via_effect_summary():
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["ptr", "value"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.unary_op("INT_2COMP", value),
                conditions=[ptr_nonnull],
                order_key=1,
            ),
        ],
    )

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return Expression.memory(ptr, size=4)

    class FakeOp:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("ptr", size=8, is_signed=False),
            _param("value", size=4, is_signed=True, index=1),
        ],
    )

    canonicalized = expander._trace_operation_expression(FakeOp(), [ptr_nonnull], depth=0, output_size=4)

    assert canonicalized is not None
    assert canonicalized.to_string() == "MEM[ptr]"

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
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
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

def test_return_analyzer_effect_sensitive_rewrite_does_not_double_apply_outer_delta():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )
    negate_nonzero = negate_zero.negate()

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[value_nonnull, negate_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[value_nonnull, negate_nonzero],
                order_key=5,
            ),
        ],
    )

    results = analyzer._build_return_infos_from_expansions(
        "00100000",
        [
            ExpandedValue(
                Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                [value_nonnull, negate_nonzero],
            )
        ],
        return_index=0,
    )

    assert len(results) == 1
    assert results[0].value.to_string() == "(delta - MEM[value])"

def test_return_analyzer_materializes_normalized_composite_effect_value_at_root():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    copy_flag = Expression.parameter("copy_flag", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    accumulate_taken = Condition(
        Expression.binary_op("INT_EQUAL", copy_flag, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("copy_flag", size=4, is_signed=False, index=2),
    ]
    effect_summary = EffectSummary(
        parameter_names=["dst", "src", "copy_flag"],
        effects=[
            StoreEffect(
                location=_loc("dst", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(dst, size=4, read_order_key=10),
                    Expression.memory(src, size=4, read_order_key=11),
                ),
                conditions=[dst_nonnull, src_nonnull, accumulate_taken],
                order_key=7,
            ),
        ],
    )

    stale_replayed = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_ADD",
            Expression.memory(dst, size=4, runtime_ref=_loc("dst", 0, 4)),
            Expression.memory(src, size=4, runtime_ref=_loc("src", 0, 4)),
        ),
        Expression.memory(src, size=4, runtime_ref=_loc("src", 0, 4)),
    )

    normalized = analyzer._normalize_return_value_with_effect_summary(
        stale_replayed,
        [dst_nonnull, src_nonnull, accumulate_taken],
        effect_summary,
    )

    assert normalized is not None
    assert normalized.to_string() == "(MEM[dst] + MEM[src])"
    assert isinstance(getattr(normalized, "runtime_ref", None), PostStateValueRef)
    assert normalized.runtime_ref.location == _loc("dst", 0, 4)
