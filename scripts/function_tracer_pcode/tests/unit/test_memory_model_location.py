from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *

def test_memory_resolver_concretizes_direct_readonly_pointer_slot():
    load_expr = Expression.memory(
        _addr_var("PTR_ptr_op_add_00113090", 0x00113090, size=8),
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

def test_memory_resolver_concretizes_direct_readonly_constant_address_in_value_position():
    address = Expression.constant(0x00113090, 8)
    address.runtime_ref = AddressValueRef(
        address_offset=0x00113090,
        display_hint="DAT_00113090",
        symbol_name="DAT_00113090",
        is_initialized=True,
        can_read=True,
        can_write=False,
        is_volatile=False,
    )
    expr = Expression.binary_op(
        "INT_XOR",
        Expression.parameter("param_1", index=0, size=8),
        address,
    )

    table = {
        0x00113090: 0x8000000000000000,
    }

    resolved = concretize_readonly_loads(
        expr,
        [],
        [],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "BINARY_OP"
    assert resolved.operands[1].expr_type.name == "CONSTANT"
    assert resolved.operands[1].value == 0x8000000000000000

def test_memory_resolver_does_not_concretize_writable_constant_address_in_value_position():
    address = Expression.constant(0x00113090, 8)
    address.runtime_ref = AddressValueRef(
        address_offset=0x00113090,
        display_hint="global_00113090",
        symbol_name="global_00113090",
        is_initialized=True,
        can_read=True,
        can_write=True,
        is_volatile=False,
    )
    expr = Expression.binary_op(
        "INT_XOR",
        Expression.parameter("param_1", index=0, size=8),
        address,
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

def test_memory_resolver_does_not_concretize_constant_offset_literal_address():
    address = Expression.constant(0x00113090, 8)
    address.runtime_ref = AddressValueRef(
        address_offset=0x00113090,
        source="constant_offset",
        display_hint="DAT_00113090",
        symbol_name="DAT_00113090",
        is_initialized=True,
        can_read=True,
        can_write=False,
        is_volatile=False,
    )
    expr = Expression.binary_op(
        "INT_XOR",
        Expression.parameter("param_1", index=0, size=8),
        address,
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
    assert resolved.operands[1].runtime_ref.source == "constant_offset"

def test_memory_resolver_concretizes_mips_got_base_symbol_with_address_suffix():
    param = Expression.parameter("param_1", 0, size=8)
    address_expr = Expression.binary_op(
        "INT_ADD",
        _addr_var("PTR___DT_MIPS_BASE_ADDRESS_120011050", 0x120011050, size=8),
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

def test_effect_summary_accepts_variable_based_parameter_addresses():
    addr_expr = Expression.parameter("ptr", 0, size=8)

    location = canonicalize_param_location(
        addr_expr,
        [_param("ptr", size=8, is_signed=False)],
        size=4,
    )

    assert location == _loc("ptr", 0, 4)

def test_effect_summary_accepts_variable_plus_constant_parameter_addresses():
    addr_expr = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("box", 0, size=8),
        Expression.constant(4, 8),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("box", size=8, is_signed=False)],
        size=4,
    )

    assert location == _loc("box", 4, 4)

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

    assert location == _loc("param_1", 0, 4)

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
        base_ref=LocationBaseRef.parameter("slot", index=0),
        offset=0,
        size=4,
        steps=(LocationStep("deref", 8),),
    )

def test_memory_expression_for_location_reconstructs_double_indirect_location():
    expr = memory_expression_for_location(
        CanonicalLocation(
            base_ref=LocationBaseRef.parameter("slot", index=0),
            offset=0,
            size=4,
            steps=(LocationStep("deref", 8),),
        ),
        [_param("slot", size=8, is_signed=False)],
    )

    assert expr is not None
    assert expr.to_string() == "MEM[MEM[slot]]"

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

    assert location == _loc("__locbase__stackframe", -0x1C, 4)

def test_canonicalize_location_accepts_foldable_subpiece_constant_ptradd_index():
    params = [_param("param_1", size=8, is_signed=False)]
    pointer = Expression.parameter("param_1", index=0, size=8)
    masked_one = Expression.binary_op(
        "INT_AND",
        Expression.constant(1, size=8),
        Expression.constant(0xFFFFFFFF, size=8),
    )
    index = Expression.binary_op("SUBPIECE", masked_one, Expression.constant(0, size=4))
    index.size = 4
    address = Expression.intrinsic(
        "PTRADD",
        [pointer, Expression.unary_op("INT_ZEXT", index), Expression.constant(4, size=8)],
        size=8,
    )

    location = canonicalize_location(address, params, size=4)

    assert location == _loc("param_1", 4, 4)

def test_rewrite_location_read_from_effects_drops_stack_local_nonnull_phi_guard():
    params = [_param("a", size=4), _param("b", size=4, index=1)]
    location = _loc("__locbase__stackframe", -0x1C, 4)
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
        _build_parameter_replacements(
            [{"name": "out", "index": 2}],
            [
                Expression.binary_op(
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
            ],
        ),
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

def test_return_analyzer_keeps_stale_effect_value_wrapper_when_alias_is_not_definite():
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

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["dst", "src", "delta"],
        effects=[
            StoreEffect(
                location=_loc("dst", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
                conditions=[dst_nonnull, src_nonnull, alias_cond],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("src", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(src, size=4),
                    Expression.constant(4294967295, 4),
                ),
                conditions=[dst_nonnull, src_nonnull, alias_cond],
                order_key=20,
            ),
        ],
    )

    original = Expression.binary_op(
        "INT_ADD",
        Expression.memory(dst, size=4),
        Expression.constant(0, 4),
    )
    rewritten = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        Expression.constant(0, 4),
    )

    collapsed = analyzer._collapse_effect_sensitive_case_wrapper(
        original,
        rewritten,
        [dst_nonnull, src_nonnull],
        analyzer._current_effect_summary,
    )

    assert collapsed is not None
    assert not expression_contains_post_state_reads(collapsed)
    assert collapsed.to_string() == "(MEM[dst] + delta)"

def test_return_analyzer_rejects_no_rank_rewrite_that_drops_composite_location_wrapper():
    ptr = Expression.parameter("ptr", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("ptr", size=8, is_signed=False, index=0),
        _param("delta", size=4, index=1),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["ptr", "delta"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.memory(ptr, size=4),
                conditions=[ptr_nonnull],
                order_key=10,
            ),
        ],
    )

    original = Expression.binary_op(
        "INT_SUB",
        Expression.memory(ptr, size=4),
        delta,
    )
    rewritten = Expression.memory(ptr, size=4)

    accepted = analyzer._accept_effect_rewrite_without_rank_gain(
        original,
        rewritten,
        [ptr_nonnull],
        analyzer._current_effect_summary,
    )

    assert accepted is False

def test_find_matching_effect_value_uses_effect_guard_for_location_alias():
    left = Expression.parameter("param_1", 0, size=8)
    right = Expression.parameter("param_2", 1, size=8)
    read_from_right = Expression.memory(right, size=4)
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", left, right),
        False,
    )

    match = _find_matching_effect_value(
        read_from_right,
        _loc("param_2", 0, 4),
        [],
        [
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=read_from_right,
                conditions=[alias_cond],
                order_key=17,
            )
        ],
        [
            _param("param_1", size=8, index=0),
            _param("param_2", size=8, index=1),
        ],
    )

    assert match is not None
    assert match[0] == 17

def test_storage_location_base_matches_descriptor_storage_identity_key():
    register_base = LocationBaseRef.storage(
        space_id=0,
        space_name="register",
        offset=0x1234,
        size=8,
        display_hint="a0",
    )
    assert _parameter_base_ref_matches_descriptor(
        register_base,
        {
            "name": "arg",
            "storage": {
                "is_register": True,
                "space_name": "register",
                "space_id": 0,
                "offset": 0x1234,
                "size": 8,
                "size_bits": 64,
                "register_offset": 0x1234,
                "register_size": 8,
                "register_size_bits": 64,
                "base_register_offset": 0x1234,
                "base_register_size": 8,
                "base_register_size_bits": 64,
                "bit_offset_in_base": 0,
            },
        },
    )

    memory_base = LocationBaseRef.storage(
        space_id=1,
        space_name="stack",
        offset=0x30,
        size=4,
        display_hint="stack[0x30]",
    )
    assert _parameter_base_ref_matches_descriptor(
        memory_base,
        {"name": "stack_arg", "storage": _stack_storage(0x30, size_bytes=4)},
    )

    fragment_storage = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=0,
        offset=0x200,
        size=4,
        size_bits=32,
        register_offset=0x200,
        register_size=4,
        register_size_bits=32,
        base_register_offset=0x200,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=32,
    )
    fragment_base = LocationBaseRef.storage(
        space_id=0,
        space_name="register",
        offset=0x200,
        size=8,
        storage_identity_key=fragment_storage.storage_identity_key(),
        display_hint="a0_hi",
    )
    assert _parameter_base_ref_matches_descriptor(
        fragment_base,
        {"name": "a0_hi", "storage": fragment_storage},
    )
    coarse_base = LocationBaseRef.storage(
        space_id=0,
        space_name="register",
        offset=0x200,
        size=8,
        display_hint="a0",
    )
    assert fragment_base != coarse_base

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

def test_resolve_parameter_name_prefers_index_and_storage_over_stale_name():
    params = [
        _param(
            "param_1",
            size=8,
            is_signed=False,
            index=0,
            storage=_reg_storage("a0", size_bytes=8, register_name="a0"),
        ),
        _param(
            "param_2",
            size=8,
            is_signed=False,
            index=1,
            storage=_reg_storage("a1", size_bytes=8, register_name="a1"),
        ),
    ]

    expr = Expression.parameter(
        "stale_name",
        index=1,
        size=8,
        storage_info=StorageInfo(**_reg_storage("a1", size_bytes=8, register_name="a1")),
    )

    assert _resolve_parameter_name(expr, params) == "param_2"

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

    assert location == _loc("__locbase__stackframe", -0x30, 4)

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
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["value", "out"],
            parameter_refs=[
                LocationBaseRef.parameter("value", index=0),
                LocationBaseRef.parameter("out", index=1),
            ],
            effects=[
                StoreEffect(
                    location=_loc("out", 0, 4),
                    value=Expression.parameter("value", 0, size=4),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("value", size=8, is_signed=False, index=0),
            _param("out", size=8, is_signed=False, index=1),
        ],
        debug=False,
    )

    assert len(summary.effects) == 1
    assert summary.effects[0].location == _loc("__locbase__stackframe", -0x1C, 4)
    # callee の 4 byte の node は 8 byte の parameter `value` の下位 4 byte: 引数 param_1（8 byte）の下位 4 byte
    # （review 7。以前は 8 byte の param_1 を丸ごと入れていた）
    value = summary.effects[0].value
    assert value.expr_type.name == "BINARY_OP" and value.operator == "SUBPIECE" and value.size == 4
    assert value.operands[0].name == "param_1" and value.operands[1].value == 0

def test_summarize_store_effects_keeps_pointer_actual_to_address_sized_scalar_missing_summary_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("ptr", 8),
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

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "ptr":
                return Expression.parameter("ptr", 0, data_type="int *", size=8)
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

def test_effect_summary_accepts_mul_by_one_wrapped_parameter_addresses():
    addr_expr = Expression.binary_op(
        "INT_MULT",
        Expression.constant(1, 8),
        Expression.binary_op(
            "INT_ADD",
            Expression.parameter("box", 0, size=8),
            Expression.constant(4, 8),
        ),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("box", size=8, is_signed=False)],
        size=4,
    )

    assert location == _loc("box", 4, 4)

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

    assert location == _loc("ptr", 0, 4)

def test_effect_summary_does_not_rebind_no_index_location_by_parameter_name():
    unresolved_location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("dst"),
        offset=0,
        size=4,
    )

    summary = EffectSummary(
        parameter_names=["dst", "dst"],
        effects=[
            StoreEffect(
                location=unresolved_location,
                value=Expression.constant(1, size=4),
                conditions=[],
                order_key=1,
            )
        ],
    )

    bound_ref = summary.effects[0].location.base_ref
    assert isinstance(bound_ref, LocationBaseRef)
    assert bound_ref.is_parameter()
    assert bound_ref.parameter_index is None

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
    expander._get_edge_condition = lambda from_block_info, to_block: (
        no_swap if from_block_info.index == 3 else swap_taken
    )

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
        ("MEM[b]", (swap_taken.to_string(),)),
    }

def test_expression_expander_keeps_multiequal_location_leaf_when_outer_update_reuses_it():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )
    negate_nonzero = negate_zero.negate()
    effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[negate_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[negate_nonzero],
                order_key=5,
            ),
        ],
    )

    pred_zero = object()
    pred_nonzero = object()

    class FakeInputVarnode:
        def __init__(self, expr=None, def_op=None, size=4):
            self.expr = expr
            self._def_op = def_op
            self._size = size

        def getDef(self):
            return self._def_op

        def getSize(self):
            return self._size

        def getHigh(self):
            return None

    class FakeParent:
        def getInSize(self):
            return 2

        def getIn(self, index):
            return [pred_zero, pred_nonzero][index]

    class FakeMultiequalOp:
        def getParent(self):
            return FakeParent()

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            return [
                FakeInputVarnode(Expression.memory(value, size=4)),
                FakeInputVarnode(Expression.memory(value, size=4)),
            ][index]

        def getMnemonic(self):
            return "MULTIEQUAL"

    phi = FakeMultiequalOp()

    class FakeOutput:
        def getSize(self):
            return 4

    class FakeAddOp:
        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            return [
                FakeInputVarnode(def_op=phi, size=4),
                FakeInputVarnode(expr=delta, size=4),
            ][index]

        def getOutput(self):
            return FakeOutput()

    class FakeBlockInfo:
        def __init__(self, index):
            self.index = index

    class FakeConditionTracker:
        def get_block_by_hash(self, block):
            if block is pred_zero:
                return FakeBlockInfo(3)
            if block is pred_nonzero:
                return FakeBlockInfo(4)
            return None

        def get_all_valid_paths_to_block(self, target_block):
            return [[]]

    class FakeTracer:
        def trace_varnode(self, varnode, depth=0, use_cache=False):
            return varnode.expr

        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            raise AssertionError("recursive multiequal expansion should handle this case")

        def _get_op_order_key(self, _op):
            return 10

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=FakeConditionTracker(),
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=4, index=2),
        ],
    )
    expander._get_edge_condition = lambda from_block_info, to_block: (
        negate_zero if from_block_info.index == 3 else negate_nonzero
    )

    expanded = expander._expand_input_operation(
        FakeAddOp(),
        [],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].conditions == []
    assert expanded[0].value.to_string() == "(MEM[value] + delta)"

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

    assert inferred == _loc("b", 0, 4)

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
        location=_loc("dst", 0, 4),
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

def test_effect_summary_returns_code_address_target_ref_for_raw_local_target():
    class FakeVarnode:
        def __init__(self):
            self._address = None

        def getAddress(self):
            return self._address

    class FakeAddressSpace:
        def getAddress(self, value):
            return value

    class FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return FakeAddressSpace()

    class FakeFunctionManager:
        def getFunctionAt(self, _addr):
            return None

        def getFunctionContaining(self, _addr):
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
            return Expression.constant(0x401234, 8)

    class FakeOp:
        def __init__(self):
            self._input = FakeVarnode()

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input

        def getMnemonic(self):
            return "CALLIND"

    target_ref = _resolve_call_target_ref(FakeTracer(), FakeOp())

    assert target_ref is not None
    assert target_ref.is_code_address() is True
    assert target_ref.address_offset == 0x401234
    assert target_ref.display_name() == "ADDR_401234"

def test_type_fixer_does_not_pattern_fix_pointer_types():
    fixer = object.__new__(TypeFixer)
    fixer.config = TypeFixerConfig()
    fixer.debug = False

    assert fixer._should_fix_type(resolve_mock_data_type("undefined4"))
    assert not fixer._should_fix_type("undefined4 *")
