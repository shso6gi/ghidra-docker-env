from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *

def test_enumerate_call_argument_variants_dedup_does_not_require_to_string(monkeypatch):
    shared = Expression.parameter("param_1", index=0, size=4)
    phi_expr = Expression.phi(
        [
            (Condition(Expression.binary_op("INT_EQUAL", shared, Expression.constant(0, 4))), shared),
            (Condition(Expression.binary_op("INT_EQUAL", shared, Expression.constant(0, 4))), shared),
        ]
    )

    def _boom_expr(_self, simplify=True):
        raise AssertionError("variant dedup should not depend on Expression.to_string")

    def _boom_cond(_self):
        raise AssertionError("variant dedup should not depend on Condition.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom_expr)
    monkeypatch.setattr(Condition, "to_string", _boom_cond)

    variants = _enumerate_call_argument_variants([phi_expr])

    assert len(variants) == 1
    assert variants[0][1][0].structural_key(normalize_commutative=True) == shared.structural_key(
        normalize_commutative=True
    )

def test_call_argument_semantic_rank_uses_pointer_datatype_object_not_name():
    class MockPointerType:
        def isPointer(self):
            return True

    rank = _call_argument_semantic_rank(
        Expression.constant(0, size=8),
        caller_parameters=[],
        callee_param={
            "name": "param_1",
            "size": 8,
            "data_type": "opaque_alias",
            "data_type_obj": MockPointerType(),
        },
    )

    assert rank == 3

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
        _loc("a", 0, 4),
        [{"name": "a", "index": 0}, {"name": "b", "index": 1}],
        call_args,
        [
            _param("param_1", size=8, is_signed=False, storage=_reg_storage("A0")),
            _param("param_2", size=8, is_signed=False, index=1, storage=_reg_storage("A1")),
        ],
    )

    assert substituted == _loc("param_1", 0, 4)

def test_substitute_location_accepts_stack_local_call_arguments():
    caller_params = [_param("param_1", size=8, is_signed=False)]
    local_out = Expression.variable(
        "local_out",
        size=8,
        storage_info=StorageInfo(**_stack_storage(24, size_bytes=4)),
    )

    substituted = substitute_location(
        _loc("out", 0, 4),
        [{"name": "in", "index": 0}, {"name": "out", "index": 1}],
        [Expression.parameter("param_1", 0, size=8), local_out],
        caller_params,
    )

    assert substituted == canonicalize_location(local_out, caller_params, size=4)

def test_substitute_location_accepts_storage_only_callee_effect_base():
    callee_storage = StorageInfo(**_reg_storage("a0", size_bytes=8))
    callee_location = CanonicalLocation(
        base_ref=LocationBaseRef.storage(
            space_id=callee_storage.space_id,
            space_name=callee_storage.space_name,
            offset=callee_storage.offset,
            size=callee_storage.size,
            storage_identity_key=callee_storage.storage_identity_key(),
        ),
        offset=0,
        size=4,
    )
    actual_dst = Expression.parameter("dst", 0, size=8, data_type="int *")

    substituted = substitute_location(
        callee_location,
        [{"name": "callee_dst", "size": 8, "storage": _reg_storage("a0", size_bytes=8)}],
        [actual_dst],
        [_param("dst", size=8, index=0, data_type="int *")],
    )

    assert substituted == _loc("dst", 0, 4)

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

        def getDef(self):
            return None

        def getAddress(self):
            return FakeAddress(self.storage.offset, self.storage.space_name)

        def getOffset(self):
            return self.storage.offset

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
    call_block = type("FakeBlock", (), {"pcode_ops": tracer.get_all_pcode_ops() + [call_op]})()

    class FakeConditionTracker:
        block_by_index = {0: call_block}

        def get_all_valid_block_paths_to_block(self, _block):
            return [([call_block], [])]

    recovered = _recover_call_argument_from_storage(
        call_op,
        tracer,
        [_param("param_1", size=4, is_signed=False, index=0)],
        {"storage": _reg_storage("a2"), "size": 8},
        condition_tracker=FakeConditionTracker(),
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

    class MockPointerType:
        def isPointer(self):
            return True

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
    call_block = type("FakeBlock", (), {"pcode_ops": tracer.get_all_pcode_ops() + [call_op]})()

    class FakeConditionTracker:
        block_by_index = {0: call_block}

        def get_all_valid_block_paths_to_block(self, _block):
            return [([call_block], [])]

    recovered = _recover_call_argument_from_storage(
        call_op,
        tracer,
        [_param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0_lo", size_bytes=4, register_name="a0_lo"))],
        {
            "storage": _reg_storage("a2"),
            "size": 8,
            "data_type": "int *",
            "data_type_obj": MockPointerType(),
        },
        condition_tracker=FakeConditionTracker(),
    )

    assert recovered is not None
    assert recovered.to_string() == "(sp + (-48))"

def test_recover_call_argument_from_storage_refuses_no_tracker_global_scan():
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
        def __init__(self, name, storage, expr):
            self.name = name
            self.storage = storage
            self.expr = expr

        def getDef(self):
            return None

        def getSize(self):
            return 4

    class FakeOp:
        def __init__(self, output, order):
            self._output = output
            self._seqnum = FakeSeqnum(0x1000, order)

        def getMnemonic(self):
            return "CALL" if self._output is None else "COPY"

        def getOutput(self):
            return self._output

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeTracer:
        def __init__(self, ops):
            self._ops = list(ops)

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return getattr(varnode, "expr", None)

    storage = StorageInfo(**_reg_storage("a0", size_bytes=4))
    reaching_output = FakeVarnode(
        "a0_def",
        storage,
        Expression.parameter("param_1", 0, size=4),
    )
    reaching_def = FakeOp(reaching_output, 1)
    call_op = FakeOp(None, 10)

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer([reaching_def]),
        [_param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4))],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
    )

    assert recovered is None

def test_recover_call_argument_expressions_does_not_fabricate_formal_storage_argument():
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
        def getTarget(self):
            return FakeAddress(0x1000)

        def getOrder(self):
            return 1

    class FakeCallOp:
        def getSeqnum(self):
            return FakeSeqnum()

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

    args = _recover_call_argument_expressions(
        FakeCallOp(),
        FakeTracer(),
        [_param("caller_value", size=8, is_signed=False, storage=_reg_storage("a0"))],
        [{"name": "callee_value", "index": 0, "size": 8, "storage": _reg_storage("a0")}],
        [],
    )

    assert args == []

def test_recover_call_argument_from_storage_requires_all_compatible_paths():
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
        def __init__(self, name, storage=None, expr=None, size=4):
            self.name = name
            self.storage = storage
            self.expr = expr
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class FakeOp:
        def __init__(self, mnemonic, output, offset, order):
            self._mnemonic = mnemonic
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def __init__(self, ops):
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return getattr(varnode, "expr", None) or Expression.variable(varnode.name, size=varnode.getSize())

    storage = StorageInfo(**_reg_storage("a0", size_bytes=4))
    output = FakeVarnode(
        "a0_def",
        storage=storage,
        expr=Expression.parameter("param_1", 0, size=4),
    )
    reaching_def = FakeOp("COPY", output, 0x1000, 1)
    call_op = FakeOp("CALL", None, 0x1000, 10)
    path_with_def = FakeBlock([reaching_def])
    path_without_def = FakeBlock([])
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer([reaching_def]),
        [_param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a1", size_bytes=4))],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [path_with_def, call_block],
                [path_without_def, call_block],
            ],
        ),
    )

    assert recovered is None

def test_recover_call_argument_from_storage_accepts_unmodified_live_in_on_all_paths():
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
        def __init__(self, mnemonic, offset, order):
            self._mnemonic = mnemonic
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return None

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    call_op = FakeOp("CALL", 0x1000, 10)
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer(),
        [_param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4))],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [FakeBlock([]), call_block],
                [FakeBlock([]), call_block],
            ],
        ),
    )

    assert recovered is not None
    assert recovered.to_string() == "param_1"

def test_recover_call_argument_from_storage_marks_unknown_full_register_live_in_fragment_partial():
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
        def __init__(self, mnemonic, offset, order):
            self._mnemonic = mnemonic
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return None

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    def reg_storage(
        register_name: str,
        base_name: str,
        *,
        offset: int,
        size_bits: int,
        bit_offset_in_base: int,
    ) -> dict:
        return {
            "is_register": True,
            "space_name": "register",
            "space_id": 0,
            "offset": offset,
            "size": max(1, size_bits // 8),
            "size_bits": size_bits,
            "register_name": register_name,
            "base_register_name": base_name,
            "base_register_offset": 0x30,
            "base_register_size": 8,
            "base_register_size_bits": 64,
            "bit_offset_in_base": bit_offset_in_base,
        }

    call_op = FakeOp("CALL", 0x1000, 10)
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer(),
        [
            _param(
                "param_3",
                size=4,
                is_signed=True,
                index=2,
                storage=reg_storage(
                    "a2_lo",
                    "a2",
                    offset=0x34,
                    size_bits=32,
                    bit_offset_in_base=32,
                ),
            )
        ],
        {
            "name": "callee_b",
            "index": 2,
            "size": 8,
            "storage": reg_storage(
                "a2",
                "a2",
                offset=0x30,
                size_bits=64,
                bit_offset_in_base=0,
            ),
        },
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [FakeBlock([]), call_block],
                [FakeBlock([]), call_block],
            ],
        ),
    )

    assert recovered is not None
    assert recovered.to_string() == "param_3"
    assert recovered.size == 4
    evidence = getattr(recovered, "call_argument_width_evidence", None)
    assert evidence is not None
    assert evidence.is_partial() is True
    assert evidence.source_bits == 32
    assert evidence.target_bits == 64

def test_partial_live_in_argument_rejects_full_width_callee_return_use():
    arg = Expression.parameter("param_3", 2, size=4).clone_with(
        call_argument_width_evidence=CallArgumentWidthEvidence(
            source_bits=32,
            target_bits=64,
        )
    )
    callee_analysis = FunctionReturnAnalysis(
        function_name="callee",
        entry_point="0x1000",
        parameters=[
            {
                "name": "param_3",
                "index": 2,
                "size": 8,
                "data_type": "undefined8",
                "storage": _reg_storage("a2", size_bytes=8),
            }
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.parameter("param_3", 2, size=8),
                conditions=[],
                branch_index=0,
            )
        ],
    )

    assert _call_arguments_width_safe_for_callee_analysis(callee_analysis, [arg]) is False

def test_partial_live_in_argument_allows_low_subpiece_callee_return_use():
    arg = Expression.parameter("param_3", 2, size=4).clone_with(
        call_argument_width_evidence=CallArgumentWidthEvidence(
            source_bits=32,
            target_bits=64,
        )
    )
    callee_param = Expression.parameter("param_3", 2, size=8)
    low_piece = Expression.binary_op(
        "SUBPIECE",
        callee_param,
        Expression.constant(0, size=8),
    )
    low_piece.size = 4
    callee_analysis = FunctionReturnAnalysis(
        function_name="callee",
        entry_point="0x1000",
        parameters=[
            {
                "name": "param_3",
                "index": 2,
                "size": 8,
                "data_type": "undefined8",
                "storage": _reg_storage("a2", size_bytes=8),
            }
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=low_piece,
                conditions=[],
                branch_index=0,
            )
        ],
    )

    assert _call_arguments_width_safe_for_callee_analysis(callee_analysis, [arg]) is True

def test_partial_live_in_argument_allows_low_subpiece_callee_effect_use():
    callee_arg = Expression.parameter("arg", 1, size=8)
    low_piece = Expression.binary_op(
        "SUBPIECE",
        callee_arg,
        Expression.constant(0, size=8),
    )
    low_piece.size = 4

    summary = _summarize_partial_width_effect_call(low_piece)

    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1

def test_partial_live_in_argument_rejects_full_width_callee_effect_use():
    summary = _summarize_partial_width_effect_call(
        Expression.parameter("arg", 1, size=8)
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True

def test_coerce_argument_to_unknown_callee_param_preserves_fragment_width():
    arg = Expression.parameter("param_3", 2, size=4)

    coerced = _coerce_argument_to_callee_parameter(
        arg,
        {
            "name": "callee_b",
            "index": 2,
            "size": 8,
            "data_type": "undefined8",
        },
    )

    assert coerced is not None
    assert coerced.expr_type == ExpressionType.PARAMETER
    assert coerced.size == 4
    assert coerced.to_string() == "param_3"

def test_recover_call_argument_from_storage_refuses_pointer_live_in_from_integer_fragment():
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
        def __init__(self, mnemonic, offset, order):
            self._mnemonic = mnemonic
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return None

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def _get_storage_info_from_varnode(self, _varnode):
            return None

    def reg_storage(register_name, base_name, *, offset, size_bits, bit_offset_in_base):
        return {
            "is_register": True,
            "space_name": "register",
            "space_id": 0,
            "offset": offset,
            "size": max(1, size_bits // 8),
            "size_bits": size_bits,
            "register_name": register_name,
            "base_register_name": base_name,
            "base_register_offset": 0x30,
            "base_register_size": 8,
            "base_register_size_bits": 64,
            "bit_offset_in_base": bit_offset_in_base,
        }

    call_op = FakeOp("CALL", 0x1000, 10)
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer(),
        [
            {
                **_param(
                    "param_3",
                    size=4,
                    is_signed=True,
                    index=2,
                    storage=reg_storage("a2_lo", "a2", offset=0x34, size_bits=32, bit_offset_in_base=32),
                ),
                "data_type": "int",
                "data_type_obj": resolve_mock_data_type("int"),
            }
        ],
        {
            "name": "callee_ptr",
            "index": 2,
            "size": 8,
            "data_type": "int *",
            "storage": reg_storage("a2", "a2", offset=0x30, size_bits=64, bit_offset_in_base=0),
        },
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [FakeBlock([]), call_block],
                [FakeBlock([]), call_block],
            ],
        ),
    )

    assert recovered is None

def test_recover_call_argument_from_storage_accepts_semantic_width_fragment_live_in():
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
        def __init__(self, mnemonic, offset, order):
            self._mnemonic = mnemonic
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return None

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def _get_storage_info_from_varnode(self, _varnode):
            return None

    def reg_storage(
        register_name: str,
        base_name: str,
        *,
        offset: int,
        size_bits: int,
        bit_offset_in_base: int,
    ) -> dict:
        return {
            "is_register": True,
            "space_name": "register",
            "space_id": 0,
            "offset": offset,
            "size": max(1, size_bits // 8),
            "size_bits": size_bits,
            "register_name": register_name,
            "base_register_name": base_name,
            "base_register_offset": 0x30,
            "base_register_size": 8,
            "base_register_size_bits": 64,
            "bit_offset_in_base": bit_offset_in_base,
        }

    call_op = FakeOp("CALL", 0x1000, 10)
    call_block = FakeBlock([call_op])
    int_type = resolve_mock_data_type("int")

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer(),
        [
            {
                **_param(
                    "param_3",
                    size=4,
                    is_signed=True,
                    index=2,
                    storage=reg_storage(
                        "a2_lo",
                        "a2",
                        offset=0x34,
                        size_bits=32,
                        bit_offset_in_base=32,
                    ),
                ),
                "data_type": "int",
                "data_type_obj": int_type,
            }
        ],
        {
            "name": "callee_b",
            "index": 2,
            "size": 8,
            "data_type": "int",
            "data_type_obj": int_type,
            "storage": reg_storage(
                "a2",
                "a2",
                offset=0x30,
                size_bits=64,
                bit_offset_in_base=0,
            ),
        },
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [FakeBlock([]), call_block],
                [FakeBlock([]), call_block],
            ],
        ),
    )

    assert recovered is not None
    assert recovered.to_string() == "param_3"
    assert recovered.size == 4

def test_recover_call_argument_from_storage_refuses_global_scan_when_cfg_paths_inconclusive():
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
        def __init__(self, name, storage=None, expr=None, size=4):
            self.name = name
            self.storage = storage
            self.expr = expr
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class FakeOp:
        def __init__(self, mnemonic, output, offset, order):
            self._mnemonic = mnemonic
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class InconclusiveConditionTracker:
        block_by_index = {}

        def get_all_valid_block_paths_to_block(self, _block):
            raise AssertionError("block lookup should fail before path enumeration")

    class FakeTracer:
        def __init__(self, ops):
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return getattr(varnode, "expr", None) or Expression.variable(varnode.name, size=varnode.getSize())

    storage = StorageInfo(**_reg_storage("a0", size_bytes=4))
    reaching_output = FakeVarnode(
        "a0_def",
        storage=storage,
        expr=Expression.parameter("param_1", 0, size=4),
    )
    reaching_def = FakeOp("COPY", reaching_output, 0x1000, 1)
    call_op = FakeOp("CALL", None, 0x1000, 10)

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer([reaching_def]),
        [_param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4))],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
        condition_tracker=InconclusiveConditionTracker(),
    )

    assert recovered is None

def test_recover_call_argument_from_storage_rejects_conflicting_path_args():
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
        def __init__(self, name, storage=None, expr=None, size=4):
            self.name = name
            self.storage = storage
            self.expr = expr
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class FakeOp:
        def __init__(self, mnemonic, output, offset, order):
            self._mnemonic = mnemonic
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def __init__(self, ops):
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return getattr(varnode, "expr", None) or Expression.variable(varnode.name, size=varnode.getSize())

    storage = StorageInfo(**_reg_storage("a0", size_bytes=4))
    out_a = FakeVarnode("a0_a", storage=storage, expr=Expression.parameter("param_1", 0, size=4))
    out_b = FakeVarnode("a0_b", storage=storage, expr=Expression.parameter("param_2", 1, size=4))
    def_a = FakeOp("COPY", out_a, 0x1000, 1)
    def_b = FakeOp("COPY", out_b, 0x1000, 2)
    call_op = FakeOp("CALL", None, 0x1000, 10)
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer([def_a, def_b]),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [FakeBlock([def_a]), call_block],
                [FakeBlock([def_b]), call_block],
            ],
        ),
    )

    assert recovered is None

def test_recover_call_argument_from_storage_builds_phi_for_conditioned_path_args():
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
        def __init__(self, name, storage=None, expr=None, size=4):
            self.name = name
            self.storage = storage
            self.expr = expr
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class FakeOp:
        def __init__(self, mnemonic, output, offset, order):
            self._mnemonic = mnemonic
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return list(self._paths)

    class FakeTracer:
        def __init__(self, ops):
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return getattr(varnode, "expr", None) or Expression.variable(varnode.name, size=varnode.getSize())

    selector = Expression.parameter("selector", 0, size=4)
    false_cond = Condition(
        Expression.binary_op("INT_EQUAL", selector, Expression.constant(0, 4)),
        False,
    )
    true_cond = Condition(
        Expression.binary_op("INT_NOTEQUAL", selector, Expression.constant(0, 4)),
        False,
    )
    storage = StorageInfo(**_reg_storage("a0", size_bytes=4))
    out_false = FakeVarnode(
        "a0_false",
        storage=storage,
        expr=Expression.parameter("param_1", 1, size=4),
    )
    out_true = FakeVarnode(
        "a0_true",
        storage=storage,
        expr=Expression.parameter("param_2", 2, size=4),
    )
    def_false = FakeOp("COPY", out_false, 0x1000, 1)
    def_true = FakeOp("COPY", out_true, 0x1000, 2)
    call_op = FakeOp("CALL", None, 0x1000, 10)
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer([def_false, def_true]),
        [
            _param("selector", size=4, is_signed=False, index=0, storage=_reg_storage("a2", size_bytes=4)),
            _param("param_1", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                ([FakeBlock([def_false]), call_block], [false_cond]),
                ([FakeBlock([def_true]), call_block], [true_cond]),
            ],
        ),
    )

    assert recovered is not None
    assert recovered.expr_type == ExpressionType.PHI
    assert recovered.size == 4
    assert len(recovered.value) == 2
    branch_values = {value.to_string() for _cond, value in recovered.value}
    assert branch_values == {"param_1", "param_2"}

def test_recover_call_argument_from_storage_rejects_overlapping_conditioned_path_args():
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
        def __init__(self, name, storage=None, expr=None, size=4):
            self.name = name
            self.storage = storage
            self.expr = expr
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class FakeOp:
        def __init__(self, mnemonic, output, offset, order):
            self._mnemonic = mnemonic
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return list(self._paths)

    class FakeTracer:
        def __init__(self, ops):
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return getattr(varnode, "expr", None) or Expression.variable(varnode.name, size=varnode.getSize())

    selector = Expression.parameter("selector", 0, size=4)
    other = Expression.parameter("other", 1, size=4)
    selector_nonzero = Condition(
        Expression.binary_op("INT_NOTEQUAL", selector, Expression.constant(0, 4)),
        False,
    )
    other_nonzero = Condition(
        Expression.binary_op("INT_NOTEQUAL", other, Expression.constant(0, 4)),
        False,
    )
    storage = StorageInfo(**_reg_storage("a0", size_bytes=4))
    out_a = FakeVarnode(
        "a0_a",
        storage=storage,
        expr=Expression.parameter("param_1", 2, size=4),
    )
    out_b = FakeVarnode(
        "a0_b",
        storage=storage,
        expr=Expression.parameter("param_2", 3, size=4),
    )
    def_a = FakeOp("COPY", out_a, 0x1000, 1)
    def_b = FakeOp("COPY", out_b, 0x1000, 2)
    call_op = FakeOp("CALL", None, 0x1000, 10)
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer([def_a, def_b]),
        [
            _param("selector", size=4, is_signed=False, index=0, storage=_reg_storage("a2", size_bytes=4)),
            _param("other", size=4, is_signed=False, index=1, storage=_reg_storage("a3", size_bytes=4)),
            _param("param_1", size=4, is_signed=False, index=2, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=3, storage=_reg_storage("a2", size_bytes=4)),
        ],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                ([FakeBlock([def_a]), call_block], [selector_nonzero]),
                ([FakeBlock([def_b]), call_block], [selector_nonzero, other_nonzero]),
            ],
        ),
    )

    assert recovered is None

def test_incomplete_call_argument_evidence_is_not_applied_to_deferred_call():
    pcode_ref = PcodeOpRef(address_offset=0x1000, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        call_argument_evidence={
            pcode_ref.stable_key(): CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=CallTargetRef.from_name("callee"),
                callee_param_identities=(("parameter", 0),),
                arguments=(),
                sources=(),
                path_conditions=((),),
                coverage_complete=False,
                reason="argument_recovery_incomplete",
            )
        },
    )

    ReturnAnalyzer(program=None, debug=False)._apply_effect_call_argument_evidence_to_deferred_calls(analysis)

    assert deferred.arguments == []
    assert deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE
    assert deferred.call_argument_recovery_reason == "argument_recovery_incomplete"
    assert "effect_call_argument_evidence_incomplete" in analysis.analysis_notes
