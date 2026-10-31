from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *

def test_recover_call_argument_expressions_rejects_fixed_prefix_when_hidden_const_precedes_format():
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
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def resolve_call_target_ref(self, _target_varnode, **_kwargs):
            return CallTargetRef(kind="function", function_name="printf", display_hint="printf")

        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=8)

    recovered = _recover_call_argument_expressions(
        FakeCallOp(
            [
                FakeVarnode(_reg_storage("target", size_bytes=8)),
                FakeVarnode(None),
                FakeVarnode(None),
            ]
        ),
        FakeTracer(),
        [],
        [
            _param(
                "__format",
                size=8,
                is_signed=False,
                index=0,
                data_type="char *",
                storage=_reg_storage("x0", size_bytes=8),
            ),
        ],
        [
            Expression.constant(1, 8),
            _readonly_format_string_expr(0x1004D0),
        ],
    )

    assert recovered == []

    recovered = _recover_call_argument_expressions(
        FakeCallOp(
            [
                FakeVarnode(_reg_storage("target", size_bytes=8)),
                FakeVarnode(None),
                FakeVarnode(None),
            ]
        ),
        FakeTracer(),
        [],
        [
            _param(
                "__format",
                size=8,
                is_signed=False,
                index=0,
                data_type="char *",
                storage=_reg_storage("x0", size_bytes=8),
            ),
        ],
        [
            Expression.constant(0x200000, 8),
            _readonly_format_string_expr(0x1004D0),
        ],
    )

    assert recovered == []

    recovered = _recover_call_argument_expressions(
        FakeCallOp(
            [
                FakeVarnode(_reg_storage("target", size_bytes=8)),
                FakeVarnode(None),
                FakeVarnode(None),
            ]
        ),
        FakeTracer(),
        [],
        [
            _param(
                "__format",
                size=8,
                is_signed=False,
                index=0,
                data_type="char *",
                storage=_reg_storage("x0", size_bytes=8),
            ),
        ],
        [
            Expression.binary_op(
                "INT_ADD",
                Expression.constant(0x200000, 8),
                Expression.constant(0, 8),
            ),
            _readonly_format_string_expr(0x1004D0),
        ],
    )

    assert recovered == []

    recovered = _recover_call_argument_expressions(
        FakeCallOp(
            [
                FakeVarnode(_reg_storage("target", size_bytes=8)),
                FakeVarnode(None),
                FakeVarnode(None),
            ]
        ),
        FakeTracer(),
        [],
        [
            _param(
                "__format",
                size=8,
                is_signed=False,
                index=0,
                data_type="char *",
                storage=_reg_storage("x0", size_bytes=8),
            ),
        ],
        [
            _readonly_format_string_expr(0x400800, can_execute=True),
            _readonly_format_string_expr(0x1004D0),
        ],
    )

    assert recovered == []

def test_recover_call_argument_expressions_selects_target_specific_format_prefix():
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
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def resolve_call_target_ref(self, _target_varnode, **_kwargs):
            return CallTargetRef(kind="function", function_name="fprintf", display_hint="fprintf")

        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=8)

    recovered = _recover_call_argument_expressions(
        FakeCallOp(
            [
                FakeVarnode(_reg_storage("target", size_bytes=8)),
                FakeVarnode(None),
                FakeVarnode(None),
                FakeVarnode(None),
            ]
        ),
        FakeTracer(),
        [],
        [
            _param(
                "stream",
                size=8,
                is_signed=False,
                index=0,
                data_type="FILE *",
                storage=_reg_storage("x0", size_bytes=8),
            ),
            _param(
                "param_2",
                size=8,
                is_signed=False,
                index=1,
                data_type="char *",
                storage=_reg_storage("x1", size_bytes=8),
            ),
        ],
        [
            Expression.constant(0x200000, 8),
            _readonly_format_string_expr(0x1004D0),
            Expression.constant(0x1004F5, 8),
        ],
    )

    assert [arg.to_string() for arg in recovered] == ["2097152", "1049808"]

def test_recover_call_argument_expressions_rejects_ambiguous_storage_windows():
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
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    target = FakeVarnode(_reg_storage("target", size_bytes=8))
    input_a0_first = FakeVarnode(_reg_storage("a0", size_bytes=4))
    input_a0_second = FakeVarnode(_reg_storage("a0", size_bytes=4))
    immediate_arg = FakeVarnode(None)

    recovered = _recover_call_argument_expressions(
        FakeCallOp([target, input_a0_first, immediate_arg, input_a0_second, immediate_arg]),
        FakeTracer(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
        ],
        [
            _param("value", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        [
            Expression.parameter("param_1", 0, size=4),
            Expression.constant(1, 4),
            Expression.parameter("param_1", 0, size=4),
            Expression.constant(2, 4),
        ],
    )

    assert recovered == []

def test_recover_call_argument_expressions_rejects_tail_when_selected_storage_mismatches_callee_storage():
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
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return getattr(_varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    call_op = FakeCallOp(
        [
            FakeVarnode(_reg_storage("target", size_bytes=8)),
            FakeVarnode(_reg_storage("a2", size_bytes=4)),
            FakeVarnode(_reg_storage("a3", size_bytes=4)),
            FakeVarnode(_const_storage(size_bytes=8)),
        ]
    )
    callee_parameters = [
        _param("value", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
        _param("bias", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
    ]
    explicit_args = [
        Expression.parameter("param_3", 2, size=4),
        Expression.parameter("param_3", 2, size=4),
        Expression.constant(0xFFFFFFFD, 4),
    ]

    recovered = effect_summary_module._select_explicit_call_arguments_by_dependency_tail(
        call_op,
        FakeTracer(),
        callee_parameters,
        explicit_args,
    )

    assert recovered is None

def test_recover_call_argument_expressions_selects_tail_when_hidden_duplicate_and_tail_storage_matches():
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
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return getattr(_varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    recovered = _recover_call_argument_expressions(
        FakeCallOp(
            [
                FakeVarnode(_reg_storage("target", size_bytes=8)),
                FakeVarnode(_reg_storage("a2", size_bytes=4)),
                FakeVarnode(_reg_storage("a0", size_bytes=4)),
                FakeVarnode(_const_storage(size_bytes=8)),
            ]
        ),
        FakeTracer(),
        [
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            _param("value", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        [
            Expression.parameter("param_3", 2, size=4),
            Expression.parameter("param_3", 2, size=4),
            Expression.constant(0xFFFFFFFD, 4),
        ],
    )

    assert len(recovered) == 2
    assert [arg.to_string() for arg in recovered] == ["param_3", "4294967293"]

def test_recover_call_argument_expressions_rejects_tail_when_hidden_prefix_has_independent_dependency():
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
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return getattr(_varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    call_op = FakeCallOp(
        [
            FakeVarnode(_reg_storage("target", size_bytes=8)),
            FakeVarnode(_reg_storage("a1", size_bytes=4)),
            FakeVarnode(_reg_storage("a0", size_bytes=4)),
            FakeVarnode(None),
        ]
    )
    callee_parameters = [
        _param("value", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
        _param("bias", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
    ]
    explicit_args = [
        Expression.parameter("param_2", 1, size=4),
        Expression.parameter("param_1", 0, size=4),
        Expression.constant(1, 4),
    ]

    recovered = effect_summary_module._select_explicit_call_arguments_by_dependency_tail(
        call_op,
        FakeTracer(),
        callee_parameters,
        explicit_args,
    )

    assert recovered is None

def test_recover_call_argument_expressions_rejects_tail_when_shared_dependency_changes_first_slot():
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
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return getattr(_varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    x = Expression.parameter("param_3", 2, size=4)
    call_op = FakeCallOp(
        [
            FakeVarnode(_reg_storage("target", size_bytes=8)),
            FakeVarnode(_reg_storage("a2", size_bytes=4)),
            FakeVarnode(_reg_storage("a2", size_bytes=4)),
            FakeVarnode(None),
        ]
    )

    recovered = effect_summary_module._select_explicit_call_arguments_by_dependency_tail(
        call_op,
        FakeTracer(),
        [
            _param("value", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        [
            x,
            Expression.binary_op("INT_ADD", x, Expression.constant(1, 4)),
            x,
        ],
    )

    assert recovered is None

def test_recover_call_argument_expressions_rejects_tail_when_shared_dependency_is_not_same_expression():
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
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return getattr(_varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    x = Expression.parameter("param_3", 2, size=4)
    call_op = FakeCallOp(
        [
            FakeVarnode(_reg_storage("target", size_bytes=8)),
            FakeVarnode(_reg_storage("a2", size_bytes=4)),
            FakeVarnode(_reg_storage("a2", size_bytes=4)),
            FakeVarnode(None),
        ]
    )

    recovered = effect_summary_module._select_explicit_call_arguments_by_dependency_tail(
        call_op,
        FakeTracer(),
        [
            _param("value", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        [
            x,
            Expression.binary_op("INT_OR", x, Expression.constant(1, 4)),
            Expression.constant(7, 4),
        ],
    )

    assert recovered is None

def test_recover_call_argument_expressions_rejects_tail_without_any_object_storage():
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
        def __init__(self, input_count):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._input_count = input_count

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return self._input_count

        def getInput(self, _index):
            return object()

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    recovered = effect_summary_module._select_explicit_call_arguments_by_dependency_tail(
        FakeCallOp(input_count=4),
        FakeTracer(),
        [
            _param("value", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        [
            Expression.parameter("param_3", 2, size=4),
            Expression.parameter("param_3", 2, size=4),
            Expression.constant(0xFFFFFFFD, 4),
        ],
    )

    assert recovered is None

def test_recover_call_argument_expressions_refuses_right_aligned_hidden_prefix_without_object_evidence():
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

    assert recovered == []

def test_recover_call_argument_expressions_selects_semantic_window_with_parameter_identity_and_immediate():
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
            _param("loop_index", size=4, is_signed=False, index=1, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            _param("x", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("b", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        [
            Expression.binary_op(
                "INT_ADD",
                Expression.parameter("loop_index", 1, size=4),
                Expression.constant(0xFFFFFFF8, 4),
            ),
            Expression.parameter("param_1", 0, size=4),
            Expression.constant(1, 4),
        ],
    )

    assert len(recovered) == 2
    assert recovered[0].to_string() == "param_1"
    assert recovered[1].to_string() == "1"

def test_recover_call_argument_expressions_rejects_semantic_window_without_strong_identity():
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
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            _param("x", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("b", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        [
            Expression.variable("hidden", size=4),
            Expression.parameter("param_3", 2, size=4),
            Expression.constant(1, 4),
        ],
    )

    assert recovered == []

def test_recover_call_argument_expressions_uses_path_sensitive_multiequal_input_for_hidden_arg():
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
        def __init__(self, name):
            self.name = name

        def getDef(self):
            return None

        def getSize(self):
            return 4

        def getHigh(self):
            return None

    class FakeBlock:
        def __init__(self, index):
            self._index = index
            self._ins = []

        def getIndex(self):
            return self._index

        def getInSize(self):
            return len(self._ins)

        def getIn(self, index):
            return self._ins[index]

    class FakeBlockInfo:
        def __init__(self, block, pcode_ops):
            self.block = block
            self.index = block.getIndex()
            self.pcode_ops = list(pcode_ops)

    class FakeOp:
        def __init__(self, mnemonic, order, output=None, inputs=None):
            self._mnemonic = mnemonic
            self._seqnum = FakeSeqnum(0x4000, order)
            self._output = output
            self._inputs = list(inputs or [])

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return self._output

        def getMnemonic(self):
            return self._mnemonic

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def __init__(self, expressions, storage_map, ops):
            self._expressions = expressions
            self._storage_map = storage_map
            self._ops = ops

        def get_all_pcode_ops(self):
            return list(self._ops)

        def _get_storage_info_from_varnode(self, varnode):
            return self._storage_map.get(varnode)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return self._expressions[varnode]

    class FakeConditionTracker:
        def __init__(self, block_infos, path_entries):
            self.block_by_index = {info.index: info for info in block_infos}
            self._paths = list(path_entries)

        def get_all_valid_block_paths_to_block(self, _target_block):
            return list(self._paths)

    output = FakeVarnode("out")
    path_true_input = FakeVarnode("path_true")
    path_false_input = FakeVarnode("path_false")
    target_storage = StorageInfo(**_reg_storage("a2", size_bytes=4, register_name="a2"))

    phi_op = FakeOp("MULTIEQUAL", 1, output=output, inputs=[path_false_input, path_true_input])
    call_op = FakeOp("CALL", 2)

    false_block = FakeBlock(1)
    true_block = FakeBlock(2)
    call_block = FakeBlock(3)
    call_block._ins = [false_block, true_block]

    false_info = FakeBlockInfo(false_block, [])
    true_info = FakeBlockInfo(true_block, [])
    call_info = FakeBlockInfo(call_block, [phi_op, call_op])

    selector = Expression.parameter("selector", 0, size=4)
    true_cond = Condition(
        Expression.binary_op("INT_NOTEQUAL", selector, Expression.constant(0, 4)),
        False,
    )
    false_cond = Condition(
        Expression.binary_op("INT_EQUAL", selector, Expression.constant(0, 4)),
        False,
    )

    tracer = FakeTracer(
        {
            output: Expression.phi([(false_cond, Expression.variable("tmp_x2", size=4)), (true_cond, Expression.parameter("param_3", 2, size=4))]),
            path_false_input: Expression.variable("tmp_x2", size=4),
            path_true_input: Expression.parameter("param_3", 2, size=4),
        },
        {
            output: target_storage,
        },
        [phi_op, call_op],
    )
    condition_tracker = FakeConditionTracker(
        [false_info, true_info, call_info],
        [
            ([false_info, call_info], [false_cond]),
            ([true_info, call_info], [true_cond]),
        ],
    )

    recovered = _recover_call_argument_expressions(
        call_op,
        tracer,
        [
            _param("selector", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=target_storage),
        ],
        [
            _param("rhs", size=4, is_signed=False, index=0, storage=target_storage),
        ],
        [],
        condition_tracker=condition_tracker,
        current_conditions=[true_cond],
    )

    assert len(recovered) == 1
    assert recovered[0].to_string() == "param_3"

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

def test_normalize_call_argument_expression_refuses_positional_parameter_fallback():
    unresolved = Expression.variable("opaque_arg", size=8)

    normalized = _normalize_call_argument_expression(
        unresolved,
        1,
        [
            _param("param_1", size=8, is_signed=False, index=0),
            _param("param_2", size=8, is_signed=False, index=1),
        ],
    )

    assert normalized is unresolved

def test_normalize_call_argument_expression_uses_storage_identity():
    storage = StorageInfo(**_reg_storage("a1"))
    variable = Expression.variable("opaque_arg", size=8, storage_info=storage)

    normalized = _normalize_call_argument_expression(
        variable,
        0,
        [
            _param("param_1", size=8, is_signed=False, index=0, storage=_reg_storage("a0")),
            _param("param_2", size=8, is_signed=False, index=1, storage=_reg_storage("a1")),
        ],
    )

    assert normalized.expr_type.name == "PARAMETER"
    assert normalized.name == "param_2"
    assert normalized.value == 1

def test_summarize_store_effects_marks_argumentless_call_unknown_without_callsite_arg_evidence():
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

        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("callee")

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.constant(0x401100, 8)

    call_op = FakeCallOp()
    captured_args = {}

    def _direct_call_summary(_name, args):
        captured_args["args"] = list(args)
        return EffectSummary(
            parameter_names=["a", "b"],
            effects=[
                StoreEffect(
                    location=_loc("a", 0, 4),
                    value=Expression.memory(Expression.parameter("b", 1, size=8), size=4),
                    conditions=[],
                    order_key=1,
                ),
                StoreEffect(
                    location=_loc("b", 0, 4),
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
        resolve_callee_parameters=lambda _target_ref: [
            _param("a", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("b", size=8, is_signed=False, index=1, storage=_reg_storage("x1", register_name="x1")),
        ],
        debug=False,
    )

    assert "args" not in captured_args
    assert summary.effects == []
    assert summary.has_unsupported_call is True

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

        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("fc_bias")

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

    def resolve_call(target_ref, args, call_site=None):
        captured["target"] = target_ref
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
        resolve_callee_parameters=lambda _target_ref: [
            _param("value", size=4, index=0, storage=_reg_storage("a0", size_bytes=4, register_name="a0")),
            _param("bias", size=4, index=1, storage=_reg_storage("a1", size_bytes=4, register_name="a1")),
        ],
    )
    expander._expand_input_varnode = lambda varnode, conditions, depth: {
        copied_first_arg: [ExpandedValue(Expression.parameter("param_1", 0, size=4), [])],
        bias_varnode: [ExpandedValue(Expression.constant(0xFFFFFFFD, 4), [])],
    }[varnode]

    expanded = expander._expand_call_operation(call_op, [], depth=0, output_size=4)

    assert len(expanded) == 1
    assert captured["target"] == CallTargetRef.from_name("fc_bias")
    assert [arg.to_string() for arg in captured["args"]] == ["param_3", "4294967293"]
