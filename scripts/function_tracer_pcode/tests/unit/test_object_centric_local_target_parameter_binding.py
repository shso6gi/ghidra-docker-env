# -*- coding: utf-8 -*-

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.effects.summary import (
    _enumerate_constant_expression_branches,
    substitute_expression,
)
from scripts.function_tracer_pcode.analysis.tracer import ParameterStorageDescriptor, PcodeTracer
from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    Expression,
    LocationBaseRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
from scripts.function_tracer_pcode.semantics.transform.expander import ExpandedValue


class _EmptyLocalMap:
    def getSymbols(self):
        return []


class _EmptyHighFunction:
    def getLocalSymbolMap(self):
        return _EmptyLocalMap()


class _FakeDispatchOp:
    def __init__(self, inputs):
        self._inputs = list(inputs)

    def getMnemonic(self):
        return "CALLIND"

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]


class _FakeEntryPoint:
    def __init__(self, offset):
        self._offset = offset

    def getOffset(self):
        return self._offset

    def __str__(self):
        return hex(self._offset)


class _FakeFunction:
    def __init__(self, name, offset):
        self._name = name
        self._entry = _FakeEntryPoint(offset)

    def getName(self):
        return self._name

    def getEntryPoint(self):
        return self._entry


def _reg_storage(
    register_name: str,
    base_register_name: str,
    *,
    size_bits: int,
    bit_offset_in_base: int,
    base_register_size_bits: int = 64,
    offset: int = 0,
    base_offset: int = 0,
) -> StorageInfo:
    return StorageInfo(
        is_register=True,
        space_name="register",
        space_id=0,
        offset=offset,
        size=max(1, size_bits // 8),
        size_bits=size_bits,
        register_offset=offset,
        register_size=max(1, size_bits // 8),
        register_size_bits=size_bits,
        register_name=register_name,
        base_register_name=base_register_name,
        base_register_offset=base_offset,
        base_register_size=max(1, base_register_size_bits // 8),
        base_register_size_bits=base_register_size_bits,
        bit_offset_in_base=bit_offset_in_base,
    )


def test_tracer_storage_backed_parameter_fallback_returns_parameter_object():
    tracer = PcodeTracer(Mock(), _EmptyHighFunction(), debug=False)
    tracer._parameter_descriptors = [
        ParameterStorageDescriptor(
            name="param_2",
            index=1,
            size_bytes=8,
            is_signed=True,
            data_type="long",
            data_type_obj=None,
            storage_info=_reg_storage(
                "a1",
                "a1",
                size_bits=64,
                bit_offset_in_base=0,
                offset=0x28,
                base_offset=0x28,
            ),
        )
    ]

    resolved = tracer._resolve_storage_backed_parameter_expression(
        _reg_storage(
            "a1",
            "a1",
            size_bits=64,
            bit_offset_in_base=0,
            offset=0x28,
            base_offset=0x28,
        )
    )

    assert resolved is not None
    assert resolved.expr_type.name == "PARAMETER"
    assert resolved.name == "param_2"
    assert resolved.value == 1
    assert resolved.runtime_ref.parameter_index == 1


def test_tracer_storage_backed_parameter_fallback_coerces_bound_arguments_object_centrically():
    caller_arg = Expression.parameter("caller_arg", index=7, size=8)
    tracer = PcodeTracer(
        Mock(),
        _EmptyHighFunction(),
        debug=False,
        bound_parameter_values={0: caller_arg},
    )
    tracer._parameter_descriptors = [
        ParameterStorageDescriptor(
            name="param_1",
            index=0,
            size_bytes=4,
            is_signed=True,
            data_type="int",
            data_type_obj=None,
            storage_info=_reg_storage(
                "a0_lo",
                "a0",
                size_bits=32,
                bit_offset_in_base=32,
                offset=0x24,
                base_offset=0x20,
            ),
        )
    ]

    resolved = tracer._resolve_storage_backed_parameter_expression(
        _reg_storage(
            "a0",
            "a0",
            size_bits=64,
            bit_offset_in_base=0,
            offset=0x20,
            base_offset=0x20,
        )
    )

    assert resolved is not None
    assert resolved.operator == "INT_SEXT"
    narrowed = resolved.operands[0]
    assert narrowed.operator == "SUBPIECE"
    assert narrowed.operands[0].name == "caller_arg"
    assert resolved.runtime_ref.parameter_index == 0


def test_tracer_parameter_symbol_uses_bound_argument_by_object_index():
    target = Expression.constant(0x401200, size=8)
    tracer = PcodeTracer(
        Mock(),
        _EmptyHighFunction(),
        debug=False,
        bound_parameter_values={0: target},
    )
    tracer._parameter_descriptors = [
        ParameterStorageDescriptor(
            name="param_1",
            index=0,
            size_bytes=8,
            is_signed=False,
            data_type="code *",
            data_type_obj=None,
            storage_info=_reg_storage(
                "a0",
                "a0",
                size_bits=64,
                bit_offset_in_base=0,
                offset=0x20,
                base_offset=0x20,
            ),
        )
    ]

    resolved = tracer._resolve_bound_parameter_expression(
        name="param_1",
        index=0,
        data_type="code *",
        data_type_obj=None,
        size_bytes=8,
        storage_info=_reg_storage(
            "a0",
            "a0",
            size_bits=64,
            bit_offset_in_base=0,
            offset=0x20,
            base_offset=0x20,
        ),
    )

    assert resolved is not None
    assert resolved.expr_type.name == "CONSTANT"
    assert resolved.value == 0x401200
    assert resolved.runtime_ref.parameter_index == 0


def test_tracer_parameter_symbol_uses_bound_argument_by_storage_identity_without_index():
    target = Expression.constant(0x401240, size=8)
    storage = _reg_storage(
        "a0",
        "a0",
        size_bits=64,
        bit_offset_in_base=0,
        offset=0x20,
        base_offset=0x20,
    )
    tracer = PcodeTracer(
        Mock(),
        _EmptyHighFunction(),
        debug=False,
        bound_parameter_storage_values={storage.storage_identity_key(): target},
    )
    tracer._parameter_descriptors = [
        ParameterStorageDescriptor(
            name="param_1",
            index=-1,
            size_bytes=8,
            is_signed=False,
            data_type="code *",
            data_type_obj=None,
            storage_info=storage,
        )
    ]

    resolved = tracer._resolve_bound_parameter_expression(
        name="param_1",
        index=-1,
        data_type="code *",
        data_type_obj=None,
        size_bytes=8,
        storage_info=storage,
    )

    assert resolved is not None
    assert resolved.expr_type.name == "CONSTANT"
    assert resolved.value == 0x401240
    assert resolved.runtime_ref.is_storage()
    assert resolved.runtime_ref.storage_identity_key == storage.storage_identity_key()


def test_tracer_storage_backed_parameter_fallback_uses_storage_bound_argument_without_index():
    target = Expression.constant(0x401280, size=8)
    storage = _reg_storage(
        "a0",
        "a0",
        size_bits=64,
        bit_offset_in_base=0,
        offset=0x20,
        base_offset=0x20,
    )
    tracer = PcodeTracer(
        Mock(),
        _EmptyHighFunction(),
        debug=False,
        bound_parameter_storage_values={storage.storage_identity_key(): target},
    )
    tracer._parameter_descriptors = [
        ParameterStorageDescriptor(
            name="param_1",
            index=-1,
            size_bytes=8,
            is_signed=False,
            data_type="code *",
            data_type_obj=None,
            storage_info=storage,
        )
    ]

    resolved = tracer._resolve_storage_backed_parameter_expression(storage)

    assert resolved is not None
    assert resolved.expr_type.name == "CONSTANT"
    assert resolved.value == 0x401280
    assert resolved.runtime_ref.is_storage()
    assert resolved.runtime_ref.storage_identity_key == storage.storage_identity_key()


def test_return_analyzer_specializes_local_target_expansions_with_bound_argument_objects():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()
    tracer._parameter_descriptors = [
        ParameterStorageDescriptor(
            name="param_1",
            index=0,
            size_bytes=4,
            is_signed=False,
            data_type="uint",
            data_type_obj=None,
            storage_info=None,
        ),
        ParameterStorageDescriptor(
            name="param_2",
            index=1,
            size_bytes=4,
            is_signed=True,
            data_type="int",
            data_type_obj=None,
            storage_info=None,
        ),
        ParameterStorageDescriptor(
            name="param_3",
            index=2,
            size_bytes=4,
            is_signed=True,
            data_type="int",
            data_type_obj=None,
            storage_info=None,
        ),
    ]

    expanded = [
        ExpandedValue(
            value=Expression.binary_op(
                "INT_XOR",
                Expression.parameter("param_2", index=1, size=4),
                Expression.parameter("param_3", index=2, size=4),
            ),
            conditions=[
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", index=0, size=4),
                        Expression.constant(0, 4),
                    ),
                    False,
                )
            ],
        )
    ]
    args = [
        Expression.parameter("mode", index=10, size=4),
        Expression.parameter("lhs", index=11, size=4),
        Expression.parameter("rhs", index=12, size=4),
    ]

    specialized = analyzer._specialize_local_target_expansions(expanded, tracer, args)

    assert len(specialized) == 1
    value = specialized[0].value
    assert value.operands[0].name == "lhs"
    assert value.operands[1].name == "rhs"
    cond_expr = specialized[0].conditions[0].expression
    assert cond_expr.operands[0].name == "mode"


def test_parameter_substitution_keeps_caller_scoped_parameter_objects_distinct_from_callee_scope():
    callee_parameters = [
        {
            "name": "param_1",
            "index": 0,
            "size": 4,
            "owner_program_id": 1,
            "owner_entry_offset": 0x401000,
        },
        {
            "name": "param_2",
            "index": 1,
            "size": 4,
            "owner_program_id": 1,
            "owner_entry_offset": 0x401000,
        },
    ]
    replacements = {
        ("parameter", 1, 0x401000, 0): Expression.parameter(
            "lhs",
            index=11,
            size=4,
            runtime_ref=LocationBaseRef.parameter(
                "lhs",
                index=11,
                owner_program_id=1,
                owner_entry_offset=0x400000,
            ),
        ),
        ("parameter", 1, 0x401000, 1): Expression.parameter(
            "rhs",
            index=12,
            size=4,
            runtime_ref=LocationBaseRef.parameter(
                "rhs",
                index=12,
                owner_program_id=1,
                owner_entry_offset=0x400000,
            ),
        ),
    }
    already_bound = Expression.binary_op(
        "INT_XOR",
        Expression.parameter(
            "lhs",
            index=11,
            size=4,
            runtime_ref=LocationBaseRef.parameter(
                "lhs",
                index=11,
                owner_program_id=1,
                owner_entry_offset=0x400000,
            ),
        ),
        Expression.parameter(
            "rhs",
            index=12,
            size=4,
            runtime_ref=LocationBaseRef.parameter(
                "rhs",
                index=12,
                owner_program_id=1,
                owner_entry_offset=0x400000,
            ),
        ),
    )

    rewritten = substitute_expression(already_bound, replacements, callee_parameters)

    assert rewritten.operands[0].name == "lhs"
    assert rewritten.operands[1].name == "rhs"


def test_call_specialization_respects_callee_formal_parameter_widths():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    callee_analysis = create_mock_analysis(
        "ptr_op_add",
        parameters=[
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x2000",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("param_1", index=0, size=4),
                    Expression.parameter("param_2", index=1, size=4),
                ),
                conditions=[],
            )
        ],
    )

    specialized = analyzer._specialize_call_analysis(
        callee_analysis,
        [
            Expression.parameter("lhs64", index=10, size=8),
            Expression.parameter("rhs64", index=11, size=8),
        ],
    )

    assert len(specialized.returns) == 1
    value = specialized.returns[0].value
    assert value.size == 4
    assert value.operands[0].operator == "SUBPIECE"
    assert value.operands[1].operator == "SUBPIECE"
    assert value.operands[0].operands[0].name == "lhs64"
    assert value.operands[1].operands[0].name == "rhs64"


def test_return_analyzer_local_target_cache_key_depends_on_argument_objects():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    key_a = analyzer._local_target_cache_key(
        0x401000,
        [Expression.parameter("lhs", index=1, size=4)],
    )
    key_b = analyzer._local_target_cache_key(
        0x401000,
        [Expression.parameter("rhs", index=2, size=4)],
    )

    assert key_a != key_b


def test_return_analyzer_binds_call_args_to_callee_parameter_indexes():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    target_expr = Expression.constant(0x401200, size=8)
    lhs_expr = Expression.constant(7, size=4)
    rhs_expr = Expression.binary_op("INT_ADD", Expression.constant(1, size=4), Expression.constant(2, size=4))

    bound = analyzer._bound_parameter_values_from_call_args(
        [target_expr, lhs_expr, rhs_expr],
        [
            {"name": "param_1", "index": 1, "size": 8, "data_type": "code *"},
            {"name": "param_2", "index": 2, "size": 4, "data_type": "int"},
            {"name": "param_3", "index": 3, "size": 4, "data_type": "int"},
        ],
    )

    assert set(bound) == {1, 2, 3}
    assert bound[1].value == 0x401200
    assert bound[2].value == 7
    assert bound[3].operator == "INT_ADD"


def test_return_analyzer_binds_only_context_free_call_args():
    """Issue #281 review 5: caller の parameter・memory の読み出し・frame の番地は callee の解析へ束縛しない。

    束縛すると、caller の順序の読み出しが callee の effect と比べられ、caller の parameter が callee の
    parameter と同じ key で置き換えられ、caller の frame の番地が callee の frame に分類される。束縛しない
    引数は、呼び出しの境界（`call_boundary`）の置き換えで caller の値になる。
    """

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    caller_parameter = Expression.parameter("lhs", index=10, size=4)
    caller_read = Expression.memory(Expression.parameter("p", index=0, size=8), 4, read_order_key=3)
    caller_frame = Expression.binary_op(
        "INT_ADD",
        Expression.variable("sp", size=8, storage_info=StorageInfo(is_register=True, register_name="sp", size=8)),
        Expression.constant(-16, size=8),
    )
    callee_parameters = [
        {"name": "param_1", "index": 1, "size": 4, "data_type": "int"},
        {"name": "param_2", "index": 2, "size": 4, "data_type": "int"},
        {"name": "param_3", "index": 3, "size": 8, "data_type": "int *"},
        {"name": "param_4", "index": 4, "size": 4, "data_type": "int"},
    ]

    bound = analyzer._bound_parameter_values_from_call_args(
        [caller_parameter, caller_read, caller_frame, Expression.constant(5, size=4)],
        callee_parameters,
    )

    assert set(bound) == {4}
    assert bound[4].value == 5


def test_return_analyzer_does_not_bind_call_args_by_ordinal_without_identity():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    target_expr = Expression.constant(0x401200, size=8)

    bound = analyzer._bound_parameter_values_from_call_args(
        [target_expr],
        [{"name": "param_1", "size": 8, "data_type": "code *"}],
    )
    storage_bound = analyzer._bound_parameter_storage_values_from_call_args(
        [target_expr],
        [{"name": "param_1", "size": 8, "data_type": "code *"}],
    )

    assert bound == {}
    assert storage_bound == {}


def test_return_analyzer_binds_call_args_by_callee_storage_identity_without_index():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    target_expr = Expression.constant(0x401240, size=8)
    storage = _reg_storage(
        "a0",
        "a0",
        size_bits=64,
        bit_offset_in_base=0,
        offset=0x20,
        base_offset=0x20,
    )

    bound = analyzer._bound_parameter_values_from_call_args(
        [target_expr],
        [{"name": "param_1", "size": 8, "data_type": "code *", "storage": storage}],
    )
    storage_bound = analyzer._bound_parameter_storage_values_from_call_args(
        [target_expr],
        [{"name": "param_1", "size": 8, "data_type": "code *", "storage": storage}],
    )

    assert bound == {}
    assert set(storage_bound) == {storage.storage_identity_key()}
    assert storage_bound[storage.storage_identity_key()].value == 0x401240


def test_return_analyzer_call_target_analysis_does_not_bind_args_by_ordinal_without_identity(monkeypatch):
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    callee = _FakeFunction("callee", 0x401000)
    target_ref = CallTargetRef.from_name("callee", entry_offset=0x401000, function_obj=callee)
    captured_kwargs = []

    monkeypatch.setattr(
        analyzer,
        "_get_freshest_callee_parameters",
        lambda _target_ref: [{"name": "param_1", "size": 8, "data_type": "code *"}],
    )

    def fake_analyze_function(_function, **kwargs):
        captured_kwargs.append(kwargs)
        return create_mock_analysis("callee")

    analyzer.analyze_function = fake_analyze_function

    result = analyzer._get_or_analyze_call_target(
        target_ref,
        set(),
        args=[Expression.constant(0x401200, size=8)],
    )

    assert result is not None
    assert captured_kwargs
    assert captured_kwargs[0]["bound_parameter_values"] == {}
    assert captured_kwargs[0]["bound_parameter_storage_values"] == {}


def test_return_analyzer_call_target_analysis_binds_storage_identity_without_index(monkeypatch):
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    callee = _FakeFunction("callee", 0x401000)
    target_ref = CallTargetRef.from_name("callee", entry_offset=0x401000, function_obj=callee)
    storage = _reg_storage(
        "a0",
        "a0",
        size_bits=64,
        bit_offset_in_base=0,
        offset=0x20,
        base_offset=0x20,
    )
    captured_kwargs = []

    monkeypatch.setattr(
        analyzer,
        "_get_freshest_callee_parameters",
        lambda _target_ref: [
            {"name": "param_1", "size": 8, "data_type": "code *", "storage": storage}
        ],
    )

    def fake_analyze_function(_function, **kwargs):
        captured_kwargs.append(kwargs)
        return create_mock_analysis("callee")

    analyzer.analyze_function = fake_analyze_function

    result = analyzer._get_or_analyze_call_target(
        target_ref,
        set(),
        args=[Expression.constant(0x401240, size=8)],
    )

    assert result is not None
    assert captured_kwargs
    assert captured_kwargs[0]["bound_parameter_values"] == {}
    storage_values = captured_kwargs[0]["bound_parameter_storage_values"]
    assert set(storage_values) == {storage.storage_identity_key()}
    assert storage_values[storage.storage_identity_key()].value == 0x401240


def test_return_analyzer_propagates_specialized_deferred_calls_to_parent_context():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer._current_deferred_calls = {}
    analyzer._apply_bounded_call_refinement = Mock()

    deferred_info = DeferredCallInfo(
        target_ref=CallTargetRef.unknown(),
        arguments=[
            Expression.parameter("param_2", index=1, size=4),
            Expression.parameter("param_3", index=2, size=4),
        ],
        call_target_expr=Expression.parameter("param_1", index=0, size=8),
        sequence=0,
    )
    callee_analysis = create_mock_analysis(
        "ptr_apply_callback",
        parameters=[
            {"name": "param_1", "index": 0, "size": 8, "data_type": "void *"},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int"},
            {"name": "param_3", "index": 2, "size": 4, "data_type": "int"},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.unknown(
                    deferred_info.placeholder_name,
                    runtime_ref=deferred_info.unknown_ref,
                ),
                conditions=[],
            )
        ],
    )
    callee_analysis.deferred_calls = {
        deferred_info.deferred_call_ref.stable_key(): deferred_info
    }

    analyzer._get_or_analyze_call_target = Mock(return_value=callee_analysis)
    analyzer._call_summary_is_safe = Mock(return_value=True)

    expanded = analyzer._resolve_call_expansions(
        CallTargetRef.from_name("ptr_apply_callback"),
        [
            Expression.parameter("op", index=7, size=8),
            Expression.parameter("lhs", index=8, size=4),
            Expression.parameter("rhs", index=9, size=4),
        ],
        set(),
    )

    assert expanded is not None
    assert len(analyzer._current_deferred_calls) == 1
    merged_info = next(iter(analyzer._current_deferred_calls.values()))
    assert merged_info.call_target_expr is not None
    assert merged_info.call_target_expr.name == "op"
    assert [arg.name for arg in merged_info.arguments] == ["lhs", "rhs"]


def test_return_analyzer_scopes_call_analysis_cache_by_bound_argument_objects():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    callee = _FakeFunction("callee", 0x401000)
    analyzer._effect_summary_parameter_cache[analyzer._function_cache_key(callee)] = [
        {"name": "param_1", "index": 0, "size": 4},
    ]
    target_ref = CallTargetRef.from_name(
        "callee",
        entry_offset=0x401000,
        function_obj=callee,
    )
    analyses = [
        create_mock_analysis(
            "callee",
            parameters=[{"name": "param_1", "index": 0, "size": 4}],
            returns=[ReturnInfo(address="0x401000", value=Expression.parameter("param_1", 0, size=4), conditions=[])],
        ),
        create_mock_analysis(
            "callee",
            parameters=[{"name": "param_1", "index": 0, "size": 4}],
            returns=[ReturnInfo(address="0x401000", value=Expression.parameter("param_1", 0, size=4), conditions=[])],
        ),
    ]
    analyzer.analyze_function = Mock(side_effect=analyses)

    first = analyzer._get_or_analyze_call_target(
        target_ref,
        set(),
        args=[Expression.constant(1, size=4)],
    )
    second = analyzer._get_or_analyze_call_target(
        target_ref,
        set(),
        args=[Expression.constant(1, size=4)],
    )
    third = analyzer._get_or_analyze_call_target(
        target_ref,
        set(),
        args=[Expression.constant(2, size=4)],
    )

    assert first is second
    assert third is not None
    assert analyzer.analyze_function.call_count == 2



def test_return_analyzer_shares_one_call_analysis_for_symbolic_arguments():
    """束縛しない引数（caller の parameter）は cache の scope を分けない: callee の解析は 1 回で、
    呼び出しごとの値は境界の置き換えで入る（Issue #281 review 5）。"""

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    callee = _FakeFunction("callee", 0x401000)
    analyzer._effect_summary_parameter_cache[analyzer._function_cache_key(callee)] = [
        {"name": "param_1", "index": 0, "size": 4},
    ]
    target_ref = CallTargetRef.from_name("callee", entry_offset=0x401000, function_obj=callee)
    analysis = create_mock_analysis(
        "callee",
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
        returns=[ReturnInfo(address="0x401000", value=Expression.parameter("param_1", 0, size=4), conditions=[])],
    )
    analyzer.analyze_function = Mock(return_value=analysis)

    first = analyzer._get_or_analyze_call_target(target_ref, set(), args=[Expression.parameter("lhs", index=10, size=4)])
    second = analyzer._get_or_analyze_call_target(target_ref, set(), args=[Expression.parameter("rhs", index=11, size=4)])

    assert first is second
    assert analyzer.analyze_function.call_count == 1

def test_constant_branch_enumerator_handles_ptrsub_function_targets():
    direct = Expression.intrinsic(
        "PTRSUB",
        [
            Expression.constant(0, size=8),
            Expression.constant(0x1010, size=8),
        ],
        size=8,
    )

    branches = _enumerate_constant_expression_branches(direct)

    assert branches == [([], 0x1010)]

    phi = Expression.phi(
        [
            (
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.parameter("mode", index=0, size=4),
                        Expression.constant(0, size=4),
                    ),
                    False,
                ),
                direct,
            ),
            (
                None,
                Expression.intrinsic(
                    "PTRSUB",
                    [
                        Expression.constant(0, size=8),
                        Expression.constant(0x2020, size=8),
                    ],
                    size=8,
                ),
            ),
        ]
    )

    phi_branches = _enumerate_constant_expression_branches(phi)

    assert len(phi_branches) == 2
    assert phi_branches[0][1] == 0x1010
    assert phi_branches[1][1] == 0x2020


def test_condition_simplifier_evaluates_ptrsub_non_null_conditions():
    ptrsub_expr = Expression.intrinsic(
        "PTRSUB",
        [
            Expression.constant(0, size=8),
            Expression.constant(0x1010, size=8),
        ],
        size=8,
    )
    non_null = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            ptrsub_expr,
            Expression.constant(0, size=8),
        ),
        False,
    )
    is_null = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            ptrsub_expr,
            Expression.constant(0, size=8),
        ),
        False,
    )

    assert ConditionSimplifier.evaluate_condition_truth(non_null) is True
    assert ConditionSimplifier.evaluate_condition_truth(is_null) is False


def test_switch_dispatch_argument_recovery_preserves_callind_operands():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer._current_parameters = [
        {"name": "param_1", "index": 0, "size": 8},
        {"name": "param_2", "index": 1, "size": 4},
        {"name": "param_3", "index": 2, "size": 4},
    ]
    tracer = Mock()
    arg_a = Expression.parameter("param_2", index=1, size=4)
    arg_b = Expression.parameter("param_3", index=2, size=4)
    tracer.trace_varnode.side_effect = [arg_a, arg_b]
    dispatch = _FakeDispatchOp([Mock(), Mock(), Mock()])

    args = analyzer._recover_dispatch_call_arguments(dispatch, tracer)

    assert [arg.to_string() for arg in args] == ["param_2", "param_3"]
