# -*- coding: utf-8 -*-

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.equivalence.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.equivalence.formula.types import ParameterInfo
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import QueryResult, ReturnCase
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
    solve_query_twostage,
    validate_counterexample_across_cases,
)
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.transform.expander import ExpandedValue, ExpressionExpander


def _param_expr(name: str, index: int = 0, size: int = 4) -> Expression:
    return Expression.parameter(name, index=index, size=size)


def _cond_eq(left: Expression, right: Expression) -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", left, right), False)


def _cond_ne(left: Expression, right: Expression) -> Condition:
    return Condition(Expression.binary_op("INT_NOTEQUAL", left, right), False)


class _FakeFunction:
    def __init__(self, name: str, entry: int):
        self._name = name
        self._entry = entry

    def getName(self):
        return self._name

    def getEntryPoint(self):
        return self._entry


class _FakeFunctionManager:
    def __init__(self, by_addr, by_name):
        self._by_addr = dict(by_addr)
        self._by_name = dict(by_name)

    def getFunctionAt(self, addr):
        return self._by_addr.get(addr)

    def getFunctionContaining(self, addr):
        return self._by_addr.get(addr)

    def getFunctions(self, _forward):
        return list(self._by_name.values())


class _FakeAddressSpace:
    def getAddress(self, value):
        return value


class _FakeAddressFactory:
    def getDefaultAddressSpace(self):
        return _FakeAddressSpace()


class _FakeProgram:
    def __init__(self, functions):
        by_name = {func.getName(): func for func in functions}
        by_addr = {func.getEntryPoint(): func for func in functions}
        self._function_manager = _FakeFunctionManager(by_addr, by_name)

    def getFunctionManager(self):
        return self._function_manager

    def getAddressFactory(self):
        return _FakeAddressFactory()


def test_return_analyzer_resolves_call_summary_with_argument_substitution():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    callee_analysis = FunctionReturnAnalysis(
        function_name="callee",
        entry_point="0x401000",
        parameters=[{"name": "x", "size": 4, "index": 0}],
        returns=[
            ReturnInfo(
                address="0x401010",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("x", 0, size=4),
                    Expression.constant(2, 4),
                ),
                conditions=[
                    _cond_ne(
                        Expression.parameter("x", 0, size=4),
                        Expression.constant(0, 4),
                    )
                ],
                branch_index=0,
            )
        ],
        return_type="int",
    )

    with patch.object(analyzer, "_get_or_analyze_call_target", return_value=callee_analysis):
        expanded = analyzer._resolve_call_expansions(
            "callee",
            [_param_expr("arg0", 0, size=4)],
            active_functions=set(),
        )

    assert expanded is not None
    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "(arg0 + 2)"
    assert [cond.to_string() for cond in expanded[0].conditions] == ["(arg0 != 0)"]
    assert [cond.to_string() for cond in expanded[0].conditions] == ["(arg0 != 0)"]


def test_return_analyzer_allows_safe_call_summary_despite_incomplete_control_flow():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    callee_analysis = FunctionReturnAnalysis(
        function_name="callee",
        entry_point="0x401000",
        parameters=[{"name": "x", "size": 4, "index": 0}],
        returns=[
            ReturnInfo(
                address="0x401010",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("x", 0, size=4),
                    Expression.constant(2, 4),
                ),
                conditions=[
                    _cond_ne(
                        Expression.parameter("x", 0, size=4),
                        Expression.constant(0, 4),
                    )
                ],
                branch_index=0,
            )
        ],
        return_type="int",
        unknown_event_count=4,
        unknown_event_reasons=["OTHER"],
        incomplete_control_flow=True,
    )

    with patch.object(analyzer, "_get_or_analyze_call_target", return_value=callee_analysis):
        expanded = analyzer._resolve_call_expansions(
            "callee",
            [_param_expr("arg0", 0, size=4)],
            active_functions=set(),
        )

    assert expanded is not None
    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "(arg0 + 2)"


def test_return_analyzer_accepts_pure_passthrough_ops_after_terminal_call():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    class _FakeOp:
        def __init__(self, mnemonic):
            self._mnemonic = mnemonic

        def getMnemonic(self):
            return self._mnemonic

    call_op = _FakeOp("CALL")
    copy_op = _FakeOp("COPY")
    subpiece_op = _FakeOp("SUBPIECE")
    return_op = _FakeOp("RETURN")
    block_info = Mock(pcode_ops=[call_op, copy_op, subpiece_op, return_op])

    terminal = analyzer._find_terminal_call_on_block_path([block_info], return_op)

    assert terminal is call_op


def test_expression_expander_inlines_direct_call_results():
    class _FakeVarnode:
        def __init__(self, name, size=4):
            self.name = name
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class _FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class _FakeCallOp:
        def __init__(self, target, arg):
            self._inputs = [target, arg]
            self._output = _FakeOutput(4)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

    target_varnode = _FakeVarnode("callee_addr", size=8)
    arg_varnode = _FakeVarnode("arg0", size=4)

    class _FakeTracer:
        debug = False

        def _get_function_name(self, _varnode):
            return "callee"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return Expression.constant(0x401000, 8)
            if varnode is arg_varnode:
                return _param_expr("arg0", 0, size=4)
            raise AssertionError(f"unexpected varnode: {varnode}")

        def emit_unknown_event(self, **kwargs):
            raise AssertionError(f"call should have been resolved: {kwargs}")

        def _trace_pcode_op(self, *_args, **_kwargs):
            raise AssertionError("recursive tracing fallback should not run")

    def _resolve_call(function_name, args):
        assert function_name == "callee"
        assert len(args) == 1
        return [
            ExpandedValue(
                Expression.binary_op("INT_ADD", args[0], Expression.constant(1, 4)),
                [_cond_ne(args[0], Expression.constant(0, 4))],
            )
        ]

    expander = ExpressionExpander(
        _FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=_resolve_call,
    )
    base_conditions = [_cond_eq(_param_expr("arg0", 0, size=4), Expression.constant(7, 4))]

    expanded = expander._expand_call_operation(
        _FakeCallOp(target_varnode, arg_varnode),
        base_conditions,
        depth=0,
        output_size=4,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "(arg0 + 1)"
    assert [cond.to_string() for cond in expanded[0].conditions] == ["(arg0 == 7)"]


def test_expression_expander_truncates_wide_call_summary_to_call_output_size():
    class _FakeVarnode:
        def __init__(self, name, size=4):
            self.name = name
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class _FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class _FakeCallOp:
        def __init__(self, target, arg):
            self._inputs = [target, arg]
            self._output = _FakeOutput(4)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

    target_varnode = _FakeVarnode("callee_addr", size=8)
    arg_varnode = _FakeVarnode("arg0", size=4)

    class _FakeTracer:
        debug = False

        def _get_function_name(self, _varnode):
            return "callee"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return Expression.constant(0x401000, 8)
            if varnode is arg_varnode:
                return _param_expr("arg0", 0, size=4)
            raise AssertionError(f"unexpected varnode: {varnode}")

        def emit_unknown_event(self, **kwargs):
            raise AssertionError(f"call should have been resolved: {kwargs}")

        def _trace_pcode_op(self, *_args, **_kwargs):
            raise AssertionError("recursive tracing fallback should not run")

    def _resolve_call(function_name, args):
        assert function_name == "callee"
        assert len(args) == 1
        return [
            ExpandedValue(
                Expression.binary_op("INT_ADD", args[0], Expression.constant(1, 8)),
                [],
            )
        ]

    expander = ExpressionExpander(
        _FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=_resolve_call,
    )

    expanded = expander._expand_call_operation(
        _FakeCallOp(target_varnode, arg_varnode),
        [],
        depth=0,
        output_size=4,
    )

    assert len(expanded) == 1
    assert expanded[0].value.operator == "SUBPIECE"
    assert expanded[0].value.size == 4
    assert expanded[0].value.operands[0].to_string() == "(arg0 + 1)"


def test_expression_expander_recovers_callee_aligned_call_arguments_before_resolution():
    class _FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return "ram"

    class _FakeSeqnum:
        def __init__(self, offset, order):
            self._target = _FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class _FakeVarnode:
        def __init__(self, name, size=4):
            self.name = name
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class _FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class _FakeCallOp:
        def __init__(self, inputs):
            self._inputs = inputs
            self._output = _FakeOutput(4)
            self._seqnum = _FakeSeqnum(0x401020, 10)

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

    target_varnode = _FakeVarnode("callee_addr", size=8)
    hidden_varnode = _FakeVarnode("hidden", size=4)
    lhs_varnode = _FakeVarnode("lhs", size=4)
    rhs_varnode = _FakeVarnode("rhs", size=4)
    bias_varnode = _FakeVarnode("bias", size=4)
    call_op = _FakeCallOp([target_varnode, hidden_varnode, lhs_varnode, rhs_varnode, bias_varnode])

    class _FakeTracer:
        debug = False

        def _get_function_name(self, _varnode):
            return "callee"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return Expression.constant(0x401000, 8)
            raise AssertionError(f"unexpected direct trace: {varnode}")

        def emit_unknown_event(self, **kwargs):
            raise AssertionError(f"call should have been resolved: {kwargs}")

        def _trace_pcode_op(self, *_args, **_kwargs):
            raise AssertionError("recursive tracing fallback should not run")

        def get_all_pcode_ops(self):
            return [call_op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    captured = {}

    def _resolve_call(function_name, args):
        captured["target"] = function_name
        captured["args"] = list(args)
        return [ExpandedValue(Expression.constant(7, 4), [])]

    expander = ExpressionExpander(
        _FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=_resolve_call,
        parameters=[
            {
                "name": "param_1",
                "index": 0,
                "size": 4,
                "storage": {
                    "is_register": True,
                    "register_name": "a0",
                    "base_register_name": "a0",
                    "bit_offset_in_base": 0,
                    "size_bits": 32,
                    "base_register_size_bits": 32,
                    "size": 4,
                },
            },
            {
                "name": "param_2",
                "index": 1,
                "size": 4,
                "storage": {
                    "is_register": True,
                    "register_name": "a1",
                    "base_register_name": "a1",
                    "bit_offset_in_base": 0,
                    "size_bits": 32,
                    "base_register_size_bits": 32,
                    "size": 4,
                },
            },
            {
                "name": "param_3",
                "index": 2,
                "size": 4,
                "storage": {
                    "is_register": True,
                    "register_name": "a2",
                    "base_register_name": "a2",
                    "bit_offset_in_base": 0,
                    "size_bits": 32,
                    "base_register_size_bits": 32,
                    "size": 4,
                },
            },
        ],
        resolve_callee_parameters=lambda _name: [
            {
                "name": "lhs",
                "index": 0,
                "size": 4,
                "storage": {
                    "is_register": True,
                    "register_name": "a0",
                    "base_register_name": "a0",
                    "bit_offset_in_base": 0,
                    "size_bits": 32,
                    "base_register_size_bits": 32,
                    "size": 4,
                },
            },
            {
                "name": "rhs",
                "index": 1,
                "size": 4,
                "storage": {
                    "is_register": True,
                    "register_name": "a1",
                    "base_register_name": "a1",
                    "bit_offset_in_base": 0,
                    "size_bits": 32,
                    "base_register_size_bits": 32,
                    "size": 4,
                },
            },
            {
                "name": "bias",
                "index": 2,
                "size": 4,
                "storage": {
                    "is_register": True,
                    "register_name": "a2",
                    "base_register_name": "a2",
                    "bit_offset_in_base": 0,
                    "size_bits": 32,
                    "base_register_size_bits": 32,
                    "size": 4,
                },
            },
        ],
    )
    expander._expand_input_varnode = Mock(
        side_effect=lambda varnode, _conds, _depth: {
            hidden_varnode: [
                ExpandedValue(
                    Expression.binary_op(
                        "INT_SUB",
                        _param_expr("param_1", 0, size=4),
                        _param_expr("param_2", 1, size=4),
                    ),
                    [],
                )
            ],
            lhs_varnode: [ExpandedValue(_param_expr("param_1", 0, size=4), [])],
            rhs_varnode: [ExpandedValue(_param_expr("param_2", 1, size=4), [])],
            bias_varnode: [ExpandedValue(Expression.constant(1, 4), [])],
        }[varnode]
    )

    expanded = expander._expand_call_operation(
        call_op,
        [],
        depth=0,
        output_size=4,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "7"
    assert captured["target"] == "callee"
    assert [arg.to_string() for arg in captured["args"]] == ["param_1", "param_2", "1"]


def test_expression_expander_resolves_guarded_indirect_dispatch_from_readonly_table():
    class _FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class _FakeFunctionManager:
        def __init__(self, mapping):
            self._mapping = mapping

        def getFunctionAt(self, addr):
            name = self._mapping.get(addr)
            return _FakeFunction(name) if name else None

        def getFunctionContaining(self, addr):
            return self.getFunctionAt(addr)

    class _FakeAddressSpace:
        def getAddress(self, value):
            return value

    class _FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return _FakeAddressSpace()

    class _FakeProgram:
        def __init__(self, mapping):
            self._mapping = mapping

        def getAddressFactory(self):
            return _FakeAddressFactory()

        def getFunctionManager(self):
            return _FakeFunctionManager(self._mapping)

    class _FakeVarnode:
        def __init__(self, name, size=8):
            self.name = name
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class _FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class _FakeCallIndOp:
        def __init__(self, target):
            self._inputs = [target]
            self._output = _FakeOutput(4)

        def getMnemonic(self):
            return "CALLIND"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

    param = Expression.parameter("param_1", 0, size=4)
    index = Expression.unary_op("INT_ZEXT", param)
    index.size = 8
    table_address = Expression.binary_op(
        "INT_ADD",
        Expression.variable("PTR_00114058", size=8),
        Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_MULT", index, Expression.constant(8, 8)),
            Expression.constant(0x3668, 8),
        ),
    )
    target_expr = Expression.binary_op(
        "INT_ADD",
        Expression.constant(0x11C010, 8),
        Expression.memory(table_address, size=8),
    )
    range_guard = Condition(
        Expression.binary_op("INT_LESS", param, Expression.constant(4, 4)),
        False,
    )

    target_varnode = _FakeVarnode("dispatch_target", size=8)
    function_map = {
        0x11C110: "case_0",
        0x11C120: "case_1",
        0x11C130: "case_2",
        0x11C140: "case_3",
    }

    class _FakeTracer:
        debug = False

        def __init__(self):
            self.program = _FakeProgram(function_map)
            self.unknown_events = []

        def _get_function_name(self, _varnode):
            return "UNKNOWN_FUNC"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return target_expr
            raise AssertionError(f"unexpected varnode: {varnode}")

        def emit_unknown_event(self, **kwargs):
            self.unknown_events.append(kwargs)

    table = {
        0x114058: 0,
        0x11C010 + 0x3668 + 0x0: 0x100,
        0x11C010 + 0x3668 + 0x8: 0x110,
        0x11C010 + 0x3668 + 0x10: 0x120,
        0x11C010 + 0x3668 + 0x18: 0x130,
    }
    return_values = {
        "case_0": 1000,
        "case_1": 1001,
        "case_2": 1002,
        "case_3": 1003,
    }

    def _resolve_call(function_name, args):
        assert args == []
        return [ExpandedValue(Expression.constant(return_values[function_name], 4), [])]

    expander = ExpressionExpander(
        _FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=_resolve_call,
        parameters=[{"name": "param_1", "index": 0, "size": 4, "is_signed": False}],
        read_memory_value=lambda addr, size: table.get(addr),
        image_base=0x11C010,
    )

    expanded = expander._expand_call_operation(
        _FakeCallIndOp(target_varnode),
        [range_guard],
        depth=0,
        output_size=4,
    )

    assert [ev.value.value for ev in expanded] == [1000, 1001, 1002, 1003]
    assert all(ev.conditions for ev in expanded)


def test_expression_expander_records_recovered_args_for_deferred_call_fallback():
    reg_a0 = {
        "register_name": "a0",
        "base_register_name": "a0",
        "space_name": "register",
        "size": 8,
        "size_bits": 64,
        "base_register_size": 8,
        "base_register_size_bits": 64,
        "bit_offset_in_base": 0,
        "is_register": True,
    }
    reg_a1_lo = {
        "register_name": "a1_lo",
        "base_register_name": "a1",
        "space_name": "register",
        "size": 4,
        "size_bits": 32,
        "base_register_size": 8,
        "base_register_size_bits": 64,
        "bit_offset_in_base": 32,
        "is_register": True,
    }
    reg_a2_lo = {
        "register_name": "a2_lo",
        "base_register_name": "a2",
        "space_name": "register",
        "size": 4,
        "size_bits": 32,
        "base_register_size": 8,
        "base_register_size_bits": 64,
        "bit_offset_in_base": 32,
        "is_register": True,
    }

    class _FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return "ram"

    class _FakeSeqnum:
        def __init__(self, offset, order):
            self._target = _FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class _FakeVarnode:
        def __init__(self, name, size=8):
            self.name = name
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class _FakeOutput:
        def getSize(self):
            return 4

    class _FakeCallOp:
        def __init__(self, target):
            self._inputs = [target]
            self._output = _FakeOutput()
            self._seqnum = _FakeSeqnum(0x1000, 0)

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

    target_varnode = _FakeVarnode("callee_addr", size=8)
    call_op = _FakeCallOp(target_varnode)
    recorded = {}

    class _FakeTracer:
        debug = False

        def _get_function_name(self, _varnode):
            return "callee"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return Expression.constant(0x401000, 8)
            raise AssertionError(f"unexpected varnode: {varnode}")

        def emit_unknown_event(self, **kwargs):
            recorded["unknown_event"] = kwargs

        def _trace_pcode_op(self, *_args, **_kwargs):
            raise AssertionError("recursive tracing fallback should not run")

        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    def _record_deferred_call(target_name, args):
        recorded["call"] = (target_name, [arg.to_string() for arg in args])
        return "call_out_of_scope:callee#0"

    expander = ExpressionExpander(
        _FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=lambda _name, _args: None,
        parameters=[
            {"name": "param_1", "index": 0, "size": 8, "storage": reg_a0},
            {"name": "param_2", "index": 1, "size": 4, "storage": reg_a1_lo},
            {"name": "param_3", "index": 2, "size": 4, "storage": reg_a2_lo},
        ],
        resolve_callee_parameters=lambda _name: [
            {"name": "trace", "index": 0, "size": 8, "storage": reg_a0},
            {"name": "start", "index": 1, "size": 4, "storage": reg_a1_lo},
            {"name": "limit", "index": 2, "size": 4, "storage": reg_a2_lo},
        ],
        record_deferred_call=_record_deferred_call,
    )

    expanded = expander._expand_call_operation(
        call_op,
        [],
        depth=0,
        output_size=4,
    )

    assert len(expanded) == 1
    assert recorded["call"][0] == "callee"
    assert recorded["call"][1] == ["param_1", "param_2", "param_3"]
    assert expanded[0].value.to_string() == "call_out_of_scope:callee#0"


def test_expression_expander_resolves_guarded_indirect_dispatch_with_wrapped_pic_offsets():
    class _FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class _FakeFunctionManager:
        def __init__(self, mapping):
            self._mapping = mapping

        def getFunctionAt(self, addr):
            name = self._mapping.get(addr)
            return _FakeFunction(name) if name else None

    class _FakeAddressSpace:
        def getAddress(self, value):
            return value

    class _FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return _FakeAddressSpace()

    class _FakeProgram:
        def __init__(self, mapping):
            self._mapping = mapping

        def getAddressFactory(self):
            return _FakeAddressFactory()

        def getFunctionManager(self):
            return _FakeFunctionManager(self._mapping)

    class _FakeVarnode:
        def __init__(self, name, size=8):
            self.name = name
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class _FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class _FakeCallIndOp:
        def __init__(self, target):
            self._inputs = [target]
            self._output = _FakeOutput(8)

        def getMnemonic(self):
            return "CALLIND"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

    param = Expression.parameter("param_1", 0, size=4)
    widened = Expression.unary_op("INT_ZEXT", param)
    widened.size = 8
    table_address = Expression.binary_op(
        "INT_ADD",
        Expression.variable("PTR_00114058", size=8),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op(
                "INT_ADD",
                Expression.binary_op("INT_MULT", widened, Expression.constant(8, 8)),
                Expression.constant(0x3668, 8),
            ),
            Expression.constant(1, 8),
        ),
    )
    loaded_offset = Expression.memory(table_address, size=8)
    target_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.constant(0, 8), Expression.constant(0x11C010, 8)),
        Expression.binary_op("INT_MULT", loaded_offset, Expression.constant(1, 8)),
    )
    range_guard = Condition(
        Expression.binary_op("INT_LESS", widened, Expression.constant(4, 8)),
        False,
    )

    target_varnode = _FakeVarnode("dispatch_target", size=8)
    function_map = {
        0x102528: "case_0",
        0x102538: "case_1",
        0x102548: "case_2",
        0x102558: "case_3",
    }

    class _FakeTracer:
        debug = False

        def __init__(self):
            self.program = _FakeProgram(function_map)
            self.unknown_events = []

        def _get_function_name(self, _varnode):
            return "UNKNOWN_FUNC"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return target_expr
            raise AssertionError(f"unexpected varnode: {varnode}")

        def emit_unknown_event(self, **kwargs):
            self.unknown_events.append(kwargs)

    table = {
        0x114058: 0,
        0x100000 + 0x3668 + 0x0: 0xFFFFFFFFFFFE6518,
        0x100000 + 0x3668 + 0x8: 0xFFFFFFFFFFFE6528,
        0x100000 + 0x3668 + 0x10: 0xFFFFFFFFFFFE6538,
        0x100000 + 0x3668 + 0x18: 0xFFFFFFFFFFFE6548,
    }
    return_values = {
        "case_0": 1000,
        "case_1": 1001,
        "case_2": 1002,
        "case_3": 1003,
    }

    def _resolve_call(function_name, args):
        assert args == []
        return [ExpandedValue(Expression.constant(return_values[function_name], 8), [])]

    expander = ExpressionExpander(
        _FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=_resolve_call,
        parameters=[{"name": "param_1", "index": 0, "size": 4, "is_signed": False}],
        read_memory_value=lambda addr, size: table.get(addr),
        image_base=0x100000,
    )

    expanded = expander._expand_call_operation(
        _FakeCallIndOp(target_varnode),
        [range_guard],
        depth=0,
        output_size=8,
    )

    assert [ev.value.value for ev in expanded] == [1000, 1001, 1002, 1003]
    assert all(ev.conditions for ev in expanded)


def test_expression_expander_resolves_guarded_indirect_dispatch_to_raw_code_targets():
    class _FakeInstruction:
        pass

    class _FakeListing:
        def __init__(self, instruction_addrs):
            self._instruction_addrs = set(instruction_addrs)

        def getInstructionAt(self, addr):
            return _FakeInstruction() if addr in self._instruction_addrs else None

    class _FakeFunctionManager:
        def getFunctionAt(self, _addr):
            return None

    class _FakeAddressSpace:
        def getAddress(self, value):
            return value

    class _FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return _FakeAddressSpace()

    class _FakeProgram:
        def __init__(self, instruction_addrs):
            self._listing = _FakeListing(instruction_addrs)

        def getAddressFactory(self):
            return _FakeAddressFactory()

        def getFunctionManager(self):
            return _FakeFunctionManager()

        def getListing(self):
            return self._listing

    class _FakeVarnode:
        def __init__(self, name, size=8):
            self.name = name
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class _FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class _FakeCallIndOp:
        def __init__(self, target):
            self._inputs = [target]
            self._output = _FakeOutput(8)

        def getMnemonic(self):
            return "CALLIND"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

    param = Expression.parameter("param_1", 0, size=4)
    widened = Expression.unary_op("INT_ZEXT", param)
    widened.size = 8
    table_address = Expression.binary_op(
        "INT_ADD",
        Expression.variable("PTR_00114058", size=8),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op(
                "INT_ADD",
                Expression.binary_op("INT_MULT", widened, Expression.constant(8, 8)),
                Expression.constant(0x3668, 8),
            ),
            Expression.constant(1, 8),
        ),
    )
    loaded_offset = Expression.memory(table_address, size=8)
    target_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.constant(0, 8), Expression.constant(0x11C010, 8)),
        Expression.binary_op("INT_MULT", loaded_offset, Expression.constant(1, 8)),
    )
    range_guard = Condition(
        Expression.binary_op("INT_LESS", widened, Expression.constant(4, 8)),
        False,
    )

    target_varnode = _FakeVarnode("dispatch_target", size=8)

    class _FakeTracer:
        debug = False

        def __init__(self):
            self.program = _FakeProgram({0x102528, 0x102538, 0x102548, 0x102558})
            self.unknown_events = []

        def _get_function_name(self, _varnode):
            return "UNKNOWN_FUNC"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return target_expr
            raise AssertionError(f"unexpected varnode: {varnode}")

        def emit_unknown_event(self, **kwargs):
            self.unknown_events.append(kwargs)

    table = {
        0x114058: 0,
        0x100000 + 0x3668 + 0x0: 0xFFFFFFFFFFFE6518,
        0x100000 + 0x3668 + 0x8: 0xFFFFFFFFFFFE6528,
        0x100000 + 0x3668 + 0x10: 0xFFFFFFFFFFFE6538,
        0x100000 + 0x3668 + 0x18: 0xFFFFFFFFFFFE6548,
    }
    return_values = {
        "ADDR_102528": 1000,
        "ADDR_102538": 1001,
        "ADDR_102548": 1002,
        "ADDR_102558": 1003,
    }

    def _resolve_call(function_name, args):
        assert args == []
        return [ExpandedValue(Expression.constant(return_values[function_name], 8), [])]

    expander = ExpressionExpander(
        _FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=_resolve_call,
        parameters=[{"name": "param_1", "index": 0, "size": 4, "is_signed": False}],
        read_memory_value=lambda addr, size: table.get(addr),
        image_base=0x100000,
    )

    expanded = expander._expand_call_operation(
        _FakeCallIndOp(target_varnode),
        [range_guard],
        depth=0,
        output_size=8,
    )

    assert [ev.value.value for ev in expanded] == [1000, 1001, 1002, 1003]
    assert all(ev.conditions for ev in expanded)


def test_return_analyzer_dispatches_local_address_targets_before_normal_call_resolution():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    captured = []

    def _fake_local(address_value, active_functions, current_function):
        captured.append((address_value, active_functions, current_function))
        return ["ok"]

    analyzer._resolve_local_code_target_expansions = _fake_local

    resolved = analyzer._resolve_call_expansions("ADDR_102528", [], {"branch_switch_dense"})

    assert resolved == ["ok"]
    assert captured == [(0x102528, {"branch_switch_dense"}, None)]


def test_return_analyzer_uses_current_function_when_containing_lookup_fails():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    current_function = Mock()
    current_function.getName.return_value = "branch_switch_dense"

    fake_body = Mock()
    fake_body.contains.return_value = False
    fake_min = Mock()
    fake_min.getOffset.return_value = 0x1024C8
    fake_max = Mock()
    fake_max.getOffset.return_value = 0x10258C
    fake_body.getMinAddress.return_value = fake_min
    fake_body.getMaxAddress.return_value = fake_max
    current_function.getBody.return_value = fake_body

    addr_obj = Mock()
    addr_obj.getOffset.return_value = 0x102528
    analyzer.program.getAddressFactory.return_value.getDefaultAddressSpace.return_value.getAddress.return_value = addr_obj
    analyzer.program.getFunctionManager.return_value.getFunctionContaining.return_value = None

    with patch.object(analyzer, "_get_decompiler") as mock_get_decompiler, patch.object(
        analyzer, "_expand_linear_code_target", return_value=["expanded"]
    ):
        mock_results = Mock()
        mock_results.decompileCompleted.return_value = True
        mock_results.getHighFunction.return_value = Mock()
        mock_decompiler = Mock()
        mock_decompiler.decompileFunction.return_value = mock_results
        mock_get_decompiler.return_value = mock_decompiler

        resolved = analyzer._resolve_local_code_target_expansions(
            0x102528,
            {"branch_switch_dense"},
            current_function=current_function,
        )

    assert resolved == ["expanded"]


def test_return_analyzer_disassembles_local_target_and_follows_unconditional_branch():
    class _FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

        def __str__(self):
            return f"{self._offset:08x}"

    class _FakeVarnode:
        pass

    class _FakePcodeOp:
        def __init__(self, mnemonic, inputs=None):
            self._mnemonic = mnemonic
            self._inputs = list(inputs or [])

        def getMnemonic(self):
            return self._mnemonic

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class _FakeInstruction:
        def __init__(self, addr, pcode_ops, flows=None, next_instruction=None):
            self._addr = addr
            self._pcode_ops = list(pcode_ops)
            self._flows = list(flows or [])
            self._next = next_instruction

        def getAddress(self):
            return self._addr

        def getPcode(self):
            return self._pcode_ops

        def getFlows(self):
            return list(self._flows)

        def getFallThrough(self):
            return None

        def getNext(self):
            return self._next

    class _FakeListing:
        def __init__(self, start_addr, start_instruction, target_instruction):
            self._start_addr = start_addr
            self._start_instruction = start_instruction
            self._target_instruction = target_instruction
            self.disassembled = False

        def getInstructionAt(self, addr):
            if addr.getOffset() == self._start_addr.getOffset():
                return self._start_instruction if self.disassembled else None
            if addr.getOffset() == self._target_instruction.getAddress().getOffset():
                return self._target_instruction
            return None

        def getInstructionContaining(self, addr):
            return self.getInstructionAt(addr)

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    start_addr = _FakeAddress(0x102528)
    target_addr = _FakeAddress(0x102570)
    ret_varnode = _FakeVarnode()
    branch_instruction = _FakeInstruction(
        start_addr,
        [_FakePcodeOp("BRANCH")],
        flows=[target_addr],
    )
    return_instruction = _FakeInstruction(
        target_addr,
        [_FakePcodeOp("RETURN", [object(), ret_varnode])],
    )
    listing = _FakeListing(start_addr, branch_instruction, return_instruction)
    analyzer.program.getListing.return_value = listing

    tracer = Mock()
    tracer.trace_varnode.return_value = Expression.constant(1000, 4)

    def _fake_disassemble(addr):
        assert addr is start_addr
        listing.disassembled = True
        return True

    analyzer._attempt_disassemble_at = _fake_disassemble

    expanded = analyzer._expand_linear_code_target(start_addr, tracer)

    assert expanded is not None
    assert len(expanded) == 1
    assert expanded[0].value.value == 1000
    tracer.trace_varnode.assert_called_once_with(ret_varnode, use_cache=False)


def test_return_analyzer_program_transaction_commits_on_success():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer.program.startTransaction.return_value = 7

    with analyzer._program_transaction("disassemble target"):
        pass

    analyzer.program.startTransaction.assert_called_once_with("disassemble target")
    analyzer.program.endTransaction.assert_called_once_with(7, True)


def test_return_analyzer_tracks_local_store_load_into_return_register():
    class _FakeAddressSpace:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class _FakeAddress:
        def __init__(self, offset, space="ram"):
            self._offset = offset
            self._space = _FakeAddressSpace(space)

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self._space

        def __str__(self):
            return f"{self._offset:08x}"

    class _FakeVarnode:
        def __init__(self, offset, size, space="register", is_constant=False, def_op=None):
            self._offset = offset
            self._size = size
            self._space = space
            self._is_constant = is_constant
            self._def_op = def_op
            self._address = _FakeAddress(offset, space=space)

        def getAddress(self):
            return self._address

        def getOffset(self):
            return self._offset

        def getSize(self):
            return self._size

        def getDef(self):
            return self._def_op

        def isConstant(self):
            return self._is_constant

    class _FakeOutput:
        def __init__(self, varnode):
            self._varnode = varnode

        def getAddress(self):
            return self._varnode.getAddress()

        def getOffset(self):
            return self._varnode.getOffset()

        def getSize(self):
            return self._varnode.getSize()

    class _FakePcodeOp:
        def __init__(self, mnemonic, inputs=None, output=None):
            self._mnemonic = mnemonic
            self._inputs = list(inputs or [])
            self._output = output

        def getMnemonic(self):
            return self._mnemonic

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

    class _FakeInstruction:
        def __init__(self, addr, pcode_ops, flows=None, next_instruction=None):
            self._addr = addr
            self._pcode_ops = list(pcode_ops)
            self._flows = list(flows or [])
            self._next = next_instruction

        def getAddress(self):
            return self._addr

        def getPcode(self):
            return self._pcode_ops

        def getFlows(self):
            return list(self._flows)

        def getFallThrough(self):
            return None

        def getNext(self):
            return self._next

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()

    start_addr = _FakeAddress(0x102528)
    target_addr = _FakeAddress(0x102578)
    space_vn = _FakeVarnode(0, 8, space="const", is_constant=True)
    stack_slot_vn = _FakeVarnode(0x2000, 8, space="const", is_constant=True)
    stored_value_vn = _FakeVarnode(1000, 4, space="const", is_constant=True)
    return_reg_vn = _FakeVarnode(0x10, 4, space="register", is_constant=False)

    store_instruction = _FakeInstruction(
        start_addr,
        [
            _FakePcodeOp("STORE", [space_vn, stack_slot_vn, stored_value_vn]),
            _FakePcodeOp("BRANCH"),
        ],
        flows=[target_addr],
    )
    load_instruction = _FakeInstruction(
        target_addr,
        [
            _FakePcodeOp("LOAD", [space_vn, stack_slot_vn], output=return_reg_vn),
        ],
    )
    return_instruction = _FakeInstruction(
        _FakeAddress(0x10258C),
        [_FakePcodeOp("RETURN", [object()])],
    )
    load_instruction._next = return_instruction

    analyzer._get_instruction_with_fallback = Mock(side_effect=[store_instruction, load_instruction])

    current_function = Mock()
    current_function.getReturn.return_value.getVariableStorage.return_value.getVarnodes.return_value = [return_reg_vn]

    expanded = analyzer._expand_linear_code_target(start_addr, tracer, current_function=current_function)

    assert expanded is not None
    assert len(expanded) == 1
    assert expanded[0].value.value == 1000
    tracer.trace_varnode.assert_not_called()


def test_return_analyzer_resolves_return_register_alias_from_local_output():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()

    class _Storage:
        def __init__(self, register_name, base_register_name, size_bits, bit_offset_in_base):
            self.is_register = True
            self.register_name = register_name
            self.base_register_name = base_register_name
            self.size_bits = size_bits
            self.size = size_bits // 8
            self.bit_offset_in_base = bit_offset_in_base

        def shares_base_register_with(self, other):
            return self.base_register_name == other.base_register_name

        def bit_range_overlaps_with(self, other):
            self_high = self.bit_offset_in_base + self.size_bits
            other_high = other.bit_offset_in_base + other.size_bits
            return not (self_high <= other.bit_offset_in_base or other_high <= self.bit_offset_in_base)

    output_varnode = Mock()
    return_varnode = Mock()
    output_varnode.getAddress.side_effect = RuntimeError("unused in test")
    return_varnode.getAddress.side_effect = RuntimeError("unused in test")
    output_varnode.getSize.return_value = 8
    return_varnode.getSize.return_value = 4

    tracer._get_storage_info_from_varnode.side_effect = lambda vn: (
        _Storage("v0", "v0", 64, 0) if vn is output_varnode else _Storage("v0_lo", "v0", 32, 32)
    )

    local_values = {("synthetic", 1, 8): Expression.constant(1000, 8)}
    local_storages = {("synthetic", 1, 8): tracer._get_storage_info_from_varnode(output_varnode)}

    aliased = analyzer._lookup_local_alias_expression(return_varnode, tracer, local_values, local_storages)

    assert aliased is not None
    assert aliased.value == 1000
    assert aliased.size == 4


def test_return_analyzer_recovers_implicit_return_from_same_block_output():
    class _FakeStorage:
        def __init__(self, register_name, base_register_name, size_bits, bit_offset_in_base):
            self.is_register = True
            self.register_name = register_name
            self.base_register_name = base_register_name
            self.size_bits = size_bits
            self.size = size_bits // 8
            self.bit_offset_in_base = bit_offset_in_base

        def shares_base_register_with(self, other):
            return self.base_register_name == other.base_register_name

        def bit_range_overlaps_with(self, other):
            self_high = self.bit_offset_in_base + self.size_bits
            other_high = other.bit_offset_in_base + other.size_bits
            return not (self_high <= other.bit_offset_in_base or other_high <= self.bit_offset_in_base)

    class _FakeOp:
        def __init__(self, mnemonic, output=None):
            self._mnemonic = mnemonic
            self._output = output
            self._parent = object()
            self._seq = Mock()
            self._seq.getTarget.return_value = "0x1000"

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

        def getParent(self):
            return self._parent

        def getSeqnum(self):
            return self._seq

        def getNumInputs(self):
            return 1

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()
    condition_tracker = Mock()
    condition_tracker.get_all_valid_block_paths_to_return.return_value = Mock(name="invalid_path_entries")
    condition_tracker.get_path_conditions_to_return.return_value = []
    condition_tracker.get_all_valid_paths_to_return.return_value = [[]]

    source_varnode = Mock(name="source_varnode")
    return_varnode = Mock(name="return_varnode")
    return_op = _FakeOp("RETURN")

    block_info = Mock()
    block_info.pcode_ops = [_FakeOp("COPY", output=source_varnode), return_op]
    condition_tracker.get_block_by_hash.return_value = block_info

    tracer._get_storage_info_from_varnode.side_effect = lambda vn: (
        _FakeStorage("x0", "x0", 64, 0)
        if vn is source_varnode
        else _FakeStorage("w0", "x0", 32, 0)
    )

    current_function = Mock()
    current_function.getReturn.return_value.getVariableStorage.return_value.getVarnodes.return_value = [return_varnode]

    recovered = [ReturnInfo(address="0x1000", value=Expression.constant(7, 4), conditions=[], branch_index=0)]
    with patch.object(analyzer, "_analyze_return_value", return_value=recovered) as mock_analyze:
        result = analyzer._analyze_return_op(
            return_op,
            tracer,
            condition_tracker,
            0,
            current_function=current_function,
            active_functions=set(),
        )

    assert result == recovered
    assert mock_analyze.call_args.args[0] is source_varnode


def test_return_analyzer_recovers_implicit_return_from_predecessor_block_path_output():
    class _FakeStorage:
        def __init__(self, register_name, base_register_name, size_bits, bit_offset_in_base):
            self.is_register = True
            self.register_name = register_name
            self.base_register_name = base_register_name
            self.size_bits = size_bits
            self.size = size_bits // 8
            self.bit_offset_in_base = bit_offset_in_base

        def shares_base_register_with(self, other):
            return self.base_register_name == other.base_register_name

        def bit_range_overlaps_with(self, other):
            self_high = self.bit_offset_in_base + self.size_bits
            other_high = other.bit_offset_in_base + other.size_bits
            return not (self_high <= other.bit_offset_in_base or other_high <= self.bit_offset_in_base)

    class _FakeOp:
        def __init__(self, mnemonic, output=None):
            self._mnemonic = mnemonic
            self._output = output
            self._parent = object()
            self._seq = Mock()
            self._seq.getTarget.return_value = "0x1000"

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

        def getParent(self):
            return self._parent

        def getSeqnum(self):
            return self._seq

        def getNumInputs(self):
            return 1

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()
    condition_tracker = Mock()

    source_varnode = Mock(name="source_varnode")
    return_varnode = Mock(name="return_varnode")
    return_op = _FakeOp("RETURN")

    pred_block = Mock(index=1, pcode_ops=[_FakeOp("COPY", output=source_varnode)])
    return_block = Mock(index=2, pcode_ops=[return_op])

    tracer._get_storage_info_from_varnode.side_effect = lambda vn: (
        _FakeStorage("v0", "v0", 64, 0)
        if vn is source_varnode
        else _FakeStorage("v0_lo", "v0", 32, 32)
    )

    current_function = Mock()
    current_function.getReturn.return_value.getVariableStorage.return_value.getVarnodes.return_value = [return_varnode]

    recovered = [
        ReturnInfo(address="0x1000", value=Expression.constant(13, 4), conditions=[], branch_index=0)
    ]
    with patch.object(analyzer, "_analyze_return_value", return_value=recovered) as mock_analyze:
        result = analyzer._analyze_implicit_return_value(
            return_op,
            "0x1000",
            tracer,
            condition_tracker,
            [],
            0,
            all_path_conditions=[[]],
            path_entries=[([pred_block, return_block], [])],
            active_functions=set(),
            current_function=current_function,
        )

    assert result == recovered
    assert mock_analyze.call_args.args[0] is source_varnode


def test_return_analyzer_uses_abi_fallback_return_storage_when_signature_is_void():
    class _FakeStorage:
        def __init__(self, register_name, base_register_name, size_bits, bit_offset_in_base):
            self.is_register = True
            self.register_name = register_name
            self.base_register_name = base_register_name
            self.size_bits = size_bits
            self.size = size_bits // 8
            self.bit_offset_in_base = bit_offset_in_base

        def shares_base_register_with(self, other):
            return self.base_register_name == other.base_register_name

        def bit_range_overlaps_with(self, other):
            self_high = self.bit_offset_in_base + self.size_bits
            other_high = other.bit_offset_in_base + other.size_bits
            return not (self_high <= other.bit_offset_in_base or other_high <= self.bit_offset_in_base)

    class _FakeOp:
        def __init__(self, mnemonic, output=None):
            self._mnemonic = mnemonic
            self._output = output
            self._parent = object()

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

        def getParent(self):
            return self._parent

    program = Mock()
    language = Mock()
    language.getLanguageID.return_value = "MIPS:BE:64:default"
    language.getProcessor.return_value = "MIPS"
    program.getLanguage.return_value = language
    program.getDefaultPointerSize.return_value = 8

    analyzer = ReturnAnalyzer(program=program, debug=False)
    tracer = Mock()
    condition_tracker = Mock()

    source_varnode = Mock(name="source_varnode")
    return_op = _FakeOp("RETURN")
    pred_block = Mock(index=1, pcode_ops=[_FakeOp("COPY", output=source_varnode)])
    return_block = Mock(index=2, pcode_ops=[return_op])

    tracer._get_storage_info_from_varnode.side_effect = lambda vn: _FakeStorage("v0_lo", "v0", 32, 32)

    current_function = Mock()
    current_function.getReturn.return_value = None

    recovered = [
        ReturnInfo(address="0x1000", value=Expression.constant(21, 4), conditions=[], branch_index=0)
    ]
    with patch.object(analyzer, "_analyze_return_value", return_value=recovered) as mock_analyze:
        result = analyzer._analyze_implicit_return_value(
            return_op,
            "0x1000",
            tracer,
            condition_tracker,
            [],
            0,
            all_path_conditions=[[]],
            path_entries=[([pred_block, return_block], [])],
            active_functions=set(),
            current_function=current_function,
        )

    assert result == recovered
    assert mock_analyze.call_args.args[0] is source_varnode


def test_return_analyzer_prefers_phi_input_for_actual_predecessor_path():
    class _FakeBlock:
        def __init__(self, index):
            self.index = index
            self._ins = []

        def getInSize(self):
            return len(self._ins)

        def getIn(self, index):
            return self._ins[index]

    class _FakePhiOp:
        def __init__(self, inputs, parent):
            self._inputs = inputs
            self._parent = parent

        def getMnemonic(self):
            return "MULTIEQUAL"

        def getParent(self):
            return self._parent

        def getInput(self, index):
            return self._inputs[index]

    predecessor_a = _FakeBlock(1)
    predecessor_b = _FakeBlock(2)
    return_block = _FakeBlock(3)
    return_block._ins = [predecessor_a, predecessor_b]

    input_a = Mock(name="input_a")
    input_b = Mock(name="input_b")
    phi_output = Mock(name="phi_output")
    phi_output.getDef.return_value = _FakePhiOp([input_a, input_b], return_block)

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    selected = analyzer._select_path_specific_return_source(
        phi_output,
        [predecessor_b, return_block],
    )

    assert selected is input_b


def test_return_analyzer_prefers_phi_input_when_phi_block_is_not_last_path_block():
    class _FakeBlock:
        def __init__(self, index):
            self.index = index
            self._ins = []

        def getInSize(self):
            return len(self._ins)

        def getIn(self, index):
            return self._ins[index]

    class _FakePhiOp:
        def __init__(self, inputs, parent):
            self._inputs = inputs
            self._parent = parent

        def getMnemonic(self):
            return "MULTIEQUAL"

        def getParent(self):
            return self._parent

        def getInput(self, index):
            return self._inputs[index]

    entry_block = _FakeBlock(0)
    predecessor_a = _FakeBlock(1)
    predecessor_b = _FakeBlock(2)
    phi_block = _FakeBlock(3)
    return_block = _FakeBlock(4)
    phi_block._ins = [predecessor_a, predecessor_b]

    input_a = Mock(name="input_a")
    input_b = Mock(name="input_b")
    phi_output = Mock(name="phi_output")
    phi_output.getDef.return_value = _FakePhiOp([input_a, input_b], phi_block)

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    selected = analyzer._select_path_specific_return_source(
        phi_output,
        [entry_block, predecessor_b, phi_block, return_block],
    )

    assert selected is input_b


def test_return_analyzer_prefers_phi_input_whose_block_conditions_match_return_path():
    class _FakeBlock:
        def __init__(self, index):
            self.index = index
            self._ins = []

        def getInSize(self):
            return len(self._ins)

        def getIn(self, index):
            return self._ins[index]

        def hashCode(self):
            return self.index

    class _FakePhiOp:
        def __init__(self, inputs, parent):
            self._inputs = inputs
            self._parent = parent

        def getMnemonic(self):
            return "MULTIEQUAL"

        def getParent(self):
            return self._parent

        def getInput(self, index):
            return self._inputs[index]

    predecessor_a = _FakeBlock(1)
    predecessor_b = _FakeBlock(2)
    phi_block = _FakeBlock(3)
    return_block = _FakeBlock(4)
    phi_block._ins = [predecessor_a, predecessor_b]

    input_a = Mock(name="input_a")
    input_b = Mock(name="input_b")
    phi_output = Mock(name="phi_output")
    phi_output.getDef.return_value = _FakePhiOp([input_a, input_b], phi_block)

    current_conditions = [
        _cond_ne(_param_expr("param_1", 0, size=4), Expression.constant(1, 4)),
        _cond_eq(_param_expr("param_2", 1, size=4), Expression.constant(1, 4)),
    ]

    fake_tracker = Mock()
    fake_tracker.get_block_by_hash.side_effect = lambda block: block
    fake_tracker.get_path_conditions_to_block.side_effect = lambda block: {
        predecessor_a: [_cond_eq(_param_expr("param_2", 1, size=4), Expression.constant(1, 4))],
        predecessor_b: [
            _cond_eq(_param_expr("param_2", 1, size=4), Expression.constant(1, 4)),
            _cond_ne(_param_expr("param_1", 0, size=4), Expression.constant(1, 4)),
        ],
    }[block]

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    selected = analyzer._select_path_specific_return_source(
        phi_output,
        [predecessor_a, phi_block, return_block],
        condition_tracker=fake_tracker,
        path_conditions=current_conditions,
    )

    assert selected is input_b


def test_return_analyzer_falls_back_to_terminal_call_wrapper_recovery():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()
    condition_tracker = Mock()
    return_op = Mock()
    call_op = Mock()
    recovered = [ReturnInfo(address="0x1000", value=Expression.constant(9, 4), conditions=[], branch_index=0)]

    with patch.object(analyzer, "_find_implicit_return_source_varnode", return_value=None):
        with patch.object(analyzer, "_find_terminal_call_before_return", return_value=call_op):
            with patch.object(
                analyzer,
                "_recover_implicit_return_from_terminal_call",
                return_value=recovered,
            ) as mock_recover:
                result = analyzer._analyze_implicit_return_value(
                    return_op,
                    "0x1000",
                    tracer,
                    condition_tracker,
                    [],
                    0,
                    all_path_conditions=[[]],
                    active_functions=set(),
                    current_function=Mock(),
                )

    assert result == recovered
    assert mock_recover.call_args.args[0] is call_op


def test_return_analyzer_uses_last_terminal_call_for_implicit_return_wrapper():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()
    condition_tracker = Mock()
    return_op = Mock()
    call_op_1 = Mock()
    call_op_2 = Mock()

    call_op_1.getMnemonic.return_value = "CALL"
    call_op_1.getOutput.return_value = None
    call_op_2.getMnemonic.return_value = "CALL"
    call_op_2.getOutput.return_value = None
    return_op.getParent.return_value = Mock()

    block_info = Mock()
    block_info.pcode_ops = [call_op_1, call_op_2, return_op]
    condition_tracker.get_block_by_hash.return_value = block_info

    recovered = [ReturnInfo(address="0x1000", value=Expression.constant(9, 4), conditions=[], branch_index=0)]

    with patch.object(analyzer, "_find_implicit_return_source_varnode", return_value=None):
        with patch.object(
            analyzer,
            "_recover_implicit_return_from_terminal_call",
            return_value=recovered,
        ) as mock_recover:
            result = analyzer._analyze_implicit_return_value(
                return_op,
                "0x1000",
                tracer,
                condition_tracker,
                [],
                0,
                all_path_conditions=[[]],
                active_functions=set(),
                current_function=Mock(),
            )

    assert result == recovered
    assert mock_recover.call_args.args[0] is call_op_2


def test_return_analyzer_recovers_call_wrapper_from_pcode_block_paths():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()
    condition_tracker = Mock()
    current_function = Mock()

    analysis = FunctionReturnAnalysis(
        function_name="ptr_select_path",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int"}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("void"), conditions=[], branch_index=0)],
        return_type="void",
    )

    class _Seq:
        def getTarget(self):
            return "0x1000"

    class _FakeOp:
        def __init__(self, mnemonic):
            self._mnemonic = mnemonic

        def getMnemonic(self):
            return self._mnemonic

    call_then = _FakeOp("CALL")
    call_else = _FakeOp("CALL")
    branch = _FakeOp("BRANCH")
    return_op = _FakeOp("RETURN")
    return_op.getSeqnum = Mock(return_value=_Seq())

    then_block = Mock(index=1, pcode_ops=[call_then, branch])
    else_block = Mock(index=2, pcode_ops=[call_else, branch])
    return_block = Mock(index=3, pcode_ops=[return_op])

    cond_then = Condition(
        Expression.binary_op("INT_NOTEQUAL", _param_expr("param_1", 0), Expression.constant(0, 4))
    )
    cond_else = Condition(
        Expression.binary_op("INT_EQUAL", _param_expr("param_1", 0), Expression.constant(0, 4))
    )
    condition_tracker.get_all_valid_block_paths_to_return.return_value = [
        ([then_block, return_block], [cond_then]),
        ([else_block, return_block], [cond_else]),
    ]

    recovered_then = [
        ReturnInfo(
            address="0x1000",
            value=Expression.constant(11, 4),
            conditions=[cond_then],
            branch_index=0,
        )
    ]
    recovered_else = [
        ReturnInfo(
            address="0x1000",
            value=Expression.constant(22, 4),
            conditions=[cond_else],
            branch_index=1,
        )
    ]

    with patch.object(
        analyzer,
        "_recover_implicit_return_from_terminal_call",
        side_effect=[recovered_then, recovered_else],
    ) as mock_recover:
        recovered = analyzer._recover_call_wrapper_returns_from_pcode(
            analysis,
            tracer,
            condition_tracker,
            [return_op],
            current_function,
            set(),
        )

    assert recovered == recovered_then + recovered_else
    assert mock_recover.call_args_list[0].args[0] is call_then
    assert mock_recover.call_args_list[1].args[0] is call_else


def test_return_analyzer_detects_noreturn_stack_chk_fail_target_from_symbol_name():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()
    tracer._get_function_name.return_value = "UNKNOWN_FUNC"
    tracer.trace_varnode.return_value = Expression.variable("PTR___stack_chk_fail_120013158", size=8)

    symbol = Mock()
    symbol.getName.return_value = "PTR___stack_chk_fail_120013158"
    high_var = Mock()
    high_var.getName.return_value = "PTR___stack_chk_fail_120013158"
    high_var.getSymbol.return_value = symbol
    target_varnode = Mock()
    target_varnode.getHigh.return_value = high_var

    call_op = Mock()
    call_op.getMnemonic.return_value = "CALLIND"
    call_op.getNumInputs.return_value = 1
    call_op.getInput.return_value = target_varnode

    assert analyzer._is_noreturn_call_op(call_op, tracer) is True


def test_return_analyzer_prunes_noreturn_paths_before_return_expansion():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()
    tracer._get_function_name.return_value = "UNKNOWN_FUNC"
    tracer.trace_varnode.return_value = Expression.variable("PTR___stack_chk_fail_120013158", size=8)

    symbol = Mock()
    symbol.getName.return_value = "PTR___stack_chk_fail_120013158"
    high_var = Mock()
    high_var.getName.return_value = "PTR___stack_chk_fail_120013158"
    high_var.getSymbol.return_value = symbol
    target_varnode = Mock()
    target_varnode.getHigh.return_value = high_var

    fail_call = Mock()
    fail_call.getMnemonic.return_value = "CALLIND"
    fail_call.getNumInputs.return_value = 1
    fail_call.getInput.return_value = target_varnode

    normal_op = Mock()
    normal_op.getMnemonic.return_value = "COPY"

    return_varnode = Mock()
    return_op = Mock()
    return_op.getSeqnum.return_value = Mock(getTarget=Mock(return_value="0x1000"))
    return_op.getNumInputs.return_value = 2
    return_op.getInput.side_effect = lambda index: return_varnode if index == 1 else None

    cond_ok = _cond_eq(_param_expr("param_1", 0), Expression.constant(0, 4))
    cond_fail = _cond_ne(_param_expr("param_1", 0), Expression.constant(0, 4))
    ok_block = Mock(index=1, pcode_ops=[normal_op, return_op])
    fail_block = Mock(index=2, pcode_ops=[fail_call, return_op])

    condition_tracker = Mock()
    condition_tracker.get_all_valid_block_paths_to_return.return_value = [
        ([ok_block], [cond_ok]),
        ([fail_block], [cond_fail]),
    ]

    recovered = [ReturnInfo(address="0x1000", value=Expression.constant(7, 4), conditions=[cond_ok], branch_index=0)]
    with patch.object(analyzer, "_analyze_return_value", return_value=recovered) as mock_analyze:
        result = analyzer._analyze_return_op(
            return_op,
            tracer,
            condition_tracker,
            0,
            current_function=Mock(),
            active_functions=set(),
        )

    assert result == recovered
    assert mock_analyze.call_args.kwargs["all_path_conditions"] == [[cond_ok]]


def test_return_analyzer_skips_return_when_all_paths_are_pruned_as_noreturn():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()
    tracer._get_function_name.return_value = "UNKNOWN_FUNC"
    tracer.trace_varnode.return_value = Expression.variable("PTR___stack_chk_fail_120013158", size=8)

    symbol = Mock()
    symbol.getName.return_value = "PTR___stack_chk_fail_120013158"
    high_var = Mock()
    high_var.getName.return_value = "PTR___stack_chk_fail_120013158"
    high_var.getSymbol.return_value = symbol
    target_varnode = Mock()
    target_varnode.getHigh.return_value = high_var

    fail_call = Mock()
    fail_call.getMnemonic.return_value = "CALLIND"
    fail_call.getNumInputs.return_value = 1
    fail_call.getInput.return_value = target_varnode

    return_op = Mock()
    return_op.getSeqnum.return_value = Mock(getTarget=Mock(return_value="0x1000"))
    return_op.getNumInputs.return_value = 0

    cond_fail = _cond_ne(_param_expr("param_1", 0), Expression.constant(0, 4))
    fail_block = Mock(index=2, pcode_ops=[fail_call, return_op])

    condition_tracker = Mock()
    condition_tracker.get_all_valid_block_paths_to_return.return_value = [
        ([fail_block], [cond_fail]),
    ]

    result = analyzer._analyze_return_op(
        return_op,
        tracer,
        condition_tracker,
        0,
        current_function=Mock(),
        active_functions=set(),
    )

    assert result == []


def test_return_analyzer_prefers_pcode_wrapper_recovery_before_decompiler_fallback():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="ptr_call_leaf",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int"}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("void"), conditions=[], branch_index=0)],
        return_type="void",
    )
    recovered = [ReturnInfo(address="0x1000", value=Expression.constant(9, 4), conditions=[], branch_index=0)]

    with patch.object(
        analyzer,
        "_recover_call_wrapper_returns_from_pcode",
        return_value=recovered,
    ) as mock_pcode:
        with patch.object(
            analyzer,
            "_recover_call_wrapper_returns_from_decompiler",
            side_effect=AssertionError("decompiler fallback must not run"),
        ):
            result = analyzer._recover_call_wrapper_returns(
                Mock(),
                analysis,
                Mock(),
                Mock(),
                Mock(),
                [],
                set(),
            )

    assert result == recovered
    mock_pcode.assert_called_once()


def test_function_return_analysis_skips_monolithic_fallback_for_nested_unresolved_values():
    param_1 = Expression.parameter("param_1", 0, size=8)
    analysis = FunctionReturnAnalysis(
        function_name="ptr_call_and_store",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "size": 8, "data_type": "int *"}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op(
                    "INT_SUB",
                    Expression.unknown("call_out_of_scope:ptr_call_chain"),
                    Expression.constant(1, 4),
                ),
                conditions=[_cond_ne(param_1, Expression.constant(0, 8))],
                branch_index=0,
            )
        ],
        return_type="int",
        unknown_event_reasons=["call_out_of_scope"],
        unknown_event_count=1,
        incomplete_control_flow=True,
    )

    assert analysis.has_unknown_return() is False
    assert analysis.has_unresolved_return_value() is True
    assert analysis.should_skip_monolithic_fallback() is True


def test_return_analyzer_parses_simple_decompiler_call_wrapper():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    parsed = analyzer._parse_call_wrapper_from_c_text(
        """void ptr_call_leaf(undefined4 param_1)
{
  ptr_add_bias(param_1,7);
  return;
}
""",
        [{"name": "param_1", "size": 4, "data_type": "undefined4"}],
    )

    assert parsed is not None
    callee_name, args = parsed
    assert callee_name == "ptr_add_bias"
    assert [arg.to_string() for arg in args] == ["param_1", "7"]


def test_return_analyzer_normalizes_pointer_symbol_call_wrapper_to_underlying_function():
    analyzer = ReturnAnalyzer(
        program=_FakeProgram([_FakeFunction("ptr_op_xor", 0x401200)]),
        debug=False,
    )
    parsed = analyzer._parse_call_wrapper_from_c_text(
        """undefined8 ptr_dispatch_callback(undefined4 param_2,undefined4 param_3)
{
  (*(code *)PTR_ptr_op_xor_120013098)(param_2,param_3);
  return;
}
""",
        [
            {"name": "param_2", "size": 4, "data_type": "undefined4"},
            {"name": "param_3", "size": 4, "data_type": "undefined4"},
        ],
    )

    assert parsed is not None
    callee_name, args = parsed
    assert callee_name == "ptr_op_xor"
    assert [arg.to_string() for arg in args] == ["param_2", "param_3"]


def test_return_analyzer_does_not_treat_parameter_name_as_direct_wrapper_callee():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    parsed = analyzer._parse_call_wrapper_from_c_text(
        """void ptr_apply_callback(code *param_1,undefined4 param_2,undefined4 param_3)
{
  (*param_1)(param_2,param_3);
  return;
}
""",
        [
            {"name": "param_1", "size": 8, "data_type": "code *"},
            {"name": "param_2", "size": 4, "data_type": "undefined4"},
            {"name": "param_3", "size": 4, "data_type": "undefined4"},
        ],
    )

    assert parsed is None


def test_return_analyzer_recovers_call_wrapper_from_decompiler_text():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="ptr_call_leaf",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "size": 4, "data_type": "undefined4"}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("void"), conditions=[], branch_index=0)],
        return_type="void",
    )

    with patch.object(
        analyzer,
        "_get_decompiled_c_text",
        return_value="""void ptr_call_leaf(undefined4 param_1)
{
  ptr_add_bias(param_1,7);
  return;
}
""",
    ):
        with patch.object(
            analyzer,
            "_resolve_call_expansions",
            return_value=[ExpandedValue(Expression.constant(42, 4), [])],
        ) as mock_expand:
            recovered = analyzer._recover_call_wrapper_returns_from_decompiler(
                Mock(),
                analysis,
                Mock(),
                set(),
            )

    assert recovered is not None
    assert [ret.value.to_string() for ret in recovered] == ["42"]
    assert mock_expand.call_args.args[0] == "ptr_add_bias"
    assert [arg.to_string() for arg in mock_expand.call_args.args[1]] == ["param_1", "7"]


def test_return_analyzer_recovers_store_then_read_wrapper_with_mixed_unresolved_returns():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    param_1 = Expression.parameter("param_1", 0, size=8)
    param_4 = Expression.parameter("param_4", 3, size=4)
    analysis = FunctionReturnAnalysis(
        function_name="ptr_call_and_store",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "size": 8, "data_type": "int *"},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "int"},
            {"name": "param_3", "index": 2, "size": 4, "data_type": "int"},
            {"name": "param_4", "index": 3, "size": 4, "data_type": "int"},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(0xFFFFFD44, 4),
                conditions=[_cond_eq(param_1, Expression.constant(0, 8))],
                branch_index=0,
            ),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op(
                    "INT_SUB",
                    Expression.unknown("call_out_of_scope:ptr_call_chain"),
                    Expression.parameter("param_2", 1, size=4),
                ),
                conditions=[
                    _cond_ne(param_1, Expression.constant(0, 8)),
                    _cond_eq(param_4, Expression.constant(0, 4)),
                ],
                branch_index=1,
            ),
        ],
        return_type="int",
        unknown_event_reasons=["call_out_of_scope"],
        unknown_event_count=1,
    )

    c_text = """int ptr_call_and_store(int *param_1,int param_2,int param_3,int param_4)
{
  int value;
  if (param_1 == (int *)0x0) {
    return -700;
  }
  if (param_4 == 0) {
    value = ptr_call_chain(param_2);
    value = value + param_3;
  }
  else {
    value = ptr_apply_callback(param_2,param_3);
  }
  *param_1 = value;
  return *param_1 - param_2;
}
"""

    def _resolve_call(function_name, args, active_functions, current_function=None):
        if function_name == "ptr_call_chain":
            return [
                ExpandedValue(
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op("INT_MULT", args[0], Expression.constant(2, 4)),
                        Expression.constant(11, 4),
                    ),
                    [],
                )
            ]
        if function_name == "ptr_apply_callback":
            return [
                ExpandedValue(
                    Expression.binary_op("INT_XOR", args[0], args[1]),
                    [],
                )
            ]
        raise AssertionError(f"unexpected callee: {function_name}")

    with patch.object(analyzer, "_get_decompiled_c_text", return_value=c_text):
        with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
            recovered = analyzer._recover_call_wrapper_returns_from_decompiler(
                Mock(),
                analysis,
                Mock(),
                set(),
            )

    assert recovered is not None
    assert len(recovered) == 3
    assert recovered[0].value.to_string() == "(-700)"
    assert recovered[1].value.to_string() == "((((param_2 * 2) + 11) + param_3) - param_2)"
    assert recovered[2].value.to_string() == "((param_2 ^ param_3) - param_2)"


def test_return_analyzer_recovers_straightline_call_chain_wrapper_from_decompiler_text():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="ptr_call_chain",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "size": 4, "data_type": "undefined4"}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("void"), conditions=[], branch_index=0)],
        return_type="void",
        unknown_event_reasons=["call_out_of_scope"],
        unknown_event_count=1,
    )

    c_text = """void ptr_call_chain(undefined4 param_1)
{
  undefined8 uVar1;
  uVar1 = ptr_call_leaf(param_1);
  ptr_scale_then_bias(uVar1,2,0xfffffffffffffffd);
  return;
}
"""

    def _resolve_call(function_name, args, active_functions, current_function=None):
        if function_name == "ptr_call_leaf":
            return [
                ExpandedValue(
                    Expression.binary_op("INT_ADD", args[0], Expression.constant(7, 4)),
                    [],
                )
            ]
        if function_name == "ptr_scale_then_bias":
            return [
                ExpandedValue(
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op("INT_MULT", args[0], args[1]),
                        args[2],
                    ),
                    [],
                )
            ]
        raise AssertionError(f"unexpected callee: {function_name}")

    with patch.object(analyzer, "_get_decompiled_c_text", return_value=c_text):
        with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
            recovered = analyzer._recover_call_wrapper_returns_from_decompiler(
                Mock(),
                analysis,
                Mock(),
                set(),
            )

    assert recovered is not None
    assert [ret.value.to_string() for ret in recovered] == ["(((param_1 + 7) * 2) + 18446744073709551613)"]


def test_return_analyzer_resolves_decompiler_return_call_chain_wrapper():
    functions = [
        _FakeFunction("ptr_call_chain", 0x403000),
        _FakeFunction("ptr_call_leaf", 0x401000),
        _FakeFunction("ptr_scale_then_bias", 0x402000),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)

    chain_analysis = FunctionReturnAnalysis(
        function_name="ptr_call_chain",
        entry_point="0x403000",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int", "index": 0}],
        returns=[
            ReturnInfo(
                address="0x403010",
                value=Expression.unknown("call_out_of_scope:ptr_scale_then_bias"),
                conditions=[],
                branch_index=0,
            )
        ],
        return_type="int",
        unknown_event_reasons=["call_out_of_scope"],
        unknown_event_count=1,
    )
    leaf_analysis = FunctionReturnAnalysis(
        function_name="ptr_call_leaf",
        entry_point="0x401000",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int", "index": 0}],
        returns=[
            ReturnInfo(
                address="0x401010",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("param_1", 0, size=4),
                    Expression.constant(7, 4),
                ),
                conditions=[],
                branch_index=0,
            )
        ],
        return_type="int",
    )
    scale_analysis = FunctionReturnAnalysis(
        function_name="ptr_scale_then_bias",
        entry_point="0x402000",
        parameters=[
            {"name": "param_1", "size": 4, "data_type": "int", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
            {"name": "param_3", "size": 4, "data_type": "int", "index": 2},
        ],
        returns=[
            ReturnInfo(
                address="0x402010",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op(
                        "INT_MULT",
                        Expression.parameter("param_1", 0, size=4),
                        Expression.parameter("param_2", 1, size=4),
                    ),
                    Expression.parameter("param_3", 2, size=4),
                ),
                conditions=[],
                branch_index=0,
            )
        ],
        return_type="int",
    )

    chain_text = """int ptr_call_chain(int param_1)
{
  int local_c;
  local_c = ptr_call_leaf(param_1);
  return ptr_scale_then_bias(local_c,2,-3);
}
"""

    class _FakeDecompileResult:
        def __init__(self, name):
            self.name = name

    def _analysis_side_effect(function_name, _active_functions):
        return {
            "ptr_call_chain": chain_analysis,
            "ptr_call_leaf": leaf_analysis,
            "ptr_scale_then_bias": scale_analysis,
        }.get(function_name)

    with patch.object(analyzer, "_get_or_analyze_call_target", side_effect=_analysis_side_effect):
        with patch.object(
            analyzer,
            "_decompile_function",
            side_effect=lambda function, timeout=60: _FakeDecompileResult(function.getName()),
        ):
            with patch.object(
                analyzer,
                "_get_decompiled_c_text",
                side_effect=lambda results: {
                    "ptr_call_chain": chain_text,
                }[results.name],
            ):
                recovered = analyzer._resolve_call_expansions_from_decompiler(
                    "ptr_call_chain",
                    [Expression.parameter("arg", 0, size=4)],
                    active_functions=set(),
                    analysis=chain_analysis,
                )

    assert recovered is not None
    assert [ret.value.to_string() for ret in recovered] == ["(((arg + 7) * 2) + (-3))"]


def test_return_analyzer_recovers_branching_call_wrapper_from_decompiler_text():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="ptr_select_path",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "size": 4, "data_type": "undefined4"},
            {"name": "param_2", "size": 4, "data_type": "undefined4"},
            {"name": "param_3", "size": 4, "data_type": "int", "is_signed": True},
        ],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("void"), conditions=[], branch_index=0)],
        return_type="void",
    )

    c_text = """void ptr_select_path(undefined4 param_1,undefined4 param_2,int param_3)
{
  if (param_3 == 0) {
    ptr_scale_then_bias(param_2,3,1);
  }
  else {
    ptr_add_bias(param_1,10);
  }
  return;
}
"""

    def _resolve_call(function_name, args, active_functions, current_function=None):
        if function_name == "ptr_scale_then_bias":
            return [
                ExpandedValue(
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op("INT_MULT", args[0], args[1]),
                        args[2],
                    ),
                    [],
                )
            ]
        if function_name == "ptr_add_bias":
            return [
                ExpandedValue(
                    Expression.binary_op("INT_ADD", args[0], args[1]),
                    [],
                )
            ]
        raise AssertionError(f"unexpected callee: {function_name}")

    with patch.object(analyzer, "_get_decompiled_c_text", return_value=c_text):
        with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
            recovered = analyzer._recover_call_wrapper_returns_from_decompiler(
                Mock(),
                analysis,
                Mock(),
                set(),
            )

    assert recovered is not None
    assert len(recovered) == 2
    recovered_by_condition = {
        ret.conditions[0].to_string() if ret.conditions else "(unconditional)": ret.value.to_string()
        for ret in recovered
    }
    assert recovered_by_condition["(param_3 == 0)"] == "((param_2 * 3) + 1)"
    assert recovered_by_condition.get("(param_3 != 0)") == "(param_1 + 10)" or recovered_by_condition.get(
        "(not (param_3 == 0))"
    ) == "(param_1 + 10)"


def test_return_analyzer_recovers_else_if_call_wrapper_from_decompiler_text():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="fc_branch_chain",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_3", "size": 4, "data_type": "int", "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.unknown("void"),
                conditions=[
                    _cond_eq(
                        Expression.binary_op("INT_LESS", _param_expr("param_2", 1, 4), _param_expr("param_1", 0, 4)),
                        Expression.constant(0, 1),
                    )
                ],
                branch_index=0,
            )
        ],
        return_type="void",
    )

    c_text = """void fc_branch_chain(int param_1,int param_2,int param_3)
{
  int local_4;
  if (param_2 < param_1) {
    local_4 = fc_wrap_add_then_bias(param_1,param_2,1);
  }
  else if (param_3 < 0) {
    local_4 = fc_wrap_scaled_delta(param_2,param_1);
  }
  else {
    local_4 = fc_bias(param_3,0xfffffffd);
  }
  if (local_4 < 0x15) {
    fc_sub(local_4,7);
  }
  else {
    fc_scale(local_4,2);
  }
  return;
}
"""

    def _resolve_call(function_name, args, active_functions, current_function=None):
        if function_name == "fc_wrap_add_then_bias":
            return [ExpandedValue(Expression.binary_op("INT_ADD", Expression.binary_op("INT_ADD", args[0], args[1]), args[2]), [])]
        if function_name == "fc_wrap_scaled_delta":
            return [ExpandedValue(Expression.binary_op("INT_MULT", Expression.binary_op("INT_SUB", args[0], args[1]), Expression.constant(3, 4)), [])]
        if function_name == "fc_bias":
            return [ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])]
        if function_name == "fc_sub":
            return [ExpandedValue(Expression.binary_op("INT_SUB", args[0], args[1]), [])]
        if function_name == "fc_scale":
            return [ExpandedValue(Expression.binary_op("INT_MULT", args[0], args[1]), [])]
        raise AssertionError(f"unexpected callee: {function_name}")

    with patch.object(analyzer, "_get_decompiled_c_text", return_value=c_text):
        with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
            recovered = analyzer._recover_call_wrapper_returns_from_decompiler(
                Mock(),
                analysis,
                Mock(),
                set(),
            )

    assert recovered is not None
    values = {ret.value.to_string() for ret in recovered}
    assert any("(param_1 + param_2)" in value and "- 7" in value for value in values)
    assert any("(param_2 - param_1)" in value and "* 3" in value for value in values)
    assert any("param_3" in value and ("4294967293" in value or "(-3)" in value) for value in values)


def test_return_analyzer_uses_signed_compare_for_arithmetic_expr_built_from_signed_params():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    parameters = [
        {"name": "param_1", "size": 4, "data_type": "int", "is_signed": True},
        {"name": "param_2", "size": 4, "data_type": "int", "is_signed": True},
    ]
    expanded_local = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", _param_expr("param_1", 0, 4), _param_expr("param_2", 1, 4)),
        Expression.constant(1, 4),
    )

    compare_expr = analyzer._parse_wrapper_condition_expr(
        "21 <= local_24",
        parameters,
        {"local_24": expanded_local},
    )

    assert compare_expr is not None
    assert compare_expr.operator == "INT_SLESSEQUAL"


def test_return_analyzer_recovers_nested_dispatch_wrapper_from_decompiler_text():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="ptr_nested_dispatch",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_2", "size": 4, "data_type": "int", "is_signed": True},
            {"name": "param_3", "size": 4, "data_type": "int", "is_signed": True},
        ],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("void"), conditions=[], branch_index=0)],
        return_type="void",
        unknown_event_reasons=["call_out_of_scope"],
        unknown_event_count=1,
    )

    c_text = """void ptr_nested_dispatch(int param_1,int param_2,int param_3)
{
  int iVar1;
  iVar1 = ptr_select_path(param_1,param_2,param_2 < param_1);
  if (param_3 < iVar1) {
    ptr_add_bias(iVar1 - param_3,5);
  }
  else {
    ptr_scale_then_bias(param_3 - iVar1,2,0xffffffffffffffff);
  }
  return;
}
"""

    def _resolve_call(function_name, args, active_functions, current_function=None):
        if function_name == "ptr_select_path":
            return [
                ExpandedValue(
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op("INT_MULT", args[1], Expression.constant(3, 4)),
                        Expression.constant(1, 4),
                    ),
                    [Condition(Expression.binary_op("INT_EQUAL", args[2], Expression.constant(0, 1)))],
                ),
                ExpandedValue(
                    Expression.binary_op("INT_ADD", args[0], Expression.constant(10, 4)),
                    [Condition(Expression.binary_op("INT_NOTEQUAL", args[2], Expression.constant(0, 1)))],
                ),
            ]
        if function_name == "ptr_add_bias":
            return [ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])]
        if function_name == "ptr_scale_then_bias":
            return [
                ExpandedValue(
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op("INT_MULT", args[0], args[1]),
                        args[2],
                    ),
                    [],
                )
            ]
        raise AssertionError(f"unexpected callee: {function_name}")

    with patch.object(analyzer, "_get_decompiled_c_text", return_value=c_text):
        with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
            recovered = analyzer._recover_call_wrapper_returns_from_decompiler(
                Mock(),
                analysis,
                Mock(),
                set(),
            )

    assert recovered is not None
    assert len(recovered) == 4
    recovered_values = sorted(ret.value.to_string() for ret in recovered)
    assert "(((param_3 - ((param_2 * 3) + 1)) * 2) + 18446744073709551615)" in recovered_values
    assert "(((param_3 - (param_1 + 10)) * 2) + 18446744073709551615)" in recovered_values
    assert "((((param_2 * 3) + 1) - param_3) + 5)" in recovered_values
    assert "(((param_1 + 10) - param_3) + 5)" in recovered_values
    condition_strings = [" && ".join(cond.to_string() for cond in ret.conditions) for ret in recovered]
    assert any("(param_2 < param_1) == 0" in conds and "(param_3 < ((param_2 * 3) + 1))" in conds for conds in condition_strings)
    assert any("(param_2 < param_1) != 0" in conds and "(param_3 < (param_1 + 10))" in conds for conds in condition_strings)


def test_return_analyzer_falls_back_to_decompiler_for_higher_order_call_summary():
    functions = [
        _FakeFunction("ptr_apply_callback", 0x402000),
        _FakeFunction("ptr_op_add", 0x401100),
        _FakeFunction("ptr_op_xor", 0x401200),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)

    ptr_apply_analysis = FunctionReturnAnalysis(
        function_name="ptr_apply_callback",
        entry_point="0x402000",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "code *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
            {"name": "param_3", "size": 4, "data_type": "int", "index": 2},
        ],
        returns=[
            ReturnInfo(
                address="0x402010",
                value=Expression.unknown("call_out_of_scope:UNKNOWN_FUNC"),
                conditions=[_cond_ne(Expression.parameter("param_1", 0, size=8), Expression.constant(0, 8))],
                branch_index=0,
            ),
            ReturnInfo(
                address="0x402020",
                value=Expression.constant(0xFFFFFDA8, 4),
                conditions=[_cond_eq(Expression.parameter("param_1", 0, size=8), Expression.constant(0, 8))],
                branch_index=1,
            ),
        ],
        return_type="int",
        unknown_event_reasons=["call_out_of_scope", "callind_out_of_scope"],
        unknown_event_count=2,
    )
    add_analysis = FunctionReturnAnalysis(
        function_name="ptr_op_add",
        entry_point="0x401100",
        parameters=[
            {"name": "a", "size": 4, "index": 0},
            {"name": "b", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(
                address="0x401110",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("a", 0, size=4),
                    Expression.parameter("b", 1, size=4),
                ),
                conditions=[],
                branch_index=0,
            )
        ],
        return_type="int",
    )
    xor_analysis = FunctionReturnAnalysis(
        function_name="ptr_op_xor",
        entry_point="0x401200",
        parameters=[
            {"name": "a", "size": 4, "index": 0},
            {"name": "b", "size": 4, "index": 1},
        ],
        returns=[
            ReturnInfo(
                address="0x401210",
                value=Expression.binary_op(
                    "INT_XOR",
                    Expression.parameter("a", 0, size=4),
                    Expression.parameter("b", 1, size=4),
                ),
                conditions=[],
                branch_index=0,
            )
        ],
        return_type="int",
    )

    c_text = """undefined4 ptr_apply_callback(code *param_1,undefined4 param_2,undefined4 param_3)
{
  undefined4 local_14;
  if (param_1 == (code *)0x0) {
    local_14 = 0xfffffda8;
  }
  else {
    local_14 = (*param_1)(param_2,param_3);
  }
  return local_14;
}
"""

    def _analysis_side_effect(function_name, _active_functions):
        return {
            "ptr_apply_callback": ptr_apply_analysis,
            "ptr_op_add": add_analysis,
            "ptr_op_xor": xor_analysis,
        }.get(function_name)

    with patch.object(analyzer, "_get_or_analyze_call_target", side_effect=_analysis_side_effect):
        with patch.object(analyzer, "_decompile_function", return_value=object()):
            with patch.object(analyzer, "_get_decompiled_c_text", return_value=c_text):
                expanded = analyzer._resolve_call_expansions(
                    "ptr_apply_callback",
                    [
                        Expression.constant(0x401100, 8),
                        _param_expr("lhs", 0, size=4),
                        _param_expr("rhs", 1, size=4),
                    ],
                    active_functions=set(),
                )

    assert expanded is not None
    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "(lhs + rhs)"
    assert expanded[0].conditions == []


def test_return_analyzer_decompiler_fallback_handles_early_return_higher_order_wrapper():
    functions = [
        _FakeFunction("ptr_apply_callback", 0x402000),
        _FakeFunction("ptr_op_add", 0x401100),
        _FakeFunction("ptr_op_xor", 0x401200),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)

    ptr_apply_analysis = FunctionReturnAnalysis(
        function_name="ptr_apply_callback",
        entry_point="0x402000",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "code *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "undefined4", "index": 1},
            {"name": "param_3", "size": 4, "data_type": "undefined4", "index": 2},
        ],
        returns=[
            ReturnInfo(
                address="0x402010",
                value=Expression.unknown("call_out_of_scope:UNKNOWN_FUNC"),
                conditions=[_cond_ne(Expression.parameter("param_1", 0, size=8), Expression.constant(0, 8))],
                branch_index=0,
            ),
            ReturnInfo(
                address="0x402020",
                value=Expression.constant(0xFFFFFDA8, 8),
                conditions=[_cond_eq(Expression.parameter("param_1", 0, size=8), Expression.constant(0, 8))],
                branch_index=1,
            ),
        ],
        return_type="undefined8",
        unknown_event_reasons=["call_out_of_scope"],
        unknown_event_count=1,
    )

    c_text = """undefined8 ptr_apply_callback(code *param_1,undefined4 param_2,undefined4 param_3)
{
  undefined8 uVar1;
  if (param_1 != (code *)0x0) {
    uVar1 = (*param_1)(param_2,param_3);
    return uVar1;
  }
  return 0xfffffda8;
}
"""

    selector = Expression.parameter("param_1", 0, size=4)
    phi_target = Expression.phi(
        [
            (
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression.binary_op("INT_AND", selector, Expression.constant(1, 4)),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
                Expression.binary_op("INT_ADD", Expression.constant(0, 8), Expression.constant(0x401100, 8)),
            ),
            (
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.binary_op("INT_AND", selector, Expression.constant(1, 4)),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
                Expression.binary_op("INT_ADD", Expression.constant(0, 8), Expression.constant(0x401200, 8)),
            ),
        ]
    )

    def _resolve_call(function_name, args, active_functions, current_function=None):
        if function_name == "ptr_op_add":
            return [ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])]
        if function_name == "ptr_op_xor":
            return [ExpandedValue(Expression.binary_op("INT_XOR", args[0], args[1]), [])]
        raise AssertionError(f"unexpected callee: {function_name}")

    with patch.object(analyzer, "_decompile_function", return_value=object()):
        with patch.object(analyzer, "_get_decompiled_c_text", return_value=c_text):
            with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
                recovered = analyzer._resolve_call_expansions_from_decompiler(
                    "ptr_apply_callback",
                    [
                        phi_target,
                        Expression.parameter("param_2", 1, size=4),
                        Expression.parameter("param_3", 2, size=4),
                    ],
                    set(),
                    analysis=ptr_apply_analysis,
                )

    assert recovered is not None
    assert sorted(ev.value.to_string() for ev in recovered) == [
        "(param_2 + param_3)",
        "(param_2 ^ param_3)",
        "4294966696",
    ]
    condition_strings = [" && ".join(cond.to_string() for cond in ev.conditions) for ev in recovered]
    assert any("((param_1 & 1) == 0)" in conds for conds in condition_strings)
    assert any("((param_1 & 1) != 0)" in conds for conds in condition_strings)


def test_return_analyzer_structured_wrapper_ignores_unreachable_tail_after_constant_true_branch():
    functions = [
        _FakeFunction("ptr_op_add", 0x401100),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)
    c_text = """undefined8 ptr_apply_callback(code *param_1,undefined4 param_2,undefined4 param_3)
{
  undefined8 uVar1;
  if (param_1 != (code *)0x0) {
    uVar1 = (*param_1)(param_2,param_3);
    return uVar1;
  }
  return 0xfffffda8;
}
"""
    parameters = [
        {"name": "param_1", "size": 8, "data_type": "code *", "index": 0},
        {"name": "param_2", "size": 4, "data_type": "undefined4", "index": 1},
        {"name": "param_3", "size": 4, "data_type": "undefined4", "index": 2},
    ]

    def _resolve_call(function_name, args, active_functions, current_function=None):
        if function_name == "ptr_op_add":
            return [ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])]
        raise AssertionError(f"unexpected callee: {function_name}")

    with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
        recovered = analyzer._recover_structured_call_wrapper_from_c_text(
            c_text,
            parameters,
            "0x1000",
            Mock(),
            set(),
            initial_bindings={
                "param_1": Expression.variable("ptr_op_add", size=8),
                "param_2": Expression.parameter("param_2", 1, size=4),
                "param_3": Expression.parameter("param_3", 2, size=4),
            },
        )

    assert recovered is not None
    assert len(recovered) == 1
    assert recovered[0].value.to_string() == "(param_2 + param_3)"
    assert recovered[0].conditions == []


def test_return_analyzer_structured_wrapper_ignores_decompiler_warning_comments_before_indirect_call():
    functions = [
        _FakeFunction("ptr_op_add", 0x401100),
        _FakeFunction("ptr_op_xor", 0x401200),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)
    c_text = """void ptr_dispatch_callback(ulong param_1,undefined8 param_2,undefined8 param_3)
{
  code *UNRECOVERED_JUMPTABLE;
  UNRECOVERED_JUMPTABLE = (code *)PTR_ptr_op_add_120012068;
  if ((param_1 & 1) != 0) {
    UNRECOVERED_JUMPTABLE = (code *)PTR_ptr_op_xor_120012070;
  }
                    /* WARNING: Could not recover jumptable at 0x000120000e7c. Too many branches */
                    /* WARNING: Treating indirect jump as call */
  (*UNRECOVERED_JUMPTABLE)(param_2,param_3);
  return;
}
"""
    parameters = [
        {"name": "param_1", "size": 8, "data_type": "ulong", "index": 0},
        {"name": "param_2", "size": 8, "data_type": "undefined8", "index": 1},
        {"name": "param_3", "size": 8, "data_type": "undefined8", "index": 2},
    ]

    def _resolve_call(function_name, args, active_functions, current_function=None):
        if function_name == "ptr_op_add":
            return [ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])]
        if function_name == "ptr_op_xor":
            return [ExpandedValue(Expression.binary_op("INT_XOR", args[0], args[1]), [])]
        raise AssertionError(f"unexpected callee: {function_name}")

    with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
        recovered = analyzer._recover_structured_call_wrapper_from_c_text(
            c_text,
            parameters,
            "0x1000",
            Mock(),
            set(),
        )

    assert recovered is not None
    assert len(recovered) == 2
    recovered_by_condition = {
        tuple(cond.to_string() for cond in ret.conditions): ret.value.to_string()
        for ret in recovered
    }
    assert recovered_by_condition.get(("((param_1 & 1) == 0)",)) == "(param_2 + param_3)" or recovered_by_condition.get(
        ("(not ((param_1 & 1) != 0))",)
    ) == "(param_2 + param_3)"
    assert recovered_by_condition.get(("((param_1 & 1) != 0)",)) == "(param_2 ^ param_3)" or recovered_by_condition.get(
        ("(not ((param_1 & 1) == 0))",)
    ) == "(param_2 ^ param_3)"


def test_return_analyzer_recovers_indirect_dispatch_wrapper_from_pointer_slots():
    functions = [
        _FakeFunction("ptr_op_add", 0x401100),
        _FakeFunction("ptr_op_xor", 0x401200),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="ptr_dispatch_callback",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "size": 8, "data_type": "ulong", "index": 0}],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("void"), conditions=[], branch_index=0)],
        return_type="void",
        unknown_event_reasons=["call_out_of_scope"],
        unknown_event_count=1,
    )

    c_text = """undefined4 ptr_dispatch_callback(ulong param_1,undefined8 param_2,undefined8 param_3)
{
  undefined4 uVar1;
  undefined **ppuVar2;
  ppuVar2 = &PTR_ptr_op_xor_00112070;
  if ((param_1 & 1) == 0) {
    ppuVar2 = &PTR_ptr_op_add_00112078;
  }
  uVar1 = (*(code *)*ppuVar2)(param_2,param_3);
  return uVar1;
}
"""

    def _resolve_call(function_name, args, active_functions, current_function=None):
        if function_name == "ptr_op_add":
            return [ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])]
        if function_name == "ptr_op_xor":
            return [ExpandedValue(Expression.binary_op("INT_XOR", args[0], args[1]), [])]
        raise AssertionError(f"unexpected callee: {function_name}")

    slot_table = {
        0x00112070: 0x401200,
        0x00112078: 0x401100,
    }

    with patch.object(analyzer, "_get_decompiled_c_text", return_value=c_text):
        with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
            with patch.object(analyzer, "_read_memory_value", side_effect=lambda addr, size: slot_table.get(addr)):
                recovered = analyzer._recover_call_wrapper_returns_from_decompiler(
                    Mock(),
                    analysis,
                    Mock(),
                    set(),
                )

    assert recovered is not None
    assert len(recovered) == 2
    recovered_by_condition = {
        ret.conditions[0].to_string() if ret.conditions else "(unconditional)": ret.value.to_string()
        for ret in recovered
    }
    assert recovered_by_condition["((param_1 & 1) == 0)"] == "(param_2 + param_3)"
    assert recovered_by_condition.get("((param_1 & 1) != 0)") == "(param_2 ^ param_3)" or recovered_by_condition.get(
        "(not ((param_1 & 1) == 0))"
    ) == "(param_2 ^ param_3)"


def test_return_analyzer_prunes_impossible_null_branch_for_known_function_pointer_binding():
    functions = [
        _FakeFunction("ptr_dispatch_callback", 0x403000),
        _FakeFunction("ptr_apply_callback", 0x402000),
        _FakeFunction("ptr_op_add", 0x401100),
        _FakeFunction("ptr_op_xor", 0x401200),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)

    dispatch_analysis = FunctionReturnAnalysis(
        function_name="ptr_dispatch_callback",
        entry_point="0x403000",
        parameters=[
            {"name": "param_1", "size": 4, "index": 0},
            {"name": "param_2", "size": 4, "index": 1},
            {"name": "param_3", "size": 4, "index": 2},
        ],
        returns=[ReturnInfo(address="0x403000", value=Expression.unknown("void"), conditions=[], branch_index=0)],
        return_type="void",
        unknown_event_reasons=["call_out_of_scope"],
        unknown_event_count=1,
    )
    apply_analysis = FunctionReturnAnalysis(
        function_name="ptr_apply_callback",
        entry_point="0x402000",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "code *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "undefined4", "index": 1},
            {"name": "param_3", "size": 4, "data_type": "undefined4", "index": 2},
        ],
        returns=[
            ReturnInfo(
                address="0x402010",
                value=Expression.unknown("call_out_of_scope:UNKNOWN_FUNC"),
                conditions=[],
                branch_index=0,
            )
        ],
        return_type="undefined8",
        unknown_event_reasons=["call_out_of_scope", "callind_out_of_scope"],
        unknown_event_count=1,
    )

    dispatch_text = """undefined8 ptr_dispatch_callback(uint param_1,undefined4 param_2,undefined4 param_3)
{
  undefined *local_28;
  undefined8 uVar1;
  local_28 = PTR_ptr_op_xor_120013098;
  if ((param_1 & 1) == 0) {
    local_28 = PTR_ptr_op_add_120013090;
  }
  uVar1 = ptr_apply_callback((code *)local_28,param_2,param_3);
  return uVar1;
}
"""
    apply_text = """undefined8 ptr_apply_callback(code *param_1,undefined4 param_2,undefined4 param_3)
{
  undefined8 uVar1;
  if (param_1 == (code *)0x0) {
    uVar1 = 0xfffffffffffffda8;
  }
  else {
    uVar1 = (*param_1)(param_2,param_3);
  }
  return uVar1;
}
"""

    class _FakeDecompileResult:
        def __init__(self, name):
            self.name = name

    def _analysis_side_effect(function_name, _active_functions):
        return {
            "ptr_dispatch_callback": dispatch_analysis,
            "ptr_apply_callback": apply_analysis,
            "ptr_op_add": FunctionReturnAnalysis(
                function_name="ptr_op_add",
                entry_point="0x401100",
                parameters=[{"name": "a", "size": 4, "index": 0}, {"name": "b", "size": 4, "index": 1}],
                returns=[
                    ReturnInfo(
                        address="0x401110",
                        value=Expression.binary_op(
                            "INT_ADD",
                            Expression.parameter("a", 0, size=4),
                            Expression.parameter("b", 1, size=4),
                        ),
                        conditions=[],
                        branch_index=0,
                    )
                ],
                return_type="int",
            ),
            "ptr_op_xor": FunctionReturnAnalysis(
                function_name="ptr_op_xor",
                entry_point="0x401200",
                parameters=[{"name": "a", "size": 4, "index": 0}, {"name": "b", "size": 4, "index": 1}],
                returns=[
                    ReturnInfo(
                        address="0x401210",
                        value=Expression.binary_op(
                            "INT_XOR",
                            Expression.parameter("a", 0, size=4),
                            Expression.parameter("b", 1, size=4),
                        ),
                        conditions=[],
                        branch_index=0,
                    )
                ],
                return_type="int",
            ),
        }.get(function_name)

    with patch.object(analyzer, "_get_or_analyze_call_target", side_effect=_analysis_side_effect):
        with patch.object(
            analyzer,
            "_decompile_function",
            side_effect=lambda function, timeout=60: _FakeDecompileResult(function.getName()),
        ):
            with patch.object(
                analyzer,
                "_get_decompiled_c_text",
                side_effect=lambda results: {
                    "ptr_dispatch_callback": dispatch_text,
                    "ptr_apply_callback": apply_text,
                }[results.name],
            ):
                recovered = analyzer._resolve_call_expansions_from_decompiler(
                    "ptr_dispatch_callback",
                    [
                        Expression.parameter("param_1", 0, size=4),
                        Expression.parameter("param_2", 1, size=4),
                        Expression.parameter("param_3", 2, size=4),
                    ],
                    active_functions=set(),
                    analysis=dispatch_analysis,
                )

    assert recovered is not None
    assert len(recovered) == 2
    recovered_by_condition = {
        tuple(cond.to_string() for cond in ret.conditions): ret.value.to_string()
        for ret in recovered
    }
    assert recovered_by_condition[( "((param_1 & 1) == 0)",)] == "(param_2 + param_3)"
    assert recovered_by_condition.get(("((param_1 & 1) != 0)",)) == "(param_2 ^ param_3)" or recovered_by_condition.get(
        ("(not ((param_1 & 1) == 0))",)
    ) == "(param_2 ^ param_3)"
    assert all("600" not in value for value in recovered_by_condition.values())


def test_return_analyzer_augments_wrapper_call_with_implicit_passthrough_register_args():
    functions = [
        _FakeFunction("ptr_apply_callback", 0x402000),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)

    current_parameters = [
        {
            "name": "param_1",
            "index": 0,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a0",
                "base_register_name": "a0",
                "bit_offset_in_base": 0,
                "size_bits": 64,
            },
        },
        {
            "name": "param_2",
            "index": 1,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a1",
                "base_register_name": "a1",
                "bit_offset_in_base": 0,
                "size_bits": 64,
            },
        },
        {
            "name": "param_3",
            "index": 2,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a2",
                "base_register_name": "a2",
                "bit_offset_in_base": 0,
                "size_bits": 64,
            },
        },
    ]
    callee_analysis = FunctionReturnAnalysis(
        function_name="ptr_apply_callback",
        entry_point="0x402000",
        parameters=[
            {
                "name": "param_1",
                "index": 0,
                "size": 8,
                "storage": {
                    "is_register": True,
                    "register_name": "a0",
                    "base_register_name": "a0",
                    "bit_offset_in_base": 0,
                    "size_bits": 64,
                },
            },
            {
                "name": "param_2",
                "index": 1,
                "size": 8,
                "storage": {
                    "is_register": True,
                    "register_name": "a1",
                    "base_register_name": "a1",
                    "bit_offset_in_base": 0,
                    "size_bits": 64,
                },
            },
            {
                "name": "param_3",
                "index": 2,
                "size": 8,
                "storage": {
                    "is_register": True,
                    "register_name": "a2",
                    "base_register_name": "a2",
                    "bit_offset_in_base": 0,
                    "size_bits": 64,
                },
            },
        ],
        returns=[],
        return_type="undefined8",
    )

    captured = {}

    def _resolve_call(function_name, args, active_functions, current_function=None):
        captured["function_name"] = function_name
        captured["args"] = [arg.to_string() for arg in args]
        return [ExpandedValue(Expression.constant(0, 8), [])]

    with patch.object(analyzer, "_get_or_analyze_call_target", return_value=callee_analysis):
        with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
            expanded = analyzer._resolve_wrapper_call_target(
                "ptr_apply_callback",
                [Expression.variable("PTR_ptr_op_add_120012068", size=8)],
                [],
                current_parameters,
                {},
                set(),
                None,
            )

    assert expanded is not None
    assert captured["function_name"] == "ptr_apply_callback"
    assert captured["args"] == [
        "PTR_ptr_op_add_120012068",
        "param_2",
        "param_3",
    ]
    assert expanded[0].value.to_string() == "0"


def test_return_analyzer_restores_parent_analysis_context_after_nested_call():
    parent = _FakeFunction("parent", 0x401000)
    child = _FakeFunction("child", 0x402000)
    analyzer = ReturnAnalyzer(program=_FakeProgram([parent, child]), debug=False)

    class _FakeHighFunction:
        def __init__(self, name: str):
            self.name = name

    class _FakeResults:
        def __init__(self, function_name: str):
            self._high_function = _FakeHighFunction(function_name)

        def decompileCompleted(self):
            return True

        def getHighFunction(self):
            return self._high_function

    class _FakeDecompiler:
        def decompileFunction(self, function, _timeout, _monitor):
            return _FakeResults(function.getName())

    class _FakeUnknownTracker:
        def __init__(self):
            self.events = []

        def get_summary(self):
            return ""

        def filter_phi_related(self):
            return []

    class _FakeTracer:
        def __init__(self, _program, _high_function, debug=False):
            self.debug = debug
            self.unknown_tracker = _FakeUnknownTracker()
            self.phi_handler = None

        def find_return_ops(self):
            return []

    class _FakeConditionTracker:
        def __init__(self, _tracer):
            pass

        def build(self):
            return None

        def refine_branch_conditions(self, **_kwargs):
            return 0

    class _FakePhiHandler:
        def __init__(self, *_args, **_kwargs):
            pass

    observed = {}

    def _collect_parameters(high_function):
        if high_function.name == "parent":
            return [
                {"name": "param_1", "index": 0, "size": 4},
                {"name": "param_2", "index": 1, "size": 4},
                {"name": "param_3", "index": 2, "size": 4},
            ]
        return [
            {"name": "param_1", "index": 0, "size": 4},
            {"name": "param_2", "index": 1, "size": 4},
        ]

    def _build_effect_summary(function, _high_function, _tracer, _condition_tracker, _parameters, active_functions):
        if function.getName() == "parent":
            child_analysis = analyzer.analyze_function(child, active_functions=active_functions)
            assert child_analysis is not None
            observed["after_child_params"] = [param["name"] for param in analyzer._current_parameters]
            observed["after_child_effect_summary"] = analyzer._current_effect_summary
        return Mock(synthetic_expr=None, has_unsupported_call=False)

    with patch("scripts.function_tracer_pcode.analysis.analyzer.PcodeTracer", _FakeTracer), patch(
        "scripts.function_tracer_pcode.analysis.analyzer.ConditionTracker",
        _FakeConditionTracker,
    ), patch(
        "scripts.function_tracer_pcode.analysis.phi_resolver.PhiHandler",
        _FakePhiHandler,
    ), patch.object(
        analyzer,
        "_get_decompiler",
        return_value=_FakeDecompiler(),
    ), patch.object(
        analyzer,
        "_collect_parameters",
        side_effect=_collect_parameters,
    ), patch.object(
        analyzer,
        "_augment_parameters_with_implicit_passthrough",
        side_effect=lambda parameters, *_args, **_kwargs: parameters,
    ), patch.object(
        analyzer,
        "_build_effect_summary",
        side_effect=_build_effect_summary,
    ), patch.object(
        analyzer,
        "_get_return_type",
        return_value="int",
    ), patch.object(
        analyzer,
        "_detect_signedness",
        return_value=None,
    ), patch.object(
        analyzer,
        "_recover_switch_like_returns_from_decompiler",
        return_value=None,
    ), patch.object(
        analyzer,
        "_recover_call_wrapper_returns",
        return_value=None,
    ), patch.object(
        analyzer,
        "_synchronize_parameters_with_referenced_parameter_expressions",
        return_value=None,
    ), patch.object(
        analyzer,
        "_mark_incomplete_control_flow",
        return_value=None,
    ), patch.object(
        analyzer,
        "_dump_return_infos",
        return_value=None,
    ):
        analysis = analyzer.analyze_function(parent)

    assert analysis is not None
    assert [param["name"] for param in analysis.parameters] == ["param_1", "param_2", "param_3"]
    assert observed["after_child_params"] == ["param_1", "param_2", "param_3"]
    assert observed["after_child_effect_summary"] is None


def test_return_analyzer_augments_current_parameters_with_implicit_passthrough_registers():
    functions = [
        _FakeFunction("ptr_apply_callback", 0x402000),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)

    class _FakeCallOp:
        def __init__(self):
            self._target = object()

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            if index == 0:
                return self._target
            return object()

        def getOutput(self):
            return None

    call_op = _FakeCallOp()

    class _FakeTracer:
        def get_all_pcode_ops(self):
            return [call_op]

        def _get_function_name(self, target_varnode):
            if target_varnode is call_op.getInput(0):
                return "ptr_apply_callback"
            return "UNKNOWN_FUNC"

        def trace_varnode(self, *_args, **_kwargs):
            raise AssertionError("direct target resolution should be enough")

        def _get_op_order_key(self, _op):
            return 10

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    current_parameters = [
        {
            "name": "param_1",
            "index": 0,
            "size": 4,
            "storage": {
                "is_register": True,
                "register_name": "a0_lo",
                "base_register_name": "a0",
                "bit_offset_in_base": 32,
                "size_bits": 32,
                "base_register_size_bits": 64,
            },
        }
    ]
    callee_parameters = [
        {
            "name": "param_1",
            "index": 0,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a0",
                "base_register_name": "a0",
                "bit_offset_in_base": 0,
                "size_bits": 64,
                "base_register_size_bits": 64,
            },
        },
        {
            "name": "param_2",
            "index": 1,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a1",
                "base_register_name": "a1",
                "bit_offset_in_base": 0,
                "size_bits": 64,
                "base_register_size_bits": 64,
            },
        },
        {
            "name": "param_3",
            "index": 2,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a2",
                "base_register_name": "a2",
                "bit_offset_in_base": 0,
                "size_bits": 64,
                "base_register_size_bits": 64,
            },
        },
    ]

    with patch.object(analyzer, "_get_freshest_callee_parameters", return_value=callee_parameters):
        augmented = analyzer._augment_parameters_with_implicit_passthrough(
            current_parameters,
            _FakeTracer(),
            set(),
        )

    assert [param["name"] for param in augmented] == ["param_1", "param_2", "param_3"]
    assert augmented[1]["storage"]["base_register_name"] == "a1"
    assert augmented[2]["storage"]["base_register_name"] == "a2"


def test_return_analyzer_does_not_duplicate_fragment_backed_passthrough_parameter():
    functions = [
        _FakeFunction("ptr_apply_callback", 0x402000),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)

    class _FakeCallOp:
        def __init__(self):
            self._target = object()

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 3

        def getInput(self, index):
            if index == 0:
                return self._target
            return object()

        def getOutput(self):
            return None

    call_op = _FakeCallOp()

    class _FakeTracer:
        def get_all_pcode_ops(self):
            return [call_op]

        def _get_function_name(self, target_varnode):
            if target_varnode is call_op.getInput(0):
                return "ptr_apply_callback"
            return "UNKNOWN_FUNC"

        def trace_varnode(self, *_args, **_kwargs):
            raise AssertionError("direct target resolution should be enough")

        def _get_op_order_key(self, _op):
            return 10

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    current_parameters = [
        {
            "name": "param_1",
            "index": 0,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a0",
                "base_register_name": "a0",
                "bit_offset_in_base": 0,
                "size_bits": 64,
                "base_register_size_bits": 64,
            },
        },
        {
            "name": "param_2",
            "index": 1,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a1",
                "base_register_name": "a1",
                "bit_offset_in_base": 0,
                "size_bits": 64,
                "base_register_size_bits": 64,
            },
        },
        {
            "name": "param_3",
            "index": 2,
            "size": 4,
            "storage": {
                "is_register": True,
                "register_name": "a2_lo",
                "base_register_name": "a2",
                "bit_offset_in_base": 32,
                "size_bits": 32,
                "base_register_size_bits": 64,
            },
        },
    ]
    callee_parameters = [
        {
            "name": "param_1",
            "index": 0,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a0",
                "base_register_name": "a0",
                "bit_offset_in_base": 0,
                "size_bits": 64,
                "base_register_size_bits": 64,
            },
        },
        {
            "name": "param_2",
            "index": 1,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a1",
                "base_register_name": "a1",
                "bit_offset_in_base": 0,
                "size_bits": 64,
                "base_register_size_bits": 64,
            },
        },
        {
            "name": "param_3",
            "index": 2,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a2",
                "base_register_name": "a2",
                "bit_offset_in_base": 0,
                "size_bits": 64,
                "base_register_size_bits": 64,
            },
        },
    ]

    with patch.object(analyzer, "_get_freshest_callee_parameters", return_value=callee_parameters):
        augmented = analyzer._augment_parameters_with_implicit_passthrough(
            current_parameters,
            _FakeTracer(),
            set(),
        )

    assert [param["name"] for param in augmented] == ["param_1", "param_2", "param_3"]


def test_return_analyzer_augments_hidden_passthrough_even_when_live_in_check_is_too_conservative():
    functions = [
        _FakeFunction("ptr_apply_callback", 0x402000),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)

    class _FakeOutput:
        def __init__(self, storage):
            self.storage = analyzer._coerce_wrapper_storage_info(storage)

    class _FakeCallOp:
        def __init__(self):
            self._target = object()

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            if index == 0:
                return self._target
            return object()

        def getOutput(self):
            return None

    class _FakeWriteOp:
        def __init__(self, storage):
            self._output = _FakeOutput(storage)

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return 0

        def getInput(self, _index):
            raise IndexError

        def getOutput(self):
            return self._output

    class _FakeLocalMap:
        def getSymbols(self):
            return []

    class _FakeHighFunction:
        def getLocalSymbolMap(self):
            return _FakeLocalMap()

    call_op = _FakeCallOp()
    prior_write = _FakeWriteOp(
        {
            "is_register": True,
            "register_name": "a1",
            "base_register_name": "a1",
            "bit_offset_in_base": 0,
            "size_bits": 64,
            "size": 8,
        }
    )

    class _FakeTracer:
        high_function = _FakeHighFunction()

        def get_all_pcode_ops(self):
            return [prior_write, call_op]

        def _get_function_name(self, target_varnode):
            if target_varnode is call_op.getInput(0):
                return "ptr_apply_callback"
            return "UNKNOWN_FUNC"

        def trace_varnode(self, *_args, **_kwargs):
            raise AssertionError("direct target resolution should be enough")

        def _get_op_order_key(self, op):
            return 1 if op is prior_write else 10

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

    current_parameters = [
        {
            "name": "param_1",
            "index": 0,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a0",
                "base_register_name": "a0",
                "bit_offset_in_base": 0,
                "size_bits": 64,
            },
        }
    ]
    callee_parameters = [
        {
            "name": "param_1",
            "index": 0,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a0",
                "base_register_name": "a0",
                "bit_offset_in_base": 0,
                "size_bits": 64,
            },
        },
        {
            "name": "param_2",
            "index": 1,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a1",
                "base_register_name": "a1",
                "bit_offset_in_base": 0,
                "size_bits": 64,
                "size": 8,
            },
        },
    ]

    with patch.object(analyzer, "_get_freshest_callee_parameters", return_value=callee_parameters):
        augmented = analyzer._augment_parameters_with_implicit_passthrough(
            current_parameters,
            _FakeTracer(),
            set(),
        )

    assert [param["name"] for param in augmented] == ["param_1", "param_2"]


def test_return_analyzer_does_not_synthesize_hidden_param_when_register_has_local_symbol():
    functions = [
        _FakeFunction("ptr_apply_callback", 0x402000),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)

    class _FakeCallOp:
        def __init__(self):
            self._target = object()

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            if index == 0:
                return self._target
            return object()

        def getOutput(self):
            return None

    class _FakeSymbol:
        def __init__(self, storage):
            self._storage = storage

        def isParameter(self):
            return False

        def getStorage(self):
            class _Storage:
                def __init__(self, storage):
                    self._storage = storage

                def getVarnodes(self):
                    class _Addr:
                        def __init__(self, storage):
                            self._storage = storage

                        def getAddressSpace(self):
                            class _Space:
                                def __init__(self, storage):
                                    self._storage = storage

                                def isRegisterSpace(self):
                                    return self._storage.get("is_register", False)

                                def getName(self):
                                    return self._storage.get("space_name", "register")

                            return _Space(self._storage)

                    class _Varnode:
                        def __init__(self, storage):
                            self._storage = storage

                        def getAddress(self):
                            return _Addr(self._storage)

                        def getOffset(self):
                            return self._storage.get("offset", 0)

                        def getSize(self):
                            return self._storage.get("size", 8)

                    return [_Varnode(self._storage)]

            return _Storage(self._storage)

    class _FakeLocalMap:
        def __init__(self, symbols):
            self._symbols = symbols

        def getSymbols(self):
            return list(self._symbols)

    class _FakeHighFunction:
        def __init__(self, symbols):
            self._symbols = symbols

        def getLocalSymbolMap(self):
            return _FakeLocalMap(self._symbols)

    call_op = _FakeCallOp()
    claimed_storage = {
        "is_register": True,
        "space_name": "register",
        "offset": 8,
        "size": 8,
        "size_bits": 64,
        "register_name": "a1",
        "base_register_name": "a1",
        "base_register_size": 8,
        "base_register_size_bits": 64,
        "bit_offset_in_base": 0,
    }

    class _FakeTracer:
        high_function = _FakeHighFunction([_FakeSymbol(claimed_storage)])

        def get_all_pcode_ops(self):
            return [call_op]

        def _get_function_name(self, target_varnode):
            if target_varnode is call_op.getInput(0):
                return "ptr_apply_callback"
            return "UNKNOWN_FUNC"

        def trace_varnode(self, *_args, **_kwargs):
            raise AssertionError("direct target resolution should be enough")

        def _get_op_order_key(self, _op):
            return 10

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    current_parameters = [
        {
            "name": "param_1",
            "index": 0,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a0",
                "base_register_name": "a0",
                "bit_offset_in_base": 0,
                "size_bits": 64,
            },
        }
    ]
    callee_parameters = [
        {
            "name": "param_1",
            "index": 0,
            "size": 8,
            "storage": {
                "is_register": True,
                "register_name": "a0",
                "base_register_name": "a0",
                "bit_offset_in_base": 0,
                "size_bits": 64,
            },
        },
        {
            "name": "param_2",
            "index": 1,
            "size": 8,
            "storage": claimed_storage,
        },
    ]

    with patch.object(analyzer, "_get_freshest_callee_parameters", return_value=callee_parameters):
        with patch.object(analyzer, "_get_storage_info", side_effect=lambda sym: sym._storage):
            augmented = analyzer._augment_parameters_with_implicit_passthrough(
                current_parameters,
                _FakeTracer(),
                set(),
            )

    assert [param["name"] for param in augmented] == ["param_1"]


def test_return_analyzer_promotes_referenced_hidden_parameters_into_formal_signature():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="ptr_dispatch_callback",
        entry_point="0x401000",
        parameters=[
            {
                "name": "param_1",
                "index": 0,
                "size": 8,
                "storage": {
                    "is_register": True,
                    "register_name": "x0",
                    "base_register_name": "x0",
                    "bit_offset_in_base": 0,
                    "size_bits": 64,
                    "base_register_size_bits": 64,
                },
            }
        ],
        returns=[
            ReturnInfo(
                address="0x401020",
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter(
                        "param_2",
                        1,
                        size=4,
                        storage_info=analyzer._coerce_wrapper_storage_info(
                            {
                                "is_register": True,
                                "register_name": "w1",
                                "base_register_name": "x1",
                                "bit_offset_in_base": 32,
                                "size_bits": 32,
                                "base_register_size_bits": 64,
                            }
                        ),
                    ),
                    Expression.parameter(
                        "param_3",
                        2,
                        size=4,
                        storage_info=analyzer._coerce_wrapper_storage_info(
                            {
                                "is_register": True,
                                "register_name": "w2",
                                "base_register_name": "x2",
                                "bit_offset_in_base": 32,
                                "size_bits": 32,
                                "base_register_size_bits": 64,
                            }
                        ),
                    ),
                ),
                conditions=[
                    Condition(
                        Expression.binary_op(
                            "INT_NOTEQUAL",
                            Expression.parameter(
                                "param_1",
                                0,
                                size=8,
                                storage_info=analyzer._coerce_wrapper_storage_info(
                                    {
                                        "is_register": True,
                                        "register_name": "x0",
                                        "base_register_name": "x0",
                                        "bit_offset_in_base": 0,
                                        "size_bits": 64,
                                        "base_register_size_bits": 64,
                                    }
                                ),
                            ),
                            Expression.constant(0, 8),
                        ),
                        False,
                    )
                ],
                branch_index=0,
            )
        ],
        return_type="undefined8",
    )

    analyzer._synchronize_parameters_with_referenced_parameter_expressions(analysis)

    assert [param["name"] for param in analysis.parameters] == ["param_1", "param_2", "param_3"]
    assert analysis.parameters[1]["storage"]["base_register_name"] == "x1"
    assert analysis.parameters[2]["storage"]["base_register_name"] == "x2"
    assert analysis.parameters[1]["implicit_passthrough"] is True
    assert analysis.parameters[2]["implicit_passthrough"] is True


def test_return_analyzer_augments_hidden_passthrough_by_name_when_storage_is_missing():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    augmented = analyzer._augment_wrapper_call_args_with_implicit_passthrough(
        "ptr_apply_callback",
        [Expression.variable("pcVar1", size=8)],
        [
            {"name": "param_1", "index": 0, "size": 8},
            {"name": "param_2", "index": 1, "size": 4},
            {"name": "param_3", "index": 2, "size": 4},
        ],
        set(),
    )

    assert [arg.to_string() for arg in augmented] == ["pcVar1"]

    callee_analysis = FunctionReturnAnalysis(
        function_name="ptr_apply_callback",
        entry_point="0x402000",
        parameters=[
            {"name": "param_1", "index": 0, "size": 8},
            {"name": "param_2", "index": 1, "size": 4},
            {"name": "param_3", "index": 2, "size": 4},
        ],
        returns=[],
        return_type="undefined8",
    )

    with patch.object(analyzer, "_get_or_analyze_call_target", return_value=callee_analysis):
        augmented = analyzer._augment_wrapper_call_args_with_implicit_passthrough(
            "ptr_apply_callback",
            [Expression.variable("pcVar1", size=8)],
            [
                {"name": "param_1", "index": 0, "size": 8},
                {"name": "param_2", "index": 1, "size": 4},
                {"name": "param_3", "index": 2, "size": 4},
            ],
            set(),
        )

    assert [arg.to_string() for arg in augmented] == ["pcVar1", "param_2", "param_3"]


def test_return_analyzer_matches_fragment_parameter_for_wide_passthrough_storage():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    callee_analysis = FunctionReturnAnalysis(
        function_name="ptr_apply_callback",
        entry_point="0x402000",
        parameters=[
            {
                "name": "param_1",
                "index": 0,
                "size": 8,
                "storage": {
                    "is_register": True,
                    "register_name": "a0",
                    "base_register_name": "a0",
                    "bit_offset_in_base": 0,
                    "size_bits": 64,
                    "base_register_size_bits": 64,
                },
            },
            {
                "name": "param_2",
                "index": 1,
                "size": 8,
                "storage": {
                    "is_register": True,
                    "register_name": "a1",
                    "base_register_name": "a1",
                    "bit_offset_in_base": 0,
                    "size_bits": 64,
                    "base_register_size_bits": 64,
                },
            },
            {
                "name": "param_3",
                "index": 2,
                "size": 8,
                "storage": {
                    "is_register": True,
                    "register_name": "a2",
                    "base_register_name": "a2",
                    "bit_offset_in_base": 0,
                    "size_bits": 64,
                    "base_register_size_bits": 64,
                },
            },
        ],
        returns=[],
        return_type="undefined8",
    )

    with patch.object(analyzer, "_get_or_analyze_call_target", return_value=callee_analysis):
        augmented = analyzer._augment_wrapper_call_args_with_implicit_passthrough(
            "ptr_apply_callback",
            [Expression.variable("fp", size=8), Expression.parameter("param_2", 1, size=8)],
            [
                {
                    "name": "param_1",
                    "index": 0,
                    "size": 8,
                    "storage": {
                        "is_register": True,
                        "register_name": "a0",
                        "base_register_name": "a0",
                        "bit_offset_in_base": 0,
                        "size_bits": 64,
                        "base_register_size_bits": 64,
                    },
                },
                {
                    "name": "param_2",
                    "index": 1,
                    "size": 8,
                    "storage": {
                        "is_register": True,
                        "register_name": "a1",
                        "base_register_name": "a1",
                        "bit_offset_in_base": 0,
                        "size_bits": 64,
                        "base_register_size_bits": 64,
                    },
                },
                {
                    "name": "param_3",
                    "index": 2,
                    "size": 4,
                    "storage": {
                        "is_register": True,
                        "register_name": "a2_lo",
                        "base_register_name": "a2",
                        "bit_offset_in_base": 32,
                        "size_bits": 32,
                        "base_register_size_bits": 64,
                    },
                },
            ],
            set(),
        )

    assert [arg.to_string() for arg in augmented] == ["fp", "param_2", "param_3"]


def test_return_analyzer_outer_wrapper_recovers_void_call_with_name_based_passthrough():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="ptr_dispatch_callback",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "size": 8, "data_type": "ulong"},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "undefined4"},
            {"name": "param_3", "index": 2, "size": 4, "data_type": "undefined4"},
        ],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("call_out_of_scope:ptr_apply_callback"), conditions=[], branch_index=0)],
        return_type="void",
        unknown_event_reasons=["call_out_of_scope"],
        unknown_event_count=1,
    )
    ptr_apply_analysis = FunctionReturnAnalysis(
        function_name="ptr_apply_callback",
        entry_point="0x402000",
        parameters=[
            {"name": "param_1", "index": 0, "size": 8, "data_type": "code *"},
            {"name": "param_2", "index": 1, "size": 4, "data_type": "undefined4"},
            {"name": "param_3", "index": 2, "size": 4, "data_type": "undefined4"},
        ],
        returns=[
            ReturnInfo(
                address="0x1",
                value=Expression.unknown("call_out_of_scope:UNKNOWN_FUNC"),
                conditions=[_cond_ne(Expression.parameter("param_1", 0, size=8), Expression.constant(0, 8))],
                branch_index=0,
            ),
            ReturnInfo(
                address="0x2",
                value=Expression.constant(0xFFFFFDA8, 8),
                conditions=[_cond_eq(Expression.parameter("param_1", 0, size=8), Expression.constant(0, 8))],
                branch_index=1,
            ),
        ],
        return_type="undefined8",
        unknown_event_reasons=["call_out_of_scope"],
        unknown_event_count=1,
    )
    c_text = """/* WARNING: Unknown calling convention -- yet parameter storage is locked */
void ptr_dispatch_callback(ulong param_1)
{
  code *pcVar1;
  pcVar1 = ptr_op_add;
  if ((param_1 & 1) != 0) {
    pcVar1 = ptr_op_xor;
  }
  ptr_apply_callback(pcVar1);
  return;
}
"""

    captured = []

    def _get_or_analyze(function_name, active_functions, minimum_param_count=0):
        if function_name == "ptr_apply_callback":
            return ptr_apply_analysis
        return None

    def _decompiler_fallback(function_name, args, active_functions, current_function=None, analysis=None):
        if function_name != "ptr_apply_callback":
            return None
        captured.append([arg.to_string() for arg in args])
        return [ExpandedValue(Expression.binary_op("INT_ADD", args[1], args[2]), [])]

    with patch.object(analyzer, "_get_decompiled_c_text", return_value=c_text):
        with patch.object(analyzer, "_get_or_analyze_call_target", side_effect=_get_or_analyze):
            with patch.object(analyzer, "_resolve_call_expansions_from_decompiler", side_effect=_decompiler_fallback):
                recovered = analyzer._recover_call_wrapper_returns_from_decompiler(
                    object(),
                    analysis,
                    Mock(),
                    set(),
                )

    assert recovered is not None
    assert captured == [["ptr_op_xor", "param_2", "param_3"], ["ptr_op_add", "param_2", "param_3"]]
    assert len(recovered) == 1
    assert recovered[0].value.to_string() == "(param_2 + param_3)"


def test_return_analyzer_refreshes_callee_parameter_cache_when_decompilation_is_richer():
    functions = [
        _FakeFunction("ptr_apply_callback", 0x402000),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)

    cache_key = str(functions[0].getEntryPoint())
    analyzer._effect_summary_parameter_cache[cache_key] = [
        {"name": "param_1", "index": 0, "size": 8}
    ]

    fresh_parameters = [
        {"name": "param_1", "index": 0, "size": 8},
        {"name": "param_2", "index": 1, "size": 8},
        {"name": "param_3", "index": 2, "size": 8},
    ]
    fake_results = Mock()
    fake_results.getHighFunction.return_value = Mock()

    with patch.object(analyzer, "_decompile_function", return_value=fake_results):
        with patch.object(analyzer, "_collect_parameters", return_value=fresh_parameters):
            refreshed = analyzer._get_freshest_callee_parameters("ptr_apply_callback")

    assert [param["name"] for param in refreshed] == ["param_1", "param_2", "param_3"]
    assert len(analyzer._effect_summary_parameter_cache[cache_key]) == 3


def test_return_analyzer_reanalyzes_call_target_when_cached_signature_is_too_small():
    functions = [
        _FakeFunction("ptr_apply_callback", 0x402000),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)

    cache_key = str(functions[0].getEntryPoint())
    stale_analysis = FunctionReturnAnalysis(
        function_name="ptr_apply_callback",
        entry_point="0x402000",
        parameters=[{"name": "param_1", "index": 0, "size": 8}],
        returns=[],
        return_type="undefined8",
    )
    fresh_analysis = FunctionReturnAnalysis(
        function_name="ptr_apply_callback",
        entry_point="0x402000",
        parameters=[
            {"name": "param_1", "index": 0, "size": 8},
            {"name": "param_2", "index": 1, "size": 8},
            {"name": "param_3", "index": 2, "size": 8},
        ],
        returns=[],
        return_type="undefined8",
    )
    analyzer._call_analysis_cache[cache_key] = stale_analysis

    with patch.object(analyzer, "analyze_function", return_value=fresh_analysis) as patched_analyze:
        refreshed = analyzer._get_or_analyze_call_target(
            "ptr_apply_callback",
            set(),
            minimum_param_count=3,
        )

    assert refreshed is fresh_analysis
    patched_analyze.assert_called_once()
    assert analyzer._call_analysis_cache[cache_key] is fresh_analysis


def test_return_analyzer_parsed_wrapper_parameters_keep_storage_info():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    params = [
        {
            "name": "param_1",
            "size": 8,
            "index": 0,
            "storage": {
                "is_register": True,
                "register_name": "a0",
                "base_register_name": "a0",
                "bit_offset_in_base": 0,
                "size_bits": 64,
            },
        },
        {
            "name": "param_2",
            "size": 8,
            "index": 1,
            "storage": {
                "is_register": True,
                "register_name": "a1",
                "base_register_name": "a1",
                "bit_offset_in_base": 0,
                "size_bits": 64,
            },
        },
    ]

    parsed = analyzer._parse_wrapper_argument_expr(
        "param_2",
        params,
        fallback_index=1,
        local_bindings={},
    )

    assert parsed is not None
    assert parsed.storage_info is not None
    assert parsed.storage_info.base_register_name == "a1"


def test_return_analyzer_does_not_collapse_complementary_cases_across_conflicting_value():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    xor_value = Expression.binary_op(
        "INT_XOR",
        Expression.parameter("param_2", 1, size=4),
        Expression.parameter("param_3", 2, size=4),
    )
    add_value = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("param_2", 1, size=4),
        Expression.parameter("param_3", 2, size=4),
    )
    even_cond = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.binary_op(
                "INT_AND",
                Expression.parameter("param_1", 0, size=4),
                Expression.constant(1, 4),
            ),
            Expression.constant(0, 4),
        ),
        False,
    )
    odd_cond = Condition(even_cond.expression, True)

    merged = analyzer._merge_equivalent_return_infos(
        [
            ReturnInfo(address="0x1000", value=xor_value, conditions=[odd_cond], branch_index=0),
            ReturnInfo(address="0x1000", value=xor_value, conditions=[even_cond], branch_index=1),
            ReturnInfo(address="0x1000", value=add_value, conditions=[even_cond], branch_index=2),
        ]
    )

    assert all(
        not (ret.value.to_string() == "(param_2 ^ param_3)" and ret.conditions == [])
        for ret in merged
    )
    assert any(ret.value.to_string() == "(param_2 + param_3)" for ret in merged)


def test_return_analyzer_resolves_wrapper_parameter_bound_to_pointer_symbol_target():
    functions = [
        _FakeFunction("ptr_op_add", 0x401100),
        _FakeFunction("ptr_op_xor", 0x401200),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)
    parameters = [
        {"name": "param_1", "size": 8, "index": 0},
        {"name": "param_2", "size": 4, "index": 1},
        {"name": "param_3", "size": 4, "index": 2},
    ]

    def _resolve_call(function_name, args, active_functions, current_function=None):
        if function_name == "ptr_op_add":
            return [ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])]
        if function_name == "ptr_op_xor":
            return [ExpandedValue(Expression.binary_op("INT_XOR", args[0], args[1]), [])]
        raise AssertionError(f"unexpected callee: {function_name}")

    with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
        expanded = analyzer._resolve_wrapper_call_target(
            "param_1",
            [
                Expression.parameter("param_2", 1, size=4),
                Expression.parameter("param_3", 2, size=4),
            ],
            [],
            parameters,
            {"param_1": Expression.variable("PTR_ptr_op_add_00112078", size=8)},
            set(),
            None,
        )

    assert expanded is not None
    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "(param_2 + param_3)"


def test_return_analyzer_treats_generic_decompiler_generated_names_as_non_callees():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    assert analyzer._looks_like_decompiler_temp_name("UNRECOVERED_JUMPTABLE")
    assert analyzer._looks_like_decompiler_temp_name("extraout_a0")
    assert analyzer._looks_like_decompiler_temp_name("unaff_gp")
    assert analyzer._looks_like_decompiler_temp_name("in_a1_hi")
    assert analyzer._resolve_named_wrapper_target("UNRECOVERED_JUMPTABLE") is None
    assert analyzer._resolve_named_wrapper_target("extraout_a0") is None
    assert analyzer._resolve_named_wrapper_target("ptr_op_add") == "ptr_op_add"


def test_return_analyzer_recovers_mips64_gcc_apply_wrapper_from_pointer_symbol_binding():
    functions = [
        _FakeFunction("ptr_op_add", 0x401100),
        _FakeFunction("ptr_op_xor", 0x401200),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)
    c_text = """undefined8 ptr_apply_callback(code *param_1,undefined4 param_2,undefined4 param_3)
{
  undefined8 uVar1;
  if (param_1 == (code *)0x0) {
    uVar1 = 0xfffffffffffffda8;
  }
  else {
    uVar1 = (*param_1)(param_2,param_3);
  }
  return uVar1;
}
"""
    params = [
        {"name": "param_1", "size": 8, "data_type": "code *", "index": 0},
        {"name": "param_2", "size": 4, "data_type": "undefined4", "index": 1},
        {"name": "param_3", "size": 4, "data_type": "undefined4", "index": 2},
    ]

    def _resolve_call(function_name, args, active_functions, current_function=None):
        if function_name == "ptr_op_add":
            return [ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])]
        if function_name == "ptr_op_xor":
            return [ExpandedValue(Expression.binary_op("INT_XOR", args[0], args[1]), [])]
        raise AssertionError(f"unexpected callee: {function_name}")

    with patch.object(analyzer, "_resolve_call_expansions", side_effect=_resolve_call):
        recovered = analyzer._recover_structured_call_wrapper_from_c_text(
            c_text,
            params,
            "0x1000",
            Mock(),
            set(),
            initial_bindings={
                "param_1": Expression.variable("PTR_ptr_op_add_120013090", size=8),
                "param_2": Expression.parameter("param_2", 1, size=4),
                "param_3": Expression.parameter("param_3", 2, size=4),
            },
        )

    assert recovered is not None
    assert len(recovered) == 1
    assert recovered[0].conditions == []
    assert recovered[0].value.to_string() == "(param_2 + param_3)"


def test_return_analyzer_preserves_phi_branch_conditions_for_pointer_symbol_targets():
    functions = [
        _FakeFunction("ptr_op_add", 0x401100),
        _FakeFunction("ptr_op_xor", 0x401200),
    ]
    analyzer = ReturnAnalyzer(program=_FakeProgram(functions), debug=False)
    cond_even = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.binary_op(
                "INT_AND",
                Expression.parameter("selector", 0, size=4),
                Expression.constant(1, 4),
            ),
            Expression.constant(0, 4),
        ),
        False,
    )
    cond_odd = Condition(cond_even.expression, True)
    phi_target = Expression.phi(
        [
            (cond_even, Expression.variable("PTR_ptr_op_add_120013090", size=8)),
            (cond_odd, Expression.variable("PTR_ptr_op_xor_120013098", size=8)),
        ]
    )

    targets = analyzer._resolve_wrapper_indirect_call_targets(phi_target, [], [])

    target_map = {
        name: [cond.to_string() for cond in conditions]
        for name, conditions in targets
    }
    assert target_map["ptr_op_add"] == ["((selector & 1) == 0)"]
    assert target_map["ptr_op_xor"] in (
        ["((selector & 1) != 0)"],
        ["(not ((selector & 1) == 0))"],
    )


def test_return_analyzer_straightline_wrapper_recovery_rejects_branching_body():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    c_text = """void ptr_select_path(undefined4 param_1,undefined4 param_2,int param_3)
{
  if (param_3 == 0) {
    ptr_scale_then_bias(param_2,3,1);
  }
  else {
    ptr_add_bias(param_1,10);
  }
  return;
}
"""

    recovered = analyzer._recover_straightline_call_chain_from_c_text(
        c_text,
        [
            {"name": "param_1", "size": 4, "data_type": "undefined4"},
            {"name": "param_2", "size": 4, "data_type": "undefined4"},
            {"name": "param_3", "size": 4, "data_type": "int"},
        ],
        "0x1000",
        Mock(),
        set(),
    )

    assert recovered is None


def test_solve_query_twostage_skips_full_query_for_unresolved_values():
    class _FakeStrategy:
        def __init__(self):
            self.messages = []
            self._active_normalization_stats = None

        def _build_condition_only_query(self, *_args, **_kwargs):
            return "(check-sat)"

        def _build_pair_query(self, *_args, **_kwargs):
            raise AssertionError("full query should not be built for unresolved values")

        def _solve_query_internal(self, query, pair_id, stage="full", use_hard_timeout=False):
            assert query == "(check-sat)"
            assert stage == "conds-only"
            return QueryResult(is_equivalent=False)

        def _debug_print(self, message):
            self.messages.append(message)

    strategy = _FakeStrategy()
    resolved_case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression.constant(1, 4),
        return_info=ReturnInfo(address="0x1000", value=Expression.constant(1, 4)),
        return_type="int",
    )
    unresolved_case = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression.unknown("void"),
        return_info=ReturnInfo(address="0x1001", value=Expression.unknown("void")),
        return_type="void",
    )

    result = solve_query_twostage(
        strategy,
        {"header_lines": [], "return_size1": 32, "return_size2": 32},
        unresolved_case,
        resolved_case,
        lambda text: text,
        lambda text: text,
        "(0,0)",
    )

    assert result.is_equivalent is None
    assert result.pair_stage == "with-ineq-skipped"
    assert any("unresolved value expression" in message for message in strategy.messages)


def test_expand_input_operation_skips_direct_shortcut_for_recursive_subgraphs():
    class _FakeOutput:
        def getSize(self):
            return 4

    class _FakeVarnode:
        def __init__(self, def_op=None):
            self._def_op = def_op

        def getDef(self):
            return self._def_op

    class _FakeOp:
        def __init__(self, inputs):
            self._inputs = inputs

        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return _FakeOutput()

    tracer = Mock()
    expander = ExpressionExpander(tracer, condition_tracker=None, debug=False)
    fake_op = _FakeOp([_FakeVarnode(), _FakeVarnode()])

    expander._op_requires_recursive_expansion = Mock(return_value=True)
    expander._trace_operation_expression = Mock(side_effect=AssertionError("direct shortcut must not run"))
    expander._expand_input_varnode = Mock(
        return_value=[ExpandedValue(Expression.constant(1, 4), [])]
    )
    expander._combine_input_expansions_with_conditions = Mock(
        return_value=[ExpandedValue(Expression.constant(2, 4), [])]
    )

    expanded = expander._expand_input_operation(fake_op, [], depth=0)

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "2"
    assert expander._expand_input_varnode.call_count == 2
    expander._combine_input_expansions_with_conditions.assert_called_once()


def test_expand_operation_skips_direct_shortcut_for_recursive_subgraphs():
    class _FakeVarnode:
        def __init__(self, def_op=None):
            self._def_op = def_op

        def getDef(self):
            return self._def_op

    class _FakeOp:
        def __init__(self, inputs):
            self._inputs = inputs

        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

    tracer = Mock()
    expander = ExpressionExpander(tracer, condition_tracker=None, debug=False)
    fake_op = _FakeOp([_FakeVarnode(), _FakeVarnode()])

    expander._op_requires_recursive_expansion = Mock(return_value=True)
    expander._trace_operation_expression = Mock(side_effect=AssertionError("top-level direct shortcut must not run"))
    expander.expand_from_varnode = Mock(
        side_effect=[
            [ExpandedValue(Expression.constant(1, 4), [])],
            [ExpandedValue(Expression.constant(2, 4), [])],
        ]
    )
    expander._combine_input_expansions_with_conditions = Mock(
        return_value=[ExpandedValue(Expression.constant(3, 4), [])]
    )

    expanded = expander._expand_operation(fake_op, [], depth=0)

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "3"
    assert expander.expand_from_varnode.call_count == 2
    expander._combine_input_expansions_with_conditions.assert_called_once()


def test_expand_input_operation_expands_phi_direct_trace_without_recursive_pcode_fallback():
    class _FakeOutput:
        def getSize(self):
            return 4

    class _FakeVarnode:
        def __init__(self, def_op=None):
            self._def_op = def_op

        def getDef(self):
            return self._def_op

    class _FakeOp:
        def __init__(self, inputs):
            self._inputs = inputs

        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return _FakeOutput()

    tracer = Mock()
    expander = ExpressionExpander(tracer, condition_tracker=None, debug=False)
    fake_op = _FakeOp([_FakeVarnode(), _FakeVarnode()])
    phi_expr = Expression.phi(
        [
            (None, Expression.constant(1, 4)),
            (None, Expression.constant(2, 4)),
        ]
    )
    phi_expr.size = 4

    expander._op_requires_recursive_expansion = Mock(return_value=False)
    expander._trace_operation_expression = Mock(return_value=phi_expr)
    expander._expand_expression_cases = Mock(
        return_value=[
            ExpandedValue(Expression.constant(1, 4), []),
            ExpandedValue(Expression.constant(2, 4), []),
        ]
    )

    expanded = expander._expand_input_operation(fake_op, [], depth=0)

    assert len(expanded) == 2
    assert [ev.value.to_string() for ev in expanded] == ["1", "2"]
    expander._expand_expression_cases.assert_called_once()


def test_expand_operation_expands_phi_direct_trace_without_recursive_pcode_fallback():
    class _FakeVarnode:
        def __init__(self, def_op=None):
            self._def_op = def_op

        def getDef(self):
            return self._def_op

    class _FakeOp:
        def __init__(self, inputs):
            self._inputs = inputs

        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

    tracer = Mock()
    expander = ExpressionExpander(tracer, condition_tracker=None, debug=False)
    fake_op = _FakeOp([_FakeVarnode(), _FakeVarnode()])
    phi_expr = Expression.phi(
        [
            (None, Expression.constant(1, 4)),
            (None, Expression.constant(2, 4)),
        ]
    )
    phi_expr.size = 4

    expander._op_requires_recursive_expansion = Mock(return_value=False)
    expander._trace_operation_expression = Mock(return_value=phi_expr)
    expander._expand_expression_cases = Mock(
        return_value=[
            ExpandedValue(Expression.constant(1, 4), []),
            ExpandedValue(Expression.constant(2, 4), []),
        ]
    )

    expanded = expander._expand_operation(fake_op, [], depth=0)

    assert len(expanded) == 2
    assert [ev.value.to_string() for ev in expanded] == ["1", "2"]
    expander._expand_expression_cases.assert_called_once()


def test_expand_multiequal_input_skips_canonical_shortcut_for_recursive_varnode():
    class _FakeParent:
        def __init__(self, pred):
            self._pred = pred

        def getInSize(self):
            return 1

        def getIn(self, index):
            assert index == 0
            return self._pred

    class _FakeOp:
        def __init__(self, parent, input_varnode):
            self._parent = parent
            self._input_varnode = input_varnode

        def getParent(self):
            return self._parent

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input_varnode

    input_varnode = Mock()
    pred_block = object()
    block_info = Mock(index=3)
    condition_tracker = Mock()
    condition_tracker.get_block_by_hash.return_value = block_info
    condition_tracker.get_all_valid_paths_to_block.return_value = [[]]

    expander = ExpressionExpander(Mock(), condition_tracker=condition_tracker, debug=False)
    expander._get_edge_condition = Mock(return_value=None)
    expander._varnode_requires_recursive_expansion = Mock(return_value=True)
    expander._trace_and_canonicalize_input_value = Mock(
        side_effect=AssertionError("canonical shortcut must not run")
    )
    expander._expand_input_varnode = Mock(
        return_value=[ExpandedValue(Expression.constant(3, 4), [])]
    )
    expander._deduplicate_expanded_values = Mock(
        return_value=[ExpandedValue(Expression.constant(3, 4), [])]
    )

    expanded = expander._expand_multiequal_internal(
        _FakeOp(_FakeParent(pred_block), input_varnode),
        [],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "3"
    expander._expand_input_varnode.assert_called_once()


def test_expand_multiequal_carries_base_conditions_into_predicate_filtering():
    class _FakeParent:
        def __init__(self, pred):
            self._pred = pred

        def getInSize(self):
            return 1

        def getIn(self, index):
            assert index == 0
            return self._pred

    class _FakeOp:
        def __init__(self, parent, input_varnode):
            self._parent = parent
            self._input_varnode = input_varnode

        def getParent(self):
            return self._parent

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input_varnode

    input_varnode = Mock()
    pred_block = object()
    block_info = Mock(index=3)
    condition_tracker = Mock()
    condition_tracker.get_block_by_hash.return_value = block_info

    param = Expression.parameter("param_1", size=8)
    zero = Expression.constant(0, 8)
    base_condition = Condition(Expression.binary_op("INT_SLESSEQUAL", zero, param))
    pred_condition = Condition(Expression.binary_op("INT_SLESSEQUAL", param, Expression.constant(-1, 8)))
    condition_tracker.get_all_valid_paths_to_block.return_value = [[pred_condition]]

    expander = ExpressionExpander(Mock(), condition_tracker=condition_tracker, debug=False)
    expander._get_edge_condition = Mock(return_value=None)
    expander._varnode_requires_recursive_expansion = Mock(return_value=True)
    expander._expand_input_varnode = Mock(
        return_value=[ExpandedValue(Expression.constant(3, 4), [])]
    )
    expander._deduplicate_expanded_values = Mock(return_value=[])

    expanded = expander._expand_multiequal_internal(
        _FakeOp(_FakeParent(pred_block), input_varnode),
        [base_condition],
        depth=0,
    )

    assert expanded[0].value.to_string() == "phi_no_valid_branch"
    assert expanded[0].conditions == [base_condition]
    expander._expand_input_varnode.assert_not_called()


def test_expand_multiequal_simplifies_phi_conditions_before_recursive_expansion():
    class _FakeParent:
        def __init__(self, pred):
            self._pred = pred

        def getInSize(self):
            return 1

        def getIn(self, index):
            assert index == 0
            return self._pred

    class _FakeOp:
        def __init__(self, parent, input_varnode):
            self._parent = parent
            self._input_varnode = input_varnode

        def getParent(self):
            return self._parent

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input_varnode

    input_varnode = Mock()
    pred_block = object()
    block_info = Mock(index=7)
    condition_tracker = Mock()
    condition_tracker.get_block_by_hash.return_value = block_info
    condition_tracker.get_all_valid_paths_to_block.return_value = [[]]

    param = Expression.parameter("param_2", size=4)
    zero = Expression.constant(0, 4)
    two = Expression.constant(2, 4)
    select_first_branch = Condition(Expression.binary_op("INT_SLESS", param, two))
    selected_expr = Expression.binary_op("INT_EQUAL", Expression.memory(Expression.constant(0x100, 8), size=4), zero)
    fallback_expr = Expression.binary_op("INT_EQUAL", Expression.memory(Expression.constant(0x200, 8), size=4), zero)
    edge_condition = Condition(
        Expression.phi([
            (select_first_branch, selected_expr),
            (None, fallback_expr),
        ]),
        negated=True,
    )

    expander = ExpressionExpander(Mock(), condition_tracker=condition_tracker, debug=False)
    expander._get_edge_condition = Mock(return_value=edge_condition)
    expander._varnode_requires_recursive_expansion = Mock(return_value=True)

    def _expand_input(input_vn, conditions, depth):
        assert input_vn is input_varnode
        assert all(cond.expression.expr_type != ExpressionType.PHI for cond in conditions)
        rendered = {cond.to_string() for cond in conditions}
        assert select_first_branch.to_string() in rendered
        assert f"(not {selected_expr.to_string()})" in rendered
        return [ExpandedValue(Expression.constant(3, 4), conditions)]

    expander._expand_input_varnode = Mock(side_effect=_expand_input)

    expanded = expander._expand_multiequal_internal(
        _FakeOp(_FakeParent(pred_block), input_varnode),
        [select_first_branch],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "3"
    assert all(cond.expression.expr_type != ExpressionType.PHI for cond in expanded[0].conditions)
    expander._expand_input_varnode.assert_called_once()


def test_counterexample_validation_rejects_ambiguous_sat_model():
    class _Strategy:
        def __init__(self):
            self.solver_runner = _FakeSolverRunner()
            self.per_query_timeout = 5
            self.messages = []

        def _debug_print(self, msg: str):
            self.messages.append(msg)

    class _FakeSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_sequential(self, query: str):
            if "(assert (= (_ bv7 32) (_ bv7 32)))" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
                )
            if "(assert (= x_1 (bvadd x_2 (_ bv1 32))))" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.UNSAT)]
                )
            return ParallelResult(
                results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
            )

    strategy = _Strategy()
    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    replace1 = build_symbol_replacer(params1, [])
    replace2 = build_symbol_replacer(params2, [])
    x1 = _param_expr("x", 0, size=4)
    x2 = _param_expr("x", 0, size=4)

    cases1 = [
        ReturnCase(
            index=0,
            conditions=[],
            value_expr=x1,
            return_info=ReturnInfo(address="0x1", value=x1, conditions=[]),
            return_type="int",
        ),
        ReturnCase(
            index=1,
            conditions=[_cond_eq(x1, Expression.constant(5, 4))],
            value_expr=Expression.constant(7, 4),
            return_info=ReturnInfo(
                address="0x2",
                value=Expression.constant(7, 4),
                conditions=[_cond_eq(x1, Expression.constant(5, 4))],
            ),
            return_type="int",
        ),
    ]
    cases2 = [
        ReturnCase(
            index=0,
            conditions=[],
            value_expr=Expression.binary_op("INT_ADD", x2, Expression.constant(1, 4)),
            return_info=ReturnInfo(
                address="0x3",
                value=Expression.binary_op("INT_ADD", x2, Expression.constant(1, 4)),
                conditions=[],
            ),
            return_type="int",
        ),
        ReturnCase(
            index=1,
            conditions=[_cond_eq(x2, Expression.constant(5, 4))],
            value_expr=Expression.constant(7, 4),
            return_info=ReturnInfo(
                address="0x4",
                value=Expression.constant(7, 4),
                conditions=[_cond_eq(x2, Expression.constant(5, 4))],
            ),
            return_type="int",
        ),
    ]
    base_ctx = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    is_decisive = validate_counterexample_across_cases(
        strategy,
        base_ctx,
        cases1,
        cases2,
        replace1,
        replace2,
        sat_case_indices=(0, 0),
        counterexample_raw={"x_1": 5, "x_2": 5},
    )

    assert not is_decisive
    assert any("ambiguous" in message for message in strategy.messages)
