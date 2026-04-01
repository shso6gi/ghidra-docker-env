# -*- coding: utf-8 -*-

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.equivalence.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.equivalence.formula.types import ParameterInfo
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
    validate_counterexample_across_cases,
)
from scripts.function_tracer_pcode.model import Condition, Expression, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.transform.expander import ExpandedValue, ExpressionExpander


def _param_expr(name: str, index: int = 0, size: int = 4) -> Expression:
    return Expression.parameter(name, index=index, size=size)


def _cond_eq(left: Expression, right: Expression) -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", left, right), False)


def _cond_ne(left: Expression, right: Expression) -> Condition:
    return Condition(Expression.binary_op("INT_NOTEQUAL", left, right), False)


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
    expander._expand_input_varnode.assert_not_called()


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
