# -*- coding: utf-8 -*-

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.phi_resolver import ExpandedBranch, PhiHandler
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.model import (
    AddressValueRef,
    Expression,
    ExpressionType,
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
)
from scripts.function_tracer_pcode.model.render_smt import (
    expression_contains_unsupported_smt_ops,
    expression_to_smt,
)
from scripts.function_tracer_pcode.transform.expander import ExpandedValue, ExpressionExpander


def _param(name: str, size: int = 8) -> Expression:
    return Expression.parameter(name, size=size)


def _const(value: int, size: int = 8) -> Expression:
    return Expression.constant(value, size=size)


def test_expression_to_smt_lowers_ptradd_intrinsic_without_uninterpreted_symbol():
    expr = Expression.intrinsic(
        "PTRADD",
        [_param("base"), _const(1), _const(8)],
        size=8,
        opcode=PTRADD_OPCODE,
    )

    smt = expression_to_smt(expr)

    assert expression_contains_unsupported_smt_ops(expr) is False
    assert smt == "(bvadd base (bvmul (_ bv1 64) (_ bv8 64)))"
    assert "PTRADD" not in smt


def test_pairwise_supported_intrinsic_is_not_marked_unresolved():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    expr = Expression.intrinsic(
        "PTRADD",
        [_param("base"), _const(2), _const(4)],
        size=8,
        opcode=PTRADD_OPCODE,
    )

    assert strategy._expression_contains_unresolved(expr) is False
    assert strategy._expression_contains_unresolved(Expression.call("callee", [_param("base")])) is True


def test_expander_combines_three_input_ptradd_as_intrinsic(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: False),
    )
    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(lambda cls, conds: list(conds)),
    )

    result = expander._combine_input_expansions_with_conditions(
        "PTRADD",
        [
            [ExpandedValue(_param("base"), [])],
            [ExpandedValue(_const(3), [])],
            [ExpandedValue(_const(8), [])],
        ],
        [],
        depth=0,
        output_size=8,
        opcode=PTRADD_OPCODE,
    )

    assert len(result) == 1
    assert result[0].value.expr_type == ExpressionType.INTRINSIC
    assert result[0].value.opcode == PTRADD_OPCODE
    assert expression_to_smt(result[0].value) == "(bvadd base (bvmul (_ bv3 64) (_ bv8 64)))"


def test_phi_handler_combines_ptrsub_as_intrinsic_even_for_two_inputs():
    tracer = type("Tracer", (), {"debug": False})()
    tracker = Mock()
    handler = PhiHandler(tracer, tracker)

    result = handler._combine_expansions(
        "PTRSUB",
        [
            [ExpandedBranch([], _param("base"))],
            [ExpandedBranch([], _const(0x20))],
        ],
        [],
        opcode=PTRSUB_OPCODE,
        output_size=8,
    )

    assert len(result) == 1
    assert result[0].value.expr_type == ExpressionType.INTRINSIC
    assert result[0].value.opcode == PTRSUB_OPCODE
    assert expression_to_smt(result[0].value) == "(bvadd base (_ bv32 64))"


def test_tracer_emits_ptrsub_intrinsic_with_derived_address_runtime_ref():
    anchor_ref = AddressValueRef(
        address_offset=0x00112008,
        source="unit_test",
        display_hint="ptr_anchor",
        symbol_name="PTR_lookup_table",
        block_name=".rodata",
        is_initialized=True,
        can_read=True,
        can_write=False,
        can_execute=False,
        is_volatile=False,
    )
    base_expr = Expression.constant(0, size=8)
    anchor_expr = Expression.constant(
        anchor_ref.address_offset,
        size=8,
        runtime_ref=anchor_ref,
    )

    class _FakeOutput:
        def getSize(self):
            return 8

    class _FakePcodeOp:
        def __init__(self, inputs):
            self._inputs = inputs

        def getMnemonic(self):
            return "PTRSUB"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return _FakeOutput()

    input_base = object()
    input_offset = object()
    tracer = object.__new__(PcodeTracer)
    tracer._debug_available = lambda: False
    tracer.trace_varnode = lambda varnode, depth, use_cache: {
        input_base: base_expr,
        input_offset: anchor_expr,
    }[varnode]
    tracer._derive_pointer_runtime_ref = lambda expr, display_name=None: AddressValueRef(
        address_offset=0x00112008,
        source="derived_test",
        display_hint=display_name,
        symbol_name="PTR_lookup_table",
        block_name=".rodata",
        is_initialized=True,
        can_read=True,
        can_write=False,
        can_execute=False,
        is_volatile=False,
    )

    expr = PcodeTracer._trace_pcode_op_internal(
        tracer,
        _FakePcodeOp([input_base, input_offset]),
        0,
        True,
    )

    assert expr.expr_type == ExpressionType.INTRINSIC
    assert expr.opcode == PTRSUB_OPCODE
    assert expr.runtime_ref.address_offset == 0x00112008


def test_tracer_promotes_constant_varnode_to_address_object_when_ghidra_exposes_readonly_data():
    class _FakeSpace:
        def getSpaceID(self):
            return 1

        def getName(self):
            return "ram"

    class _FakeAddress:
        def __init__(self, offset):
            self._offset = offset
            self._space = _FakeSpace()

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self._space

    class _FakeDefaultSpace:
        def getAddress(self, offset):
            return _FakeAddress(offset)

    class _FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return _FakeDefaultSpace()

    class _FakeBlock:
        def getName(self):
            return ".rodata"

        def isInitialized(self):
            return True

        def isRead(self):
            return True

        def isWrite(self):
            return False

        def isExecute(self):
            return False

        def isVolatile(self):
            return False

    class _FakeMemory:
        def getBlock(self, _address):
            return _FakeBlock()

    class _FakeData:
        def getPrimarySymbol(self):
            return None

    class _FakeListing:
        def getDataAt(self, _address):
            return _FakeData()

        def getDataContaining(self, _address):
            return None

    class _FakeSymbolTable:
        def getPrimarySymbol(self, _address):
            return None

    class _FakeProgram:
        def getAddressFactory(self):
            return _FakeAddressFactory()

        def getMemory(self):
            return _FakeMemory()

        def getListing(self):
            return _FakeListing()

        def getSymbolTable(self):
            return _FakeSymbolTable()

    class _FakeConstantVarnode:
        def isConstant(self):
            return True

        def getOffset(self):
            return 0x00112008

        def getSize(self):
            return 8

    tracer = object.__new__(PcodeTracer)
    tracer.program = _FakeProgram()
    tracer.debug = False
    tracer._debug_available = lambda: False

    expr = PcodeTracer._trace_varnode_internal(
        tracer,
        _FakeConstantVarnode(),
        0,
        True,
    )

    assert expr.expr_type == ExpressionType.CONSTANT
    assert isinstance(expr.runtime_ref, AddressValueRef)
    assert expr.runtime_ref.address_offset == 0x00112008
    assert expr.runtime_ref.block_name == ".rodata"
