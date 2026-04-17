# -*- coding: utf-8 -*-

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.effect_summary import EffectSummary, StoreEffect
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_builder import (
    build_pair_query,
    extract_return_cases,
)
from scripts.function_tracer_pcode.model import (
    CanonicalLocation,
    CallTargetRef,
    DeferredCallRef,
    Expression,
    ReturnInfo,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.model.render_smt import collect_unknown_smt_declarations
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def test_expression_unknown_uses_object_centric_runtime_identity_for_smt():
    expr = Expression.unknown("call_out_of_scope:ptr_dispatch_callback")

    assert getattr(expr.runtime_ref, "kind", None) == "opaque_unknown"

    declarations = collect_unknown_smt_declarations(expr)
    assert declarations == [(expr.to_smt(), 32)]
    assert expr.to_smt().startswith("rtunk_")
    assert expr.to_smt() != "unknown"


def test_pairwise_query_declares_runtime_unknown_symbols():
    unknown_expr = Expression.unknown("call_out_of_scope:ptr_call_chain")
    analysis1 = create_mock_analysis(
        "left",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int"}],
        returns=[ReturnInfo(address="0x1000", value=unknown_expr, conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int"}],
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )

    builder = FormulaBuilder()
    base_ctx = builder.build_base_context(analysis1, analysis2)
    query = build_pair_query(
        base_ctx,
        extract_return_cases(analysis1)[0],
        extract_return_cases(analysis2)[0],
        lambda expr: expr.to_smt(),
        lambda expr: expr.to_smt(),
        "0,0",
    )

    declared_symbol, bit_width = base_ctx["runtime_unknown_declarations"][0]
    assert bit_width == 32
    assert declared_symbol == unknown_expr.to_smt()
    assert f"(declare-const {declared_symbol} (_ BitVec 32))" in "\n".join(base_ctx["header_lines"])
    assert f"(declare-const {declared_symbol} (_ BitVec 32))" in query
    assert " unknown" not in query


def test_tracer_promotes_unresolved_direct_call_to_deferred_call_runtime_object():
    class _FakeVarnode:
        def __init__(self, name):
            self.name = name

    class _FakeCallOp:
        def __init__(self, inputs):
            self._inputs = inputs

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

    tracer = PcodeTracer(program=Mock(), high_function=Mock(), debug=False)
    target = _FakeVarnode("target")
    arg0 = _FakeVarnode("arg0")
    arg1 = _FakeVarnode("arg1")
    call_op = _FakeCallOp([target, arg0, arg1])
    recorded = {}

    tracer.resolve_call_target_ref = lambda *_args, **_kwargs: CallTargetRef.from_name("callee")
    tracer.trace_varnode = lambda varnode, depth=0, use_cache=True: {
        target: Expression.constant(0x401000, 8),
        arg0: Expression.parameter("param_1", index=0, size=8),
        arg1: Expression.parameter("param_2", index=1, size=4),
    }[varnode]

    def _record_deferred_call(target_ref, args, call_target_expr=None):
        recorded["target_ref"] = target_ref
        recorded["args"] = [arg.to_string() for arg in args]
        recorded["target_expr"] = None if call_target_expr is None else call_target_expr.to_string()
        return UnknownValueRef.deferred_call(
            deferred_call_ref=DeferredCallRef(
                target_ref=target_ref,
                sequence=7,
            ),
            target_ref=target_ref,
        )

    tracer.record_deferred_call = _record_deferred_call

    result = tracer._trace_pcode_op_internal(call_op, depth=0, use_cache=False)

    assert result.expr_type.name == "UNKNOWN"
    assert getattr(result.runtime_ref, "kind", None) == "deferred_call"
    assert recorded["target_ref"] == CallTargetRef.from_name("callee")
    assert recorded["args"] == ["param_1", "param_2"]
    assert recorded["target_expr"] == "4198400"


def test_effect_sensitive_wrapper_collapse_keeps_non_identity_binary_wrappers():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    analyzer._current_parameters = [
        {"name": "param_1", "index": 0, "size": 8},
        {"name": "param_2", "index": 1, "size": 4},
    ]
    original = Expression.binary_op(
        "INT_SUB",
        Expression.memory(Expression.parameter("param_1", index=0, size=8), size=4),
        Expression.parameter("param_2", index=1, size=4),
    )
    rewritten = Expression.binary_op(
        "INT_SUB",
        Expression.constant(7, 4),
        Expression.parameter("param_2", index=1, size=4),
    )
    effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.constant(7, 4),
                conditions=[],
                order_key=0,
            )
        ],
    )

    collapsed = analyzer._collapse_effect_sensitive_case_wrapper(
        original,
        rewritten,
        [],
        effect_summary,
    )

    assert collapsed.to_string() == rewritten.to_string()
