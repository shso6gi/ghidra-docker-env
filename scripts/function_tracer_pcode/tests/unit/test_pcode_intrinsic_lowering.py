# -*- coding: utf-8 -*-

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.phi_resolver import ExpandedBranch, PhiHandler
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.model import (
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
