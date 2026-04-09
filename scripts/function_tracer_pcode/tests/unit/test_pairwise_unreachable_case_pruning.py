# -*- coding: utf-8 -*-
"""Unreachable return-case pruning regressions for PairwiseStrategy."""

import sys
from pathlib import Path
from unittest.mock import Mock


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus


def _param(name: str) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=8)


def _const(value: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=8)


def _binary(op: str, left: Expression, right: Expression) -> Expression:
    return Expression(ExpressionType.BINARY_OP, operator=op, operands=[left, right], size=8 if op.startswith("INT_") and "LESS" not in op and "EQUAL" not in op else 1)


def _analysis(name: str, returns) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x1000",
        parameters=[],
        returns=returns,
        return_type="long",
    )


def _mock_parallel(status: SolverStatus) -> ParallelResult:
    return ParallelResult(
        results=[SolverResult("mock", status, elapsed_time=0.01)]
    )


def test_pairwise_strategy_prunes_unreachable_unknown_case_before_pairing():
    phi_selector = Condition(_binary("INT_EQUAL", _param("param_1"), _const(0)))
    impossible_phi = Expression.phi(
        [
            (phi_selector, _const(1)),
            (None, _const(2)),
        ]
    )
    impossible_condition = Condition(_binary("INT_EQUAL", impossible_phi, _const(0)))

    analysis1 = _analysis(
        "f1",
        [
            ReturnInfo(
                address="0x1001",
                value=Expression.unknown("phi_no_valid_branch"),
                conditions=[impossible_condition],
            ),
            ReturnInfo(
                address="0x1002",
                value=_const(7),
                conditions=[],
            ),
        ],
    )
    analysis2 = _analysis(
        "f2",
        [
            ReturnInfo(
                address="0x2001",
                value=_const(7),
                conditions=[],
            )
        ],
    )

    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "return_size1": 64,
        "return_size2": 64,
    }

    solver_runner = Mock()
    solver_runner.timeout = 5

    def _run_sequential(query: str):
        if "Single Case Reachability: Case1[0]" in query:
            return _mock_parallel(SolverStatus.UNSAT)
        if "; Value inequality" in query:
            return _mock_parallel(SolverStatus.UNSAT)
        return _mock_parallel(SolverStatus.SAT)

    solver_runner.run_sequential.side_effect = _run_sequential

    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    assert result.sat_pairs == 0
