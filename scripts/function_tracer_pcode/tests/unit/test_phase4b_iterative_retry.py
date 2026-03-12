# -*- coding: utf-8 -*-
"""Phase 4-B の反復 ABI リトライ挙動を検証するテスト"""

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
from scripts.function_tracer_pcode.equivalence.phases.handler import PhaseContext
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.smt import SolverStatus

from conftest import create_mock_analysis, create_mock_result


def _create_phase_context() -> PhaseContext:
    analysis1 = create_mock_analysis(
        function_name="branch_lt",
        parameters=[
            {"name": "param_1", "data_type": "long", "size": 8, "index": 0},
            {"name": "param_2", "data_type": "long", "size": 8, "index": 1},
        ],
    )
    analysis2 = create_mock_analysis(
        function_name="branch_lt",
        parameters=[
            {"name": "param_1", "data_type": "int", "size": 4, "index": 0},
            {"name": "param_2", "data_type": "int", "size": 4, "index": 1},
        ],
    )

    return PhaseContext(
        program1=Mock(),
        program2=Mock(),
        function_name1="branch_lt",
        function_name2="branch_lt",
        binary1_name="mips64-bin",
        binary2_name="arm64-bin",
        decompile_timeout=60,
        save_formula=True,
        type_fix_result=TypeFixResult(),
        original_signature1=None,
        original_signature2=None,
        analysis1=analysis1,
        analysis2=analysis2,
    )


def test_iterative_phase4b_accumulates_new_constraints_before_resolving():
    checker = EquivalenceChecker(debug=True)
    ctx = _create_phase_context()

    initial_constraints = {"param_2_1": ("signed", 32)}
    sat_result = create_mock_result(
        is_equivalent=False,
        solver_status=SolverStatus.SAT,
        counterexample={
            "param_1_1": 0x7FFFFFFF80000000,
            "param_1_2": 0x80000000,
            "param_2_1": 0x7FFFFFFF,
            "param_2_2": 0x7FFFFFFF,
        },
    )
    unsat_result = create_mock_result(
        is_equivalent=True,
        solver_status=SolverStatus.UNSAT,
    )

    with patch.object(
        checker,
        "_retry_with_abi_constraints",
        side_effect=[sat_result, unsat_result],
    ) as mock_retry, patch.object(
        checker.phase_handler,
        "run_phase4_mips64_retry",
        return_value={"param_1_1": ("signed", 32)},
    ) as mock_phase4b:
        result = checker._retry_with_iterative_abi_constraints(
            ctx, initial_constraints, retry_count=1
        )

    assert result.is_equivalent is True
    assert mock_retry.call_count == 2
    assert mock_phase4b.call_count == 1

    first_constraints = mock_retry.call_args_list[0].args[1]
    second_constraints = mock_retry.call_args_list[1].args[1]
    assert first_constraints == {"param_2_1": ("signed", 32)}
    assert second_constraints == {
        "param_2_1": ("signed", 32),
        "param_1_1": ("signed", 32),
    }


def test_iterative_phase4b_stops_when_detector_repeats_same_constraints():
    checker = EquivalenceChecker(debug=True)
    ctx = _create_phase_context()

    initial_constraints = {"param_2_1": ("signed", 32)}
    sat_result = create_mock_result(
        is_equivalent=False,
        solver_status=SolverStatus.SAT,
        counterexample={
            "param_1_1": 0x7FFFFFFF80000000,
            "param_1_2": 0x80000000,
            "param_2_1": 0x7FFFFFFF,
            "param_2_2": 0x7FFFFFFF,
        },
    )

    with patch.object(
        checker,
        "_retry_with_abi_constraints",
        return_value=sat_result,
    ) as mock_retry, patch.object(
        checker.phase_handler,
        "run_phase4_mips64_retry",
        return_value={"param_2_1": ("signed", 32)},
    ) as mock_phase4b:
        result = checker._retry_with_iterative_abi_constraints(
            ctx, initial_constraints, retry_count=1
        )

    assert result.is_equivalent is False
    assert mock_retry.call_count == 1
    assert mock_phase4b.call_count == 1
