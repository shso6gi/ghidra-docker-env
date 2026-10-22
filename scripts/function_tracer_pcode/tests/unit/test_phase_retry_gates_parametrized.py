# -*- coding: utf-8 -*-
"""Phase遷移のリトライゲート（停止条件）テスト"""

import pytest
from unittest.mock import Mock

from scripts.function_tracer_pcode.checker.phases.handler import PhaseHandler, PhaseContext
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixerConfig, TypeFixResult
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.core import Expression, ExpressionType

# ★ [P3] conftest からhelper関数をインポート（fixture化されているのでOK）
from conftest import create_mock_result, create_mock_analysis, MockProgram

class TestPhaseRetryGatesParametrized:
    """★ Parametrized tests for recovery phase → SAT flow"""
    
    
    @pytest.mark.parametrize("phase_name,phase_mocks", [
        pytest.param(
            "Phase_1_signedness",
            {"run_phase1_signedness_fix": True},
            id="phase1_signedness"
        ),
        pytest.param(
            "Phase_1_5_param_signedness",
            {"run_phase1_signedness_fix": False, "run_phase1_5_param_signedness_fix": True},
            id="phase1_5_param_signedness"
        ),
        pytest.param(
            "Phase_2_pattern",
            {"run_phase1_signedness_fix": False, "run_phase1_5_param_signedness_fix": False,
             "run_phase2_return_type_fix": True},
            id="phase2_pattern"
        ),
        pytest.param(
            "Phase_3_param_type",
            {"run_phase1_signedness_fix": False, "run_phase1_5_param_signedness_fix": False,
             "run_phase2_return_type_fix": False, "run_phase3_param_type_fix": True},
            id="phase3_param_type"
        ),
        pytest.param(
            "Phase_4A_mips64_fix",
            {"run_phase1_signedness_fix": False, "run_phase1_5_param_signedness_fix": False,
             "run_phase2_return_type_fix": False, "run_phase3_param_type_fix": False,
             "run_phase4_mips64_fix": True},
            id="phase4a_mips64_fix"
        ),
    ])
    def test_recovery_sat_genuine_stops_not_equivalent(
        self, mock_program_mips64, mock_program_x86, phase_name, phase_mocks
    ):
        """★ 各recovery phase後のSAT（真性反例）でNOT EQUIVALENTで停止することを確認"""
        from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
        from unittest.mock import Mock, patch
        
        checker = EquivalenceChecker(debug=True, canonical_decision_cutover=False)
        
        mock_analysis_mips64 = create_mock_analysis(
            function_name="test_func",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}]
        )
        
        mock_analysis_x86 = create_mock_analysis(
            function_name="test_func",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}]
        )
        
        counterexample = {
            "param_1_1": 0x0000000012345678,
            "param_1_2": 0x12345678,
        }
        
        with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
            analyzer_call_count = [0]
            
            def mock_analyze_side_effect(func_name, timeout):
                analyzer_call_count[0] += 1
                if analyzer_call_count[0] % 2 == 1:
                    return mock_analysis_mips64
                else:
                    return mock_analysis_x86
            
            mock_analyzer = Mock()
            mock_analyzer.analyze_function_by_name.side_effect = mock_analyze_side_effect
            mock_analyzer.dispose = Mock()
            mock_analyzer_class.return_value = mock_analyzer
            
            check_count = [0]
            
            def mock_check_side_effect(*args, **kwargs):
                check_count[0] += 1
                if check_count[0] == 1:
                    return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)
                elif check_count[0] == 2:
                    return create_mock_result(
                        is_equivalent=False,
                        solver_status=SolverStatus.SAT,
                        counterexample=counterexample
                    )
                else:
                    raise Exception(f"Unexpected check call #{check_count[0]}")
            
            with patch.object(checker, 'check', side_effect=mock_check_side_effect):
                default_mocks = {
                    "run_phase1_signedness_fix": False,
                    "run_phase1_5_param_signedness_fix": False,
                    "run_phase2_return_type_fix": False,
                    "run_phase3_param_type_fix": False,
                    "run_phase4_mips64_fix": False,
                }
                default_mocks.update(phase_mocks)
                
                patches = []
                for method_name, return_value in default_mocks.items():
                    p = patch.object(checker.phase_handler, method_name, return_value=return_value)
                    patches.append(p)
                
                for p in patches:
                    p.start()
                
                try:
                    result = checker.check_from_binaries(
                        mock_program_mips64, mock_program_x86,
                        "test_func", "test_func",
                        retry_with_type_fix=True
                    )

                    assert result.is_equivalent is False, \
                        f"[{phase_name}] Should stop as NOT EQUIVALENT for genuine counterexample"
                finally:
                    for p in patches:
                        p.stop()
