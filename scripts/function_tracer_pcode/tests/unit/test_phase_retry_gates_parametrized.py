# -*- coding: utf-8 -*-
"""Phase遷移のリトライゲート（停止条件）テスト"""

import pytest
from unittest.mock import Mock

from scripts.function_tracer_pcode.equivalence.phases.handler import PhaseHandler, PhaseContext
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixerConfig, TypeFixResult
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.model import Expression, ExpressionType

# ★ [P3] conftest からhelper関数をインポート（fixture化されているのでOK）
from conftest import create_mock_result, create_mock_analysis, MockProgram

class TestPhaseRetryGatesParametrized:
    """★ Parametrized tests for recovery phase → SAT → Phase 4-B flow"""
    
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
    def test_recovery_sat_spurious_triggers_phase4b(
        self, mock_program_mips64, mock_program_x86, phase_name, phase_mocks
    ):
        """★ 各recovery phase後のSAT（偽反例）でPhase 4-Bが呼ばれることを確認"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from unittest.mock import Mock, patch
        
        checker = EquivalenceChecker(debug=True, canonical_decision_cutover=False)
        
        mock_analysis_mips64 = create_mock_analysis(
            function_name="test_func",
            return_type="undefined4",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}]
        )
        
        mock_analysis_x86 = create_mock_analysis(
            function_name="test_func",
            return_type="undefined4",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}]
        )
        
        counterexample = {
            "param_1_1": 0x0000000080000001,
            "param_1_2": 0x80000001,
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
                    with patch.object(checker, '_retry_with_abi_constraints') as mock_retry:
                        mock_retry.return_value = create_mock_result(
                            is_equivalent=True, solver_status=SolverStatus.UNSAT
                        )
                        
                        result = checker.check_from_binaries(
                            mock_program_mips64, mock_program_x86,
                            "test_func", "test_func",
                            retry_with_type_fix=True
                        )
                        
                        assert mock_retry.called, \
                            f"[{phase_name}] _retry_with_abi_constraints should be called for spurious counterexample"
                        assert result.is_equivalent is True, \
                            f"[{phase_name}] Should resolve to EQUIVALENT after ABI retry"
                        
                        print(f"\n[{phase_name}] Phase 4-B correctly triggered after recovery SAT (spurious)")
                finally:
                    for p in patches:
                        p.stop()
    
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
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
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
                    with patch.object(checker, '_retry_with_abi_constraints') as mock_retry:
                        result = checker.check_from_binaries(
                            mock_program_mips64, mock_program_x86,
                            "test_func", "test_func",
                            retry_with_type_fix=True
                        )
                        
                        assert not mock_retry.called, \
                            f"[{phase_name}] _retry_with_abi_constraints should NOT be called for genuine counterexample"
                        assert result.is_equivalent is False, \
                            f"[{phase_name}] Should stop as NOT EQUIVALENT for genuine counterexample"
                        
                        print(f"\n[{phase_name}] Correctly stopped as NOT EQUIVALENT (genuine counterexample)")
                finally:
                    for p in patches:
                        p.stop()
