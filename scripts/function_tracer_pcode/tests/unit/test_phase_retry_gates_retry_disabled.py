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

class TestRetryDisabledEarlyExit:
    """★ retry_with_type_fix=False の早期終了テスト（単発）"""
    
    def test_retry_disabled_exits_at_phase0_unknown(self, mock_program_mips64, mock_program_x86):
        """retry_with_type_fix=False では Phase 0 UNKNOWN で即終了し、recovery に入らない"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from unittest.mock import Mock, patch
        
        checker = EquivalenceChecker(debug=True, canonical_decision_cutover=False)
        
        mock_analysis = create_mock_analysis(
            function_name="test_func",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}]
        )
        
        with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
            mock_analyzer = Mock()
            mock_analyzer.analyze_function_by_name.return_value = mock_analysis
            mock_analyzer.dispose = Mock()
            mock_analyzer_class.return_value = mock_analyzer
            
            with patch.object(checker, 'check') as mock_check:
                mock_check.return_value = create_mock_result(
                    is_equivalent=None, solver_status=SolverStatus.UNKNOWN
                )
                
                # recovery phases がモニタリングされていることを確認
                with patch.object(checker.phase_handler, 'run_phase1_signedness_fix') as mock_p1, \
                     patch.object(checker.phase_handler, 'run_phase1_5_param_signedness_fix') as mock_p1_5, \
                     patch.object(checker.phase_handler, 'run_phase2_return_type_fix') as mock_p2, \
                     patch.object(checker.phase_handler, 'run_phase3_param_type_fix') as mock_p3, \
                     patch.object(checker.phase_handler, 'run_phase4_mips64_fix') as mock_p4a, \
                     patch.object(checker.phase_handler, 'run_phase4_mips64_retry') as mock_p4b:
                    
                    result = checker.check_from_binaries(
                        mock_program_mips64, mock_program_x86,
                        "test_func", "test_func",
                        retry_with_type_fix=False
                    )
                    
                    # Phase 0 UNKNOWN でそのまま終了
                    assert result.is_equivalent is None
                    
                    # recovery phases は一切呼ばれない
                    assert not mock_p1.called, "Phase 1 should NOT be called"
                    assert not mock_p1_5.called, "Phase 1.5 should NOT be called"
                    assert not mock_p2.called, "Phase 2 should NOT be called"
                    assert not mock_p3.called, "Phase 3 should NOT be called"
                    assert not mock_p4a.called, "Phase 4-A should NOT be called"
                    assert not mock_p4b.called, "Phase 4-B should NOT be called"
                    
                    print("\n[RETRY DISABLED] Correctly exited at Phase 0 UNKNOWN without entering recovery")
    
    def test_retry_disabled_exits_at_phase0_sat(self, mock_program_mips64, mock_program_x86):
        """retry_with_type_fix=False では Phase 0 SAT で即終了し、Phase 4-B も実行しない"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from unittest.mock import Mock, patch
        
        checker = EquivalenceChecker(debug=True, canonical_decision_cutover=False)
        
        mock_analysis = create_mock_analysis(
            function_name="test_func",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}]
        )
        
        counterexample = {
            "param_1_1": 0x0000000080000001,
            "param_1_2": 0x80000001,
        }
        
        with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
            mock_analyzer = Mock()
            mock_analyzer.analyze_function_by_name.return_value = mock_analysis
            mock_analyzer.dispose = Mock()
            mock_analyzer_class.return_value = mock_analyzer
            
            with patch.object(checker, 'check') as mock_check:
                mock_check.return_value = create_mock_result(
                    is_equivalent=False,
                    solver_status=SolverStatus.SAT,
                    counterexample=counterexample
                )
                
                with patch.object(checker.phase_handler, 'run_phase4_mips64_retry') as mock_p4b, \
                     patch.object(checker, '_retry_with_abi_constraints') as mock_retry:
                    
                    result = checker.check_from_binaries(
                        mock_program_mips64, mock_program_x86,
                        "test_func", "test_func",
                        retry_with_type_fix=False
                    )
                    
                    # Phase 0 SAT で終了
                    assert result.is_equivalent is False
                    
                    # Phase 4-B も ABI retry も呼ばれない
                    assert not mock_p4b.called, "Phase 4-B gate should NOT be called"
                    assert not mock_retry.called, "_retry_with_abi_constraints should NOT be called"
                    
                    print("\n[RETRY DISABLED] Correctly exited at Phase 0 SAT without Phase 4-B")
