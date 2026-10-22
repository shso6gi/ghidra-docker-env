# -*- coding: utf-8 -*-
"""Phase遷移のリトライゲート（停止条件）テスト"""

from unittest.mock import Mock

from scripts.function_tracer_pcode.checker.phases.handler import PhaseHandler
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixerConfig
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.core import Expression, ExpressionType

# ★ [P3] conftest からhelper関数をインポート（fixture化されているのでOK）
from conftest import create_mock_result

class TestPhaseRetryGates:
    """★ [P2] リトライゲート（should_retry）の責務分離テスト"""
    
    def test_sat_result_blocks_normal_retry(self):
        """★ [P2] SAT結果は should_retry=False （通常Recoveryブロック）"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(is_equivalent=False, solver_status=SolverStatus.SAT)
        
        should_retry = handler.should_retry(result)
        assert should_retry is False, \
            "SAT should block normal retry (P1/P2 recovery phases)"
        
        print("\n[GATE CHECK] SAT blocks normal retry to P1_SIGNEDNESS, P2_PATTERN_INT")
    
    def test_unknown_result_allows_normal_retry(self):
        """UNKNOWN結果は通常リトライ許可"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)
        
        should_retry = handler.should_retry(result)
        assert should_retry is True, "UNKNOWN should allow normal retry"
        
        reason = handler.get_retry_reason(result)
        assert reason == "UNKNOWN"
    
    def test_timeout_result_allows_normal_retry(self):
        """TIMEOUT結果は通常リトライ許可"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(is_equivalent=None, solver_status=SolverStatus.TIMEOUT)
        
        should_retry = handler.should_retry(result)
        assert should_retry is True, "TIMEOUT should allow normal retry"
        
        assert result.is_timeout() is True
        reason = handler.get_retry_reason(result)
        assert reason == "TIMEOUT"
    
    def test_unsat_result_stops_immediately(self):
        """UNSAT結果は即終了"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(is_equivalent=True, solver_status=SolverStatus.UNSAT)
        
        should_retry = handler.should_retry(result)
        assert should_retry is False, "UNSAT should stop retry"
        
        reason = handler.get_retry_reason(result)
        assert "EQUIVALENT" in reason or reason == "EQUIVALENT (no retry needed)"
    
    
    def test_critical_error_stops_all_retry(self):
        """致命的エラー → 全リトライ禁止"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(
            is_equivalent=None,
            error_message="Function 'test_func' not found in binary"
        )
        
        has_error = result.has_critical_error()
        assert has_error is True, "Function not found should be critical"
        
        should_retry = handler.should_retry(result)
        assert should_retry is False, "Critical error should stop all retry"
