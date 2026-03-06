# -*- coding: utf-8 -*-
"""Phase遷移のリトライゲート（停止条件）テスト"""

import pytest
from unittest.mock import Mock

from scripts.function_tracer_pcode.equivalence.phases.handler import PhaseHandler, PhaseContext
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixerConfig, TypeFixResult
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.equivalence.counterexample import FormattedCounterexample

from conftest import create_mock_result, create_mock_analysis


class TestPhaseRetryGates:
    """リトライゲート（Phase遷移の停止条件）テスト"""
    
    def test_sat_result_stops_retry_immediately(self):
        """★ [P1] SAT結果は原則リトライ禁止（仕様に準拠）"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(is_equivalent=False, solver_status=SolverStatus.SAT)
        
        # ★ 修正: SAT時は should_retry() が False を返すべき
        should_retry = handler.should_retry(result)
        assert should_retry is False, \
            "SAT should stop retry immediately (spec: only P4B is exception)"
        
        print("\n[GATE CHECK] SAT result blocks retry to Phase 1-3")
    
    def test_unknown_result_allows_retry(self):
        """UNKNOWN結果はリトライ許可"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)
        
        should_retry = handler.should_retry(result)
        assert should_retry is True, "UNKNOWN should allow retry"
        
        reason = handler.get_retry_reason(result)
        assert reason == "UNKNOWN"
    
    def test_timeout_result_allows_retry(self):
        """TIMEOUT結果はリトライ許可"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(is_equivalent=None, solver_status=SolverStatus.TIMEOUT)
        
        should_retry = handler.should_retry(result)
        assert should_retry is True, "TIMEOUT should allow retry"
        
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
        assert "EQUIVALENT" in reason
    
    def test_mips64_spurious_counterexample_allows_phase4b(self, mock_program_mips64, mock_program_x86):
        """★ [P1] MIPS64偽反例検出時のみ、SAT後もPhase 4-Bへ進む"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        counterexample = {
            "param_1_1": 0xFFFFFFFF00000001,
            "param_1_2": 0x0000000000000001,
        }
        
        result = create_mock_result(
            is_equivalent=False,
            solver_status=SolverStatus.SAT,
            counterexample=counterexample
        )
        
        result.counterexample = FormattedCounterexample(
            parameters={
                "param_1_1": "0xffffffff00000001",
                "param_1_2": "0x0000000000000001",
            },
            return_value1=None,
            return_value2=None,
            raw_model=counterexample
        )
        
        analysis1 = create_mock_analysis(
            function_name="func1",
            parameters=[{"name": "param_1", "data_type": "int"}]
        )
        
        analysis2 = create_mock_analysis(
            function_name="func2",
            parameters=[{"name": "param_1", "data_type": "int"}]
        )
        
        ctx = PhaseContext(
            program1=mock_program_mips64,
            program2=mock_program_x86,
            function_name1="func1",
            function_name2="func2",
            binary1_name="mips64.elf",
            binary2_name="x86.exe",
            decompile_timeout=60,
            save_formula=False,
            type_fix_result=TypeFixResult(),
            original_signature1=None,
            original_signature2=None,
            analysis1=analysis1,
            analysis2=analysis2
        )
        
        from scripts.function_tracer_pcode.equivalence.arch.detector import ArchitectureDetector
        detector = ArchitectureDetector()
        is_mips64_1 = detector.is_mips64(ctx.program1)
        is_mips64_2 = detector.is_mips64(ctx.program2)
        
        print(f"\n[DEBUG] MIPS64 detection: program1={is_mips64_1}, program2={is_mips64_2}")
        
        # ★ [P1] 修正: スキップせず、検出失敗をテスト失敗として扱う
        assert (is_mips64_1 or is_mips64_2), \
            f"MIPS64 detection MUST work for mock_program_mips64 " \
            f"(got: program1={is_mips64_1}, program2={is_mips64_2})"
        
        can_retry = handler.should_run_phase4_retry(result, ctx)
        
        print(f"[DEBUG] should_run_phase4_retry returned: {can_retry}")
        
        assert can_retry is True, \
            f"MIPS64 with counterexample should allow Phase 4-B " \
            f"(is_mips64_1={is_mips64_1}, is_mips64_2={is_mips64_2})"
        
        abi_constraints = handler.run_phase4_mips64_retry(result, ctx)
        
        if abi_constraints:
            print(f"\n[SPURIOUS DETECTED] ABI constraints: {abi_constraints}")
        else:
            print("\n[GENUINE COUNTEREXAMPLE] No ABI violation detected")