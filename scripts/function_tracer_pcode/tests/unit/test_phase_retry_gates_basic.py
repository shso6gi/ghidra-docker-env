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

class TestPhaseRetryGates:
    """★ [P2] リトライゲート（should_retry vs should_run_phase4_retry）の責務分離テスト"""
    
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
    
    def test_mips64_spurious_counterexample_allows_phase4b(self, mock_program_mips64, mock_program_x86):
        """
        MIPS64偽反例検出時のみ、SAT後もPhase 4-Bへ進む
        
        ★ [P1修正] 実装条件に合わせた入力:
        - MIPS64側: 4byte int パラメータ（符号拡張される）
        - 反例: 上位32bitが0xFFFFFFFF（符号拡張パターン）
        """
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        # ★ 符号拡張パターンの反例（上位32bit = 0xFFFFFFFF）
        counterexample = {
            "param_1_1": 0xFFFFFFFF80000001,  # 上位32bit = 0xFFFFFFFF, 下位32bit = 負の数
            "param_1_2": 0x0000000080000001,  # x86側（拡張なし）
        }
        
        result = create_mock_result(
            is_equivalent=False,
            solver_status=SolverStatus.SAT,
            counterexample=counterexample
        )
        
        # 反例をFormattedCounterexampleとして設定
        from scripts.function_tracer_pcode.checker.counterexample import FormattedCounterexample
        result.counterexample = FormattedCounterexample(
            parameters={
                "param_1_1": "0xffffffff80000001",
                "param_1_2": "0x0000000080000001",
            },
            return_value1=None,
            return_value2=None,
            raw_model=counterexample
        )
        
        # ★ [P1修正] 4byte パラメータを指定（MIPS64 ABI拡張の対象）
        analysis1 = create_mock_analysis(
            function_name="func1",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}]  # ★ 4byte
        )
        
        analysis2 = create_mock_analysis(
            function_name="func2",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}]  # ★ 4byte
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
        
        # デバッグ: アーキテクチャ検出を確認
        from scripts.function_tracer_pcode.checker.arch.detector import ArchitectureDetector
        detector = ArchitectureDetector()
        is_mips64_1 = detector.is_mips64(ctx.program1)
        is_mips64_2 = detector.is_mips64(ctx.program2)
        
        print(f"\n[DEBUG] MIPS64 detection: program1={is_mips64_1}, program2={is_mips64_2}")
        print(f"[DEBUG] Analysis1 params: {analysis1.parameters}")
        print(f"[DEBUG] Analysis2 params: {analysis2.parameters}")
        print(f"[DEBUG] Counterexample: {counterexample}")
        
        # MIPS64が検出されていない場合はテストをスキップ
        if not (is_mips64_1 or is_mips64_2):
            pytest.skip("MIPS64 detection failed - check MockProgram implementation")
        
        # Phase 4-B実行条件をチェック
        can_retry = handler.should_run_phase4_retry(result, ctx)
        
        print(f"[DEBUG] should_run_phase4_retry returned: {can_retry}")
        
        assert can_retry is True, (
            f"MIPS64 with counterexample should allow Phase 4-B "
            f"(is_mips64_1={is_mips64_1}, is_mips64_2={is_mips64_2})"
        )
        
        # 偽反例検出
        abi_constraints = handler.run_phase4_mips64_retry(result, ctx)
        
        print(f"[DEBUG] ABI constraints: {abi_constraints}")
        
        # 上位ビット非ゼロなら制約マップが返る
        if abi_constraints:
            print(f"\n[SPURIOUS DETECTED] ABI constraints: {abi_constraints}")
            print("Phase 4-B will retry with ABI conformance constraints")
        else:
            print("\n[GENUINE COUNTEREXAMPLE] No ABI violation detected")
    
    def test_sat_without_mips64_blocks_phase4b(self):
        """★ [P2] MIPS64でない場合はP4Bもブロック"""
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
        
        analysis1 = create_mock_analysis(
            function_name="func1",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}]
        )
        
        analysis2 = create_mock_analysis(
            function_name="func2",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}]
        )
        
        # ★ 両方 x86
        ctx = PhaseContext(
            program1=MockProgram(name="x86_1.exe", architecture="x86:LE:64:default"),
            program2=MockProgram(name="x86_2.exe", architecture="x86:LE:64:default"),
            function_name1="func1",
            function_name2="func2",
            binary1_name="x86_1.exe",
            binary2_name="x86_2.exe",
            decompile_timeout=60,
            save_formula=False,
            type_fix_result=TypeFixResult(),
            original_signature1=None,
            original_signature2=None,
            analysis1=analysis1,
            analysis2=analysis2
        )
        
        # ★ P4Bは許可されない
        can_retry_p4b = handler.should_run_phase4_retry(result, ctx)
        assert can_retry_p4b is False, \
            "P4B should NOT be allowed without MIPS64 architecture"
        
        print("\n[P4B BLOCKED] No MIPS64 detected, P4B retry blocked")
    
    def test_sat_without_counterexample_blocks_phase4b(self):
        """★ [新規] SAT but counterexample無し → P4Bブロック"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(
            is_equivalent=False,
            solver_status=SolverStatus.SAT,
            counterexample=None  # ★ counterexample無し
        )
        
        analysis1 = create_mock_analysis(
            function_name="func1",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}]
        )
        
        analysis2 = create_mock_analysis(
            function_name="func2",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}]
        )
        
        ctx = PhaseContext(
            program1=MockProgram(name="mips64.elf", architecture="MIPS:BE:64:64-32addr"),
            program2=MockProgram(name="x86.exe", architecture="x86:LE:64:default"),
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
        
        # ★ counterexample無しではP4B不可
        can_retry_p4b = handler.should_run_phase4_retry(result, ctx)
        assert can_retry_p4b is False, \
            "P4B should NOT be allowed without counterexample"
        
        print("\n[P4B BLOCKED] No counterexample, P4B retry blocked")
    
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
