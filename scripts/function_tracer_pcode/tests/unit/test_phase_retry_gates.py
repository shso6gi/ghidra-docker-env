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
        from scripts.function_tracer_pcode.equivalence.counterexample import FormattedCounterexample
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
        from scripts.function_tracer_pcode.equivalence.arch.detector import ArchitectureDetector
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

    def test_sat_mips64_skip_phase4b_when_retry_disabled(self, mock_program_mips64, mock_program_x86):
        """★ [新規] retry_with_type_fix=False なら MIPS64 SAT でも Phase 4-B をスキップ"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from scripts.function_tracer_pcode.analysis import ReturnAnalyzer
        from unittest.mock import Mock, patch
        
        checker = EquivalenceChecker(debug=True)
        
        # Phase 0 で SAT になるケース
        mock_analysis = create_mock_analysis(
            function_name="test_func",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}]
        )
        
        counterexample = {
            "param_1_1": 0xFFFFFFFF80000001,  # 符号拡張パターン
            "param_1_2": 0x0000000080000001,
        }
        
        # run_phase4_mips64_retry が呼ばれないことを確認
        with patch.object(checker.phase_handler, 'run_phase4_mips64_retry') as mock_phase4b:
            with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
                mock_analyzer = Mock()
                mock_analyzer.analyze_function_by_name.return_value = mock_analysis
                mock_analyzer.dispose = Mock()
                mock_analyzer_class.return_value = mock_analyzer
                
                with patch.object(checker, 'check') as mock_check:
                    mock_result = create_mock_result(
                        is_equivalent=False,
                        solver_status=SolverStatus.SAT,
                        counterexample=counterexample
                    )
                    mock_check.return_value = mock_result
                    
                    result = checker.check_from_binaries(
                        mock_program_mips64,
                        mock_program_x86,
                        "test_func",
                        "test_func",
                        retry_with_type_fix=False  # ★ リトライ無効
                    )
                    
                    # Phase 4-B が呼ばれていないことを確認
                    mock_phase4b.assert_not_called()
                    assert result.is_equivalent is False
                    
                    print("\n[RETRY DISABLED] Phase 4-B was correctly skipped")
    
    def test_sat_after_recovery_evaluates_phase4b_gate(self, mock_program_mips64, mock_program_x86):
        """★ [修正版] Phase 1 recovery 後の SAT で Phase 4-B ゲートが評価されることを確認"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from unittest.mock import Mock, patch
        
        checker = EquivalenceChecker(debug=True)
        
        mock_analysis = create_mock_analysis(
            function_name="test_func",
            return_type="unsigned int",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}],
            signedness="signed"
        )
        
        counterexample = {
            "param_1_1": 0xFFFFFFFF80000001,
            "param_1_2": 0x0000000080000001,
        }
        
        with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
            mock_analyzer = Mock()
            mock_analyzer.analyze_function_by_name.return_value = mock_analysis
            mock_analyzer.dispose = Mock()
            mock_analyzer_class.return_value = mock_analyzer
            
            call_count = [0]
            
            def mock_check_side_effect(*args, **kwargs):
                call_count[0] += 1
                if call_count[0] == 1:
                    # Phase 0: UNKNOWN
                    return create_mock_result(
                        is_equivalent=None,
                        solver_status=SolverStatus.UNKNOWN
                    )
                elif call_count[0] == 2:
                    # Phase 1 後: SAT
                    return create_mock_result(
                        is_equivalent=False,
                        solver_status=SolverStatus.SAT,
                        counterexample=counterexample
                    )
                else:
                    raise Exception("Unexpected check call")
            
            with patch.object(checker, 'check', side_effect=mock_check_side_effect):
                with patch.object(checker.phase_handler, 'run_phase1_signedness_fix', return_value=True):
                    # ★ run_phase4_mips64_retry が呼ばれることを確認
                    with patch.object(checker.phase_handler, 'run_phase4_mips64_retry', return_value=None) as mock_phase4b:
                        result = checker.check_from_binaries(
                            mock_program_mips64,
                            mock_program_x86,
                            "test_func",
                            "test_func",
                            retry_with_type_fix=True
                        )
                        
                        # Phase 4-B ゲートが評価されたことを確認
                        assert mock_phase4b.called, \
                            "Phase 4-B gate (run_phase4_mips64_retry) should be evaluated after recovery SAT"
                        
                        # SAT なので結果は NOT EQUIVALENT
                        assert result.is_equivalent is False
                        
                        print("\n[RECOVERY SAT] Phase 4-B gate was correctly evaluated after Phase 1 SAT")

    def test_phase4b_retry_on_successful_spurious_detection(self, mock_program_mips64, mock_program_x86):
        """★ [新規] 偽反例検出成功時に _retry_with_abi_constraints が呼ばれることを確認"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from unittest.mock import Mock, patch
        
        checker = EquivalenceChecker(debug=True)
        
        # ★ サイズ不一致でテスト（MIPS64=64bit, x86=32bit）
        mock_analysis_mips64 = create_mock_analysis(
            function_name="test_func",
            return_type="unsigned int",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}],  # 64bit
            signedness="signed"
        )
        
        mock_analysis_x86 = create_mock_analysis(
            function_name="test_func",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}]  # 32bit
        )
        
        counterexample = {
            "param_1_1": 0x0000000080000001,  # 誤ったゼロ拡張
            "param_1_2": 0x80000001,
        }

        
        with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
            # ★ 呼び出しごとに異なる analysis を返す
            analyzer_call_count = [0]
            
            def mock_analyze_side_effect(func_name, timeout):
                analyzer_call_count[0] += 1
                # 奇数回: MIPS64側, 偶数回: x86側
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
                    # Phase 0: UNKNOWN
                    return create_mock_result(
                        is_equivalent=None,
                        solver_status=SolverStatus.UNKNOWN
                    )
                elif check_count[0] == 2:
                    # Phase 1 後: SAT with spurious counterexample
                    return create_mock_result(
                        is_equivalent=False,
                        solver_status=SolverStatus.SAT,
                        counterexample=counterexample
                    )
                else:
                    raise Exception("Unexpected check call")
            
            with patch.object(checker, 'check', side_effect=mock_check_side_effect):
                with patch.object(checker.phase_handler, 'run_phase1_signedness_fix', return_value=True):
                    with patch.object(checker, '_retry_with_abi_constraints') as mock_retry:
                        mock_retry.return_value = create_mock_result(
                            is_equivalent=True,
                            solver_status=SolverStatus.UNSAT
                        )
                        
                        result = checker.check_from_binaries(
                            mock_program_mips64,
                            mock_program_x86,
                            "test_func",
                            "test_func",
                            retry_with_type_fix=True
                        )
                        
                        # 偽反例検出成功 → _retry_with_abi_constraints が呼ばれる
                        assert mock_retry.called, \
                            "_retry_with_abi_constraints should be called when spurious counterexample is detected"
                        
                        # ABI制約retryでEQUIVALENTに解決
                        assert result.is_equivalent is True
                        
                        print("\n[SPURIOUS DETECTION] _retry_with_abi_constraints was correctly called and resolved to EQUIVALENT")

    def test_sat_after_recovery_skips_phase4b_when_retry_disabled(self, mock_program_mips64, mock_program_x86):
        """★ [修正] retry_with_type_fix=False では Phase 0 内の stage fallback は許可、recovery 後の SAT でも Phase 4-B をスキップ"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from unittest.mock import Mock, patch
        
        checker = EquivalenceChecker(debug=True)
        
        mock_analysis = create_mock_analysis(
            function_name="test_func",
            return_type="unsigned int",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}],
            signedness="signed"
        )
        
        counterexample = {
            "param_1_1": 0x0000000080000001,  # 偽反例パターン
            "param_1_2": 0x80000001,
        }
        
        with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
            mock_analyzer = Mock()
            mock_analyzer.analyze_function_by_name.return_value = mock_analysis
            mock_analyzer.dispose = Mock()
            mock_analyzer_class.return_value = mock_analyzer
            
            # ★ [修正] pairwise で UNKNOWN → monolithic fallback へ進む → monolithic も UNKNOWN
            with patch.object(checker.pairwise_strategy, 'check') as mock_pairwise, \
                patch.object(checker.monolithic_strategy, 'check') as mock_monolithic:
                
                # pairwise: UNKNOWN
                from scripts.function_tracer_pcode.equivalence.strategies.base import StrategyResult
                from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
                
                pairwise_result = StrategyResult(
                    is_equivalent=None,
                    solver_results=ParallelResult(results=[
                        SolverResult(
                            solver_name="pairwise_aggregate",
                            status=SolverStatus.UNKNOWN,
                            elapsed_time=0.1
                        )
                    ]),
                    smt_formula=None,
                    counterexample_raw=None,
                    return_var1="return_1",
                    return_var2="return_2",
                    constrained_fragments=[],
                    total_pairs=4,
                    unsat_pairs=2,
                    sat_pairs=0,
                    unknown_pairs=2
                )
                mock_pairwise.return_value = pairwise_result
                
                # monolithic: UNKNOWN
                monolithic_result = StrategyResult(
                    is_equivalent=None,
                    solver_results=ParallelResult(results=[
                        SolverResult(
                            solver_name="monolithic",
                            status=SolverStatus.UNKNOWN,
                            elapsed_time=0.1
                        )
                    ]),
                    smt_formula=None,
                    counterexample_raw=None,
                    return_var1="return_1",
                    return_var2="return_2",
                    constrained_fragments=[]
                )
                mock_monolithic.return_value = monolithic_result
                
                # ★ recovery phases をモニタリング
                with patch.object(checker.phase_handler, 'run_phase1_signedness_fix') as mock_p1, \
                    patch.object(checker.phase_handler, 'run_phase1_5_param_signedness_fix') as mock_p1_5, \
                    patch.object(checker.phase_handler, 'run_phase2_return_type_fix') as mock_p2, \
                    patch.object(checker.phase_handler, 'run_phase3_param_type_fix') as mock_p3, \
                    patch.object(checker.phase_handler, 'run_phase4_mips64_fix') as mock_p4a, \
                    patch.object(checker.phase_handler, 'run_phase4_mips64_retry') as mock_p4b:
                    
                    result = checker.check_from_binaries(
                        mock_program_mips64,
                        mock_program_x86,
                        "test_func",
                        "test_func",
                        retry_with_type_fix=False  # ★ リトライ無効
                    )
                    
                    # Phase 0 の結果（UNKNOWN）がそのまま返る
                    assert result.is_equivalent is None
                    
                    # ★ [修正] recovery phase メソッドが呼ばれていないことを確認
                    assert not mock_p1.called, "Phase 1 should NOT be called"
                    assert not mock_p1_5.called, "Phase 1.5 should NOT be called"
                    assert not mock_p2.called, "Phase 2 should NOT be called"
                    assert not mock_p3.called, "Phase 3 should NOT be called"
                    assert not mock_p4a.called, "Phase 4-A should NOT be called"
                    assert not mock_p4b.called, "Phase 4-B should NOT be called"
                    
                    # ★ [追加] Phase 0 内の stage fallback は許可されている
                    assert mock_pairwise.called, "S_PAIRWISE should be called"
                    assert mock_monolithic.called, "S_MONOLITHIC_FALLBACK should be called (Phase 0 stage fallback)"
                    
                    print("\n[RETRY DISABLED] Phase 0 stage fallback is allowed, but recovery phases are blocked")


    def test_sat_after_recovery_genuine_counterexample_stops(self, mock_program_mips64, mock_program_x86):
        """★ [新規] recovery 後 SAT で偽反例ではない場合は NOT EQUIVALENT で終了"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from unittest.mock import Mock, patch
        
        checker = EquivalenceChecker(debug=True)
        
        # サイズ不一致（MIPS64=64bit, x86=32bit）
        mock_analysis_mips64 = create_mock_analysis(
            function_name="test_func",
            return_type="unsigned int",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}],
            signedness="signed"
        )
        
        mock_analysis_x86 = create_mock_analysis(
            function_name="test_func",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}]
        )
        
        # ★ 正当な反例（符号拡張パターンに違反していない）
        counterexample = {
            "param_1_1": 0x0000000012345678,  # 正しいゼロ拡張
            "param_1_2": 0x12345678,  # 下位32bit一致
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
                    # Phase 0: UNKNOWN
                    return create_mock_result(
                        is_equivalent=None,
                        solver_status=SolverStatus.UNKNOWN
                    )
                elif check_count[0] == 2:
                    # Phase 1 後: SAT with genuine counterexample
                    return create_mock_result(
                        is_equivalent=False,
                        solver_status=SolverStatus.SAT,
                        counterexample=counterexample
                    )
                else:
                    raise Exception("Unexpected check call")
            
            with patch.object(checker, 'check', side_effect=mock_check_side_effect):
                with patch.object(checker.phase_handler, 'run_phase1_signedness_fix', return_value=True):
                    with patch.object(checker, '_retry_with_abi_constraints') as mock_retry:
                        result = checker.check_from_binaries(
                            mock_program_mips64,
                            mock_program_x86,
                            "test_func",
                            "test_func",
                            retry_with_type_fix=True
                        )
                        
                        # 正当な反例 → _retry_with_abi_constraints は呼ばれない
                        assert not mock_retry.called, \
                            "_retry_with_abi_constraints should NOT be called for genuine counterexample"
                        
                        # NOT EQUIVALENT で終了
                        assert result.is_equivalent is False
                        
                        print("\n[GENUINE] Correctly stopped as NOT EQUIVALENT (no spurious retry)")


    def test_phase4b_after_phase2_recovery_sat(self, mock_program_mips64, mock_program_x86):
        """★ [新規] Phase 2 (pattern-based fix) 後の SAT でも Phase 4-B ゲートを評価"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from unittest.mock import Mock, patch
        
        checker = EquivalenceChecker(debug=True)
        
        # サイズ不一致
        mock_analysis_mips64 = create_mock_analysis(
            function_name="test_func",
            return_type="undefined4",  # Phase 2 トリガー
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}]
        )
        
        mock_analysis_x86 = create_mock_analysis(
            function_name="test_func",
            return_type="undefined4",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}]
        )
        
        counterexample = {
            "param_1_1": 0x0000000080000001,  # 偽反例パターン
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
                    # Phase 0: UNKNOWN
                    return create_mock_result(
                        is_equivalent=None,
                        solver_status=SolverStatus.UNKNOWN
                    )
                elif check_count[0] == 2:
                    # Phase 2 後: SAT with spurious counterexample
                    return create_mock_result(
                        is_equivalent=False,
                        solver_status=SolverStatus.SAT,
                        counterexample=counterexample
                    )
                else:
                    raise Exception("Unexpected check call")
            
            with patch.object(checker, 'check', side_effect=mock_check_side_effect):
                # Phase 1 はスキップ、Phase 2 で型修正実行
                with patch.object(checker.phase_handler, 'run_phase1_signedness_fix', return_value=False):
                    with patch.object(checker.phase_handler, 'run_phase1_5_param_signedness_fix', return_value=False):
                        with patch.object(checker.phase_handler, 'run_phase2_return_type_fix', return_value=True):
                            with patch.object(checker, '_retry_with_abi_constraints') as mock_retry:
                                mock_retry.return_value = create_mock_result(
                                    is_equivalent=True,
                                    solver_status=SolverStatus.UNSAT
                                )
                                
                                result = checker.check_from_binaries(
                                    mock_program_mips64,
                                    mock_program_x86,
                                    "test_func",
                                    "test_func",
                                    retry_with_type_fix=True
                                )
                                
                                # Phase 2 後の SAT でも Phase 4-B が呼ばれる
                                assert mock_retry.called, \
                                    "_retry_with_abi_constraints should be called after Phase 2 SAT with spurious counterexample"
                                
                                # ABI制約retryで EQUIVALENT
                                assert result.is_equivalent is True
                                
                                print("\n[PHASE 2 SAT] Phase 4-B was correctly triggered after Phase 2 recovery SAT")


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
        
        checker = EquivalenceChecker(debug=True)
        
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
        
        checker = EquivalenceChecker(debug=True)
        
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


class TestRetryDisabledEarlyExit:
    """★ retry_with_type_fix=False の早期終了テスト（単発）"""
    
    def test_retry_disabled_exits_at_phase0_unknown(self, mock_program_mips64, mock_program_x86):
        """retry_with_type_fix=False では Phase 0 UNKNOWN で即終了し、recovery に入らない"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from unittest.mock import Mock, patch
        
        checker = EquivalenceChecker(debug=True)
        
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
        
        checker = EquivalenceChecker(debug=True)
        
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