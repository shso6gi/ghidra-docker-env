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

    def test_sat_after_phase4b_runs_return_type_fix_for_suspicious_return(
        self,
        mock_program_mips64,
        mock_program_x86,
    ):
        """Phase 4-B 後も SAT なら、undefined系戻り値に限って戻り値型修正を試す"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from unittest.mock import Mock, patch

        checker = EquivalenceChecker(debug=True)

        analysis1 = create_mock_analysis(
            function_name="test_func",
            return_type="undefined8",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}],
        )
        analysis2 = create_mock_analysis(
            function_name="test_func",
            return_type="undefined8",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}],
        )
        fixed_analysis1 = create_mock_analysis(
            function_name="test_func",
            return_type="int",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}],
        )
        fixed_analysis2 = create_mock_analysis(
            function_name="test_func",
            return_type="int",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}],
        )

        counterexample = {
            "param_1_1": 0xFFFFFFFF80000001,
            "param_1_2": 0x80000001,
        }

        with patch("scripts.function_tracer_pcode.analysis.ReturnAnalyzer") as mock_analyzer_class:
            mock_analyzer = Mock()
            mock_analyzer.analyze_function_by_name.side_effect = [analysis1, analysis2]
            mock_analyzer.dispose = Mock()
            mock_analyzer_class.return_value = mock_analyzer

            with patch.object(checker, "check") as mock_check, \
                 patch.object(
                     checker.phase_handler,
                     "run_phase4_mips64_retry",
                     return_value={"param_1_1": ("signed", 32)},
                 ) as mock_phase4b, \
                 patch.object(
                     checker,
                     "_retry_with_abi_constraints",
                     return_value=create_mock_result(
                         is_equivalent=False,
                         solver_status=SolverStatus.SAT,
                         counterexample=counterexample,
                     ),
                 ) as mock_retry, \
                 patch.object(
                     checker.phase_handler,
                     "run_phase2_return_type_fix",
                     return_value=(True, True, True),
                 ) as mock_p2, \
                 patch.object(
                     checker,
                     "_selective_reanalysis_and_check",
                     return_value=(
                         fixed_analysis1,
                         fixed_analysis2,
                         create_mock_result(
                             is_equivalent=True,
                             solver_status=SolverStatus.UNSAT,
                         ),
                     ),
                 ) as mock_reanalyze:
                mock_check.return_value = create_mock_result(
                    is_equivalent=False,
                    solver_status=SolverStatus.SAT,
                    counterexample=counterexample,
                )

                result = checker.check_from_binaries(
                    mock_program_mips64,
                    mock_program_x86,
                    "test_func",
                    "test_func",
                    retry_with_type_fix=True,
                )

                assert mock_phase4b.call_count >= 2
                assert mock_retry.called, "Phase 4-B ABI retry should run first"
                assert mock_p2.called, "Suspicious undefined return type should trigger Phase 4-C"
                assert mock_reanalyze.called, "Return type fix should re-analyze before re-check"
                assert result.is_equivalent is True

    def test_sat_after_phase4b_skips_return_type_fix_when_return_type_is_not_suspicious(
        self,
        mock_program_mips64,
        mock_program_x86,
    ):
        """Phase 4-B 後 SAT でも、戻り値型が怪しくないなら追加の戻り値修正はしない"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from unittest.mock import Mock, patch

        checker = EquivalenceChecker(debug=True)

        analysis1 = create_mock_analysis(
            function_name="test_func",
            return_type="int",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}],
        )
        analysis2 = create_mock_analysis(
            function_name="test_func",
            return_type="int",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}],
        )

        counterexample = {
            "param_1_1": 0xFFFFFFFF80000001,
            "param_1_2": 0x80000001,
        }

        with patch("scripts.function_tracer_pcode.analysis.ReturnAnalyzer") as mock_analyzer_class:
            mock_analyzer = Mock()
            mock_analyzer.analyze_function_by_name.side_effect = [analysis1, analysis2]
            mock_analyzer.dispose = Mock()
            mock_analyzer_class.return_value = mock_analyzer

            with patch.object(checker, "check") as mock_check, \
                 patch.object(
                     checker.phase_handler,
                     "run_phase4_mips64_retry",
                     return_value={"param_1_1": ("signed", 32)},
                 ) as mock_phase4b, \
                 patch.object(
                     checker,
                     "_retry_with_abi_constraints",
                     return_value=create_mock_result(
                         is_equivalent=False,
                         solver_status=SolverStatus.SAT,
                         counterexample=counterexample,
                     ),
                 ) as mock_retry, \
                 patch.object(checker.phase_handler, "run_phase2_return_type_fix") as mock_p2, \
                 patch.object(checker, "_selective_reanalysis_and_check") as mock_reanalyze:
                mock_check.return_value = create_mock_result(
                    is_equivalent=False,
                    solver_status=SolverStatus.SAT,
                    counterexample=counterexample,
                )

                result = checker.check_from_binaries(
                    mock_program_mips64,
                    mock_program_x86,
                    "test_func",
                    "test_func",
                    retry_with_type_fix=True,
                )

                assert mock_phase4b.call_count >= 2
                assert mock_retry.called, "Phase 4-B ABI retry should still run"
                mock_p2.assert_not_called()
                mock_reanalyze.assert_not_called()
                assert result.is_equivalent is False

    def test_sat_before_stop_runs_phase4a_tail_for_mips64_param_fix(
        self,
        mock_program_mips64,
        mock_program_x86,
    ):
        """SAT 停止直前に Phase 4-A を試し、MIPS64 引数型修正で解決できるようにする"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from scripts.function_tracer_pcode.equivalence.phases.handler import PhaseResult, PhaseID
        from unittest.mock import Mock, patch

        checker = EquivalenceChecker(debug=True)

        analysis1 = create_mock_analysis(
            function_name="test_func",
            return_type="int",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}],
        )
        analysis2 = create_mock_analysis(
            function_name="test_func",
            return_type="int",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}],
        )
        fixed_analysis1 = create_mock_analysis(
            function_name="test_func",
            return_type="int",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}],
        )
        fixed_analysis2 = create_mock_analysis(
            function_name="test_func",
            return_type="int",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}],
        )

        counterexample = {
            "param_1_1": 0xFFFFFFFF80000001,
            "param_1_2": 0x80000001,
        }

        with patch("scripts.function_tracer_pcode.analysis.ReturnAnalyzer") as mock_analyzer_class:
            mock_analyzer = Mock()
            mock_analyzer.analyze_function_by_name.side_effect = [analysis1, analysis2]
            mock_analyzer.dispose = Mock()
            mock_analyzer_class.return_value = mock_analyzer

            with patch.object(checker, "check") as mock_check, \
                 patch.object(
                     checker.phase_handler,
                     "run_phase4_mips64_retry",
                     return_value={"param_1_1": ("signed", 32)},
                 ) as mock_phase4b, \
                 patch.object(
                     checker,
                     "_retry_with_abi_constraints",
                     return_value=create_mock_result(
                         is_equivalent=False,
                         solver_status=SolverStatus.SAT,
                         counterexample=counterexample,
                     ),
                 ) as mock_retry, \
                 patch.object(checker.phase_handler, "run_phase2_return_type_fix") as mock_p2, \
                 patch.object(
                     checker.phase_handler,
                     "execute_phase",
                     return_value=PhaseResult(
                         PhaseID.P4A_MIPS64_ABI,
                         applied=True,
                         retry_name="mips64_abi_fix",
                         changed_binary1=True,
                         changed_binary2=False,
                     ),
                 ) as mock_execute_phase, \
                 patch.object(
                     checker,
                     "_selective_reanalysis_and_check",
                     return_value=(
                         fixed_analysis1,
                         fixed_analysis2,
                         create_mock_result(
                             is_equivalent=True,
                             solver_status=SolverStatus.UNSAT,
                         ),
                     ),
                 ) as mock_reanalyze:
                mock_check.return_value = create_mock_result(
                    is_equivalent=False,
                    solver_status=SolverStatus.SAT,
                    counterexample=counterexample,
                )

                result = checker.check_from_binaries(
                    mock_program_mips64,
                    mock_program_x86,
                    "test_func",
                    "test_func",
                    retry_with_type_fix=True,
                )

                assert mock_phase4b.call_count >= 2
                assert mock_retry.called
                mock_p2.assert_not_called()
                assert mock_execute_phase.called, "Phase 4-A tail should be attempted before SAT stop"
                assert mock_reanalyze.called
                assert result.is_equivalent is True

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
