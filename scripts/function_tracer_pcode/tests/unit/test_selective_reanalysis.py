# -*- coding: utf-8 -*-
"""再解析キャッシュ（未変更側再利用）のユニットテスト"""

import pytest
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixer
from scripts.function_tracer_pcode.equivalence.phases.handler import PhaseHandler, PhaseResult, PhaseID
from scripts.function_tracer_pcode.model import Expression, ReturnInfo, SignatureHypothesis
from scripts.function_tracer_pcode.smt import SolverStatus

# ★ conftest から MockProgram、create_mock_analysis、create_mock_result をインポート
from conftest import MockProgram, create_mock_analysis, create_mock_result


class TestSelectiveReanalysis:
    """changed side だけ fresh reanalysis し、unchanged side を再利用することを検証"""
    
    @pytest.fixture
    def checker(self):
        """EquivalenceChecker（デバッグモード）"""
        return EquivalenceChecker(
            timeout=5,
            debug=True,
            enable_rewrite=False,
            strategy="pairwise"
        )
    
    @pytest.fixture
    def mock_program_x86(self):
        """x86バイナリのモック（conftest.MockProgram を使用）"""
        return MockProgram(name="test_binary.exe", architecture="x86:LE:64:default")
    
    def test_binary1_only_changed_should_reanalyze_only_binary1(
        self, checker, mock_program_x86, monkeypatch
    ):
        """binary1 だけ変更されたときに binary1 だけ再解析されることを検証"""
        
        # ★ conftest.create_mock_analysis を使用（return_type を反映）
        analysis1_initial = create_mock_analysis("func1", return_type="ulong")
        analysis2_initial = create_mock_analysis("func2", return_type="int")
        
        # Phase 1 後の binary1 の型が変更される
        analysis1_after_fix = create_mock_analysis("func1", return_type="long")
        
        # ReturnAnalyzer のモック
        analyze_call_count = {"binary1": 0, "binary2": 0}
        
        def mock_analyze_function_by_name(self, function_name, timeout):
            if function_name == "func1":
                analyze_call_count["binary1"] += 1
                if analyze_call_count["binary1"] == 1:
                    return analysis1_initial
                else:
                    return analysis1_after_fix
            elif function_name == "func2":
                analyze_call_count["binary2"] += 1
                return analysis2_initial
            return None
        
        # ReturnAnalyzer.analyze_function_by_name をパッチ
        with patch(
            'scripts.function_tracer_pcode.analysis.analyzer.ReturnAnalyzer.analyze_function_by_name',
            mock_analyze_function_by_name
        ):
            # PhaseHandler のモック
            phase_handler = Mock(spec=PhaseHandler)
            
            # Phase P1 が binary1 だけ変更したことを示す PhaseResult を返す
            phase_result_p1 = PhaseResult(
                phase_id=PhaseID.P1_SIGNEDNESS,
                applied=True,
                retry_name="signedness_fix",
                changed_binary1=True,
                changed_binary2=False
            )
            
            phase_handler.execute_phase.return_value = phase_result_p1
            # ★ 修正: Phase 0 後は True, Phase 1 後は False

            phase_handler.should_retry.side_effect = [True, False]
            phase_handler.get_retry_reason.side_effect = ["UNKNOWN", "UNKNOWN"]
            # ★ 修正: Phase 4-B が呼ばれないように None を明示
            phase_handler.run_phase4_mips64_retry.return_value = None
            
            # checker の phase_handler を差し替え
            checker.phase_handler = phase_handler
            
            # ★ 修正: pairwise と monolithic の両方をモック
            from scripts.function_tracer_pcode.equivalence.strategies.base import StrategyResult
            from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult
            
            strategy_result_unknown = StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[
                    SolverResult(
                        solver_name="mock",
                        status=SolverStatus.UNKNOWN,
                        elapsed_time=0.1
                    )
                ]),
                smt_formula="(mock smt)",
                counterexample_raw=None,
                return_var1="return_1",
                return_var2="return_2",
                constrained_fragments=[],
                total_pairs=1,
                unsat_pairs=0,
                sat_pairs=0,
                unknown_pairs=1,
                error_pairs=0,
                sat_pair_info=None
            )
            
            with patch.object(checker.pairwise_strategy, 'check', return_value=strategy_result_unknown):
                with patch.object(checker.monolithic_strategy, 'check', return_value=strategy_result_unknown):
                    # 実行
                    result = checker.check_from_binaries(
                        program1=mock_program_x86,
                        program2=mock_program_x86,
                        function_name1="func1",
                        function_name2="func2",
                        decompile_timeout=60,
                        save_formula=False,
                        retry_with_type_fix=True
                    )
        
        # 検証: changed 側だけ fresh reanalysis され、unchanged 側は再利用される
        assert analyze_call_count["binary1"] == 2, \
            f"binary1 should be reanalyzed once after the initial analysis, but was {analyze_call_count['binary1']}"
        assert analyze_call_count["binary2"] == 1, \
            f"binary2 should be reused without reanalysis, but was {analyze_call_count['binary2']}"

    def test_void_return_hypothesis_rewrites_artifact_return_values(self):
        analysis = create_mock_analysis(
            "sphbes",
            return_type="ulong",
            returns=[
                ReturnInfo(
                    address="0x1000",
                    value=Expression.parameter("param_2", index=1, size=8),
                    conditions=[],
                ),
                ReturnInfo(
                    address="0x1004",
                    value=Expression.variable("poststate_0_8", size=8),
                    conditions=[],
                ),
            ],
        )

        rewritten = analysis.with_signature_hypothesis(
            SignatureHypothesis(
                return_type_override="void",
                phase="P2_PATTERN_INT",
                reason="counterpart void return surface",
            )
        )

        assert rewritten.return_type == "void"
        assert [ret.value.name for ret in rewritten.returns] == ["void", "void"]
        assert all(getattr(ret.value.expr_type, "name", None) == "UNKNOWN" for ret in rewritten.returns)
    
    def test_both_binaries_changed_should_reanalyze_both(
        self, checker, mock_program_x86, monkeypatch
    ):
        """両側変更時は両側再解析されることを検証"""
        
        # ★ conftest.create_mock_analysis を使用
        analysis1_initial = create_mock_analysis("func1", return_type="ulong")
        analysis2_initial = create_mock_analysis("func2", return_type="ulong")
        
        analysis1_after_fix = create_mock_analysis("func1", return_type="long")
        analysis2_after_fix = create_mock_analysis("func2", return_type="long")
        
        # ReturnAnalyzer のモック
        analyze_call_count = {"binary1": 0, "binary2": 0}
        
        def mock_analyze_function_by_name(self, function_name, timeout):
            if function_name == "func1":
                analyze_call_count["binary1"] += 1
                if analyze_call_count["binary1"] == 1:
                    return analysis1_initial
                else:
                    return analysis1_after_fix
            elif function_name == "func2":
                analyze_call_count["binary2"] += 1
                if analyze_call_count["binary2"] == 1:
                    return analysis2_initial
                else:
                    return analysis2_after_fix
            return None
        
        # ReturnAnalyzer.analyze_function_by_name をパッチ
        with patch(
            'scripts.function_tracer_pcode.analysis.analyzer.ReturnAnalyzer.analyze_function_by_name',
            mock_analyze_function_by_name
        ):
            # PhaseHandler のモック
            phase_handler = Mock(spec=PhaseHandler)
            
            # Phase P1 が両側を変更したことを示す PhaseResult を返す
            phase_result_p1 = PhaseResult(
                phase_id=PhaseID.P1_SIGNEDNESS,
                applied=True,
                retry_name="signedness_fix",
                changed_binary1=True,
                changed_binary2=True
            )
            
            phase_handler.execute_phase.return_value = phase_result_p1
            # ★ 修正: Phase 0 後は True, Phase 1 後は False
            phase_handler.should_retry.side_effect = [True, False]
            phase_handler.get_retry_reason.side_effect = ["UNKNOWN", "UNKNOWN"]
            # ★ 修正: Phase 4-B が呼ばれないように None を明示
            phase_handler.run_phase4_mips64_retry.return_value = None
            
            # checker の phase_handler を差し替え
            checker.phase_handler = phase_handler
            
            # ★ 修正: pairwise と monolithic の両方をモック
            from scripts.function_tracer_pcode.equivalence.strategies.base import StrategyResult
            from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult
            
            strategy_result_unknown = StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[
                    SolverResult(
                        solver_name="mock",
                        status=SolverStatus.UNKNOWN,
                        elapsed_time=0.1
                    )
                ]),
                smt_formula="(mock smt)",
                counterexample_raw=None,
                return_var1="return_1",
                return_var2="return_2",
                constrained_fragments=[],
                total_pairs=1,
                unsat_pairs=0,
                sat_pairs=0,
                unknown_pairs=1,
                error_pairs=0,
                sat_pair_info=None
            )
            
            with patch.object(checker.pairwise_strategy, 'check', return_value=strategy_result_unknown):
                with patch.object(checker.monolithic_strategy, 'check', return_value=strategy_result_unknown):
                    # 実行
                    result = checker.check_from_binaries(
                        program1=mock_program_x86,
                        program2=mock_program_x86,
                        function_name1="func1",
                        function_name2="func2",
                        decompile_timeout=60,
                        save_formula=False,
                        retry_with_type_fix=True
                    )
        
        # 検証: 両側変更時は両側とも fresh reanalysis される
        assert analyze_call_count["binary1"] == 2, \
            f"binary1 should be reanalyzed once after the initial analysis, but was {analyze_call_count['binary1']}"
        assert analyze_call_count["binary2"] == 2, \
            f"binary2 should be reanalyzed once after the initial analysis, but was {analyze_call_count['binary2']}"
    
    def test_phase_result_applied_false_should_skip_recheck(
        self, checker, mock_program_x86
    ):
        """phase_result.applied == False のときは recheck 自体をスキップ"""
        
        analyze_call_count = {"binary1": 0, "binary2": 0}
        
        def mock_analyze_function_by_name(self, function_name, timeout):
            if function_name == "func1":
                analyze_call_count["binary1"] += 1
            elif function_name == "func2":
                analyze_call_count["binary2"] += 1
            return create_mock_analysis(function_name)
        
        with patch(
            'scripts.function_tracer_pcode.analysis.analyzer.ReturnAnalyzer.analyze_function_by_name',
            mock_analyze_function_by_name
        ):
            # PhaseHandler のモック
            phase_handler = Mock(spec=PhaseHandler)
            
            # Phase P1 が applied=False を返す（何も変更されていない）
            phase_result_p1 = PhaseResult(
                phase_id=PhaseID.P1_SIGNEDNESS,
                applied=False,
                retry_name="signedness_fix",
                changed_binary1=False,
                changed_binary2=False
            )
            
            phase_handler.execute_phase.return_value = phase_result_p1
            phase_handler.should_retry.return_value = False
            # ★ 修正: Phase 4-B が呼ばれないように None を明示
            phase_handler.run_phase4_mips64_retry.return_value = None
            
            checker.phase_handler = phase_handler
            
            from scripts.function_tracer_pcode.equivalence.strategies.base import StrategyResult
            from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult
            
            strategy_result_unknown = StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[
                    SolverResult(
                        solver_name="mock",
                        status=SolverStatus.UNKNOWN,
                        elapsed_time=0.1
                    )
                ]),
                smt_formula="(mock smt)",
                counterexample_raw=None,
                return_var1="return_1",
                return_var2="return_2",
                constrained_fragments=[],
                total_pairs=1,
                unsat_pairs=0,
                sat_pairs=0,
                unknown_pairs=1,
                error_pairs=0,
                sat_pair_info=None
            )
            
            with patch.object(checker.pairwise_strategy, 'check', return_value=strategy_result_unknown):
                with patch.object(checker.monolithic_strategy, 'check', return_value=strategy_result_unknown):
                    result = checker.check_from_binaries(
                        program1=mock_program_x86,
                        program2=mock_program_x86,
                        function_name1="func1",
                        function_name2="func2",
                        decompile_timeout=60,
                        save_formula=False,
                        retry_with_type_fix=True
                    )
        
        # 検証: P0 の初回解析のみ（P1 は applied=False なので再解析されない）
        assert analyze_call_count["binary1"] == 1, \
            f"binary1 should be analyzed only once (P0), but was {analyze_call_count['binary1']}"
        assert analyze_call_count["binary2"] == 1, \
            f"binary2 should be analyzed only once (P0), but was {analyze_call_count['binary2']}"
        

class TestSelectiveReanalysisIntegration:
    """Real PhaseHandler を使用した selective reanalysis + hypothesis replay の統合テスト"""
    
    @pytest.fixture
    def checker(self):
        """EquivalenceChecker（デバッグモード）"""
        return EquivalenceChecker(
            timeout=5,
            debug=True,
            enable_rewrite=False,
            strategy="pairwise"
        )
    
    @pytest.fixture
    def mock_program_x86(self):
        """x86バイナリのモック（conftest.MockProgram を使用）"""
        return MockProgram(name="test_binary.exe", architecture="x86:LE:64:default")
    
    def test_selective_reanalysis_with_real_phase_handler(
        self, checker, mock_program_x86
    ):
        """Real PhaseHandler で changed_binary1/2 が正しく設定され、未変更側が再利用されることを確認"""
        
        # モック解析結果
        analysis1_initial = create_mock_analysis("func1", return_type="ulong", signedness="signed")
        analysis2_initial = create_mock_analysis("func2", return_type="int")
        
        analysis1_after_fix = create_mock_analysis("func1", return_type="long", signedness="signed").with_signature_hypothesis(
            SignatureHypothesis(
                return_type_override="long",
                phase="P1_SIGNEDNESS",
                reason="integration_test_replay",
            )
        )
        
        # ReturnAnalyzer のモック
        analyze_call_count = {"binary1": 0, "binary2": 0}
        
        def mock_analyze_function_by_name(self, function_name, timeout):
            if function_name == "func1":
                analyze_call_count["binary1"] += 1
                return analysis1_initial
            elif function_name == "func2":
                analyze_call_count["binary2"] += 1
                return analysis2_initial
            return None
        
        # _run_stage_plan() を patch して、渡された analysis をキャプチャ
        captured_analyses = []
        refresh_call_count = {"binary1": 0, "binary2": 0}
        
        def mock_run_stage_plan(
            analysis1, analysis2,
            binary1_name, binary2_name,
            save_formula,
            type_fix_result=None,
            retry_count=0,
            original_signature1=None,
            original_signature2=None
        ):
            # 渡された analysis をキャプチャ
            captured_analyses.append((analysis1, analysis2, retry_count))
            
            # UNKNOWN を返す
            from scripts.function_tracer_pcode.equivalence.strategies.base import StrategyResult
            from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult
            
            return create_mock_result(
                is_equivalent=None,
                solver_status=SolverStatus.UNKNOWN
            )

        def mock_refresh_structural_recurrence_summary(self, analysis, timeout=60):
            if getattr(analysis, "signature_hypotheses", None):
                refresh_call_count["binary1"] += 1
            else:
                refresh_call_count["binary2"] += 1
            return analysis
        
        def mock_apply_analysis_fix_binary1(
            analysis,
            **kwargs,
        ):
            if kwargs.get("override_return_type_name") == "long":
                return (analysis1_after_fix, True, False)
            return (analysis, False, False)

        def mock_apply_analysis_fix_binary2(
            analysis,
            **kwargs,
        ):
            return (analysis, False, False)
        
        with patch(
            'scripts.function_tracer_pcode.analysis.analyzer.ReturnAnalyzer.analyze_function_by_name',
            mock_analyze_function_by_name
        ):
            with patch(
                'scripts.function_tracer_pcode.analysis.analyzer.ReturnAnalyzer.refresh_structural_recurrence_summary',
                mock_refresh_structural_recurrence_summary
            ):
                with patch.object(checker, '_run_stage_plan', side_effect=mock_run_stage_plan):
                    with patch('scripts.function_tracer_pcode.equivalence.checker.TypeFixer') as MockTypeFixer:
                        # TypeFixer インスタンスを作成
                        mock_type_fixer1 = Mock()
                        mock_type_fixer2 = Mock()

                        mock_type_fixer1.apply_analysis_signature_fix.side_effect = mock_apply_analysis_fix_binary1
                        mock_type_fixer2.apply_analysis_signature_fix.side_effect = mock_apply_analysis_fix_binary2

                        # TypeFixer() の呼び出しで適切なインスタンスを返す
                        def type_fixer_factory(program, config, debug=False):
                            if program == mock_program_x86:
                                # 最初の呼び出し（binary1）と2回目の呼び出し（binary2）を区別
                                if not hasattr(type_fixer_factory, 'call_count'):
                                    type_fixer_factory.call_count = 0
                                type_fixer_factory.call_count += 1

                                if type_fixer_factory.call_count == 1:
                                    return mock_type_fixer1
                                else:
                                    return mock_type_fixer2
                            return Mock()

                        MockTypeFixer.side_effect = type_fixer_factory

                        # 実行
                        result = checker.check_from_binaries(
                            program1=mock_program_x86,
                            program2=mock_program_x86,
                            function_name1="func1",
                            function_name2="func2",
                            decompile_timeout=60,
                            save_formula=False,
                            retry_with_type_fix=True
                        )
        
        # 検証1: changed 側だけ fresh reanalysis される
        assert analyze_call_count["binary1"] == 2, \
            f"binary1 should be reanalyzed once after the initial analysis, but was {analyze_call_count['binary1']}"
        assert analyze_call_count["binary2"] == 1, \
            f"binary2 should be reused without reanalysis, but was {analyze_call_count['binary2']}"
        
        # 検証2: _run_stage_plan() が 2回呼ばれている（P0, P1）
        assert len(captured_analyses) == 2, \
            f"_run_stage_plan should be called 2 times, but was {len(captured_analyses)}"
        
        # 検証3: Phase 0 (retry_count=0)
        analysis1_p0, analysis2_p0, retry_count_p0 = captured_analyses[0]
        assert retry_count_p0 == 0, "First call should be Phase 0"
        assert analysis1_p0 is analysis1_initial, "Phase 0: analysis1 should be initial"
        assert analysis2_p0 is analysis2_initial, "Phase 0: analysis2 should be initial"
        
        # 検証4: Phase 1 (retry_count=1) - binary1 は fresh analysis + hypothesis replay、binary2 は再利用
        analysis1_p1, analysis2_p1, retry_count_p1 = captured_analyses[1]
        assert retry_count_p1 == 1, "Second call should be Phase 1"
        assert analysis1_p1.return_type == analysis1_after_fix.return_type
        assert analysis1_p1.signature_hypotheses == analysis1_after_fix.signature_hypotheses
        assert analysis2_p1 is analysis2_initial, \
            "Phase 1: analysis2 should be REUSED (same object as Phase 0)"

        # 検証5: replay 後の changed 側だけ structural summary refresh が呼ばれる
        assert refresh_call_count["binary1"] == 1
        assert refresh_call_count["binary2"] == 0
        
        # 検証6: TypeFixer が binary1 のみ呼ばれた
        assert mock_type_fixer1.apply_analysis_signature_fix.called, \
            "TypeFixer for binary1 should be called"
