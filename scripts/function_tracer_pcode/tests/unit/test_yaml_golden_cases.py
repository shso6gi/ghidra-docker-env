# -*- coding: utf-8 -*-
"""★ [P3] YAMLゴールデンケースの網羅テスト"""

import pytest
from conftest import load_golden_cases, create_mock_result, create_mock_analysis, MockProgram

from scripts.function_tracer_pcode.checker.phases.handler import PhaseHandler, PhaseContext
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixerConfig, TypeFixResult


class TestYAMLGoldenCases:
    """cases.ymlの全ケースを網羅的にテスト"""
    
    @pytest.mark.parametrize("case", [
        pytest.param(case, id=case['id'])
        for case in load_golden_cases()
    ], indirect=False)
    def test_phase0_stop_after_policy(self, case, solver_status_map, is_equiv_map):
        """★ [P2] 修正: should_retry（通常ゲート）のみを検証"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        phase0 = case['phase0']
        expected = case['expected']
        
        status_str = phase0.get('status', 'UNKNOWN')
        is_equiv = is_equiv_map[status_str]
        status = solver_status_map[status_str]
        
        counterexample = phase0.get('counterexample')
        
        result = create_mock_result(
            is_equivalent=is_equiv,
            solver_status=status,
            counterexample=counterexample
        )
        
        should_retry = handler.should_retry(result)
        
        # ★ [P2] 修正: should_retry は SAT時に常にFalse（P4Bは別ゲート）
        if status_str == "SAT":
            assert should_retry is False, \
                f"Case {case['id']}: SAT always blocks normal retry (should_retry=False)"
        elif status_str == "UNSAT":
            assert should_retry is False, \
                f"Case {case['id']}: UNSAT stops immediately (should_retry=False)"
        else:  # UNKNOWN/TIMEOUT
            if expected['stop_after_phase0']:
                # 特殊ケース（YAMLで明示的に停止指定）
                pass
            else:
                assert should_retry is True, \
                    f"Case {case['id']}: UNKNOWN/TIMEOUT allows normal retry (should_retry=True)"
    
    @pytest.mark.parametrize("case", [
        pytest.param(case, id=case['id'])
        for case in load_golden_cases()
        if 'P4B_MIPS64_SPURIOUS' in case['expected'].get('allowed_recovery_phases', [])
    ], indirect=False)
    def test_phase4b_special_gate(self, case, solver_status_map, is_equiv_map):
        """★ [重要度2] 修正: P4B特殊ゲートの検証を厳格化"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        phase0 = case['phase0']
        expected = case['expected']
        
        status_str = phase0.get('status', 'UNKNOWN')
        is_equiv = is_equiv_map[status_str]
        status = solver_status_map[status_str]
        
        counterexample = phase0.get('counterexample')
        
        result = create_mock_result(
            is_equivalent=is_equiv,
            solver_status=status,
            counterexample=counterexample
        )
        
        # ★ P4BケースではSAT
        assert status_str == "SAT", \
            f"Case {case['id']}: P4B is only allowed for SAT results"
        
        # ★ MIPS64アーキテクチャを設定
        arch = case.get('architecture', {})
        binary1_arch = arch.get('binary1', 'x86:LE:64:default')
        binary2_arch = arch.get('binary2', 'x86:LE:64:default')
        
        # ★ proper な analysis を作成
        analysis1 = create_mock_analysis(
            function_name="func1",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}]
        )
        
        analysis2 = create_mock_analysis(
            function_name="func2",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8}]
        )
        
        ctx = PhaseContext(
            program1=MockProgram(name="binary1", architecture=binary1_arch),
            program2=MockProgram(name="binary2", architecture=binary2_arch),
            function_name1="func1",
            function_name2="func2",
            binary1_name="binary1",
            binary2_name="binary2",
            decompile_timeout=60,
            save_formula=False,
            type_fix_result=TypeFixResult(),
            original_signature1=None,
            original_signature2=None,
            analysis1=analysis1,
            analysis2=analysis2
        )
        
        # ★ 通常ゲートはブロック
        should_retry_normal = handler.should_retry(result)
        assert should_retry_normal is False, \
            f"Case {case['id']}: SAT blocks normal retry"
        
        # ★ [重要度2] 修正: P4B特殊ゲートの期待値を厳格にassert
        expected_phase4b = expected.get('phase4b_gate_allowed', True)  # デフォルトはTrue（後方互換）
        
        can_retry_p4b = handler.should_run_phase4_retry(result, ctx)
        
        assert can_retry_p4b is expected_phase4b, \
            f"Case {case['id']}: P4B gate should be {expected_phase4b}, got {can_retry_p4b}"
        
        print(f"\n[P4B GATE] Case {case['id']}: can_retry_p4b={can_retry_p4b} (expected={expected_phase4b})")
    
    @pytest.mark.parametrize("case", [
        pytest.param(case, id=case['id'])
        for case in load_golden_cases()
        if case.get('assumptions', {}).get('structural_match') is True
    ], indirect=False)
    def test_structural_match_cases_require_smt(self, case):
        """★ [P2] 構造一致ケースでもSMT確認が必須"""
        assumptions = case.get('assumptions', {})
        
        # 構造一致フラグがTrueのケース
        assert assumptions.get('structural_match') is True
        
        # SMT確認が必須
        assert assumptions.get('smt_confirmed_after_structural') is True, \
            f"Case {case['id']}: structural_match=True requires smt_confirmed_after_structural=True"
        
        print(f"\n[STRUCTURAL SAFETY] Case {case['id']}: SMT confirmation is mandatory")
    
    @pytest.mark.parametrize("case", [
        pytest.param(case, id=case['id'])
        for case in load_golden_cases()
        if 'required_stage_path' in case['expected']
    ], indirect=False)
    def test_required_stage_path(self, case, solver_status_map, is_equiv_map):
        """★ [P1/P2修正] Stage経路の実行時検証（本物のParallelResultを使用）"""
        from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
        from scripts.function_tracer_pcode.proof.strategies.base import StrategyResult
        from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
        from unittest.mock import Mock, patch
        
        expected = case['expected']
        required_stage_path = expected['required_stage_path']
        
        # Stage経路が定義されているケースでは、最低限のStageを通過する
        assert len(required_stage_path) >= 1, \
            f"Case {case['id']}: required_stage_path must have at least one stage"
        
        # ★ [P2追加] 実際に checker を実行して stage_path を検証
        checker_kwargs = {"debug": True}
        if "S_LOOP_TEMPLATE_ABSTRACTION" in required_stage_path:
            checker_kwargs["enable_template_abstraction"] = True
        checker = EquivalenceChecker(
            canonical_decision_cutover=False, **checker_kwargs
        )
        
        mock_analysis = create_mock_analysis(
            function_name="test_func",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}]
        )
        
        phase0 = case['phase0']
        status_str = phase0.get('status', 'UNKNOWN')
        is_equiv = is_equiv_map[status_str]
        status = solver_status_map[status_str]
        
        # ★ [P1修正] 本物の ParallelResult/SolverResult を作成する helper
        def create_strategy_result(is_equiv, status, counterexample=None):
            return StrategyResult(
                is_equivalent=is_equiv,
                solver_results=ParallelResult(results=[
                    SolverResult(
                        solver_name="test_solver",
                        status=status,
                        elapsed_time=0.1,
                        model=counterexample
                    )
                ]),
                smt_formula=None,
                counterexample_raw=counterexample,
                return_var1="return_1",
                return_var2="return_2",
                constrained_fragments=[],
                total_pairs=4 if is_equiv is not None else 0,
                unsat_pairs=4 if is_equiv is True else 0,
                sat_pairs=1 if is_equiv is False else 0,
                unknown_pairs=1 if is_equiv is None else 0,
                error_pairs=0,
                sat_pair_info={"i": 0, "j": 0} if is_equiv is False else None
            )
        
        with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
            mock_analyzer = Mock()
            mock_analyzer.analyze_function_by_name.return_value = mock_analysis
            mock_analyzer.dispose = Mock()
            mock_analyzer_class.return_value = mock_analyzer
            
            with patch.object(checker.pairwise_strategy, 'check') as mock_pairwise:
                # ★ [P2追加] TIMEOUT 分岐を追加
                result = None  # 初期化
                
                if status_str == "UNSAT":
                    # S_PAIRWISE で UNSAT → 即終了
                    mock_pairwise.return_value = create_strategy_result(
                        is_equiv=True, status=SolverStatus.UNSAT
                    )
                    
                    result = checker.check_from_binaries(
                        MockProgram(name="binary1", architecture="x86:LE:64:default"),
                        MockProgram(name="binary2", architecture="x86:LE:64:default"),
                        "test_func",
                        "test_func",
                        retry_with_type_fix=False
                    )
                    
                    # expected stage_path と比較
                    assert result.stage_path == required_stage_path, \
                        f"Case {case['id']}: expected stage_path={required_stage_path}, got {result.stage_path}"
                
                elif status_str == "SAT":
                    # S_PAIRWISE で SAT → 即終了
                    counterexample = phase0.get('counterexample', {"param_1_1": 1, "param_1_2": 2})
                    mock_pairwise.return_value = create_strategy_result(
                        is_equiv=False,
                        status=SolverStatus.SAT,
                        counterexample=counterexample
                    )
                    
                    result = checker.check_from_binaries(
                        MockProgram(name="binary1", architecture="x86:LE:64:default"),
                        MockProgram(name="binary2", architecture="x86:LE:64:default"),
                        "test_func",
                        "test_func",
                        retry_with_type_fix=False
                    )
                    
                    # expected stage_path と比較
                    assert result.stage_path == required_stage_path, \
                        f"Case {case['id']}: expected stage_path={required_stage_path}, got {result.stage_path}"
                
                elif status_str in ("UNKNOWN", "TIMEOUT"):
                    # S_PAIRWISE で UNKNOWN/TIMEOUT → S_MONOLITHIC_FALLBACK へ
                    mock_pairwise.return_value = create_strategy_result(
                        is_equiv=None, status=status
                    )
                    
                    # monolithic も UNKNOWN/TIMEOUT を返す
                    with patch.object(checker.monolithic_strategy, 'check') as mock_monolithic:
                        mock_monolithic.return_value = create_strategy_result(
                            is_equiv=None, status=status
                        )
                        
                        result = checker.check_from_binaries(
                            MockProgram(name="binary1", architecture="x86:LE:64:default"),
                            MockProgram(name="binary2", architecture="x86:LE:64:default"),
                            "test_func",
                            "test_func",
                            retry_with_type_fix=False
                        )
                        
                        # expected stage_path と比較
                        assert result.stage_path == required_stage_path, \
                            f"Case {case['id']}: expected stage_path={required_stage_path}, got {result.stage_path}"
                
                else:
                    pytest.fail(f"Case {case['id']}: Unknown status '{status_str}'")
                
                # ★ result が None でないことを確認
                assert result is not None, f"Case {case['id']}: result should not be None"
                
                print(f"\n[STAGE PATH VERIFIED] Case {case['id']}: {result.stage_path}")


class TestMonolithicStrategyBackwardCompatibility:
    """strategy="monolithic" の後方互換性テスト"""
    
    def test_monolithic_strategy_skips_pairwise(self):
        """★ [P2] strategy="monolithic" なら pairwise が呼ばれない"""
        from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
        from scripts.function_tracer_pcode.proof.strategies.base import StrategyResult
        from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
        from unittest.mock import Mock, patch
        
        # monolithic strategy で初期化
        checker = EquivalenceChecker(
            strategy="monolithic", debug=True, canonical_decision_cutover=False
        )
        
        # stage_plan が monolithic のみであることを確認
        assert len(checker.stage_plan) == 1
        assert checker.stage_plan[0].stage_id.value == "S_MONOLITHIC_FALLBACK"
        assert checker.stage_plan[0].strategy == "monolithic"
        
        mock_analysis = create_mock_analysis(
            function_name="test_func",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4}]
        )
        
        with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
            mock_analyzer = Mock()
            mock_analyzer.analyze_function_by_name.return_value = mock_analysis
            mock_analyzer.dispose = Mock()
            mock_analyzer_class.return_value = mock_analyzer
            
            # monolithic strategy の check をモック化
            with patch.object(checker.monolithic_strategy, 'check') as mock_monolithic:
                monolithic_result = StrategyResult(
                    is_equivalent=True,
                    solver_results=ParallelResult(results=[
                        SolverResult(
                            solver_name="monolithic",
                            status=SolverStatus.UNSAT,
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
                
                # pairwise strategy をモニタリング
                with patch.object(checker.pairwise_strategy, 'check') as mock_pairwise:
                    result = checker.check_from_binaries(
                        MockProgram(name="binary1", architecture="x86:LE:64:default"),
                        MockProgram(name="binary2", architecture="x86:LE:64:default"),
                        "test_func",
                        "test_func",
                        retry_with_type_fix=False
                    )
                    
                    # pairwise が呼ばれていないことを確認
                    assert not mock_pairwise.called, \
                        "Pairwise strategy should NOT be called when strategy='monolithic'"
                    
                    # monolithic が呼ばれたことを確認
                    assert mock_monolithic.called, \
                        "Monolithic strategy should be called when strategy='monolithic'"
                    
                    # stage_path が S_MONOLITHIC_FALLBACK のみであることを確認
                    assert result.stage_path == ['S_MONOLITHIC_FALLBACK'], \
                        f"Expected stage_path=['S_MONOLITHIC_FALLBACK'], got {result.stage_path}"
                    
                    # 結果が EQUIVALENT であることを確認
                    assert result.is_equivalent is True
                    
                    print("\n[MONOLITHIC STRATEGY] Pairwise was correctly skipped, only monolithic was called")

    def test_monolithic_strategy_uses_extended_formula_result(self):
        """monolithic 戦略は FormulaBuilderResult を使って詳細情報を受け取る"""
        from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy
        from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilderResult
        from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
        from unittest.mock import ANY, Mock
        from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
            InputCorrespondenceStatus,
        )
        from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import (
            echo_input_correspondence,
        )

        formula_builder = echo_input_correspondence(Mock())
        formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
            formula="(set-logic QF_BV)\n(check-sat)",
            return_var1="return_1",
            return_var2="return_2",
            extra_vars1=[],
            extra_vars2=[],
            constrained_fragments=["param_2_hi"],
            param_fragment_constrained=["param_2_hi"],
        )
        solver_runner = Mock()
        solver_runner.run_parallel.return_value = ParallelResult(
            results=[
                SolverResult(
                    solver_name="z3",
                    status=SolverStatus.UNSAT,
                    elapsed_time=0.01,
                )
            ]
        )

        strategy = MonolithicStrategy(formula_builder, solver_runner, debug=False)
        analysis1 = create_mock_analysis(function_name="func1")
        analysis2 = create_mock_analysis(function_name="func2")

        result = strategy.check(analysis1, analysis2)

        formula_builder.build_equivalence_formula_extended.assert_called_once_with(
            analysis1, analysis2, input_correspondence=ANY
        )
        # Issue #167: 両側 0 parameter の EMPTY は十分（decisive gate を通る）。
        passed = formula_builder.build_equivalence_formula_extended.call_args.kwargs[
            "input_correspondence"
        ]
        assert passed.status is InputCorrespondenceStatus.EMPTY
        assert result.is_equivalent is True
        assert result.smt_formula == "(set-logic QF_BV)\n(check-sat)"
        assert result.return_var1 == "return_1"
        assert result.return_var2 == "return_2"
        assert result.constrained_fragments == ["param_2_hi"]
    
    def test_pairwise_strategy_defaults_to_three_stages(self):
        """strategy="pairwise" の既定は pairwise -> abstraction -> monolithic"""
        from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
        
        # pairwise strategy で初期化
        checker = EquivalenceChecker(
            strategy="pairwise", debug=True, canonical_decision_cutover=False
        )
        
        assert len(checker.stage_plan) == 3
        assert checker.stage_plan[0].stage_id.value == "S_PAIRWISE"
        assert checker.stage_plan[0].strategy == "pairwise"
        assert checker.stage_plan[1].stage_id.value == "S_ABSTRACT_RECURSIVE_SUMMARY"
        assert checker.stage_plan[1].strategy == "abstract_pairwise"
        assert checker.stage_plan[2].stage_id.value == "S_MONOLITHIC_FALLBACK"
        assert checker.stage_plan[2].strategy == "monolithic"

        print("\n[PAIRWISE STRATEGY] default 3-stage plan (pairwise -> abstraction -> monolithic fallback) is configured")

    def test_pairwise_strategy_can_enable_loop_template_stage(self):
        """template abstraction は opt-in でだけ stage plan に入る"""
        from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker

        checker = EquivalenceChecker(
            strategy="pairwise",
            debug=True,
            enable_template_abstraction=True,
            canonical_decision_cutover=False,
        )

        assert len(checker.stage_plan) == 4
        assert checker.stage_plan[1].stage_id.value == "S_LOOP_TEMPLATE_ABSTRACTION"
        assert checker.stage_plan[1].strategy == "loop_template_pairwise"
