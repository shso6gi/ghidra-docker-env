# -*- coding: utf-8 -*-
"""デバッグトレース統合テスト（既存テストとの互換性確認）"""

import pytest
from unittest.mock import Mock, patch
from scripts.function_tracer_pcode.equivalence import EquivalenceChecker
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.equivalence.strategies.base import StrategyResult
from scripts.function_tracer_pcode.model import FunctionReturnAnalysis, ReturnInfo, Expression, ExpressionType


def test_stage_path_still_recorded(mock_program_x86):
    """既存の stage_path テストが壊れていないことを確認"""
    checker = EquivalenceChecker(
        debug=False,
        strategy="pairwise",
        canonical_decision_cutover=False,
    )
    
    # モック解析結果を作成
    mock_analysis = FunctionReturnAnalysis(
        function_name="test_func",
        entry_point="0x00401000",
        parameters=[],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.CONSTANT, value=42, size=32)
            )
        ]
    )
    mock_analysis.return_type = "int"
    
    # ReturnAnalyzer をモック
    with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
        mock_analyzer = Mock()
        mock_analyzer.analyze_function_by_name.return_value = mock_analysis
        mock_analyzer.dispose = Mock()
        mock_analyzer_class.return_value = mock_analyzer
        
        # check メソッドをモック（UNSAT を返す）
        with patch.object(checker, 'check') as mock_check:
            mock_result = StrategyResult(
                is_equivalent=True,
                solver_results=ParallelResult(results=[
                    SolverResult(
                        solver_name="mock_solver",
                        status=SolverStatus.UNSAT,
                        elapsed_time=0.1
                    )
                ]),
                smt_formula="(assert ...)",
                counterexample_raw=None,
                return_var1="return_1",
                return_var2="return_2",
                constrained_fragments=[],
                total_pairs=1,
                unsat_pairs=1,
                sat_pairs=0,
                unknown_pairs=0,
                error_pairs=0
            )
            
            # StrategyResult を EquivalenceResult に変換する処理をスキップして、
            # check の戻り値として EquivalenceResult を直接返す
            from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
            from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
            
            eq_result = EquivalenceResult(
                is_equivalent=True,
                function1_name="test_func",
                function2_name="test_func",
                binary1_name=mock_program_x86.getName(),
                binary2_name=mock_program_x86.getName(),
                solver_results=mock_result.solver_results,
                counterexample=None,
                smt_formula=mock_result.smt_formula,
                total_time=0.1,
                type_fix_result=TypeFixResult(),
                retry_count=0,
                function1_signature=None,
                function2_signature=None,
                constrained_fragments=[],
                stage_path=["S_PAIRWISE"]  # ★ stage_path を設定
            )
            
            mock_check.return_value = eq_result
            
            result = checker.check_from_binaries(
                mock_program_x86, mock_program_x86,
                "test_func", "test_func",
                retry_with_type_fix=False
            )
            
            # stage_path が記録されていることを確認
            assert hasattr(result, 'stage_path')
            assert isinstance(result.stage_path, list)
            assert len(result.stage_path) > 0
            
            # debug_trace も記録されていることを確認
            assert hasattr(result, 'debug_trace')
            if result.debug_trace:
                assert len(result.debug_trace.attempts) > 0


def test_debug_trace_multiple_attempts_on_unknown(mock_program_x86):
    """UNKNOWN時に複数のattemptが記録されることを確認
    
    シナリオ:
    - Phase 0 (P0_BASE): _run_stage_plan が UNKNOWN を返す → 次Phaseへ
    - Phase 1 (P1_SIGNEDNESS): 型修正後に _run_stage_plan が UNSAT を返す → 終了
    → attempt が2件記録される
    """
    checker = EquivalenceChecker(
        debug=False,
        strategy="pairwise",
        canonical_decision_cutover=False,
    )
    
    # unsigned int 型で Phase 1 のトリガーになる
    mock_analysis = FunctionReturnAnalysis(
        function_name="unknown_func",
        entry_point="0x00401000",
        parameters=[],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.CONSTANT, value=42, size=32)
            )
        ]
    )
    mock_analysis.return_type = "unsigned int"
    
    # signedness情報を追加（Phase 1 を有効化）
    from scripts.function_tracer_pcode.model.analysis import SignednessResult
    mock_analysis.signedness_result = SignednessResult(signedness="signed")
    
    with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
        mock_analyzer = Mock()
        mock_analyzer.analyze_function_by_name.return_value = mock_analysis
        mock_analyzer.dispose = Mock()
        mock_analyzer_class.return_value = mock_analyzer
        
        call_count = [0]
        
        # ★ _run_stage_plan をモック（Phase 単位で結果を返す）
        def mock_run_stage_plan_side_effect(*args, **kwargs):
            from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
            from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
            
            call_count[0] += 1
            
            # retry_count を取得（kwargs から）
            retry_count = kwargs.get('retry_count', 0)
            
            # Phase 0: UNKNOWN
            if call_count[0] == 1:
                return EquivalenceResult(
                    is_equivalent=None,  # UNKNOWN
                    function1_name="unknown_func",
                    function2_name="unknown_func",
                    binary1_name=mock_program_x86.getName(),
                    binary2_name=mock_program_x86.getName(),
                    solver_results=ParallelResult(results=[
                        SolverResult(
                            solver_name="pairwise_aggregate",
                            status=SolverStatus.UNKNOWN,
                            elapsed_time=0.1
                        )
                    ]),
                    total_time=0.1,
                    type_fix_result=kwargs.get('type_fix_result', TypeFixResult()),
                    retry_count=retry_count,
                    stage_path=["S_PAIRWISE", "S_MONOLITHIC_FALLBACK"]
                )
            # Phase 1: UNSAT
            else:
                return EquivalenceResult(
                    is_equivalent=True,  # UNSAT
                    function1_name="unknown_func",
                    function2_name="unknown_func",
                    binary1_name=mock_program_x86.getName(),
                    binary2_name=mock_program_x86.getName(),
                    solver_results=ParallelResult(results=[
                        SolverResult(
                            solver_name="pairwise_aggregate",
                            status=SolverStatus.UNSAT,
                            elapsed_time=0.1
                        )
                    ]),
                    total_time=0.1,
                    type_fix_result=kwargs.get('type_fix_result', TypeFixResult()),
                    retry_count=retry_count,
                    stage_path=["S_PAIRWISE"]
                )
        
        with patch.object(checker, '_run_stage_plan', side_effect=mock_run_stage_plan_side_effect):
            # ★ Phase 1 で signedness fix が適用されるようにモック
            with patch.object(checker.phase_handler, 'execute_phase') as mock_execute_phase:
                from scripts.function_tracer_pcode.equivalence.phases.handler import PhaseResult, PhaseID
                
                def execute_phase_side_effect(phase_spec, *args, **kwargs):
                    if phase_spec.phase_id == PhaseID.P0_BASE:
                        # P0: 何もしない
                        return PhaseResult(
                            phase_id=PhaseID.P0_BASE,
                            applied=False,
                            retry_name="initial",
                            changed_binary1=False,
                            changed_binary2=False
                        )
                    elif phase_spec.phase_id == PhaseID.P1_SIGNEDNESS:
                        # P1: signedness fix を適用
                        return PhaseResult(
                            phase_id=PhaseID.P1_SIGNEDNESS,
                            applied=True,
                            retry_name="signedness_fix",
                            changed_binary1=True,
                            changed_binary2=False
                        )
                    else:
                        return PhaseResult(
                            phase_id=phase_spec.phase_id,
                            applied=False,
                            retry_name="none",
                            changed_binary1=False,
                            changed_binary2=False
                        )
                
                mock_execute_phase.side_effect = execute_phase_side_effect
                
                result = checker.check_from_binaries(
                    mock_program_x86, mock_program_x86,
                    "unknown_func", "unknown_func",
                    retry_with_type_fix=True  # リトライ有効
                )
                
                # debug_trace が存在する
                assert result.debug_trace is not None
                
                # ★ 複数の attempt が記録されるはず（P0_BASE + P1_SIGNEDNESS）
                assert len(result.debug_trace.attempts) >= 2, \
                    f"Expected at least 2 attempts, got {len(result.debug_trace.attempts)}"
                
                # P0_BASE が含まれている
                phases = [attempt.phase for attempt in result.debug_trace.attempts]
                assert "P0_BASE" in phases, f"Expected P0_BASE in phases, got {phases}"
                
                # P1_SIGNEDNESS も含まれている
                assert "P1_SIGNEDNESS" in phases, f"Expected P1_SIGNEDNESS in phases, got {phases}"
                
                # P0_BASE は UNKNOWN
                p0_attempt = next(a for a in result.debug_trace.attempts if a.phase == "P0_BASE")
                assert p0_attempt.result is None, "P0_BASE should be UNKNOWN"
                assert p0_attempt.transition_reason == "UNKNOWN"
                
                # P1_SIGNEDNESS は UNSAT
                p1_attempt = next(a for a in result.debug_trace.attempts if a.phase == "P1_SIGNEDNESS")
                assert p1_attempt.result is True, "P1_SIGNEDNESS should be UNSAT"
                assert p1_attempt.transition_reason == "UNSAT"
                
                # 最終結果はUNSAT
                assert result.is_equivalent is True

def test_debug_trace_to_dict_machine_readable(mock_program_x86):
    """to_dict()が機械可読であることを確認"""
    import json
    
    checker = EquivalenceChecker(
        debug=False,
        strategy="pairwise",
        canonical_decision_cutover=False,
    )
    
    mock_analysis = FunctionReturnAnalysis(
        function_name="test_func",
        entry_point="0x00401000",
        parameters=[],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.CONSTANT, value=42, size=32)
            )
        ]
    )
    mock_analysis.return_type = "undefined4"
    
    with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
        mock_analyzer = Mock()
        mock_analyzer.analyze_function_by_name.return_value = mock_analysis
        mock_analyzer.dispose = Mock()
        mock_analyzer_class.return_value = mock_analyzer
        
        call_count = [0]
        
        def mock_check_side_effect(*args, **kwargs):
            from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
            from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
            
            call_count[0] += 1
            
            if call_count[0] == 1:
                # Phase 0: UNKNOWN
                return EquivalenceResult(
                    is_equivalent=None,
                    function1_name="test_func",
                    function2_name="test_func",
                    binary1_name=mock_program_x86.getName(),
                    binary2_name=mock_program_x86.getName(),
                    solver_results=ParallelResult(results=[
                        SolverResult(
                            solver_name="mock_solver",
                            status=SolverStatus.UNKNOWN,
                            elapsed_time=0.1
                        )
                    ]),
                    total_time=0.1,
                    type_fix_result=TypeFixResult(),
                    retry_count=0,
                    stage_path=["S_PAIRWISE", "S_MONOLITHIC_FALLBACK"]
                )
            else:
                # Phase 1: UNSAT
                return EquivalenceResult(
                    is_equivalent=True,
                    function1_name="test_func",
                    function2_name="test_func",
                    binary1_name=mock_program_x86.getName(),
                    binary2_name=mock_program_x86.getName(),
                    solver_results=ParallelResult(results=[
                        SolverResult(
                            solver_name="mock_solver",
                            status=SolverStatus.UNSAT,
                            elapsed_time=0.1
                        )
                    ]),
                    total_time=0.1,
                    type_fix_result=TypeFixResult(),
                    retry_count=1,
                    stage_path=["S_PAIRWISE"]
                )
        
        with patch.object(checker, 'check', side_effect=mock_check_side_effect):
            result = checker.check_from_binaries(
                mock_program_x86, mock_program_x86,
                "test_func", "test_func",
                retry_with_type_fix=True
            )
            
            # to_dict() がJSON可能な形式を返すことを確認
            result_dict = result.to_dict()
            
            # JSONシリアライズ可能性を確認
            json_str = json.dumps(result_dict, indent=2)
            assert isinstance(json_str, str)
            
            # パース可能性を確認
            parsed = json.loads(json_str)
            assert "debug_trace" in parsed
            
            if parsed["debug_trace"]:
                assert "attempts" in parsed["debug_trace"]
                assert "final_result" in parsed["debug_trace"]
                assert "total_time" in parsed["debug_trace"]
