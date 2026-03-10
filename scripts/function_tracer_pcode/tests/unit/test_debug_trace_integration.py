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
        strategy="pairwise"
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
        strategy="pairwise"
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


def test_debug_trace_sat_with_pairwise_decisive(mock_program_x86):
    """SAT時にpairwise decisive情報が記録されることを確認（中身の詳細検証を含む）"""
    checker = EquivalenceChecker(
        debug=False,
        strategy="pairwise"
    )
    
    mock_analysis = FunctionReturnAnalysis(
        function_name="not_equiv_func",
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
    
    # ★ SAT時のfinal_queryモック（実際のSMTクエリ）
    mock_final_query = """(set-logic QF_BV)
(declare-fun param_1_1 () (_ BitVec 32))
(declare-fun param_1_2 () (_ BitVec 32))
; Parameter equality constraints
(assert (= param_1_1 param_1_2))
; Case1[0] conditions
(assert (bvsgt param_1_1 #x00000000))
; Case2[1] conditions
; (unconditional)
; Value inequality
(assert (not (= (bvadd param_1_1 #x00000001) (bvadd param_1_2 #x00000002))))
(check-sat)
(get-model)
"""
    
    with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
        mock_analyzer = Mock()
        mock_analyzer.analyze_function_by_name.return_value = mock_analysis
        mock_analyzer.dispose = Mock()
        mock_analyzer_class.return_value = mock_analyzer
        
        with patch.object(checker, 'check') as mock_check:
            from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
            from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
            
            eq_result = EquivalenceResult(
                is_equivalent=False,
                function1_name="not_equiv_func",
                function2_name="not_equiv_func",
                binary1_name=mock_program_x86.getName(),
                binary2_name=mock_program_x86.getName(),
                solver_results=ParallelResult(results=[
                    SolverResult(
                        solver_name="pairwise_aggregate",
                        status=SolverStatus.SAT,
                        elapsed_time=0.1,
                        model={"param_1": 123}
                    )
                ]),
                total_time=0.1,
                type_fix_result=TypeFixResult(),
                retry_count=0,
                stage_path=["S_PAIRWISE"],
                pairwise_stats={
                    'total_pairs': 4,
                    'unsat_pairs': 3,
                    'sat_pairs': 1,
                    'unknown_pairs': 0,
                    'error_pairs': 0,
                },
                sat_pair_info={
                    'i': 0,
                    'j': 1,
                    'case1_summary': 'x > 0',
                    'case2_summary': 'unconditional',
                    'value1': 'x + 1',
                    'value2': 'x + 2',
                    'pair_stage': 'with-ineq',
                    'final_query': mock_final_query,  # ★ 完全なクエリを設定
                }
            )
            
            mock_check.return_value = eq_result
            
            result = checker.check_from_binaries(
                mock_program_x86, mock_program_x86,
                "not_equiv_func", "not_equiv_func",
                retry_with_type_fix=False
            )
            
            # SAT の場合
            assert result.is_equivalent is False
            assert result.debug_trace is not None
            assert len(result.debug_trace.attempts) > 0
            
            # 最初のattemptにpairwise_decisive情報があるはず
            first_attempt = result.debug_trace.attempts[0]
            assert first_attempt.pairwise_decisive is not None, \
                "SAT result should have pairwise_decisive info"
            
            pairwise_decisive = first_attempt.pairwise_decisive
            assert pairwise_decisive.decisive_result == "SAT"
            assert pairwise_decisive.decisive_pair is not None
            
            # ★ 追加: final_query の中身を詳細に検証
            assert pairwise_decisive.final_query is not None, \
                "pairwise_decisive should have final_query"
            
            final_query = pairwise_decisive.final_query
            
            # SMTクエリとして必要な要素が含まれているか確認
            assert "(set-logic QF_BV)" in final_query, \
                "final_query should contain set-logic declaration"
            
            assert "(declare-fun" in final_query, \
                "final_query should contain function declarations"
            
            assert "(assert" in final_query, \
                "final_query should contain assertions"
            
            assert "(check-sat)" in final_query, \
                "final_query should contain check-sat command"
            
            # 値不等式が含まれているか確認
            assert "(not (=" in final_query, \
                "final_query should contain value inequality (not (= ...))"
            
            # ★ 追加: final_query_excerpt との整合性確認
            assert pairwise_decisive.final_query_excerpt is not None, \
                "pairwise_decisive should have final_query_excerpt"
            
            # final_query_excerpt は final_query の先頭部分であること
            assert final_query.startswith(pairwise_decisive.final_query_excerpt[:100]), \
                "final_query_excerpt should be a prefix of final_query"
            
            # ★ 追加: to_dict() にも final_query が含まれることを確認
            attempt_dict = first_attempt.to_dict()
            assert "pairwise_decisive" in attempt_dict
            assert attempt_dict["pairwise_decisive"]["final_query"] is not None, \
                "to_dict() should include pairwise_decisive.final_query"
            
            print(f"✓ pairwise_decisive.final_query validated: {len(final_query)} chars")
            print(f"✓ final_query contains necessary SMT elements")


def test_debug_trace_to_dict_machine_readable(mock_program_x86):
    """to_dict()が機械可読であることを確認"""
    import json
    
    checker = EquivalenceChecker(
        debug=False,
        strategy="pairwise"
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

def test_debug_trace_phase4a_to_phase4b_transition(mock_program_mips64, mock_program_x86):
    """Phase 4-A SAT → Phase 4-B の transition_reason が SAT->Phase4B になることを確認"""
    from scripts.function_tracer_pcode.equivalence import EquivalenceChecker
    from unittest.mock import Mock, patch
    from scripts.function_tracer_pcode.model import FunctionReturnAnalysis, ReturnInfo, Expression, ExpressionType
    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
    from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
    from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
    from scripts.function_tracer_pcode.equivalence.phases.handler import PhaseResult, PhaseID
    
    checker = EquivalenceChecker(debug=False, strategy="pairwise")
    
    # MIPS64側: 64bit long パラメータ
    mock_analysis_mips64 = FunctionReturnAnalysis(
        function_name="test_func",
        entry_point="0x00401000",
        parameters=[{"name": "param_1", "data_type": "long", "size": 8}],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.PARAMETER, name="param_1")
            )
        ]
    )
    mock_analysis_mips64.return_type = "long"
    
    # x86側: 32bit int パラメータ
    mock_analysis_x86 = FunctionReturnAnalysis(
        function_name="test_func",
        entry_point="0x00401000",
        parameters=[{"name": "param_1", "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.PARAMETER, name="param_1")
            )
        ]
    )
    mock_analysis_x86.return_type = "int"
    
    # 偽反例（符号拡張パターン）
    counterexample = {
        "param_1_1": 0x0000000080000001,  # ゼロ拡張（本来は符号拡張すべき）
        "param_1_2": 0x80000001,
    }
    
    # ★ Phase 4-B で使用する SMT formula をモック
    mock_phase4b_smt_formula = """(set-logic QF_BV)
(declare-fun param_1_1 () (_ BitVec 64))
(declare-fun param_1_2 () (_ BitVec 32))
; ABI constraints (sign-extend)
(assert (= param_1_1 ((_ sign_extend 32) param_1_2)))
(assert (not (= param_1_1 ((_ sign_extend 32) param_1_2))))
(check-sat)
(get-model)
"""
    
    with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
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
        
        run_stage_plan_count = [0]
        
        def mock_run_stage_plan_side_effect(*args, **kwargs):
            run_stage_plan_count[0] += 1
            retry_count = kwargs.get('retry_count', 0)
            
            # P0: UNKNOWN
            if run_stage_plan_count[0] == 1:
                return EquivalenceResult(
                    is_equivalent=None,
                    function1_name="test_func",
                    function2_name="test_func",
                    binary1_name=mock_program_mips64.getName(),
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
            # P4A: SAT (偽反例)
            else:
                return EquivalenceResult(
                    is_equivalent=False,
                    function1_name="test_func",
                    function2_name="test_func",
                    binary1_name=mock_program_mips64.getName(),
                    binary2_name=mock_program_x86.getName(),
                    solver_results=ParallelResult(results=[
                        SolverResult(
                            solver_name="pairwise_aggregate",
                            status=SolverStatus.SAT,
                            elapsed_time=0.1,
                            model=counterexample
                        )
                    ]),
                    total_time=0.1,
                    type_fix_result=kwargs.get('type_fix_result', TypeFixResult()),
                    retry_count=retry_count,
                    stage_path=["S_PAIRWISE"]
                )
        
        # ★ _retry_with_abi_constraints をモック（P4B の結果を返す）
        def mock_retry_with_abi_constraints(ctx, abi_constraints, retry_count):
            return EquivalenceResult(
                is_equivalent=True,  # ★ UNSAT
                function1_name="test_func",
                function2_name="test_func",
                binary1_name=mock_program_mips64.getName(),
                binary2_name=mock_program_x86.getName(),
                solver_results=ParallelResult(results=[
                    SolverResult(
                        solver_name="pairwise_aggregate",
                        status=SolverStatus.UNSAT,
                        elapsed_time=0.1
                    )
                ]),
                total_time=0.1,
                type_fix_result=ctx.type_fix_result,
                retry_count=retry_count,
                stage_path=["S_PAIRWISE"],
                mips64_abi_constraints=abi_constraints,
                smt_formula=mock_phase4b_smt_formula  # ★ SMT formula を設定
            )
        
        with patch.object(checker, '_run_stage_plan', side_effect=mock_run_stage_plan_side_effect):
            # ★ _retry_with_abi_constraints をモック
            with patch.object(checker, '_retry_with_abi_constraints', side_effect=mock_retry_with_abi_constraints):
                with patch.object(checker.phase_handler, 'execute_phase') as mock_execute_phase:
                    def execute_phase_side_effect(phase_spec, *args, **kwargs):
                        if phase_spec.phase_id == PhaseID.P0_BASE:
                            return PhaseResult(
                                phase_id=PhaseID.P0_BASE,
                                applied=False,
                                retry_name="initial",
                                changed_binary1=False,
                                changed_binary2=False
                            )
                        elif phase_spec.phase_id == PhaseID.P4A_MIPS64_ABI:
                            # Phase 4-A: MIPS64 ABI fix を適用
                            return PhaseResult(
                                phase_id=PhaseID.P4A_MIPS64_ABI,
                                applied=True,
                                retry_name="mips64_abi_fix",
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
                        mock_program_mips64, mock_program_x86,
                        "test_func", "test_func",
                        retry_with_type_fix=True,
                        save_formula=False  # ★ 明示的に False を指定
                    )
                    
                    # debug_trace が存在する
                    assert result.debug_trace is not None
                    
                    # P0_BASE, P4A_MIPS64_ABI, P4B_MIPS64_SPURIOUS の3件の attempt があるはず
                    assert len(result.debug_trace.attempts) >= 3, \
                        f"Expected at least 3 attempts, got {len(result.debug_trace.attempts)}"
                    
                    phases = [attempt.phase for attempt in result.debug_trace.attempts]
                    assert "P0_BASE" in phases
                    assert "P4A_MIPS64_ABI" in phases
                    assert "P4B_MIPS64_SPURIOUS" in phases
                    
                    # P4A_MIPS64_ABI の transition_reason が SAT->Phase4B であることを確認
                    p4a_attempt = next(a for a in result.debug_trace.attempts if a.phase == "P4A_MIPS64_ABI")
                    assert p4a_attempt.result is False, "P4A should be SAT"
                    assert p4a_attempt.transition_reason == "SAT->Phase4B", \
                        f"Expected 'SAT->Phase4B', got '{p4a_attempt.transition_reason}'"
                    
                    # P4B_MIPS64_SPURIOUS の結果が UNSAT
                    p4b_attempt = next(a for a in result.debug_trace.attempts if a.phase == "P4B_MIPS64_SPURIOUS")
                    assert p4b_attempt.result is True, "P4B should be UNSAT"
                    assert p4b_attempt.transition_reason == "UNSAT"
                    
                    # ★ 追加: Phase 4-B の final_smt が保存されていることを確認（save_formula=False でも）
                    assert p4b_attempt.final_smt is not None, \
                        "Phase 4-B attempt should have final_smt even with save_formula=False"
                    
                    assert len(p4b_attempt.final_smt) > 0, \
                        "Phase 4-B final_smt should not be empty"
                    
                    # ★ 追加: final_smt に ABI constraints が含まれていることを確認
                    assert "sign_extend" in p4b_attempt.final_smt or "ABI constraints" in p4b_attempt.final_smt, \
                        "Phase 4-B final_smt should contain ABI constraints"
                    
                    # ★ 追加: final_smt_excerpt も設定されていることを確認（互換性）
                    assert p4b_attempt.final_smt_excerpt is not None, \
                        "Phase 4-B attempt should have final_smt_excerpt"
                    
                    # ★ 追加: mips64_abi_constraints が記録されていることを確認
                    assert p4b_attempt.mips64_abi_constraints is not None, \
                        "Phase 4-B attempt should have mips64_abi_constraints"
                    
                    # 最終結果は EQUIVALENT
                    assert result.is_equivalent is True

def test_phase4b_final_smt_in_to_dict(mock_program_mips64, mock_program_x86):
    """Phase 4-B の final_smt が to_dict() にも含まれることを確認"""
    from scripts.function_tracer_pcode.equivalence import EquivalenceChecker
    from unittest.mock import Mock, patch
    from scripts.function_tracer_pcode.model import FunctionReturnAnalysis, ReturnInfo, Expression, ExpressionType
    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
    from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
    from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
    from scripts.function_tracer_pcode.equivalence.phases.handler import PhaseResult, PhaseID
    import json
    
    checker = EquivalenceChecker(debug=False, strategy="pairwise")
    
    # 前テストと同じセットアップ
    mock_analysis_mips64 = FunctionReturnAnalysis(
        function_name="test_func",
        entry_point="0x00401000",
        parameters=[{"name": "param_1", "data_type": "long", "size": 8}],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.PARAMETER, name="param_1")
            )
        ]
    )
    mock_analysis_mips64.return_type = "long"
    
    mock_analysis_x86 = FunctionReturnAnalysis(
        function_name="test_func",
        entry_point="0x00401000",
        parameters=[{"name": "param_1", "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.PARAMETER, name="param_1")
            )
        ]
    )
    mock_analysis_x86.return_type = "int"
    
    counterexample = {
        "param_1_1": 0x0000000080000001,
        "param_1_2": 0x80000001,
    }
    
    mock_phase4b_smt_formula = """(set-logic QF_BV)
(declare-fun param_1_1 () (_ BitVec 64))
(declare-fun param_1_2 () (_ BitVec 32))
; ABI constraints
(assert (= param_1_1 ((_ sign_extend 32) param_1_2)))
(check-sat)
"""
    
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
        
        run_stage_plan_count = [0]
        
        def mock_run_stage_plan_side_effect(*args, **kwargs):
            run_stage_plan_count[0] += 1
            retry_count = kwargs.get('retry_count', 0)
            
            if run_stage_plan_count[0] == 1:
                return EquivalenceResult(
                    is_equivalent=None,
                    function1_name="test_func",
                    function2_name="test_func",
                    binary1_name=mock_program_mips64.getName(),
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
            else:
                return EquivalenceResult(
                    is_equivalent=False,
                    function1_name="test_func",
                    function2_name="test_func",
                    binary1_name=mock_program_mips64.getName(),
                    binary2_name=mock_program_x86.getName(),
                    solver_results=ParallelResult(results=[
                        SolverResult(
                            solver_name="pairwise_aggregate",
                            status=SolverStatus.SAT,
                            elapsed_time=0.1,
                            model=counterexample
                        )
                    ]),
                    total_time=0.1,
                    type_fix_result=kwargs.get('type_fix_result', TypeFixResult()),
                    retry_count=retry_count,
                    stage_path=["S_PAIRWISE"]
                )
        
        def mock_retry_with_abi_constraints(ctx, abi_constraints, retry_count):
            return EquivalenceResult(
                is_equivalent=True,
                function1_name="test_func",
                function2_name="test_func",
                binary1_name=mock_program_mips64.getName(),
                binary2_name=mock_program_x86.getName(),
                solver_results=ParallelResult(results=[
                    SolverResult(
                        solver_name="pairwise_aggregate",
                        status=SolverStatus.UNSAT,
                        elapsed_time=0.1
                    )
                ]),
                total_time=0.1,
                type_fix_result=ctx.type_fix_result,
                retry_count=retry_count,
                stage_path=["S_PAIRWISE"],
                mips64_abi_constraints=abi_constraints,
                smt_formula=mock_phase4b_smt_formula
            )
        
        with patch.object(checker, '_run_stage_plan', side_effect=mock_run_stage_plan_side_effect):
            with patch.object(checker, '_retry_with_abi_constraints', side_effect=mock_retry_with_abi_constraints):
                with patch.object(checker.phase_handler, 'execute_phase') as mock_execute_phase:
                    def execute_phase_side_effect(phase_spec, *args, **kwargs):
                        if phase_spec.phase_id == PhaseID.P0_BASE:
                            return PhaseResult(
                                phase_id=PhaseID.P0_BASE,
                                applied=False,
                                retry_name="initial",
                                changed_binary1=False,
                                changed_binary2=False
                            )
                        elif phase_spec.phase_id == PhaseID.P4A_MIPS64_ABI:
                            return PhaseResult(
                                phase_id=PhaseID.P4A_MIPS64_ABI,
                                applied=True,
                                retry_name="mips64_abi_fix",
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
                        mock_program_mips64, mock_program_x86,
                        "test_func", "test_func",
                        retry_with_type_fix=True,
                        save_formula=False
                    )
                    
                    assert result.debug_trace is not None
                    
                    # to_dict() を呼び出し
                    trace_dict = result.debug_trace.to_dict()
                    
                    # JSON シリアライズ可能性を確認
                    json_str = json.dumps(trace_dict, indent=2)
                    assert isinstance(json_str, str)
                    
                    # Phase 4-B の attempt を探す
                    phase4b_attempts = [
                        a for a in trace_dict["attempts"]
                        if a["phase"] == "P4B_MIPS64_SPURIOUS"
                    ]
                    
                    assert len(phase4b_attempts) > 0, "Phase 4-B was not triggered"
                    
                    # to_dict() に final_smt が含まれることを確認
                    for attempt_dict in phase4b_attempts:
                        assert "final_smt" in attempt_dict, \
                            f"to_dict() missing 'final_smt' for Phase 4-B attempt {attempt_dict['attempt_id']}"
                        
                        assert attempt_dict["final_smt"] is not None, \
                            f"to_dict() has None 'final_smt' for Phase 4-B attempt {attempt_dict['attempt_id']}"
                        
                        assert len(attempt_dict["final_smt"]) > 0, \
                            "final_smt should not be empty"
                        
                        # final_smt_excerpt も存在
                        assert "final_smt_excerpt" in attempt_dict, \
                            f"to_dict() missing 'final_smt_excerpt'"
                        
                        # mips64_abi_constraints も存在
                        assert "mips64_abi_constraints" in attempt_dict, \
                            f"to_dict() missing 'mips64_abi_constraints'"
                        
                        # final_smt に ABI constraints が含まれることを確認
                        assert "sign_extend" in attempt_dict["final_smt"] or \
                               "ABI constraints" in attempt_dict["final_smt"], \
                            "final_smt should contain ABI constraints"
                    
                    print(f"✓ to_dict() includes final_smt for {len(phase4b_attempts)} Phase 4-B attempts")

def test_final_smt_excerpt_compatibility():
    """final_smt_excerpt 互換性が維持されていることを確認"""
    from scripts.function_tracer_pcode.equivalence.debug_trace import Attempt
    
    # final_smt_excerpt と final_smt の両方を持つ Attempt をシミュレート
    attempt = Attempt(
        attempt_id=0,
        retry_count=0,
        phase="P4B_MIPS64_SPURIOUS",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=True,
        transition_reason="UNSAT",
        final_smt_excerpt="(declare-fun x () (_ BitVec 64))",
        final_smt="(declare-fun x () (_ BitVec 64))\n(assert (= x #x0000000000000000))\n(check-sat)",
        elapsed_time=0.5
    )
    
    # to_dict() が両方含むこと
    attempt_dict = attempt.to_dict()
    assert "final_smt_excerpt" in attempt_dict
    assert "final_smt" in attempt_dict
    assert attempt_dict["final_smt_excerpt"] == "(declare-fun x () (_ BitVec 64))"
    assert len(attempt_dict["final_smt"]) > len(attempt_dict["final_smt_excerpt"])
    
    # final_smt_excerpt は final_smt の先頭部分であること
    assert attempt_dict["final_smt"].startswith(attempt_dict["final_smt_excerpt"][:50])
    
    print("✓ final_smt_excerpt compatibility maintained")

def test_debug_trace_normalization_rules_end_to_end(mock_program_x86):
    """正規化ルールがend-to-endで記録されることを確認
    
    シナリオ:
    - pairwise戦略をモックして正規化ルールを含む結果を返す
    - normalization_rulesが記録される
    - to_dict()にも含まれる
    """
    from scripts.function_tracer_pcode.equivalence import EquivalenceChecker
    from unittest.mock import Mock, patch
    from scripts.function_tracer_pcode.model import (
        FunctionReturnAnalysis, ReturnInfo, Expression, ExpressionType
    )
    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
    from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
    from scripts.function_tracer_pcode.equivalence.debug_trace import NormalizationRuleApplication
    from scripts.function_tracer_pcode.equivalence.strategies.base import StrategyResult
    import json
    
    checker = EquivalenceChecker(debug=False, strategy="pairwise")
    
    # ★ シンプルな解析結果（詳細は pairwise_strategy.check のモックで制御）
    mock_analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x00401000",
        parameters=[{"name": "x", "data_type": "unsigned int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.PARAMETER, name="x")
            )
        ]
    )
    mock_analysis1.return_type = "unsigned int"
    
    mock_analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x00401000",
        parameters=[{"name": "x", "data_type": "unsigned int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.PARAMETER, name="x")
            )
        ]
    )
    mock_analysis2.return_type = "unsigned int"
    
    with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
        analyzer_call_count = [0]
        
        def mock_analyze_side_effect(func_name, timeout):
            analyzer_call_count[0] += 1
            if analyzer_call_count[0] == 1:
                return mock_analysis1
            else:
                return mock_analysis2
        
        mock_analyzer = Mock()
        mock_analyzer.analyze_function_by_name.side_effect = mock_analyze_side_effect
        mock_analyzer.dispose = Mock()
        mock_analyzer_class.return_value = mock_analyzer
        
        # ★ pairwise strategy の check をモック（正規化ルールを含む結果を返す）
        with patch.object(checker.pairwise_strategy, 'check') as mock_pairwise_check:
            # ★ 正規化ルールをモック（実際のudiv→shift変換を模擬）
            mock_normalization_rules = [
                NormalizationRuleApplication(
                    rule_name="udiv_to_shift",
                    reason="Power-of-2 divisor with nonneg dividend",
                    applied_to="pair_(0,0)",
                    before="(bvudiv x_1 #x00000002)",
                    after="(bvshr x_1 #x00000001)"
                ),
                NormalizationRuleApplication(
                    rule_name="negate_double_negation",
                    reason="Simplify double negation",
                    applied_to="pair_(0,0)",
                    before="(bvneg (bvneg x_1))",
                    after="x_1"
                )
            ]
            
            strategy_result = StrategyResult(
                is_equivalent=True,  # 正規化後に等価
                solver_results=ParallelResult(results=[
                    SolverResult(
                        solver_name="pairwise_aggregate",
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
                error_pairs=0,
                normalization_rules=mock_normalization_rules  # ★ 正規化ルールを設定
            )
            
            mock_pairwise_check.return_value = strategy_result
            
            result = checker.check_from_binaries(
                mock_program_x86, mock_program_x86,
                "func1", "func2",
                retry_with_type_fix=False
            )
            
            # 結果は EQUIVALENT
            assert result.is_equivalent is True
            
            # debug_trace が存在
            assert result.debug_trace is not None
            assert len(result.debug_trace.attempts) > 0
            
            # ★ normalization_rules が記録されていることを確認
            first_attempt = result.debug_trace.attempts[0]
            assert len(first_attempt.normalization_rules) > 0, \
                "normalization_rules should be recorded"
            
            # ★ 複数の正規化ルールが記録されていることを確認
            assert len(first_attempt.normalization_rules) == 2, \
                f"Expected 2 normalization rules, got {len(first_attempt.normalization_rules)}"
            
            # ★ 最初の正規化ルールの中身を確認（udiv_to_shift）
            norm_rule1 = first_attempt.normalization_rules[0]
            assert norm_rule1.rule_name == "udiv_to_shift", \
                f"Expected 'udiv_to_shift', got '{norm_rule1.rule_name}'"
            
            assert norm_rule1.applied_to == "pair_(0,0)", \
                f"Expected 'pair_(0,0)', got '{norm_rule1.applied_to}'"
            
            assert norm_rule1.before is not None and norm_rule1.before != "", \
                "norm_rule1.before should not be empty"
            
            assert "bvudiv" in norm_rule1.before, \
                f"Expected 'bvudiv' in before, got '{norm_rule1.before}'"
            
            assert norm_rule1.after is not None and norm_rule1.after != "", \
                "norm_rule1.after should not be empty"
            
            assert "bvshr" in norm_rule1.after, \
                f"Expected 'bvshr' in after, got '{norm_rule1.after}'"
            
            # ★ 2番目の正規化ルールの中身を確認（negate_double_negation）
            norm_rule2 = first_attempt.normalization_rules[1]
            assert norm_rule2.rule_name == "negate_double_negation", \
                f"Expected 'negate_double_negation', got '{norm_rule2.rule_name}'"
            
            assert norm_rule2.before is not None and norm_rule2.before != "", \
                "norm_rule2.before should not be empty"

            assert "bvneg" in norm_rule2.before, \
                f"Expected 'bvneg' in before, got '{norm_rule2.before}'"
            
            # ★ to_dict() にも normalization_rules が含まれることを確認
            trace_dict = result.debug_trace.to_dict()
            assert "attempts" in trace_dict
            
            first_attempt_dict = trace_dict["attempts"][0]
            assert "normalization_rules" in first_attempt_dict, \
                "to_dict() should include normalization_rules"
            
            assert len(first_attempt_dict["normalization_rules"]) == 2, \
                f"Expected 2 normalization_rules in to_dict(), got {len(first_attempt_dict['normalization_rules'])}"
            
            # ★ 各正規化ルールの必須フィールドを確認
            for i, norm_rule_dict in enumerate(first_attempt_dict["normalization_rules"]):
                assert "rule_name" in norm_rule_dict, \
                    f"normalization_rules[{i}] missing 'rule_name'"
                assert "reason" in norm_rule_dict, \
                    f"normalization_rules[{i}] missing 'reason'"
                assert "applied_to" in norm_rule_dict, \
                    f"normalization_rules[{i}] missing 'applied_to'"
                assert "before" in norm_rule_dict, \
                    f"normalization_rules[{i}] missing 'before'"
                assert "after" in norm_rule_dict, \
                    f"normalization_rules[{i}] missing 'after'"
            
            # ★ 1つ目のルールの詳細を確認
            norm_rule1_dict = first_attempt_dict["normalization_rules"][0]
            assert norm_rule1_dict["rule_name"] == "udiv_to_shift"
            assert "Power-of-2" in norm_rule1_dict["reason"]
            
            # ★ JSONシリアライズ可能性を確認
            json_str = json.dumps(trace_dict, indent=2)
            assert isinstance(json_str, str)
            
            parsed = json.loads(json_str)
            assert "attempts" in parsed
            assert len(parsed["attempts"][0]["normalization_rules"]) == 2
            
            # ★ パースされたJSONから正規化ルールを取り出せることを確認
            parsed_norm_rules = parsed["attempts"][0]["normalization_rules"]
            assert parsed_norm_rules[0]["rule_name"] == "udiv_to_shift"
            assert parsed_norm_rules[1]["rule_name"] == "negate_double_negation"
            
            print(f"✓ normalization_rules recorded: {len(first_attempt.normalization_rules)} rules")
            print(f"  - Rule 1: {norm_rule1.rule_name}")
            print(f"  - Rule 2: {norm_rule2.rule_name}")
            print(f"✓ normalization_rules included in to_dict()")
            print(f"✓ normalization_rules JSON serializable")

def test_pairwise_decisive_final_query_structure(mock_program_x86):
    """pairwise_decisive.final_queryのSMT構造を詳細に検証"""
    from scripts.function_tracer_pcode.equivalence import EquivalenceChecker
    from unittest.mock import Mock, patch
    from scripts.function_tracer_pcode.model import FunctionReturnAnalysis, ReturnInfo, Expression, ExpressionType
    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
    from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
    from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
    import re
    
    checker = EquivalenceChecker(debug=False, strategy="pairwise")
    
    mock_analysis = FunctionReturnAnalysis(
        function_name="test_func",
        entry_point="0x00401000",
        parameters=[{"name": "param_1", "data_type": "int", "size": 4}],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.CONSTANT, value=42, size=32)
            )
        ]
    )
    mock_analysis.return_type = "int"
    
    # ★ 実際のSMTクエリ構造をモック
    mock_final_query = """(set-logic QF_BV)
; ============================================================
; Pairwise Query: Pair (0,1)
; Case1[0]: x > 0
; Case2[1]: unconditional
; ============================================================

(declare-fun param_1_1 () (_ BitVec 32))
(declare-fun param_1_2 () (_ BitVec 32))

; ----------------------------------------
; Parameter equality constraints
; ----------------------------------------
(assert (= param_1_1 param_1_2))

; ----------------------------------------
; UB constraints
; ----------------------------------------
; (none)

; ----------------------------------------
; Case1[0] conditions
; ----------------------------------------
(assert (bvsgt param_1_1 #x00000000))

; ----------------------------------------
; Case2[1] conditions
; ----------------------------------------
; (unconditional)

; ----------------------------------------
; Value inequality
; ----------------------------------------
(assert (not (= (bvadd param_1_1 #x00000001) (bvadd param_1_2 #x00000002))))

(check-sat)
(get-model)
"""
    
    with patch('scripts.function_tracer_pcode.analysis.ReturnAnalyzer') as mock_analyzer_class:
        mock_analyzer = Mock()
        mock_analyzer.analyze_function_by_name.return_value = mock_analysis
        mock_analyzer.dispose = Mock()
        mock_analyzer_class.return_value = mock_analyzer
        
        with patch.object(checker, 'check') as mock_check:
            eq_result = EquivalenceResult(
                is_equivalent=False,
                function1_name="test_func",
                function2_name="test_func",
                binary1_name=mock_program_x86.getName(),
                binary2_name=mock_program_x86.getName(),
                solver_results=ParallelResult(results=[
                    SolverResult(
                        solver_name="pairwise_aggregate",
                        status=SolverStatus.SAT,
                        elapsed_time=0.1,
                        model={"param_1_1": 5, "param_1_2": 5}
                    )
                ]),
                total_time=0.1,
                type_fix_result=TypeFixResult(),
                retry_count=0,
                stage_path=["S_PAIRWISE"],
                pairwise_stats={
                    'total_pairs': 4,
                    'unsat_pairs': 3,
                    'sat_pairs': 1,
                    'unknown_pairs': 0,
                    'error_pairs': 0,
                },
                sat_pair_info={
                    'i': 0,
                    'j': 1,
                    'case1_summary': 'x > 0',
                    'case2_summary': 'unconditional',
                    'value1': 'x + 1',
                    'value2': 'x + 2',
                    'pair_stage': 'with-ineq',
                    'final_query': mock_final_query,
                }
            )
            
            mock_check.return_value = eq_result
            
            result = checker.check_from_binaries(
                mock_program_x86, mock_program_x86,
                "test_func", "test_func",
                retry_with_type_fix=False
            )
            
            assert result.is_equivalent is False
            assert result.debug_trace is not None
            
            first_attempt = result.debug_trace.attempts[0]
            assert first_attempt.pairwise_decisive is not None
            
            final_query = first_attempt.pairwise_decisive.final_query
            assert final_query is not None
            
            # ★ SMTクエリの構造を詳細に検証
            
            # 1. set-logic宣言があること
            assert re.search(r'\(set-logic\s+\w+\)', final_query), \
                "final_query should have (set-logic ...) declaration"
            
            # 2. 関数宣言があること
            assert re.search(r'\(declare-fun\s+\w+\s+\(\)\s+\(_\s+BitVec\s+\d+\)\)', final_query), \
                "final_query should have (declare-fun ...) declarations"
            
            # 3. パラメータ等価制約があること
            assert re.search(r'\(assert\s+\(=\s+param_\w+_1\s+param_\w+_2\)\)', final_query), \
                "final_query should have parameter equality constraints"
            
            # 4. 条件のアサーションがあること（または unconditional のコメント）
            has_condition_assert = re.search(r'; Case\d+\[\d+\] conditions', final_query)
            assert has_condition_assert, \
                "final_query should have case condition sections"
            
            # 5. 値不等式があること
            assert re.search(r'\(assert\s+\(not\s+\(=', final_query), \
                "final_query should have value inequality (assert (not (= ...)))"
            
            # 6. check-sat があること
            assert re.search(r'\(check-sat\)', final_query), \
                "final_query should have (check-sat) command"
            
            # 7. get-model があること（オプション）
            has_get_model = re.search(r'\(get-model\)', final_query)
            if has_get_model:
                print("✓ final_query includes (get-model) command")
            
            # 8. コメントセクションがあること（可読性のため）
            assert re.search(r';.*Pairwise Query', final_query), \
                "final_query should have header comments"
            
            print("✓ final_query structure validated:")
            print("  - set-logic declaration: ✓")
            print("  - function declarations: ✓")
            print("  - parameter equality constraints: ✓")
            print("  - case conditions: ✓")
            print("  - value inequality: ✓")
            print("  - check-sat command: ✓")
            print(f"  - total length: {len(final_query)} chars")