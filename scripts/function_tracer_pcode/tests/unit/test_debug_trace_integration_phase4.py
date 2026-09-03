# -*- coding: utf-8 -*-
"""デバッグトレース統合テスト（既存テストとの互換性確認）"""

import pytest
from unittest.mock import Mock, patch
from scripts.function_tracer_pcode.checker import EquivalenceChecker
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.proof.strategies.base import StrategyResult
from scripts.function_tracer_pcode.core import (
    FunctionReturnAnalysis,
    ReturnInfo,
    Expression,
    ExpressionType,
)


def test_debug_trace_phase4a_to_phase4b_transition(mock_program_mips64, mock_program_x86):
    """Phase 4-A SAT → Phase 4-B の transition_reason が SAT->Phase4B になることを確認"""
    from scripts.function_tracer_pcode.checker import EquivalenceChecker
    from unittest.mock import Mock, patch
    from scripts.function_tracer_pcode.core import (
        FunctionReturnAnalysis,
        ReturnInfo,
        Expression,
        ExpressionType,
    )
    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult
    from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
    from scripts.function_tracer_pcode.checker.phases.handler import PhaseResult, PhaseID
    
    checker = EquivalenceChecker(debug=False, strategy="pairwise", canonical_decision_cutover=False)
    
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
    from scripts.function_tracer_pcode.checker import EquivalenceChecker
    from unittest.mock import Mock, patch
    from scripts.function_tracer_pcode.core import (
        FunctionReturnAnalysis,
        ReturnInfo,
        Expression,
        ExpressionType,
    )
    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult
    from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
    from scripts.function_tracer_pcode.checker.phases.handler import PhaseResult, PhaseID
    import json
    
    checker = EquivalenceChecker(debug=False, strategy="pairwise", canonical_decision_cutover=False)
    
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
    from scripts.function_tracer_pcode.checker.debug_trace import Attempt
    
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
