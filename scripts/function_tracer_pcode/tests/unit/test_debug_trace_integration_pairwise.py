# -*- coding: utf-8 -*-
"""デバッグトレース統合テスト（既存テストとの互換性確認）"""

import pytest
from unittest.mock import Mock, patch
from scripts.function_tracer_pcode.equivalence import EquivalenceChecker
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.equivalence.strategies.base import StrategyResult
from scripts.function_tracer_pcode.model import FunctionReturnAnalysis, ReturnInfo, Expression, ExpressionType


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
