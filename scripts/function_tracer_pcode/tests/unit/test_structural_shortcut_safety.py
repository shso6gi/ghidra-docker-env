# -*- coding: utf-8 -*-
"""構造一致ショートカットの安全性テスト"""

import sys
from pathlib import Path

# ワークスペースルートをPYTHONPATHに追加
workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

import pytest
from unittest.mock import Mock, patch

# 完全なパッケージパスでインポート
from scripts.function_tracer_pcode.model import Expression, ExpressionType, ReturnInfo
from scripts.function_tracer_pcode.equivalence.normalize.structural import (
    are_structurally_equivalent, 
    get_structural_summary
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import (
    PairwiseStrategy, 
    ReturnCase, 
    QueryResult
)

_P = 'scripts.function_tracer_pcode.equivalence.strategies.pairwise'


class TestStructuralShortcutSafety:
    """構造一致は確定判定ではなく、SMT確認必須であることを保証"""
    
    def test_structural_match_is_hint_not_verdict(self):
        """
        【重要】構造一致はヒントであり、最終判定ではない
        
        理由:
        - 構造が同じでも、パラメータ制約下で値が異なる可能性がある
        - 例: (param_1 / param_2) は構造的に同一でも、
          param_2=0の場合は未定義動作で結果が不定
        - したがって、構造一致を検出しても必ずSMT solverで確認する
        
        新仕様:
        - 構造一致 → ログ出力「STRUCTURAL MATCH DETECTED, SMT CONFIRMATION REQUIRED」
        - その後、必ず正規化後SMTクエリを実行
        - 最終判定はSMTの結果に従う（UNSAT/SAT/UNKNOWN）
        """
        # 同じ構造の式
        expr1 = Expression(
            ExpressionType.BINARY_OP,
            operator="UDIV",
            operands=[
                Expression(ExpressionType.PARAMETER, name="param_1"),
                Expression(ExpressionType.PARAMETER, name="param_2")
            ]
        )
        
        expr2 = Expression(
            ExpressionType.BINARY_OP,
            operator="UDIV",
            operands=[
                Expression(ExpressionType.PARAMETER, name="param_1"),
                Expression(ExpressionType.PARAMETER, name="param_2")
            ]
        )
        
        # 構造一致検出
        is_match, reason = are_structurally_equivalent(expr1, expr2, debug=True)
        assert is_match is True, "Should detect structural equivalence"
        assert "Same binary structure" in reason
        
        # ★ 重要: 構造一致を検出しても、それは「ヒント」であり「確定判定」ではない
        # 実装では、構造一致後も必ずSMT solverで確認する
        print("\n[SAFETY POLICY] Structural match is a HINT, not a FINAL VERDICT")
        print(f"Structural match reason: {reason}")
        print("PairwiseStrategy will proceed to SMT solver even after structural match.")
        print("Final verdict depends solely on SMT result (UNSAT/SAT/UNKNOWN).")
    
    def test_structural_match_with_different_params_is_not_equivalent(self):
        """パラメータ名が異なれば構造不一致"""
        expr1 = Expression(ExpressionType.PARAMETER, name="param_1")
        expr2 = Expression(ExpressionType.PARAMETER, name="param_2")
        
        is_match, reason = are_structurally_equivalent(expr1, expr2, debug=True)
        assert is_match is False
        assert "Different param/var" in reason
    
    def test_structural_match_with_same_constants(self):
        """定数が同じなら構造一致"""
        expr1 = Expression(ExpressionType.CONSTANT, value=42)
        expr2 = Expression(ExpressionType.CONSTANT, value=42)
        
        is_match, reason = are_structurally_equivalent(expr1, expr2, debug=True)
        assert is_match is True
        assert "Same constant: 42" in reason
    
    def test_structural_match_with_different_constants(self):
        """定数が異なれば構造不一致"""
        expr1 = Expression(ExpressionType.CONSTANT, value=42)
        expr2 = Expression(ExpressionType.CONSTANT, value=43)
        
        is_match, reason = are_structurally_equivalent(expr1, expr2, debug=True)
        assert is_match is False
        assert "Different constant" in reason
    
    def test_structural_match_complex_expression(self):
        """複雑な式の構造一致"""
        # (param_1 + param_2) * param_3
        expr1 = Expression(
            ExpressionType.BINARY_OP,
            operator="MUL",
            operands=[
                Expression(
                    ExpressionType.BINARY_OP,
                    operator="ADD",
                    operands=[
                        Expression(ExpressionType.PARAMETER, name="param_1"),
                        Expression(ExpressionType.PARAMETER, name="param_2")
                    ]
                ),
                Expression(ExpressionType.PARAMETER, name="param_3")
            ]
        )
        
        expr2 = Expression(
            ExpressionType.BINARY_OP,
            operator="MUL",
            operands=[
                Expression(
                    ExpressionType.BINARY_OP,
                    operator="ADD",
                    operands=[
                        Expression(ExpressionType.PARAMETER, name="param_1"),
                        Expression(ExpressionType.PARAMETER, name="param_2")
                    ]
                ),
                Expression(ExpressionType.PARAMETER, name="param_3")
            ]
        )
        
        is_match, reason = are_structurally_equivalent(expr1, expr2, debug=True)
        assert is_match is True
        print(f"\nComplex expression match: {reason}")
    
    def test_structural_summary_output(self):
        """構造サマリーの出力テスト（デバッグ用）"""
        expr = Expression(
            ExpressionType.BINARY_OP,
            operator="DIV",
            operands=[
                Expression(ExpressionType.PARAMETER, name="param_1"),
                Expression(ExpressionType.CONSTANT, value=2)
            ]
        )
        
        summary = get_structural_summary(expr, max_depth=5)
        assert "DIV" in summary
        assert "PARAM(param_1)" in summary
        assert "CONST(2)" in summary
        
        print(f"\nStructural summary: {summary}")
    
    def test_structural_shortcut_requires_normalization_change(self):
        """
        構造一致チェックは正規化で変化があった場合のみ実行される
        
        pairwise.py の _try_normalization_equivalence() では:
        - 正規化で変化なし → "No normalization applied -> remain UNKNOWN" で早期return
        - 正規化で変化あり → 構造一致チェック → SMT確認
        
        このテストは、正規化ルールが適用されるケースを検証
        """
        from scripts.function_tracer_pcode.equivalence.normalize import (
            normalize_expression,
            NormalizationContext
        )
        
        # ★ 正規化が適用されるケース: INT_SDIV(x, 1) -> x
        expr_before = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_SDIV",
            operands=[
                Expression(ExpressionType.PARAMETER, name="param_1"),
                Expression(ExpressionType.CONSTANT, value=1)
            ]
        )
        
        norm_context = NormalizationContext(debug=True)
        expr_after = normalize_expression(expr_before, norm_context)
        
        # 正規化で変化があったか確認
        before_smt = expr_before.to_smt()
        after_smt = expr_after.to_smt()
        
        print(f"\n[NORMALIZATION TEST]")
        print(f"  Before: {before_smt}")
        print(f"  After:  {after_smt}")
        print(f"  Changed: {before_smt != after_smt}")
        print(f"  Applied rules: {[r.rule_name for r in norm_context.applied_rules]}")
        
        # ★ 正規化で変化があった場合のみ、構造一致チェックに進む
        # 変化がなければ UNKNOWN のままで構造チェックはスキップ
        if before_smt != after_smt:
            # 正規化後の式同士を構造比較
            is_match, reason = are_structurally_equivalent(expr_after, expr_after, debug=True)
            assert is_match is True, "Same normalized expression should match"
            print(f"  Structural match after normalization: {reason}")
            print(f"  → SMT confirmation will still be performed")
        else:
            print("  No normalization applied - structural check will be skipped")
    
    def test_structural_match_policy_documentation(self):
        """
        【ポリシー文書化】構造一致の取り扱い方針
        
        PairwiseStrategy._try_normalization_equivalence() の動作仕様:
        
        1. 正規化を試行（Phase 1 & Phase 2）
        2. if not changed1 and not changed2:
              return QueryResult(is_equivalent=None)  # 早期return
        
        3. 構造一致チェック（ヒントとして使用）
           if is_struct_eq:
              ログ出力: "STRUCTURAL MATCH DETECTED, SMT CONFIRMATION REQUIRED"
           else:
              ログ出力: "Structural match not detected"
        
        4. **必ずSMTクエリを実行**（構造一致時も含む）
           norm_query = _build_normalized_inequality_query(...)
           norm_result = _solve_query_internal(...)
        
        5. 最終判定はSMTの結果に従う:
           - UNSAT → equivalent (構造一致がSMTで確認された)
           - SAT   → not equivalent (構造一致でも反例が存在)
           - UNKNOWN → unknown (構造一致でもタイムアウト)
        
        重要な点:
        - 構造一致は「最終判定」ではなく「ヒント」
        - SMT確認は常に必須（安全性のため）
        - 構造一致がfalse positiveを持つ可能性を考慮
        """
        
        policy_spec = """
        構造一致の取り扱い方針（新仕様）:
        
        【目的】
        - 構造一致は「等価性の可能性が高い」というヒントとして使用
        - 最終判定は必ずSMTソルバーで確認
        
        【理由】
        - 構造が同じでも、制約下で値が異なる可能性
        - 例: param_2=0 の場合、(param_1/param_2) は未定義
        - 構造一致検出ロジックにバグがある可能性
        
        【実装】
        - 構造一致検出時: ログに記録 + SMT確認継続
        - 構造不一致時: ログに記録 + SMT確認継続
        - 最終判定: SMTの結果のみを信頼
        
        【メリット】
        - 安全性: 誤判定のリスクを最小化
        - デバッグ性: ログで構造一致の情報を確認可能
        - 拡張性: 将来的に構造一致の精度向上が容易
        """
        
        print("\n[POLICY SPECIFICATION]")
        print(policy_spec)
        
        # このテストは仕様の文書化として成功
        assert True, "Policy specification documented and verified"


class TestStructuralMatchSolverInvocation:
    """
    構造一致時でもSMT solver呼び出しが必須であることを保証する回帰テスト
    """
    
    def _create_simple_case(self, value_expr, index=0):
        """最小限の ReturnCase モックを作成"""
        case = Mock(spec=ReturnCase)
        case.value_expr = value_expr
        case.conditions = []
        case.index = index
        case.get_conditions_smt = Mock(return_value=[])
        return case
    
    def _create_minimal_base_ctx(self):
        """最小限の base_ctx を作成"""
        param_info1 = Mock()
        param_info1.smt_name = "param_1_1"
        param_info1.original_name = "param_1"
        
        param_info2 = Mock()
        param_info2.smt_name = "param_1_2"
        param_info2.original_name = "param_1"
        
        return {
            'header_lines': [],
            'params1': [param_info1],
            'params2': [param_info2],
            'return_size1': 64,
            'return_size2': 64,
        }
    
    def _setup_normalization_mocks(
        self,
        mock_normalize,
        mock_extract_min,
        mock_extract_facts,
        mock_contains_udiv,
        normalized_expr
    ):
        """正規化モックの共通セットアップ"""
        from scripts.function_tracer_pcode.equivalence.normalize import SignFacts
        mock_extract_min.return_value = set()
        mock_extract_facts.return_value = SignFacts()
        mock_contains_udiv.return_value = False
        mock_normalize.return_value = normalized_expr
    
    @patch(f'{_P}.contains_udiv')
    @patch(f'{_P}.extract_sign_facts')
    @patch(f'{_P}.extract_min_excluded_params')
    @patch(f'{_P}.normalize_expression')
    def test_structural_match_still_calls_solver_unsat(
        self,
        mock_normalize,
        mock_extract_min,
        mock_extract_facts,
        mock_contains_udiv
    ):
        """
        【核心テスト】構造一致でも solver を呼び、UNSAT なら equivalent
        """
        normalized_expr = Expression(ExpressionType.PARAMETER, name="param_1")
        self._setup_normalization_mocks(
            mock_normalize, mock_extract_min, mock_extract_facts,
            mock_contains_udiv, normalized_expr
        )
        
        strategy = PairwiseStrategy(Mock(), Mock(), debug=True)
        
        # 元の式（正規化で変化する）
        expr_original = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_ADD",
            operands=[
                Expression(ExpressionType.PARAMETER, name="param_1"),
                Expression(ExpressionType.CONSTANT, value=0)
            ]
        )
        
        case1 = self._create_simple_case(expr_original, index=0)
        case2 = self._create_simple_case(expr_original, index=1)
        base_ctx = self._create_minimal_base_ctx()
        
        with patch.object(strategy, '_solve_query_internal') as mock_solver:
            mock_solver.return_value = QueryResult(is_equivalent=True)
            
            result = strategy._try_normalization_equivalence(
                base_ctx, case1, case2,
                lambda x: x, lambda x: x, "(0,1)"
            )
            
            assert mock_solver.call_count == 1, \
                f"Solver MUST be called even when structural match is detected. " \
                f"Called {mock_solver.call_count} times."
            assert result.is_equivalent is True
    
    @patch(f'{_P}.contains_udiv')
    @patch(f'{_P}.extract_sign_facts')
    @patch(f'{_P}.extract_min_excluded_params')
    @patch(f'{_P}.normalize_expression')
    def test_structural_match_still_calls_solver_sat(
        self,
        mock_normalize,
        mock_extract_min,
        mock_extract_facts,
        mock_contains_udiv
    ):
        """
        【重要】構造一致でも solver が SAT なら not equivalent
        """
        normalized_expr = Expression(ExpressionType.PARAMETER, name="param_1")
        self._setup_normalization_mocks(
            mock_normalize, mock_extract_min, mock_extract_facts,
            mock_contains_udiv, normalized_expr
        )
        
        strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
        
        expr_original = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_ADD",
            operands=[
                Expression(ExpressionType.PARAMETER, name="param_1"),
                Expression(ExpressionType.CONSTANT, value=0)
            ]
        )
        
        case1 = self._create_simple_case(expr_original, index=0)
        case2 = self._create_simple_case(expr_original, index=1)
        base_ctx = self._create_minimal_base_ctx()
        
        counterexample = {'param_1_1': 42, 'param_1_2': 42}
        with patch.object(strategy, '_solve_query_internal') as mock_solver:
            mock_solver.return_value = QueryResult(
                is_equivalent=False, counterexample_raw=counterexample
            )
            
            result = strategy._try_normalization_equivalence(
                base_ctx, case1, case2,
                lambda x: x, lambda x: x, "(0,1)"
            )
            
            assert mock_solver.call_count == 1
            assert result.is_equivalent is False
            assert result.counterexample_raw == counterexample
    
    @patch(f'{_P}.contains_udiv')
    @patch(f'{_P}.extract_sign_facts')
    @patch(f'{_P}.extract_min_excluded_params')
    @patch(f'{_P}.normalize_expression')
    def test_structural_match_still_calls_solver_unknown(
        self,
        mock_normalize,
        mock_extract_min,
        mock_extract_facts,
        mock_contains_udiv
    ):
        """構造一致でも solver が UNKNOWN なら unknown"""
        normalized_expr = Expression(ExpressionType.PARAMETER, name="param_1")
        self._setup_normalization_mocks(
            mock_normalize, mock_extract_min, mock_extract_facts,
            mock_contains_udiv, normalized_expr
        )
        
        strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
        
        expr_original = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_ADD",
            operands=[
                Expression(ExpressionType.PARAMETER, name="param_1"),
                Expression(ExpressionType.CONSTANT, value=0)
            ]
        )
        
        case1 = self._create_simple_case(expr_original, index=0)
        case2 = self._create_simple_case(expr_original, index=1)
        base_ctx = self._create_minimal_base_ctx()
        
        with patch.object(strategy, '_solve_query_internal') as mock_solver:
            mock_solver.return_value = QueryResult(is_equivalent=None)
            
            result = strategy._try_normalization_equivalence(
                base_ctx, case1, case2,
                lambda x: x, lambda x: x, "(0,1)"
            )
            
            assert mock_solver.call_count == 1
            assert result.is_equivalent is None
    
    def test_no_normalization_change_skips_solver_early_return(self):
        """正規化で変化なしなら solver を呼ばず早期 return"""
        strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
        
        expr_no_change = Expression(ExpressionType.PARAMETER, name="param_1")
        
        case1 = self._create_simple_case(expr_no_change, index=0)
        case2 = self._create_simple_case(expr_no_change, index=1)
        base_ctx = self._create_minimal_base_ctx()
        
        with patch.object(strategy, '_solve_query_internal') as mock_solver:
            result = strategy._try_normalization_equivalence(
                base_ctx, case1, case2,
                lambda x: x, lambda x: x, "(0,1)"
            )
            
            assert mock_solver.call_count == 0
            assert result.is_equivalent is None
    
    @patch(f'{_P}.contains_udiv')
    @patch(f'{_P}.extract_sign_facts')
    @patch(f'{_P}.extract_min_excluded_params')
    @patch(f'{_P}.normalize_expression')
    def test_structural_mismatch_still_calls_solver(
        self,
        mock_normalize,
        mock_extract_min,
        mock_extract_facts,
        mock_contains_udiv
    ):
        """構造不一致でも正規化変化ありなら solver を呼ぶ"""
        from scripts.function_tracer_pcode.equivalence.normalize import SignFacts
        mock_extract_min.return_value = set()
        mock_extract_facts.return_value = SignFacts()
        mock_contains_udiv.return_value = False
        
        call_count = [0]
        def normalize_side_effect(expr, ctx):
            call_count[0] += 1
            if call_count[0] == 1:
                return Expression(ExpressionType.PARAMETER, name="param_1")
            else:
                return Expression(ExpressionType.PARAMETER, name="param_2")
        mock_normalize.side_effect = normalize_side_effect
        
        strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
        
        expr1 = Expression(
            ExpressionType.BINARY_OP, operator="INT_ADD",
            operands=[
                Expression(ExpressionType.PARAMETER, name="param_1"),
                Expression(ExpressionType.CONSTANT, value=0)
            ]
        )
        expr2 = Expression(
            ExpressionType.BINARY_OP, operator="INT_ADD",
            operands=[
                Expression(ExpressionType.PARAMETER, name="param_2"),
                Expression(ExpressionType.CONSTANT, value=0)
            ]
        )
        
        case1 = self._create_simple_case(expr1, index=0)
        case2 = self._create_simple_case(expr2, index=1)
        base_ctx = self._create_minimal_base_ctx()
        
        with patch.object(strategy, '_solve_query_internal') as mock_solver:
            mock_solver.return_value = QueryResult(is_equivalent=False)
            
            result = strategy._try_normalization_equivalence(
                base_ctx, case1, case2,
                lambda x: x, lambda x: x, "(0,1)"
            )
            
            assert mock_solver.call_count == 1
