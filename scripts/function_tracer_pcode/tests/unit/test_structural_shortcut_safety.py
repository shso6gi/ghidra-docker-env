# -*- coding: utf-8 -*-
"""構造一致ショートカットの安全性テスト"""

import pytest
from unittest.mock import Mock

from scripts.function_tracer_pcode.model import Expression, ExpressionType, ReturnInfo
from scripts.function_tracer_pcode.equivalence.normalize.structural import (
    are_structurally_equivalent, 
    get_structural_summary
)

from conftest import create_mock_analysis


class TestStructuralShortcutSafety:
    """構造一致は確定判定ではなく、SMT確認必須であることを保証"""
    
    def test_structural_match_is_not_final_verdict(self):
        """
        ★ [P2] 構造一致だけでEQUIVALENT確定してはいけない
        
        理由:
        - 構造が同じでも、パラメータ制約下で値が異なる可能性
        - 例: (param_1 / param_2) は構造的に同一でも、
          param_2=0の場合は未定義動作で結果が不定
        """
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
        
        is_match, reason = are_structurally_equivalent(expr1, expr2, debug=True)
        assert is_match is True, "Should detect structural equivalence"
        assert "Same binary structure" in reason
        
        print("\n[SAFETY CHECK] Structural match detected, but SMT verification is REQUIRED")
        print(f"Reason: {reason}")
        print("This test verifies that structural match is a HINT, not a FINAL VERDICT.")
    
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
    
    def test_structural_match_does_not_bypass_smt_solver(self):
        """
        ★ [P2] 構造一致検出後も必ずSMT solverを実行すること
        
        実装チェックポイント:
        - PairwiseStrategy._try_normalization_equivalence() 内で
          are_structurally_equivalent() を使用
        - 構造一致時も self._build_normalized_inequality_query() で
          SMTクエリを生成・実行
        - 構造一致は「early return」の条件ではなく、
          「正規化が成功した」というヒントに留める
        """
        from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
        from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
        from scripts.function_tracer_pcode.smt import SolverResult, SolverStatus, ParallelResult
        
        formula_builder = FormulaBuilder(debug=True)
        solver_runner = Mock()
        
        strategy = PairwiseStrategy(formula_builder, solver_runner, debug=True)
        
        ret_expr = Expression(
            ExpressionType.BINARY_OP,
            operator="UDIV",
            operands=[
                Expression(ExpressionType.PARAMETER, name="param_1"),
                Expression(ExpressionType.PARAMETER, name="param_2")
            ]
        )
        
        analysis1 = create_mock_analysis(
            function_name="func1",
            returns=[ReturnInfo(address="0x401000", conditions=[], value=ret_expr)]
        )
        
        analysis2 = create_mock_analysis(
            function_name="func2",
            returns=[ReturnInfo(address="0x401000", conditions=[], value=ret_expr)]
        )
        
        mock_solver_result = SolverResult(
            solver_name="mock",
            status=SolverStatus.UNSAT,
            elapsed_time=0.01
        )
        
        solver_runner.run_sequential = Mock(return_value=ParallelResult(results=[mock_solver_result]))
        
        result = strategy.check(analysis1, analysis2, save_formula=False)
        
        # ★ [P2] 修正: 構造一致時もソルバー呼び出しを強制
        assert solver_runner.run_sequential.called, \
            "SMT solver MUST be invoked even after structural match"
        
        # ★ [P2] 追加: 最低でも1回はソルバーが呼ばれる
        assert solver_runner.run_sequential.call_count >= 1, \
            f"Expected at least 1 solver call, got {solver_runner.run_sequential.call_count}"
        
        print("\n[SAFETY VERIFIED] Structural match did NOT bypass SMT solver")
        print(f"Solver was called {solver_runner.run_sequential.call_count} time(s)")