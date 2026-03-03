# -*- coding: utf-8 -*-
"""Monolithic戦略（既存方式）"""

from typing import Optional, Dict

from ...model import FunctionReturnAnalysis
from ...smt import ParallelResult
from .base import CheckStrategy, StrategyResult


class MonolithicStrategy(CheckStrategy):
    """
    既存の巨大ite方式
    
    全ReturnInfoを1つの大きなite式にまとめて判定
    """
    
    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        """等価性をチェック（monolithic方式）"""
        self._debug_print("Using monolithic strategy (single large ite expression)")
        
        # 既存の build_equivalence_formula_extended を使用
        formula_result = self.formula_builder.build_equivalence_formula_extended(
            analysis1, analysis2
        )
        
        smt_formula = formula_result.formula
        return_var1 = formula_result.return_var1
        return_var2 = formula_result.return_var2
        constrained_fragments = formula_result.param_fragment_constrained
        
        if self.debug:
            print("\n" + "=" * 60)
            print("Generated SMT formula (monolithic):")
            print("=" * 60)
            print(smt_formula)
            print("=" * 60 + "\n")
        
        # ソルバー実行
        if self.debug:
            parallel_result = self.solver_runner.run_sequential(smt_formula)
        else:
            parallel_result = self.solver_runner.run_parallel(smt_formula)
        
        # 反例取得
        counterexample_raw = None
        if parallel_result.is_equivalent is False:
            counterexample_raw = parallel_result.get_counterexample()
        
        return StrategyResult(
            is_equivalent=parallel_result.is_equivalent,
            solver_results=parallel_result,
            smt_formula=smt_formula if save_formula else None,
            counterexample_raw=counterexample_raw,
            return_var1=return_var1,
            return_var2=return_var2,
            constrained_fragments=constrained_fragments
        )