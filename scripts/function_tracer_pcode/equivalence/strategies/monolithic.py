# -*- coding: utf-8 -*-
"""Monolithic戦略（全条件を一度に検証）"""

import time

from typing import Optional, Dict, Any

from ...model import FunctionReturnAnalysis
from ...smt import ParallelResult
from .base import CheckStrategy, StrategyResult


class MonolithicStrategy(CheckStrategy):
    """Monolithic戦略（全条件を一度に検証）"""
    
    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        """等価性をチェック（monolithic方式）"""
        start_time = time.time()  # ★ これで使える
        
        try:
            # SMT式を構築
            result = self.formula_builder.build_equivalence_formula_extended(
                analysis1, analysis2
            )
            smt_formula = result.formula
            return_var1 = result.return_var1
            return_var2 = result.return_var2
            constrained_fragments = result.constrained_fragments
            
            if self.debug:
                print("\n" + "=" * 60)
                print("Generated SMT formula (monolithic):")
                print("=" * 60)
                print(smt_formula)
                print("=" * 60 + "\n")
            
            # ソルバーを実行
            if self.debug:
                parallel_result = self.solver_runner.run_sequential(smt_formula)
            else:
                parallel_result = self.solver_runner.run_parallel(smt_formula)
            
            # 反例を取得
            counterexample_raw = None
            if parallel_result.is_equivalent is False:
                counterexample_raw = parallel_result.get_counterexample()
            
            return StrategyResult(
                is_equivalent=parallel_result.is_equivalent,
                solver_results=parallel_result,
                smt_formula=smt_formula,  # ★ 修正: save_formula の条件を削除（常に保存）
                counterexample_raw=counterexample_raw,
                return_var1=return_var1,
                return_var2=return_var2,
                constrained_fragments=constrained_fragments
            )
        
        except Exception as e:
            self._debug_print(f"Exception in monolithic check: {e}")
            if self.debug:
                import traceback
                print(traceback.format_exc())
            
            return StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[]),
                smt_formula=None,
                counterexample_raw=None,
                return_var1=None,
                return_var2=None,
                constrained_fragments=[]
            )
