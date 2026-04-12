# -*- coding: utf-8 -*-
"""Monolithic戦略（全条件を一度に検証）"""

import time

from typing import Optional, Dict, Any

from ...model import FunctionReturnAnalysis
from ...smt import ParallelResult
from ..formula.symbol_replace import build_symbol_replacer
from ..param_semantics import infer_parameter_semantics
from ..semantic_width import normalize_analysis_semantic_width
from .base import CheckStrategy, StrategyResult
from .pairwise_query_builder import extract_return_cases
from .pairwise_query_executor import validate_counterexample_globally


class MonolithicStrategy(CheckStrategy):
    """Monolithic戦略（全条件を一度に検証）"""

    def _counterexample_is_decisive_across_case_split(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        counterexample_raw: Optional[Dict[str, Any]],
    ) -> bool:
        if not counterexample_raw:
            return True

        hints1 = infer_parameter_semantics(analysis1)
        hints2 = infer_parameter_semantics(analysis2)
        analysis1 = normalize_analysis_semantic_width(analysis1, hints1)
        analysis2 = normalize_analysis_semantic_width(analysis2, hints2)
        base_ctx = self.formula_builder.build_base_context(analysis1, analysis2)
        analysis1 = normalize_analysis_semantic_width(
            analysis1,
            hints1,
            base_ctx.get("extra_vars1", []),
        )
        analysis2 = normalize_analysis_semantic_width(
            analysis2,
            hints2,
            base_ctx.get("extra_vars2", []),
        )

        cases1 = extract_return_cases(analysis1)
        cases2 = extract_return_cases(analysis2)
        if not cases1 or not cases2:
            self._debug_print(
                "Monolithic SAT counterexample rejected: no return cases available for validation"
            )
            return False

        replace1 = build_symbol_replacer(
            base_ctx["params1"],
            base_ctx.get("extra_vars1", []),
        )
        replace2 = build_symbol_replacer(
            base_ctx["params2"],
            base_ctx.get("extra_vars2", []),
        )
        return validate_counterexample_globally(
            self,
            base_ctx,
            cases1,
            cases2,
            replace1,
            replace2,
            counterexample_raw,
        )
    
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

            final_is_equivalent = parallel_result.is_equivalent
            sat_unsafety_reasons = self._collect_decisive_sat_unsafety_reasons(
                analysis1,
                analysis2,
            )
            if final_is_equivalent is False:
                hints1 = infer_parameter_semantics(analysis1)
                hints2 = infer_parameter_semantics(analysis2)
                normalized1 = normalize_analysis_semantic_width(analysis1, hints1)
                normalized2 = normalize_analysis_semantic_width(analysis2, hints2)
                base_ctx = self.formula_builder.build_base_context(normalized1, normalized2)
                normalized1 = normalize_analysis_semantic_width(
                    normalized1,
                    hints1,
                    base_ctx.get("extra_vars1", []),
                )
                normalized2 = normalize_analysis_semantic_width(
                    normalized2,
                    hints2,
                    base_ctx.get("extra_vars2", []),
                )
                cases1 = extract_return_cases(normalized1)
                cases2 = extract_return_cases(normalized2)
                replace1 = build_symbol_replacer(
                    base_ctx["params1"],
                    base_ctx.get("extra_vars1", []),
                )
                replace2 = build_symbol_replacer(
                    base_ctx["params2"],
                    base_ctx.get("extra_vars2", []),
                )
                sat_unsafety_reasons.extend(
                    self._collect_return_coverage_unsafety_reasons(
                        base_ctx,
                        cases1,
                        cases2,
                        replace1,
                        replace2,
                    )
                )
            if final_is_equivalent is False and sat_unsafety_reasons:
                self._debug_print(
                    "Monolithic SAT downgraded to UNKNOWN due to unsafe analysis summary "
                    f"({', '.join(sat_unsafety_reasons)})"
                )
                final_is_equivalent = None
                counterexample_raw = None
            elif final_is_equivalent is False and not self._counterexample_is_decisive_across_case_split(
                analysis1,
                analysis2,
                counterexample_raw,
            ):
                self._debug_print(
                    "Monolithic SAT downgraded to UNKNOWN after global counterexample validation"
                )
                final_is_equivalent = None
                counterexample_raw = None
            
            return StrategyResult(
                is_equivalent=final_is_equivalent,
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
