# -*- coding: utf-8 -*-
"""戦略基底クラス"""

from abc import ABC, abstractmethod
from typing import Optional, Dict, Any, List, Sequence
from dataclasses import dataclass, field

from ...model import FunctionReturnAnalysis
from ...model import ExpressionType
from ...model.render_smt import expression_contains_unsupported_smt_ops
from ...smt import ParallelResult


@dataclass
class StrategyResult:
    """戦略実行結果"""
    is_equivalent: Optional[bool]
    solver_results: ParallelResult
    smt_formula: Optional[str] = None
    counterexample_raw: Optional[Dict] = None
    return_var1: Optional[str] = None
    return_var2: Optional[str] = None
    constrained_fragments: List[str] = field(default_factory=list)
    
    # Pairwise 専用フィールド
    total_pairs: int = 0
    unsat_pairs: int = 0
    sat_pairs: int = 0
    unknown_pairs: int = 0
    error_pairs: int = 0
    sat_pair_info: Optional[Dict[str, Any]] = None  # (i, j, conditions, values)
    normalization_rules: List[Any] = field(default_factory=list)  # List[NormalizationRuleApplication]
    pairwise_debug_stats: Optional[Dict[str, int]] = None


class CheckStrategy(ABC):
    """等価性判定戦略の基底クラス"""
    
    def __init__(self, formula_builder, solver_runner, debug: bool = False):
        """
        Args:
            formula_builder: FormulaBuilder インスタンス
            solver_runner: ParallelSolverRunner インスタンス
            debug: デバッグモード
        """
        self.formula_builder = formula_builder
        self.solver_runner = solver_runner
        self.debug = debug
    
    @abstractmethod
    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        """
        等価性をチェック
        
        Args:
            analysis1: 関数1の解析結果
            analysis2: 関数2の解析結果
            save_formula: SMT式を保存するか
        
        Returns:
            StrategyResult
        """
        pass
    
    def _debug_print(self, msg: str):
        """デバッグ出力"""
        if self.debug:
            print(f"[{self.__class__.__name__}] {msg}")

    def _collect_decisive_sat_unsafety_reasons(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> List[str]:
        """SAT を最終確定するには危険な解析要因を収集する。"""
        reasons: List[str] = []
        for label, analysis in (("function1", analysis1), ("function2", analysis2)):
            for reason in analysis.get_decisive_sat_unsafety_reasons():
                reasons.append(f"{label}:{reason}")
        return reasons

    def _collect_return_coverage_unsafety_reasons(
        self,
        base_ctx: Dict[str, Any],
        cases1: Sequence[Any],
        cases2: Sequence[Any],
        param_replace_fn1,
        param_replace_fn2,
    ) -> List[str]:
        reasons: List[str] = []
        for label, cases, replace_fn in (
            ("function1", cases1, param_replace_fn1),
            ("function2", cases2, param_replace_fn2),
        ):
            status, detail = self._check_return_case_coverage_gap(
                base_ctx,
                cases,
                replace_fn,
                label,
            )
            if status == "gap":
                reasons.append(f"{label}:return_coverage_gap")
            elif status == "inconclusive":
                reasons.append(f"{label}:return_coverage_inconclusive")
            if detail:
                self._debug_print(detail)
        return reasons

    def _check_return_case_coverage_gap(
        self,
        base_ctx: Dict[str, Any],
        cases: Sequence[Any],
        param_replace_fn,
        label: str,
    ) -> tuple[str, Optional[str]]:
        if not cases:
            return "gap", f"{label} has no return cases after extraction"
        if any(not getattr(case, "conditions", None) for case in cases):
            return "covered", None
        if not base_ctx.get("header_lines"):
            return "inconclusive", f"{label} return-case coverage query skipped: base context has no declarations"
        if any(self._case_conditions_contain_unresolved_expression(case) for case in cases):
            return "inconclusive", f"{label} return-case coverage query skipped: unresolved condition expression"

        query = self._build_return_case_coverage_query(
            base_ctx,
            cases,
            param_replace_fn,
            label,
        )
        if query is None:
            return "inconclusive", f"{label} return-case coverage query could not be built"

        result = self.solver_runner.run_sequential(query)
        if result.is_equivalent is False:
            model = result.get_counterexample()
            detail = f"{label} has uncovered return-condition region"
            if model:
                detail += f" under model {model}"
            return "gap", detail
        if result.is_equivalent is None:
            return "inconclusive", f"{label} return-case coverage query was inconclusive"
        return "covered", None

    def _build_return_case_coverage_query(
        self,
        base_ctx: Dict[str, Any],
        cases: Sequence[Any],
        param_replace_fn,
        label: str,
    ) -> Optional[str]:
        disjuncts: List[str] = []
        for case in cases:
            conditions = list(getattr(case, "get_conditions_smt")(param_replace_fn))
            if not conditions:
                return None
            if len(conditions) == 1:
                disjuncts.append(conditions[0])
            else:
                disjuncts.append(f"(and {' '.join(conditions)})")

        if not disjuncts:
            return None

        lines = [
            f"; Return coverage gap query: {label}",
            *base_ctx.get("header_lines", []),
            f"(assert (not (or {' '.join(disjuncts)})))",
            "(check-sat)",
            "(get-model)",
        ]
        return "\n".join(lines)

    def _case_conditions_contain_unresolved_expression(self, case: Any) -> bool:
        return any(
            self._expression_contains_unresolved(getattr(cond, "expression", None))
            for cond in getattr(case, "conditions", []) or []
        )

    def _expression_contains_unresolved(self, expr: Any) -> bool:
        if expr is None:
            return False

        expr_type = getattr(expr, "expr_type", None)
        if expr_type == ExpressionType.UNKNOWN:
            return True
        if expression_contains_unsupported_smt_ops(expr):
            return True

        if expr_type == ExpressionType.PHI and getattr(expr, "value", None):
            for cond, value in expr.value:
                if cond is not None and self._expression_contains_unresolved(getattr(cond, "expression", None)):
                    return True
                if self._expression_contains_unresolved(value):
                    return True
            return False

        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_unresolved(operand):
                return True

        return False
