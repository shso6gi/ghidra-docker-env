# -*- coding: utf-8 -*-
"""戦略基底クラス"""

from abc import ABC, abstractmethod
from typing import Optional, Dict, Any, List, Sequence
from dataclasses import dataclass, field

from ...analysis.condition.smt_oracle import ConditionSMTOracle
from ...model import Condition, Expression, FunctionReturnAnalysis
from ...model import ExpressionType
from ...model.render_smt import expression_contains_unsupported_smt_ops
from ...smt import ParallelResult
from ..unknown_reason import UnknownReasonRecord, coerce_unknown_reason_records


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
    unknown_reasons: List[UnknownReasonRecord] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.unknown_reasons = list(coerce_unknown_reason_records(self.unknown_reasons))


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

    def _collect_equivalence_blocking_unsafety_reasons(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> List[str]:
        """UNSAT を final EQUIVALENT と確定するには危険な解析要因を収集する。"""
        reasons: List[str] = []
        for label, analysis in (("function1", analysis1), ("function2", analysis2)):
            getter = getattr(analysis, "get_equivalence_blocking_unsafety_reasons", None)
            if not callable(getter):
                continue
            for reason in getter():
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
        object_centric_status = self._return_cases_have_object_centric_total_coverage(
            cases
        )
        if object_centric_status is True:
            return "covered", None
        if object_centric_status is False:
            return (
                "gap",
                f"{label} object-centric return-case coverage check found uncovered region",
            )
        if object_centric_status is None:
            case_conditions = [
                cond
                for case in (cases or ())
                for cond in (getattr(case, "conditions", None) or ())
            ]
            if not ConditionSMTOracle.has_object_identity_support(case_conditions):
                return (
                    "inconclusive",
                    f"{label} return-case object-centric coverage check was inconclusive",
                )
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

    def _return_cases_have_object_centric_total_coverage(
        self,
        cases: Sequence[Any],
    ) -> Optional[bool]:
        if not cases:
            return False
        if any(not getattr(case, "conditions", None) for case in cases):
            return True
        smt_result = self._return_cases_have_smt_total_coverage(cases)
        if smt_result is not None:
            return smt_result
        return None

    def _return_cases_have_smt_total_coverage(
        self,
        cases: Sequence[Any],
    ) -> Optional[bool]:
        """Prove coverage from Condition objects without rendered-query plumbing.

        A coverage gap exists iff every return case can be missed at once.
        For a case with conditions c1..cn, the case is missed by
        (not c1) or ... or (not cn).  If the conjunction of all case-miss
        formulas is UNSAT, the return partition is total.
        """

        miss_conditions: List[Condition] = []
        for case in cases or ():
            conditions = list(getattr(case, "conditions", None) or [])
            if not conditions:
                return True
            miss_expr = self._case_miss_expression(conditions)
            if miss_expr is None:
                return None
            miss_conditions.append(Condition(miss_expr, False))
        if not miss_conditions:
            return False
        return ConditionSMTOracle.conjunction_is_unsat(miss_conditions)

    def _case_miss_expression(
        self,
        conditions: Sequence[Condition],
    ) -> Optional[Expression]:
        miss_terms = [self._negated_condition_expression(condition) for condition in conditions]
        miss_terms = [term for term in miss_terms if term is not None]
        if not miss_terms:
            return None
        result = miss_terms[0]
        for term in miss_terms[1:]:
            result = Expression.binary_op("BOOL_OR", result, term)
        return result

    def _negated_condition_expression(
        self,
        condition: Condition,
    ) -> Optional[Expression]:
        expr = getattr(condition, "expression", None)
        if expr is None:
            return None
        if bool(getattr(condition, "negated", False)):
            return expr
        return Expression.unary_op("BOOL_NEGATE", expr)

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
