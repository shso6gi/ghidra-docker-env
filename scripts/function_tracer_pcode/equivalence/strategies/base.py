# -*- coding: utf-8 -*-
"""戦略基底クラス"""

from abc import ABC, abstractmethod
from typing import Optional, Dict, Any, List, Sequence, Tuple
from dataclasses import dataclass, field

from ...analysis.condition.smt_oracle import ConditionSMTOracle
from ...model import Condition, Expression, FunctionReturnAnalysis, expression_provenance_key
from ...model import ExpressionType
from ...model.render_smt import expression_contains_unsupported_smt_ops
from ...smt import ParallelResult
from ..unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
    UnknownReasonId,
    UnknownReasonRecord,
    coerce_unknown_reason_records,
    make_unknown_reason,
)


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

    def _unknown_reason_id_for_blocking_unsafety(self, reason: Optional[str]):
        reason_kind = self._blocking_reason_kind(reason)
        if reason_kind == "return_coverage_gap":
            return UnknownReasonId.RETURN_COVERAGE_GAP
        if reason_kind == "return_coverage_inconclusive":
            return UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
        if reason_kind in {"recoverable_partial", "argument_recovery_recoverable_partial"}:
            return UnknownReasonId.RECOVERABLE_PARTIAL
        return UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY

    def _make_blocking_unsafety_unknown_reason(
        self,
        blocking_reason: str,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        *,
        stage: str,
    ):
        typed_reason_id = self._unknown_reason_id_for_blocking_unsafety(blocking_reason)
        if typed_reason_id != UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY:
            return make_unknown_reason(
                typed_reason_id,
                stage=stage,
                evidence_refs=(blocking_reason,),
                detail=blocking_reason,
            )

        object_target_key = self._call_effect_blocking_object_target_key(
            blocking_reason,
            analysis1,
            analysis2,
        )
        if object_target_key is None:
            return make_unknown_reason(
                typed_reason_id,
                stage=stage,
                evidence_refs=(blocking_reason,),
                detail=blocking_reason,
            )

        return make_unknown_reason(
            typed_reason_id,
            stage=stage,
            evidence_refs=(blocking_reason,),
            detail=blocking_reason,
            recovery_proof_kind=UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
            recovery_proof_obligations=(
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
                    "object_evidence_collected",
                    required_evidence=(
                        "call_effect_summary",
                        "runtime_ref",
                        "callsite_storage",
                    ),
                    description="Collect object-derived call/effect evidence before using UNSAT as equivalence proof.",
                ),
            ),
            proof_stage="object_evidence_collected",
            evidence_kind="call_effect_summary",
            object_target_key=object_target_key,
            recovery_action="call_effect_summary_proof_required",
            action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        )

    def _call_effect_blocking_object_target_key(
        self,
        blocking_reason: str,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> Optional[Tuple[Any, ...]]:
        label, reason_text = self._split_blocking_reason(blocking_reason)
        reason_kind = self._blocking_reason_kind(blocking_reason)
        if reason_kind not in {
            "unsupported_call_effect_summary",
            "effect_summary_path_coverage_incomplete",
            "effect_call_argument_evidence_incomplete",
            "bounded_call_refinement_argument_alignment_failed",
            "bounded_call_refinement_deferred_target_unresolved",
            "bounded_call_refinement_return_summary_unusable",
        }:
            return None
        analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
        if analysis is None:
            return None
        deferred_call_keys = tuple(
            self._deferred_call_object_target_key(info, analysis=analysis, side_label=label)
            for info in getattr(analysis, "deferred_calls", {}).values()
            if self._deferred_call_is_blocking(info)
        )
        effect_summary = getattr(analysis, "effect_summary", None)
        evidence_keys = ()
        unsupported_call_site_keys = ()
        if effect_summary is not None:
            evidence_keys = tuple(
                self._call_argument_evidence_object_key(
                    evidence,
                    analysis=analysis,
                    side_label=label,
                )
                for evidence in getattr(effect_summary, "call_argument_evidence", {}).values()
                if evidence is not None
            )
            unsupported_call_site_keys = tuple(
                self._unsupported_call_effect_object_key(
                    site,
                    analysis=analysis,
                    side_label=label,
                )
                for site in getattr(effect_summary, "unsupported_call_sites", ()) or ()
                if site is not None
            )
        selected_deferred_keys: Tuple[Any, ...] = ()
        selected_evidence_keys: Tuple[Any, ...] = ()
        selected_unsupported_keys: Tuple[Any, ...] = ()

        if reason_kind == "unsupported_call_effect_summary":
            selected_unsupported_keys = unsupported_call_site_keys
            if len(selected_unsupported_keys) == 1:
                return selected_unsupported_keys[0]
        elif reason_kind == "effect_call_argument_evidence_incomplete":
            selected_evidence_keys = evidence_keys
            if not selected_evidence_keys:
                selected_deferred_keys = deferred_call_keys
                if len(selected_deferred_keys) == 1:
                    return selected_deferred_keys[0]
        elif reason_kind in {
            "bounded_call_refinement_argument_alignment_failed",
            "bounded_call_refinement_deferred_target_unresolved",
            "bounded_call_refinement_return_summary_unusable",
        }:
            selected_deferred_keys = deferred_call_keys
            if len(selected_deferred_keys) == 1:
                return selected_deferred_keys[0]
        elif reason_kind == "effect_summary_path_coverage_incomplete":
            selected_evidence_keys = evidence_keys
            selected_unsupported_keys = unsupported_call_site_keys

        return (
            "call_effect_blocker",
            label,
            self._analysis_entry_key(analysis),
            reason_kind,
            reason_text,
            selected_deferred_keys,
            selected_evidence_keys,
            selected_unsupported_keys,
        )

    @staticmethod
    def _split_blocking_reason(blocking_reason: str) -> Tuple[str, str]:
        text = str(blocking_reason or "")
        if ":" not in text:
            return "", text
        label, reason = text.split(":", 1)
        return label, reason

    @classmethod
    def _blocking_reason_kind(cls, blocking_reason: Optional[str]) -> str:
        _label, reason = cls._split_blocking_reason(str(blocking_reason or ""))
        return reason.split(":", 1)[0]

    @staticmethod
    def _deferred_call_is_blocking(info: Any) -> bool:
        status = getattr(info, "call_argument_recovery_status", None)
        return status != "complete"

    def _deferred_call_object_target_key(
        self,
        info: Any,
        *,
        analysis: Optional[FunctionReturnAnalysis] = None,
        side_label: Optional[str] = None,
    ) -> Tuple[Any, ...]:
        deferred_ref = getattr(info, "deferred_call_ref", None)
        target_ref = getattr(info, "target_ref", None)
        pcode_op_ref = getattr(deferred_ref, "pcode_op_ref", None)
        target_expr_key = self._typed_target_expression_key(
            getattr(info, "call_target_expr", None)
        )
        return (
            "deferred_call",
            side_label,
            self._analysis_entry_key(analysis) if analysis is not None else None,
            self._stable_key_or_none(deferred_ref),
            self._stable_key_or_none(pcode_op_ref),
            self._stable_key_or_none(target_ref),
            target_expr_key,
            tuple(
                (
                    "argument",
                    index,
                    self._expression_runtime_object_key(argument),
                )
                for index, argument in enumerate(getattr(info, "arguments", ()) or ())
            ),
            getattr(info, "call_argument_recovery_status", None),
        )

    def _call_argument_evidence_object_key(
        self,
        evidence: Any,
        *,
        analysis: Optional[FunctionReturnAnalysis] = None,
        side_label: Optional[str] = None,
    ) -> Tuple[Any, ...]:
        return (
            "call_argument_evidence",
            side_label,
            self._analysis_entry_key(analysis) if analysis is not None else None,
            self._stable_key_or_none(evidence),
            self._stable_key_or_none(getattr(evidence, "target_ref", None)),
            tuple(
                (
                    "argument",
                    index,
                    self._expression_runtime_object_key(argument),
                )
                for index, argument in enumerate(getattr(evidence, "arguments", ()) or ())
            ),
            bool(getattr(evidence, "coverage_complete", False)),
            getattr(evidence, "recovery_status", None),
        )

    def _unsupported_call_effect_object_key(
        self,
        site: Any,
        *,
        analysis: Optional[FunctionReturnAnalysis] = None,
        side_label: Optional[str] = None,
    ) -> Tuple[Any, ...]:
        return (
            "unsupported_call_effect",
            side_label,
            self._analysis_entry_key(analysis) if analysis is not None else None,
            self._stable_key_or_none(getattr(site, "pcode_op_ref", None)),
            self._stable_key_or_none(getattr(site, "target_ref", None)),
            self._typed_target_expression_key(getattr(site, "target_expr", None)),
            int(getattr(site, "order_key", 0) or 0),
            getattr(site, "reason", None),
        )

    @classmethod
    def _typed_target_expression_key(cls, expr: Any) -> Optional[Tuple[Any, ...]]:
        if expr is None:
            return None
        return ("typed_target_expression", cls._expression_runtime_object_key(expr))

    @staticmethod
    def _analysis_entry_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        function_ref = getattr(analysis, "function_ref", None)
        stable_key = getattr(function_ref, "stable_key", None)
        if callable(stable_key):
            try:
                key = stable_key()
                if key is not None:
                    return ("function_ref", key)
            except (AttributeError, TypeError, ValueError, RecursionError):
                pass
        return ("entry_point", getattr(analysis, "entry_point", None))

    @staticmethod
    def _stable_key_or_none(value: Any):
        stable_key = getattr(value, "stable_key", None)
        if callable(stable_key):
            try:
                return stable_key()
            except (AttributeError, TypeError, ValueError, RecursionError):
                return None
        return None

    @classmethod
    def _expression_runtime_object_key(cls, expr: Any) -> Tuple[Any, ...]:
        return expression_provenance_key(expr)

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
        case_conditions = [
            condition
            for case in cases
            for condition in (getattr(case, "conditions", None) or ())
        ]
        if not ConditionSMTOracle.has_object_identity_support(case_conditions):
            return None
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
