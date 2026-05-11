# -*- coding: utf-8 -*-
"""Attempt 記録と遷移理由判定のヘルパー"""

from typing import Any, Dict, List, Optional

from .debug_trace import (
    Attempt,
    DebugTrace,
    NormalizationRuleApplication,
    PairwiseDecisiveInfo,
    TransitionReason,
)
from .result import EquivalenceResult, RewriteInfo
from .typing.fixer import TypeFixResult
from .unknown_reason import coerce_unknown_reason_records
from ..smt import ParallelResult


def get_transition_reason(
    result: EquivalenceResult,
    retry_with_type_fix: bool,
    phase_id: Optional[str] = None,
    will_try_phase4b: bool = False
) -> str:
    """結果から phase レベルの遷移理由を返す"""
    del retry_with_type_fix
    del phase_id

    if result.is_equivalent is True:
        return TransitionReason.UNSAT.value
    if result.is_equivalent is False:
        if will_try_phase4b:
            return TransitionReason.SAT_PHASE4B.value
        return TransitionReason.SAT.value
    if result.has_critical_error():
        return TransitionReason.CRITICAL_ERROR.value
    if result.is_timeout():
        return TransitionReason.TIMEOUT.value
    return TransitionReason.UNKNOWN.value


def record_attempt(
    debug_trace: DebugTrace,
    attempt_id: int,
    retry_count: int,
    phase: str,
    stage_path: List[str],
    strategy: str,
    result: Optional[bool],
    transition_reason: str,
    type_fix_result: Optional[TypeFixResult],
    rewrite_info: Optional[RewriteInfo],
    original_function1_signature: Optional[Dict[str, Any]],
    original_function2_signature: Optional[Dict[str, Any]],
    effective_function1_signature: Optional[Dict[str, Any]],
    effective_function2_signature: Optional[Dict[str, Any]],
    function1_signature_hypotheses: Optional[List[Dict[str, Any]]],
    function2_signature_hypotheses: Optional[List[Dict[str, Any]]],
    solver_results: Optional[ParallelResult],
    final_smt: Optional[str],
    counterexample: Optional[Dict[str, Any]],
    pairwise_decisive: Optional[PairwiseDecisiveInfo],
    normalization_rules: Optional[List[Any]],
    mips64_abi_constraints: Optional[Dict[str, Any]],
    elapsed_time: float,
    unknown_reasons: Optional[List[Any]] = None,
) -> None:
    """Attempt を追加する"""
    attempt = Attempt(
        attempt_id=attempt_id,
        retry_count=retry_count,
        phase=phase,
        stage_path=stage_path.copy() if stage_path else [],
        strategy=strategy,
        result=result,
        transition_reason=transition_reason,
        type_fix_result=type_fix_result.to_dict() if type_fix_result else None,
        rewrite_info=rewrite_info.to_dict() if rewrite_info else None,
        original_function1_signature=original_function1_signature,
        original_function2_signature=original_function2_signature,
        effective_function1_signature=effective_function1_signature,
        effective_function2_signature=effective_function2_signature,
        function1_signature_hypotheses=function1_signature_hypotheses or [],
        function2_signature_hypotheses=function2_signature_hypotheses or [],
        solver_results=solver_results.to_dict() if solver_results else None,
        final_smt_excerpt=final_smt[:500] if final_smt else None,
        final_smt=final_smt,
        counterexample=counterexample,
        pairwise_decisive=pairwise_decisive,
        normalization_rules=normalization_rules or [],
        unknown_reasons=list(coerce_unknown_reason_records(unknown_reasons)),
        mips64_abi_constraints=mips64_abi_constraints,
        elapsed_time=elapsed_time,
    )
    debug_trace.add_attempt(attempt)


def record_attempt_from_result(
    debug_trace: DebugTrace,
    attempt_id: int,
    retry_count: int,
    phase: str,
    result: EquivalenceResult,
    transition_reason: str,
    type_fix_result: TypeFixResult,
    strategy_name: str
) -> None:
    """EquivalenceResult から Attempt を構築して追加する"""
    pairwise_decisive = _build_pairwise_decisive_info(result)
    normalization_rules = _extract_normalization_rules(result)
    counterexample_dict = result.counterexample.to_dict() if result.counterexample else None
    mips64_abi_dict = _build_mips64_abi_dict(result)

    record_attempt(
        debug_trace=debug_trace,
        attempt_id=attempt_id,
        retry_count=retry_count,
        phase=phase,
        stage_path=result.stage_path,
        strategy=strategy_name,
        result=result.is_equivalent,
        transition_reason=transition_reason,
        type_fix_result=type_fix_result,
        rewrite_info=result.rewrite_info,
        original_function1_signature=result.function1_signature.to_dict() if result.function1_signature else None,
        original_function2_signature=result.function2_signature.to_dict() if result.function2_signature else None,
        effective_function1_signature=result.get_effective_function1_signature().to_dict() if result.get_effective_function1_signature() else None,
        effective_function2_signature=result.get_effective_function2_signature().to_dict() if result.get_effective_function2_signature() else None,
        function1_signature_hypotheses=list(result.function1_signature_hypotheses),
        function2_signature_hypotheses=list(result.function2_signature_hypotheses),
        solver_results=result.solver_results,
        final_smt=result.smt_formula,
        counterexample=counterexample_dict,
        pairwise_decisive=pairwise_decisive,
        normalization_rules=normalization_rules,
        mips64_abi_constraints=mips64_abi_dict,
        elapsed_time=result.total_time,
        unknown_reasons=list(result.unknown_reasons),
    )


def _build_pairwise_decisive_info(
    result: EquivalenceResult
) -> Optional[PairwiseDecisiveInfo]:
    if not result.pairwise_stats or result.pairwise_stats["total_pairs"] <= 0:
        return None

    decisive_result_str = "UNKNOWN"
    if result.is_equivalent is True:
        decisive_result_str = "UNSAT"
    elif result.is_equivalent is False:
        decisive_result_str = "SAT"

    decisive = PairwiseDecisiveInfo(
        decisive_result=decisive_result_str,
        total_pairs=result.pairwise_stats["total_pairs"],
        unsat_pairs=result.pairwise_stats["unsat_pairs"],
        sat_pairs=result.pairwise_stats["sat_pairs"],
        unknown_pairs=result.pairwise_stats["unknown_pairs"],
    )

    if result.sat_pair_info:
        info = result.sat_pair_info
        decisive.decisive_pair = (info["i"], info["j"])
        decisive.pair_stage = info.get("pair_stage", "unknown")
        decisive.case1_summary = info.get("case1_summary")
        decisive.case2_summary = info.get("case2_summary")
        decisive.value1_expr = info.get("value1", "")[:200]
        decisive.value2_expr = info.get("value2", "")[:200]

        final_query_full = info.get("final_query")
        if final_query_full:
            decisive.final_query = final_query_full
            decisive.final_query_excerpt = final_query_full[:200]
        elif result.smt_formula:
            decisive.final_query = result.smt_formula
            decisive.final_query_excerpt = result.smt_formula[:200]

    return decisive


def _extract_normalization_rules(result: EquivalenceResult) -> List[Any]:
    extracted: List[Any] = []
    if not hasattr(result, "normalization_rules") or not result.normalization_rules:
        return extracted

    for rule in result.normalization_rules:
        if isinstance(rule, NormalizationRuleApplication):
            extracted.append(rule)
        else:
            extracted.append(rule)
    return extracted


def _build_mips64_abi_dict(result: EquivalenceResult) -> Optional[Dict[str, Any]]:
    if not result.mips64_abi_constraints:
        return None

    return {
        key: {"signedness": value[0], "narrow_bits": value[1]}
        for key, value in result.mips64_abi_constraints.items()
    }
