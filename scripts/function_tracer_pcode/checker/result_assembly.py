"""Finishing / result assembly / exception-result factories for :meth:`EquivalenceChecker.check` (Phase 6b-5, #82).

E・F 段（結果組み立て）と G 段（例外 → result）の **本体** を、checker facade を直接書き換えず明示的な入力を受け取る
module-level の関数に移す。トップレベルの ``try/except`` 自体、handler の種類と順序、どの処理の例外がどの handler に
捕捉されるか（catch scope）は orchestration として ``check()`` に残す。

- :func:`assemble_equivalence_result` — 通常経路。identity 計算 → debug の SMT 出力 → total_time → 反例整形 →
  completed proof payload / completion contexts → ``EquivalenceResult(...)`` → 私的付帯 3 つ
  （``_prepared_dispatch_frame`` / ``_strategy_result`` / ``_inconclusive_comparison_authority``）を旧順序で行う。
- :func:`unsupported_smt_result` — ``UnknownSmtExtensionWidthError`` / ``UnsupportedSmtOperatorError`` handler の本体。
- :func:`canonical_abi_error_result` — ``ReturnAbiAuthorityInvalid`` 用の canonical error result。
  その他の例外は従来どおり ``check()`` が ``self._create_error_result`` を呼ぶ。

checker の mixin メソッド（identity / 反例整形 / completed proof payload / completion contexts / recurrence receipt）は
callable として受け取る（instance patch seam 維持）。
"""

from __future__ import annotations

import time
from typing import Any, Callable, Optional

from scripts.function_tracer_pcode.proof.obligations.branch_context import BranchCheckContext
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.checker.result_factory import create_error_result
from scripts.function_tracer_pcode.checker.unknown_reason import make_internal_v2_reason_diagnostic
from scripts.function_tracer_pcode.core import FunctionSignature
from scripts.function_tracer_pcode.core.render_smt import UnknownSmtExtensionWidthError
from scripts.function_tracer_pcode.smt import ParallelResult


def assemble_equivalence_result(
    strategy_result,
    analysis1,
    analysis2,
    binary1_name: str,
    binary2_name: str,
    *,
    ctx: BranchCheckContext,
    dispatch_frame,
    preflight_gate_delta_diagnostic,
    call_effect_shadow_manifest,
    start_time: float,
    type_fix_result,
    retry_count: int,
    original_signature1: Optional[FunctionSignature],
    original_signature2: Optional[FunctionSignature],
    rewrite_info,
    debug: bool,
    deterministic_analysis_identity: Callable[..., Any],
    format_counterexample: Callable[..., Any],
    completed_recovery_proof_payload: Callable[..., Any],
    reason_completion_applicability_contexts: Callable[..., Any],
    recurrence_promotion_result_receipt: Callable[..., Any],
) -> EquivalenceResult:
    function1_identity = deterministic_analysis_identity(ctx.strategy, analysis1)
    function2_identity = deterministic_analysis_identity(ctx.strategy, analysis2)
    
    if debug and strategy_result.smt_formula:
        print("\n" + "=" * 60)
        print("Generated SMT formula:")
        print("=" * 60)
        print(strategy_result.smt_formula)
        print("=" * 60 + "\n")
    
    total_time = time.time() - start_time
    
    # 反例をフォーマット
    counterexample = None
    if strategy_result.is_equivalent is False and strategy_result.counterexample_raw:
        counterexample = format_counterexample(
            strategy_result.counterexample_raw,
            analysis1, analysis2,
            strategy_result.return_var1 or "return_1",
            strategy_result.return_var2 or "return_2"
        )

    completed_proofs = completed_recovery_proof_payload(
        analysis1,
        analysis2,
        binary1_name,
        binary2_name,
        extra_records=getattr(
            strategy_result, "completed_recovery_proof_evidence", ()
        ),
    )
    completion_contexts = reason_completion_applicability_contexts(
        completed_proofs,
        analysis1,
        analysis2,
    )
    from scripts.function_tracer_pcode.authority.domains.comparison_closure import (
        query_execution_record_projection,
    )
    
    equivalence_result = EquivalenceResult(
        is_equivalent=strategy_result.is_equivalent,
        function1_name=analysis1.function_name,
        function2_name=analysis2.function_name,
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        solver_results=strategy_result.solver_results,
        counterexample=counterexample,
        # ★ 修正: save_formula に関わらず smt_formula を保持（debug trace 用）
        # ただし to_string() での出力は save_formula で制御
        smt_formula=strategy_result.smt_formula,  # ← 条件を削除
        total_time=total_time,
        type_fix_result=type_fix_result,
        retry_count=retry_count,
        function1_signature=original_signature1,
        function2_signature=original_signature2,
        effective_function1_signature=FunctionSignature.from_analysis(analysis1),
        effective_function2_signature=FunctionSignature.from_analysis(analysis2),
        function1_signature_hypotheses=list(analysis1.signature_hypotheses),
        function2_signature_hypotheses=list(analysis2.signature_hypotheses),
        constrained_fragments=strategy_result.constrained_fragments,
        rewrite_info=rewrite_info,
        pairwise_stats={
            'total_pairs': strategy_result.total_pairs,
            'unsat_pairs': strategy_result.unsat_pairs,
            'sat_pairs': strategy_result.sat_pairs,
            'unknown_pairs': strategy_result.unknown_pairs,
            'error_pairs': strategy_result.error_pairs,
        } if strategy_result.total_pairs > 0 else None,
        pairwise_debug_stats=strategy_result.pairwise_debug_stats,
        unknown_reasons=strategy_result.unknown_reasons,
        error_message=strategy_result.error_message,
        failure_status=strategy_result.error_kind,
        failure_message=strategy_result.error_message,
        sat_pair_info=strategy_result.sat_pair_info,
        normalization_rules=strategy_result.normalization_rules,
        completed_recovery_proof_evidence=completed_proofs,
        reason_completion_applicability_contexts=completion_contexts,
        call_effect_shadow_manifest=call_effect_shadow_manifest,
        recurrence_promotion_receipt=recurrence_promotion_result_receipt(
            strategy_result
        ),
        call_proof_terminal_provenance=(
            {
                "comparison_session_id": ctx.comparison_session_id,
                "terminal_branch_id": ctx.branch_id,
                "decision_owner_mode": ctx.decision_mode.value,
                "decision_owner_lease_id": (
                    dispatch_frame.decision_lease.decision_owner_id
                    if dispatch_frame is not None else None
                ),
                "terminal_outcome": (
                    "EQ" if strategy_result.is_equivalent is True
                    else "NOT_EQ" if strategy_result.is_equivalent is False
                    else "UNKNOWN"
                ),
                "projection_generation": ctx.generation,
                "comparison_receipt_id": (
                    dispatch_frame.receipt.receipt_id
                    if dispatch_frame is not None and dispatch_frame.receipt is not None
                    else None
                ),
                "monolithic_terminal_receipt": (
                    {
                        "receipt_digest": dispatch_frame.monolithic_terminal_receipt.receipt_digest,
                        "comparison_receipt_id": dispatch_frame.monolithic_terminal_receipt.comparison_receipt_id,
                        "outcome_kind": dispatch_frame.monolithic_terminal_receipt.outcome_kind,
                        "parent_lease_digest": dispatch_frame.monolithic_terminal_receipt.parent_lease_digest,
                        "execution_lease_digest": dispatch_frame.monolithic_terminal_receipt.execution_lease_digest,
                        "frozen_surface_digest": dispatch_frame.monolithic_terminal_receipt.frozen_surface_digest,
                        "census_digest": dispatch_frame.monolithic_terminal_receipt.census_digest,
                        "region_receipt_digests": list(
                            dispatch_frame.monolithic_terminal_receipt.region_receipt_digests
                        ),
                        "sat_region_id": dispatch_frame.monolithic_terminal_receipt.sat_region_id,
                        "model_digest": dispatch_frame.monolithic_terminal_receipt.model_digest,
                        "fixed_model_assertion_digest": dispatch_frame.monolithic_terminal_receipt.fixed_model_assertion_digest,
                        "legacy_replay_receipt_digest": dispatch_frame.monolithic_terminal_receipt.legacy_replay_receipt_digest,
                        "counterexample_safety_receipt_digest": dispatch_frame.monolithic_terminal_receipt.counterexample_safety_receipt_digest,
                        "proof_bundle_digest": dispatch_frame.monolithic_terminal_receipt.proof_bundle_digest,
                        "typed_global_replay_receipt_count": len(tuple(
                            getattr(
                                dispatch_frame.monolithic_terminal_receipt.counterexample_safety_receipt,
                                "global_replay_receipts", (),
                            ) or ()
                        )),
                        "gate_reference_digests": list(dispatch_frame.monolithic_terminal_receipt.gate_reference_digests),
                        "validated": dispatch_frame.monolithic_terminal_receipt.validates(),
                    }
                    if dispatch_frame is not None
                    and dispatch_frame.monolithic_terminal_receipt is not None
                    else None
                ),
                "query_execution_receipts": [
                    query_execution_record_projection(record)
                    for record in tuple(getattr(
                        getattr(dispatch_frame, "receipt", None),
                        "query_records",
                        (),
                    ) or ())
                ],
                "dispatch_cleanup_complete": (
                    dispatch_frame.cleanup_complete if dispatch_frame is not None else True
                ),
                "preflight_gate_delta_diagnostic": (
                    preflight_gate_delta_diagnostic
                ),
            }
        ),
        function1_identity=function1_identity,
        function2_identity=function2_identity,
    )
    # The obligation runner performs the final runtime-generation
    # validation after proof gates and evidence application.  Keep the
    # capability objects private; they are never serialized.
    equivalence_result._prepared_dispatch_frame = dispatch_frame
    equivalence_result._strategy_result = strategy_result
    if (
        dispatch_frame is not None
        and dispatch_frame.receipt is not None
        and dispatch_frame.monolithic_terminal_receipt is not None
        and dispatch_frame.monolithic_terminal_receipt.outcome_kind
        == "inconclusive_diagnostic"
        and tuple(dispatch_frame.receipt.query_records)
    ):
        from scripts.function_tracer_pcode.authority.domains.comparison_closure import (
            InconclusiveComparisonAuthority,
        )
        equivalence_result._inconclusive_comparison_authority = (
            InconclusiveComparisonAuthority.issue(dispatch_frame)
        )
    else:
        equivalence_result._inconclusive_comparison_authority = None
    return equivalence_result


def unsupported_smt_diagnostic_kind(exc: Exception) -> str:
    return (
        "unknown_smt_extension_width"
        if isinstance(exc, UnknownSmtExtensionWidthError)
        else "unsupported_smt_operator"
    )


def unsupported_smt_result(
    exc,
    *,
    analysis1,
    analysis2,
    binary1_name: str,
    binary2_name: str,
    start_time: float,
    type_fix_result,
    retry_count: int,
    original_signature1: Optional[FunctionSignature],
    original_signature2: Optional[FunctionSignature],
) -> EquivalenceResult:
    """unsupported SMT expression semantics で check が止まったときの UNKNOWN result（handler 本体）。"""
    diagnostic_kind = unsupported_smt_diagnostic_kind(exc)
    return EquivalenceResult(
        is_equivalent=None,
        function1_name=analysis1.function_name,
        function2_name=analysis2.function_name,
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        solver_results=ParallelResult(results=[]),
        counterexample=None,
        smt_formula=None,
        total_time=time.time() - start_time,
        type_fix_result=type_fix_result,
        retry_count=retry_count,
        function1_signature=original_signature1,
        function2_signature=original_signature2,
        effective_function1_signature=FunctionSignature.from_analysis(analysis1),
        effective_function2_signature=FunctionSignature.from_analysis(analysis2),
        function1_signature_hypotheses=list(analysis1.signature_hypotheses),
        function2_signature_hypotheses=list(analysis2.signature_hypotheses),
        constrained_fragments=[],
        pairwise_debug_stats={
            diagnostic_kind: 1,
        },
        unknown_reasons=[
            make_internal_v2_reason_diagnostic(
                "expression_semantics_unsupported",
                stage="S_PAIRWISE",
                evidence_refs=(diagnostic_kind,),
                object_target_key=(
                    diagnostic_kind,
                    exc.operator,
                    exc.operand_bits,
                    getattr(exc, "result_bits", 0),
                    tuple(analysis1.outcome_function_identity()),
                    tuple(analysis2.outcome_function_identity()),
                ),
                detail=str(exc),
            )
        ],
    )


def canonical_abi_error_result(
    exc,
    *,
    analysis1,
    analysis2,
    binary1_name: str,
    binary2_name: str,
    start_time: float,
    type_fix_result,
    retry_count: int,
    original_signature1: Optional[FunctionSignature],
    original_signature2: Optional[FunctionSignature],
) -> EquivalenceResult:
    """``ReturnAbiAuthorityInvalid`` の canonical error kind を error_message / failure_status に載せる。"""
    return create_error_result(
        analysis1=analysis1,
        analysis2=analysis2,
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        error_message=exc.canonical_error_kind,
        start_time=start_time,
        type_fix_result=type_fix_result,
        retry_count=retry_count,
        original_signature1=original_signature1,
        original_signature2=original_signature2,
        failure_status=exc.canonical_error_kind,
        failure_message=str(exc),
    )
