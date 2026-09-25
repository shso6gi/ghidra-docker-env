"""Finishing / result assembly / exception-result factories for :meth:`EquivalenceChecker.check` (Phase 6b-5, #82).

E・F 段（結果組み立て）と G 段（例外 → result）の **本体** を、checker facade を直接書き換えず明示的な入力を受け取る
module-level の関数に移す。トップレベルの ``try/except`` 自体、handler の種類と順序、どの処理の例外がどの handler に
捕捉されるか（catch scope）は orchestration として ``check()`` に残す。

- :func:`assemble_equivalence_result` — 通常経路。identity 計算 → debug の SMT 出力 → total_time → 反例整形 →
  completed proof payload / completion contexts → ``EquivalenceResult(...)`` → 私的付帯 3 つ
  （``_prepared_dispatch_frame`` / ``_strategy_result`` / ``_inconclusive_comparison_authority``）を旧順序で行う。
- :func:`unsupported_smt_result` — ``UnknownSmtExtensionWidthError`` / ``UnsupportedSmtOperatorError`` handler の本体。
- :func:`canonical_abi_error_result` — ``ReturnAbiAuthorityInvalid`` 用の canonical error result。
- :func:`analysis_limitation_result` — ``AnalysisLimitation`` handler の本体（Issue #125）。
  帰属できた限界は UNKNOWN、帰属できなければ ``limitation_unattributed`` /
  ``unregistered_reason`` の ERROR（fail-closed）。
- :func:`internal_error_result` — ``InternalError`` handler の本体。``internal_exception`` の ERROR。
- :func:`generic_internal_error_result` — **族の外**の例外用（Issue #106 PR-106-0 の
  軸 F）。pair failure の結果化とは別経路で、観測点は捕まえた場所になる。
- :func:`analysis_limitation_result_for_pair` / :func:`internal_error_result_for_pair` —
  pair 境界（Issue #106 PR-106-0）用。両側 analysis を前提にせずに同じ判定規則で
  結果を組む。判定規則は ``analysis_limitation_result`` / ``internal_error_result``
  と同一で、違うのは入力の前提だけ。

checker の mixin メソッド（identity / 反例整形 / completed proof payload / completion contexts / recurrence receipt）は
callable として受け取る（instance patch seam 維持）。
"""

from __future__ import annotations

import time
from typing import Any, Callable, Dict, Optional

from scripts.function_tracer_pcode.core.errors import (
    AnalysisLimitation,
    InternalError,
    PairStopState,
)
from scripts.function_tracer_pcode.proof.obligations.branch_context import BranchCheckContext
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.checker.result_factory import create_error_result
from scripts.function_tracer_pcode.checker.unknown_reason import make_internal_v2_reason_diagnostic
from scripts.function_tracer_pcode.core import FunctionSignature, live_values
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
        total_time=time.time() - live_values.as_float(start_time),
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


#: 内部バグの ERROR に載せる `failure_status`（`LegacyBoundaryErrorKind` と同値）。
INTERNAL_EXCEPTION_STATUS = "internal_exception"


def analysis_limitation_result(
    exc: AnalysisLimitation,
    *,
    session,
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
    """解析の限界で check が止まったときの結果（handler 本体、Issue #125）。

    判定は **帰属先の cause** が決める。この関数は cause を作らず（producer 経路が
    作る）、強化もしない。帰属できなかった限界は UNKNOWN にせず ERROR に落とす
    （限界を表現する authority が無いまま EQ / NOT_EQ へ抜けないため）。
    """
    from scripts.function_tracer_pcode.authority.decision.limitation_attribution import (
        attribute_analysis_limitation,
    )
    from scripts.function_tracer_pcode.checker.diagnostics import (
        FAILURE_ANALYSIS_LIMITATION,
        record_failure_diagnostic,
    )

    attribution = attribute_analysis_limitation(session, exc)
    diagnostic = {
        **attribution.to_diagnostic(),
        "site": exc.site,
        "exception_type": type(exc).__name__,
        "evidence_refs": list(exc.evidence_refs),
        "message": str(exc)[:500],
    }
    if not attribution.is_attributed:
        result = create_error_result(
            analysis1=analysis1,
            analysis2=analysis2,
            binary1_name=binary1_name,
            binary2_name=binary2_name,
            error_message=attribution.failure_status,
            start_time=start_time,
            type_fix_result=type_fix_result,
            retry_count=retry_count,
            original_signature1=original_signature1,
            original_signature2=original_signature2,
            failure_status=attribution.failure_status,
            failure_message=f"{attribution.detail}: {exc}",
        )
        record_failure_diagnostic(result, FAILURE_ANALYSIS_LIMITATION, diagnostic)
        return result

    result = EquivalenceResult(
        is_equivalent=None,
        function1_name=analysis1.function_name,
        function2_name=analysis2.function_name,
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        solver_results=ParallelResult(results=[]),
        counterexample=None,
        smt_formula=None,
        total_time=time.time() - live_values.as_float(start_time),
        type_fix_result=type_fix_result,
        retry_count=retry_count,
        function1_signature=original_signature1,
        function2_signature=original_signature2,
        effective_function1_signature=FunctionSignature.from_analysis(analysis1),
        effective_function2_signature=FunctionSignature.from_analysis(analysis2),
        function1_signature_hypotheses=list(analysis1.signature_hypotheses),
        function2_signature_hypotheses=list(analysis2.signature_hypotheses),
        constrained_fragments=[],
        pairwise_debug_stats={"analysis_limitation": 1},
        unknown_reasons=[
            make_internal_v2_reason_diagnostic(
                exc.reason_id,
                stage="S_ANALYSIS_LIMITATION",
                evidence_refs=(exc.site, *exc.evidence_refs),
                object_target_key=(
                    "analysis_limitation_v1",
                    exc.reason_id,
                    exc.site,
                    exc.target_key,
                ),
                detail=exc.detail,
            )
        ],
    )
    record_failure_diagnostic(result, FAILURE_ANALYSIS_LIMITATION, diagnostic)
    return result


def internal_error_result(
    exc: InternalError,
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
    """内部エラーの ERROR 結果（handler 本体、Issue #125）。

    `legacy_compatibility_error` に混ぜず `internal_exception` として分類し、
    stack を診断に残す（rerun manifest は ERROR をそのまま再実行対象にする）。
    """
    from scripts.function_tracer_pcode.checker.diagnostics import (
        FAILURE_INTERNAL_EXCEPTION,
        record_failure_diagnostic,
    )

    result = create_error_result(
        analysis1=analysis1,
        analysis2=analysis2,
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        error_message=str(exc),
        start_time=start_time,
        type_fix_result=type_fix_result,
        retry_count=retry_count,
        original_signature1=original_signature1,
        original_signature2=original_signature2,
        failure_status=INTERNAL_EXCEPTION_STATUS,
        failure_message=str(exc),
    )
    record_failure_diagnostic(result, FAILURE_INTERNAL_EXCEPTION, {
        "exception_type": exc.exception_type,
        "site": exc.site,
        "stack": list(exc.stack_lines()),
        "stack_digest": exc.stack_digest(),
    })
    return result


def generic_internal_error_result(
    exc: BaseException,
    *,
    site: str,
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
    """**族の外**の例外を従来どおり `internal_exception` の ERROR にする。

    これは pair failure の結果化 **ではない**（Issue #106 PR-106-0 の軸 F）。
    `AnalysisFailureError` 族は execution control が winner を決めてから
    `checker.pair_execution` が結果にするので、この関数は通らない。ここを通るのは
    「台帳に対応する failure が無く、型でも pair failure と分からない例外」だけで、
    観測点は **捕まえた場所** になる（台帳が持つ観測点ではない）。
    """
    return internal_error_result(
        InternalError(exc, site=site),
        analysis1=analysis1,
        analysis2=analysis2,
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        start_time=start_time,
        type_fix_result=type_fix_result,
        retry_count=retry_count,
        original_signature1=original_signature1,
        original_signature2=original_signature2,
    )


def analysis_limitation_result_for_pair(
    exc: AnalysisLimitation,
    *,
    session,
    stop_state,
    function_name1: str,
    function_name2: str,
    binary1_name: str,
    binary2_name: str,
    start_time: float,
    analysis1=None,
    analysis2=None,
    type_fix_result=None,
    retry_count: int = 0,
    original_signature1: Optional[FunctionSignature] = None,
    original_signature2: Optional[FunctionSignature] = None,
    carry_from=None,
) -> EquivalenceResult:
    """pair 境界で限界を結果化する（Issue #106 PR-106-0）。

    :func:`analysis_limitation_result` との違いは **両側 analysis を前提にしない**
    ことだけ。初回解析の途中で限界が出た pair には `FunctionReturnAnalysis` が
    片側も無いことがあり、その場合でも判定 authority へ UNKNOWN を渡せる必要が
    ある（`create_context_unknown_result` と同じ考え方）。

    判定規則そのものは変えない。帰属できた限界は reason 付き UNKNOWN、帰属でき
    なければ ``limitation_unattributed`` の ERROR（fail-closed、pilot 無し経路）。
    `stop_state` は診断としてだけ載せる（control authority にはしない）。
    """
    from scripts.function_tracer_pcode.authority.decision.limitation_attribution import (
        attribute_analysis_limitation,
    )
    from scripts.function_tracer_pcode.checker.diagnostics import (
        FAILURE_ANALYSIS_LIMITATION,
        record_failure_diagnostic,
    )

    attribution = attribute_analysis_limitation(session, exc)
    diagnostic = {
        **attribution.to_diagnostic(),
        "site": exc.site,
        "exception_type": type(exc).__name__,
        "evidence_refs": list(exc.evidence_refs),
        "message": str(exc)[:500],
        "pair_scoped": True,
    }
    effective1 = (
        FunctionSignature.from_analysis(analysis1)
        if analysis1 is not None else original_signature1
    )
    effective2 = (
        FunctionSignature.from_analysis(analysis2)
        if analysis2 is not None else original_signature2
    )
    common = _common_fields(
        function1_name=(
            live_values.attribute(analysis1, "function_name") if analysis1 is not None else function_name1
        ),
        function2_name=(
            live_values.attribute(analysis2, "function_name") if analysis2 is not None else function_name2
        ),
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        solver_results=ParallelResult(results=[]),
        total_time=time.time() - live_values.as_float(start_time),
        type_fix_result=type_fix_result,
        retry_count=retry_count,
        function1_signature=original_signature1,
        function2_signature=original_signature2,
        effective_function1_signature=effective1,
        effective_function2_signature=effective2,
        function1_signature_hypotheses=(
            _hypotheses_of(analysis1)
        ),
        function2_signature_hypotheses=(
            _hypotheses_of(analysis2)
        ),
        constrained_fragments=[],
    )
    if not attribution.is_attributed:
        result = EquivalenceResult(
            is_equivalent=None,
            error_message=attribution.failure_status,
            failure_status=attribution.failure_status,
            failure_message=f"{attribution.detail}: {exc}",
            **common,
        )
    else:
        result = EquivalenceResult(
            is_equivalent=None,
            counterexample=None,
            smt_formula=None,
            pairwise_debug_stats={"analysis_limitation": 1},
            unknown_reasons=[
                make_internal_v2_reason_diagnostic(
                    exc.reason_id,
                    stage="S_ANALYSIS_LIMITATION",
                    evidence_refs=(exc.site, *exc.evidence_refs),
                    object_target_key=(
                        "analysis_limitation_v1",
                        exc.reason_id,
                        exc.site,
                        exc.target_key,
                    ),
                    detail=exc.detail,
                )
            ],
            **common,
        )
    _carry_pair_diagnostics(result, carry_from)
    attach_pair_stop_state(result, stop_state)
    record_failure_diagnostic(result, FAILURE_ANALYSIS_LIMITATION, diagnostic)
    return result


def _carry_pair_diagnostics(result: EquivalenceResult, carry_from) -> None:
    """差し替え前の結果が持っていた **診断だけ** を引き継ぐ（判定面は引き継がない）。

    `debug_trace` と `diagnostics` は観測で、`is_equivalent` / `solver_results` /
    `decision_receipt` のような判定面は新しい結果側の空値のままにする。型が想定
    外のときは黙って捨てる（包括捕捉は増やさない）。
    """
    if carry_from is None or carry_from is result:
        return
    # 引き継ぐ元の結果は owner の規則で読む（`__getattr__`・上書きした容器の code を呼ばない）
    trace = live_values.attribute(carry_from, "debug_trace")
    if trace is not None:
        live_values.set_state(result, "debug_trace", trace)
        live_values.set_state(
            result, "emit_debug_trace", live_values.as_bool(live_values.attribute(carry_from, "emit_debug_trace", True)),
        )
    carried = live_values.attribute(carry_from, "diagnostics")
    if type(carried) is dict:
        if not carried:
            return
        current = live_values.attribute(result, "diagnostics")
        live_values.set_state(
            result, "diagnostics",
            live_values.merged_mappings(carried, current) if type(current) is dict
            else live_values.merged_mappings(carried),
        )


def attach_pair_stop_state(result: EquivalenceResult, stop_state) -> None:
    """pair の stop state を結果へ写す（object 属性 + 診断、Issue #106 PR-106-0）。

    渡ってくるのは **winner になった failure 自身の stop state**
    （`PairPendingFailure.stop_state`）で、台帳の aggregate
    （`PairExecutionControl.stop_state()`）ではない。結果は「この結果を作らせた
    failure」を説明するものなので、その failure の stop state を書く。現 scope
    では同一 kind に異なる severity が無いので両者は一致する。

    どちらにせよ **診断であって判定入力ではない**（判定は `failure_status` /
    `unknown_reasons` 側が持つ）。`PairStopState.NONE` のときは何も書かない —
    限界が無い pair の出力 schema を変えないための条件で、診断 block の key
    集合は従来どおりになる。
    """
    from scripts.function_tracer_pcode.checker.diagnostics import (
        FAILURE_PAIR_STOP_STATE,
        record_failure_diagnostic,
    )

    if stop_state is None or stop_state is PairStopState.NONE:
        return
    state = live_values.enum_value(stop_state)
    live_values.set_state(result, "pair_stop_state", state)
    record_failure_diagnostic(result, FAILURE_PAIR_STOP_STATE, state)


def internal_error_result_for_pair(
    exc: InternalError,
    *,
    stop_state,
    function_name1: str,
    function_name2: str,
    binary1_name: str,
    binary2_name: str,
    start_time: float,
    analysis1=None,
    analysis2=None,
    type_fix_result=None,
    retry_count: int = 0,
    original_signature1: Optional[FunctionSignature] = None,
    original_signature2: Optional[FunctionSignature] = None,
    carry_from=None,
) -> EquivalenceResult:
    """pair 境界で内部バグを結果化する（`internal_exception` の ERROR）。

    限界と内部バグが同時にあるときは **内部バグを優先** してこちらを使う。
    限界のときと同じく両側 analysis を前提にしない。
    """
    from scripts.function_tracer_pcode.checker.diagnostics import (
        FAILURE_INTERNAL_EXCEPTION,
        record_failure_diagnostic,
    )

    result = EquivalenceResult(
        is_equivalent=None,
        function1_name=(
            live_values.attribute(analysis1, "function_name") if analysis1 is not None else function_name1
        ),
        function2_name=(
            live_values.attribute(analysis2, "function_name") if analysis2 is not None else function_name2
        ),
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        solver_results=ParallelResult(results=[]),
        total_time=time.time() - live_values.as_float(start_time),
        error_message=str(exc),
        failure_status=INTERNAL_EXCEPTION_STATUS,
        failure_message=str(exc),
        type_fix_result=type_fix_result,
        retry_count=retry_count,
        function1_signature=original_signature1,
        function2_signature=original_signature2,
        effective_function1_signature=(
            FunctionSignature.from_analysis(analysis1)
            if analysis1 is not None else original_signature1
        ),
        effective_function2_signature=(
            FunctionSignature.from_analysis(analysis2)
            if analysis2 is not None else original_signature2
        ),
        function1_signature_hypotheses=(
            _hypotheses_of(analysis1)
        ),
        function2_signature_hypotheses=(
            _hypotheses_of(analysis2)
        ),
        constrained_fragments=[],
    )
    _carry_pair_diagnostics(result, carry_from)
    attach_pair_stop_state(result, stop_state)
    record_failure_diagnostic(result, FAILURE_INTERNAL_EXCEPTION, {
        "exception_type": exc.exception_type,
        "site": exc.site,
        "stack": list(exc.stack_lines()),
        "stack_digest": exc.stack_digest(),
        "pair_scoped": True,
    })
    return result


def _hypotheses_of(analysis: Any) -> list:
    """解析の signature 仮説の列の写し（無ければ空）。解析の値は owner の規則で読む。"""

    if analysis is None:
        return []
    hypotheses = live_values.attribute(analysis, "signature_hypotheses")
    return [] if hypotheses is None else list(live_values.elements_of(hypotheses))


def _common_fields(**fields: Any) -> Dict[str, Any]:
    """結果の共通の field（`dict(**fields)` と同じ。keyword の名前は組み込みの `str`）。"""

    return fields
