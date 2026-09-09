# -*- coding: utf-8 -*-
"""解析と再解析のヘルパー"""

from typing import Optional, Tuple
import time

from scripts.function_tracer_pcode.core import (
    FunctionReturnAnalysis,
    FunctionSignature,
    SignatureHypothesis,
)
from scripts.function_tracer_pcode.checker.phases.handler import PhaseContext, PhaseResult
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.checker.diagnostics import AnalysisTimer
from scripts.function_tracer_pcode.checker.result_factory import (
    create_context_error_result,
    create_context_unknown_result,
    create_reanalysis_error,
)
from scripts.function_tracer_pcode.analysis.failure import (
    ANALYSIS_STATUS_DECOMPILATION_FAILED,
    ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
    ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
)


def analyze_and_check_with_analysis(
    checker,
    ctx: PhaseContext,
    retry_count: int = 0
) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
    """初回解析を実行し、その結果で stage plan を走らせる"""
    from scripts.function_tracer_pcode.analysis import ReturnAnalyzer

    start_time = time.time()
    timer = AnalysisTimer()
    checker._analysis_timer = timer

    checker._debug_print(f"Analyzing function '{ctx.function_name1}' in {ctx.binary1_name}...")
    analyzer1 = ReturnAnalyzer(
        ctx.program1,
        debug=checker.debug,
        binary_id=ctx.binary1_id,
        enable_completed_recovery_proofs=getattr(checker, "enable_completed_recovery_proofs", True),
        external_call_effect_policy=getattr(checker, "external_call_effect_policy", None),
    )
    try:
        analysis1 = timer.timed(
            "function1",
            lambda: analyzer1.analyze_function_by_name(ctx.function_name1, ctx.decompile_timeout),
        )
        timer.record_analysis("function1", analysis1)
        timer.record_callee_parameter_cache("function1", analyzer1)
        timer.record_callee_analysis_cache("function1", analyzer1)
        if analysis1 is None:
            failure = analyzer1.get_last_analysis_failure()
            failure_status = getattr(failure, "status", None)
            error_message = getattr(failure, "message", None) or analyzer1.get_last_function_lookup_error() or (
                f"Function '{ctx.function_name1}' not found in {ctx.binary1_name}"
            )
            if failure_status in {
                ANALYSIS_STATUS_DECOMPILATION_FAILED,
                ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
            }:
                return None, None, create_context_unknown_result(
                    ctx=ctx,
                    failure_status=failure_status,
                    message=error_message,
                    start_time=start_time,
                    retry_count=retry_count,
                )
            return None, None, create_context_error_result(
                ctx=ctx,
                error_message=error_message,
                start_time=start_time,
                retry_count=retry_count,
                failure_status=failure_status or ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
                failure_message=error_message,
            )
    finally:
        analyzer1.dispose()

    checker._debug_print(f"Analyzing function '{ctx.function_name2}' in {ctx.binary2_name}...")
    analyzer2 = ReturnAnalyzer(
        ctx.program2,
        debug=checker.debug,
        binary_id=ctx.binary2_id,
        enable_completed_recovery_proofs=getattr(checker, "enable_completed_recovery_proofs", True),
        external_call_effect_policy=getattr(checker, "external_call_effect_policy", None),
    )
    try:
        analysis2 = timer.timed(
            "function2",
            lambda: analyzer2.analyze_function_by_name(ctx.function_name2, ctx.decompile_timeout),
        )
        timer.record_analysis("function2", analysis2)
        timer.record_callee_parameter_cache("function2", analyzer2)
        timer.record_callee_analysis_cache("function2", analyzer2)
        if analysis2 is None:
            failure = analyzer2.get_last_analysis_failure()
            failure_status = getattr(failure, "status", None)
            error_message = getattr(failure, "message", None) or analyzer2.get_last_function_lookup_error() or (
                f"Function '{ctx.function_name2}' not found in {ctx.binary2_name}"
            )
            if failure_status in {
                ANALYSIS_STATUS_DECOMPILATION_FAILED,
                ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
            }:
                return analysis1, None, create_context_unknown_result(
                    ctx=ctx,
                    failure_status=failure_status,
                    message=error_message,
                    start_time=start_time,
                    retry_count=retry_count,
                    analysis1=analysis1,
                )
            return analysis1, None, create_context_error_result(
                ctx=ctx,
                error_message=error_message,
                start_time=start_time,
                retry_count=retry_count,
                analysis1=analysis1,
                failure_status=failure_status or ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
                failure_message=error_message,
            )
    finally:
        analyzer2.dispose()

    if ctx.original_signature1 is None:
        ctx.original_signature1 = FunctionSignature.from_analysis(analysis1)
    if ctx.original_signature2 is None:
        ctx.original_signature2 = FunctionSignature.from_analysis(analysis2)

    checker._debug_print("Running stage plan...")
    result = checker._run_stage_plan(
        analysis1,
        analysis2,
        ctx.binary1_name,
        ctx.binary2_name,
        ctx.save_formula,
        type_fix_result=ctx.type_fix_result,
        retry_count=retry_count,
        original_signature1=ctx.original_signature1,
        original_signature2=ctx.original_signature2,
    )
    _attach_analysis_diagnostics(checker, result)

    return analysis1, analysis2, result


def selective_reanalysis_and_check(
    checker,
    ctx: PhaseContext,
    phase_result: PhaseResult,
    retry_count: int
) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
    """変更側だけ fresh analyze し、仮説を replay して stage plan を再実行する。"""

    from scripts.function_tracer_pcode.analysis import ReturnAnalyzer

    need_reanalyze1 = phase_result.changed_binary1
    need_reanalyze2 = phase_result.changed_binary2

    checker._debug_print(
        f"Selective analysis reuse: binary1_changed={need_reanalyze1}, "
        f"binary2_changed={need_reanalyze2}"
    )

    analysis1 = ctx.analysis1
    analysis2 = ctx.analysis2
    if analysis1 is None:
        return create_reanalysis_error(
            ctx,
            "Cached analysis for binary1 is not available",
            retry_count,
        )
    if analysis2 is None:
        return create_reanalysis_error(
            ctx,
            "Cached analysis for binary2 is not available",
            retry_count,
        )

    def _reanalyze_with_hypotheses(
        *,
        program,
        function_name: str,
        binary_name: str,
        cached_analysis: FunctionReturnAnalysis,
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[str], Optional[str]]:
        binary_id = ctx.binary1_id if program is ctx.program1 else ctx.binary2_id if program is ctx.program2 else None
        analyzer = ReturnAnalyzer(
            program,
            debug=checker.debug,
            binary_id=binary_id,
            enable_completed_recovery_proofs=getattr(checker, "enable_completed_recovery_proofs", True),
            external_call_effect_policy=getattr(checker, "external_call_effect_policy", None),
        )
        try:
            checker._debug_print(
                f"Fresh reanalysis requested for {binary_name} after signature-changing retry phase"
            )
            side = "function1" if program is ctx.program1 else "function2"
            timer = getattr(checker, "_analysis_timer", None) or AnalysisTimer()
            checker._analysis_timer = timer
            fresh_analysis = timer.timed(
                side,
                lambda: analyzer.analyze_function_by_name(function_name, ctx.decompile_timeout),
            )
            timer.record_analysis(side, fresh_analysis)
            timer.record_callee_parameter_cache(side, analyzer)
            timer.record_callee_analysis_cache(side, analyzer)
            if fresh_analysis is None:
                failure = analyzer.get_last_analysis_failure()
                failure_status = getattr(failure, "status", None)
                error_message = getattr(failure, "message", None) or analyzer.get_last_function_lookup_error() or (
                    f"Fresh reanalysis failed for '{function_name}' in {binary_name}"
                )
                return None, error_message, failure_status

            replayed = fresh_analysis
            for hypothesis_payload in list(getattr(cached_analysis, "signature_hypotheses", []) or []):
                hypothesis = SignatureHypothesis.from_dict(
                    hypothesis_payload,
                    program=program,
                )
                replayed = replayed.with_signature_hypothesis(hypothesis)
            if getattr(replayed, "signature_hypotheses", None):
                replayed = analyzer.refresh_structural_recurrence_summary(
                    replayed,
                    timeout=ctx.decompile_timeout,
                )
            return replayed, None, None
        finally:
            analyzer.dispose()

    if need_reanalyze1:
        analysis1, error_message, failure_status = _reanalyze_with_hypotheses(
            program=ctx.program1,
            function_name=ctx.function_name1,
            binary_name=ctx.binary1_name,
            cached_analysis=analysis1,
        )
        if analysis1 is None:
            checker._debug_print(f"Fresh reanalysis failed for binary1: {error_message}")
            if failure_status in {
                ANALYSIS_STATUS_DECOMPILATION_FAILED,
                ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
            }:
                return ctx.analysis1, ctx.analysis2, create_context_unknown_result(
                    ctx=ctx,
                    failure_status=failure_status,
                    message=str(error_message),
                    start_time=time.time(),
                    retry_count=retry_count,
                    analysis1=ctx.analysis1,
                    analysis2=ctx.analysis2,
                )
            return create_reanalysis_error(
                ctx,
                str(error_message),
                retry_count,
                failure_status=failure_status,
            )

    if need_reanalyze2:
        analysis2, error_message, failure_status = _reanalyze_with_hypotheses(
            program=ctx.program2,
            function_name=ctx.function_name2,
            binary_name=ctx.binary2_name,
            cached_analysis=analysis2,
        )
        if analysis2 is None:
            checker._debug_print(f"Fresh reanalysis failed for binary2: {error_message}")
            if failure_status in {
                ANALYSIS_STATUS_DECOMPILATION_FAILED,
                ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
            }:
                return ctx.analysis1, ctx.analysis2, create_context_unknown_result(
                    ctx=ctx,
                    failure_status=failure_status,
                    message=str(error_message),
                    start_time=time.time(),
                    retry_count=retry_count,
                    analysis1=ctx.analysis1,
                    analysis2=ctx.analysis2,
                )
            return create_reanalysis_error(
                ctx,
                str(error_message),
                retry_count,
                failure_status=failure_status,
            )

    ctx.analysis1 = analysis1
    ctx.analysis2 = analysis2

    result = checker._run_stage_plan(
        analysis1,
        analysis2,
        ctx.binary1_name,
        ctx.binary2_name,
        ctx.save_formula,
        type_fix_result=ctx.type_fix_result,
        retry_count=retry_count,
        original_signature1=ctx.original_signature1,
        original_signature2=ctx.original_signature2,
    )
    _attach_analysis_diagnostics(checker, result)

    return analysis1, analysis2, result


def _attach_analysis_diagnostics(checker, result) -> None:
    """解析時間と式サイズを結果に添付する（非署名の診断領域）。"""
    timer = getattr(checker, "_analysis_timer", None)
    if timer is None or result is None:
        return
    try:
        result.diagnostics = timer.snapshot()
    except Exception:  # diagnostics never fail the verdict
        return
