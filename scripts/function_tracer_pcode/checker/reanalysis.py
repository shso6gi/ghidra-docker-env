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
from scripts.function_tracer_pcode.checker.diagnostics import AnalysisTimer, phase_timeline_of
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

    # Issue #109: 解析器の生成点は checker の 1 つの collaborator に委ねる。
    # 既定（None）では従来どおり ``ReturnAnalyzer`` をそのまま使う。
    make_analyzer = getattr(checker, "analyzer_factory", None) or ReturnAnalyzer

    start_time = time.time()
    timer = AnalysisTimer()
    checker._analysis_timer = timer
    phases = phase_timeline_of(checker)

    checker._debug_print(f"Analyzing function '{ctx.function_name1}' in {ctx.binary1_name}...")
    analyzer1 = make_analyzer(
        ctx.program1,
        debug=checker.debug,
        binary_id=ctx.binary1_id,
        enable_completed_recovery_proofs=getattr(checker, "enable_completed_recovery_proofs", True),
        external_call_effect_policy=getattr(checker, "external_call_effect_policy", None),
    )
    try:
        phases.record_reanalyzed_side("function1")
        with phases.measure("analysis", side="function1"):
            analysis1 = timer.timed(
                "function1",
                lambda: analyzer1.analyze_function_by_name(ctx.function_name1, ctx.decompile_timeout),
            )
        timer.record_analysis("function1", analysis1)
        timer.record_callee_parameter_cache("function1", analyzer1)
        timer.record_callee_analysis_cache("function1", analyzer1)
        timer.record_callee_unbound_reuse("function1", analyzer1)
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
    analyzer2 = make_analyzer(
        ctx.program2,
        debug=checker.debug,
        binary_id=ctx.binary2_id,
        enable_completed_recovery_proofs=getattr(checker, "enable_completed_recovery_proofs", True),
        external_call_effect_policy=getattr(checker, "external_call_effect_policy", None),
    )
    try:
        phases.record_reanalyzed_side("function2")
        with phases.measure("analysis", side="function2"):
            analysis2 = timer.timed(
                "function2",
                lambda: analyzer2.analyze_function_by_name(ctx.function_name2, ctx.decompile_timeout),
            )
        timer.record_analysis("function2", analysis2)
        timer.record_callee_parameter_cache("function2", analyzer2)
        timer.record_callee_analysis_cache("function2", analyzer2)
        timer.record_callee_unbound_reuse("function2", analyzer2)
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
    with phases.measure("stage_plan"):
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
    bind_conditional_lane_analyses(result, analysis1, analysis2)

    return analysis1, analysis2, result


def selective_reanalysis_and_check(
    checker,
    ctx: PhaseContext,
    phase_result: PhaseResult,
    retry_count: int
) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
    """変更側だけ fresh analyze し、仮説を replay して stage plan を再実行する。"""

    from scripts.function_tracer_pcode.analysis import ReturnAnalyzer

    make_analyzer = getattr(checker, "analyzer_factory", None) or ReturnAnalyzer

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
        analyzer = make_analyzer(
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
            phases = phase_timeline_of(checker)
            phases.record_reanalyzed_side(side)
            with phases.measure("analysis", side=side):
                fresh_analysis = timer.timed(
                    side,
                    lambda: analyzer.analyze_function_by_name(function_name, ctx.decompile_timeout),
                )
            timer.record_analysis(side, fresh_analysis)
            timer.record_callee_parameter_cache(side, analyzer)
            timer.record_callee_analysis_cache(side, analyzer)
            timer.record_callee_unbound_reuse(side, analyzer)
            if fresh_analysis is None:
                failure = analyzer.get_last_analysis_failure()
                failure_status = getattr(failure, "status", None)
                error_message = getattr(failure, "message", None) or analyzer.get_last_function_lookup_error() or (
                    f"Fresh reanalysis failed for '{function_name}' in {binary_name}"
                )
                return None, error_message, failure_status

            with phases.measure("hypothesis_replay"):
                replayed = fresh_analysis
                for hypothesis_payload in list(getattr(cached_analysis, "signature_hypotheses", []) or []):
                    hypothesis = SignatureHypothesis.from_dict(
                        hypothesis_payload,
                        program=program,
                    )
                    replayed = replayed.with_signature_hypothesis(hypothesis)
            if getattr(replayed, "signature_hypotheses", None):
                with phases.measure("recurrence_refresh"):
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

    with phase_timeline_of(checker).measure("stage_plan"):
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
    bind_conditional_lane_analyses(result, analysis1, analysis2)

    return analysis1, analysis2, result


def bind_conditional_lane_analyses(result, analysis1, analysis2) -> None:
    """この結果を生んだ base analysis を結果へ結び付ける（Issue #20 PR-20-B3）。

    conditional lane は無条件判定が UNKNOWN のときだけ、この 2 つから
    conditional view を作る。署名対象でも serialization 対象でもない補助参照で、
    付いていなければ lane は起動しない（fail closed）。
    """

    if result is None or analysis1 is None or analysis2 is None:
        return
    try:
        result._conditional_lane_analyses = (analysis1, analysis2)
    except Exception:
        return


def _attach_analysis_diagnostics(checker, result) -> None:
    """解析時間と式サイズを結果に添付する（判定には効かない診断領域）。

    Issue #124: 丸ごと上書きせず merge する。同じ結果には `phases`
    （`phase-timing-v1`）/ `boundary_seconds` / `stages` / `conditional_lane`
    など別の生産者が書く診断も載るので、上書きすると先に書かれたものが消える。
    この関数が持つのは `AnalysisTimer` の snapshot が返す key だけで、その key
    は最新の観測で置き換える（同じ側を再解析したら新しい値が正）。
    """
    timer = getattr(checker, "_analysis_timer", None)
    if timer is None or result is None:
        return
    try:
        diagnostics = dict(getattr(result, "diagnostics", None) or {})
        diagnostics.update(timer.snapshot())
        result.diagnostics = diagnostics
    except Exception:  # diagnostics never fail the verdict
        return
