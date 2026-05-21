# -*- coding: utf-8 -*-
"""解析と再解析のヘルパー"""

from typing import Optional, Tuple
import time

from ..model import FunctionReturnAnalysis, FunctionSignature, SignatureHypothesis
from .phases.handler import PhaseContext, PhaseResult
from .result import EquivalenceResult
from .result_factory import create_context_error_result, create_reanalysis_error


def analyze_and_check_with_analysis(
    checker,
    ctx: PhaseContext,
    retry_count: int = 0
) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
    """初回解析を実行し、その結果で stage plan を走らせる"""
    from ..analysis import ReturnAnalyzer

    start_time = time.time()

    checker._debug_print(f"Analyzing function '{ctx.function_name1}' in {ctx.binary1_name}...")
    analyzer1 = ReturnAnalyzer(ctx.program1, debug=checker.debug, binary_id=ctx.binary1_id)
    try:
        analysis1 = analyzer1.analyze_function_by_name(
            ctx.function_name1, ctx.decompile_timeout
        )
        if analysis1 is None:
            error_message = analyzer1.get_last_function_lookup_error() or (
                f"Function '{ctx.function_name1}' not found in {ctx.binary1_name}"
            )
            return None, None, create_context_error_result(
                ctx=ctx,
                error_message=error_message,
                start_time=start_time,
                retry_count=retry_count,
            )
    finally:
        analyzer1.dispose()

    checker._debug_print(f"Analyzing function '{ctx.function_name2}' in {ctx.binary2_name}...")
    analyzer2 = ReturnAnalyzer(ctx.program2, debug=checker.debug, binary_id=ctx.binary2_id)
    try:
        analysis2 = analyzer2.analyze_function_by_name(
            ctx.function_name2, ctx.decompile_timeout
        )
        if analysis2 is None:
            error_message = analyzer2.get_last_function_lookup_error() or (
                f"Function '{ctx.function_name2}' not found in {ctx.binary2_name}"
            )
            return analysis1, None, create_context_error_result(
                ctx=ctx,
                error_message=error_message,
                start_time=start_time,
                retry_count=retry_count,
                analysis1=analysis1,
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

    return analysis1, analysis2, result


def selective_reanalysis_and_check(
    checker,
    ctx: PhaseContext,
    phase_result: PhaseResult,
    retry_count: int
) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
    """変更側だけ fresh analyze し、仮説を replay して stage plan を再実行する。"""

    from ..analysis import ReturnAnalyzer

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
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[str]]:
        binary_id = ctx.binary1_id if program is ctx.program1 else ctx.binary2_id if program is ctx.program2 else None
        analyzer = ReturnAnalyzer(program, debug=checker.debug, binary_id=binary_id)
        try:
            checker._debug_print(
                f"Fresh reanalysis requested for {binary_name} after signature-changing retry phase"
            )
            fresh_analysis = analyzer.analyze_function_by_name(
                function_name,
                ctx.decompile_timeout,
            )
            if fresh_analysis is None:
                error_message = analyzer.get_last_function_lookup_error() or (
                    f"Fresh reanalysis failed for '{function_name}' in {binary_name}"
                )
                return None, error_message

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
            return replayed, None
        finally:
            analyzer.dispose()

    if need_reanalyze1:
        analysis1, error_message = _reanalyze_with_hypotheses(
            program=ctx.program1,
            function_name=ctx.function_name1,
            binary_name=ctx.binary1_name,
            cached_analysis=analysis1,
        )
        if analysis1 is None:
            checker._debug_print(f"Fresh reanalysis failed for binary1: {error_message}")
            return create_reanalysis_error(ctx, str(error_message), retry_count)

    if need_reanalyze2:
        analysis2, error_message = _reanalyze_with_hypotheses(
            program=ctx.program2,
            function_name=ctx.function_name2,
            binary_name=ctx.binary2_name,
            cached_analysis=analysis2,
        )
        if analysis2 is None:
            checker._debug_print(f"Fresh reanalysis failed for binary2: {error_message}")
            return create_reanalysis_error(ctx, str(error_message), retry_count)

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

    return analysis1, analysis2, result
