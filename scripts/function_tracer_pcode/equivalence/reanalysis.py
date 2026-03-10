# -*- coding: utf-8 -*-
"""解析と再解析のヘルパー"""

from typing import Optional, Tuple
import time

from ..model import FunctionReturnAnalysis, FunctionSignature
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
    analyzer1 = ReturnAnalyzer(ctx.program1, debug=checker.debug)
    try:
        analysis1 = analyzer1.analyze_function_by_name(
            ctx.function_name1, ctx.decompile_timeout
        )
        if analysis1 is None:
            return None, None, create_context_error_result(
                ctx=ctx,
                error_message=f"Function '{ctx.function_name1}' not found in {ctx.binary1_name}",
                start_time=start_time,
                retry_count=retry_count,
            )
    finally:
        analyzer1.dispose()

    checker._debug_print(f"Analyzing function '{ctx.function_name2}' in {ctx.binary2_name}...")
    analyzer2 = ReturnAnalyzer(ctx.program2, debug=checker.debug)
    try:
        analysis2 = analyzer2.analyze_function_by_name(
            ctx.function_name2, ctx.decompile_timeout
        )
        if analysis2 is None:
            return analysis1, None, create_context_error_result(
                ctx=ctx,
                error_message=f"Function '{ctx.function_name2}' not found in {ctx.binary2_name}",
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
    """変更された側だけ再解析して stage plan を実行する"""
    from ..analysis import ReturnAnalyzer

    need_reanalyze1 = phase_result.changed_binary1
    need_reanalyze2 = phase_result.changed_binary2

    checker._debug_print(
        f"Selective reanalysis: binary1={need_reanalyze1}, binary2={need_reanalyze2}"
    )

    if need_reanalyze1:
        checker._debug_print(f"Re-analyzing binary1: {ctx.function_name1}")
        analyzer1 = ReturnAnalyzer(ctx.program1, debug=checker.debug)
        try:
            analysis1 = analyzer1.analyze_function_by_name(
                ctx.function_name1, ctx.decompile_timeout
            )
            if analysis1 is None:
                return create_reanalysis_error(
                    ctx,
                    f"Function '{ctx.function_name1}' not found after type fix",
                    retry_count,
                )
        finally:
            analyzer1.dispose()
    else:
        checker._debug_print("Reusing cached analysis for binary1")
        analysis1 = ctx.analysis1
        if analysis1 is None:
            return create_reanalysis_error(
                ctx,
                "Cached analysis for binary1 is not available",
                retry_count,
            )

    if need_reanalyze2:
        checker._debug_print(f"Re-analyzing binary2: {ctx.function_name2}")
        analyzer2 = ReturnAnalyzer(ctx.program2, debug=checker.debug)
        try:
            analysis2 = analyzer2.analyze_function_by_name(
                ctx.function_name2, ctx.decompile_timeout
            )
            if analysis2 is None:
                return create_reanalysis_error(
                    ctx,
                    f"Function '{ctx.function_name2}' not found after type fix",
                    retry_count,
                )
        finally:
            analyzer2.dispose()
    else:
        checker._debug_print("Reusing cached analysis for binary2")
        analysis2 = ctx.analysis2
        if analysis2 is None:
            return create_reanalysis_error(
                ctx,
                "Cached analysis for binary2 is not available",
                retry_count,
            )

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
