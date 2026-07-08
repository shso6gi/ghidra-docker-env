# -*- coding: utf-8 -*-
"""EquivalenceResult 作成ヘルパー"""

from typing import Optional, Tuple
import time

from ..model import FunctionReturnAnalysis, FunctionSignature
from ..smt import ParallelResult
from .phases.handler import PhaseContext
from .result import EquivalenceResult
from .typing.fixer import TypeFixResult
from .unknown_reason import UnknownReasonId, make_unknown_reason
from ..analysis.failure import (
    ANALYSIS_STATUS_DECOMPILATION_FAILED,
    ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
)


_OPERATIONAL_UNKNOWN_REASON_BY_FAILURE_STATUS = {
    ANALYSIS_STATUS_DECOMPILATION_FAILED: UnknownReasonId.DECOMPILATION_FAILED,
    ANALYSIS_STATUS_HIGH_FUNCTION_MISSING: UnknownReasonId.HIGH_FUNCTION_MISSING,
}


def create_error_result(
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    binary1_name: str,
    binary2_name: str,
    error_message: str,
    start_time: float,
    type_fix_result: Optional[TypeFixResult],
    retry_count: int,
    original_signature1: Optional[FunctionSignature],
    original_signature2: Optional[FunctionSignature],
    failure_status: Optional[str] = None,
    failure_message: Optional[str] = None,
) -> EquivalenceResult:
    """通常のエラー結果を作成する"""
    return EquivalenceResult(
        is_equivalent=None,
        function1_name=analysis1.function_name,
        function2_name=analysis2.function_name,
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        solver_results=ParallelResult(results=[]),
        total_time=time.time() - start_time,
        error_message=error_message,
        failure_status=failure_status,
        failure_message=failure_message,
        type_fix_result=type_fix_result,
        retry_count=retry_count,
        function1_signature=original_signature1,
        function2_signature=original_signature2,
        effective_function1_signature=FunctionSignature.from_analysis(analysis1),
        effective_function2_signature=FunctionSignature.from_analysis(analysis2),
        function1_signature_hypotheses=list(analysis1.signature_hypotheses),
        function2_signature_hypotheses=list(analysis2.signature_hypotheses),
        constrained_fragments=[]
    )


def create_context_error_result(
    ctx: PhaseContext,
    error_message: str,
    start_time: float,
    retry_count: int,
    analysis1: Optional[FunctionReturnAnalysis] = None,
    analysis2: Optional[FunctionReturnAnalysis] = None,
    failure_status: Optional[str] = None,
    failure_message: Optional[str] = None,
) -> EquivalenceResult:
    """PhaseContext ベースのエラー結果を作成する"""
    function1_name = analysis1.function_name if analysis1 is not None else ctx.function_name1
    function2_name = analysis2.function_name if analysis2 is not None else ctx.function_name2

    return EquivalenceResult(
        is_equivalent=None,
        function1_name=function1_name,
        function2_name=function2_name,
        binary1_name=ctx.binary1_name,
        binary2_name=ctx.binary2_name,
        solver_results=ParallelResult(results=[]),
        total_time=time.time() - start_time,
        error_message=error_message,
        failure_status=failure_status,
        failure_message=failure_message,
        type_fix_result=ctx.type_fix_result,
        retry_count=retry_count,
        function1_signature=ctx.original_signature1,
        function2_signature=ctx.original_signature2,
        effective_function1_signature=FunctionSignature.from_analysis(analysis1) if analysis1 is not None else ctx.original_signature1,
        effective_function2_signature=FunctionSignature.from_analysis(analysis2) if analysis2 is not None else ctx.original_signature2,
        function1_signature_hypotheses=list(analysis1.signature_hypotheses) if analysis1 is not None else [],
        function2_signature_hypotheses=list(analysis2.signature_hypotheses) if analysis2 is not None else [],
        constrained_fragments=[]
    )


def create_reanalysis_error(
    ctx: PhaseContext,
    error_message: str,
    retry_count: int,
    failure_status: Optional[str] = None,
) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
    """再解析失敗時の戻り値を作成する"""
    result = create_context_error_result(
        ctx=ctx,
        error_message=error_message,
        start_time=time.time(),
        retry_count=retry_count,
        analysis1=ctx.analysis1,
        analysis2=ctx.analysis2,
        failure_status=failure_status,
        failure_message=error_message,
    )
    return ctx.analysis1, ctx.analysis2, result


def create_context_unknown_result(
    ctx: PhaseContext,
    failure_status: str,
    message: str,
    start_time: float,
    retry_count: int,
    analysis1: Optional[FunctionReturnAnalysis] = None,
    analysis2: Optional[FunctionReturnAnalysis] = None,
) -> EquivalenceResult:
    """Create a non-error operational UNKNOWN result."""
    function1_name = analysis1.function_name if analysis1 is not None else ctx.function_name1
    function2_name = analysis2.function_name if analysis2 is not None else ctx.function_name2
    unknown_reason_id = _OPERATIONAL_UNKNOWN_REASON_BY_FAILURE_STATUS.get(failure_status)
    unknown_reasons = []
    if unknown_reason_id is not None:
        unknown_reasons.append(
            make_unknown_reason(
                unknown_reason_id,
                stage="reanalysis",
                pair_or_case=f"{function1_name} ↔ {function2_name}",
                evidence_refs=(failure_status,),
                detail=message,
            )
        )

    return EquivalenceResult(
        is_equivalent=None,
        function1_name=function1_name,
        function2_name=function2_name,
        binary1_name=ctx.binary1_name,
        binary2_name=ctx.binary2_name,
        solver_results=ParallelResult(results=[]),
        total_time=time.time() - start_time,
        error_message=None,
        failure_status=failure_status,
        failure_message=message,
        type_fix_result=ctx.type_fix_result,
        retry_count=retry_count,
        function1_signature=ctx.original_signature1,
        function2_signature=ctx.original_signature2,
        effective_function1_signature=FunctionSignature.from_analysis(analysis1) if analysis1 is not None else ctx.original_signature1,
        effective_function2_signature=FunctionSignature.from_analysis(analysis2) if analysis2 is not None else ctx.original_signature2,
        function1_signature_hypotheses=list(analysis1.signature_hypotheses) if analysis1 is not None else [],
        function2_signature_hypotheses=list(analysis2.signature_hypotheses) if analysis2 is not None else [],
        constrained_fragments=[],
        pairwise_debug_stats={"operational_failure": 1},
        unknown_reasons=unknown_reasons,
    )
