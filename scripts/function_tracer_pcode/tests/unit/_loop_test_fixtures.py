# -*- coding: utf-8 -*-
"""loop recurrence の最小 fixture（test 専用）。

exact に展開した 2 要素の和と、同じ和を ``READONLY_SUM`` の loop summary で
表したものを、同じ ``count == 2`` の条件で並べた 1 組。loop domain の test、
Issue #124 の timeout 分類の test、Issue #163 の supervisor harness（実 child が
loop solver 境界を通す）が同じものを使う。どれかの test module の private に
依存させないため、ここに置く。
"""

from __future__ import annotations

from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    LocationBaseRef,
    LoopSideEffectProfileRef,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    ReadonlyReductionRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis


def readonly_loop_summary(*, start: int, seed_terms=(), step: int = 1) -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=Expression.constant(start, size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        step_expr=Expression.constant(step, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        seed_terms=tuple(seed_terms or ()),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True),
        loop_var_unit="element_index",
    )


def readonly_sum_expr(loop_summary: LoopSummaryRef) -> Expression:
    return Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("base", index=0, data_type="int *", size=8),
            Expression.parameter("count", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=LocationBaseRef.parameter("base", index=0),
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            loop_summary=loop_summary,
        ),
    )


def loop_function_analysis(name: str = "loop_fn") -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x1000",
        parameters=[],
        returns=[],
        binary_id="binary-content-a",
    )


def loop_exact_fixture():
    """(blocker, term, guard, strategy, exact_case, summary_case, left, right)。"""

    from unittest.mock import Mock

    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
        LoopBlockerProductionSignal,
        LoopExactGuardPartitionCompletionSignal,
        LoopExactTermRelationCompletionSignal,
    )
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase

    base = Expression.parameter("base", index=0, data_type="int *", size=8)
    exact_value = Expression.binary_op(
        "INT_ADD",
        Expression.memory(base, size=4),
        Expression.memory(
            Expression.binary_op(
                "INT_ADD", base, Expression.constant(4, size=8)
            ),
            size=4,
        ),
    )
    summary_value = readonly_sum_expr(readonly_loop_summary(start=0, step=1))
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    count_is_two = Condition(
        Expression.binary_op(
            "INT_EQUAL", count, Expression.constant(2, size=4)
        ),
        False,
    )
    parameters = [
        {"name": "base", "index": 0, "data_type": "int *", "size": 8},
        {"name": "count", "index": 1, "data_type": "int", "size": 4},
    ]
    exact_return = ReturnInfo(
        address="0x1010",
        value=exact_value,
        conditions=[count_is_two],
        pcode_identity="exact-return-a",
    )
    summary_return = ReturnInfo(
        address="0x2020",
        value=summary_value,
        conditions=[count_is_two],
        pcode_identity="summary-return-b",
    )
    exact_case = ReturnCase(
        0, [count_is_two], exact_value, exact_return, parameters=parameters
    )
    summary_case = ReturnCase(
        1, [count_is_two], summary_value, summary_return, parameters=parameters
    )
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left = loop_function_analysis("left-loop-exact")
    right = loop_function_analysis("right-loop-summary")
    blocker = LoopBlockerProductionSignal.from_loop_fallback(
        left,
        right,
        exact_case,
        summary_case,
        "counted_loop_summary_expression_proof_missing",
        observation_contract_id="return-and-memory-v1",
    )
    term = LoopExactTermRelationCompletionSignal.from_pairwise_cases(
        blocker, exact_case, summary_case
    )
    guard = LoopExactGuardPartitionCompletionSignal.from_pairwise_cases(
        term, exact_case, summary_case
    )
    return blocker, term, guard, strategy, exact_case, summary_case, left, right
