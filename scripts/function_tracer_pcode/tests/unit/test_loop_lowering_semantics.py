# -*- coding: utf-8 -*-
"""loop lowering の意味 owner（Issue #22 PR-22-B, blocker 2）。

renderer は `core/loop_lowering_semantics.py` が凍結時に確定させた値だけを読む。
ここで確かめるのは 3 つ:

1. 種別・厳密 lowering の可否が **凍結時に決まる**（描画のたびに生 ref を
   読み直さない）
2. 厳密 lowering の可否が緩まない（健全性: 表せないものは未解釈関数へ）
3. 意味そのものが不変（consumer が書き換えられない）
"""

from __future__ import annotations

import dataclasses

import pytest

from scripts.function_tracer_pcode.core import Expression
from scripts.function_tracer_pcode.core.loop_lowering_semantics import (
    LoopLoweringSemantics,
    LoweringKind,
)
from scripts.function_tracer_pcode.core.render_smt.loop_lowering import (
    _counted_loop_sum_function_name,
    _counted_loop_sum_has_exact_lowering,
    _counted_state_transition_value_has_exact_lowering,
)
from scripts.function_tracer_pcode.core.runtime_refs import (
    CountedLoopSummaryRef,
    CountedStateTransitionLoopSummaryRef,
    LoopBodyEffectRef,
    LoopSideEffectProfileRef,
    ReadonlyReductionRef,
    LocationBaseRef,
)
from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection
from scripts.function_tracer_pcode.tests.unit._publication import published


def _counted_loop_sum_expr(ref) -> Expression:
    return published(
        Expression.intrinsic(
            "COUNTED_LOOP_SUM",
            [
                Expression.constant(0, size=4),
                Expression.parameter("start", 0, size=4),
                Expression.parameter("limit", 1, size=4),
            ],
            size=4,
            runtime_ref=ref,
        )
    )


def _counted_loop_sum_ref(*, induction_step: int, residue_cases) -> CountedLoopSummaryRef:
    return CountedLoopSummaryRef(
        induction_step=induction_step,
        result_size=4,
        signed_loop=False,
        residue_cases=residue_cases,
    )


# ---------------------------------------------------------------------------
# 1. 凍結時に決まる
# ---------------------------------------------------------------------------


def test_the_lowering_kind_is_decided_once_at_freeze():
    expr = _counted_loop_sum_expr(
        _counted_loop_sum_ref(induction_step=1, residue_cases=((1, 0, 1, 0),))
    )

    lowering = semantic_projection(expr).loop_lowering

    assert lowering.kind is LoweringKind.COUNTED_LOOP_SUM
    assert lowering.induction_step == 1
    assert lowering.exact_lowering_available is True


def test_the_renderer_does_not_re_read_the_runtime_ref():
    """凍結後に生 ref が別物へ差し替わっても、描画の答えは変わらない。

    renderer が生 ref を読み直していたら、SMT 関数名も厳密 lowering の可否も
    「いつ描画したか」で変わってしまう。
    """

    expr = _counted_loop_sum_expr(
        _counted_loop_sum_ref(induction_step=1, residue_cases=((1, 0, 1, 0),))
    )
    before_name = _counted_loop_sum_function_name(expr)
    assert _counted_loop_sum_has_exact_lowering(expr) is True

    # 凍結済みの式の背後で生 ref を取り替える（本来起こらないが、読み直して
    # いれば必ず結果が動く）。
    object.__setattr__(expr, "runtime_ref", None)

    assert _counted_loop_sum_function_name(expr) == before_name
    assert _counted_loop_sum_has_exact_lowering(expr) is True


# ---------------------------------------------------------------------------
# 2. 厳密 lowering の可否は緩まない
# ---------------------------------------------------------------------------


def test_a_non_power_of_two_modulus_is_not_lowered_exactly():
    """step 1 の剰余分解は 2 冪でなければ閉じた式にできない。"""

    expr = _counted_loop_sum_expr(
        _counted_loop_sum_ref(induction_step=1, residue_cases=((3, 0, 1, 0),))
    )

    assert _counted_loop_sum_has_exact_lowering(expr) is False
    assert semantic_projection(expr).loop_lowering.exact_lowering_available is False


def test_a_multi_step_loop_with_residues_is_not_lowered_exactly():
    expr = _counted_loop_sum_expr(
        _counted_loop_sum_ref(induction_step=2, residue_cases=((2, 0, 1, 0),))
    )

    assert _counted_loop_sum_has_exact_lowering(expr) is False


def test_a_side_effecting_transition_is_not_lowered_exactly():
    """副作用のある loop 本体を閉じた式で表すと、偽の EQUIVALENT になり得る。"""

    state = Expression.parameter("state", 0, size=4)
    transition = Expression.binary_op("INT_MULT", state, Expression.constant(2, size=4))
    impure = LoopSideEffectProfileRef(profile="impure", memory_writes=True)
    ref = CountedStateTransitionLoopSummaryRef(
        initial_state=Expression.constant(1, size=4),
        start_expr=Expression.constant(0, size=4),
        limit_expr=Expression.parameter("n", 1, size=4),
        step_expr=Expression.constant(1, size=4),
        transition_expr=transition,
        state_placeholder=state,
        transition_cases=(((), transition.structural_key()),),
        side_effect_profile=impure,
        state_size=4,
        result_size=4,
    )
    expr = published(
        Expression.intrinsic(
            "COUNTED_STATE_TRANSITION_VALUE",
            [
                Expression.constant(1, size=4),
                Expression.constant(0, size=4),
                Expression.parameter("n", 1, size=4),
            ],
            size=4,
            runtime_ref=ref,
        )
    )

    assert _counted_state_transition_value_has_exact_lowering(expr) is False
    assert semantic_projection(expr).loop_lowering.exact_multiplier is None


def test_a_guard_only_transition_is_still_lowered_exactly():
    """経路 guard だけなら状態は変わらないので、閉じた式で表してよい。"""

    state = Expression.parameter("state", 0, size=4)
    transition = Expression.binary_op("INT_MULT", state, Expression.constant(2, size=4))
    guard_only = LoopSideEffectProfileRef(
        profile="pure_conditional",
        conditional_guards=True,
        guard_count=1,
        effect_descriptors=(LoopBodyEffectRef(kind="conditional_guard"),),
    )
    ref = CountedStateTransitionLoopSummaryRef(
        initial_state=Expression.constant(1, size=4),
        start_expr=Expression.constant(0, size=4),
        limit_expr=Expression.parameter("n", 1, size=4),
        step_expr=Expression.constant(1, size=4),
        transition_expr=transition,
        state_placeholder=state,
        transition_cases=(((), transition.structural_key()),),
        side_effect_profile=guard_only,
        state_size=4,
        result_size=4,
    )
    expr = published(
        Expression.intrinsic(
            "COUNTED_STATE_TRANSITION_VALUE",
            [
                Expression.constant(1, size=4),
                Expression.constant(0, size=4),
                Expression.parameter("n", 1, size=4),
            ],
            size=4,
            runtime_ref=ref,
        )
    )

    assert _counted_state_transition_value_has_exact_lowering(expr) is True
    assert semantic_projection(expr).loop_lowering.exact_multiplier == 2


# ---------------------------------------------------------------------------
# 3. 意味は不変
# ---------------------------------------------------------------------------


def test_the_lowering_semantics_cannot_be_rewritten_by_a_consumer():
    expr = _counted_loop_sum_expr(
        _counted_loop_sum_ref(induction_step=1, residue_cases=((1, 0, 1, 0),))
    )
    lowering = semantic_projection(expr).loop_lowering

    with pytest.raises(dataclasses.FrozenInstanceError):
        lowering.exact_lowering_available = False


def test_an_expression_without_a_loop_summary_has_no_lowering():
    expr = published(Expression.parameter("p", 0, size=4))

    lowering = semantic_projection(expr).loop_lowering

    assert isinstance(lowering, LoopLoweringSemantics)
    assert lowering.kind is LoweringKind.NONE
    assert lowering.exact_lowering_available is False


def test_a_readonly_reduction_is_classified_as_a_reduction():
    ref = ReadonlyReductionRef(
        reduction_kind="sum",
        pointer_base_ref=LocationBaseRef.stack_frame(),
        count_parameter_name="n",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
    )
    expr = published(
        Expression.intrinsic(
            "READONLY_SUM",
            [Expression.constant(0, size=4), Expression.parameter("n", 1, size=4)],
            size=4,
            runtime_ref=ref,
        )
    )

    lowering = semantic_projection(expr).loop_lowering

    assert lowering.kind is LoweringKind.READONLY_REDUCTION
    assert lowering.reduction_kind == "sum"
    # reduction は未解釈関数で表す（閉じた式にはしない）。
    assert lowering.exact_lowering_available is False
