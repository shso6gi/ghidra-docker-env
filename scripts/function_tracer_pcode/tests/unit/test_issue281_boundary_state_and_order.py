# -*- coding: utf-8 -*-
"""Issue #281 review 4: 関数境界の post-state の主張と、読み出し・書き込みの順序（#285）。

1. callee の値の node に付いた post-state の主張（`PostStateValueRef` など）は callee の出口の状態のもの。
   caller の consumer は caller の出口の状態と読むので、境界で落とすか拒否する（review: callee が `*p = 5` の
   後に返す 5 が、caller が `q` を渡して呼んだ後の `*p = 9` の 9 に化けた）。
2. 読み出し・書き込み・呼び出しの位置は、同じ関数の `ProgramOrder` の key で比べる（review: caller が
   `*p = 2` の後で呼び出すと、読み出しの順序 3 と書き込みの `0x1004 << 8` を比べ、読み出しが `MEM[p]` のまま
   残った）。loop の中の書き込みは key で前後を表せないので、effect 要約を不完全にする。

ここの順序の数は production と同じ作り方（偽の CFG から tracer が作る key）にしてある。
"""

import pytest

from scripts.function_tracer_pcode.analysis.effects.call_boundary import (
    REFUSED_CALLEE_PLACE,
    REFUSED_CALLEE_STATE_READ,
    REFUSED_CALLEE_SUMMARY_REF,
    CallBoundaryRefused,
    CallSite,
    CalleeTimeline,
    import_callee_expression,
)
from scripts.function_tracer_pcode.analysis.effects.location import substitute_expression
from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary, StoreEffect
from scripts.function_tracer_pcode.analysis.effects.post_state import (
    _attach_materialized_post_state_value_ref,
    collapse_post_state_expr_to_canonical_read,
    rewrite_loads_from_effects,
    rewrite_observed_loads_from_effects,
)
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    ObservedMemoryReadRef,
    PostStateReadRef,
)
from scripts.function_tracer_pcode.core.program_order import ProgramOrder
from scripts.function_tracer_pcode.core.runtime_refs import LoopTermDescriptorRef, LoopSummaryRef
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.tests.unit._program_order_fakes import FakeOp, fake_cfg

CALLEE_PARAMETERS = [{"name": "param_1", "index": 0, "data_type": "int *", "size": 8}]
CALLER_PARAMETERS = [
    {"name": "p", "index": 0, "data_type": "int *", "size": 8},
    {"name": "q", "index": 1, "data_type": "int *", "size": 8},
]


def _callee_pointer() -> Expression:
    return Expression.parameter("param_1", index=0, data_type="int *", size=8)


def _p() -> Expression:
    return Expression.parameter("p", index=0, data_type="int *", size=8)


def _q() -> Expression:
    return Expression.parameter("q", index=1, data_type="int *", size=8)


def _callee_location() -> CanonicalLocation:
    return CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=0, size=4)


def _caller_store_to_p(value: int, order_key: int, conditions=()) -> StoreEffect:
    return StoreEffect(
        location=CanonicalLocation(base_ref=LocationBaseRef.parameter("p", index=0), offset=0, size=4),
        value=Expression.constant(value, size=4),
        conditions=list(conditions),
        order_key=order_key,
    )


def _callee_writes_5() -> CalleeTimeline:
    effect = StoreEffect(location=_callee_location(), value=Expression.constant(5, size=4), conditions=[], order_key=10)
    return CalleeTimeline.from_effect_summary(
        EffectSummary(parameter_names=["param_1"], effects=[effect]),
        CALLEE_PARAMETERS,
    )


def _to_caller(expr: Expression, site: CallSite, timeline: CalleeTimeline, argument: Expression) -> Expression:
    imported = import_callee_expression(expr, site, timeline)
    return substitute_expression(imported, {("parameter", 0): argument}, CALLEE_PARAMETERS)


# ---------------------------------------------------------------------------
# 1. post-state の主張: review の例（callee が *param_1 = 5 の後に 5 を返し、caller は q を渡して呼んだ後 *p = 9）
# ---------------------------------------------------------------------------


def _callee_returns_its_written_value() -> Expression:
    """callee の出口の値 5 に「callee の出口の状態の `*param_1` と等しい」という主張が付いた形。"""

    return _attach_materialized_post_state_value_ref(Expression.constant(5, size=4), _callee_location())


def test_without_the_boundary_the_callee_post_state_claim_becomes_the_caller_store():
    """修正前の経路（置き換えだけ）: 主張が残り、caller の後処理で 5 → `MEM[param_1]` → 9 になる。"""

    substituted = substitute_expression(_callee_returns_its_written_value(), {("parameter", 0): _q()}, CALLEE_PARAMETERS)
    caller_store = _caller_store_to_p(9, order_key=5)
    collapsed = collapse_post_state_expr_to_canonical_read(substituted, [caller_store], CALLER_PARAMETERS)
    assert collapsed is not None and collapsed.expr_type is ExpressionType.MEMORY
    rewritten = rewrite_loads_from_effects(collapsed, [], [caller_store], CALLER_PARAMETERS)
    assert rewritten.expr_type is ExpressionType.CONSTANT and rewritten.value == 9


def test_the_boundary_drops_the_callee_post_state_claim_and_keeps_the_value():
    moved = _to_caller(_callee_returns_its_written_value(), CallSite(3), _callee_writes_5(), _q())
    assert moved.expr_type is ExpressionType.CONSTANT and moved.value == 5
    assert moved.runtime_ref is None
    assert collapse_post_state_expr_to_canonical_read(moved, [_caller_store_to_p(9, order_key=5)], CALLER_PARAMETERS) is None


def test_a_composite_value_with_a_post_state_claim_keeps_its_operands_moved():
    """複合式の主張も落とし、operand（callee の parameter）は caller の引数に置き換わる。"""

    value = _attach_materialized_post_state_value_ref(
        Expression.binary_op("+", _callee_pointer(), Expression.constant(1, size=8)),
        _callee_location(),
    )
    moved = _to_caller(value, CallSite(3), _callee_writes_5(), _q())
    assert moved.runtime_ref is None
    assert moved.operands[0].name == "q"


def test_a_phi_with_a_post_state_claim_drops_the_claim_even_when_its_branches_do_not_change():
    phi = Expression.phi(
        [
            (Condition(Expression.variable("c", size=1)), Expression.constant(5, size=4)),
            (None, Expression.constant(6, size=4)),
        ]
    )
    phi.size = 4
    claimed = _attach_materialized_post_state_value_ref(phi, _callee_location())
    moved = import_callee_expression(claimed, CallSite(3), _callee_writes_5())
    assert moved.expr_type is ExpressionType.PHI
    assert moved.runtime_ref is None


@pytest.mark.parametrize(
    "ref",
    [
        PostStateReadRef(location=_callee_location()),
        _callee_location(),
    ],
    ids=["symbolic-post-state-read", "canonical-location-read"],
)
def test_a_callee_post_state_read_variable_is_refused(ref):
    """`poststate_*` の変数は callee の出口の状態の読み出しそのもの: caller の言葉に無い。"""

    variable = Expression.variable("poststate_param_1_size_4", size=4, runtime_ref=ref)
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(variable, CallSite(3), _callee_writes_5())
    assert refused.value.reason == REFUSED_CALLEE_STATE_READ


def test_a_global_base_is_kept_and_a_callee_place_is_refused():
    global_value = Expression.variable(
        "g", size=8, runtime_ref=LocationBaseRef.global_object("g", 4)
    )
    assert import_callee_expression(global_value, CallSite(3), _callee_writes_5()) is global_value

    callee_frame = Expression.variable("stack", size=8, runtime_ref=LocationBaseRef.stack_frame())
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(callee_frame, CallSite(3), _callee_writes_5())
    assert refused.value.reason == REFUSED_CALLEE_PLACE


def test_a_parameter_base_is_kept_only_on_the_parameter_that_substitution_replaces():
    parameter = Expression.parameter(
        "param_1", index=0, data_type="int *", size=8, runtime_ref=LocationBaseRef.parameter("param_1", index=0)
    )
    assert import_callee_expression(parameter, CallSite(3), _callee_writes_5()) is parameter
    adapter = Expression.unary_op("ZEXT", _callee_pointer()).derive_with(
        runtime_ref=LocationBaseRef.parameter("param_1", index=0)
    )
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(adapter, CallSite(3), _callee_writes_5())
    assert refused.value.reason == REFUSED_CALLEE_PLACE


def test_a_value_that_claims_the_callee_stack_is_refused():
    stack_value = Expression.variable(
        "sp",
        size=8,
        storage_info=StorageInfo(is_register=True, register_name="sp", size=8, is_stack_pointer=True),
    )
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(stack_value, CallSite(3), _callee_writes_5())
    assert refused.value.reason == REFUSED_CALLEE_PLACE


def test_a_summary_ref_that_holds_callee_expressions_is_refused():
    summary = LoopSummaryRef(
        start_expr=_callee_pointer(),
        limit_expr=Expression.constant(4, size=4),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="reduction", result_size=4),
    )
    node = Expression.variable("loop_sum", size=4, runtime_ref=summary)
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(node, CallSite(3), _callee_writes_5())
    assert refused.value.reason == REFUSED_CALLEE_SUMMARY_REF


# ---------------------------------------------------------------------------
# 2. 読み出しと書き込みの順序（#285）: production と同じ作り方の key
# ---------------------------------------------------------------------------


def _tracer(successors):
    high_function, blocks = fake_cfg(successors)
    tracer = object.__new__(PcodeTracer)
    tracer.high_function = high_function
    return tracer, blocks


def _callee_read(order: int = 10) -> Expression:
    return Expression.memory(
        _callee_pointer(),
        4,
        read_order_key=order,
        runtime_ref=ObservedMemoryReadRef(order_key=order),
    )


def _callee_reads_only() -> CalleeTimeline:
    return CalleeTimeline.from_effect_summary(EffectSummary(parameter_names=["param_1"], effects=[]), CALLEE_PARAMETERS)


def test_with_the_old_units_a_store_before_the_call_is_not_seen():
    """修正前の単位: 読み出しは `getOrder()`（3）、書き込みは `(番地 << 8) | getOrder()`。前の書き込みを見ない。"""

    moved = _to_caller(_callee_read(), CallSite(3), _callee_reads_only(), _p())
    rewritten = rewrite_observed_loads_from_effects(moved, [], [_caller_store_to_p(2, (0x1004 << 8) | 1)], CALLER_PARAMETERS)
    assert rewritten.expr_type is ExpressionType.MEMORY


def test_a_callee_read_sees_a_caller_store_made_before_the_call():
    """review の例: caller が `*p = 2` の後で呼び出す。読み出しは呼び出しの位置で 2 を見る。"""

    tracer, blocks = _tracer({0: []})
    store_key = tracer._get_op_order_key(FakeOp(blocks[0], 1, mnemonic="STORE", address=0x1004))
    call_key = tracer._get_op_order_key(FakeOp(blocks[0], 3, mnemonic="CALL", address=0x1008))
    moved = _to_caller(_callee_read(), CallSite(call_key), _callee_reads_only(), _p())
    rewritten = rewrite_observed_loads_from_effects(moved, [], [_caller_store_to_p(2, store_key)], CALLER_PARAMETERS)
    assert rewritten.expr_type is ExpressionType.CONSTANT and rewritten.value == 2


def test_a_callee_read_does_not_see_a_caller_store_in_a_later_block():
    tracer, blocks = _tracer({0: [1], 1: []})
    call_key = tracer._get_op_order_key(FakeOp(blocks[0], 5, mnemonic="CALL"))
    later_store_key = tracer._get_op_order_key(FakeOp(blocks[1], 0, mnemonic="STORE"))
    moved = _to_caller(_callee_read(), CallSite(call_key), _callee_reads_only(), _p())
    rewritten = rewrite_observed_loads_from_effects(moved, [], [_caller_store_to_p(9, later_store_key)], CALLER_PARAMETERS)
    assert rewritten.expr_type is ExpressionType.MEMORY


def test_a_store_in_a_block_laid_out_after_the_call_but_executed_before_it_is_seen():
    """CFG 0 → 2 → 1: block 2（番号・番地が後ろ）の書き込みは block 1 の呼び出しより先に実行される。"""

    tracer, blocks = _tracer({0: [2], 2: [1], 1: []})
    store_key = tracer._get_op_order_key(FakeOp(blocks[2], 4, mnemonic="STORE", address=0x2000))
    call_key = tracer._get_op_order_key(FakeOp(blocks[1], 0, mnemonic="CALL", address=0x1000))
    moved = _to_caller(_callee_read(), CallSite(call_key), _callee_reads_only(), _p())
    rewritten = rewrite_observed_loads_from_effects(moved, [], [_caller_store_to_p(2, store_key)], CALLER_PARAMETERS)
    assert rewritten.expr_type is ExpressionType.CONSTANT and rewritten.value == 2


def test_a_store_on_one_arm_of_a_branch_is_seen_only_under_its_condition():
    """0 → {1, 2} → 3、書き込みは腕 1（条件 c）、呼び出しは合流 3。読み出しは c の下でだけ 2。"""

    tracer, blocks = _tracer({0: [1, 2], 1: [3], 2: [3], 3: []})
    condition = Condition(Expression.variable("c", size=1))
    store_key = tracer._get_op_order_key(FakeOp(blocks[1], 0, mnemonic="STORE"))
    call_key = tracer._get_op_order_key(FakeOp(blocks[3], 0, mnemonic="CALL"))
    moved = _to_caller(_callee_read(), CallSite(call_key), _callee_reads_only(), _p())
    rewritten = rewrite_observed_loads_from_effects(
        moved, [], [_caller_store_to_p(2, store_key, conditions=[condition])], CALLER_PARAMETERS
    )
    assert rewritten.expr_type is ExpressionType.PHI
    branches = rewritten.value
    assert branches[0][1].expr_type is ExpressionType.CONSTANT and branches[0][1].value == 2
    assert branches[-1][0] is None and branches[-1][1].expr_type is ExpressionType.MEMORY


def test_the_last_write_of_a_function_is_the_last_in_its_cfg():
    """同じ位置への 2 つの書き込みを再生する。CFG 0 → 2 → 1 で後に実行される block 1（番号・番地は小さい）の
    書き込みが最後。修正前の `(番地 << 8) | getOrder()` では番地の大きい block 2 の書き込みが最後になった。"""

    from scripts.function_tracer_pcode.analysis.effects.location import (
        _impl__replay_definite_active_effects_for_location as replay,
    )

    tracer, blocks = _tracer({0: [2], 2: [1], 1: []})
    first = tracer._get_op_order_key(FakeOp(blocks[2], 0, mnemonic="STORE", address=0x3000))
    last = tracer._get_op_order_key(FakeOp(blocks[1], 0, mnemonic="STORE", address=0x1000))
    location = _caller_store_to_p(0, 0).location
    final = replay(location, [], [_caller_store_to_p(1, first), _caller_store_to_p(7, last)], CALLER_PARAMETERS)
    assert final.expr_type is ExpressionType.CONSTANT and final.value == 7

    by_address = replay(
        location, [], [_caller_store_to_p(1, 0x3000 << 8), _caller_store_to_p(7, 0x1000 << 8)], CALLER_PARAMETERS
    )
    assert by_address.value == 1


# ---------------------------------------------------------------------------
# loop の中の書き込み: effect 要約が不完全になり、両方の判定を止める
# ---------------------------------------------------------------------------


def _summarize_one_call(successors, call_block: int):
    from scripts.function_tracer_pcode.analysis.effects.summary import summarize_store_effects
    from scripts.function_tracer_pcode.core.call_target import CallTargetRef
    from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import _param, _reg_storage

    high_function, blocks = fake_cfg(successors)

    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

    class FakeCallOp(FakeOp):
        def __init__(self):
            super().__init__(blocks[call_block], 0, mnemonic="CALL")
            self._inputs = [FakeVarnode("target", 8), FakeVarnode("slot", 8)]

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        index = call_block
        pcode_ops = [FakeCallOp()]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    order_source = object.__new__(PcodeTracer)
    order_source.high_function = high_function

    class FakeTracer:
        def program_order(self):
            return order_source.program_order()

        def _get_op_order_key(self, op):
            return order_source._get_op_order_key(op)

        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("callee")

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "slot":
                return Expression.parameter("slot", 0, size=8)
            return Expression.constant(0, max(1, varnode.getSize()))

    slot = _param("slot", size=8, index=0, storage=_reg_storage("x0", register_name="x0"))
    callee_effect = StoreEffect(
        location=CanonicalLocation(base_ref=LocationBaseRef.parameter("slot", index=0), offset=0, size=4),
        value=Expression.constant(5, size=4),
        conditions=[],
        order_key=1,
    )
    return summarize_store_effects(
        [FakeBlockInfo()],
        FakeTracer(),
        FakeConditionTracker(),
        [slot],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["slot"],
            parameter_refs=[LocationBaseRef.parameter("slot", index=0)],
            effects=[callee_effect],
        ),
        resolve_callee_parameters=lambda _target_ref: [slot],
        debug=False,
    )


def test_an_effect_outside_any_loop_keeps_the_summary_complete():
    summary = _summarize_one_call({0: [1], 1: []}, call_block=1)
    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    assert summary.effects[0].order_key == ProgramOrder({0: [1], 1: []}).key(1, 0)


def test_an_effect_inside_a_loop_blocks_both_verdicts():
    """loop（0 → 1 → 0）の中の書き込みは、key で前後を表せない: 要約を不完全にする。"""

    from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis

    summary = _summarize_one_call({0: [1], 1: [0, 2], 2: []}, call_block=1)
    assert summary.has_unsupported_call is True
    assert "effect_order_in_cycle" in summary.incomplete_reasons
    analysis = create_mock_analysis("caller")
    analysis.effect_summary = summary
    assert "unsupported_call_effect_summary" in analysis.get_equivalence_blocking_unsafety_reasons()
    assert "unsupported_call_effect_summary" in analysis.get_decisive_sat_unsafety_reasons()
