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
from scripts.function_tracer_pcode.core.program_order import ProgramOrder, call_effect_key
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
@pytest.mark.parametrize("with_binding", [False, True], ids=["import-only", "import-and-substitute"])
def test_a_callee_post_state_read_variable_is_refused(ref, with_binding):
    """`poststate_*` の変数は callee の出口の状態の読み出しそのもの: caller の言葉に無い。

    `*param_1` の post-state は param_1 の基底の key を持つが、parameter の値ではない。置き換え（binding）が
    あっても、引数（番地）に置き換えてはいけない（review 5 の自己レビュー: ref の規則を置き換えより先に見る）。
    """

    from scripts.function_tracer_pcode.analysis.effects.call_boundary import CalleeBinding

    variable = Expression.variable("poststate_param_1_size_4", size=4, runtime_ref=ref)
    binding = CalleeBinding.for_arguments(CALLEE_PARAMETERS, [_q()]) if with_binding else None
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(variable, CallSite(3), _callee_writes_5(), binding=binding)
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


def _summarize_one_call(successors, call_block: int, *, callee_effects=None, callee_parameter_names=("slot",)):
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
            # caller は同じ `slot` を callee のすべての引数に渡す（2 引数なら alias）
            self._inputs = [FakeVarnode("target", 8)] + [FakeVarnode("slot", 8) for _ in callee_parameter_names]

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
    callee_params = [
        _param(name, size=8, index=index, storage=_reg_storage(f"x{index}", register_name=f"x{index}"))
        for index, name in enumerate(callee_parameter_names)
    ]
    if callee_effects is None:
        callee_effects = [
            StoreEffect(
                location=CanonicalLocation(base_ref=LocationBaseRef.parameter("slot", index=0), offset=0, size=4),
                value=Expression.constant(5, size=4),
                conditions=[],
                order_key=1,
            )
        ]
    return summarize_store_effects(
        [FakeBlockInfo()],
        FakeTracer(),
        FakeConditionTracker(),
        [slot],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=list(callee_parameter_names),
            parameter_refs=[
                LocationBaseRef.parameter(name, index=index) for index, name in enumerate(callee_parameter_names)
            ],
            effects=list(callee_effects),
        ),
        resolve_callee_parameters=lambda _target_ref: callee_params,
        debug=False,
    )


def test_an_effect_outside_any_loop_keeps_the_summary_complete():
    summary = _summarize_one_call({0: [1], 1: []}, call_block=1)
    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    # callee の書き込みは呼び出しの op の key の中の slot 1（呼び出しの位置の読み出しより後、次の op より前）
    assert summary.effects[0].order_key == call_effect_key(ProgramOrder({0: [1], 1: []}).key(1, 0), 1)


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


# ---------------------------------------------------------------------------
# review 5-1: callee の複数の書き込みは、呼び出しの中で callee の順に並ぶ
# ---------------------------------------------------------------------------


def _callee_store(name: str, index: int, value: int, order_key: int) -> StoreEffect:
    return StoreEffect(
        location=CanonicalLocation(base_ref=LocationBaseRef.parameter(name, index=index), offset=0, size=4),
        value=Expression.constant(value, size=4),
        conditions=[],
        order_key=order_key,
    )


def _caller_final_value_of_slot(summary) -> Expression:
    from scripts.function_tracer_pcode.analysis.effects.location import (
        _impl__replay_definite_active_effects_for_location as replay,
    )
    from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import _param, _reg_storage

    slot = _param("slot", size=8, index=0, storage=_reg_storage("x0", register_name="x0"))
    location = CanonicalLocation(base_ref=LocationBaseRef.parameter("slot", index=0), offset=0, size=4)
    return replay(location, [], summary.effects, [slot])


@pytest.mark.parametrize("listed_order", ["callee_order", "reversed"])
def test_two_callee_writes_to_one_place_keep_their_callee_order_in_the_caller(listed_order):
    """callee が `*p = 5; *p = 9`。caller の要約の最後の書き込みは 9（effect の並びの順に依らない）。

    修正前はどちらの書き込みも呼び出しの key になり、consumer ごとに 5 か 9 を選んだ（review 5-1）。
    """

    effects = [_callee_store("slot", 0, 5, order_key=10), _callee_store("slot", 0, 9, order_key=20)]
    if listed_order == "reversed":
        effects.reverse()
    summary = _summarize_one_call({0: [1], 1: []}, call_block=1, callee_effects=effects)
    assert summary.has_unsupported_call is False
    keys = sorted(effect.order_key for effect in summary.effects)
    assert len(set(keys)) == 2
    final = _caller_final_value_of_slot(summary)
    assert final.expr_type is ExpressionType.CONSTANT and final.value == 9


def test_callee_writes_through_two_aliasing_parameters_keep_their_order():
    """callee が `*a = 5; *b = 9` で、caller は同じ番地を a と b に渡す（alias）。最後は 9。"""

    effects = [_callee_store("b", 1, 9, order_key=20), _callee_store("a", 0, 5, order_key=10)]
    summary = _summarize_one_call(
        {0: [1], 1: []}, call_block=1, callee_effects=effects, callee_parameter_names=("a", "b")
    )
    assert summary.has_unsupported_call is False
    final = _caller_final_value_of_slot(summary)
    assert final.expr_type is ExpressionType.CONSTANT and final.value == 9


def test_callee_writes_sit_between_the_call_and_the_next_op():
    order = ProgramOrder({0: [1], 1: []})
    call_key = order.key(1, 4)
    effects = [_callee_store("slot", 0, 5, order_key=10), _callee_store("slot", 0, 9, order_key=20)]
    timeline = CalleeTimeline.from_effect_summary(EffectSummary(parameter_names=["slot"], effects=effects))
    site = CallSite(call_key)
    slots = timeline.effect_slots()
    first, second = site.effect_key(slots[10]), site.effect_key(slots[20])
    # 呼び出しの位置で読む caller の読み出し（key = 呼び出しの key）< callee の書き込み < 呼び出しの後の op
    assert call_key < first < second < order.key(1, 5)


def test_a_callee_write_with_an_unknown_order_makes_the_call_unsupported():
    effects = [_callee_store("slot", 0, 5, order_key=-1), _callee_store("slot", 0, 9, order_key=20)]
    summary = _summarize_one_call({0: [1], 1: []}, call_block=1, callee_effects=effects)
    assert summary.has_unsupported_call is True
    assert summary.effects == []


# ---------------------------------------------------------------------------
# review 5-2: 引数の一部だけを束縛した callee の parameter を caller へ残さない
# ---------------------------------------------------------------------------


TWO_CALLEE_PARAMETERS = [
    {"name": "param_1", "index": 0, "data_type": "int", "size": 4},
    {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
]


def test_a_callee_parameter_without_an_argument_is_refused_by_the_boundary():
    from scripts.function_tracer_pcode.analysis.effects.call_boundary import (
        REFUSED_CALLEE_PARAMETER_UNBOUND,
        CalleeBinding,
    )

    value = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("param_1", index=0, size=4),
        Expression.parameter("param_2", index=1, size=4),
    )
    binding = CalleeBinding.for_arguments(TWO_CALLEE_PARAMETERS, [Expression.constant(3, size=4)])
    with pytest.raises(CallBoundaryRefused) as raised:
        import_callee_expression(value, CallSite(None), CalleeTimeline.unknown(), binding=binding)
    assert raised.value.reason == REFUSED_CALLEE_PARAMETER_UNBOUND


def test_a_partially_bound_callee_is_not_expanded_with_its_parameters_left_in_place():
    """修正前: 解析の scope に束縛が 1 つでもあると「特殊化済み」とされ、置き換えを飛ばして callee の
    `param_2` が caller の式に残った（review 5-2）。"""

    from unittest.mock import Mock

    from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
    from scripts.function_tracer_pcode.core.call_target import CallTargetRef
    from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
    from scripts.function_tracer_pcode.core.analysis import ReturnInfo

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analysis = create_mock_analysis(
        "callee",
        parameters=list(TWO_CALLEE_PARAMETERS),
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("param_2", index=1, size=4), conditions=[])],
    )
    analysis.analysis_scope_key = ("analysis_scope", ("function", "callee"), ((0, ("bound", 3)),), ())
    analyzer._get_or_analyze_call_target = Mock(return_value=analysis)
    analyzer._call_summary_is_safe = Mock(return_value=True)

    expanded = analyzer._resolve_call_expansions(
        CallTargetRef.from_name("callee"), [Expression.constant(3, size=4)], set()
    )

    leaked = [
        item for item in (expanded or [])
        if any(node.name == "param_2" for node in _walk(item.value))
    ]
    assert leaked == []


def _walk(expr):
    stack = [expr]
    while stack:
        node = stack.pop()
        if node is None:
            continue
        yield node
        stack.extend(node.operands or ())


# ---------------------------------------------------------------------------
# review 5-3: callee の frame（stack / frame pointer、stack 空間）を caller の frame と読ませない
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "storage",
    [
        StorageInfo(is_register=True, register_name="s8", size=8),
        StorageInfo(is_register=True, register_name="x29", size=8),
        StorageInfo(is_register=False, space_name="stack", offset=-16, size=8),
    ],
    ids=["mips_frame_pointer", "arm64_frame_pointer", "stack_space"],
)
def test_a_value_on_the_callee_frame_is_refused(storage):
    value = Expression.binary_op(
        "INT_ADD",
        Expression.variable("fp", size=8, storage_info=storage),
        Expression.constant(8, size=8),
    )
    with pytest.raises(CallBoundaryRefused) as raised:
        import_callee_expression(value, CallSite(None), CalleeTimeline.unknown())
    assert raised.value.reason == REFUSED_CALLEE_PLACE


def test_a_stack_passed_callee_parameter_is_replaced_not_refused():
    """callee の stack で渡る parameter は、置き換えがあれば caller の引数になる（frame の主張として拒否しない）。"""

    from scripts.function_tracer_pcode.analysis.effects.call_boundary import CalleeBinding

    stack_slot = StorageInfo(is_register=False, space_name="stack", offset=8, size=4)
    params = [{"name": "param_9", "index": 0, "data_type": "int", "size": 4, "storage": stack_slot}]
    value = Expression.parameter("param_9", index=0, size=4).clone_with(storage_info=stack_slot)
    binding = CalleeBinding.for_arguments(params, [_q()])
    imported = import_callee_expression(value, CallSite(None), CalleeTimeline.unknown(), binding=binding)
    # 引数は callee の parameter の幅へ合わせて入る（4 byte の parameter へ 8 byte の q）
    names = {node.name for node in _walk(imported) if node.expr_type is ExpressionType.PARAMETER}
    assert names == {"q"}


# ---------------------------------------------------------------------------
# review 5-4: 読めない CFG の辺を無視して順序を作らない
# ---------------------------------------------------------------------------


def test_an_unreadable_edge_gives_no_program_order():
    from scripts.function_tracer_pcode.analysis.program_points import program_order_for_high_function

    high_function, blocks = fake_cfg({0: [1], 1: []})
    blocks[0].getOut = lambda position: None
    assert program_order_for_high_function(high_function) is None


def test_a_java_exception_from_an_edge_gives_no_program_order(monkeypatch):
    """Ghidra の `getOut` は decode で埋まらなかった辺を `NullPointerException` にする（JPype の `JException`）。"""

    import sys
    import types

    from scripts.function_tracer_pcode.analysis.program_points import program_order_for_high_function

    class FakeJException(Exception):
        pass

    monkeypatch.setitem(sys.modules, "jpype", types.SimpleNamespace(JException=FakeJException))
    high_function, blocks = fake_cfg({0: [1], 1: []})

    def raising(position):
        raise FakeJException("java.lang.NullPointerException")

    blocks[0].getOut = raising
    assert program_order_for_high_function(high_function) is None


# ---------------------------------------------------------------------------
# 入れ子の呼び出し（bounded refinement）: 入れ子の結果も境界を通る
# ---------------------------------------------------------------------------


def test_a_nested_deferred_call_result_is_imported_to_the_caller():
    """caller が f(p) を呼び、f は g(param_1) の値を返し、g は自分の parameter を返す。caller の値は p。

    修正前は f の parameter を先に p へ置き換えてから、f の文脈で g を展開していた。g の結果（f の
    `param_1`）が境界を通らずに caller へ入り、caller の値が f の `param_1` になった（review 5）。
    """

    from scripts.function_tracer_pcode.analysis.bounded_refinement import BoundedCallRefiner
    from scripts.function_tracer_pcode.core import CallTargetRef, DeferredCallInfo, DeferredCallRef, PcodeOpRef, ReturnInfo
    from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis

    def deferred(name, caller_entry, argument):
        target = CallTargetRef.from_name(name)
        return DeferredCallInfo(
            placeholder_name=f"call:{name}#0",
            target_ref=target,
            arguments=[argument],
            deferred_call_ref=DeferredCallRef(
                caller_entry_offset=caller_entry,
                pcode_op_ref=PcodeOpRef(seq_order=1, mnemonic="CALL"),
                target_ref=target,
                sequence=0,
            ),
            sequence=0,
        )

    def placeholder(info):
        return Expression.unknown(info.placeholder_name, runtime_ref=info.unknown_ref)

    int_param = lambda name, index: {"name": name, "index": index, "data_type": "int", "size": 4}
    call_f = deferred("f", 0x1000, Expression.parameter("p", index=0, size=4))
    caller = create_mock_analysis(
        "caller",
        parameters=[int_param("p", 0)],
        returns=[ReturnInfo(address="0x1000", value=placeholder(call_f), conditions=[])],
    )
    caller.entry_point = "0x00001000"
    caller.deferred_calls = {call_f.deferred_call_ref.stable_key(): call_f}

    call_g = deferred("g", 0x2000, Expression.parameter("param_1", index=0, size=4))
    f = create_mock_analysis(
        "f",
        parameters=[int_param("param_1", 0)],
        returns=[ReturnInfo(address="0x2000", value=placeholder(call_g), conditions=[])],
    )
    f.entry_point = "0x00002000"
    f.deferred_calls = {call_g.deferred_call_ref.stable_key(): call_g}
    g = create_mock_analysis(
        "g",
        parameters=[int_param("x", 0)],
        returns=[ReturnInfo(address="0x3000", value=Expression.parameter("x", index=0, size=4), conditions=[])],
    )
    analyses = {"f": f, "g": g}
    refiner = BoundedCallRefiner(
        lambda target_ref, args=None: analyses.get(target_ref.function_name),
        max_unroll=2,
        max_cases=8,
        debug=False,
    )

    refiner.refine_analysis(caller)

    names = {node.name for ret in caller.returns for node in _walk(ret.value) if node.expr_type is ExpressionType.PARAMETER}
    assert "param_1" not in names
    assert names == {"p"}
