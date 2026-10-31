# -*- coding: utf-8 -*-
"""Issue #281: callee の式の memory 読み出しを caller の時間軸へ移す境界（`analysis.effects.call_boundary`）。

callee の読み出しの順序（`read_order_key` / `ObservedMemoryReadRef.order_key`）・location は callee の時間軸・
frame の上にある。caller の consumer はそれを caller の effect と比べるので、そのまま caller へ渡すと、callee が
読んだ後で caller が書いた値に読み出しが化ける（review の例: callee が `*p` を読み、caller が呼び出しの後で
`*p = 2`）。境界は、callee の書き込みが読み出しより前に無いと言えるときだけ、読み出しを caller の呼び出し位置の
読み出しにし、言えなければ `CallBoundaryRefused`（呼び出し側が展開をまるごとやめる）。

ここでの順序の数は caller / callee それぞれの中で比べられる小さな値にしてある（production の読み出しと effect の
順序の単位の違いは別 Issue。境界は effect どうしの順序しか比べない）。
"""

from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.analysis.bounded_refinement import BoundedCallRefiner
from scripts.function_tracer_pcode.analysis.effects.call_boundary import (
    REFUSED_CALL_SITE_ORDER_UNKNOWN,
    REFUSED_CALLEE_EFFECTS_UNKNOWN,
    REFUSED_CALLEE_FRAME_READ,
    REFUSED_CALLEE_STATE_READ,
    REFUSED_CALLEE_WRITE_MAY_PRECEDE_READ,
    CallBoundaryRefused,
    CallSite,
    CalleeTimeline,
    import_callee_condition,
    import_callee_expression,
    read_order_key_for_op,
)
from scripts.function_tracer_pcode.analysis.effects.location import substitute_expression
from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary, StoreEffect
from scripts.function_tracer_pcode.analysis.effects.post_state import rewrite_observed_loads_from_effects
from scripts.function_tracer_pcode.analysis.returns import call_recovery
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateSnapshotRef,
)
from scripts.function_tracer_pcode.core.analysis import DeferredCallInfo, ReturnInfo
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.operand_derivation import OperandDerivationRefused
from scripts.function_tracer_pcode.core.runtime_refs import DeferredCallRef, PcodeOpRef
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis

CALLEE_PARAMETERS = [{"name": "param_1", "index": 0, "data_type": "int *", "size": 8}]
CALLER_PARAMETERS = [{"name": "p", "index": 0, "data_type": "int *", "size": 8}]


def _callee_pointer() -> Expression:
    return Expression.parameter("param_1", index=0, data_type="int *", size=8)


def _caller_pointer() -> Expression:
    return Expression.parameter("p", index=0, data_type="int *", size=8)


def _callee_read(order=10, *, location=None) -> Expression:
    """callee の op（順序 `order`）が `*param_1` を読んだ値。"""

    return Expression.memory(
        _callee_pointer(),
        4,
        read_order_key=order,
        runtime_ref=ObservedMemoryReadRef(order_key=order, location=location),
    )


def _caller_store(value: int, order: int) -> StoreEffect:
    return StoreEffect(
        location=CanonicalLocation(base_ref=LocationBaseRef.parameter("p", index=0), offset=0, size=4),
        value=Expression.constant(value, size=4),
        conditions=[],
        order_key=order,
    )


def _callee_effect(order: int, value: Expression = None) -> StoreEffect:
    return StoreEffect(
        location=CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=4, size=4),
        value=value if value is not None else Expression.constant(1, size=4),
        conditions=[],
        order_key=order,
    )


def _timeline(*effects: StoreEffect, **summary_fields) -> CalleeTimeline:
    summary = EffectSummary(parameter_names=["param_1"], effects=list(effects), **summary_fields)
    return CalleeTimeline.from_effect_summary(summary, CALLEE_PARAMETERS)


def _to_caller(expr: Expression, site: CallSite, timeline: CalleeTimeline) -> Expression:
    imported = import_callee_expression(expr, site, timeline)
    return substitute_expression(imported, {("parameter", 0): _caller_pointer()}, CALLEE_PARAMETERS)


# ---------------------------------------------------------------------------
# review の例: 呼び出しの後の caller の書き込みを、callee の読み出しに適用しない
# ---------------------------------------------------------------------------


def test_without_the_boundary_a_callee_read_takes_a_caller_store_made_after_the_call():
    """修正前の経路（置き換えだけ）: callee の順序 10 を caller の effect（呼び出し 3 の後の順序 5）と比べ、2 に化ける。"""

    substituted = substitute_expression(_callee_read(), {("parameter", 0): _caller_pointer()}, CALLEE_PARAMETERS)
    assert substituted.read_order_key == 10
    rewritten = rewrite_observed_loads_from_effects(substituted, [], [_caller_store(2, order=5)], CALLER_PARAMETERS)
    assert rewritten.expr_type is ExpressionType.CONSTANT and rewritten.value == 2


def test_a_callee_read_becomes_a_read_at_the_call_site():
    """境界の後: 読み出しは caller の呼び出し位置（順序 3）の読み出しで、呼び出しの後の書き込み（5）は見ず、前（1）は見る。"""

    moved = _to_caller(_callee_read(), CallSite(3), _timeline())
    assert moved.read_order_key == 3
    assert moved.runtime_ref.order_key == 3
    assert moved.runtime_ref.location is None

    after_only = rewrite_observed_loads_from_effects(moved, [], [_caller_store(2, order=5)], CALLER_PARAMETERS)
    assert after_only.expr_type is ExpressionType.MEMORY

    before_and_after = rewrite_observed_loads_from_effects(
        moved,
        [],
        [_caller_store(7, order=1), _caller_store(2, order=5)],
        CALLER_PARAMETERS,
    )
    assert before_and_after.expr_type is ExpressionType.CONSTANT and before_and_after.value == 7


def test_a_callee_location_is_dropped_so_substitution_does_not_refuse_it():
    """callee の parameter を基底にした location は落とす（番地は caller の parameter で計算し直される）。"""

    location = CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=0, size=4)
    moved = _to_caller(_callee_read(location=location), CallSite(3), _timeline())
    assert moved.runtime_ref.location is None
    assert moved.operands[0].name == "p"


def test_an_untimed_return_read_is_pinned_to_the_call_site():
    """順序の無い読み出し（戻り値の文脈では callee の出口の状態）も、callee が書かなければ呼び出し位置の読み出し。"""

    untimed = Expression.memory(_callee_pointer(), 4)
    moved = _to_caller(untimed, CallSite(3), _timeline())
    assert moved.read_order_key == 3
    assert isinstance(moved.runtime_ref, ObservedMemoryReadRef)


# ---------------------------------------------------------------------------
# 移せない読み出し: 拒否（呼び出し側が展開をまるごとやめる）
# ---------------------------------------------------------------------------


def test_a_callee_write_before_the_read_is_refused():
    """callee が書いた後の読み出しは、caller の呼び出し位置の memory ではない。"""

    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(_callee_read(), CallSite(3), _timeline(_callee_effect(order=1)))
    assert refused.value.reason == REFUSED_CALLEE_WRITE_MAY_PRECEDE_READ


@pytest.mark.parametrize(
    "summary_fields",
    [
        {"has_unsupported_call": True},
        {"incomplete_reasons": ("effect_summary_path_coverage_incomplete",)},
    ],
)
def test_unknown_callee_writes_are_refused(summary_fields):
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(_callee_read(), CallSite(3), _timeline(**summary_fields))
    assert refused.value.reason == REFUSED_CALLEE_EFFECTS_UNKNOWN


def test_a_missing_effect_summary_is_refused():
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(_callee_read(), CallSite(3), CalleeTimeline.from_effect_summary(None))
    assert refused.value.reason == REFUSED_CALLEE_EFFECTS_UNKNOWN


@pytest.mark.parametrize(
    "ref",
    [
        PostStateReadRef(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=0, size=4)
        ),
        ObservedMemoryReadRef(order_key=10, snapshot_ref=PostStateSnapshotRef.function_return()),
    ],
    ids=["post-state-read", "observed-with-snapshot"],
)
def test_a_post_write_state_read_is_refused(ref):
    expr = Expression.memory(_callee_pointer(), 4, runtime_ref=ref)
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(expr, CallSite(3), _timeline())
    assert refused.value.reason == REFUSED_CALLEE_STATE_READ


def test_an_unknown_call_site_is_refused():
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(_callee_read(), CallSite(None), _timeline())
    assert refused.value.reason == REFUSED_CALL_SITE_ORDER_UNKNOWN


def test_a_read_of_the_callee_frame_is_refused():
    stack_pointer = Expression.variable("sp", size=8).clone_with(
        storage_info=StorageInfo(is_register=True, register_name="sp", size=8, is_stack_pointer=True),
    )
    frame_read = Expression.memory(stack_pointer, 4, read_order_key=10, runtime_ref=ObservedMemoryReadRef(order_key=10))
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(frame_read, CallSite(3), _timeline())
    assert refused.value.reason == REFUSED_CALLEE_FRAME_READ


def test_the_refusal_is_an_operand_derivation_refusal_so_every_boundary_catches_it():
    assert issubclass(CallBoundaryRefused, OperandDerivationRefused)


# ---------------------------------------------------------------------------
# effect の値の文脈: その effect より前の書き込みだけを見る
# ---------------------------------------------------------------------------


def test_an_effect_value_read_before_any_callee_write_is_kept_untimed():
    """effect の値の順序なしの読み出しは、その effect の前の状態（caller へ入る effect の順序は呼び出し位置）。"""

    value_read = Expression.memory(_callee_pointer(), 4)
    later_effect = _callee_effect(order=30)
    imported = import_callee_expression(value_read, CallSite(3), _timeline(later_effect), context_order=20)
    assert imported is value_read


def test_an_effect_value_read_after_an_earlier_callee_write_is_refused():
    value_read = Expression.memory(_callee_pointer(), 4)
    with pytest.raises(CallBoundaryRefused):
        import_callee_expression(value_read, CallSite(3), _timeline(_callee_effect(order=10)), context_order=20)


def test_an_effect_with_an_unknown_order_may_precede_any_read():
    value_read = Expression.memory(_callee_pointer(), 4)
    with pytest.raises(CallBoundaryRefused):
        import_callee_expression(value_read, CallSite(3), _timeline(_callee_effect(order=-1)), context_order=20)


# ---------------------------------------------------------------------------
# 置き換えが空の経路・memory を読まない式
# ---------------------------------------------------------------------------


def test_an_expression_without_memory_reads_is_returned_unchanged():
    expr = Expression.binary_op("INT_ADD", _callee_pointer(), Expression.constant(1, size=8))
    assert import_callee_expression(expr, CallSite(None), CalleeTimeline.unknown()) is expr


def test_conditions_are_imported_too():
    condition = Condition(Expression.binary_op("INT_EQUAL", _callee_read(), Expression.constant(0, size=4)), False)
    imported = import_callee_condition(condition, CallSite(3), _timeline())
    assert imported.expression.operands[0].read_order_key == 3


def _analysis_with(value: Expression, *effects: StoreEffect):
    analysis = create_mock_analysis(
        "callee",
        parameters=list(CALLEE_PARAMETERS),
        returns=[ReturnInfo(address="0x1000", value=value, conditions=[])],
    )
    analysis.effect_summary = EffectSummary(parameter_names=["param_1"], effects=list(effects))
    return analysis


def _specializer():
    return SimpleNamespace(_rewrite_deferred_runtime_refs_in_expression=lambda expr, mapping: expr)


def test_an_already_specialized_callee_is_moved_to_the_call_site_without_substitution():
    """引数で特殊化済み（置き換えが空・operand が変わらない）の callee も、読み出しの順序は caller の呼び出し位置にする。"""

    analysis = _analysis_with(_callee_read())
    specialized = call_recovery._impl__specialize_call_analysis(
        _specializer(),
        analysis,
        [],
        CallSite(3),
        substitute_parameters=False,
    )
    value = specialized.returns[0].value
    assert value.read_order_key == 3
    assert value.operands[0].name == "param_1"


def test_an_already_specialized_callee_that_writes_before_the_read_is_refused():
    analysis = _analysis_with(_callee_read(), _callee_effect(order=1))
    with pytest.raises(CallBoundaryRefused):
        call_recovery._impl__specialize_call_analysis(
            _specializer(), analysis, [], CallSite(3), substitute_parameters=False
        )


def test_the_call_expansion_is_abandoned_when_the_boundary_refuses():
    """call_recovery の展開: 境界が拒否したら None（callee の元の式を caller へ渡さない）。"""

    analysis = _analysis_with(_callee_read(), _callee_effect(order=1))
    target_ref = SimpleNamespace(is_code_address=lambda: False, address_offset=None, display_name=lambda: "callee")
    messages = []
    owner = SimpleNamespace(
        _coerce_runtime_target_ref=lambda target: target_ref,
        _target_active_key=lambda ref: None,
        _invoke_get_or_analyze_call_target=lambda *a, **k: analysis,
        _analysis_is_fully_argument_specialized=lambda a: True,
        _debug_print=messages.append,
    )
    owner._specialize_call_analysis = lambda *a, **k: call_recovery._impl__specialize_call_analysis(
        _specializer(), *a, **k
    )
    result = call_recovery._impl__resolve_call_expansions(owner, "callee", [], set(), call_site=CallSite(3))
    assert result is None
    assert any(REFUSED_CALLEE_WRITE_MAY_PRECEDE_READ in message for message in messages)


# ---------------------------------------------------------------------------
# 呼び出し位置
# ---------------------------------------------------------------------------


def test_the_call_site_order_uses_the_same_rule_as_the_tracer_read_order():
    seqnum = SimpleNamespace(getOrder=lambda: 4)
    op = SimpleNamespace(getSeqnum=lambda: seqnum)
    assert read_order_key_for_op(op) == 4
    assert CallSite.for_op(op).read_order_key == 4


def _deferred_ref(caller_entry_offset, seq_order=4):
    return DeferredCallRef(
        caller_entry_offset=caller_entry_offset,
        pcode_op_ref=PcodeOpRef(seq_order=seq_order),
        target_ref=CallTargetRef.from_name("callee"),
        sequence=0,
    )


def test_a_deferred_call_of_the_caller_itself_has_a_known_site():
    assert CallSite.for_deferred_call(_deferred_ref(0x4000), 0x4000).read_order_key == 4


@pytest.mark.parametrize("caller_entry", [0x5000, None], ids=["merged-from-a-callee", "caller-entry-unknown"])
def test_a_deferred_call_merged_from_a_callee_has_an_unknown_site(caller_entry):
    """callee の展開から合流した deferred call の op は callee のもの: caller の時間軸での位置は分からない。"""

    assert CallSite.for_deferred_call(_deferred_ref(0x4000), caller_entry).read_order_key is None


def test_bounded_refinement_abandons_the_whole_expansion_when_one_candidate_cannot_be_moved():
    """bounded refinement: 2 つの target のうち 1 つの読み出しを移せなければ、呼び出しの展開をまるごとやめる。"""

    reader = _analysis_with(_callee_read())
    writer = _analysis_with(_callee_read(), _callee_effect(order=1))
    candidates = {"reader": reader, "writer": writer}
    deferred = DeferredCallInfo(
        placeholder_name="call",
        target_ref=CallTargetRef.from_name("reader"),
        arguments=[_caller_pointer()],
        deferred_call_ref=_deferred_ref(None),
    )
    caller = create_mock_analysis("caller", parameters=list(CALLER_PARAMETERS))
    refiner = BoundedCallRefiner(lambda target_ref: None, max_unroll=1, max_cases=16, debug=False)
    refiner._resolve_deferred_call_candidates = lambda info: [
        (CallTargetRef.from_name(name), [], analysis) for name, analysis in candidates.items()
    ]
    assert refiner._expand_deferred_call(deferred, caller, 1, set()) == []
    assert any("callee_write_may_precede_read" in note or "call_site_order_unknown" in note for note in caller.analysis_notes)


# ---------------------------------------------------------------------------
# effect の置き換え（summarize_store_effects）: 同じ呼び出しの effect の一部だけが拒否されたとき
# ---------------------------------------------------------------------------


def _summarize_call_with_callee_effects(callee_effects):
    """1 つの CALL（callee の parameter `slot` に caller の `slot` を渡す）だけの block の effect 要約。"""

    from scripts.function_tracer_pcode.analysis.effects.summary import summarize_store_effects
    from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import _param, _reg_storage

    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [FakeVarnode("target", 8), FakeVarnode("slot", 8)]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getSeqnum(self):
            return None

    class FakeBlockInfo:
        pcode_ops = [FakeCallOp()]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("callee")

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "slot":
                return Expression.parameter("slot", 0, size=8)
            return Expression.constant(0, max(1, varnode.getSize()))

    slot = _param("slot", size=8, index=0, storage=_reg_storage("x0", register_name="x0"))
    return summarize_store_effects(
        [FakeBlockInfo()],
        FakeTracer(),
        FakeConditionTracker(),
        [slot],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["slot"],
            parameter_refs=[LocationBaseRef.parameter("slot", index=0)],
            effects=list(callee_effects),
        ),
        resolve_callee_parameters=lambda _target_ref: [slot],
        debug=False,
    )


def _slot_location(offset: int) -> CanonicalLocation:
    return CanonicalLocation(base_ref=LocationBaseRef.parameter("slot", index=0), offset=offset, size=4)


def _slot_read() -> Expression:
    return Expression.memory(Expression.parameter("slot", 0, size=8), 4)


def test_a_refused_callee_effect_marks_the_call_unsupported_which_blocks_both_verdicts():
    """2 つ目の effect の値は 1 つ目の書き込みの後の読み出しで、caller の言葉で表せない（拒否）。

    呼び出しは「effect の分からない呼び出し」になる。先に入った 1 つ目の effect は要約に残るが、要約が
    `has_unsupported_call` なので、EQ（`get_equivalence_blocking_unsafety_reasons`）も NOT_EQ の反例
    （`get_decisive_sat_unsafety_reasons`）も止まる。
    """

    summary = _summarize_call_with_callee_effects(
        [
            StoreEffect(location=_slot_location(0), value=Expression.constant(5, size=4), conditions=[], order_key=1),
            StoreEffect(location=_slot_location(4), value=_slot_read(), conditions=[], order_key=2),
        ]
    )
    assert summary.has_unsupported_call is True
    assert [site.reason for site in summary.unsupported_call_sites] == ["substituted_effect_read_not_relocatable"]

    analysis = create_mock_analysis("caller")
    analysis.effect_summary = summary
    assert "unsupported_call_effect_summary" in analysis.get_equivalence_blocking_unsafety_reasons()
    assert "unsupported_call_effect_summary" in analysis.get_decisive_sat_unsafety_reasons()


def test_a_callee_effect_value_read_before_every_callee_write_is_imported():
    """読み出しが callee のどの書き込みより前なら、両方の effect が caller へ入り、呼び出しは分かる呼び出しのまま。"""

    summary = _summarize_call_with_callee_effects(
        [
            StoreEffect(location=_slot_location(4), value=_slot_read(), conditions=[], order_key=1),
            StoreEffect(location=_slot_location(0), value=Expression.constant(5, size=4), conditions=[], order_key=2),
        ]
    )
    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 2
