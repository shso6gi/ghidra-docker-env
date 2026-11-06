"""Issue #282 PR-282-A: 左右の memory を根拠なく同一視しない・同じ側の中の store との関係を証明できない読み出しを
入口の値で描かない（設計 v3 の負例 N* と正例 P*）。

* 描画（I1 / I2 / I4）: pre-state の memory・image の object の番地・出口の状態の値は側ごとの記号。側の無い写像では
  描かない。読み出しの幅は狭めない。
* 観測（I9）: store の比較面は番地を量化した 1 byte の観測（書き込みの順・alias・部分重なりを構成から扱う）。
* 読み出し（I3）: 先行し得る store と重ならないと証明できない入口の memory の読み出しは EQ と NOT_EQ を止める。
* frame（I11 / AC 9）: entry SP より下の store を局所としない（確保された frame の範囲も、入口の pointer・global の
  番地との alias も示せない）。そうした store は `effect_store_location_unmodeled` で EQ と NOT_EQ を止め、frame と
  parameter・global の関係は `UNKNOWN`。frame の位置どうしの関係（定数の範囲）は決める。
* 具体化（Q1 / I7）: image の値は init・read-only・block の中・再配置の条件を満たすときだけ。
* 出自（不変条件 3）: image の番地の定数は畳み込まない。
* SAT（I6）: 側ごとの状態に依存する反例は `memory_state_unrealized`（replay で解除されない）。
* 構造の同一視・oracle（I1）: gate と左右をまたぐ oracle は側ごとの状態を拒否する。
* P12（I12）: 同一 binary の EQ は方針表が認めた前提だけを使い、前提を記録する。

SMT の結果は z3 の Python API で解く（production の builder が作った query をそのまま渡す）。
"""

from __future__ import annotations

import pytest
import z3

from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import _param
from scripts.function_tracer_pcode.tests.unit._publication import published

from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.core.memory_relation import MemoryRelation
from scripts.function_tracer_pcode.core.runtime_refs import (
    AddressValueRef,
    CanonicalLocation,
    LocationBaseRef,
    PostStateReadRef,
    PostStateSnapshotRef,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary, StoreEffect
from scripts.function_tracer_pcode.analysis.effects.location_relation import frame_local_range, location_relation
from scripts.function_tracer_pcode.analysis.effects.summary import build_void_effect_summary_expr
from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.proof.formula.input_correspondence import build_input_correspondence_set

P = LocationBaseRef.parameter("p", index=0)
Q = LocationBaseRef.parameter("q", index=1)
PARAMS = [_param("p", size=8, index=0), _param("q", size=8, index=1)]


def _p(name="p", index=0):
    return Expression.parameter(name, index, size=8)


def _mem(addr, size=4):
    return Expression.memory(addr, size=size)


def _store(base, offset, size, value, order, conditions=()):
    return StoreEffect(
        location=CanonicalLocation(base_ref=base, offset=offset, size=size, steps=()),
        value=value if isinstance(value, Expression) else Expression.constant(value, size),
        conditions=list(conditions),
        order_key=order,
    )


def _analysis(name, value, *, params=PARAMS, conditions=(), effects=(), return_type="int"):
    analysis = FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x0",
        parameters=list(params),
        returns=[ReturnInfo(address="0x1", conditions=list(conditions), value=value)],
        return_type=return_type,
    )
    if effects:
        analysis.effect_summary = EffectSummary(parameter_names=[p["name"] for p in params], effects=list(effects))
    return analysis


def _formula(left, right):
    left, right = published(left), published(right)
    return FormulaBuilder(debug=False, exclude_ub=False).build_equivalence_formula_extended(
        left, right, input_correspondence=build_input_correspondence_set(left, right)
    ).formula


def _check(formula):
    solver = z3.Solver()
    solver.set("timeout", 30000)
    solver.from_string(formula.replace("(check-sat)", "").replace("(get-model)", ""))
    return solver.check()


def _surface_analysis(name, effects):
    surface = build_void_effect_summary_expr(effects, PARAMS, big_endian=False)
    assert surface is not None
    return _analysis(name, surface, return_type="void")


def _image_constant(value, *, writable=False, symbol=None, size=8):
    ref = AddressValueRef(
        address_offset=value,
        source="constant_offset",
        block_name=".rodata" if not writable else ".data",
        is_initialized=True,
        can_read=True,
        can_write=writable,
        is_volatile=False,
        object_symbol_name=symbol,
        object_base_offset=value if symbol else None,
        object_size=8 if symbol else None,
    )
    return Expression.constant(value, size, runtime_ref=ref)


# ---------------------------------------------------------------------------
# 描画: 側ごとの memory（N1 / N2 / N4 / N19）
# ---------------------------------------------------------------------------


def test_n2_pointer_read_on_both_sides_is_not_equivalent_with_per_side_memory():
    """`f(p) = *p` を左右で比べる。p が各側の image の中を指せば中身は違い得る（共有の配列は EQ にしていた）。"""

    formula = _formula(_analysis("f", _mem(_p())), _analysis("g", _mem(_p())))
    assert "(declare-const mem32_s1 " in formula and "(declare-const mem32_s2 " in formula
    assert "(select mem32_s1 p_1)" in formula and "(select mem32_s2 p_2)" in formula
    assert _check(formula) == z3.sat


def test_n1_bessi0_shape_guard_reading_the_same_image_address_is_per_side():
    """閾値を同じ番地の image の定数から読む guard（bessi0）。左右の閾値は別の記号。"""

    threshold = lambda: _mem(_image_constant(0x100160), size=8)  # noqa: E731
    x = Expression.parameter("x", 0, size=8)
    guard = lambda: Condition(Expression.binary_op("INT_LESS", x, threshold()))  # noqa: E731
    params = [_param("x", size=8, index=0)]
    left = FunctionReturnAnalysis(
        function_name="f", entry_point="0x0", parameters=params, return_type="long",
        returns=[
            ReturnInfo(address="0x1", conditions=[guard()], value=Expression.constant(1, 8)),
            ReturnInfo(address="0x2", conditions=[guard().negate()], value=Expression.constant(2, 8)),
        ],
    )
    right = FunctionReturnAnalysis(
        function_name="g", entry_point="0x0", parameters=params, return_type="long",
        returns=[
            ReturnInfo(address="0x1", conditions=[guard()], value=Expression.constant(1, 8)),
            ReturnInfo(address="0x2", conditions=[guard().negate()], value=Expression.constant(2, 8)),
        ],
    )
    formula = _formula(left, right)
    assert "imgbase_s1" in formula and "imgbase_s2" in formula
    assert _check(formula) == z3.sat


def test_n19_wide_reads_keep_their_width_and_unknown_width_is_refused():
    from scripts.function_tracer_pcode.core.render_smt.render import UnsupportedSmtSemanticsError

    formula = _formula(_analysis("f", _mem(_p(), size=16)), _analysis("g", _mem(_p(), size=16)))
    assert "(select mem128_s1 p_1)" in formula
    unknown = Expression.memory(_p(), size=0)
    with pytest.raises(UnsupportedSmtSemanticsError):
        published(unknown).to_smt(symbol_name_mapping={"p": "p_1", "\x00smt_side": "s1"})


def test_memory_under_a_mapping_without_a_side_is_refused():
    from scripts.function_tracer_pcode.core.render_smt.render import UndeclaredSmtSymbolError

    with pytest.raises(UndeclaredSmtSymbolError):
        published(_mem(_p())).to_smt(symbol_name_mapping={"p": "p_1"})


def test_n3_named_global_addresses_are_per_side_symbols():
    left = _mem(_image_constant(0x101000, writable=True, symbol="g"))
    right = _mem(_image_constant(0x101000, writable=True, symbol="g"))
    formula = _formula(_analysis("f", left), _analysis("g", right))
    assert "_s1" in formula and "gaddr_g_8_" in formula
    assert _check(formula) == z3.sat


def test_n25_post_state_values_with_the_same_name_are_per_side_symbols():
    """出口の状態の値（自前で宣言する記号）は名前が左右で同じでも別の記号（以前は 1 つの記号だった）。"""

    def post_state():
        location = CanonicalLocation(base_ref=P, offset=0, size=4)
        ref = PostStateReadRef(location=location, snapshot_ref=PostStateSnapshotRef.function_return())
        return Expression.variable("poststate_0_4", size=4, runtime_ref=ref)

    from scripts.function_tracer_pcode.core.render_smt.unknowns import side_state_symbol_name

    formula = _formula(_analysis("f", post_state()), _analysis("g", post_state()))
    symbol = side_state_symbol_name(published(post_state()))
    assert f"{symbol}_s1" in formula and f"{symbol}_s2" in formula
    assert "poststate_0_4" not in formula
    assert _check(formula) == z3.sat


def test_248_post_state_symbols_of_distinct_locations_differ_on_one_side():
    """#248: `poststate_{abs(offset)}_{size}` は p+8 と p-8 を同じ記号にしていた。"""

    from scripts.function_tracer_pcode.core.render_smt.unknowns import side_state_symbol_name

    def post_state(offset):
        location = CanonicalLocation(base_ref=P, offset=offset, size=4)
        ref = PostStateReadRef(location=location, snapshot_ref=PostStateSnapshotRef.function_return())
        return published(Expression.variable("poststate_8_4", size=4, runtime_ref=ref))

    assert side_state_symbol_name(post_state(8)) != side_state_symbol_name(post_state(-8))
    assert side_state_symbol_name(post_state(8)) == side_state_symbol_name(post_state(8))
    on_q = PostStateReadRef(
        location=CanonicalLocation(base_ref=Q, offset=8, size=4), snapshot_ref=PostStateSnapshotRef.function_return()
    )
    base_only = published(Expression.variable("poststate_8_4", size=4, runtime_ref=on_q))
    assert side_state_symbol_name(base_only) != side_state_symbol_name(post_state(8))


def test_p1_parameter_only_functions_stay_equivalent():
    x = lambda: Expression.binary_op("INT_ADD", _p(), Expression.constant(1, 8))  # noqa: E731
    assert _check(_formula(_analysis("f", x()), _analysis("g", x()))) == z3.unsat


# ---------------------------------------------------------------------------
# 観測（N26 / N27 / N16 / P13 / P14）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "left, right",
    [
        pytest.param([_store(P, 0, 4, 1, 1), _store(Q, 0, 4, 2, 2)], [_store(Q, 0, 4, 2, 1), _store(P, 0, 4, 1, 2)], id="n26-order-alias"),
        pytest.param(
            [_store(P, 0, 4, 0x01020304, 1), _store(P, 1, 1, 9, 2)],
            [_store(P, 1, 1, 9, 1), _store(P, 0, 4, 0x01020304, 2)],
            id="n27-partial-overlap",
        ),
        pytest.param([_store(P, 0, 4, 5, 1)], [_store(P, 8, 4, 5, 1)], id="n16-offsets"),
    ],
)
def test_store_order_alias_and_offsets_are_not_equivalent(left, right):
    assert _check(_formula(_surface_analysis("f", left), _surface_analysis("g", right))) == z3.sat


@pytest.mark.parametrize(
    "left, right",
    [
        pytest.param([_store(P, 0, 4, 1, 1), _store(Q, 0, 4, 2, 2)], [_store(P, 0, 4, 1, 1), _store(Q, 0, 4, 2, 2)], id="p13-same-order"),
        pytest.param(
            [_store(P, 0, 8, Expression.binary_op("INT_ADD", _p(), _p("q", 1)), 1)],
            [_store(P, 0, 8, Expression.binary_op("INT_ADD", _p("q", 1), _p()), 1)],
            id="p14-commuted-value",
        ),
        pytest.param([_store(P, 0, 4, 0x01020304, 1)], [_store(P, 0, 2, 0x0304, 1), _store(P, 2, 2, 0x0102, 2)], id="split-store"),
    ],
)
def test_same_final_memory_stays_equivalent(left, right):
    assert _check(_formula(_surface_analysis("f", left), _surface_analysis("g", right))) == z3.unsat


def test_global_object_store_is_not_composed_into_the_surface():
    effect = StoreEffect(
        location=CanonicalLocation(base_ref=LocationBaseRef.global_object("g", 4), offset=0, size=4),
        value=Expression.constant(1, 4), conditions=[], order_key=1,
    )
    assert build_void_effect_summary_expr([effect], PARAMS, big_endian=False) is None


def test_surface_needs_the_byte_order():
    assert build_void_effect_summary_expr([_store(P, 0, 4, 1, 1)], PARAMS, big_endian=None) is None


# ---------------------------------------------------------------------------
# 同じ側の中の関係（N28 / N29 / P15）
# ---------------------------------------------------------------------------


def test_location_relation_proves_only_disjoint_or_same():
    loc = lambda base, off, size: CanonicalLocation(base_ref=base, offset=off, size=size)  # noqa: E731
    assert location_relation(loc(P, 0, 4), loc(P, 4, 4)) is MemoryRelation.DISJOINT
    assert location_relation(loc(P, 0, 4), loc(P, 0, 4)) is MemoryRelation.SAME
    assert location_relation(loc(P, 0, 4), loc(P, 1, 1)) is MemoryRelation.OVERLAP
    assert location_relation(loc(P, 0, 4), loc(Q, 0, 4)) is MemoryRelation.UNKNOWN
    # offset は 64 bit の剰余（`p + 0xffff…fe` は `p - 2`）。符号なしのまま比べると重なりを見落とす
    assert location_relation(loc(P, (1 << 64) - 2, 4), loc(P, 0, 4)) is MemoryRelation.OVERLAP
    assert location_relation(None, loc(Q, 0, 4)) is MemoryRelation.UNKNOWN



def test_frame_locations_are_related_to_outside_locations_only_as_unknown():
    """負例: frame の slot と、入口の pointer・global を起点とする位置は、条件に比較が無くても DISJOINT にしない（AC 9）。

    修正前は D-S（と、frame の番地が外へ出ない証拠）だけで DISJOINT にしていた。"""

    loc = lambda base, off, size: CanonicalLocation(base_ref=base, offset=off, size=size)  # noqa: E731
    frame = LocationBaseRef.stack_frame()
    image = LocationBaseRef.global_object("table", 8, space_name="ram")
    for outside in (loc(P, 0, 8), loc(image, 0, 8)):
        assert location_relation(loc(frame, -16, 8), outside) is MemoryRelation.UNKNOWN
        assert location_relation(outside, loc(frame, -0x100000, 8)) is MemoryRelation.UNKNOWN
    assert location_relation(loc(frame, 8, 8), loc(P, 0, 8)) is MemoryRelation.UNKNOWN


def test_frame_locations_are_related_to_each_other_by_their_constant_ranges():
    """正例: 同じ frame の slot どうしは同じ基底なので、定数の範囲で SAME / DISJOINT / OVERLAP を決める。"""

    loc = lambda off, size: CanonicalLocation(base_ref=LocationBaseRef.stack_frame(), offset=off, size=size)  # noqa: E731
    assert location_relation(loc(-16, 8), loc(-16, 8)) is MemoryRelation.SAME
    assert location_relation(loc(-16, 8), loc(-32, 8)) is MemoryRelation.DISJOINT
    assert location_relation(loc(-16, 8), loc(-12, 4)) is MemoryRelation.OVERLAP


def test_n28_read_after_a_may_alias_store_blocks_both_verdicts():
    """左 `x = *r; *p = 0; y = *r` の y（store の後の読み出し）を入口の値で描くと store を無視する。"""

    r = Expression.parameter("q", 1, size=8)
    read = Expression.memory(r, size=4)
    read.read_order_key = 10
    analysis = _analysis("f", read, effects=[_store(P, 0, 4, 0, 5)])
    assert analysis.has_unresolved_memory_read_aliases()
    assert "memory_read_alias_unresolved" in analysis.get_equivalence_blocking_unsafety_reasons()
    assert "memory_read_alias_unresolved" in analysis.get_decisive_sat_unsafety_reasons()


def test_n29_read_after_a_wider_overlapping_store_blocks():
    read = Expression.memory(Expression.binary_op("INT_ADD", _p(), Expression.constant(1, 8)), size=1)
    read.read_order_key = 10
    analysis = _analysis("f", read, effects=[_store(P, 0, 4, 7, 5)])
    assert analysis.has_unresolved_memory_read_aliases()


def test_p15_reads_disjoint_from_or_before_every_store_pass():
    disjoint = Expression.memory(Expression.binary_op("INT_ADD", _p(), Expression.constant(8, 8)), size=4)
    disjoint.read_order_key = 10
    assert not _analysis("f", disjoint, effects=[_store(P, 0, 4, 7, 5)]).has_unresolved_memory_read_aliases()
    before = Expression.memory(_p("q", 1), size=4)
    before.read_order_key = 3
    assert not _analysis("f", before, effects=[_store(P, 0, 4, 7, 5)]).has_unresolved_memory_read_aliases()


def _read_of_q(order):
    read = Expression.memory(_p("q", 1), size=4)
    read.read_order_key = order
    return read


def _contradiction():
    return Condition(Expression.binary_op("INT_EQUAL", Expression.constant(0, 8), Expression.constant(1, 8)))


def _move_store_before_the_read(analysis):
    analysis.effect_summary.effects[0].order_key = 5


def _replace_store_location(analysis):
    analysis.effect_summary.effects[0].location = CanonicalLocation(base_ref=Q, offset=0, size=4, steps=())


def _drop_contradicting_store_guard(analysis):
    analysis.effect_summary.effects[0].conditions.clear()


def _drop_contradicting_path_condition(analysis):
    analysis.returns[0].conditions.clear()


@pytest.mark.parametrize(
    "build, change",
    [
        # 検査の後に store の順序が読み出しより前へ動く（20 → 5）
        pytest.param(lambda: dict(effects=[_store(P, 0, 4, 7, 20)]), _move_store_before_the_read, id="order_key"),
        # 位置が読み出しと重ならない `q + 8` から読み出しと同じ `q` に変わる
        pytest.param(lambda: dict(effects=[_store(Q, 8, 4, 7, 5)]), _replace_store_location, id="location"),
        # store の条件の list を同じ object のまま書き換える（矛盾する条件を外す）
        pytest.param(
            lambda: dict(effects=[_store(P, 0, 4, 7, 5, conditions=[_contradiction()])]),
            _drop_contradicting_store_guard,
            id="store_conditions",
        ),
        # 戻り値の経路の条件の list を同じ object のまま書き換える
        pytest.param(
            lambda: dict(effects=[_store(P, 0, 4, 7, 5)], conditions=[_contradiction()]),
            _drop_contradicting_path_condition,
            id="path_conditions",
        ),
    ],
)
def test_alias_check_follows_inputs_changed_after_an_earlier_check(build, change):
    """検査の結果を、検査が読んだ入力が変わった後に使い回さない（PR #289 review: 以前の memo は object の identity
    だけを比べ、同じ `StoreEffect` の `order_key` を 20 → 5 に変えても、検出なしの結果を返していた）。"""

    from scripts.function_tracer_pcode.analysis.effects.read_validation import _unresolved_memory_read_aliases

    analysis = _analysis("f", _read_of_q(10), **build())
    assert not analysis.has_unresolved_memory_read_aliases()
    change(analysis)
    assert _unresolved_memory_read_aliases(analysis), "the changed input must have a finding when checked afresh"
    assert analysis.has_unresolved_memory_read_aliases()
    assert "memory_read_alias_unresolved" in analysis.get_equivalence_blocking_unsafety_reasons()
    assert "memory_read_alias_unresolved" in analysis.get_decisive_sat_unsafety_reasons()


def test_alias_check_of_unchanged_inputs_gives_the_same_answer():
    """入力が変わらなければ、何度検査しても同じ答え（検出なし・検出ありの両方）。"""

    clean = _analysis("f", _read_of_q(10), effects=[_store(P, 0, 4, 7, 20)])
    flagged = _analysis("f", _read_of_q(10), effects=[_store(P, 0, 4, 7, 5)])
    for _ in range(3):
        assert not clean.has_unresolved_memory_read_aliases()
        assert flagged.has_unresolved_memory_read_aliases()


def test_fallback_branch_under_the_negated_store_guard_passes():
    """`if (c) *p = 1; return *p;` の lowering（c なら 1、そうでなければ入口の値）は検査に通る。"""

    c = Condition(Expression.binary_op("INT_EQUAL", _p("q", 1), Expression.constant(0, 8)))
    fallback = Expression.memory(_p(), size=4)
    value = Expression.phi([(c, Expression.constant(1, 4)), (None, fallback)])
    value.size = 4
    analysis = _analysis("f", value, effects=[_store(P, 0, 4, 1, 5, conditions=[c])])
    assert not analysis.has_unresolved_memory_read_aliases()


# ---------------------------------------------------------------------------
# frame（N30 / N31 / N32 / P16）
# ---------------------------------------------------------------------------


def _register(name, *, sp=False, fp=False):
    storage = StorageInfo(is_register=True, register_name=name, base_register_name=name, size=8, size_bits=64)
    storage.is_stack_pointer = sp
    storage.is_frame_pointer = fp
    return Expression.variable(name, size=8, storage_info=storage)


def _plus(base, offset):
    return Expression.binary_op("INT_ADD", base, Expression.constant(offset & 0xFFFFFFFFFFFFFFFF, 8))


def test_frame_local_range_is_below_entry_sp_only():
    frame = LocationBaseRef.stack_frame()
    assert frame_local_range(CanonicalLocation(base_ref=frame, offset=-16, size=8)) == (-16, -8)
    assert frame_local_range(CanonicalLocation(base_ref=frame, offset=-4, size=8)) is None
    assert frame_local_range(CanonicalLocation(base_ref=frame, offset=8, size=8)) is None


def test_store_classification_keeps_caller_area_frame_pointer_and_indexed_stores_observable():
    from scripts.function_tracer_pcode.analysis.effects.location import _impl_classify_store_address as classify

    sp = _register("sp", sp=True)
    assert classify(_plus(sp, -16), [], size=8)[0] == "stack_frame"  # P16
    assert classify(_plus(sp, 16), [], size=8)[0] == "unresolved"  # N31: caller area
    assert classify(_plus(_register("x29", fp=True), -16), [], size=8)[0] == "unresolved"  # N30
    index = Expression.binary_op("INT_ADD", sp, _p())
    assert classify(index, PARAMS, size=8)[0] == "unresolved"  # N32


# ---------------------------------------------------------------------------
# frame の局所性の証拠（AC 9: entry SP より下というだけでは局所にしない）
# ---------------------------------------------------------------------------


class _FrameVarnode:
    def __init__(self, key, size=8):
        self.key = key
        self._size = size

    def getSize(self):
        return self._size

    def getDef(self):
        return None


class _FrameOp:
    def __init__(self, mnemonic, inputs, order):
        self.mnemonic = mnemonic
        self.inputs = [_FrameVarnode(key) for key in inputs]
        self.order = order

    def getMnemonic(self):
        return self.mnemonic

    def getNumInputs(self):
        return len(self.inputs)

    def getInput(self, index):
        return self.inputs[index]

    def getOutput(self):
        return None

    def getSeqnum(self):
        order = self.order

        class _Seq:
            def getTarget(self):
                return _Address(0x1000 + order * 4)

            def getOrder(self):
                return 0

        return _Seq()


def _summarize_frame(ops, values):
    """`ops` を 1 block に並べ、`values`（varnode の key → 追跡した式）で effect 要約を作る。"""

    from scripts.function_tracer_pcode.analysis.effects.summary import summarize_store_effects
    from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import CallTargetRef

    class _Block:
        pcode_ops = ops

    class _Coverage:
        status = "complete"
        condition_paths = [[]]

    class _Tracker:
        def get_path_coverage_to_block(self, _block):
            return _Coverage()

    class _Tracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("callee")

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=True):
            return values.get(varnode.key, Expression.constant(0, max(1, varnode.getSize())))

    return summarize_store_effects(
        [_Block()],
        _Tracer(),
        _Tracker(),
        list(PARAMS),
        direct_call_summary=lambda _target, _args: EffectSummary(parameter_names=[], effects=[]),
        resolve_callee_parameters=lambda _target: [],
        debug=False,
    )


def _frame_values(**extra):
    sp = _register("sp", sp=True)
    values = {"slot": _plus(sp, -16), "one": Expression.constant(1, 8), "p": _p(), "slot_value": _mem(_plus(sp, -16), 8)}
    values.update(extra)
    return values


def _frame_store():
    return _FrameOp("STORE", ["space", "slot", "one"], order=1)


def _frame_summary_and_reads(ops, values, read):
    """`ops` の関数の effect 要約（本番の producer）と、関数の出口で `read` を返す解析。"""

    summary = _summarize_frame(ops, values)
    analysis = _analysis("f", read)
    analysis.effect_summary = summary
    return summary, analysis


@pytest.mark.parametrize(
    "ops",
    [
        # 呼び出しも frame の番地の流出も無い関数の、entry SP の 16 byte 下への store（`p` との比較も無い）
        pytest.param([_FrameOp("RETURN", ["ret", "slot_value"], order=2)], id="no_call_no_escape"),
        # 同じ関数が後で `*p` へ書く（`p == sp - 16` なら frame の store を上書きする・される）
        pytest.param([_FrameOp("STORE", ["space", "p", "one"], order=2)], id="store_through_p_after"),
        # frame の番地を callee へ渡す
        pytest.param([_FrameOp("CALL", ["target", "slot"], order=2)], id="address_passed_to_callee"),
        # 引数の無い呼び出しも stack で渡す引数の領域を読み得る
        pytest.param([_FrameOp("CALL", ["target"], order=2)], id="callee_may_read_outgoing_area"),
        # frame の番地を memory（parameter の指す先）へ書く
        pytest.param([_FrameOp("STORE", ["space", "p", "slot"], order=2)], id="address_stored_to_memory"),
        # frame の番地を返す
        pytest.param([_FrameOp("RETURN", ["ret", "slot"], order=2)], id="address_returned"),
    ],
)
def test_frame_store_is_not_proven_local(ops):
    """負例（b）: entry SP より下の store は、呼び出しも番地の流出も無くても局所にしない（AC 9）。

    store が確保された frame の中にあることも、入口の pointer・global の番地がその番地と等しくなり得ないことも
    high P-code からは示せないので、位置を証明できない store として EQ と NOT_EQ を止める。修正前は entry SP より
    下の定数の範囲で、呼び出しと番地の流出が無ければ観測から外し、EQ を止めなかった。"""

    summary = _summarize_frame([_frame_store(), *ops], _frame_values())
    assert "effect_store_location_unmodeled" in summary.incomplete_reasons
    analysis = _analysis("f", Expression.constant(0, 4))
    analysis.effect_summary = summary
    assert "effect_store_location_unmodeled" in analysis.get_equivalence_blocking_unsafety_reasons()
    assert "effect_store_location_unmodeled" in analysis.get_decisive_sat_unsafety_reasons()


def test_frame_store_far_below_entry_sp_is_not_proven_local():
    """負例: entry SP より大きく下（1 MiB）の store は、確保された frame の外（global の番地にも届き得る）。"""

    far = _plus(_register("sp", sp=True), -0x100000)
    summary = _summarize_frame(
        [_FrameOp("STORE", ["space", "far", "one"], order=1), _FrameOp("RETURN", ["ret"], order=2)],
        _frame_values(far=far),
    )
    assert "effect_store_location_unmodeled" in summary.incomplete_reasons


def test_read_through_parameter_after_a_frame_store_is_not_disjoint():
    """負例（a）: 呼び出しも番地の流出も無い関数で、frame の slot へ書いた後に `*p` を読む（`p` と frame の番地を比べる
    条件は無い）。`p == sp - 16` の実行では読み出しが store の値を返すので、入口の値で描けない。

    修正前は frame が局所と示せたとして frame と parameter を DISJOINT にし、読み出しを止めなかった。"""

    read = _mem(_p(), 8)
    summary, analysis = _frame_summary_and_reads(
        [_frame_store(), _FrameOp("RETURN", ["ret", "p_value"], order=2)], _frame_values(p_value=read), read
    )
    assert summary.frame_local_effects
    assert analysis.has_unresolved_memory_read_aliases()
    assert "memory_read_alias_unresolved" in analysis.get_equivalence_blocking_unsafety_reasons()
    assert "memory_read_alias_unresolved" in analysis.get_decisive_sat_unsafety_reasons()


def test_read_of_another_frame_slot_after_a_frame_store_is_disjoint():
    """正例: frame の別の slot の読み出しは、frame の store と同じ基底の定数の範囲で離れている（検査は止めない）。"""

    read = _mem(_plus(_register("sp", sp=True), -32), 8)
    summary, analysis = _frame_summary_and_reads(
        [_frame_store(), _FrameOp("RETURN", ["ret", "other"], order=2)], _frame_values(other=read), read
    )
    assert summary.frame_local_effects
    assert not analysis.has_unresolved_memory_read_aliases()


def test_function_without_frame_stores_is_not_blocked_by_the_frame_rule():
    """正例: frame へ書かない関数（`*p` への store だけ）は、frame の規則で止めない（不要な UNKNOWN にしない）。"""

    summary = _summarize_frame(
        [_FrameOp("STORE", ["space", "p", "one"], order=1), _FrameOp("RETURN", ["ret"], order=2)], _frame_values()
    )
    assert summary.frame_local_effects == ()
    assert "effect_store_location_unmodeled" not in summary.incomplete_reasons
    assert len(summary.effects) == 1


# ---------------------------------------------------------------------------
# 具体化（N21 / N35）
# ---------------------------------------------------------------------------


class _Address:
    def __init__(self, offset):
        self.offset = offset

    def getOffset(self):
        return self.offset

    def add(self, delta):
        return _Address(self.offset + delta)

    def getAddressSpace(self):
        return _Space()


class _Space:
    def getAddress(self, offset):
        return _Address(offset)

    def getName(self):
        return "ram"


class _Block:
    def __init__(self, start, end, *, write=False, volatile=False, init=True, read=True, overlay=False):
        self.start, self.end = start, end
        self.flags = dict(write=write, volatile=volatile, init=init, read=read, overlay=overlay)

    def getStart(self):
        return _Address(self.start)

    def getEnd(self):
        return _Address(self.end)

    def isWrite(self):
        return self.flags["write"]

    def isVolatile(self):
        return self.flags["volatile"]

    def isInitialized(self):
        return self.flags["init"]

    def isRead(self):
        return self.flags["read"]

    def isOverlay(self):
        return self.flags["overlay"]


class _Relocation:
    def __init__(self, address, status, length=8):
        self.address, self.status, self.length = address, status, length

    def getAddress(self):
        return _Address(self.address)

    def getStatus(self):
        return self.status

    def getBytes(self):
        return bytes(self.length)


class _Program:
    def __init__(self, blocks, relocations=(), data=None):
        self.blocks, self.relocations, self.data = blocks, list(relocations), data or {}

    def getMemory(self):
        program = self

        class _Memory:
            def getBlock(self, address):
                return next((b for b in program.blocks if b.start <= address.offset <= b.end), None)

            def getBlocks(self):
                return list(program.blocks)

            def getByte(self, address):
                return program.data.get(address.offset, 0)

        return _Memory()

    def getAddressFactory(self):
        class _Factory:
            def getDefaultAddressSpace(self):
                return _Space()

        return _Factory()

    def getRelocationTable(self):
        program = self

        class _Table:
            def getRelocations(self, address):
                return iter([r for r in program.relocations if r.address == address.offset])

        return _Table()

    def getLanguage(self):
        class _Language:
            def isBigEndian(self):
                return False

        return _Language()


def test_q1_reads_only_initialized_read_only_unrelocated_bytes_in_one_block():
    from scripts.function_tracer_pcode.analysis.program_image import CODE_TARGET, DATA_VALUE, read_image_value

    data = {0x100160 + i: b for i, b in enumerate(b"\x01\x02\x03\x04\x05\x06\x07\x08")}
    rodata = _Block(0x100160, 0x1001EF)
    assert read_image_value(_Program([rodata], data=data), 0x100160, 4) == 0x04030201
    assert read_image_value(_Program([_Block(0x100160, 0x1001EF, write=True)], data=data), 0x100160, 4) is None
    assert read_image_value(_Program([_Block(0x100160, 0x1001EF, volatile=True)], data=data), 0x100160, 4) is None
    assert read_image_value(_Program([_Block(0x100160, 0x100161)], data=data), 0x100160, 4) is None  # crosses the end
    partial = _Program([rodata], [_Relocation(0x100160, "PARTIAL")], data)
    assert read_image_value(partial, 0x100160, 8, purpose=CODE_TARGET) is None  # N35
    applied = _Program([rodata], [_Relocation(0x100160, "APPLIED")], data)
    assert read_image_value(applied, 0x100160, 8, purpose=DATA_VALUE) is None
    assert read_image_value(applied, 0x100160, 8, purpose=CODE_TARGET) == 0x0807060504030201
    preceding = _Program([rodata], [_Relocation(0x10015C, "APPLIED", length=8)], data)
    assert read_image_value(preceding, 0x100160, 4) is None  # a relocation that starts before the read


class _JLongSpace(_Space):
    """JPype の `AddressSpace.getAddress(long)` と同じく、Java の long に収まらない offset で `OverflowError`。"""

    def getAddress(self, offset):
        if not -(1 << 63) <= offset <= (1 << 63) - 1:
            raise OverflowError("int too big to convert")
        return _Address(offset)


class _JLongProgram(_Program):
    def getAddressFactory(self):
        class _Factory:
            def getDefaultAddressSpace(self):
                return _JLongSpace()

        return _Factory()


def test_image_reads_past_the_java_long_offset_range_are_not_concretized():
    """Neq 正式評価 4285315a の INVALID 72 件: 戻り値の定数 `2**64 - 1` を番地の候補にした読み出しが
    `getAddress` の `OverflowError` で pair 全体を落としていた。収まらない番地は具体化しない（None）。"""

    from scripts.function_tracer_pcode.analysis.program_image import read_image_value

    data = {0x100160 + i: b for i, b in enumerate(b"\x01\x02\x03\x04")}
    program = _JLongProgram([_Block(0x100160, 0x1001EF)], data=data)
    assert read_image_value(program, 0x100160, 4) == 0x04030201
    assert read_image_value(program, (1 << 64) - 1, 4) is None
    assert read_image_value(program, (1 << 64) - 16, 4) is None
    assert read_image_value(program, (1 << 63) - 2, 4) is None  # 最後の byte が long の範囲を越える
    assert read_image_value(program, (1 << 63) - 4, 4) is None  # 収まるが block の外


def test_readonly_affine_literal_ignores_return_constants_outside_the_address_range():
    from types import SimpleNamespace

    from scripts.function_tracer_pcode.analysis.recurrence import readonly_reduction as rr

    lanes = b"".join(v.to_bytes(4, "little") for v in (3, 5, 7, 9))
    data = {0x100160 + i: b for i, b in enumerate(lanes)}
    host = SimpleNamespace(tracer=SimpleNamespace(program=_JLongProgram([_Block(0x100160, 0x1001EF)], data=data)))
    host._read_readonly_int32_lanes = lambda address, count: rr._impl__read_readonly_int32_lanes(host, address, count)
    host._expression_integer_constants = lambda value: list(value)
    analysis = SimpleNamespace(returns=[SimpleNamespace(value=((1 << 64) - 1,))])
    assert rr._impl__readonly_affine_progression_literal(host, analysis) is None
    analysis = SimpleNamespace(returns=[SimpleNamespace(value=((1 << 64) - 1, 0x100160))])
    literal = rr._impl__readonly_affine_progression_literal(host, analysis)
    assert (literal.step, literal.lane_base) == (2, 3)


def test_image_ranges_skip_overlay_blocks():
    from scripts.function_tracer_pcode.analysis.program_image import image_ranges

    program = _Program([_Block(0x100000, 0x10011F), _Block(0, 0x43F, overlay=True), _Block(0x100160, 0x1001EF)])
    assert image_ranges(program) == ((0x100000, 0x100120), (0x100160, 0x1001F0))


# ---------------------------------------------------------------------------
# 出自（N34）
# ---------------------------------------------------------------------------


def test_image_address_constants_are_not_folded_into_bare_numbers():
    from scripts.function_tracer_pcode.semantics.normalize.bitmask import _fold_constant_expression

    folded = _fold_constant_expression(Expression.binary_op("INT_ADD", _image_constant(0x100160), Expression.constant(8, 8)))
    assert folded.expr_type is ExpressionType.BINARY_OP
    plain = _fold_constant_expression(Expression.binary_op("INT_ADD", Expression.constant(0x10, 8), Expression.constant(8, 8)))
    assert plain.expr_type is ExpressionType.CONSTANT and plain.value == 0x18


# ---------------------------------------------------------------------------
# SAT（N5 / N24）
# ---------------------------------------------------------------------------


class _Case:
    def __init__(self, value, conditions=()):
        self.value_expr = value
        self.normalized_value_expr = value
        self.conditions = list(conditions)
        self.summary_conditions = list(conditions)
        self.comparison_surface = None


def test_n5_counterexample_reading_per_side_memory_is_unrealized_and_not_replay_resolvable():
    from scripts.function_tracer_pcode.proof.formula.memory_state import case_pair_memory_state_refs
    from scripts.function_tracer_pcode.proof.sat_safety_resolution import (
        SatSafetyResolution,
        sat_safety_ref_resolution,
        sat_safety_reason_id_for_refs,
    )

    refs = case_pair_memory_state_refs(_Case(_mem(_p())), _Case(Expression.constant(1, 4)))
    assert refs and all(ref.startswith("memory_state_unrealized:array:") for ref in refs)
    assert all(sat_safety_ref_resolution(ref) is SatSafetyResolution.ANALYSIS_UNSAFETY for ref in refs)
    assert sat_safety_reason_id_for_refs(refs) == "counterexample_analysis_safety_unproven"
    assert case_pair_memory_state_refs(_Case(_p()), _Case(Expression.constant(1, 8))) == []


def test_counterexample_on_the_observation_index_is_unrealized_in_pr_a():
    surface = build_void_effect_summary_expr([_store(P, 0, 4, 1, 1)], PARAMS, big_endian=False)
    from scripts.function_tracer_pcode.proof.formula.memory_state import case_pair_memory_state_refs

    refs = case_pair_memory_state_refs(_Case(surface), _Case(surface))
    assert any(ref.startswith("memory_state_unrealized:observation:") for ref in refs)


# ---------------------------------------------------------------------------
# 構造の同一視と oracle（N9 / N12 / N15）
# ---------------------------------------------------------------------------


def test_cross_side_identity_gate_refuses_memory_and_image_addresses():
    from scripts.function_tracer_pcode.proof.formula.input_correspondence import owner_free_identity_gate
    from scripts.function_tracer_pcode.tests.unit.test_cross_side_identity_gate import _identity_pair, _p as gate_p

    relation = build_input_correspondence_set(*_identity_pair())
    read = (_mem(gate_p("n", 0)),)
    refused = owner_free_identity_gate(read, (_mem(gate_p("n", 0)),), ics=relation)
    assert not refused.passed
    assert any("memory_uncorresponded:left:array" in ref for ref in refused.evidence_refs)
    address = (_image_constant(0x100160),)
    assert not owner_free_identity_gate(address, (_image_constant(0x100160),), ics=relation).passed
    assert owner_free_identity_gate((gate_p("n", 0),), (gate_p("n", 0),), ics=relation).passed


def test_cross_side_oracle_helpers_do_not_prove_with_memory_conditions():
    from scripts.function_tracer_pcode.proof.strategies.pairwise_services import case_conditions

    left = Condition(Expression.binary_op("INT_EQUAL", _mem(Expression.constant(0x10, 8)), Expression.constant(0, 4)))
    right = left.negate()

    class _Host:
        def _conditions_with_object_identity_parameter_symbols(self, conditions, parameters):
            return list(conditions)

        def _conditions_have_parameter_mask_constant_conflict(self, conditions):
            return False

    # 共有の配列では矛盾（UNSAT）になる組。左右の memory は別なので証明できない
    assert case_conditions._impl__condition_set_is_unsat(_Host(), [left, right], []) is False
    assert case_conditions._impl__condition_set_implies(_Host(), [left], [left], []) is False


def test_deferred_call_keys_do_not_match_memory_arguments_across_sides():
    from scripts.function_tracer_pcode.proof.deferred_call_abstraction import _object_centric_expression_key

    left = _object_centric_expression_key(_mem(_p()), for_call_target=False)
    right = _object_centric_expression_key(_mem(_p()), for_call_target=False)
    assert left != right
    assert _object_centric_expression_key(_p(), for_call_target=False) == _object_centric_expression_key(_p(), for_call_target=False)


# ---------------------------------------------------------------------------
# P12（N37 / P17）
# ---------------------------------------------------------------------------


def test_identical_binary_premises_are_admitted_by_the_policy_and_recorded():
    from scripts.function_tracer_pcode.proof.formula.input_correspondence.memory_policy import (
        IDENTICAL_BINARY_PREMISES,
        MemoryPremise,
        PremiseAdmission,
        premise_record,
        premises_admit_unconditional_eq,
    )

    assert premises_admit_unconditional_eq(IDENTICAL_BINARY_PREMISES)
    assert premise_record(IDENTICAL_BINARY_PREMISES) == (
        ("image_identity", "admitted_by_d"),
        ("caller_state_same", "admitted_by_d"),
    )
    conditional = {MemoryPremise.IMAGE_IDENTITY: PremiseAdmission.ADMITTED_BY_D}
    assert not premises_admit_unconditional_eq(IDENTICAL_BINARY_PREMISES, conditional)  # N37


def test_post_state_read_is_not_lowered_past_a_may_alias_store():
    """`*p = 1; *q = 2; return *p`: 以前の lowering は `*q` を見ずに `*p` の store の値を返し得た（p == q なら 2）。

    出口の状態の読み出しは、先行する store と同じ場所（SAME）の store の値か、重ならない（DISJOINT）なら入口の値に
    なる。どちらとも言えない store があれば簡約せず、描かれる入口の読み出しは検査に落ちる。
    """

    from scripts.function_tracer_pcode.analysis.effects.post_state import _effects_may_alias_without_proof
    from scripts.function_tracer_pcode.analysis.effects.summary import post_state_read_expression_for_location

    location = CanonicalLocation(base_ref=P, offset=0, size=4)
    assert _effects_may_alias_without_proof(location, [], [_store(P, 0, 4, 1, 1), _store(Q, 0, 4, 2, 2)])
    assert not _effects_may_alias_without_proof(location, [], [_store(P, 0, 4, 1, 1), _store(P, 8, 4, 2, 2)])
    assert _effects_may_alias_without_proof(location, [], [_store(P, 2, 4, 1, 1)])  # 部分重なり
    read = post_state_read_expression_for_location(location, PARAMS)
    assert _analysis("f", read, effects=[_store(P, 0, 4, 1, 1), _store(Q, 0, 4, 2, 2)]).has_unresolved_memory_read_aliases()


def test_image_bytes_are_read_only_through_the_program_image_gate():
    """Q1（I7）: image の byte を読む Ghidra の API は `analysis/program_image.py` だけが呼ぶ（判定の無い経路を残さない）。"""

    import ast
    from pathlib import Path

    package = Path(__file__).resolve().parents[2]
    readers = {"getByte", "getBytes", "getShort", "getInt", "getLong"}
    found = set()
    for path in package.rglob("*.py"):
        relative = path.relative_to(package).as_posix()
        if relative.startswith("tests/"):
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            name = None
            if isinstance(node, ast.Attribute):
                name = node.attr
            elif isinstance(node, ast.Constant) and isinstance(node.value, str):
                name = node.value
            if name in readers:
                found.add(relative)
    assert found == {"analysis/program_image.py"}


def test_memory_array_names_come_only_from_the_sides_module():
    """I2: 配列名を文字列で組み立てる経路を残さない（`core/render_smt/sides.py` の 1 つの規則）。"""

    from pathlib import Path

    package = Path(__file__).resolve().parents[2]
    offenders = []
    for path in package.rglob("*.py"):
        relative = path.relative_to(package).as_posix()
        if relative.startswith("tests/") or relative == "core/render_smt/sides.py":
            continue
        text = path.read_text(encoding="utf-8")
        if "(select mem{" in text or "f\"(select mem" in text:
            offenders.append(relative)
    assert offenders == []


def test_float_store_values_are_observed_as_their_bits():
    """浮動小数点の値の store（SphereConstructor の半径）。値の bit 列を観測する（以前の実装では SMT の sort が合わなかった）。"""

    r = Expression.parameter("r", 2, data_type="float", size=4)
    params = PARAMS + [_param("r", size=4, index=2, data_type="float")]
    left = build_void_effect_summary_expr([_store(P, 0, 4, r, 1)], params, big_endian=False)
    right = build_void_effect_summary_expr([_store(P, 0, 4, r, 1)], params, big_endian=False)
    formula = _formula(
        _analysis("f", left, params=params, return_type="void"), _analysis("g", right, params=params, return_type="void")
    )
    assert _check(formula) == z3.unsat
