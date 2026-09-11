"""Issue #104 follow-up: MIPS ``sdl``/``sdr`` (``swl``/``swr``) unaligned store
pairs are composed into one ordinary store of the whole value.

The expression shapes mirror what Ghidra's MIPS64 sleigh + decompiler
produce for ``obj->field = v`` compiled by clang -O0 (observed on
``raytrace/sphere SphereConstructor``):

    left : STORE (Y - (Y & 7)) <- (MEM[Y - (Y & 7)] & (-1 << ((8 - (Y & 7)) * 8))) | (v >> ((Y & 7) * 8))
    right: STORE (Y' - (Y' & 7)) <- (v << ((7 - (Y' & 7)) * 8)) | (MEM[Y' - (Y' & 7)] & (-1 >> (((Y' & 7) + 1) * 8)))

with ``Y = X`` and ``Y' = X + 7``.
"""
from scripts.function_tracer_pcode.analysis.effects.summary import (
    match_unaligned_store_half,
    pair_unaligned_store_halves,
    summarize_store_effects,
)
from scripts.function_tracer_pcode.analysis.effects._shared import (
    _EFFECT_STORE_LOCATION_UNMODELED_REASON,
)
from scripts.function_tracer_pcode.core import Expression
from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import forbid_callee_summary
from scripts.function_tracer_pcode.tests.unit.test_global_effect_surface_issue104 import (
    _Address,
    _Block,
    _Op,
    _Tracer,
    _Tracker,
    _Varnode,
    _param,
)


def _c(value, size=8):
    return Expression.constant(value, size)


def _b(op, left, right, size=8):
    expr = Expression.binary_op(op, left, right)
    expr.size = size
    return expr


def _p1():
    return Expression.parameter("param_1", 0, data_type="undefined8 *", size=8)


def _v(name="param_6", index=5):
    return Expression.parameter(name, index, data_type="ulong", size=8)


def _align_down(y, width=8):
    return _b("INT_SUB", y, _b("INT_AND", y, _c(width - 1)))


def _low(y, width=8):
    return _b("INT_AND", y, _c(width - 1))


def _left_half(y, value, width=8):
    addr = _align_down(y, width)
    mem = Expression.memory(addr, width)
    keep = _b("INT_AND", mem, _b("INT_LEFT", _c(-1), _b("INT_MULT", _b("INT_SUB", _c(width), _low(y, width)), _c(8))))
    part = _b("INT_RIGHT", value, _b("INT_MULT", _low(y, width), _c(8)))
    return addr, _b("INT_OR", keep, part)


def _right_half(y, value, width=8):
    addr = _align_down(y, width)
    mem = Expression.memory(addr, width)
    part = _b("INT_LEFT", value, _b("INT_MULT", _b("INT_SUB", _c(width - 1), _low(y, width)), _c(8)))
    keep = _b("INT_AND", mem, _b("INT_RIGHT", _c(-1), _b("INT_MULT", _b("INT_ADD", _low(y, width), _c(1)), _c(8))))
    return addr, _b("INT_OR", part, keep)


def test_left_and_right_halves_are_recognised_with_the_same_base_and_value():
    x = _b("INT_ADD", _p1(), _c(32))
    left_addr, left_val = _left_half(x, _v())
    right_addr, right_val = _right_half(_b("INT_ADD", _p1(), _c(39)), _v())
    left = match_unaligned_store_half(left_addr, left_val, 8)
    right = match_unaligned_store_half(right_addr, right_val, 8)
    assert left is not None and left.side == "left" and left.width == 8
    assert right is not None and right.side == "right" and right.width == 8
    assert left.value_expr.to_string() == "param_6"
    assert right.value_expr.to_string() == "param_6"
    assert left.base_key == right.base_key
    assert left.pair_key == right.pair_key


def test_plain_stores_and_foreign_shapes_are_not_halves():
    assert match_unaligned_store_half(_p1(), _v(), 8) is None
    x = _b("INT_ADD", _p1(), _c(32))
    addr, val = _left_half(x, _v())
    assert match_unaligned_store_half(addr, val, 4) is None  # width mismatch
    assert match_unaligned_store_half(addr, _v(), 8) is None  # aligned address but plain value
    # mask on the wrong operand
    wrong = _b("INT_OR", _b("INT_AND", Expression.memory(addr, 8), _c(0xFF)), _b("INT_RIGHT", _v(), _b("INT_MULT", _low(x), _c(8))))
    assert match_unaligned_store_half(addr, wrong, 8) is None


def test_interleaved_field_pairs_compose_in_clang_o0_order():
    """clang -O0 emits sdl(f4) sdl(f3) sd(f0) sdr(f4) sdr(f3): every pair is
    separated only by disjoint fields of the same object."""
    from scripts.function_tracer_pcode.core import CanonicalLocation, LocationBaseRef

    def locate(base_expr, width):
        off = base_expr.operands[1].value if base_expr.operands[1].expr_type.name == "CONSTANT" else 0
        return CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=int(off), size=width)

    l32a, l32v = _left_half(_b("INT_ADD", _p1(), _c(32)), _v())
    l24a, l24v = _left_half(_b("INT_ADD", _p1(), _c(24)), _v("param_5", 4))
    r32a, r32v = _right_half(_b("INT_ADD", _p1(), _c(39)), _v())
    r24a, r24v = _right_half(_b("INT_ADD", _p1(), _c(31)), _v("param_5", 4))
    halves = [
        ("L32", match_unaligned_store_half(l32a, l32v, 8), (0, 0)),
        ("L24", match_unaligned_store_half(l24a, l24v, 8), (0, 1)),
        ("R32", match_unaligned_store_half(r32a, r32v, 8), (0, 3)),
        ("R24", match_unaligned_store_half(r24a, r24v, 8), (0, 4)),
    ]
    pairs, unmatched = pair_unaligned_store_halves(
        halves, locate, barriers=[((0, 2), CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=0, size=8))]
    )
    assert sorted((l, r) for l, r, _h in pairs) == [("L24", "R24"), ("L32", "R32")]
    assert unmatched == []


def test_pairing_requires_same_value_and_base_and_reports_leftovers():
    x = _b("INT_ADD", _p1(), _c(32))
    la, lv = _left_half(x, _v())
    ra, rv = _right_half(_b("INT_ADD", _p1(), _c(39)), _v())
    other_ra, other_rv = _right_half(_b("INT_ADD", _p1(), _c(39)), _v("param_5", 4))
    left = match_unaligned_store_half(la, lv, 8)
    right = match_unaligned_store_half(ra, rv, 8)
    other = match_unaligned_store_half(other_ra, other_rv, 8)
    pairs, unmatched = pair_unaligned_store_halves([("L", left, (0, 0)), ("R", right, (0, 1))])
    assert [(l, r) for l, r, _h in pairs] == [("L", "R")]
    assert unmatched == []
    # a right half with a different value never pairs, and it also breaks the
    # adjacency of the real pair: both leftovers are reported
    pairs, unmatched = pair_unaligned_store_halves([("L", left, (0, 0)), ("R2", other, (0, 1)), ("R", right, (0, 2))])
    assert pairs == []
    assert [tag for tag, _h in unmatched] == ["L", "R2", "R"]


def test_halves_in_different_blocks_never_pair():
    """if (c) SDL(X, v) else SDR(X+7, v): no execution performs the full store."""
    x = _b("INT_ADD", _p1(), _c(32))
    la, lv = _left_half(x, _v())
    ra, rv = _right_half(_b("INT_ADD", _p1(), _c(39)), _v())
    left = match_unaligned_store_half(la, lv, 8)
    right = match_unaligned_store_half(ra, rv, 8)
    pairs, unmatched = pair_unaligned_store_halves([("L", left, (0, 3)), ("R", right, (1, 0))])
    assert pairs == []
    assert [tag for tag, _h in unmatched] == ["L", "R"]


def test_halves_separated_by_a_memory_or_call_barrier_never_pair():
    x = _b("INT_ADD", _p1(), _c(32))
    la, lv = _left_half(x, _v())
    ra, rv = _right_half(_b("INT_ADD", _p1(), _c(39)), _v())
    left = match_unaligned_store_half(la, lv, 8)
    right = match_unaligned_store_half(ra, rv, 8)
    from scripts.function_tracer_pcode.core import CanonicalLocation, LocationBaseRef

    def _loc(name, index, offset, size):
        return CanonicalLocation(base_ref=LocationBaseRef.parameter(name, index=index), offset=offset, size=size)

    def locate(base_expr, width):
        return _loc("param_1", 0, 32, width)

    # a call (location None) between the halves is a barrier
    pairs, unmatched = pair_unaligned_store_halves(
        [("L", left, (0, 0)), ("R", right, (0, 2))], locate, barriers=[((0, 1), None)]
    )
    assert pairs == []
    assert [tag for tag, _h in unmatched] == ["L", "R"]
    # an overlapping store between them is a barrier
    pairs, unmatched = pair_unaligned_store_halves(
        [("L", left, (0, 0)), ("R", right, (0, 2))], locate,
        barriers=[((0, 1), _loc("param_1", 0, 36, 4))],
    )
    assert pairs == []
    # a store to a different base object may alias: barrier
    pairs, unmatched = pair_unaligned_store_halves(
        [("L", left, (0, 0)), ("R", right, (0, 2))], locate,
        barriers=[((0, 1), _loc("param_2", 1, 64, 8))],
    )
    assert pairs == []
    # a provably disjoint store of the same object (another field) is not
    pairs, unmatched = pair_unaligned_store_halves(
        [("L", left, (0, 0)), ("R", right, (0, 2))], locate,
        barriers=[((0, 1), _loc("param_1", 0, 0, 8))],
    )
    assert [(l, r) for l, r, _h in pairs] == [("L", "R")]
    # barriers outside the span do not matter
    pairs, unmatched = pair_unaligned_store_halves(
        [("L", left, (0, 1)), ("R", right, (0, 2))], locate, barriers=[((0, 0), None), ((0, 3), None), ((1, 1), None)]
    )
    assert [(l, r) for l, r, _h in pairs] == [("L", "R")]
    # without a canonical location the span can never be proven clear
    pairs, unmatched = pair_unaligned_store_halves(
        [("L", left, (0, 0)), ("R", right, (0, 2))], None,
        barriers=[((0, 1), _loc("param_1", 0, 0, 8))],
    )
    assert pairs == []


def test_zext_and_sext_of_the_same_source_are_different_stored_values():
    """ZEXT32(0xffffffff) != SEXT32(0xffffffff): the halves store different
    64-bit values and must not be composed."""
    x = _b("INT_ADD", _p1(), _c(32))
    source = Expression.parameter("param_6", 5, data_type="uint", size=4)
    zext = Expression.unary_op("INT_ZEXT", source)
    zext.size = 8
    sext = Expression.unary_op("INT_SEXT", source)
    sext.size = 8
    la, lv = _left_half(x, zext)
    ra, rv = _right_half(_b("INT_ADD", _p1(), _c(39)), sext)
    left = match_unaligned_store_half(la, lv, 8)
    right = match_unaligned_store_half(ra, rv, 8)
    assert left is not None and right is not None
    assert left.value_key != right.value_key
    pairs, unmatched = pair_unaligned_store_halves([("L", left, (0, 0)), ("R", right, (0, 1))])
    assert pairs == []
    assert len(unmatched) == 2


def _store(addr_key, val_key, target):
    return _Op(
        "STORE",
        None,
        [_Varnode("const", 0x1b1, 4), _Varnode("unique", 0x10, 8, key=addr_key), _Varnode("register", 0x20, 8, key=val_key)],
        _Address("ram", target),
    )


def test_matched_pair_becomes_one_eight_byte_parameter_store():
    """Old behaviour: both halves were dropped (address not canonicalisable),
    then (PR 1) marked unmodelled.  New behaviour: one store of v at p+32."""
    x = _b("INT_ADD", _p1(), _c(32))
    la, lv = _left_half(x, _v())
    ra, rv = _right_half(_b("INT_ADD", _p1(), _c(39)), _v())
    tracer = _Tracer([], values={"la": la, "lv": lv, "ra": ra, "rv": rv})
    params = [_param("param_1", 0, size=8, data_type="undefined8 *"), _param("param_6", 5, size=8, data_type="ulong")]
    summary = summarize_store_effects(
        [_Block([_store("la", "lv", 0x100), _store("ra", "rv", 0x104)])], tracer, _Tracker(), params,
        direct_call_summary=forbid_callee_summary
    )
    assert summary.incomplete_reasons == ()
    assert len(summary.effects) == 1
    effect = summary.effects[0]
    assert effect.location.base_ref.is_parameter()
    assert effect.location.offset == 32
    assert effect.location.size == 8
    assert effect.value.to_string() == "param_6"


def test_ptradd_left_half_pairs_with_int_add_right_half():
    """clang emits PTRADD(p, 4, 8) for the left half and p + 39 for the right."""
    from scripts.function_tracer_pcode.core import ExpressionType

    ptradd = Expression(ExpressionType.INTRINSIC, name="PTRADD", operands=[_p1(), _c(4), _c(8)], size=8)
    la, lv = _left_half(ptradd, _v())
    ra, rv = _right_half(_b("INT_ADD", _p1(), _c(39)), _v())
    tracer = _Tracer([], values={"la": la, "lv": lv, "ra": ra, "rv": rv})
    params = [_param("param_1", 0, size=8, data_type="undefined8 *"), _param("param_6", 5, size=8, data_type="ulong")]
    summary = summarize_store_effects(
        [_Block([_store("la", "lv", 0x100), _store("ra", "rv", 0x104)])], tracer, _Tracker(), params,
        direct_call_summary=forbid_callee_summary
    )
    assert summary.incomplete_reasons == ()
    assert [(e.location.offset, e.location.size) for e in summary.effects] == [(32, 8)]


def test_unmatched_half_fails_closed():
    x = _b("INT_ADD", _p1(), _c(32))
    la, lv = _left_half(x, _v())
    tracer = _Tracer([], values={"la": la, "lv": lv})
    params = [_param("param_1", 0, size=8, data_type="undefined8 *"), _param("param_6", 5, size=8, data_type="ulong")]
    summary = summarize_store_effects([_Block([_store("la", "lv", 0x100)])], tracer, _Tracker(), params, direct_call_summary=forbid_callee_summary)
    assert summary.effects == []
    assert summary.incomplete_reasons == (_EFFECT_STORE_LOCATION_UNMODELED_REASON,)


def test_four_byte_swl_swr_pair_is_supported():
    x = _b("INT_ADD", _p1(), _c(52))
    value = Expression.parameter("param_9", 8, data_type="uint", size=4)
    la, lv = _left_half(x, value, width=4)
    ra, rv = _right_half(_b("INT_ADD", _p1(), _c(55)), value, width=4)
    left = match_unaligned_store_half(la, lv, 4)
    right = match_unaligned_store_half(ra, rv, 4)
    assert left is not None and right is not None and left.pair_key == right.pair_key
    assert left.width == 4


def _call_op(target):
    return _Op("CALL", _Varnode("register", 0x4000, 8), [_Varnode("ram", 0x101000, 8)], _Address("ram", target))


def test_intervening_plain_store_or_call_keeps_the_halves_unmodelled():
    x = _b("INT_ADD", _p1(), _c(32))
    la, lv = _left_half(x, _v())
    ra, rv = _right_half(_b("INT_ADD", _p1(), _c(39)), _v())
    other = Expression.parameter("param_7", 6, data_type="ulong", size=8)
    tracer = _Tracer([], values={"la": la, "lv": lv, "ra": ra, "rv": rv, "p": _p1(), "o": other})
    params = [
        _param("param_1", 0, size=8, data_type="undefined8 *"),
        _param("param_6", 5, size=8, data_type="ulong"),
        _param("param_7", 6, size=8, data_type="ulong"),
    ]
    # a plain store to a *disjoint* field of the same object (p + 0) between
    # the halves is exactly the clang -O0 interleaving: still composed
    with_store = summarize_store_effects(
        [_Block([_store("la", "lv", 0x100), _store("p", "o", 0x104), _store("ra", "rv", 0x108)])], tracer, _Tracker(), params,
        direct_call_summary=forbid_callee_summary
    )
    assert with_store.incomplete_reasons == ()
    assert sorted((e.location.offset, e.location.size) for e in with_store.effects) == [(0, 8), (32, 8)]

    # an overlapping store (p + 36) between the halves is a barrier
    overlap = _b("INT_ADD", _p1(), _c(36))
    tracer_overlap = _Tracer([], values={"la": la, "lv": lv, "ra": ra, "rv": rv, "q": overlap, "o": other})
    with_overlap = summarize_store_effects(
        [_Block([_store("la", "lv", 0x100), _store("q", "o", 0x104), _store("ra", "rv", 0x108)])], tracer_overlap, _Tracker(), params,
        direct_call_summary=forbid_callee_summary
    )
    assert _EFFECT_STORE_LOCATION_UNMODELED_REASON in with_overlap.incomplete_reasons
    assert all(e.location.offset != 32 for e in with_overlap.effects)

    with_call = summarize_store_effects(
        [_Block([_store("la", "lv", 0x100), _call_op(0x104), _store("ra", "rv", 0x108)])], tracer, _Tracker(), params,
        direct_call_summary=lambda _target_ref, _arguments: None
    )
    assert _EFFECT_STORE_LOCATION_UNMODELED_REASON in with_call.incomplete_reasons
    assert all(e.location.offset != 32 for e in with_call.effects)
    # Issue #121: 介在する call は barrier であると同時に call-effect lane の
    # blocker としても記録される。この test の前提を明示する。
    assert with_call.has_unsupported_call is True
    assert {ref.reason for ref in with_call.unsupported_call_sites} == {"target_identity_unavailable"}


def test_halves_split_across_blocks_are_unmodelled_at_summary_level():
    x = _b("INT_ADD", _p1(), _c(32))
    la, lv = _left_half(x, _v())
    ra, rv = _right_half(_b("INT_ADD", _p1(), _c(39)), _v())
    tracer = _Tracer([], values={"la": la, "lv": lv, "ra": ra, "rv": rv})
    params = [_param("param_1", 0, size=8, data_type="undefined8 *"), _param("param_6", 5, size=8, data_type="ulong")]
    summary = summarize_store_effects(
        [_Block([_store("la", "lv", 0x100)], 0), _Block([_store("ra", "rv", 0x108)], 1)], tracer, _Tracker(), params,
        direct_call_summary=forbid_callee_summary
    )
    assert summary.effects == []
    assert summary.incomplete_reasons == (_EFFECT_STORE_LOCATION_UNMODELED_REASON,)
