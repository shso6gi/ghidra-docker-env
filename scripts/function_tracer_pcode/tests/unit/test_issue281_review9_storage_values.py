# -*- coding: utf-8 -*-
"""Issue #281 review 9: parameter の入口の値を「別の記憶域の値」として読む producer の位置。

review 8 の `parameter_entry` は node がどの bit を主張するかを決めたが、**記憶域 S にある値が parameter の
どの bit か**（記憶域 → 値）を決める owner が無く、producer ごとに位置を決めていた:

1. live-in の引数の回復（`_recover_unmodified_live_in_argument`）: 記憶域の包含だけで caller の parameter を選び、
   parameter を丸ごと（幅が違えば下位の bit を）返した。64 bit の parameter の上位 32 bit を受ける呼び出しに
   下位 32 bit が渡った（`0x0000000200000001` の上位の 2 が 1 になる）。parameter が引数の記憶域の上位にある
   ときも、部分的な幅の引数（下位の bit）として渡った。
2. 呼び出しの入力を記憶域で選ぶ・位置で対応させる経路: parameter の記憶域の上位にある入力が parameter の値
   （下位の bit）として束縛され得た。
3. tracer の記憶域の幅の変換（`_coerce_expression_width`）: 番地の順の位置を `SUBPIECE` の位置にした（big endian で
   上位と下位が入れ替わる）。広げるときは `INT_SEXT` / `INT_ZEXT` で上位の bit を作った。
4. tracer の束縛値（`_resolve_bound_parameter_expression`）: parameter の幅の値に varnode（parameter の register の
   一部）の記憶域を付けた。狭い束縛値は `INT_SEXT` / `INT_ZEXT` で広げた。

→ `parameter_entry.significance_low_offset` / `entry_value_in_storage` / `bit_offset_in_parameter` が byte order で
位置を決め、決められない・値の外の bit を含むなら回復・選択・束縛をしない。

ここの例は production の関数を合成入力で実行したもの。r9 の probe（V281 診断 96 pair と V-sound）では、
どの経路も記憶域がちょうど同じ組しか通らなかった（実 binary の判定に届いた例は無い）。
"""

from types import SimpleNamespace
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.analysis.effects import call_argument, call_paths
from scripts.function_tracer_pcode.analysis.effects.call_boundary import (
    CallBoundaryRefused,
    CalleeBinding,
    CallSite,
    CalleeTimeline,
    import_callee_expression,
)
from scripts.function_tracer_pcode.analysis.effects.parameter_entry import (
    bit_offset_in_parameter,
    entry_value_in_storage,
    significance_low_offset,
)
from scripts.function_tracer_pcode.analysis.tracer import ParameterStorageDescriptor, PcodeTracer
from scripts.function_tracer_pcode.core import Expression, ExpressionType, LocationBaseRef
from scripts.function_tracer_pcode.core.storage import StorageInfo

OWNER = dict(owner_program_id=1, owner_entry_offset=0x1000)
WIDE = 0x0000000200000001
UPPER, LOWER = 2, 1


#: 基底の register の番地（register 空間）
BASE_OFFSETS = {"x0": 0x4000, "x1": 0x4008}


def _register(name, *, base, byte_offset=0, size=8, base_size=8):
    return StorageInfo(
        is_register=True,
        space_name="register",
        register_name=name,
        offset=BASE_OFFSETS[base] + byte_offset,
        register_offset=BASE_OFFSETS[base] + byte_offset,
        base_register_offset=BASE_OFFSETS[base],
        size=size,
        size_bits=size * 8,
        base_register_name=base,
        base_register_size=base_size,
        base_register_size_bits=base_size * 8,
        bit_offset_in_base=byte_offset * 8,
    )


X0 = _register("x0", base="x0")
X1 = _register("x1", base="x1")
#: 番地の順で x0 の先頭 4 byte / 後ろ 4 byte（little endian では下位 / 上位、big endian では上位 / 下位）
X0_FIRST = _register("x0_first", base="x0", size=4)
X0_SECOND = _register("x0_second", base="x0", byte_offset=4, size=4)


def _halves(big_endian):
    """(上位 32 bit の記憶域, 下位 32 bit の記憶域)。"""

    return (X0_FIRST, X0_SECOND) if big_endian else (X0_SECOND, X0_FIRST)


BYTE_ORDERS = pytest.mark.parametrize("big_endian", [False, True], ids=["LE", "BE"])


def _descriptor(name="p", index=0, storage=X0, size=8, data_type="long", **owner):
    return {"name": name, "index": index, "size": size, "data_type": data_type, "storage": storage, **owner}


def _evaluate(expr, parameter_value):
    """p を `parameter_value` とした値。`PARAMETER` の node は幅の分だけ下位の bit と読む（consumer の読み方）。"""

    mask = (1 << (8 * expr.size)) - 1
    if expr.expr_type is ExpressionType.PARAMETER:
        return parameter_value & mask
    if expr.expr_type is ExpressionType.CONSTANT:
        return int(expr.value) & mask
    if expr.operator == "SUBPIECE":
        source, offset = expr.operands
        return (_evaluate(source, parameter_value) >> (8 * int(offset.value))) & mask
    raise AssertionError(expr.operator)


def _program(big_endian):
    language = None if big_endian is None else SimpleNamespace(isBigEndian=lambda: big_endian)
    return SimpleNamespace(getLanguage=lambda: language)


def _call_tracer(big_endian):
    return SimpleNamespace(
        program=_program(big_endian),
        _get_storage_info_from_varnode=lambda varnode: varnode.storage,
    )


def _import_into_callee(arg, callee_parameter, big_endian, *, read_size=None):
    """生成元（caller の引数）から利用先（callee の parameter の置き換え）まで。"""

    binding = CalleeBinding.for_arguments([callee_parameter], [arg], big_endian=big_endian)
    size = read_size or callee_parameter["size"]
    callee_node = Expression.parameter(
        callee_parameter["name"], callee_parameter["index"], size=size, storage_info=callee_parameter["storage"]
    )
    return import_callee_expression(callee_node, CallSite(None), CalleeTimeline.unknown(), binding=binding)


# ---------------------------------------------------------------------------
# owner: 記憶域どうしの significance の位置
# ---------------------------------------------------------------------------


@BYTE_ORDERS
def test_the_owner_places_register_halves_by_byte_order(big_endian):
    upper, lower = _halves(big_endian)
    assert significance_low_offset(upper, X0, big_endian) == 32
    assert significance_low_offset(lower, X0, big_endian) == 0
    assert significance_low_offset(X0, upper, big_endian) == -32
    assert significance_low_offset(X0, X0, big_endian) == 0


def test_the_owner_does_not_place_a_register_piece_without_a_byte_order():
    assert significance_low_offset(X0_SECOND, X0, None) is None
    assert significance_low_offset(X0, X0, None) == 0


def test_the_same_range_of_another_register_is_not_the_same_place():
    """修正前の `bit_offset_in_parameter` は番地の範囲の数だけを比べ、x1 を x0 の位置 0 としていた。"""

    assert significance_low_offset(X1, X0, False) is None
    assert bit_offset_in_parameter(X1, 64, X0, 64, False) is None


@BYTE_ORDERS
def test_the_entry_value_in_an_upper_storage_is_the_upper_bits(big_endian):
    upper, lower = _halves(big_endian)
    whole = Expression.parameter("p", 0, size=8, storage_info=X0)
    value, determined = entry_value_in_storage(whole, X0, 64, upper, 32, big_endian)
    assert determined == 32 and _evaluate(value, WIDE) == UPPER
    # 低い端が同じなら parameter の決めている範囲そのもの（要る幅より広くてよい: 引数の正規化が下位を取る）
    value, determined = entry_value_in_storage(whole, X0, 64, lower, 32, big_endian)
    assert determined == 32 and value is whole and _evaluate(value, WIDE) & 0xFFFFFFFF == LOWER
    value, determined = entry_value_in_storage(whole, X0, 64, X0, 64, big_endian)
    assert determined == 64 and value is whole


@BYTE_ORDERS
def test_a_parameter_above_the_low_end_of_the_storage_is_not_its_value(big_endian):
    upper, lower = _halves(big_endian)
    half = Expression.parameter("p", 0, size=4, storage_info=upper)
    assert entry_value_in_storage(half, upper, 32, X0, 64, big_endian) is None
    low = Expression.parameter("p", 0, size=4, storage_info=lower)
    value, determined = entry_value_in_storage(low, lower, 32, X0, 64, big_endian)
    assert value is low and determined == 32


# ---------------------------------------------------------------------------
# 1. live-in の引数: 生成元から CalleeBinding・callee の parameter の置き換えまで
# ---------------------------------------------------------------------------


def _live_in(target_storage, callee_parameter, caller_parameters, big_endian):
    return call_paths._impl__recover_unmodified_live_in_argument(
        [], target_storage, _call_tracer(big_endian), caller_parameters, callee_parameter
    )


@BYTE_ORDERS
def test_a_live_in_argument_in_the_upper_half_is_the_upper_bits(big_endian):
    """修正前: 上位 32 bit を受ける呼び出しに p の下位 32 bit（1）が渡った。"""

    upper, _ = _halves(big_endian)
    callee_parameter = _descriptor("v", 0, upper, size=4, data_type="int")
    arg = _live_in(upper, callee_parameter, [_descriptor(**OWNER)], big_endian)
    assert arg is not None and arg.size == 4 and _evaluate(arg, WIDE) == UPPER
    assert _evaluate(_import_into_callee(arg, callee_parameter, big_endian), WIDE) == UPPER


@BYTE_ORDERS
def test_a_live_in_argument_in_the_lower_half_is_the_lower_bits(big_endian):
    _, lower = _halves(big_endian)
    callee_parameter = _descriptor("v", 0, lower, size=4, data_type="int")
    arg = _live_in(lower, callee_parameter, [_descriptor(**OWNER)], big_endian)
    assert arg is not None and _evaluate(arg, WIDE) & 0xFFFFFFFF == LOWER
    assert _evaluate(_import_into_callee(arg, callee_parameter, big_endian), WIDE) == LOWER


@BYTE_ORDERS
def test_a_full_width_live_in_argument_is_the_parameter(big_endian):
    callee_parameter = _descriptor("v", 0, X0)
    arg = _live_in(X0, callee_parameter, [_descriptor(**OWNER)], big_endian)
    assert arg.expr_type is ExpressionType.PARAMETER and arg.size == 8
    assert arg.call_argument_width_evidence is None
    assert _evaluate(_import_into_callee(arg, callee_parameter, big_endian), WIDE) == WIDE


@BYTE_ORDERS
def test_a_live_in_parameter_in_the_upper_half_is_not_the_low_bits_of_a_wide_argument(big_endian):
    """修正前: caller の parameter が x0 の上位 32 bit にあるのに、x0 の引数の下位 32 bit（部分的な幅）として渡った。"""

    upper, _ = _halves(big_endian)
    caller = [_descriptor("p", 0, upper, size=4, data_type="int", **OWNER)]
    callee_parameter = _descriptor("v", 0, X0, data_type="undefined8")
    assert _live_in(X0, callee_parameter, caller, big_endian) is None


@BYTE_ORDERS
def test_a_live_in_parameter_in_the_lower_half_determines_only_the_low_bits(big_endian):
    _, lower = _halves(big_endian)
    caller = [_descriptor("p", 0, lower, size=4, data_type="int", **OWNER)]
    callee_parameter = _descriptor("v", 0, X0, data_type="undefined8")
    arg = _live_in(X0, callee_parameter, caller, big_endian)
    assert arg is not None and arg.size == 4
    evidence = arg.call_argument_width_evidence
    assert evidence is not None and evidence.source_bits == 32 and evidence.target_bits == 64
    # callee が下位 32 bit だけを読むなら caller の値。64 bit 全体は caller が決めていないので拒否
    callee_low = _register("w0", base="x0", size=4, byte_offset=4 if big_endian else 0)
    binding = CalleeBinding.for_arguments([callee_parameter], [arg], big_endian=big_endian)
    low_node = Expression.parameter("v", 0, size=4, storage_info=callee_low)
    assert binding.resolve(low_node) is not None
    with pytest.raises(CallBoundaryRefused):
        binding.resolve(Expression.parameter("v", 0, size=8, storage_info=X0))


def test_a_live_in_register_piece_without_a_byte_order_is_not_recovered():
    callee_parameter = _descriptor("v", 0, X0_SECOND, size=4, data_type="int")
    assert _live_in(X0_SECOND, callee_parameter, [_descriptor(**OWNER)], None) is None


def test_the_descriptor_expression_is_always_the_whole_parameter():
    """review 8 で足した `size`（幅だけで下位の bit を取る）は撤去した。"""

    whole = call_argument._impl__parameter_expression_from_descriptor(_descriptor(**OWNER))
    assert whole.expr_type is ExpressionType.PARAMETER and whole.size == 8 and whole.storage_info == X0
    with pytest.raises(TypeError):
        call_argument._impl__parameter_expression_from_descriptor(_descriptor(**OWNER), size=4)


# ---------------------------------------------------------------------------
# 2. 呼び出しの入力: parameter の値を運ぶ入力だけを引数にする
# ---------------------------------------------------------------------------


class _Input:
    def __init__(self, storage):
        self.storage = storage


class _CallOp:
    def __init__(self, *storages):
        self._inputs = [_Input(None)] + [_Input(storage) for storage in storages]

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]


A, B = Expression.constant(0xA, size=4), Expression.constant(0xB, size=8)


@BYTE_ORDERS
def test_an_input_in_the_upper_half_is_not_selected_as_the_parameter_value(big_endian):
    """修正前: x0 の上位 32 bit にある入力が、x0 の parameter の値（下位の bit）として選ばれた。"""

    upper, lower = _halves(big_endian)
    callee = [_descriptor("v", 0, X0)]
    select = call_argument._impl__select_explicit_call_arguments_by_input_storage
    assert select(_CallOp(upper, X1), _call_tracer(big_endian), callee, [A, B]) is None
    assert select(_CallOp(lower, X1), _call_tracer(big_endian), callee, [A, B]) == [A]
    assert select(_CallOp(X0, X1), _call_tracer(big_endian), callee, [B, A]) == [B]


@BYTE_ORDERS
def test_a_storage_window_needs_inputs_that_carry_the_parameter_values(big_endian):
    upper, lower = _halves(big_endian)
    callee = [_descriptor("v", 0, X0)]
    window = call_argument._impl__explicit_call_argument_window_matches_storage
    assert not window([upper], [A], [X0], big_endian=big_endian)
    assert window([lower], [A], [X0], big_endian=big_endian)
    # あいまいさの判定（複数の窓が当たれば選ばない）は位置を問わない包含で数える
    assert window([upper], [A], [X0], value_position=False)
    select = call_argument._impl__select_explicit_call_arguments_by_storage_window
    assert select(_CallOp(X1, upper), _call_tracer(big_endian), callee, [B, A]) is None
    assert select(_CallOp(X1, lower), _call_tracer(big_endian), callee, [B, A]) == [A]


@BYTE_ORDERS
def test_a_positional_input_in_the_upper_half_is_not_the_parameter_value(big_endian):
    upper, lower = _halves(big_endian)
    callee = [_descriptor("v", 0, X0)]
    aligned = call_argument._impl__select_aligned_explicit_call_arguments
    assert aligned(_CallOp(upper), _call_tracer(big_endian), [], callee, [A]) is None
    assert aligned(_CallOp(lower), _call_tracer(big_endian), [], callee, [A]) == [A]
    assert aligned(_CallOp(X0), _call_tracer(big_endian), [], callee, [B]) == [B]
    # 別の記憶域（定数など）の入力は decompiler の並べた引数として位置で対応させる
    assert aligned(_CallOp(X1), _call_tracer(big_endian), [], callee, [B]) == [B]


def test_a_positional_register_piece_without_a_byte_order_is_not_the_parameter_value():
    callee = [_descriptor("v", 0, X0)]
    aligned = call_argument._impl__select_aligned_explicit_call_arguments
    assert aligned(_CallOp(X0_FIRST), _call_tracer(None), [], callee, [A]) is None


# ---------------------------------------------------------------------------
# 3, 4. tracer: 記憶域の幅の変換と束縛値
# ---------------------------------------------------------------------------


class _EmptyLocalMap:
    def getSymbols(self):
        return []


class _EmptyHighFunction:
    def getLocalSymbolMap(self):
        return _EmptyLocalMap()


def _tracer(big_endian, **bound):
    program = Mock()
    if big_endian is None:
        program.getLanguage.return_value = None
    else:
        program.getLanguage.return_value.isBigEndian.return_value = big_endian
    tracer = PcodeTracer(program, _EmptyHighFunction(), debug=False, **bound)
    tracer._parameter_descriptors = [
        ParameterStorageDescriptor(
            name="p", index=0, size_bytes=8, is_signed=True, data_type="long", data_type_obj=None, storage_info=X0
        )
    ]
    return tracer


@BYTE_ORDERS
def test_a_register_piece_of_a_parameter_is_its_bits_by_byte_order(big_endian):
    """修正前: 番地の順の位置を `SUBPIECE` の位置にした（big endian で上位と下位が入れ替わる）。"""

    upper, lower = _halves(big_endian)
    tracer = _tracer(big_endian)
    high = tracer._resolve_storage_backed_parameter_expression(upper)
    low = tracer._resolve_storage_backed_parameter_expression(lower)
    assert high.size == 4 and high.storage_info == upper and _evaluate(high, WIDE) == UPPER
    assert low.size == 4 and low.storage_info == lower and _evaluate(low, WIDE) == LOWER
    whole = tracer._resolve_storage_backed_parameter_expression(X0)
    assert whole.expr_type is ExpressionType.PARAMETER and whole.size == 8


@BYTE_ORDERS
def test_a_register_wider_than_the_parameter_is_not_an_extension_of_it(big_endian):
    """修正前: x0 の読み出しを 32 bit の parameter の `INT_SEXT` / `INT_ZEXT` にした（上位の bit を作る）。"""

    _, lower = _halves(big_endian)
    tracer = _tracer(big_endian)
    tracer._parameter_descriptors = [
        ParameterStorageDescriptor(
            name="p", index=0, size_bytes=4, is_signed=False, data_type="uint", data_type_obj=None, storage_info=lower
        )
    ]
    assert tracer._resolve_storage_backed_parameter_expression(X0) is None
    assert tracer._resolve_storage_backed_parameter_expression(lower).expr_type is ExpressionType.PARAMETER


@BYTE_ORDERS
def test_a_bound_value_read_through_a_register_piece_is_its_bits(big_endian):
    """修正前: parameter の幅の束縛値（下位の bit を取った値）に varnode の記憶域を付けた: 上位の varnode も 1。"""

    upper, lower = _halves(big_endian)
    tracer = _tracer(big_endian, bound_parameter_values={0: Expression.constant(WIDE, size=8)})
    resolve = tracer._resolve_bound_parameter_expression
    common = dict(name="p", index=0, data_type="long", data_type_obj=None)
    high = resolve(size_bytes=4, storage_info=upper, **common)
    low = resolve(size_bytes=4, storage_info=lower, **common)
    whole = resolve(size_bytes=8, storage_info=X0, **common)
    assert high.size == 4 and high.storage_info == upper and _evaluate(high, 0) == UPPER
    assert low.size == 4 and low.storage_info == lower and _evaluate(low, 0) == LOWER
    assert whole.expr_type is ExpressionType.CONSTANT and whole.value == WIDE and whole.storage_info == X0


def test_a_bound_value_read_through_a_register_piece_without_a_byte_order_is_not_bound():
    tracer = _tracer(None, bound_parameter_values={0: Expression.constant(WIDE, size=8)})
    assert (
        tracer._resolve_bound_parameter_expression(
            name="p", index=0, data_type="long", data_type_obj=None, size_bytes=4, storage_info=X0_SECOND
        )
        is None
    )


@BYTE_ORDERS
def test_a_bound_value_narrower_than_the_parameter_is_not_extended(big_endian):
    """修正前: 32 bit の束縛値を `INT_SEXT` で 64 bit の parameter にした（caller の決めていない上位の bit）。"""

    tracer = _tracer(big_endian, bound_parameter_values={0: Expression.constant(0xFFFFFFFF, size=4)})
    assert (
        tracer._resolve_bound_parameter_expression(
            name="p", index=0, data_type="long", data_type_obj=None, size_bytes=8, storage_info=X0
        )
        is None
    )
    # 束縛しない parameter は parameter の node のまま（境界の置き換えで caller の値になる）
    fallback = tracer._resolve_storage_backed_parameter_expression(X0)
    assert fallback.expr_type is ExpressionType.PARAMETER and fallback.size == 8


@BYTE_ORDERS
def test_a_bound_value_wider_than_the_parameter_is_its_low_bits(big_endian):
    tracer = _tracer(big_endian, bound_parameter_values={0: Expression.constant(WIDE, size=16)})
    resolved = tracer._resolve_bound_parameter_expression(
        name="p", index=0, data_type="long", data_type_obj=None, size_bytes=8, storage_info=X0
    )
    assert resolved.size == 8 and _evaluate(resolved, 0) == WIDE
