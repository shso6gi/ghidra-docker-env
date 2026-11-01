# -*- coding: utf-8 -*-
"""Issue #281 review 7: 関数をまたぐ値の bit の範囲と、記憶域への書き込みの「重ならない」の根拠。

1. 幅・bit の位置・符号: callee の parameter の一部（32 bit）を表す node を、64 bit の引数で丸ごと置き換えていた。
   0x100000001 の下位 32 bit は 1 だが、「下位 32 bit == 1」が「64 bit 全体 == 1」に変わり得た。引数より広い
   parameter の上位（SEXT / ZEXT で補った bit）も、引数が決めているように扱っていた。
   → `CalleeBinding.resolve` が node の bit の範囲を決め、引数の決めている bit（`known_bits`）に収まるときだけ
   その範囲の値に置き換える。決められなければ拒否（`callee_parameter_bits_unknown`）。条件 `x == v` による
   同じ関数の中の置き換え（`_apply_condition_parameter_replacements`）も、x と同じ bit の node だけを置き換える。
2. 書き込み先の分からない STORE・呼び出し: stack の引数の選択・live-in の判定は、書き込み先を特定できない
   STORE を「重ならない」と扱い、上書き前の値を使い得た。stack の load の回復とも扱いが違った。
   → `_op_write_relation`（`MemoryRelation`: 重ならないと証明できた `DISJOINT` と、分からない `UNKNOWN` を分ける）
   を引数の選択・live-in の判定の唯一の owner にし、load の回復も同じ規則（STORE の書き込み先は pointer の値が
   指す場所で、pointer を置いた stack の範囲ではない）にする。

ここの例は production の関数を合成入力で実行したもの（実 binary の判定まで届くかは未確認）。
"""

from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.analysis.bounded_refinement import BoundedCallRefiner
from scripts.function_tracer_pcode.analysis.effects import call_argument
from scripts.function_tracer_pcode.analysis.effects.call_boundary import (
    REFUSED_CALLEE_PARAMETER_BITS,
    CallBoundaryRefused,
    CalleeBinding,
    CallSite,
    CalleeTimeline,
    import_callee_expression,
)
from scripts.function_tracer_pcode.analysis.effects.summary import CallArgumentWidthEvidence
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
)
from scripts.function_tracer_pcode.core.program_order import ProgramOrder
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.tests.unit._program_order_fakes import FakeOp, fake_cfg

MemoryRelation = call_argument.MemoryRelation


def _register(name, *, byte_offset=0, size=8, base="a0"):
    return StorageInfo(
        is_register=True,
        space_name="register",
        register_name=name,
        size=size,
        size_bits=size * 8,
        base_register_name=base,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=byte_offset * 8,
    )


A0 = _register("a0")
#: 番地の順で a0 の先頭 4 byte / 後ろ 4 byte（little endian では下位 / 上位、big endian では上位 / 下位）
A0_FIRST = _register("a0_first", byte_offset=0, size=4)
A0_SECOND = _register("a0_second", byte_offset=4, size=4)


def _descriptor(storage=A0, *, size=8, data_type="long"):
    return {"name": "param_1", "index": 0, "size": size, "data_type": data_type, "storage": storage}


def _node(storage, size):
    return Expression.parameter("param_1", index=0, size=size, storage_info=storage)


def _import(expr, binding):
    return import_callee_expression(expr, CallSite(None), CalleeTimeline.unknown(), binding=binding)


def _evaluate(expr):
    """定数と SUBPIECE / INT_EQUAL / INT_ZEXT だけの式の値（置き換えの結果の意味を確かめる）。"""

    if expr.expr_type is ExpressionType.CONSTANT:
        return int(expr.value) & ((1 << (8 * expr.size)) - 1)
    if expr.operator == "SUBPIECE":
        source, offset = expr.operands
        return (_evaluate(source) >> (8 * int(offset.value))) & ((1 << (8 * expr.size)) - 1)
    if expr.operator == "INT_EQUAL":
        return int(_evaluate(expr.operands[0]) == _evaluate(expr.operands[1]))
    if expr.operator == "INT_ZEXT":
        return _evaluate(expr.operands[0])
    raise AssertionError(expr.operator)


WIDE = Expression.constant(0x100000001, size=8)


# ---------------------------------------------------------------------------
# 1. parameter の bit の範囲
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("big_endian, low_storage", [(False, A0_FIRST), (True, A0_SECOND)])
def test_the_low_half_of_a_wide_argument_is_its_low_32_bits(big_endian, low_storage):
    """修正前: 32 bit の node を 64 bit の引数 0x100000001 で丸ごと置き換え、「下位 32 bit == 1」が「全体 == 1」（偽）になった。"""

    binding = CalleeBinding.for_arguments([_descriptor()], [WIDE], big_endian=big_endian)
    low_is_one = Expression.binary_op("INT_EQUAL", _node(low_storage, 4), Expression.constant(1, size=4))
    imported = _import(low_is_one, binding)
    assert imported.operands[0].size == 4
    assert _evaluate(imported) == 1


@pytest.mark.parametrize("big_endian, high_storage", [(False, A0_SECOND), (True, A0_FIRST)])
def test_the_high_half_of_a_wide_argument_is_its_high_32_bits(big_endian, high_storage):
    binding = CalleeBinding.for_arguments([_descriptor()], [Expression.constant(0x200000001, size=8)], big_endian=big_endian)
    imported = _import(_node(high_storage, 4), binding)
    assert imported.size == 4 and _evaluate(imported) == 2


def test_a_register_fragment_without_a_byte_order_is_refused():
    """番地の順の位置を significance の位置へ直せない（byte order が分からない）: 範囲を決められないので拒否する。"""

    binding = CalleeBinding.for_arguments([_descriptor()], [WIDE])
    with pytest.raises(CallBoundaryRefused) as raised:
        _import(_node(A0_SECOND, 4), binding)
    assert raised.value.reason == REFUSED_CALLEE_PARAMETER_BITS


def test_a_node_with_the_parameter_storage_and_width_is_the_argument_itself():
    binding = CalleeBinding.for_arguments([_descriptor()], [WIDE])
    assert _import(_node(A0, 8), binding) is binding.parameters[0].value


def test_a_storage_less_node_narrower_than_the_argument_is_its_low_bits():
    """記憶域の無い `PARAMETER` は parameter そのもの: 4 byte の node は 8 byte の引数の下位 4 byte。"""

    binding = CalleeBinding.for_arguments([_descriptor()], [WIDE])
    imported = _import(Expression.parameter("param_1", index=0, size=4), binding)
    assert imported.operator == "SUBPIECE" and _evaluate(imported) == 1


def test_the_extended_bits_of_a_narrow_argument_are_not_the_argument():
    """32 bit の引数を 64 bit の parameter へ渡す。上位 32 bit は caller が渡す register の値と限らない（SEXT は推測）。

    修正前: SEXT した 64 bit の値で 64 bit の node を置き換えた（符号の拡張の向きは引数の元の型で決まる）。
    """

    narrow = Expression.parameter("x", index=0, size=4)
    binding = CalleeBinding.for_arguments([_descriptor()], [narrow], big_endian=False)
    assert binding.parameters[0].known_bits == 32
    with pytest.raises(CallBoundaryRefused) as raised:
        _import(_node(A0, 8), binding)
    assert raised.value.reason == REFUSED_CALLEE_PARAMETER_BITS
    # 下位 32 bit だけを読む node は引数そのもの（正しく決まる場合は保つ）
    low = Expression.binary_op("SUBPIECE", _node(A0, 8), Expression.constant(0, size=8))
    low.size = 4
    imported = _import(low, binding)
    assert imported.operator == "SUBPIECE" and imported.size == 4 and imported.operands[1].value == 0
    assert imported.operands[0].operator == "INT_SEXT" and imported.operands[0].operands[0].name == "x"
    # 上位の bit を読む部分は拒否する
    high = Expression.binary_op("SUBPIECE", _node(A0, 8), Expression.constant(4, size=8))
    high.size = 4
    with pytest.raises(CallBoundaryRefused):
        _import(high, binding)


@pytest.mark.parametrize("big_endian, low, high", [(False, A0_FIRST, A0_SECOND), (True, A0_SECOND, A0_FIRST)])
def test_without_parameter_storage_only_the_low_end_of_the_register_with_the_value_width_binds(big_endian, low, high):
    """effect 要約の束縛は parameter の記憶域を持たない（`LocationBaseRef` だけ）。register の下位の端にある、値と
    同じ幅の node だけを値とする（実 binary: testCollision4 の w0 / x1 / w2）。それ以外は位置が決まらないので拒否する。"""

    from scripts.function_tracer_pcode.core import LocationBaseRef

    refs = [LocationBaseRef.parameter("param_1", index=0)]
    binding = CalleeBinding.for_arguments(refs, [Expression.constant(0x2_0000_0001, size=4)], big_endian=big_endian)
    assert _import(_node(low, 4), binding) is binding.parameters[0].value
    with pytest.raises(CallBoundaryRefused):
        _import(_node(high, 4), binding)
    with pytest.raises(CallBoundaryRefused):
        _import(_node(A0, 8), binding)
    unknown_order = CalleeBinding.for_arguments(refs, [Expression.constant(1, size=4)])
    with pytest.raises(CallBoundaryRefused):
        _import(_node(low, 4), unknown_order)


def test_a_partial_width_argument_binds_only_its_source_bits():
    evidence = CallArgumentWidthEvidence(source_bits=32, target_bits=64)
    partial = Expression.parameter("x", index=0, size=8).clone_with(call_argument_width_evidence=evidence)
    binding = CalleeBinding.for_arguments([_descriptor()], [partial])
    assert binding.parameters[0].known_bits == 32
    with pytest.raises(CallBoundaryRefused):
        _import(_node(A0, 8), binding)


def test_a_stack_slot_wider_than_the_declared_value_is_refused():
    """stack の 8 byte の slot に int（4 byte）の parameter。slot 全体を表す node の上位は引数の値ではない。"""

    slot = StorageInfo(is_register=False, space_name="stack", space_id=0x1B, offset=8, size=8, size_bits=64)
    binding = CalleeBinding.for_arguments([_descriptor(slot, size=4, data_type="int")], [Expression.constant(7, size=4)])
    with pytest.raises(CallBoundaryRefused):
        _import(_node(slot, 8), binding)
    assert _evaluate(_import(_node(slot, 4), binding)) == 7


def test_bounded_refinement_leaves_the_width_to_the_binding():
    """修正前: deferred call の引数を先に SEXT しており、補った上位の bit を束縛が「引数が決めている」と読んだ。"""

    narrow = Expression.parameter("x", index=0, size=4)
    deferred = SimpleNamespace(
        arguments=[narrow],
        deferred_call_ref=SimpleNamespace(pcode_op_ref=SimpleNamespace(mnemonic="CALL")),
    )
    refiner = BoundedCallRefiner.__new__(BoundedCallRefiner)
    aligned = refiner._align_deferred_arguments_to_callee(deferred, [], [_descriptor()])
    assert aligned == [narrow]


# 同じ関数の中の置き換え（条件 `x == v`）


def test_a_condition_on_the_low_half_does_not_replace_the_whole_parameter():
    """条件「下位 32 bit == 1」から 64 bit の parameter を 1 にしない（修正前は key が当たれば幅に関係なく置き換えた）。"""

    parameters = [_descriptor()]
    low = _node(A0_FIRST, 4)
    whole = _node(A0, 8)
    condition = Condition(Expression.binary_op("INT_EQUAL", low, Expression.constant(1, size=4)), False)
    assert call_argument._impl__apply_condition_parameter_replacements(whole, [condition], parameters) is whole
    replaced = call_argument._impl__apply_condition_parameter_replacements(low, [condition], parameters)
    assert replaced.expr_type is ExpressionType.CONSTANT and replaced.value == 1


def test_a_condition_on_one_half_does_not_replace_the_other_half():
    parameters = [_descriptor()]
    condition = Condition(Expression.binary_op("INT_EQUAL", _node(A0_FIRST, 4), Expression.constant(1, size=4)), False)
    other = _node(A0_SECOND, 4)
    assert call_argument._impl__apply_condition_parameter_replacements(other, [condition], parameters) is other


def test_a_partly_overlapping_memory_storage_is_not_the_same_storage():
    """記憶域の同一性（引数の対応の scoring）は、一部だけ重なる memory を同じ場所としない（review 6 の rank の変更の後始末）。"""

    whole = StorageInfo(is_register=False, space_name="stack", space_id=0x1B, offset=8, size=8)
    half = StorageInfo(is_register=False, space_name="stack", space_id=0x1B, offset=8, size=4)
    assert call_argument._impl__storage_infos_match(whole, whole)
    assert not call_argument._impl__storage_infos_match(whole, half)


# ---------------------------------------------------------------------------
# 2. 記憶域への書き込み
# ---------------------------------------------------------------------------

STACK_SPACE_ID = 0x1B


class _Space:
    def __init__(self, name, space_id):
        self._name = name
        self._id = space_id

    def getName(self):
        return self._name

    def getSpaceID(self):
        return self._id


STACK = _Space("stack", STACK_SPACE_ID)
RAM = _Space("ram", 0x2)
REGISTER = _Space("register", 0x4)


class _Varnode:
    def __init__(self, space, offset, size, label=None):
        self.space = space
        self.offset = offset
        self.size = size
        self.label = label

    def getAddress(self):
        return SimpleNamespace(getAddressSpace=lambda: self.space)

    def getOffset(self):
        return self.offset

    def getSize(self):
        return self.size


def _value(label, size=8):
    return _Varnode(REGISTER, 0x100, size, label)


class _Op:
    def __init__(self, mnemonic, inputs=(), output=None):
        self.mnemonic = mnemonic
        self.inputs = list(inputs)
        self.output = output

    def getMnemonic(self):
        return self.mnemonic

    def getNumInputs(self):
        return len(self.inputs)

    def getInput(self, index):
        return self.inputs[index]

    def getOutput(self):
        return self.output


SLOT = StorageInfo(is_register=False, space_name="stack", space_id=STACK_SPACE_ID, offset=-16, size=8, size_bits=64)


def _tracer():
    def storage_of(varnode):
        if getattr(varnode, "space", None) is REGISTER:
            return _register(f"r{varnode.offset}", base=f"r{varnode.offset}")
        return None

    return SimpleNamespace(_get_storage_info_from_varnode=storage_of)


@pytest.fixture
def _values(monkeypatch):
    monkeypatch.setattr(
        call_argument,
        "_resolve_call_argument_expression",
        lambda varnode, *a, **k: Expression.variable(varnode.label, size=varnode.size),
    )


def _write_slot(label):
    return _Op("COPY", [_value(label)], output=_Varnode(STACK, -16, 8, label))


def _store_through(pointer, label="stored"):
    return _Op("STORE", [_Varnode(_Space("const", 0), 0, 8), pointer, _value(label)])


def _select(ops):
    return call_argument._impl__select_best_storage_candidate(ops, SLOT, _tracer(), [], {})


def test_an_unknown_store_after_the_argument_write_makes_it_unknown(_values):
    """修正前: 書き込み先の分からない STORE を「重ならない」とし、上書き前の値を stack の引数にした。"""

    assert _select([_write_slot("before"), _store_through(_value("ptr"))]) is None


def test_an_unknown_store_is_a_write_for_the_live_in_check():
    """修正前: live-in（呼び出しまで書き込みが無い）の判定で、書き込み先の分からない STORE を数えなかった。"""

    assert call_argument._impl__path_writes_storage([_store_through(_value("ptr"))], SLOT, _tracer())


def test_a_store_through_a_pointer_kept_in_the_slot_does_not_write_the_slot(_values):
    """STORE の入力 1 が stack の varnode でも、それは pointer を置いた場所で、書き込み先ではない。

    修正前: pointer の変数が引数の slot と同じ範囲にあると、`*ptr = v` の v を slot の値（引数）にした。
    """

    assert _select([_write_slot("pointer"), _store_through(_Varnode(STACK, -16, 8, "pointer"))]) is None


def test_an_earlier_call_makes_a_stack_argument_unknown(_values):
    """呼び出しは caller の frame の番地が渡っていれば stack の範囲を書き得る（load の回復と同じ扱い）。"""

    call = _Op("CALL", [_value("target")], output=_Varnode(REGISTER, 0x200, 8, "ret"))
    assert _select([_write_slot("before"), call]) is None


def test_a_write_to_a_disjoint_slot_keeps_the_argument(_values):
    """重ならないと分かっている書き込み（別の stack の範囲・register）は値を変えない（正しく決まる場合は保つ）。"""

    other_slot = _Op("COPY", [_value("other")], output=_Varnode(STACK, -8, 8, "other"))
    register = _Op("INT_ADD", [_value("a"), _value("b")], output=_Varnode(REGISTER, 0x300, 8, "sum"))
    selected = _select([_write_slot("argument"), other_slot, register])
    assert selected is not None and selected.name == "argument"


def test_a_store_does_not_write_a_register_argument(_values):
    x1 = _register("r1", base="r1")
    write = _Op("COPY", [_value("x")], output=_Varnode(REGISTER, 1, 8, "x"))
    selected = call_argument._impl__select_best_storage_candidate(
        [write, _store_through(_value("ptr"))], x1, _tracer(), [], {}
    )
    assert selected is not None and selected.name == "x"


def test_relation_of_an_unreadable_space_is_unknown_not_disjoint():
    unreadable = SimpleNamespace(getAddress=lambda: SimpleNamespace(getAddressSpace=lambda: None), getSize=lambda: 8)
    assert call_argument._impl__stack_varnode_storage_rank(unreadable, SLOT) == MemoryRelation.UNKNOWN
    assert call_argument._impl__stack_varnode_storage_rank(_Varnode(RAM, -16, 8), SLOT) == MemoryRelation.DISJOINT


# stack の load の回復: 同じ pointer を通した store → load


class _OrderedOp(FakeOp):
    def __init__(self, block, position, mnemonic, inputs=(), output=None):
        super().__init__(block, position, mnemonic=mnemonic)
        self._inputs = list(inputs)
        self._output = output

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]

    def getOutput(self):
        return self._output


POINTER_SLOT = _Varnode(STACK, -32, 8, "ptr")


def _recover(monkeypatch, build):
    successors = {0: [1], 1: []}
    _high, blocks = fake_cfg(successors)
    ops, load = build(blocks)
    order = ProgramOrder(successors)
    tracer = SimpleNamespace(program_order=lambda: order, get_all_pcode_ops=lambda: list(ops) + [load])
    monkeypatch.setattr(
        call_argument,
        "_recover_parameter_expression_from_varnode",
        lambda varnode, *a, **k: Expression.variable(varnode.label, size=varnode.getSize()),
    )
    return call_argument._impl__recover_parameter_from_stack_load(load, tracer, [], 0, set())


def _load(block, position=0, size=8):
    return _OrderedOp(block, position, "LOAD", [None, POINTER_SLOT], output=_value("loaded", size))


def test_a_store_through_the_same_pointer_is_the_loaded_value(monkeypatch):
    def build(blocks):
        return [_OrderedOp(blocks[0], 0, "STORE", [None, POINTER_SLOT, _value("v")])], _load(blocks[1])

    recovered = _recover(monkeypatch, build)
    assert recovered is not None and recovered.name == "v"


def test_the_pointer_variable_write_is_not_the_pointee_value(monkeypatch):
    """修正前: LOAD の入力 1 の stack の範囲（pointer の変数）を読む番地とみなし、`ptr = &x` の &x を `*ptr` の値にした。"""

    def build(blocks):
        return [_OrderedOp(blocks[0], 0, "COPY", [_value("address_of_x")], output=POINTER_SLOT)], _load(blocks[1])

    assert _recover(monkeypatch, build) is None


@pytest.mark.parametrize(
    "writer",
    [
        lambda block: _OrderedOp(block, 1, "COPY", [_value("w")], output=_Varnode(STACK, -8, 8)),
        lambda block: _OrderedOp(block, 1, "COPY", [_value("w")], output=_Varnode(RAM, 0x4000, 8)),
        lambda block: _OrderedOp(block, 1, "COPY", [_value("p2")], output=POINTER_SLOT),
        lambda block: _OrderedOp(block, 1, "STORE", [None, _value("q"), _value("w")]),
        lambda block: _OrderedOp(block, 1, "CALL", [_value("target")]),
    ],
    ids=["other_stack_slot", "global", "pointer_changed", "other_store", "call"],
)
def test_a_memory_write_between_store_and_load_makes_the_load_unknown(monkeypatch, writer):
    """pointer の指す先は分からないので、間の memory の書き込みはどれも重なりを否定できない。"""

    def build(blocks):
        store = _OrderedOp(blocks[0], 0, "STORE", [None, POINTER_SLOT, _value("v")])
        return [store, writer(blocks[0])], _load(blocks[1])

    assert _recover(monkeypatch, build) is None


def test_a_register_write_between_store_and_load_keeps_the_value(monkeypatch):
    def build(blocks):
        store = _OrderedOp(blocks[0], 0, "STORE", [None, POINTER_SLOT, _value("v")])
        add = _OrderedOp(blocks[0], 1, "INT_ADD", [_value("a"), _value("b")], output=_value("sum"))
        return [store, add], _load(blocks[1])

    recovered = _recover(monkeypatch, build)
    assert recovered is not None and recovered.name == "v"


def test_a_store_of_another_width_through_the_same_pointer_is_not_the_loaded_value(monkeypatch):
    def build(blocks):
        return [_OrderedOp(blocks[0], 0, "STORE", [None, POINTER_SLOT, _value("v", 4)])], _load(blocks[1])

    assert _recover(monkeypatch, build) is None
