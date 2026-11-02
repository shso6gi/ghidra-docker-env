# -*- coding: utf-8 -*-
"""Issue #281 review 8: node がどの関数のどの parameter の入口の値の、どの bit を表すか。

1. 条件 `p == 0x1000` の下で `MEM[p]`（位置の基底が p の読み出し）が 0x1000 と読まれた。p の出口の状態の読み出し・
   所有者の違う同じ index の parameter も同じ。置き換えの表を node の identity key（index・記憶域・位置の基底・
   descriptor）で引いていたため。引数の正規化（`*p` が p に化ける）・条件の下の parameter の等しさ（`-p == q` や
   `*p == q` から `*p` と `*q` を同じ場所とする）も同じ原因。
   → `parameter_entry` が node の主張（入口の値か・所有者・bit）の唯一の owner。置き換え・正規化・位置の基底・
   等しさは、入口の値を表す node だけを parameter として扱う。
2. varnode から回復した parameter の一部（64 bit の parameter の上位 32 bit）が、parameter の記憶域全体を持つ
   32 bit の node になり、下位 32 bit と読まれた（0x0000000200000001 の上位は 2 だが 1 になり得た）。
   → 回復は varnode の記憶域から位置を決め、`SUBPIECE(parameter, 位置)` にする。記憶域の無い node は parameter の
   値そのもの（幅が違えば位置を決めない）。
3. 出力の記憶域を作れない op を register と重ならないとし、その前の値を引数に使い得た。名前の無い register の
   範囲・Ghidra の `space_id` と名前からの合成値の比較も「重ならない」になっていた。
   → 重ならないと言えるのは証明できたときだけ（`MemoryRelation.UNKNOWN` を分ける）。callee の stack で渡る
   parameter の記憶域は callee の frame にあり、caller の op と比べられないので、その引数は分からない。

ここの例は production の関数を合成入力で実行したもの（実 binary の判定まで届くかは未確認）。
"""

from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.analysis.effects import call_argument
from scripts.function_tracer_pcode.analysis.effects.call_boundary import (
    REFUSED_CALLEE_FOREIGN_PARAMETER,
    CallBoundaryRefused,
    CalleeBinding,
    CallSite,
    CalleeTimeline,
    import_callee_expression,
)
from scripts.function_tracer_pcode.analysis.effects.condition_algebra import (
    _impl__expressions_equivalent_under_conditions as expressions_equivalent_under_conditions,
)
from scripts.function_tracer_pcode.analysis.effects.location import _impl_locations_match as locations_match
from scripts.function_tracer_pcode.analysis.effects.parameter_entry import (
    entry_claim,
    same_entry_bits,
    whole_parameter_descriptor,
)
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    PostStateReadRef,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo

MemoryRelation = call_argument.MemoryRelation

OWNER = dict(owner_program_id=1, owner_entry_offset=0x1000)
OTHER_OWNER = dict(owner_program_id=1, owner_entry_offset=0x2000)


def _register(name, *, base, byte_offset=0, size=8, base_size=8):
    return StorageInfo(
        is_register=True,
        space_name="register",
        register_name=name,
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
X0_FIRST = _register("w0", base="x0", size=4)
X0_SECOND = _register("x0_second", base="x0", byte_offset=4, size=4)


def _descriptor(name="p", index=0, storage=X0, size=8, **owner):
    return {"name": name, "index": index, "size": size, "data_type": "long", "storage": storage, **owner}


PARAMETERS = [_descriptor("p", 0, X0, **OWNER), _descriptor("q", 1, X1, **OWNER)]


def _param(name="p", index=0, *, storage=X0, size=8, owner=OWNER):
    return Expression.parameter(
        name,
        index,
        size=size,
        storage_info=storage,
        runtime_ref=LocationBaseRef.parameter(name, index=index, **owner),
    )


def _location(name="p", index=0, size=8, owner=OWNER):
    return CanonicalLocation(base_ref=LocationBaseRef.parameter(name, index=index, **owner), offset=0, size=size)


def _load(name="p", index=0):
    """`*p`（位置の基底が p の、p の入口の値を番地にした読み出し）。"""

    return Expression.memory(_param(name, index), size=8, runtime_ref=_location(name, index))


def _poststate(name="p", index=0):
    """p の出口の状態の読み出し（`poststate_*` の変数: 位置の基底が p）。"""

    return Expression.variable("poststate_0_8", size=8, runtime_ref=PostStateReadRef(location=_location(name, index)))


def _const(value, size=8):
    return Expression.constant(value, size=size)


def _equal(left, right):
    return Condition(Expression.binary_op("INT_EQUAL", left, right), False)


# ---------------------------------------------------------------------------
# 1. 条件の下の置き換え: 入口の値を表す node だけ
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("source_storage", [None, X0], ids=["storage-less-p", "p-in-x0"])
@pytest.mark.parametrize(
    "node",
    [_load(), _poststate(), _param(owner=OTHER_OWNER)],
    ids=["load-of-p", "post-state-of-p", "parameter-of-another-function"],
)
def test_a_condition_on_p_does_not_make_other_values_equal_to_its_value(node, source_storage):
    """修正前: `p == 0x1000` の下で、`MEM[p]`・p の出口の状態・所有者の違う同じ index の parameter が 0x1000 と等しいとされた
    （review 7 の置き換えは幅と記憶域だけを揃えていた: 記憶域の無い p の条件は、記憶域の無い 8 byte の node すべてに当たった）。"""

    condition = _equal(_param(storage=source_storage), _const(0x1000))
    assert not expressions_equivalent_under_conditions(node, _const(0x1000), [condition], PARAMETERS)


def test_a_condition_on_p_makes_p_equal_to_its_value():
    """正しく決まる場合は保つ: p の入口の値（所有者の無い node も同じ関数の parameter）は 0x1000。"""

    condition = _equal(_param(), _const(0x1000))
    assert expressions_equivalent_under_conditions(_param(), _const(0x1000), [condition], PARAMETERS)
    unscoped = Expression.parameter("p", 0, size=8, storage_info=X0)
    assert expressions_equivalent_under_conditions(unscoped, _const(0x1000), [condition], PARAMETERS)


def test_a_condition_on_a_load_does_not_replace_the_pointer():
    """修正前: `MEM[p] == 5` から p を 5 にし得た（`MEM[p]` の key が p の key を含む）。"""

    condition = _equal(_load(), _const(5))
    assert not expressions_equivalent_under_conditions(_param(storage=None), _const(5), [condition], PARAMETERS)


def test_the_replacement_key_is_only_for_entry_values():
    assert entry_claim(_param()) is not None
    assert entry_claim(_load()) is None and entry_claim(_poststate()) is None
    assert not same_entry_bits(_param(owner=OTHER_OWNER), _param())
    assert same_entry_bits(Expression.parameter("p", 0, size=8, storage_info=X0), _param())


# 条件の下の parameter の等しさ（`*p` と `*q` を同じ場所とするか）


def _unscoped(name, index, **kwargs):
    return _param(name, index, owner={}, **kwargs)


@pytest.mark.parametrize(
    "condition",
    [
        _equal(Expression.unary_op("INT_2COMP", _unscoped("p", 0)), _unscoped("q", 1, storage=X1)),
        _equal(Expression.memory(_unscoped("p", 0), size=8, runtime_ref=_location("p", 0, owner={})), _unscoped("q", 1, storage=X1)),
        _equal(Expression.unary_op("INT_ZEXT", _unscoped("p", 0, size=4, storage=X0_FIRST)), _unscoped("q", 1, storage=X1)),
    ],
    ids=["negated-p-equals-q", "load-of-p-equals-q", "extended-p-equals-q"],
)
def test_only_equal_entry_values_make_two_pointers_alias(condition):
    """修正前: 片側の ZEXT / 2 の補数を外し、位置の基底が p の読み出しも p と読んで、`*p` と `*q` を同じ場所とした。"""

    assert not locations_match(_location("p", 0, owner={}), _location("q", 1, owner={}), [condition])


@pytest.mark.parametrize(
    "condition",
    [
        _equal(_param(), _param("q", 1, storage=X1)),
        _equal(
            Expression.unary_op("INT_ZEXT", _param(size=8)).clone_with(size=16),
            Expression.unary_op("INT_ZEXT", _param("q", 1, storage=X1, size=8)).clone_with(size=16),
        ),
    ],
    ids=["p-equals-q", "same-extension-on-both-sides"],
)
def test_equal_entry_values_make_two_pointers_alias(condition):
    """正しく決まる場合は保つ。所有者のある parameter も、位置の基底と同じ形の key で比べる（修正前は条件の側だけ
    所有者の無い key にしていたので、所有者のある位置とは比べられなかった）。"""

    assert locations_match(_location("p", 0), _location("q", 1), [condition])


# 引数の正規化・位置の基底


@pytest.mark.parametrize(
    "argument",
    [
        _load(),
        _poststate(),
        Expression.variable("x0_second", size=4, storage_info=X0_SECOND),
        Expression.variable("w0", size=4, storage_info=X0_FIRST),
    ],
    ids=["load-of-p", "post-state-of-p", "upper-half-register", "lower-half-register"],
)
def test_a_value_other_than_the_whole_entry_value_is_not_normalized_to_the_parameter(argument):
    """修正前: descriptor が引ければ式の種類・bit に関係なく引数を parameter にした（引数 `*p` が p になった）。"""

    assert call_argument._impl__normalize_call_argument_expression(argument, 0, PARAMETERS) is argument
    assert whole_parameter_descriptor(argument, PARAMETERS) is None


def test_the_whole_entry_value_of_a_register_is_normalized_to_the_parameter():
    """tracer は定義の無い register の varnode を ref の無い `VARIABLE` の葉にする: その register の入口の値。"""

    register_value = Expression.variable("x1", size=8, storage_info=X1)
    normalized = call_argument._impl__normalize_call_argument_expression(register_value, 1, PARAMETERS)
    assert normalized.expr_type is ExpressionType.PARAMETER and normalized.name == "q"


@pytest.mark.parametrize(
    "address",
    [_poststate(), Expression.variable("x0_second", size=4, storage_info=X0_SECOND)],
    ids=["post-state-of-p", "upper-half-register"],
)
def test_a_value_other_than_the_entry_value_of_p_is_not_the_address_p(address):
    """修正前: 番地の値が p の出口の状態や p の一部の bit でも、位置の基底を p（offset 0）にした: `*poststate` を `*p` と
    同じ場所とし得た。"""

    from scripts.function_tracer_pcode.analysis.effects.location import canonicalize_location

    rooted_at_p = _location("p", 0, owner={})  # 位置の基底は descriptor の名前と index（所有者を持たない）
    assert canonicalize_location(address, PARAMETERS, size=8) != rooted_at_p
    assert canonicalize_location(_param(), PARAMETERS, size=8) == rooted_at_p


# 生成元から利用先まで: caller が `*p` を渡す呼び出しの effect


class _Varnode:
    def __init__(self, key, size=8):
        self.key = key
        self._size = size

    def getSize(self):
        return self._size

    def getDef(self):
        return None

    def getHigh(self):
        return None


class _CallOp:
    def __init__(self):
        self._inputs = [_Varnode("target"), _Varnode("arg0"), _Varnode("out0")]

    def getMnemonic(self):
        return "CALL"

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]

    def getOutput(self):
        return None

    def getSeqnum(self):
        address = SimpleNamespace(getOffset=lambda: 0x401100)
        return SimpleNamespace(getTarget=lambda: address, getOrder=lambda: 3)


def _summarize_call_passing(argument):
    from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary, StoreEffect
    from scripts.function_tracer_pcode.analysis.effects.summary import summarize_store_effects

    op = _CallOp()
    out = Expression.binary_op("INT_ADD", Expression.variable("sp", size=8, storage_info=_register("sp", base="sp")), _const(-0x20))

    class Tracer:
        program = SimpleNamespace(getLanguage=lambda: SimpleNamespace(isBigEndian=lambda: False))

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            return {"arg0": argument, "out0": out}.get(varnode.key, _const(0x401100))

    callee_value = Expression.parameter("value", 0, size=8)
    callee_out = CanonicalLocation(base_ref=LocationBaseRef.parameter("out", index=1), offset=0, size=8)
    return summarize_store_effects(
        [SimpleNamespace(pcode_ops=[op])],
        Tracer(),
        SimpleNamespace(get_all_valid_paths_to_block=lambda _block: [[]]),
        PARAMETERS,
        direct_call_summary=lambda _target, _args: EffectSummary(
            parameter_names=["value", "out"],
            parameter_refs=[LocationBaseRef.parameter("value", index=0), LocationBaseRef.parameter("out", index=1)],
            effects=[StoreEffect(location=callee_out, value=callee_value, conditions=[], order_key=1)],
        ),
        resolve_callee_parameters=lambda _target: [_descriptor("value", 0, None), _descriptor("out", 1, None)],
        debug=False,
    )


def test_a_call_passing_a_load_stores_the_loaded_value_not_the_pointer():
    """修正前: 引数 `*p` を正規化が p にし、callee の `*out = value` が `*out = p` になった。"""

    summary = _summarize_call_passing(_load())
    values = [effect.value for effect in summary.effects]
    assert values and all(value.expr_type is ExpressionType.MEMORY for value in values)


def test_a_call_passing_the_parameter_stores_the_parameter():
    summary = _summarize_call_passing(_param())
    values = [effect.value for effect in summary.effects]
    assert values and all(value.expr_type is ExpressionType.PARAMETER and value.name == "p" for value in values)


# 関数をまたぐ置き換えの所有者（`CalleeBinding` も同じ規則）


def test_the_boundary_refuses_a_parameter_of_another_function():
    binding = CalleeBinding.for_arguments([_descriptor("p", 0, X0, **OWNER)], [_const(7)])
    with pytest.raises(CallBoundaryRefused) as refused:
        import_callee_expression(_param(owner=OTHER_OWNER), CallSite(None), CalleeTimeline.unknown(), binding=binding)
    assert refused.value.reason == REFUSED_CALLEE_FOREIGN_PARAMETER


# ---------------------------------------------------------------------------
# 2. varnode から回復した parameter の bit の位置
# ---------------------------------------------------------------------------


def _evaluate(expr, parameter_value):
    """p（8 byte）を `parameter_value` とした値。`PARAMETER` の node は幅の分だけ下位の bit と読む（consumer の読み方）。"""

    mask = (1 << (8 * expr.size)) - 1
    if expr.expr_type is ExpressionType.PARAMETER:
        return parameter_value & mask
    if expr.expr_type is ExpressionType.CONSTANT:
        return int(expr.value) & mask
    if expr.operator == "SUBPIECE":
        source, offset = expr.operands
        return (_evaluate(source, parameter_value) >> (8 * int(offset.value))) & mask
    raise AssertionError(expr.operator)


class _ParameterSymbol:
    def getName(self):
        return "p"

    def isParameter(self):
        return True

    def getCategoryIndex(self):
        return 0


class _ParameterPiece:
    """p の入力 varnode（定義が無い）で、記憶域は x0 の一部。"""

    def __init__(self, storage):
        self.storage = storage

    def getSize(self):
        return self.storage.size

    def getDef(self):
        return None

    def getHigh(self):
        return SimpleNamespace(getSymbol=lambda: _ParameterSymbol(), getSlot=lambda: 0, getName=lambda: "p")


def _tracer(big_endian):
    language = None if big_endian is None else SimpleNamespace(isBigEndian=lambda: big_endian)
    return SimpleNamespace(
        program=SimpleNamespace(getLanguage=lambda: language),
        _get_storage_info_from_varnode=lambda varnode: varnode.storage,
    )


WIDE = 0x0000000200000001


@pytest.mark.parametrize("big_endian, high, low", [(False, X0_SECOND, X0_FIRST), (True, X0_FIRST, X0_SECOND)])
def test_a_recovered_upper_half_of_a_parameter_is_its_upper_bits(big_endian, high, low):
    """修正前: 上位 32 bit の varnode を、p の記憶域全体を持つ 32 bit の node にし、下位 32 bit（1）と読まれた。"""

    upper = call_argument._impl__parameter_expression_from_varnode(_ParameterPiece(high), _tracer(big_endian), PARAMETERS)
    assert upper is not None and upper.size == 4 and _evaluate(upper, WIDE) == 2
    lower = call_argument._impl__parameter_expression_from_varnode(_ParameterPiece(low), _tracer(big_endian), PARAMETERS)
    assert lower is not None and lower.size == 4 and _evaluate(lower, WIDE) == 1


def test_a_recovered_parameter_piece_without_a_byte_order_is_not_recovered():
    assert call_argument._impl__parameter_expression_from_varnode(_ParameterPiece(X0_SECOND), _tracer(None), PARAMETERS) is None


def test_a_recovered_whole_parameter_is_the_parameter():
    whole = call_argument._impl__parameter_expression_from_varnode(_ParameterPiece(X0), _tracer(False), PARAMETERS)
    assert whole.expr_type is ExpressionType.PARAMETER and whole.size == 8 and whole.storage_info == X0


def test_the_recovered_upper_half_reaches_the_callee_as_its_upper_bits():
    """生成元（caller の引数の回復）から利用先（callee の parameter の置き換え）まで: 上位 32 bit は 2。"""

    upper = call_argument._impl__parameter_expression_from_varnode(_ParameterPiece(X0_SECOND), _tracer(False), PARAMETERS)
    callee_parameter = _descriptor("v", 0, _register("w0", base="x0", size=4), size=4)
    binding = CalleeBinding.for_arguments([callee_parameter], [upper], big_endian=False)
    callee_node = Expression.parameter("v", 0, size=4, storage_info=callee_parameter["storage"])
    imported = import_callee_expression(callee_node, CallSite(None), CalleeTimeline.unknown(), binding=binding)
    assert _evaluate(imported, WIDE) == 2


# ---------------------------------------------------------------------------
# 3. 記憶域への書き込み: 重ならないのは証明できたときだけ
# ---------------------------------------------------------------------------


class _Space:
    def __init__(self, name, space_id, *, register=False):
        self._name, self._id, self._register = name, space_id, register

    def getName(self):
        return self._name

    def getSpaceID(self):
        return self._id

    def isRegisterSpace(self):
        return self._register


REGISTER_SPACE = _Space("register", 548, register=True)
UNIQUE_SPACE = _Space("unique", 291)


class _Out:
    def __init__(self, space, offset=0x100, size=8, label=None):
        self.space, self.offset, self.size, self.label = space, offset, size, label

    def getAddress(self):
        return SimpleNamespace(getAddressSpace=lambda: self.space)

    def getOffset(self):
        return self.offset

    def getSize(self):
        return self.size


class _Op:
    def __init__(self, mnemonic, output, inputs=()):
        self.mnemonic, self.output, self.inputs = mnemonic, output, list(inputs)

    def getMnemonic(self):
        return self.mnemonic

    def getOutput(self):
        return self.output

    def getNumInputs(self):
        return len(self.inputs)

    def getInput(self, index):
        return self.inputs[index]


def _write_tracer(known):
    """`known` に入った varnode だけ記憶域を作れる tracer（Ghidra が register を返さない範囲などを模す）。"""

    return SimpleNamespace(_get_storage_info_from_varnode=lambda varnode: known.get(id(varnode)))


@pytest.fixture
def _values(monkeypatch):
    monkeypatch.setattr(
        call_argument,
        "_resolve_call_argument_expression",
        lambda varnode, *a, **k: Expression.variable(varnode.label or "v", size=varnode.size),
    )


def test_a_register_space_write_whose_storage_cannot_be_read_makes_the_argument_unknown(_values):
    """修正前: 出力の記憶域を作れない op を x1 と重ならないとし、その前の書き込み（古い値）を引数にした。"""

    argument_write = _Op("COPY", _Out(REGISTER_SPACE, label="before"))
    unreadable = _Op("INT_ADD", _Out(REGISTER_SPACE, offset=0x4F2, label="later"))
    tracer = _write_tracer({id(argument_write.output): X1})
    assert call_argument._impl__op_write_relation(unreadable, X1, tracer) is MemoryRelation.UNKNOWN
    assert call_argument._impl__select_best_storage_candidate([argument_write, unreadable], X1, tracer, [], {}) is None
    assert call_argument._impl__path_writes_storage([unreadable], X1, tracer)


def test_a_write_outside_the_register_space_keeps_the_argument(_values):
    """正しく決まる場合は保つ: register でない空間（unique）への書き込みは register の値を変えない。"""

    argument_write = _Op("COPY", _Out(REGISTER_SPACE, label="before"))
    temporary = _Op("INT_ADD", _Out(UNIQUE_SPACE, label="tmp"))
    tracer = _write_tracer({id(argument_write.output): X1})
    assert call_argument._impl__op_write_relation(temporary, X1, tracer) is MemoryRelation.DISJOINT
    selected = call_argument._impl__select_best_storage_candidate([argument_write, temporary], X1, tracer, [], {})
    assert selected is not None and selected.name == "before"


def test_a_register_range_without_a_name_is_not_disjoint_from_a_named_register():
    """Ghidra が register を返さない範囲の記憶域（名前が無い）は、どの register と重なるか分からない。"""

    unnamed = StorageInfo(is_register=True, space_name="register", offset=0x4002, size=4)
    assert call_argument._impl__storage_match_rank(unnamed, X1) == MemoryRelation.UNKNOWN
    # 分からない（rank 2）を同じ場所と読まない
    assert not call_argument._impl__storage_infos_match(unnamed, X1)
    assert call_argument._impl__storage_match_rank(X0, X1) == MemoryRelation.DISJOINT
    assert call_argument._impl__storage_infos_match(X1, X1)


def test_memory_spaces_are_compared_by_name_not_by_a_synthetic_id():
    """descriptor の記憶域の `space_id` は名前からの合成値で、Ghidra の値と食い違う（修正前は別の空間 = 重ならない）。"""

    from_descriptor = StorageInfo(is_register=False, space_name="stack", offset=8, size=8)
    from_varnode = StorageInfo(is_register=False, space_name="stack", space_id=0x2B5, offset=8, size=8)
    assert call_argument._impl__storage_match_rank(from_descriptor, from_varnode) == MemoryRelation.SAME
    ram = StorageInfo(is_register=False, space_name="ram", space_id=0x1A5, offset=8, size=8)
    assert call_argument._impl__storage_match_rank(from_descriptor, ram) == MemoryRelation.DISJOINT
    stack_varnode = _Out(_Space("stack", 0x2B5), offset=12, size=4)
    assert call_argument._impl__stack_varnode_storage_rank(stack_varnode, from_descriptor) == MemoryRelation.OVERLAP


def test_a_callee_stack_parameter_has_no_caller_value(monkeypatch):
    """callee の stack の parameter の記憶域は callee の frame の場所: caller の op・parameter と比べられない。

    修正前: 呼び出しまでの経路に書き込みが無いと、同じ offset にある caller の stack の parameter（caller の入口の
    frame の場所）を、callee の stack の引数（呼び出しの位置の frame の場所）とした。
    """

    call = _Op("CALL", None)
    monkeypatch.setattr(
        call_argument, "_compatible_call_block_paths", lambda *_a, **_k: [([SimpleNamespace(pcode_ops=[call])], [])]
    )
    callee_stack_parameter = {"name": "s", "index": 8, "size": 8, "storage": StorageInfo(space_name="stack", offset=0, size=8)}
    caller_stack_parameter = {"name": "a", "index": 8, "size": 8, "storage": StorageInfo(space_name="stack", offset=0, size=8)}
    recovered = call_argument._impl__recover_call_argument_from_storage(
        call, _write_tracer({}), [caller_stack_parameter], callee_stack_parameter, condition_tracker=object()
    )
    assert recovered is None
    # register で渡る parameter は caller の言葉の記憶域（呼び出しの前後で同じ register）: live-in の値を保つ
    register_parameter = _descriptor("q", 1, X1)
    recovered = call_argument._impl__recover_call_argument_from_storage(
        call, _write_tracer({}), [register_parameter], register_parameter, condition_tracker=object()
    )
    assert recovered is not None and recovered.name == "q"
