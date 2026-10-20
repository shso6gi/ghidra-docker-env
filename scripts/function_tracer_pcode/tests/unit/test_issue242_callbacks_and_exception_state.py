# -*- coding: utf-8 -*-
"""Issue #242（第 6 回のレビュー）: 暗黙の callback の戻り値と、例外の状態（無い / 明示的な `None` / 値）。

期待値は実装と独立に作る: どれも **正直な双子**（callback が基底型の値を返す object・基底型の値の例外）に Python の
組み込みの演算（`==` / `!=` / `<` / `in` / `sorted` / `str`）を当てた結果。旧 head との一致は根拠にしない。

- 比べる側の契約（`live_values.equal` / `unequal` / `contains` / `less` / `sorted_trees`）: 葉の外の object の比較の戻り値が
  `__bool__` を偽る scalar の subclass でも、結果は双子と同じで、偽る型の code を呼ばない（直接・容器の中・入れ子・
  identity・dict の値・`__ne__`）。組み込みの code だけでは忠実に比べられない値（外の object を key に持つ dict・要素に
  持つ set）は `UndecidableComparison`（等しい / 違うと推測しない）。状態で答えが変わる callback・容器を変える
  callback・hash の衝突は `test_issue242_comparison_invariants.py`（第 7 回）。
- ref の層: どの ref の class のどの field に `Callback`（外の object）を置いても、構築・key・`==`・hash が双子と同じ。
- 例外: field の種類（`__slots__`・組み込みの C の field・getset・`__dict__`）× 状態（無い / 明示的な `None` / 値）×
  traceback の有無で、`exception_text` が双子の `str()` と同じ（NULL と `None` を決められないときだけ `<unprintable>`）。
  写しの途中の例外で元の例外を置き換えない（`CallTargetRef.from_function`）。
"""

from __future__ import annotations

import dataclasses
import itertools
import math
from typing import Any, Optional, Tuple

import pytest

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.live_values import UndecidableComparison
from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import (
    HOOK_CALLS, Callback, Liar, LiarStr, callbacks, view,
)


# ---------------------------------------------------------------------------
# 比べる側の契約: 双子に組み込みの演算を当てた結果が期待値
# ---------------------------------------------------------------------------

#: 葉の指定: exact な scalar はそのまま、`("cb", v)` は `Callback(v)`、`("same",)` は左の値そのもの（identity）
LEAVES = [1, 2, "a", None, 1.5, ("cb", 1), ("cb", 2), ("cb", "a"), ("cb", 1.5)]
#: 容器の形（`x` が葉の位置）
SHAPES = [
    lambda x: x,
    lambda x: (x,),
    lambda x: (0, x),
    lambda x: [x, "z"],
    lambda x: ((x,), 1),
    lambda x: {"k": x},
    lambda x: ("t", [x, (x,)]),
]


def _leaf(spec: Any, lying: bool) -> Any:
    if type(spec) is tuple and spec and spec[0] == "cb":
        return Callback(spec[1], lying)
    return spec


def _pair(shape: Any, left: Any, right: Any, lying: bool, same: bool = False) -> Tuple[Any, Any]:
    a = shape(_leaf(left, lying))
    b = a if same else shape(_leaf(right, lying))
    return a, b


def _outcome(operation: Any) -> Any:
    try:
        return ("value", operation())
    except UndecidableComparison:
        return ("undecidable",)
    except TypeError as error:
        return ("raises", type(error).__name__)


def _pairs():
    for (si, shape), left, right in itertools.product(enumerate(SHAPES), LEAVES, LEAVES):
        yield pytest.param(si, left, right, False, id=f"s{si}-{left!r}-{right!r}")
    for (si, shape), left in itertools.product(enumerate(SHAPES), LEAVES):
        yield pytest.param(si, left, left, True, id=f"s{si}-same-{left!r}")


@pytest.mark.parametrize("shape_index, left, right, same", list(_pairs()))
def test_equality_and_order_read_callback_results_like_the_twin(shape_index, left, right, same):
    shape = SHAPES[shape_index]
    ta, tb = _pair(shape, left, right, lying=False, same=same)
    la, lb = _pair(shape, left, right, lying=True, same=same)
    expected = {
        "equal": _outcome(lambda: bool(ta == tb)),
        "unequal": _outcome(lambda: bool(ta != tb)),
        "less": _outcome(lambda: bool(ta < tb)),
        "contains": _outcome(lambda: bool(tb in (ta, "z"))),
    }
    HOOK_CALLS.clear()
    got = {
        "equal": _outcome(lambda: live_values.equal(la, lb)),
        "unequal": _outcome(lambda: live_values.unequal(la, lb)),
        "less": _outcome(lambda: live_values.less(la, lb)),
        "contains": _outcome(lambda: live_values.contains((la, "z"), lb)),
    }
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert got == expected


def test_the_lying_callback_changes_the_builtin_result():
    """反例の再現の確認: 組み込みの容器の比較は葉の比較の戻り値の `__bool__` を読む（偽る側だけ結果が変わる）。"""

    HOOK_CALLS.clear()
    assert ((Callback(1, True),) == (Callback(2, True),)) is True  # 偽る 0 の真偽が真
    assert HOOK_CALLS["Liar.__bool__"] >= 1
    assert ((Callback(1, False),) == (Callback(2, False),)) is False
    HOOK_CALLS.clear()
    assert live_values.equal((Callback(1, True),), (Callback(2, True),)) is False
    assert HOOK_CALLS == {}


def test_identity_and_nan_follow_the_container_rules():
    nan = float("nan")
    assert live_values.equal(nan, nan) is False  # 最上位の `==` は identity を見ない
    assert live_values.equal((nan,), (nan,)) is True  # 容器の要素は identity を先に見る
    assert live_values.unequal((nan,), (nan,)) is False
    shared = Callback(1, True)
    HOOK_CALLS.clear()
    assert live_values.equal((shared,), (shared,)) is True and HOOK_CALLS == {}


def test_ne_uses_the_ne_protocol_on_leaves_and_eq_inside_containers():
    class Odd:
        def __eq__(self, other):
            return Liar(1)

        def __ne__(self, other):
            return Liar(1)

        __hash__ = object.__hash__

    a, b = Odd(), Odd()
    HOOK_CALLS.clear()
    assert live_values.unequal(a, b) is True  # `a != b` の戻り値（基底型の値 1）の真偽
    assert live_values.unequal((a,), (b,)) is False  # tuple の `!=` は要素を `==` で比べる（`__eq__` の 1: 等しい）
    assert HOOK_CALLS == {}


def test_undecidable_containers_are_not_guessed():
    key = Callback(1, True)
    with pytest.raises(UndecidableComparison):
        live_values.equal({key: 1}, {key: 1})
    with pytest.raises(UndecidableComparison):
        live_values.equal(frozenset({key}), frozenset({key}))
    with pytest.raises(UndecidableComparison):
        live_values.contains({key}, 1)
    with pytest.raises(UndecidableComparison):
        live_values.inert_key((key,))
    # 第 8 回: 判定不能は「回復できる」普通の例外の派生ではない（helper の `except TypeError` に吸収されない）
    assert not issubclass(UndecidableComparison, TypeError)


def test_membership_in_inert_sets_reads_the_callback_result():
    """不活性な set / dict を外の object で引く: hash の等しい要素だけを、要素を左に置いた `==` で比べる（双子と同じ）。"""

    for lying_value, expected in ((Callback("a", True), True), (Callback("x", True), False)):
        twin = Callback(lying_value.value, False)
        assert (twin in {"a", "b"}) is expected
        HOOK_CALLS.clear()
        assert live_values.contains({"a", "b"}, lying_value) is expected
        assert live_values.contains({"a": 1}, lying_value) is expected
        assert HOOK_CALLS == {}


def test_sorting_trees_matches_the_twin_order():
    values = [(Callback(3, False), 1), (Callback(1, False), 2), (Callback(2, False), 0), (Callback(1, False), 1)]
    lying = [(Callback(item[0].value, True), item[1]) for item in values]
    expected = [view(item) for item in sorted(values)]
    HOOK_CALLS.clear()
    assert [view(item) for item in live_values.sorted_trees(lying)] == expected
    assert HOOK_CALLS == {}


def test_inert_values_are_exactly_builtin_trees():
    assert live_values.inert((1, "a", None, 1.5, True, [1], {"k": (2,)}, frozenset({1})))
    for value in (Callback(1, True), (Callback(1, True),), [Liar(1)], {"k": LiarStr("x")}, (object(),)):
        assert not live_values.inert(value)
    # 閉路の list も葉が exact なら不活性（比べる code は組み込みのものだけ: 閉路は比較の側の規則で `RecursionError`）
    looped: list = [1]
    looped.append(looped)
    assert live_values.inert(looped)


# ---------------------------------------------------------------------------
# 反例（レビュー第 6 回 1）: P-code の親の中の序数と loop summary の比較
# ---------------------------------------------------------------------------


def _ordinal(zero: Any) -> Optional[int]:
    from scripts.function_tracer_pcode.core.runtime_refs import pcode

    class Iterator:
        def __init__(self, items):
            self.items = list(items)

        def hasNext(self):
            return bool(self.items)

        def next(self):
            return self.items.pop(0)

    class Parent:
        def __init__(self):
            self.items = []

        def getIterator(self):
            return Iterator(self.items)

    class Op:
        def __init__(self, opcode, parent):
            self.parent, self.opcode = parent, opcode

        def getParent(self):
            return self.parent

        def getOpcode(self):
            return self.opcode

        def __eq__(self, other):
            return zero(0)  # Java の equals の結果（偽る側は `__bool__` が真を返す 0）

        __hash__ = object.__hash__

    parent = Parent()
    first, second = Op(1, parent), Op(2, parent)
    parent.items = [first, second]
    return pcode._local_op_ordinal_from_parent(second)


def test_pcode_ordinal_reads_the_api_equality_like_the_twin():
    expected = _ordinal(int)
    HOOK_CALLS.clear()
    assert _ordinal(Liar) == expected == 1
    assert HOOK_CALLS == {}


def _summary_comparison(lying: bool) -> Any:
    from scripts.function_tracer_pcode.core.runtime_refs.loops import compare_loop_summaries

    class Summary:
        side_effect_profile = None
        cases = ()

        def __init__(self, key):
            self.key = key

        def pairwise_semantic_key(self):
            return self.key

    left = Summary(("loop", Callback(1, lying)))
    right = Summary(("loop", Callback(2, lying)))
    return compare_loop_summaries(left, right)


def test_loop_summary_comparison_reads_key_leaves_like_the_twin():
    expected = _summary_comparison(False)
    HOOK_CALLS.clear()
    got = _summary_comparison(True)
    assert HOOK_CALLS == {}
    assert got.status == expected.status == "unknown"


def test_undecidable_loop_keys_never_claim_equivalence():
    from scripts.function_tracer_pcode.core.runtime_refs.loops import compare_loop_summaries

    class Summary:
        side_effect_profile = None
        cases = ()

        def pairwise_semantic_key(self):
            return ("loop", {Callback(1, False): 1})  # 不活性でない key の dict: 比べられない

    assert compare_loop_summaries(Summary(), Summary()).status == "unknown"


# ---------------------------------------------------------------------------
# ref の層: どの field に外の object（`Callback`）を置いても双子と同じ
# ---------------------------------------------------------------------------


def _key_methods(cls):
    import inspect

    return [
        name for name, member in vars(cls).items()
        if inspect.isfunction(getattr(member, "__func__", member)) and not name.startswith("_")
        and (name.endswith("_key") or name == "key") and len(inspect.signature(member).parameters) == 1
    ]


def _observe(cls, make_kwargs) -> Any:
    try:
        built = cls(**make_kwargs())
        other = cls(**make_kwargs())  # 別の外の object（identity で比べを飛ばさない）
    except Exception as error:
        return ("raises", type(error).__name__)
    keys = []
    for name in _key_methods(cls):
        try:
            keys.append((name, view(getattr(built, name)())))
        except Exception as error:
            keys.append((name, ("raises", type(error).__name__)))
    try:
        hashed = hash(built)
    except Exception as error:
        hashed = ("raises", type(error).__name__)
    outputs = []
    for name, read in (("materialize", lambda: _json(built)), ("repr", lambda: live_values.exact_scalar(repr(built)))):
        try:
            outputs.append((name, read()))
        except Exception as error:
            outputs.append((name, ("raises", type(error).__name__)))
    return ("built", view(built), tuple(keys), bool(built == other), hashed, tuple(outputs))


def _json(built: Any) -> Any:
    import json

    from scripts.function_tracer_pcode.core.json_encoding import materialize

    return json.dumps(materialize(built), sort_keys=True, default=lambda value: ("object", type(value).__name__))


def _field_cases():
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    for cls, make in corpus.BASES.items():
        base = make()
        for item in dataclasses.fields(cls):
            if not item.init or item.name not in base:
                continue
            value = base[item.name]
            if callbacks(value, True) == value and type(value) not in (int, str, float):
                continue  # 写せる scalar の葉を持たない値（ref・式・None）
            yield pytest.param(cls, item.name, id=f"{cls.__qualname__}.{item.name}")


@pytest.mark.parametrize("cls, name", list(_field_cases()))
def test_refs_holding_foreign_objects_with_lying_callbacks_match_their_twins(cls, name):
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    base = corpus.BASES[cls]()
    expected = _observe(cls, lambda: {**base, name: callbacks(base[name], False)})
    HOOK_CALLS.clear()
    got = _observe(cls, lambda: {**base, name: callbacks(base[name], True)})
    assert HOOK_CALLS == {}, (cls.__name__, name, dict(HOOK_CALLS))
    assert got == expected


def test_every_ref_class_compares_through_the_owner_or_its_checked_equality():
    from scripts.function_tracer_pcode.core.runtime_ref_record import _ref_equal
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    own = {cls.__qualname__ for cls in corpus.BASES if cls.__dict__.get("__eq__") is not _ref_equal}
    assert own == {"LocationBaseRef"}  # 自分の `__eq__` の本体は構築の guard が検査する
    for cls in corpus.BASES:
        assert cls.__hash__ is not None  # frozen の dataclass の `__hash__` は今までどおり


# ---------------------------------------------------------------------------
# 例外の状態: 無い / 明示的な `None` / 値 × field の種類 × traceback
# ---------------------------------------------------------------------------


class _Slotted(ValueError):
    __slots__ = ("marker",)

    def __str__(self):
        try:
            marker = repr(self.marker)
        except AttributeError:
            marker = "<unset>"
        return f"{self.args[0]} marker={marker} traceback={self.__traceback__ is not None}"


class _Traced(ValueError):
    def __str__(self):
        return (
            f"{self.args[0]} traceback={self.__traceback__ is not None} cause={self.__cause__!r} "
            f"suppress={self.__suppress_context__} note={getattr(self, 'note', '<unset>')!r}"
        )


def _raised(error: BaseException) -> BaseException:
    try:
        raise error
    except BaseException as caught:  # noqa: BLE001 - test が作った例外
        return caught


def _slotted(message, marker_state, traced):
    error = _Slotted(message)
    if marker_state == "none":
        error.marker = None
    elif marker_state == "value":
        error.marker = "v"
    elif marker_state == "lying":
        error.marker = LiarStr("v") if type(message) is not str else "v"
    return _raised(error) if traced else error


def _oserror(message, filename_state, filename2_state, errno_state, traced):
    error = OSError(2, message)
    for name, state in (("filename", filename_state), ("filename2", filename2_state), ("errno", errno_state)):
        if state == "none":
            setattr(error, name, None)
        elif state == "value":
            setattr(error, name, "f" if name != "errno" else 5)
    return _raised(error) if traced else error


def _traced(message, cause_state, note_state, traced):
    error = _Traced(message)
    if cause_state == "none":
        error.__cause__ = None
    elif cause_state == "value":
        error.__cause__ = KeyError("c")
    if note_state == "none":
        error.note = None
    elif note_state == "value":
        error.note = "n"
    return _raised(error) if traced else error


STATES = ("unset", "none", "value")


def _exception_cases():
    for marker, traced in itertools.product(STATES + ("lying",), (False, True)):
        yield pytest.param(_slotted, (marker, traced), id=f"slot-{marker}-tb{traced}")
    for filename, filename2, errno, traced in itertools.product(STATES, STATES, ("unset", "none"), (False, True)):
        yield pytest.param(_oserror, (filename, filename2, errno, traced), id=f"os-{filename}-{filename2}-{errno}-tb{traced}")
    for cause, note, traced in itertools.product(STATES, STATES, (False, True)):
        yield pytest.param(_traced, (cause, note, traced), id=f"chain-{cause}-{note}-tb{traced}")


def _state_ambiguous(error: BaseException) -> bool:
    """観測（field の読み・型の traverse の参照の `None` の数）と矛盾しない、別の NULL / `None` の割り当てが在るか。

    実装と独立に総当たりで数える: `None` と読める組み込みの C の field の部分集合ごとに、その部分集合だけを明示的な
    `None` にした割り当てを考え、参照の `None` の数が観測と合う（`None` を残し得る `__traceback__` の分を含む）ものが、
    実際の割り当てのほかに在れば曖昧。
    """

    import gc
    import types as _types

    readable = []
    for klass in type(error).__mro__:
        for name, descriptor in vars(klass).items():
            if (
                isinstance(descriptor, _types.MemberDescriptorType) and descriptor.__objclass__.__module__ == "builtins"
                and not name.startswith("__") and getattr(error, name) is None
            ):
                readable.append(name)
    observed = sum(1 for item in gc.get_referents(error) if item is None)
    probe = BaseException()
    probe.__traceback__ = None
    keeps = sum(1 for item in gc.get_referents(probe) if item is None) == 1
    slack = (0, 1) if keeps and error.__traceback__ is None else (0,)
    consistent = [
        subset for size in range(len(readable) + 1) for subset in itertools.combinations(readable, size)
        if any(observed - kept == len(subset) for kept in slack)
    ]
    return len(consistent) > 1


@pytest.mark.parametrize("build, states", list(_exception_cases()))
def test_exception_text_reproduces_every_observable_state(build, states):
    twin = build("m", *states)
    try:
        expected = ("text", str(twin))
    except Exception as error:  # noqa: BLE001 - 双子の `__str__` が投げる例外の型
        expected = ("raises", type(error).__name__)
    lying = build(LiarStr("m"), *states)
    HOOK_CALLS.clear()
    try:
        got = ("text", live_values.exception_text(lying))
    except Exception as error:  # noqa: BLE001
        got = ("raises", type(error).__name__)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    unprintable = ("text", f"<unprintable {type(lying).__name__} object>")
    if got == unprintable and expected != unprintable:
        # 判定しないのは、観測と矛盾しない別の状態が在るときだけ（推測できる状態で判定を捨てない）
        assert _state_ambiguous(lying), (states, expected)
    else:
        assert got == expected
    # 写す前と同じ: subclass を持たない例外は `str()` のまま
    assert live_values.exception_text(twin) == expected[1] if expected[0] == "text" else True


def test_the_reviewed_exception_states_are_reproduced():
    """反例（レビュー第 6 回 2）: `None` の slot を読む `__str__` と、traceback を読む `__str__`。"""

    class Marked(ValueError):
        __slots__ = ("marker",)

        def __init__(self, message):
            super().__init__(message)
            self.marker = None

        def __str__(self):
            return f"{self.args[0]} marker={self.marker!r}"

    class Traced(ValueError):
        def __str__(self):
            return f"{self.args[0]} traceback={self.__traceback__ is not None}"

    assert live_values.exception_text(Marked(LiarStr("m"))) == str(Marked("m")) == "m marker=None"
    assert live_values.exception_text(_raised(Traced(LiarStr("m")))) == str(_raised(Traced("m"))) == "m traceback=True"


def test_errors_raised_while_reading_never_replace_the_original_exception():
    """`CallTargetRef.from_function` が API の例外を読むとき、写しの途中の例外で元の例外を置き換えない。"""

    from scripts.function_tracer_pcode.core.call_target import CallTargetRef

    class Marked(ValueError):
        __slots__ = ("marker",)

        def __init__(self, message):
            super().__init__(message)
            self.marker = None

        def __str__(self):
            return f"{self.args[0]} marker={self.marker!r}"

    class Function:
        def __init__(self, message):
            self.message = message

        def getName(self):
            raise Marked(self.message)

        def __getattr__(self, name):
            raise Marked(self.message)

    outcomes = []
    for message in ("m", LiarStr("m")):
        try:
            CallTargetRef.from_function(Function(message))
            outcomes.append("returned")
        except Marked:
            outcomes.append("Marked")
        except Exception as error:  # noqa: BLE001
            outcomes.append(type(error).__name__)
    assert outcomes[0] == outcomes[1]
    assert "AttributeError" not in outcomes


def test_ambiguous_builtin_fields_are_undecidable_not_guessed():
    error = OSError(2, LiarStr("m"))
    error.filename = None  # 明示的な None。filename2 は NULL（どちらも None と読める）
    assert _state_ambiguous(error)
    assert live_values.exception_text(error) == f"<unprintable {type(error).__name__} object>"
    # 全部 NULL（よくある形）は決まる
    plain = OSError(2, LiarStr("m"))
    assert live_values.exception_text(plain) == str(OSError(2, "m")) == "[Errno 2] m"
    twin = OSError(2, "m")
    twin.filename = None
    assert str(twin) == "[Errno 2] m: None"  # 組み込みの `__str__` は区別する: 推測すると誤る


def test_owner_repr_and_equality_match_the_dataclass_semantics_for_exact_values():
    """owner の `__repr__` / `__eq__` は、exact な値では dataclass の生成するものと同じ（独立に組み立てた期待値）。"""

    from scripts.function_tracer_pcode.core.runtime_ref_record import _ref_equal, _ref_repr
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    checked = 0
    for cls, make in corpus.BASES.items():
        try:
            left, right = cls(**make()), cls(**make())
        except Exception:  # noqa: BLE001 - 基底の構成で作れない class は対象外
            continue
        fields = dataclasses.fields(cls)
        if cls.__dict__.get("__repr__") is _ref_repr:
            expected = cls.__qualname__ + "(" + ", ".join(
                f"{item.name}={getattr(left, item.name)!r}" for item in fields if item.repr
            ) + ")"
            assert repr(left) == expected
        if cls.__dict__.get("__eq__") is _ref_equal:
            values = lambda ref: tuple(getattr(ref, item.name) for item in fields if item.compare)  # noqa: E731
            assert (left == right) is (values(left) == values(right))
            shared = dataclasses.replace(left)  # 同じ field の object を持つ別の instance
            assert (left == shared) is (values(left) == values(shared)) is True
            try:
                assert hash(left) == hash(shared)
            except TypeError:  # 容器の field（dict など）を持つ ref は dataclass の `__hash__` が hash できない（双方同じ）
                with pytest.raises(TypeError):
                    hash(shared)
            checked += 1
    assert checked >= 30


def test_top_level_equality_does_not_assume_identity():
    """最上位の `==` は identity を見ない（自分と等しくない外の object）。容器の要素は identity を先に見る。"""

    def not_self(zero):
        class NotSelf:
            def __eq__(self, other):
                return zero(0)

            __hash__ = object.__hash__

        return NotSelf()

    twin = not_self(int)
    expected = (bool(twin == twin), bool((twin,) == (twin,)))
    item = not_self(Liar)
    HOOK_CALLS.clear()
    assert (live_values.equal(item, item), live_values.equal((item,), (item,))) == expected == (False, True)
    assert HOOK_CALLS == {}


def test_ordinal_signature_with_a_foreign_target_uses_the_tuple_rule():
    from scripts.function_tracer_pcode.core.runtime_refs import pcode

    class Op:
        def getOpcode(self):
            return 7

    signature = pcode._pcode_op_ordinal_signature(Op())
    for lying in (False, True):
        target = signature[:4] + (Callback(7, lying), signature[5])
        expected_twin = signature == tuple(Callback(7, False) if i == 4 else v for i, v in enumerate(target))
        HOOK_CALLS.clear()
        got = pcode._pcode_op_ordinal_signature(Op(), target)
        assert HOOK_CALLS == {}
        assert (got is not None) is expected_twin is True
        assert got == signature


def test_undecidable_keys_never_claim_a_difference():
    """判定できない key（不活性でない key の dict）は「違う」側にも使わない: loop summary を incompatible に、
    引数の ref を「必ず別」にしない。"""

    from scripts.function_tracer_pcode.core.runtime_refs.call_arguments import fresh_call_argument_refs_are_side_distinct
    from scripts.function_tracer_pcode.core.runtime_refs.loops import compare_loop_summaries

    class Profile:
        memory_reads = memory_writes = calls = escapes = conditional_guards = False
        effect_count = guard_count = 0

        def __init__(self, marker):
            self.profile = {Callback(marker, False): 1}

        def stable_key(self):
            return ("p",)

    class Summary:
        cases = ()

        def __init__(self, marker):
            self.side_effect_profile = Profile(marker)

        def pairwise_semantic_key(self):
            return None

    assert compare_loop_summaries(Summary(1), Summary(2)).status == "unknown"

    class Ref:
        def __init__(self, marker):
            self.marker = marker

        def stable_key(self):
            return ("arg", {Callback(self.marker, False): 1})

    assert fresh_call_argument_refs_are_side_distinct(Ref(1), Ref(2)) is False


def test_cause_setter_side_effects_do_not_leak_into_the_copy():
    """`__cause__` の setter は `__suppress_context__` を真にする: 写しでも元と同じ値（getset を先に置く）。"""

    def build(message):
        error = _Traced(message)
        error.__cause__ = KeyError("c")
        error.__suppress_context__ = False
        return error

    assert live_values.exception_text(build(LiarStr("m"))) == str(build("m"))
    assert "suppress=False" in str(build("m"))


# ---------------------------------------------------------------------------
# 独立の review（第 6 回）の反例: 期待値はどれも双子に組み込みの演算を当てた結果
# ---------------------------------------------------------------------------


def _outcome_of(operation: Any) -> Any:
    try:
        return ("value", operation())
    except Exception as error:  # noqa: BLE001 - 期待値と同じ例外の型か
        return ("raises", type(error).__name__)


def test_tuples_compare_the_common_prefix_before_the_length():
    class Boom:
        def __eq__(self, other):
            raise KeyError("eq")

        __hash__ = object.__hash__

    boom = Boom()
    cases = [
        (lambda: (boom,) == (1, 2), lambda: live_values.equal((boom,), (1, 2))),
        (lambda: (boom,) != (1, 2), lambda: live_values.unequal((boom,), (1, 2))),
        (lambda: (1, 2) in [(boom,)], lambda: live_values.contains([(boom,)], (1, 2))),
        (lambda: [boom] == [1, 2], lambda: live_values.equal([boom], [1, 2])),  # list は長さを先に比べる
    ]
    for builtin, contract in cases:
        assert _outcome_of(contract) == _outcome_of(builtin)


def test_shared_lying_leaves_keep_their_identity_in_the_copy():
    from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import LiarFloat

    twin = float("nan")
    lying = LiarFloat(float("nan"))
    expected = [(twin,) == (twin,), [twin] == [twin], {1: twin} == {1: twin}, twin in (twin,)]
    HOOK_CALLS.clear()
    got = [
        live_values.equal((lying,), (lying,)), live_values.equal([lying], [lying]),
        live_values.equal({1: lying}, {1: lying}), live_values.contains((lying,), lying),
    ]
    assert HOOK_CALLS == {}
    assert got == expected == [True, True, True, True]
    shared = (lying, lying)
    tree = live_values.exact_tree(shared)
    assert tree[0] is tree[1]  # 1 回の読みの中で共有された葉は 1 度だけ写す
    # 外の object の後ろの共有された葉（読みから比べ直す経路）: 2 つを 1 回の読みで写す
    twin_pair = ((Callback(1, False), twin), (Callback(1, False), twin))
    HOOK_CALLS.clear()
    assert live_values.equal((Callback(1, True), lying), (Callback(1, True), lying)) is (twin_pair[0] == twin_pair[1]) is True
    assert HOOK_CALLS == {}


def test_sets_are_searched_with_a_frozen_copy_like_python():
    assert live_values.contains({frozenset({1})}, {1}) is ({1} in {frozenset({1})}) is True
    assert live_values.contains(frozenset({frozenset({2})}), {1}) is False
    with pytest.raises(TypeError):
        live_values.contains({"k": 1}, {1})  # dict は引き直さない（Python と同じ unhashable）


def test_large_honest_trees_are_compared_not_refused():
    """量は `exact_tree` と同じ反復の確かめ（量の owner の無い文脈では上限なし）: 量だけで判定を捨てない。"""

    flat = tuple(range(live_values.SCAN_LIMIT + 500))
    nested = tuple((index, (index,)) for index in range(live_values.SCAN_LIMIT + 10))
    assert live_values.equal(flat, tuple(flat)) is True
    assert live_values.equal(nested, tuple(nested)) is True
    assert live_values.contains(list(flat), live_values.SCAN_LIMIT + 1) is True
    assert live_values.less(flat, flat + (0,)) is True
    assert live_values.inert(nested) is True


def test_cycles_follow_python_comparison_rules():
    looped: list = [1]
    looped.append(looped)
    assert live_values.equal(looped, [1, looped]) is (looped == [1, looped]) is True
    other: list = [1]
    other.append(other)
    with pytest.raises(RecursionError):
        looped == other
    with pytest.raises(RecursionError):
        live_values.equal(looped, other)


def test_ambiguous_fields_decide_when_the_builtin_text_does_not_depend_on_them():
    """`None` と読める C の field の割り当てが観測から決まらなくても、組み込みの `__str__` の文字列がどの割り当てでも
    同じなら決まる（ImportError / SyntaxError）。文字列が割り当てで変わる・投げるなら判定しない。"""

    assert live_values.exception_text(ImportError(LiarStr("m"), name=None)) == str(ImportError("m", name=None)) == "m"
    assert live_values.exception_text(SyntaxError(LiarStr("m"), ("f", 1, 1, None))) == str(SyntaxError("m", ("f", 1, 1, None)))
    error = UnicodeEncodeError("ascii", "x", 0, 1, LiarStr("bad"))
    error.encoding = None  # 明示的な None（NULL と組み込みの `__str__` の結果が違い得る）
    twin = UnicodeEncodeError("ascii", "x", 0, 1, "bad")
    twin.encoding = None
    got = live_values.exception_text(error)
    assert got in (_outcome_of(lambda: str(twin))[1], "<unprintable UnicodeEncodeError object>")


def test_user_str_with_ambiguous_builtin_fields_is_not_rendered_twice():
    """型の Python の `__str__` が何を観測するか決められないとき、割り当てを試して描かない（判定しない）。"""

    calls = []

    class Custom(OSError):
        def __str__(self):
            calls.append(1)
            return str(self.args[1])  # どの割り当てでも同じ文字列だが、型の code を割り当ての数だけ走らせない

    error = Custom(2, LiarStr("m"))
    error.filename = None
    assert live_values.exception_text(error) == f"<unprintable {live_values.type_name(type(error))} object>"
    assert calls == []


def test_set_probes_compare_container_items_without_builtin_truth_tests():
    """不活性な set を、葉に外の object を持つ tuple で引く: hash の等しい要素との比較も要素ごとに戻り値を読む。"""

    expected = (Callback(1, False),) in {(1,)}
    HOOK_CALLS.clear()
    assert live_values.contains({(1,)}, (Callback(1, True),)) is expected is True
    assert HOOK_CALLS == {}


def test_sets_with_foreign_elements_are_undecidable_items():
    """set の値で引き直すとき、要素が不活性でなければ frozenset を作る hash の比較を写せない: 判定しない
    （素の `hash` の `TypeError` ではなく、判定しない印）。"""

    with pytest.raises(UndecidableComparison):
        live_values.contains(frozenset({frozenset({1})}), {Callback(1, True)})


# ---------------------------------------------------------------------------
# 独立の review（第 6 回の 2 巡目）の反例
# ---------------------------------------------------------------------------


def test_ref_equality_reads_the_current_field_type_equality():
    """field の値の型の `__eq__` を後から変えても、ref の `==` は今の `__eq__` を使う（判断を cache しない）。"""

    import dataclasses as _dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    class Obj:
        pass

    @_dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class R:
        a: Optional[int] = None
        b: Any = None

    @_dataclasses.dataclass(frozen=True)
    class Twin:
        a: Optional[int] = None
        b: Any = None

    assert (R(1, Obj()) == R(1, Obj())) is (Twin(1, Obj()) == Twin(1, Obj())) is False
    Obj.__eq__ = lambda self, other: True  # 後から足した `__eq__`
    Obj.__hash__ = object.__hash__
    assert (R(1, Obj()) == R(1, Obj())) is (Twin(1, Obj()) == Twin(1, Obj())) is True


def test_ref_equality_does_not_read_equality_through_the_metaclass():
    import dataclasses as _dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    class Meta(type):
        @property
        def __eq__(cls):  # metaclass の data descriptor: 型の名前空間の `__eq__` ではない
            raise AssertionError("the metaclass property was read")

    class Odd(metaclass=Meta):
        pass

    @_dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class R:
        a: Optional[int] = None
        b: Any = None

    first, second = Odd(), Odd()
    assert (R(1, first) == R(1, second)) is (first == second) is False


def test_comparisons_deeper_than_python_allows_are_not_answered():
    """組み込みの比較が再帰の上限に当たる深さでは、値を答えない（双子は `RecursionError`）。"""

    import sys

    def deep(depth):
        value: Any = [1.0]
        for _ in range(depth):
            value = [value]
        return value

    # どの版でも組み込みの比較が `RecursionError` になる深さ（3.10 は再帰の上限、3.12 は C の再帰の上限）。値を答えない
    # 側の境（再帰の上限から今の frame と余裕を引いた深さ）は、どの版でも組み込みの比較が答えられる深さより浅い
    depth = 100_000
    left, right = deep(depth), deep(depth)
    with pytest.raises(RecursionError):
        left == right
    with pytest.raises((RecursionError, UndecidableComparison)):
        live_values.equal(left, right)
    with pytest.raises((RecursionError, UndecidableComparison)):
        live_values.less(left, right)
    assert live_values.equal(deep(50), deep(50)) is True  # 浅い入れ子は答える


def test_exact_tree_does_not_rebuild_sets_with_foreign_elements():
    """set / dict の key を作り直すと、hash の等しい要素どうしの `==` の戻り値を C が真偽で読む: 不活性でない要素の
    set・key の dict は作り直さない（`TypeError`: 閉路と同じく写せない値）。作り直さずに済む値はそのまま。

    元の set では衝突しない（`LiarStr` の hash は偽る）が、写した `"x"` の hash は外の object の hash と等しい。
    """

    class Colliding:
        def __init__(self, lying):
            self.lying = lying

        def __hash__(self):
            return hash("x")

        def __eq__(self, other):
            return Liar(0) if self.lying else 0

    for build in (lambda: {Colliding(True), LiarStr("x")}, lambda: {Colliding(True): 1, LiarStr("x"): 2}):
        value = build()
        assert len(value) == 2
        HOOK_CALLS.clear()
        with pytest.raises(TypeError):
            live_values.exact_tree((value,))
        assert HOOK_CALLS == {}
    plain = {Colliding(False), "x"}
    assert live_values.exact_tree(plain) is plain  # 写す葉が無ければ作り直さない
