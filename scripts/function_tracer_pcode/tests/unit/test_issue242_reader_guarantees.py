# -*- coding: utf-8 -*-
"""Issue #242: reader が返す値の保証（review 4）と、それを使う ref の経路。

reader は「入力をどう読むか」と「返した値が何を保証するか」を持つ。返した値の保証は、外の constructor・
method を呼んだ後の値（再び scalar の subclass を作り得る）を含めない形で成り立たせる:

- `exact_tree`: **組み込みの木**を返す。容器は組み込みの tuple / list / dict / set / frozenset そのもの
  （subclass・named tuple・`OrderedDict` / `Counter` / `deque` は基底の型の容器へ。外の constructor / `_make` を
  呼ばない）、scalar の葉は組み込みの型そのもの、それ以外の葉（enum の member・scalar でない object）は同じ object。
- `scalar_text` / `type_name` / `type_module`: 組み込みの `str` そのもの。
- 型の判定（`is_kind`）と型の名前（`type_name`）は、値の `__class__` / `__getattribute__` も metaclass の
  `__getattribute__` も呼ばない。

ここでは reader 単体（保証を返した値で確かめる）と、実際の ref・比較の経路（loop summary の比較・診断の key・
記録の集め直し）の両方で、基底型の双子と結果・型・拒否が同じで、偽る型の code が 0 回であることを確かめる。
"""

from __future__ import annotations

import collections
import enum
from typing import Any

import pytest

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import HOOK_CALLS, Liar, LiarStr, view


# ---------------------------------------------------------------------------
# 外の code が値を作り直す型（constructor / `_make` で葉を偽る型へ包み直す）と、metaclass の hook
# ---------------------------------------------------------------------------


class Rewrapping(tuple):
    """作るときに int の葉を偽る型へ包み直す tuple の subclass（外の constructor）。"""

    def __new__(cls, items=()):
        return super().__new__(cls, tuple(Liar(item) if type(item) is int else item for item in items))


Pair = collections.namedtuple("Pair", "left right")


class RewrappingPair(Pair):
    """`_make` で葉を偽る型へ包み直す named tuple。"""

    @classmethod
    def _make(cls, iterable):
        return super()._make(Liar(item) if type(item) is int else item for item in iterable)


class RewrappingDict(dict):
    def __init__(self, items=()):
        super().__init__({key: (Liar(value) if type(value) is int else value) for key, value in dict(items).items()})


class Hooked(type):
    """型の属性の読み（`__name__` など）を数え、例外にする metaclass（metaclass の `__getattribute__`）。"""

    def __getattribute__(cls, name):
        if name in ("__name__", "__qualname__", "__module__", "__class__"):
            HOOK_CALLS[f"Hooked.{name}"] += 1
            raise RuntimeError(f"metaclass read {name}")
        return type.__getattribute__(cls, name)


class HookedInt(int, metaclass=Hooked):
    """metaclass が型の名前の読みで例外を投げる int の subclass。instance の `__class__` の読みも数える。"""

    def __getattribute__(self, name):
        HOOK_CALLS[f"HookedInt.{name}"] += 1
        return int.__getattribute__(self, name)


def _is_plain_tree(value: Any, seen=None) -> bool:
    """組み込みの木か（容器は組み込みの型そのもの、scalar の葉は組み込みの型そのもの）。型を identity で見る。"""

    kind = type(value)
    if value is None or kind in (int, str, bool, float, bytes):
        return True
    if kind in (tuple, list, set, frozenset):
        return all(_is_plain_tree(item) for item in (value if kind is not dict else ()))
    if kind is dict:
        return all(_is_plain_tree(key) and _is_plain_tree(item) for key, item in dict.items(value))
    if isinstance(value, enum.Enum):
        return True
    # 組み込みの容器・scalar の subclass は木に残らない
    return not issubclass(kind, (tuple, list, dict, set, frozenset, int, str, float, collections.deque))


# ---------------------------------------------------------------------------
# reader 単体: 返した値の保証
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "make",
    [
        pytest.param(lambda: Rewrapping((1, 2)), id="rewrapping_tuple"),
        pytest.param(lambda: RewrappingPair(1, 2), id="rewrapping_namedtuple"),
        pytest.param(lambda: RewrappingDict({"a": 1}), id="rewrapping_dict"),
        pytest.param(lambda: Pair(Liar(1), LiarStr("x")), id="namedtuple"),
        pytest.param(lambda: collections.OrderedDict([(LiarStr("a"), Liar(1))]), id="ordered_dict"),
        pytest.param(lambda: collections.Counter({LiarStr("a"): 2}), id="counter"),
        pytest.param(lambda: collections.deque([Liar(1), (Liar(2),)]), id="deque"),
        pytest.param(lambda: ("k", [Rewrapping((3,)), {Pair(1, 2)}]), id="nested"),
        pytest.param(lambda: (Pair(1, 2),), id="exact_leaves_in_a_namedtuple"),
    ],
)
def test_exact_tree_returns_a_plain_tree_without_calling_foreign_constructors(make):
    value = make()
    HOOK_CALLS.clear()
    result = live_values.exact_tree(value)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert _is_plain_tree(result), result
    # 双子（同じ値の組み込みの木）と値で同じ
    assert view(result) == view(live_values.exact_tree(result))


def test_exact_tree_keeps_exact_plain_trees_identical():
    value = ("k", [1, ("a", frozenset({2}))], {"x": None})
    assert live_values.exact_tree(value) is value


@pytest.mark.parametrize("value", [HookedInt(1), Liar(1), LiarStr("x")])
def test_type_readers_do_not_run_metaclass_or_instance_hooks(value):
    HOOK_CALLS.clear()
    assert type(live_values.type_name(type(value))) is str
    assert type(live_values.type_module(type(value))) is str
    assert live_values.is_kind(value, (tuple, list)) is False
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_scalar_text_returns_a_builtin_str_even_when_the_object_returns_a_subclass():
    class Speaks:
        def __str__(self):
            return LiarStr("speaks")

    HOOK_CALLS.clear()
    text = live_values.scalar_text(Speaks())
    assert HOOK_CALLS == {}
    assert type(text) is str and text == "speaks"


# ---------------------------------------------------------------------------
# 実際の ref・比較の経路
# ---------------------------------------------------------------------------


def _summary_with_key(key_value: Any):
    """`pairwise_semantic_key` を上書きした `LoopSummaryRef` の派生型（外の method が key を返す）。"""

    from scripts.function_tracer_pcode.tests.unit.test_issue242_entry_matrix import _loop_summary

    base = _loop_summary()
    # path の証明が要る summary（method B の key を作らない）: 比較は外の method が返す key で決まる
    cls = type("KeyedSummary", (type(base),), {
        "pairwise_semantic_key": lambda self: key_value,
        "requires_path_proof": lambda self: True,
    })
    import dataclasses

    return cls(**{f.name: getattr(base, f.name) for f in dataclasses.fields(base) if f.init})


def test_loop_summaries_keyed_by_rewrapping_tuples_compare_on_base_values():
    """P1: 外の constructor が葉を偽る型へ包み直すと、異なる値 1・2 が等しいと読まれていた。"""

    from scripts.function_tracer_pcode.core.runtime_refs.loops import compare_loop_summaries

    twin = compare_loop_summaries(_summary_with_key((1,)), _summary_with_key((2,)))
    left, right = _summary_with_key(Rewrapping((1,))), _summary_with_key(Rewrapping((2,)))
    HOOK_CALLS.clear()
    built = compare_loop_summaries(left, right)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert view(built) == view(twin)
    assert built.status != "equivalent"


@pytest.mark.parametrize(
    "make",
    [
        pytest.param(lambda: Rewrapping((1, 2)), id="rewrapping_tuple"),
        pytest.param(lambda: RewrappingPair(1, 2), id="rewrapping_namedtuple"),
        pytest.param(lambda: HookedInt(1), id="metaclass"),
    ],
)
def test_diagnostic_keys_do_not_rebuild_or_name_values_through_their_own_code(make):
    """P1（診断の key の `repr`）と、型の名前の読み（metaclass）。"""

    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import UnknownValueRef

    origin = make()
    HOOK_CALLS.clear()
    key = UnknownValueRef.opaque(reason="r", origin_kind="k", origin_ref=origin).diagnostic_key()
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert _is_plain_tree(key)


def test_collector_rejects_a_non_iterable_like_its_twin_without_reading_its_type():
    """P2: 拒否の経路の例外の文が型の名前を metaclass で読み、例外の型が変わっていた。"""

    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import ExpansionBudgetCollector

    with pytest.raises(TypeError):
        ExpansionBudgetCollector().extend(1)
    HOOK_CALLS.clear()
    with pytest.raises(TypeError):
        ExpansionBudgetCollector().extend(HookedInt(1))
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


@pytest.mark.parametrize("value", [HookedInt(3), Liar(3), LiarStr("x")])
def test_ref_layer_type_tests_do_not_read_the_class_of_the_value(value):
    """`isinstance(x, C)` は `type(x)` が C の subclass でなければ `x.__class__` を値の `__getattribute__` で読む。"""

    from scripts.function_tracer_pcode.core.runtime_refs import loops
    from scripts.function_tracer_pcode.core.runtime_refs._reading import items, optional_items

    HOOK_CALLS.clear()
    loops._loop_object_key(value)
    loops._loop_object_semantic_key(value)
    for read in (items, optional_items):
        try:
            read(value)
        except TypeError:
            pass  # 双子（基底型の値）の `tuple()` と同じく拒む
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


# ---------------------------------------------------------------------------
# key の出口と型の名前空間の読み
# ---------------------------------------------------------------------------


def _ref_modules():
    import importlib
    import pkgutil

    from scripts.function_tracer_pcode.core import call_target, runtime_refs

    yield call_target
    for info in pkgutil.iter_modules(runtime_refs.__path__):
        yield importlib.import_module(f"{runtime_refs.__name__}.{info.name}")


def _is_key_name(name: str) -> bool:
    return not name.startswith("_") and (name.endswith("_key") or name == "key" or "_key_" in name)


def test_every_public_key_of_the_ref_layer_exits_through_the_owner():
    """公開の key の method / 関数は `runtime_ref_key`（戻り値を組み込みの木にする出口）を通る。新しい key も
    decorator が無ければここで落ちる（受け取った側の比較・hash が外の constructor の作った容器を読まない）。"""

    import inspect

    from scripts.function_tracer_pcode.core.runtime_ref_record import is_runtime_ref_key

    missing, found = [], 0
    for module in _ref_modules():
        for name, value in vars(module).items():
            if inspect.isfunction(value) and value.__module__ == module.__name__ and _is_key_name(name):
                found += 1
                if not is_runtime_ref_key(value):
                    missing.append(f"{module.__name__}.{name}")
            if inspect.isclass(value) and value.__module__ == module.__name__:
                for attr, member in vars(value).items():
                    function = getattr(member, "__func__", member)
                    if inspect.isfunction(function) and _is_key_name(attr):
                        found += 1
                        if not is_runtime_ref_key(function):
                            missing.append(f"{module.__name__}.{value.__name__}.{attr}")
    assert found > 50
    assert missing == []


def test_defined_attribute_reads_the_namespace_without_metaclass_hooks():
    HOOK_CALLS.clear()
    assert live_values.defined_attribute(HookedInt, "__add__") is int.__dict__["__add__"]
    assert live_values.defined_attribute(HookedInt, "missing", None) is None
    with pytest.raises(AttributeError):
        live_values.defined_attribute(HookedInt, "missing")
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    # 組み込みの slot の wrapper と関数は class から読んだ値と同じ object
    assert live_values.defined_attribute(KeyError, "__str__") is KeyError.__str__
    assert live_values.defined_attribute(OSError, "__str__") is OSError.__str__


def test_defined_attribute_refuses_types_beyond_the_scan_limit():
    class LongMro(type):
        def mro(cls):
            return [cls] + [object] * (live_values.SCAN_LIMIT + 1)

    deep = LongMro("Deep", (), {})
    with pytest.raises(TypeError):
        live_values.defined_attribute(deep, "__str__")


class HookedError(Exception, metaclass=type("HookedErrorMeta", (type,), {
    "__getattribute__": lambda cls, name: (
        HOOK_CALLS.update({f"HookedErrorMeta.{name}": HOOK_CALLS.get(f"HookedErrorMeta.{name}", 0) + 1})
        or type.__getattribute__(cls, name)
    ),
})):
    """例外の型の属性の読み（`type(error).__str__`）を metaclass で数える例外。"""


@pytest.mark.parametrize(
    "make, text",
    [
        pytest.param(lambda: HookedError("x"), "x", id="one_argument"),
        pytest.param(lambda: HookedError(Liar(3), LiarStr("y")), "(3, 'y')", id="lying_arguments"),
        pytest.param(lambda: HookedError(), "", id="no_argument"),
    ],
)
def test_error_text_does_not_read_the_exception_type_through_its_metaclass(make, text):
    from scripts.function_tracer_pcode.core.call_target import _error_text

    error = make()
    HOOK_CALLS.clear()
    assert _error_text(error) == text
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


# ---------------------------------------------------------------------------
# 独立 review（第 4 回の対応の後）の反例
# ---------------------------------------------------------------------------


class _EqMeta(type):
    """型どうしの `==` を真にし、型の属性の読みを数える metaclass（`type(x) in (...)` は `==` を呼ぶ）。"""

    def __eq__(cls, other):
        HOOK_CALLS["_EqMeta.__eq__"] += 1
        return True

    __hash__ = type.__hash__

    def __getattribute__(cls, name):
        if name not in ("__mro__", "__dict__", "__name__", "__qualname__", "__module__"):
            HOOK_CALLS[f"_EqMeta.{name}"] += 1
        return type.__getattribute__(cls, name)


class EqTuple(tuple, metaclass=_EqMeta):
    pass


def test_exact_tree_tells_container_types_apart_by_identity():
    HOOK_CALLS.clear()
    for value in (EqTuple((1, 2)), {"a": EqTuple((1, 2))}, [EqTuple((Liar(1),))]):
        result = live_values.exact_tree(value)
        assert _is_plain_tree(result), result
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


class _CountingMeta(type):
    """型の属性の読みと `==` をすべて数える metaclass（ABC の `__subclasscheck__` は `__mro__` などを読む）。"""

    def __getattribute__(cls, name):
        HOOK_CALLS[f"_CountingMeta.{name}"] += 1
        return type.__getattribute__(cls, name)

    def __eq__(cls, other):
        HOOK_CALLS["_CountingMeta.__eq__"] += 1
        return type.__eq__(cls, other)

    __hash__ = type.__hash__


class CountedInt(int, metaclass=_CountingMeta):
    pass


@pytest.mark.parametrize("make", [lambda: CountedInt(1), lambda: HookedInt(1), lambda: Liar(1), lambda: LiarStr("x")])
def test_is_kind_with_abstract_bases_does_not_run_hooks_of_the_value_type(make):
    value = make()
    from collections.abc import Iterable, Mapping

    HOOK_CALLS.clear()
    assert live_values.is_kind(value, Mapping) is False
    assert live_values.is_kind(value, (Mapping, enum.Enum)) is False
    assert live_values.is_kind(value, Iterable) is (type(live_values.exact_scalar(value)) is str)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


class _AttributeForger(int):
    """属性の読み（`__getattr__`）で偽の method を返す int の subclass。"""

    def __getattr__(self, name):
        HOOK_CALLS[f"_AttributeForger.{name}"] += 1
        return lambda *args, **kwargs: ("forged",)


def _outcome(call):
    try:
        return ("ok", view(call()))
    except Exception as error:  # 双子と同じ例外の型か
        return ("raised", type(error).__name__)


def test_methods_of_accepted_values_are_named_on_base_values():
    """B2: 未確認の値の method の名前の読みが scalar の subclass の `__getattr__` を呼び、偽の key を返していた。"""

    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopSummaryRef, loop_summary_method_b_key
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    summary = LoopSummaryRef(**corpus.BASES[LoopSummaryRef]())

    class Fake:
        pass

    def fake(**over):
        value = Fake()
        for item in dataclasses.fields(LoopSummaryRef):
            setattr(value, item.name, getattr(summary, item.name))
        value.requires_effect_proof = lambda: False
        value.requires_path_proof = lambda: False
        for name, item in over.items():
            setattr(value, name, item)
        return value

    for field in ("term_descriptor", "side_effect_profile"):
        twin = _outcome(lambda: loop_summary_method_b_key(fake(**{field: 1})))
        HOOK_CALLS.clear()
        built = _outcome(lambda: loop_summary_method_b_key(fake(**{field: _AttributeForger(1)})))
        assert HOOK_CALLS == {}, (field, dict(HOOK_CALLS))
        assert built == twin, field


@pytest.mark.parametrize(
    "make",
    [
        pytest.param(lambda: collections.deque([1]), id="deque"),
        pytest.param(lambda: Pair(1, 2), id="namedtuple"),
        pytest.param(lambda: collections.OrderedDict({"a": 1}), id="ordered_dict"),
        pytest.param(lambda: collections.Counter({"a": 2, "b": 1}), id="counter"),
        pytest.param(lambda: {}.keys(), id="view"),
    ],
)
def test_text_of_values_without_scalar_subclasses_is_the_text_of_the_value(make):
    """N1: 葉に scalar の subclass が無い値の文字列は、元の値の文字列（容器の型の `repr` を保つ）。"""

    from scripts.function_tracer_pcode.core.call_target import _error_text

    value = make()
    assert live_values.scalar_text(value) == str(value)
    assert live_values.scalar_repr(value) == repr(value)
    assert _error_text(ValueError(value)) == str(ValueError(value))
    assert live_values.holds_scalar_subclass(value) is False


@pytest.mark.parametrize(
    "make, text",
    [
        pytest.param(lambda: collections.deque([Liar(1)]), "[1]", id="deque"),
        pytest.param(lambda: Pair(Liar(1), LiarStr("y")), "(1, 'y')", id="namedtuple"),
        pytest.param(lambda: {LiarStr("a"): Liar(1)}.values(), "[1]", id="view"),
    ],
)
def test_text_of_containers_holding_scalar_subclasses_is_the_text_of_the_plain_tree(make, text):
    """意図した差 D5: scalar の subclass を持つ容器は、写した組み込みの容器の文字列（元の型で作り直さない）。"""

    value = make()
    HOOK_CALLS.clear()
    assert live_values.holds_scalar_subclass(value) is True
    assert live_values.scalar_text(value) == text
    assert live_values.scalar_repr(value) == text
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_diagnostic_keys_read_the_stable_key_of_the_original_container():
    """N2: 型の名前と `stable_key` は元の型（容器を写す前）から読む（双子と同じ）。"""

    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import UnknownValueRef

    class Keyed(tuple):
        def stable_key(self):
            return ("sk", Liar(1))

    def key(origin):
        return UnknownValueRef.opaque(reason="r", origin_kind="k", origin_ref=origin).diagnostic_key()[-1]

    HOOK_CALLS.clear()
    assert key(Keyed((1, 2))) == ("diagnostic_origin", ("stable", ("sk", 1)))
    first, second = collections.namedtuple("A", "x"), collections.namedtuple("B", "x")
    assert key(first(1)) != key(second(1))
    assert key(collections.deque([1])) != key([1])
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_budget_scope_keys_read_dict_subclasses_without_hashing_their_keys():
    """N4: `OrderedDict.items()` は key を hash で引き直す: dict の slot で読む。"""

    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import ExpansionBudgetTruncation

    def scope(text):
        return (collections.OrderedDict({text("a"): 1}),)

    twin = ExpansionBudgetTruncation(kind="k", owner_scope_key=scope(str))
    lying = scope(LiarStr)  # 作るときの hash は入力の側（数える前）
    HOOK_CALLS.clear()
    built = ExpansionBudgetTruncation(kind="k", owner_scope_key=lying)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert built.event_id == twin.event_id


def test_declared_return_types_are_read_before_package_code_outside_the_ref_layer():
    """N6: 宣言の戻り型は基底型の値にしてから `core/signature` へ渡す。"""

    from scripts.function_tracer_pcode.core import call_target

    class Function:
        def __init__(self, return_type):
            self.return_type = return_type

        def getReturnType(self):
            return self.return_type

        def getName(self):
            return "f"

        def isExternal(self):
            return False

        def isThunk(self):
            return False

        def getEntryPoint(self):
            return 4096

    for name in ("double", "void", "undefined"):
        twin_ref = call_target.CallTargetRef.from_function(Function(name))
        twin = (call_target.call_target_returns_floating_value(twin_ref), view(call_target.call_target_declared_return_data_types(twin_ref)))
        HOOK_CALLS.clear()
        ref = call_target.CallTargetRef.from_function(Function(LiarStr(name)))
        built = (call_target.call_target_returns_floating_value(ref), view(call_target.call_target_declared_return_data_types(ref)))
        assert HOOK_CALLS == {}, (name, dict(HOOK_CALLS))
        assert built == twin, name


# ---------------------------------------------------------------------------
# owner の分類と key の出口（mutation で検出できなかった保証）
# ---------------------------------------------------------------------------


def _corpus_items():
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    return list(corpus.BASES.items())


def test_record_fields_hold_base_values_for_scalar_subclasses():
    """注釈が dataclass の型の field に来た scalar の subclass は基底型の値（`record` の分類、意図した差 D6）。"""

    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import _field_hints, _kind_of

    checked = 0
    for cls, make in _corpus_items():
        hints = _field_hints(cls)
        for item in dataclasses.fields(cls):
            if not item.init or _kind_of(hints[item.name]) != "record":
                continue
            try:
                built = cls(**{**make(), item.name: Liar(3)})
            except (TypeError, ValueError, AttributeError):
                continue
            value = object.__getattribute__(built, item.name)
            if value is None:
                continue  # 検証が書き直した（ref でない値を落とす）
            assert type(value) is int and value == 3, (cls.__name__, item.name)
            checked += 1
    assert checked >= 5


def _record_class(annotation):
    import typing

    args = [arg for arg in typing.get_args(annotation) if arg is not type(None)] if typing.get_origin(annotation) else [annotation]
    return args[0] if len(args) == 1 and isinstance(args[0], type) else None


def test_public_keys_return_plain_trees_when_record_fields_hold_subclasses_with_their_own_keys():
    """key の出口（`runtime_ref_key`）: record の field に、key を上書きした subclass（外の method）が在っても、
    それを組み合わせた公開の key は組み込みの木（子の key をそのまま組み込む本体の結果を出口が読む）。"""

    import dataclasses
    import inspect

    from scripts.function_tracer_pcode.core.runtime_ref_record import _field_hints, _kind_of

    def foreign_key(self, *args, **kwargs):
        return Rewrapping((1, 2))

    checked = 0
    for cls, make in _corpus_items():
        hints = _field_hints(cls)
        base = make()
        names = [
            name for name, member in vars(cls).items()
            if inspect.isfunction(member) and not name.startswith("_") and (name.endswith("_key") or name == "key")
            and len(inspect.signature(member).parameters) == 1
        ]
        for item in dataclasses.fields(cls):
            original = base.get(item.name)
            kind = _record_class(hints[item.name])
            if not item.init or _kind_of(hints[item.name]) != "record" or original is None or kind is None:
                continue
            subclass = type(f"Keyed{kind.__name__}", (kind,), {"stable_key": foreign_key, "semantic_key": foreign_key})
            try:
                child = subclass(**{f.name: getattr(original, f.name) for f in dataclasses.fields(original) if f.init})
                built = cls(**{**base, item.name: child})
            except (TypeError, ValueError, AttributeError):
                continue
            for name in names:
                HOOK_CALLS.clear()
                try:
                    result = getattr(built, name)()
                except (TypeError, ValueError, AttributeError):
                    continue
                assert _is_plain_tree(result), (cls.__name__, item.name, name, result)
                assert HOOK_CALLS == {}, (cls.__name__, item.name, name, dict(HOOK_CALLS))
                checked += 1
    assert checked >= 10


def test_public_keys_return_plain_trees_when_fields_hold_foreign_containers():
    """key の出口（`runtime_ref_key`）: 注釈が Any の field に外の容器が在っても、公開の key は組み込みの木。"""

    import dataclasses
    import inspect

    from scripts.function_tracer_pcode.core.runtime_ref_record import _field_hints, _kind_of

    checked = 0
    for cls, make in _corpus_items():
        hints = _field_hints(cls)
        names = [
            name for name, member in vars(cls).items()
            if inspect.isfunction(member) and not name.startswith("_") and (name.endswith("_key") or name == "key")
            and len(inspect.signature(member).parameters) == 1
        ]
        if not names:
            continue
        for item in dataclasses.fields(cls):
            if not item.init or _kind_of(hints[item.name]) != "object":
                continue
            try:
                built = cls(**{**make(), item.name: Rewrapping((1, 2))})
            except (TypeError, ValueError, AttributeError):
                continue
            for name in names:
                HOOK_CALLS.clear()
                try:
                    result = getattr(built, name)()
                except (TypeError, ValueError, AttributeError):
                    continue
                assert _is_plain_tree(result), (cls.__name__, item.name, name, result)
                assert HOOK_CALLS == {}, (cls.__name__, item.name, name, dict(HOOK_CALLS))
                checked += 1
    assert checked >= 10


# ---------------------------------------------------------------------------
# 独立 review 2 巡目の反例
# ---------------------------------------------------------------------------


def test_exact_tree_keeps_every_visited_container_alive_while_it_walks():
    """view の反復が作る組は走査の間だけ生きる: 解放された `id` の再利用で別の組の写しを返していた。"""

    lying = [{(f"k{i}", j): Liar(j) for j in range(2)}.items() for i in range(3)]
    twin = [list({(f"k{i}", j): j for j in range(2)}.items()) for i in range(3)]
    HOOK_CALLS.clear()
    assert live_values.exact_tree(lying) == twin
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_ordered_dict_views_are_rejected_without_hashing_their_keys():
    """`OrderedDict` の view の反復は key ごとに node を hash で引き直す: 判定しない（TypeError。葉として残さない）。"""

    mapping = collections.OrderedDict({LiarStr("a"): Liar(1)})
    HOOK_CALLS.clear()
    for view_of in (mapping.keys, mapping.values, mapping.items):
        with pytest.raises(TypeError):
            live_values.exact_tree(view_of())
        with pytest.raises(TypeError):
            live_values.scalar_text(view_of())
        with pytest.raises(TypeError):
            live_values.holds_scalar_subclass(view_of())
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_cycles_without_scalar_subclasses_keep_their_text():
    """閉路の容器: 葉に scalar の subclass が無ければ文字列は双子と同じ（組み込みの木は作れないので `exact_tree` は拒む）。"""

    items: list = []
    items.append(collections.deque([items]))
    assert live_values.scalar_text(items) == str(items)
    assert live_values.holds_scalar_subclass(items) is False
    with pytest.raises(TypeError):
        live_values.exact_tree(items)


@pytest.mark.parametrize(
    "make",
    [
        pytest.param(lambda s, i: OSError(s("a"), s("b")), id="oserror"),
        pytest.param(lambda s, i: OSError(i(2), s("b"), s("f")), id="oserror_filename"),
        pytest.param(lambda s, i: UnicodeDecodeError("utf-8", b"x", 0, 1, s("why")), id="unicode"),
    ],
)
def test_error_text_of_builtin_exceptions_with_their_own_str_matches_the_twin(make):
    from scripts.function_tracer_pcode.core.call_target import _error_text

    twin = _error_text(make(str, int))
    error = make(LiarStr, Liar)  # 作るときの hash（`OSError` の errno の表）は入力の側
    HOOK_CALLS.clear()
    assert _error_text(error) == twin
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_method_of_reads_the_name_before_the_arguments_like_a_method_call():
    class Plain:
        pass

    def boom():
        raise RuntimeError("argument evaluated")

    with pytest.raises(AttributeError):
        Plain().missing(boom())
    with pytest.raises(AttributeError):
        live_values.method_of(Plain(), "missing")(boom())
    assert live_values.method_of(Liar(5), "bit_length")() == 3


def test_budget_values_of_dict_subclasses_with_their_own_items_use_them_like_the_twin():
    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import _canonical_budget_value

    class Renamed(dict):
        def items(self):
            return [("renamed", 1)]

    assert _canonical_budget_value(Renamed({"a": 1})) == {"renamed": 1}
