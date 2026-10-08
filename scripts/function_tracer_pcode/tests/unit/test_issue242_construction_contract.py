# -*- coding: utf-8 -*-
"""Issue #242: runtime ref の構築の契約（`core/runtime_ref_record` と各 ref の検証）。

構築（生成された `__init__` / 自前の `__init__` / `dataclasses.replace` と、既存の `__post_init__`）は、
scalar の subclass の code（`__int__` / `__index__` / `__str__` / `__bool__` / 比較・hash・算術、その型の
metaclass の hook）を **1 度も呼ばない**。値は基底型の slot の値として扱う。ここでは次を固定する:

- 値を偽る subclass（`Liar`: `int()` が 999、`str()` が別の文字列、真偽が逆）を、scalar の field・exact な
  tuple の葉・list・tuple の中の list に入れても、基底型の双子から作った ref と同じ値になり、hook は 0 回。
  owner は exact な tuple だけを写す（list は辿らない）。list を読むのは ref の検証で、読み方は
  `live_values.scalar_int` / `scalar_text`（静的な guard: `test_construction_paths_read_scalars_through_live_values`）。
- 型は identity で見る（metaclass の `__eq__` / `__hash__` が「int と等しい」と答えても subclass を残さない）。
- 共有された tuple の DAG は distinct な tuple ごとに 1 度だけ辿り、共有を保つ。入れ子の深さは再帰の上限に依らない。
- 注釈の表現（`X | None`・`Optional`・`Annotated`・裸の `tuple`）と、field の値の置き場所（`__dict__`・slot・
  class の既定値）に依らない。
"""

from __future__ import annotations

import ast
import collections
import dataclasses
import enum
import json
import pathlib
from typing import Annotated, Any, Dict, List, Optional, Tuple

import pytest

from scripts.function_tracer_pcode.core import runtime_ref_record
from scripts.function_tracer_pcode.core.json_encoding import materialize
from scripts.function_tracer_pcode.core.runtime_ref_record import field_kinds, runtime_ref_record as record_decorator
from scripts.function_tracer_pcode.core.runtime_refs.locations import LocationBaseRef
from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeOpRef
from scripts.function_tracer_pcode.core.runtime_refs.readonly import ReductionAccumulatorProof
from scripts.function_tracer_pcode.core.runtime_refs.unknowns import ExpansionBudgetTruncation
from scripts.function_tracer_pcode.core.semantic_freeze import _capture_runtime_ref
from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

PACKAGE = pathlib.Path(__file__).resolve().parents[2]

# ---------------------------------------------------------------------------
# 値を偽る subclass（hook の呼び出しを数える）
# ---------------------------------------------------------------------------

HOOK_CALLS: "collections.Counter[str]" = collections.Counter()

_LYING_INT = {
    "__int__": lambda self: 999,
    "__index__": lambda self: 999,
    "__float__": lambda self: 999.0,
    "__bool__": lambda self: not int.__bool__(self),
    "__repr__": lambda self: "LIE",
    "__str__": lambda self: "LIE",
    "__format__": lambda self, spec: "LIE",
    "__eq__": lambda self, other: False,
    "__ne__": lambda self, other: True,
    "__hash__": lambda self: 7,
    "__lt__": lambda self, other: True,
    "__le__": lambda self, other: True,
    "__gt__": lambda self, other: True,
    "__ge__": lambda self, other: True,
    "__neg__": lambda self: 999,
    "__add__": lambda self, other: 999,
    "__radd__": lambda self, other: 999,
    "__sub__": lambda self, other: 999,
    "__rsub__": lambda self, other: 999,
    "__mul__": lambda self, other: 999,
    "__mod__": lambda self, other: 999,
    "__rmod__": lambda self, other: 999,
    "__and__": lambda self, other: 999,
    "__or__": lambda self, other: 999,
    "__lshift__": lambda self, other: 999,
    "__rshift__": lambda self, other: 999,
}
_LYING_STR = {
    "__str__": lambda self: "LIE",
    "__repr__": lambda self: "'LIE'",
    "__format__": lambda self, spec: "LIE",
    "__eq__": lambda self, other: False,
    "__ne__": lambda self, other: True,
    "__hash__": lambda self: 7,
    "__lt__": lambda self, other: True,
    "__len__": lambda self: 3,
    "__bool__": lambda self: False,
    "__iter__": lambda self: iter("LIE"),
    "__getitem__": lambda self, key: "L",
    "__contains__": lambda self, item: True,
    "strip": lambda self, *args: "LIE",
    "__add__": lambda self, other: "LIE",
}


def _lying(base: type, name: str, table: Dict[str, Any]) -> type:
    namespace = {}
    for method, implementation in table.items():
        def hook(self, *args, _method=method, _implementation=implementation):
            HOOK_CALLS[f"{name}.{_method}"] += 1
            return _implementation(self, *args)

        namespace[method] = hook
    return type(name, (base,), namespace)


Liar = _lying(int, "Liar", _LYING_INT)
LiarStr = _lying(str, "LiarStr", _LYING_STR)


def _lie(value: Any) -> Any:
    """exact な int / str を値を偽る subclass へ（bool・None・それ以外はそのまま）。"""

    if type(value) is int:
        return Liar(value)
    if type(value) is str:
        return LiarStr(value)
    return value


def _base(value: Any) -> Any:
    """比べるための値: subclass の葉を基底型の slot の値へ（容器は型を保って辿る。subclass の code を呼ばない）。"""

    kind = type(value)
    if kind is tuple or kind is list:
        return (kind.__name__, tuple(_base(item) for item in value))
    if issubclass(kind, enum.Enum):
        return value
    if kind is not bool and issubclass(kind, int):
        return int.__index__(value)
    if issubclass(kind, str):
        return str.__str__(value)
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        return (kind.__qualname__, tuple((item.name, _base(getattr(value, item.name))) for item in dataclasses.fields(value)))
    return value


def _containers(base_value: Any):
    """tuple の field の基底の値から、容器の組合せの variant（list・tuple の中の list）を作る。"""

    if type(base_value) is not tuple or not base_value:
        return
    yield "list", lambda f: [_map(item, f) for item in base_value]
    if any(type(item) is tuple for item in base_value):
        yield "tuple_of_list", lambda f: tuple(
            [_map(x, f) for x in item] if type(item) is tuple else f(item) for item in base_value
        )
    yield "tuple", lambda f: _map(base_value, f)


def _map(value: Any, leaf) -> Any:
    if type(value) is tuple:
        return tuple(_map(item, leaf) for item in value)
    return leaf(value)


def _cases():
    for cls in corpus.REF_CLASSES:
        base = corpus.BASES[cls]()
        kinds = corpus.field_kinds(cls)
        for name, value in base.items():
            kind = kinds.get(name, "object")
            if kind in ("int", "str", "float") and type(value) in (int, str):
                yield pytest.param(cls, name, "scalar", (lambda f, v=value: f(v)), id=f"{cls.__qualname__}.{name}.scalar")
            elif kind == "tuple":
                for label, make in _containers(value):
                    yield pytest.param(cls, name, label, make, id=f"{cls.__qualname__}.{name}.{label}")


def _observe(ref: Any) -> Any:
    stable_key = getattr(type(ref), "stable_key", None)
    return {
        "fields": _base(ref),
        "stable_key": _base(stable_key(ref)) if stable_key else None,
        "json": json.dumps(materialize(ref), sort_keys=True),
    }


@pytest.mark.parametrize("cls, name, label, make", list(_cases()))
def test_lying_subclasses_in_every_position_build_the_base_typed_ref_without_calling_them(cls, name, label, make):
    kwargs = corpus.BASES[cls]()
    twin_kwargs = dict(kwargs, **{name: make(lambda v: v)})
    lying_kwargs = dict(kwargs, **{name: make(_lie)})
    try:
        twin = cls(**twin_kwargs)
    except Exception as error:  # 双子が受理されない形（検証の対象外）: 偽る値でも同じ型の例外で拒む
        HOOK_CALLS.clear()
        with pytest.raises(type(error)):
            cls(**lying_kwargs)
        assert HOOK_CALLS == {}
        return
    HOOK_CALLS.clear()
    built = cls(**lying_kwargs)
    assert HOOK_CALLS == {}, (cls.__qualname__, name, label)
    assert _base(built) == _base(twin)
    if not _holds_list(_base(twin)):
        # 検証が list を tuple にした（または list が無い）ref: 出力（`stable_key`・LEGACY の JSON）も双子と同じ。
        # list のまま受理した値は写さない（owner は list を辿らない）ので、その出力は比べない
        assert _observe(built) == _observe(twin)


def _holds_list(view: Any) -> bool:
    if type(view) is tuple:
        if len(view) == 2 and view[0] == "list" and type(view[1]) is tuple:
            return True
        return any(_holds_list(item) for item in view)
    return False


def test_container_reads_in_validation_use_the_base_slot():
    # 内部の整数は 4、`int()` は 999 を返す subclass: 容器の形によらず 4（main は list で 999 だった）
    kwargs = dict(
        reduction_kind="memory_sum", pointer_base_ref=LocationBaseRef(kind="parameter", parameter_index=0),
        count_parameter_name="c", count_parameter_index=1, limit_expr=None, result_size=4, stride=4,
        element_size=4, index_scale=4,
    )
    HOOK_CALLS.clear()
    for lane_terms in (((Liar(4), Liar(4)),), [(Liar(4), Liar(4))], ([Liar(4), Liar(4)],), [[Liar(4), Liar(4)]]):
        assert ReductionAccumulatorProof(**kwargs, lane_terms=lane_terms).lane_terms == ((4, 4),)
    for counts in ((Liar(4), 1, 1), [Liar(4), 1, 1]):
        truncation = ExpansionBudgetTruncation(kind="k", dedup=counts, referenced_event_ids=[LiarStr("e")])
        assert truncation.dedup == (4, 1, 1) and truncation.referenced_event_ids == ("e",)
    for sizes in ((Liar(4),), [Liar(4)]):
        assert PcodeOpRef(input_sizes=sizes).input_sizes == (4,)
    # 注釈が `Any` の field（owner は写さない）も、検証が数値として読むときは基底型の値
    assert PcodeOpRef(opcode=Liar(4)).opcode == 4
    assert HOOK_CALLS == {}


def test_owner_derived_identity_holds_no_subclass():
    HOOK_CALLS.clear()
    truncation = ExpansionBudgetTruncation(kind="k", owner_scope_key=[Liar(4), (LiarStr("s"), [Liar(5)])])
    assert HOOK_CALLS == {}
    exact = ExpansionBudgetTruncation(kind="k", owner_scope_key=[4, ("s", [5])])
    assert truncation.event_id == exact.event_id
    assert json.dumps(materialize(truncation), sort_keys=True) == json.dumps(materialize(exact), sort_keys=True)
    # 出力が読むのは構築のときに作った identity の写し: subclass を残さないので写せる（C-RS2 の規則のまま）
    assert _capture_runtime_ref(truncation) is not None


# ---------------------------------------------------------------------------
# 型は identity で見る（指摘 B）
# ---------------------------------------------------------------------------

META_CALLS: "collections.Counter[str]" = collections.Counter()


class _ClaimsToBeInt(type):
    """「int と等しい」と答え、自分の hook の呼び出しを数える metaclass。"""

    def __eq__(cls, other):
        META_CALLS["__eq__"] += 1
        return other is int or type.__eq__(cls, other)

    def __ne__(cls, other):
        META_CALLS["__ne__"] += 1
        return not cls.__eq__(other)

    def __hash__(cls):
        META_CALLS["__hash__"] += 1
        return hash(int)

    def __instancecheck__(cls, instance):
        META_CALLS["__instancecheck__"] += 1
        return type.__instancecheck__(cls, instance)

    def __subclasscheck__(cls, subclass):
        META_CALLS["__subclasscheck__"] += 1
        return type.__subclasscheck__(cls, subclass)


class Sneaky(int, metaclass=_ClaimsToBeInt):
    pass


class SneakyStr(str, metaclass=_ClaimsToBeInt):
    pass


class Opaque(metaclass=_ClaimsToBeInt):
    pass


def test_annotation_classification_is_identity_and_calls_no_metaclass_hook():
    @dataclasses.dataclass(frozen=True)
    @record_decorator
    class _AnnotatedWithHookedTypes:
        sneaky: Sneaky = 0
        opaque: Opaque = None
        plain: int = 0

    # 注釈を解決するのは typing（`get_type_hints` の評価は注釈を `==` で比べる。class ごとに 1 度）。owner の分類は
    # 解決した注釈を identity で見るので、「int と等しい」と答える型を int と取り違えない。
    # `Optional[Opaque]` は使わない: typing 自身の `Union` の cache が引数を hash と `==` で引くので、
    # その型は注釈の評価の時点で `Optional[int]` に取り違えられる（owner の外の性質）
    assert dict(field_kinds(_AnnotatedWithHookedTypes)) == {"plain": "scalar"}
    opaque = Opaque()
    META_CALLS.clear()
    built = _AnnotatedWithHookedTypes(Sneaky(3), opaque, Sneaky(4))
    # 構築（値の判定）は hook を呼ばない。写さない分類の field は値もそのまま
    assert META_CALLS == {}
    assert type(built.sneaky) is Sneaky and built.opaque is opaque and type(built.plain) is int


def test_type_checks_are_identity_and_call_no_metaclass_hook():
    opaque = Opaque()
    META_CALLS.clear()
    ref = LocationBaseRef(
        kind="storage", parameter_name=SneakyStr("a"), storage_offset=Sneaky(8),
        storage_identity_key=("register", Sneaky(8), (Sneaky(4),), opaque),
    )
    target = corpus.CallTargetRef(kind="function", function_name="f", is_external=Sneaky(1), library_name="l")
    assert META_CALLS == {}
    assert type(ref.storage_offset) is int and type(ref.parameter_name) is str
    assert [type(ref.storage_identity_key[1]), type(ref.storage_identity_key[2][0])] == [int, int]
    assert ref.storage_identity_key[3] is opaque
    assert target.is_external is True


# ---------------------------------------------------------------------------
# 共有された tuple の DAG と深い入れ子（指摘 A）
# ---------------------------------------------------------------------------


def _dag(levels: int, leaf: Any) -> Tuple[Any, ...]:
    node: Tuple[Any, ...] = (leaf,)
    for _ in range(levels):
        node = (node, node)
    return node


def _distinct_tuples(value: Any) -> int:
    seen = set()
    pending = [value]
    while pending:
        item = pending.pop()
        if type(item) is tuple and id(item) not in seen:
            seen.add(id(item))
            pending.extend(item)
    return len(seen)


def test_shared_tuples_are_walked_once_and_stay_shared(monkeypatch):
    calls = []
    original = runtime_ref_record.exact_scalar

    def counting(value):
        calls.append(value)
        return original(value)

    monkeypatch.setattr(runtime_ref_record, "exact_scalar", counting)
    key = _dag(24, corpus.JInt(1))  # 25 個の distinct な tuple、葉までの経路は 2**24
    ref = LocationBaseRef(kind="storage", storage_identity_key=key)
    written = ref.storage_identity_key
    assert len(calls) == 1  # distinct な subclass の葉 1 つを 1 度だけ写す
    assert _distinct_tuples(written) == _distinct_tuples(key) == 25
    node = written
    while type(node[0]) is tuple:
        assert node[0] is node[1]
        node = node[0]
    assert type(node[0]) is int

    calls.clear()
    exact = _dag(24, 1)
    assert LocationBaseRef(kind="storage", storage_identity_key=exact).storage_identity_key is exact
    assert calls == []


@pytest.mark.parametrize("leaf", [1, corpus.JInt(1)])
def test_deep_tuples_do_not_depend_on_the_recursion_limit(leaf):
    import sys

    deep: Any = (leaf,)
    for _ in range(sys.getrecursionlimit() + 500):
        deep = (deep,)
    ref = LocationBaseRef(kind="storage", storage_identity_key=deep)
    node = ref.storage_identity_key
    if type(leaf) is int:
        assert node is deep
    while type(node) is tuple:
        node = node[0]
    assert type(node) is int


# ---------------------------------------------------------------------------
# 注釈の表現と field の値の置き場所（指摘 D）
# ---------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
@record_decorator
class _Annotations:
    pipe: "int | None" = None
    optional: Optional[int] = None
    annotated: Annotated[int, "meta"] = 0
    optional_annotated: Optional[Annotated[bool, "meta"]] = None
    bare_tuple: tuple = ()
    typing_tuple: Tuple = ()
    builtin_generic: "tuple[int, ...]" = ()
    pipe_tuple: "tuple | None" = None
    two_types: "int | str | None" = None
    mapping: Dict[str, int] = dataclasses.field(default_factory=dict)


def test_annotation_forms_are_classified():
    kinds = dict(field_kinds(_Annotations))
    assert kinds == {
        "pipe": "scalar", "optional": "scalar", "annotated": "scalar", "optional_annotated": "bool",
        "bare_tuple": "tuple", "typing_tuple": "tuple", "builtin_generic": "tuple", "pipe_tuple": "tuple",
    }
    j = corpus.JInt
    built = _Annotations(j(1), j(2), j(3), j(1), (j(4),), (j(5),), (j(6),), (j(7),), j(8))
    assert [type(built.pipe), type(built.optional), type(built.annotated)] == [int, int, int]
    assert built.optional_annotated is True
    assert [type(t[0]) for t in (built.bare_tuple, built.typing_tuple, built.builtin_generic, built.pipe_tuple)] == [int] * 4
    # 複数の型の Union は分類しない（写さない）
    assert type(built.two_types) is corpus.JInt


@dataclasses.dataclass(frozen=True, slots=True)
@record_decorator
class _SlottedBase:
    x: int = 0


@dataclasses.dataclass(frozen=True)
@record_decorator
class _DictOnSlots(_SlottedBase):
    y: int = 0


@dataclasses.dataclass(frozen=True)
@record_decorator
class _InitFalse:
    x: int = 0
    z: int = dataclasses.field(init=False, default=5)
    w: Tuple[int, ...] = dataclasses.field(init=False, default=(corpus.JInt(6),))


@dataclasses.dataclass(frozen=True, init=False)
@record_decorator
class _PartialInit:
    x: int
    unset: int  # 自前の `__init__` が置かない field（値が無い）

    def __init__(self, x):
        object.__setattr__(self, "x", x)


def test_field_storage_does_not_matter():
    j = corpus.JInt
    mixed = _DictOnSlots(j(1), j(2))
    assert (type(mixed.x), type(mixed.y)) == (int, int)
    defaults = _InitFalse(j(1))
    assert (defaults.x, defaults.z, type(defaults.w[0])) == (1, 5, int)
    partial = _PartialInit(j(3))
    assert type(partial.x) is int and not hasattr(partial, "unset")


# ---------------------------------------------------------------------------
# 静的な guard: 構築の経路は scalar を live_values の reader で読む（指摘 C の規則）
# ---------------------------------------------------------------------------

_RAW_CONVERSIONS = frozenset({"int", "str", "float"})


def _construction_paths(path: pathlib.Path):
    """`@runtime_ref_record` の class の構築の入口（`__post_init__` / `__init__` と、ref を作る classmethod /
    staticmethod）と、そこから同じ module の中で呼ぶ関数・method（推移的に）。"""

    tree = ast.parse(path.read_text())
    functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
    methods = {}
    pending = []
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and any(
            isinstance(d, ast.Name) and d.id == "runtime_ref_record" for d in node.decorator_list
        ):
            for item in node.body:
                if isinstance(item, ast.FunctionDef):
                    methods[(node.name, item.name)] = item
                    factory = any(
                        isinstance(d, ast.Name) and d.id in ("classmethod", "staticmethod") for d in item.decorator_list
                    )
                    if item.name in ("__post_init__", "__init__") or factory:
                        pending.append((node.name, item))
    seen = set()
    while pending:
        owner, function = pending.pop()
        if (owner, function.name) in seen:
            continue
        seen.add((owner, function.name))
        yield owner, function
        for node in ast.walk(function):
            if not isinstance(node, ast.Call):
                continue
            callee = node.func
            if isinstance(callee, ast.Name) and callee.id in functions:
                pending.append((None, functions[callee.id]))
            elif (
                isinstance(callee, ast.Attribute) and isinstance(callee.value, ast.Name)
                and callee.value.id in ("self", "cls") and (owner, callee.attr) in methods
            ):
                pending.append((owner, methods[(owner, callee.attr)]))


def _ref_modules():
    return sorted((PACKAGE / "core" / "runtime_refs").glob("*.py")) + [PACKAGE / "core" / "call_target.py"]


def test_construction_paths_read_scalars_through_live_values():
    violations = []
    reached = set()
    for path in _ref_modules():
        for owner, function in _construction_paths(path):
            reached.add(f"{owner}.{function.name}")
            for node in ast.walk(function):
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in _RAW_CONVERSIONS:
                    violations.append(f"{path.name}:{node.lineno} {owner}.{function.name}: {node.func.id}()")
    # 走査が空回りしていない: 検証・自前の構築と、そこから呼ぶ helper に届く
    assert {
        "LocationBaseRef.__post_init__", "CanonicalLocation.__init__", "PcodeOpRef.__post_init__",
        "ReductionAccumulatorProof.__post_init__", "ExpansionBudgetTruncation.__post_init__",
        "None._coerce_opcode", "None._optional_int", "None._bias_key", "None._canonical_budget_value",
        "LocationBaseRef.storage", "PcodeOpRef.from_pcode_op",
    } <= reached
    assert violations == []


def test_the_static_guard_sees_a_raw_conversion(tmp_path):
    module = tmp_path / "sample.py"
    module.write_text(
        "@dataclass(frozen=True)\n@runtime_ref_record\nclass R:\n"
        "    def __post_init__(self):\n        helper(self.x)\n\n"
        "def helper(value):\n    return int(value)\n"
    )
    found = [
        node.func.id
        for _owner, function in _construction_paths(module)
        for node in ast.walk(function)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in _RAW_CONVERSIONS
    ]
    assert found == ["int"]
