# -*- coding: utf-8 -*-
"""Issue #242: runtime ref の構築の契約（`core/runtime_ref_record` と各 ref の検証）。

構築（生成された `__init__` / 自前の `__init__` / `dataclasses.replace` と、既存の `__post_init__`）は、
scalar の subclass の code（`__int__` / `__index__` / `__str__` / `__bool__` / 比較・hash・算術、その型の
metaclass の hook）を **1 度も呼ばない**。値は基底型の slot の値として扱う。ここでは次を固定する:

- 値を偽る subclass（`Liar`: `int()` が 999、`str()` が別の文字列、真偽が逆）を、scalar の field・exact な
  tuple の葉・list・tuple の中の list に入れても、基底型の双子から作った ref と同じ値になり、hook は 0 回。
  owner は exact な tuple だけを写す（list は辿らない）。list を読むのは ref の検証で、読み方は
  `live_values` の reader（静的な guard: `test_issue242_construction_guard.py`。factory・入口の引数・API の
  戻り値の行列: `test_issue242_entry_matrix.py`）。
- 型は identity で見る（metaclass の `__eq__` / `__hash__` が「int と等しい」と答えても subclass を残さない）。
- 共有された tuple の DAG は distinct な tuple ごとに 1 度だけ辿り、共有を保つ。入れ子の深さは再帰の上限に依らない。
- 注釈の表現（`X | None`・`Optional`・`Annotated`・裸の `tuple`）と、field の値の置き場所（`__dict__`・slot・
  class の既定値）に依らない。
"""

from __future__ import annotations

import collections
import dataclasses
import enum
import json
from typing import Annotated, Any, Dict, Optional, Tuple

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
from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import HOOK_CALLS, Liar, LiarStr, lie


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
        "json": _json_text(ref),
    }


def _json_text(ref: Any) -> Any:
    """ref の JSON の文字列。JSON の値にならない ref（表現を持たない宣言の object）はその事実（双子と同じかを比べる）。"""

    try:
        return json.dumps(materialize(ref), sort_keys=True)
    except TypeError as error:
        return ("not a JSON value", type(error).__name__)


@pytest.mark.parametrize("cls, name, label, make", list(_cases()))
def test_lying_subclasses_in_every_position_build_the_base_typed_ref_without_calling_them(cls, name, label, make):
    kwargs = corpus.BASES[cls]()
    twin_kwargs = dict(kwargs, **{name: make(lambda v: v)})
    lying_kwargs = dict(kwargs, **{name: make(lie)})
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
_BUILTIN_TYPES = (int, bool, str, float, tuple)


class _ClaimsToBeInt(type):
    """組み込みの scalar 型・tuple のどれとも「等しい」と答え、自分の hook の呼び出しを数える metaclass。"""

    def __eq__(cls, other):
        META_CALLS["__eq__"] += 1
        return other in _BUILTIN_TYPES or type.__eq__(cls, other)

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


def test_supplied_candidate_key_is_compared_on_base_values():
    # 検証が list の key を tuple に作り直して、渡された key と比べる経路（helper の戻り値は guard が信用する
    # 位置なので、振る舞いで固定する）: 葉は基底型の値で比べ、偽る型の `__eq__` を呼ばない
    from scripts.function_tracer_pcode.core.runtime_refs.call_models import CallModelCandidateRef

    def build(leaf):
        signature = ["sig", leaf("sin"), [[leaf("float"), leaf(64)]]]
        provenance = ["prov", leaf("libm")]
        derived = ("call_model_candidate", "p", "sin", ("sig", "sin", (("float", 64),)), ("prov", "libm"))
        supplied = [derived[0], derived[1], derived[2], ["sig", leaf("sin"), [[leaf("float"), leaf(64)]]], ["prov", leaf("libm")]]
        return CallModelCandidateRef(
            provider="p", canonical_symbol="sin", signature_key=signature, provenance_key=provenance, candidate_key=supplied,
        )

    twin = build(lambda value: value)
    HOOK_CALLS.clear()
    built = build(lie)
    assert HOOK_CALLS == {}
    assert built == twin and built.candidate_key == twin.candidate_key
