"""bounded path の能力（positive capability）の固定（Issue #22 PR-22-D、6 回目のレビュー）。

* J19: live な値は owner（`core.live_values` / walker の API）だけで読む（`_live_flow_audit`）。
  監査が空でないこと（禁止した操作をそれぞれ見つけること）も合成の package で確かめる。
* J21: walker が呼ぶ callback の種類（source の構成子・登録した converter・package の
  `Reducer`・record の protocol）は閉じた集合。新しい producer は登録しないと落ちる。
* exact-once: 作業量・出力の byte は 1 つの owner に 1 回だけ数える（property test）。
"""

from __future__ import annotations

import ast
import inspect
import pathlib
import random
from typing import Any, Iterable, List, Set, Tuple

import pytest

from scripts.function_tracer_pcode.tests.unit._package_sources import parse_source
from scripts.function_tracer_pcode.tests.unit import _live_flow_audit as flow

PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]


# ---------------------------------------------------------------------------
# J19: live な値の流れ
# ---------------------------------------------------------------------------


def test_j19_live_values_are_read_only_through_the_owner():
    """bounded path の関数は live な値を owner の API にしか渡さない（違反 0・入口の欠落 0）。"""

    violations, analyzed, _index, missing = flow.audit(PACKAGE_ROOT)
    assert missing == []
    rest, used = flow.undeclared(violations)
    assert rest == [], "\n".join(f"{m}::{q}:{line} {message}" for m, q, line, message in rest)
    # 宣言した依存（#110 / #194）は全部まだ使われている（使われなくなった宣言は消す）
    assert used == set(flow.DECLARED_DEPENDENCIES)
    assert flow.audit.last.declared_callees_used == set(flow.DECLARED_CALLEES)
    # 監査が bounded path を実際に辿っている（入口・record の protocol・reducer・converter から）
    assert len(analyzed) > 400


#: #194（identity key の組み立て）へ bounded path が入る場所: owner の `identity_key_of` を呼ぶ関数
_IDENTITY_KEY_CALLERS = {
    ("core.analysis", "ReturnInfo.json_items"),
    ("proof.obligations.snapshot", "SnapshotFingerprintCodec._freeze"),
    ("proof.obligations.snapshot", "SnapshotFingerprintCodec._freeze_unmetered"),
}


def test_j19_the_declared_dependencies_are_exactly_the_ones_owned_elsewhere():
    """作業量の外の依存は宣言した場所だけ（#194: identity key。#110 の封印と event の契約は接続済み）。

    増えた依存は落ちる（登録しないと通らない）。依存の owner の Issue が片づけば宣言を消す。
    """

    flow.audit(PACKAGE_ROOT)
    callers = flow.audit.last.identity_key_callers
    assert callers == _IDENTITY_KEY_CALLERS, callers
    reasons = list(flow.DECLARED_DEPENDENCIES.values()) + list(flow.DECLARED_CALLEES.values())
    assert all(reason.startswith("#194:") for reason in reasons), reasons


_STUB_LIVE_VALUES = """
def as_int(value): pass
def as_str(value): pass
def attribute(value, name, default=None): pass
def elements_of(value): pass
def builtin_sequence(value): pass
class readable_property(property): pass
def state_setter(fn): return fn
"""

_STUB_READ_LIMITS = """
def elements_within_limit(values, scan=None): pass
def prefix_within_limit(values): pass
"""

_STUB_JSON_ENCODING = """
class Reducer:
    def add(self, element, *, work): pass
    def result(self, *, work): pass
def source_converter(fn): return fn
def each(values, fn=None): pass
class _Policy:
    def dumps(self, value): pass
RESULT_JSON_POLICY = _Policy()
"""

_CASES = """
from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, Reducer, each, source_converter
from scripts.function_tracer_pcode.core.live_values import (
    as_int, as_str, attribute, builtin_sequence, elements_of, readable_property, state_setter,
)
from scripts.function_tracer_pcode.core.read_limits import elements_within_limit, prefix_within_limit
import dataclasses


class IntCall:
    def json_items(self):
        yield "x", int(self.x)

class IsInstance:
    def json_items(self):
        if isinstance(self.x, str):
            yield "x", 1

class AttributeOfField:
    def json_items(self):
        yield "x", self.x.name

class IterateField:
    def json_items(self):
        for value in self.x:
            yield "x", 1

class TruthOfField:
    def json_items(self):
        if self.x:
            yield "x", 1

class CompareField:
    def json_items(self):
        if self.x == 1:
            yield "x", 1

class HashField:
    def json_items(self):
        yield "x", {self.x: 1}

class FormatField:
    def json_items(self):
        yield "x", f"{self.x}"

class MethodOfField:
    def json_items(self):
        yield "x", self.x.to_dict()

class LambdaConverter:
    def json_items(self):
        yield "x", each(self.x, lambda value: value)

class LenField:
    def json_items(self):
        yield "x", len(self.x)

class StrField:
    def json_items(self):
        yield "x", str(self.x)

class GetattrField:
    def json_items(self):
        yield "x", getattr(self.x, "a", None)

class BaseSlotField:
    def json_items(self):
        yield "x", int.__index__(self.x)

class ExternalField:
    def json_items(self):
        yield "x", dataclasses.fields(self.x)

class UnpackField:
    def json_items(self):
        a, b = self.x
        yield "x", a

class NestedFunction:
    def json_items(self):
        def inner():
            return 1
        yield "x", inner()

class ThroughHelper:
    def json_items(self):
        yield "x", _helper(self.x)

def _helper(value):
    return value + 1

@source_converter
def bad_converter(value):
    return value.name

class BadReducer(Reducer):
    def add(self, element, *, work):
        element.fold()
    def result(self, *, work):
        return 1

class OwnedHolder:
    def json_items(self):
        holder = _Holder(self.x)
        yield "x", holder.value.name

class _Holder:
    def __init__(self, value):
        self.value = value

@source_converter
def good_converter(value):
    return as_int(value)

def _stringify(value):
    return str(value)

def _plain_builder(value):
    return value

class AliasAcrossBranches:
    def json_items(self):
        build = _plain_builder
        if self.flag is None:
            build = _stringify
        yield "x", build(self.x)

def _forwarded(**fields):
    return _takes_value(**fields)

def _takes_value(value=None):
    return len(value)

class KwargsForwarding:
    def json_items(self):
        yield "x", _forwarded(value=self.x)

class FilledContainer:
    def json_items(self):
        rows = []
        rows.append(self.x)
        yield "x", rows[0].name

def _key_of(item):
    return item.rank

class KeyCallback:
    def json_items(self):
        yield "x", sorted(elements_of(self.x), key=_key_of)

class TypeCompared:
    def json_items(self):
        if type(self.x) == int:
            yield "x", 1

class TableCall:
    def json_items(self):
        yield "x", {"a": _stringify}["a"](self.x)

class TypeQualname:
    def json_items(self):
        yield "x", type(self.x).__qualname__

class VerifiedMethod:
    def json_items(self):
        items = self.w
        if builtin_sequence(items):
            yield "x", items.index(1)

def _starred(value):
    return value.name

class StarredForwarding:
    def json_items(self):
        rows = [self.x]
        yield "x", _starred(*rows)

class ContainerPlus:
    def json_items(self):
        rows = [] + [self.x]
        yield "x", rows[0].name

class BoundKey:
    def json_items(self):
        rows = [self.x]
        yield "x", sorted(elements_of(self.y), key=rows.__getitem__)

class SelfFilled:
    def __init__(self, x):
        self.rows = []
        self.rows.append(x)

    def json_items(self):
        yield "x", self.rows[0].name

class LaunderedByBox:
    def json_items(self):
        box = _Holder(1)
        box.value = self.x
        yield "x", box.value

_MODULE_ROWS = []
_MODULE_TABLE = {}

class ModuleAppend:
    def json_items(self):
        _MODULE_ROWS.append(self.x)
        yield "x", 1

class ModuleSubscript:
    def json_items(self):
        _MODULE_TABLE["k"] = self.x
        yield "x", 1

class GlobalName:
    def json_items(self):
        global _LAST
        _LAST = self.x
        yield "x", 1

class _SuperBase:
    def helper(self, value):
        return str(value)

class SuperCall(_SuperBase):
    def json_items(self):
        yield "x", super().helper(self.x)

class ExceptAs:
    def json_items(self):
        try:
            yield "x", as_int(self.x)
        except ValueError as exc:
            yield "y", str(exc)

class VerifiedAttribute:
    def json_items(self):
        items = self.w
        if builtin_sequence(items):
            yield "x", items.meta

class OwnerDumps:
    def json_items(self):
        yield "x", RESULT_JSON_POLICY.dumps(self.x)

class ReadableRecord:
    @readable_property
    def label(self):
        return str(self.raw)

class CheckedRecord:
    @state_setter
    def __setattr__(self, name, value):
        if value.flag:
            object.__setattr__(self, name, value)

class Clean:
    def json_items(self):
        yield "a", as_int(self.x)
        if self.x is not None:
            yield "b", self.x
        for value in elements_of(self.y):
            yield "c", as_str(value)
        yield "d", each(self.y, good_converter)
        name = attribute(self.x, "name")
        yield "e", name
        text = self.z
        if type(text) is str:
            yield "f", len(text) + 1
        items = self.w
        if builtin_sequence(items):
            yield "g", len(items)
            for item in items:
                yield "h", item

class ReadLimitElement:
    def json_items(self):
        for value in elements_within_limit(self.y):
            yield "c", str(value)

class ReadLimitPrefix:
    def json_items(self):
        for value in prefix_within_limit(self.y):
            yield "c", value.name

class CleanReadLimits:
    def json_items(self):
        for value in elements_within_limit(self.y):
            yield "c", as_str(value)

class CleanReducer(Reducer):
    def add(self, element, *, work):
        work.charge(1)
        self.last = as_int(element)
    def result(self, *, work):
        return self.last
"""

_EXPECTED_VIOLATIONS = {
    "IntCall.json_items", "IsInstance.json_items", "AttributeOfField.json_items", "IterateField.json_items",
    "TruthOfField.json_items", "CompareField.json_items", "HashField.json_items", "FormatField.json_items",
    "MethodOfField.json_items", "LambdaConverter.json_items", "LenField.json_items", "StrField.json_items",
    "GetattrField.json_items", "BaseSlotField.json_items", "ExternalField.json_items", "UnpackField.json_items",
    "NestedFunction.json_items", "_helper", "bad_converter", "BadReducer.add", "OwnedHolder.json_items",
    # 2 回目の cross-audit が見つけた監査の穴（枝ごとに違う関数の別名・`**kwargs` の転送・容器へ入れた
    # live な値・`key=` の callback・型の `==`・関数の表の呼び出し）
    "_stringify", "_takes_value", "FilledContainer.json_items", "_key_of", "TypeCompared.json_items",
    "TableCall.json_items",
    # 3 回目の cross-audit が見つけた穴（`type(live)` の属性・確かめた容器の method・`*` の転送・
    # 容器の `+`・bound method の `key=`・`self` の field へ入れた live な値）
    "TypeQualname.json_items", "VerifiedMethod.json_items", "_starred", "ContainerPlus.json_items",
    "BoundKey.json_items", "SelfFilled.json_items",
    # 4 回目の cross-audit が見つけた穴（他の object の属性・module の状態・`super()`・`except as`・
    # 確かめた容器の属性・owner の上限の無い API）
    "LaunderedByBox.json_items", "ModuleAppend.json_items", "ModuleSubscript.json_items",
    "GlobalName.json_items", "_SuperBase.helper", "ExceptAs.json_items", "VerifiedAttribute.json_items",
    "OwnerDumps.json_items",
    # 宣言した能力（`readable_property` / `state_setter`）の本体も root として監査する
    "ReadableRecord.label", "CheckedRecord.__setattr__",
    # `core/read_limits` の読みが返す要素も live（owner の関数の戻り値の種類は module ごとの表から）
    "ReadLimitElement.json_items", "ReadLimitPrefix.json_items",
}


def _synthetic_package(root: pathlib.Path) -> pathlib.Path:
    package = root / "scripts" / "function_tracer_pcode"
    (package / "core").mkdir(parents=True)
    (package / "core" / "live_values.py").write_text(_STUB_LIVE_VALUES)
    (package / "core" / "json_encoding.py").write_text(_STUB_JSON_ENCODING)
    (package / "core" / "read_limits.py").write_text(_STUB_READ_LIMITS)
    (package / "cases.py").write_text(_CASES)
    return package


def test_j19_the_audit_finds_every_forbidden_operation_and_accepts_the_owner_api(tmp_path):
    """監査が空の合格にならない: 禁止した操作は 1 つずつ見つかり、owner の API だけの record は通る。"""

    violations, _analyzed, _index, _missing = flow.audit(_synthetic_package(tmp_path), entry_roots=())
    flagged = {qual for module, qual, _line, _message in violations if module == "cases"}
    missed = _EXPECTED_VIOLATIONS - flagged
    assert missed == set(), missed
    assert not {
        "Clean.json_items", "CleanReducer.add", "CleanReducer.result", "good_converter", "CleanReadLimits.json_items",
    } & flagged, [
        v for v in violations if v[1].startswith(("Clean", "good_"))
    ]


# ---------------------------------------------------------------------------
# J21: callback の種類は閉じた集合
# ---------------------------------------------------------------------------


def _package_modules() -> Iterable[Tuple[str, ast.Module]]:
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        relative = path.relative_to(PACKAGE_ROOT)
        if relative.parts[0] == "tests":
            continue
        yield relative.as_posix(), parse_source(path)


def _is_source_converter(decorator: ast.expr) -> bool:
    return (isinstance(decorator, ast.Name) and decorator.id == "source_converter") or (
        isinstance(decorator, ast.Attribute) and decorator.attr == "source_converter"
    )


def _reducer_subclasses() -> Set[Tuple[str, str]]:
    index = flow.PackageIndex(PACKAGE_ROOT)
    reducer = (flow.PKG + ".core.json_encoding", "Reducer")
    return {
        (module[len(flow.PKG) + 1:], cls)
        for (module, cls) in index.classes
        if (module, cls) != reducer and index.subclass_of(module, cls, reducer)
    }


def _converters() -> Set[Tuple[str, str]]:
    found = set()
    for relative, tree in _package_modules():
        for node in tree.body:
            if isinstance(node, ast.FunctionDef) and any(_is_source_converter(d) for d in node.decorator_list):
                found.add((relative, node.name))
    return found


def test_j21_converters_are_module_level_functions_registered_by_decorator_only():
    """converter は module の top-level の関数に decorator で付けたものだけ（入れ子・呼び出しの形を拒む）。"""

    offenders = []
    for relative, tree in _package_modules():
        top_level = {id(node) for node in tree.body}
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and id(node) not in top_level:
                if any(_is_source_converter(d) for d in node.decorator_list):
                    offenders.append(f"{relative}:{node.lineno} nested converter {node.name}")
            if isinstance(node, ast.Call) and _is_source_converter(node.func) and relative != "core/json_encoding.py":
                offenders.append(f"{relative}:{node.lineno} source_converter(...) called directly")
    assert offenders == []


def test_j21_the_walker_rejects_callbacks_that_are_not_registered_capabilities():
    from scripts.function_tracer_pcode.core import json_encoding
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, JsonValueRejected, each, scan

    with pytest.raises(TypeError):
        json_encoding.source_converter(lambda value: value)

    def local(value):
        return value

    with pytest.raises(TypeError):
        json_encoding.source_converter(local)
    with pytest.raises((TypeError, JsonValueRejected)):
        RESULT_JSON_POLICY.prepare(each([1], local))
    with pytest.raises(TypeError):
        scan([1], object())
    # 任意の callable を包む構成子は無い（`metered` は撤去した）
    assert not hasattr(json_encoding, "metered")
    assert "metered" not in json_encoding.__all__


def test_j21_reducers_take_the_walk_work_and_nothing_else():
    """package の `Reducer` は `add(element, *, work)` / `result(*, work)` だけを持つ protocol。"""

    import importlib

    for module, cls in sorted(_reducer_subclasses()):
        kind = getattr(importlib.import_module(flow.PKG + "." + module[: -len(".py")].replace("/", ".")
                                               if module.endswith(".py") else flow.PKG + "." + module), cls)
        add = inspect.signature(kind.add)
        result = inspect.signature(kind.result)
        assert list(add.parameters)[:2] == ["self", "element"] or len(add.parameters) >= 2, (module, cls)
        assert add.parameters["work"].kind is inspect.Parameter.KEYWORD_ONLY, (module, cls)
        assert result.parameters["work"].kind is inspect.Parameter.KEYWORD_ONLY, (module, cls)


# ---------------------------------------------------------------------------
# exact-once: 出力の byte と作業量は 1 つの owner に 1 回だけ数える
# ---------------------------------------------------------------------------


class _Calls:
    """live な値の上書きした special method が呼ばれた回数（bounded path では常に 0）。"""

    count = 0


class _LiveInt(int):
    def __int__(self):
        _Calls.count += 1
        return 7

    def __index__(self):
        _Calls.count += 1
        return 7

    def __repr__(self):
        _Calls.count += 1
        return "7"

    __str__ = __repr__

    def __hash__(self):
        _Calls.count += 1
        return 7

    def __eq__(self, other):
        _Calls.count += 1
        return False

    def __bool__(self):
        _Calls.count += 1
        return False


class _LiveFloat(float):
    def __float__(self):
        _Calls.count += 1
        return 7.0

    def __repr__(self):
        _Calls.count += 1
        return "7.0"

    __str__ = __repr__


class _LiveStr(str):
    def __len__(self):
        _Calls.count += 1
        return 1

    def __str__(self):
        _Calls.count += 1
        return "spoof"

    __repr__ = __str__

    def __iter__(self):
        _Calls.count += 1
        return iter("spoof")

    def __hash__(self):
        _Calls.count += 1
        return 7

    def encode(self, *args, **kwargs):  # noqa: D401 - live な method
        _Calls.count += 1
        return b"spoof"


class _SpoofedClass:
    """`__class__` を偽る object（`isinstance` はこれを int と見る）。"""

    @property
    def __class__(self):  # type: ignore[override]
        _Calls.count += 1
        return int


class _LiveDict(dict):
    def items(self):
        _Calls.count += 1
        return iter(())

    def get(self, key, default=None):
        _Calls.count += 1
        return default

    def __getattribute__(self, name):
        if name not in ("__class__", "__dict__"):
            _Calls.count += 1
        return dict.__getattribute__(self, name)

    def __iter__(self):
        _Calls.count += 1
        return iter(())

    def __len__(self):
        _Calls.count += 1
        return 0


class _LiveList(list):
    def __iter__(self):
        _Calls.count += 1
        return iter(())

    def __len__(self):
        _Calls.count += 1
        return 0


class _Record:
    """package の record（test の module も package の directory の中）。field は live な値。"""

    def __init__(self, **fields):
        self.__dict__.update(fields)

    def json_items(self):
        from scripts.function_tracer_pcode.core.json_encoding import each, flatten

        yield "fields", dict(self.__dict__)
        yield "flat", flatten(self.groups)
        yield "each", each(self.groups)


def _random_plain(rng: random.Random, depth: int = 0) -> Any:
    choice = rng.randrange(9 if depth < 4 else 5)
    if choice == 0:
        return None
    if choice == 1:
        return rng.choice([True, False])
    if choice == 2:
        return rng.choice([0, -1, 7, 2**70, -(2**65)])
    if choice == 3:
        return rng.choice([0.0, -1.5, 1e300, 3.25])
    if choice == 4:
        return rng.choice(["", "a", "é" * rng.randrange(1, 4), "\n\"\\", "\ud800x", "長い" * rng.randrange(5)])
    if choice == 5:
        return [_random_plain(rng, depth + 1) for _ in range(rng.randrange(4))]
    if choice == 6:
        return tuple(_random_plain(rng, depth + 1) for _ in range(rng.randrange(4)))
    if choice == 7:
        return {f"k{index}": _random_plain(rng, depth + 1) for index in range(rng.randrange(4))}
    return _Record(a=_random_plain(rng, depth + 1), groups=[[_random_plain(rng, depth + 2)] for _ in range(rng.randrange(3))])


def _encoded_length(value: Any) -> int:
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    return len(RESULT_JSON_POLICY.dumps(value).encode("utf-8", "surrogatepass"))


@pytest.mark.parametrize("seed", range(40))
def test_exact_once_output_bytes_have_one_owner(seed):
    """`measure` = `prepare` の byte = 書いた JSON の byte。上限ちょうどで通り、1 byte 少なければ止まる。"""

    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, JsonBudgetExhausted

    value = _random_plain(random.Random(seed))
    size = RESULT_JSON_POLICY.measure(value)
    prepared = RESULT_JSON_POLICY.prepare(value, max_bytes=size)
    assert prepared.encoded_bytes == size == _encoded_length(prepared.value())
    if size:
        with pytest.raises(JsonBudgetExhausted):
            RESULT_JSON_POLICY.prepare(value, max_bytes=size - 1)


def _bytes_and_effort(value: Any) -> Tuple[int, int]:
    """同じ走査の出力の byte と作業量（別々の owner に数えさせた量）。"""

    from scripts.function_tracer_pcode.core import json_encoding
    from scripts.function_tracer_pcode.core.json_encoding import LEGACY, RESULT_JSON_POLICY, JsonBudget

    output = JsonBudget(None)
    effort = JsonBudget(None, detached=True)
    json_encoding._Walk(RESULT_JSON_POLICY, LEGACY, output, build=False, effort=effort).run(value)
    return output.consumed, effort.consumed


@pytest.mark.parametrize("seed", range(40))
def test_exact_once_a_caller_work_receives_each_unit_once(seed):
    """`count_into` は呼ぶ側の作業量へ、走査の byte と作業量をそれぞれちょうど 1 回数える。

    byte は `measure` と同じ量、作業量は高速経路が辿り直した分と構成子の空の要素の分（出力の
    byte を持たない仕事）。どちらかを 2 回数える・別の予算へ逃がすと等式が崩れる。
    """

    from scripts.function_tracer_pcode.core.json_encoding import LEGACY, RESULT_JSON_POLICY, JsonBudget

    value = _random_plain(random.Random(seed))
    output, effort = _bytes_and_effort(value)
    assert output == RESULT_JSON_POLICY.measure(value, mode=LEGACY)
    if not _contains_record(value):
        # 組み込みの値だけなら辿り直しは無い: 作業量は byte そのもの
        assert effort == 0
    work = JsonBudget(None)
    RESULT_JSON_POLICY.count_into(value, work, mode=LEGACY)
    assert work.consumed == output + effort
    # 同じ作業量へ 2 回数えれば 2 倍（数えた分は owner にだけ残り、別の予算へ漏れない）
    RESULT_JSON_POLICY.count_into(value, work, mode=LEGACY)
    assert work.consumed == 2 * (output + effort)


def _contains_record(value: Any) -> bool:
    if type(value) is _Record:
        return True
    if type(value) in (list, tuple):
        return any(_contains_record(item) for item in value)
    if type(value) is dict:
        return any(_contains_record(item) for item in value.values())
    return False


def test_exact_once_nested_work_is_counted_into_the_walk_once():
    from scripts.function_tracer_pcode.core.json_encoding import LEGACY, RESULT_JSON_POLICY, scan

    elements = [_random_plain(random.Random(seed)) for seed in range(20)]
    reducer = _DeltaReducer()
    RESULT_JSON_POLICY.prepare(scan(elements, reducer), max_bytes=1 << 30)
    # 入れ子の `count_into` は walk の作業量へ、その走査の byte + 作業量をちょうど 1 回
    assert reducer.deltas == [sum(_bytes_and_effort(element)) for element in elements]


from scripts.function_tracer_pcode.core.json_encoding import Reducer as _Reducer  # noqa: E402


class _DeltaReducer(_Reducer):
    def __init__(self):
        self.deltas: List[int] = []

    def add(self, element, *, work):
        from scripts.function_tracer_pcode.core.json_encoding import LEGACY, RESULT_JSON_POLICY

        before = work.consumed
        RESULT_JSON_POLICY.count_into(element, work, mode=LEGACY)
        self.deltas.append(work.consumed - before)

    def result(self, *, work):
        return len(self.deltas)


# ---------------------------------------------------------------------------
# adversarial: 上書きした special method は bounded path から 1 回も呼ばれない
# ---------------------------------------------------------------------------


def _adversarial_values() -> List[Any]:
    return [
        _LiveInt(3), _LiveFloat(2.5), _LiveStr("abc"), _SpoofedClass(), _LiveDict(a=1), _LiveList([1, 2]),
        (_LiveInt(1), _LiveStr("x")), {"k": _LiveInt(4)}, _Record(a=_LiveInt(5), groups=[[_LiveStr("g")]]),
    ]


@pytest.mark.parametrize("index", range(9))
def test_adversarial_overrides_are_never_called_by_the_bounded_path(index):
    from scripts.function_tracer_pcode.core import live_values
    from scripts.function_tracer_pcode.core.canonical_digest import canonical_fingerprint
    from scripts.function_tracer_pcode.core.json_encoding import (
        LEGACY,
        RESULT_JSON_POLICY,
        JsonBudget,
        JsonValueRejected,
        bounded_evidence,
        bounded_repr,
        builtin_str,
        builtin_view,
        hashable_key,
        value_token,
    )
    from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec

    value = _adversarial_values()[index]
    _Calls.count = 0
    outcomes = []
    for run in (
        lambda: RESULT_JSON_POLICY.prepare(value, max_bytes=1 << 20).value(),
        lambda: RESULT_JSON_POLICY.measure(value, mode=LEGACY, max_bytes=1 << 20),
        lambda: RESULT_JSON_POLICY.materialize(value),
        lambda: RESULT_JSON_POLICY.token_fingerprint(value, work=JsonBudget(1 << 20)),
        lambda: bounded_evidence(value, work=JsonBudget(1 << 20)),
        lambda: bounded_repr(value),
        lambda: builtin_str(value),
        lambda: builtin_view(value),
        lambda: hashable_key(value, JsonBudget(1 << 20)),
        lambda: value_token(value),
        lambda: canonical_fingerprint(value, work=JsonBudget(1 << 20)),
        lambda: SnapshotFingerprintCodec.freeze({"v": value}, budget=JsonBudget(1 << 20)),
        lambda: live_values.plain_scalar(value),
        lambda: live_values.json_scalar(value),
        lambda: live_values.builtin_container(value),
    ):
        try:
            outcomes.append(run())
        except (TypeError, ValueError, JsonValueRejected):
            # 読めない値は拒む（その値の code は呼ばない）
            outcomes.append("rejected")
    assert _Calls.count == 0, outcomes


def test_adversarial_scalar_subclasses_are_written_by_their_base_value():
    """scalar の subclass は基底型の slot の値で書く（上書きした `__int__` / `__float__` / `__str__` の値でない）。"""

    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    _Calls.count = 0
    prepared = RESULT_JSON_POLICY.prepare([_LiveInt(3), _LiveFloat(2.5), _LiveStr("abc")]).value()
    assert prepared == [3, 2.5, "abc"]
    assert [type(item) for item in prepared] == [int, float, str]
    assert _Calls.count == 0


class _LoudError(ValueError):
    def __str__(self):
        _Calls.count += 1
        return "loud"

    __repr__ = __str__

    @property
    def args(self):  # type: ignore[override]
        _Calls.count += 1
        return ("loud",)


class _Opaque:
    def __repr__(self):
        _Calls.count += 1
        return "opaque"

    __str__ = __repr__

    def __getattr__(self, name):
        _Calls.count += 1
        raise AttributeError(name)


def _raise_loud(value):
    raise _LoudError(_LiveStr("x" * 10), _LiveInt(3), _Opaque())


from scripts.function_tracer_pcode.core.json_encoding import source_converter as _source_converter  # noqa: E402

_raise_loud = _source_converter(_raise_loud)


class _LoudReducer(_Reducer):
    def add(self, element, *, work):
        raise _LoudError(_LiveStr("reducer"))

    def result(self, *, work):
        return 0


def test_adversarial_error_paths_do_not_render_live_values():
    """失敗の経路（producer の例外・拒む値・閉路）も live な値の code を呼ばない（別の unbounded な経路を持たない）。"""

    from scripts.function_tracer_pcode.core.json_encoding import (
        RESULT_JSON_POLICY,
        JsonValueRejected,
        each,
        exception_text,
        scan,
    )

    _Calls.count = 0
    with pytest.raises(JsonValueRejected) as rejected:
        RESULT_JSON_POLICY.prepare(each([_Opaque()], _raise_loud))
    assert "_LoudError" in str(rejected.value)
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(scan([_LiveInt(1)], _LoudReducer()))
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare({"opaque": _Opaque()})
    cycle: list = []
    cycle.append(cycle)
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare([_Opaque(), cycle])
    text = exception_text(_LoudError(_LiveStr("x"), _Opaque()))
    assert text.startswith("_LoudError")
    assert _Calls.count == 0


# package の外の code（test の module は package の directory の中なので、外の file 名で compile する）
_OUTSIDE_SOURCE = '''
class OutsideRecord:
    calls = 0

    def __init__(self):
        self.plain = 1

    @property
    def computed(self):
        OutsideRecord.calls += 1
        return 2

    def __getattr__(self, name):
        OutsideRecord.calls += 1
        return 3

    def json_items(self):
        OutsideRecord.calls += 1
        yield "x", 1
'''
_OUTSIDE: dict = {}
exec(compile(_OUTSIDE_SOURCE, "/nonexistent/outside_the_package.py", "exec"), _OUTSIDE)
_OutsideRecord = _OUTSIDE["OutsideRecord"]


def test_code_outside_the_package_is_never_run_by_the_owner():
    """package の外の property・`__getattr__`・`json_items` は呼ばない（instance の値だけを読む）。"""

    from scripts.function_tracer_pcode.core import live_values
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, JsonValueRejected, is_json_record

    record = _OutsideRecord()
    _OutsideRecord.calls = 0
    assert live_values.attribute(record, "plain") == 1
    assert live_values.attribute(record, "computed", "default") == "default"
    assert live_values.attribute(record, "missing", "default") == "default"
    assert live_values.has_attribute(record, "missing") is False
    assert is_json_record(record) is False
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(record)
    assert _OutsideRecord.calls == 0


def test_lazy_sources_are_pulled_only_until_the_budget_stops_them():
    """`flatten` / `each` / `scan` の producer は列を先に作らない（引き出した数は予算で止まる）。"""

    from scripts.function_tracer_pcode.core.json_encoding import (
        RESULT_JSON_POLICY,
        JsonBudgetExhausted,
        each,
        flatten,
        scan,
    )

    pulled = []

    def outer():
        for index in range(1_000_000):
            pulled.append(index)
            yield [index]

    def empty_outer():
        for index in range(1_000_000):
            pulled.append(index)
            yield []

    def plain():
        for index in range(1_000_000):
            pulled.append(index)
            yield index

    for source in (lambda: flatten(outer()), lambda: flatten(empty_outer()), lambda: each(plain()),
                   lambda: scan(plain(), _DeltaReducer()), lambda: scan(plain(), _IdleReducer())):
        pulled.clear()
        with pytest.raises(JsonBudgetExhausted):
            RESULT_JSON_POLICY.prepare(source(), max_bytes=1_000)
        # 上限を超えた 1 つ目で止まる（予算 + 1 個まで）
        assert 0 < len(pulled) <= 1_001


def test_the_walker_reads_identity_keys_only_for_raw_leaves():
    """owner の中で `identity_key_of`（#194）を呼ぶのは LEGACY の生の葉を数える場所だけ。"""

    import ast as _ast

    tree = _ast.parse((PACKAGE_ROOT / "core" / "json_encoding.py").read_text(encoding="utf-8"))
    callers = set()
    for node in tree.body:
        members = node.body if isinstance(node, _ast.ClassDef) else [node]
        for member in members:
            if not isinstance(member, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
                continue
            name = (node.name + "." if isinstance(node, _ast.ClassDef) else "") + member.name
            for inner in _ast.walk(member):
                if isinstance(inner, _ast.Call) and isinstance(inner.func, _ast.Name) and inner.func.id == "identity_key_of":
                    callers.add(name)
    assert callers == {"_Walk.count_raw_leaf"}


# ---------------------------------------------------------------------------
# J22: 入力に比例する仕事の owner（ループ・内包・列を完了させる組み込み）
# ---------------------------------------------------------------------------
#
# bounded path の関数（J19 の監査が辿った関数）のうち、ループ・内包・`tuple()` / `sorted()` などを
# 持ち、作業量 / 予算を引数に取らず（B）、反復ごとに yield もしない（C）ものは、ここで分類する。
# 分類は A〜D だけ（E = owner の無い入力比例の仕事は 0）。関数が増えれば登録しないと落ち、
# 消えれば stale として落ちる。

_A_FIXED = "A: 固定の大きさ（出力 schema の field / 列・定数の組・2 引数の max / min）だけを辿る"
_B_COUNTED = "B: `_counted` が同じ直列化の作業量へ数えた trace / canonical reason（とその写し）だけを辿る"
_B_PREPARED = "B: 準備済みの値（上限 `max_bytes` の中で作った `PreparedJson` の写し）だけを辿る"
_B_BOUND = "B: 上限（`max_bytes` / `sink.work` / 木の計測器）を持ち、辿る前にその上限へ数える"
_B_CAPTURED = (
    "B: 固定の上限（`frozen_representation.CAPTURE_MAX_BYTES`）の中で直列化の owner が"
    "作った表現の写し（組み込みの値だけ）を辿る。写す走査は上限を数えながら辿り、超えた時点で止まる（Issue #219）"
)
_B_SIZED = "B: 木を作る前に `__json_tree_bytes__` で大きさを数え、上限の中でだけ作る"
_B_FROZEN = (
    "B / D(#194): snapshot の作成では `freeze(budget=)` が数えた写し（組み込みの値だけ）を辿る。"
    " proof の obligation の digest（`SnapshotFingerprintCodec.digest` の解析時の呼び出し）は"
    " identity の owner の範囲"
)
_B_SCHEMA_ROWS = "B: G4-b（`finitize_legacy_reasons`）が出力 schema の行数へ切った列を辿る"
_C_LAZY = "C: 1 要素ずつ yield する generator を walker へ渡す（walker が引き出すたびに数える）"
_B_OWNER_ELEMENTS = (
    "B: 作業量を受け取らない record の構築・写し。解析の値の列・mapping は `read_limits.elements_within_limit` /"
    " `items_within_limit` だけで辿る（owner の固定の上限 `SCAN_LIMIT`。辿る前に O(1) で比べ、超えれば"
    " 登録済みの限界）。入れ子の列は 1 つの上限を共有し、深さは `NESTING_LIMIT` まで"
)
_A_FIXED_CALL = "A: 固定の形（呼び出しの keyword・定数の上限の stack の行・型の dataclass の field 名）だけを辿る"
_B_COUNTED_RECORD = (
    "B: record の列の構築・写し。bounded path（G4-b → finish → 最終 envelope）の呼び出しは、渡す列が"
    " 出力 schema の行数以下（G4-b が切った列・pair の失敗の変換の固定の形の record）か、呼ぶ側が同じ"
    " 作業量へ先に数えた列だけ（`test_record_walks_on_the_bounded_path_never_see_uncounted_input`"
    " が実行して確かめる）"
)
_B_DIAGNOSTIC_KEYS = (
    "B: 診断の mapping の key の写しは先頭の `live_values.SCAN_LIMIT` 組まで（`read_limits.prefix_within_limit`。"
    " 残りは件数の marker で、判定には使わない）"
)
_D_IDENTITY = "D(#194): 構造の identity の atom の digest（identity の owner の `core/semantic_snapshot`）"
_A_LIMITATION = "A: 限界の record の構築（target / evidence は登録した限界の場所が作る固定の形の値）"
_C_SKIP_KEY = "C: mapping の key ごとに yield し、読み飛ばすのは 1 つの固定の key（`data_type_obj`）だけ"

_PROPORTIONAL_WORK_OWNERS = {
    ("analysis.effects.models", "StoreEffectProvenance.is_complete"): _A_FIXED,
    **{("checker.cause_aggregate", name): _B_COUNTED for name in (
        "_add_to_group", "_build_root_causes", "_build_unknown_cause_aggregate", "_event_views",
        "_final_attempt_identity", "_final_legacy_attempt", "_freeze_cause", "_in_key_order", "_multiset_rows",
        "_ordered_members", "_payload_occurrence_views", "_plain_reason_payload", "_trace_occurrence_views",
        "build_reason_view", "build_trace_cause_evidence", "completion_counts", "contains_tagged_identity",
        "cyclic_nodes", "freeze_identity", "is_proof_backlog", "recovery_action_key",
        "resolve_occurrence_transitions", "resolve_required_proofs", "select_primary_reason_records",
        "transition_counts", "validate_legacy_cause_key",
    )},
    ("checker.diagnostics", "_mapping_copy"): _A_FIXED,
    ("checker.diagnostics", "unknown_reason_ids"): _B_SCHEMA_ROWS,
    **{("checker.output_preparation", name): _A_FIXED for name in (
        "AuthorityDecisionEnvelope.prepare", "ComposedPreimage.truncated_fields", "OutputMetadata.prepare",
        "OutputMetadata.truncated", "OutputPreparer._raise_exceeded", "OutputPreparer.prepare",
        "_compose_members", "_field_order", "_ordered", "_prepare_member",
        "check_prepared_field_bounds", "compose_result_preimage", "prepare_pair_output",
    )},
    ("checker.output_preparation", "OutputPreparer._prepare_cause_evidence"): _B_PREPARED,
    ("checker.output_preparation", "_attach_budget_diagnostics"): _B_DIAGNOSTIC_KEYS,
    ("checker.output_preparation", "_attach_condition_counters"): _B_DIAGNOSTIC_KEYS,
    ("core.condition_metrics", "pairwise_debug_counters"): _A_FIXED,
    ("checker.output_preparation", "output_contract_policy"): _A_FIXED,
    ("checker.output_schema", "required_headroom_bytes"): _A_FIXED,
    ("checker.output_preparation", "_bounded_utf8_length"): _B_BOUND,
    ("checker.output_preparation", "_rows"): _B_SCHEMA_ROWS,
    **{("checker.output_schema", name): _A_FIXED for name in (
        "_object_bytes", "_superseded_max_bytes", "authority_field_bounds", "conditional_receipt_max_bytes",
        "metadata_field_bounds",
    )},
    ("checker.result", "EquivalenceResult.__post_init__"): _B_COUNTED_RECORD,
    ("checker.result", "EquivalenceResult._has_pending_proof_gate"): _B_COUNTED_RECORD,
    ("checker.result", "EquivalenceResult.is_timeout"): _B_OWNER_ELEMENTS,
    ("checker.result_assembly", "analysis_limitation_result_for_pair"): _B_OWNER_ELEMENTS,
    ("checker.result_assembly", "internal_error_result_for_pair"): _A_FIXED_CALL,
    **{("checker.unknown_reason", name): _B_COUNTED_RECORD for name in (
        "_index_positions", "_optional_tuple_of", "_payload_view", "coerce_unknown_reason_records", "coerce_unknown_recovery_actions",
    )},
    **{("checker.unknown_reason", name): _A_FIXED_CALL for name in (
        "_field_values", "make_internal_v2_reason_diagnostic", "make_unknown_reason",
    )},
    ("core.budget_policy", "raise_expression_size_budget_exceeded"): _A_FIXED,
    ("core.canonical_digest", "_emit"): _B_BOUND,
    ("core.expression", "Expression._to_dict_active"): _B_SIZED,
    ("core.frozen_representation", "_thaw"): _B_CAPTURED,
    ("core.frozen_representation", "_push_children"): _B_CAPTURED,
    ("core.frozen_representation", "_pop_children"): _B_CAPTURED,
    ("core.expression", "_bounded_local_bytes"): _B_BOUND,
    ("core.expression", "runtime_ref_source"): _C_LAZY,
    ("core.runtime_refs.loops", "CountedLoopSummaryRef.json_items"): _A_FIXED,
    ("core.runtime_refs.loops", "LoopTermDescriptorRef.json_items"): _A_FIXED,
    ("core.runtime_refs.loops", "_lane_term_source"): _A_FIXED,
    ("core.runtime_refs.readonly", "ReadonlyReductionTermRef.json_items"): _A_FIXED,
    ("core.runtime_refs.readonly", "ReductionAccumulatorProof.json_items"): _A_FIXED,
    ("core.signature", "FunctionSignature.from_analysis"): _B_OWNER_ELEMENTS,
    ("core.signature", "clone_parameter_descriptor"): _B_OWNER_ELEMENTS,
    **{("proof.cause_identity", name): _B_COUNTED for name in (
        "_tuple", "_tuple_item", "canonical_cause_tuple", "cause_key_from_dict",
    )},
    ("proof.obligations.snapshot", "SnapshotFingerprintCodec._freeze_unmetered"): _B_FROZEN,
    ("proof.obligations.snapshot", "SnapshotFingerprintCodec.sorted_mapping_items"): _B_FROZEN,
    ("proof.obligations.snapshot", "_frozen_repr"): _B_FROZEN,
    ("proof.obligations.snapshot", "_set_members"): _B_FROZEN,
    ("proof.unknown_reason", "UnknownRecoveryPlan.json_items"): _C_LAZY,
    ("proof.unknown_reason", "UnknownRecoveryProofObligation.json_items"): _C_LAZY,
    **{("proof.unknown_reason", name): _B_COUNTED_RECORD for name in (
        "_coerce_evidence_refs", "_coerce_optional_tuple", "coerce_unknown_recovery_proof_obligations",
    )},
    ("proof.unknown_reason", "_registered_recovery_proof_kind_values"): _A_FIXED,
    ("checker.cause_aggregate", "_multiset_row_order"): _B_COUNTED,
    ("checker.cause_aggregate", "primary_reason_record_sort_key"): _B_COUNTED,
    ("checker.output_preparation", "_in_field_order"): _A_FIXED,
    ("checker.result_assembly", "_hypotheses_of"): _B_OWNER_ELEMENTS,
    ("core.budget_policy", "SerializationWork.__init__"): _A_FIXED,
    ("core.canonical_digest", "_Sink._put"): _B_BOUND,
    ("core.canonical_digest", "_Sink.emit_leaf"): _A_FIXED,
    ("core.canonical_digest", "_Sink.emit_string"): _B_BOUND,
    ("core.expression", "_plain_local"): _B_BOUND,
    ("core.semantic_snapshot", "_encode_atoms"): _D_IDENTITY,
    ("core.semantic_snapshot", "_encode_atoms_to_bytes"): _D_IDENTITY,
    ("core.semantic_snapshot", "stable_atoms_digest"): _D_IDENTITY,
    # 検出の穴を塞いだ後に見えた構文（`repr` / `dumps` / `*` / 切り出し / 数えない work 引数）
    ("checker.cause_aggregate", "IdentityPool.intern"): _B_COUNTED,
    ("checker.cause_aggregate", "canonicalize_legacy_cause_key"): _B_COUNTED,
    ("checker.cause_aggregate", "identity_digest"): _B_COUNTED,
    ("core.signature", "_parameter_descriptor_pairs"): _C_SKIP_KEY,
    ("proof.obligations.snapshot", "_fingerprint_json"): _B_FROZEN,
    # `super().__init__` を辿るようにした後に見えた限界の構築
    ("core.errors", "AnalysisLimitation.__init__"): _A_LIMITATION,
    ("core.errors", "_exact_tuple"): _A_LIMITATION,
}


def test_j22_only_the_identity_owner_is_left_as_a_dependency():
    """J22 の分類で「owner の Issue に委ねる（D）」のは identity key の #194 だけ（他は A / B / C で抑える）。"""

    dependencies = {
        key: label for key, label in _PROPORTIONAL_WORK_OWNERS.items() if "D(" in label
    }
    assert dependencies and all("#194" in label for label in dependencies.values()), dependencies


def test_j19_declared_dependencies_are_the_identity_owner_only():
    """宣言した作業量の外の依存（場所と呼び先）は #194 だけ（#110 の宣言は接続で撤去した）。"""

    from scripts.function_tracer_pcode.tests.unit import _live_flow_audit as flow

    reasons = list(flow.DECLARED_DEPENDENCIES.values()) + list(flow.DECLARED_CALLEES.values())
    assert reasons and all(reason.startswith("#194:") for reason in reasons), reasons


def test_j22_every_input_proportional_construct_has_a_work_owner():
    """bounded path の入力に比例し得る仕事は、作業量の owner を持つか、A〜D に分類済み（E は 0）。"""

    _violations, analyzed, index, _missing = flow.audit(PACKAGE_ROOT)
    unowned = flow.unowned_proportional_work(PACKAGE_ROOT, analyzed, index)
    missing = sorted(set(unowned) - set(_PROPORTIONAL_WORK_OWNERS))
    stale = sorted(set(_PROPORTIONAL_WORK_OWNERS) - set(unowned))
    assert missing == [], {key: unowned[key] for key in missing}
    assert stale == [], stale
    assert all(reason[0] in "ABCD" for reason in _PROPORTIONAL_WORK_OWNERS.values())


_OUTSIDE_SETATTR: dict = {}
exec(compile(
    "class LoudSetattr:\n"
    "    calls = 0\n"
    "    def __setattr__(self, name, value):\n"
    "        LoudSetattr.calls += 1\n"
    "        object.__setattr__(self, name, value)\n",
    "/nonexistent/outside_setattr.py", "exec",
), _OUTSIDE_SETATTR)


def test_the_owner_api_never_runs_the_code_of_the_values_it_reads():
    """`live_values` の関数そのもの（読む・書く・真偽・長さ・引く）は値の上書きした code を呼ばない。"""

    from scripts.function_tracer_pcode.core import live_values

    readers = (
        live_values.as_bool, live_values.as_int, live_values.as_float, live_values.as_str, live_values.as_repr,
        live_values.size, live_values.plain_scalar, live_values.json_scalar, live_values.builtin_container,
        lambda value: live_values.lookup(value, "k"), lambda value: list(live_values.items_of(value)),
        lambda value: list(live_values.elements_of(value)), lambda value: live_values.attribute(value, "x"),
        lambda value: live_values.is_kind(value, int),
    )
    for value in _adversarial_values():
        for read in readers:
            _Calls.count = 0
            try:
                read(value)
            except (TypeError, ValueError):
                # 読めない値は拒む（`int("abc")` と同じ ValueError も含む。どちらも値の code は呼ばない）
                pass
            assert _Calls.count == 0, (type(value).__name__, read)
    loud = _OUTSIDE_SETATTR["LoudSetattr"]()
    _OUTSIDE_SETATTR["LoudSetattr"].calls = 0
    with pytest.raises(TypeError):
        live_values.set_state(loud, "x", 1)
    assert _OUTSIDE_SETATTR["LoudSetattr"].calls == 0


class _IdleReducer(_Reducer):
    """要素に何もしない reducer: 引き出しの作業量は walker だけが数える（出力は小さい）。"""

    def add(self, element, *, work):
        pass

    def result(self, *, work):
        return 0


def test_only_terminal_serializations_are_observed_for_the_budget_defaults():
    """予算の既定値の根拠（観測値）に残すのは terminal な直列化だけ（診断の作業量は run ごとに揺れる）。"""

    from scripts.function_tracer_pcode.core.budget_policy import (
        BudgetPolicy,
        budget_observations,
        budget_policy_scope,
        serialization_scope,
    )

    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="diagnostic", target_parts=("d",), terminal=False, max_bytes=1 << 20) as work:
            work.charge(123)
        assert budget_observations() == {}
        with serialization_scope(site="terminal", target_parts=("t",)) as work:
            work.charge(7)
        assert budget_observations() != {}


def test_producer_time_recovery_actions_charge_every_record_they_read():
    """producer 時点の action の構築（`iter_unknown_recovery_actions`）も、読み飛ばす record を 1 件ずつ数える。"""

    import time

    from scripts.function_tracer_pcode.checker.unknown_reason import iter_unknown_recovery_actions, make_unknown_reason
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget, JsonBudgetExhausted

    record = make_unknown_reason("unknown", stage="S")
    started = time.perf_counter()
    with pytest.raises(JsonBudgetExhausted):
        # 同じ集計単位: 最初の 1 件の後は action を作らずに読み飛ばす（それでも数える）
        for _action in iter_unknown_recovery_actions(
            [record] * 1_000_000, primary_by_aggregation_unit=True, work=JsonBudget(10_000),
        ):
            pass
    assert time.perf_counter() - started < 1.0


# ---------------------------------------------------------------------------
# 2 回目の cross-audit: owner の信頼の判定（型の `__module__`・test の directory・proxy・偽の表・enum）
# ---------------------------------------------------------------------------

_SPOOF_SOURCE = '''
import enum
import dataclasses

calls = []

class SpoofedRecord:
    """package の module を名乗る型（`__module__` は書き換えられる）。"""

    def json_items(self):
        calls.append("json_items")
        yield "x", 1

SpoofedRecord.__module__ = "scripts.function_tracer_pcode.core.expression"

class LoudDict(dict):
    def values(self):
        calls.append("values")
        return dict.values(self)

    def get(self, key, default=None):
        calls.append("get")
        return dict.get(self, key, default)

    def __getattribute__(self, name):
        calls.append("getattribute")
        return dict.__getattribute__(self, name)

class LoudField:
    @property
    def _field_type(self):
        calls.append("_field_type")
        return None

class ForgedDataclass:
    __dataclass_fields__ = {"a": LoudField()}

class LoudEnum(enum.Enum):
    A = 1

    def __getattribute__(self, name):
        calls.append("enum_getattribute")
        return object.__getattribute__(self, name)

class LoudMeta(type):
    def __eq__(cls, other):
        calls.append("meta_eq")
        return False

    def __hash__(cls):
        calls.append("meta_hash")
        return 1

class MetaObject(metaclass=LoudMeta):
    pass

class OutsideKey:
    def stable_key(self):
        calls.append("stable_key")
        return ("k",)

def outside_converter(value):
    calls.append("converter")
    return value

from scripts.function_tracer_pcode.core.json_encoding import Reducer as _Base

class OutsideReducer(_Base):
    def add(self, element, *, work):
        calls.append("reducer")

    def result(self, *, work):
        return 0
'''
_SPOOF: dict = {}
exec(compile(_SPOOF_SOURCE, "/nonexistent/spoofing_outside_the_package.py", "exec"), _SPOOF)


def test_the_owner_trusts_code_by_its_file_not_by_the_type_name():
    """package の code かは関数の code の file で決める（`__module__` を名乗っても外の code は呼ばない）。"""

    import types

    from scripts.function_tracer_pcode.core import live_values
    from scripts.function_tracer_pcode.core.json_encoding import (
        RESULT_JSON_POLICY,
        JsonValueRejected,
        identity_key_of,
        is_json_record,
        source_converter,
    )

    calls = _SPOOF["calls"]
    calls.clear()
    record = _SPOOF["SpoofedRecord"]()
    assert is_json_record(record) is False
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(record)
    # 包んだ dict の subclass の method を proxy 経由で呼ばない
    proxy = types.MappingProxyType(_SPOOF["LoudDict"](a=1))
    assert list(live_values.values_of(proxy)) == [1]
    assert live_values.lookup(proxy, "a") == 1
    assert list(live_values.items_of(proxy)) == [("a", 1)]
    # 偽の `__dataclass_fields__` の中身を読まない
    assert live_values.dataclass_field_names(_SPOOF["ForgedDataclass"]()) is None
    # 属性の読み方を上書きした enum は組み込みのままの enum ではない
    assert live_values.builtin_enum(_SPOOF["LoudEnum"].A) is False
    # metaclass が `__eq__` / `__hash__` を持つ型は hash・比較しない
    meta = _SPOOF["MetaObject"]()
    assert live_values.builtin_iterator(meta) is False
    assert live_values.builtin_sequence(meta) is False
    # package の外の `stable_key` / converter は呼ばない・登録しない
    assert identity_key_of(_SPOOF["OutsideKey"]()) == (False, None)
    with pytest.raises(TypeError):
        source_converter(_SPOOF["outside_converter"])
    # package の外の code の reducer は `scan` へ渡せない（`Reducer` の subclass でも）
    from scripts.function_tracer_pcode.core.json_encoding import scan

    with pytest.raises(TypeError):
        scan([1], _SPOOF["OutsideReducer"]())
    assert calls == []


def test_fixtures_are_not_trusted_as_package_code():
    """test / fixture の directory は package の code ではない（test の harness が足す `tests/unit` だけ）。"""

    from scripts.function_tracer_pcode.core import live_values

    fixture = str(PACKAGE_ROOT / "tests" / "fixtures" / "pcode" / "recorded_program.py")
    assert live_values.package_file(fixture) is False
    assert live_values.package_file(str(PACKAGE_ROOT / "core" / "json_encoding.py")) is True
    assert live_values.package_file(__file__) is True  # conftest が `tests/unit` を信頼する


def test_an_effort_stop_reports_at_least_the_limit():
    """作業量（effort）が先に尽きて止めた走査も、超過は上限 + 1 以上として伝える（測った大きさを小さく読ませない）。"""

    from scripts.function_tracer_pcode.core.json_encoding import LEGACY, RESULT_JSON_POLICY, JsonBudgetExhausted

    # reducer の要素（byte を持たない仕事）だけで作業量を使い切る
    with pytest.raises(JsonBudgetExhausted) as stopped:
        RESULT_JSON_POLICY.measure(
            _scan_of_idle_elements(), mode=LEGACY, max_bytes=1_000,
        )
    assert stopped.value.consumed_bytes >= 1_001


def _scan_of_idle_elements():
    from scripts.function_tracer_pcode.core.json_encoding import scan

    return scan(range(1_000_000), _IdleReducer())


# ---------------------------------------------------------------------------
# 3 回目の cross-audit: package の型を継承した外の型・instance の method・owner の読み方の端
# ---------------------------------------------------------------------------

_OUTSIDE_SUBCLASS_SOURCE = '''
from scripts.function_tracer_pcode.core.json_encoding import Tally
from scripts.function_tracer_pcode.core.storage import StorageInfo

calls = []

class PropertyStorage(StorageInfo):
    @property
    def space_name(self):
        calls.append("property")
        return "x"

    @space_name.setter
    def space_name(self, value):
        pass

class GetattributeStorage(StorageInfo):
    def __getattribute__(self, name):
        calls.append("getattribute")
        return object.__getattribute__(self, name)

class EmptyStorage(StorageInfo):
    pass

class OutsideTally(Tally):
    __slots__ = ()

    def __getattribute__(self, name):
        calls.append("tally_getattribute")
        return object.__getattribute__(self, name)

class EmptyTally(Tally):
    __slots__ = ()

import dataclasses

@dataclasses.dataclass
class DataclassStorage(StorageInfo):
    """外の dataclass: `dataclasses` が作る名前（`__repr__`）を外の code で定義する。"""

    def __repr__(self):
        calls.append("repr")
        return "outside"

@dataclasses.dataclass
class EmptyDataclassStorage(StorageInfo):
    pass

def _outside_repr(self):
    calls.append("wrapped_repr")
    return "outside"

_wrap = getattr(dataclasses, "_recursive_repr", None)

class LoudDescriptor:
    def __get__(self, instance, owner=None):
        calls.append("descriptor")
        return "opcode"

    def __set__(self, instance, value):
        pass

class LoudCallable:
    def __call__(self, *args, **kwargs):
        calls.append("callable")

class DescriptorTally(Tally):
    """package の関数を写し、外の descriptor を足した型（関数の数では見分けられない）。"""

    __slots__ = ()
    add = Tally.add
    attribute = LoudDescriptor()

class CallableTally(Tally):
    __slots__ = ()
    add = Tally.add
    result = LoudCallable()

_namespace = {}
exec("def __hash__(self):\\n    return 1\\n", _namespace)

class StringCodeStorage(StorageInfo):
    """dataclass でない body に置いた `<string>` の関数（dataclass が作った関数ではない）。"""

    __hash__ = _namespace["__hash__"]

@dataclasses.dataclass
class WrappedReprStorage(StorageInfo):
    """`dataclasses` の wrapper（同じ code）で外の関数を包み、package の関数を写した型。"""

    json_items = StorageInfo.json_items
    if _wrap is not None:
        __repr__ = _wrap(_outside_repr)
'''
_OUTSIDE_SUBCLASS: dict = {}
exec(compile(_OUTSIDE_SUBCLASS_SOURCE, "/nonexistent/subclassing_outside_the_package.py", "exec"), _OUTSIDE_SUBCLASS)


def test_outside_subclasses_of_package_types_are_not_trusted():
    """package の型を package の外で継承し code を足した型は信頼しない（型の MRO の package の関数を
    呼ばない）。足したのが関数でなくても（descriptor・callable な object・`<string>` の関数）同じ。"""

    from scripts.function_tracer_pcode.core import live_values
    from scripts.function_tracer_pcode.core.json_encoding import (
        RESULT_JSON_POLICY,
        JsonValueRejected,
        Tally,
        is_json_record,
        scan,
    )
    from scripts.function_tracer_pcode.core.storage import StorageInfo

    calls = _OUTSIDE_SUBCLASS["calls"]
    assert live_values.package_type(StorageInfo) and live_values.package_type(Tally)
    names = ["PropertyStorage", "GetattributeStorage", "DataclassStorage", "StringCodeStorage"]
    if _OUTSIDE_SUBCLASS["_wrap"] is not None:
        names.append("WrappedReprStorage")
    # 中身を足さない subclass は信頼する（足した code が無い）
    empty = ("EmptyStorage", "EmptyDataclassStorage")
    # 作るとき（dataclass の `__init__`）の呼び出しは数えない: owner が呼ぶかだけを見る
    records = {name: _OUTSIDE_SUBCLASS[name]() for name in (*names, *empty)}
    tallies = ("OutsideTally", "DescriptorTally", "CallableTally")
    reducers = {name: _OUTSIDE_SUBCLASS[name]("a") for name in (*tallies, "EmptyTally")}
    calls.clear()
    for name in names:
        kind = _OUTSIDE_SUBCLASS[name]
        record = records[name]
        assert live_values.package_type(kind) is False, name
        assert is_json_record(record) is False, name
        with pytest.raises(JsonValueRejected):
            RESULT_JSON_POLICY.prepare(record)
    for name in tallies:
        assert live_values.package_type(_OUTSIDE_SUBCLASS[name]) is False, name
        with pytest.raises(TypeError):
            scan([1], reducers[name])
    for name in empty:
        assert live_values.package_type(_OUTSIDE_SUBCLASS[name]) is True, name
        assert RESULT_JSON_POLICY.prepare(records[name], max_bytes=10_000).value()["space_name"] == ""
    assert live_values.package_type(_OUTSIDE_SUBCLASS["EmptyTally"]) is True
    counted = RESULT_JSON_POLICY.prepare(scan([], reducers["EmptyTally"]), max_bytes=1_000).value()
    assert counted == {}
    assert calls == []


class _InstanceMethodReducer(_Reducer):
    def __init__(self) -> None:
        self.count = 0

    def add(self, element, *, work):
        work.charge(1)
        self.count += 1

    def result(self, *, work):
        return self.count


def test_the_walker_calls_reducer_methods_of_the_type_not_of_the_instance():
    """reducer の `add` / `result` は型の関数を呼ぶ（instance に置いた callable を呼ばない）。"""

    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, scan

    calls: List[str] = []
    reducer = _InstanceMethodReducer()
    reducer.add = lambda *args, **kwargs: calls.append("instance_add")  # type: ignore[method-assign]
    reducer.result = lambda *args, **kwargs: calls.append("instance_result")  # type: ignore[method-assign]
    assert RESULT_JSON_POLICY.prepare(scan([1, 2, 3], reducer), max_bytes=1_000).value() == 3
    assert calls == []


def test_as_bool_reads_the_truth_of_builtin_values_only():
    """`as_bool` は組み込みの値の真偽だけ（mixin の enum は基底型の値、`__bool__` を持つ型は `TypeError`）。"""

    import enum

    from scripts.function_tracer_pcode.core import live_values

    class Number(enum.IntEnum):
        ZERO = 0
        ONE = 1

    class Text(str, enum.Enum):
        EMPTY = ""
        FULL = "a"

    class Plain(enum.Enum):
        A = 0

    class Flags(enum.Flag):
        NONE = 0
        A = 1

    class NoneBool:
        __bool__ = None

    class Truthy:
        pass

    assert live_values.as_bool(Number.ZERO) is False
    assert live_values.as_bool(Number.ONE) is True
    assert live_values.as_bool(Text.EMPTY) is False
    assert live_values.as_bool(Text.FULL) is True
    assert live_values.as_bool(Plain.A) is True
    assert live_values.as_bool(Truthy()) is True
    for value in (Flags.NONE, NoneBool()):
        with pytest.raises(TypeError):
            live_values.as_bool(value)


def test_nested_proxies_are_read_through_the_wrapped_mapping():
    """proxy を重ねた mapping も、包んだ mapping の基底型の method で読む（proxy の method を呼ばない）。"""

    import types

    from scripts.function_tracer_pcode.core import live_values

    inner = _SPOOF["LoudDict"](a=1)
    nested = types.MappingProxyType(types.MappingProxyType(inner))
    calls = _SPOOF["calls"]
    calls.clear()
    assert live_values.builtin_mapping(nested) is None or list(live_values.items_of(nested)) == [("a", 1)]
    plain_nested = types.MappingProxyType(types.MappingProxyType({"a": 1}))
    assert live_values.builtin_mapping(plain_nested) is plain_nested
    assert list(live_values.items_of(plain_nested)) == [("a", 1)]
    assert list(live_values.values_of(plain_nested)) == [1]
    assert live_values.lookup(plain_nested, "a") == 1
    assert calls == []


def test_relative_code_file_names_are_not_package_code():
    """相対の file 名（cwd に依る名前・`<string>`）は package の code ではない。"""

    import os

    from scripts.function_tracer_pcode.core import live_values

    absolute = str(PACKAGE_ROOT / "core" / "json_encoding.py")
    assert live_values.package_file(absolute) is True
    assert live_values.package_file(os.path.relpath(absolute)) is False
    assert live_values.package_file("scripts/function_tracer_pcode/core/json_encoding.py") is False
    assert live_values.package_file("<string>") is False


def test_trust_code_directory_is_called_only_by_the_test_harness():
    """`trust_code_directory` を呼ぶのは test の harness（`tests/conftest.py`）だけ（production は呼ばない）。"""

    callers = []
    for path in PACKAGE_ROOT.rglob("*.py"):
        text = path.read_text(encoding="utf-8")
        if "trust_code_directory(" not in text:
            continue
        for node in ast.walk(ast.parse(text)):
            if isinstance(node, ast.Call):
                func = node.func
                name = func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)
                if name == "trust_code_directory":
                    callers.append(str(path.relative_to(PACKAGE_ROOT)))
    assert sorted(callers) == ["tests/conftest.py"], callers


def test_plain_local_matches_the_encoder_on_cycles_keys_and_proxies():
    """node の local の写しは encoder と同じく循環は `ValueError`・scalar でない key は `TypeError`、
    proxy も数える（共有した容器は何度でも写す）。"""

    import types

    from scripts.function_tracer_pcode.core import expression

    cyclic: list = []
    cyclic.append(cyclic)
    with pytest.raises(ValueError):
        expression._plain_local({"a": cyclic})
    with pytest.raises(TypeError):
        expression._plain_local({(1, 2): 1})
    shared = [1, 2]
    assert expression._plain_local({"a": shared, "b": shared}) == {"a": [1, 2], "b": [1, 2]}
    proxy = types.MappingProxyType({"k": "v" * 100})
    assert expression._plain_local({"p": proxy}) == {"p": {"k": "v" * 100}}
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    # 事前の数え上げも proxy の中の文字列を数える（上限を超えれば書かずに上限 + 1）
    assert expression._bounded_local_bytes(RESULT_JSON_POLICY, {"p": proxy}, 50) == 51


def test_inline_canonical_charges_the_walk_that_found_a_live_value():
    """plain でないと分かって `None` を返した走査も、辿った分を `work` へ数える。"""

    from scripts.function_tracer_pcode.checker import unknown_reason
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget

    work = JsonBudget(10_000)
    value = (tuple(range(200)), _Opaque())
    assert unknown_reason._inline_canonical(value, work=work) is None
    assert work.consumed >= 200


def test_parameter_descriptor_clones_copy_containers_by_their_base_slots():
    """記述子の複製は dict / list を（subclass も）基底型の slot で写す（元の容器を共有せず、上書きを呼ばない）。"""

    from scripts.function_tracer_pcode.core.signature import clone_parameter_descriptor

    calls: List[str] = []

    class LoudMapping(dict):
        def items(self):
            calls.append("items")
            return dict.items(self)

        def keys(self):
            calls.append("keys")
            return dict.keys(self)

        def __iter__(self):
            calls.append("iter")
            return dict.__iter__(self)

        def copy(self):
            calls.append("copy")
            return dict.copy(self)

    class LoudList(list):
        def __iter__(self):
            calls.append("list_iter")
            return list.__iter__(self)

        def copy(self):
            calls.append("list_copy")
            return list.copy(self)

    mapping = LoudMapping(a=1)
    sequence = LoudList([1, 2])
    cloned = clone_parameter_descriptor({"m": mapping, "s": sequence, "n": 3})
    assert cloned == {"m": {"a": 1}, "s": [1, 2], "n": 3}
    assert type(cloned["m"]) is dict and cloned["m"] is not mapping
    assert type(cloned["s"]) is list and cloned["s"] is not sequence
    assert calls == []


def test_builtin_enum_checks_each_member_value_not_only_the_type():
    """型の側の判定を型ごとに cache しても、member の値の判定は member ごと（非 scalar の値は外す）。"""

    import enum

    from scripts.function_tracer_pcode.core import live_values

    class Mixed(enum.Enum):
        SCALAR = 1
        PAIR = (1, 2)

    assert live_values.builtin_enum(Mixed.SCALAR) is True
    assert live_values.builtin_enum(Mixed.PAIR) is False
    assert live_values.builtin_enum(Mixed.SCALAR) is True


# ---------------------------------------------------------------------------
# 4 回目の cross-audit: 汎用の `reversed`・live な key・metaclass・enum の名前・予算の exact-once
# ---------------------------------------------------------------------------


class _IndexedSequence:
    """`__len__` / `__getitem__` だけの列（`reversed()` の汎用の型はこれを呼ぶ）。"""

    def __init__(self, calls):
        self.calls = calls

    def __len__(self):
        self.calls.append("len")
        return 2

    def __getitem__(self, index):
        self.calls.append("getitem")
        return index


def test_generic_reversed_iterators_are_not_builtin_iterators():
    """`reversed(seq)` の汎用の型は包んだ値の `__len__` / `__getitem__` を呼ぶ: 組み込みの iterator ではない。"""

    from scripts.function_tracer_pcode.core import live_values
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, JsonValueRejected, as_list

    calls: List[str] = []
    sequence = _IndexedSequence(calls)
    # `reversed()` を作るときの `__len__` は呼ぶ側の code（owner が呼ぶかだけを見る）
    iterators = [reversed(sequence) for _ in range(3)]
    calls.clear()
    assert live_values.builtin_iterator(iterators[0]) is False
    with pytest.raises(TypeError):
        live_values.elements_of(iterators[0])
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(iterators[1], max_bytes=1_000)
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(as_list(iterators[2]), max_bytes=1_000)
    assert calls == []
    # list の専用の reverse iterator と、非 ASCII の文字列の iterator は組み込みの iterator
    assert live_values.builtin_iterator(reversed([1, 2])) is True
    assert RESULT_JSON_POLICY.prepare(iter("éa"), max_bytes=100).value() == ["é", "a"]


class _LoudKey(str):
    calls: List[str] = []

    def __hash__(self):
        _LoudKey.calls.append("hash")
        return str.__hash__(str.__str__(self))

    def __eq__(self, other):
        _LoudKey.calls.append("eq")
        return False


class _LoudIntKey(int):
    calls: List[str] = []

    def __hash__(self):
        _LoudIntKey.calls.append("hash")
        return 7

    def __eq__(self, other):
        _LoudIntKey.calls.append("eq")
        return False


class _EqOnlyKey(str):
    calls: List[str] = []
    __hash__ = str.__hash__

    def __eq__(self, other):
        _EqOnlyKey.calls.append("eq")
        return False


class _PlainHolder:
    pass


def test_owner_lookups_never_run_the_code_of_stored_keys():
    """instance の状態・mapping の lookup・`OrderedDict` の読み・LEGACY の key の配置は、格納された key の
    `__hash__` / `__eq__` を呼ばない（組み込みの `str` の key だけを組み込みの比較で探す）。"""

    from collections import OrderedDict

    from scripts.function_tracer_pcode.core import live_values
    from scripts.function_tracer_pcode.core.json_encoding import (
        RESULT_JSON_POLICY,
        JsonValueRejected,
        as_dict,
        mapping_of,
    )

    holder = _PlainHolder()
    holder.__dict__[_LoudKey("status")] = 1
    holder.__dict__["plain"] = 2
    ordered = OrderedDict([(_LoudKey("a"), 1), ("b", 2)])
    colliding = {"a": 1}
    colliding[_LoudKey("a")] = 2
    int_keys = {_LoudIntKey(1): "x", _LoudIntKey(2): "y"}
    loud_mapping = {_LoudKey("k"): 1, "j": 2}
    # hash は `str` のままで比較だけを上書きした key（同じ文字列の key と並べると比較が呼ばれる）
    eq_only = {"a": 1}
    eq_only[_EqOnlyKey("a")] = 2
    eq_only_ordered = OrderedDict([("a", 1)])
    eq_only_ordered[_EqOnlyKey("a")] = 2
    _EqOnlyKey.calls.clear()
    # 値を作るときの hash は test の code（owner が呼ぶかだけを見る）
    _LoudKey.calls.clear()
    _LoudIntKey.calls.clear()
    assert live_values.attribute(holder, "status") is None
    assert live_values.attribute(holder, "plain") == 2
    with pytest.raises(TypeError):
        live_values.set_state(holder, "plain", 3)
    assert live_values.lookup(loud_mapping, "k") is None
    assert live_values.lookup(loud_mapping, "j") == 2
    # `OrderedDict` の iterator は key の hash で node を引く: hash を上書きした key の `OrderedDict` は
    # 組み込みの振る舞いの mapping ではない
    assert live_values.builtin_mapping(ordered) is None
    with pytest.raises(TypeError):
        live_values.items_of(ordered)
    # CANONICAL: 組み込みの `str` でない key は一般の経路で衝突を拒む（黙って片方を消さない）
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(colliding, max_bytes=1_000)
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(mapping_of(colliding), max_bytes=1_000)
    # LEGACY: 元の key を新しい dict へ置くのは hash・比較が組み込みの key だけ。hash を上書きした
    # scalar の subclass（JPype の `JInt` の形）は値と同じく基底型の値の key として置く
    placed = RESULT_JSON_POLICY.materialize(as_dict(int_keys))
    assert placed == {1: "x", 2: "y"} and all(type(key) is int for key in placed)
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.materialize(as_dict(eq_only))
    # `OrderedDict` の iterator は同じ hash の key を比べる: 比較を上書きした key の `OrderedDict` は読まない
    assert live_values.builtin_mapping(eq_only_ordered) is None
    with pytest.raises(TypeError):
        list(live_values.items_of(eq_only_ordered))
    assert _EqOnlyKey.calls == []
    assert _LoudKey.calls == []
    assert _LoudIntKey.calls == []


def test_mro_membership_never_runs_a_metaclass_eq():
    """instance の `__dict__` の持ち主の型を MRO の中で探すのは identity（metaclass の `__eq__` を呼ばない）。"""

    from scripts.function_tracer_pcode.core import live_values

    calls: List[str] = []

    class Meta(type):
        def __eq__(cls, other):
            calls.append("meta_eq")
            return False

        __hash__ = type.__hash__

    class Base(metaclass=Meta):
        pass

    class Slotted(Base):
        __slots__ = ()

    value = Slotted()
    value.status = "ok"
    calls.clear()
    assert live_values.attribute(value, "status") in ("ok", None)
    live_values.instance_state(value, "status", None)
    try:
        live_values.set_state(value, "status", "x")
    except TypeError:
        pass
    assert calls == []


def test_builtin_enum_requires_a_builtin_member_name():
    """member の `_name_` が組み込みの `str` でない enum は組み込みのままの enum ではない。"""

    import enum

    from scripts.function_tracer_pcode.core import live_values

    calls: List[str] = []

    class Name(str):
        def __format__(self, spec):
            calls.append("format")
            return "X"

        def __hash__(self):
            calls.append("hash")
            return 1

    class Renamed(enum.Enum):
        A = 1

        def __init__(self, value):
            self._name_ = Name("A")

    calls.clear()
    assert live_values.builtin_enum(Renamed.A) is False
    with pytest.raises(TypeError):
        live_values.as_str(Renamed.A)
    assert calls == []


def test_as_bool_rejects_enums_with_their_own_truth():
    """mixin の enum が真偽・長さを上書きしていれば、plain な enum が `__len__` を持てば `TypeError`
    （`bool()` と違う値を返さない）。`OrderedDict` の subclass は組み込みの容器の真偽。"""

    import enum
    from collections import OrderedDict

    from scripts.function_tracer_pcode.core import live_values

    class Truthy(enum.IntEnum):
        ZERO = 0

        def __bool__(self):
            return True

    class Sized(enum.Enum):
        A = 1

        def __len__(self):
            return 0

    class Ordered(OrderedDict):
        pass

    for value in (Truthy.ZERO, Sized.A):
        with pytest.raises(TypeError):
            live_values.as_bool(value)
    assert live_values.as_bool(Ordered()) is False
    assert live_values.as_bool(Ordered(a=1)) is True


def test_ordered_dict_subclasses_without_overrides_are_builtin_mappings():
    """中身を上書きしない `OrderedDict` の subclass は組み込みの振る舞いの mapping（順は linked list の順）。"""

    from collections import OrderedDict

    from scripts.function_tracer_pcode.core import live_values
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    class Ordered(OrderedDict):
        pass

    value = Ordered([("b", 1), ("a", 2)])
    value.move_to_end("b")
    assert live_values.builtin_mapping(value) is value
    assert list(live_values.items_of(value)) == [("a", 2), ("b", 1)]
    assert RESULT_JSON_POLICY.prepare(value, max_bytes=100).value() == {"a": 2, "b": 1}


def test_large_tuple_keys_are_stringified_within_the_work_only():
    """tuple の key の文字列は `work` の中で 1 回だけ辿って作る（固定の上限で別に止めない）。"""

    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget, stringify_plain_key

    key = tuple(range(70_000))
    work = JsonBudget(None)
    assert stringify_plain_key(key, work) == str(key)
    assert 70_000 < work.consumed < 2 * 70_000 + 10


def test_runtime_ref_effort_is_charged_once_and_not_multiplied_through_the_dag():
    """式の木の見積もりは byte だけ（実際に書く木と同じ）。runtime ref を辿る作業量は distinct な ref ごとに
    1 回だけ呼ぶ側の作業量へ数える（出現の数だけ足さない）。"""

    from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType, estimate_legacy_dict_bytes
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, JsonBudget
    from scripts.function_tracer_pcode.core.runtime_refs.call_arguments import AbiArgumentSlotRef

    from scripts.function_tracer_pcode.core.storage import StorageInfo

    # 末尾の record で高速経路が途中で辿れなくなる ref（辿り直しの作業量を持つ。record の LEGACY の
    # 表現は JSON の object と同じ byte）
    slot = AbiArgumentSlotRef(ordinal=0, storage_identity_key=(tuple(range(200)) + (StorageInfo(space_name="s"),),))
    root = leaf = Expression(ExpressionType.VARIABLE, name="x", size=4, runtime_ref=slot)
    for _ in range(6):
        root = Expression(ExpressionType.BINARY_OP, operator="+", operands=[root, root], size=4)
    actual = len(RESULT_JSON_POLICY.dumps(root._to_dict(set()), default=_enum_name).encode("utf-8"))
    work = JsonBudget(None)
    # 見積もりは実際に書く木の byte と同じ（ref の作業量を byte に混ぜない）
    assert estimate_legacy_dict_bytes(root, work=work) == actual
    single = JsonBudget(None)
    estimate_legacy_dict_bytes(leaf, work=single)
    # ref を辿る作業量は 1 回分（木の中の 64 回の出現ぶんではない）
    assert work.consumed <= single.consumed + 10


def _enum_name(value):
    # LEGACY の木に元のまま置かれた record は、その `json_items` の object として書く（walker が数える形）
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    return RESULT_JSON_POLICY.materialize(value)


def test_a_failed_fast_path_prefix_is_walked_once():
    """LEGACY で高速経路が途中で辿れなくなった容器は、一般の経路で 1 回だけ辿り直す（前半を 2 回数えない）。"""

    from scripts.function_tracer_pcode.core.expression import ExpressionType
    from scripts.function_tracer_pcode.core.json_encoding import LEGACY, RESULT_JSON_POLICY, JsonBudget

    prefix = [7] * 1_000
    value = prefix + [ExpressionType.CONSTANT]
    output = RESULT_JSON_POLICY.measure(value, mode=LEGACY)
    work = JsonBudget(None)
    RESULT_JSON_POLICY.count_into(value, work, mode=LEGACY)
    effort = work.consumed - output
    prefix_bytes = len(RESULT_JSON_POLICY.dumps(prefix)) - 1
    assert effort <= prefix_bytes + 10


def test_exhaustion_reports_the_limit_plus_one_independent_of_walk_history():
    """予算の超過は上限 + 1（前に同じ tuple を辿ったか・cache の当たり方に依らない）。"""

    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, JsonBudgetExhausted

    shared = tuple(range(5_000))
    observed = []
    for _ in range(2):
        with pytest.raises(JsonBudgetExhausted) as stopped:
            RESULT_JSON_POLICY.measure([shared, shared, shared], max_bytes=10_000)
        observed.append(stopped.value.consumed_bytes)
    assert observed == [10_001, 10_001]


def test_a_terminal_scope_stops_at_its_own_limit_under_a_wider_policy():
    """terminal な作業量は自分の上限で止まる（入れ子の scope の policy が大きくても黙って超えない）。"""

    from scripts.function_tracer_pcode.core import budget_policy as bp
    from scripts.function_tracer_pcode.core.errors import ExpressionSizeBudgetExceeded

    with bp.budget_policy_scope(bp.BudgetPolicy(serialization_bytes=100)):
        with pytest.raises(ExpressionSizeBudgetExceeded):
            with bp.serialization_scope(site="outer", target_parts=("x",)) as work:
                with bp.budget_policy_scope(bp.BudgetPolicy(serialization_bytes=10**9)):
                    work.charge(5_000)


def test_no_serialization_scope_starts_inside_a_walk():
    """walk の中（converter・`json_items`）で新しい直列化の作業量を作らない（`JsonBudget` と同じ規則）。"""

    from scripts.function_tracer_pcode.core import budget_policy as bp
    from scripts.function_tracer_pcode.core import json_encoding

    token = json_encoding._ACTIVE_WORK.set(json_encoding.JsonBudget(10**6, detached=True))
    try:
        with pytest.raises(TypeError):
            with bp.serialization_scope(site="inner", target_parts=("x",)):
                pass
    finally:
        json_encoding._ACTIVE_WORK.reset(token)


def test_an_expression_tree_inside_a_walk_is_counted_into_the_walk():
    """walk の中で式の `to_dict()` を呼ぶと、木はその walk の作業量へ数えて作る（別の作業量を開かない）。"""

    from scripts.function_tracer_pcode.core import json_encoding
    from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType

    expr = Expression(ExpressionType.VARIABLE, name="x" * 100, size=4)
    walk_work = json_encoding.JsonBudget(10**6, detached=True)
    token = json_encoding._ACTIVE_WORK.set(walk_work)
    try:
        built = expr.to_dict()
    finally:
        json_encoding._ACTIVE_WORK.reset(token)
    assert built["name"] == "x" * 100
    assert walk_work.consumed >= 100


def test_fingerprints_charge_the_bytes_they_hash():
    """canonical な fingerprint は流した byte（escape・多 byte の文字を含む）を数える。"""

    from scripts.function_tracer_pcode.core.canonical_digest import canonical_fingerprint
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget

    text = "\x01" * 10_000
    work = JsonBudget(None)
    canonical_fingerprint(text, work=work)
    assert work.consumed >= 6 * 10_000


def test_cause_aggregate_copies_are_built_by_the_walk_that_charges_them():
    """cause の集計の写しは、作る走査そのものが作業量へ数える（写しの中身と数えた量が同じ走査）。"""

    from scripts.function_tracer_pcode.checker import cause_aggregate
    from scripts.function_tracer_pcode.core import budget_policy as bp
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY
    from scripts.function_tracer_pcode.core.storage import StorageInfo

    record = StorageInfo(space_name="x" * 500)
    expected = RESULT_JSON_POLICY.prepare(record, max_bytes=10_000)
    with bp.budget_policy_scope(bp.BudgetPolicy(serialization_bytes=10**6)):
        with bp.serialization_scope(site="aggregate", target_parts=("x",)) as work:
            before = work.consumed
            copy = cause_aggregate._prepared_within_work(record)
            charged = work.consumed - before
    assert copy == expected.value()
    assert charged >= expected.encoded_bytes


def test_a_node_limit_stop_reports_at_least_the_byte_limit():
    """node の上限で止めた（terminal でない）作業量も、byte の超過として上限 + 1 以上を伝える。"""

    from scripts.function_tracer_pcode.core import budget_policy as bp
    from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudgetExhausted

    leaf = Expression(ExpressionType.VARIABLE, name="x", size=4)
    root = Expression(ExpressionType.BINARY_OP, operator="+", operands=[leaf, leaf], size=4)
    with bp.budget_policy_scope(bp.BudgetPolicy(serialization_bytes=10**6, serialization_nodes=1)):
        with bp.serialization_scope(site="nodes", target_parts=("x",), terminal=False, max_bytes=1_000) as work:
            with pytest.raises(JsonBudgetExhausted) as stopped:
                work.tree(root, build=False)
    assert stopped.value.consumed_bytes >= 1_001


def test_a_schema_bound_violation_reports_the_field_bound():
    """field の schema の上限を破った違反は、その上限と field の要求量を報告する（envelope の値ではない）。"""

    from scripts.function_tracer_pcode.checker.output_preparation import _violation

    violation = _violation("field exceeds its output schema bound of 64 bytes", None, 74, field_bound=64)
    assert (violation.max_bytes, violation.requested_bytes) == (64, 74)


_J22_CASES = """
import json


def uncharged(values, work):
    for value in values:
        pass


def charged_each(values, work):
    for value in values:
        work.charge(1)


def charged_before(values, work):
    work.charge(len(values))
    for value in values:
        pass


def token_charge_then_loop(values, work):
    work.charge(1)
    for value in values:
        pass


def token_charge_then_sorted(values, work):
    work.charge(1)
    return sorted(values)


def token_charge_then_comprehension(values, work):
    work.charge(1)
    return [value for value in values]


def work_only_to_a_builtin(values, work):
    for value in values:
        repr(work)


def width_then_sorted(values, work):
    work.charge(len(values))
    return sorted(values)


def counted_width_then_comprehension(values, work):
    count = len(values)
    work.charge(count + 1)
    return [value for value in values]


def rebinds_local(values, work):
    kept = []
    kept = values
    work.charge(1)
    return sorted(kept)


def fills_local_in_place(values, work):
    kept = []
    work.charge(1)
    kept += values
    return tuple(kept)


def subscripts_local(values, work):
    box = []
    box.append(values)
    work.charge(1)
    inner = box[0]
    return sorted(inner)


def while_after_token_charge(values, work):
    work.charge(1)
    index = 0
    while index < len(values):
        index += 1


def mentions_without_measuring(values, work):
    work.charge(values is None)
    return sorted(values)


def filled_then_completed(values, work):
    kept = []
    for value in values:
        work.charge(1)
        kept.append(value)
    order = sorted(kept)
    return tuple(order)


def skipping(values):
    for value in values:
        if value is None:
            continue
        yield value


def sorted_then_yield(values):
    for value in sorted(values):
        yield value


def lazy(values):
    for value in values:
        yield value


def sorts(values):
    values.sort()


def writes(value):
    return repr(value) + json.dumps(value)


def unpacks(values):
    return max(*values)


def repeats(count):
    return [None] * count


def slices(values, start):
    return values[start:]


def bounded_slice(text):
    return text[:MAX_CHARS]


def recurses(value):
    return recurses(value)
"""


def test_j22_the_detector_sees_every_proportional_construct_and_every_unowned_loop(tmp_path):
    """J22 の検出が空の合格にならない: 数えない work 引数・読み飛ばす generator・完了させてから yield する
    generator は owner でなく、`sort()` / `repr` / `dumps` / `*` / 繰り返し / 切り出し / 再帰を見つける。"""

    package = _synthetic_package(tmp_path)
    (package / "j22cases.py").write_text(_J22_CASES)
    index = flow.PackageIndex(package)
    module = flow.PKG + ".j22cases"
    owners = {name: flow.work_owner(index, (module, name)) for name in (
        "uncharged", "charged_each", "charged_before", "skipping", "sorted_then_yield", "lazy",
        "token_charge_then_loop", "token_charge_then_sorted", "token_charge_then_comprehension",
        "work_only_to_a_builtin", "width_then_sorted", "counted_width_then_comprehension", "filled_then_completed",
        "rebinds_local", "fills_local_in_place", "subscripts_local", "while_after_token_charge",
        "mentions_without_measuring",
    )}
    assert owners == {
        "uncharged": None, "charged_each": "B", "charged_before": "B", "skipping": None,
        "sorted_then_yield": None, "lazy": "C",
        # 前に数えるのは辿る値の幅（引数が辿る値を参照する charge）でなければ owner でない。列を完成させる
        # 構文も反復と同じ規則。作業量を組み込みへ渡しても数えたことにならない
        "token_charge_then_loop": None, "token_charge_then_sorted": None, "token_charge_then_comprehension": None,
        "work_only_to_a_builtin": None, "width_then_sorted": "B", "counted_width_then_comprehension": "B",
        # 関数の中で数えながら詰めた容器を完成させるのは、詰めた反復の規則で足りる
        "filled_then_completed": "B",
        # 関数の中で作った容器と言えない形（束ね直し・live な入力を `+=` で詰める・中の値を取り出す）、
        # `while` の前の形だけの charge、幅を測らない charge は owner でない
        "rebinds_local": None, "fills_local_in_place": None, "subscripts_local": None,
        "while_after_token_charge": None, "mentions_without_measuring": None,
    }
    constructs = {
        name: flow.proportional_constructs(index.functions[(module, name)])
        for name in ("sorts", "writes", "unpacks", "repeats", "slices", "bounded_slice", "recurses")
    }
    assert constructs["sorts"] and constructs["writes"] and constructs["unpacks"]
    assert constructs["repeats"] and constructs["slices"] and constructs["recurses"]
    assert constructs["bounded_slice"] == []


class _PlainPropertyRecord:
    """test の directory（信頼する code）の型の、宣言していない property と `__setattr__`。"""

    calls: List[str] = []

    @property
    def status(self):
        _PlainPropertyRecord.calls.append("status")
        return "read"

    def __setattr__(self, name, value):
        _PlainPropertyRecord.calls.append("setattr")
        object.__setattr__(self, name, value)


def test_only_declared_properties_and_state_setters_are_capabilities():
    """`attribute()` が呼ぶ property は `readable_property`、`set_state()` が呼ぶ `__setattr__` は
    `state_setter` で宣言したものだけ（package の code でも宣言していなければ呼ばない）。"""

    from scripts.function_tracer_pcode.core import live_values

    record = object.__new__(_PlainPropertyRecord)
    _PlainPropertyRecord.calls.clear()
    assert live_values.attribute(record, "status") is None
    with pytest.raises(TypeError):
        live_values.set_state(record, "status", 1)
    assert _PlainPropertyRecord.calls == []
    with pytest.raises(TypeError):
        live_values.state_setter(len)


def test_declared_dependencies_excuse_only_their_declared_number_of_violations():
    """宣言した依存の場所の違反は宣言した数だけを除く（同じ違反を足しても宣言に紛れ込まない）。"""

    key = next(iter(flow.DECLARED_DEPENDENCY_SITES))
    count = flow.DECLARED_DEPENDENCY_SITES[key]
    module, qual, message = key
    violations = [(module, qual, line, message) for line in range(count + 1)]
    rest, used = flow.undeclared(violations)
    assert len(rest) == 1 and used == {key}
    assert set(flow.DECLARED_DEPENDENCY_SITES) == set(flow.DECLARED_DEPENDENCIES)


def test_the_snapshot_mapping_order_rejects_duplicate_canonical_keys():
    """凍結した mapping の並べ替えは key の JSON で並べ、同じ JSON の key（canonical な重複）は拒む。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec

    ordered = SnapshotFingerprintCodec.sorted_mapping_items((("b", 2), ("a", 1), ("c", 3)))
    assert ordered == (("a", 1), ("b", 2), ("c", 3))
    with pytest.raises(ValueError, match="duplicate canonical semantic keys"):
        SnapshotFingerprintCodec.sorted_mapping_items((("a", 1), ("b", 2), ("a", 3)))


def test_every_counted_record_label_is_checked_at_runtime():
    """「数えてから辿る」record のラベルは、実行して確かめる test の対象と同じ集合（その test は対象の
    うち bounded path の入口を実行して観測する。残りは下の静的な閉包が確かめる）。"""

    from scripts.function_tracer_pcode.tests.unit.test_issue22d_compositional_boundedness import (
        _record_walk_targets,
    )

    labelled = {name for (_module, name), label in _PROPORTIONAL_WORK_OWNERS.items() if label == _B_COUNTED_RECORD}
    assert labelled == set(_record_walk_targets().values())


#: 渡す値の要素の数を抑える呼び出し（作業量へ数えながら渡す generator・読みの上限）。この呼び出しの値は
#: 呼ぶ側の引数に由来しても有界
_COUNTING_CALLS = frozenset({
    "_counted", "elements_within_limit", "items_within_limit", "prefix_within_limit", "copied_within_limit",
})
def _post_init_walked_fields(function) -> set:
    """`__post_init__` が呼び出しへ渡す自分の field（`coerce_*(self.unknown_reasons)` など。構築の keyword）。
    production の `__post_init__` の AST から導く（test に field の一覧を書き写さない）。"""

    found = set()
    for node in ast.walk(function):
        if isinstance(node, ast.Call):
            for argument in (*node.args, *(keyword.value for keyword in node.keywords)):
                if (
                    isinstance(argument, ast.Attribute) and isinstance(argument.value, ast.Name)
                    and argument.value.id == "self"
                ):
                    found.add(argument.attr)
    return found


def _call_name(func: ast.expr) -> Optional[str]:
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        return func.attr
    return None


def _parameters(function) -> List[str]:
    args = function.args
    names = [arg.arg for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs)]
    names += [arg.arg for arg in (args.vararg, args.kwarg) if arg is not None]
    return names


def _own_statements(function):
    """関数の本体の node（入れ子の関数・class の中は除く）。"""

    pending = list(function.body)
    while pending:
        node = pending.pop()
        yield node
        for child in ast.iter_child_nodes(node):
            if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
                pending.append(child)


class _Summaries:
    """package の関数の戻り値へ流れる引数の名前（関数ごとに 1 度だけ。再帰の途中は `None` = 保守的）。"""

    def __init__(self, index):
        self.index = index
        self.memo: dict = {}
        self.active: set = set()

    def resolve(self, module: str, func: ast.expr):
        if isinstance(func, ast.Name):
            key = (module, func.id)
            if key in self.index.functions:
                return key
            imported = self.index.imports.get(module, {}).get(func.id)
            if imported is not None and imported in self.index.functions:
                return imported
        return None

    def returns(self, key):
        if key in self.memo:
            return self.memo[key]
        if key in self.active:
            return None
        self.active.add(key)
        try:
            flow_of = _Forwarding(self.index.functions[key], key[0], self)
            found: Set[str] = set()
            for node in flow_of.nodes:
                if isinstance(node, (ast.Return, ast.Yield, ast.YieldFrom)) and node.value is not None:
                    found |= flow_of.of(node.value)
        finally:
            self.active.discard(key)
        self.memo[key] = found
        return found


class _Forwarding:
    """関数の中で、どの引数の値がどの式へ流れるか（代入・反復・with を不動点まで）。数える呼び出し・
    比較・否定で止まり、package の関数の呼び出しは戻り値へ流れる引数だけを通す（解決できない呼び出しは
    全部の引数を通す: 保守的）。"""

    def __init__(self, function, module: str, summaries: "_Summaries"):
        self.module = module
        self.summaries = summaries
        self.taint = {name: {name} for name in _parameters(function)}
        nodes = list(_own_statements(function))
        self.nodes = nodes
        for _ in range(12):
            changed = False
            for node in nodes:
                for targets, value in self._bindings(node):
                    flow_in = self.of(value)
                    for target in targets:
                        for name in (n.id for n in ast.walk(target) if isinstance(n, ast.Name)):
                            before = self.taint.setdefault(name, set())
                            if not flow_in <= before:
                                before |= flow_in
                                changed = True
            if not changed:
                break

    @staticmethod
    def _bindings(node):
        if isinstance(node, ast.Assign):
            yield node.targets, node.value
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)) and node.value is not None:
            yield [node.target], node.value
        elif isinstance(node, (ast.For, ast.AsyncFor)):
            yield [node.target], node.iter
        elif isinstance(node, ast.comprehension):
            yield [node.target], node.iter
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                if item.optional_vars is not None:
                    yield [item.optional_vars], item.context_expr
        elif isinstance(node, ast.NamedExpr):
            yield [node.target], node.value

    def of(self, expr) -> Set[str]:
        if expr is None:
            return set()
        if isinstance(expr, ast.Name):
            return set(self.taint.get(expr.id, ()))
        if isinstance(expr, ast.IfExp):
            # 条件は値へ流れない（どちらかの枝の値）
            return self.of(expr.body) | self.of(expr.orelse)
        if isinstance(expr, ast.Compare) or (isinstance(expr, ast.UnaryOp) and isinstance(expr.op, ast.Not)):
            # 比較・否定の値は真偽（辿る列を持たない）
            return set()
        if isinstance(expr, ast.Call):
            if _call_name(expr.func) in _COUNTING_CALLS:
                return set()
            key = self.summaries.resolve(self.module, expr.func)
            flows = None if key is None else self.summaries.returns(key)
            if flows is not None:
                params = _parameters(self.summaries.index.functions[key])
                found: Set[str] = set()
                for position, arg in enumerate(expr.args):
                    if isinstance(arg, ast.Starred) or position >= len(params) or params[position] in flows:
                        found |= self.of(arg)
                for keyword in expr.keywords:
                    if keyword.arg is None or keyword.arg in flows:
                        found |= self.of(keyword.value)
                return found
        found = set()
        for child in ast.iter_child_nodes(expr):
            if not isinstance(child, ast.Lambda):
                found |= self.of(child)
        return found


def _forwarded(index, caller, target, walked: Set[str]) -> Set[str]:
    """`caller` が `target` を呼ぶ式で、`target` が辿る入力（`walked`）へ流れる `caller` の引数の名前。
    呼ぶ式を見つけられなければ（`replace` など）、全部の引数を渡すとみなす（保守的）。"""

    function = index.functions[caller]
    flow_of = _Forwarding(function, caller[0], _Summaries(index))
    module, qual = target
    owner_cls, _, method = qual.rpartition(".")
    target_function = index.functions.get(target)
    if method == "__post_init__":
        names = {owner_cls}
        positional: List[str] = []
    else:
        names = {method}
        positional = _parameters(target_function) if target_function is not None else []
    forwarded: Set[str] = set()
    matched = False
    for node in flow_of.nodes:
        if not (isinstance(node, ast.Call) and _call_name(node.func) in names):
            continue
        matched = True
        params = list(positional)
        if params and params[0] in ("self", "cls") and isinstance(node.func, ast.Attribute):
            receiver = params.pop(0)
            if receiver in walked:
                forwarded |= flow_of.of(node.func.value)
        for position, arg in enumerate(node.args):
            name = params[position] if position < len(params) else None
            if isinstance(arg, ast.Starred) or name is None or name in walked:
                forwarded |= flow_of.of(arg)
        for keyword in node.keywords:
            if keyword.arg is None or keyword.arg in walked:
                forwarded |= flow_of.of(keyword.value)
    if not matched:
        return set(_parameters(function))
    return forwarded


def _walked_inputs(index, target) -> Set[str]:
    _module, qual = target
    method = qual.rpartition(".")[2]
    function = index.functions.get(target)
    if method == "__post_init__":
        return _post_init_walked_fields(function) if function is not None else set()
    return set(_parameters(function)) if function is not None else set()


def test_counted_record_functions_reach_the_bounded_path_only_through_bounding_callers():
    """「数えてから辿る」record の関数が辿る入力を、bounded path の呼び出しの辺（監査が解決したもの）で遡る:
    呼ぶ側が自分で作った値（引数に由来しない値・数える呼び出しを通した値）を渡す経路で終わり、入口の
    引数（live な入力）を数えずにそのまま辿る経路は無い。固定の形の構築も、自分の引数を渡すなら中継として遡る。"""

    _violations, _analyzed, index, _missing = flow.audit(PACKAGE_ROOT)
    callers = flow.audit.last.callers
    labelled = {
        (flow.PKG + "." + module, qual)
        for (module, qual), label in _PROPORTIONAL_WORK_OWNERS.items() if label == _B_COUNTED_RECORD
    }
    unbounded = []
    for target in sorted(labelled):
        assert callers.get(target), target  # bounded path から呼ばれている（空の合格にしない）
        pending = [(target, frozenset(_walked_inputs(index, target)), (target,))]
        seen = set()
        while pending:
            key, walked, path = pending.pop()
            for caller in sorted(callers.get(key, ())):
                if caller in labelled or caller not in index.functions:
                    continue
                if flow.work_owner(index, caller) == "B":
                    # 受け取った作業量を反復ごとに数えるか渡す関数（作業量の owner）: 渡す値はその作業量の中
                    continue
                forwarded = frozenset(_forwarded(index, caller, key, set(walked)))
                if not forwarded or (caller, forwarded) in seen:
                    continue
                seen.add((caller, forwarded))
                chain = path + (caller,)
                if not callers.get(caller) or len(chain) > 10:
                    unbounded.append((tuple(f"{m[len(flow.PKG) + 1:]}::{q}" for m, q in chain), sorted(forwarded)))
                    continue
                pending.append((caller, forwarded, chain))
    assert unbounded == []


def test_snapshot_creation_never_runs_the_code_of_the_values_it_freezes():
    """snapshot の作成は fingerprint を先に求め（上書きした容器・opaque な値は digest が拒む）、写しと
    note の分類も `live_values` の規則で読む（上書きした `items()` / `__iter__` / `__str__` を呼ばない）。"""

    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY
    from scripts.function_tracer_pcode.proof.obligations.snapshot import (
        AnalysisSnapshot,
        _classify_analysis_notes,
        deep_freeze,
    )

    calls = []

    class _Hostile(dict):
        def items(self):  # pragma: no cover - must never run
            calls.append("items")
            return dict.items(self)

        def __iter__(self):  # pragma: no cover - must never run
            calls.append("iter")
            return dict.__iter__(self)

    class _Note:
        def __str__(self):  # pragma: no cover - must never run
            calls.append("str")
            return "note"

    built = RESULT_JSON_POLICY.materialize({"analysis_scope_key": _Hostile(a=1)})
    with pytest.raises(TypeError):
        AnalysisSnapshot.create(("s",), built)
    # 上書きした容器は写さない（写すとその code を呼ぶ）: 変更できる mapping をそのまま置かずに拒む
    with pytest.raises(TypeError):
        deep_freeze(_Hostile(a=1))
    # key の hash が組み込みでない mapping も読み取り専用の写し（変更できる元の dict を置かない）
    inner = {frozenset({1}): [1, 2]}
    frozen_inner = deep_freeze({"m": inner})["m"]
    assert frozen_inner is not inner and frozen_inner[frozenset({1})] == (1, 2)
    frozen = deep_freeze({"a": [1, (2, 3)], "b": {"c": {4}}})
    assert frozen["a"] == (1, (2, 3)) and frozen["b"]["c"] == frozenset({4})
    semantic, diagnostic = _classify_analysis_notes(["debug:x", _Note(), "custom"])
    from scripts.function_tracer_pcode.core.live_values import type_name

    assert diagnostic == ("debug:x",) and semantic[1] == "custom"
    assert semantic[0].startswith(f"<{type_name(_Note)}@")
    # 型の同じ別の note は別の note（1 つに合併しない）
    first, second = _classify_analysis_notes([_Note(), _Note()])[0]
    assert first != second
    assert calls == []


def test_the_bounded_path_owners_never_read_type_attributes_with_getattr_static():
    """owner の module・bounded path の core は型の属性を `live_values.type_attribute`（組み込みの slot だけを
    読む）で読む。`inspect.getattr_static` は `klass.__dict__` を普通の属性の読みで引くので metaclass の
    `__getattribute__` を呼び、名前の比較で namespace の key の `__eq__` を呼び得る。"""

    import ast

    modules = sorted(flow.OWNER_MODULES | {
        flow.PKG + ".core.canonical_digest", flow.PKG + ".core.budget_policy",
        flow.PKG + ".proof.obligations.snapshot", flow.PKG + ".checker.output_preparation",
    })
    offenders = []
    for module in modules:
        path = PACKAGE_ROOT / (module[len(flow.PKG) + 1:].replace(".", "/") + ".py")
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if (isinstance(node, ast.Attribute) and node.attr == "getattr_static") or (
                isinstance(node, ast.alias) and node.name == "getattr_static"
            ):
                offenders.append((module, getattr(node, "lineno", 0)))
    assert offenders == []
