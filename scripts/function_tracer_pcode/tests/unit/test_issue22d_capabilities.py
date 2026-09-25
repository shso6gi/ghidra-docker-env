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
    """作業量の外の依存は宣言した場所だけ（#110: 封印と authority の event、#194: identity key）。

    増えた依存は落ちる（登録しないと通らない）。依存の owner の Issue が片づけば宣言を消す。
    """

    flow.audit(PACKAGE_ROOT)
    callers = flow.audit.last.identity_key_callers
    assert callers == _IDENTITY_KEY_CALLERS, callers
    reasons = list(flow.DECLARED_DEPENDENCIES.values()) + list(flow.DECLARED_CALLEES.values())
    assert all(reason.startswith(("#110:", "#194:")) for reason in reasons), reasons


_STUB_LIVE_VALUES = """
def as_int(value): pass
def as_str(value): pass
def attribute(value, name, default=None): pass
def elements_of(value): pass
def builtin_sequence(value): pass
"""

_STUB_JSON_ENCODING = """
class Reducer:
    def add(self, element, *, work): pass
    def result(self, *, work): pass
def source_converter(fn): return fn
def each(values, fn=None): pass
"""

_CASES = """
from scripts.function_tracer_pcode.core.json_encoding import Reducer, each, source_converter
from scripts.function_tracer_pcode.core.live_values import as_int, as_str, attribute, builtin_sequence, elements_of
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
}


def _synthetic_package(root: pathlib.Path) -> pathlib.Path:
    package = root / "scripts" / "function_tracer_pcode"
    (package / "core").mkdir(parents=True)
    (package / "core" / "live_values.py").write_text(_STUB_LIVE_VALUES)
    (package / "core" / "json_encoding.py").write_text(_STUB_JSON_ENCODING)
    (package / "cases.py").write_text(_CASES)
    return package


def test_j19_the_audit_finds_every_forbidden_operation_and_accepts_the_owner_api(tmp_path):
    """監査が空の合格にならない: 禁止した操作は 1 つずつ見つかり、owner の API だけの record は通る。"""

    violations, _analyzed, _index, _missing = flow.audit(_synthetic_package(tmp_path), entry_roots=())
    flagged = {qual for module, qual, _line, _message in violations if module == "cases"}
    missed = _EXPECTED_VIOLATIONS - flagged
    assert missed == set(), missed
    assert not {"Clean.json_items", "CleanReducer.add", "CleanReducer.result", "good_converter"} & flagged, [
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
        yield relative.as_posix(), ast.parse(path.read_text(encoding="utf-8"))


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
                   lambda: scan(plain(), _DeltaReducer())):
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
_B_SIZED = "B: 木を作る前に `__json_tree_bytes__` で大きさを数え、上限の中でだけ作る"
_B_FROZEN = "B: `freeze(budget=)` が数えた写し（組み込みの値だけ）を辿る"
_B_SCHEMA_ROWS = "B: G4-b（`finitize_legacy_reasons`）が出力 schema の行数へ切った列を辿る"
_C_LAZY = "C: 1 要素ずつ yield する generator を walker へ渡す（walker が引き出すたびに数える）"
_D_PAIR_FAILURE = (
    "D(#106): pair の台帳が決めた 1 件の failure から結果を組む（record の件数は定数、field は解析が"
    " 作った値の写し）"
)
_D_RECORD = "D(#106): record の構築（field は解析の producer が作った値。大きさは構築の owner）"
_D_TRUNCATION = "D(#131): 展開の上限の事実の列（構築のときに確定した record の数）"
_D_LEGACY_RESULT = "D(#106): receipt の無い旧来の結果だけ（production の結果は receipt だけを読む）"

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
        "_attach_budget_diagnostics", "_compose_members", "_field_order", "_ordered", "_prepare_member",
        "check_prepared_field_bounds", "compose_result_preimage", "prepare_pair_output",
    )},
    ("checker.output_preparation", "OutputPreparer._prepare_cause_evidence"): _B_PREPARED,
    ("checker.output_preparation", "_bounded_utf8_length"): _B_BOUND,
    ("checker.output_preparation", "_rows"): _B_SCHEMA_ROWS,
    **{("checker.output_schema", name): _A_FIXED for name in (
        "_object_bytes", "_superseded_max_bytes", "authority_field_bounds", "conditional_receipt_max_bytes",
        "metadata_field_bounds",
    )},
    ("checker.result", "EquivalenceResult.__post_init__"): _D_RECORD,
    ("checker.result", "EquivalenceResult._has_pending_proof_gate"): _D_RECORD,
    ("checker.result", "EquivalenceResult.is_timeout"): _D_LEGACY_RESULT,
    ("checker.result_assembly", "analysis_limitation_result_for_pair"): _D_PAIR_FAILURE,
    ("checker.result_assembly", "internal_error_result_for_pair"): _D_PAIR_FAILURE,
    **{("checker.unknown_reason", name): _D_RECORD for name in (
        "_field_values", "_index_positions", "_optional_tuple_of", "_payload_view", "coerce_unknown_reason_records",
        "coerce_unknown_recovery_actions", "make_internal_v2_reason_diagnostic", "make_unknown_reason",
    )},
    ("core.budget_policy", "raise_expression_size_budget_exceeded"): _A_FIXED,
    ("core.canonical_digest", "_emit"): _B_BOUND,
    ("core.expression", "Expression._to_dict_active"): _B_SIZED,
    ("core.expression", "_bounded_local_bytes"): _B_BOUND,
    ("core.expression", "_node_local_bytes"): _B_BOUND,
    ("core.expression", "estimate_legacy_dict_bytes"): _B_BOUND,
    ("core.expression", "runtime_ref_source"): _C_LAZY,
    ("core.runtime_refs.loops", "CountedLoopSummaryRef.json_items"): _A_FIXED,
    ("core.runtime_refs.loops", "LoopTermDescriptorRef.json_items"): _A_FIXED,
    ("core.runtime_refs.loops", "_lane_term_source"): _A_FIXED,
    ("core.runtime_refs.readonly", "ReadonlyReductionTermRef.json_items"): _A_FIXED,
    ("core.runtime_refs.readonly", "ReductionAccumulatorProof.json_items"): _A_FIXED,
    ("core.runtime_refs.unknowns", "merge_expansion_budget_truncations"): _D_TRUNCATION,
    ("core.runtime_refs.unknowns", "normalize_expansion_budget_truncations"): _D_TRUNCATION,
    ("core.signature", "FunctionSignature.from_analysis"): _D_RECORD,
    ("core.signature", "clone_parameter_descriptor"): _D_RECORD,
    **{("proof.cause_identity", name): _B_COUNTED for name in (
        "_tuple", "_tuple_item", "canonical_cause_tuple", "cause_key_from_dict",
    )},
    ("proof.obligations.snapshot", "SnapshotFingerprintCodec._freeze_unmetered"): _B_FROZEN,
    ("proof.obligations.snapshot", "SnapshotFingerprintCodec.sorted_mapping_items"): _B_FROZEN,
    ("proof.obligations.snapshot", "_frozen_repr"): _B_FROZEN,
    ("proof.obligations.snapshot", "_set_members"): _B_FROZEN,
    ("proof.unknown_reason", "UnknownRecoveryPlan.json_items"): _C_LAZY,
    ("proof.unknown_reason", "UnknownRecoveryProofObligation.json_items"): _C_LAZY,
    **{("proof.unknown_reason", name): _D_RECORD for name in (
        "_coerce_evidence_refs", "_coerce_optional_tuple", "coerce_unknown_recovery_proof_obligations",
    )},
    ("proof.unknown_reason", "_registered_recovery_proof_kind_values"): _A_FIXED,
}


def test_j22_every_input_proportional_construct_has_a_work_owner():
    """bounded path の入力に比例し得る仕事は、作業量の owner を持つか、A〜D に分類済み（E は 0）。"""

    _violations, analyzed, index, _missing = flow.audit(PACKAGE_ROOT)
    unowned = flow.unowned_proportional_work(PACKAGE_ROOT, analyzed, index)
    missing = sorted(set(unowned) - set(_PROPORTIONAL_WORK_OWNERS))
    stale = sorted(set(_PROPORTIONAL_WORK_OWNERS) - set(unowned))
    assert missing == [], {key: unowned[key] for key in missing}
    assert stale == [], stale
    assert all(reason[0] in "ABCD" for reason in _PROPORTIONAL_WORK_OWNERS.values())
