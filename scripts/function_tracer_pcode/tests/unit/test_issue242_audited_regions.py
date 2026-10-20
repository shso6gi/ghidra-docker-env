# -*- coding: utf-8 -*-
"""Issue #242（第 10 回）: 監査済みの区間（`live_values.audited_region`）と、その外の code の区間の契約。

前提（`core/live_values` の前提の表の「監査済みの区間」の行）:

- 区間の記録（型ごとの protocol の判定など）は、区間の中で監査済みの code（owner の API と J19 の監査が辿る package
  の関数）だけが走る間だけ使う。
- 監査の外の code（identity key の method・宣言していない package の generator）は、走る間ずっと区間の外
  （`outside_audit`）: その中から API に入り直しても区間の記録を見ない。戻った後（例外・中断を含む）は記録を捨てる。

期待値は実装と独立: 区間の記録を使わない新しい判定（同じ値を新しい process で読んだときと同じ規則）の結果。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.core import json_encoding, live_values
from scripts.function_tracer_pcode.core.json_encoding import JsonValueRejected, RESULT_JSON_POLICY, active_walk_work


def _foreign_function():
    # 外の code（package の外の file 名）。method としても generator の中からも呼べる
    return eval(compile("lambda self=None, *args: iter(())", "<foreign>", "eval"))  # noqa: S307


def _record_type():
    def items(self):
        yield "a", 1

    return type("Record", (), {"__module__": __name__, "json_items": items}), items


def _reentrant_result(kind):
    """区間の中の外の code から API に入り直したときの結果（拒んだら `"rejected"`）。"""

    try:
        return RESULT_JSON_POLICY.prepare_into(kind(), active_walk_work() or json_encoding.JsonBudget(1 << 20))
    except JsonValueRejected:
        return "rejected"


def test_an_undeclared_generator_reentering_the_api_sees_no_region_record():
    """反例（第 10 回 指摘 1）: 外の walk で Record を読んだ後、宣言していない package の generator の中で
    `Record.json_items` を外の関数へ変え、`prepare_into(Record(), active_walk_work())` を呼ぶ。区間の記録を使えば
    変える前の method で直列化してしまう。期待値は新しい判定（拒む）。"""

    kind, items = _record_type()
    seen = []

    def rewriting():
        yield kind()
        kind.json_items = _foreign_function()
        seen.append(_reentrant_result(kind))
        yield 1

    try:
        RESULT_JSON_POLICY.prepare([kind(), rewriting()]).value()
    except JsonValueRejected:
        pass
    finally:
        kind.json_items = items
    assert seen == ["rejected"]


def test_an_identity_key_method_reentering_the_api_sees_no_region_record():
    """反例（第 10 回 指摘 1、key の method 経由）: identity key の method の中で型を書き換えて API に入り直す。"""

    kind, items = _record_type()
    seen = []

    class Keyed:
        def stable_key(self):
            kind.json_items = _foreign_function()
            seen.append(_reentrant_result(kind))
            return ("keyed",)

    try:
        with live_values.audited_region():
            assert json_encoding.is_json_record(kind())  # 区間に記録を作る
            json_encoding.identity_key_of(Keyed())
            after = json_encoding.is_json_record(kind())
    finally:
        kind.json_items = items
    assert seen == ["rejected"]
    assert after is False


def test_a_region_is_suspended_while_outside_code_runs_and_restored_after():
    """区間の外の code の間は区間が無い（`region_cache` は `None`）。戻ったら同じ区間に戻り、記録は捨てられている。
    例外で抜けても同じ。区間の外の中で開いた区間は、その中だけのもの。"""

    slot = object()
    with live_values.audited_region():
        live_values.region_cache(slot)["k"] = "v"
        with live_values.outside_audit():
            assert live_values.region_cache(slot) is None
            with live_values.audited_region():
                inner = live_values.region_cache(slot)
                assert inner == {}
                inner["inner"] = 1
            assert live_values.region_cache(slot) is None
        assert live_values.region_cache(slot) == {}
        live_values.region_cache(slot)["k"] = "v"
        with pytest.raises(RuntimeError):
            with live_values.outside_audit():
                raise RuntimeError("boom")
        assert live_values.region_cache(slot) == {}
    assert live_values.region_cache(slot) is None


def test_an_abandoned_undeclared_generator_is_closed_outside_the_region():
    """walk の途中で止まった（例外で抜けた）宣言していない generator の後始末（`finally`）も区間の外で走る。"""

    kind, items = _record_type()
    seen = []

    def generator():
        try:
            yield kind()
            yield object()  # walk はここで拒む（JSON にならない値）
        finally:
            seen.append(live_values.region_cache(json_encoding._PROTOCOL_SLOT))

    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare([generator()]).value()
    assert seen == [None]
    kind.json_items = items


def test_owner_functions_called_by_audited_code_never_run_value_code_unless_declared():
    """J19 の監査が辿る code（区間の中で走る code）が呼ぶ owner の関数は、値の code を呼ばないと確かめた関数
    （`VALUE_CODE_FREE`: 下の adversarial test が全部を値の code を数えて確かめる）か、区間を外す境界
    （`live_values.VALUE_CODE_BOUNDARIES`）のどちらか。owner の関数を新しく使えば、どちらかに分類するまで落ちる。"""

    import pathlib

    from scripts.function_tracer_pcode.tests.unit import _live_flow_audit as audit

    root = pathlib.Path(__file__).resolve().parents[2]
    _violations, _analyzed, _index, _missing = audit.audit(root)
    called = set(audit.LAST_OWNER_CALLS)
    boundaries = {f"{fn.__module__.rsplit('.', 1)[-1]}.{fn.__qualname__}" for fn in live_values.VALUE_CODE_BOUNDARIES}
    # 境界の method は owner の object の method としても記録される（`owner.<名前>`）
    boundaries |= {f"owner.{fn.__name__}" for fn in live_values.VALUE_CODE_BOUNDARIES}
    assert called, "the audit records owner calls"
    assert sorted(called - set(VALUE_CODE_FREE) - boundaries - set(FROZEN_INPUT_WRITERS)) == []


#: 凍結した値だけを受ける owner の書き手（名前 → 呼んでよい唯一の package の関数）
FROZEN_INPUT_WRITERS = {
    "json_encoding.JsonEncodingPolicy.dumps_frozen": ("proof.obligations.snapshot", "_fingerprint_json"),
    "owner.dumps_frozen": ("proof.obligations.snapshot", "_fingerprint_json"),
}


def test_frozen_input_writers_are_called_only_by_their_declared_caller():
    """凍結した値だけを受ける書き手（`dumps_frozen`: 区間を外さない）を呼ぶ package の関数は、宣言した 1 つだけ。"""

    import ast
    import pathlib

    root = pathlib.Path(__file__).resolve().parents[2]
    callers = set()
    for path in sorted(root.rglob("*.py")):
        if "tests" in path.relative_to(root).parts:
            continue
        module = ".".join(path.relative_to(root).with_suffix("").parts)
        tree = ast.parse(path.read_text(encoding="utf-8"))

        def visit(node, qual):
            for child in ast.iter_child_nodes(node):
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    visit(child, f"{qual}.{child.name}" if qual else child.name)
                    continue
                if isinstance(child, ast.Attribute) and child.attr == "dumps_frozen" and not module.endswith("json_encoding"):
                    callers.add((module, qual))
                visit(child, qual)

        visit(tree, "")
    assert callers == set(FROZEN_INPUT_WRITERS.values())


def _budget():
    return json_encoding.JsonBudget(1 << 20)


def _walked(source):
    return RESULT_JSON_POLICY.materialize(source)


def _summary_of(value):
    evidence = json_encoding.bounded_evidence(value, work=_budget())
    return evidence.summary() if type(evidence) is json_encoding.BoundedEvidence else evidence


#: 値の code を呼ばないと確かめた owner の関数（名前 → adversarial な値での呼び方）。`audit.LAST_OWNER_CALLS` の名前と同じ
#: 形（`module.qualname`）。遅延の source を作る関数は walker で引き出して確かめる（作るだけでは読まない）
VALUE_CODE_FREE = {
    "live_values.as_bool": lambda v: live_values.as_bool(v),
    "live_values.as_int": lambda v: live_values.as_int(v),
    "live_values.as_float": lambda v: live_values.as_float(v),
    "live_values.as_str": lambda v: live_values.as_str(v),
    "live_values.as_repr": lambda v: live_values.as_repr(v),
    "live_values.attribute": lambda v: live_values.attribute(v, "x"),
    "live_values.builtin_container": lambda v: live_values.builtin_container(v),
    "live_values.builtin_mapping": lambda v: live_values.builtin_mapping(v),
    "live_values.builtin_sequence": lambda v: live_values.builtin_sequence(v),
    "live_values.builtin_set": lambda v: live_values.builtin_set(v),
    "live_values.dataclass_field_names": lambda v: live_values.dataclass_field_names(v),
    "live_values.elements_of": lambda v: list(live_values.elements_of(v)),
    "live_values.enum_name": lambda v: live_values.enum_name(v),
    "live_values.enum_value": lambda v: live_values.enum_value(v),
    "live_values.field_value": lambda v: live_values.field_value(v, "x"),
    "live_values.instance_state": lambda v: live_values.instance_state(v, "x", None),
    "live_values.is_enum": lambda v: live_values.is_enum(v),
    "live_values.is_kind": lambda v: live_values.is_kind(v, int),
    "live_values.items_of": lambda v: list(live_values.items_of(v)),
    "live_values.json_scalar": lambda v: live_values.json_scalar(v),
    "live_values.lookup": lambda v: live_values.lookup(v, "k"),
    "live_values.merged_mappings": lambda v: live_values.merged_mappings(v, {}),
    "live_values.plain_scalar": lambda v: live_values.plain_scalar(v),
    "live_values.set_state": lambda v: live_values.set_state(v, "x", 1),
    "live_values.size": lambda v: live_values.size(v),
    "live_values.str_value": lambda v: live_values.str_value(v),
    "live_values.values_of": lambda v: list(live_values.values_of(v)),
    "read_limits.copied_within_limit": lambda v: _read_limits().copied_within_limit(v),
    "read_limits.elements_within_limit": lambda v: list(_read_limits().elements_within_limit(v)),
    "read_limits.items_within_limit": lambda v: list(_read_limits().items_within_limit(v)),
    "read_limits.omitted_beyond_limit": lambda v: _read_limits().omitted_beyond_limit(v, kept=1),
    "read_limits.prefix_items_within_limit": lambda v: _read_limits().prefix_items_within_limit(v),
    "json_encoding.BoundedEvidence.summary": _summary_of,
    "json_encoding.JsonEncodingPolicy.encode_bounded": lambda v: RESULT_JSON_POLICY.encode_bounded(v, max_bytes=1 << 20),
    "json_encoding.JsonEncodingPolicy.materialize": lambda v: RESULT_JSON_POLICY.materialize(v),
    "json_encoding.JsonEncodingPolicy.prepare": lambda v: RESULT_JSON_POLICY.prepare(v).value(),
    "json_encoding._walk_iter": lambda v: list(json_encoding._walk_iter(v)),
    "json_encoding.as_dict": lambda v: _walked(json_encoding.as_dict(v)),
    "json_encoding.as_list": lambda v: _walked(json_encoding.as_list(v)),
    "json_encoding.bounded_evidence": lambda v: json_encoding.bounded_evidence(v, work=_budget()),
    "json_encoding.bounded_repr": lambda v: json_encoding.bounded_repr(v),
    "json_encoding.bounded_text": lambda v: json_encoding.bounded_text(v, 8, work=_budget()),
    "json_encoding.builtin_str": lambda v: json_encoding.builtin_str(v),
    "json_encoding.builtin_view": lambda v: json_encoding.builtin_view(v, _budget()),
    "json_encoding.copy_legacy_containers": lambda v: json_encoding.copy_legacy_containers(v),
    "json_encoding.each": lambda v: _walked(json_encoding.each(v)),
    "json_encoding.exception_text": lambda v: json_encoding.exception_text(ValueError(v)),
    "json_encoding.flatten": lambda v: _walked(json_encoding.flatten(v)),
    "json_encoding.hashable_key": lambda v: json_encoding.hashable_key(v, _budget()),
    "json_encoding.inline": lambda v: _walked(json_encoding.inline(("k", v))),
    "json_encoding.is_json_record": lambda v: json_encoding.is_json_record(v),
    "json_encoding.mapping_of": lambda v: _walked(json_encoding.mapping_of(v)),
    "json_encoding.materialize": lambda v: json_encoding.materialize(v),
    "json_encoding.nested": lambda v: _walked(json_encoding.nested(v)),
    "json_encoding.pairs_of": lambda v: _walked(json_encoding.pairs_of(v)),
    "json_encoding.protocol_method": lambda v: json_encoding.protocol_method(v, "json_items"),
    "json_encoding.call_protocol": lambda v: json_encoding.call_protocol(v, "__json_tree__"),
    "live_values.read_pair": lambda v: live_values.read_pair(v),
    "live_values.package_instance": lambda v: live_values.package_instance(v, type(v)),
    "json_encoding.raw": lambda v: _walked(json_encoding.raw(v)),
    "json_encoding.row_items": lambda v: list(json_encoding.row_items((), v)),
    "json_encoding.scalar_record_dict": lambda v: json_encoding.scalar_record_dict(v),
    "json_encoding.scan": lambda v: _walked(json_encoding.scan(v, _idle_reducer())),
    "json_encoding.text": lambda v: _walked(json_encoding.text(v, 8)),
    "json_encoding.value_token": lambda v: json_encoding.value_token(v, _budget()),
    "json_encoding.JsonObjectBudget": lambda v: json_encoding.JsonObjectBudget(RESULT_JSON_POLICY, v).add("k", 1),
    # owner の object（policy）と作業量の object の method
    "owner.prepare": lambda v: RESULT_JSON_POLICY.prepare(v).value(),
    "owner.prepare_into": lambda v: RESULT_JSON_POLICY.prepare_into(v, _budget()),
    "owner.materialize": lambda v: RESULT_JSON_POLICY.materialize(v),
    "owner.measure": lambda v: RESULT_JSON_POLICY.measure(v, max_bytes=1 << 20),
    "owner.count_into": lambda v: RESULT_JSON_POLICY.count_into(v, _budget()),
    "work.charge": lambda v: _budget().charge(v),
    "work.container_frame_bytes": lambda v: RESULT_JSON_POLICY.container_frame_bytes(v),
    "work.count_into": lambda v: RESULT_JSON_POLICY.count_into(v, _budget()),
    "work.measure": lambda v: RESULT_JSON_POLICY.measure(v, max_bytes=1 << 20),
    "work.plain_bytes": lambda v: RESULT_JSON_POLICY.plain_bytes(v, max_bytes=1 << 20),
}


def _read_limits():
    from scripts.function_tracer_pcode.core import read_limits

    return read_limits


def _idle_reducer():
    from scripts.function_tracer_pcode.tests.unit.test_issue22d_capabilities import _IdleReducer

    return _IdleReducer()


#: adversarial な値を読んで投げてよい例外（読めない値は拒む。値の code を呼んだかは数で確かめる）
_REFUSALS = (
    TypeError, ValueError, LookupError, AttributeError, RuntimeError, JsonValueRejected, live_values.UndecidableComparison,
)


@pytest.mark.parametrize("name", sorted(VALUE_CODE_FREE))
def test_value_code_free_owner_functions_never_run_value_code(name):
    """`VALUE_CODE_FREE` の関数は、上書きした special method を持つ adversarial な値（scalar の subclass・偽る class・
    上書きした容器・record）のどれを渡しても、その code を呼ばない（呼んだ回数 0）。"""

    from scripts.function_tracer_pcode.tests.unit.test_issue22d_capabilities import _adversarial_values, _Calls

    call = VALUE_CODE_FREE[name]
    for value in _adversarial_values():
        _Calls.count = 0
        try:
            call(value)
        except _REFUSALS:
            pass
        assert _Calls.count == 0, (name, type(value).__name__)


def test_value_code_boundaries_call_value_code_only_outside_the_region():
    """境界（`value_code_boundary`）の本体は `outside_audit` を使う（値の code を区間の外で呼ぶ）。"""

    import ast
    import inspect
    import textwrap

    assert live_values.VALUE_CODE_BOUNDARIES
    for function in live_values.VALUE_CODE_BOUNDARIES:
        tree = ast.parse(textwrap.dedent(inspect.getsource(function)))
        uses = [
            node for node in ast.walk(tree)
            if isinstance(node, ast.Attribute) and node.attr == "outside_audit"
            or isinstance(node, ast.Name) and node.id == "outside_audit"
        ]
        assert uses, function.__qualname__


def test_a_reducer_rewritten_after_scan_is_judged_when_it_is_called():
    """反例（第 10 回の独立 review 1）: `scan()` を作った後に外の code が `Reducer.add` を外の関数へ差し替える。walker は
    `add` / `result` を呼ぶ時点で型から引き直す（package の型の package の関数だけ）: 外の関数を区間の中で呼ばない。"""

    kind, items = _record_type()
    calls = []

    class Counter(json_encoding.Reducer):
        def __init__(self):
            self.count = 0

        def add(self, element, *, work):
            self.count += 1

        def result(self, *, work):
            return self.count

    source = json_encoding.scan([1, 2], Counter())

    foreign_add = eval(  # noqa: S307
        compile("lambda calls, kind, foreign: (lambda self, element, *, work: (calls.append(element), setattr(kind, 'json_items', foreign)))", "<foreign>", "eval")
    )(calls, kind, _foreign_function())
    Counter.add = foreign_add
    try:
        with pytest.raises(JsonValueRejected):
            RESULT_JSON_POLICY.prepare([kind(), source, kind()]).value()
    finally:
        kind.json_items = items
    assert calls == []


def test_an_undeclared_generator_closed_inside_a_region_finishes_outside_it():
    """区間の中で止めた（close した）宣言していない generator の後始末（`finally`）も区間の外で走る（区間の記録を見ない）。"""

    seen = []

    def generator():
        try:
            yield 1
            yield 2
        finally:
            seen.append(live_values.region_cache(json_encoding._PROTOCOL_SLOT))

    with live_values.audited_region():
        iterator = json_encoding._walk_iter(generator())
        assert next(iterator) == 1
        iterator.close()
        assert live_values.region_cache(json_encoding._PROTOCOL_SLOT) == {}
    assert seen == [None]


def test_dumps_runs_value_code_outside_the_region():
    """`dumps`（組み込みの `json` の C の encoder: 容器の subclass の `items()` を呼ぶ）は区間の外で書く。"""

    seen = []

    class Loud(dict):
        def items(self):
            seen.append(live_values.region_cache(json_encoding._PROTOCOL_SLOT))
            return dict.items(self)

    with live_values.audited_region():
        live_values.region_cache(json_encoding._PROTOCOL_SLOT)["k"] = "v"
        RESULT_JSON_POLICY.dumps({"outer": Loud(a=1)})
        assert live_values.region_cache(json_encoding._PROTOCOL_SLOT) == {}
    assert seen and all(cache is None for cache in seen)


def test_an_enum_payload_with_ordered_python_keys_never_sorts_inside_the_region():
    """反例（第 10 回の独立 review 2）: enum の値が dict で、その key が Python の `__lt__` を持つ IntEnum。凍結の中で
    key を並べると（`sort_keys`）その `__lt__` が区間の中で走る。組み込みのままの enum は並べる dunder も組み込みの実装
    だけ: その member は組み込みの値として写さない（凍結は拒む）。"""

    import enum

    from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec

    calls = []

    class Ordered(enum.IntEnum):
        A = 1
        B = 2

        def __lt__(self, other):
            calls.append(live_values.region_cache(json_encoding._PROTOCOL_SLOT) is not None)
            return int(self) < int(other)

    class Holder(enum.Enum):
        X = {Ordered.A: 1, Ordered.B: 2}

    assert not live_values.builtin_enum(Ordered.A)
    try:
        SnapshotFingerprintCodec.digest({Holder.X: 1})
    except (TypeError, ValueError):
        pass
    assert True not in calls


def test_bounded_evidence_summary_is_read_from_its_type():
    """反例（第 10 回の独立 review 2）: `BoundedEvidence` の instance の属性で `summary` を覆っても、walker は型の
    method を呼ぶ（instance の属性を呼ばない）。"""

    calls = []
    evidence = json_encoding.bounded_evidence(list(range(50)), work=json_encoding.JsonBudget(1 << 20), inline_bytes=1)
    assert type(evidence) is json_encoding.BoundedEvidence
    object.__setattr__(evidence, "summary", lambda: calls.append(1) or {"fake": True})
    RESULT_JSON_POLICY.materialize([evidence])
    RESULT_JSON_POLICY.prepare([evidence]).value()
    assert calls == []


def test_a_converter_swapped_after_the_source_was_built_is_not_called():
    """反例（第 10 回の独立 review 2）: `each` / `as_list` の source の converter を作った後に登録していない callable へ
    書き換える。walker は呼ぶ時点で登録した converter かを確かめる（呼ばずに拒む）。"""

    calls = []
    source = json_encoding.as_list([1, 2])
    with pytest.raises(TypeError):
        source.fn = lambda value: calls.append(value) or value  # source は作った後は変えない
    # owner の object の状態を直接書き換えても（契約の外）、walker は呼ぶ時点で登録した converter かを確かめる
    object.__setattr__(source, "fn", lambda value: calls.append(value) or value)
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.materialize(source)
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(source).value()
    assert calls == []


def test_owner_object_methods_in_the_registry_name_one_owner_class_each():
    """`owner.<名前>` / `work.<名前>`（owner の object の method をまとめた名前）の名前は、owner の module の class の
    うち 1 つ（または作業量の型）だけが定義する: 名前でまとめても、確かめた method と違う method を通さない。"""

    import inspect

    from scripts.function_tracer_pcode.core import budget_policy, read_limits

    owners = [json_encoding, live_values, read_limits]
    for name in sorted(key for key in VALUE_CODE_FREE if key.startswith("owner.")):
        method = name.split(".", 1)[1]
        defining = [
            cls for module in owners for _n, cls in inspect.getmembers(module, inspect.isclass)
            if cls.__module__ == module.__name__ and method in vars(cls)
        ]
        assert len(defining) == 1, (name, defining)
    work_types = (json_encoding.JsonBudget, budget_policy.SerializationWork, json_encoding.JsonEncodingPolicy)
    for name in sorted(key for key in VALUE_CODE_FREE if key.startswith("work.")):
        method = name.split(".", 1)[1]
        assert any(method in vars(cls) for cls in work_types), name


def test_budget_limits_are_read_as_builtin_ints():
    """作業量の上限（`JsonBudget` / `JsonObjectBudget` / `SerializationWork`）は組み込みの int にして持つ: 上書きした比較を
    持つ int の subclass を上限に渡しても、数えるときにその code を呼ばない。"""

    from scripts.function_tracer_pcode.core.budget_policy import SerializationWork
    from scripts.function_tracer_pcode.tests.unit.test_issue22d_capabilities import _Calls, _LiveInt

    counted = []

    def counting(name):
        def operation(self, other):
            counted.append(name)
            return getattr(int, name)(self, other)
        return operation

    names = ("__sub__", "__rsub__", "__add__", "__radd__", "__lt__", "__le__", "__gt__", "__ge__")
    Arithmetic = type("Arithmetic", (int,), {name: counting(name) for name in names})

    _Calls.count = 0
    work = SerializationWork(site="t", target_parts=("t",), max_bytes=_LiveInt(100))
    work.charge(1)
    budget = json_encoding.JsonObjectBudget(RESULT_JSON_POLICY, Arithmetic(100))
    budget.add("k", 1)
    budget.remaining_for("j")
    other = SerializationWork(site="t", target_parts=("t",), max_bytes=Arithmetic(100))
    other.charge(1)
    other.remaining()
    plain = json_encoding.JsonBudget(Arithmetic(100), detached=True)
    plain.charge(1)
    plain.remaining()
    assert _Calls.count == 0 and counted == []
    assert all(type(owner.max_bytes) is int for owner in (work, budget, other, plain))


@pytest.mark.parametrize("dunder", ["__lt__", "__le__", "__gt__", "__ge__", "__ne__"])
def test_an_enum_with_a_python_ordering_dunder_is_not_a_builtin_enum(dunder):
    """組み込みのままの enum は並べる・比べる dunder のどれも Python の code でない（`sorted` / `sort_keys` が呼ぶ）。"""

    import enum

    def ordering(self, other):
        return int.__lt__(self, other)

    kind = enum.IntEnum("Ordered", {"A": 1, "B": 2})
    assert live_values.builtin_enum(kind.A)
    setattr(kind, dunder, ordering)
    assert not live_values.builtin_enum(kind.A)


def test_owner_objects_used_by_the_walker_are_fixed_once_built():
    """`Tally`（owner の reducer）と `PreparedJson` の field は作った後に変えない（区間の中で確かめた後に差し替えない）。"""

    tally = json_encoding.Tally("x")
    with pytest.raises(TypeError):
        tally.attribute = "y"
    with pytest.raises(TypeError):
        tally.counts = {}
    prepared = RESULT_JSON_POLICY.prepare([1])
    with pytest.raises(TypeError):
        prepared._value = [2]
    assert prepared.value() == [1]


def test_a_reread_converter_is_checked_when_it_is_called():
    """証拠の読み直し（`_reread`）は converter を呼ぶ時点で確かめる（owner の object の状態を直接書き換えても、登録して
    いない callable を呼ばない）。"""

    calls = []
    reread = json_encoding.Reread(record=type("Holder", (), {"x": 1})(), attribute="x", converter=None)
    forged = reread._replace(converter=lambda value: calls.append(value) or value)
    with pytest.raises(TypeError):
        json_encoding._reread(forged)
    assert calls == []


# ---------------------------------------------------------------------------
# 第 10 回の独立レビューの反例（作った後の書き込み・凍結の形・他の thread）
# ---------------------------------------------------------------------------


def test_a_fixed_once_object_is_written_only_by_its_constructor():
    """構成子の外の書き込みは名前によらず拒む: 同じ slot の並びの型への `__class__` の代入（walker の source の意味が
    変わる）・`__new__` だけで作った object への書き込み（`PreparedJson` の token の確かめを飛ばす）・`copy` の写し
    （状態を置き直す: 写しと元が中身を共有する）。"""

    import copy

    nested = json_encoding._Nested(1)
    with pytest.raises(TypeError):
        nested.__class__ = json_encoding._Raw
    assert type(nested) is json_encoding._Nested
    forged = json_encoding.PreparedJson.__new__(json_encoding.PreparedJson)
    for name, value in (("_value", {"a": 1}), ("encoded_bytes", 1), ("policy", RESULT_JSON_POLICY)):
        with pytest.raises(TypeError):
            setattr(forged, name, value)
    prepared = RESULT_JSON_POLICY.prepare({"a": 1})
    for make in (copy.copy, copy.deepcopy):
        with pytest.raises(TypeError):
            make(prepared)
    assert prepared.value() == {"a": 1}



def test_a_constructor_sets_each_field_once_and_never_the_class():
    """構成子の実行中も規則は同じ: 同じ field の 2 度目の書き込みと、slot でない名前（`__class__` の代入: 同じ slot の
    並びの型へは `object.__setattr__` が通す）は拒む。"""

    def twice(self, value):
        self.value = value
        self.value = value

    def swap(self, value):
        self.value = value
        self.__class__ = json_encoding._Raw

    for init in (twice, swap):
        kind = type("Built", (json_encoding._Nested,), {"__slots__": (), "__init__": init})
        with pytest.raises(TypeError):
            kind(1)

def test_a_fixed_once_subclass_declares_its_slots():
    """`__dict__` を持つ subclass は slot でない名前を後から置けてしまう: class を作る時点で拒む。"""

    with pytest.raises(TypeError):
        type("Loose", (json_encoding.Tally,), {})
    kept = type("Kept", (json_encoding.Tally,), {"__slots__": ()})("x")
    with pytest.raises(TypeError):
        kept.extra = 1


def test_dumps_frozen_refuses_an_unfrozen_value_without_running_its_code():
    """`dumps_frozen` は区間を外さないので、凍結していない値（容器の subclass の `items()`・反復、key の並べ替えが呼ぶ
    比較、`default` に渡る値）と閉路を、呼ぶ場所の固定に頼らずに書く前に拒む（Python の code を呼ばない）。"""

    seen = []

    class Mapping(dict):
        def items(self):
            seen.append(live_values.region_cache("probe") is not None)
            return super().items()

    class Sequence(list):
        def __iter__(self):
            seen.append("iter")
            return super().__iter__()

    class Key(str):
        def __lt__(self, other):
            seen.append("lt")
            return str.__lt__(self, other)

        __hash__ = str.__hash__

    cycle: list = []
    cycle.append(cycle)
    policy = json_encoding.JsonEncodingPolicy(ensure_ascii=True, item_separator=",", key_separator=":")
    with live_values.audited_region():
        for value in (
            Mapping(a=1), Sequence([1]), {Key("b"): 1, Key("a"): 2}, [{1}], (1, Mapping(a=1)), [object()],
            {(1,): 1},
        ):
            with pytest.raises(TypeError):
                json_encoding.JsonEncodingPolicy.dumps_frozen(policy, value)
        with pytest.raises(ValueError):
            json_encoding.JsonEncodingPolicy.dumps_frozen(policy, cycle)
    assert seen == []

#: package の製品の code が thread を始める場所と、その thread が走らせる code（値の code を走らせない理由）。
#: 型の判定の記録・監査済みの区間の記録は「判定の途中・区間の間、外の code が走らない」ことに依る（同じ thread の中は
#: `outside_audit` が切り替える）。他の thread が値の code を走らせて class を書き換えるのは前提の外
#: （`core/live_values` の前提の外の段落）: その前提が製品で成り立つことをここで固定する。
PRODUCTION_THREAD_STARTS = {
    ("authority/process/stack_dump_diagnostic.py", "Thread"): "frame の読みだけ（faulthandler の stack dump）",
    ("smt/parallel.py", "ThreadPoolExecutor"): "solver の backend の起動と SMT の文字列の読み（呼ぶ側は待つ）",
}


def test_production_threads_are_the_registered_ones():
    """製品の code（`tests/` の外）が thread を始める呼び出し（`Thread` / `Timer` / `ThreadPoolExecutor` / `ThreadPool` /
    `start_new_thread`）は登録した場所だけ（新しい thread が値の code を走らせ得るかを、足すときに確かめる）。"""

    import ast
    import pathlib

    root = pathlib.Path(json_encoding.__file__).resolve().parents[1]
    starters = {"Thread", "Timer", "ThreadPoolExecutor", "ThreadPool", "start_new_thread"}
    found = set()
    for path in sorted(root.rglob("*.py")):
        relative = path.relative_to(root).as_posix()
        if relative.startswith("tests/"):
            continue
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
            if isinstance(node, ast.Call):
                name = node.func.attr if isinstance(node.func, ast.Attribute) else getattr(node.func, "id", None)
                if name in starters:
                    found.add((relative, name))
    assert found == set(PRODUCTION_THREAD_STARTS)


@pytest.mark.parametrize("ensure_ascii", [True, False])
def test_dumps_frozen_writes_what_json_dumps_writes(ensure_ascii):
    """凍結した値の encoder（閉路の検出だけを外した C の encoder を 1 度だけ作る）は `json.dumps` と同じ文字列を書く
    （scalar の端・surrogate・enum の member・入れ子の tuple）。"""

    import enum
    import json

    Kind = enum.IntEnum("Kind", {"A": 1})
    Text = enum.Enum("Text", {"B": "x"}, type=str)
    shared = [1, {"k": (2,)}]
    values = [
        "abc", "é\ud800x", 1, -2 ** 70, 3.5, 1e300, float("nan"), float("inf"), -0.0, None, True, False, (), ((),),
        ("a", (1, 2.5, None, True, Kind.A, Text.B)), tuple((f"k{i}", i, (i, "あ")) for i in range(50)),
        [1, [2, (3,)]], {"b": [1], "a": {"c": None}}, {Kind.A: 1, 0: 2}, {Text.B: 1, "a": 2}, (shared, shared, [shared]),
    ]
    policy = json_encoding.JsonEncodingPolicy(ensure_ascii=ensure_ascii, item_separator=",", key_separator=":")
    for value in values:
        expected = json.dumps(value, ensure_ascii=ensure_ascii, sort_keys=True, separators=(",", ":"))
        if not ensure_ascii:
            expected = policy._escape_surrogates(expected)
        assert json_encoding.JsonEncodingPolicy.dumps_frozen(policy, value) == expected
