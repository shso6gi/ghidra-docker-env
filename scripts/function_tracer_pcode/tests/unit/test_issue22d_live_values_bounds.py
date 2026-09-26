# -*- coding: utf-8 -*-
"""Issue #22 PR-22-D: `core/live_values`（bounded path が live な値を読む唯一の owner）自身の仕事の上限。

live な値の storage（instance の `__dict__`・class の namespace と MRO・closure・dict の key・key の
tuple・包んだ proxy）を作業量を受け取らずに読む関数は、どれも次のどれか（J22 を owner 自身へ）:

* A: 固定の大きさ（module の定数の組・登録した directory）だけを辿る
* B: 固定の上限の型の契約（`SCAN_LIMIT`）: 長さを組み込みの slot で O(1) に読んで比べてから辿る。
  上限の外は、述語は「確かめられない」（信頼しない）、key で読む関数は `TypeError`
* C: iterator を返し、辿る側が要素ごとに数える

上限の外の入力（100 万 key の `__dict__`・大きい class の namespace・大きい OrderedDict・深い / 幅の広い
key の tuple）で、どの関数も storage を辿らずに止まる。
"""

from __future__ import annotations

import ast
import time
import types
from collections import OrderedDict
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.tests.unit import _live_flow_audit as audit

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
BIG = 1_000_000


def _quick(call, *args, seconds=0.05):
    """`call(*args)` の結果（または上げた例外）と、それが一瞬で終わったこと。"""

    started = time.perf_counter()
    try:
        outcome = call(*args)
    except TypeError as exc:
        outcome = exc
    assert time.perf_counter() - started < seconds, call
    return outcome


class _Record:
    pass


@pytest.fixture(scope="module")
def big_record():
    record = _Record()
    record.__dict__.update({f"k{index}": index for index in range(BIG)})
    return record


def test_a_million_key_instance_state_is_not_read_by_key(big_record, monkeypatch):
    """100 万 key の `__dict__`: key の型を確かめる走査をせず、key で読む関数は `TypeError`。"""

    scanned = []
    real_is = live_values._IS
    monkeypatch.setattr(live_values, "_IS", lambda *args: scanned.append(1) or real_is(*args))
    outcome = _quick(live_values.instance_state, big_record, "k1")
    assert isinstance(outcome, TypeError) and "more than the bounded path reads" in str(outcome)
    # 型の namespace（小さい）は確かめても、100 万 key の `__dict__` の key は 1 つも確かめない
    assert len(scanned) < 100
    assert isinstance(_quick(live_values.attribute, big_record, "k1"), TypeError)
    assert isinstance(_quick(live_values.set_state, big_record, "k1", 0), TypeError)
    # 上限の内側の record は今までどおり読める
    small = _Record()
    small.x = 1
    assert live_values.instance_state(small, "x") == 1


def test_a_large_class_namespace_is_not_trusted_or_read(monkeypatch):
    namespace = {f"m{index}": index for index in range(BIG)}
    big_type = type("BigNamespace", (), namespace)
    assert _quick(live_values.package_type, big_type) is False
    outcome = _quick(live_values.type_attribute, big_type, "m1")
    assert isinstance(outcome, TypeError)


def test_a_long_mro_is_not_walked():
    kinds = [object]
    for index in range(live_values.SCAN_LIMIT + 5):
        kinds.append(type(f"Deep{index}", (kinds[-1],), {}))
    deepest = kinds[-1]
    assert _quick(live_values.package_type, deepest) is False
    assert isinstance(_quick(live_values.type_attribute, deepest, "x"), TypeError)


def test_a_large_ordered_dict_is_not_a_builtin_mapping_without_a_scan():
    big = OrderedDict((index, index) for index in range(BIG))
    assert _quick(live_values.builtin_mapping, big) is None
    small = OrderedDict(a=1)
    assert live_values.builtin_mapping(small) is small


def test_deep_and_wide_tuple_keys_stop_at_the_bound():
    wide = tuple(range(BIG))
    deep = ()
    for _ in range(BIG):
        deep = (deep,)
    for key in (wide, deep):
        assert _quick(live_values.hash_safe_key, key) is False
        assert _quick(live_values._plain_key, key) is False
        assert isinstance(_quick(live_values.lookup, {}, key), TypeError)
    assert live_values.hash_safe_key((1, ("a", 2.0))) is True


def test_mapping_reads_by_key_stop_at_the_bound():
    big = {index: index for index in range(BIG)}
    big["odd"] = 1
    assert isinstance(_quick(live_values.copied_container, big), TypeError)
    assert isinstance(_quick(live_values.merged_mappings, {"a": 1}, {f"k{i}": i for i in range(10)} | big), TypeError)
    assert isinstance(_quick(live_values.copied_container, list(range(BIG))), TypeError)
    # 組み込みでない key を持つ大きい mapping は key で探さない
    class _Key(str):
        def __eq__(self, other):  # pragma: no cover - must never run
            raise AssertionError("a live key's __eq__ ran")

        __hash__ = str.__hash__

    mixed = {f"k{i}": i for i in range(live_values.SCAN_LIMIT + 1)}
    mixed[_Key("x")] = 0
    assert isinstance(_quick(live_values.lookup, mixed, "k1"), TypeError)


def test_a_chain_of_mapping_proxies_stops_at_the_bound():
    proxy = types.MappingProxyType({"a": 1})
    for _ in range(live_values.SCAN_LIMIT + 5):
        proxy = types.MappingProxyType(proxy)
    assert _quick(live_values.builtin_mapping, proxy) is None
    assert isinstance(_quick(live_values._unwrapped, proxy), TypeError)
    shallow = types.MappingProxyType(types.MappingProxyType({"a": 1}))
    assert live_values.builtin_mapping(shallow) is shallow


def test_nested_closures_are_checked_without_recursion():
    """実行環境の wrapper が包んだ callable の入れ子は 1 つの列で辿り、上限を超えれば信頼しない。"""

    import functools

    wrapped = len
    for _ in range(live_values.SCAN_LIMIT + 5):
        wrapped = functools.lru_cache(maxsize=None)(wrapped)
    started = time.perf_counter()
    assert live_values._trusted_callable(wrapped, generated=False) is False
    assert time.perf_counter() - started < 0.5
    assert live_values._trusted_callable(functools.lru_cache(maxsize=None)(len), generated=False) is True


def test_an_unverifiable_type_is_never_left_trusted():
    """判定の途中で上限の外の値に当たっても、その型を信頼しない（仮の「信頼」を残さない）。"""

    blob = _Record()
    blob.__dict__.update({f"a{index}": index for index in range(live_values.SCAN_LIMIT + 10)})

    def outside():  # pragma: no cover - never called
        return None

    outside.__code__ = outside.__code__.replace(co_filename="/elsewhere/outside.py")
    kind = type("Unverifiable", (), {"blob": blob, "f": outside})
    assert live_values.package_type(kind) is False
    assert live_values.package_type(kind) is False  # 2 回目も（cache に信頼が残らない）


def test_class_chains_are_checked_once_per_class():
    """class の body は class ごとに 1 度だけ確かめる: 継承の鎖でも MRO × namespace を毎回辿らない。"""

    kinds = [object]
    for index in range(100):
        body = {f"attr{member}": member for member in range(1_000)}
        kinds.append(type(f"Chain{index}", (kinds[-1],), body))
    started = time.perf_counter()
    for kind in kinds[1:]:
        live_values.package_type(kind)
    assert time.perf_counter() - started < 5.0


def test_non_str_namespaces_are_bounded_across_the_whole_mro():
    """組み込みの `str` でない key の namespace を key で探すときは、MRO 全体の和で上限と比べる。"""

    kinds = [object]
    for index in range(40):
        namespace = {f"n{member}": member for member in range(200)}
        namespace[1] = "not a str key"
        kinds.append(type(f"Odd{index}", (kinds[-1],), namespace))
    outcome = _quick(live_values.type_attribute, kinds[-1], "missing", seconds=0.5)
    assert isinstance(outcome, TypeError) and "non-str namespaces" in str(outcome)


def test_nested_type_references_stop_at_the_nesting_limit():
    """型の中の値が別の型を指す入れ子が深くても、判定は深さの上限で止まる（stack を使い尽くさない）。"""

    inner = type("Leaf", (), {})
    for index in range(live_values.NESTING_LIMIT * 4):
        inner = type(f"Holder{index}", (), {"inner": inner})
    assert live_values.package_type(inner) in (True, False)


# ---------------------------------------------------------------------------
# J22 を owner 自身へ: 入力に比例する構文を持つ関数は A / B / C のどれかに分類する
# ---------------------------------------------------------------------------

_A = "A: 固定の大きさ（module の定数の組・登録した directory）だけを辿る"
_B = "B: `SCAN_LIMIT` の固定の上限（長さを O(1) で比べてから辿る。上限の外は信頼しない / TypeError）"
_C = "C: iterator を返し、辿る側が要素ごとに数える"

LIVE_VALUES_WORK_OWNERS = {
    "package_file": _A,
    "_package_type_uncached": _B,
    "_trusted_callables": _B,
    "_trusted_namespace_value": _A,
    "_trusted_class_body_uncached": _B,
    "_type_lookup": _B,
    "_exact_str_keys": _B,
    "_scan_str_key": _B,
    "_builtin_hashed_type": _A,
    "_one_of": _A,
    "_in_mro": _B,
    "_dataclass_field_names": _B,
    "builtin_mapping": _B,
    "_builtin_behaviour": _A,
    "_unwrapped": _B,
    "_plain_keys": _B,
    "_hash_safe_keys": _B,
    "_hash_safe_key": _B,
    "merged_mappings": _B,
    "copied_container": _B,
    "lookup": _B,
    "_plain_key": _B,
    "_counted": _B,
}

#: B の関数が上限と比べる呼び出し（長さを O(1) で読んで比べる owner の関数）
_BOUNDING_CALLS = frozenset({"_within_scan", "_require_scan", "_exact_str_keys", "admit"})


def _live_values_functions():
    tree = ast.parse((PACKAGE_ROOT / "core" / "live_values.py").read_text(encoding="utf-8"))
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node.name, node
        elif isinstance(node, ast.ClassDef):
            for item in node.body:
                if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    yield f"{node.name}.{item.name}", item


def test_j22_every_proportional_function_of_the_owner_is_classified():
    proportional = {
        name: audit.proportional_constructs(function)
        for name, function in _live_values_functions()
        if audit.proportional_constructs(function)
    }
    assert set(proportional) == set(LIVE_VALUES_WORK_OWNERS), set(proportional) ^ set(LIVE_VALUES_WORK_OWNERS)


def test_j22_the_bounded_functions_compare_with_the_bound_before_they_walk():
    functions = dict(_live_values_functions())
    unbounded = []
    for name, kind in LIVE_VALUES_WORK_OWNERS.items():
        if kind != _B:
            continue
        calls = {
            (sub.func.id if isinstance(sub.func, ast.Name) else getattr(sub.func, "attr", None))
            for sub in ast.walk(functions[name]) if isinstance(sub, ast.Call)
        }
        ranges = any(
            isinstance(sub, ast.Call) and getattr(sub.func, "id", None) == "range"
            and any(isinstance(arg, ast.Name) and arg.id == "SCAN_LIMIT" for arg in sub.args)
            for sub in ast.walk(functions[name])
        )
        if not (calls & _BOUNDING_CALLS or ranges):
            unbounded.append(name)
    assert unbounded == []


def test_the_bound_has_one_owner():
    assert live_values.SCAN_LIMIT == 1 << 12
    source = (PACKAGE_ROOT / "core" / "live_values.py").read_text(encoding="utf-8")
    assert source.count("SCAN_LIMIT = ") == 1
