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

from scripts.function_tracer_pcode.core import live_values, read_limits
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
_AMORTIZED = (
    "B(償却): 型の信頼の判定 1 つにつき高々 1 つの仮の判定で、深さの組を移るのは高々 `NESTING_LIMIT` 回"
    "（仕事は判定の数に比例し、判定そのものは `SCAN_LIMIT` の中。循環の test が数を確かめる）"
)

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
    # 判定の途中の状態の 2 引数の `min`（入れ子の深さの比較）だけ
    "package_type": _A,
    "_trusted_class_body": _A,
    # 深さの組（`NESTING_LIMIT + 1` 個）を作るだけ
    "_Nesting.__init__": _A,
    "_settle": _AMORTIZED,
}

#: `core/read_limits`（作業量を受け取らない読みの固定の上限の owner）の入力に比例する関数
READ_LIMITS_WORK_OWNERS = {
    "_counted": _B,
    "prefix_within_limit": _B,
    # 2 引数の `max` だけ
    "omitted_beyond_limit": _A,
}

#: owner の file → その分類（J22 を owner 自身へ）
OWNER_WORK = {
    "core/live_values.py": LIVE_VALUES_WORK_OWNERS,
    "core/read_limits.py": READ_LIMITS_WORK_OWNERS,
}

#: B の関数が上限と比べる呼び出し（長さを O(1) で読んで比べる owner の関数）
_BOUNDING_CALLS = frozenset({"_within_scan", "_require_scan", "_exact_str_keys", "admit", "_admitted"})


def _live_values_functions(path="core/live_values.py"):
    tree = ast.parse((PACKAGE_ROOT / path).read_text(encoding="utf-8"))
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node.name, node
        elif isinstance(node, ast.ClassDef):
            for item in node.body:
                if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    yield f"{node.name}.{item.name}", item


@pytest.mark.parametrize("path", sorted(OWNER_WORK))
def test_j22_every_proportional_function_of_the_owner_is_classified(path):
    owners = OWNER_WORK[path]
    proportional = {
        name: audit.proportional_constructs(function)
        for name, function in _live_values_functions(path)
        if audit.proportional_constructs(function)
    }
    assert set(proportional) == set(owners), set(proportional) ^ set(owners)


@pytest.mark.parametrize("path", sorted(OWNER_WORK))
def test_j22_the_bounded_functions_compare_with_the_bound_before_they_walk(path):
    functions = dict(_live_values_functions(path))
    unbounded = []
    for name, kind in OWNER_WORK[path].items():
        if kind != _B:
            continue
        calls = {
            (sub.func.id if isinstance(sub.func, ast.Name) else getattr(sub.func, "attr", None))
            for sub in ast.walk(functions[name]) if isinstance(sub, ast.Call)
        }
        # `range(SCAN_LIMIT)` / `islice(..., SCAN_LIMIT [+ 1])`: 辿る数そのものを上限で切る
        ranges = any(
            isinstance(sub, ast.Call)
            and (getattr(sub.func, "id", None) == "range" or getattr(sub.func, "attr", None) == "islice")
            and any(
                isinstance(node, ast.Name) and node.id == "SCAN_LIMIT"
                for arg in sub.args for node in ast.walk(arg)
            )
            for sub in ast.walk(functions[name])
        )
        if not (calls & _BOUNDING_CALLS or ranges):
            unbounded.append(name)
    assert unbounded == []


def test_the_bound_has_one_owner():
    assert live_values.SCAN_LIMIT == 1 << 12
    source = (PACKAGE_ROOT / "core" / "live_values.py").read_text(encoding="utf-8")
    assert source.count("SCAN_LIMIT = ") == 1


def test_a_verified_container_never_runs_its_own_truth_method():
    """確かめた容器（反復・長さ・真偽は組み込みの slot）は、`__bool__` を上書きした subclass を含まない
    （audit は確かめた容器の真偽の判定を許すので、owner がその slot まで確かめる）。"""

    def _boom(self):  # pragma: no cover - must never run
        raise AssertionError("a live __bool__ ran")

    for base, predicate in (
        (list, live_values.builtin_sequence), (tuple, live_values.builtin_sequence),
        (set, live_values.builtin_set), (frozenset, live_values.builtin_set),
    ):
        loud = type(f"Loud{base.__name__}", (base,), {"__bool__": _boom})
        quiet = type(f"Quiet{base.__name__}", (base,), {})
        assert predicate(loud()) is False
        assert predicate(quiet()) is True
    assert live_values.builtin_mapping(type("LoudDict", (dict,), {"__bool__": _boom})()) is None
    assert live_values.builtin_mapping(type("QuietDict", (dict,), {})()) is not None


# ---------------------------------------------------------------------------
# 作業量を受け取らない関数の入口（`core/read_limits`: 上限の超過は登録済みの限界、診断は先頭だけ）
# ---------------------------------------------------------------------------


def _limitation(call, *args):
    """`call(*args)`（反復するなら最後まで）が上げた、固定の上限の超過の登録済みの限界。"""

    from scripts.function_tracer_pcode.core.errors import DeadlineExceeded

    started = time.perf_counter()
    with pytest.raises(DeadlineExceeded) as raised:
        for _ in call(*args):
            pass
    assert time.perf_counter() - started < 0.5, call
    assert raised.value.site == read_limits.SCAN_LIMITATION_SITE
    assert raised.value.reason_id == "analysis_budget_exceeded"
    return raised.value


def test_the_unmetered_readers_stop_at_the_bound_with_a_registered_limitation():
    """上限の外は内部バグ（`TypeError`）でなく、pair terminal な登録済みの限界（pair の台帳へ記録してから）。"""

    from scripts.function_tracer_pcode.core.errors import PairStopState, pair_failure_scope

    limit = live_values.SCAN_LIMIT
    inside = list(range(limit))
    assert list(read_limits.elements_within_limit(inside)) == inside
    assert dict(read_limits.items_within_limit({"a": 1})) == {"a": 1}
    for container in (list(range(limit + 1)), tuple(range(limit + 1)), set(range(limit + 1))):
        _limitation(read_limits.elements_within_limit, container)
    _limitation(read_limits.items_within_limit, {index: index for index in range(limit + 1)})
    # 文字列は要素の列として読まない（`elements_of` と同じ）
    with pytest.raises(TypeError):
        read_limits.elements_within_limit("x")
    # iterator は 1 要素ずつ数え、上限を超えた要素で止まる（それより先を引き出さない）
    pulled = []

    def _source():
        for index in range(BIG):
            pulled.append(index)
            yield index

    _limitation(read_limits.elements_within_limit, _source())
    assert len(pulled) == limit + 1
    with pair_failure_scope(("live_values", "scan"), None) as ledger:
        _limitation(read_limits.elements_within_limit, list(range(limit + 1)))
        pending = ledger.pending_failure()
    assert pending is not None and pending.stop_state is PairStopState.PAIR_TERMINAL_LIMITATION


def test_the_diagnostic_prefix_keeps_the_head_and_counts_the_rest():
    limit = live_values.SCAN_LIMIT
    values = tuple(range(limit + 7))
    assert read_limits.prefix_within_limit(values) == tuple(range(limit))
    assert read_limits.omitted_beyond_limit(values) == 7
    assert read_limits.prefix_within_limit(("a", "b")) == ("a", "b")
    assert read_limits.omitted_beyond_limit(("a", "b")) == 0
    # iterator は上限の個数を写したところで止める（残りを引き出さない）
    pulled = []

    def _source():
        for index in range(BIG):
            pulled.append(index)
            yield index

    assert len(_quick(read_limits.prefix_within_limit, _source())) == limit
    assert len(pulled) == limit + 1


def test_a_shared_scan_bounds_the_sum_of_nested_sequences():
    half = live_values.SCAN_LIMIT // 2 + 1
    scan = read_limits.scan_budget()
    assert len(list(read_limits.elements_within_limit(list(range(half)), scan))) == half
    _limitation(read_limits.elements_within_limit, list(range(half)), scan)
    # 共有しなければそれぞれは上限の内側
    assert len(list(read_limits.elements_within_limit(list(range(half))))) == half


def test_normalizing_truncations_bounds_records_and_references_together():
    """記録の参照 ID は 1 つの上限を共有する（1 件ずつは内側でも、和が外なら登録済みの限界）。"""

    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import (
        ExpansionBudgetTruncation,
        normalize_expansion_budget_truncations,
    )

    half = live_values.SCAN_LIMIT // 2 + 1
    records = [
        ExpansionBudgetTruncation(kind="paths", label=f"t{side}",
                                  referenced_event_ids=tuple(f"r{side}-{index}" for index in range(half)))
        for side in range(2)
    ]
    assert len(normalize_expansion_budget_truncations(records[:1])) == 1
    _limitation(lambda: iter(normalize_expansion_budget_truncations(records)))
    # 記録そのものも同じ上限に数える: 参照 ID の和は上限ちょうどでも、記録の 2 件で外
    exact = [
        ExpansionBudgetTruncation(kind="paths", label=f"e{side}", referenced_event_ids=tuple(
            f"e{side}-{index}" for index in range(live_values.SCAN_LIMIT // 2)
        ))
        for side in range(2)
    ]
    _limitation(lambda: iter(normalize_expansion_budget_truncations(exact)))
    assert len(normalize_expansion_budget_truncations(exact[:1])) == 1


def test_a_metaclass_hash_never_runs_through_the_class_body_cache():
    """class の body の cache の key は metaclass が `__hash__` / `__eq__` を持たない class だけ。"""

    calls = []

    class _Loud(type):
        def __hash__(cls):  # pragma: no cover - must never run
            calls.append("hash")
            return type.__hash__(cls)

        def __eq__(cls, other):  # pragma: no cover - must never run
            calls.append("eq")
            return type.__eq__(cls, other)

    class _Quiet(_Loud):
        __hash__ = type.__hash__
        __eq__ = type.__eq__

    base = _Loud("LoudBase", (), {})
    kind = _Quiet("QuietKind", (base,), {})
    live_values.package_type(kind)
    live_values._trusted_class_body(base)
    assert calls == []


def _holder_chain(tag):
    chain = [type(f"{tag}Leaf", (), {})]
    for index in range(live_values.NESTING_LIMIT + 4):
        chain.append(type(f"{tag}Holder{index}", (), {"inner": chain[-1]}))
    return chain


def test_a_verdict_cut_by_the_nesting_limit_is_not_cached():
    """入れ子の上限で切った判定は残さない: 深い型を先に聞いても、浅い深さから聞けば同じ形の新しい型と
    同じ判定（上限の内側）になる。"""

    cut_first = _holder_chain("Cut")
    fresh = _holder_chain("Fresh")
    mid = len(cut_first) // 2
    assert live_values.package_type(cut_first[-1]) is False  # 上限で切られる
    expected = live_values.package_type(fresh[mid])
    assert expected is True
    assert live_values.package_type(cut_first[mid]) is expected


def test_a_verdict_that_assumed_an_untrusted_ancestor_is_not_cached():
    """循環の途中で祖先を仮に信頼して出した判定は、祖先の判定が「信頼しない」に決まったら残らない。"""

    def outside():  # pragma: no cover - never called
        return None

    outside.__code__ = outside.__code__.replace(co_filename="/elsewhere/outside.py")
    ancestor = type("Ancestor", (), {})
    child = type("Child", (), {"ancestor": ancestor})
    ancestor.child = child
    ancestor.outside = outside
    assert live_values.package_type(ancestor) is False
    # child は ancestor を指す: 信頼しない型を指す型は信頼しない（仮定で出した「信頼」を残さない）
    assert live_values.package_type(child) is False


def test_timeout_reads_of_solver_results_are_bounded_by_the_read_limit():
    """receipt の無い結果の `is_timeout` は solver の結果の列を読みの上限までしか辿らない（外は登録済みの限界）。"""

    from types import SimpleNamespace

    from conftest import create_mock_result
    from scripts.function_tracer_pcode.core.errors import DeadlineExceeded
    from scripts.function_tracer_pcode.smt import SolverStatus

    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult

    result = create_mock_result(is_equivalent=None)
    # solver の owner が作った集約は、作ったときの事実を読む（行の数に依らず、読みの上限にかからない）
    rows = [SolverResult(solver_name="z3", status=SolverStatus.UNKNOWN)] * (live_values.SCAN_LIMIT + 1)
    result.solver_results = ParallelResult(results=rows + [SolverResult(solver_name="z3", status=SolverStatus.TIMEOUT)])
    assert result.is_timeout() is True
    result.solver_results = ParallelResult(results=rows)
    assert result.is_timeout() is False
    # owner の外の列（test の値など）は読みの固定の上限まで（外は登録済みの限界）
    result.solver_results = SimpleNamespace(
        results=[SimpleNamespace(status=SolverStatus.UNKNOWN)] * (live_values.SCAN_LIMIT + 1),
    )
    with pytest.raises(DeadlineExceeded):
        result.is_timeout()
    result.solver_results = SimpleNamespace(results=[SimpleNamespace(status=SolverStatus.TIMEOUT)])
    assert result.is_timeout() is True


def _connected_types(tag, count):
    kinds = [type(f"{tag}{index}", (), {}) for index in range(count)]
    for kind in kinds:
        for index, other in enumerate(kinds):
            if other is not kind:
                setattr(kind, f"peer{index}", other)
    return kinds


def _counting_evaluations(monkeypatch):
    calls = []
    real = live_values._package_type_uncached

    def _count(kind):
        calls.append(kind)
        return real(kind)

    monkeypatch.setattr(live_values, "_package_type_uncached", _count)
    return calls


def test_a_cycle_of_mutually_trusting_types_is_judged_once_per_type(monkeypatch):
    """互いを指す型の循環（強連結）でも、1 回の判定で型ごとに高々 1 度だけ判定する（循環の経路ごとに判定し直さない）。"""

    kinds = _connected_types("Peer", 12)
    calls = _counting_evaluations(monkeypatch)
    settled = []
    real_settle = live_values._settle

    def _settle(state, depth, **kwargs):
        settled.append(len(state.by_depth[depth]))
        return real_settle(state, depth, **kwargs)

    monkeypatch.setattr(live_values, "_settle", _settle)
    started = time.perf_counter()
    assert live_values.package_type(kinds[0]) is True
    assert time.perf_counter() - started < 1.0
    assert len(calls) <= len(kinds)
    # 仮の判定を確定する仕事は判定の数 × 入れ子の深さ以下（償却）
    assert sum(settled) <= len(calls) * live_values.NESTING_LIMIT
    # 根の判定が「信頼」に決まったので、循環の全部が確定した（聞き直しても判定しない）
    assert all(live_values.package_type(kind) is True for kind in kinds)
    assert len(calls) <= len(kinds)


def test_a_cycle_with_one_untrusted_member_is_untrusted_everywhere(monkeypatch):
    """循環の 1 つが信頼しない値を持てば、どの型から聞いても信頼しない（仮定の「信頼」を残さない）。判定の数も線形。"""

    def outside():  # pragma: no cover - never called
        return None

    outside.__code__ = outside.__code__.replace(co_filename="/elsewhere/outside.py")
    kinds = _connected_types("Tainted", 12)
    kinds[7].outside = outside
    calls = _counting_evaluations(monkeypatch)
    assert live_values.package_type(kinds[0]) is False
    assert all(live_values.package_type(kind) is False for kind in kinds)
    assert len(calls) <= 3 * len(kinds)


def test_cloning_a_signature_bounds_the_sum_of_parameters_members_and_copies():
    """signature の写しは、記述子の列・member・写す容器の要素の和を 1 つの読みの上限にする（積にしない）。"""

    from types import SimpleNamespace

    from scripts.function_tracer_pcode.core.errors import DeadlineExceeded
    from scripts.function_tracer_pcode.core.signature import FunctionSignature

    third = live_values.SCAN_LIMIT // 3
    # 1 つずつは上限の内側（記述子の数・member の数・容器の要素の数のどれも）でも、和は外
    parameters = [{"name": f"p{index}", "tags": ["t"]} for index in range(third)]
    analysis = SimpleNamespace(return_type="int", return_type_obj=None, parameters=parameters)
    with pytest.raises(DeadlineExceeded):
        FunctionSignature.from_analysis(analysis)
    small = SimpleNamespace(return_type="int", return_type_obj=None, parameters=[{"name": "p", "tags": ["t"]}])
    signature = FunctionSignature.from_analysis(small)
    assert signature.parameters == [{"name": "p", "tags": ["t"]}]
    assert signature.parameters[0]["tags"] is not small.parameters[0]["tags"]
