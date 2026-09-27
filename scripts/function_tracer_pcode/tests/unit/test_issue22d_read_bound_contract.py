# -*- coding: utf-8 -*-
"""Issue #22 PR-22-D: 作業量を受け取らない読みの「量が多すぎる」の意味の契約（責務の境界を型と test で固定する）。

* `core/live_values`（安全の owner）: 値の storage の読みが固定の上限を超えたら、意味を今の文脈の量の
  owner へ渡す（作業量へ数える・呼ぶ側へ量の信号 `StorageBeyondReadBound`・登録した `core/read_limits`）。
  安全でない値は `TypeError` / `None`（量と混同しない）。
* `core/read_limits`（量の意味の owner）: 基底型の slot で O(1) に数えてから（安全の判定より先に）上限と
  比べ、上限の外は型つきの登録済みの限界 `FixedReadBoundExceeded`（pair terminal）。作業量の無い文脈の
  入れ子の読みの上限の外も、登録した owner として同じ限界にする（記録が先）。
* `DeadlineExceeded` は #106 の時間・段数の型で、読みの量の限界に使わない。
* 量の多い入力は容器の種類（dict / OrderedDict / subclass / proxy / iterator）で意味が変わらない。
"""

from __future__ import annotations

import ast
import json
import time
import types
from collections import OrderedDict, namedtuple
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.core import live_values, read_limits
from scripts.function_tracer_pcode.core.errors import (
    AnalysisFailureError,
    AnalysisLimitation,
    DeadlineExceeded,
    PairFailureKind,
    PairStopState,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.core.json_encoding import (
    RESULT_JSON_POLICY,
    JsonBudgetExhausted,
    JsonValueRejected,
)
from scripts.function_tracer_pcode.core.read_limits import FixedReadBoundExceeded
from scripts.function_tracer_pcode.tests.unit.test_issue106_pair_limitation_propagation import (
    _new_checker,
    _run_pair,
)
from scripts.function_tracer_pcode.tests.unit.test_issue125_limitation_finalization import _connector
from scripts.function_tracer_pcode.tests.unit.test_issue22d_output_preparation import (
    _analyses,
    _analyze_from,
)

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
LIMIT = live_values.SCAN_LIMIT
BEYOND = live_values.StorageBeyondReadBound


@pytest.fixture(autouse=True)
def _clean_scopes():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


class _DictSub(dict):
    pass


class _OrderedSub(OrderedDict):
    pass


class _ListSub(list):
    pass


class _SetSub(set):
    pass


_Pair = namedtuple("_Pair", "a b")


class _LoudDict(dict):
    """振る舞いを上書きした（安全でない）mapping: 上書きした code は 1 度も呼ばれない。"""

    def items(self):  # pragma: no cover - must never run
        raise AssertionError("a live items() ran")

    def __iter__(self):  # pragma: no cover - must never run
        raise AssertionError("a live __iter__ ran")

    def __len__(self):  # pragma: no cover - must never run
        raise AssertionError("a live __len__ ran")


def _mappings(count):
    base = {f"k{index}": index for index in range(count)}
    return {
        "dict": dict(base),
        "OrderedDict": OrderedDict(base),
        "dict_subclass": _DictSub(base),
        "OrderedDict_subclass": _OrderedSub(base),
        "proxy(dict)": types.MappingProxyType(dict(base)),
        "proxy(OrderedDict)": types.MappingProxyType(OrderedDict(base)),
    }


def _sequences(count):
    return {
        "list": list(range(count)),
        "tuple": tuple(range(count)),
        "set": set(range(count)),
        "frozenset": frozenset(range(count)),
        "list_subclass": _ListSub(range(count)),
        "set_subclass": _SetSub(range(count)),
        "iterator": iter(list(range(count))),
        "dict_keys": {index: index for index in range(count)}.keys(),
    }


def _drain(result):
    if hasattr(result, "__next__"):
        return list(result)
    return result


def _limitation(call, *args):
    started = time.perf_counter()
    with pytest.raises(FixedReadBoundExceeded) as raised:
        _drain(call(*args))
    assert time.perf_counter() - started < 1.0, call
    return raised.value


# ---------------------------------------------------------------------------
# 型: 読みの量の限界は deadline と別の型・同じ登録済みの reason・pair terminal
# ---------------------------------------------------------------------------


def test_a_fixed_read_overflow_is_a_dedicated_limitation_not_a_deadline():
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import ANALYSIS_BUDGET_REASON_ID
    from scripts.function_tracer_pcode.core import errors

    exc = FixedReadBoundExceeded("probe", observed=LIMIT + 1)
    assert isinstance(exc, AnalysisLimitation)
    assert not isinstance(exc, DeadlineExceeded) and DeadlineExceeded not in type(exc).__mro__
    # reason id は authority の契約と共通、分類（型・site・target の種類・stop state）は deadline と別
    assert exc.reason_id == ANALYSIS_BUDGET_REASON_ID == DeadlineExceeded.REASON_ID
    assert exc.site == read_limits.SCAN_LIMITATION_SITE
    assert exc.target_key[0] == read_limits.READ_BOUND_TARGET == "fixed_read_bound"
    # stop state は軸 C の owner が型から決める（作る場所で選ばない。deadline の stop state にならない）
    assert errors._default_stop_state(PairFailureKind.LIMITATION, exc) is PairStopState.PAIR_TERMINAL_LIMITATION
    deadline = DeadlineExceeded("probe", site="probe")
    assert errors._default_stop_state(PairFailureKind.LIMITATION, deadline) is PairStopState.PAIR_TERMINAL_DEADLINE


def test_a_fixed_read_overflow_is_recorded_as_a_pair_terminal_limitation():
    with pair_failure_scope(("read_limits", "stop"), None) as ledger:
        _limitation(read_limits.elements_within_limit, list(range(LIMIT + 1)))
        pending = ledger.pending_failure()
    assert pending is not None and pending.kind is PairFailureKind.LIMITATION
    assert pending.stop_state is PairStopState.PAIR_TERMINAL_LIMITATION
    assert type(pending.exception) is FixedReadBoundExceeded


_DEADLINE_OWNERS: frozenset = frozenset()
"""production で `DeadlineExceeded` を作ってよい module（#106 の deadline / checkpoint の owner が足す）。"""


def _production_modules():
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        relative = path.relative_to(PACKAGE_ROOT).as_posix()
        if relative.startswith("tests/"):
            continue
        yield relative, ast.parse(path.read_text(encoding="utf-8"))


def _name_of(node):
    return node.id if isinstance(node, ast.Name) else getattr(node, "attr", None)


def test_only_the_deadline_owner_constructs_or_subclasses_deadline_exceeded():
    """`DeadlineExceeded` を作る・継承するのは #106 の deadline の owner だけ（読みの量の限界に流用しない）。"""

    constructed, subclassed = [], []
    for relative, tree in _production_modules():
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and _name_of(node.func) == "DeadlineExceeded":
                constructed.append(relative)
            if isinstance(node, ast.ClassDef) and any(_name_of(base) == "DeadlineExceeded" for base in node.bases):
                subclassed.append(relative)
    assert set(constructed) <= _DEADLINE_OWNERS, constructed
    assert set(subclassed) <= _DEADLINE_OWNERS, subclassed


def test_the_storage_signal_is_neither_unsafety_nor_a_limitation():
    for base in (TypeError, AnalysisFailureError, AnalysisLimitation, DeadlineExceeded):
        assert not issubclass(BEYOND, base), base


#: 量の信号を受け取ってよい module（`signalled_storage_reads` の中で、同じ関数の中で捕まえる）と、その意味
_SIGNAL_OWNERS = {
    "core/read_limits.py": "診断の写し（止めない: 写せた先頭まで）",
    "core/live_values.py": "型の信頼の判定（文脈に依らない: 上限の外の値を持つ型は信頼しない）",
}
#: 値の storage の読みを作業量へ数えてよい owner（`metered_storage_reads` を使う module）
_METER_OWNERS = frozenset({
    "core/json_encoding.py", "core/canonical_digest.py", "core/budget_policy.py", "proof/obligations/snapshot.py",
    "checker/unknown_reason.py",
})
#: 作業量の型を登録してよい owner（その作業量の超過の意味の owner）
_METER_TYPE_OWNERS = frozenset({"core/json_encoding.py", "core/budget_policy.py"})
_OWNER_NAMES = (
    "StorageBeyondReadBound", "signalled_storage_reads", "register_unmetered_read_owner", "fixed_bound_reads",
)


def _references(tree, name):
    """`name` を名前か属性で参照する node（別名への代入・`except` の tuple・`is` の比較も参照）。"""

    return [node for node in ast.walk(tree) if (isinstance(node, ast.Name) and node.id == name)
            or (isinstance(node, ast.Attribute) and node.attr == name)
            or (isinstance(node, ast.alias) and (node.name == name or node.asname == name))]


def test_only_declared_owners_decide_the_meaning_of_a_read_beyond_the_bound():
    """量の意味を決める入口は参照で数える（handler の形・別名・`except Exception` に依らない）: 量の信号と
    その文脈を参照するのは宣言した owner だけ、作業量を受け取らない文脈の owner の登録は `read_limits` だけ。"""

    referencing = {name: set() for name in _OWNER_NAMES}
    registering, metering, meter_types = set(), set(), set()
    for relative, tree in _production_modules():
        for name in _OWNER_NAMES:
            if _references(tree, name):
                referencing[name].add(relative)
        for node in ast.walk(tree):
            if isinstance(node, ast.Call):
                called = _name_of(node.func)
                if called == "register_unmetered_read_owner":
                    registering.add(relative)
                if called == "metered_storage_reads":
                    metering.add(relative)
                if called == "register_storage_meter":
                    meter_types.add(relative)
    assert referencing["StorageBeyondReadBound"] <= set(_SIGNAL_OWNERS), referencing
    assert referencing["signalled_storage_reads"] <= set(_SIGNAL_OWNERS), referencing
    assert registering == {"core/read_limits.py"}, registering
    assert referencing["register_unmetered_read_owner"] <= {"core/read_limits.py", "core/live_values.py"}
    assert metering == _METER_OWNERS, metering
    # 反復の確かめも含めて固定の上限で読む文脈は、作業量を受け取らない読みの入口だけ
    assert referencing["fixed_bound_reads"] <= {"core/read_limits.py", "core/live_values.py"}, referencing
    assert meter_types == _METER_TYPE_OWNERS, meter_types


def _functions(tree):
    return [node for node in ast.walk(tree) if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))]


def test_every_signalled_read_catches_the_signal_in_the_same_function():
    """`signalled_storage_reads` の本体は `StorageBeyondReadBound` を捕まえる `try` だけ（信号を関数の外へ出さない）。"""

    found = 0
    for relative in _SIGNAL_OWNERS:
        tree = ast.parse((PACKAGE_ROOT / relative).read_text(encoding="utf-8"))
        for function in _functions(tree):
            for node in ast.walk(function):
                if not isinstance(node, ast.With):
                    continue
                if not any(isinstance(item.context_expr, ast.Call) and _name_of(item.context_expr.func) == "signalled_storage_reads"
                           for item in node.items):
                    continue
                found += 1
                assert len(node.body) == 1 and isinstance(node.body[0], ast.Try), (relative, function.name)
                handlers = node.body[0].handlers
                caught = [item for handler in handlers if handler.type is not None
                          for item in (handler.type.elts if isinstance(handler.type, ast.Tuple) else [handler.type])]
                assert [_name_of(item) for item in caught] == ["StorageBeyondReadBound"], (relative, function.name)
    assert found == 2  # 型の信頼の判定と、診断の写し


def test_the_production_entries_register_the_unmetered_read_owner():
    """作業量を受け取らない読みの量の意味の owner は、pair を実行する入口を import しただけで登録済み
    （登録が無いと量の信号が pair の境界まで届く）。"""

    import subprocess
    import sys

    root = PACKAGE_ROOT.parents[1]
    for entry in ("scripts.function_tracer_pcode.checker.pair_execution", "scripts.function_tracer_pcode.checker.checker",
                  "scripts.function_tracer_pcode.authority.lifecycle.production_boundary"):
        probe = (f"import {entry}\n"
                 "from scripts.function_tracer_pcode.core import live_values, read_limits\n"
                 "assert live_values._UNMETERED_READ_OWNER == [read_limits.raise_read_bound_exceeded]\n")
        completed = subprocess.run([sys.executable, "-B", "-c", probe], cwd=root, capture_output=True, text=True)
        assert completed.returncode == 0, (entry, completed.stderr[-2000:])


def test_a_second_unmetered_read_owner_is_refused():
    with pytest.raises(ValueError):
        live_values.register_unmetered_read_owner(_production_modules)
    with pytest.raises(TypeError):
        live_values.register_unmetered_read_owner(len)
    # 同じ owner の登録は何もしない
    live_values.register_unmetered_read_owner(read_limits.raise_read_bound_exceeded)


# ---------------------------------------------------------------------------
# 容器の種類に依らない意味（4096 / 4097 の境界）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("kind", sorted(_sequences(1)))
def test_every_sequence_kind_reads_up_to_the_bound_and_overflows_with_the_same_limitation(kind):
    assert len(_drain(read_limits.elements_within_limit(_sequences(LIMIT)[kind]))) == LIMIT
    exc = _limitation(read_limits.elements_within_limit, _sequences(LIMIT + 1)[kind])
    assert exc.observed == LIMIT + 1


@pytest.mark.parametrize("kind", sorted(_mappings(1)))
def test_every_mapping_kind_reads_up_to_the_bound_and_overflows_with_the_same_limitation(kind):
    assert len(_drain(read_limits.items_within_limit(_mappings(LIMIT)[kind]))) == LIMIT
    assert len(_drain(read_limits.elements_within_limit(_mappings(LIMIT)[kind]))) == LIMIT
    _limitation(read_limits.items_within_limit, _mappings(LIMIT + 1)[kind])
    _limitation(read_limits.elements_within_limit, _mappings(LIMIT + 1)[kind])


@pytest.mark.parametrize("kind", ["dict", "OrderedDict", "dict_subclass", "list", "list_subclass"])
def test_every_copied_kind_copies_up_to_the_bound_and_overflows_with_the_same_limitation(kind):
    small = {**_mappings(LIMIT), **_sequences(LIMIT)}[kind]
    copied = read_limits.copied_within_limit(small)
    assert type(copied) in (dict, list) and len(copied) == LIMIT
    _limitation(read_limits.copied_within_limit, {**_mappings(LIMIT + 1), **_sequences(LIMIT + 1)}[kind])


def test_unsafe_custom_behaviour_is_rejected_safely_and_not_mistaken_for_overflow():
    """上書きした振る舞いの mapping: 上限の内側は安全でないとして拒む（`TypeError`、限界にしない）。上限の外は
    量を先に数えるので同じ量の限界（上書きした code はどちらでも呼ばない）。"""

    small = _LoudDict({"a": 1})
    for call in (read_limits.items_within_limit, read_limits.elements_within_limit):
        with pytest.raises(TypeError) as raised:
            _drain(call(small))
        assert not isinstance(raised.value, AnalysisLimitation)
    big = _LoudDict({f"k{index}": index for index in range(LIMIT + 1)})
    _limitation(read_limits.items_within_limit, big)
    _limitation(read_limits.copied_within_limit, big)


def test_mapping_proxy_depth_and_size_are_separate_quantities_with_the_same_bound():
    def _chain(layers, inner):
        proxy = inner
        for _ in range(layers):
            proxy = types.MappingProxyType(proxy)
        return proxy

    # 包む段は要素と別の量: 要素がちょうど上限の proxy は読める、段がちょうど上限の鎖も読める
    assert len(_drain(read_limits.items_within_limit(_chain(1, {f"k{i}": i for i in range(LIMIT)})))) == LIMIT
    assert len(_drain(read_limits.items_within_limit(_chain(LIMIT, {"a": 1})))) == 1
    _limitation(read_limits.items_within_limit, _chain(1, {f"k{i}": i for i in range(LIMIT + 1)}))
    _limitation(read_limits.items_within_limit, _chain(LIMIT + 1, {"a": 1}))


def test_a_shared_scan_bounds_the_sum_at_the_boundary():
    half = LIMIT // 2
    scan = read_limits.scan_budget()
    assert len(_drain(read_limits.elements_within_limit(list(range(half)), scan))) == half
    assert len(_drain(read_limits.elements_within_limit(list(range(half)), scan))) == half  # 和がちょうど上限
    exc = _limitation(read_limits.elements_within_limit, [0], scan)
    assert exc.observed == LIMIT + 1
    other = read_limits.scan_budget()
    _drain(read_limits.elements_within_limit(list(range(half)), other))
    # iterator も同じ和（1 要素ずつ数える）: 和がちょうど上限までは読め、その次で限界
    assert len(_drain(read_limits.elements_within_limit(iter(range(half)), other))) == half
    _limitation(read_limits.elements_within_limit, iter(range(1)), other)


def test_nested_quantities_inside_a_read_are_the_same_limitation():
    """写しの中の入れ子の読み（key の tuple の node）の量も、同じ量の限界（安全でない key と混同しない）。"""

    _limitation(read_limits.copied_within_limit, {tuple(range(LIMIT + 5)): 1})
    with pytest.raises(TypeError) as raised:
        read_limits.copied_within_limit({(1, object()): 1})
    assert not isinstance(raised.value, AnalysisLimitation)


def test_the_overflow_check_runs_before_any_safety_scan_or_iteration(monkeypatch):
    """上限の外の容器は、安全の判定（key の走査）も反復も始める前に限界になる（O(1) の数だけで決める）。"""

    touched = []
    for name in ("_hash_safe_keys", "_plain_keys", "_exact_str_raw", "elements_of", "items_of", "copied_container"):
        real = getattr(live_values, name)
        monkeypatch.setattr(live_values, name, lambda *args, _real=real, _name=name, **kw: touched.append(_name) or _real(*args, **kw))
    big = OrderedDict((f"k{index}", index) for index in range(LIMIT + 1))
    for call in (read_limits.items_within_limit, read_limits.elements_within_limit, read_limits.copied_within_limit):
        _limitation(call, big)
    assert touched == []


def test_diagnostic_prefixes_never_stop_the_pair():
    values = tuple(range(LIMIT + 7))
    head = read_limits.prefix_within_limit(values)
    assert head == tuple(range(LIMIT)) and read_limits.omitted_beyond_limit(values, kept=len(head)) == 7
    # 反復の安全を上限の中で確かめられない容器は、何も写さずに全部を写さなかった件数にする（限界にしない）
    big = OrderedDict((f"k{index}", index) for index in range(LIMIT + 7))
    rows = read_limits.prefix_items_within_limit(big)
    assert rows == () and read_limits.omitted_beyond_limit(big, kept=0) == LIMIT + 7
    assert read_limits.prefix_within_limit(big) == ()
    pulled = []

    def _source():
        for index in range(10 * LIMIT):
            pulled.append(index)
            yield index

    assert len(read_limits.prefix_within_limit(_source())) == LIMIT
    assert len(pulled) == LIMIT + 1


# ---------------------------------------------------------------------------
# 作業量を持つ owner の中では容器の種類に依らず同じ（meter が上限を超えた分を数える）
# ---------------------------------------------------------------------------


class _Record:
    def __init__(self, width):
        self.x = 1
        self.__dict__.update({f"a{index}": index for index in range(width)})

    def json_items(self):
        yield "x", live_values.attribute(self, "x")


@pytest.mark.parametrize("kind", ["dict", "OrderedDict", "dict_subclass", "OrderedDict_subclass", "proxy(OrderedDict)"])
def test_the_walker_treats_large_containers_alike(kind):
    """作業量で数える walker の中では、確かめの要る容器（OrderedDict・proxy）も dict と同じに読む
    （予算が足りればどれも書け、足りなければどれも同じ予算の超過）。"""

    value = _mappings(LIMIT + 500)[kind]
    reference = RESULT_JSON_POLICY.prepare({"f": _mappings(LIMIT + 500)["dict"]}, max_bytes=1 << 24)
    prepared = RESULT_JSON_POLICY.prepare({"f": value}, max_bytes=1 << 24)
    assert prepared.value() == reference.value()
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare({"f": value}, max_bytes=1 << 10)


def test_the_walker_reads_a_record_with_a_large_instance_state():
    record = _Record(LIMIT + 10)
    assert RESULT_JSON_POLICY.prepare(record, max_bytes=1 << 20).value() == {"x": 1}
    # 作業量の外では作業量を受け取らない読みの量の限界（登録した owner が決める）
    with pytest.raises(FixedReadBoundExceeded):
        live_values.attribute(record, "x")


@pytest.mark.parametrize("kind", ["dict", "OrderedDict", "proxy(OrderedDict)"])
def test_an_unbounded_walk_and_a_nested_uncounted_walk_treat_large_containers_alike(kind):
    """上限の無い作業量の walk・入れ子の数えない walk も、容器の種類で結果を変えない（上限なしで読む）。"""

    from scripts.function_tracer_pcode.core.budget_policy import serialization_scope
    from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec
    from scripts.function_tracer_pcode.core.canonical_digest import canonical_fingerprint
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget

    reference = _mappings(LIMIT + 50)["dict"]
    value = _mappings(LIMIT + 50)[kind]
    assert RESULT_JSON_POLICY.materialize(value) == RESULT_JSON_POLICY.materialize(reference)
    assert RESULT_JSON_POLICY.prepare({"f": value}, max_bytes=None).value() == {"f": dict(reference)}
    assert canonical_fingerprint(value, work=JsonBudget(None)) == canonical_fingerprint(dict(reference), work=JsonBudget(None))
    # 予算なしの凍結は予算つきの凍結と同じ写し（容器の種類で予算なしの側だけ失敗しない）
    assert SnapshotFingerprintCodec.freeze(value) == SnapshotFingerprintCodec.freeze(value, budget=JsonBudget(1 << 26))
    with serialization_scope(site="probe", target_parts=("probe",), terminal=False, max_bytes=1 << 24, enabled=True) as work:
        counted = RESULT_JSON_POLICY.materialize(value, budget=work)
        uncounted = RESULT_JSON_POLICY.materialize(value, counted=True)
    assert counted == uncounted == RESULT_JSON_POLICY.materialize(reference)


def test_iteration_safety_is_not_weakened_to_length_safety():
    """`builtin_container` は反復してよいかの判定: key の hash を上書きした `OrderedDict` は長さは読めても
    反復してよい容器ではない（その `__hash__` を呼ぶ読み方を許さない）。"""

    armed = []

    class _Key(str):
        def __hash__(self):
            if armed:  # pragma: no cover - must never run once armed
                raise AssertionError("a live key's __hash__ ran")
            return str.__hash__(self)

        __eq__ = str.__eq__

    loud = OrderedDict()
    loud[_Key("k")] = 1
    armed.append(True)
    assert live_values.size(loud) == 1 and live_values.as_bool(loud) is True
    assert live_values.builtin_container(loud) is False
    assert live_values.builtin_mapping(loud) is None
    with pytest.raises(TypeError):
        live_values.elements_of(loud)


def test_solver_totals_read_the_rows_through_the_live_value_rules():
    from scripts.function_tracer_pcode.checker.diagnostics import _SolverTotals
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget

    class _LoudRows(list):
        def __iter__(self):  # pragma: no cover - must never run
            raise AssertionError("a live __iter__ ran")

    totals = _SolverTotals("invocations")
    with pytest.raises(TypeError):
        totals.add(SimpleNamespace(results=_LoudRows([SimpleNamespace(elapsed_time=1.0)])), work=JsonBudget(100))
    seconds = _SolverTotals("seconds")
    seconds.add(SimpleNamespace(results=[SimpleNamespace(elapsed_time=1.5)] * 2), work=JsonBudget(100))
    assert seconds.result(work=None) == 3.0


def test_legacy_reason_lookups_count_their_reads_in_the_matching_work():
    """診断の legacy の照合は索引の読みも照合の作業量で数える（固定の上限の外でも作業量の中なら引ける、
    足りなければ一致しない。量の限界で pair を止めない・量を「安全でない」にしない）。"""

    from scripts.function_tracer_pcode.checker.unknown_reason import _count_of, _index_positions
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget

    index = {f"k{position}": [position] for position in range(LIMIT + 100)}
    with pair_failure_scope(("read_limits", "legacy"), None) as ledger:
        work = JsonBudget(1 << 20)
        assert _index_positions(index, "k7", work) == {7}
        assert work.consumed >= 100
        assert _index_positions(index, "k7", JsonBudget(10)) == set()
        counts = {f"r{position}": position for position in range(LIMIT + 100)}
        assert _count_of(counts, "r3", JsonBudget(1 << 20)) == 3
        assert _count_of(counts, "r3", JsonBudget(10)) == 0
        assert ledger.pending_failure() is None


def test_a_meter_charges_one_traversal_once():
    """key の判定・写しの走査は 1 回につき上限を超えた分を 1 度だけ数える（入れ子の node は同じ走査へ）。"""

    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget

    mixed = {index: index for index in range(LIMIT + 10)}
    work = JsonBudget(1 << 20)
    with live_values.metered_storage_reads(work):
        copied = live_values.copied_container(mixed)
    assert copied == mixed and work.consumed == 10
    pairs = {(index, index): index for index in range(LIMIT)}
    work = JsonBudget(1 << 20)
    with live_values.metered_storage_reads(work):
        assert live_values.lookup(pairs, (1, 1)) == 1
    # key の数（LIMIT、上限の中）と key の tuple の node（2 * LIMIT）は別の量: node の上限を超えた分だけ
    # （lookup の key 自身の判定は別の読みで上限の中）
    assert work.consumed == 2 * LIMIT - LIMIT


def test_keys_and_key_tuple_nodes_are_separate_quantities():
    """key の数（O(1) で数える）と key の tuple の node（走査の中で数える）は別の量で、それぞれ 1 回の
    走査の中の和を上限と比べる（key ごとに上限まで辿らない: 上限の積にしない）。上限の内側の数の mapping
    を、node を足して上限の外にしない（数えて通した入口の後で落ちない）。"""

    small = {(index, "x"): index for index in range(1400)}  # key 1,400・node 2,800
    ordered = OrderedDict(small)
    assert live_values.lookup(small, (3, "x")) == 3
    assert len(live_values.copied_container(small)) == 1400
    assert len(read_limits.copied_within_limit(small)) == 1400
    assert live_values.builtin_mapping(ordered) is ordered
    assert len(list(read_limits.items_within_limit(ordered))) == 1400
    assert len(read_limits.prefix_items_within_limit(ordered)) == 1400

    width = 8
    keys = LIMIT // width  # node の和がちょうど上限
    probe = tuple(range(width))
    at_bound = OrderedDict((tuple(range(index, index + width)), index) for index in range(keys))
    beyond = OrderedDict((tuple(range(index, index + width)), index) for index in range(keys + 1))
    assert live_values.lookup(dict(at_bound), probe) == 0
    assert len(list(read_limits.items_within_limit(at_bound))) == keys
    with pytest.raises(FixedReadBoundExceeded):
        live_values.lookup(dict(beyond), probe)  # 隠れた読み（key で引く前の確かめ）
    with pytest.raises(FixedReadBoundExceeded):
        read_limits.items_within_limit(beyond)  # 固定の上限の入口（入れ子の量も同じ上限）
    with pytest.raises(FixedReadBoundExceeded):
        read_limits.copied_within_limit(dict(beyond))

    # key ごとには上限の中（1 つの key の node は上限より少し少ない）でも、和は 2 つ目の key で外
    shared = tuple(range(LIMIT - 10))
    wide = {(index, shared): index for index in range(LIMIT)}
    started = time.perf_counter()
    with pytest.raises(FixedReadBoundExceeded):
        live_values.lookup(wide, "absent")
    with pytest.raises(FixedReadBoundExceeded):
        read_limits.copied_within_limit(wide)
    with pytest.raises(FixedReadBoundExceeded):
        read_limits.items_within_limit(OrderedDict(wide))
    assert time.perf_counter() - started < 1.0


def test_unowned_traversals_verify_like_they_iterate_and_hidden_reads_are_bounded():
    """量の owner の無い文脈: 反復の確かめ（`OrderedDict` の key の hash）は反復の一部で、dict の反復と
    同じく上限なしで読む（容器の種類で結果を変えない・台帳に何も残さない）。隠れた読み（key で引く・
    名前で属性を読む）は固定の上限の限界。"""

    from scripts.function_tracer_pcode.checker.cause_aggregate import freeze_identity
    from scripts.function_tracer_pcode.proof.cause_identity import _tuple_item

    count = LIMIT + 900
    reference = {f"k{index}": index for index in range(count)}
    with pair_failure_scope(("read_limits", "traversals"), None) as ledger:
        for kind in ("OrderedDict", "OrderedDict_subclass", "proxy(OrderedDict)", "dict_subclass"):
            value = _mappings(count)[kind]
            assert len(list(live_values.items_of(value))) == count, kind
            assert live_values.builtin_container(value) is True, kind
            assert _tuple_item({"a": value}) == _tuple_item({"a": dict(reference)}), kind
            assert freeze_identity({"m": value}) == freeze_identity({"m": dict(reference)}), kind
            assert len(live_values.copied_container(_mappings(count)["OrderedDict"])) == count
        assert ledger.pending_failure() is None
        with pytest.raises(FixedReadBoundExceeded):
            live_values.lookup(_mappings(count)["OrderedDict"], "k1")
        assert type(ledger.pending_failure().exception) is FixedReadBoundExceeded


def test_the_read_limit_entries_keep_their_fixed_bound_inside_a_meter():
    """作業量を受け取らない読みの入口は、作業量の文脈の中でも固定の上限（API の選択。作業量を持つ呼ぶ
    側は walker を使う）。"""

    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget

    big = OrderedDict((f"k{index}", index) for index in range(LIMIT + 1))
    with live_values.metered_storage_reads(JsonBudget(None)):
        assert len(list(live_values.items_of(big))) == LIMIT + 1
        with pytest.raises(FixedReadBoundExceeded):
            read_limits.items_within_limit(big)
        with pytest.raises(FixedReadBoundExceeded):
            read_limits.elements_within_limit(list(range(LIMIT + 1)))


# ---------------------------------------------------------------------------
# pair の結果: 量の多い入力は登録済みの理由の UNKNOWN（ERROR / TypeError にしない）
# ---------------------------------------------------------------------------


def _pair_with(read):
    def _plan(*_args, **_kwargs):
        read()
        raise AssertionError("the read should have stopped the pair")  # pragma: no cover

    return _run_pair(analyze=_analyze_from(*_analyses()), stage_plan=_plan, checker=_new_checker(_connector()))


def _read_bound_unknown(result):
    assert result.final_outcome == "UNKNOWN", result.final_outcome
    reasons = {reason.reason_id for reason in result.unknown_reasons}
    assert read_limits.READ_BOUND_REASON_ID in reasons
    assert "FixedReadBoundExceeded" in json.dumps(result.diagnostics, default=str)


@pytest.mark.parametrize("kind", ["OrderedDict", "dict_subclass", "proxy(OrderedDict)"])
def test_a_large_container_read_without_work_is_a_reason_unknown(kind):
    big = _mappings(LIMIT + 100)[kind]
    _read_bound_unknown(_pair_with(lambda: list(read_limits.items_within_limit(big))))


def test_an_unmetered_live_value_read_beyond_the_bound_is_the_same_reason_unknown():
    """`live_values` の読みを作業量の外で直接使っても、同じ登録済みの限界（内部バグの ERROR にしない）。"""

    big = {f"k{index}": index for index in range(LIMIT + 100)}
    _read_bound_unknown(_pair_with(lambda: live_values.lookup(big, "k1")))


def test_an_unmetered_read_beyond_the_bound_is_recorded_before_it_can_be_swallowed():
    """登録した owner は限界を台帳へ記録してから上げる: 途中の `except Exception` が握り潰しても pair は止まる。"""

    big = {f"k{index}": index for index in range(LIMIT + 100)}
    with pair_failure_scope(("read_limits", "swallowed"), None) as ledger:
        try:
            live_values.lookup(big, "k1")  # 隠れた読み（key で引く前の key の確かめ）
        except Exception:  # noqa: BLE001 - the swallowing intermediate the ledger exists for
            pass
        pending = ledger.pending_failure()
    assert pending is not None and type(pending.exception) is FixedReadBoundExceeded
    assert pending.stop_state is PairStopState.PAIR_TERMINAL_LIMITATION


# ---------------------------------------------------------------------------
# 作業量を受け取らない読みの利用者（record の構築・写し）
# ---------------------------------------------------------------------------


def test_normalizing_truncations_bounds_records_and_references_together():
    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import (
        ExpansionBudgetTruncation,
        normalize_expansion_budget_truncations,
    )

    half = LIMIT // 2
    exact = [
        ExpansionBudgetTruncation(kind="paths", label=f"e{side}", referenced_event_ids=tuple(
            f"e{side}-{index}" for index in range(half)
        ))
        for side in range(2)
    ]
    assert len(normalize_expansion_budget_truncations(exact[:1])) == 1
    # 記録そのものも同じ上限に数える: 参照 ID の和は上限ちょうどでも、記録の 2 件で外
    _limitation(lambda: iter(normalize_expansion_budget_truncations(exact)))


def test_timeout_reads_of_solver_results_are_bounded_by_the_read_limit():
    from conftest import create_mock_result
    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus

    result = create_mock_result(is_equivalent=None)
    rows = [SolverResult(solver_name="z3", status=SolverStatus.UNKNOWN)] * (LIMIT + 1)
    result.solver_results = ParallelResult(results=rows + [SolverResult(solver_name="z3", status=SolverStatus.TIMEOUT)])
    assert result.is_timeout() is True
    result.solver_results = ParallelResult(results=rows)
    assert result.is_timeout() is False
    result.solver_results = SimpleNamespace(results=[SimpleNamespace(status=SolverStatus.UNKNOWN)] * (LIMIT + 1))
    with pytest.raises(FixedReadBoundExceeded):
        result.is_timeout()


def test_cloning_a_signature_bounds_the_sum_of_parameters_members_and_copies():
    from scripts.function_tracer_pcode.core.signature import FunctionSignature

    third = LIMIT // 3
    parameters = [{"name": f"p{index}", "tags": ["t"]} for index in range(third)]
    with pytest.raises(FixedReadBoundExceeded):
        FunctionSignature.from_analysis(SimpleNamespace(return_type="int", return_type_obj=None, parameters=parameters))
    small = SimpleNamespace(return_type="int", return_type_obj=None, parameters=[{"name": "p", "tags": ["t"]}])
    signature = FunctionSignature.from_analysis(small)
    assert signature.parameters == [{"name": "p", "tags": ["t"]}]
    assert signature.parameters[0]["tags"] is not small.parameters[0]["tags"]


def test_a_serialization_scope_meters_reads_beyond_the_fixed_bound():
    """直列化の scope の中（walker の外の読み: 原因集計など）も、上限を超えた分はその作業量へ数えて読む
    （足りなければその作業量の超過: 診断は marker、判定の scope は限界）。"""

    from scripts.function_tracer_pcode.core.budget_policy import serialization_scope

    big = {f"k{index}": index for index in range(LIMIT + 50)}
    with serialization_scope(site="probe", target_parts=("probe",), terminal=False, max_bytes=1 << 20, enabled=True) as work:
        assert live_values.lookup(big, "k1") == 1
    assert work.consumed >= 50
    # 無効な scope は数えるだけ（その直列化が組み込みの容器を上限なしで辿るのと同じ）
    with serialization_scope(site="probe", target_parts=("probe",), terminal=False, enabled=False):
        assert live_values.lookup(big, "k1") == 1
    with pytest.raises(JsonBudgetExhausted):
        with serialization_scope(site="probe", target_parts=("probe",), terminal=False, max_bytes=10, enabled=True):
            live_values.lookup(big, "k1")
