# -*- coding: utf-8 -*-
"""`core/atomic_tables` の契約（Issue #215 Gate B）。

同期の実装だけを持つ部品なので、ここでは意味（何を登録するか）を持ち込まずに
「操作 1 つが不可分」「登録は消えない」「弱参照の行は object と共に消える」だけを確かめる。
intern（構造 identity）側の race は `test_sn3_exact_structural_key.py` が同じ hook で確かめる。
"""

from __future__ import annotations

import gc
import threading

import pytest

from scripts.function_tracer_pcode.core.atomic_tables import (
    AppendOnlyBuckets,
    SerialCounter,
    WeakKeyedTable,
)


class _Owner:
    """弱参照できる object。`__eq__` は全部一致にして、表が identity で引くことを確かめる。"""

    def __eq__(self, other):
        return True

    def __hash__(self):
        return 0


def _threads(target, count):
    threads = [threading.Thread(target=target) for _ in range(count)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(10)


def test_positions_are_stable_and_injective_per_bucket():
    table = AppendOnlyBuckets()
    assert table.position("d", b"x") == 0
    assert table.position("d", b"y") == 1
    assert table.position("d", b"x") == 0
    assert table.position("e", b"y") == 0
    assert table.statistics(size=len) == {"buckets": 2, "items": 3, "item_bytes": 3, "shared_buckets": 1}


def test_concurrent_positions_never_share_an_index():
    table = AppendOnlyBuckets()
    results = {}
    lock = threading.Lock()

    def worker():
        mine = [(item, table.position("same", item)) for item in (b"a", b"b", b"c", b"d") * 50]
        with lock:
            for item, index in mine:
                results.setdefault(item, set()).add(index)

    _threads(worker, 8)
    assert all(len(indexes) == 1 for indexes in results.values())
    assert len({next(iter(indexes)) for indexes in results.values()}) == 4
    assert table.statistics()["items"] == 4


def test_serials_are_unique_under_concurrency():
    counter = SerialCounter()
    seen = []
    lock = threading.Lock()

    def worker():
        mine = [counter.next() for _ in range(500)]
        with lock:
            seen.extend(mine)

    _threads(worker, 8)
    assert sorted(seen) == list(range(4000))
    assert counter.issued() == 4000


def test_weak_table_looks_up_by_identity_not_equality():
    table = WeakKeyedTable()
    first, second = _Owner(), _Owner()
    table.put(first, "k", 1)
    assert table.get(first, "k") == 1
    assert table.get(second, "k") is None  # `==` が真でも別 object


def test_weak_table_rows_die_with_the_object_and_ids_are_not_reused_into_them():
    table = WeakKeyedTable()
    owner = _Owner()
    table.put(owner, "k", "value")
    owner_id = id(owner)
    del owner
    gc.collect()
    assert len(table) == 0  # 消えた行は次の操作（lock の中）で外れる
    assert owner_id not in table._rows
    # 同じ id を再利用した別 object に古い値が付かない
    for _ in range(1000):
        candidate = _Owner()
        if id(candidate) == owner_id:
            assert table.get(candidate, "k") is None
            break


def test_get_or_create_is_atomic_and_rejects_objects_without_weak_references():
    table = WeakKeyedTable()
    owner = _Owner()
    counter = SerialCounter()
    values = []
    lock = threading.Lock()

    def worker():
        value = table.get_or_create(owner, "serial", counter.next)
        with lock:
            values.append(value)

    _threads(worker, 16)
    assert set(values) == {0}
    assert counter.issued() == 1
    with pytest.raises(TypeError):
        table.get_or_create(1, "serial", counter.next)
    assert table.put(1, "k", 1) is False


# --------------------------------------------------------------------------
# module の契約（利用者に隠れた前提を置かない）の反例
# --------------------------------------------------------------------------

def _run_with_timeout(target, seconds=10.0):
    """別 thread で実行し、終わらなければ（deadlock）失敗にする。"""

    errors = []

    def runner():
        try:
            target()
        except BaseException as exc:  # noqa: BLE001 - test は thread の例外を持ち帰る
            errors.append(exc)

    thread = threading.Thread(target=runner, daemon=True)
    thread.start()
    thread.join(seconds)
    assert not thread.is_alive(), "operation did not finish (deadlock under the table lock)"
    if errors:
        raise errors[0]


def test_statistics_is_one_snapshot_even_when_items_arrive_while_counting():
    table = AppendOnlyBuckets()
    for index in range(3):
        table.position("d", b"item%d" % index)
    arrived = []

    def size(item):
        # 数えている途中に別の登録が来る（lock の外で呼ばれるので再入できる）
        if not arrived:
            arrived.append(table.position("d", b"late"))
        return 1

    stats = {}
    _run_with_timeout(lambda: stats.update(table.statistics(size=size)))
    assert arrived == [3]
    assert stats["item_bytes"] == stats["items"] == 3  # 1 時点の snapshot（late を混ぜない）
    assert table.statistics(size=lambda item: 1)["items"] == 4


def test_get_or_create_calls_make_outside_the_lock_so_make_may_use_the_table():
    table = WeakKeyedTable()
    owner, other = _Owner(), _Owner()
    table.put(other, "k", "other")

    def make():
        # 再入: 同じ表の別の行を読む・作る
        assert table.get(other, "k") == "other"
        return table.get_or_create(other, "nested", lambda: "nested")

    result = []
    _run_with_timeout(lambda: result.append(table.get_or_create(owner, "k", make)))
    assert result == ["nested"]
    assert table.get(owner, "k") == "nested"


def test_racing_makes_publish_exactly_one_value():
    table = WeakKeyedTable()
    owner = _Owner()
    barrier = threading.Barrier(8)
    counter = SerialCounter()
    returned = []
    lock = threading.Lock()

    def make():
        barrier.wait(5)  # 全員が「無い」と見てから作る
        return counter.next()

    def worker():
        value = table.get_or_create(owner, "serial", make)
        with lock:
            returned.append(value)

    _threads(worker, 8)
    assert counter.issued() == 8  # make は全員が呼んだ
    assert len(set(returned)) == 1  # 公開されたのは 1 つ
    assert table.get(owner, "serial") == returned[0]


def test_a_failing_make_leaves_the_table_unchanged():
    table = WeakKeyedTable()
    owner = _Owner()

    def make():
        raise RuntimeError("boom")

    with pytest.raises(RuntimeError):
        table.get_or_create(owner, "k", make)
    assert table.get(owner, "k", "absent") == "absent"
    assert table.get_or_create(owner, "k", lambda: 7) == 7


class _LockAssertingRows(dict):
    """`_rows` の変更が必ず lock の中で起きることを記録する dict。"""

    def __init__(self, lock, violations):
        super().__init__()
        self._table_lock = lock
        self._violations = violations

    def _check(self, what):
        if not self._table_lock.locked():
            self._violations.append(what)

    def __setitem__(self, key, value):
        self._check("setitem")
        super().__setitem__(key, value)

    def __delitem__(self, key):
        self._check("delitem")
        super().__delitem__(key)

    def pop(self, *args):
        self._check("pop")
        return super().pop(*args)


def test_weak_reference_callbacks_never_change_the_table_outside_its_lock():
    table = WeakKeyedTable()
    violations = []
    table._rows = _LockAssertingRows(table._lock, violations)
    for _ in range(200):
        owner = _Owner()
        table.put(owner, "k", 1)
        del owner  # callback は lock の外（ここ）で走る
    gc.collect()
    assert len(table) == 0  # 次の操作が lock の中で外す
    assert violations == []


def test_a_collection_inside_the_locked_section_does_not_deadlock():
    table = WeakKeyedTable()

    class _Cyclic(_Owner):
        pass

    def make_garbage():
        for _ in range(50):
            owner = _Cyclic()
            owner.self_ref = owner  # 循環: 循環 GC でだけ回収される
            table.put(owner, "k", 1)
            del owner

    original = table._row

    def collecting_row(owner, create):
        gc.collect()  # lock を持ったまま callback が走る
        return original(owner, create)

    make_garbage()
    table._row = collecting_row
    keeper = _Owner()
    _run_with_timeout(lambda: table.put(keeper, "k", "kept"))
    assert table.get(keeper, "k") == "kept"
    assert len(table) == 1


def test_concurrent_get_put_and_owner_death_keep_each_live_owner_its_own_value():
    table = WeakKeyedTable()
    errors = []
    lock = threading.Lock()

    def worker(seed):
        keep = []
        for index in range(300):
            owner = _Owner()
            table.put(owner, "v", (seed, index))
            if index % 3 == 0:
                keep.append((owner, (seed, index)))
            del owner
            if index % 50 == 0:
                gc.collect()
        for owner, value in keep:
            got = table.get(owner, "v")
            if got != value:
                with lock:
                    errors.append((value, got))

    threads = [threading.Thread(target=worker, args=(seed,)) for seed in range(6)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(30)
    assert errors == []
    gc.collect()
    assert len(table) == 0


@pytest.mark.parametrize("bad", [[1], {"a": 1}, object(), (1, [2]), bytearray(b"x")])
def test_only_plain_values_are_compared_under_the_lock(bad):
    buckets = AppendOnlyBuckets()
    buckets.position("d", b"ok")
    before = buckets.statistics(size=len)
    with pytest.raises(TypeError):
        buckets.position("d", bad)
    with pytest.raises(TypeError):
        buckets.position(bad if not isinstance(bad, (list, dict, bytearray)) else (bad,), b"x")
    assert buckets.statistics(size=len) == before  # 拒んだ操作は何も登録しない
    table = WeakKeyedTable()
    owner = _Owner()
    for call in (
        lambda: table.put(owner, bad, 1),
        lambda: table.get(owner, bad),
        lambda: table.get_or_create(owner, bad, lambda: 1),
    ):
        with pytest.raises(TypeError):
            call()
    assert len(table) == 0


def test_an_item_with_a_raising_equality_never_reaches_the_lock():
    class _Raising:
        def __eq__(self, other):
            raise RuntimeError("eq")

        __hash__ = object.__hash__

    buckets = AppendOnlyBuckets()
    buckets.position("d", b"ok")
    with pytest.raises(TypeError):
        buckets.position("d", _Raising())
    assert buckets.position("d", b"next") == 1  # 表も lock も壊れていない
