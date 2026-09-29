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
