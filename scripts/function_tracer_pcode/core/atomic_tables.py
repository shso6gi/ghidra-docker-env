# -*- coding: utf-8 -*-
"""Process-local tables whose operations are atomic (Issue #215 Gate B).

ここは **同期の実装だけ** を持つ。何を登録するか・何を identity とするかは知らない
（`core/structural.py` などの利用者が決める）。利用者は lock を持たず、この module の
操作 1 つが不可分であることだけに依存する。同期の方式（lock の粒度、free-threaded
build への対応など）を変えるときに触るのはこの module だけで、利用者の意味は変わらない。

契約:

* 各操作は linearizable。複数の値を読んでから書く操作（`AppendOnlyBuckets.position`、
  `WeakKeyedTable.get_or_create`）も 1 つの操作として不可分。
* 登録したものは消さない（`WeakKeyedTable` は key の object が消えたときだけ消える）。
  したがって返した位置・serial は process の中で安定。
* lock の中では、呼び出し側から渡された値の `==` と、`get_or_create` の `make` だけを
  呼ぶ。`make` はこの表に再入してはいけない。
* **process をまたいだ意味は持たない**。位置や serial は登録順で決まる。
"""

from __future__ import annotations

import threading
import weakref
from typing import Any, Callable, Dict, Hashable, List


class AppendOnlyBuckets:
    """bucket ごとの追記専用の列。`position` が「在ればその位置、無ければ末尾に足した位置」。"""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._buckets: Dict[Hashable, List[Any]] = {}

    def position(self, bucket_key: Hashable, item: Any) -> int:
        """`item` の bucket 内の位置（不可分: 読む → 決める → 足す）。"""

        with self._lock:
            bucket = self._buckets.setdefault(bucket_key, [])
            return self._position_in(bucket, item)

    def _position_in(self, bucket: List[Any], item: Any) -> int:
        """lock の中だけで呼ぶ（test はここで thread を揃えて race を再現する）。"""

        for index, existing in enumerate(bucket):
            if existing == item:
                return index
        bucket.append(item)
        return len(bucket) - 1

    def statistics(self, size: Callable[[Any], int] = lambda item: 0) -> Dict[str, int]:
        with self._lock:
            buckets = list(self._buckets.values())
        return {
            "buckets": len(buckets),
            "items": sum(len(bucket) for bucket in buckets),
            "item_bytes": sum(size(item) for bucket in buckets for item in bucket),
            "shared_buckets": sum(1 for bucket in buckets if len(bucket) > 1),
        }


class SerialCounter:
    """再利用しない serial（0, 1, 2, …）。"""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._next = 0

    def next(self) -> int:
        with self._lock:
            value = self._next
            self._next += 1
            return value

    def issued(self) -> int:
        """これまでに発行した数（診断用）。"""

        with self._lock:
            return self._next


class WeakKeyedTable:
    """object に弱参照で結び付けた値の表（object が消えると行も消える）。

    key の object は `==` / `hash` ではなく **identity** で引く（`weakref.WeakKeyDictionary`
    は key の `__eq__` を使うので、ここでは `id()` + 弱参照の生存確認で引く）。
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._rows: Dict[int, Any] = {}

    def _row(self, owner: Any, create: bool):
        key = id(owner)
        row = self._rows.get(key)
        if row is not None and row[0]() is owner:
            return row
        if not create:
            return None
        rows = self._rows

        def _drop(_ref, key=key, rows=rows):
            # 別 thread の操作と競合しないよう、消すのは同じ ref の行だけ
            current = rows.get(key)
            if current is not None and current[0] is _ref:
                rows.pop(key, None)

        row = (weakref.ref(owner, _drop), {})
        rows[key] = row
        return row

    def get(self, owner: Any, subkey: Hashable, default: Any = None) -> Any:
        with self._lock:
            row = self._row(owner, create=False)
            return default if row is None else row[1].get(subkey, default)

    def put(self, owner: Any, subkey: Hashable, value: Any) -> bool:
        """値を置く。弱参照できない object なら置かずに False。"""

        try:
            with self._lock:
                self._row(owner, create=True)[1][subkey] = value
            return True
        except TypeError:
            return False

    def get_or_create(self, owner: Any, subkey: Hashable, make: Callable[[], Any]) -> Any:
        """在ればその値、無ければ `make()` の値を置いて返す（不可分）。弱参照できなければ TypeError。"""

        with self._lock:
            values = self._row(owner, create=True)[1]
            if subkey not in values:
                values[subkey] = make()
            return values[subkey]
