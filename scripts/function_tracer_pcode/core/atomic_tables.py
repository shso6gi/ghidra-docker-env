# -*- coding: utf-8 -*-
"""Process-local tables whose operations are atomic (Issue #215 Gate B).

ここは **同期の実装だけ** を持つ。何を登録するか・何を identity とするかは知らない
（`core/structural.py` などの利用者が決める）。利用者は lock を持たず、この module の
操作 1 つが不可分であることだけに依存する。同期の方式（lock の粒度、free-threaded
build への対応など）を変えるときに触るのはこの module だけで、利用者の意味は変わらない。

契約（どの利用者にも同じ。利用者側に隠れた前提条件を置かない）:

* **linearizable**: 各操作は 1 点で起きたように見える。読んで決めて書く操作
  （`AppendOnlyBuckets.position`、`WeakKeyedTable.get_or_create`）も 1 操作。
  `statistics()` は 1 時点の snapshot（数える途中の追加を混ぜない）。
* **lock の中で利用者のコードを呼ばない**: lock の中で行う比較・hash は、この module が
  受け付ける plain な値（exact type の None / bool / int / float / str / bytes と、その
  tuple）どうしのものだけ。それ以外の key・item は `TypeError` で拒む（利用者の
  `__eq__` / `__hash__` が再入する・別の lock を取る、といった前提を作らない）。
  `get_or_create` の `make` と `statistics` の `size` は lock の外で呼ぶ。
* **弱参照の callback は表を直接変えない**: callback は GC が起きたどの thread でも、
  lock を持っている thread の中でも走り得る。消えた行は、次の操作が lock の中で外す。
* **登録は消えない**: `AppendOnlyBuckets` の位置、`SerialCounter` の値は process の中で
  再利用しない。`WeakKeyedTable` の行は、key の object が消えたときだけ消え、
  同じ `id()` を再利用した別の object に古い値が付くことは無い。
* **失敗しても表は変わらない**: 例外（`TypeError` の拒否、`make` の例外）で抜けた操作は
  何も登録しない。
* **process をまたいだ意味は持たない**: 位置や serial は登録順で決まる。
"""

from __future__ import annotations

import threading
import weakref
from typing import Any, Callable, Dict, Hashable, List, Tuple

_PLAIN_SCALARS = (type(None), bool, int, float, str, bytes)
_MISSING = object()


def require_plain(value: Any, what: str = "value") -> None:
    """lock の中で比べてよい値か（exact type の scalar と、その tuple）。違えば TypeError。"""

    stack = [value]
    while stack:
        item = stack.pop()
        kind = type(item)
        if kind is tuple:
            stack.extend(item)
        elif kind not in _PLAIN_SCALARS:
            raise TypeError(f"{what} must be a plain value, got {kind.__name__}")


class AppendOnlyBuckets:
    """bucket ごとの追記専用の列。`position` が「在ればその位置、無ければ末尾に足した位置」。"""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._buckets: Dict[Hashable, List[Any]] = {}

    def position(self, bucket_key: Hashable, item: Any) -> int:
        """`item` の bucket 内の位置（不可分: 読む → 決める → 足す）。"""

        require_plain(bucket_key, "bucket key")
        require_plain(item, "bucket item")
        with self._lock:
            bucket = self._buckets.get(bucket_key)
            if bucket is None:
                bucket = self._buckets[bucket_key] = []
            return self._position_in(bucket, item)

    def _position_in(self, bucket: List[Any], item: Any) -> int:
        """lock の中だけで呼ぶ（test はここで thread を揃えて race を再現する）。"""

        for index, existing in enumerate(bucket):
            if existing == item:
                return index
        bucket.append(item)
        return len(bucket) - 1

    def statistics(self, size: Callable[[Any], int] = lambda item: 0) -> Dict[str, int]:
        """1 時点の snapshot から数える（`size` は snapshot に対して lock の外で呼ぶ）。"""

        with self._lock:
            snapshot: Tuple[Tuple[Any, ...], ...] = tuple(tuple(bucket) for bucket in self._buckets.values())
        return {
            "buckets": len(snapshot),
            "items": sum(len(bucket) for bucket in snapshot),
            "item_bytes": sum(size(item) for bucket in snapshot for item in bucket),
            "shared_buckets": sum(1 for bucket in snapshot if len(bucket) > 1),
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


class _KeyedRef(weakref.ref):
    """行の key（`id(owner)`）を覚えた弱参照（object が消えた後でも行を引ける）。"""

    __slots__ = ("key",)

    def __new__(cls, owner: Any, callback: Callable[[Any], Any], key: int) -> "_KeyedRef":
        self = super().__new__(cls, owner, callback)
        self.key = key
        return self

    def __init__(self, owner: Any, callback: Callable[[Any], Any], key: int) -> None:
        super().__init__(owner, callback)


class WeakKeyedTable:
    """object に弱参照で結び付けた値の表（object が消えると行も消える）。

    key の object は `==` / `hash` ではなく **identity** で引く（`weakref.WeakKeyDictionary`
    は key の `__eq__` を使うので、ここでは `id()` + 弱参照の生存確認で引く）。subkey は
    plain な値（module の契約）。消えた object の ref は callback が `_dead` に積むだけで
    （`list.append` は単独で不可分）、行を外すのは次の操作が lock の中で行う
    （`weakref.WeakKeyDictionary` の pending removals と同じ方式）。
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._rows: Dict[int, Tuple[_KeyedRef, Dict[Hashable, Any]]] = {}
        self._dead: List[_KeyedRef] = []

    def _purge_dead(self) -> None:
        """lock の中だけで呼ぶ。消えた object の行を外す（同じ id の新しい行は残す）。"""

        dead = self._dead
        while dead:
            ref = dead.pop()
            row = self._rows.get(ref.key)
            if row is not None and row[0] is ref:
                del self._rows[ref.key]

    def _row(self, owner: Any, create: bool):
        """lock の中だけで呼ぶ。生きている `owner` の行（無ければ create のときだけ作る）。"""

        key = id(owner)
        row = self._rows.get(key)
        if row is not None and row[0]() is owner:
            return row
        if not create:
            return None
        # 同じ id の古い行（object は消え、callback が未処理）はここで置き換わる。古い ref の
        # 後始末は `_purge_dead` が「行の ref が同じときだけ」外すので、新しい行は残る
        row = (_KeyedRef(owner, self._dead.append, key), {})
        self._rows[key] = row
        return row

    @staticmethod
    def _require_weakrefable(owner: Any) -> None:
        try:
            weakref.ref(owner)
        except TypeError:
            raise TypeError(f"{type(owner).__name__} objects cannot be weakly referenced") from None

    def get(self, owner: Any, subkey: Hashable, default: Any = None) -> Any:
        require_plain(subkey, "subkey")
        with self._lock:
            self._purge_dead()
            row = self._row(owner, create=False)
            return default if row is None else row[1].get(subkey, default)

    def put(self, owner: Any, subkey: Hashable, value: Any) -> bool:
        """値を置く。弱参照できない object なら置かずに False（subkey の型違いは TypeError）。"""

        require_plain(subkey, "subkey")
        try:
            self._require_weakrefable(owner)
        except TypeError:
            return False
        with self._lock:
            self._purge_dead()
            self._row(owner, create=True)[1][subkey] = value
        return True

    def get_or_create(self, owner: Any, subkey: Hashable, make: Callable[[], Any]) -> Any:
        """在ればその値、無ければ `make()` の値を置いて返す（公開されるのは 1 つの値だけ）。

        `make` は lock の外で呼ぶ。並行に同じ行を作る呼び出しでは `make` が複数回呼ばれ
        得るが、置かれて全員に返るのは最初に置かれた 1 つだけ。`make` が例外なら何も
        置かない。弱参照できない object は TypeError。
        """

        require_plain(subkey, "subkey")
        self._require_weakrefable(owner)
        with self._lock:
            self._purge_dead()
            row = self._row(owner, create=False)
            if row is not None:
                existing = row[1].get(subkey, _MISSING)
                if existing is not _MISSING:
                    return existing
        value = make()
        with self._lock:
            self._purge_dead()
            values = self._row(owner, create=True)[1]
            existing = values.get(subkey, _MISSING)
            if existing is not _MISSING:
                return existing
            values[subkey] = value
            return value

    def __len__(self) -> int:
        """生きている行の数（診断・test 用）。"""

        with self._lock:
            self._purge_dead()
            return len(self._rows)
