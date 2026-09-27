# -*- coding: utf-8 -*-
"""条件簡約・条件 oracle の cache の **保存と寿命** の owner（Issue #105 PR-105-A）。

責務の分け方:

```text
identity の owner（何が同じか）   query_identity（SolverQueryIdentity / RewriteIdentity）,
                                   core/structural（Condition / ConditionsSignature）
cache の owner（どこに・いつまで） この module: bucket 表・root 単位の memo・pair の scope
consumer（何を覚えるか）          smt_oracle（verdict・書き換え）, simplifier（含意・矛盾）
計測                              condition_metrics（hit / miss などの数だけ）
```

* **一致の判定は key の型が持つ**。表は `hash(key)` を bucket に、`key == stored` を
  完全比較に使うだけで、identity の中身を知らない（consumer も identity の内部を
  組み立て直さない）。bucket が当たって完全比較が外れたら miss（`bucket_collision`
  として数える）で、誤った hit にはならない。
* **寿命は pair**。`condition_cache_scope()` を pair 境界
  （`authority/lifecycle/production_boundary.py`）が開閉し、scope ごとに空の store から
  始めて抜けたら捨てる。次の pair へ意味の状態を持ち越さない。scope の外（部品単体の
  呼び出し）では **何も覚えない**（lookup は常に miss、store は捨てる）: process 全体に
  生きる意味の cache は作らない。
* root 単位の memo（`root_memo`）は root **object** を key にする（取り出した参照が
  同じ object を指すときだけ hit。式 object は弱参照で持ち、回収されたら entry も消える
  ので、memo が DAG を生かし続けない）。root だけに依存する値にしか使わない
  （mapping や描画文脈に依存する値は identity を key にした表へ）。

保持の仕方は `core/budget_policy` の scope と同じ module 単位の stack（contextvar に
すると solver worker thread から見えなくなる）。
"""

from __future__ import annotations

import threading
import weakref
from contextlib import contextmanager
from typing import Any, Callable, Dict, Iterator, List, Optional, Tuple

from scripts.function_tracer_pcode.core.condition_metrics import note


#: 表 1 つの既定の上限（件数）。旧 class 属性 cache と同じく、超えたら全消去する。
DEFAULT_TABLE_LIMIT = 8192
#: root 単位の memo 1 種の上限（件数）
DEFAULT_ROOT_MEMO_LIMIT = 16384


class IdentityTable:
    """identity を key にした bounded な表（bucket → 完全比較）。"""

    __slots__ = ("name", "limit", "_buckets", "_size")

    def __init__(self, name: str, limit: int) -> None:
        self.name = name
        self.limit = int(limit)
        self._buckets: Dict[int, List[Tuple[Any, Any]]] = {}
        self._size = 0

    def __len__(self) -> int:
        return self._size

    def lookup(self, key: Any) -> Tuple[bool, Any]:
        bucket = self._buckets.get(hash(key))
        if bucket:
            for stored_key, value in bucket:
                if stored_key is key or stored_key == key:
                    note(f"cache.{self.name}.hit")
                    return True, value
            note(f"cache.{self.name}.bucket_collision")
        note(f"cache.{self.name}.miss")
        return False, None

    def store(self, key: Any, value: Any) -> None:
        if self._size >= self.limit:
            self._buckets.clear()
            self._size = 0
            note(f"cache.{self.name}.cleared")
        bucket = self._buckets.setdefault(hash(key), [])
        for index, (stored_key, _value) in enumerate(bucket):
            if stored_key is key or stored_key == key:
                bucket[index] = (key, value)
                return
        bucket.append((key, value))
        self._size += 1

    def clear(self) -> None:
        self._buckets.clear()
        self._size = 0


class ConditionCacheStore:
    """1 pair 分の cache（表と root 単位の memo）。"""

    def __init__(self) -> None:
        self._lock = threading.RLock()
        self._tables: Dict[str, IdentityTable] = {}
        self._roots: Dict[str, Dict[int, Tuple[Any, Any]]] = {}

    def table(self, name: str, limit: int = DEFAULT_TABLE_LIMIT) -> IdentityTable:
        with self._lock:
            table = self._tables.get(name)
            if table is None:
                table = IdentityTable(name, limit)
                self._tables[name] = table
            return table

    def lookup(self, name: str, key: Any, *, limit: int) -> Tuple[bool, Any]:
        with self._lock:
            return self.table(name, limit).lookup(key)

    def store(self, name: str, key: Any, value: Any, *, limit: int) -> None:
        with self._lock:
            self.table(name, limit).store(key, value)

    def root_memo(self, kind: str, root: Any, build: Callable[[Any], Any]) -> Any:
        with self._lock:
            memo = self._roots.setdefault(kind, {})
            entry = memo.get(id(root))
            if entry is not None and entry[0]() is root:
                note(f"memo.{kind}.hit")
                return entry[1]
        value = build(root)
        with self._lock:
            memo = self._roots.setdefault(kind, {})
            if len(memo) >= DEFAULT_ROOT_MEMO_LIMIT:
                memo.clear()
                note(f"memo.{kind}.cleared")
            memo[id(root)] = (_root_reference(root, memo), value)
        return value

    def clear(self, names: Optional[Tuple[str, ...]] = None) -> None:
        """表を消す（`names` を渡せばその表だけ）。root memo は `names=None` のときだけ。"""

        with self._lock:
            if names is None:
                self._tables.clear()
                self._roots.clear()
                return
            for name in names:
                table = self._tables.get(name)
                if table is not None:
                    table.clear()


def _root_reference(root: Any, memo: Dict[int, Tuple[Any, Any]]) -> Callable[[], Any]:
    """root を指す参照（取り出すと root か `None`）。

    式 object は弱参照で持つ: memo が root を生かし続けると、pair の間ずっと本来は
    捨てられる DAG が残る。root が回収されたら entry も消す（callback は回収の途中、
    memory が再利用される前に走るので、同じ `id()` の別の object と取り違えない）。
    値は root だけで決まるので、root が消えた entry は誰にも引かれず、捨てても答えは
    変わらない。弱参照を持てない値（tuple の構造 key など）は強参照で持つ（表の件数の
    上限で有界）。
    """

    key = id(root)

    def _evict(_reference: Any) -> None:
        entry = memo.get(key)
        if entry is not None and entry[0] is _reference:
            memo.pop(key, None)

    try:
        return weakref.ref(root, _evict)
    except TypeError:
        return lambda: root


_SCOPE_LOCK = threading.Lock()
_SCOPES: List[ConditionCacheStore] = []


@contextmanager
def condition_cache_scope() -> Iterator[ConditionCacheStore]:
    """1 pair（解析 1 単位）の cache の寿命。入るたびに空の store から始める。"""

    store = ConditionCacheStore()
    with _SCOPE_LOCK:
        _SCOPES.append(store)
    try:
        yield store
    finally:
        with _SCOPE_LOCK:
            if _SCOPES and _SCOPES[-1] is store:
                _SCOPES.pop()
            elif store in _SCOPES:
                del _SCOPES[_SCOPES.index(store):]


def active_condition_cache() -> Optional[ConditionCacheStore]:
    """今の pair の store（scope の外では `None` = 何も覚えない）。"""

    with _SCOPE_LOCK:
        return _SCOPES[-1] if _SCOPES else None


def cache_lookup(name: str, key: Any, *, limit: int = DEFAULT_TABLE_LIMIT) -> Tuple[bool, Any]:
    """`(見つかったか, 値)`。値が `None` でも見つかったなら `(True, None)`。"""

    store = active_condition_cache()
    if store is None:
        note("cache.unscoped")
        return False, None
    return store.lookup(name, key, limit=limit)


def cache_store(name: str, key: Any, value: Any, *, limit: int = DEFAULT_TABLE_LIMIT) -> None:
    store = active_condition_cache()
    if store is not None:
        store.store(name, key, value, limit=limit)


def root_memo(kind: str, root: Any, build: Callable[[Any], Any]) -> Any:
    """root だけに依存する値の memo（scope の外・`root is None` では毎回作る）。"""

    store = active_condition_cache()
    if store is None or root is None:
        return build(root)
    return store.root_memo(kind, root, build)


def clear_condition_caches(names: Tuple[str, ...]) -> None:
    """今の pair の store から、指定した表だけを消す（owner の `reset_caches()` 用）。"""

    store = active_condition_cache()
    if store is not None:
        store.clear(names)


__all__ = [
    "ConditionCacheStore",
    "IdentityTable",
    "active_condition_cache",
    "cache_lookup",
    "cache_store",
    "clear_condition_caches",
    "condition_cache_scope",
    "root_memo",
]
