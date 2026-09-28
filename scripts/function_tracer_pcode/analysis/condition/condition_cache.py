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

* **量は重みで抑える**。表と root memo は、件数に加えて **重み**（`cache_weight()` の
  合計。条件の identity では key が生かす graph の node 数）に上限を持ち、どちらかを
  超えたら **古い entry から** 捨てる（FIFO、決定的）。件数だけでは 1 件の大きさが
  抑えられず、root の式が回収された後も key の中の graph が上限の件数まで残る
  （長く走る pair で RSS が数 GB 増えた実測がある）。重みの定義は identity の型が持ち
  （`cache_weight()`）、表は中身を知らない。捨てても答えは変わらない（miss になるだけ）。

保持の仕方は `core/budget_policy` の scope と同じ module 単位の stack（contextvar に
すると solver worker thread から見えなくなる）。
"""

from __future__ import annotations

import threading
import weakref
from contextlib import contextmanager
from typing import Any, Callable, Dict, Iterator, List, Optional, Tuple

from scripts.function_tracer_pcode.core.condition_metrics import note


#: 表 1 つの既定の上限（件数）
DEFAULT_TABLE_LIMIT = 8192
#: 表 1 つが保持してよい重みの合計（条件の identity では graph の node 数）。1 node は
#: 値の複製（NodeRecord と凍結時の意味値）で 1〜2 KB を占めるので、表 1 つで高々
#: 数百 MB に収まる値にする。hit 率との釣り合いは ell / 固定 subset で測った（PR 本文）
DEFAULT_TABLE_WEIGHT_LIMIT = 50_000
#: root 単位の memo 1 種の上限（件数）
DEFAULT_ROOT_MEMO_LIMIT = 16384
#: root 単位の memo 1 種が保持してよい重みの合計
DEFAULT_ROOT_MEMO_WEIGHT_LIMIT = 100_000


def cache_weight(value: Any) -> int:
    """値が cache の中で生かす量の目安（1 以上）。

    `cache_weight()` を持つ値（identity の型）はそれに従う。tuple / list / set /
    frozenset は **1 段だけ** 見て、要素ごとに `cache_weight()` があればその値、無ければ 1 を
    足す（+1）。入れ子の container は再帰しない: 共有された tuple の DAG を木として
    たどると指数時間になるので、量を数えたい値は自分で `cache_weight()` を持つ。
    それ以外は 1。
    """

    weigh = getattr(value, "cache_weight", None)
    if callable(weigh):
        return max(1, int(weigh()))
    if isinstance(value, (tuple, list, set, frozenset)):
        total = 1
        for item in value:
            item_weigh = getattr(item, "cache_weight", None)
            total += max(1, int(item_weigh())) if callable(item_weigh) else 1
        return total
    return 1


class IdentityTable:
    """identity を key にした bounded な表（bucket → 完全比較、件数と重みで FIFO）。"""

    __slots__ = ("name", "limit", "weight_limit", "_buckets", "_entries", "_weight", "_serial")

    def __init__(self, name: str, limit: int, weight_limit: int) -> None:
        self.name = name
        self.limit = int(limit)
        self.weight_limit = int(weight_limit)
        #: hash → その bucket の entry の通し番号
        self._buckets: Dict[int, List[int]] = {}
        #: 通し番号 → (key, value, weight, hash)。挿入順（古い順）に並ぶ
        self._entries: Dict[int, Tuple[Any, Any, int, int]] = {}
        self._weight = 0
        self._serial = 0

    def __len__(self) -> int:
        return len(self._entries)

    @property
    def weight(self) -> int:
        return self._weight

    def _find(self, key: Any, key_hash: int) -> Optional[int]:
        for serial in self._buckets.get(key_hash, ()):
            stored_key = self._entries[serial][0]
            if stored_key is key or stored_key == key:
                return serial
        return None

    def lookup(self, key: Any) -> Tuple[bool, Any]:
        key_hash = hash(key)
        bucket = self._buckets.get(key_hash)
        if bucket:
            serial = self._find(key, key_hash)
            if serial is not None:
                note(f"cache.{self.name}.hit")
                return True, self._entries[serial][1]
            note(f"cache.{self.name}.bucket_collision")
        note(f"cache.{self.name}.miss")
        return False, None

    def store(self, key: Any, value: Any) -> None:
        key_hash = hash(key)
        weight = cache_weight(key) + cache_weight(value)
        serial = self._find(key, key_hash)
        if serial is not None:
            self._drop(serial)
        if weight > self.weight_limit:
            # 1 件で上限を越える値は覚えない（覚えると他の全部を追い出す）
            note(f"cache.{self.name}.too_large")
            return
        self._serial += 1
        self._entries[self._serial] = (key, value, weight, key_hash)
        self._buckets.setdefault(key_hash, []).append(self._serial)
        self._weight += weight
        while len(self._entries) > self.limit or self._weight > self.weight_limit:
            self._drop(next(iter(self._entries)))
            note(f"cache.{self.name}.evicted")

    def _drop(self, serial: int) -> None:
        _key, _value, weight, key_hash = self._entries.pop(serial)
        self._weight -= weight
        bucket = self._buckets.get(key_hash)
        if bucket is not None:
            bucket.remove(serial)
            if not bucket:
                del self._buckets[key_hash]

    def clear(self) -> None:
        self._buckets.clear()
        self._entries.clear()
        self._weight = 0


class _RootMemo:
    """root object ごとの memo 1 種（弱参照、件数と重みで FIFO）。"""

    __slots__ = ("kind", "_entries", "_weight")

    def __init__(self, kind: str) -> None:
        self.kind = kind
        #: id(root) → (root を指す参照, 値, 重み)。挿入順（古い順）
        self._entries: Dict[int, Tuple[Callable[[], Any], Any, int]] = {}
        self._weight = 0

    def __len__(self) -> int:
        return len(self._entries)

    @property
    def weight(self) -> int:
        return self._weight

    def get(self, root: Any) -> Tuple[bool, Any]:
        entry = self._entries.get(id(root))
        if entry is not None and entry[0]() is root:
            return True, entry[1]
        return False, None

    def put(self, root: Any, value: Any) -> None:
        key = id(root)
        self.discard(key, None)
        weight = cache_weight(value)
        if weight > DEFAULT_ROOT_MEMO_WEIGHT_LIMIT:
            note(f"memo.{self.kind}.too_large")
            return
        self._entries[key] = (_root_reference(root, self, key), value, weight)
        self._weight += weight
        while len(self._entries) > DEFAULT_ROOT_MEMO_LIMIT or self._weight > DEFAULT_ROOT_MEMO_WEIGHT_LIMIT:
            self.discard(next(iter(self._entries)), None)
            note(f"memo.{self.kind}.evicted")

    def discard(self, key: int, reference: Any) -> None:
        """entry を消す（`reference` を渡したら、その参照の entry のときだけ）。"""

        entry = self._entries.get(key)
        if entry is None or (reference is not None and entry[0] is not reference):
            return
        del self._entries[key]
        self._weight -= entry[2]


class ConditionCacheStore:
    """1 pair 分の cache（表と root 単位の memo）。"""

    def __init__(self) -> None:
        self._lock = threading.RLock()
        self._tables: Dict[str, IdentityTable] = {}
        self._roots: Dict[str, _RootMemo] = {}

    def table(self, name: str, limit: int = DEFAULT_TABLE_LIMIT) -> IdentityTable:
        with self._lock:
            table = self._tables.get(name)
            if table is None:
                table = IdentityTable(name, limit, DEFAULT_TABLE_WEIGHT_LIMIT)
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
            memo = self._roots.get(kind)
            if memo is not None:
                found, value = memo.get(root)
                if found:
                    note(f"memo.{kind}.hit")
                    return value
        value = build(root)
        with self._lock:
            memo = self._roots.get(kind)
            if memo is None:
                memo = self._roots[kind] = _RootMemo(kind)
            memo.put(root, value)
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


def _root_reference(root: Any, memo: "_RootMemo", key: int) -> Callable[[], Any]:
    """root を指す参照（取り出すと root か `None`）。

    式 object は弱参照で持つ: memo が root を生かし続けると、pair の間ずっと本来は
    捨てられる DAG が残る。root が回収されたら entry も消す（callback は回収の途中、
    memory が再利用される前に走るので、同じ `id()` の別の object と取り違えない）。
    値は root だけで決まるので、root が消えた entry は誰にも引かれず、捨てても答えは
    変わらない。弱参照を持てない値（tuple の構造 key など）は強参照で持つ（件数と重みの
    上限で有界）。
    """

    def _evict(reference: Any) -> None:
        memo.discard(key, reference)

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
    "DEFAULT_ROOT_MEMO_LIMIT",
    "DEFAULT_ROOT_MEMO_WEIGHT_LIMIT",
    "DEFAULT_TABLE_LIMIT",
    "DEFAULT_TABLE_WEIGHT_LIMIT",
    "ConditionCacheStore",
    "IdentityTable",
    "active_condition_cache",
    "cache_lookup",
    "cache_weight",
    "cache_store",
    "clear_condition_caches",
    "condition_cache_scope",
    "root_memo",
]
