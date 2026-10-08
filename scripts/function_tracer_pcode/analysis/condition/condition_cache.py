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
* 並び単位の memo（`sequence_lookup` / `sequence_store`、PR-105-B）は root の memo を object の
  並びへ広げたもの（同じ object を同じ順で持つ並びだけが hit）。root 単位の memo と同じ実装
  （`_ObjectMemo`）で、root は長さ 1 の並び。
* root 単位の memo（`root_memo`）は root **object** を key にする（取り出した参照が
  同じ object を指すときだけ hit。式 object は弱参照で持ち、回収されたら entry も消える
  ので、memo が DAG を生かし続けない）。root だけに依存する値にしか使わない
  （mapping や描画文脈に依存する値は identity を key にした表へ）。

* **量は重みで抑える**。表と root memo は、件数に加えて **重み**（`cache_weight()` の
  合計。条件の identity では key が生かす graph の node 数）に上限を持ち、どちらかを
  超えたら **古い entry から** 捨てる（FIFO、決定的）。件数だけでは 1 件の大きさが
  抑えられず、root の式が回収された後も key の中の graph が上限の件数まで残る
  （長く走る pair で RSS が数 GB 増えた実測がある）。重みの定義は identity の型が持ち
  （`cache_weight()`）、それを持たない値は distinct な入れ物の数で量る（共有を 1 回だけ
  数えるので線形時間）。捨てても答えは変わらない（miss になるだけ）。
* **覚えてよい key かは key の型が決める**（`cacheable`）。`cacheable` が偽の key
  （比較できない graph を含む identity）は表が受け付けない（lookup は miss、store は
  捨てる）。consumer ごとに同じ判定を書かない。

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


#: 文字列・byte 列はこの byte 数ごとに重み 1（graph の node 1 つが値の複製で 1〜2 KB
#: を占めるのと釣り合わせる）。短いものは入れ物の要素として重み 0
_BYTES_PER_WEIGHT = 1024
_CONTAINERS = (tuple, list, set, frozenset, dict)


def _own_weight(value: Any) -> Optional[int]:
    weigh = getattr(value, "cache_weight", None)
    if callable(weigh):
        return max(1, int(weigh()))
    return None


def cache_weight(value: Any) -> int:
    """値が cache の中で生かす量の目安（1 以上）。

    * `cache_weight()` を持つ値（identity の型）はそれに従う（中は辿らない）。
    * tuple / list / set / frozenset / dict は、辿れる **distinct な** 入れ物 1 つにつき 1、
      中の `cache_weight()` を持つ値はその重み（distinct なものを 1 回）、文字列・byte 列は
      `_BYTES_PER_WEIGHT` ごとに 1 を足す。共有された部分は 1 回だけ数える（`id()` で
      訪問済みを覚える）ので、入れ子の tuple の DAG でも distinct な object の数に比例する
      時間で終わる（木として展開しない）。
    * 文字列・byte 列そのものは `1 + len // _BYTES_PER_WEIGHT`、それ以外は 1。
    """

    own = _own_weight(value)
    if own is not None:
        return own
    if isinstance(value, (str, bytes)):
        return 1 + len(value) // _BYTES_PER_WEIGHT
    if not isinstance(value, _CONTAINERS):
        return 1
    total = 0
    visited = set()
    pending = [value]
    while pending:
        current = pending.pop()
        if id(current) in visited:
            continue
        visited.add(id(current))
        own = _own_weight(current)
        if own is not None:
            total += own
            continue
        if isinstance(current, (str, bytes)):
            total += len(current) // _BYTES_PER_WEIGHT
            continue
        if not isinstance(current, _CONTAINERS):
            continue
        total += 1
        if isinstance(current, dict):
            pending.extend(current.keys())
            pending.extend(current.values())
        else:
            pending.extend(current)
    return max(1, total)


def key_is_cacheable(key: Any) -> bool:
    """表に覚えてよい key か（key の型の `cacheable`。持たない値は覚えてよい）。"""

    return bool(getattr(key, "cacheable", True))


class IdentityTable:
    """identity を key にした bounded な表（bucket → 完全比較、件数と重みで FIFO）。

    `cacheable` が偽の key は受け付けない（lookup は miss、store は何もしない）。
    """

    __slots__ = ("name", "limit", "weight_limit", "_family", "_buckets", "_entries", "_weight", "_serial")

    def __init__(self, name: str, limit: int, weight_limit: int) -> None:
        self.name = name
        #: 表の owner（名前の先頭: `simplifier` / `oracle`）。owner ごとの hit / miss の合計も数える
        self._family = name.split(".", 1)[0]
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
        if not key_is_cacheable(key):
            note(f"cache.{self.name}.uncacheable")
            return False, None
        key_hash = hash(key)
        bucket = self._buckets.get(key_hash)
        if bucket:
            serial = self._find(key, key_hash)
            if serial is not None:
                note(f"cache.{self.name}.hit")
                note(f"cache_family.{self._family}.hit")
                return True, self._entries[serial][1]
            note(f"cache.{self.name}.bucket_collision")
        note(f"cache.{self.name}.miss")
        note(f"cache_family.{self._family}.miss")
        return False, None

    def store(self, key: Any, value: Any) -> None:
        if not key_is_cacheable(key):
            return
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


class _ObjectMemo:
    """object の **並び**（順序を含む。root 1 つなら長さ 1）ごとの memo 1 種（弱参照、件数と重みで FIFO）。

    root 単位の memo（`root_memo`）と並び単位の memo（`sequence_lookup` / `sequence_store`、
    Issue #105 PR-105-B）の **唯一の実装**: 引き当て・片付け・追い出しの規則はここだけにある。
    取り出した参照が並びの **同じ object を同じ順で** 指すときだけ hit（`id()` は引くためだけに
    使い、hit は参照の同一性で確かめる）。値は並びの object だけで決まるものにしか使わない
    （identity で一致する別の object の並びには使い回さない: それは identity を key にした表の仕事）。

    要素は弱参照で持ち、どれか 1 つが回収されたら entry を消す予定を積む。callback は
    **消す予定を積むだけ** で、表そのものは触らない（callback は GC の途中、どの thread のどの
    bytecode の間でも走り得る。`put` が古い順に捨てている最中に表の大きさが変わると壊れる）。
    積んだ予定は次の `get` / `put`（store の lock の中）で片付ける。

    重みは値の重み + 要素ごとの `element_weight`（弱参照を持てない要素は memo が生かすので
    その要素の重みも足す）。
    """

    __slots__ = ("kind", "_element_weight", "_entries", "_weight", "_dead")

    def __init__(self, kind: str, *, element_weight: int) -> None:
        self.kind = kind
        self._element_weight = int(element_weight)
        #: 要素の id の並び → (要素を指す参照の並び, 値, 重み, entry の印)。挿入順（古い順）
        self._entries: Dict[Tuple[int, ...], Tuple[Tuple[Callable[[], Any], ...], Any, int, object]] = {}
        self._weight = 0
        #: 回収された要素の (key, entry の印)。callback が積み、`_reap` が片付ける
        self._dead: List[Tuple[Tuple[int, ...], Any]] = []

    def __len__(self) -> int:
        self._reap()
        return len(self._entries)

    @property
    def weight(self) -> int:
        self._reap()
        return self._weight

    def _reap(self) -> None:
        while self._dead:
            key, marker = self._dead.pop()
            self._discard(key, marker)

    def get(self, items: Tuple[Any, ...]) -> Tuple[bool, Any]:
        self._reap()
        entry = self._entries.get(tuple(id(item) for item in items))
        if (
            entry is not None
            and len(entry[0]) == len(items)
            and all(reference() is item for reference, item in zip(entry[0], items))
        ):
            return True, entry[1]
        return False, None

    def put(self, items: Tuple[Any, ...], value: Any) -> None:
        self._reap()
        key = tuple(id(item) for item in items)
        self._discard(key, None)
        marker = object()
        references = []
        weight = cache_weight(value) + self._element_weight * len(items)
        for item in items:
            reference, strong = _root_reference(item, self._dead, key, marker)
            if strong:
                weight += cache_weight(item)
            references.append(reference)
        if weight > DEFAULT_ROOT_MEMO_WEIGHT_LIMIT:
            note(f"memo.{self.kind}.too_large")
            return
        self._entries[key] = (tuple(references), value, weight, marker)
        self._weight += weight
        while len(self._entries) > DEFAULT_ROOT_MEMO_LIMIT or self._weight > DEFAULT_ROOT_MEMO_WEIGHT_LIMIT:
            self._discard(next(iter(self._entries)), None)
            note(f"memo.{self.kind}.evicted")

    def _discard(self, key: Tuple[int, ...], marker: Any) -> None:
        """entry を消す（`marker` を渡したら、その印の entry のときだけ）。"""

        entry = self._entries.get(key)
        if entry is None or (marker is not None and entry[3] is not marker):
            return
        del self._entries[key]
        self._weight -= entry[2]


#: root 1 つの memo は値の重みだけ、並びの memo は要素 1 つにつき 1 を足す（要素の参照の分）
_ROOT_ELEMENT_WEIGHT = 0
_SEQUENCE_ELEMENT_WEIGHT = 1


class ConditionCacheStore:
    """1 pair 分の cache（表と root 単位の memo と並び単位の memo）。"""

    def __init__(self) -> None:
        self._lock = threading.RLock()
        self._tables: Dict[str, IdentityTable] = {}
        self._roots: Dict[str, _ObjectMemo] = {}
        self._sequences: Dict[str, _ObjectMemo] = {}

    def sequence_lookup(self, kind: str, items: Tuple[Any, ...]) -> Tuple[bool, Any]:
        with self._lock:
            memo = self._sequences.get(kind)
            found, value = (False, None) if memo is None else memo.get(items)
        note(f"memo.{kind}.{'hit' if found else 'miss'}")
        return found, value

    def sequence_store(self, kind: str, items: Tuple[Any, ...], value: Any) -> None:
        with self._lock:
            memo = self._sequences.get(kind)
            if memo is None:
                memo = self._sequences[kind] = _ObjectMemo(kind, element_weight=_SEQUENCE_ELEMENT_WEIGHT)
            memo.put(items, value)

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

    def root_memo(
        self, kind: str, root: Any, build: Callable[[Any], Any],
        store_if: Optional[Callable[[Any], bool]] = None,
    ) -> Any:
        with self._lock:
            memo = self._roots.get(kind)
            if memo is not None:
                found, value = memo.get((root,))
                if found:
                    note(f"memo.{kind}.hit")
                    return value
        value = build(root)
        if store_if is not None and not store_if(value):
            return value
        with self._lock:
            memo = self._roots.get(kind)
            if memo is None:
                memo = self._roots[kind] = _ObjectMemo(kind, element_weight=_ROOT_ELEMENT_WEIGHT)
            memo.put((root,), value)
        return value

    def clear(self, names: Optional[Tuple[str, ...]] = None) -> None:
        """表を消す（`names` を渡せばその表だけ）。root memo は `names=None` のときだけ。"""

        with self._lock:
            if names is None:
                self._tables.clear()
                self._roots.clear()
                self._sequences.clear()
                return
            for name in names:
                table = self._tables.get(name)
                if table is not None:
                    table.clear()
                self._sequences.pop(name, None)


def _root_reference(root: Any, dead: List[Tuple[Any, Any]], key: Any, marker: Any) -> Tuple[Callable[[], Any], bool]:
    """root を指す参照（取り出すと root か `None`）と、それが強参照か。

    式 object は弱参照で持つ: memo が root を生かし続けると、pair の間ずっと本来は
    捨てられる DAG が残る。root が回収されたら entry を消す予定（key と entry の印）を積む
    （callback は回収の途中、memory が再利用される前に走るので、同じ `id()` の別の object の
    entry と取り違えない: 消すのは印が一致する entry だけ）。値は root だけで決まるので、root が
    消えた entry は誰にも引かれず、捨てても答えは変わらない。弱参照を持てない値
    （tuple の構造 key など）は強参照で持つ（件数と重みの上限で有界）。
    """

    def _collected(_reference: Any) -> None:
        dead.append((key, marker))

    try:
        return weakref.ref(root, _collected), False
    except TypeError:
        return (lambda: root), True


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


def root_memo(
    kind: str, root: Any, build: Callable[[Any], Any], store_if: Optional[Callable[[Any], bool]] = None,
) -> Any:
    """root だけに依存する値の memo（scope の外・`root is None` では毎回作る）。

    `store_if` を渡すと、それが偽を返す値は保存しない（毎回作り直す値。例: 識別不能 token を
    含む identity は memo してはいけない — `core.structural.identity_is_memoizable`）。
    """

    store = active_condition_cache()
    if store is None or root is None:
        return build(root)
    return store.root_memo(kind, root, build, store_if)


def sequence_lookup(kind: str, items: Tuple[Any, ...]) -> Tuple[bool, Any]:
    """object の並びごとの memo を引く（scope の外では常に miss）。"""

    store = active_condition_cache()
    if store is None:
        return False, None
    return store.sequence_lookup(kind, items)


def sequence_store(kind: str, items: Tuple[Any, ...], value: Any) -> None:
    """object の並びごとの memo に覚える（scope の外では捨てる）。値は並びの object だけで
    決まるものに限る（覚えてよい答えかの判断は consumer: 打ち切りを材料にした答えは渡さない）。"""

    store = active_condition_cache()
    if store is not None:
        store.sequence_store(kind, items, value)


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
    "key_is_cacheable",
    "clear_condition_caches",
    "condition_cache_scope",
    "root_memo",
    "sequence_lookup",
    "sequence_store",
]
