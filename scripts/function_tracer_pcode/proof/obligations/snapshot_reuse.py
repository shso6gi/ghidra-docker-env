"""pair の中の snapshot の再利用（Issue #219 PR-219-B）: **read-set witness** の owner。

`AnalysisSnapshot.from_function_analysis` の本体を、同じ read-set の解析に対して pair の中で作り直さない。
再利用の根拠・token・store・寿命・計測はこの module だけが持つ（caller・writer は何も持たない。投影と codec は
schema の owner `snapshot.py`）。

**保証**: 同じ初期状態から始めた呼び出しの列は、再利用の on / off（と main の本体）で、返す snapshot の全 field・
fingerprint・参照の保持の意味、上げる例外と予算の成功 / 失敗・種類、そして入力に対して走る code（解析の view・
record の protocol・`stable_key`・runtime ref の表現）の回数と順が同じ。

**根拠（単一の読み）**: canonical な生成経路（`snapshot.canonical_generation_path`）の呼び出しは、本体と同じ読みを
同じ順に **1 回だけ** 行う（`snapshot.read_snapshot_inputs`。本体と同じ scope・上限・観測）。違いは 1 つだけ:
意味の view の木の中の serialization-closed な検証済みの値（C-RS2: 不変で、直列化は写しから描く純粋な処理）を、
その値への identity token に置いたまま読む（view が owner の `FunctionReturnAnalysis` の定義のままで、walk の結果を
そのまま返すときだけ。それ以外の view では token を置かない: 置いた葉を view 自身の code が受け取り得る）。snapshot は読んだ値の **純粋な関数**（`snapshot.assemble_snapshot`:
token を戻し、digest を求め、`retained_form` の写しを作る）で、witness はその関数の入力そのもの（codec の写しと
`retained_form` の写し。token は値の identity）。等しい witness からは等しい snapshot が出るので、hit は純粋な部分
だけを省く。入力に対して走る code は hit / miss / on / off で変わらない（読みは毎回 1 回、hit が省くのは純粋な部分）。

**通常の本体へ回す境界**（読む前に決める。回した呼び出しは main の本体そのもの）:

* scope の外（`snapshot_reuse_scope` が無い。部品単体の呼び出し・tool）
* 別の直列化（作業量・walk）の中からの呼び出し（外側の勘定を変えない）
* canonical でない生成経路（派生の型、置き換えた `create` / 本体）: 単一の読みが再現する経路ではない

**方針**（`_ElisionPolicy`。正しさに関わらない費用の判断）: pair の最初の 16 回の読みで、token に置けた sized leaf が
半分に届かなければ、その pair の残りは token を置かず witness も作らない（memo を切ったときと同じ読みと組み立て）。

**sealing**（C-RS2 の接続）: closed かどうかは読むだけ。単一の読みの中で pending だった値（runtime ref の写しを
待つ値）は、読みの後で、**その読みが描いた ref の表現** から写す（`seal_serialization(observed=...)`。表現を作る
code を走らせない）。on / off で同じ値を同じように写す。写した値は以後、写しから描く（C-RS2 の契約: 検証済みの
値の runtime ref の表現は写した時点の表現。main は写さないので、ref の表現を作る code が外の状態を読むときだけ、
写した後の表現が main と違い得る。production の runtime ref は field だけを読む frozen dataclass）。

C-RS3〜C-RS8 は計画 v2 のとおり（寿命・失敗の原子性・透過性・入れ子・token の封じ込め・並行性）。本体の例外は
そのまま上がり、store を変えない（読みが上げれば witness も snapshot も作らない）。
"""

from __future__ import annotations

import dataclasses
import threading
import time
from types import MappingProxyType
from contextlib import contextmanager
from typing import Any, Dict, Iterator, List, Optional, Tuple

from scripts.function_tracer_pcode.core.budget_policy import (
    NO_SUBSTITUTION,
    LeafSubstitution,
    active_budget_policy,
    active_serialization_work,
    budget_scope_is_active,
)
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.json_encoding import active_walk_work, protocol_method
from scripts.function_tracer_pcode.core.semantic_freeze import NOT_OBSERVED, seal_serialization
from scripts.function_tracer_pcode.core.semantic_lifecycle import (
    serialization_closed,
    serialization_pending,
)
from scripts.function_tracer_pcode.core.stage_journal import journal_note
from scripts.function_tracer_pcode.proof.obligations.snapshot import (
    SnapshotRead,
    assemble_snapshot,
    canonical_generation_path,
    read_snapshot_inputs,
    register_witness_token_type,
    witness_fingerprint_digest,
)

#: 再利用を切る test の口（module の名前を monkeypatch で切る。DI は足さない）。切っても読みと sealing は
#: 同じ（on / off で入力に対して走る code が同じ）で、token を置かず store を引かない
_SNAPSHOT_REUSE_ENABLED = True

#: witness の形の版（形を変えたら上げる。pair をまたがないので互換は要らない）
_WITNESS_FORMAT = 3


# ---------------------------------------------------------------------------
# token
# ---------------------------------------------------------------------------


class ElidedSemanticValue:
    """単一の読みの中で、serialization-closed な検証済みの意味値の代わりに置く identity token。

    `value` への強参照を持つ（witness が生きている間 `id` は再利用されない）。比べ方は `_same` / `_hash`
    だけが決める（`value` が同じ object であること）: この型は等しさを定義しない。codec が読む protocol を
    持たず dataclass でもないので、本体の digest（`witness` の偽の codec）に入れば `TypeError`（C-RS7）。
    `snapshot.assemble_snapshot` は、登録した展開（`_token_tree`）で、置かれるはずだった木に戻す。
    """

    __slots__ = ("value", "tree")

    def __init__(self, value: Any) -> None:
        self.value = value
        #: 置かれるはずだった LEGACY の木（初めて要るときに 1 回作る。closed な値の木は純粋に決まる）
        self.tree: Any = None


def _token_tree(token: ElidedSemanticValue) -> Any:
    """token が代わりに置かれた葉の、walker が置くはずだった木（`SerializationWork.tree` の構築と同じ関数）。

    closed な値の木は、写した ref の表現と検証済みの値だけから作る（入力の code を呼ばない。C-RS2）。
    """

    if token.tree is None:
        token.tree = protocol_method(token.value, "__json_tree__")(token.value)
    return token.tree


def _token_identity(token: ElidedSemanticValue) -> int:
    """token が代わりに置かれた値の identity（token が値への強参照を持つ間は別の値と重ならない）。"""

    return id(token.value)


register_witness_token_type(ElidedSemanticValue, _token_tree, _token_identity)


class _Retained:
    """witness の中で、snapshot が写さずに参照で置く値（`retained_form` の `snapshot_id`）の印。

    比べ方だけを変える: 中の変わり得る object（不変な tuple / frozenset と scalar 以外）は同じ object で
    あることを求める。
    """

    __slots__ = ("value",)

    def __init__(self, value: Any) -> None:
        self.value = value




class _ReadHook(LeafSubstitution):
    """単一の読みの、意味の view の sized leaf への hook（`snapshot.snapshot_material` が view の間だけ渡す）。

    closed かどうかは **読むだけ**（`serialization_closed` / `serialization_pending`）。`elide` なら closed な値を
    token に置く（同じ値には同じ token）。pending な値は置き換えず（本体と同じく描く）、読みの後で写すために集める。
    """

    __slots__ = ("elide", "pending", "_tokens", "elided")

    def __init__(self, *, elide: bool) -> None:
        self.elide = elide
        self.pending: List[Any] = []
        self._tokens: Dict[int, ElidedSemanticValue] = {}
        #: token に置いた葉の、作業量が見積もった大きさの和（再利用の得の目安: `_ElisionPolicy`）。大きさを
        #: 数えない作業量では葉ごとに 1
        self.elided = 0

    def __leaf_substitute__(self, leaf: Any, size: Optional[int]) -> Any:
        # sized leaf（`__json_tree__` を持つ型）は式だけ（条件は record として walk される）
        if type(leaf) is not Expression:
            return NO_SUBSTITUTION
        if serialization_closed(leaf):
            if not self.elide:
                return NO_SUBSTITUTION
            self.elided += 1 if size is None or size < 1 else size
            token = self._tokens.get(id(leaf))
            if token is None:
                token = self._tokens[id(leaf)] = ElidedSemanticValue(leaf)
            return token
        if serialization_pending(leaf):
            self.pending.append(leaf)
        return NO_SUBSTITUTION


# ---------------------------------------------------------------------------
# witness の比べ方（snapshot の等しさと保持から導く。1 つの規則）
# ---------------------------------------------------------------------------
#
# witness は本体の投影そのもの（fingerprint の codec の写しと、`create` が置く値）。比べ方は、返す snapshot が
# 等しいこと（容器は要素を `a is b or a == b` で比べる）と、参照の保持が同じことから導く:
#
# * 型は同じ型 **そのもの**（`True` / `1`、list / tuple を畳まない）
# * 値で比べるのは、同じ値なら返す値どうしが `==` になる組み込みの型だけ（`str` / `int` / `bytes`、NaN で
#   ない `float` は表現まで: `0.0` / `-0.0` は fingerprint が違う）。NaN は同じ object だけ
# * token は包んだ値が同じ object
# * 本体の投影が新しく作る容器（tuple / mapping / frozenset）は中身で比べる
# * それ以外の object は同じ object だけ（その状態が fingerprint に効くなら、codec の写しが状態を値として持つ）
# * 参照で置かれる値（`_Retained`）の中の変わり得る容器は同じ object だけ（不変な tuple / frozenset は辿る）
#
# hash は同じ規則に合わせる（等しいなら同じ hash）。利用者の code（`__eq__` / `__hash__`）を呼ばない。

def _same(a: Any, b: Any, retained: bool = False) -> bool:
    if a is b:
        return True
    kind = type(a)
    if kind is not type(b):
        return False
    if kind is str or kind is int or kind is bytes:
        return a == b
    if kind is float:
        return a == a and float.__repr__(a) == float.__repr__(b)
    if kind is ElidedSemanticValue:
        return a.value is b.value
    if kind is _Retained:
        return _same(a.value, b.value, True)
    if kind is tuple:
        if len(a) != len(b):
            return False
        for x, y in zip(a, b):
            if not _same(x, y, retained):
                return False
        return True
    if kind is frozenset:
        return _same_set(a, b, retained)
    if retained:
        # 参照で置かれる変わり得る値・object: 同じ object だけ（上の `is`）
        return False
    if kind is list:
        if len(a) != len(b):
            return False
        for x, y in zip(a, b):
            if not _same(x, y):
                return False
        return True
    if kind is dict or kind is MappingProxyType:
        if len(a) != len(b):
            return False
        for (key_a, item_a), (key_b, item_b) in zip(a.items(), b.items()):
            if not (_same(key_a, key_b) and _same(item_a, item_b)):
                return False
        return True
    if kind is set:
        return _same_set(a, b, False)
    return False


def _same_set(a: Any, b: Any, retained: bool) -> bool:
    if len(a) != len(b):
        return False
    buckets: Dict[int, List[Any]] = {}
    for item in b:
        buckets.setdefault(_hash(item, retained), []).append(item)
    for item in a:
        candidates = buckets.get(_hash(item, retained))
        if not candidates:
            return False
        for index, candidate in enumerate(candidates):
            if _same(item, candidate, retained):
                del candidates[index]
                break
        else:
            return False
    return True


def _hash(value: Any, retained: bool = False) -> int:
    kind = type(value)
    if kind is str or kind is int or kind is bytes:
        return hash((kind.__name__, value))
    if value is None or kind is bool:
        return hash(("scalar", value is True, value is None))
    if kind is float:
        if value != value:
            return hash(("nan", id(value)))
        return hash(("float", float.__repr__(value)))
    if kind is ElidedSemanticValue:
        return hash(("token", id(value.value)))
    if kind is _Retained:
        return hash(("retained", _hash(value.value, True)))
    if kind is tuple:
        return hash(("tuple", tuple(_hash(item, retained) for item in value)))
    if kind is frozenset:
        return hash(("frozenset", sum(_hash(item, retained) for item in value) & 0xFFFFFFFFFFFFFFFF, len(value)))
    if not retained:
        if kind is list:
            return hash(("list", tuple(_hash(item) for item in value)))
        if kind is dict or kind is MappingProxyType:
            return hash((kind.__name__, tuple((_hash(k), _hash(v)) for k, v in value.items())))
        if kind is set:
            return hash(("set", sum(_hash(item) for item in value) & 0xFFFFFFFFFFFFFFFF, len(value)))
    return hash(("object", id(value)))


#: witness の hash が読む node の数の上限（幅優先: 浅い node から。比べるのは `_same` なので、hash は
#: 候補を絞るだけ。上限の外の違いは `_same` が見つける）
_WITNESS_HASH_NODES = 2048


def _witness_hash(parts: Tuple[Any, ...]) -> int:
    """`_hash` と同じ規則の、読む node の数を抑えた hash（`_same` で等しい組は同じ hash）。

    容器は型と長さ、葉は `_hash` を、幅優先の順に上限まで畳む。set / frozenset は要素の順が
    決まらないので、長さだけを畳む（中へ入らない）。
    """

    folded: List[int] = []
    queue: List[Tuple[Any, bool]] = [(parts, False)]
    index = 0
    while index < len(queue):
        value, retained = queue[index]
        index += 1
        kind = type(value)
        room = _WITNESS_HASH_NODES - len(queue)
        if kind is _Retained:
            if room > 0:
                queue.append((value.value, True))
        elif kind is tuple or (not retained and kind is list):
            folded.append(hash((kind.__name__, len(value))))
            if room > 0:
                queue.extend((item, retained) for item in value[:room])
        elif not retained and (kind is dict or kind is MappingProxyType):
            folded.append(hash((kind.__name__, len(value))))
            for key, item in value.items():
                if room < 2:
                    break
                queue.append((key, False))
                queue.append((item, False))
                room -= 2
        elif kind is frozenset or (not retained and kind is set):
            folded.append(hash((kind.__name__, len(value))))
        else:
            folded.append(_hash(value, retained))
    return hash(tuple(folded))


class _Witness:
    """store の key（hash を 1 回だけ求める。比べるのは `_same`: 利用者の code を呼ばない）。"""

    __slots__ = ("parts", "_hash")

    def __init__(self, parts: Tuple[Any, ...]) -> None:
        self.parts = parts
        self._hash = _witness_hash(parts)

    def __eq__(self, other: Any) -> bool:
        return type(other) is _Witness and other._hash == self._hash and _same(self.parts, other.parts)

    def __ne__(self, other: Any) -> bool:
        return not self.__eq__(other)

    def __hash__(self) -> int:
        return self._hash



# ---------------------------------------------------------------------------
# store / scope / 計測
# ---------------------------------------------------------------------------


class SnapshotReuse:
    """pair 1 つ分の store と計測（`snapshot_reuse_scope` が作る）。

    get / put は lock で linearize する。lock の中で比べるのは witness（組み込みの値と token）
    だけで、利用者の code を呼ばない。本体と witness は lock の外で作る。
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._entries: Dict[_Witness, Any] = {}
        self._counts: Dict[str, int] = {}
        self._seconds: Dict[str, float] = {}
        self.policy = _ElisionPolicy()

    def lookup(self, witness: _Witness) -> Any:
        with self._lock:
            return self._entries.get(witness)

    def put_if_absent(self, witness: _Witness, snapshot: Any) -> bool:
        with self._lock:
            if witness in self._entries:
                return False
            self._entries[witness] = snapshot
            return True

    def count(self, name: str, amount: int = 1) -> None:
        with self._lock:
            self._counts[name] = self._counts.get(name, 0) + amount

    def add_seconds(self, name: str, seconds: float) -> None:
        with self._lock:
            self._seconds[name] = self._seconds.get(name, 0.0) + seconds

    def metrics(self) -> Dict[str, Any]:
        with self._lock:
            return {
                "counts": dict(sorted(self._counts.items())),
                "seconds": {key: round(value, 6) for key, value in sorted(self._seconds.items())},
                "entries": len(self._entries),
            }

    def release(self) -> None:
        """entry（token が持つ値への強参照）を手放す。"""

        with self._lock:
            self._entries.clear()


class _ElisionPolicy:
    """pair の中で、token を置いて比べる（再利用する）かの方針（再利用の owner の判断。正しさに関わらない）。

    token を置いた読みが省くのは、token が代わりに置かれた値を作る分（読みと組み立て）で、token に置いた葉の
    大きさに比例する。比べる費用（witness の digest と `retained_form` の写しの比較）は、token の外の、読みが
    直列化した残りの全部（式の葉でない record・効果の要約・条件を含む）に比例する。そこで、読みの作業量が
    数えた byte の大きさ（`SnapshotRead.serialized_bytes`）のうち、token に置いた葉の大きさの割合で量る
    （式の葉の中の割合では量らない: 実 run には、葉はほぼ全部 closed でも、葉が直列化の 0.1 % しかない pair
    がある）。pair の最初の `_POLICY_READS` 回の読みで、その割合が `_POLICY_MIN_SHARE` に届かなければ、その
    pair の残りでは token を置かず、witness も作らない（読みと組み立ては同じ 1 回: memo を切ったときと同じ）。
    判断は数え上げだけで決まる（時間に依らない）。
    """

    __slots__ = ("_lock", "reads", "serialized", "elided", "elide")

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self.reads = 0
        self.serialized = 0
        self.elided = 0
        self.elide = True

    def observe(self, serialized: int, elided: int) -> bool:
        """token を置いた読みの数え上げ（直列化した byte と、token に置いた葉の byte）を足し、方針が
        「置かない」に変わったら真。"""

        with self._lock:
            if not self.elide:
                return False
            self.reads += 1
            self.serialized += serialized
            self.elided += elided
            numerator, denominator = _POLICY_MIN_SHARE
            if self.reads >= _POLICY_READS and self.elided * denominator < self.serialized * numerator:
                self.elide = False
                return True
            return False


#: 方針を決めるまでに数える、token を置いた読みの数
_POLICY_READS = 16

#: token に置いた葉の大きさが、読みが直列化した大きさに占める割合の下限（分子, 分母）。recorded corpus の
#: replay では、token が省く読みの費用は 1 MB あたり約 73〜86 ms、比べる費用は token の外の 1 MB あたり
#: 約 26〜33 ms で、損益の分かれ目は割合 0.26〜0.28（得をする variant の割合は 0.30〜0.58、実 run の
#: 損をする pair は 0.001）
_POLICY_MIN_SHARE = (1, 4)


_SCOPE_LOCK = threading.Lock()
_SCOPES: List[SnapshotReuse] = []


@contextmanager
def snapshot_reuse_scope() -> Iterator[SnapshotReuse]:
    """1 pair の store の寿命（入るたびに空の store。抜けると entry を捨てる）。

    thread をまたいで見える module の stack（`budget_policy_scope` / `condition_cache_scope` と
    同じ形）。入れ子は内側の store だけを使い、抜けると外側へ戻る。
    """

    store = SnapshotReuse()
    with _SCOPE_LOCK:
        _SCOPES.append(store)
    try:
        yield store
    finally:
        with _SCOPE_LOCK:
            # 自分の store だけを外す（別の thread が後から開いた scope の store を巻き込まない）
            for index in range(len(_SCOPES) - 1, -1, -1):
                if _SCOPES[index] is store:
                    del _SCOPES[index]
                    break
        metrics = store.metrics()
        store.release()
        if metrics["counts"]:
            # 計測は結果の JSON に入れない（on / off で値が違い、結果の大きさの予算に効くため）。
            # pair の journal（診断の sidecar）にだけ 1 行残す
            journal_note("snapshot_reuse", {"counts": metrics["counts"], "seconds": metrics["seconds"]})


def _active_store() -> Optional[SnapshotReuse]:
    with _SCOPE_LOCK:
        return _SCOPES[-1] if _SCOPES else None


def snapshot_reuse_metrics() -> Dict[str, Any]:
    """今の scope の計測（scope の外では空）。判定には使わない。

    `counts`:
    `requests`（scope の中の入れ子でない呼び出し）、`body_executions`（本体を実際に実行した回数。
    bypass・同時の重複を含む）、`hits`、`misses`、`stores`、`unstable`（前後の witness が違った・
    後の witness を作れなかった）、`bypass:<理由>`、`sealed`（写して closed になった値）、
    `seal_left_open`（写しても closed にならなかった値）。
    `seconds`: `witness`（sealing を含まない抽出と複製）、`seal`、`body`。
    """

    store = _active_store()
    return {} if store is None else store.metrics()



# ---------------------------------------------------------------------------
# 再利用の判断
# ---------------------------------------------------------------------------


def _witness_of(read: SnapshotRead) -> _Witness:
    """`assemble_snapshot` の入力と、予算の scope・policy。

    codec の写しは、snapshot に効くのが fingerprint（写しの JSON の digest）だけなので、token を値の identity の印で
    書いた JSON の digest で持つ（`witness_fingerprint_digest`）。`retained_form` の写しは型・順・object の identity
    まで効くので、そのまま `_same` で比べる。token の位置は両方に同じく現れる。
    """

    return _Witness((
        _WITNESS_FORMAT,
        budget_scope_is_active(),
        active_budget_policy().to_diagnostic(),
        witness_fingerprint_digest(read.frozen_payload),
        _Retained(read.held_id),
        read.held_fields,
        read.held_refs,
    ))


def _seal_observed(store: SnapshotReuse, pending: List[Any], read: SnapshotRead) -> None:
    """読みが描いた ref の表現から、読みの中で pending だった値を写す（表現を作る code は走らせない）。"""

    if not pending:
        return
    started = time.perf_counter()

    def observed(ref: Any) -> Any:
        return read.observed_runtime_ref(ref, NOT_OBSERVED)

    try:
        for value in pending:
            if seal_serialization(value, observed=observed):
                store.count("sealed")
            else:
                store.count("seal_left_open")
    finally:
        store.add_seconds("seal", time.perf_counter() - started)


def reuse_or_build(cls: Any, analysis: Any) -> Any:
    """`cls.from_function_analysis(analysis)` の snapshot（同じ witness の間だけ保存した snapshot を返す）。

    `AnalysisSnapshot.from_function_analysis` だけが呼ぶ。返す値と上げる例外は本体と同じ（C-RS5）。手順は
    module の docstring のとおり。
    """

    store = _active_store()
    if store is None:
        # scope の外（部品単体の呼び出し・tool）: main と同じ本体だけ
        return cls._build_from_function_analysis(analysis)
    if active_serialization_work() is not None or active_walk_work() is not None:
        # C-RS6: 別の直列化の中。外側の勘定を変えない（sealing もしない）
        store.count("bypass:nested_serialization")
        return cls._build_from_function_analysis(analysis)
    if not canonical_generation_path(cls):
        # 単一の読みが再現しない生成経路（派生の型・置き換えた本体）: 読む前に通常の本体へ
        store.count("bypass:generation_path")
        return cls._build_from_function_analysis(analysis)
    store.count("requests")
    enabled = _SNAPSHOT_REUSE_ENABLED and store.policy.elide
    if _SNAPSHOT_REUSE_ENABLED and not enabled:
        # pair の方針で token を置かない（読みと組み立ては同じ 1 回: memo を切ったときと同じ）
        store.count("bypass:elision_policy")
    hook = _ReadHook(elide=enabled)
    started = time.perf_counter()
    # 本体と同じ読み（1 回）。上げた例外はそのまま上げる（witness も snapshot も作らない）
    read = read_snapshot_inputs(analysis, hook)
    store.add_seconds("read", time.perf_counter() - started)
    if enabled and store.policy.observe(read.serialized_bytes, hook.elided):
        store.count("policy:elision_off")
    snapshot = None
    witness = None
    if enabled:
        started = time.perf_counter()
        try:
            witness = _witness_of(read)
            snapshot = store.lookup(witness)
        except RecursionError:
            # 比べる途中で再帰の深さに当たった: 判断できないので保存せずに作る（結果は同じ純粋な関数）
            store.count("bypass:witness_failed:RecursionError")
            witness = None
        store.add_seconds("witness", time.perf_counter() - started)
        store.count("hits" if snapshot is not None else "misses")
        if snapshot is not None:
            # main は呼び出しごとに新しい snapshot を返す: 保存した値を持つ新しい object を返す（`is` で比べる
            # consumer にも main と同じ）
            snapshot = dataclasses.replace(snapshot)
    if snapshot is None:
        started = time.perf_counter()
        store.count("body_executions")
        snapshot = assemble_snapshot(read, has_tokens=hook.elided > 0)
        store.add_seconds("body", time.perf_counter() - started)
        if witness is not None:
            try:
                stored = store.put_if_absent(witness, snapshot)
            except RecursionError:
                store.count("bypass:witness_failed:RecursionError")
                stored = False
            if stored:
                store.count("stores")
    _seal_observed(store, hook.pending, read)
    return snapshot


__all__ = [
    "ElidedSemanticValue",
    "SnapshotReuse",
    "reuse_or_build",
    "snapshot_reuse_metrics",
    "snapshot_reuse_scope",
]
