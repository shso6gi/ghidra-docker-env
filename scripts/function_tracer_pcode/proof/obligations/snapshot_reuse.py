"""pair の中の snapshot の再利用（Issue #219 PR-219-B）: **read-set witness** の owner。

`AnalysisSnapshot.from_function_analysis` の本体（`_build_from_function_analysis`）を、同じ
read-set の解析に対して pair の中で作り直さない。再利用の根拠・token・store・寿命・計測は
この module だけが持つ（caller・writer・schema の owner は何も持たない）。

契約（計画 v2 §4 の C-RS1〜C-RS8。C-RS2 は `core/semantic_freeze` / `core/semantic_lifecycle`）:

* **C-RS1 再利用の唯一の根拠**: 呼び出しのたびに witness を作り、保存済みの witness と等しい
  ときだけ保存済みの snapshot を返す。witness は本体と **同じ抽出**（`snapshot.snapshot_material`）
  を、serialization-closed な検証済みの意味値だけを identity token（`ElidedSemanticValue`。強参照
  を持つ）に置き換えて作り、残りは値の複製（live な容器を残さない、型と順序を保つ）にする。
  writer を列挙せず、invalidate の hook も置かない（書き換えは witness の値の差になる）。
* **sealing**（C-RS2 の接続）: closed かどうかは読むだけ（`serialization_closed`）。runtime ref の
  写しを待つ値（pending）は、抽出の外で `seal_serialization` を明示的に呼んで確定させてから
  witness を作り直す。sealing は memo の on / off に依らず、scope の中の入れ子でない呼び出しで
  同じように行う（写した後の値は写しから描くので、on だけが写すと on / off の本体が別の状態を
  読み得る）。sealing が上げた例外はそのまま上げる（値は pending のまま。本体が生の ref を
  描いても同じ code が走る）。
* **C-RS3 寿命**: store は `snapshot_reuse_scope()` の中だけ（pair 境界が開閉する）。入れ子の scope は
  自分の store を持ち、抜けると entry（token の強参照）を捨てる。scope の外は今と同じ本体だけ。
* **C-RS4 失敗の原子性**: store へ入れるのは、本体が例外なしに完成し、本体の前後の witness が
  等しいときだけ。本体の例外は store を変えずにそのまま上げる。
* **C-RS5 透過性**: on / off で同じ snapshot・同じ例外。witness は `BudgetObservations` に残さず
  （`record_observations=False`）、hit は本体の観測を増やさない。計測は `snapshot_reuse_metrics()`。
* **C-RS6 入れ子の直列化**: 別の直列化（作業量・walk）の中からの呼び出しは lookup も store も
  sealing もしない（外側の勘定を変えない）。置き換えは core の作業量の規則で terminal でなく、
  外側へ合算されない。
* **C-RS7 token の封じ込め**: token は codec にとって opaque（`stable_key` / `json_items` などを
  持たない）なので、本体の digest に入れば `TypeError`。置き換えの hook を渡すのはこの module だけ。
* **C-RS8 並行性**: store の get / put は lock で linearize する（lock の中で利用者の code を呼ばない）。
  同時の初回 build は両方が作り、残るのは 1 つ。解析の並行 writer は前提の外。

witness を作れないとき（作業量の上限・凍結できない値・閉路の深さ）は本体へ回す。凍結できない値・
walker の拒否は本体でも同じ規則で失敗するはずなので、本体が成功したら再利用の側の誤りとして
内部エラーにする（fallback に紛れさせない）。
"""

from __future__ import annotations

import threading
import time
from contextlib import contextmanager
from typing import Any, Callable, Dict, Iterator, List, Optional, Tuple

from scripts.function_tracer_pcode.core.budget_policy import (
    NO_SUBSTITUTION,
    LeafSubstitution,
    active_budget_policy,
    active_serialization_work,
    budget_scope_is_active,
    serialization_scope,
)
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.errors import InternalError, record_internal_bug
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.json_encoding import (
    JsonBudgetExhausted,
    JsonValueRejected,
    active_walk_work,
)
from scripts.function_tracer_pcode.core.live_values import (
    builtin_mapping,
    builtin_sequence,
    builtin_set,
    elements_of,
    items_of,
)
from scripts.function_tracer_pcode.core.semantic_freeze import seal_serialization
from scripts.function_tracer_pcode.core.semantic_lifecycle import (
    serialization_closed,
    serialization_pending,
)
from scripts.function_tracer_pcode.core.stage_journal import journal_note
from scripts.function_tracer_pcode.proof.obligations.snapshot import (
    WITNESS_TOKEN_MARKER,
    SnapshotFingerprintCodec,
    snapshot_material,
    snapshot_references,
    snapshot_serialization_target,
)

#: 再利用を切る test の口（module の名前を monkeypatch で切る。DI は足さない）。切っても
#: sealing は同じように行う（on / off の本体が同じ状態を読む）
_SNAPSHOT_REUSE_ENABLED = True

#: witness の抽出の作業量の観測点（`record_observations=False` なので観測値には現れない）
SNAPSHOT_WITNESS_SITE = "proof.obligations.snapshot_reuse.witness"
#: witness が予測しなかった本体の成功（再利用の側の誤り）の観測点
SNAPSHOT_REUSE_DIVERGENCE_SITE = "proof.obligations.snapshot_reuse.witness_divergence"

#: witness の形の版（形を変えたら上げる。pair をまたがないので互換は要らない）
_WITNESS_FORMAT = 1


# ---------------------------------------------------------------------------
# token
# ---------------------------------------------------------------------------


class ElidedSemanticValue:
    """witness の中で、serialization-closed な検証済みの意味値の代わりに置く identity token。

    `value` への強参照を持つ（witness が生きている間 `id` は再利用されない）。等しさは同じ
    object であることだけ。codec が読む protocol（`stable_key` / `to_key` / `json_items` /
    `__json_tree__`）を持たず dataclass でもないので、本体の digest に入れば `TypeError`（C-RS7）。
    """

    __slots__ = ("value",)

    def __init__(self, value: Any) -> None:
        self.value = value

    def __eq__(self, other: Any) -> bool:
        return type(other) is ElidedSemanticValue and other.value is self.value

    def __ne__(self, other: Any) -> bool:
        return not self.__eq__(other)

    def __hash__(self) -> int:
        return id(self.value)


#: witness の材料を写す codec だけが token をそのまま置く（`SnapshotFingerprintCodec` の `witness`）
setattr(ElidedSemanticValue, WITNESS_TOKEN_MARKER, True)


class _SameObject:
    """snapshot が参照で持つ object（`diagnostic_refs` の値など）の identity（強参照）。"""

    __slots__ = ("value",)

    def __init__(self, value: Any) -> None:
        self.value = value

    def __eq__(self, other: Any) -> bool:
        return type(other) is _SameObject and other.value is self.value

    def __ne__(self, other: Any) -> bool:
        return not self.__eq__(other)

    def __hash__(self) -> int:
        return id(self.value)


class _Tag:
    """witness の値の複製の区切り（identity で比べる印）。"""

    __slots__ = ("name",)

    def __init__(self, name: str) -> None:
        self.name = name

    def __repr__(self) -> str:
        return f"<witness:{self.name}>"


setattr(_Tag, WITNESS_TOKEN_MARKER, True)

_TRUE = _Tag("true")
_FALSE = _Tag("false")
_FLOAT = _Tag("float")
_MAPPING = _Tag("mapping")
_SEQUENCE = _Tag("sequence")
_SET = _Tag("set")
_OBJECT = _Tag("object")
_OPAQUE = _Tag("opaque")
#: 抽出の 1 回目で、写しを待つ値の代わりに置く印（その抽出の材料は witness にしない）
_PENDING = _Tag("pending")


class _LeafSubstitution(LeafSubstitution):
    """witness の抽出の sized leaf の置き換え（`serialization_scope(leaf_substitution=...)`）。

    closed かどうかは **読むだけ**（`serialization_closed` / `serialization_pending`）。写すのは
    抽出の外（`_witness`）。`collect` の回は、写しを待つ値を印に置き換えて集める。
    """

    __slots__ = ("collect", "pending")

    def __init__(self, *, collect: bool) -> None:
        self.collect = collect
        self.pending: List[Any] = []

    def __leaf_substitute__(self, leaf: Any) -> Any:
        kind = type(leaf)
        if kind is not Expression and kind is not Condition:
            return NO_SUBSTITUTION
        if serialization_closed(leaf):
            return ElidedSemanticValue(leaf)
        if self.collect and serialization_pending(leaf):
            self.pending.append(leaf)
            return _PENDING
        return NO_SUBSTITUTION


# ---------------------------------------------------------------------------
# witness
# ---------------------------------------------------------------------------


def _freeze_witness(value: Any) -> Any:
    """witness の値の複製。組み込みの型 **そのもの** ごとに区別し、順序を保つ。

    返す snapshot の field と同じか細かい同値で比べる: scalar は型ごと（`True` / `1` / `1.0` / `-0.0` を
    `==` で畳まない）、mapping は挿入順、set は要素の集合。容器の型の違い（list / tuple など）が snapshot に
    残るのは `snapshot_id` の要素だけで、そのうち変わり得る容器は identity で持つ（`snapshot_references`）。
    残りの field は `deep_freeze` が容器の型を揃える。容器でない object は snapshot が参照で持ち得るので
    identity（`_SameObject`）と、digest が読む値（codec の写し。作れなければ印）の両方。
    """

    kind = type(value)
    if kind is str or kind is int or value is None:
        return value
    if kind is bool:
        return _TRUE if value else _FALSE
    if kind is float:
        return (_FLOAT, float.__repr__(value))
    if kind is ElidedSemanticValue or value is _PENDING:
        return value
    if kind is dict:
        return (_MAPPING, tuple((_freeze_witness(key), _freeze_witness(item)) for key, item in dict.items(value)))
    if kind is tuple or kind is list:
        return (_SEQUENCE, tuple(_freeze_witness(item) for item in value))
    if kind is frozenset or kind is set:
        return (_SET, frozenset(_freeze_witness(item) for item in value))
    mapping = builtin_mapping(value)
    if mapping is not None:
        return (_MAPPING, tuple((_freeze_witness(key), _freeze_witness(item)) for key, item in items_of(mapping)))
    if builtin_sequence(value):
        return (_SEQUENCE, tuple(_freeze_witness(item) for item in elements_of(value)))
    if builtin_set(value):
        return (_SET, frozenset(_freeze_witness(item) for item in elements_of(value)))
    try:
        frozen = SnapshotFingerprintCodec._freeze_unmetered(value, True)
    except (TypeError, ValueError):
        # digest が拒む値（本体で同じ値を digest すれば同じ拒否。参照で持つだけの値なら identity で足りる）
        frozen = _OPAQUE
    # codec が値そのものを写しに置く object（mixin の enum の member: 値は class の定義）は identity で足りる
    payload = _OPAQUE if frozen is value or frozen is _OPAQUE else _freeze_witness(frozen)
    return (_OBJECT, _SameObject(value), payload)


class _Witness:
    """store の key（hash を 1 回だけ求める。比べるのは値の複製と token だけ = 利用者の code を呼ばない）。"""

    __slots__ = ("parts", "_hash")

    def __init__(self, parts: Tuple[Any, ...]) -> None:
        self.parts = parts
        self._hash = hash(parts)

    def __eq__(self, other: Any) -> bool:
        return type(other) is _Witness and other._hash == self._hash and other.parts == self.parts

    def __ne__(self, other: Any) -> bool:
        return not self.__eq__(other)

    def __hash__(self) -> int:
        return self._hash


def _extract(analysis: Any, *, collect: bool) -> Tuple[Optional[Tuple[Any, ...]], List[Any]]:
    """本体と同じ抽出を、closed な値を token に置き換えて行う（witness の部品と、写しを待つ値の列）。

    `collect` の回に写しを待つ値があれば、部品は作らずに値の列だけを返す（印を含む材料を
    witness にしない）。
    """

    policy = active_budget_policy()
    substitution = _LeafSubstitution(collect=collect)
    with serialization_scope(
        site=SNAPSHOT_WITNESS_SITE,
        target_parts=snapshot_serialization_target(analysis),
        # 上限は本体と同じ（`max_bytes` を渡さなければ今の policy の直列化の上限）。超えれば
        # `JsonBudgetExhausted`（terminal でない: 限界にしない）で、本体が判定する
        terminal=False,
        leaf_substitution=substitution,
        record_observations=False,
    ) as work:
        material = snapshot_material(analysis, work, True)
        if substitution.pending:
            return None, substitution.pending
        # 抽出の量（値の複製の前に読む: 複製の storage の読みは本体の抽出には無い）
        extracted = (work.consumed, work.distinct_nodes)
        # witness が等しければ本体の結果（返す snapshot の全 field と、予算で止まるか）が等しい、を
        # 次の材料で言う（どれも本体が読むもの）:
        # * 材料の値（型・順序まで）と、closed な値の identity（token）
        # * この抽出の作業量の量。置き換えた葉も本体と同じく数え、同じ上限で止まる
        #   （`SerializationWork.tree`）。distinct な node は DAG の共有・object の identity で決まり、
        #   見積もりの作業量も distinct な ref ごとに数えるので、byte も値だけの関数とは言えない。
        #   抽出の後の本体（`create`）は材料だけの関数なので、本体の量が等しいことはこの組で言える
        # * snapshot が写さずに参照で置く、変わり得る object の identity（`snapshot_references`）
        # * 予算の scope と policy（本体が限界になるかを決める上限）
        # 値の複製も同じ作業量の中で作る（値の storage の読みは本体と同じくこの作業量へ数える）
        parts = (
            _WITNESS_FORMAT,
            budget_scope_is_active(),
            _freeze_witness(policy.to_diagnostic()),
            _freeze_witness(tuple(material)),
            tuple(_SameObject(item) for item in snapshot_references(material)),
            extracted,
        )
    return parts, []


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
            if _SCOPES and _SCOPES[-1] is store:
                _SCOPES.pop()
            elif store in _SCOPES:
                del _SCOPES[_SCOPES.index(store):]
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


#: witness を作れない理由のうち、本体に任せればよいもの（witness の上限・Python の再帰の深さ）
_WITNESS_UNBUILDABLE = (JsonBudgetExhausted, RecursionError)
#: 本体の抽出・digest も同じ規則で失敗するはずの理由（本体が成功したら再利用の側の誤り）
_WITNESS_PREDICTED_FAILURES = (TypeError, ValueError, JsonValueRejected)


def _seal_pending(store: SnapshotReuse, pending: List[Any]) -> None:
    started = time.perf_counter()
    try:
        for value in pending:
            # 写す（ref の表現を作る code が 1 回走る）。表現を作れないのは closed にならないだけ、
            # それ以外の例外はそのまま上げる（値は pending のまま。生の ref を描く本体でも同じ code）
            if seal_serialization(value):
                store.count("sealed")
            else:
                store.count("seal_left_open")
    finally:
        store.add_seconds("seal", time.perf_counter() - started)


def _witness(store: SnapshotReuse, analysis: Any, *, complete: bool) -> Optional[_Witness]:
    """写しを待つ値を確定させ、`complete` なら witness を返す。"""

    started = time.perf_counter()
    parts, pending = _extract(analysis, collect=True)
    store.add_seconds("witness", time.perf_counter() - started)
    if pending:
        _seal_pending(store, pending)
        if not complete:
            return None
        started = time.perf_counter()
        parts, _pending = _extract(analysis, collect=False)
        store.add_seconds("witness", time.perf_counter() - started)
    if not complete:
        return None
    return _Witness(parts)


def _run_body(store: SnapshotReuse, analysis: Any, build: Callable[[Any], Any]) -> Any:
    started = time.perf_counter()
    store.count("body_executions")
    try:
        return build(analysis)
    finally:
        store.add_seconds("body", time.perf_counter() - started)


def _body_after_witness_failure(
    store: SnapshotReuse, analysis: Any, build: Callable[[Any], Any], failure: BaseException,
) -> Any:
    """witness を作れなかった呼び出しの本体。予測した失敗なのに本体が成功したら内部エラー。"""

    store.count(f"bypass:witness_failed:{type(failure).__name__}")
    snapshot = _run_body(store, analysis, build)
    if isinstance(failure, _WITNESS_PREDICTED_FAILURES):
        error = InternalError(failure, site=SNAPSHOT_REUSE_DIVERGENCE_SITE)
        record_internal_bug(error, site=SNAPSHOT_REUSE_DIVERGENCE_SITE)
        raise error
    return snapshot


def reuse_or_build(analysis: Any, build: Callable[[Any], Any]) -> Any:
    """`build(analysis)`（snapshot の本体）の結果を、同じ witness の間だけ再利用する。

    `AnalysisSnapshot.from_function_analysis` だけが呼ぶ。返す値と上げる例外は `build` と同じ
    （C-RS5）。手順は module の docstring の契約どおり。
    """

    store = _active_store()
    if store is None:
        # scope の外（部品単体の呼び出し・tool）: 今と同じ本体だけ
        return build(analysis)
    if active_serialization_work() is not None or active_walk_work() is not None:
        # C-RS6: 別の直列化の中。外側の勘定を変えない（sealing もしない）
        store.count("bypass:nested_serialization")
        return _run_body(store, analysis, build)
    store.count("requests")
    try:
        witness = _witness(store, analysis, complete=_SNAPSHOT_REUSE_ENABLED)
    except _WITNESS_UNBUILDABLE as failure:
        store.count(f"bypass:witness_failed:{type(failure).__name__}")
        return _run_body(store, analysis, build)
    except _WITNESS_PREDICTED_FAILURES as failure:
        return _body_after_witness_failure(store, analysis, build, failure)
    if witness is None:
        store.count("bypass:disabled")
        return _run_body(store, analysis, build)
    cached = store.lookup(witness)
    if cached is not None:
        store.count("hits")
        return cached
    store.count("misses")
    snapshot = _run_body(store, analysis, build)
    try:
        after = _witness(store, analysis, complete=True)
    except _WITNESS_UNBUILDABLE + _WITNESS_PREDICTED_FAILURES:
        store.count("unstable")
        return snapshot
    if after != witness:
        # 本体の間に読む値が変わった（同じ thread の書き換え）: どちらの状態の snapshot か
        # 言えないので保存しない
        store.count("unstable")
        return snapshot
    if store.put_if_absent(witness, snapshot):
        store.count("stores")
    return snapshot


__all__ = [
    "ElidedSemanticValue",
    "SNAPSHOT_WITNESS_SITE",
    "SnapshotReuse",
    "reuse_or_build",
    "snapshot_reuse_metrics",
    "snapshot_reuse_scope",
]
