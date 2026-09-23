# -*- coding: utf-8 -*-
"""式の大きさの予算（Issue #22 PR-22-D）: **値** と **適用口** の owner。

責務の分け方:

```text
config/settings.py        … 既定値と環境変数の解決（入口だけが読む）
        ↓ BudgetPolicy（typed な値）
core/budget_policy.py     … 値の型・pair 単位の scope・超過 → 限界への変換・観測
        ↓ active_budget_policy() / enforce_budget()
checkpoint（呼ぶ側）       … 何を数えるか（展開の distinct node / case、描画 byte、
                            直列化 byte）。数え方はそれぞれの owner が持つ
```

ここが持たないもの: 既定値（config）、数え方（expander / `CountingWriter` /
`core/json_encoding`）、UNKNOWN / ERROR の判断（authority）。深い module は
環境変数も config も読まず、ここから **今の pair の policy** を受け取るだけなので、
既定値を変える変更は config と policy の構築だけで閉じる（計画 §4.8 M-1）。

scope の寿命は pair の実行制御（`core/errors.pair_failure_scope`）と同じで、pair
境界（`authority/lifecycle/production_boundary.py`）が開閉する。保持の仕方も台帳と
同じ module 単位の stack にしてある（contextvar にすると solver worker thread から
描画したときに policy が見えなくなり、予算が黙って無効になる）。scope の外では
**無制限**（`BudgetPolicy.unlimited()`）: pair 境界を通らない呼び出し（部品単体の
test など）の挙動は変わらない。

予算は **打ち切り** で、切り詰めて続行はしない。超えたら
`ExpressionSizeBudgetExceeded` を `raise_limitation`（記録が先、例外が後）で上げ、
stop state は `PAIR_TERMINAL_LIMITATION`（phase 再解析・conditional lane・新規
solver query をしない）。#131 の切り捨て marker（`ExpansionBudgetTruncation`）とは
別物で、あちらは「削って続けた」事実の記録。
"""

from __future__ import annotations

import threading
from contextlib import contextmanager
from dataclasses import dataclass, fields
from enum import Enum
from typing import Any, Callable, Dict, Iterable, Iterator, List, Mapping, NoReturn, Optional, Tuple

from scripts.function_tracer_pcode.core.errors import (
    ExpressionSizeBudgetExceeded,
    PairStopState,
    raise_limitation,
)
from scripts.function_tracer_pcode.core.stage_journal import journal_note


class BudgetKind(str, Enum):
    """予算の種類。値は `BudgetPolicy` の field 名と同じ（1 対 1）。

    種類を足すときは: ここに 1 member、`BudgetPolicy` に同名 field、config に既定値、
    その量を数える checkpoint で `enforce_budget(kind, ...)` を 1 回呼ぶ。超過の扱い
    （reason / stop state / evidence の書式）は共通なので分岐は増えない。
    """

    #: 1 つの MULTIEQUAL を展開した候補 case 群が持つ distinct な式 node の数
    EXPRESSION_NODES = "expression_nodes"
    #: 1 つの MULTIEQUAL を展開した候補 case の数（重複排除の前）
    EXPANSION_CASES = "expansion_cases"
    #: solver へ渡す SMT 項 1 つの byte 数（`CountingWriter` が数える）
    RENDER_BYTES = "render_bytes"
    #: 直列化 1 つ（結果 JSON 全体 / 解析 1 件分の表現全体 = 木とそれ以外）の JSON byte 数
    #: （`core/json_encoding` の policy で数える）
    SERIALIZATION_BYTES = "serialization_bytes"
    #: 直列化 1 つ（解析 1 件分の表現）の木が参照する distinct な式 node の数
    SERIALIZATION_NODES = "serialization_nodes"


def _check_limit(name: str, value: Any) -> Optional[int]:
    if value is None:
        return None
    if type(value) is not int or value < 1:
        raise ValueError(f"budget {name} must be None (unlimited) or a positive int")
    return value


@dataclass(frozen=True)
class BudgetPolicy:
    """1 pair に適用する予算の値（`None` は無制限）。

    **値だけ** を持つ。どこで数えるか・超えたらどうするかは持たないので、値を
    変えても checkpoint 側のコードは変わらない。
    """

    expression_nodes: Optional[int] = None
    expansion_cases: Optional[int] = None
    render_bytes: Optional[int] = None
    serialization_bytes: Optional[int] = None
    serialization_nodes: Optional[int] = None
    #: `serialization_bytes` のうち、authority 確定 **後** に足される field
    #: （判定・canonical reason・receipt・finalization bundle・診断）のために
    #: 出力の準備（authority 確定前）が空けておく byte 数。準備した payload が
    #: 使えるのは `serialization_bytes - envelope_headroom_bytes` まで。
    envelope_headroom_bytes: int = 0

    def __post_init__(self) -> None:
        for kind in BudgetKind:
            _check_limit(kind.value, getattr(self, kind.value))
        headroom = self.envelope_headroom_bytes
        if type(headroom) is not int or headroom < 0:
            raise ValueError("envelope headroom must be a non-negative int")
        if (
            self.serialization_bytes is not None
            and headroom >= self.serialization_bytes
        ):
            raise ValueError(
                "envelope headroom must leave room for the prepared payload "
                f"({headroom} >= serialization budget {self.serialization_bytes})"
            )

    @classmethod
    def unlimited(cls) -> "BudgetPolicy":
        return cls()

    def limit(self, kind: BudgetKind) -> Optional[int]:
        return getattr(self, BudgetKind(kind).value)

    def exceeds(self, kind: BudgetKind, observed: int) -> bool:
        limit = self.limit(kind)
        return limit is not None and int(observed) > limit

    def prepared_payload_limit(self) -> Optional[int]:
        """authority 確定前に準備する payload が使ってよい byte 数。"""

        if self.serialization_bytes is None:
            return None
        return self.serialization_bytes - self.envelope_headroom_bytes

    def to_diagnostic(self) -> Dict[str, Any]:
        return {item.name: getattr(self, item.name) for item in fields(self)}


# ---------------------------------------------------------------------------
# 観測（診断専用）
# ---------------------------------------------------------------------------


class BudgetObservations:
    """1 scope（= 1 pair）で観測した量の最大値。**診断専用**（判定に使わない）。

    既定値を実測から決める（U-1）ための値で、`site` ごとに分けて持つ。同じ予算でも
    「結果 JSON」と「式の木表現」では分布が違うので、1 つに畳むと読めなくなる。
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._maxima: Dict[Tuple[str, str], int] = {}
        self._counts: Dict[Tuple[str, str], int] = {}
        self._journaled: Dict[Tuple[str, str], int] = {}

    def observe(self, kind: BudgetKind, value: int, *, site: str) -> None:
        key = (BudgetKind(kind).value, str(site))
        value = int(value)
        crossed = False
        with self._lock:
            self._counts[key] = self._counts.get(key, 0) + 1
            if value > self._maxima.get(key, -1):
                self._maxima[key] = value
            # 最大値が 2 の冪を越えたときだけ journal にも残す（書き込みは値の
            # 桁数ぶん = 対数回）。kill された pair は結果 JSON を出さないので、
            # 膨張していった大きさを後から読めるのはここだけになる。
            bucket = value.bit_length()
            if bucket > self._journaled.get(key, 0):
                self._journaled[key] = bucket
                crossed = True
        if crossed:
            journal_note(
                "expression_budget_observed",
                {"budget": key[0], "site": key[1], "value": value},
            )

    def snapshot(self) -> Dict[str, Any]:
        with self._lock:
            rows = sorted(self._maxima)
            return {
                f"{kind}@{site}": {
                    "max": self._maxima[(kind, site)],
                    "count": self._counts[(kind, site)],
                }
                for kind, site in rows
            }


@dataclass(frozen=True)
class _BudgetScope:
    policy: BudgetPolicy
    observations: BudgetObservations


_SCOPE_LOCK = threading.Lock()
_SCOPES: List[_BudgetScope] = []
_UNLIMITED = BudgetPolicy.unlimited()


@contextmanager
def budget_policy_scope(policy: Optional[BudgetPolicy]) -> Iterator[BudgetPolicy]:
    """pair 1 件に予算を適用する scope（`None` は無制限）。

    入れ子（preflight 経由の別 pair など）は内側が勝ち、抜けると外側へ戻る。
    観測値は scope ごとに新しく持つので、次の pair へ持ち越さない。
    """

    if policy is None:
        policy = _UNLIMITED
    if type(policy) is not BudgetPolicy:
        raise TypeError("budget policy scope needs an exact BudgetPolicy")
    scope = _BudgetScope(policy, BudgetObservations())
    with _SCOPE_LOCK:
        _SCOPES.append(scope)
    try:
        yield policy
    finally:
        with _SCOPE_LOCK:
            if _SCOPES and _SCOPES[-1] is scope:
                _SCOPES.pop()
            elif scope in _SCOPES:
                del _SCOPES[_SCOPES.index(scope):]
            outermost = not _SCOPES
        if outermost:
            # pair の終わり: walker の大きさの cache が持つ値への参照を手放す
            from scripts.function_tracer_pcode.core.json_encoding import clear_size_caches

            clear_size_caches()


def _active_scope() -> Optional[_BudgetScope]:
    with _SCOPE_LOCK:
        return _SCOPES[-1] if _SCOPES else None


def active_budget_policy() -> BudgetPolicy:
    """今の pair の policy（scope の外では無制限）。"""

    scope = _active_scope()
    return _UNLIMITED if scope is None else scope.policy


def budget_scope_is_active() -> bool:
    """pair の予算 scope の中か（見積り自体に費用が掛かる checkpoint が読む）。"""

    return _active_scope() is not None


def observe_budget_usage(kind: BudgetKind, value: int, *, site: str) -> None:
    """観測値を今の scope へ残す（scope の外では捨てる）。"""

    scope = _active_scope()
    if scope is not None:
        scope.observations.observe(kind, value, site=site)


def budget_observations() -> Dict[str, Any]:
    """今の scope の観測値（scope の外では空）。"""

    scope = _active_scope()
    return {} if scope is None else scope.observations.snapshot()


# ---------------------------------------------------------------------------
# 超過 → 限界
# ---------------------------------------------------------------------------


def raise_expression_size_budget_exceeded(
    kind: BudgetKind,
    *,
    observed: int,
    limit: int,
    site: str,
    target_key: Any,
    evidence: Iterable[str] = (),
) -> NoReturn:
    """予算超過を登録済み reason の限界として上げる（**唯一の組み立て口**）。

    evidence の書式（`budget=` / `limit=` / `observed=` + checkpoint 固有の量）を
    ここ 1 箇所で決める。stop state は常に `PAIR_TERMINAL_LIMITATION`（初回で確定、
    phase recovery 無し）。
    """

    kind = BudgetKind(kind)
    raise_limitation(
        ExpressionSizeBudgetExceeded(
            f"{kind.value} {int(observed)} exceeded the budget {int(limit)}",
            site=site,
            target_key=target_key,
            evidence_refs=(
                f"budget={kind.value}",
                f"limit={int(limit)}",
                f"observed={int(observed)}",
                *tuple(str(item) for item in evidence),
            ),
        ),
        stop=PairStopState.PAIR_TERMINAL_LIMITATION,
    )


def raise_render_budget_exceeded(exc: Any, *, subject: Any) -> NoReturn:
    """描画の書き出し口（`CountingWriter`）が止めた出力を限界にする。

    予算の判定は書き出し口が済ませているので、ここは型の写し替えだけ。target は
    描いた式の **identity digest**（`core/structural.structural_identity_digest`）で、
    renderer に identity を import させないためにここで引く（renderer は描画規則の
    owner で、identity の owner ではない）。
    """

    from scripts.function_tracer_pcode.core.structural import (
        structural_identity_digest,
    )

    expression = getattr(subject, "expression", subject)
    negated = getattr(subject, "negated", None)
    target_key = ("smt_render", structural_identity_digest(expression), negated)
    raise_expression_size_budget_exceeded(
        BudgetKind.RENDER_BYTES,
        observed=exc.requested_bytes,
        limit=exc.limit_bytes,
        site=exc.site,
        target_key=target_key,
    )


# ---------------------------------------------------------------------------
# 直列化の作業量（aggregate）
# ---------------------------------------------------------------------------


class SerializationWork:
    """1 回の直列化（解析 1 件分の snapshot など、1 つの出力になる単位）の作業量。

    **snapshot 側の唯一の aggregate**。`core/json_encoding.JsonBudget` と同じ interface
    （walker が数えた byte を `charge` で受け取り、sized leaf の大きさを `tree` で作る前に
    求める）で、上限を超えたら pair terminal な限界にする（`exceeded`）。

    * 解析の表現（`FunctionReturnAnalysis.to_dict()` など）は walker が record の
      `json_items()` から 1 要素ずつ引き出し、byte をここへ足しながら作る。超えた時点で
      残りを作らない（作るのは残り予算 + 気付いた 1 要素まで）。
    * 式の木（sized leaf）は DAG のまま大きさを求め（`Expression.__json_tree_bytes__`）、
      byte と distinct node を足して予算と比べてから作る。指数的に大きい木は作られない。
    * snapshot の codec（`SnapshotFingerprintCodec.freeze(value, budget=work)`）も、
      写しながら同じ作業量へ足す。

    単位:

    * `serialization_bytes` — その単位の表現の JSON byte 数（`RESULT_JSON_POLICY`
      で数える。木は legacy tree schema の byte 数）
    * `serialization_nodes` — その単位の木が参照する distinct な式 node の数（DAG の
      見積りの作業量）。byte 以外の走査量は byte 数で抑えられる（1 歩で 1 byte 以上）
    """

    __slots__ = (
        "site", "enabled", "_target_parts", "max_bytes", "consumed", "tree_bytes",
        "trees", "_meter", "_policy", "terminal",
    )

    def __init__(
        self,
        *,
        site: str,
        target_parts: Tuple[Any, ...],
        enabled: bool = True,
        terminal: bool = True,
        max_bytes: Optional[int] = None,
    ) -> None:
        from scripts.function_tracer_pcode.core.semantic_snapshot import (
            SemanticGraphMeter,
        )

        self.site = str(site)
        #: pair の予算 scope の外（部品単体の呼び出し）では数えない（従来どおり）
        self.enabled = bool(enabled)
        self._target_parts = tuple(target_parts)
        #: この直列化の間の policy（scope は直列化より長く生きるので変わらない）
        self._policy = active_budget_policy()
        #: 超えたときに pair terminal な限界にするか（`False` は診断: `JsonBudgetExhausted`）
        self.terminal = bool(terminal)
        limit = self._policy.serialization_bytes if max_bytes is None else max_bytes
        self.max_bytes = limit if self.enabled else None
        self.consumed = 0
        self.tree_bytes = 0
        self.trees = 0
        self._meter = SemanticGraphMeter()

    # -- JsonBudget の interface -------------------------------------------------

    def remaining(self) -> Optional[int]:
        return None if self.max_bytes is None else self.max_bytes - self.consumed

    def charge(self, size: int) -> None:
        self.consumed += int(size)
        if self.max_bytes is not None and self.consumed > self.max_bytes:
            self.exceeded()

    def exceeded(self) -> None:
        if not self.terminal:
            from scripts.function_tracer_pcode.core.json_encoding import JsonBudgetExhausted

            raise JsonBudgetExhausted(consumed_bytes=self.consumed, max_bytes=self.max_bytes)
        # target と evidence は限界にするときだけ組み立てる
        enforce_budget(
            BudgetKind.SERIALIZATION_BYTES, self.consumed, site=self.site,
            target_key=self.target_key(), evidence=self._evidence(),
        )

    def tree(self, leaf: Any, *, build: bool) -> Tuple[Any, int]:
        """sized leaf（式の木）の大きさを **作る前に** 求めて足し、`build` なら作る。"""

        if not self.enabled:
            return (leaf.__json_tree__() if build else None), 0
        from scripts.function_tracer_pcode.core.json_encoding import (
            LEGACY,
            RESULT_JSON_POLICY,
        )

        size = leaf.__json_tree_bytes__(RESULT_JSON_POLICY, self.remaining())
        built = None
        if size is None:
            # 見積りできない形（閉路など、未凍結の式の中だけ）: 作ってから数える
            built = leaf.__json_tree__()
            size = RESULT_JSON_POLICY.measure(built, max_bytes=self.remaining(), mode=LEGACY)
        self.trees += 1
        self.tree_bytes += int(size)
        self.charge(size)
        # 数えるのは予算の分まで（超えたと分かれば残りの node は辿らない）
        self._meter.add_root(leaf, max_distinct=self._policy.serialization_nodes)
        if self._policy.exceeds(BudgetKind.SERIALIZATION_NODES, self.distinct_nodes):
            if not self.terminal:
                from scripts.function_tracer_pcode.core.json_encoding import JsonBudgetExhausted

                raise JsonBudgetExhausted(consumed_bytes=self.consumed, max_bytes=self.max_bytes)
            enforce_budget(
                BudgetKind.SERIALIZATION_NODES, self.distinct_nodes, site=self.site,
                target_key=self.target_key(), evidence=self._evidence(),
            )
        if build and built is None:
            built = leaf.__json_tree__()
        return (built if build else None), size

    # -- 勘定 ----------------------------------------------------------------

    @property
    def total_bytes(self) -> int:
        return self.consumed

    @property
    def distinct_nodes(self) -> int:
        return self._meter.distinct_nodes

    def remaining_bytes(self, policy: Optional[BudgetPolicy] = None) -> Optional[int]:
        policy = self._policy if policy is None else policy
        limit = policy.serialization_bytes
        return None if limit is None else max(0, limit - self.consumed)

    def target_key(self) -> Tuple[str, str]:
        from scripts.function_tracer_pcode.core.semantic_snapshot import (
            stable_atoms_digest,
        )

        return ("serialization", stable_atoms_digest(self._target_parts))

    def _evidence(self) -> Tuple[str, ...]:
        return (
            f"trees={self.trees}",
            f"tree_bytes={self.tree_bytes}",
            f"value_bytes={self.consumed - self.tree_bytes}",
            f"distinct_nodes={self.distinct_nodes}",
        )

    def observe(self) -> None:
        """この直列化の最終的な量を観測値へ残す（量は単調に増えるので最後の値が最大）。"""

        if self.enabled:
            observe_budget_usage(BudgetKind.SERIALIZATION_BYTES, self.consumed, site=self.site)
            observe_budget_usage(BudgetKind.SERIALIZATION_NODES, self.distinct_nodes, site=self.site)


_SERIALIZATION = threading.local()


def active_serialization_work() -> Optional[SerializationWork]:
    """今開いている直列化の作業量（無ければ `None`）。"""

    stack = getattr(_SERIALIZATION, "stack", None)
    return stack[-1] if stack else None


@contextmanager
def serialization_scope(
    *,
    site: str,
    target_parts: Tuple[Any, ...],
    terminal: bool = True,
    max_bytes: Optional[int] = None,
    enabled: Optional[bool] = None,
) -> Iterator[SerializationWork]:
    """直列化 1 つ分の作業量を数える scope（入れ子は外側へ合流する）。

    解析 1 件分の表現を作る側（`FunctionReturnAnalysis.to_dict` /
    `AnalysisSnapshot.from_function_analysis`）が開き、その中で作られる表現は
    すべて同じ作業量へ足される。scope の外で単独に呼ばれた `Expression.to_dict`
    は、その 1 本だけの作業量になる。thread ごとに持つ（直列化は同期処理で、
    別 thread の直列化と合算しない）。
    """

    stack = getattr(_SERIALIZATION, "stack", None)
    if stack is None:
        stack = []
        _SERIALIZATION.stack = stack
    if stack:
        yield stack[-1]
        return
    work = SerializationWork(
        site=site, target_parts=target_parts,
        enabled=budget_scope_is_active() if enabled is None else enabled,
        terminal=terminal, max_bytes=max_bytes,
    )
    stack.append(work)
    try:
        yield work
    finally:
        stack.pop()
        work.observe()


def enforce_budget(
    kind: BudgetKind,
    observed: int,
    *,
    site: str,
    target_key: Any,
    evidence: Iterable[str] = (),
) -> None:
    """観測値を残し、今の policy を超えていたら限界にする（checkpoint の入口）。"""

    observe_budget_usage(kind, observed, site=site)
    policy = active_budget_policy()
    if policy.exceeds(kind, observed):
        raise_expression_size_budget_exceeded(
            kind,
            observed=observed,
            limit=policy.limit(kind),
            site=site,
            target_key=target_key,
            evidence=evidence,
        )


__all__ = [
    "BudgetKind",
    "BudgetObservations",
    "BudgetPolicy",
    "active_budget_policy",
    "budget_observations",
    "budget_policy_scope",
    "budget_scope_is_active",
    "enforce_budget",
    "observe_budget_usage",
    "raise_expression_size_budget_exceeded",
    "raise_render_budget_exceeded",
    "serialization_scope",
    "SerializationWork",
    "active_serialization_work",
]
