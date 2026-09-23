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


def _opaque_leaf_text(value: Any) -> str:
    """JSON 型でない葉（snapshot の codec が別途 canonical にする値）を数えるときの代用。

    enum は値の文字列、それ以外は型名。中へは入らない（snapshot の表現に入る値は
    解析 object の `to_dict` が作った JSON 型が基本で、ここに来るのは enum などの
    小さい葉だけ）。
    """

    raw = getattr(value, "value", None) if isinstance(value, Enum) else None
    return raw if isinstance(raw, str) else type(value).__qualname__


def _opaque_leaf_bytes(value: Any) -> int:
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    return RESULT_JSON_POLICY.string_bytes(_opaque_leaf_text(value))


class SerializationWork:
    """1 回の直列化（解析 1 件分の snapshot など、1 つの出力になる単位）の作業量。

    **snapshot 側の唯一の aggregate**。その単位の表現を作る producer は、作る前か
    record 1 件を作った直後に、必ずここを通す:

    * `tree(expr)` — 式の木表現。DAG のまま大きさを見積もり（distinct node ごとに
      1 回、`core/expression.estimate_legacy_dict_bytes`）、byte と distinct node を
      足して予算と比べてから、木を作る。指数的に大きい木は作られない。
    * `value(v)` — 既に在る値（list / dict / 文字列）。写す前に、要素 1 つずつ
      書き出し器（`JsonEncodingPolicy.measure_elements`）で数える。予算を超えた
      時点で残りの要素を数えない（写さない）。
    * `record(build)` / `records(items, build)` — record 1 件分の表現を作らせ、
      書き出し器で 1 回で数える。中の木は `tree` が数え済みなので、その byte を
      引く（木の byte は書き出し器の byte と等しい）。codec が木を別の形へ写した
      record だけは、写した側を避けて辿る。列は 1 件ずつなので、超えた時点で
      残りの record を作らない。**eager に作るのは record 1 件分まで**。
    * `object_framing(mapping)` — 値を別に数えた object の括弧・区切り・key。

    単位:

    * `serialization_bytes` — その単位の表現の JSON byte 数（`RESULT_JSON_POLICY`
      で数える。木は legacy tree schema の byte 数）
    * `serialization_nodes` — その単位の木が参照する distinct な式 node の数（DAG の
      見積りの作業量）。byte 以外の走査量は byte 数で抑えられる（1 歩で 1 byte 以上）
    """

    __slots__ = (
        "site", "enabled", "_target_parts", "tree_bytes", "value_bytes", "trees",
        "records_built", "_meter", "_tree_ids", "_trees_kept", "_aliases", "_policy",
    )

    def __init__(self, *, site: str, target_parts: Tuple[Any, ...], enabled: bool = True) -> None:
        from scripts.function_tracer_pcode.core.semantic_snapshot import (
            SemanticGraphMeter,
        )

        self.site = str(site)
        #: pair の予算 scope の外（部品単体の呼び出し）では数えない（従来どおり）
        self.enabled = bool(enabled)
        self._target_parts = tuple(target_parts)
        self.tree_bytes = 0
        self.value_bytes = 0
        self.trees = 0
        self.records_built = 0
        self._meter = SemanticGraphMeter()
        #: 数え済みの木表現（id と、id の再利用を防ぐための参照）
        self._tree_ids: set = set()
        self._trees_kept: List[Any] = []
        #: 数え済みの木を別の形へ写した回数（`alias_tree`）
        self._aliases = 0
        #: この直列化の間の policy（scope は直列化より長く生きるので変わらない）
        self._policy = active_budget_policy()

    # -- 勘定 ----------------------------------------------------------------

    @property
    def total_bytes(self) -> int:
        return self.tree_bytes + self.value_bytes

    @property
    def distinct_nodes(self) -> int:
        return self._meter.distinct_nodes

    def remaining_bytes(self, policy: Optional[BudgetPolicy] = None) -> Optional[int]:
        policy = self._policy if policy is None else policy
        limit = policy.serialization_bytes
        return None if limit is None else max(0, limit - self.total_bytes)

    def target_key(self) -> Tuple[str, str]:
        from scripts.function_tracer_pcode.core.semantic_snapshot import (
            stable_atoms_digest,
        )

        return ("serialization", stable_atoms_digest(self._target_parts))

    def _evidence(self) -> Tuple[str, ...]:
        return (
            f"trees={self.trees}",
            f"tree_bytes={self.tree_bytes}",
            f"value_bytes={self.value_bytes}",
            f"records={self.records_built}",
            f"distinct_nodes={self.distinct_nodes}",
        )

    def _enforce(self) -> None:
        policy = self._policy
        for kind, observed in (
            (BudgetKind.SERIALIZATION_BYTES, self.total_bytes),
            (BudgetKind.SERIALIZATION_NODES, self.distinct_nodes),
        ):
            if policy.exceeds(kind, observed):
                # target と evidence は限界にするときだけ組み立てる
                enforce_budget(
                    kind, observed, site=self.site,
                    target_key=self.target_key(), evidence=self._evidence(),
                )

    def observe(self) -> None:
        """この直列化の最終的な量を観測値へ残す（量は単調に増えるので最後の値が最大）。"""

        if self.enabled:
            observe_budget_usage(BudgetKind.SERIALIZATION_BYTES, self.total_bytes, site=self.site)
            observe_budget_usage(BudgetKind.SERIALIZATION_NODES, self.distinct_nodes, site=self.site)

    # -- producer の入口 -------------------------------------------------------

    def tree(self, expr: Any) -> Dict[str, Any]:
        """式の木表現を、大きさを数えて予算と比べてから作る。"""

        from scripts.function_tracer_pcode.core.expression import estimate_legacy_dict_bytes

        if not self.enabled:
            return expr._to_dict(set())
        try:
            size = estimate_legacy_dict_bytes(expr, max_bytes=self.remaining_bytes())
        except (TypeError, ValueError):
            size = None
        if size is not None:
            self.trees += 1
            self.tree_bytes += int(size)
            # 数えるのは予算の分まで（超えたと分かれば残りの node は辿らない）
            self._meter.add_root(expr, max_distinct=self._policy.serialization_nodes)
            self._enforce()
        built = expr._to_dict(set())
        if size is None:
            # 見積りできない形（閉路・JSON にならない key）: 作った木をそのまま数える
            size = self._measure(built, holds_trees=True)
            self.trees += 1
            self.tree_bytes += int(size)
            self._enforce()
        self._register_tree(built)
        return built

    def value(self, value: Any) -> Any:
        """既に在る値の JSON byte 数を足す（写さない。超えたら限界）。値をそのまま返す。

        要素 1 つずつ数え、予算を超えた時点で残りの要素を数えない。
        """

        if self.enabled:
            self._count(value, holds_trees=False)
        return value

    def record(self, build: Callable[[], Any]) -> Any:
        """record 1 件分の表現を作らせ、その byte 数を足す（中の木は数え直さない）。"""

        trees_before = len(self._tree_ids)
        tree_bytes_before = self.tree_bytes
        aliases_before = self._aliases
        built = build()
        if not self.enabled:
            return built
        self.records_built += 1
        # record 1 件は 1 回で書いて数える（record の表現は既に作ってある）
        if len(self._tree_ids) == trees_before:
            self._count(built, holds_trees=False, whole=True)
        elif self._aliases == aliases_before:
            # 中の木はこの record の間に作られ、byte は数え済み（木の byte は書き出し
            # 器の byte と等しい）。record 全体を書いた byte から木の分を引く
            self._count(
                built, holds_trees=False, whole=True,
                already=self.tree_bytes - tree_bytes_before,
            )
        else:
            # 木を codec が別の形へ写した: 写した側を避けて辿る
            self._count(built, holds_trees=True)
        return built

    def _measure(
        self, value: Any, *, holds_trees: bool, already: int = 0, whole: bool = False,
    ) -> int:
        from scripts.function_tracer_pcode.core.json_encoding import (
            RESULT_JSON_POLICY,
            JsonBudgetExhausted,
        )

        remaining = self.remaining_bytes()
        try:
            if holds_trees:
                return RESULT_JSON_POLICY.measure(
                    value,
                    max_bytes=remaining,
                    exclude_ids=self._tree_ids,
                    opaque_bytes=_opaque_leaf_bytes,
                )
            limit = None if remaining is None else remaining + already
            return RESULT_JSON_POLICY.measure_elements(
                value, max_bytes=limit, opaque_text=_opaque_leaf_text, whole=whole,
            ) - already
        except JsonBudgetExhausted as exc:
            return exc.consumed_bytes - already

    def _count(
        self, value: Any, *, holds_trees: bool, already: int = 0, whole: bool = False,
    ) -> None:
        self.value_bytes += int(self._measure(
            value, holds_trees=holds_trees, already=already, whole=whole,
        ))
        self._enforce()

    def records(self, items: Iterable[Any], build: Optional[Callable[[Any], Any]] = None) -> List[Any]:
        """record の列を 1 件ずつ作る（超えた時点で残りを作らない）。

        `build` を省くと各 item の `to_dict()`。
        """

        from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

        out: List[Any] = []
        frame = RESULT_JSON_POLICY.container_frame_bytes
        self._charge_raw(frame(0))
        for item in items:
            # 要素を 1 つ足すと増える framing（区切りの長さは policy だけが知る）
            self._charge_raw(frame(len(out) + 1) - frame(len(out)))
            out.append(self.record(
                item.to_dict if build is None else (lambda item=item: build(item))
            ))
        return out

    def object_framing(self, mapping: Mapping[str, Any]) -> Mapping[str, Any]:
        """値を別に数えた object の、括弧・区切り・key の byte 数を足す（mapping を返す）。"""

        from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

        if self.enabled:
            self._charge_raw(
                RESULT_JSON_POLICY.container_frame_bytes(len(mapping))
                + sum(RESULT_JSON_POLICY.member_bytes(key, 0) for key in mapping)
            )
        return mapping

    def _charge_raw(self, size: int) -> None:
        if not self.enabled:
            return
        self.value_bytes += int(size)
        self._enforce()

    def alias_tree(self, source: Any, derived: Any) -> None:
        """数え済みの木 `source` から作った別の表現 `derived` も数え済みにする。

        snapshot の codec が木表現を canonical な tuple へ写すとき、写した側を
        もう一度数えないために使う（大きさは元の木の byte 数で数えてある）。
        """

        if self.enabled and id(source) in self._tree_ids:
            self._aliases += 1
            self._register_tree(derived)

    def _register_tree(self, built: Any) -> None:
        self._tree_ids.add(id(built))
        self._trees_kept.append(built)


_SERIALIZATION = threading.local()


def active_serialization_work() -> Optional[SerializationWork]:
    """今開いている直列化の作業量（無ければ `None`）。"""

    stack = getattr(_SERIALIZATION, "stack", None)
    return stack[-1] if stack else None


def alias_serialized_tree(source: Any, derived: Any) -> None:
    """今の作業量で数え済みの木 `source` から作った表現 `derived` を数え済みにする。"""

    work = active_serialization_work()
    if work is not None:
        work.alias_tree(source, derived)


@contextmanager
def serialization_scope(*, site: str, target_parts: Tuple[Any, ...]) -> Iterator[SerializationWork]:
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
        site=site, target_parts=target_parts, enabled=budget_scope_is_active(),
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
    "alias_serialized_tree",
]
