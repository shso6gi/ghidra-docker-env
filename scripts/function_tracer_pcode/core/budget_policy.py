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

Issue #105 PR-105-B: **fallback の予算**（`FallbackBudgetKind`: 条件簡約の DPLL の決定回数・
条件 oracle の query 数）は別の型で、超えても限界にならない（その問いに答えないだけ）。ここが
持つのは値（`BudgetPolicy` の field）と、上限との比較（`FallbackBudgetMeter.take()`、唯一の
実装）と、pair あたりの消費の寿命（`pair_fallback_meter()`: 予算の scope と同じ寿命）だけ。
何を 1 単位と数えるか・尽きたら何を返すか・記録（`condition_metrics.budget_event`）は
数える側（`analysis/condition/`）が持つ。
"""

from __future__ import annotations

import threading
from contextlib import contextmanager
from dataclasses import dataclass, field, fields
from enum import Enum
from typing import Any, Callable, Dict, Iterable, Iterator, List, Mapping, NoReturn, Optional, Tuple

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.errors import (
    ExpressionSizeBudgetExceeded,
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


class FallbackBudgetKind(str, Enum):
    """超えたら **その問いに答えない方向へ fallback する** 予算（Issue #105 PR-105-B）。

    `BudgetKind`（超えたら pair terminal な限界）とは別の型にしてある: fallback の予算は
    限界にも UNKNOWN の reason にもならず、`enforce_budget` へは渡せない（`BudgetKind(...)`
    が値を拒む）。数える単位・いつ数えるか・尽きたら何を返すかは数える側
    （`analysis/condition/`）の責務で、ここは値と上限との比較（`FallbackBudgetMeter`）だけを持つ。
    値は `BudgetPolicy` の field 名と同じ（1 対 1）。
    """

    #: CNF の DPLL（`simplifier_cnf._clauses_satisfiability`）の決定（分岐）の数。最上位の
    #: 充足可能性判定 1 回あたり（再帰の枝で共有し、枝ごとに戻さない）
    DPLL_DECISIONS = "dpll_decisions"
    #: 条件 oracle（`ConditionSMTOracle.conjunction_is_unsat`）が solver へ実際に発行した
    #: query の数。pair あたり（cache hit は数えない）
    ORACLE_QUERIES = "oracle_queries"


def _kind_value(kind: Any) -> str:
    if isinstance(kind, FallbackBudgetKind):
        return kind.value
    return BudgetKind(kind).value


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
    #: （判定・canonical reason・receipt・診断）のために出力の準備（authority 確定前）
    #: が空けておく byte 数。準備した payload が使えるのは
    #: `serialization_bytes - envelope_headroom_bytes` まで。値は出力 schema から導く
    #: 下限以上でなければならない（`checker/output_schema.validate_envelope_headroom`）。
    #: finalization bundle は最終 JSON の予算の中で、headroom の残りに収まるかを出力時に
    #: 確かめる（大きさの上限は authority の event stream の契約 #110 が無いと導けない）。
    envelope_headroom_bytes: int = 0
    #: fallback の予算（`FallbackBudgetKind`。`None` は無制限）
    dpll_decisions: Optional[int] = None
    oracle_queries: Optional[int] = None

    def __post_init__(self) -> None:
        for kind in (*BudgetKind, *FallbackBudgetKind):
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

    def limit(self, kind: Any) -> Optional[int]:
        """`BudgetKind` か `FallbackBudgetKind` の上限（`None` は無制限）。"""

        return getattr(self, _kind_value(kind))

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


# ---------------------------------------------------------------------------
# fallback の予算の消費（Issue #105 PR-105-B）
# ---------------------------------------------------------------------------


class FallbackBudgetMeter:
    """fallback の予算 1 つ分の消費（**上限との比較の唯一の実装**）。

    `take()` は 1 単位を使ってよければ数えて `True`、上限まで使い切っていれば数えずに
    `False` を返す（上限 `limit` 単位までは使える。`None` は無制限で、数えるだけ）。
    何を 1 単位と数えるか・`False` のときに何を返すかは持たない（呼ぶ側の責務）。
    """

    __slots__ = ("kind", "limit", "consumed", "_lock")

    def __init__(self, kind: FallbackBudgetKind, limit: Optional[int]) -> None:
        self.kind = FallbackBudgetKind(kind)
        self.limit = _check_limit(self.kind.value, limit)
        self.consumed = 0
        self._lock = threading.Lock()

    @classmethod
    def for_active_policy(cls, kind: FallbackBudgetKind) -> "FallbackBudgetMeter":
        """今の pair の policy の上限で、新しい消費を数え始める（1 回の問い合わせの予算）。"""

        return cls(kind, active_budget_policy().limit(FallbackBudgetKind(kind)))

    def take(self, amount: int = 1) -> bool:
        with self._lock:
            if self.limit is not None and self.consumed + amount > self.limit:
                return False
            self.consumed += amount
            return True

    @property
    def exhausted(self) -> bool:
        with self._lock:
            return self.limit is not None and self.consumed >= self.limit


@dataclass(frozen=True)
class _BudgetScope:
    policy: BudgetPolicy
    observations: BudgetObservations
    #: pair あたりの fallback の予算の消費（種類ごとに 1 つ、最初に使うときに作る）
    pair_meters: Dict[FallbackBudgetKind, FallbackBudgetMeter] = field(default_factory=dict)
    pair_meters_lock: Any = field(default_factory=threading.Lock)


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
        # 観測値は owner の API で基底型の整数にしてから渡す（`observe` の `int()` と同じ値）
        scope.observations.observe(kind, live_values.as_int(value), site=site)


def pair_fallback_meter(kind: FallbackBudgetKind) -> FallbackBudgetMeter:
    """今の pair の fallback の予算の消費（pair の scope に 1 つ。次の pair へ持ち越さない）。

    scope の外（pair 境界を通らない部品単体の呼び出し）では、その場限りの無制限の消費を
    返す（数えても残らない: 従来どおり制限しない）。
    """

    kind = FallbackBudgetKind(kind)
    scope = _active_scope()
    if scope is None:
        return FallbackBudgetMeter(kind, None)
    with scope.pair_meters_lock:
        meter = scope.pair_meters.get(kind)
        if meter is None:
            meter = scope.pair_meters[kind] = FallbackBudgetMeter(kind, scope.policy.limit(kind))
        return meter


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
    ここ 1 箇所で決める。evidence は cause の identity に入るので、走査の履歴（どこまで辿ってから
    止めたか・cache の当たり方）で変わる途中の量を入れない。stop state は軸 C（`core/errors`）の
    限界の既定 `PAIR_TERMINAL_LIMITATION`（初回で確定、phase recovery 無し。ここでは選ばない）。
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
    )


#: 出力 schema の上限（行数・byte）の超過の evidence の印（`BudgetPolicy` の予算の値ではない）
OUTPUT_SCHEMA_BOUND = "output_schema"


def raise_output_schema_exceeded(
    *,
    field_key: str,
    unit: str,
    observed: int,
    limit: int,
    site: str,
    target_key: Any,
) -> NoReturn:
    """判定の前に分かる出力の field（B）が出力 schema の上限を超えたことを、式の大きさの予算と同じ
    reason の限界として上げる（**唯一の組み立て口** の 1 つ）。

    上限の owner は `checker/output_schema`（行数は authority の event の契約 #110 から、byte は行の schema
    から導く）で、`BudgetPolicy` の予算ではない: evidence の `bound=` はその owner を、`unit=` は
    行数（`rows`）か byte（`bytes`）かを示す（予算の値の超過と読み違えない）。
    """

    raise_limitation(
        ExpressionSizeBudgetExceeded(
            f"output schema bound of {field_key} {unit} {int(observed)} exceeded {int(limit)}",
            site=site,
            target_key=target_key,
            evidence_refs=(
                f"bound={OUTPUT_SCHEMA_BOUND}",
                f"field={field_key}",
                f"unit={unit}",
                f"limit={int(limit)}",
                f"observed={int(observed)}",
            ),
        ),
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
        "site", "enabled", "_target_parts", "max_bytes", "consumed", "_meter", "_policy", "terminal", "runtime_ref_memo", "parent",
        "_substitutions",
    )

    def __init__(
        self,
        *,
        site: str,
        target_parts: Tuple[Any, ...],
        enabled: bool = True,
        terminal: bool = True,
        max_bytes: Optional[int] = None,
        parent: Optional["SerializationWork"] = None,
    ) -> None:
        from scripts.function_tracer_pcode.core.json_encoding import active_walk_work
        from scripts.function_tracer_pcode.core.semantic_snapshot import (
            SemanticGraphMeter,
        )

        if active_walk_work() is not None:
            # walk の中（converter・reducer・`json_items`）で新しい作業量を作らない（`JsonBudget` と
            # 同じ規則。その仕事は walk の作業量へ数える: owner は 1 つ）
            raise TypeError("a serialization scope cannot start inside a walk; count into the walk's work instead")
        #: 入れ子の terminal な scope は外側の作業量へも足す（外側の上限も効く）
        self.parent = parent
        #: sized leaf を作る前に呼ぶ置き換え（`substituting_leaves` の間だけ。`NO_SUBSTITUTION` 以外を返せば、
        #: その値を葉として置く）。何を置き換えるかは渡す側が決める（ここは置き換えの仕組みだけを持つ）。
        #: thread ごとの stack: 効かせた thread の、その時点で一番内側の置き換えだけが効く（別の thread・抜けた後の
        #: walk には効かない。入れ子は内側が効き、抜けると外側へ戻る）
        self._substitutions: Dict[int, List["LeafSubstitution"]] = {}

        self.site = str(site)
        #: この直列化 1 回の間だけの、式の木の中の runtime ref の LEGACY 表現の memo
        #: （`Expression._serialize_runtime_ref`）。共有 DAG を木に展開すると同じ ref が
        #: 何十回も現れる。直列化の間は解析を書き換えないので、同じ object は同じ表現。
        #: 大きさは木の見積りが出現ごとに数え済み。値への参照を持つので id は再利用されない。
        self.runtime_ref_memo: Dict[int, Tuple[Any, Any]] = {}
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
        self._meter = SemanticGraphMeter()

    # -- JsonBudget の interface -------------------------------------------------

    def remaining(self) -> Optional[int]:
        return None if self.max_bytes is None else self.max_bytes - self.consumed

    def charge(self, size: int) -> None:
        # 数える量は基底型の整数（`int(size)` と同じ値。上書きした `__int__` を呼ばない）
        size = size if type(size) is int else live_values.as_int(size)
        self.consumed += size
        if self.max_bytes is not None and self.consumed > self.max_bytes:
            self.exceeded()
        if self.parent is not None:
            self.parent.charge(size)

    def exceeded(self) -> None:
        # walker が呼ぶのは超えたときだけ（作業量が先に尽きたときを含む）: 超えた事実は上限 + 1
        # 以上として扱う（terminal なら登録した限界になり、生の例外で pair を抜けない）
        limit = self.max_bytes
        if limit is None and self.terminal:
            limit = active_budget_policy().limit(BudgetKind.SERIALIZATION_BYTES)
        # 超えた量は上限 + 1（どこまで辿ってから止めたか・cache の当たり方に依らない値。限界の
        # evidence は cause の identity に入るので、走査の履歴で変えない）
        observed = self.consumed if limit is None else limit + 1
        if not self.terminal:
            from scripts.function_tracer_pcode.core.json_encoding import JsonBudgetExhausted

            raise JsonBudgetExhausted(consumed_bytes=observed, max_bytes=self.max_bytes)
        # target と evidence は限界にするときだけ組み立てる。比べる上限はこの作業量の上限（今の
        # policy の上限ではない: 入れ子の scope の policy が大きくても、この作業量で止める）
        enforce_budget(
            BudgetKind.SERIALIZATION_BYTES, observed, site=self.site,
            target_key=self.target_key(), limit=limit,
        )

    def tree(self, leaf: Any, *, build: bool, substitutable: bool = False) -> Tuple[Any, int]:
        """sized leaf（式の木）の大きさを **作る前に** 求めて足し、`build` なら作る。

        `substitutable` は、作った葉を受け取るのが置き換えを頼んだ呼ぶ側だけのとき（walk の外から
        始めた LEGACY の構築が置く葉。`core/json_encoding._Walk`）。そのときだけ `leaf_substitution`
        に尋ねる: walk の中の code が読む値・`Expression.to_dict()` の返り値は置き換えない。尋ねるのは
        見積もりの後で、見積もった大きさ（数えない作業量では `None`）を渡す（見積もりは置き換えの有無に
        依らず走るので、尋ねるために走る code は無い）。

        **置き換えが変えるのは置く値だけで、数える量は変えない**: 置き換えた葉も、置き換えない葉と
        同じく大きさを見積もって足し、distinct な node を数え、上限と比べる（作らないだけ）。この作業量の
        量（`consumed` / `distinct_nodes`）と、超過で止まるかは、置き換えの有無に依らない。
        """

        from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, protocol_method

        # 置き換えは package の `LeafSubstitution` の protocol（型の関数を直接呼ぶ）
        substitution = self.active_leaf_substitution() if substitutable else None
        # sized leaf の protocol は package の型の関数を直接呼ぶ（instance の属性を引かない）
        if not self.enabled:
            substitute = NO_SUBSTITUTION
            if substitution is not None:
                substitute = protocol_method(substitution, "__leaf_substitute__")(substitution, leaf, None)
            if substitute is not NO_SUBSTITUTION:
                return (substitute if build else None), 0
            return (protocol_method(leaf, "__json_tree__")(leaf) if build else None), 0
        # 見積もりの作業量（runtime ref を辿る分）もこの作業量へ数える（byte の大きさとは分ける）
        size = protocol_method(leaf, "__json_tree_bytes__")(leaf, RESULT_JSON_POLICY, self.remaining(), self)
        built = None
        if size is None:
            # DAG のまま見積もれない形（閉路。未凍結の式の中だけ）: node を 1 つ作るたびに
            # 数えながら作る（作ってから数えない）
            before = self.consumed
            built = protocol_method(leaf, "__json_tree_metered__")(leaf, RESULT_JSON_POLICY, self)
            size = self.consumed - before
        else:
            self.charge(size)
        # 数えるのは予算の分まで（超えたと分かれば残りの node は辿らない）
        self._meter.add_root(leaf, max_distinct=self._policy.serialization_nodes)
        if self._policy.exceeds(BudgetKind.SERIALIZATION_NODES, self.distinct_nodes):
            if not self.terminal:
                from scripts.function_tracer_pcode.core.json_encoding import JsonBudgetExhausted

                # node の上限で止めた: byte の超過として上限 + 1 を伝える（呼ぶ側が上限の内側と
                # 読み違えない）
                raise JsonBudgetExhausted(
                    consumed_bytes=self.consumed if self.max_bytes is None else self.max_bytes + 1,
                    max_bytes=self.max_bytes,
                )
            enforce_budget(
                BudgetKind.SERIALIZATION_NODES, self.distinct_nodes, site=self.site,
                target_key=self.target_key(),
                limit=self._policy.serialization_nodes,
            )
        substitute = NO_SUBSTITUTION
        if substitution is not None:
            substitute = protocol_method(substitution, "__leaf_substitute__")(substitution, leaf, size)
        if substitute is not NO_SUBSTITUTION:
            return (substitute if build else None), size
        if build and built is None:
            built = protocol_method(leaf, "__json_tree__")(leaf)
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

    def active_leaf_substitution(self) -> Optional["LeafSubstitution"]:
        """この thread が今この作業量に効かせている置き換え（無ければ `None`）。"""

        stack = self._substitutions.get(threading.get_ident())
        return stack[-1] if stack else None

    def observed_runtime_ref(self, ref: Any, missing: Any) -> Any:
        """この直列化が描いた runtime ref の LEGACY 表現（`runtime_ref_memo`。描いていなければ `missing`）。

        memo は直列化の間だけの写しの元で、描いた表現を書き換えない（置くたびに容器を作り直す）。
        """

        entry = self.runtime_ref_memo.get(id(ref))
        if entry is None or entry[0] is not ref:
            return missing
        return entry[1]

    def target_key(self) -> Tuple[str, str]:
        from scripts.function_tracer_pcode.core.semantic_snapshot import (
            stable_atoms_digest,
        )

        return ("serialization", stable_atoms_digest(self._target_parts))

    def observe(self) -> None:
        """この直列化の最終的な量を観測値へ残す（量は単調に増えるので最後の値が最大）。

        観測は予算の既定値を決めるため（U-1）の値で、意味の限界になる（terminal な）直列化
        だけを残す。診断用の作業量（terminal でない）は時間などの記録の長さを数えるので
        run ごとに揺れ、既定値の根拠にもならない。
        """

        if self.enabled and self.terminal:
            observe_budget_usage(BudgetKind.SERIALIZATION_BYTES, self.consumed, site=self.site)
            observe_budget_usage(BudgetKind.SERIALIZATION_NODES, self.distinct_nodes, site=self.site)


#: 直列化の作業量は値の storage の読みも数える（`live_values.metered_storage_reads`）
live_values.register_storage_meter(SerializationWork)

_SERIALIZATION = threading.local()


class _NoSubstitution:
    """`leaf_substitution` が「この葉は置き換えない」と答える印（1 つだけ）。"""

    __slots__ = ()

    def __repr__(self) -> str:
        return "NO_SUBSTITUTION"


#: `leaf_substitution` の答え: 置き換えない（葉は通常どおり見積もって作る）
NO_SUBSTITUTION = _NoSubstitution()


class LeafSubstitution:
    """直列化の作業量の sized leaf の置き換え（`substituting_leaves`）の protocol。

    `__leaf_substitute__(leaf, size)` は、作業量が sized leaf の大きさを見積もって数えた後、葉を作る
    **前** に呼ばれ、置く値か `NO_SUBSTITUTION` を返す。`size` は見積もった byte の大きさ（数えない
    作業量では `None`）。何を置き換えるかは subclass（渡す側）が決める。呼ばれるのは walk の外から始めた
    LEGACY の構築が置く葉だけ（`SerializationWork.tree`）。上限を超えた葉には尋ねない（作業量が先に止まる）。
    """

    __slots__ = ()

    def __leaf_substitute__(self, leaf: Any, size: Optional[int]) -> Any:
        return NO_SUBSTITUTION

    def __placed_values__(self) -> Tuple[Any, ...]:
        """これまでに置いた値（`NO_SUBSTITUTION` 以外の答え）そのもの。置いた値を後で特別に扱う側（例: snapshot の
        読みが token を codec に通す）は、型ではなくこの値の identity で照合する。"""

        return ()


@contextmanager
def substituting_leaves(work: Optional[SerializationWork], substitution: Optional[LeafSubstitution]) -> Iterator[None]:
    """この中で `work` が作る sized leaf を `substitution` に尋ねる（`None` なら何もしない）。

    置き換えは置く値だけを変え、数える量は変えない（`SerializationWork.tree`）: 作業量の量・上限の
    超過・観測値は、置き換えの有無に依らない。そのため terminal な作業量（意味の限界になる本体の直列化）
    でも使える。置き換えた葉を受け取るのは呼ぶ側だけ（walk の外から始めた LEGACY の構築が置く葉）。
    """

    if substitution is None or work is None:
        yield
        return
    if not isinstance(substitution, LeafSubstitution):
        raise TypeError("a leaf substitution must be a LeafSubstitution")
    # 効くのは、効かせた thread の、この `with` の間だけ（入れ子は内側が効き、抜けると外側へ戻る: 呼ぶ側が誰でも
    # 同じ規則。別の thread が同じ作業量で始めた walk には効かない）
    ident = threading.get_ident()
    stack = work._substitutions.setdefault(ident, [])
    stack.append(substitution)
    try:
        yield
    finally:
        stack.pop()
        if not stack:
            work._substitutions.pop(ident, None)


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
    """直列化 1 つ分の作業量を数える scope（同じ意味の入れ子は外側へ合流する）。

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
    parent = stack[-1] if stack else None
    if parent is not None and terminal and max_bytes is None:
        # 同じ意味の入れ子（terminal・上限なし）は外側の作業量へ合流する
        yield parent
        return
    # 入れ子でも自分の上限・terminal を持つ。terminal なら外側へも足す。terminal でない
    # （診断の）scope は外側と独立に数える: 診断の超過が外側の意味の限界にならない
    work = SerializationWork(
        site=site, target_parts=target_parts,
        enabled=(budget_scope_is_active() if enabled is None else enabled),
        terminal=terminal, max_bytes=max_bytes,
        parent=parent if terminal else None,
    )
    stack.append(work)
    try:
        # この scope の中の値の storage の読みも、固定の上限を超えた分はこの作業量へ（無効な scope は
        # 数えるだけ: この scope の直列化が組み込みの容器を辿るのと同じ。`live_values.metered_storage_reads`）
        with live_values.metered_storage_reads(work):
            yield work
    finally:
        stack.pop()
        work.observe()


def exceeded_budget_bound(
    kind: BudgetKind, observed: int, *, site: str, limit: Optional[int] = None,
) -> Optional[int]:
    """観測値を残し、上限を超えていればその上限を、そうでなければ `None` を返す（checkpoint の比較の
    半分: 上限の内側の checkpoint は限界の target / evidence を作らない）。"""

    # 限界になる予算だけ（fallback の予算 `FallbackBudgetKind` は値を拒む: 限界にしない）
    kind = BudgetKind(kind)
    observe_budget_usage(kind, observed, site=site)
    bound = active_budget_policy().limit(kind) if limit is None else limit
    if bound is not None and live_values.as_int(observed) > bound:
        return bound
    return None


def enforce_budget(
    kind: BudgetKind,
    observed: int,
    *,
    site: str,
    target_key: Any,
    evidence: Iterable[str] = (),
    limit: Optional[int] = None,
) -> None:
    """観測値を残し、上限を超えていたら限界にする（checkpoint の入口）。

    上限は `limit`（作業量が自分の上限を持つとき）か、`None` なら今の policy の上限。
    target と evidence を作るのに仕事が要る checkpoint は `exceeded_budget_bound` で比べてから、
    超えたときだけ組み立てて `raise_expression_size_budget_exceeded` を呼ぶ。
    """

    bound = exceeded_budget_bound(kind, observed, site=site, limit=limit)
    if bound is not None:
        raise_expression_size_budget_exceeded(
            kind,
            observed=observed,
            limit=bound,
            site=site,
            target_key=target_key,
            evidence=evidence,
        )


__all__ = [
    "BudgetKind",
    "BudgetObservations",
    "FallbackBudgetKind",
    "FallbackBudgetMeter",
    "pair_fallback_meter",
    "BudgetPolicy",
    "active_budget_policy",
    "budget_observations",
    "budget_policy_scope",
    "budget_scope_is_active",
    "enforce_budget",
    "raise_output_schema_exceeded",
    "exceeded_budget_bound",
    "observe_budget_usage",
    "raise_expression_size_budget_exceeded",
    "raise_render_budget_exceeded",
    "serialization_scope",
    "SerializationWork",
    "active_serialization_work",
    "LeafSubstitution",
    "NO_SUBSTITUTION",
    "substituting_leaves",
]
