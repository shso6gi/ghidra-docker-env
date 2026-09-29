# -*- coding: utf-8 -*-
"""条件簡約・条件 oracle の **計測** の owner（Issue #105 PR-105-A）。診断専用。

DPLL の決定回数予算・oracle の query 数予算（PR-105-B）の値を決める分布と、予算が
尽きて fallback した記録（`budget_events`）を持つ。ここにある値は **判定にも cache の
意味にも使わない**: 数えるだけで、何も止めず、何も選ばない（`note` / `observe` /
`budget_event` は値を返さない）。予算の消費と上限の比較は `core/budget_policy` の
`FallbackBudgetMeter`、尽きたときの fallback は数える側（`analysis/condition/`）が持つ。

独立に数える counter（名前は `snapshot()` の key）:

* `dpll.decisions` — DPLL の分岐（決定）の総数。1 回の充足可能性判定あたりの分布は
  `dpll.decisions_per_call`（log2 の度数・最大・合計・件数）
* `dpll.satisfiability_calls` — 充足可能性判定（`_clauses_satisfiability` の最上位
  呼び出し）の回数
* `oracle.queries` — solver（z3）を実際に呼んだ回数。1 回の時間は `oracle.check_ms`
* `oracle.timeouts` — solver が `unknown`（timeout / canceled）を返した回数
* `oracle.unknowns` — solver が `unknown` を返した回数（timeout 以外も含む）
* `cache_family.<owner>.hit` / `.miss` — owner（`simplifier` / `oracle`）の表の合計
* `cache.<表>.hit` / `.miss` / `.bucket_collision` / `.evicted` / `.too_large` /
  `.uncacheable` — cache 表ごと（`memo.<種別>.*` は root 単位の memo）
* `oracle.unknown_hit` — cache hit のうち記憶していた値が `None`（未判定）だったもの
* `identity.*` / `memo.*` — identity の構築と root 単位 memo の hit
* `simplifier.reentry_guard_hit` / `simplifier.guard_tainted_not_stored` — 再入 guard の
  打ち切り（と予算の fallback）と、それを材料にしたので覚えなかった答え
* `budget.<種類>.exceeded` — fallback の予算（Issue #105 PR-105-B、`core/budget_policy`
  の `FallbackBudgetKind`）が尽きて問いに答えなかった回数。1 件ずつの記録は
  `budget_events`（`{budget_type, site, limit, consumed, fallback_taken}`、先頭
  `MAX_BUDGET_EVENTS` 件まで。超えた分は `budget_events_dropped` の件数だけ）

置き場所が `core` なのは、値を書く側（`analysis/condition`）と読む側（出力の準備
`checker/output_preparation`。出力層は analysis に依存しない）の両方から下向きに参照
できる唯一の層だから（`core/budget_policy` の観測値と同じ）。counter の意味を持つのは
書く側で、ここは数え方（件数・log2 の度数・journal）だけを持つ。

寿命は cache と同じく pair（`condition_metrics_scope()` を pair 境界が開閉する）だが、
**別の scope**: cache を消しても数は消えず、数を見ても cache は変わらない。scope の外
では何も数えない。kill された pair は結果 JSON を出さないので、主要な counter は
2 の冪を越えたときだけ journal にも残す（`core/stage_journal`、書き込みは対数回）。
"""

from __future__ import annotations

import threading
from contextlib import contextmanager
from typing import Any, Dict, Iterator, List, Optional

from scripts.function_tracer_pcode.core.stage_journal import journal_note


METRICS_SCHEMA = "condition-simplify-metrics-v1"

#: journal にも残す counter（kill された pair の下限を後から読めるように）
JOURNALED_COUNTERS = frozenset(
    {
        "dpll.decisions",
        "dpll.satisfiability_calls",
        "oracle.queries",
        "oracle.timeouts",
        "cache.oracle.verdict.miss",
        "cache.oracle.verdict.hit",
    }
)

#: `budget_events` に 1 件ずつ残す上限（超えた分は件数だけ: 出力を有界にする）
MAX_BUDGET_EVENTS = 256

#: 予算の fallback の記録の field（この順で出す）
BUDGET_EVENT_FIELDS = ("budget_type", "site", "limit", "consumed", "fallback_taken")

#: 分布の最大値を journal にも残す観測
JOURNALED_OBSERVATIONS = frozenset({"dpll.decisions_per_call", "oracle.check_ms"})


class _Distribution:
    __slots__ = ("count", "total", "maximum", "buckets")

    def __init__(self) -> None:
        self.count = 0
        self.total = 0
        self.maximum = 0
        #: `value.bit_length()` → 件数（0 は 0、1 は 1、2..3 は 2、...）
        self.buckets: Dict[int, int] = {}

    def add(self, value: int) -> bool:
        self.count += 1
        self.total += value
        bucket = value.bit_length()
        self.buckets[bucket] = self.buckets.get(bucket, 0) + 1
        if value > self.maximum:
            crossed = value.bit_length() > self.maximum.bit_length()
            self.maximum = value
            return crossed
        return False

    def to_diagnostic(self) -> Dict[str, Any]:
        return {
            "count": self.count,
            "total": self.total,
            "max": self.maximum,
            "log2_buckets": {str(key): self.buckets[key] for key in sorted(self.buckets)},
        }


class ConditionSimplifyMetrics:
    """1 pair 分の計測値。"""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._counts: Dict[str, int] = {}
        self._distributions: Dict[str, _Distribution] = {}
        self._budget_events: List[Dict[str, Any]] = []
        self._budget_events_total = 0

    def budget_event(
        self, *, budget_type: str, site: str, limit: Optional[int], consumed: int, fallback_taken: str
    ) -> None:
        """予算が尽きて fallback した 1 件（診断専用: 何も止めず、何も選ばない）。"""

        with self._lock:
            self._budget_events_total += 1
            total = self._budget_events_total
            if len(self._budget_events) < MAX_BUDGET_EVENTS:
                self._budget_events.append(
                    {
                        "budget_type": str(budget_type),
                        "site": str(site),
                        "limit": None if limit is None else int(limit),
                        "consumed": int(consumed),
                        "fallback_taken": str(fallback_taken),
                    }
                )
        self.note(f"budget.{budget_type}.exceeded")
        if total == 1:
            # kill された pair にも「予算で答えなかった」事実が残るように最初の 1 件だけ
            journal_note("condition_simplify_budget", {"budget": str(budget_type), "site": str(site)})

    def note(self, name: str, amount: int = 1) -> None:
        with self._lock:
            before = self._counts.get(name, 0)
            after = before + amount
            self._counts[name] = after
        if name in JOURNALED_COUNTERS and after.bit_length() > before.bit_length():
            journal_note("condition_simplify_counter", {"counter": name, "value": after})

    def observe(self, name: str, value: int) -> None:
        value = max(0, int(value))
        with self._lock:
            distribution = self._distributions.get(name)
            if distribution is None:
                distribution = self._distributions[name] = _Distribution()
            crossed = distribution.add(value)
        if crossed and name in JOURNALED_OBSERVATIONS:
            journal_note("condition_simplify_max", {"observation": name, "value": value})

    def count(self, name: str) -> int:
        with self._lock:
            return self._counts.get(name, 0)

    def snapshot(self) -> Dict[str, Any]:
        with self._lock:
            snapshot: Dict[str, Any] = {
                "schema": METRICS_SCHEMA,
                "counters": {name: self._counts[name] for name in sorted(self._counts)},
                "distributions": {
                    name: self._distributions[name].to_diagnostic()
                    for name in sorted(self._distributions)
                },
            }
            if self._budget_events_total:
                snapshot["budget_events"] = [dict(event) for event in self._budget_events]
                snapshot["budget_events_total"] = self._budget_events_total
                snapshot["budget_events_dropped"] = self._budget_events_total - len(self._budget_events)
            return snapshot


_SCOPE_LOCK = threading.Lock()
_SCOPES: List[ConditionSimplifyMetrics] = []
_FRAMES = threading.local()


@contextmanager
def condition_metrics_scope() -> Iterator[ConditionSimplifyMetrics]:
    """1 pair（解析 1 単位）の計測の寿命。入るたびに 0 から数える。"""

    metrics = ConditionSimplifyMetrics()
    with _SCOPE_LOCK:
        _SCOPES.append(metrics)
    try:
        yield metrics
    finally:
        with _SCOPE_LOCK:
            if _SCOPES and _SCOPES[-1] is metrics:
                _SCOPES.pop()
            elif metrics in _SCOPES:
                del _SCOPES[_SCOPES.index(metrics):]


def active_condition_metrics() -> Optional[ConditionSimplifyMetrics]:
    with _SCOPE_LOCK:
        return _SCOPES[-1] if _SCOPES else None


def note(name: str, amount: int = 1) -> None:
    """counter を足す（scope の外では何もしない）。"""

    metrics = active_condition_metrics()
    if metrics is not None:
        metrics.note(name, amount)


def observe(name: str, value: int) -> None:
    """分布へ 1 件足す（scope の外では何もしない）。"""

    metrics = active_condition_metrics()
    if metrics is not None:
        metrics.observe(name, value)


def budget_event(
    *, budget_type: str, site: str, limit: Optional[int], consumed: int, fallback_taken: str
) -> None:
    """予算の fallback を 1 件記録する（scope の外では何もしない）。"""

    metrics = active_condition_metrics()
    if metrics is not None:
        metrics.budget_event(
            budget_type=budget_type, site=site, limit=limit, consumed=consumed,
            fallback_taken=fallback_taken,
        )


def condition_metrics_snapshot() -> Dict[str, Any]:
    """今の scope の計測値（scope の外では空）。出力の準備が診断へ写す。"""

    metrics = active_condition_metrics()
    return {} if metrics is None else metrics.snapshot()


#: `pairwise_debug_stats` へ載せる要約の名前（計画 §6.B-1 / D3）→ 数え方
#: 条件簡約の表（`simplifier.*`）の hit / miss の合計（`condition_cache` が表ごとの数と一緒に数える）
_SIMPLIFIER_FAMILY_HIT = "cache_family.simplifier.hit"
_SIMPLIFIER_FAMILY_MISS = "cache_family.simplifier.miss"
_PAIRWISE_DEBUG_COUNTERS = (
    ("condition_oracle_query", "oracle.queries"),
    ("condition_oracle_cache_hit", "cache.oracle.verdict.hit"),
    ("condition_oracle_unknown_hit", "oracle.unknown_hit"),
    ("condition_oracle_identity_miss_after_hash_hit", "cache.oracle.verdict.bucket_collision"),
    ("condition_oracle_timeout", "oracle.timeouts"),
    ("condition_satisfiability_calls", "dpll.satisfiability_calls"),
    ("condition_dpll_decisions", "dpll.decisions"),
)


#: `pairwise_debug_counters()` が書く key の全部（出力の準備が上書きの対象を知るため）
#: 予算の fallback の件数（`budget_events` の全件。計画 §6.B-2 の `pairwise_debug_stats` 名）
SIMPLIFY_BUDGET_EXCEEDED_STAT = "simplify_budget_exceeded"

CONDITION_COUNTER_STAT_KEYS = frozenset(
    {
        "structural_key_cache_hit",
        "structural_key_cache_miss",
        "condition_dpll_decisions_per_call_max",
        SIMPLIFY_BUDGET_EXCEEDED_STAT,
    }
    | {key for key, _name in _PAIRWISE_DEBUG_COUNTERS}
)


def pairwise_debug_counters(snapshot: Optional[Dict[str, Any]] = None) -> Dict[str, int]:
    """計測の snapshot を、`pairwise_debug_stats` 用の平たい整数の要約にする（0 は載せない）。

    `snapshot` を渡さなければ今の scope の snapshot（scope の外では空）。分布（log2 の
    度数など）は `diagnostics.condition_simplify` にだけ出し、ここは件数と 1 回あたりの
    DPLL 決定数の最大だけ。`structural_key_cache_*` は条件簡約の表（`simplifier.*`: conjunction の
    充足不能性・含意）の合計（`cache_family.simplifier.*`、表が数える）。
    """

    if snapshot is None:
        metrics = active_condition_metrics()
        if metrics is None:
            return {}
        snapshot = metrics.snapshot()
    if not snapshot:
        return {}
    counters = snapshot.get("counters") or {}
    summary = {
        "structural_key_cache_hit": counters.get(_SIMPLIFIER_FAMILY_HIT, 0),
        "structural_key_cache_miss": counters.get(_SIMPLIFIER_FAMILY_MISS, 0),
    }
    for key, name in _PAIRWISE_DEBUG_COUNTERS:
        summary[key] = counters.get(name, 0)
    decisions = (snapshot.get("distributions") or {}).get("dpll.decisions_per_call")
    summary["condition_dpll_decisions_per_call_max"] = int(decisions["max"]) if decisions else 0
    summary[SIMPLIFY_BUDGET_EXCEEDED_STAT] = int(snapshot.get("budget_events_total") or 0)
    return {key: value for key, value in summary.items() if value}


class _SatisfiabilityFrame:
    __slots__ = ("decisions",)

    def __init__(self) -> None:
        self.decisions = 0


@contextmanager
def satisfiability_call() -> Iterator[None]:
    """充足可能性判定 1 回（DPLL の最上位呼び出し）の計測枠。

    枠の中の `note_dpll_decision()` をこの 1 回の決定回数として数え、抜けるときに
    分布へ足す。判定の結果・例外には触れない。
    """

    stack = getattr(_FRAMES, "stack", None)
    if stack is None:
        stack = _FRAMES.stack = []
    frame = _SatisfiabilityFrame()
    stack.append(frame)
    try:
        yield
    finally:
        stack.pop()
        note("dpll.satisfiability_calls")
        observe("dpll.decisions_per_call", frame.decisions)


def note_dpll_decision() -> None:
    """DPLL が 1 回分岐した（決定した）。"""

    stack = getattr(_FRAMES, "stack", None)
    if stack:
        stack[-1].decisions += 1
    note("dpll.decisions")


__all__ = [
    "BUDGET_EVENT_FIELDS",
    "MAX_BUDGET_EVENTS",
    "METRICS_SCHEMA",
    "SIMPLIFY_BUDGET_EXCEEDED_STAT",
    "budget_event",
    "CONDITION_COUNTER_STAT_KEYS",
    "ConditionSimplifyMetrics",
    "active_condition_metrics",
    "condition_metrics_scope",
    "condition_metrics_snapshot",
    "note",
    "note_dpll_decision",
    "observe",
    "pairwise_debug_counters",
    "satisfiability_call",
]
