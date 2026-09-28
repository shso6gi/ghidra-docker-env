# -*- coding: utf-8 -*-
"""条件簡約・条件 oracle の **計測** の owner（Issue #105 PR-105-A）。診断専用。

PR-105-B が DPLL の決定回数予算・oracle の query 数予算を決めるための分布を取る。
ここにある値は **判定にも cache の意味にも使わない**: 数えるだけで、何も止めず、
何も選ばない（`note` / `observe` は値を返さない）。予算の有効化は PR-105-B の責務。

独立に数える counter（名前は `snapshot()` の key）:

* `dpll.decisions` — DPLL の分岐（決定）の総数。1 回の充足可能性判定あたりの分布は
  `dpll.decisions_per_call`（log2 の度数・最大・合計・件数）
* `dpll.satisfiability_calls` — 充足可能性判定（`_clauses_are_satisfiable` の最上位
  呼び出し）の回数
* `oracle.queries` — solver（z3）を実際に呼んだ回数。1 回の時間は `oracle.check_ms`
* `oracle.timeouts` — solver が `unknown`（timeout / canceled）を返した回数
* `oracle.unknowns` — solver が `unknown` を返した回数（timeout 以外も含む）
* `cache.<表>.hit` / `.miss` / `.bucket_collision` / `.cleared` — cache 表ごと
* `oracle.unknown_hit` — cache hit のうち記憶していた値が `None`（未判定）だったもの
* `identity.*` / `memo.*` — identity の構築と root 単位 memo の hit

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
            return {
                "schema": METRICS_SCHEMA,
                "counters": {name: self._counts[name] for name in sorted(self._counts)},
                "distributions": {
                    name: self._distributions[name].to_diagnostic()
                    for name in sorted(self._distributions)
                },
            }


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


def condition_metrics_snapshot() -> Dict[str, Any]:
    """今の scope の計測値（scope の外では空）。出力の準備が診断へ写す。"""

    metrics = active_condition_metrics()
    return {} if metrics is None else metrics.snapshot()


#: `pairwise_debug_stats` へ載せる要約の名前（計画 §6.B-1 / D3）→ 数え方
_SIMPLIFIER_CACHE_PREFIX = "cache.simplifier."
_PAIRWISE_DEBUG_COUNTERS = (
    ("condition_oracle_query", "oracle.queries"),
    ("condition_oracle_cache_hit", "cache.oracle.verdict.hit"),
    ("condition_oracle_unknown_hit", "oracle.unknown_hit"),
    ("condition_oracle_identity_miss_after_hash_hit", "cache.oracle.verdict.bucket_collision"),
    ("condition_oracle_timeout", "oracle.timeouts"),
    ("condition_satisfiability_calls", "dpll.satisfiability_calls"),
    ("condition_dpll_decisions", "dpll.decisions"),
)


def pairwise_debug_counters() -> Dict[str, int]:
    """今の scope の計測を、`pairwise_debug_stats` 用の平たい整数の要約にする（0 は載せない）。

    分布（log2 の度数など）は `diagnostics.condition_simplify` にだけ出し、ここは件数と
    1 回あたりの DPLL 決定数の最大だけ。`structural_key_cache_*` は条件簡約の表
    （`cache.simplifier.*`: 含意・矛盾・formula の含意）の合計。scope の外では空。
    """

    metrics = active_condition_metrics()
    if metrics is None:
        return {}
    snapshot = metrics.snapshot()
    counters = snapshot["counters"]
    summary = {
        "structural_key_cache_hit": sum(
            value for name, value in counters.items()
            if name.startswith(_SIMPLIFIER_CACHE_PREFIX) and name.endswith(".hit")
        ),
        "structural_key_cache_miss": sum(
            value for name, value in counters.items()
            if name.startswith(_SIMPLIFIER_CACHE_PREFIX) and name.endswith(".miss")
        ),
    }
    for key, name in _PAIRWISE_DEBUG_COUNTERS:
        summary[key] = counters.get(name, 0)
    decisions = snapshot["distributions"].get("dpll.decisions_per_call")
    summary["condition_dpll_decisions_per_call_max"] = int(decisions["max"]) if decisions else 0
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
    "METRICS_SCHEMA",
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
