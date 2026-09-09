# -*- coding: utf-8 -*-
"""結果 JSON に添付する非署名の診断ブロック（Issue #17）。

段階別の経過時間・式サイズ・ソルバ呼び出し数を機械可読に残す。receipt / digest
の対象ではない診断領域なので、ここに項目を足しても既存の署名契約は変わらない。
"""

from __future__ import annotations

import os
import time
from contextlib import contextmanager
from typing import Any, Dict, Iterable, Iterator, Mapping, Optional

DIAGNOSTICS_SCHEMA = "result-diagnostics-v1"


class StageClock:
    """ペア 1 件の実行を段階（JVM 起動 / import / auto-analysis / 判定 …）に
    分けて計測する（Issue #14）。

    ``timed(stage)`` で囲んだ区間の秒数を ``seconds[stage]`` に加算し、同じ
    stage を複数回囲めば合算する。``mark(stage, seconds)`` は外部で測った値の
    登録用。``snapshot()`` は結果 JSON の診断ブロックへそのまま入る dict。
    診断なので計測に失敗しても例外を外へ出さない。
    """

    def __init__(self) -> None:
        self.seconds: Dict[str, float] = {}
        self.order: list = []
        self.notes: Dict[str, Any] = {}
        self._process_age_at_start = process_age_seconds()
        self._started = time.monotonic()

    @contextmanager
    def timed(self, stage: str) -> Iterator[None]:
        started = time.monotonic()
        try:
            yield
        finally:
            self.mark(stage, time.monotonic() - started)

    def mark(self, stage: str, seconds: float) -> None:
        try:
            value = max(0.0, float(seconds))
        except (TypeError, ValueError):
            return
        if stage not in self.seconds:
            self.order.append(stage)
            self.seconds[stage] = 0.0
        self.seconds[stage] += value

    def note(self, key: str, value: Any) -> None:
        self.notes[key] = value

    def snapshot(self) -> Dict[str, Any]:
        payload: Dict[str, Any] = {
            "schema": "pair-stage-timing-v1",
            "seconds": {stage: round(self.seconds[stage], 6) for stage in self.order},
            "elapsed_seconds": round(time.monotonic() - self._started, 6),
        }
        if self._process_age_at_start is not None:
            # Python 起動から計測開始までの時間（インタプリタ起動・import 込み）。
            payload["process_age_at_start_seconds"] = round(self._process_age_at_start, 6)
        if self.notes:
            payload["notes"] = dict(self.notes)
        return payload


def process_age_seconds() -> Optional[float]:
    """このプロセスの起動からの経過秒（Linux の /proc、fail-open で None）。"""
    try:
        with open("/proc/self/stat", "r", encoding="ascii", errors="replace") as handle:
            stat = handle.read()
        fields = stat[stat.rindex(")") + 2:].split()
        start_ticks = int(fields[19])
        with open("/proc/uptime", "r", encoding="ascii") as handle:
            uptime = float(handle.read().split()[0])
        ticks_per_second = os.sysconf("SC_CLK_TCK")
        return max(0.0, uptime - start_ticks / float(ticks_per_second))
    except Exception:
        return None


def attach_stage_timing(result: Any, clock: StageClock) -> None:
    """結果オブジェクトの診断ブロックに段階別時間を添付する（署名対象外）。"""
    try:
        diagnostics = dict(getattr(result, "diagnostics", None) or {})
        diagnostics["stages"] = clock.snapshot()
        result.diagnostics = diagnostics
    except Exception:
        return


def expression_stats(analysis: Any) -> Dict[str, int]:
    """戻り値式とガード条件の総ノード数・最大深さ・return case 数。

    明示スタックによる反復走査（再帰しない）。深い式でも RecursionError を
    起こさず、走査中に何か失敗しても診断は判定本体に影響しない（fail-open で
    ``error`` を残す）。
    """
    node_count = 0
    max_depth = 0
    seen: set = set()
    stack: list = []
    returns = tuple(getattr(analysis, "returns", ()) or ())
    for ret in returns:
        stack.append((getattr(ret, "value", None), 1))
        for cond in getattr(ret, "conditions", ()) or ():
            stack.append((getattr(cond, "expression", None), 1))
    try:
        while stack:
            expr, depth = stack.pop()
            if expr is None:
                continue
            if depth > max_depth:
                max_depth = depth
            key = id(expr)
            if key in seen:
                # shared sub-expression: depth already accounted, do not re-expand
                continue
            seen.add(key)
            node_count += 1
            for child in getattr(expr, "operands", None) or ():
                stack.append((child, depth + 1))
            branches = getattr(expr, "value", None)
            if isinstance(branches, (list, tuple)):
                for item in branches:
                    if isinstance(item, tuple) and len(item) == 2:
                        cond, value = item
                        stack.append((getattr(cond, "expression", None), depth + 1))
                        stack.append((value, depth + 1))
    except Exception as exc:  # diagnostics never fail the verdict
        return {
            "return_case_count": len(returns),
            "node_count": node_count,
            "max_depth": max_depth,
            "error": f"{type(exc).__name__}: {exc}"[:200],
        }
    return {
        "return_case_count": len(returns),
        "node_count": node_count,
        "max_depth": max_depth,
    }


_CACHE_STAT_COUNTERS = ("hits", "misses", "snapshots_stored", "invalidations")
_CACHE_STAT_REASON_MAPS = ("miss_reasons", "uncacheable_reasons")


_ANALYSIS_CACHE_STAT_COUNTERS = ("hits", "misses", "bound_misses_without_unbound_entry")


def _merge_cache_stats(
    accumulated: Optional[Mapping[str, Any]], observed: Mapping[str, Any]
) -> Dict[str, Any]:
    """analyzer instance ごとの cache 計数を 1 つの side 単位の集計にまとめる。"""
    if not accumulated:
        merged = dict(observed)
        merged["analyzer_instances"] = 1
        merged["snapshot_entries"] = observed.get("entries", 0)
        merged.pop("entries", None)
        return merged
    merged = dict(accumulated)
    for key in _CACHE_STAT_COUNTERS:
        merged[key] = int(merged.get(key, 0) or 0) + int(observed.get(key, 0) or 0)
    for key in _CACHE_STAT_REASON_MAPS:
        totals = dict(merged.get(key) or {})
        for reason, count in (observed.get(key) or {}).items():
            totals[reason] = totals.get(reason, 0) + int(count or 0)
        merged[key] = dict(sorted(totals.items()))
    merged["analyzer_instances"] = int(merged.get("analyzer_instances", 1) or 1) + 1
    merged["snapshot_entries"] = observed.get("entries", 0)
    merged.pop("entries", None)
    return merged


def _binding_induced_miss_counts(miss_reasons) -> Dict[str, int]:
    from scripts.function_tracer_pcode.analysis.runtime_state import binding_induced_miss_counts

    return binding_induced_miss_counts(miss_reasons)


def _merge_target_rows(
    accumulated: Iterable[Mapping[str, Any]], observed: Iterable[Mapping[str, Any]]
) -> list:
    """target 単位の analysis cache 計数を identity で足し合わせる。"""
    rows: Dict[str, Dict[str, Any]] = {}
    for row in list(accumulated) + list(observed):
        identity = str(row.get("target"))
        current = rows.get(identity)
        if current is None:
            rows[identity] = dict(row)
            rows[identity]["miss_reasons"] = dict(row.get("miss_reasons") or {})
            continue
        for key in ("hits", "misses", "bound_misses_without_unbound_entry"):
            current[key] = int(current.get(key, 0) or 0) + int(row.get(key, 0) or 0)
        reasons = dict(current.get("miss_reasons") or {})
        for reason, count in (row.get("miss_reasons") or {}).items():
            reasons[reason] = reasons.get(reason, 0) + int(count or 0)
        current["miss_reasons"] = dict(sorted(reasons.items()))
        current["distinct_scope_keys"] = max(
            int(current.get("distinct_scope_keys", 0) or 0),
            int(row.get("distinct_scope_keys", 0) or 0),
        )
        for key in ("is_external", "is_thunk", "thunked_is_external"):
            if current.get(key) is None and row.get(key) is not None:
                current[key] = row.get(key)
        current.update(_binding_induced_miss_counts(current.get("miss_reasons")))
    return sorted(
        rows.values(),
        key=lambda row: (-int(row.get("misses", 0) or 0), -int(row.get("hits", 0) or 0), str(row.get("target"))),
    )


def _merge_analysis_cache_stats(
    accumulated: Optional[Mapping[str, Any]], observed: Mapping[str, Any]
) -> Dict[str, Any]:
    """callee 解析 cache の計数を side 単位で集約する（parameter cache と同じ集約規則）。

    counter と reason map は加算、``entries`` は最後の analyzer の値、target 行は
    identity ごとに加算し、``repeated_miss_targets`` は集約後の値から作り直す。
    """
    from scripts.function_tracer_pcode.analysis.runtime_state import repeated_miss_targets

    if not accumulated:
        merged = dict(observed)
        merged["analyzer_instances"] = 1
        merged["cache_entries"] = observed.get("entries", 0)
        merged.pop("entries", None)
        return merged
    merged = dict(accumulated)
    for key in _ANALYSIS_CACHE_STAT_COUNTERS:
        merged[key] = int(merged.get(key, 0) or 0) + int(observed.get(key, 0) or 0)
    totals = dict(merged.get("miss_reasons") or {})
    for reason, count in (observed.get("miss_reasons") or {}).items():
        totals[reason] = totals.get(reason, 0) + int(count or 0)
    merged["miss_reasons"] = dict(sorted(totals.items()))
    merged.update(_binding_induced_miss_counts(merged["miss_reasons"]))
    merged["targets"] = _merge_target_rows(
        merged.get("targets") or (), observed.get("targets") or ()
    )
    merged["targets_truncated"] = int(merged.get("targets_truncated", 0) or 0) + int(
        observed.get("targets_truncated", 0) or 0
    )
    merged["repeated_miss_targets"] = repeated_miss_targets(merged["targets"])
    merged["analyzer_instances"] = int(merged.get("analyzer_instances", 1) or 1) + 1
    merged["cache_entries"] = observed.get("entries", 0)
    merged.pop("entries", None)
    return merged


_REUSE_STAT_COUNTERS = (
    "reuses",
    "unbound_analyses",
    "shadow_comparisons",
    "shadow_mismatches",
    "invalidations",
    "evicted_cache_entries",
)
_REUSE_STAT_REASON_MAPS = ("verdicts", "declines")


def _merge_reuse_target_rows(
    accumulated: Iterable[Mapping[str, Any]], observed: Iterable[Mapping[str, Any]]
) -> list:
    """再利用の target 行を identity で足し合わせる（判定内容は先勝ちで保持）。"""
    rows: Dict[str, Dict[str, Any]] = {}
    for row in list(accumulated) + list(observed):
        identity = str(row.get("target"))
        current = rows.get(identity)
        if current is None:
            rows[identity] = dict(row)
            rows[identity]["declines"] = dict(row.get("declines") or {})
            continue
        for key in ("unbound_analyses", "reuses", "shadow_comparisons", "shadow_mismatches"):
            current[key] = int(current.get(key, 0) or 0) + int(row.get(key, 0) or 0)
        declines = dict(current.get("declines") or {})
        for reason, count in (row.get("declines") or {}).items():
            declines[reason] = declines.get(reason, 0) + int(count or 0)
        current["declines"] = dict(sorted(declines.items()))
        for key in ("eligible", "verdict_reason", "resolution_reason"):
            if current.get(key) is None and row.get(key) is not None:
                current[key] = row.get(key)
    return sorted(
        rows.values(),
        key=lambda row: (-int(row.get("reuses", 0) or 0), -int(row.get("unbound_analyses", 0) or 0), str(row.get("target"))),
    )


def _merge_reuse_stats(
    accumulated: Optional[Mapping[str, Any]], observed: Mapping[str, Any]
) -> Dict[str, Any]:
    """再利用の計数を side 単位で集約する（cache 診断と同じ集約規則）。"""
    if not accumulated:
        merged = dict(observed)
        merged["analyzer_instances"] = 1
        merged["verdict_entries"] = observed.get("entries", 0)
        merged.pop("entries", None)
        return merged
    merged = dict(accumulated)
    for key in _REUSE_STAT_COUNTERS:
        merged[key] = int(merged.get(key, 0) or 0) + int(observed.get(key, 0) or 0)
    for key in _REUSE_STAT_REASON_MAPS:
        totals = dict(merged.get(key) or {})
        for reason, count in (observed.get(key) or {}).items():
            totals[reason] = totals.get(reason, 0) + int(count or 0)
        merged[key] = dict(sorted(totals.items()))
    merged["targets"] = _merge_reuse_target_rows(
        merged.get("targets") or (), observed.get("targets") or ()
    )
    merged["targets_truncated"] = int(merged.get("targets_truncated", 0) or 0) + int(
        observed.get("targets_truncated", 0) or 0
    )
    merged["shadow_mismatch_targets"] = sorted(
        {
            str(row.get("target"))
            for row in merged["targets"]
            if int(row.get("shadow_mismatches", 0) or 0) > 0
        }
    )
    merged["analyzer_instances"] = int(merged.get("analyzer_instances", 1) or 1) + 1
    # 保持数は累積ではなく最後の analyzer の値。
    merged["verdict_entries"] = observed.get("entries", 0)
    merged["owned_cache_entries"] = observed.get("owned_cache_entries", 0)
    merged.pop("entries", None)
    return merged


class AnalysisTimer:
    """関数解析の経過時間を side ごとに記録する。"""

    def __init__(self) -> None:
        self.seconds: Dict[str, float] = {}
        self.stats: Dict[str, Dict[str, int]] = {}
        self.cache_stats: Dict[str, Dict[str, Any]] = {}
        self.analysis_cache_stats: Dict[str, Dict[str, Any]] = {}
        self.reuse_stats: Dict[str, Dict[str, Any]] = {}

    def timed(self, side: str, run: Any) -> Any:
        started = time.perf_counter()
        try:
            return run()
        finally:
            try:
                self.seconds[side] = self.seconds.get(side, 0.0) + (time.perf_counter() - started)
            except Exception:
                pass

    def record_analysis(self, side: str, analysis: Any) -> None:
        """Fail-open: a diagnostics failure must never surface to the caller."""
        if analysis is None:
            return
        try:
            self.stats[side] = expression_stats(analysis)
        except Exception as exc:
            self.stats[side] = {"error": f"{type(exc).__name__}: {exc}"[:200]}

    def record_callee_parameter_cache(self, side: str, analyzer: Any) -> None:
        """Issue #47: callee parameter snapshot cache の hit/miss を side ごとに残す。

        同じ side が複数回解析される（再解析）場合は analyzer が作り直されるので、
        instance ごとの計数を側単位で足し合わせる。``snapshot_entries`` だけは累積では
        なく最後の analyzer の保持数。Fail-open: 診断の失敗を呼び出し側へ出さない。
        """
        reader = getattr(analyzer, "callee_parameter_cache_diagnostics", None)
        if not callable(reader):
            return
        try:
            self.cache_stats[side] = _merge_cache_stats(
                self.cache_stats.get(side), dict(reader() or {})
            )
        except Exception as exc:
            self.cache_stats[side] = {"error": f"{type(exc).__name__}: {exc}"[:200]}

    def record_callee_analysis_cache(self, side: str, analyzer: Any) -> None:
        """Issue #47: callee 解析 cache の hit/miss と miss 原因を side ごとに残す。

        parameter snapshot cache とは別の観測なので別 bucket に置く。集約規則は
        ``record_callee_parameter_cache`` と同じ（instance ごとの計数を side で加算）。
        Fail-open: 診断の失敗を呼び出し側へ出さない。
        """
        reader = getattr(analyzer, "callee_analysis_cache_diagnostics", None)
        if not callable(reader):
            return
        try:
            self.analysis_cache_stats[side] = _merge_analysis_cache_stats(
                self.analysis_cache_stats.get(side), dict(reader() or {})
            )
        except Exception as exc:
            self.analysis_cache_stats[side] = {"error": f"{type(exc).__name__}: {exc}"[:200]}

    def record_callee_unbound_reuse(self, side: str, analyzer: Any) -> None:
        """Issue #47 (PR-B): external placeholder callee の再利用計数を side ごとに残す。

        cache の hit/miss とは別の観測（「解析を何回省いたか」「shadow が一致したか」）
        なので別 bucket に置く。Fail-open: 診断の失敗を呼び出し側へ出さない。
        """
        reader = getattr(analyzer, "callee_unbound_reuse_diagnostics", None)
        if not callable(reader):
            return
        try:
            self.reuse_stats[side] = _merge_reuse_stats(
                self.reuse_stats.get(side), dict(reader() or {})
            )
        except Exception as exc:
            self.reuse_stats[side] = {"error": f"{type(exc).__name__}: {exc}"[:200]}

    def snapshot(self) -> Dict[str, Any]:
        try:
            return {
                "analysis_seconds": {side: round(value, 6) for side, value in self.seconds.items()},
                "expressions": {side: dict(stats) for side, stats in self.stats.items()},
                "callee_parameter_cache": {
                    side: dict(stats) for side, stats in self.cache_stats.items()
                },
                "callee_analysis_cache": {
                    side: dict(stats) for side, stats in self.analysis_cache_stats.items()
                },
                "callee_unbound_reuse": {
                    side: dict(stats) for side, stats in self.reuse_stats.items()
                },
            }
        except Exception as exc:
            return {"error": f"{type(exc).__name__}: {exc}"[:200]}


def _solver_rows(container: Any) -> Iterable[Any]:
    results = getattr(container, "results", None)
    if results is None and isinstance(container, Mapping):
        results = container.get("results") or container.get("all_results")
    return tuple(results or ())


def _elapsed(row: Any) -> float:
    value = getattr(row, "elapsed_time", None)
    if value is None and isinstance(row, Mapping):
        value = row.get("elapsed_time")
    try:
        return float(value or 0.0)
    except (TypeError, ValueError):
        return 0.0


def result_diagnostics_payload(result: Any) -> Dict[str, Any]:
    """`EquivalenceResult.to_dict()` 用に、解析時の記録と結果の統計を合成する。

    診断は判定結果に影響してはならないため、失敗しても最小のブロックを返す。
    """
    try:
        return _result_diagnostics_payload(result)
    except Exception as exc:
        return {"schema": DIAGNOSTICS_SCHEMA, "error": f"{type(exc).__name__}: {exc}"[:200]}


def _result_diagnostics_payload(result: Any) -> Dict[str, Any]:
    base = dict(getattr(result, "diagnostics", None) or {})
    attempts_out = []
    solver_seconds = 0.0
    solver_invocations = 0
    trace = getattr(result, "debug_trace", None)
    for attempt in tuple(getattr(trace, "attempts", ()) or ()):
        rows = _solver_rows(getattr(attempt, "solver_results", None))
        seconds = sum(_elapsed(row) for row in rows)
        solver_seconds += seconds
        solver_invocations += len(rows)
        attempts_out.append({
            "attempt_id": getattr(attempt, "attempt_id", None),
            "phase": getattr(attempt, "phase", None),
            "strategy": getattr(attempt, "strategy", None),
            "elapsed_seconds": getattr(attempt, "elapsed_time", None),
            "solver_seconds": round(seconds, 6),
            "solver_invocations": len(rows),
        })
    if not attempts_out:
        rows = _solver_rows(getattr(result, "solver_results", None))
        solver_seconds = sum(_elapsed(row) for row in rows)
        solver_invocations = len(rows)
    pairwise = dict(getattr(result, "pairwise_stats", None) or {})
    return {
        "schema": DIAGNOSTICS_SCHEMA,
        "timings": {
            "total_seconds": getattr(result, "total_time", None),
            "analysis_seconds": dict(base.get("analysis_seconds") or {}),
            "solver_seconds": round(solver_seconds, 6),
            "attempts": attempts_out,
            "stages": dict(base.get("stages") or {}),
            "boundary_seconds": dict(base.get("boundary_seconds") or {}),
        },
        "expressions": dict(base.get("expressions") or {}),
        "caches": {
            "callee_parameter_decompile": dict(base.get("callee_parameter_cache") or {}),
            "callee_analysis": dict(base.get("callee_analysis_cache") or {}),
            "callee_unbound_reuse": dict(base.get("callee_unbound_reuse") or {}),
        },
        "validated_once_entries": base.get("validated_once_entries"),
        "pairs": pairwise,
        "solver_invocations": solver_invocations,
        "stage_path": list(getattr(result, "stage_path", ()) or ()),
    }
