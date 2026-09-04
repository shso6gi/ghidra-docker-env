# -*- coding: utf-8 -*-
"""結果 JSON に添付する非署名の診断ブロック（Issue #17）。

段階別の経過時間・式サイズ・ソルバ呼び出し数を機械可読に残す。receipt / digest
の対象ではない診断領域なので、ここに項目を足しても既存の署名契約は変わらない。
"""

from __future__ import annotations

import time
from typing import Any, Dict, Iterable, Mapping, Optional

DIAGNOSTICS_SCHEMA = "result-diagnostics-v1"


def expression_stats(analysis: Any) -> Dict[str, int]:
    """戻り値式とガード条件の総ノード数・最大深さ・return case 数。"""
    node_count = 0
    max_depth = 0
    seen: set = set()

    def walk(expr: Any, depth: int) -> None:
        nonlocal node_count, max_depth
        if expr is None:
            return
        key = id(expr)
        if key in seen:
            return
        seen.add(key)
        node_count += 1
        max_depth = max(max_depth, depth)
        for child in getattr(expr, "operands", None) or ():
            walk(child, depth + 1)
        branches = getattr(expr, "value", None)
        if isinstance(branches, (list, tuple)):
            for item in branches:
                if isinstance(item, tuple) and len(item) == 2:
                    cond, value = item
                    walk(getattr(cond, "expression", None), depth + 1)
                    walk(value, depth + 1)

    returns = tuple(getattr(analysis, "returns", ()) or ())
    for ret in returns:
        walk(getattr(ret, "value", None), 1)
        for cond in getattr(ret, "conditions", ()) or ():
            walk(getattr(cond, "expression", None), 1)
    return {
        "return_case_count": len(returns),
        "node_count": node_count,
        "max_depth": max_depth,
    }


class AnalysisTimer:
    """関数解析の経過時間を side ごとに記録する。"""

    def __init__(self) -> None:
        self.seconds: Dict[str, float] = {}
        self.stats: Dict[str, Dict[str, int]] = {}

    def timed(self, side: str, run: Any) -> Any:
        started = time.perf_counter()
        try:
            return run()
        finally:
            self.seconds[side] = self.seconds.get(side, 0.0) + (time.perf_counter() - started)

    def record_analysis(self, side: str, analysis: Any) -> None:
        if analysis is not None:
            self.stats[side] = expression_stats(analysis)

    def snapshot(self) -> Dict[str, Any]:
        return {
            "analysis_seconds": {side: round(value, 6) for side, value in self.seconds.items()},
            "expressions": {side: dict(stats) for side, stats in self.stats.items()},
        }


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
    """`EquivalenceResult.to_dict()` 用に、解析時の記録と結果の統計を合成する。"""
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
        },
        "expressions": dict(base.get("expressions") or {}),
        "pairs": pairwise,
        "solver_invocations": solver_invocations,
        "stage_path": list(getattr(result, "stage_path", ()) or ()),
    }
