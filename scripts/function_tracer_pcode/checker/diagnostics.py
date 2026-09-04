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

    def snapshot(self) -> Dict[str, Any]:
        try:
            return {
                "analysis_seconds": {side: round(value, 6) for side, value in self.seconds.items()},
                "expressions": {side: dict(stats) for side, stats in self.stats.items()},
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
        },
        "expressions": dict(base.get("expressions") or {}),
        "pairs": pairwise,
        "solver_invocations": solver_invocations,
        "stage_path": list(getattr(result, "stage_path", ()) or ()),
    }
