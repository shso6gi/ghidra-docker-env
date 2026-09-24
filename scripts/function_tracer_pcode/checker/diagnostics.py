# -*- coding: utf-8 -*-
"""結果 JSON に添付する診断ブロック（Issue #17）。

段階別の経過時間・式サイズ・ソルバ呼び出し数を機械可読に残す。

digest との関係（ここに項目を足すときの契約）:

* 診断は**判定にも semantic projection にも影響しない**。`_semantic_projection`
  はこのブロックを読まない。
* ただし診断は `EquivalenceResult.to_dict()` に含まれるので、**canonical result
  payload preimage は変わり得る**。したがって
  `canonical_result_payload_preimage_digest` も変わり得る（署名対象外ではない）。
* 「preimage は変わるが semantic projection は変わらない」ことは、同じ入力から
  session / evidence / bundle を共有しない **finalization を 2 本独立に起こして**
  確認する（`tests/unit/_finalization_support.py`、計画 v4 §9.2）。実 run 間の
  digest 一致・不一致は根拠にしない。
"""

from __future__ import annotations

import time
from contextlib import contextmanager
from typing import Any, Dict, Iterable, Iterator, Mapping, Optional

from scripts.function_tracer_pcode.checker.debug_trace import TransitionReason
from scripts.function_tracer_pcode.core.json_encoding import Reducer, exception_text
# Issue #124: StageClock は core へ移した（analysis / proof / smt からも同じ型で
# 計測し、checker が pull するため）。ここは既存 import を壊さないための再公開。
from scripts.function_tracer_pcode.core.stage_clock import (  # noqa: F401
    STAGE_TIMING_SCHEMA,
    StageClock,
    open_stage_region,
    process_age_seconds,
    region_identity_rows,
    stage_region,
)
# Issue #124 PR-124-B: 同じ計測を kill 耐性のある JSONL にも出す journal。
# 実体は `core` にある（solver worker thread と authority の finalize 区間から
# 同じ関数を呼ぶため）。ここは checker から読む既存の窓口を揃えるための再公開で、
# **結果 JSON には入らない**（journal は結果 JSON の外に置く）。
from scripts.function_tracer_pcode.core.stage_journal import (  # noqa: F401
    STAGE_JOURNAL_SCHEMA,
    StageJournal,
    active_stage_journal,
    close_active_stage_journal,
    journal_counter,
    journal_note,
    journal_stage_end,
    journal_stage_start,
    set_active_stage_journal,
)

DIAGNOSTICS_SCHEMA = "result-diagnostics-v1"

#: `diagnostics["failures"]` に載る typed failure の種類（Issue #125）。
FAILURE_ANALYSIS_LIMITATION = "analysis_limitation"
FAILURE_INTERNAL_EXCEPTION = "internal_exception"
FAILURE_SWALLOWED_EXCEPTIONS = "swallowed_exceptions"
# Issue #106 PR-106-0: pair 1 件をどこで打ち切ったか（`PairStopState` の値）。
# 打ち切っていない pair には **書かない** ので、通常の結果 JSON の key 集合は
# 変わらない。判定には読ませない診断で、control authority は台帳側が持つ。
FAILURE_PAIR_STOP_STATE = "pair_stop_state"


def record_failure_diagnostic(result: Any, kind: str, payload: Any) -> None:
    """`diagnostics["failures"][kind]` を 1 件書く（merge・fail-open）。

    既存の診断（`stages` / `phases` / `boundary_seconds` …）も、同じ `failures`
    block の他の key も消さない。診断なので、書けなくても判定は変えない。
    """
    try:
        diagnostics = dict(getattr(result, "diagnostics", None) or {})
        failures = dict(diagnostics.get("failures") or {})
        failures[kind] = payload
        diagnostics["failures"] = failures
        result.diagnostics = diagnostics
    except Exception:  # 診断は判定を壊さない
        return


def attach_failure_diagnostics(result: Any) -> None:
    """握り潰した例外の集計を `diagnostics["failures"]` へ載せる（merge・fail-open）。

    catch-all が書いた `analysis_limitation` / `internal_exception` は残したまま、
    `swallowed_exceptions` だけを足す。集計はペア 1 件の実行の冒頭で
    `reset_swallowed_exceptions()` により空にしてある。

    **この block は判定にも semantic projection にも効かない**。`to_dict()` には
    入るので canonical result payload preimage は変わり得る（この module 冒頭の
    digest 契約と同じ）。
    """
    try:
        from scripts.function_tracer_pcode.core.errors import (
            swallowed_exception_snapshot,
            swallowed_exception_total,
        )

        rows = swallowed_exception_snapshot()
        payload = {
            "total": swallowed_exception_total(),
            "by_site": rows,
        }
    except Exception as exc:  # 診断は判定を壊さない
        payload = {"error": exception_text(exc, 200)}
    record_failure_diagnostic(result, FAILURE_SWALLOWED_EXCEPTIONS, payload)


def attach_stage_timing(result: Any, clock: StageClock) -> None:
    """結果オブジェクトの診断ブロックに段階別時間を添付する（判定には効かない）。

    既存の診断（`analysis_seconds` / `phases` / `boundary_seconds` …）は保持し、
    `stages` だけを差し替える（merge）。`stages` には clock の stage / region に
    加えて、region では測れない process 全体の counter（solver）も載せる。
    counter はペアの最後に 1 回だけ pull するので、conditional lane のように
    判定確定後に動く solver 呼び出しも取りこぼさない。
    """
    try:
        payload = clock.snapshot()
    except Exception as exc:  # diagnostics never fail the verdict
        payload = {"schema": STAGE_TIMING_SCHEMA, "error": exception_text(exc, 200)}
    payload.update(process_counter_payload())
    try:
        diagnostics = dict(getattr(result, "diagnostics", None) or {})
    except Exception:
        return
    # Issue #124: 恒等式 A / B / C をその場で評価して残す。phase 行はこの時点で
    # すでに添付されている（`attach_phase_timings` は workflow の finally、
    # `attach_stage_timing` は CLI の最後）ので、結果 JSON 単体で閉包を確認できる。
    try:
        rows = region_identity_rows(payload, diagnostics.get("phases") or ())
        if rows:
            payload["identities"] = rows
    except Exception:
        pass
    try:
        diagnostics["stages"] = payload
        result.diagnostics = diagnostics
    except Exception:
        return


def process_counter_payload() -> Dict[str, Any]:
    """region では測れない process 単位の counter を集める（fail-open）。

    ``solver``: `smt/parallel.py` の 4 counter。worker thread から加算されるので
    region（contextvars）では測れない。decompile は解析の主 thread から呼ばれる
    ので region（`regions.*.decompile` / `region_totals.decompile`）で測り、
    ここには載せない。

    同じ block の `timings.solver_seconds` とは意味が違う: あちらは attempt の
    `solver_results` 行の合計で、pairwise strategy はそこへ
    `pairwise_aggregate` という合成行を 1 本だけ置く（`elapsed_time` は pairwise
    段全体で、backend 実行 1 回分ではない）。固定 subset ではその合計が、同じ
    プロセスの backend 実行時間の合計より大きい。両者を足したり比べたりしない。
    """
    payload: Dict[str, Any] = {}
    try:
        from scripts.function_tracer_pcode.smt.parallel import solver_counter_snapshot

        payload["solver"] = solver_counter_snapshot()
    except Exception:
        pass
    return payload


def expression_stats(analysis: Any) -> Dict[str, int]:
    """戻り値式とガード条件の総ノード数・最大深さ・return case 数。

    明示スタックによる反復走査（再帰しない）。深い式でも RecursionError を
    起こさず、走査中に何か失敗しても診断は判定本体に影響しない（fail-open で
    ``error`` を残す）。

    ``node_count`` は distinct な node 数で、``tree_node_count`` は木に展開した
    ときの node 数（共有部分木を親の数だけ数える）。両方を出すのは、DAG として
    小さい式が木としては桁違いに大きいことがあり、その差が rendering や
    serialization の費用そのものだから。木換算は凍結時に確定するので、未凍結の
    式が混ざると ``tree_node_count_complete`` が偽になる。``cycle_nodes`` は
    走査中に経路上の node へ戻った回数で、0 以外は凍結できない graph
    （内部不整合）を意味する。
    """
    node_count = 0
    max_depth = 0
    cycle_nodes = 0
    seen: set = set()
    active: set = set()
    stack: list = []
    returns = tuple(getattr(analysis, "returns", ()) or ())
    for ret in returns:
        stack.append((getattr(ret, "value", None), 1, False))
        for cond in getattr(ret, "conditions", ()) or ():
            stack.append((getattr(cond, "expression", None), 1, False))
    try:
        while stack:
            expr, depth, exiting = stack.pop()
            if expr is None:
                continue
            if exiting:
                active.discard(id(expr))
                continue
            if depth > max_depth:
                max_depth = depth
            key = id(expr)
            if key in active:
                # 経路上の node へ戻った = 閉路。数えるだけで展開はしない。
                cycle_nodes += 1
                continue
            if key in seen:
                # shared sub-expression: depth already accounted, do not re-expand
                continue
            seen.add(key)
            active.add(key)
            node_count += 1
            stack.append((expr, depth, True))
            for child in getattr(expr, "operands", None) or ():
                stack.append((child, depth + 1, False))
            branches = getattr(expr, "value", None)
            if isinstance(branches, (list, tuple)):
                for item in branches:
                    if isinstance(item, tuple) and len(item) == 2:
                        cond, value = item
                        stack.append((getattr(cond, "expression", None), depth + 1, False))
                        stack.append((value, depth + 1, False))
    except Exception as exc:  # diagnostics never fail the verdict
        return {
            "return_case_count": len(returns),
            "node_count": node_count,
            "max_depth": max_depth,
            "error": exception_text(exc, 200),
        }
    tree_total, tree_complete = _tree_node_total(returns)
    return {
        "return_case_count": len(returns),
        "node_count": node_count,
        "max_depth": max_depth,
        "tree_node_count": tree_total,
        "tree_node_count_complete": tree_complete,
        "cycle_nodes": cycle_nodes,
    }


def _tree_node_total(returns: Any) -> tuple:
    """凍結時に確定した木換算 node 数の合計（未凍結が混ざれば不完全）。"""

    total = 0
    complete = True
    for ret in returns:
        roots = [getattr(ret, "value", None)]
        for cond in getattr(ret, "conditions", ()) or ():
            roots.append(getattr(cond, "expression", None))
        for root in roots:
            if root is None:
                continue
            tree_size = getattr(root, "tree_size", None)
            size = tree_size() if callable(tree_size) else None
            if size is None:
                complete = False
                continue
            total += int(size)
    return total, complete


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
        """side（function1 / function2）の解析を計測する。

        Issue #124: 同じ区間を `analysis_regions.<side>` region としても開き、
        解析内部の sub-stage（trace_returns / effect_summary …）が side ごとに
        木の下へ積まれるようにする。region は clock が無ければ no-op。
        """
        started = time.perf_counter()
        try:
            with stage_region("analysis_regions"), stage_region(side):
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
            self.stats[side] = {"error": exception_text(exc, 200)}

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
            self.cache_stats[side] = {"error": exception_text(exc, 200)}

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
            self.analysis_cache_stats[side] = {"error": exception_text(exc, 200)}

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
            self.reuse_stats[side] = {"error": exception_text(exc, 200)}

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
            return {"error": exception_text(exc, 200)}


def _solver_rows(container: Any) -> Any:
    results = getattr(container, "results", None)
    if results is None and isinstance(container, Mapping):
        results = container.get("results") or container.get("all_results")
    if results is None:
        return ()
    # 列はそのまま返す（写さない）。長さの分からない列は、数える前に辿ることになるので
    # producer の不備（walker が JSON にならない値として扱う）
    if not hasattr(results, "__len__"):
        raise TypeError(f"solver results {type(results).__name__} have no length")
    return results


def _elapsed(row: Any) -> float:
    value = getattr(row, "elapsed_time", None)
    if value is None and isinstance(row, Mapping):
        value = row.get("elapsed_time")
    try:
        return float(value or 0.0)
    except (TypeError, ValueError):
        return 0.0


def result_diagnostics_payload(result: Any, *, lazy: bool = False) -> Any:
    """結果 JSON の `diagnostics`（解析時の記録と結果の統計）。

    `lazy=True` は JSON source（出力の準備が使う）: 固定の形の view で、attempt ごとの
    行は walker が 1 つずつ引き出す（`core/json_encoding`）。出力の準備が残り予算まで
    しか辿らないので、attempt が大量でも行の list を先に作らない。既定は上限なしで
    作った canonical な dict（直接の読み手用。結果 JSON と同じ値）。

    診断は判定結果に影響してはならないため、失敗しても最小のブロックを返す
    （行の generator が行う計算は、ここで合計を数える loop が先に済ませている）。
    """
    try:
        view = _ResultDiagnosticsView(result)
        if lazy:
            return view
        from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

        return RESULT_JSON_POLICY.prepare(view).value()
    except Exception as exc:
        return {"schema": DIAGNOSTICS_SCHEMA, "error": exception_text(exc, 200)}


def _attempt_rows(attempts: Any) -> Iterable[Any]:
    from scripts.function_tracer_pcode.core.json_encoding import inline, scan

    for attempt in attempts:
        container = getattr(attempt, "solver_results", None)
        # 行の合計・件数は walker が行の数を数えてから畳み込む（`_SolverTotals`）
        yield inline(
            ("attempt_id", getattr(attempt, "attempt_id", None)),
            ("phase", getattr(attempt, "phase", None)),
            ("strategy", getattr(attempt, "strategy", None)),
            ("elapsed_seconds", getattr(attempt, "elapsed_time", None)),
            ("solver_seconds", scan((container,), _SolverTotals("seconds"))),
            ("solver_invocations", scan((container,), _SolverTotals("invocations"))),
        )


class TraceTimingsView:
    """trace（解析の記録）から決まる時間の行（attempt 行と solver の合計）。

    Issue #22 PR-22-D: authority 確定 **前**（G4-b）に準備する
    （`PreparedSemanticPayload.trace_timings`）。authority 後の `diagnostics` は準備した
    値だけを読み、live な trace を辿らない。
    """

    __slots__ = ("_trace", "_attempts", "_result")

    def __init__(self, result: Any) -> None:
        trace = getattr(result, "debug_trace", None)
        self._trace = trace
        self._result = result
        self._attempts = getattr(trace, "attempts", None) or ()

    def _solver_containers(self) -> Any:
        # attempt ごとの solver 結果（attempt が無ければ結果そのものの solver 結果）
        if self._attempts:
            return (getattr(attempt, "solver_results", None) for attempt in self._attempts)
        return iter((getattr(self._result, "solver_results", None),))

    #: 行の名前（`json_items` の順）
    NAMES = ("solver_seconds", "solver_invocations", "attempts", "phase_usage")

    def source(self, name: str) -> Any:
        """行 1 つの source（walker が辿る。辿る前に何も数えない・写さない）。"""

        from scripts.function_tracer_pcode.core.json_encoding import each, scan

        if name in ("solver_seconds", "solver_invocations"):
            # 合計は walker が attempt と solver の行を 1 つずつ数えながら畳み込む（`scan`）
            what = "seconds" if name == "solver_seconds" else "invocations"
            return scan(self._solver_containers(), _SolverTotals(what))
        if name == "attempts":
            return each(_attempt_rows(self._attempts))
        if name == "phase_usage":
            # 人向けの text の phase 利用状況（debug trace を出力へ添付しないときも使う）
            phase_usage = getattr(self._trace, "phase_usage_source", None)
            return None if phase_usage is None else phase_usage()
        raise KeyError(name)

    def json_items(self):
        for name in self.NAMES:
            yield name, self.source(name)


class _SolverTotals(Reducer):
    """`scan` の reducer: solver 結果の容器（1 要素 = 1 容器）の行の秒の合計（`seconds`）か件数（`invocations`）。

    畳む前に容器の行の数を作業量へ数える。
    """

    __slots__ = ("what", "seconds", "invocations")

    def __init__(self, what: str) -> None:
        self.what = what
        self.seconds = 0.0
        self.invocations = 0

    def add(self, container: Any, *, work: Any) -> None:
        rows = _solver_rows(container)
        work.charge(len(rows))
        for row in rows:
            self.seconds += _elapsed(row)
        self.invocations += len(rows)

    def result(self, *, work: Any) -> Any:
        return round(self.seconds, 6) if self.what == "seconds" else self.invocations


def trace_timings_payload(result: Any) -> Any:
    """trace 由来の時間の行（準備済みならその値、無ければ今の pair の上限で trace から作る）。"""

    prepared = _prepared_trace_timings(result)
    if prepared is not None:
        return prepared
    from scripts.function_tracer_pcode.core.budget_policy import active_budget_policy
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    return RESULT_JSON_POLICY.prepare(
        TraceTimingsView(result), max_bytes=active_budget_policy().prepared_payload_limit(),
    ).value()


def _prepared_trace_timings(result: Any) -> Any:
    prepared = getattr(result, "prepared_semantic_payload", None)
    timings = getattr(prepared, "trace_timings", None)
    if timings is None:
        return None
    value = timings.value()
    return value if isinstance(value, dict) and "attempts" in value else {
        "solver_seconds": None, "solver_invocations": None, "attempts": value,
    }


class _ResultDiagnosticsView:
    """`diagnostics` の固定の形の view。

    C（authority 確定後に合成する診断）: 結果の診断記録（`result.diagnostics`、boundary と
    lane が書く C の値）を authority 後に読む。trace 由来の行は authority 前に準備した値
    （`trace_timings`）を読み、live な trace を読み直さない（準備していない結果だけ、
    その場で trace から作る）。判定には使わない。
    """

    __slots__ = ("_result", "_base", "_timings", "_view")

    def __init__(self, result: Any) -> None:
        self._result = result
        self._base = getattr(result, "diagnostics", None) or {}
        # 準備済みならその値。無ければ trace の行の source（この walk の予算の中で辿る。
        # 別の予算で先に準備しない）
        self._timings = _prepared_trace_timings(result)
        self._view = None if self._timings is not None else TraceTimingsView(result)

    def _timing(self, name: str) -> Any:
        if self._view is not None:
            return self._view.source(name)
        return self._timings.get(name) if isinstance(self._timings, dict) else None

    def json_items(self):
        from scripts.function_tracer_pcode.core.json_encoding import each, inline

        base = self._base
        result = self._result
        caches_empty: Dict[str, Any] = {}
        attempts = self._timing("attempts")
        yield "schema", DIAGNOSTICS_SCHEMA
        yield "timings", inline(
            ("total_seconds", getattr(result, "total_time", None)),
            ("analysis_seconds", base.get("analysis_seconds") or caches_empty),
            ("solver_seconds", self._timing("solver_seconds")),
            ("attempts", attempts),
            ("stages", base.get("stages") or caches_empty),
            ("boundary_seconds", base.get("boundary_seconds") or caches_empty),
            ("phases", base.get("phases") or ()),
        )
        yield "expressions", base.get("expressions") or caches_empty
        yield "caches", inline(
            ("callee_parameter_decompile", base.get("callee_parameter_cache") or caches_empty),
            ("callee_analysis", base.get("callee_analysis_cache") or caches_empty),
            ("callee_unbound_reuse", base.get("callee_unbound_reuse") or caches_empty),
        )
        # Issue #125: typed failure（限界 / 内部エラー / 握り潰し）の記録。
        # 判定にも semantic projection にも効かない診断。
        yield "failures", base.get("failures") or caches_empty
        yield "validated_once_entries", base.get("validated_once_entries")
        # Issue #20 PR-20-B3: conditional lane が回ったか、回ったなら何で
        # decisive にならなかったか。判定には効かない観測。
        yield "conditional_lane", base.get("conditional_lane")
        # Issue #22 PR-22-D: 式サイズ予算の値・観測した最大値・出力準備の内訳。
        # 判定には効かない観測（既定値の根拠と headroom の使用量を読むため）。
        yield "expression_budget", base.get("expression_budget")
        yield "pairs", getattr(result, "pairwise_stats", None) or caches_empty
        yield "solver_invocations", self._timing("solver_invocations")
        yield "stage_path", getattr(result, "stage_path", ()) or ()


PHASE_TIMING_SCHEMA = "phase-timing-v1"

# 「phase は実行したが型修正を何も適用しなかった」ことを表す機械可読な理由。
# 既存の attempt 遷移理由と同じ語彙を使う（新しい語彙を作らない）。
PHASE_SKIPPED_NO_CHANGES = TransitionReason.NO_CHANGES.value

# 1 phase の内訳として計測する区間。`total` は phase 全体の実測値なので、
# 内訳の合計とは一致しない（計測していない区間の分だけ total の方が大きい）。
PHASE_TIMING_SEGMENTS = (
    "phase_fix",
    "analysis",
    "hypothesis_replay",
    "recurrence_refresh",
    "stage_plan",
)


def unknown_reason_ids(result: Any) -> list:
    """結果が保持する UNKNOWN reason id を安定順で返す（診断専用）。

    phase 前後の reason 集合を比べるための観測で、判定にも reason 集合にも
    影響しない。壊れた入力でも例外を出さず空リストを返す。
    """
    if result is None:
        return []
    try:
        ids = set()
        for reason in getattr(result, "unknown_reasons", None) or ():
            reason_id = getattr(reason, "reason_id", None)
            if reason_id is None and isinstance(reason, Mapping):
                reason_id = reason.get("reason_id")
            reason_id = getattr(reason_id, "value", reason_id)
            if reason_id:
                ids.add(str(reason_id))
        return sorted(ids)
    except Exception:
        return []


class PhaseTimeline:
    """retry phase 1 件ごとの内訳時間と reason 遷移を記録する（Issue #107）。

    `#107-B` 以降の削減余地を測るための観測専用ブロックであり、判定結果にも
    最終 UNKNOWN reason 集合にも関与しない。``begin()`` から ``end()`` までを
    1 phase とし、``measure()`` で囲んだ区間の秒数を種別ごとに加算する。
    診断なので、記録に失敗しても例外を呼び出し側へ出さない。
    """

    def __init__(self) -> None:
        self.phases: list = []
        self._current: Optional[Dict[str, Any]] = None
        self._started: float = 0.0

    def begin(
        self,
        phase: str,
        *,
        retry_name: str = "",
        attempt_id: Optional[int] = None,
        reason_before: Iterable[str] = (),
    ) -> None:
        """phase の記録を開始する（閉じ忘れた記録があれば先に閉じる）。

        ``attempt_id`` は、この phase の結果が記録される attempt の id。phase 行と
        ``debug_trace.attempts[]`` の対応をこの id で固定し、位置合わせのような
        不安定な対応付けを作らない。attempt を必ず生成する phase だけがここで id を
        渡せる。生成するか未確定な phase は渡さず、確定した時点で
        ``record_attempt_id()`` で結び付ける（存在しない attempt の id を予約すると、
        後続 phase が使う id と衝突して別 attempt を指してしまう）。
        """
        try:
            if self._current is not None:
                self.end()
            self._current = {
                "phase": str(phase),
                "retry_name": str(retry_name),
                "attempt_id": attempt_id,
                # 型修正の適用という概念が無い attempt（P0）は None のまま。
                # False は「phase を実行したが何も適用されなかった」を意味する。
                "applied": None,
                "changed_sides": [],
                "reanalyzed_sides": [],
                "seconds": {segment: 0.0 for segment in PHASE_TIMING_SEGMENTS},
                "analysis_seconds_by_side": {},
                "reason_before": [str(reason) for reason in reason_before],
                "reason_after": [],
            }
            self._started = time.perf_counter()
        except Exception:
            self._current = None

    def record_applied(
        self,
        applied: bool,
        changed_binary1: bool = False,
        changed_binary2: bool = False,
        *,
        retry_name: Optional[str] = None,
    ) -> None:
        """型修正が適用されたか、どちら側の解析ビューが変わったかを記録する。"""
        current = self._current
        if current is None:
            return
        try:
            current["applied"] = bool(applied)
            if retry_name:
                current["retry_name"] = str(retry_name)
            changed = []
            if changed_binary1:
                changed.append("function1")
            if changed_binary2:
                changed.append("function2")
            current["changed_sides"] = changed
        except Exception:
            return

    def record_phase_result(self, phase_result: Any) -> None:
        """``PhaseResult`` から適用状況を記録する。"""
        if phase_result is None:
            return
        self.record_applied(
            getattr(phase_result, "applied", False),
            getattr(phase_result, "changed_binary1", False),
            getattr(phase_result, "changed_binary2", False),
            retry_name=getattr(phase_result, "retry_name", None),
        )

    def record_attempt_id(self, attempt_id: Optional[int]) -> None:
        """この phase の結果を記録する attempt が確定した時点で id を結び付ける。"""
        current = self._current
        if current is None:
            return
        try:
            current["attempt_id"] = attempt_id
        except Exception:
            return

    def record_reanalyzed_side(self, side: str) -> None:
        """この phase で fresh 解析し直した側を記録する。"""
        current = self._current
        if current is None:
            return
        try:
            sides = current["reanalyzed_sides"]
            if side not in sides:
                sides.append(str(side))
        except Exception:
            return

    def add(self, segment: str, seconds: float, *, side: Optional[str] = None) -> None:
        """内訳区間へ秒数を加算する（同じ区間を複数回囲めば合算）。"""
        current = self._current
        if current is None:
            return
        try:
            value = max(0.0, float(seconds))
        except (TypeError, ValueError):
            return
        try:
            totals = current["seconds"]
            totals[segment] = totals.get(segment, 0.0) + value
            if side is not None:
                by_side = current["analysis_seconds_by_side"]
                by_side[side] = by_side.get(side, 0.0) + value
        except Exception:
            return

    @contextmanager
    def measure(self, segment: str, *, side: Optional[str] = None) -> Iterator[None]:
        """区間の経過時間を計測して加算する。``begin()`` 前なら何も記録しない。"""
        started = time.perf_counter()
        try:
            yield
        finally:
            self.add(segment, time.perf_counter() - started, side=side)

    def end(self, *, reason_after: Iterable[str] = ()) -> Optional[Dict[str, Any]]:
        """phase の記録を閉じ、phase 全体の経過時間と後 reason を確定する。

        閉じた行の snapshot を返す。呼び出し側はそれをそのまま attempt 記録へ渡せる
        （phase 行と attempt が同じ観測から作られることを構成で保証する）。
        """
        current = self._current
        if current is None:
            return None
        try:
            current["seconds"]["total"] = max(0.0, time.perf_counter() - self._started)
            current["reason_after"] = [str(reason) for reason in reason_after]
            if current.get("applied") is False:
                current["skipped_reason"] = PHASE_SKIPPED_NO_CHANGES
            self.phases.append(current)
            return self._snapshot_phase(current)
        except Exception:
            return None
        finally:
            self._current = None

    def snapshot(self) -> list:
        """結果 JSON の診断ブロックへそのまま入る phase 行のリスト。"""
        try:
            return [self._snapshot_phase(phase) for phase in self.phases]
        except Exception as exc:
            return [{"error": exception_text(exc, 200)}]

    @staticmethod
    def _snapshot_phase(phase: Mapping[str, Any]) -> Dict[str, Any]:
        return {
            "schema": PHASE_TIMING_SCHEMA,
            "phase": phase.get("phase"),
            "retry_name": phase.get("retry_name"),
            "attempt_id": phase.get("attempt_id"),
            "applied": phase.get("applied"),
            "skipped_reason": phase.get("skipped_reason"),
            "changed_sides": list(phase.get("changed_sides") or ()),
            "reanalyzed_sides": list(phase.get("reanalyzed_sides") or ()),
            "seconds": {
                key: round(value, 6) for key, value in (phase.get("seconds") or {}).items()
            },
            "analysis_seconds_by_side": {
                side: round(value, 6)
                for side, value in (phase.get("analysis_seconds_by_side") or {}).items()
            },
            "reason_before": list(phase.get("reason_before") or ()),
            "reason_after": list(phase.get("reason_after") or ()),
        }


def phase_timeline_of(checker: Any) -> PhaseTimeline:
    """checker に紐づく phase timeline を返す。

    workflow を経由しない呼び出し（単体テストや `check()` 直呼び）では記録先が
    無いので、``begin()`` されていない timeline を返して no-op にする。
    """
    timeline = getattr(checker, "_phase_timeline", None)
    if isinstance(timeline, PhaseTimeline):
        return timeline
    return PhaseTimeline()


def attach_phase_timings(result: Any, timeline: Optional[PhaseTimeline]) -> None:
    """結果の診断ブロックへ phase 別の内訳時間を添付する（判定には効かない）。"""
    if result is None or timeline is None:
        return
    try:
        phases = timeline.snapshot()
        if not phases:
            return
        diagnostics = dict(getattr(result, "diagnostics", None) or {})
        diagnostics["phases"] = phases
        result.diagnostics = diagnostics
    except Exception:
        return
