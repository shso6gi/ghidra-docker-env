# -*- coding: utf-8 -*-
"""解析の期限と process の期限の間の余裕（margin）の実測（Issue #106 PR-106-B）。

runner の `ANALYSIS_TIMEOUT_MARGIN`（`runner_timeout_policy`）は、期限で打ち切った pair が
process の期限より前に終わるための余裕。その根拠をここで run の出力から測る。判定にも
runner の policy にも入力を渡さない（報告だけを作る）。

期限で打ち切った pair 1 件の時間を、重ならない連続した区間に分ける（二重計上しない）:

=================== ==================================================================
区間                端点（読む file）
=================== ==================================================================
``pre``             supervisor の開始 → 期限の起点（`check_from_binaries` の入口）。JVM 起動・
                    project open・import・auto analyze。起点 = trip の時刻 − trip の経過秒
``overrun``         期限 → trip（`deadline_tripped` の ``elapsed_seconds − budget_seconds``）。
                    checkpoint の無い区間・止まるまで戻らない処理（solver の停止と join を含む）
``post_trip``       trip → 最後の journal event（通常は ``result_emit`` の終わり）。限界の帰属・
                    結果の組み立て・出力の準備・``connector.finish``・conditional lane・
                    ``close_programs``・結果 JSON の出力。内訳は下の ``post_trip_parts``
``tail``            最後の journal event → runner が pair の終わりを観測した時刻。JVM の停止・
                    process の終了・supervisor の pair status の durable write・回収
=================== ==================================================================

``needed`` = supervisor 上の wall − 期限 = ``pre + overrun + post_trip + tail``（恒等式、
端点はすべて同じ pair の記録）。``ANALYSIS_TIMEOUT + margin <= PAIR_PROCESS_TIMEOUT`` を守る
margin は ``needed`` に supervisor の stack dump の先行時間（`pair_stack_dump_lead`）を足した
ものより大きくなければならない（先行時間の窓の中で終わると #204 の経路に入る）。

``post_trip_parts``: ``unwind``（trip → ``authority_finalize`` の開始。限界の帰属・組み立て・
出力の準備）、``authority_finalize``（``connector.finish``・receipt）、``conditional_lane``、
``close_programs``、``result_emit``、``other``（残り）。journal の stage の区間から取る。

wall は runner の `.runtime-metrics/<pair>.runtime.json`（GNU time が測った supervisor の寿命）、
journal は `<pair>.stage.jsonl`（`pair-stage-journal-v1`）。runtime receipt の無い pair（Neq の
runner は書かない、#160）は journal だけで測れる ``overrun`` / ``post_trip`` と、child の journal
の開始からの ``pre_child`` だけを持ち、``pre`` / ``tail`` / ``needed`` には入れない。期限を持たない pair・trip の無い
pair・process TIMEOUT の pair は区間に入れず、件数だけ別に数える（後者は margin が足りなかった
可能性の証拠として一覧を残す）。観測した最大値は保証ではない（負荷・入力が変われば越え得る）。
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

SCHEMA = "deadline-margin-summary-v1"
PAIR_STATUS_SUFFIX = ".pair-status.json"
TRIP_NOTE = "deadline_tripped"
INTERVALS = ("pre", "pre_child", "overrun", "post_trip", "tail", "needed")
POST_TRIP_STAGES = ("authority_finalize", "conditional_lane", "close_programs", "result_emit")
POST_TRIP_PARTS = ("unwind",) + POST_TRIP_STAGES + ("other",)
#: p99 を名乗る最小の件数（それ未満は max と median / p90 だけ）
P99_MIN_SAMPLES = 100


@dataclass(frozen=True)
class PairMargin:
    key: str
    outcome: str
    budget_seconds: float
    trip_stage: str
    wall_seconds: Optional[float]
    pre: Optional[float]
    pre_child: float
    overrun: float
    post_trip: float
    tail: Optional[float]
    needed: Optional[float]
    post_trip_parts: Dict[str, float] = field(default_factory=dict)


@dataclass
class MarginReport:
    roots: List[str]
    pairs: List[PairMargin]
    #: 期限を持たない run（manifest の analysis_timeout が 0）の pair。key の無い manifest
    #: （PR-106-B より前の計測 run）は trip の有無で読む
    without_deadline: int = 0
    #: 期限はあったが trip しなかった（期限内に終わった）pair
    finished_before_deadline: int = 0
    #: process TIMEOUT（supervisor の wall clock）で終わった pair
    process_timeouts: List[str] = field(default_factory=list)
    #: 区間を作れなかった pair（journal / runtime receipt の欠け）と理由
    unreadable: List[Tuple[str, str]] = field(default_factory=list)
    pair_stack_dump_lead_seconds: Optional[float] = None


def _percentile(values: Sequence[float], q: float) -> float:
    """nearest-rank の百分位。"""

    ordered = sorted(values)
    rank = max(1, math.ceil(q * len(ordered)))
    return ordered[rank - 1]


def describe(values: Sequence[float]) -> Dict[str, Any]:
    if not values:
        return {"n": 0}
    row: Dict[str, Any] = {
        "n": len(values),
        "median": round(_percentile(values, 0.5), 3),
        "p90": round(_percentile(values, 0.9), 3),
        "max": round(max(values), 3),
    }
    if len(values) >= P99_MIN_SAMPLES:
        row["p99"] = round(_percentile(values, 0.99), 3)
    return row


def _read_key_values(path: Path) -> Dict[str, str]:
    fields: Dict[str, str] = {}
    if not path.is_file():
        return fields
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            fields[key.strip()] = value.strip()
    return fields


def _journal_rows(path: Path) -> List[Mapping[str, Any]]:
    rows = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            row = json.loads(line)
        except ValueError:
            continue  # a torn last line of a killed process
        if isinstance(row, dict):
            rows.append(row)
    return rows


def _current_segment(rows: Sequence[Mapping[str, Any]]) -> List[Mapping[str, Any]]:
    """最後の execution（`pair_journal_opened` の最後から）だけを読む。"""

    start = 0
    for index, row in enumerate(rows):
        payload = row.get("payload")
        if row.get("event") == "note" and isinstance(payload, Mapping) \
                and payload.get("note") == "pair_journal_opened":
            start = index
    return list(rows[start:])


def pair_margin(
    key: str, outcome: str, journal: Sequence[Mapping[str, Any]],
    runtime: Optional[Mapping[str, Any]],
) -> Optional[PairMargin]:
    """1 pair の区間（trip の無い pair は ``None``）。欠けた記録は ``ValueError``。

    ``runtime`` が ``None``（runtime receipt の無い pair）なら supervisor 側の区間は持たない。
    """

    rows = _current_segment(journal)
    trips = [
        row for row in rows
        if row.get("event") == "note" and isinstance(row.get("payload"), Mapping)
        and row["payload"].get("note") == TRIP_NOTE
    ]
    if not trips:
        return None
    trip = trips[0]
    payload = trip["payload"]
    budget = float(payload["budget_seconds"])
    elapsed = float(payload["elapsed_seconds"])
    trip_mono = float(trip["t_monotonic"])
    trip_epoch = float(trip["t_epoch"])
    last = max(rows, key=lambda row: float(row.get("t_monotonic") or 0.0))
    last_mono = float(last["t_monotonic"])
    last_epoch = trip_epoch + (last_mono - trip_mono)
    first_mono = min(float(row.get("t_monotonic") or trip_mono) for row in rows)
    origin_epoch = trip_epoch - elapsed
    pre_child = (trip_mono - elapsed) - first_mono
    overrun = elapsed - budget
    post_trip = last_mono - trip_mono
    wall = pre = tail = needed = None
    if runtime is not None:
        wall = float(runtime["elapsed_seconds"])
        finished = float(runtime["finished_at_epoch"])
        pre = round(origin_epoch - (finished - wall), 3)
        tail = round(finished - last_epoch, 3)
        needed = round(wall - budget, 3)
    parts = {name: 0.0 for name in POST_TRIP_PARTS}
    finalize_starts = [
        float(row["t_monotonic"]) for row in rows
        if row.get("event") == "stage_start" and row.get("stage") == "authority_finalize"
        and float(row["t_monotonic"]) >= trip_mono
    ]
    parts["unwind"] = (min(finalize_starts) if finalize_starts else last_mono) - trip_mono
    for row in rows:
        if (row.get("event") == "stage_end" and row.get("stage") in POST_TRIP_STAGES
                and float(row["t_monotonic"]) >= trip_mono):
            parts[row["stage"]] += float(row.get("seconds") or 0.0)
    parts["other"] = post_trip - sum(value for name, value in parts.items() if name != "other")
    return PairMargin(
        key=key, outcome=outcome, budget_seconds=budget,
        trip_stage=str(payload.get("stage")), wall_seconds=wall,
        pre=pre, pre_child=round(pre_child, 3), overrun=round(overrun, 3),
        post_trip=round(post_trip, 3), tail=tail, needed=needed,
        post_trip_parts={name: round(value, 3) for name, value in parts.items()},
    )


def _pair_files(status: Path) -> Tuple[Path, Path]:
    stem = status.name[: -len(PAIR_STATUS_SUFFIX)]
    return (
        status.with_name(stem + ".stage.jsonl"),
        status.parent / ".runtime-metrics" / (stem + ".runtime.json"),
    )


def summarize_roots(roots: Iterable[Path]) -> MarginReport:
    root_list = [Path(root) for root in roots]
    report = MarginReport(roots=[str(root) for root in root_list], pairs=[])
    for root in root_list:
        manifest = _read_key_values(root / "run_manifest.txt")
        lead = manifest.get("pair_stack_dump_lead", "").rstrip("s")
        if lead:
            report.pair_stack_dump_lead_seconds = float(lead)
        deadline = manifest.get("analysis_timeout")
        for status in sorted(root.rglob("*" + PAIR_STATUS_SUFFIX)):
            key = str(status.relative_to(root))[: -len(PAIR_STATUS_SUFFIX)]
            try:
                outcome = str(json.loads(status.read_text(encoding="utf-8"))
                              .get("canonical_outcome"))
            except (OSError, ValueError) as exc:
                report.unreadable.append((key, f"pair status: {exc}"))
                continue
            if outcome == "TIMEOUT":
                report.process_timeouts.append(key)
                continue
            if deadline == "0":
                report.without_deadline += 1
                continue
            journal_path, runtime_path = _pair_files(status)
            try:
                runtime = (
                    json.loads(runtime_path.read_text(encoding="utf-8"))
                    if runtime_path.is_file() else None
                )
                margin = pair_margin(key, outcome, _journal_rows(journal_path), runtime)
            except (OSError, ValueError, KeyError, TypeError) as exc:
                report.unreadable.append((key, f"{type(exc).__name__}: {exc}"))
                continue
            if margin is None:
                report.finished_before_deadline += 1
            else:
                report.pairs.append(margin)
    return report


def report_dict(report: MarginReport) -> Dict[str, Any]:
    intervals = {
        name: describe([
            getattr(pair, name) for pair in report.pairs if getattr(pair, name) is not None
        ])
        for name in INTERVALS
    }
    parts = {
        name: describe([pair.post_trip_parts.get(name, 0.0) for pair in report.pairs])
        for name in POST_TRIP_PARTS
    }
    sum_of_max = round(sum(
        intervals[name].get("max", 0.0) for name in ("pre", "overrun", "post_trip", "tail")
    ), 3)
    return {
        "schema": SCHEMA,
        "roots": report.roots,
        "tripped_pairs": len(report.pairs),
        "tripped_pairs_without_runtime_receipt": sum(
            1 for pair in report.pairs if pair.needed is None
        ),
        "finished_before_deadline": report.finished_before_deadline,
        "without_deadline": report.without_deadline,
        "process_timeouts": report.process_timeouts,
        "unreadable": [list(row) for row in report.unreadable],
        "pair_stack_dump_lead_seconds": report.pair_stack_dump_lead_seconds,
        "intervals": intervals,
        "post_trip_parts": parts,
        "sum_of_interval_max": sum_of_max,
        "pairs": [asdict(pair) for pair in report.pairs],
    }


def format_report(payload: Mapping[str, Any]) -> str:
    lines = [
        "Deadline margin summary:",
        f"  tripped pairs: {payload['tripped_pairs']}"
        f" (without a runtime receipt: {payload['tripped_pairs_without_runtime_receipt']})"
        f" (finished before the deadline: {payload['finished_before_deadline']},"
        f" no deadline: {payload['without_deadline']},"
        f" process TIMEOUT: {len(payload['process_timeouts'])},"
        f" unreadable: {len(payload['unreadable'])})",
        f"  stack dump lead: {payload['pair_stack_dump_lead_seconds']}",
    ]
    for title, table in (("intervals", payload["intervals"]),
                         ("post_trip parts", payload["post_trip_parts"])):
        lines.append(f"  {title}:")
        for name, row in table.items():
            stats = " ".join(f"{key}={value}" for key, value in row.items())
            lines.append(f"    - {name}: {stats}")
    lines.append(f"  sum of interval max: {payload['sum_of_interval_max']}")
    for key in payload["process_timeouts"]:
        lines.append(f"  process TIMEOUT: {key}")
    return "\n".join(lines)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("roots", nargs="+", type=Path, help="run result trees (one per half)")
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args(argv)
    payload = report_dict(summarize_roots(args.roots))
    print(format_report(payload))
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(payload, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
