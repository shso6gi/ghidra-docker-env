# -*- coding: utf-8 -*-
"""解析の期限と process の期限の間の余裕（margin）の実測と、採用式（Issue #106 PR-106-B）。

runner の `ANALYSIS_TIMEOUT_MARGIN`（`runner_timeout_policy`）は、期限で打ち切った pair が
process の期限より前（supervisor が stack dump の SIGUSR1 を送る lead window の手前）に
終わるための余裕。その根拠を run の出力から測る。判定にも runner の policy にも入力を渡さない
（報告だけを作る）。

## 時計と端点（すべて supervisor と child が共有する monotonic 時計）

supervisor は barrier を外した瞬間に ``deadline = monotonic + PAIR_PROCESS_TIMEOUT`` を 1 回だけ
決め、診断の sidecar（`<pair>.stack-dump.status.json`）に ``deadline_monotonic`` /
``timeout_seconds`` / ``lead_seconds`` と、child の終了を観測した時刻
（``cancel_linearized_offset_seconds``、deadline からの相対）を残す。Eq / Neq の両方の runner が
書く。GNU time の wall（supervisor の起動と、child の終了後の durable write を含む）は使わない:
process の期限に数えられるのは barrier から child の終了までだけ。

期限で打ち切った pair 1 件を、重ならない連続した区間に分ける:

=================== ==================================================================
区間                端点
=================== ==================================================================
``pre``             process の期限の起点 → 解析の期限の起点（trip 時刻 − trip の経過秒）。CLI の
                    起動・JVM・project open・import・auto analyze
``overrun``         解析の期限 → trip（``elapsed_seconds − budget_seconds``）。checkpoint の
                    無い区間・止まるまで戻らない処理（協調的な solver の停止と join を含む）。
                    負の値は「残りが sub-operation の余裕を切ったので始めなかった」
``post_trip``       trip → journal の最後の event。限界の帰属・組み立て・出力の準備・
                    ``connector.finish``・conditional lane・``close_programs``・結果 JSON
``tail``            journal の最後の event → supervisor が child の終了を観測。JVM の停止・
                    interpreter の終了
=================== ==================================================================

``needed = child の終了 − process の期限の起点 − 解析の期限 = pre + overrun + post_trip + tail``。

``post_trip_parts`` は journal の stage の区間（`core.stage_journal_reader.stage_intervals`）と
trip 後の窓の **交差** を、窓の各瞬間をその時点で最も内側に開いていた stage へ 1 回だけ
割り当てて求める。どの stage にも入らない時間は ``other``。各値は 0 以上で、和は
``post_trip`` に一致する（処理の順序・入れ子・trip より前に始まった stage に依らない）。

## 終了の分類（独自の規則を持たない）

TIMEOUT の pair は `timeout_hotspot_summary`（`timeout_kind` の owner）が同じ証拠から分類する:
``PROCESS_DEADLINE_KINDS``（supervisor の wall clock）は ``process_timeout``、
``child_solver_timeout``（checker 自身の terminal timeout）は ``solver_timeout``、
証拠の足りないものは ``timeout_unclassified``。canonical outcome の無い pair は
``termination_invalid``。child の終了より先に SIGUSR1 の送信が始まった pair は
``entered_lead_window``（margin が足りなかった証拠）。

## 観測と判定の分担

この module は **観測** だけを作る: run ごとの事実（`RunFacts`: 期限・process の期限・並列度・
commit・sample の母集団）と、pair ごとの終了の分類・期限で打ち切ったか（読めなければ理由）・
区間ごとの値か欠測の理由（`PairObservation`）。区間は 1 つずつ別に求め、ある区間が測れない
ことは他の区間を消さない。どの run をどの pool に入れてよいか・採用式・判定（holds /
violated / undetermined）は `reporting/deadline_margin_acceptance.py` だけが決める（集計の
前に決まる規則で、結果を見て標本を除かない）。

* 観測した最大は保証ではない（負荷・入力が変われば越え得る）。
* ``lead`` は supervisor が SIGUSR1 を送る先行時間。child がその窓の中で終わると #204 の経路に
  入るので、margin の中に取る。SIGTERM の後の grace（kill-after）は process の期限の **後** なので
  margin には使えない（入れない）。
* 止められない worker（能力を宣言しない backend）の join には上限が無い: その pair は
  supervisor の TIMEOUT（fallback）になる。margin には入れない。
"""


from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.stage_journal_reader import (
    SUMMARY_READ_LIMIT_BYTES,
    JournalSegment,
    read_stage_journal,
    select_current_segment,
    stage_intervals,
)
from scripts.function_tracer_pcode.reporting import deadline_margin_acceptance as acceptance
from scripts.function_tracer_pcode.reporting.pair_outcomes import (
    OUTCOME_INVALID,
    OUTCOME_MISSING,
    PAIR_STATUS_SUFFIX,
    iter_pair_outcomes,
)
from scripts.function_tracer_pcode.reporting.timeout_hotspot_summary import (
    KIND_CHILD_SOLVER_TIMEOUT,
    PROCESS_DEADLINE_KINDS,
    TIMEOUT_OUTCOME,
    load_pair_evidence,
)

SCHEMA = "deadline-margin-summary-v3"
TRIP_NOTE = "deadline_tripped"
#: margin の和に入る区間（``needed`` は確認用の合計）。採用式の項の表（acceptance）が唯一の一覧
MARGIN_INTERVALS = tuple(acceptance.TERM_POOLS)
INTERVALS = MARGIN_INTERVALS + ("needed",)
POST_TRIP_STAGES = ("authority_finalize", "conditional_lane", "close_programs", "result_emit")
POST_TRIP_PARTS = POST_TRIP_STAGES + ("other",)
#: p99 を名乗る最小の件数（それ未満は max と median / p90 だけ）
P99_MIN_SAMPLES = 100


@dataclass(frozen=True)
class RunFacts:
    """1 run（result tree の 1 half）の事実。読めない項目は ``None`` と理由。"""

    root: str
    #: 解析の期限（秒）。manifest の ``analysis_timeout``、無ければ trip の note の
    #: ``budget_seconds``（全 pair で 1 つの値のときだけ）
    deadline_seconds: Optional[float]
    deadline_off: bool
    deadline_note: str
    pair_process_timeout_seconds: Optional[float]
    parallel_jobs: Optional[int]
    git_commit: Optional[str]
    git_dirty: Optional[bool]
    samples: frozenset

    def to_dict(self) -> Dict[str, Any]:
        return {
            "root": self.root, "deadline_seconds": self.deadline_seconds,
            "deadline_off": self.deadline_off, "deadline_note": self.deadline_note,
            "pair_process_timeout_seconds": self.pair_process_timeout_seconds,
            "parallel_jobs": self.parallel_jobs, "git_commit": self.git_commit,
            "git_dirty": self.git_dirty, "samples": len(self.samples),
        }


@dataclass(frozen=True)
class PairObservation:
    key: str
    outcome: str
    #: `deadline_margin_acceptance.TERMINATION_*`
    termination: str
    timeout_kind: Optional[str]
    #: 期限で打ち切った（``True``）/ 打ち切らずに終わった（``False``）/ 読めない（``None``）
    cut: Optional[bool]
    cut_unknown_reason: Optional[str] = None
    #: 測れた区間（``MARGIN_INTERVALS`` の部分集合）と測れなかった区間の理由（打ち切った pair だけ）
    values: Dict[str, float] = field(default_factory=dict)
    missing: Dict[str, str] = field(default_factory=dict)
    lead_seconds: Optional[float] = None
    needed: Optional[float] = None
    entered_lead_window: bool = False
    budget_seconds: Optional[float] = None
    trip_stage: Optional[str] = None
    post_trip_parts: Dict[str, float] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "key": self.key, "outcome": self.outcome, "termination": self.termination,
            "timeout_kind": self.timeout_kind, "cut": self.cut,
            "cut_unknown_reason": self.cut_unknown_reason, "values": dict(self.values),
            "missing": dict(self.missing), "lead_seconds": self.lead_seconds,
            "needed": self.needed, "entered_lead_window": self.entered_lead_window,
            "budget_seconds": self.budget_seconds, "trip_stage": self.trip_stage,
            "post_trip_parts": dict(self.post_trip_parts),
        }


@dataclass(frozen=True)
class RunObservation:
    facts: RunFacts
    pairs: Tuple[PairObservation, ...]


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


def _seconds(text: Optional[str]) -> Optional[float]:
    if text is None or text == "":
        return None
    try:
        value = float(text[:-1] if text.endswith("s") else text)
    except ValueError:
        return None
    return value if math.isfinite(value) else None


def _sidecar_number(sidecar: Optional[Mapping[str, Any]], key: str) -> Tuple[Optional[float], str]:
    if not isinstance(sidecar, Mapping):
        return None, "no stack-dump status sidecar"
    value = sidecar.get(key)
    if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value):
        return None, f"sidecar has no usable {key}"
    return float(value), ""


def _tripped(segment: JournalSegment) -> List[Any]:
    return [
        row for row in segment.rows
        if row.event == "note" and row.payload.get("note") == TRIP_NOTE
    ]


def post_trip_parts(
    segment: JournalSegment, start: float, end: float,
) -> Dict[str, float]:
    """``[start, end]`` を stage の区間との交差で分ける（各値 >= 0、和 = end − start）。

    窓の各瞬間は、その時点で開いていた区間のうち最後に開いたもの（最も内側）にだけ
    割り当てる。``POST_TRIP_STAGES`` 以外の stage の中の時間は ``other``。
    """

    parts = {name: 0.0 for name in POST_TRIP_PARTS}
    clipped = []
    for interval in stage_intervals(segment):
        lo = max(interval.start, start)
        hi = min(end if interval.end is None else interval.end, end)
        if hi > lo:
            clipped.append((lo, hi, interval))
    cuts = sorted({start, end, *(lo for lo, _, _ in clipped), *(hi for _, hi, _ in clipped)})
    for lo, hi in zip(cuts, cuts[1:]):
        open_now = [interval for a, b, interval in clipped if a <= lo and hi <= b]
        owner = max(open_now, key=lambda interval: interval.start).stage if open_now else None
        parts[owner if owner in POST_TRIP_STAGES else "other"] += hi - lo
    return parts


def termination_of(outcome: str, timeout_kind: Optional[str]) -> str:
    """終了の分類（`timeout_kind` の owner の分類をそのまま写す）。"""

    if outcome in (OUTCOME_INVALID, OUTCOME_MISSING):
        return acceptance.TERMINATION_INVALID
    if outcome != TIMEOUT_OUTCOME:
        return acceptance.TERMINATION_RESOLVED
    if timeout_kind in PROCESS_DEADLINE_KINDS:
        return acceptance.TERMINATION_PROCESS_TIMEOUT
    if timeout_kind == KIND_CHILD_SOLVER_TIMEOUT:
        return acceptance.TERMINATION_SOLVER_TIMEOUT
    return acceptance.TERMINATION_TIMEOUT_UNCLASSIFIED


def observe_pair(
    key: str, outcome: str, *, termination: str, timeout_kind: Optional[str],
    segment: Optional[JournalSegment], segment_reason: Optional[str],
    sidecar: Optional[Mapping[str, Any]],
) -> PairObservation:
    """1 pair の観測。区間は 1 つずつ別に求め、測れない区間は理由を残す（0 で埋めない）。"""

    entered = bool(
        isinstance(sidecar, Mapping) and sidecar.get("signal_sent") is True
        and sidecar.get("cancel_linearized_offset_seconds") is None
    )
    base = dict(key=key, outcome=outcome, termination=termination,
                timeout_kind=timeout_kind, entered_lead_window=entered)
    if segment is None:
        return PairObservation(cut=None, cut_unknown_reason=f"journal: {segment_reason}", **base)
    trips = _tripped(segment)
    if not trips:
        return PairObservation(cut=False, **base)
    trip = trips[0]
    values: Dict[str, float] = {}
    missing: Dict[str, str] = {}
    try:
        budget: Optional[float] = float(trip.payload["budget_seconds"])
        elapsed: Optional[float] = float(trip.payload["elapsed_seconds"])
        trip_at: Optional[float] = float(trip.t_monotonic)
        note_problem = ""
    except (KeyError, TypeError, ValueError) as exc:
        budget = elapsed = trip_at = None
        note_problem = f"deadline_tripped note is incomplete: {exc!r}"
    times = [float(row.t_monotonic) for row in segment.rows if row.t_monotonic is not None]
    last = max(times) if times else None
    deadline, deadline_problem = _sidecar_number(sidecar, "deadline_monotonic")
    process, process_problem = _sidecar_number(sidecar, "timeout_seconds")
    lead, _ = _sidecar_number(sidecar, "lead_seconds")
    offset, offset_problem = _sidecar_number(sidecar, "cancel_linearized_offset_seconds")
    if entered:
        offset_problem = "the child exit was not observed before the stack-dump send"
    child_exit = None if deadline is None or offset is None or entered else deadline + offset
    origin = None if deadline is None or process is None else deadline - process

    def put(name: str, value: Optional[float], problem: str) -> None:
        if value is None:
            missing[name] = problem
        else:
            values[name] = round(value, 3)

    if note_problem:
        for name in acceptance.TERM_POOLS:
            missing[name] = note_problem
    else:
        put("pre", None if origin is None else trip_at - elapsed - origin,
            deadline_problem or process_problem)
        put("overrun", elapsed - budget, "")
        put("post_trip", None if last is None else last - trip_at, "journal has no timestamps")
        put("tail", None if child_exit is None or last is None else child_exit - last,
            deadline_problem or offset_problem or "journal has no timestamps")
    for name in acceptance.TERM_POOLS:
        if name not in values and name not in missing:
            missing[name] = "no observer for this interval"
    needed = None
    if not missing and child_exit is not None and origin is not None and budget is not None:
        needed = round(child_exit - origin - budget, 3)
    parts = {}
    if trip_at is not None and last is not None:
        parts = {name: round(value, 3)
                 for name, value in post_trip_parts(segment, trip_at, last).items()}
    return PairObservation(
        cut=True, values=values, missing=missing, lead_seconds=lead, needed=needed,
        budget_seconds=budget, trip_stage=None if note_problem else str(trip.payload.get("stage")),
        post_trip_parts=parts, **base,
    )


def _sample_of(key: str) -> str:
    """pair の key（``<sample identity>/<function>/<pair stem>``）の sample identity。"""

    return str(Path(key).parent.parent)


def observe_run(root: Path) -> RunObservation:
    """result tree（1 half）の観測。pair を 1 件も除かない。"""

    root = Path(root)
    manifest = _read_key_values(root / "run_manifest.txt")
    pairs: List[PairObservation] = []
    for record in iter_pair_outcomes(root):
        key = str(Path(record.status_path).relative_to(root))[: -len(PAIR_STATUS_SUFFIX)]
        evidence = load_pair_evidence(record.status_path)
        kind = evidence.timeout_kind_report().kind if record.outcome == TIMEOUT_OUTCOME else None
        sidecar = evidence.sidecar
        segment, reason = select_current_segment(
            read_stage_journal(evidence.paths.journal, max_bytes=SUMMARY_READ_LIMIT_BYTES),
            pid=(sidecar or {}).get("child_pid"),
            start_token=(sidecar or {}).get("child_start_token"),
        )
        pairs.append(observe_pair(
            key, record.outcome, termination=termination_of(record.outcome, kind),
            timeout_kind=kind, segment=segment, segment_reason=reason, sidecar=sidecar,
        ))
    recorded = manifest.get("analysis_timeout")
    deadline_off = recorded == "0"
    deadline = None if deadline_off else _seconds(recorded)
    note = "run_manifest analysis_timeout"
    if deadline is None and not deadline_off:
        budgets = {pair.budget_seconds for pair in pairs if pair.budget_seconds is not None}
        if len(budgets) == 1:
            deadline = budgets.pop()
            note = "deadline_tripped budget_seconds (the manifest does not record it)"
        else:
            note = (f"neither the manifest nor a single trip budget gives it "
                    f"({len(budgets)} distinct budgets)")
    jobs = manifest.get("parallel_jobs")
    dirty = manifest.get("git_dirty")
    facts = RunFacts(
        root=str(root), deadline_seconds=deadline, deadline_off=deadline_off,
        deadline_note=note,
        pair_process_timeout_seconds=_seconds(manifest.get("pair_process_timeout_seconds")),
        parallel_jobs=int(jobs) if jobs and jobs.isdigit() else None,
        git_commit=manifest.get("git_commit") or None,
        git_dirty=None if dirty not in ("0", "1") else dirty == "1",
        samples=frozenset(_sample_of(pair.key) for pair in pairs),
    )
    return RunObservation(facts=facts, pairs=tuple(pairs))


def observe_runs(roots: Iterable[Path]) -> List[RunObservation]:
    return [observe_run(Path(root)) for root in roots]


def _pool_summary(runs: Sequence[RunObservation]) -> Dict[str, Any]:
    pairs = [pair for run in runs for pair in run.pairs]
    cut = [pair for pair in pairs if pair.cut]

    def keys(predicate) -> List[str]:
        return [pair.key for pair in pairs if predicate(pair)]

    return {
        "runs": [run.facts.to_dict() for run in runs],
        "pairs": len(pairs),
        "cut_pairs": len(cut),
        "finished_before_deadline": sum(1 for pair in pairs if pair.cut is False),
        "cut_unknown": [[pair.key, pair.cut_unknown_reason] for pair in pairs if pair.cut is None],
        "terminations": {
            name: keys(lambda pair, name=name: pair.termination == name)
            for name in (acceptance.TERMINATION_PROCESS_TIMEOUT,
                         acceptance.TERMINATION_SOLVER_TIMEOUT,
                         acceptance.TERMINATION_TIMEOUT_UNCLASSIFIED,
                         acceptance.TERMINATION_INVALID)
        },
        "entered_lead_window": keys(lambda pair: pair.entered_lead_window),
        "missing_intervals": [
            [pair.key, name, reason] for pair in cut for name, reason in pair.missing.items()
        ],
        "intervals": {
            **{name: describe([pair.values[name] for pair in cut if name in pair.values])
               for name in acceptance.TERM_POOLS},
            "needed": describe([pair.needed for pair in cut if pair.needed is not None]),
        },
    }


def report_dict(
    profile: acceptance.MarginProfile, pools: Mapping[str, Sequence[RunObservation]],
) -> Dict[str, Any]:
    """観測の要約と `deadline_margin_acceptance.evaluate_margin` の判定。"""

    verdict = acceptance.evaluate_margin(profile, pools)
    profile_pairs = [pair for run in pools.get(acceptance.POOL_P, ()) for pair in run.pairs if pair.cut]
    return {
        "schema": SCHEMA,
        "profile": {
            "name": profile.name, "deadline_seconds": profile.deadline_seconds,
            "margin_seconds": profile.margin_seconds,
            "pair_process_timeout_seconds": profile.pair_process_timeout_seconds,
            "population": None if profile.population is None else len(profile.population),
            "machinery_commits": None if profile.machinery_commits is None
            else sorted(profile.machinery_commits),
        },
        "pools": {name: _pool_summary(pools.get(name, ())) for name in acceptance.POOLS},
        "post_trip_parts": {
            name: describe([pair.post_trip_parts.get(name, 0.0) for pair in profile_pairs])
            for name in POST_TRIP_PARTS
        },
        "verdict": verdict.to_dict(),
        "required_margin_seconds": verdict.required_margin_seconds,
        "margin_holds": verdict.holds,
        "profile_pairs": [pair.to_dict() for pair in profile_pairs],
    }


def format_report(payload: Mapping[str, Any]) -> str:
    profile = payload["profile"]
    verdict = payload["verdict"]
    lines = [
        "Deadline margin summary:",
        f"  profile {profile['name']}: deadline {profile['deadline_seconds']}"
        f" margin {profile['margin_seconds']} process {profile['pair_process_timeout_seconds']}",
    ]
    for name, pool in payload["pools"].items():
        terminations = pool["terminations"]
        lines.append(
            f"  pool {name}: runs {len(pool['runs'])}, pairs {pool['pairs']}, cut {pool['cut_pairs']},"
            f" finished {pool['finished_before_deadline']}, cut unknown {len(pool['cut_unknown'])},"
            f" missing intervals {len(pool['missing_intervals'])};"
            f" TIMEOUT process {len(terminations['process_timeout'])}"
            f" solver {len(terminations['solver_timeout'])}"
            f" unclassified {len(terminations['timeout_unclassified'])},"
            f" invalid {len(terminations['termination_invalid'])},"
            f" lead window {len(pool['entered_lead_window'])}"
        )
        for interval, row in pool["intervals"].items():
            stats = " ".join(f"{key}={value}" for key, value in row.items())
            lines.append(f"    - {interval}: {stats}")
    lines.append("  post_trip parts (pool P):")
    for name, row in payload["post_trip_parts"].items():
        lines.append(f"    - {name}: " + " ".join(f"{key}={value}" for key, value in row.items()))
    for term, row in verdict["terms"].items():
        lines.append(f"  term {term}: " + " ".join(f"{key}={value}" for key, value in row.items()))
    lines.append(
        f"  required margin: {verdict['required_margin_seconds']}; verdict: {verdict['status']}"
    )
    for reason in verdict["violations"]:
        lines.append(f"  violated: {reason}")
    for reason in verdict["undetermined"]:
        lines.append(f"  undetermined: {reason}")
    return "\n".join(lines)


def _population(manifest: Optional[Path]) -> Optional[frozenset]:
    """固定 subset の manifest（`eqbench_subset.json`）の source 一覧（Eq と Neq）。"""

    if manifest is None:
        return None
    data = json.loads(manifest.read_text(encoding="utf-8"))
    return frozenset(
        source for half in ("eq", "neq") for source in data.get(half, {}).get("sources", ())
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("roots", nargs="+", type=Path,
                        help="pool P: the profile's run result trees (one per half)")
    parser.add_argument("--load-root", action="append", type=Path, default=[],
                        help="pool L: a run of the load pool (pre / overrun; repeatable)")
    parser.add_argument("--pre-root", action="append", type=Path, default=[],
                        help="pool F: a run of the fixed-cost pool (pre only; repeatable)")
    parser.add_argument("--margin", type=float, default=None,
                        help="the ANALYSIS_TIMEOUT_MARGIN under evaluation")
    parser.add_argument("--profile", default="unnamed", help="the profile's name")
    parser.add_argument("--profile-deadline", type=float, default=None,
                        help="the profile's ANALYSIS_TIMEOUT (pool P needs a deadline at least this)")
    parser.add_argument("--pair-process-timeout", type=float, default=None,
                        help="the profile's PAIR_PROCESS_TIMEOUT (pool P must match it)")
    parser.add_argument("--population-manifest", type=Path, default=None,
                        help="the fixed subset manifest whose sources are the profile's population")
    parser.add_argument("--machinery-commit", action="append", default=None,
                        help="a commit whose deadline machinery is the one under evaluation "
                             "(pools P and L; repeatable)")
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args(argv)
    profile = acceptance.MarginProfile(
        name=args.profile, deadline_seconds=args.profile_deadline, margin_seconds=args.margin,
        pair_process_timeout_seconds=args.pair_process_timeout,
        population=_population(args.population_manifest),
        machinery_commits=None if args.machinery_commit is None else frozenset(args.machinery_commit),
    )
    pools = {
        acceptance.POOL_P: observe_runs(args.roots),
        acceptance.POOL_L: observe_runs(args.load_root),
        acceptance.POOL_F: observe_runs(args.pre_root),
    }
    payload = report_dict(profile, pools)
    print(format_report(payload))
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(payload, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
