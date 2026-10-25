# -*- coding: utf-8 -*-
"""wrapper の記録の形式・状態・検査（評価計画 v2 PR-D）。標準 library だけ。

``eval/wrapper.py``（host）と ``eval/summarize.py``（読み取り専用の container）が同じ規則で
読む。記録を書くのは wrapper だけ。

**launch の状態機械**（``<wrapper>/launches/<n>/``。各記録は 1 回だけ確定し、上書きしない）

==================  ======================================================================
記録                 確定する時点
==================  ======================================================================
``launch.json``      起動の要求。staging dir に書き、dir の rename 1 回で ``<n>`` として確定する
``container.json``   ``docker run`` が container の id を返した後（回復では inspect で見つけた後）
``runner.log``       ``docker logs`` が成功した後（失敗の出力は保存しない）
``exit.json``        container の終了を観測した後。``runner.log`` の sha256 と bytes を持つ
``evidence.json``    未終端の pair の写しと検証器の判定を取得できた後
``released.json``    ``docker rm`` の後、container が「存在しない」と観測できた後
==================  ======================================================================

``exit.json`` の ``kind``:

* ``ran``: container の終了を観測した（exit code・``OOMKilled``・runner の出力）
* ``not_started``: container が作られなかった（``docker run`` の失敗、または起動前の中断。
  container が存在しないことを観測してから書く）
* ``exit_unobserved``: container が wrapper の外で消され、終了を観測できなかった。成功には
  数えない（``summarize`` が未完了の理由にする）

状態は確定した記録の集合から決まる: ``released`` だけが終端。それ以外（``requested`` /
``container_recorded`` / ``exit_recorded`` / ``evidence_recorded``）は未完了で、``stop`` が
続きから回収する。記録の組が規則に合わない、読めない、確定した記録が欠けている、launch の番号が
欠けている、終端でない launch の後に launch がある、journal にある launch の dir が無い、は
すべて **破損**（``problems``）として報告し、隠さない。書きかけ（``.<name>.tmp-*`` と
``.launch-*.uncommitted-*``）は証拠ではなく、無視する。

**観測**（``watch.jsonl``）: cgroup の観測を **毎回** 1 行で保存する（保存の間隔と観測の間隔を
同じにする）。読めなかった観測も ``observed: false`` で保存する。OOM の帰属は ``oom_attribution``。
"""

from __future__ import annotations

from dataclasses import dataclass, field
import json
from pathlib import Path
import re
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

import protocol  # 同じ dir（eval/）。応答と記録の契約の owner

LAUNCHES_DIR = "launches"
JOURNAL = "events.jsonl"
META = "meta.json"
LAUNCH = "launch.json"
CONTAINER = "container.json"
RUNNER_LOG = "runner.log"
EXIT = "exit.json"
EVIDENCE = "evidence.json"
RELEASED = "released.json"
WATCH = "watch.jsonl"
SUPERVISOR_LOG = "supervisor.log"

LAUNCH_SCHEMA = "eval-launch-v2"
EXIT_SCHEMA = "eval-launch-exit-v2"
CONTAINER_SCHEMA = "eval-launch-container-v2"
RELEASED_SCHEMA = "eval-launch-released-v2"
EVIDENCE_SCHEMA = protocol.EVIDENCE_SCHEMA

KIND_RAN = "ran"
KIND_NOT_STARTED = "not_started"
KIND_EXIT_UNOBSERVED = "exit_unobserved"
EXIT_KINDS = (KIND_RAN, KIND_NOT_STARTED, KIND_EXIT_UNOBSERVED)

STATE_REQUESTED = "requested"
STATE_CONTAINER = "container_recorded"
STATE_EXIT = "exit_recorded"
STATE_EVIDENCE = "evidence_recorded"
STATE_RELEASED = "released"
STATE_DAMAGED = "damaged"

#: journal の event と、その event の前に確定している記録。
JOURNALED_RECORDS = {"container_recorded": CONTAINER, "exit_recorded": EXIT,
                     "evidence_recorded": EVIDENCE, "released": RELEASED}

STAGING_MARK = ".uncommitted-"
_TEMPORARY = re.compile(r"\..+\.tmp-\d+-[0-9a-f]+")
_STAGING = re.compile(r"\.launch-\d+" + re.escape(STAGING_MARK) + r"[0-9a-f]+")
_RUN_ID = re.compile(r"[0-9a-f]{32}")
_CONTAINER_ID = re.compile(r"[0-9a-f]{64}")
_SHA256 = re.compile(r"[0-9a-f]{64}")
#: launch dir に置いてよい、記録ではない file（診断）。
_DIAGNOSTIC_FILES = frozenset({WATCH, SUPERVISOR_LOG})


def staging_name(number: int, token: str) -> str:
    return f".launch-{number}{STAGING_MARK}{token}"


def _load(path: Path) -> Tuple[Optional[Any], Optional[str]]:
    """``(値, None)``・存在しなければ ``(None, None)``・読めなければ ``(None, 理由)``。"""
    try:
        text = Path(path).read_text(encoding="utf-8")
    except FileNotFoundError:
        return None, None
    except (OSError, UnicodeError) as exc:
        return None, f"{Path(path).name} unreadable: {exc}"
    try:
        return json.loads(text), None
    except ValueError as exc:
        return None, f"{Path(path).name} is not JSON: {exc}"


def read_jsonl(path: Path) -> Tuple[List[Dict[str, Any]], int, bool]:
    """``(行, 読めない行の数, file が存在したか)``。読めない行は黙って捨てない。"""
    try:
        text = Path(path).read_text(encoding="utf-8")
    except FileNotFoundError:
        return [], 0, False
    except (OSError, UnicodeError):
        return [], 1, True
    rows: List[Dict[str, Any]] = []
    bad = 0
    for line in text.splitlines():
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except ValueError:
            bad += 1
            continue
        if isinstance(value, dict):
            rows.append(value)
        else:
            bad += 1
    return rows, bad, True


@dataclass
class Launch:
    number: int
    state: str
    launch: Optional[Dict[str, Any]] = None
    container: Optional[Dict[str, Any]] = None
    exit: Optional[Dict[str, Any]] = None
    evidence: Optional[Dict[str, Any]] = None
    released: Optional[Dict[str, Any]] = None
    runner_log_present: bool = False
    watch: List[Dict[str, Any]] = field(default_factory=list)
    watch_unreadable_lines: int = 0
    problems: List[str] = field(default_factory=list)

    @property
    def terminal(self) -> bool:
        return self.state == STATE_RELEASED

    @property
    def container_id(self) -> Optional[str]:
        for record in (self.container, self.exit):
            value = (record or {}).get("container_id")
            if isinstance(value, str):
                return value
        return None

    @property
    def exit_kind(self) -> Optional[str]:
        return (self.exit or {}).get("kind")


def _sha256_file(path: Path) -> Optional[Tuple[str, int]]:
    import hashlib

    try:
        data = Path(path).read_bytes()
    except OSError:
        return None
    return hashlib.sha256(data).hexdigest(), len(data)


def read_launch(directory: Path, number: int) -> Launch:
    """1 つの launch の記録を読み、状態と破損を決める（書かない）。"""
    directory = Path(directory)
    problems: List[str] = []
    values: Dict[str, Any] = {}
    for name in (LAUNCH, CONTAINER, EXIT, EVIDENCE, RELEASED):
        value, error = _load(directory / name)
        if error:
            problems.append(error)
        elif value is not None and not isinstance(value, dict):
            problems.append(f"{name} is not an object")
        else:
            values[name] = value
    launch = values.get(LAUNCH)
    container = values.get(CONTAINER)
    exit_record = values.get(EXIT)
    evidence = values.get(EVIDENCE)
    released = values.get(RELEASED)
    runner_log = (directory / RUNNER_LOG).is_file()
    try:
        entries = sorted(p.name for p in directory.iterdir())
    except OSError as exc:
        entries = []
        problems.append(f"launch dir unreadable: {exc}")
    known = {LAUNCH, CONTAINER, EXIT, EVIDENCE, RELEASED, RUNNER_LOG} | _DIAGNOSTIC_FILES
    for name in entries:
        if name not in known and not _TEMPORARY.fullmatch(name):
            problems.append(f"unrecognised entry {name}")

    # 確定した記録どうしの規則。
    if launch is None:
        problems.append("launch.json is missing")
    elif launch.get("schema") != LAUNCH_SCHEMA or launch.get("launch") != number:
        problems.append("launch.json does not describe this launch")
    if container is not None:
        if container.get("schema") != CONTAINER_SCHEMA or not _CONTAINER_ID.fullmatch(
                str(container.get("container_id"))):
            problems.append("container.json is malformed")
    if exit_record is not None:
        kind = exit_record.get("kind")
        if exit_record.get("schema") != EXIT_SCHEMA or kind not in EXIT_KINDS:
            problems.append("exit.json is malformed")
        elif exit_record.get("launch") != number:
            problems.append("exit.json describes another launch")
        elif kind == KIND_NOT_STARTED:
            if container is not None or runner_log or evidence is not None:
                problems.append("a launch recorded as not started has container records")
        else:
            if container is None and kind == KIND_RAN:
                problems.append("container.json is missing for a launch whose container ran")
            elif container is None and exit_record.get("container_id") is not None:
                problems.append("exit.json names a container that container.json does not")
            elif container is not None and (
                    exit_record.get("container_id") != container.get("container_id")):
                problems.append("exit.json and container.json name different containers")
            if kind == KIND_RAN:
                log = exit_record.get("runner_log") or {}
                actual = _sha256_file(directory / RUNNER_LOG)
                if actual is None:
                    problems.append("runner.log is missing")
                elif not (_SHA256.fullmatch(str(log.get("sha256")))
                          and (log.get("sha256"), log.get("bytes")) == actual):
                    problems.append("runner.log differs from the one exit.json recorded")
            if not isinstance(exit_record.get("runtime_run_ids"), list):
                problems.append("exit.json has no runtime_run_ids")
    if evidence is not None:
        if exit_record is None:
            problems.append("evidence.json exists without exit.json")
        else:
            try:
                protocol.validate_evidence(evidence)
            except protocol.Rejected as exc:
                problems.append(f"evidence.json is malformed ({exc})")
    if released is not None:
        if released.get("schema") != RELEASED_SCHEMA:
            problems.append("released.json is malformed")
        if exit_record is None:
            problems.append("released.json exists without exit.json")
        elif exit_record.get("kind") != KIND_NOT_STARTED:
            if evidence is None:
                problems.append("released.json exists without evidence.json")
            if released.get("container_id") != exit_record.get("container_id"):
                problems.append("released.json names another container")

    watch, bad, _exists = read_jsonl(directory / WATCH)
    if problems:
        state = STATE_DAMAGED
    elif released is not None:
        state = STATE_RELEASED
    elif evidence is not None:
        state = STATE_EVIDENCE
    elif exit_record is not None:
        state = STATE_EXIT
    elif container is not None:
        state = STATE_CONTAINER
    else:
        state = STATE_REQUESTED
    return Launch(number=number, state=state, launch=launch, container=container,
                  exit=exit_record, evidence=evidence, released=released,
                  runner_log_present=runner_log, watch=watch, watch_unreadable_lines=bad,
                  problems=problems)


@dataclass
class RecordCheck:
    """wrapper の記録全体の検査の結果。"""

    launches: List[Launch] = field(default_factory=list)
    #: 破損（確定した記録の欠損・不整合・未知の entry）。回復では消えない。
    problems: List[str] = field(default_factory=list)
    #: 未完了の launch（最後の 1 つだけがなり得る）。``stop`` で回収する。
    unfinished: Optional[Launch] = None
    #: 書きかけの残骸（証拠ではない）。
    debris: List[str] = field(default_factory=list)

    @property
    def damaged(self) -> bool:
        return bool(self.problems)


def read_records(wrapper: Path) -> RecordCheck:
    """launch の記録をすべて読み、番号・順序・journal との対応を検査する（書かない）。"""
    wrapper = Path(wrapper)
    check = RecordCheck()
    root = wrapper / LAUNCHES_DIR
    numbers: List[int] = []
    if root.is_dir():
        for entry in sorted(root.iterdir()):
            if entry.name.isdigit() and entry.is_dir() and not entry.is_symlink():
                numbers.append(int(entry.name))
            elif _STAGING.fullmatch(entry.name):
                check.debris.append(entry.name)
            else:
                check.problems.append(f"launches/{entry.name}: unrecognised entry")
    elif root.exists():
        check.problems.append("launches is not a directory")
    numbers.sort()
    expected = list(range(1, len(numbers) + 1))
    if numbers != expected:
        missing = sorted(set(range(1, (max(numbers) if numbers else 0) + 1)) - set(numbers))
        check.problems.append(f"launch record(s) missing: {missing}")
    for number in numbers:
        launch = read_launch(root / str(number), number)
        check.launches.append(launch)
        check.problems += [f"launch {number}: {problem}" for problem in launch.problems]
    for launch in check.launches[:-1]:
        if launch.state not in (STATE_RELEASED, STATE_DAMAGED):
            check.problems.append(f"launch {launch.number} is unfinished but a later launch exists")
    if check.launches and check.launches[-1].state not in (STATE_RELEASED, STATE_DAMAGED):
        check.unfinished = check.launches[-1]
    journal, bad, exists = read_jsonl(wrapper / JOURNAL)
    if bad:
        check.problems.append(f"{JOURNAL}: {bad} unreadable line(s)")
    if numbers and not exists:
        check.problems.append(f"{JOURNAL} is missing")
    requested = {row.get("launch") for row in journal if row.get("event") == "launch_requested"}
    lost = sorted(n for n in requested if isinstance(n, int) and n not in numbers)
    if lost:
        check.problems.append(f"the journal names launch(es) without a record: {lost}")
    # journal は各記録を確定した後に追記する: journal にある記録が無ければ、確定した記録が消えた。
    by_number = {launch.number: launch for launch in check.launches}
    for row in journal:
        name = JOURNALED_RECORDS.get(row.get("event"))
        launch = by_number.get(row.get("launch"))
        if name and launch is not None and not (wrapper / LAUNCHES_DIR / str(launch.number) / name).exists():
            check.problems.append(f"launch {launch.number}: {name} is missing although the "
                                  f"journal recorded it ({row.get('event')})")
    return check


def attribution_problems(check: RecordCheck, executions: Iterable[str]) -> List[str]:
    """出力先の execution と launch の対応（起動要求 → container → execution）。

    ``executions`` は出力先の ``.executions`` の execution（32 桁の id の dir）。終端した launch
    が記録した execution は出力先に存在し、出力先の execution はちょうど 1 つの launch が記録
    している。未完了の launch があるときは、どの launch にも記録されていない execution はその
    launch のものとして扱う（まだ記録していない）。
    """
    on_disk = {run_id for run_id in executions if _RUN_ID.fullmatch(run_id)}
    owner: Dict[str, int] = {}
    problems: List[str] = []
    for launch in check.launches:
        if launch.exit is None or launch.state == STATE_DAMAGED:
            continue
        for run_id in launch.exit.get("runtime_run_ids") or []:
            if run_id in owner:
                problems.append(f"execution {run_id} is recorded by launches {owner[run_id]} "
                                f"and {launch.number}")
            owner[run_id] = launch.number
            if run_id not in on_disk:
                problems.append(f"launch {launch.number} records execution {run_id}, which the "
                                "output does not hold")
    if check.unfinished is None:
        stray = sorted(on_disk - set(owner))
        if stray:
            problems.append(f"{len(stray)} execution(s) in the output were not started by a "
                            f"recorded launch: {', '.join(stray[:3])}")
    return problems


# ---------------------------------------------------------------------------
# OOM の帰属
# ---------------------------------------------------------------------------

#: pair の時刻（runtime receipt）と cgroup の観測時刻（host）の許容誤差（秒）。同じ kernel の
#: 時計なので小さくてよい。
CLOCK_SLACK_SECONDS = 1.0
OOM_YES = "yes"
OOM_NO = "no"
OOM_UNOBSERVED = "unobserved"


@dataclass(frozen=True)
class CounterInterval:
    """直前の有効な観測 ``start`` から今回の有効な観測 ``end`` まで。``delta`` は増分、
    counter が戻った（reset）ときは ``None``（増分は分からない）。"""

    start: float
    end: float
    delta: Optional[int]


def counter_intervals(watch: Sequence[Mapping[str, Any]]) -> List[CounterInterval]:
    """``oom_kill`` を読めた観測だけをつないだ区間。読めなかった観測はその区間を広げるだけ。"""
    points = [
        (float(row["at_epoch"]), row["oom_kill"]) for row in watch
        if isinstance(row.get("at_epoch"), (int, float)) and type(row.get("oom_kill")) is int
    ]
    points.sort(key=lambda point: point[0])
    intervals = []
    for (t0, c0), (t1, c1) in zip(points, points[1:]):
        intervals.append(CounterInterval(t0, t1, c1 - c0 if c1 >= c0 else None))
    return intervals


def oom_attribution(watch: Sequence[Mapping[str, Any]], *, start: Optional[float],
                    end: Optional[float], container_oom_killed: Optional[bool]) -> str:
    """1 つの pair（実行区間 ``[start, end]``）が cgroup の OOM kill と結び付くか。

    * ``yes``: container 自体が OOMKilled、または増分のある区間がその pair の実行区間と重なる
    * ``no``: 実行区間が有効な観測の区間で覆われ、重なる区間の増分がすべて 0
    * ``unobserved``: それ以外（区間の外・観測の欠け・counter の reset・時刻が無い）

    SIGKILL で終わったこと自体はここに入らない（呼び出し側が外部 kill として数える）。
    """
    if container_oom_killed is True:
        return OOM_YES
    if not isinstance(start, (int, float)) or not isinstance(end, (int, float)):
        return OOM_UNOBSERVED
    lo, hi = start - CLOCK_SLACK_SECONDS, end + CLOCK_SLACK_SECONDS
    intervals = counter_intervals(watch)
    overlapping = [i for i in intervals if i.start < hi and i.end > lo]
    if any(i.delta for i in overlapping):
        return OOM_YES
    if any(i.delta is None for i in overlapping):
        return OOM_UNOBSERVED
    covered = bool(intervals) and intervals[0].start <= lo and intervals[-1].end >= hi
    return OOM_NO if covered else OOM_UNOBSERVED
