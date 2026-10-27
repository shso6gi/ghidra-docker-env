# -*- coding: utf-8 -*-
"""wrapper の記録の形式・状態・検査（評価計画 v2 PR-D）。標準 library だけ（出力の分類は
同じ worktree の ``reporting.execution_chain``、これも標準 library だけ、の reader に委ねる）。

``eval/wrapper.py``（host）と ``eval/summarize.py``（読み取り専用の container）が同じ規則で
読む。記録を書くのは wrapper だけ。入力の状態はそれぞれ 1 つの関数だけが分類する:
``read_meta``（meta の無い・正常・破損）と ``classify_output``（出力の無い・空・開始前・開始後・
破損）。安全側でない状態（初回・開始前）は owner が積極的に言えたときだけで、既定値にしない。

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


def _is_fingerprint(value: Any) -> bool:
    return isinstance(value, str) and value.startswith(FINGERPRINT_PREFIX) and bool(
        _SHA256.fullmatch(value[len(FINGERPRINT_PREFIX):]))


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
    elif not _is_fingerprint(launch.get("fingerprint")):
        problems.append("launch.json has no conditions fingerprint")
    if container is not None:
        if container.get("schema") != CONTAINER_SCHEMA or not _CONTAINER_ID.fullmatch(
                str(container.get("container_id"))):
            problems.append("container.json is malformed")
        elif not (_is_fingerprint(container.get("fingerprint"))
                  or container.get("fingerprint") is None):
            problems.append("container.json has a malformed conditions fingerprint")
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


def launch_condition_problems(check: RecordCheck, fingerprint: Optional[str]) -> List[str]:
    """launch の要求（``launch.json``）と起動した container（``container.json``、container の
    label から）が、この評価の条件の要約（valid な meta の fingerprint）と一致するか。

    ``fingerprint`` が ``None``（meta が valid でない）なら照合の基準が無い: 食い違いとは言わず
    （その評価は ``meta_invalid`` で判定できない）、何も返さない。container が作られなかった
    launch は条件で何も動かしていない。
    """
    problems: List[str] = []
    if fingerprint is None:
        return problems
    for launch in check.launches:
        if launch.state == STATE_DAMAGED or launch.launch is None:
            continue
        requested = launch.launch.get("fingerprint")
        if requested != fingerprint and launch.exit_kind != KIND_NOT_STARTED:
            problems.append(f"launch {launch.number} was requested under conditions "
                            f"{requested}, not this evaluation's {fingerprint}")
        if launch.container is not None and launch.container.get("fingerprint") != requested:
            problems.append(f"launch {launch.number}'s container ran under conditions "
                            f"{launch.container.get('fingerprint')}, not the requested {requested}")
    return problems


def attribution_problems(check: RecordCheck, executions: Iterable[str]) -> List[str]:
    """出力先の execution と launch の対応（起動要求 → container → execution）。

    ``executions`` は出力先の ``.executions`` の execution（32 桁の id の dir）。終端した launch
    が記録した execution は出力先に存在し、出力先の execution はちょうど 1 つの launch が記録
    している。未完了の launch があるときは、どの launch にも記録されていない execution はその
    launch のものとして扱う（まだ記録していない）。
    """
    on_disk = {run_id for run_id in executions if _RUN_ID.fullmatch(run_id)}
    # executions は ``classify_output`` の ``started``（開始の記録が確定したもの）を渡す。
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


# ---------------------------------------------------------------------------
# meta.json（評価の条件）: 「無い」「正常」「破損」の 3 つを 1 か所で決める
# ---------------------------------------------------------------------------

META_SCHEMA = "eval-wrapper-meta-v1"
CONDITIONS_SCHEMA = "eval-wrapper-conditions-v1"
FINGERPRINT_PREFIX = "eval-env-v1:"
MATRICES = ("neq", "eq")
#: profile のうち wrapper が使い、runner へ渡さない key（必須）。
WRAPPER_KEYS = ("IMAGE", "CONTAINER_MEMORY", "STOP_GRACE_SECONDS")
META_KEYS = frozenset({"schema", "eval_id", "created_at", "conditions", "fingerprint",
                       "observations"})
CONDITION_KEYS = frozenset({"schema", "matrix", "freeze_commit", "tag", "image", "container",
                            "profile", "mounts", "container_paths", "runner", "probe", "host"})
_COMMIT = re.compile(r"[0-9a-f]{40}")
_TAG = re.compile(r"(|[A-Za-z0-9][A-Za-z0-9._-]{0,39})")
_USER = re.compile(r"[0-9]+:[0-9]+")

META_ABSENT = "absent"
META_VALID = "valid"
META_DAMAGED = "damaged"


def canonical_digest(payload: Any) -> str:
    import hashlib

    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def fingerprint_of(conditions: Mapping[str, Any]) -> str:
    """条件の要約（runner の開始の記録に入る ``environment_fingerprint``）。"""
    return FINGERPRINT_PREFIX + canonical_digest(conditions)


def eval_id_of(matrix: str, commit: str, tag: str) -> str:
    return f"{matrix}-{commit[:12]}" + (f"-{tag}" if tag else "")


def _str(value: Any) -> bool:
    return isinstance(value, str) and bool(value)


def _str_map(value: Any) -> bool:
    return isinstance(value, dict) and all(isinstance(k, str) and isinstance(v, str)
                                           for k, v in value.items())


def condition_problems(conditions: Any, *, matrix: Optional[str] = None,
                       output_name: Optional[str] = None) -> List[str]:
    """条件（``meta.json`` の ``conditions``）が wrapper の書く形か。``matrix`` / ``output_name``
    （出力先の dir の名前。commit・matrix・tag から決まる）を渡せば、この評価のものかも確かめる。"""
    if not isinstance(conditions, dict):
        return ["conditions is not an object"]
    problems: List[str] = []
    keys = set(conditions)
    if keys != CONDITION_KEYS:
        problems.append(f"conditions keys differ (missing {sorted(CONDITION_KEYS - keys)}, "
                        f"unexpected {sorted(keys - CONDITION_KEYS)})")
        return problems
    rules = [
        ("schema", conditions["schema"] == CONDITIONS_SCHEMA),
        ("matrix", conditions["matrix"] in MATRICES
         and (matrix is None or conditions["matrix"] == matrix)),
        ("freeze_commit", isinstance(conditions["freeze_commit"], str)
         and bool(_COMMIT.fullmatch(conditions["freeze_commit"]))),
        ("tag", isinstance(conditions["tag"], str) and bool(_TAG.fullmatch(conditions["tag"]))),
        ("runner", _str(conditions["runner"])),
        ("probe", _str_map(conditions["probe"]) and bool(conditions["probe"])),
        ("host", isinstance(conditions["host"], dict)),
    ]
    image = conditions["image"]
    rules.append(("image", isinstance(image, dict) and set(image) == {"name", "id"}
                  and _str(image.get("name")) and _str(image.get("id"))))
    container = conditions["container"]
    rules.append(("container", isinstance(container, dict)
                  and set(container) == {"memory", "memory_swap", "network", "init", "user",
                                         "stop_grace_seconds"}
                  and _str(container.get("memory"))
                  and container.get("memory_swap") == container.get("memory")
                  and container.get("network") == "none" and container.get("init") is True
                  and isinstance(container.get("user"), str)
                  and bool(_USER.fullmatch(container["user"]))
                  and type(container.get("stop_grace_seconds")) is int
                  and container["stop_grace_seconds"] > 0))
    profile = conditions["profile"]
    values = profile.get("values") if isinstance(profile, dict) else None
    rules.append(("profile", isinstance(profile, dict) and set(profile) == {"sha256", "values"}
                  and isinstance(profile.get("sha256"), str)
                  and bool(_SHA256.fullmatch(profile["sha256"]))
                  and _str_map(values) and all(key in values for key in WRAPPER_KEYS)))
    if all(ok for _name, ok in rules[-3:]):  # image・container・profile の形が正しいときだけ
        # profile の値と、それから作った欄が食い違わない（片方だけ書き換えられていない）。
        rules.append(("profile.values", values["IMAGE"] == image["name"]
                      and values["CONTAINER_MEMORY"] == container["memory"]
                      and values["STOP_GRACE_SECONDS"] == str(container["stop_grace_seconds"])))
    mounts = conditions["mounts"]
    rules.append(("mounts", _str_map(mounts)
                  and set(mounts) == {"workspace", "targets", "logs", "git"}))
    paths = conditions["container_paths"]
    rules.append(("container_paths", _str_map(paths)
                  and set(paths) == {"output", "tmpdir", "private_authority_root"}
                  and (output_name is None
                       or paths.get("output", "").rsplit("/", 1)[-1] == output_name)))
    problems += [f"conditions.{name} is malformed or not this evaluation's"
                 for name, ok in rules if not ok]
    return problems


@dataclass
class MetaRead:
    """``meta.json`` の読み取り。``state`` は ``absent`` / ``valid`` / ``damaged``。

    ``absent`` は wrapper の dir が無いとき **だけ**（dir は meta.json ごと rename 1 回で確定する
    ので、dir があって meta が無い・読めない・形が違う・要約が条件と合わないのはすべて破損）。
    条件と fingerprint は ``valid`` のときだけ使える（``require``）。
    """

    state: str
    meta: Optional[Dict[str, Any]] = None
    problems: List[str] = field(default_factory=list)

    @property
    def conditions(self) -> Dict[str, Any]:
        return self.require()["conditions"]

    @property
    def fingerprint(self) -> str:
        return self.require()["fingerprint"]

    def require(self) -> Dict[str, Any]:
        if self.state != META_VALID or self.meta is None:
            raise MetaUnusable(self.describe())
        return self.meta

    def describe(self) -> str:
        if self.state == META_ABSENT:
            return "the evaluation has no wrapper records (meta.json)"
        if self.state == META_DAMAGED:
            return "meta.json is damaged: " + "; ".join(self.problems)
        return "meta.json is valid"


class MetaUnusable(Exception):
    """valid でない meta から条件を使おうとした。"""


def read_meta(wrapper: Path, *, matrix: Optional[str] = None) -> MetaRead:
    """``meta.json`` を読んで分類する（wrapper・summarize・supervisor・stop が共有する唯一の解釈）。

    ``<出力先>.wrapper`` の meta であること（条件の出力先の名前）も確かめる。
    """
    wrapper = Path(wrapper)
    output_name = wrapper.name[:-len(".wrapper")] if wrapper.name.endswith(".wrapper") else None
    if not wrapper.exists() and not wrapper.is_symlink():
        return MetaRead(META_ABSENT)
    if wrapper.is_symlink() or not wrapper.is_dir():
        return MetaRead(META_DAMAGED, problems=[f"{wrapper.name} is not a directory"])
    value, error = _load(wrapper / META)
    if error:
        return MetaRead(META_DAMAGED, problems=[error])
    if value is None:
        return MetaRead(META_DAMAGED, problems=["meta.json is missing from the wrapper records"])
    if not isinstance(value, dict):
        return MetaRead(META_DAMAGED, problems=["meta.json is not an object"])
    problems: List[str] = []
    keys = set(value)
    if keys != META_KEYS:
        problems.append(f"meta.json keys differ (missing {sorted(META_KEYS - keys)}, "
                        f"unexpected {sorted(keys - META_KEYS)})")
    if value.get("schema") != META_SCHEMA:
        problems.append(f"meta.json schema is {value.get('schema')!r}")
    if not problems:
        conditions = value["conditions"]
        problems += condition_problems(conditions, matrix=matrix, output_name=output_name)
        if output_name is None:
            problems.append(f"{wrapper.name} is not named after an output (<output>.wrapper)")
        if not problems:
            if value["fingerprint"] != fingerprint_of(conditions):
                problems.append("meta.json fingerprint does not summarize its conditions")
            if value["eval_id"] != eval_id_of(conditions["matrix"], conditions["freeze_commit"],
                                              conditions["tag"]):
                problems.append("meta.json eval_id does not follow from its conditions")
            if not _str(value["created_at"]) or not isinstance(value["observations"], dict):
                problems.append("meta.json created_at / observations are malformed")
    if problems:
        return MetaRead(META_DAMAGED, meta=value, problems=problems)
    return MetaRead(META_VALID, meta=value)


# ---------------------------------------------------------------------------
# 出力の状態: runner の記録の分類は execution_chain（PR-B）の reader が唯一の owner
# ---------------------------------------------------------------------------

START_RECORD = "run_manifest.start.txt"
RUN_MANIFEST = "run_manifest.txt"
#: 最新の execution の終わりに top level に置かれる成果物（どれかがあれば pair を始めた後）。
#: ``pair-status-verification-key.json`` は runner が manifest の前に置く準備の file なので含めない。
END_ARTIFACTS = ("matrix-publication-manifest.json", "validation-execution-receipt.json")


@dataclass
class OutputClass:
    """出力の分類（``classify_output``）。

    * ``state``: ``protocol.OUTPUT_STATES`` の 1 つ。``never_started`` は「runner の証跡が
      書きかけの残骸だけ」と owner が積極的に言えたときだけで、既定値ではない。
    * ``started``: 開始の記録が確定した execution（launch の記録と照合する母集合）。
    * ``damage``: 確定した証跡の欠損・破損・未知の entry（``read_chain_records`` の分類）。
      1 つでもあれば state は ``damaged``（退避しない・再開しない）。
    """

    state: str
    started: List[str] = field(default_factory=list)
    damage: List[str] = field(default_factory=list)
    evidence: List[str] = field(default_factory=list)
    debris: List[str] = field(default_factory=list)


def classify_output(out: Path) -> OutputClass:
    """出力先を分類する（completion・wrapper の退避・launch の execution の記録が共有）。"""
    from scripts.function_tracer_pcode.reporting import execution_chain

    out = Path(out)
    if not out.exists() and not out.is_symlink():
        return OutputClass(protocol.OUTPUT_ABSENT)
    if out.is_symlink() or not out.is_dir():
        return OutputClass(protocol.OUTPUT_DAMAGED, damage=[f"{out.name} is not a directory"])
    try:
        if not any(out.iterdir()):
            return OutputClass(protocol.OUTPUT_EMPTY)
        chain = execution_chain.read_chain_records(out)
    except OSError as exc:
        return OutputClass(protocol.OUTPUT_DAMAGED, damage=[f"the output is unreadable: {exc}"])
    result = OutputClass(protocol.OUTPUT_STARTED, started=sorted(chain.started()),
                         debris=list(chain.never_started))
    for run_id, execution in sorted(chain.executions.items()):
        result.debris += [f"{run_id}/{name}" for name in execution.debris]
        result.damage += [f"execution {run_id}: {problem}" for problem in execution.problems]
        if not execution.started:
            held = [name for name, present in (("issue records", execution.issued),
                                                ("a seal", execution.sealed)) if present]
            if held:
                result.damage.append(f"execution {run_id} holds {' and '.join(held)} but no "
                                     "committed start record")
    result.damage += [f".executions/{name}: unrecognised entry" for name in chain.unrecognised]
    # 確定した証跡（どれかがあれば pair を始めた後。退避の対象ではない）。
    result.evidence += [f"execution {run_id}" for run_id in result.started]
    for name in (RUN_MANIFEST, *END_ARTIFACTS):
        if (out / name).exists() or (out / name).is_symlink():
            result.evidence.append(name)
    for pattern in ("*" + execution_chain.PAIR_STATUS_SUFFIX, ".runtime-metrics"):
        found = next(iter(out.rglob(pattern)), None)
        if found is not None:
            result.evidence.append(found.relative_to(out).as_posix())
    if result.damage:
        result.state = protocol.OUTPUT_DAMAGED
    elif not result.evidence:
        result.state = protocol.OUTPUT_NEVER_STARTED
    return result


def output_state(out: Path) -> str:
    return classify_output(out).state


def started_executions(out: Path) -> List[str]:
    """開始の記録が確定した execution（``classify_output`` の ``started``）。"""
    return classify_output(out).started


def observe_start_records(out: Path) -> List[str]:
    """実行中の観測用: 開始の記録の file がある execution の id（分類ではない）。

    supervisor が実行中に繰り返し呼ぶので、issue の記録を読まない。launch の終了の記録は、
    この観測と ``classify_output`` の両方の和を「この launch の execution」として記録する
    （観測した execution が後で消えれば、記録と出力の対応の検査が破損として報告する）。
    """
    directory = Path(out) / ".executions"
    try:
        return sorted(entry.name for entry in directory.iterdir()
                      if _RUN_ID.fullmatch(entry.name) and (entry / START_RECORD).is_file())
    except OSError:
        return []


def output_fingerprint(out: Path) -> Optional[str]:
    """出力の top level と ``.executions`` の entry の (名前, 大きさ, mtime) の digest。

    launch の要求の時点で記録し、container の記録が無いまま container が見つからないときに、
    container が動いたか（出力が変わったか）を判断するのに使う。出力が無ければ ``None``。
    """
    import hashlib

    out = Path(out)
    if not out.is_dir():
        return None
    rows = []
    for base in (out, out / ".executions"):
        if not base.is_dir():
            continue
        for entry in sorted(base.iterdir()):
            try:
                stat = entry.lstat()
            except OSError:
                continue
            rows.append(f"{entry.relative_to(out).as_posix()}\t{stat.st_size}\t{stat.st_mtime_ns}")
    return hashlib.sha256("\n".join(rows).encode()).hexdigest()
