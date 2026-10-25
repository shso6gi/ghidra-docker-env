#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""全件評価の wrapper（評価計画 v2 PR-D）。入口は ``eval/neq.sh`` / ``eval/eq.sh``。

    eval/neq.sh start --freeze <commit>   # preflight → 背景で実行（再開を含む）
    eval/neq.sh status [--verify]         # 読み取り専用
    eval/neq.sh stop                      # docker stop（猶予は runner の停止確認より長い）
    eval/neq.sh summary [--json]          # 読み取り専用。完了の判定は検証器と ledger

**持たないもの**: 解析・確定・完全性・正式性の規則。完了かどうかは
``execution_chain verify`` と ledger の ``full_scope_evidence``（``eval/summarize.py`` が
呼ぶ）だけが決める。runner の exit code は記録するが、完了の根拠にしない。

**持つもの**:

* identity（analysis config / source digest）の外にある実行条件の記録と照合。初回の ``start``
  で ``meta.json`` に書き、その要約（fingerprint）を ``EQBENCH_ENVIRONMENT_FINGERPRINT`` として
  runner に渡す（runner が開始の記録に残し、検証器が execution 間の一致を要求する）。再開の
  たびに同じ条件を組み立て直して照合し、違えば何も書かずに拒否する。条件を変えるときは別の
  出力先（別の評価）にする。
* 評価の slot の lock（``flock -n``）。``start`` が取り、背景の supervisor が受け継いで、
  container の終了・記録・削除の確認まで保持する。
* container の一生と観測: 起動、cgroup の ``oom_kill`` / ``memory.peak`` の監視、終了の記録
  （exit code・``OOMKilled``・runner の出力）、未終端の pair の写し、削除の確認。
* run tmpdir の片付け: lock を持ち、評価の container が 1 つも無いことを確かめた後で、
  この評価専用の tmp に残った前回までの残骸（SIGKILL などで消えなかったもの）を消す。

管理 file はすべて出力先の外（``<log root>/eval_<sha12>_<matrix>[_<tag>].wrapper/``）に置く。
出力先には runner の証跡以外を置かない（FULL の FRESH 受理を壊さないため）。
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import datetime as _dt
import errno
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import shutil
import signal
import subprocess
import sys
import time
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

EVAL_DIR = Path(__file__).resolve().parent
REPO = EVAL_DIR.parent

EXIT_OK = 0
EXIT_FAILED = 1
EXIT_REFUSED = 2

META_SCHEMA = "eval-wrapper-meta-v1"
CONDITIONS_SCHEMA = "eval-wrapper-conditions-v1"
FINGERPRINT_PREFIX = "eval-env-v1:"

RUNNERS = {"neq": "neqbench_run_all_32jobs.sh", "eq": "eqbench_run_all_32jobs.sh"}
RUN_TMP_PREFIXES = {"neq": ("neqbench-run.", "neqbench-tmp."), "eq": ("eqbench-run.", "eqbench-tmp.")}
#: profile のうち wrapper が使い、runner へ渡さない key（必須）。
WRAPPER_KEYS = ("IMAGE", "CONTAINER_MEMORY", "STOP_GRACE_SECONDS")
#: wrapper が決める（profile では指定できない）runner の環境変数。
CONTROLLED_RUNNER_KEYS = frozenset({
    "OUTPUT_BASE_DIR", "EQBENCH_TMPDIR", "EQBENCH_PRIVATE_AUTHORITY_ROOT",
    "EQBENCH_ENVIRONMENT_FINGERPRINT", "TMPDIR", "TMP", "TEMP", "HOME", "PYTHON_BIN",
    "EQBENCH_PROCESS_OWNER_TOKEN", "EQBENCH_PROCESS_OWNER_ROOT",
    "EQBENCH_PROCESS_OWNER_ROOT_START",
})
_KEY = re.compile(r"[A-Z][A-Z0-9_]*")
_TAG = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]{0,39}")
_COMMIT = re.compile(r"[0-9a-f]{40}")
_MEMORY = re.compile(r"[1-9][0-9]*[bkmg]")

LABEL_SLOT = "ghidra-eval.slot"
LABEL_EVAL = "ghidra-eval.eval"
LABEL_LAUNCH = "ghidra-eval.launch"
LABEL_READER = "ghidra-eval.reader"

WATCH_POLL_SECONDS = float(os.environ.get("EVAL_WATCH_POLL_SECONDS", "10"))
WATCH_PERIOD_SECONDS = float(os.environ.get("EVAL_WATCH_PERIOD_SECONDS", "300"))
START_CONFIRM_SECONDS = 180.0
REMOVE_CONFIRM_SECONDS = 60.0
READER_MEMORY = "16g"
DEFAULT_MIN_FREE_GIB = 64
DEFAULT_LOCK_FILE = Path.home() / ".cache" / "ghidra-eval" / "eval.lock"
CGROUP_TEMPLATE = "/sys/fs/cgroup/system.slice/docker-{id}.scope"


class Refused(Exception):
    """preflight の拒否（何も書いていない）。"""


class WrapperError(Exception):
    """wrapper 自身の失敗。"""


# ---------------------------------------------------------------------------
# 永続化（同じ dir の一時名に書いて fsync → rename / link。途中で止まっても書きかけを残さない）
# ---------------------------------------------------------------------------


def _fsync_dir(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def write_atomic(path: Path, data: bytes, *, exclusive: bool = False) -> None:
    """``path`` に ``data`` を確定させる。``exclusive`` なら既存の file を上書きしない。"""
    path = Path(path)
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}-{secrets.token_hex(4)}")
    with open(temporary, "xb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    try:
        if exclusive:
            os.link(temporary, path)
        else:
            os.replace(temporary, path)
    finally:
        if exclusive or temporary.exists():
            try:
                temporary.unlink()
            except FileNotFoundError:
                pass
    _fsync_dir(path.parent)


def write_json(path: Path, payload: Any, *, exclusive: bool = False) -> None:
    write_atomic(path, (json.dumps(payload, indent=1, sort_keys=True) + "\n").encode(),
                 exclusive=exclusive)


def append_jsonl(path: Path, payload: Mapping[str, Any]) -> None:
    """1 行を O_APPEND の 1 回の write で追記し fsync する。"""
    line = (json.dumps(payload, sort_keys=True) + "\n").encode()
    fd = os.open(path, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o644)
    try:
        if os.write(fd, line) != len(line):
            raise OSError(errno.EIO, f"short append to {path}")
        os.fsync(fd)
    finally:
        os.close(fd)


def read_json(path: Path) -> Optional[Any]:
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, UnicodeError, ValueError):
        return None


def utc_now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def canonical_digest(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


# ---------------------------------------------------------------------------
# profile
# ---------------------------------------------------------------------------


def load_profile(path: Path) -> Tuple[Dict[str, str], str]:
    """``KEY=VALUE`` の行（``#`` で始まる行と空行は無視）。shell として評価しない。"""
    raw = Path(path).read_bytes()
    values: Dict[str, str] = {}
    for number, line in enumerate(raw.decode("utf-8").splitlines(), 1):
        text = line.strip()
        if not text or text.startswith("#"):
            continue
        key, sep, value = text.partition("=")
        if not sep or not _KEY.fullmatch(key):
            raise WrapperError(f"{path}:{number}: not a KEY=VALUE line")
        if key in values:
            raise WrapperError(f"{path}:{number}: {key} is set twice")
        if key in CONTROLLED_RUNNER_KEYS:
            raise WrapperError(f"{path}:{number}: {key} is set by the wrapper, not the profile")
        values[key] = value
    for key in WRAPPER_KEYS:
        if key not in values:
            raise WrapperError(f"{path}: {key} is required")
    if not _MEMORY.fullmatch(values["CONTAINER_MEMORY"]):
        raise WrapperError(f"{path}: CONTAINER_MEMORY must look like 110g")
    grace = values["STOP_GRACE_SECONDS"]
    if not grace.isdigit() or int(grace) <= minimum_stop_grace():
        raise WrapperError(
            f"{path}: STOP_GRACE_SECONDS must be an integer above {minimum_stop_grace()} "
            "(the runner's stop confirmation can take that long)")
    return values, hashlib.sha256(raw).hexdigest()


def minimum_stop_grace() -> int:
    """runner の停止の確認の上限（PR-A）に、tmp の削除などの余裕 30 秒を足した下限。"""
    sys.path.insert(0, str(REPO))
    try:
        from scripts.eqbench.runner_processes import KILL_WAIT_SECONDS
    finally:
        sys.path.remove(str(REPO))
    return int(KILL_WAIT_SECONDS) + 30


# ---------------------------------------------------------------------------
# 評価の場所
# ---------------------------------------------------------------------------


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True,
                          capture_output=True, text=True).stdout.strip()


@dataclass(frozen=True)
class Evaluation:
    matrix: str
    repo: Path            # 評価用の worktree（container の /workspace）
    main: Path            # targets / logs を持つ main checkout
    commit: str           # freeze の commit（出力先の名前に入る）
    tag: str
    profile_path: Path
    log_root: Path        # main/logs の下
    lock_file: Path
    docker: str

    @property
    def name(self) -> str:
        suffix = f"_{self.tag}" if self.tag else ""
        return f"eval_{self.commit[:12]}_{self.matrix}{suffix}"

    @property
    def eval_id(self) -> str:
        suffix = f"-{self.tag}" if self.tag else ""
        return f"{self.matrix}-{self.commit[:12]}{suffix}"

    @property
    def out(self) -> Path:
        return self.log_root / self.name

    @property
    def wrapper(self) -> Path:
        return self.log_root / f"{self.name}.wrapper"

    @property
    def tmp(self) -> Path:
        return self.wrapper / "tmp"

    @property
    def authority(self) -> Path:
        return self.wrapper / "authority"

    @property
    def container_name(self) -> str:
        return f"ghidra-eval-{self.eval_id}"

    def in_container(self, host_path: Path) -> str:
        """main/logs の下の host path を、container の /workspace/logs の下の path にする。"""
        relative = Path(host_path).relative_to(self.main / "logs")
        return str(Path("/workspace/logs") / relative)

    def launch_dir(self, launch: int) -> Path:
        return self.wrapper / "launches" / str(launch)


def resolve(matrix: str, *, freeze: Optional[str], tag: str, require_freeze: bool) -> Evaluation:
    repo = Path(os.environ.get("EVAL_REPO", REPO)).resolve()
    main = os.environ.get("EVAL_MAIN_CHECKOUT")
    if main is None:
        common = Path(_git(repo, "rev-parse", "--path-format=absolute", "--git-common-dir"))
        main = str(common.parent)
    main_path = Path(main).resolve()
    if freeze is None:
        if require_freeze:
            raise Refused("start needs --freeze <40-hex commit>: the commit this evaluation is for")
        freeze = _git(repo, "rev-parse", "HEAD")
    if not _COMMIT.fullmatch(freeze):
        raise Refused(f"--freeze must be a full 40-hex commit: {freeze}")
    if tag and not _TAG.fullmatch(tag):
        raise Refused(f"--tag must match {_TAG.pattern}: {tag}")
    log_root = Path(os.environ.get("EVAL_LOG_ROOT", main_path / "logs" / "EqBench")).resolve()
    try:
        log_root.relative_to(main_path / "logs")
    except ValueError:
        raise Refused(f"EVAL_LOG_ROOT must be under {main_path / 'logs'} (the container mount)")
    profile = Path(os.environ.get("EVAL_PROFILE", EVAL_DIR / "profile.env")).resolve()
    return Evaluation(
        matrix=matrix, repo=repo, main=main_path, commit=freeze, tag=tag,
        profile_path=profile, log_root=log_root,
        lock_file=Path(os.environ.get("EVAL_LOCK_FILE", DEFAULT_LOCK_FILE)),
        docker=os.environ.get("EVAL_DOCKER", "docker"),
    )


# ---------------------------------------------------------------------------
# docker
# ---------------------------------------------------------------------------


def docker(ev: Evaluation, *args: str, check: bool = False,
           timeout: Optional[float] = None) -> subprocess.CompletedProcess:
    try:
        completed = subprocess.run([ev.docker, *args], capture_output=True, text=True,
                                   timeout=timeout)
    except (OSError, subprocess.SubprocessError) as exc:
        raise WrapperError(f"docker {args[0]}: {exc}") from exc
    if check and completed.returncode != 0:
        raise WrapperError(f"docker {' '.join(args[:2])}: {completed.stderr.strip()}")
    return completed


def image_id(ev: Evaluation, image: str) -> str:
    completed = docker(ev, "image", "inspect", "--format", "{{.Id}}", image)
    if completed.returncode != 0 or not completed.stdout.strip():
        raise Refused(f"image {image} is not available: {completed.stderr.strip()}")
    return completed.stdout.strip()


def slot_containers(ev: Evaluation) -> List[Dict[str, str]]:
    """slot の label を持つ container（状態を問わない）。"""
    completed = docker(ev, "ps", "-a", "--filter", f"label={LABEL_SLOT}=1", "--format",
                       "{{.Names}}\t{{.State}}\t{{.Label \"" + LABEL_EVAL + "\"}}", check=True)
    rows = []
    for line in completed.stdout.splitlines():
        if line.strip():
            name, state, label = (line.split("\t") + ["", ""])[:3]
            rows.append({"name": name, "state": state, "eval": label})
    return rows


def other_running_containers(ev: Evaluation) -> List[str]:
    completed = docker(ev, "ps", "--format", "{{.Names}}\t{{.Label \"" + LABEL_SLOT + "\"}}"
                       + "\t{{.Label \"" + LABEL_READER + "\"}}")
    names = []
    for line in completed.stdout.splitlines():
        parts = (line.split("\t") + ["", ""])[:3]
        if parts[0] and parts[1] != "1" and parts[2] != "1":
            names.append(parts[0])
    return sorted(names)


def container_state(ev: Evaluation) -> Optional[Dict[str, Any]]:
    completed = docker(ev, "inspect", "--type", "container", ev.container_name)
    if completed.returncode != 0:
        return None
    try:
        payload = json.loads(completed.stdout)[0]
    except (ValueError, IndexError, KeyError):
        raise WrapperError(f"docker inspect {ev.container_name}: unreadable output")
    state = payload.get("State") or {}
    labels = (payload.get("Config") or {}).get("Labels") or {}
    return {
        "id": payload.get("Id"), "status": state.get("Status"),
        "running": state.get("Running"), "exit_code": state.get("ExitCode"),
        "oom_killed": state.get("OOMKilled"), "error": state.get("Error"),
        "started_at": state.get("StartedAt"), "finished_at": state.get("FinishedAt"),
        "launch": labels.get(LABEL_LAUNCH),
    }


def _mount_args(ev: Evaluation, *, read_only: bool) -> List[str]:
    git = str(ev.main / ".git")
    if read_only:
        # 読み取り専用の container は host の dir に mount 点を作らない（/workspace は tmpfs）。
        return ["--tmpfs", "/workspace", "-v", f"{ev.repo}:/workspace/src:ro",
                "-v", f"{ev.main / 'logs'}:/workspace/logs:ro", "-v", f"{git}:{git}:ro",
                "-w", "/workspace/src"]
    return ["-v", f"{ev.repo}:/workspace", "-v", f"{ev.main / 'targets'}:/workspace/targets",
            "-v", f"{ev.main / 'logs'}:/workspace/logs", "-v", f"{git}:{git}:ro",
            "-w", "/workspace"]


def _user() -> str:
    return f"{os.getuid()}:{os.getgid()}"


def reader(ev: Evaluation, image: str, args: Sequence[str], *, memory: str = READER_MEMORY,
           env: Optional[Mapping[str, str]] = None, timeout: Optional[float] = None,
           ) -> subprocess.CompletedProcess:
    """出力先・wrapper の dir・worktree を読み取り専用で mount した使い捨ての container。"""
    environment = ["-e", "HOME=/tmp", "-e", "PYTHONPATH=/workspace/src",
                   "-e", "PYTHONDONTWRITEBYTECODE=1"]
    for key, value in (env or {}).items():
        environment += ["-e", f"{key}={value}"]
    return docker(ev, "run", "--rm", "--init", "--network", "none", "--label", f"{LABEL_READER}=1",
                  "--memory", memory, "--memory-swap", memory, "-u", _user(),
                  *environment, *_mount_args(ev, read_only=True), image, *args, timeout=timeout)


def summarize_args(ev: Evaluation, command: str, *extra: str) -> List[str]:
    return ["python3", "-B", "eval/summarize.py", command, "--repo", "/workspace/src",
            "--out", ev.in_container(ev.out), *extra]


# ---------------------------------------------------------------------------
# lock
# ---------------------------------------------------------------------------


def open_lock(ev: Evaluation) -> int:
    ev.lock_file.parent.mkdir(parents=True, exist_ok=True)
    return os.open(ev.lock_file, os.O_WRONLY | os.O_CREAT, 0o644)


def try_lock(fd: int) -> bool:
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return True
    except BlockingIOError:
        return False


def lock_holders(ev: Evaluation) -> Optional[List[int]]:
    """lock が保持されていれば、lock file を開いている process の pid（無ければ ``None``）。

    ``/proc/locks`` で保持の有無を読み、保持者は ``/proc/<pid>/fd`` から探す（``/proc/locks``
    の pid は lock を取った process で、受け継いだ supervisor ではない）。lock には触らない。
    """
    try:
        stat = os.stat(ev.lock_file)
        text = Path("/proc/locks").read_text()
    except OSError:
        return None
    device = f"{os.major(stat.st_dev):02x}:{os.minor(stat.st_dev):02x}:{stat.st_ino}"
    held = any(
        len(fields) >= 6 and fields[1] == "FLOCK" and fields[5] == device
        for fields in (line.split() for line in text.splitlines())
    )
    if not held:
        return None
    pids = []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit() or int(entry.name) == os.getpid():
            continue
        try:
            for fd in (entry / "fd").iterdir():
                target = os.stat(fd)
                if (target.st_dev, target.st_ino) == (stat.st_dev, stat.st_ino):
                    pids.append(int(entry.name))
                    break
        except OSError:
            continue
    return sorted(pids)


# ---------------------------------------------------------------------------
# 条件（identity の外）
# ---------------------------------------------------------------------------


def probe_environment(ev: Evaluation, image: str, memory: str) -> Dict[str, str]:
    """本番と同じ image・資源上限の container で、runner の開始の記録と同じ環境の行を読む。"""
    completed = docker(
        ev, "run", "--rm", "--init", "--network", "none", "--memory", memory,
        "--memory-swap", memory, "-u", _user(), "-e", "HOME=/tmp",
        "-e", "PYTHONPATH=/workspace/src", "-e", "PYTHONDONTWRITEBYTECODE=1",
        "--label", f"{LABEL_READER}=1", *_mount_args(ev, read_only=True), image,
        "python3", "-B", "-m", "scripts.function_tracer_pcode.reporting.execution_chain",
        "environment-lines", "--repo-root", "/workspace/src", timeout=300)
    if completed.returncode != 0:
        raise Refused(f"the environment probe failed: {completed.stderr.strip()[-500:]}")
    rows = {}
    for line in completed.stdout.splitlines():
        key, sep, value = line.partition("=")
        if sep:
            rows[key] = value
    rows.pop("environment_fingerprint", None)
    return rows


def build_conditions(ev: Evaluation, profile: Mapping[str, str], profile_sha: str,
                     image: str, probe: Mapping[str, str]) -> Dict[str, Any]:
    memory = profile["CONTAINER_MEMORY"]
    return {
        "schema": CONDITIONS_SCHEMA,
        "matrix": ev.matrix,
        "freeze_commit": ev.commit,
        "tag": ev.tag,
        "image": {"name": profile["IMAGE"], "id": image},
        "container": {
            "memory": memory, "memory_swap": memory, "network": "none", "init": True,
            "user": _user(), "stop_grace_seconds": int(profile["STOP_GRACE_SECONDS"]),
        },
        "profile": {"sha256": profile_sha, "values": dict(sorted(profile.items()))},
        "mounts": {
            "workspace": str(ev.repo), "targets": str(ev.main / "targets"),
            "logs": str(ev.main / "logs"), "git": str(ev.main / ".git"),
        },
        "container_paths": {
            "output": ev.in_container(ev.out), "tmpdir": ev.in_container(ev.tmp),
            "private_authority_root": ev.in_container(ev.authority),
        },
        "runner": RUNNERS[ev.matrix],
        "probe": dict(sorted(probe.items())),
        "host": {"cpus": os.cpu_count()},
    }


def fingerprint_of(conditions: Mapping[str, Any]) -> str:
    return FINGERPRINT_PREFIX + canonical_digest(conditions)


def differing_keys(a: Any, b: Any, prefix: str = "") -> List[str]:
    if isinstance(a, dict) and isinstance(b, dict):
        keys = []
        for key in sorted(set(a) | set(b)):
            keys += differing_keys(a.get(key), b.get(key), f"{prefix}{key}.")
        return keys
    return [] if a == b else [prefix.rstrip(".")]


# ---------------------------------------------------------------------------
# preflight（読むだけ）
# ---------------------------------------------------------------------------


@dataclass
class Plan:
    profile: Dict[str, str]
    conditions: Dict[str, Any]
    fingerprint: str
    first: bool
    preflight: Optional[Dict[str, Any]]
    leftovers: List[str]
    others: List[str]
    aborted_output: bool = False


def worktree_state(ev: Evaluation) -> None:
    head = _git(ev.repo, "rev-parse", "HEAD")
    if head != ev.commit:
        raise Refused(f"the evaluation worktree is at {head}, not the freeze commit {ev.commit}")
    dirty = _git(ev.repo, "status", "--porcelain", "--untracked-files=all")
    if dirty:
        raise Refused("the evaluation worktree is not clean:\n" + dirty)


def free_bytes(path: Path) -> int:
    stat = os.statvfs(path)
    return stat.f_bavail * stat.f_frsize


def preflight(ev: Evaluation) -> Plan:
    """start の前提をすべて確かめる。ここでは何も書かない（拒否は Refused）。"""
    try:
        profile, profile_sha = load_profile(ev.profile_path)
    except (OSError, UnicodeError, WrapperError) as exc:
        raise Refused(f"profile: {exc}")
    image = image_id(ev, profile["IMAGE"])
    present = slot_containers(ev)
    if present:
        raise Refused("an evaluation-slot container exists (running or not removed): "
                      + ", ".join(f"{r['name']} ({r['state']})" for r in present)
                      + "; use `stop` on its evaluation, or inspect it before removing it")
    worktree_state(ev)
    minimum = int(os.environ.get("EVAL_MIN_FREE_GIB", DEFAULT_MIN_FREE_GIB)) * 2**30
    if free_bytes(ev.log_root if ev.log_root.exists() else ev.main / "logs") < minimum:
        raise Refused(f"less than {minimum // 2**30} GiB free under {ev.log_root}")
    meta_path = ev.wrapper / "meta.json"
    meta = read_json(meta_path) if meta_path.exists() else None
    if meta_path.exists() and not (isinstance(meta, dict) and meta.get("schema") == META_SCHEMA):
        raise Refused(f"{meta_path} is unreadable; the evaluation's conditions cannot be checked")
    out_entries = sorted(p.name for p in ev.out.iterdir()) if ev.out.is_dir() else []
    if ev.out.exists() and not ev.out.is_dir():
        raise Refused(f"{ev.out} is not a directory")
    if meta is None and out_entries:
        raise Refused(f"{ev.out} holds results but no wrapper record ({meta_path}); it was not "
                      "started by this wrapper -- use a new output (another --tag or commit)")
    if meta is None and ev.wrapper.exists() and any(ev.wrapper.iterdir()):
        raise Refused(f"{ev.wrapper} exists without meta.json; inspect it before starting")
    probe = probe_environment(ev, profile["IMAGE"], profile["CONTAINER_MEMORY"])
    conditions = build_conditions(ev, profile, profile_sha, image, probe)
    fingerprint = fingerprint_of(conditions)
    if meta is not None:
        recorded = meta.get("conditions")
        if recorded != conditions or meta.get("fingerprint") != fingerprint:
            raise Refused(
                "the conditions differ from the ones this evaluation started with: "
                + ", ".join(differing_keys(recorded, conditions) or ["fingerprint"])
                + ". To change them, start a separate evaluation (another --tag).")
    report = None
    aborted = bool(out_entries) and never_recorded_a_start(ev.out)
    if out_entries and not aborted:
        completed = reader(ev, profile["IMAGE"], summarize_args(ev, "preflight"), timeout=3600)
        report = _parse_json(completed.stdout)
        if completed.returncode != 0 or not isinstance(report, dict):
            raise Refused("cannot read the output with the execution chain verifier: "
                          + (completed.stderr.strip()[-800:] or f"exit {completed.returncode}"))
        if report.get("verify_error"):
            raise Refused(f"execution_chain verify failed: {report['verify_error']}")
        fingerprints = report.get("start_fingerprints")
        if fingerprints is None:
            raise Refused(f"start records unreadable: {report.get('start_records_error')}")
        foreign = sorted(r for r, value in fingerprints.items() if value != fingerprint)
        if foreign:
            raise Refused(f"{len(foreign)} execution(s) in {ev.out} did not run under this "
                          f"evaluation's conditions: {', '.join(foreign[:5])}")
        digests = {value for value in (report.get("start_source_digests") or {}).values()}
        if digests and digests != {report.get("current_source_digest")}:
            raise Refused("the output was made from another analysis source than this worktree")
    leftovers = sorted(p.name for p in ev.tmp.iterdir()) if ev.tmp.is_dir() else []
    return Plan(profile=profile, conditions=conditions, fingerprint=fingerprint,
                first=meta is None, preflight=report, leftovers=leftovers,
                others=other_running_containers(ev), aborted_output=aborted)


def never_recorded_a_start(out: Path) -> bool:
    """出力先が、開始の記録を残す前に止まった最初の execution のものか。

    runner は ``run_manifest.txt`` を置き、開始の記録を確定してから pair を始める。どちらも無く、
    pair-status も無い出力先では、pair は 1 つも始まっていない（関数選択などの途中で止まった）。
    runner の FULL 受理判定はこの出力先を拒否し続けるので、wrapper が脇へ移して新規に始める。
    """
    if (out / "run_manifest.txt").exists() or (out / "run_manifest.txt").is_symlink():
        return False
    executions = out / ".executions"
    if executions.is_dir() and any(executions.glob("*/run_manifest.start.txt")):
        return False
    return not any(out.rglob("*.pair-status.json"))


def _parse_json(text: str) -> Optional[Any]:
    try:
        return json.loads(text)
    except ValueError:
        return None


def is_closed(plan: Plan) -> bool:
    verify = (plan.preflight or {}).get("verify") or {}
    return verify.get("verdict") == "CLOSED_SAME_IDENTITY"


# ---------------------------------------------------------------------------
# start
# ---------------------------------------------------------------------------


def _tree_size(path: Path) -> int:
    total = 0
    for root, _dirs, files in os.walk(path):
        for name in files:
            try:
                total += os.lstat(os.path.join(root, name)).st_size
            except OSError:
                pass
    return total


def clean_leftovers(ev: Evaluation, names: Sequence[str]) -> List[Dict[str, Any]]:
    """前回までの run tmpdir などの残骸を消す（lock を持ち、slot の container が無いときだけ）。"""
    removed = []
    for name in names:
        path = ev.tmp / name
        size = _tree_size(path) if path.is_dir() else (path.lstat().st_size if path.exists() else 0)
        kind = "run_tmpdir" if name.startswith(RUN_TMP_PREFIXES[ev.matrix]) else "other"
        if path.is_dir() and not path.is_symlink():
            shutil.rmtree(path)
        else:
            path.unlink()
        removed.append({"name": name, "kind": kind, "bytes": size})
    return removed


def existing_execution_ids(ev: Evaluation) -> List[str]:
    directory = ev.out / ".executions"
    return sorted(p.name for p in directory.iterdir()) if directory.is_dir() else []


def next_launch(ev: Evaluation) -> int:
    root = ev.wrapper / "launches"
    numbers = [int(p.name) for p in root.iterdir() if p.name.isdigit()] if root.is_dir() else []
    return max(numbers, default=0) + 1


def reservation(ev: Evaluation, event: str, launch: int) -> None:
    append_jsonl(ev.lock_file.parent / "reservations.jsonl", {
        "event": event, "run_id": f"{ev.eval_id}-launch{launch}", "pid": os.getpid(),
        "at": utc_now()})


def command_start(ev: Evaluation) -> int:
    lock = open_lock(ev)
    try:
        return _start_locked(ev, lock)
    finally:
        # どの経路でも自分の fd は閉じる。起動した supervisor は自分の複製で lock を持ち続ける。
        os.close(lock)


def _start_locked(ev: Evaluation, lock: int) -> int:
    if not try_lock(lock):
        holders = lock_holders(ev) or []
        print(f"Refused (nothing was written): the evaluation slot lock {ev.lock_file} is held"
              + (f" by pid {', '.join(map(str, holders))}" if holders else ""), file=sys.stderr)
        return EXIT_REFUSED
    try:
        plan = preflight(ev)
    except Refused as exc:
        print(f"Refused (nothing was written): {exc}", file=sys.stderr)
        return EXIT_REFUSED
    if is_closed(plan):
        verify = plan.preflight["verify"]
        print(f"The evaluation is already complete across {len(verify.get('executions') or [])} "
              f"execution(s) (execution_chain verify: CLOSED_SAME_IDENTITY); nothing was "
              f"started or written. Run `summary` for the formal verdict.")
        return EXIT_OK
    for path in (ev.repo / "targets", ev.repo / "logs"):
        # container の mount 点（無ければ docker が root 所有で作る）。
        path.mkdir(exist_ok=True)
    ev.wrapper.mkdir(parents=True, exist_ok=True)
    if plan.first:
        write_json(ev.wrapper / "meta.json", {
            "schema": META_SCHEMA, "eval_id": ev.eval_id, "created_at": utc_now(),
            "conditions": plan.conditions, "fingerprint": plan.fingerprint,
            "observations": host_observations(ev),
        }, exclusive=True)
    for path in (ev.tmp, ev.authority, ev.wrapper / "launches"):
        path.mkdir(mode=0o700, exist_ok=True)
    removed = clean_leftovers(ev, plan.leftovers)
    launch = next_launch(ev)
    directory = ev.launch_dir(launch)
    directory.mkdir()
    moved_aside = None
    if plan.aborted_output:
        # 削除せずに wrapper の dir へ移す（同じ file system の rename 1 回）。
        aside = ev.wrapper / "aborted-outputs" / f"before-launch-{launch}"
        aside.parent.mkdir(exist_ok=True)
        os.rename(ev.out, aside)
        moved_aside = str(aside)
        print(f"The output held only the start of an execution that stopped before it recorded "
              f"its start (no pair was started); moved it aside to {aside}")
    verify = (plan.preflight or {}).get("verify") or {}
    write_json(directory / "launch.json", {
        "launch": launch, "requested_at": utc_now(), "fingerprint": plan.fingerprint,
        "execution_ids_before": existing_execution_ids(ev),
        "removed_leftovers": removed, "other_running_containers": plan.others,
        "moved_aside_output": moved_aside,
        "preflight_verify": {"verdict": verify.get("verdict"), "reasons": verify.get("reasons"),
                             "seconds": (plan.preflight or {}).get("verify_seconds")},
        "kind": "first" if not existing_execution_ids(ev) else "resume",
    }, exclusive=True)
    append_jsonl(ev.wrapper / "events.jsonl", {"event": "launch_requested", "launch": launch,
                                               "at": utc_now()})
    if removed:
        print(f"Removed {len(removed)} leftover entr(y/ies) of earlier executions from {ev.tmp}")
    if plan.others:
        print("Warning: other containers are running: " + ", ".join(plan.others))
    os.set_inheritable(lock, True)
    log = open(directory / "supervisor.log", "ab")
    try:
        process = subprocess.Popen(
            [sys.executable, "-B", str(Path(__file__).resolve()), "--matrix", ev.matrix,
             "_supervise", "--freeze", ev.commit, "--tag", ev.tag, "--launch", str(launch),
             "--lock-fd", str(lock)],
            stdin=subprocess.DEVNULL, stdout=log, stderr=log, pass_fds=(lock,),
            start_new_session=True, env=dict(os.environ))
    except OSError as exc:
        write_json(directory / "exit.json", {"launch": launch, "container_started": False,
                                              "error": f"supervisor: {exc}", "recorded_at": utc_now()})
        raise
    finally:
        log.close()
    deadline = time.monotonic() + START_CONFIRM_SECONDS
    while time.monotonic() < deadline:
        if (directory / "container.json").exists():
            info = read_json(directory / "container.json") or {}
            print(f"Started launch {launch} ({launch_kind(directory)}): container "
                  f"{ev.container_name} {str(info.get('id'))[:12]}, supervisor pid {process.pid}.")
            print(f"Output: {ev.out}\nRecords: {directory}\nFollow it with `status`; "
                  f"stop it with `stop`.")
            return EXIT_OK
        if process.poll() is not None:
            print(f"Error: the supervisor exited ({process.returncode}) before the container "
                  f"started; see {directory / 'supervisor.log'}", file=sys.stderr)
            return EXIT_FAILED
        time.sleep(0.5)
    print(f"Warning: the container has not started within {START_CONFIRM_SECONDS:.0f}s; "
          f"check `status` and {directory / 'supervisor.log'}", file=sys.stderr)
    return EXIT_FAILED


def launch_kind(directory: Path) -> str:
    return (read_json(directory / "launch.json") or {}).get("kind", "?")


def host_observations(ev: Evaluation) -> Dict[str, Any]:
    """照合しない参考の記録（docker の version など）。"""
    version = docker(ev, "version", "--format", "{{.Server.Version}}").stdout.strip()
    return {"docker_server": version or None, "kernel": os.uname().release,
            "hostname": os.uname().nodename}


# ---------------------------------------------------------------------------
# supervisor（背景。lock を保持し、container の一生を記録する）
# ---------------------------------------------------------------------------


def runner_command(ev: Evaluation, conditions: Mapping[str, Any], fingerprint: str,
                   launch: int) -> List[str]:
    values = conditions["profile"]["values"]
    memory = conditions["container"]["memory"]
    grace = str(conditions["container"]["stop_grace_seconds"])
    environment: List[str] = ["-e", "HOME=/tmp", "-e", "DISPLAY="]
    for key, value in sorted(values.items()):
        if key not in WRAPPER_KEYS:
            environment += ["-e", f"{key}={value}"]
    paths = conditions["container_paths"]
    environment += [
        "-e", f"OUTPUT_BASE_DIR={paths['output']}", "-e", f"EQBENCH_TMPDIR={paths['tmpdir']}",
        "-e", f"EQBENCH_PRIVATE_AUTHORITY_ROOT={paths['private_authority_root']}",
        "-e", f"EQBENCH_ENVIRONMENT_FINGERPRINT={fingerprint}",
    ]
    return ["run", "-d", "--init", "--name", ev.container_name,
            "--label", f"{LABEL_SLOT}=1", "--label", f"{LABEL_EVAL}={ev.eval_id}",
            "--label", f"{LABEL_LAUNCH}={launch}", "--network", "none",
            "--memory", memory, "--memory-swap", memory, "--stop-timeout", grace,
            "-u", conditions["container"]["user"], *environment,
            *_mount_args(ev, read_only=False), conditions["image"]["id"],
            "bash", conditions["runner"]]


def read_cgroup(container_id: str) -> Dict[str, Any]:
    directory = Path(os.environ.get("EVAL_CGROUP_TEMPLATE", CGROUP_TEMPLATE).format(id=container_id))
    values: Dict[str, Any] = {}
    try:
        for line in (directory / "memory.events").read_text().splitlines():
            key, _sep, value = line.partition(" ")
            if key in ("oom", "oom_kill") and value.strip().isdigit():
                values[key] = int(value)
        for name in ("memory.peak", "memory.current"):
            text = (directory / name).read_text().strip()
            if text.isdigit():
                values[name.split(".")[1] if name == "memory.current" else "memory_peak"] = int(text)
    except OSError:
        return {"cgroup": "unavailable"}
    if "current" in values:
        values["memory_current"] = values.pop("current")
    return values


class _Stop:
    requested = False


def command_supervise(ev: Evaluation, launch: int, lock_fd: int) -> int:
    directory = ev.launch_dir(launch)
    meta = read_json(ev.wrapper / "meta.json")
    events = ev.wrapper / "events.jsonl"

    def on_signal(_signum, _frame):
        _Stop.requested = True

    for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(signum, on_signal)
    reservation(ev, "start", launch)
    try:
        command = runner_command(ev, meta["conditions"], meta["fingerprint"], launch)
        started = docker(ev, *command)
        if started.returncode != 0:
            write_json(directory / "exit.json", {
                "launch": launch, "container_started": False,
                "error": started.stderr.strip()[-2000:], "recorded_at": utc_now()})
            append_jsonl(events, {"event": "container_start_failed", "launch": launch,
                                  "at": utc_now()})
            return EXIT_FAILED
        container = started.stdout.strip()
        write_json(directory / "container.json", {"id": container, "name": ev.container_name,
                                                  "started_at": utc_now()})
        append_jsonl(events, {"event": "container_started", "launch": launch,
                              "container": container[:12], "at": utc_now()})
        last_sample = watch(ev, launch, container)
        return finalize_launch(ev, launch, container, last_sample=last_sample)
    finally:
        reservation(ev, "end", launch)
        os.close(lock_fd)


def watch(ev: Evaluation, launch: int, container: str) -> Dict[str, Any]:
    """container の終了を待ちながら cgroup を観測する（oom_kill の変化はすぐ、他は 5 分ごと）。

    返り値は最後に読めた観測（終了の直前、最大で観測間隔ぶん前）。container が終わると cgroup
    は消えるので、終了の記録にはこれを残す。
    """
    directory = ev.launch_dir(launch)

    def new_waiter() -> subprocess.Popen:
        return subprocess.Popen([ev.docker, "wait", container], stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL)

    waiter = new_waiter()
    last_oom: Optional[int] = None
    last_period = 0.0
    stop_sent = False
    grace = str((read_json(ev.wrapper / "meta.json") or {})["conditions"]["container"]
                ["stop_grace_seconds"])
    next_poll = 0.0
    last_sample: Dict[str, Any] = {}
    while True:
        if waiter.poll() is not None:
            # `docker wait` が終わった。container がまだ動いていれば（docker の CLI の失敗など）、
            # 監視をやめずに待ち直す。
            state = container_state(ev)
            if state is None or not state.get("running"):
                break
            append_jsonl(directory / "watch.jsonl", {"at": utc_now(), "at_epoch": time.time(),
                                                     "kind": "wait_restarted"})
            time.sleep(WATCH_POLL_SECONDS)
            waiter = new_waiter()
        now = time.monotonic()
        if _Stop.requested and not stop_sent:
            # supervisor 自身が止められた: container にも正規の停止を送る（猶予付き）。
            subprocess.Popen([ev.docker, "stop", "-t", grace, container],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            append_jsonl(ev.wrapper / "events.jsonl", {
                "event": "stop_forwarded_by_supervisor", "launch": launch, "at": utc_now()})
            stop_sent = True
        if now >= next_poll:
            next_poll = now + WATCH_POLL_SECONDS
            sample = read_cgroup(container)
            if "cgroup" not in sample:
                last_sample = {"at": utc_now(), "at_epoch": time.time(), **sample}
            oom = sample.get("oom_kill")
            changed = isinstance(oom, int) and last_oom is not None and oom != last_oom
            if changed or now - last_period >= WATCH_PERIOD_SECONDS or last_oom is None:
                row = {"at": utc_now(), "at_epoch": time.time(), **sample,
                       "oom_kill_delta": (oom - last_oom) if changed else 0,
                       "kind": "oom_kill_change" if changed else "periodic"}
                if not changed:
                    row["other_running_containers"] = other_running_containers(ev)
                    last_period = now
                append_jsonl(directory / "watch.jsonl", row)
            if isinstance(oom, int):
                last_oom = oom
        time.sleep(1.0)
    return last_sample


def finalize_launch(ev: Evaluation, launch: int, container: str,
                    last_sample: Optional[Mapping[str, Any]] = None) -> int:
    """終了した container を記録してから消す。記録できなければ container を残す（証拠を失わない）。"""
    directory = ev.launch_dir(launch)
    events = ev.wrapper / "events.jsonl"
    state = container_state(ev)
    if state is None or state.get("running"):
        raise WrapperError(f"container {ev.container_name} is not in an exited state: {state}")
    logs = docker(ev, "logs", container)
    write_atomic(directory / "runner.log", (logs.stdout + logs.stderr).encode())
    after = existing_execution_ids(ev)
    before = set((read_json(directory / "launch.json") or {}).get("execution_ids_before") or [])
    exit_record = {
        "launch": launch, "container_started": True, "container_id": state.get("id"),
        "exit_code": state.get("exit_code"), "oom_killed": state.get("oom_killed"),
        "docker_error": state.get("error"), "started_at": state.get("started_at"),
        "finished_at": state.get("finished_at"),
        "finished_at_epoch": _epoch(state.get("finished_at")),
        "runtime_run_ids": [run_id for run_id in after if run_id not in before],
        "runner_exit_meaning": runner_exit_meaning(state.get("exit_code")),
        "last_cgroup_sample": dict(last_sample) if last_sample else None,
        "recorded_at": utc_now(),
    }
    recorded = read_json(directory / "exit.json")
    if recorded is None:
        write_json(directory / "exit.json", exit_record, exclusive=True)
        append_jsonl(events, {"event": "container_exited", "launch": launch,
                              "exit_code": state.get("exit_code"),
                              "oom_killed": state.get("oom_killed"), "at": utc_now()})
    elif recorded.get("container_id") != state.get("id"):
        raise WrapperError(f"{directory / 'exit.json'} records another container")
    # （記録済みなら、前の記録者が削除の前に止まった。記録はそのまま続ける。）
    # 証拠（未終端の pair の写しと検証器の判定）は、container を消す前に取る。取れなくても
    # container の終了の記録は済んでいるので削除へ進み、欠損は summary が欠損として出す。
    status = EXIT_OK
    if not (directory / "evidence.json").exists():
        status = capture_evidence(ev, launch)
    removed = docker(ev, "rm", container)
    if removed.returncode != 0:
        # 記録は済んでいる。container は残し（次の start が止まる）、`stop` で続きから消せる。
        raise WrapperError(f"container {ev.container_name} could not be removed: "
                           f"{removed.stderr.strip()}; run `stop` to finish the record")
    deadline = time.monotonic() + REMOVE_CONFIRM_SECONDS
    while container_state(ev) is not None:
        if time.monotonic() > deadline:
            raise WrapperError(f"container {ev.container_name} could not be removed: "
                               f"{removed.stderr.strip()}")
        time.sleep(1.0)
    append_jsonl(events, {"event": "released", "launch": launch, "at": utc_now()})
    return status


def capture_evidence(ev: Evaluation, launch: int) -> int:
    directory = ev.launch_dir(launch)
    events = ev.wrapper / "events.jsonl"
    meta = read_json(ev.wrapper / "meta.json") or {}
    image = ((meta.get("conditions") or {}).get("image") or {}).get("id")
    try:
        captured = reader(ev, image, summarize_args(ev, "launch-evidence"), timeout=3600)
        evidence = _parse_json(captured.stdout)
        if captured.returncode != 0 or not isinstance(evidence, dict):
            raise WrapperError(captured.stderr.strip()[-1000:] or f"exit {captured.returncode}")
        write_json(directory / "evidence.json", evidence, exclusive=True)
        append_jsonl(events, {"event": "evidence_saved", "launch": launch, "at": utc_now()})
        return EXIT_OK
    except (WrapperError, OSError) as exc:
        # 証拠の欠損は summary が欠損として出す（成功にしない）。ここでは記録を試みる。
        try:
            append_jsonl(events, {"event": "evidence_failed", "launch": launch,
                                  "at": utc_now(), "detail": str(exc)[-1000:]})
        except OSError:
            pass
        print(f"Error: post-run evidence of launch {launch} was not saved: {exc}", file=sys.stderr)
        return EXIT_FAILED


def runner_exit_meaning(code: Any) -> str:
    """runner の exit code の意味（記録用。完了の根拠にはしない）。"""
    meanings = {0: "finished", 1: "finished with failures (incomplete pairs, gate, census)",
                3: "incomplete pairs", 75: "stop not confirmed (run tmpdir kept)",
                129: "stopped (HUP)", 130: "stopped (INT)", 137: "killed (SIGKILL)",
                143: "stopped (TERM)"}
    return meanings.get(code, "other") if isinstance(code, int) else "unknown"


def _epoch(text: Any) -> Optional[float]:
    if not isinstance(text, str) or not text or text.startswith("0001-"):
        return None
    match = re.match(r"(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)(\.\d+)?Z", text)
    if not match:
        return None
    base = _dt.datetime.strptime(match.group(1), "%Y-%m-%dT%H:%M:%S").replace(
        tzinfo=_dt.timezone.utc).timestamp()
    return base + (float(match.group(2)) if match.group(2) else 0.0)


# ---------------------------------------------------------------------------
# stop
# ---------------------------------------------------------------------------


def command_stop(ev: Evaluation, wait_seconds: float) -> int:
    state = container_state(ev)
    meta = read_json(ev.wrapper / "meta.json") or {}
    grace = ((meta.get("conditions") or {}).get("container") or {}).get("stop_grace_seconds")
    if state is None:
        print(f"No container of this evaluation ({ev.container_name}).")
    elif state.get("running"):
        if not isinstance(grace, int):
            print("Error: meta.json gives no stop grace; refusing to guess one", file=sys.stderr)
            return EXIT_FAILED
        print(f"Stopping {ev.container_name} (grace {grace}s; the runner confirms its own "
              "processes stopped before it exits)...")
        append_jsonl(ev.wrapper / "events.jsonl", {"event": "stop_requested", "at": utc_now(),
                                                   "launch": state.get("launch")})
        docker(ev, "stop", "-t", str(grace), ev.container_name, timeout=grace + 60)
    # supervisor が記録と削除を終えて lock を離すまで待つ。supervisor が居なければ自分で行う。
    lock = open_lock(ev)
    try:
        deadline = time.monotonic() + wait_seconds
        while not try_lock(lock):
            if time.monotonic() > deadline:
                print(f"Error: the supervisor still holds the lock after {wait_seconds:.0f}s; "
                      "see `status`", file=sys.stderr)
                return EXIT_FAILED
            time.sleep(1.0)
        state = container_state(ev)
        if state is not None:
            if state.get("running"):
                print("Error: the container is running but nothing holds the evaluation lock; "
                      "stop it again", file=sys.stderr)
                return EXIT_FAILED
            launch = state.get("launch")
            if not (isinstance(launch, str) and launch.isdigit()):
                print("Error: the container has no launch label; inspect it by hand",
                      file=sys.stderr)
                return EXIT_FAILED
            print(f"The supervisor of launch {launch} is gone; recording the container's end.")
            append_jsonl(ev.wrapper / "events.jsonl", {"event": "finalized_by_stop",
                                                       "launch": int(launch), "at": utc_now()})
            finalize_launch(ev, int(launch), state["id"])
    finally:
        os.close(lock)
    last = latest_exit(ev)
    if last:
        print(f"Launch {last.get('launch')}: runner exit {last.get('exit_code')} "
              f"({last.get('runner_exit_meaning')}), OOMKilled={last.get('oom_killed')}.")
    print("Resume with `start` under the same conditions; `summary` shows what is decided.")
    return EXIT_OK


def latest_exit(ev: Evaluation) -> Optional[Dict[str, Any]]:
    root = ev.wrapper / "launches"
    if not root.is_dir():
        return None
    numbers = sorted(int(p.name) for p in root.iterdir() if p.name.isdigit())
    for number in reversed(numbers):
        record = read_json(ev.launch_dir(number) / "exit.json")
        if record is not None:
            return record
    return None


# ---------------------------------------------------------------------------
# status / summary（読み取り専用）
# ---------------------------------------------------------------------------


def _pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def host_state(ev: Evaluation) -> Dict[str, Any]:
    state = container_state(ev)
    holders = lock_holders(ev)
    return {
        "container": "absent" if state is None else state.get("status"),
        "container_launch": None if state is None else state.get("launch"),
        "lock_holders": holders,
    }


def tmp_entries(ev: Evaluation, state: Optional[Mapping[str, Any]]) -> List[Dict[str, Any]]:
    """tmp の entry を、実行中の execution のもの（container の起動以後）と残骸に分ける。"""
    if not ev.tmp.is_dir():
        return []
    started = _epoch((state or {}).get("started_at")) if state and state.get("running") else None
    rows = []
    for path in sorted(ev.tmp.iterdir()):
        try:
            created = path.lstat().st_mtime
        except OSError:
            continue
        current = started is not None and created >= started - 1
        rows.append({"name": path.name, "state": "current" if current else "leftover"})
    return rows


def command_status(ev: Evaluation, verify: bool) -> int:
    meta = read_json(ev.wrapper / "meta.json")
    state = container_state(ev)
    print(f"Evaluation {ev.eval_id}")
    print(f"  output:  {ev.out} ({'present' if ev.out.is_dir() else 'absent'})")
    print(f"  records: {ev.wrapper} ({'present' if meta else 'no meta.json'})")
    if isinstance(meta, dict):
        print(f"  fingerprint: {meta.get('fingerprint')}")
    if state is None:
        print("  container: absent")
    else:
        print(f"  container: {state.get('status')} (launch {state.get('launch')}, started "
              f"{state.get('started_at')}, exit {state.get('exit_code')})")
    holders = lock_holders(ev)
    print("  slot lock: " + ("free" if holders is None else
                             "held by pid " + (", ".join(map(str, holders)) or "unknown")))
    root = ev.wrapper / "launches"
    numbers = sorted(int(p.name) for p in root.iterdir() if p.name.isdigit()) if root.is_dir() else []
    for number in numbers:
        directory = ev.launch_dir(number)
        exit_record = read_json(directory / "exit.json")
        evidence = (directory / "evidence.json").exists()
        if exit_record is None:
            print(f"  launch {number}: {launch_kind(directory)}, no exit record yet")
        else:
            print(f"  launch {number}: {launch_kind(directory)}, exit "
                  f"{exit_record.get('exit_code')} ({exit_record.get('runner_exit_meaning')}), "
                  f"OOMKilled={exit_record.get('oom_killed')}, executions "
                  f"{exit_record.get('runtime_run_ids')}, evidence {'saved' if evidence else 'MISSING'}")
        rows = (directory / "watch.jsonl")
        if rows.exists():
            lines = rows.read_text(encoding="utf-8").splitlines()
            if lines:
                last = _parse_json(lines[-1]) or {}
                deltas = sum((_parse_json(line) or {}).get("oom_kill_delta") or 0 for line in lines)
                print(f"    watch: {len(lines)} sample(s), oom_kill increments {deltas}, last "
                      f"{last.get('at')} peak {last.get('memory_peak')} current "
                      f"{last.get('memory_current')}")
    if ev.out.is_dir():
        statuses = sum(1 for _ in ev.out.rglob("*.pair-status.json"))
        executions = existing_execution_ids(ev)
        print(f"  observed: {statuses} pair status file(s), {len(executions)} execution "
              "record(s) (not a verdict; `summary` reports what is decided)")
    entries = tmp_entries(ev, state)
    if entries:
        leftovers = [e["name"] for e in entries if e["state"] == "leftover"]
        print(f"  tmp: {len(entries)} entr(y/ies); {len(leftovers)} left by earlier executions "
              "(removed by the next start)" + (f": {', '.join(leftovers[:5])}" if leftovers else ""))
    if verify and ev.out.is_dir() and isinstance(meta, dict):
        image = meta["conditions"]["image"]["id"]
        completed = reader(ev, image, summarize_args(ev, "preflight"), timeout=3600)
        report = _parse_json(completed.stdout) or {}
        result = report.get("verify") or {}
        print(f"  execution_chain verify: {result.get('verdict')} "
              f"{json.dumps(result.get('reasons') or {}, sort_keys=True)} "
              f"({report.get('verify_seconds')}s)" if result else
              f"  execution_chain verify: unavailable ({report.get('verify_error') or completed.stderr.strip()[-300:]})")
    return EXIT_OK


def command_summary(ev: Evaluation, as_json: bool) -> int:
    meta = read_json(ev.wrapper / "meta.json")
    if not isinstance(meta, dict):
        print(f"No evaluation record at {ev.wrapper} (meta.json); nothing to summarize.",
              file=sys.stderr)
        return 2
    extra = ["--wrapper", ev.in_container(ev.wrapper), "--matrix", ev.matrix]
    if as_json:
        extra.append("--json")
    completed = reader(ev, meta["conditions"]["image"]["id"],
                       summarize_args(ev, "report", *extra),
                       env={"EVAL_HOST_STATE": json.dumps(host_state(ev))}, timeout=7200)
    sys.stdout.write(completed.stdout)
    if completed.returncode not in (0, 1, 2):
        sys.stderr.write(completed.stderr)
        return 2
    return completed.returncode


# ---------------------------------------------------------------------------


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--matrix", required=True, choices=sorted(RUNNERS))
    sub = parser.add_subparsers(dest="command", required=True)
    commands = {}
    for name in ("start", "status", "stop", "summary", "_supervise"):
        commands[name] = sub.add_parser(name)
        commands[name].add_argument("--freeze", default=None,
                                    help="the freeze commit (default: the worktree HEAD)")
        commands[name].add_argument("--tag", default=os.environ.get("EVAL_TAG", ""))
    commands["status"].add_argument("--verify", action="store_true")
    commands["summary"].add_argument("--json", action="store_true")
    commands["stop"].add_argument("--wait", type=float, default=3600.0)
    commands["_supervise"].add_argument("--launch", type=int, required=True)
    commands["_supervise"].add_argument("--lock-fd", type=int, required=True)
    args = parser.parse_args(argv)
    try:
        ev = resolve(args.matrix, freeze=args.freeze, tag=args.tag,
                     require_freeze=args.command == "start")
        if args.command == "start":
            return command_start(ev)
        if args.command == "status":
            return command_status(ev, args.verify)
        if args.command == "stop":
            return command_stop(ev, args.wait)
        if args.command == "summary":
            return command_summary(ev, args.json)
        return command_supervise(ev, args.launch, args.lock_fd)
    except Refused as exc:
        print(f"Refused (nothing was written): {exc}", file=sys.stderr)
        return EXIT_REFUSED
    except (WrapperError, OSError, subprocess.CalledProcessError) as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return EXIT_FAILED


if __name__ == "__main__":
    sys.exit(main())
