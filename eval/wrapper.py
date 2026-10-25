#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""全件評価の wrapper（評価計画 v2 PR-D）。入口は ``eval/neq.sh`` / ``eval/eq.sh``。

    eval/neq.sh start --freeze <commit>   # preflight → 背景で実行（再開を含む）
    eval/neq.sh status [--verify]         # 読み取り専用
    eval/neq.sh stop                      # 停止（猶予は runner の停止確認より長い）と、未完了の launch の回収
    eval/neq.sh summary [--json]          # 読み取り専用。完了の判定

**持たないもの**: 解析・確定・完全性・正式性の規則。完了は ``eval/summarize.py`` の
``completion`` だけが決め、``summary`` と ``start`` の「完了済み」は同じ結果を使う（検証器・
ledger・HEAD・fingerprint・wrapper の記録・container の状態を、それぞれの owner の判定から）。
runner の exit code は記録するが、完了の根拠にしない。

**持つもの**:

* identity（analysis config / source digest）の外にある実行条件の記録と照合。初回の ``start``
  で ``meta.json`` に書き、その要約（fingerprint）を ``EQBENCH_ENVIRONMENT_FINGERPRINT`` として
  runner に渡す。再開のたびに照合し、違えば何も書かずに拒否する。
* 評価の slot の lock（``flock -n``）。``start`` が取り、背景の supervisor が受け継ぐ（``docker
  run`` の CLI にも渡す）。launch が終端するまで保持する。
* launch の状態機械（``eval/records.py``）: 起動の要求 → container → 終了の記録 → 証拠 → 削除の
  確認。各段階は 1 回だけ確定する記録で、supervisor が途中で止まっても ``stop`` が続きから進める
  （``advance``）。container は終了と証拠を記録するまで消さない。
* 外部操作の観測は「取得できた」「存在しない」「観測できない」を区別する。観測できないときは
  fail-closed（記録しない・消さない・拒否する）。
* run tmpdir の片付け: lock を持ち、評価の container が無く、未完了の launch も無いことを
  確かめた後で、この評価専用の tmp に残った前回までの残骸を消す。

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
if str(EVAL_DIR) not in sys.path:
    sys.path.insert(0, str(EVAL_DIR))
import records  # noqa: E402  (eval/ の記録の形式と検査)
import protocol  # noqa: E402  (応答の受理と理由の分類の唯一の置き場所)

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
#: 環境の probe（runner の開始の記録と同じ行）に必ず含まれる key。
PROBE_KEYS = ("python_version", "ghidra_version", "java_version", "z3_version",
              "cgroup_memory_max", "cgroup_cpu_max")


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
# docker（外部操作の結果は「取得できた」「存在しない」「観測できない」を区別する）
# ---------------------------------------------------------------------------


class Unobservable(WrapperError):
    """外部の状態を観測できなかった（存在しない、とは区別する）。呼び出し側は fail-closed。"""


def docker(ev: Evaluation, *args: str, timeout: Optional[float] = None,
           pass_fds: Sequence[int] = ()) -> subprocess.CompletedProcess:
    """docker を 1 回呼ぶ。起動できない・時間切れは ``Unobservable``。exit code は呼び出し側が見る。"""
    try:
        return subprocess.run([ev.docker, *args], capture_output=True, text=True,
                              timeout=timeout, pass_fds=tuple(pass_fds))
    except (OSError, subprocess.SubprocessError) as exc:
        raise Unobservable(f"docker {args[0]}: {exc}") from exc


def docker_checked(ev: Evaluation, *args: str, timeout: Optional[float] = None) -> str:
    """成功しなければ ``Unobservable``（出力は使わない）。"""
    completed = docker(ev, *args, timeout=timeout)
    if completed.returncode != 0:
        raise Unobservable(f"docker {' '.join(args[:2])} failed ({completed.returncode}): "
                           f"{completed.stderr.strip()[-500:]}")
    return completed.stdout


_ABSENT = ("no such container", "no such object")


def image_id(ev: Evaluation, image: str) -> str:
    completed = docker(ev, "image", "inspect", "--format", "{{.Id}}", image)
    identifier = completed.stdout.strip()
    if completed.returncode != 0 or not re.fullmatch(r"sha256:[0-9a-f]{64}", identifier):
        raise Refused(f"image {image} is not available (exit {completed.returncode}, "
                      f"id {identifier[:80]!r}): {completed.stderr.strip()}")
    return identifier


def slot_containers(ev: Evaluation) -> List[Dict[str, str]]:
    """slot の label を持つ container（状態を問わない）。観測できなければ ``Unobservable``。"""
    output = docker_checked(ev, "ps", "-a", "--filter", f"label={LABEL_SLOT}=1", "--format",
                            "{{.Names}}\t{{.State}}\t{{.Label \"" + LABEL_EVAL + "\"}}")
    rows = []
    for line in output.splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) != 3 or not fields[0] or not fields[1]:
            raise Unobservable(f"docker ps gave a row that is not a container: {line[:120]!r}")
        rows.append({"name": fields[0], "state": fields[1], "eval": fields[2]})
    return rows


def other_running_containers(ev: Evaluation) -> Optional[List[str]]:
    """評価と reader 以外の動いている container。観測できなければ ``None``（「無い」ではない）。"""
    try:
        output = docker_checked(ev, "ps", "--format", "{{.Names}}\t{{.Label \"" + LABEL_SLOT
                                + "\"}}" + "\t{{.Label \"" + LABEL_READER + "\"}}")
    except Unobservable:
        return None
    names = []
    for line in output.splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) != 3 or not parts[0]:
            return None  # 形の違う応答は「他に無い」ではない
        if parts[1] != "1" and parts[2] != "1":
            names.append(parts[0])
    return sorted(names)


def inspect_container(ev: Evaluation, ref: str) -> Optional[Dict[str, Any]]:
    """container の状態。存在しなければ ``None``、観測できなければ ``Unobservable``。"""
    completed = docker(ev, "inspect", "--type", "container", ref, timeout=120)
    if completed.returncode != 0:
        if any(marker in completed.stderr.lower() for marker in _ABSENT):
            return None
        raise Unobservable(f"docker inspect {ref} failed ({completed.returncode}): "
                           f"{completed.stderr.strip()[-500:]}")
    try:
        payload = json.loads(completed.stdout)
        if not (isinstance(payload, list) and len(payload) == 1):
            raise ValueError("not exactly one container")
        payload = payload[0]
        state = payload["State"]
        labels = (payload.get("Config") or {}).get("Labels") or {}
        identifier = payload["Id"]
        if not (isinstance(identifier, str) and records._CONTAINER_ID.fullmatch(identifier)
                and isinstance(state, dict) and isinstance(state.get("Status"), str)
                and isinstance(state.get("Running"), bool) and isinstance(labels, dict)):
            raise ValueError("the inspect output does not describe a container")
    except (ValueError, IndexError, KeyError, TypeError) as exc:
        raise Unobservable(f"docker inspect {ref}: unreadable output ({exc})")
    return {
        "id": identifier, "status": state.get("Status"),
        "running": state.get("Running") is True, "exit_code": state.get("ExitCode"),
        "oom_killed": state.get("OOMKilled"), "error": state.get("Error"),
        "started_at": state.get("StartedAt"), "finished_at": state.get("FinishedAt"),
        "launch": labels.get(LABEL_LAUNCH), "eval": labels.get(LABEL_EVAL),
    }


def container_state(ev: Evaluation) -> Optional[Dict[str, Any]]:
    """この評価の container（名前で引く）。"""
    return inspect_container(ev, ev.container_name)


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


def read_json_from(ev: Evaluation, image: str, request: str, *extra: str,
                   env: Optional[Mapping[str, str]] = None) -> Dict[str, Any]:
    """reader に ``request`` を頼み、契約（``protocol.accept``: 終了コードと応答の形の両方）を
    満たす応答だけを返す。満たさなければ ``Unobservable``（何も確定させない）。"""
    completed = reader(ev, image, summarize_args(ev, request, *extra), env=env, timeout=7200)
    try:
        return protocol.accept(request, completed.returncode, completed.stdout)
    except protocol.Rejected as exc:
        raise Unobservable(f"the reader's {request} response was not accepted ({exc}); "
                           f"stderr: {completed.stderr.strip()[-500:]}") from exc


def summarize_args(ev: Evaluation, command: str, *extra: str) -> List[str]:
    return ["python3", "-B", "eval/summarize.py", command, "--repo", "/workspace/src",
            "--out", ev.in_container(ev.out), "--wrapper", ev.in_container(ev.wrapper),
            "--matrix", ev.matrix, *extra]


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


def holds_lock(ev: Evaluation, fd: int) -> bool:
    """``fd`` がこの評価の lock file を指し、その lock を持っている（または今取れた）か。"""
    try:
        if (os.fstat(fd).st_dev, os.fstat(fd).st_ino) != (
                os.stat(ev.lock_file).st_dev, os.stat(ev.lock_file).st_ino):
            return False
    except OSError:
        return False
    return try_lock(fd)


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
        if not sep or key in rows:
            raise Refused(f"the environment probe gave a malformed row: {line[:120]!r}")
        rows[key] = value
    rows.pop("environment_fingerprint", None)
    missing = sorted(set(PROBE_KEYS) - set(rows))
    if missing:
        # 途中で切れた応答を条件として記録しない（初回なら meta に入ってしまう）。
        raise Refused(f"the environment probe did not report {', '.join(missing)}")
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
    completion: Optional[Dict[str, Any]]
    leftovers: List[str]
    others: Optional[List[str]]


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
    try:
        present = slot_containers(ev)
    except Unobservable as exc:
        raise Refused(f"cannot observe the evaluation-slot containers: {exc}")
    if present:
        raise Refused("an evaluation-slot container exists (running or not removed): "
                      + ", ".join(f"{r['name']} ({r['state']})" for r in present)
                      + "; run `stop` on its evaluation to record and remove it")
    worktree_state(ev)
    minimum = int(os.environ.get("EVAL_MIN_FREE_GIB", DEFAULT_MIN_FREE_GIB)) * 2**30
    if free_bytes(ev.log_root if ev.log_root.exists() else ev.main / "logs") < minimum:
        raise Refused(f"less than {minimum // 2**30} GiB free under {ev.log_root}")
    if ev.out.exists() and not ev.out.is_dir():
        raise Refused(f"{ev.out} is not a directory")
    meta = read_json(ev.wrapper / records.META)
    meta = meta if isinstance(meta, dict) and meta.get("schema") == META_SCHEMA else None
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
    # 再開してよいかは、どの経路（初回・出力が無い・空・開始前の出力・通常の再開・完了後）でも
    # 同じ completion だけが決める。呼び出し側は判定を省略も複製もしない。
    try:
        completion = read_json_from(
            ev, profile["IMAGE"], "completion",
            env={"EVAL_HOST_STATE": json.dumps({"container": "absent", "observed": True})})
    except Unobservable as exc:
        raise Refused(f"cannot judge the evaluation: {exc}")
    leftovers = sorted(p.name for p in ev.tmp.iterdir()) if ev.tmp.is_dir() else []
    return Plan(profile=profile, conditions=conditions, fingerprint=fingerprint,
                first=meta is None and not ev.wrapper.exists(), completion=completion,
                leftovers=leftovers, others=other_running_containers(ev))


#: start の決定は protocol（理由の分類の owner）が持つ。ここは呼ぶだけ。
start_decision = protocol.start_decision


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
    """出力にある、開始の記録が確定した execution（launch が記録する母集合）。"""
    return records.started_executions(ev.out)


def next_launch(ev: Evaluation) -> int:
    root = ev.wrapper / records.LAUNCHES_DIR
    numbers = [int(p.name) for p in root.iterdir() if p.name.isdigit()] if root.is_dir() else []
    return max(numbers, default=0) + 1


def journal(ev: Evaluation, event: str, **fields: Any) -> None:
    append_jsonl(ev.wrapper / records.JOURNAL, {"event": event, "at": utc_now(), **fields})


def reservation(ev: Evaluation, event: str, launch: int) -> None:
    """slot の予約の記録（#130 §8.6 の慣習。診断で、判定には使わない）。"""
    try:
        append_jsonl(ev.lock_file.parent / "reservations.jsonl", {
            "event": event, "run_id": f"{ev.eval_id}-launch{launch}", "pid": os.getpid(),
            "at": utc_now()})
    except OSError as exc:
        print(f"Warning: reservation not recorded: {exc}", file=sys.stderr)


def commit_launch(ev: Evaluation, number: int, payload: Mapping[str, Any]) -> Path:
    """起動の要求を確定する: staging dir に ``launch.json`` を書き、rename 1 回で ``<n>`` にする。"""
    root = ev.wrapper / records.LAUNCHES_DIR
    final = root / str(number)
    if final.exists():
        raise WrapperError(f"{final} already exists")
    staging = root / records.staging_name(number, secrets.token_hex(4))
    staging.mkdir(mode=0o700)
    write_json(staging / records.LAUNCH, payload, exclusive=True)
    os.rename(staging, final)
    _fsync_dir(root)
    return final


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
        decision, detail = start_decision(plan.completion)
    except Refused as exc:
        print(f"Refused (nothing was written): {exc}", file=sys.stderr)
        return EXIT_REFUSED
    if decision == protocol.DECISION_COMPLETE:
        print("The evaluation is complete (the same verdict `summary` gives: chain, ledger, "
              "HEAD, fingerprint, wrapper records and container state); nothing was started "
              "or written.")
        return EXIT_OK
    if decision == protocol.DECISION_REFUSE:
        print(f"Refused (nothing was written): {detail}", file=sys.stderr)
        return EXIT_REFUSED
    for path in (ev.repo / "targets", ev.repo / "logs"):
        # container の mount 点（無ければ docker が root 所有で作る）。
        path.mkdir(exist_ok=True)
    if plan.first:
        # wrapper の dir は meta.json ごと rename 1 回で確定する（途中で止まると staging dir が
        # 残るだけで、「meta.json の無い wrapper の dir」は作らない）。
        ev.log_root.mkdir(parents=True, exist_ok=True)
        staging = ev.log_root / f".{ev.wrapper.name}{records.STAGING_MARK}{secrets.token_hex(4)}"
        staging.mkdir(mode=0o700)
        write_json(staging / records.META, {
            "schema": META_SCHEMA, "eval_id": ev.eval_id, "created_at": utc_now(),
            "conditions": plan.conditions, "fingerprint": plan.fingerprint,
            "observations": host_observations(ev),
        }, exclusive=True)
        os.rename(staging, ev.wrapper)
        _fsync_dir(ev.log_root)
    for path in (ev.tmp, ev.authority, ev.wrapper / records.LAUNCHES_DIR):
        path.mkdir(mode=0o700, exist_ok=True)
    number = next_launch(ev)
    journal(ev, "start_requested", planned_launch=number)
    removed = clean_leftovers(ev, plan.leftovers)
    moved_aside = None
    if plan.completion["output_state"] == protocol.OUTPUT_NEVER_STARTED:
        # 判定（completion）が再開を許した後でだけ、開始の記録の前に止まった出力を退避する。
        # 退避の可否は同じ owner（records.output_state）で lock の下に確かめ直す。
        if records.output_state(ev.out) != protocol.OUTPUT_NEVER_STARTED:
            raise WrapperError(f"{ev.out} changed since it was judged; nothing was moved")
        aside = ev.wrapper / "aborted-outputs" / f"{utc_now()}-{secrets.token_hex(3)}"
        aside.parent.mkdir(exist_ok=True)
        os.rename(ev.out, aside)
        moved_aside = str(aside)
        print(f"The output held only the start of an execution that stopped before it recorded "
              f"its start (no pair was started); moved it aside to {aside}")
    before = existing_execution_ids(ev)
    directory = commit_launch(ev, number, {
        "schema": records.LAUNCH_SCHEMA, "launch": number, "requested_at": utc_now(),
        "fingerprint": plan.fingerprint, "execution_ids_before": before,
        "output_before": records.output_fingerprint(ev.out),
        "removed_leftovers": removed, "other_running_containers": plan.others,
        "moved_aside_output": moved_aside,
        "completion_before": None if plan.completion is None else {
            "verdict": plan.completion.get("verdict"),
            "reasons": plan.completion.get("reasons")},
        "kind": "resume" if before else "first",
    })
    journal(ev, "launch_requested", launch=number)
    if removed:
        print(f"Removed {len(removed)} leftover entr(y/ies) of earlier executions from {ev.tmp}")
    if plan.others:
        print("Warning: other containers are running: " + ", ".join(plan.others))
    os.set_inheritable(lock, True)
    with open(directory / records.SUPERVISOR_LOG, "ab") as log:
        process = subprocess.Popen(
            [sys.executable, "-B", str(Path(__file__).resolve()), "--matrix", ev.matrix,
             "_supervise", "--freeze", ev.commit, "--tag", ev.tag, "--launch", str(number),
             "--lock-fd", str(lock)],
            stdin=subprocess.DEVNULL, stdout=log, stderr=log, pass_fds=(lock,),
            start_new_session=True, env=dict(os.environ))
    deadline = time.monotonic() + START_CONFIRM_SECONDS
    while time.monotonic() < deadline:
        launch = records.read_launch(directory, number)
        if launch.container is not None:
            print(f"Started launch {number} ({launch.launch.get('kind')}): container "
                  f"{ev.container_name} {launch.container_id[:12]}, supervisor pid {process.pid}.")
            print(f"Output: {ev.out}\nRecords: {directory}\nFollow it with `status`; "
                  f"stop it with `stop`.")
            return EXIT_OK
        if launch.exit is not None or process.poll() is not None:
            print(f"Error: launch {number} did not start a container ({launch.state}); see "
                  f"{directory / records.SUPERVISOR_LOG}"
                  + ("" if launch.terminal else "; run `stop` to record it"), file=sys.stderr)
            return EXIT_FAILED
        time.sleep(0.5)
    print(f"Warning: the container has not started within {START_CONFIRM_SECONDS:.0f}s; "
          f"check `status` and {directory / records.SUPERVISOR_LOG}", file=sys.stderr)
    return EXIT_FAILED


def host_observations(ev: Evaluation) -> Dict[str, Any]:
    """照合しない参考の記録（docker の version など）。観測できなければ null。"""
    try:
        version = docker_checked(ev, "version", "--format", "{{.Server.Version}}").strip()
    except Unobservable:
        version = None
    return {"docker_server": version or None, "kernel": os.uname().release,
            "hostname": os.uname().nodename}


# ---------------------------------------------------------------------------
# launch の進行（supervisor と stop の回収が共有する）
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
    """1 回の cgroup の観測。読めなければ ``observed: false``（0 にしない）。"""
    directory = Path(os.environ.get("EVAL_CGROUP_TEMPLATE", CGROUP_TEMPLATE).format(id=container_id))
    values: Dict[str, Any] = {"observed": True}
    try:
        events = {}
        for line in (directory / "memory.events").read_text().splitlines():
            key, _sep, value = line.partition(" ")
            events[key] = value.strip()
        for key in ("oom", "oom_kill"):
            if not events.get(key, "").isdigit():
                raise ValueError(f"memory.events has no {key}")
            values[key] = int(events[key])
        for name, key in (("memory.peak", "memory_peak"), ("memory.current", "memory_current")):
            text = (directory / name).read_text().strip()
            values[key] = int(text) if text.isdigit() else None
    except (OSError, ValueError) as exc:
        return {"observed": False, "error": f"{type(exc).__name__}: {exc}"[:200]}
    return values


class _Stop:
    requested = False


def _launch(ev: Evaluation, number: int) -> records.Launch:
    launch = records.read_launch(ev.launch_dir(number), number)
    if launch.state == records.STATE_DAMAGED:
        raise WrapperError(f"launch {number} records are damaged: {'; '.join(launch.problems)}")
    return launch


def record_container(ev: Evaluation, number: int, container_id: str, how: str) -> None:
    write_json(ev.launch_dir(number) / records.CONTAINER, {
        "schema": records.CONTAINER_SCHEMA, "container_id": container_id,
        "name": ev.container_name, "recorded_at": utc_now(), "how": how,
    }, exclusive=True)
    journal(ev, "container_recorded", launch=number, container=container_id[:12], how=how)


def _new_executions(ev: Evaluation, launch: records.Launch) -> List[str]:
    before = set((launch.launch or {}).get("execution_ids_before") or [])
    return [run_id for run_id in existing_execution_ids(ev) if run_id not in before]


def _exit_payload(ev: Evaluation, launch: records.Launch, kind: str, **fields: Any) -> Dict[str, Any]:
    return {"schema": records.EXIT_SCHEMA, "kind": kind, "launch": launch.number,
            "container_id": launch.container_id, "recorded_at": utc_now(),
            "runtime_run_ids": [] if kind == records.KIND_NOT_STARTED else _new_executions(ev, launch),
            **fields}


def save_runner_log(ev: Evaluation, launch: records.Launch) -> Tuple[str, int]:
    """``docker logs`` の出力（stdout と stderr を時系列で 1 つに）。失敗の出力は保存しない。"""
    directory = ev.launch_dir(launch.number)
    final = directory / records.RUNNER_LOG
    temporary = directory / f".{records.RUNNER_LOG}.tmp-{os.getpid()}-{secrets.token_hex(4)}"
    try:
        with open(temporary, "xb") as stream:
            try:
                completed = subprocess.run([ev.docker, "logs", launch.container_id],
                                           stdout=stream, stderr=subprocess.STDOUT, timeout=3600)
            except (OSError, subprocess.SubprocessError) as exc:
                raise Unobservable(f"docker logs: {exc}") from exc
            if completed.returncode != 0:
                raise Unobservable(f"docker logs failed ({completed.returncode}); its output "
                                   f"was not saved")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, final)
        _fsync_dir(directory)
    finally:
        if temporary.exists():
            temporary.unlink()
    digest = records._sha256_file(final)
    if digest is None:
        raise Unobservable(f"{final} cannot be read back")
    return digest


def capture_evidence(ev: Evaluation, launch: records.Launch) -> None:
    meta = read_json(ev.wrapper / records.META) or {}
    image = ((meta.get("conditions") or {}).get("image") or {}).get("id")
    try:
        evidence = read_json_from(ev, image, "launch-evidence")
    except Unobservable as exc:
        journal(ev, "evidence_failed", launch=launch.number, detail=str(exc)[-500:])
        raise
    write_json(ev.launch_dir(launch.number) / records.EVIDENCE, evidence, exclusive=True)
    journal(ev, "evidence_recorded", launch=launch.number)


def remove_container(ev: Evaluation, container_id: str) -> None:
    """消して、「存在しない」と観測できるまで確かめる。観測できなければ失敗。"""
    removed = docker(ev, "rm", container_id, timeout=300)
    if removed.returncode != 0 and inspect_container(ev, container_id) is not None:
        raise Unobservable(f"docker rm {container_id[:12]} failed: {removed.stderr.strip()[-300:]}")
    deadline = time.monotonic() + REMOVE_CONFIRM_SECONDS
    while inspect_container(ev, container_id) is not None:
        if time.monotonic() > deadline:
            raise Unobservable(f"container {container_id[:12]} is still present after docker rm")
        time.sleep(1.0)


def advance(ev: Evaluation, number: int, *, watch_running: bool) -> records.Launch:
    """launch を終端（released）まで進める。各段階は確定した記録から再開できる。

    失敗（観測できない・記録できない）は例外にし、それまでの記録はそのまま残す。container は
    終了の記録と証拠の記録が済むまで消さないので、``stop`` が続きから回収できる。
    """
    last_observation: Optional[Dict[str, Any]] = None
    write_failures = 0
    while True:
        launch = _launch(ev, number)
        state = launch.state
        if state == records.STATE_RELEASED:
            return launch
        if state == records.STATE_REQUESTED:
            found = container_state(ev)
            if found is None:
                # container の記録が無く、container も無い。container が作られなかったのか、
                # 動いて wrapper の外で消されたのかを、要求の時点の出力と比べて区別する。
                # 区別できなければ（要求の時点の記録が無い）「作られなかった」とは言わない。
                new = _new_executions(ev, launch)
                launch_record = launch.launch or {}
                changed = ("output_before" not in launch_record
                           or records.output_fingerprint(ev.out) != launch_record["output_before"])
                ran = bool(new) or changed
                kind = records.KIND_EXIT_UNOBSERVED if ran else records.KIND_NOT_STARTED
                write_json(ev.launch_dir(number) / records.EXIT, _exit_payload(
                    ev, launch, kind, reason=(
                        "no container exists and none was recorded, but the output changed "
                        "after the launch was requested: a container ran and was removed "
                        "outside the wrapper" if ran else "no container was created (docker "
                        "run failed, or the launch stopped before it); the output is as it was "
                        "when the launch was requested")), exclusive=True)
                journal(ev, "exit_recorded", launch=number, kind=kind)
                continue
            if found.get("eval") != ev.eval_id or found.get("launch") != str(number):
                raise WrapperError(f"container {ev.container_name} belongs to launch "
                                   f"{found.get('launch')}, not to the unfinished launch {number}")
            record_container(ev, number, found["id"], "found by inspect after the launch "
                             "stopped before recording it")
            continue
        if state == records.STATE_CONTAINER:
            found = inspect_container(ev, launch.container_id)
            if found is not None and found["running"]:
                if not watch_running:
                    raise WrapperError(f"container {launch.container_id[:12]} is still running")
                last_observation, write_failures = watch(ev, number, launch.container_id)
                continue
            if found is None:
                write_json(ev.launch_dir(number) / records.EXIT, _exit_payload(
                    ev, launch, records.KIND_EXIT_UNOBSERVED,
                    reason="the container was removed before its exit was recorded"),
                    exclusive=True)
                journal(ev, "exit_recorded", launch=number, kind=records.KIND_EXIT_UNOBSERVED)
                continue
            sha, size = save_runner_log(ev, launch)
            write_json(ev.launch_dir(number) / records.EXIT, _exit_payload(
                ev, launch, records.KIND_RAN, docker_status=found.get("status"),
                exit_code=found.get("exit_code"), oom_killed=found.get("oom_killed"),
                docker_error=found.get("error"), started_at=found.get("started_at"),
                finished_at=found.get("finished_at"),
                finished_at_epoch=_epoch(found.get("finished_at")),
                runner_exit_meaning=runner_exit_meaning(found.get("exit_code"), found.get("status")),
                runner_log={"sha256": sha, "bytes": size},
                last_observation=last_observation, watch_write_failures=write_failures,
            ), exclusive=True)
            journal(ev, "exit_recorded", launch=number, kind=records.KIND_RAN,
                    exit_code=found.get("exit_code"), oom_killed=found.get("oom_killed"))
            continue
        if state == records.STATE_EXIT and launch.exit_kind != records.KIND_NOT_STARTED:
            capture_evidence(ev, launch)
            continue
        # 証拠まで記録した（または container が作られなかった）: 消して確かめてから終える。
        if launch.exit_kind != records.KIND_NOT_STARTED and launch.container_id:
            remove_container(ev, launch.container_id)
        write_json(ev.launch_dir(number) / records.RELEASED, {
            "schema": records.RELEASED_SCHEMA, "container_id": launch.container_id,
            "recorded_at": utc_now(),
        }, exclusive=True)
        journal(ev, "released", launch=number)


def command_supervise(ev: Evaluation, number: int, lock_fd: int) -> int:
    if not holds_lock(ev, lock_fd):
        print(f"Error: the supervisor of launch {number} does not hold the evaluation lock",
              file=sys.stderr)
        return EXIT_FAILED

    def on_signal(_signum, _frame):
        _Stop.requested = True

    for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(signum, on_signal)
    reservation(ev, "start", number)
    try:
        launch = _launch(ev, number)
        if launch.state != records.STATE_REQUESTED:
            raise WrapperError(f"launch {number} is {launch.state}, not requested")
        meta = read_json(ev.wrapper / records.META)
        command = runner_command(ev, meta["conditions"], meta["fingerprint"], number)
        # `docker run` の CLI にも lock を持たせる: supervisor が途中で死んでも、container の
        # 作成が終わるまで回収（stop）は lock を取れない。
        started = docker(ev, *command, pass_fds=(lock_fd,), timeout=600)
        identifier = started.stdout.strip()
        if started.returncode == 0 and records._CONTAINER_ID.fullmatch(identifier):
            record_container(ev, number, identifier, "docker run")
        else:
            journal(ev, "container_start_failed", launch=number,
                    detail=started.stderr.strip()[-1000:])
            print(f"docker run failed ({started.returncode}): {started.stderr.strip()[-1000:]}",
                  file=sys.stderr)
        launch = advance(ev, number, watch_running=True)
        return EXIT_OK if launch.exit_kind == records.KIND_RAN else EXIT_FAILED
    finally:
        reservation(ev, "end", number)
        os.close(lock_fd)


def watch(ev: Evaluation, number: int, container: str) -> Tuple[Optional[Dict[str, Any]], int]:
    """container の終了を待ちながら cgroup を観測し、**すべての観測を** 1 行ずつ保存する。

    返り値は（最後の有効な観測、保存できなかった観測の数）。終了は ``docker wait`` の終わりと、
    inspect で「動いていない／存在しない」を観測したことの両方で決める（観測できなければ待ち続ける）。
    """
    path = ev.launch_dir(number) / records.WATCH
    grace = str((read_json(ev.wrapper / records.META) or {})["conditions"]["container"]
                ["stop_grace_seconds"])

    def new_waiter() -> subprocess.Popen:
        return subprocess.Popen([ev.docker, "wait", container], stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL)

    waiter = new_waiter()
    last_valid: Optional[Dict[str, Any]] = None
    failures = 0
    last_period = 0.0
    stop_sent = False
    next_poll = 0.0
    while True:
        if waiter.poll() is not None:
            try:
                found = inspect_container(ev, container)
            except Unobservable:
                found = {"running": True}  # 分からなければ終わったとしない
            if found is None or not found["running"]:
                return last_valid, failures
            waiter = new_waiter()
        now = time.monotonic()
        if _Stop.requested and not stop_sent:
            # supervisor 自身が止められた: container にも正規の停止を送る（猶予付き）。
            subprocess.Popen([ev.docker, "stop", "-t", grace, container],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            try:
                journal(ev, "stop_forwarded_by_supervisor", launch=number)
            except OSError:
                pass
            stop_sent = True
        if now >= next_poll:
            next_poll = now + WATCH_POLL_SECONDS
            row = {"at": utc_now(), "at_epoch": time.time(), **read_cgroup(container)}
            if row["observed"]:
                last_valid = row
            if now - last_period >= WATCH_PERIOD_SECONDS:
                row["other_running_containers"] = other_running_containers(ev)
                last_period = now
            try:
                append_jsonl(path, row)
            except OSError:
                # 保存できなかった観測は数えるだけ（前後の観測がその区間を覆う）。
                failures += 1
        time.sleep(min(1.0, WATCH_POLL_SECONDS))


def runner_exit_meaning(code: Any, status: Any = None) -> str:
    """runner の exit code の意味（記録用。完了の根拠にはしない）。"""
    if status == "created":
        return "never started (created only)"
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
# stop（停止と回収）
# ---------------------------------------------------------------------------


def command_stop(ev: Evaluation, wait_seconds: float) -> int:
    meta = read_json(ev.wrapper / records.META) or {}
    grace = ((meta.get("conditions") or {}).get("container") or {}).get("stop_grace_seconds")
    try:
        state = container_state(ev)
    except Unobservable as exc:
        print(f"Error: cannot observe the container: {exc}", file=sys.stderr)
        return EXIT_FAILED
    if state is None:
        print(f"No container of this evaluation ({ev.container_name}).")
    elif state["running"]:
        if not isinstance(grace, int):
            print("Error: meta.json gives no stop grace; refusing to guess one", file=sys.stderr)
            return EXIT_FAILED
        print(f"Stopping {ev.container_name} (grace {grace}s; the runner confirms its own "
              "processes stopped before it exits)...")
        journal(ev, "stop_requested", launch=state.get("launch"))
        stopped = docker(ev, "stop", "-t", str(grace), ev.container_name, timeout=grace + 60)
        if stopped.returncode != 0:
            print(f"Error: docker stop failed ({stopped.returncode}): "
                  f"{stopped.stderr.strip()[-500:]}; nothing was recorded", file=sys.stderr)
            return EXIT_FAILED
    # supervisor が記録と削除を終えて lock を離すまで待つ。居なければ自分で回収する。
    lock = open_lock(ev)
    try:
        deadline = time.monotonic() + wait_seconds
        while not try_lock(lock):
            if time.monotonic() > deadline:
                print(f"Error: the supervisor still holds the lock after {wait_seconds:.0f}s; "
                      "see `status`", file=sys.stderr)
                return EXIT_FAILED
            time.sleep(1.0)
        return _recover_locked(ev)
    except (WrapperError, OSError) as exc:
        print(f"Error: the launch could not be recorded to the end: {exc}; its records so far "
              "are kept, and `stop` continues from them", file=sys.stderr)
        return EXIT_FAILED
    finally:
        os.close(lock)


def _recover_locked(ev: Evaluation) -> int:
    check = records.read_records(ev.wrapper)
    if check.damaged:
        print("Error: the wrapper records are damaged; nothing was changed:\n  "
              + "\n  ".join(check.problems), file=sys.stderr)
        return EXIT_FAILED
    found = container_state(ev)
    if found is not None and (check.unfinished is None
                              or found.get("launch") != str(check.unfinished.number)
                              or found.get("eval") != ev.eval_id):
        print(f"Error: container {ev.container_name} (launch {found.get('launch')}, "
              f"{found.get('status')}) does not belong to an unfinished launch of this "
              "evaluation; inspect it by hand", file=sys.stderr)
        return EXIT_FAILED
    if found is not None and found["running"]:
        print("Error: the container is running but nothing holds the evaluation lock; "
              "stop it again", file=sys.stderr)
        return EXIT_FAILED
    if check.unfinished is not None:
        number = check.unfinished.number
        print(f"Recording launch {number} from its records ({check.unfinished.state}).")
        journal(ev, "recovered_by_stop", launch=number, state=check.unfinished.state)
        advance(ev, number, watch_running=False)
    last = check.launches[-1] if check.launches else None
    if last is not None:
        launch = records.read_launch(ev.launch_dir(last.number), last.number)
        exit_record = launch.exit or {}
        print(f"Launch {launch.number}: {launch.state}, {exit_record.get('kind')}, runner exit "
              f"{exit_record.get('exit_code')} ({exit_record.get('runner_exit_meaning')}), "
              f"OOMKilled={exit_record.get('oom_killed')}.")
    print("Resume with `start` under the same conditions; `summary` shows what is decided.")
    return EXIT_OK


# ---------------------------------------------------------------------------
# status / summary（読み取り専用）
# ---------------------------------------------------------------------------


def host_state(ev: Evaluation) -> Dict[str, Any]:
    """container と lock の観測（summarize に渡す）。観測できなければそう書く。"""
    try:
        state = container_state(ev)
        container = "absent" if state is None else state.get("status")
        observed = True
    except Unobservable as exc:
        state, container, observed = None, "unobservable", False
        print(f"Warning: {exc}", file=sys.stderr)
    return {"container": container, "observed": observed,
            "container_launch": None if state is None else state.get("launch"),
            "lock_holders": lock_holders(ev)}


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
    meta = read_json(ev.wrapper / records.META)
    print(f"Evaluation {ev.eval_id}")
    print(f"  output:  {ev.out} ({'present' if ev.out.is_dir() else 'absent'})")
    print(f"  records: {ev.wrapper} ({'present' if meta else 'no meta.json'})")
    if isinstance(meta, dict):
        print(f"  fingerprint: {meta.get('fingerprint')}")
    try:
        state = container_state(ev)
        print("  container: absent" if state is None else
              f"  container: {state.get('status')} (launch {state.get('launch')}, started "
              f"{state.get('started_at')}, exit {state.get('exit_code')})")
    except Unobservable as exc:
        state = None
        print(f"  container: unobservable ({exc})")
    holders = lock_holders(ev)
    print("  slot lock: " + ("free" if holders is None else
                             "held by pid " + (", ".join(map(str, holders)) or "unknown")))
    check = records.read_records(ev.wrapper)
    for launch in check.launches:
        exit_record = launch.exit or {}
        print(f"  launch {launch.number}: {launch.state}, {(launch.launch or {}).get('kind')}, "
              f"exit {exit_record.get('kind')} {exit_record.get('exit_code')} "
              f"({exit_record.get('runner_exit_meaning')}), OOMKilled="
              f"{exit_record.get('oom_killed')}, executions {exit_record.get('runtime_run_ids')}")
        observed = [row for row in launch.watch if row.get("observed")]
        if launch.watch:
            last = observed[-1] if observed else {}
            print(f"    watch: {len(launch.watch)} observation(s), {len(launch.watch) - len(observed)}"
                  f" unobserved, oom_kill {last.get('oom_kill')}, last {last.get('at')} peak "
                  f"{last.get('memory_peak')} current {last.get('memory_current')}")
    if check.unfinished is not None:
        print(f"  launch {check.unfinished.number} is unfinished ({check.unfinished.state}): "
              + ("its supervisor holds the lock" if holders else "run `stop` to record it"))
    for problem in check.problems:
        print(f"  DAMAGED: {problem}")
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
        try:
            report = read_json_from(ev, meta["conditions"]["image"]["id"], "verify")
            result = report.get("verify") or {}
            print(f"  execution_chain verify: {result.get('verdict')} "
                  f"{json.dumps(result.get('reasons') or {}, sort_keys=True)} "
                  f"({report.get('verify_seconds')}s)" if result else
                  f"  execution_chain verify: failed ({report.get('verify_error')})")
        except Unobservable as exc:
            print(f"  execution_chain verify: unavailable ({exc})")
    return EXIT_OK


def command_summary(ev: Evaluation, as_json: bool) -> int:
    """reader の ``report`` を契約どおりに受理してから表示する（終了コードは受理した結果から）。"""
    meta = read_json(ev.wrapper / records.META)
    if not isinstance(meta, dict):
        print(f"No evaluation record at {ev.wrapper} (meta.json); nothing to summarize.",
              file=sys.stderr)
        return protocol.EXIT_BY_VERDICT[protocol.VERDICT_UNVERIFIABLE]
    try:
        result = read_json_from(ev, meta["conditions"]["image"]["id"], "report", "--json",
                                env={"EVAL_HOST_STATE": json.dumps(host_state(ev))})
    except Unobservable as exc:
        print(f"Error: the summary cannot be produced: {exc}", file=sys.stderr)
        return protocol.EXIT_BY_VERDICT[protocol.VERDICT_UNVERIFIABLE]
    import summarize

    if as_json:
        print(json.dumps(result, indent=1, sort_keys=True, default=str))
    else:
        sys.stdout.write(summarize.format_report(result))
    return protocol.summary_exit_code(result)


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
