# -*- coding: utf-8 -*-
"""Issue #170 (PR-R1): 秘密鍵の keyset identity、keyset lock の capability、鍵の具体化。

固定している不変条件（計画 v5 の §0 C-L key 行 / §6 / PR-R1）:

* **keyset identity**: keyset は ``<realpath(private root)>/<1 つの path component>`` で、
  symlink でなく、OUTPUT と分離している（同一でも、包含でも、被包含でもない）。組み立てと判定の
  owner は ``validation_resolve_authority_keyset`` / ``_validation_check_authority_keyset`` だけで、
  lock と writer も同じ判定にかけ直す。したがって秘密鍵・HMAC 鍵は OUTPUT の外にある。
* **lock capability**: 鍵を書けるのは、この process が ``validation_lock_authority_keyset`` で取得し、
  いまも所有している排他 flock（kernel の fdinfo で証明）の keyset の直下だけ。shell 変数の偽装・
  stale な state・再利用された fd 番号・別の keyset の lock・環境由来の state では書けない（exit 2）。
* **unlock**: 自分が取得した lock（所有の証明が成り立つ fd）以外は閉じない。
* keyset の inode ごとに、鍵の guard・具体化を実行するのは同時に 1 つだけ。待ちは上限付きで、
  超えた run は「held by another run for too long」で exit 1、keyset にも key root にも触れない。
* 鍵を具体化する規則の owner は ``validation_materialize_pair_status_keypair`` と
  ``validation_materialize_process_key`` だけ。runner は鍵 CLI も ``/dev/urandom`` も直接使わない。
* 失敗はメッセージ付きの非 0 で、Python の traceback を出さない。

oracle は実装と独立に置く（keyset と OUTPUT の重なりは Python の realpath で求め、capability は
「lock が作った state 以外の全ての遷移」で書けないこと・fd を閉じないことを確かめる）。

runner は実物を使う。tmp に repo の形（runner と ``scripts`` への symlink、Neq の
sample 1 つ）を作り、``PYTHON_BIN`` の stub が鍵 CLI（gen / exp / val）を実物の
``pair_status_authority`` へ通しつつ barrier を置き、鍵の窓を抜けた直後の最初の
python 呼び出しで runner を exit 77 で止める。
"""

from __future__ import annotations

import fcntl
import hashlib
import os
import re
import subprocess
import sys
import time
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[4]
COMMON = REPO_ROOT / "scripts" / "validation_matrix_common.sh"
RUNNERS = {"eq": "eqbench_run_all_32jobs.sh", "neq": "neqbench_run_all_32jobs.sh"}
KEY_MODULE = "scripts.function_tracer_pcode.authority.decision.pair_status_authority"
PRIVATE_KEY = "pair-status-ed25519.key"
PUBLIC_KEY = "pair-status-verification-key.json"
STOPPED_AFTER_KEYS = 77
RUNNER_TIMEOUT = 180

_STUB = r"""#!/usr/bin/env bash
# PYTHON_BIN stub: 鍵 CLI は実物へ通す（barrier 付き）。鍵の窓を抜けたら exit 77。
G="${GATE_DIR:?}"; L="${GATE_LABEL:?}"; a="$*"
log() { printf '%s %s\n' "$L" "$*" >> "$G/events.log"; }
op=""
case "$a" in
  *pair_status_authority*--generate-private-key*) op=gen ;;
  *pair_status_authority*--export-public-from-private*) op=exp ;;
  *pair_status_authority*--validate-private-key*) op=val ;;
esac
if [[ -n "$op" ]]; then
  if [[ -e "$G/$L.$op.hold" ]]; then
    log "arrive $op"
    cat "$G/$L.$op.go" > /dev/null
  fi
  "$REAL_PYTHON" -B "$@"; rc=$?
  log "op $op $rc"
  if [[ "$op" == val && "$rc" == 0 ]]; then : > "$G/$L.keysdone"; fi
  exit "$rc"
fi
if [[ -e "$G/$L.keysdone" ]]; then
  inherited=0
  for f in /proc/$$/fd/*; do
    [[ "$(readlink "$f" 2>/dev/null)" == "${GATE_KEYSET:-/nonexistent}" ]] && inherited=$((inherited + 1))
  done
  log "stop inherited=$inherited"
  exit 77
fi
exec "$REAL_PYTHON" -B "$@"
"""

_SCRUBBED_ENV_PREFIXES = ("EQBENCH_", "NEQ_", "VALIDATION_", "GATE_")
_SCRUBBED_ENV = {"DRY_RUN", "OUTPUT_BASE_DIR", "PYTHON_BIN", "PARALLEL_JOBS"}


# ---------------------------------------------------------------------------
# harness
# ---------------------------------------------------------------------------


class Harness:
    """tmp の repo と gate。runner はここから起動する。"""

    def __init__(self, root: Path):
        self.root = root
        self.repo = root / "repo"
        self.repo.mkdir(parents=True)
        for script in RUNNERS.values():
            (self.repo / script).symlink_to(REPO_ROOT / script)
        (self.repo / "scripts").symlink_to(REPO_ROOT / "scripts")
        sample = self.repo / "targets" / "EqBench" / "benchmarks" / "S" / "Neq"
        sample.mkdir(parents=True)
        (sample / "newV.c").write_text("int f(int x) { return x; }\n", encoding="utf-8")
        (sample / "oldV.c").write_text("int f(int x) { return x + 1; }\n", encoding="utf-8")
        self.gate = root / "gate"
        self.gate.mkdir()
        (self.gate / "events.log").write_text("", encoding="utf-8")
        self.stub = root / "python-stub"
        self.stub.write_text(_STUB, encoding="utf-8")
        self.stub.chmod(0o755)
        self.key_root = root / "keys"
        self.procs: dict[str, subprocess.Popen] = {}

    # -- runner ------------------------------------------------------------

    def env(self, kind: str, label: str, output: Path, **extra: str) -> dict[str, str]:
        env = {
            key: value for key, value in os.environ.items()
            if key not in _SCRUBBED_ENV and not key.startswith(_SCRUBBED_ENV_PREFIXES)
        }
        env.update({
            "OUTPUT_BASE_DIR": str(output),
            "EQBENCH_TMPDIR": str(self.root / "tmpdir"),
            "EQBENCH_PRIVATE_AUTHORITY_ROOT": str(self.key_root),
            "PYTHON_BIN": str(self.stub),
            "REAL_PYTHON": sys.executable,
            "GATE_DIR": str(self.gate),
            "GATE_LABEL": label,
            "PARALLEL_JOBS": "1",
        })
        if kind == "eq":
            env.update({
                "EQBENCH_RUN_SCOPE": "REPRESENTATIVE",
                "EQBENCH_BUILD_POLICY": "PREBUILT_ONLY",
            })
        else:
            env.update({"NEQ_RUN_SCOPE": "REPRESENTATIVE"})
        env.update(extra)
        return env

    def start(self, kind: str, label: str, output: Path, **extra: str) -> subprocess.Popen:
        env = self.env(kind, label, output, **extra)
        proc = subprocess.Popen(
            ["bash", str(self.repo / RUNNERS[kind])],
            cwd=self.root,
            env=env,
            stdout=open(self.root / f"{label}.out", "w"),
            stderr=open(self.root / f"{label}.err", "w"),
            start_new_session=True,
        )
        self.procs[label] = proc
        return proc

    def run(self, kind: str, label: str, output: Path, **extra: str) -> tuple[int, str]:
        proc = self.start(kind, label, output, **extra)
        return self.finish(label), self.stderr(label)

    def finish(self, label: str) -> int:
        return self.procs[label].wait(timeout=RUNNER_TIMEOUT)

    def stderr(self, label: str) -> str:
        return (self.root / f"{label}.err").read_text(encoding="utf-8")

    def kill_all(self) -> None:
        for proc in self.procs.values():
            if proc.poll() is None:
                try:
                    os.killpg(proc.pid, 9)
                except ProcessLookupError:
                    pass
                proc.wait(timeout=30)

    # -- gate --------------------------------------------------------------

    def hold(self, label: str, op: str) -> None:
        (self.gate / f"{label}.{op}.hold").touch()
        os.mkfifo(self.gate / f"{label}.{op}.go")

    def release(self, label: str, op: str) -> None:
        fd = os.open(self.gate / f"{label}.{op}.go", os.O_WRONLY | os.O_NONBLOCK)
        os.write(fd, b"go\n")
        os.close(fd)

    def events(self, label: str) -> list[str]:
        lines = (self.gate / "events.log").read_text(encoding="utf-8").splitlines()
        return [line.split(" ", 1)[1] for line in lines if line.split(" ", 1)[0] == label]

    def key_ops(self, label: str) -> list[str]:
        return [event.split()[1] for event in self.events(label) if event.startswith("op ")]

    def wait_arrive(self, label: str, op: str, timeout: float = 90.0) -> None:
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if f"arrive {op}" in self.events(label):
                return
            proc = self.procs[label]
            if proc.poll() is not None:
                raise AssertionError(
                    f"{label} exited rc={proc.returncode} before {op}: {self.stderr(label)}"
                )
            time.sleep(0.05)
        raise AssertionError(f"{label} did not arrive at {op}")


@pytest.fixture
def harness(tmp_path):
    h = Harness(tmp_path)
    try:
        yield h
    finally:
        h.kill_all()


def _keyset_id(output: Path) -> str:
    return hashlib.sha256(os.path.realpath(output).encode()).hexdigest()


def _validates(private_key: Path, public_key: Path) -> bool:
    result = subprocess.run(
        [sys.executable, "-B", "-m", KEY_MODULE,
         "--validate-private-key", str(private_key), "--public-key", str(public_key)],
        cwd=REPO_ROOT, capture_output=True, text=True, timeout=60,
    )
    return result.returncode == 0


def _snapshot(directory: Path) -> dict[str, tuple[int, int, bytes]]:
    """byte・mode・ctime の snapshot（directory 自身を含む）。"""

    state: dict[str, tuple[int, int, bytes]] = {}
    if not directory.exists():
        return state
    for path in [directory, *sorted(directory.rglob("*"))]:
        st = path.lstat()
        data = path.read_bytes() if path.is_file() and not path.is_symlink() else b""
        state[str(path.relative_to(directory))] = (st.st_mode, st.st_ctime_ns, data)
    return state


def _hold_keyset_lock(keyset: Path) -> int:
    keyset.mkdir(parents=True, mode=0o700, exist_ok=True)
    fd = os.open(keyset, os.O_RDONLY)
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    return fd


def _blocked_in_flock(session_id: int) -> bool:
    """session（runner と子）の中に ``flock`` で待っている process があるか。"""

    for stat in Path("/proc").glob("[0-9]*/stat"):
        try:
            text = stat.read_text()
        except OSError:
            continue
        comm = text[text.index("(") + 1:text.rindex(")")]
        fields = text[text.rindex(")") + 2:].split()
        if comm == "flock" and int(fields[3]) == session_id:
            return True
    return False


def _wait_until(predicate, timeout: float = 90.0) -> None:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(0.05)
    raise AssertionError("condition not reached")


def _runner_setup(kind: str, harness: Harness, output: Path) -> tuple[dict[str, str], Path]:
    """runner の keyset と、同じ keyset を指すための env を返す。"""

    if kind == "eq":
        return {"EQBENCH_AUTHORITY_KEYSET_ID": "shared"}, harness.key_root / "shared"
    return {}, harness.key_root / _keyset_id(output)


# ---------------------------------------------------------------------------
# T-K1: 他の run が keyset を保持している間は具体化しない
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("kind", ["eq", "neq"])
def test_keyset_lock_blocks_materialization_while_held(harness, kind):
    output = harness.root / "out"
    extra, keyset = _runner_setup(kind, harness, output)
    fd = _hold_keyset_lock(keyset)
    try:
        rc, err = harness.run(
            kind, "B", output, VALIDATION_KEYSET_LOCK_WAIT_SECONDS="1", **extra
        )
    finally:
        os.close(fd)

    assert rc == 1, (rc, err)
    assert "authority keyset is held by another run for too long" in err, err
    assert "Traceback" not in err
    assert sorted(os.listdir(keyset)) == []
    assert not (output / PUBLIC_KEY).exists()
    assert harness.key_ops("B") == []


# ---------------------------------------------------------------------------
# T-K-timeout (C-C2): 先行 run を鍵の窓の中で止める。後続は上限まで待って exit 1
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("holder", ["eq", "neq"])
def test_waiter_times_out_without_touching_the_keyset(harness, holder):
    out_a = harness.root / "out-a"
    out_b = harness.root / "out-b"
    extra_a, keyset = _runner_setup(holder, harness, out_a)
    harness.hold("A", "gen")
    harness.start(holder, "A", out_a, **extra_a)
    harness.wait_arrive("A", "gen")

    before_keyset = _snapshot(keyset)
    before_root_ctime = harness.key_root.stat().st_ctime_ns
    started = time.monotonic()
    rc_b, err_b = harness.run(
        "eq", "B", out_b,
        EQBENCH_AUTHORITY_KEYSET_ID=keyset.name,
        VALIDATION_KEYSET_LOCK_WAIT_SECONDS="2",
    )
    waited = time.monotonic() - started

    assert rc_b == 1, (rc_b, err_b)
    assert "authority keyset is held by another run for too long" in err_b, err_b
    assert "Traceback" not in err_b
    assert waited >= 2.0
    assert harness.key_ops("B") == []
    assert _snapshot(keyset) == before_keyset
    assert harness.key_root.stat().st_ctime_ns == before_root_ctime
    assert not (out_b / PUBLIC_KEY).exists()

    harness.release("A", "gen")
    assert harness.finish("A") == STOPPED_AFTER_KEYS, harness.stderr("A")
    assert _validates(keyset / PRIVATE_KEY, out_a / PUBLIC_KEY)


# ---------------------------------------------------------------------------
# T-K-release (C-C3): 上限内に解放されれば、後続は待ってから export と validate
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("holder", ["eq", "neq"])
def test_waiter_materializes_after_the_holder_releases(harness, holder):
    out_a = harness.root / "out-a"
    out_b = harness.root / "out-b"
    extra_a, keyset = _runner_setup(holder, harness, out_a)
    harness.hold("A", "gen")
    harness.start(holder, "A", out_a, **extra_a)
    harness.wait_arrive("A", "gen")
    harness.start(
        "eq", "B", out_b,
        EQBENCH_AUTHORITY_KEYSET_ID=keyset.name,
        VALIDATION_KEYSET_LOCK_WAIT_SECONDS="60",
    )
    # B が keyset の flock で待っているところを観測する（main では待たずに gen へ進む）。
    _wait_until(lambda: _blocked_in_flock(harness.procs["B"].pid) or harness.key_ops("B"))
    time.sleep(0.5)
    # B は A が鍵の窓にいる間、どの鍵 CLI にも到達しない。
    assert harness.key_ops("B") == []
    assert _blocked_in_flock(harness.procs["B"].pid)
    assert "arrive gen" not in harness.events("B")
    assert harness.procs["B"].poll() is None

    harness.release("A", "gen")
    assert harness.finish("A") == STOPPED_AFTER_KEYS, harness.stderr("A")
    assert harness.finish("B") == STOPPED_AFTER_KEYS, harness.stderr("B")

    assert harness.key_ops("A") == ["gen", "val"]
    assert harness.key_ops("B") == ["exp", "val"]
    assert _validates(keyset / PRIVATE_KEY, out_a / PUBLIC_KEY)
    assert _validates(keyset / PRIVATE_KEY, out_b / PUBLIC_KEY)


# ---------------------------------------------------------------------------
# T-K2 (C-C4): 同じ keyset・別の出力の通常の並行実行。両方進み、鍵は整合する
# ---------------------------------------------------------------------------


def test_concurrent_runners_sharing_an_override_keep_one_consistent_keyset(harness):
    for iteration in range(3):
        keyset_id = f"shared-{iteration}"
        outs = [harness.root / f"out-{iteration}-{side}" for side in ("a", "b")]
        labels = [f"A{iteration}", f"B{iteration}"]
        for label, output in zip(labels, outs):
            harness.start("eq", label, output, EQBENCH_AUTHORITY_KEYSET_ID=keyset_id)
        for label in labels:
            assert harness.finish(label) == STOPPED_AFTER_KEYS, harness.stderr(label)
        ops = [op for label in labels for op in harness.key_ops(label)]
        assert ops.count("gen") == 1, ops
        keyset = harness.key_root / keyset_id
        for output in outs:
            assert _validates(keyset / PRIVATE_KEY, output / PUBLIC_KEY), iteration


# ---------------------------------------------------------------------------
# 鍵の窓の fd は窓を抜ける前に閉じる（以降の子は keyset の fd を持たない）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("kind", ["eq", "neq"])
def test_keyset_fd_is_closed_before_the_run_continues(harness, kind):
    output = harness.root / "out"
    extra, keyset = _runner_setup(kind, harness, output)
    rc, err = harness.run(kind, "A", output, GATE_KEYSET=str(keyset), **extra)

    assert rc == STOPPED_AFTER_KEYS, err
    assert harness.events("A")[-1] == "stop inherited=0"
    assert (keyset.stat().st_mode & 0o777) == 0o700
    for name in ("supervisor.key", "worker.key", PRIVATE_KEY):
        assert ((keyset / name).stat().st_mode & 0o777) == 0o600, name
    assert _validates(keyset / PRIVATE_KEY, output / PUBLIC_KEY)


# ---------------------------------------------------------------------------
# Issue #170 本体: 出力を消して、秘密鍵が残った keyset で取り直す
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("kind", ["eq", "neq"])
def test_rerun_into_a_cleared_output_reuses_the_retained_private_key(harness, kind):
    output = harness.root / "out"
    extra, keyset = _runner_setup(kind, harness, output)
    rc, err = harness.run(kind, "A", output, **extra)
    assert rc == STOPPED_AFTER_KEYS, err
    private_before = (keyset / PRIVATE_KEY).read_bytes()

    subprocess.run(["rm", "-rf", "--", str(output)], check=True)
    rc, err = harness.run(kind, "B", output, **extra)

    assert rc == STOPPED_AFTER_KEYS, err
    assert "Traceback" not in err
    assert harness.key_ops("B") == ["exp", "val"]
    assert (keyset / PRIVATE_KEY).read_bytes() == private_before
    assert _validates(keyset / PRIVATE_KEY, output / PUBLIC_KEY)


# ---------------------------------------------------------------------------
# T-C: keyset と OUTPUT の分離（runner 経由。private root の 6 つの綴り × 2 runner）
# ---------------------------------------------------------------------------


_CONTAINMENT_SPELLINGS = ["plain", "double-slash", "leading-double-slash", "dotdot", "symlink", "relative"]
_KEY_NAMES = {PRIVATE_KEY, "supervisor.key", "worker.key"}


def _containment_root(harness: Harness, output: Path, spelling: str) -> str:
    inside = output / "keys"
    if spelling == "plain":
        return str(inside)
    if spelling == "double-slash":
        return f"{output}//keys"
    if spelling == "leading-double-slash":
        return "/" + str(inside)
    if spelling == "dotdot":
        return f"{output.parent}/x/../{output.name}/keys"
    if spelling == "symlink":
        link = harness.root / "keys-link"
        link.symlink_to(output / "k2")
        return str(link)
    # runner は SCRIPT_DIR へ cd するので、相対 path はそこからの相対になる。
    return os.path.relpath(inside, harness.repo)


def _key_files_under(directory: Path) -> list[str]:
    return sorted(str(path) for path in directory.rglob("*") if path.name in _KEY_NAMES)


def _assert_rejected_without_touching_output(harness, label, rc, err, output, mode_before):
    assert rc == 1, (rc, err)
    assert "private authority keyset must be outside OUTPUT_BASE_DIR and must not contain it" in err, err
    assert "Traceback" not in err
    assert _key_files_under(output) == []
    assert (output.stat().st_mode & 0o777) == mode_before
    assert harness.key_ops(label) == []


@pytest.mark.parametrize("spelling", _CONTAINMENT_SPELLINGS)
@pytest.mark.parametrize("kind", ["eq", "neq"])
def test_private_root_inside_output_is_rejected_for_every_spelling(harness, kind, spelling):
    output = harness.root / "real" / "out"
    output.mkdir(parents=True, mode=0o755)
    output.chmod(0o755)
    root = _containment_root(harness, output, spelling)
    rc, err = harness.run(kind, "C", output, EQBENCH_PRIVATE_AUTHORITY_ROOT=root)

    _assert_rejected_without_touching_output(harness, "C", rc, err, output, 0o755)


@pytest.mark.parametrize("relation", ["keyset-is-output", "keyset-contains-output"])
def test_eq_rejects_a_keyset_composed_onto_or_around_output(harness, relation):
    """root も id も単独では正しいが、組み立てた keyset が OUTPUT と重なる。"""

    output = harness.root / "x" / "out"
    output.mkdir(parents=True, mode=0o755)
    output.chmod(0o755)
    if relation == "keyset-is-output":
        root, keyset_id = output.parent, output.name
    else:
        root, keyset_id = output.parent.parent, output.parent.name
    rc, err = harness.run(
        "eq", "C", output,
        EQBENCH_PRIVATE_AUTHORITY_ROOT=str(root), EQBENCH_AUTHORITY_KEYSET_ID=keyset_id,
    )

    _assert_rejected_without_touching_output(harness, "C", rc, err, output, 0o755)
    assert _key_files_under(harness.root) == []


@pytest.mark.parametrize("keyset_id", [".", ".."])
def test_eq_rejects_a_keyset_id_that_escapes_the_private_root(harness, keyset_id):
    output = harness.root / "out"
    harness.key_root.mkdir(mode=0o755)
    harness.key_root.chmod(0o755)
    before_root = _snapshot(harness.key_root)
    before_parent = harness.root.stat().st_mode
    rc, err = harness.run("eq", "C", output, EQBENCH_AUTHORITY_KEYSET_ID=keyset_id)

    assert rc == 1, (rc, err)
    assert "authority keyset id must be one path component" in err, err
    assert _snapshot(harness.key_root) == before_root
    assert harness.root.stat().st_mode == before_parent
    assert _key_files_under(harness.root) == []
    assert harness.key_ops("C") == []


# ---------------------------------------------------------------------------
# helper を直接呼ぶ test の道具。script の $1 = keyset、$2 = 公開鍵、$OUT = OUTPUT
# ---------------------------------------------------------------------------


def _bash(script: str, *args: str, env: dict[str, str] | None = None,
          cwd: Path = REPO_ROOT) -> subprocess.CompletedProcess:
    full_env = dict(os.environ)
    for name in list(full_env):
        if name.startswith("VALIDATION_") or name == "_VALIDATION_KEYSET_LOCK":
            full_env.pop(name)
    full_env.update(env or {})
    return subprocess.run(
        ["bash", "-c", f'set -euo pipefail\nsource "{COMMON}"\n{script}', "bash", *args],
        cwd=cwd, capture_output=True, text=True, timeout=120, env=full_env,
    )


def _canonical(path: Path) -> str:
    return os.path.realpath(path)


_LOCK = 'validation_lock_authority_keyset "$1" "$OUT"'

_MATERIALIZE = f"""
{_LOCK} || exit $?
rc=0
validation_materialize_pair_status_keypair "$PY" "$1/pair-status-ed25519.key" "$2" || rc=$?
validation_unlock_authority_keyset
exit "$rc"
"""


def _env(out: Path, **extra: str) -> dict[str, str]:
    return {"PY": sys.executable, "OUT": str(out), **extra}


def _materialize(keyset: Path, public_key: Path) -> subprocess.CompletedProcess:
    return _bash(_MATERIALIZE, _canonical(keyset), str(public_key), env=_env(public_key.parent))


def _generate(tmp_path: Path, name: str) -> tuple[Path, Path]:
    keyset = tmp_path / "keys" / name
    public = tmp_path / f"out-{name}" / PUBLIC_KEY
    public.parent.mkdir(parents=True)
    result = _materialize(keyset, public)
    assert result.returncode == 0, result.stderr
    return keyset / PRIVATE_KEY, public


def _assert_clean_failure(result: subprocess.CompletedProcess, reason: str, rc: int = 1) -> None:
    assert result.returncode == rc, (result.returncode, result.stderr)
    assert reason in result.stderr, result.stderr
    assert "Traceback" not in result.stderr
    assert result.stderr.startswith("Error: "), result.stderr


def _fresh_layout(tmp_path: Path) -> tuple[Path, Path]:
    """OUTPUT の外の keyset（まだ無い）と、存在する OUTPUT。"""

    out = tmp_path / "out"
    out.mkdir()
    return tmp_path / "keys" / "ks", out


# ---------------------------------------------------------------------------
# 鍵の状態（無し / 秘密鍵だけ / 両方 / 壊れている）
# ---------------------------------------------------------------------------


def test_helper_generates_a_keypair_when_the_keyset_is_empty(tmp_path):
    keyset, out = _fresh_layout(tmp_path)
    public = out / PUBLIC_KEY
    result = _materialize(keyset, public)

    assert result.returncode == 0, result.stderr
    assert (keyset.stat().st_mode & 0o777) == 0o700
    assert ((keyset / PRIVATE_KEY).stat().st_mode & 0o777) == 0o600
    assert _validates(keyset / PRIVATE_KEY, public)


def test_helper_exports_the_public_key_from_a_retained_private_key(tmp_path):
    private, public = _generate(tmp_path, "ks")
    private_before = private.read_bytes()
    public_before = public.read_bytes()
    public.unlink()
    result = _materialize(private.parent, public)

    assert result.returncode == 0, result.stderr
    assert private.read_bytes() == private_before
    assert public.read_bytes() == public_before


def test_helper_only_validates_an_existing_pair(tmp_path):
    private, public = _generate(tmp_path, "ks")
    before = (private.stat().st_mtime_ns, public.stat().st_mtime_ns,
              private.read_bytes(), public.read_bytes())
    result = _materialize(private.parent, public)

    assert result.returncode == 0, result.stderr
    assert (private.stat().st_mtime_ns, public.stat().st_mtime_ns,
            private.read_bytes(), public.read_bytes()) == before


def test_helper_rejects_a_mismatched_pair_without_rewriting_it(tmp_path):
    private, _ = _generate(tmp_path, "ks")
    _, other_public = _generate(tmp_path, "other")
    before = (private.read_bytes(), other_public.read_bytes())
    result = _materialize(private.parent, other_public)

    _assert_clean_failure(result, "are not a valid pair")
    assert (private.read_bytes(), other_public.read_bytes()) == before


@pytest.mark.parametrize("public_present", [False, True])
def test_helper_rejects_a_short_private_key(tmp_path, public_present):
    private, public = _generate(tmp_path, "ks")
    private.write_bytes(b"0123456789")
    if not public_present:
        public.unlink()
    result = _materialize(private.parent, public)

    reason = "are not a valid pair" if public_present else "cannot be exported"
    _assert_clean_failure(result, reason)
    assert private.read_bytes() == b"0123456789"


def test_helper_rejects_a_corrupt_public_key(tmp_path):
    private, public = _generate(tmp_path, "ks")
    public.write_text("{not json", encoding="utf-8")
    result = _materialize(private.parent, public)

    _assert_clean_failure(result, "are not a valid pair")
    assert public.read_text(encoding="utf-8") == "{not json"


@pytest.mark.skipif(os.geteuid() == 0, reason="root reads files regardless of mode")
def test_helper_rejects_an_unreadable_private_key(tmp_path):
    private, public = _generate(tmp_path, "ks")
    private.chmod(0o000)
    try:
        result = _materialize(private.parent, public)
    finally:
        private.chmod(0o600)

    _assert_clean_failure(result, "are not a valid pair")


@pytest.mark.skipif(os.geteuid() == 0, reason="root writes files regardless of mode")
def test_helper_rejects_an_unwritable_public_key_directory(tmp_path):
    keyset, out = _fresh_layout(tmp_path)
    out.chmod(0o500)
    try:
        result = _materialize(keyset, out / PUBLIC_KEY)
    finally:
        out.chmod(0o700)

    _assert_clean_failure(result, "cannot be generated")


def test_helper_rejects_a_public_key_path_that_is_a_directory(tmp_path):
    private, public = _generate(tmp_path, "ks")
    public.unlink()
    public.mkdir()
    result = _materialize(private.parent, public)

    _assert_clean_failure(result, "are not a valid pair")


def test_process_key_is_kept_when_present_and_written_when_empty(tmp_path):
    keyset, out = _fresh_layout(tmp_path)
    keyset.mkdir(parents=True)
    (keyset / "supervisor.key").write_bytes(b"k" * 64)
    (keyset / "worker.key").write_bytes(b"")
    result = _bash(
        f'{_LOCK}\nvalidation_materialize_process_key "$1/supervisor.key"\n'
        'validation_materialize_process_key "$1/worker.key"',
        _canonical(keyset), env=_env(out),
    )

    assert result.returncode == 0, result.stderr
    assert (keyset / "supervisor.key").read_bytes() == b"k" * 64
    assert (keyset / "worker.key").stat().st_size == 32
    assert sorted(os.listdir(keyset)) == ["supervisor.key", "worker.key"]


def test_process_key_rejects_a_non_regular_file(tmp_path):
    keyset, out = _fresh_layout(tmp_path)
    (keyset / "supervisor.key").mkdir(parents=True)
    result = _bash(f'{_LOCK}\nvalidation_materialize_process_key "$1/supervisor.key"',
                   _canonical(keyset), env=_env(out))

    _assert_clean_failure(result, "is not a regular file")


def test_lock_materialize_unlock_succeeds_and_releases(tmp_path):
    keyset, out = _fresh_layout(tmp_path)
    public = out / PUBLIC_KEY
    result = _bash(
        f"""
{_LOCK}
validation_materialize_process_key "$1/supervisor.key"
validation_materialize_process_key "$1/worker.key"
validation_materialize_pair_status_keypair "$PY" "$1/pair-status-ed25519.key" "$2"
p=${{_VALIDATION_KEYSET_LOCK[0]}}; s=${{_VALIDATION_KEYSET_LOCK[1]}}
validation_unlock_authority_keyset
declare -p _VALIDATION_KEYSET_LOCK >/dev/null 2>&1 && echo state=kept || echo state=cleared
[[ -e /dev/fd/$p || -e /dev/fd/$s ]] && echo fds=open || echo fds=closed
rc=0; validation_materialize_process_key "$1/supervisor.key" || rc=$?
echo "after_unlock=$rc"
""",
        _canonical(keyset), str(public), env=_env(out),
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout.split() == ["state=cleared", "fds=closed", "after_unlock=2"]
    for name in ("supervisor.key", "worker.key"):
        assert (keyset / name).stat().st_size == 32
        assert ((keyset / name).stat().st_mode & 0o777) == 0o600
    assert _validates(keyset / PRIVATE_KEY, public)
    fd = os.open(keyset, os.O_RDONLY)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    finally:
        os.close(fd)
    assert sorted(os.listdir(keyset)) == sorted(["supervisor.key", "worker.key", PRIVATE_KEY])


# ---------------------------------------------------------------------------
# 不変条件 1: canonical keyset は必ず OUTPUT と分離される
#
# oracle は実装と独立（Python の realpath と path の包含）。root の綴り × id の全組み合わせで、
# 「重なる ⇔ resolve が拒否し、どこにも鍵を書かず、OUTPUT の mode を変えない」
# 「重ならない ⇔ lock・両 writer・unlock が成功し、鍵は canonical keyset にだけある」を確かめる。
# ---------------------------------------------------------------------------


_ROOT_SPELLINGS = {
    "output": lambda base: f"{base}/a/out",
    "inside-output": lambda base: f"{base}/a/out/sub",
    "output-parent": lambda base: f"{base}/a",
    "output-grandparent": lambda base: f"{base}",
    "sibling-tree": lambda base: f"{base}/b",
    "double-slash-parent": lambda base: f"{base}//a",
    "dotdot-parent": lambda base: f"{base}/b/../a",
    "symlink-to-parent": lambda base: f"{base}/link-a",
    "symlink-to-output": lambda base: f"{base}/link-out",
    "relative-parent": lambda base: "a",
}
_IDS = ["out", "a", "ks", "sub", "link-out"]

_IDENTITY_SCRIPT = f"""
rc=0; keyset="$(validation_resolve_authority_keyset "$ROOT" "$ID" "$OUT")" || rc=$?
echo "resolve=$rc"
(( rc == 0 )) || exit 0
echo "keyset=$keyset"
validation_lock_authority_keyset "$keyset" "$OUT"
validation_materialize_process_key "$keyset/supervisor.key"
validation_materialize_pair_status_keypair "$PY" "$keyset/pair-status-ed25519.key" "$OUT/{PUBLIC_KEY}"
validation_unlock_authority_keyset
echo done
"""


def _overlaps(a: str, b: str) -> bool:
    return a == b or a.startswith(b + "/") or b.startswith(a + "/")


@pytest.mark.parametrize("output_exists", [True, False], ids=["output-exists", "output-absent"])
@pytest.mark.parametrize("keyset_id", _IDS)
@pytest.mark.parametrize("spelling", sorted(_ROOT_SPELLINGS))
def test_canonical_keyset_is_always_separated_from_output(tmp_path, spelling, keyset_id, output_exists):
    base = Path(_canonical(tmp_path))
    out = base / "a" / "out"
    out.parent.mkdir(parents=True)
    (base / "b").mkdir()
    (base / "link-a").symlink_to(base / "a")
    (base / "link-out").symlink_to(out)
    if output_exists:
        out.mkdir(mode=0o755)
        out.chmod(0o755)
    root = _ROOT_SPELLINGS[spelling](base)
    expected_keyset = os.path.join(os.path.realpath(os.path.join(base, root)), keyset_id)
    keyset_is_symlink = os.path.islink(expected_keyset)
    separated = not keyset_is_symlink and not _overlaps(
        os.path.realpath(expected_keyset), str(out)
    )
    before_entries = sorted(str(path) for path in base.rglob("*"))

    result = _bash(_IDENTITY_SCRIPT, env=_env(out, ROOT=root, ID=keyset_id), cwd=base)

    assert result.returncode == 0, result.stderr
    assert "Traceback" not in result.stderr
    if output_exists:
        assert (out.stat().st_mode & 0o777) == 0o755
        assert _key_files_under(out) == []
    if not separated:
        assert result.stdout.split() == ["resolve=1"], (result.stdout, result.stderr)
        assert result.stderr.startswith("Error: "), result.stderr
        assert sorted(str(path) for path in base.rglob("*")) == before_entries
        return
    assert result.stdout.split() == ["resolve=0", f"keyset={expected_keyset}", "done"], result.stderr
    keyset = Path(expected_keyset)
    assert _key_files_under(out) == []
    assert sorted(os.listdir(keyset)) == sorted(["supervisor.key", PRIVATE_KEY])
    assert _key_files_under(base) == sorted(str(keyset / name) for name in ("supervisor.key", PRIVATE_KEY))
    assert _validates(keyset / PRIVATE_KEY, out / PUBLIC_KEY)


@pytest.mark.parametrize("writer", sorted(_WRITERS_FOR_RECHECK := {
    "pair": 'validation_materialize_pair_status_keypair "$PY" "$1/pair-status-ed25519.key" "$2"',
    "hmac": 'validation_materialize_process_key "$1/supervisor.key"',
}))
def test_key_writers_recheck_the_separation_at_the_moment_they_write(tmp_path, writer):
    """lock の後で OUTPUT が keyset の別名に差し替えられたら、書く直前の判定で拒否する。"""

    base = Path(_canonical(tmp_path))
    keyset = base / "keys" / "ks"
    out = base / "out"
    out.mkdir()
    result = _bash(
        f'validation_lock_authority_keyset "$1" "$OUT"\nrmdir -- "$OUT"\nln -s -- "$1" "$OUT"\n'
        + _WRITERS_FOR_RECHECK[writer],
        str(keyset), str(out / PUBLIC_KEY), env=_env(out),
    )

    _assert_clean_failure(result, "private authority keyset must be outside OUTPUT_BASE_DIR")
    assert os.listdir(keyset) == []


@pytest.mark.parametrize("relation", ["keyset-aliases-output", "output-aliases-keyset-child"])
def test_overlap_hidden_from_canonicalization_is_caught_by_inode(tmp_path, relation):
    """canonical な綴りで見えない別名（bind mount 相当）でも、inode で重なりを検出する。

    ``realpath`` を symlink を解決しない stub に替えて、綴りの判定だけでは素通りする状況を作る。
    """

    base = Path(_canonical(tmp_path))
    out = base / "a" / "out"
    out.mkdir(parents=True, mode=0o755)
    out.chmod(0o755)
    (base / "alias").symlink_to(base / "a")
    stub = base / "stub"
    stub.mkdir()
    (stub / "realpath").write_text('#!/bin/sh\nexec /usr/bin/realpath -s "$@"\n', encoding="utf-8")
    (stub / "realpath").chmod(0o755)
    if relation == "keyset-aliases-output":
        root, keyset_id, output = f"{base}/alias", "out", str(out)
    else:
        root, keyset_id, output = f"{base}", "a", f"{base}/alias/out"
    result = _bash(
        _IDENTITY_SCRIPT,
        env=_env(Path(output), ROOT=root, ID=keyset_id, PATH=f"{stub}:{os.environ['PATH']}"),
        cwd=base,
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout.split() == ["resolve=1"], (result.stdout, result.stderr)
    assert "must be outside OUTPUT_BASE_DIR and must not contain it" in result.stderr
    assert _key_files_under(base) == []
    assert (out.stat().st_mode & 0o777) == 0o755


@pytest.mark.parametrize("keyset_id", [".", "..", "", "a/b", "a b", "../ks"])
def test_resolve_rejects_a_keyset_id_that_is_not_one_component(tmp_path, keyset_id):
    root = tmp_path / "root"
    root.mkdir(mode=0o755)
    root.chmod(0o755)
    tmp_path.chmod(0o755)
    out = tmp_path / "out"
    result = _bash('validation_resolve_authority_keyset "$1" "$2" "$OUT"',
                   _canonical(root), keyset_id, env=_env(out))

    _assert_clean_failure(result, "authority keyset id must be one path component")
    assert (root.stat().st_mode & 0o777) == 0o755
    assert (tmp_path.stat().st_mode & 0o777) == 0o755
    assert os.listdir(root) == []


@pytest.mark.parametrize("spelling", [
    "relative", "dotdot", "double-slash", "trailing-slash", "symlinked-parent",
    "symlinked-keyset", "dot-id", "is-output", "inside-output", "contains-output",
])
def test_lock_rejects_a_keyset_that_is_not_a_valid_identity(tmp_path, spelling):
    """lock は渡された keyset を resolve と同じ判定にかけ直す（手で組み立てた path も同じ規則）。"""

    base = Path(_canonical(tmp_path))
    out = base / "a" / "out"
    out.mkdir(parents=True, mode=0o755)
    out.chmod(0o755)
    (base / "real").mkdir()
    (base / "link").symlink_to(base / "real")
    (base / "ks-link").symlink_to(base / "real")
    keyset = {
        "relative": "real/ks",
        "dotdot": f"{base}/x/../real/ks",
        "double-slash": f"{base}//real/ks",
        "trailing-slash": f"{base}/real/ks/",
        "symlinked-parent": f"{base}/link/ks",
        "symlinked-keyset": f"{base}/ks-link",
        "dot-id": f"{base}/real/.",
        "is-output": str(out),
        "inside-output": f"{out}/ks",
        "contains-output": f"{base}/a",
    }[spelling]
    before_entries = sorted(str(path) for path in base.rglob("*"))
    result = _bash(f'{_LOCK}\necho locked', keyset, env=_env(out), cwd=base)

    assert result.returncode == 1, (result.returncode, result.stderr)
    assert result.stderr.startswith("Error: authority keyset") or result.stderr.startswith(
        "Error: private authority keyset"), result.stderr
    assert result.stdout == ""
    assert sorted(str(path) for path in base.rglob("*")) == before_entries
    assert (out.stat().st_mode & 0o777) == 0o755


# ---------------------------------------------------------------------------
# 不変条件 2: key writer は、いま保持している keyset lock なしでは書けない
# 不変条件 3: unlock は自分が取得した authority lock 以外を閉じない
#
# state は shell 変数を偽装・stale 化・再利用する全ての遷移（lock が作った state 以外）。
# writer は必ず 2 で何も書かない。unlock は lock の state が無ければ 0、あれば 2 で、どちらも
# process の fd を 1 つも閉じない。
# ---------------------------------------------------------------------------


_PRELUDE = """
keyset_identity() { local t; exec {t}<"$1"; flock "$t"; _validation_fd_exclusive_flock_identity "$t"; exec {t}<&-; }
"""

_STALE = 'p=${_VALIDATION_KEYSET_LOCK[0]}; s=${_VALIDATION_KEYSET_LOCK[1]}; '

# どの state も「lock が作り、いま所有している state」ではない。
_NOT_HELD_STATES = {
    "no-state": ":",
    "legacy-dir-variable": 'VALIDATION_KEYSET_LOCK_DIR="$1"',
    "legacy-fd-variable-with-a-real-lock": 'exec {fd}<"$1"; flock "$fd"; VALIDATION_KEYSET_LOCK_FD=$fd',
    "forged-state-closed-fds": '_VALIDATION_KEYSET_LOCK=(200 201 "00:00:1" "$1" "$OUT")',
    "forged-state-wrong-shape": '_VALIDATION_KEYSET_LOCK=(1 2 3)',
    "forged-scalar-state": '_VALIDATION_KEYSET_LOCK="10 11"',
    "forged-state-unlocked-fds-on-the-keyset": (
        'id=$(keyset_identity "$1"); exec {a}<"$1" {b}<"$1"; '
        '_VALIDATION_KEYSET_LOCK=("$a" "$b" "$id" "$1" "$OUT")'
    ),
    "forged-state-shared-lock": (
        'id=$(keyset_identity "$1"); exec {a}<"$1"; flock -s "$a"; exec {b}<&"$a"; '
        '_VALIDATION_KEYSET_LOCK=("$a" "$b" "$id" "$1" "$OUT")'
    ),
    "forged-state-while-another-process-holds-the-keyset": (
        'id=$(keyset_identity "$1"); '
        '( exec 9<"$1"; flock 9; : > "$1/../held"; exec sleep 30 ) >/dev/null 2>&1 & holder=$!; '
        'trap \'kill $holder\' EXIT; until [[ -e "$1/../held" ]]; do sleep 0.05; done; '
        'exec {a}<"$1" {b}<"$1"; _VALIDATION_KEYSET_LOCK=("$a" "$b" "$id" "$1" "$OUT")'
    ),
    "stale-primary-closed": f'{_LOCK}; {_STALE}exec {{p}}<&-',
    "stale-shadow-closed": f'{_LOCK}; {_STALE}exec {{s}}<&-',
    "stale-both-closed": f'{_LOCK}; {_STALE}exec {{p}}<&- {{s}}<&-',
    "primary-reused-by-another-file-with-an-exclusive-flock": (
        f'{_LOCK}; {_STALE}exec {{p}}<&-; eval "exec $p<\\"$1/../other\\""; flock "$p"'
    ),
    "primary-reused-by-another-directory-with-an-exclusive-flock": (
        f'{_LOCK}; {_STALE}exec {{p}}<&-; eval "exec $p<\\"$1/../other-dir\\""; flock "$p"'
    ),
    "both-reused-by-one-locked-description-of-another-file": (
        f'{_LOCK}; {_STALE}exec {{p}}<&- {{s}}<&-; eval "exec $p<\\"$1/../other\\""; '
        'flock "$p"; eval "exec $s<&$p"'
    ),
    "primary-reused-by-the-keyset-reopened": (
        f'{_LOCK}; {_STALE}exec {{p}}<&-; eval "exec $p<\\"$1\\""; flock -n "$p" || true'
    ),
    "state-exported": f'{_LOCK}; export _VALIDATION_KEYSET_LOCK',
}

# 所有している lock だが、書こうとしている keyset の lock ではない（writer だけが拒否する）。
_HELD_ELSEWHERE_STATES = {
    "lock-of-another-keyset": 'validation_lock_authority_keyset "$(dirname -- "$1")/other-ks" "$OUT"',
    "state-of-another-keyset-relabelled": (
        'validation_lock_authority_keyset "$(dirname -- "$1")/other-ks" "$OUT"; '
        '_VALIDATION_KEYSET_LOCK[3]="$1"'
    ),
    "keyset-replaced-after-lock": f'{_LOCK}; mv -- "$1" "$1.old"; mkdir -- "$1"',
}

_WRITERS = {
    "pair": 'validation_materialize_pair_status_keypair "$PY" "$1/pair-status-ed25519.key" "$2"',
    "hmac": 'validation_materialize_process_key "$1/supervisor.key"',
}

_OBSERVE = """
before=(/proc/$$/fd/*)
rc=0; {op} || rc=$?
after=(/proc/$$/fd/*)
echo "rc=$rc"
[[ "${{before[*]}}" == "${{after[*]}}" ]] && echo fds=unchanged || echo "fds=changed"
"""


def _state_layout(tmp_path: Path) -> tuple[Path, Path]:
    base = Path(_canonical(tmp_path))
    keyset = base / "keys" / "ks"
    keyset.mkdir(parents=True)
    (base / "keys" / "other").write_text("", encoding="utf-8")
    (base / "keys" / "other-dir").mkdir()
    out = base / "out"
    out.mkdir()
    return keyset, out


def _run_state(tmp_path: Path, state: str, op: str) -> tuple[subprocess.CompletedProcess, Path, Path]:
    keyset, out = _state_layout(tmp_path)
    states = {**_NOT_HELD_STATES, **_HELD_ELSEWHERE_STATES}
    script = _PRELUDE + states[state] + "\n" + _OBSERVE.format(op=op)
    result = _bash(script, str(keyset), str(out / PUBLIC_KEY), env=_env(out))
    return result, keyset, out


@pytest.mark.parametrize("writer", sorted(_WRITERS))
@pytest.mark.parametrize("state", sorted({**_NOT_HELD_STATES, **_HELD_ELSEWHERE_STATES}))
def test_key_writers_require_the_held_keyset_capability(tmp_path, state, writer):
    result, keyset, out = _run_state(tmp_path, state, _WRITERS[writer])

    assert result.returncode == 0, result.stderr
    assert result.stdout.split() == ["rc=2", "fds=unchanged"], (result.stdout, result.stderr)
    assert result.stderr.startswith("Error: "), result.stderr
    assert "Traceback" not in result.stderr
    assert os.listdir(keyset) == []
    assert _key_files_under(keyset.parent) == []
    assert not (out / PUBLIC_KEY).exists()


@pytest.mark.parametrize("state", sorted(_NOT_HELD_STATES))
def test_unlock_closes_only_the_lock_it_acquired(tmp_path, state):
    result, _, _ = _run_state(tmp_path, state, "validation_unlock_authority_keyset")

    expected_rc = 0 if state in {"no-state", "legacy-dir-variable", "legacy-fd-variable-with-a-real-lock"} else 2
    assert result.returncode == 0, result.stderr
    assert result.stdout.split() == [f"rc={expected_rc}", "fds=unchanged"], (result.stdout, result.stderr)
    if expected_rc == 2:
        assert "not closing any descriptor" in result.stderr


@pytest.mark.parametrize("state", sorted(_HELD_ELSEWHERE_STATES))
def test_unlock_releases_its_own_lock_even_when_writers_refuse(tmp_path, state):
    """所有している lock は、keyset の path が差し替えられても unlock で解放できる。"""

    keyset, out = _state_layout(tmp_path)
    script = _PRELUDE + _HELD_ELSEWHERE_STATES[state] + """
p=${_VALIDATION_KEYSET_LOCK[0]}; s=${_VALIDATION_KEYSET_LOCK[1]}
validation_unlock_authority_keyset
[[ -e /dev/fd/$p || -e /dev/fd/$s ]] && echo fds=open || echo fds=closed
declare -p _VALIDATION_KEYSET_LOCK >/dev/null 2>&1 && echo state=kept || echo state=cleared
"""
    result = _bash(script, str(keyset), str(out / PUBLIC_KEY), env=_env(out))

    assert result.returncode == 0, result.stderr
    assert result.stdout.split() == ["fds=closed", "state=cleared"]
    for locked in (keyset.parent / "other-ks", keyset, Path(f"{keyset}.old")):
        if locked.is_dir():
            fd = os.open(locked, os.O_RDONLY)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            finally:
                os.close(fd)


def test_the_acquired_lock_cannot_be_retaken_on_a_recycled_descriptor(tmp_path):
    """primary を閉じても shadow が同じ open file description を保つので、同じ keyset を開き直した
    fd では lock を取れない（再利用された fd 番号が自分の lock に化けない根拠）。"""

    keyset, out = _state_layout(tmp_path)
    result = _bash(
        f'{_LOCK}\n{_STALE}exec {{p}}<&-\neval "exec $p<\\"$1\\""\n'
        'flock -n "$p" && echo retaken=yes || echo retaken=no',
        str(keyset), env=_env(out),
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout.split() == ["retaken=no"]


@pytest.mark.parametrize("operation", ["lock", "unlock", "pair", "hmac"])
def test_a_lock_state_from_the_environment_is_rejected(tmp_path, operation):
    keyset, out = _state_layout(tmp_path)
    op = {"lock": _LOCK, "unlock": "validation_unlock_authority_keyset", **_WRITERS}[operation]
    result = _bash(
        _OBSERVE.format(op=op), str(keyset), str(out / PUBLIC_KEY),
        env=_env(out, _VALIDATION_KEYSET_LOCK=f"3 4 00:00:1 {keyset} {out}"),
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout.split() == ["rc=2", "fds=unchanged"], (result.stdout, result.stderr)
    assert os.listdir(keyset) == []


@pytest.mark.parametrize("writer", sorted(_WRITERS))
@pytest.mark.parametrize("target", [
    "elsewhere", "subdirectory", "double-slash", "dot-component", "relative-keyset",
])
def test_key_writers_reject_a_key_that_is_not_directly_under_the_locked_keyset(tmp_path, writer, target):
    keyset, out = _state_layout(tmp_path)
    (keyset.parent / "elsewhere").mkdir()
    directory = {
        "elsewhere": f"{keyset.parent}/elsewhere",
        "subdirectory": f"{keyset}/sub",
        "double-slash": f"{keyset}/",
        "dot-component": f"{keyset}/.",
        "relative-keyset": os.path.relpath(keyset, REPO_ROOT),
    }[target]
    op = _WRITERS[writer].replace('"$1/', '"$3/')
    result = _bash(f"{_LOCK}\n{op}", str(keyset), str(out / PUBLIC_KEY), directory, env=_env(out))

    _assert_clean_failure(result, "must be a file directly under the locked keyset", rc=2)
    assert os.listdir(keyset) == []
    assert _key_files_under(keyset.parent) == []


@pytest.mark.parametrize("writer", sorted(_WRITERS))
def test_key_writers_reject_a_symlinked_key(tmp_path, writer):
    keyset, out = _state_layout(tmp_path)
    victim = keyset.parent / "victim"
    name = PRIVATE_KEY if writer == "pair" else "supervisor.key"
    (keyset / name).symlink_to(victim)
    result = _bash(f'{_LOCK}\n{_WRITERS[writer]}', str(keyset), str(out / PUBLIC_KEY), env=_env(out))

    _assert_clean_failure(result, "must not be a symlink")
    assert not victim.exists()


@pytest.mark.parametrize("placement", ["outside-output", "inside-keyset", "symlink-into-keyset", "is-output"])
def test_pair_writer_requires_the_public_key_inside_output(tmp_path, placement):
    keyset, out = _state_layout(tmp_path)
    (out / "link").symlink_to(keyset)
    public = {
        "outside-output": f"{keyset.parent}/{PUBLIC_KEY}",
        "inside-keyset": f"{keyset}/{PUBLIC_KEY}",
        "symlink-into-keyset": f"{out}/link/{PUBLIC_KEY}",
        "is-output": str(out),
    }[placement]
    result = _bash(f'{_LOCK}\n{_WRITERS["pair"]}', str(keyset), public, env=_env(out))

    _assert_clean_failure(result, "pair-status public key must be inside OUTPUT_BASE_DIR")
    assert os.listdir(keyset) == []
    assert _key_files_under(keyset.parent) == []


def test_key_writers_write_into_the_locked_inode_not_through_the_path():
    """書き込み先は /dev/fd/<primary>/<name>（lock した inode）。path を見る判定と書き込みの間に
    keyset が差し替えられても、鍵は差し替え後の directory には入らない。"""

    source = COMMON.read_text(encoding="utf-8")
    target = _shell_function(source, "_validation_keyset_member_target")
    assert 'printf \'%s\\n\' "/dev/fd/$primary/$name"' in target
    for writer in ("validation_materialize_process_key", "validation_materialize_pair_status_keypair"):
        body = _shell_function(source, writer)
        assert '_validation_keyset_member_target "' in body
        assert '"$target' in body


# ---------------------------------------------------------------------------
# lock の lifecycle
# ---------------------------------------------------------------------------


def test_lock_rejects_a_symlinked_keyset(tmp_path):
    target = tmp_path / "elsewhere"
    target.mkdir(mode=0o755)
    link = tmp_path / "ks"
    link.symlink_to(target)
    out = tmp_path / "out"
    result = _bash(_LOCK, _canonical(tmp_path) + "/ks", env=_env(out))

    _assert_clean_failure(result, "must not be a symlink")
    assert (target.stat().st_mode & 0o777) == 0o755


def test_lock_restricts_permissions_only_after_acquiring_it(tmp_path):
    keyset, out = _fresh_layout(tmp_path)
    keyset.mkdir(parents=True, mode=0o755)
    keyset.chmod(0o755)
    fd = _hold_keyset_lock(keyset)
    try:
        refused = _bash(_LOCK, _canonical(keyset),
                        env=_env(out, VALIDATION_KEYSET_LOCK_WAIT_SECONDS="0.5"))
    finally:
        os.close(fd)
    assert (keyset.stat().st_mode & 0o777) == 0o755
    _assert_clean_failure(refused, "held by another run for too long")

    acquired = _bash(_LOCK, _canonical(keyset), env=_env(out))
    assert acquired.returncode == 0, acquired.stderr
    assert (keyset.stat().st_mode & 0o777) == 0o700


def test_lock_rejects_a_keyset_replaced_while_waiting(tmp_path):
    keyset, out = _fresh_layout(tmp_path)
    fd = _hold_keyset_lock(keyset)
    waiter = subprocess.Popen(
        ["bash", "-c", f'set -euo pipefail\nsource "{COMMON}"\n{_LOCK}', "bash", _canonical(keyset)],
        cwd=REPO_ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=True,
        env={**os.environ, **_env(out, VALIDATION_KEYSET_LOCK_WAIT_SECONDS="60")},
    )
    try:
        _wait_until(lambda: _blocked_in_flock(waiter.pid))
        keyset.rename(keyset.parent / "ks.old")
        keyset.mkdir(mode=0o755)
        keyset.chmod(0o755)
    finally:
        os.close(fd)
    _, err = waiter.communicate(timeout=60)

    assert waiter.returncode == 1, err
    assert "was replaced while waiting for its lock" in err
    assert (keyset.stat().st_mode & 0o777) == 0o755


def test_lock_refuses_a_second_keyset_and_unlock_releases(tmp_path):
    base = Path(_canonical(tmp_path))
    out = base / "out"
    out.mkdir()
    first = base / "keys" / "first"
    second = base / "keys" / "second"
    result = _bash(
        """
validation_lock_authority_keyset "$1" "$OUT"
rc=0; validation_lock_authority_keyset "$2" "$OUT" || rc=$?
echo "second=$rc"
"$PY" -c 'import fcntl, os, sys
fd = os.open(sys.argv[1], os.O_RDONLY)
try:
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB); print("held=no")
except BlockingIOError:
    print("held=yes")' "$1"
validation_unlock_authority_keyset
"$PY" -c 'import fcntl, os, sys
fd = os.open(sys.argv[1], os.O_RDONLY)
fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB); print("after_unlock=free")' "$1"
""",
        str(first), str(second), env=_env(out),
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout.split() == ["second=2", "held=yes", "after_unlock=free"]
    assert "authority keyset lock state already exists" in result.stderr
    assert not second.exists()


@pytest.mark.parametrize("value", ["", "abc", "-1", "1s"])
def test_lock_rejects_an_invalid_wait(tmp_path, value):
    keyset, out = _fresh_layout(tmp_path)
    result = _bash(_LOCK, _canonical(keyset),
                   env=_env(out, VALIDATION_KEYSET_LOCK_WAIT_SECONDS=value))
    if value == "":
        # 空は未設定と同じ（既定 120 秒）。
        assert result.returncode == 0, result.stderr
        return
    _assert_clean_failure(result, "VALIDATION_KEYSET_LOCK_WAIT_SECONDS")
    assert not keyset.exists()


def test_key_cli_does_not_depend_on_the_callers_cwd(tmp_path):
    keyset, out = _fresh_layout(tmp_path)
    python_link = tmp_path / "py"
    python_link.symlink_to(sys.executable)
    result = _bash(_MATERIALIZE, _canonical(keyset), str(out / PUBLIC_KEY),
                   env=_env(out, PY="./py"), cwd=tmp_path)

    assert result.returncode == 0, result.stderr
    assert _validates(keyset / PRIVATE_KEY, out / PUBLIC_KEY)


# ---------------------------------------------------------------------------
# 静的: owner は 1 つ、窓の形（T-K3）
# ---------------------------------------------------------------------------


_KEY_CLI_OPTIONS = ("--generate-private-key", "--export-public-from-private", "--validate-private-key")


def _shell_function(source: str, name: str) -> str:
    start = source.index(f"{name}() {{\n")
    end = source.index("\n}\n", start)
    return source[start:end]


def _repo_shell_scripts() -> list[Path]:
    return sorted(REPO_ROOT.glob("*.sh")) + sorted((REPO_ROOT / "scripts").rglob("*.sh"))


def test_runners_do_not_call_the_key_cli_directly():
    offenders = []
    for script in _repo_shell_scripts():
        source = script.read_text(encoding="utf-8")
        if script == COMMON:
            source = source.replace(
                _shell_function(source, "validation_materialize_pair_status_keypair"), ""
            )
        offenders += [
            f"{script.relative_to(REPO_ROOT)}: {option}"
            for option in _KEY_CLI_OPTIONS if option in source
        ]
    assert offenders == []
    helper = _shell_function(COMMON.read_text(encoding="utf-8"), "validation_materialize_pair_status_keypair")
    assert all(option in helper for option in _KEY_CLI_OPTIONS)


_WINDOW_PARTS = {
    "eq": (
        'validation_lock_authority_keyset "$PROCESS_AUTHORITY_ROOT" "$OUTPUT_BASE_DIR" || exit 1',
        'existing_authority_evidence="$(find',
        'validation_materialize_process_key "$PROCESS_SUPERVISOR_KEY_FILE" || exit 1',
        'validation_materialize_process_key "$PROCESS_WORKER_KEY_FILE" || exit 1',
        "validation_materialize_pair_status_keypair",
        "validation_unlock_authority_keyset || exit 1",
    ),
    "neq": (
        'validation_lock_authority_keyset "$AUTHORITY_ROOT" "$OUTPUT_BASE_DIR" || exit 1',
        'existing_status="$(find',
        'validation_materialize_process_key "$SUPERVISOR_KEY" || exit 1',
        'validation_materialize_process_key "$WORKER_KEY" || exit 1',
        "validation_materialize_pair_status_keypair",
        "validation_unlock_authority_keyset || exit 1",
    ),
}
_KEYSET_VARIABLE = {"eq": "PROCESS_AUTHORITY_ROOT", "neq": "AUTHORITY_ROOT"}


@pytest.mark.parametrize("kind", ["eq", "neq"])
def test_the_key_window_brackets_guard_hmac_and_helper_without_background_jobs(kind):
    source = (REPO_ROOT / RUNNERS[kind]).read_text(encoding="utf-8")
    parts = _WINDOW_PARTS[kind]
    for part in parts:
        assert source.count(part) == 1, part
    positions = [source.index(part) for part in parts]
    assert positions == sorted(positions)
    # 秘密鍵を置く dir の作成と chmod は lock 関数の中だけ（lock の外で触らない）。
    assert f'chmod 700 "${_KEYSET_VARIABLE[kind]}"' not in source
    window = source[positions[0]:positions[-1]]
    stripped = re.sub(r"&&|[0-9]*>&[0-9-]*|<&[0-9-]*|&>", "", window)
    assert "&" not in stripped, window


@pytest.mark.parametrize("kind", ["eq", "neq"])
def test_runners_take_the_keyset_only_from_the_identity_owner(kind):
    """runner は keyset を resolve からだけ受け取り、root/id を自分で組み立てない。"""

    source = (REPO_ROOT / RUNNERS[kind]).read_text(encoding="utf-8")
    variable = _KEYSET_VARIABLE[kind]
    assignments = re.findall(rf"^\s*{variable}=.*$", source, flags=re.MULTILINE)
    assert assignments == [f'{variable}="$(validation_resolve_authority_keyset \\'], assignments
    assert '"$EQBENCH_PRIVATE_AUTHORITY_ROOT/' not in source
    resolve = source.index("validation_resolve_authority_keyset")
    assert resolve < source.index("validation_lock_authority_keyset")


def test_every_key_write_goes_through_one_owner_that_proves_the_held_lock():
    source = COMMON.read_text(encoding="utf-8")
    process_key = _shell_function(source, "validation_materialize_process_key")
    target = _shell_function(source, "_validation_keyset_member_target")
    pair = _shell_function(source, "validation_materialize_pair_status_keypair")
    unlock = _shell_function(source, "validation_unlock_authority_keyset")
    lock = _shell_function(source, "validation_lock_authority_keyset")
    resolve = _shell_function(source, "validation_resolve_authority_keyset")
    assert "(umask 077; head -c 32 /dev/urandom >" in process_key
    assert "_validation_keyset_lock_is_owned" in target
    assert "_validation_keyset_lock_is_owned" in unlock
    assert "_validation_keyset_lock_is_valid_for" in lock
    assert '_validation_keyset_member_target "$key_file"' in process_key
    assert '_validation_keyset_member_target "$private_key"' in pair
    # keyset identity の判定は 1 つの関数だけが持ち、resolve・lock・writer がそれを使う。
    check = _shell_function(source, "_validation_check_authority_keyset")
    assert source.count('_validation_paths_overlap "') == 1
    assert '_validation_paths_overlap "' in check
    for body in (resolve, lock, target):
        assert "_validation_check_authority_keyset" in body
    # lock を保持していることを shell 変数の path で判定しない。
    assert "VALIDATION_KEYSET_LOCK_DIR" not in source
    assert "VALIDATION_KEYSET_LOCK_FD" not in source
    # keyset の外の鍵（run ごとの tmp にある execution authority の worker 鍵）は対象外。
    execution_authority = _shell_function(source, "validation_prepare_before_after_logs")
    offenders = [
        str(script.relative_to(REPO_ROOT))
        for script in _repo_shell_scripts()
        if "/dev/urandom" in script.read_text(encoding="utf-8")
        .replace(process_key, "").replace(execution_authority, "")
    ]
    assert offenders == []


def test_lock_waits_bounded_and_restricts_permissions_under_the_lock():
    source = COMMON.read_text(encoding="utf-8")
    lock = _shell_function(source, "validation_lock_authority_keyset")
    assert 'flock -E 75 -w "$wait_seconds"' in lock
    assert "VALIDATION_KEYSET_LOCK_WAIT_SECONDS:-120" in lock
    assert lock.index("flock -E 75") < lock.index('chmod 700 -- "/dev/fd/$primary"')
    assert "&" not in re.sub(r"&&|[0-9]*>&[0-9-]*|<&[0-9-]*|&>", "", lock)
