# -*- coding: utf-8 -*-
"""Issue #170 (PR-R1): pair-status 鍵の具体化と keyset の inode lock。

固定している契約（計画 v5 の §0 C-L key 行 / §6 / PR-R1）:

* 鍵を具体化する規則の owner は ``validation_matrix_common.sh`` の
  ``validation_materialize_pair_status_keypair`` 1 つだけ。runner は pair-status の
  鍵 CLI を直接呼ばない。
* 秘密鍵の keyset（``<realpath(private root)>/<KEYSET_ID>``）は出力とは別の共有資源で、
  その directory の inode を lock する。lock は evidence guard・HMAC 鍵・具体化の区間
  （S8〜S13）だけ保持し、上限付きで待つ。
* 待ちの上限を超えた run は「held by another run for too long」で exit 1 になり、
  keyset にも key root にも（ctime を含めて）触れない。
* Neq の private root も realpath してから OUTPUT の外であることを確かめる。
* 失敗はメッセージ付きの非 0 で、Python の traceback を出さない。

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
    time.sleep(1.5)
    # B は A が鍵の窓にいる間、どの鍵 CLI にも到達しない。
    assert harness.key_ops("B") == []
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
# T-C: private root の包含判定は正規化した path で行う（6 つの綴り）
# ---------------------------------------------------------------------------


_CONTAINMENT_SPELLINGS = ["plain", "double-slash", "leading-double-slash", "dotdot", "symlink", "relative"]


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


@pytest.mark.parametrize("spelling", _CONTAINMENT_SPELLINGS)
@pytest.mark.parametrize("kind", ["eq", "neq"])
def test_private_root_inside_output_is_rejected_for_every_spelling(harness, kind, spelling):
    output = harness.root / "real" / "out"
    output.mkdir(parents=True)
    root = _containment_root(harness, output, spelling)
    rc, err = harness.run(kind, "C", output, EQBENCH_PRIVATE_AUTHORITY_ROOT=root)

    assert rc == 1, (rc, err)
    assert "private authority root must be outside OUTPUT_BASE_DIR" in err, err
    assert "Traceback" not in err
    leaked = [
        str(path) for path in output.rglob("*")
        if path.name in {PRIVATE_KEY, "supervisor.key", "worker.key"}
    ]
    assert leaked == []
    assert harness.key_ops("C") == []


# ---------------------------------------------------------------------------
# helper の状態 test（validation_matrix_common.sh を直接呼ぶ）
# ---------------------------------------------------------------------------


def _bash(script: str, *args: str, env: dict[str, str] | None = None) -> subprocess.CompletedProcess:
    full_env = dict(os.environ)
    full_env.pop("VALIDATION_KEYSET_LOCK_WAIT_SECONDS", None)
    full_env.update(env or {})
    return subprocess.run(
        ["bash", "-c", f'set -euo pipefail\nsource "{COMMON}"\n{script}', "bash", *args],
        cwd=REPO_ROOT, capture_output=True, text=True, timeout=120, env=full_env,
    )


_MATERIALIZE = """
validation_lock_authority_keyset "$1" || exit $?
rc=0
validation_materialize_pair_status_keypair "$PY" "$1/pair-status-ed25519.key" "$2" || rc=$?
validation_unlock_authority_keyset
exit "$rc"
"""


def _materialize(keyset: Path, public_key: Path) -> subprocess.CompletedProcess:
    return _bash(_MATERIALIZE, str(keyset), str(public_key), env={"PY": sys.executable})


def _generate(tmp_path: Path, name: str) -> tuple[Path, Path]:
    keyset = tmp_path / name
    public = tmp_path / f"{name}.json"
    result = _materialize(keyset, public)
    assert result.returncode == 0, result.stderr
    return keyset / PRIVATE_KEY, public


def _assert_clean_failure(result: subprocess.CompletedProcess, reason: str) -> None:
    assert result.returncode == 1, (result.returncode, result.stderr)
    assert reason in result.stderr, result.stderr
    assert "Traceback" not in result.stderr
    assert result.stderr.startswith("Error: "), result.stderr


def test_helper_generates_a_keypair_when_the_keyset_is_empty(tmp_path):
    keyset = tmp_path / "keys" / "ks"
    public = tmp_path / "out" / PUBLIC_KEY
    public.parent.mkdir()
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
    keyset = tmp_path / "keys" / "ks"
    out = tmp_path / "out"
    out.mkdir()
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


def test_helper_refuses_to_run_without_the_keyset_lock(tmp_path):
    keyset = tmp_path / "ks"
    keyset.mkdir()
    result = _bash(
        'validation_materialize_pair_status_keypair "$PY" "$1/pair-status-ed25519.key" "$2"',
        str(keyset), str(tmp_path / PUBLIC_KEY), env={"PY": sys.executable},
    )

    assert result.returncode == 2, result.stderr
    assert "while holding its keyset lock" in result.stderr
    assert os.listdir(keyset) == []


def test_lock_rejects_a_symlinked_keyset(tmp_path):
    target = tmp_path / "elsewhere"
    target.mkdir(mode=0o755)
    link = tmp_path / "ks"
    link.symlink_to(target)
    result = _bash('validation_lock_authority_keyset "$1"', str(link))

    _assert_clean_failure(result, "must not be a symlink")
    assert (target.stat().st_mode & 0o777) == 0o755


def test_lock_restricts_permissions_only_after_acquiring_it(tmp_path):
    keyset = tmp_path / "ks"
    keyset.mkdir(mode=0o755)
    keyset.chmod(0o755)
    fd = _hold_keyset_lock(keyset)
    try:
        refused = _bash(
            'validation_lock_authority_keyset "$1"', str(keyset),
            env={"VALIDATION_KEYSET_LOCK_WAIT_SECONDS": "0.5"},
        )
    finally:
        os.close(fd)
    assert (keyset.stat().st_mode & 0o777) == 0o755
    _assert_clean_failure(refused, "held by another run for too long")

    acquired = _bash('validation_lock_authority_keyset "$1"', str(keyset))
    assert acquired.returncode == 0, acquired.stderr
    assert (keyset.stat().st_mode & 0o777) == 0o700


def test_lock_refuses_a_second_keyset_and_unlock_releases(tmp_path):
    first = tmp_path / "first"
    second = tmp_path / "second"
    result = _bash(
        """
validation_lock_authority_keyset "$1"
rc=0; validation_lock_authority_keyset "$2" || rc=$?
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
        str(first), str(second), env={"PY": sys.executable},
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout.split() == ["second=2", "held=yes", "after_unlock=free"]
    assert "refusing a second keyset lock" in result.stderr
    assert not second.exists()


@pytest.mark.parametrize("value", ["", "abc", "-1", "1s"])
def test_lock_rejects_an_invalid_wait(tmp_path, value):
    result = _bash(
        'validation_lock_authority_keyset "$1"', str(tmp_path / "ks"),
        env={"VALIDATION_KEYSET_LOCK_WAIT_SECONDS": value},
    )
    if value == "":
        # 空は未設定と同じ（既定 120 秒）。
        assert result.returncode == 0, result.stderr
        return
    _assert_clean_failure(result, "VALIDATION_KEYSET_LOCK_WAIT_SECONDS")
    assert not (tmp_path / "ks").exists()


# ---------------------------------------------------------------------------
# 静的: owner は 1 つ、窓の形（T-K3）
# ---------------------------------------------------------------------------


_KEY_CLI_OPTIONS = ("--generate-private-key", "--export-public-from-private", "--validate-private-key")


def _shell_function(source: str, name: str) -> str:
    start = source.index(f"{name}() {{\n")
    end = source.index("\n}\n", start)
    return source[start:end]


def test_runners_do_not_call_the_key_cli_directly():
    offenders = []
    for script in sorted(REPO_ROOT.glob("*.sh")) + sorted((REPO_ROOT / "scripts").rglob("*.sh")):
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
        'validation_lock_authority_keyset "$PROCESS_AUTHORITY_ROOT" || exit 1',
        'existing_authority_evidence="$(find',
        "head -c 32 /dev/urandom",
        "validation_materialize_pair_status_keypair",
        "validation_unlock_authority_keyset",
    ),
    "neq": (
        'validation_lock_authority_keyset "$AUTHORITY_ROOT" || exit 1',
        'existing_status="$(find',
        "head -c 32 /dev/urandom",
        "validation_materialize_pair_status_keypair",
        "validation_unlock_authority_keyset",
    ),
}


@pytest.mark.parametrize("kind", ["eq", "neq"])
def test_the_key_window_brackets_guard_hmac_and_helper_without_background_jobs(kind):
    source = (REPO_ROOT / RUNNERS[kind]).read_text(encoding="utf-8")
    parts = _WINDOW_PARTS[kind]
    for part in parts:
        assert source.count(part) == 1, part
    positions = [source.index(part) for part in parts]
    assert positions == sorted(positions)
    # 秘密鍵を置く dir の作成と chmod は lock 関数の中だけ（lock の外で触らない）。
    assert "chmod 700 \"$PROCESS_AUTHORITY_ROOT\"" not in source
    assert "chmod 700 \"$AUTHORITY_ROOT\"" not in source
    window = source[positions[0]:positions[-1]]
    stripped = re.sub(r"&&|[0-9]*>&[0-9-]*|<&[0-9-]*|&>", "", window)
    assert "&" not in stripped, window
    # HMAC 鍵は subshell の umask 077 の中で書く。
    assert "(umask 077; head -c 32 /dev/urandom >" in window


def test_lock_functions_hold_no_other_resource():
    source = COMMON.read_text(encoding="utf-8")
    lock = _shell_function(source, "validation_lock_authority_keyset")
    assert 'flock -E 75 -w "$wait_seconds"' in lock
    assert "VALIDATION_KEYSET_LOCK_WAIT_SECONDS:-120" in lock
    assert lock.index("flock -E 75") < lock.index('chmod 700 -- "$dir"')
    assert "&" not in re.sub(r"&&|[0-9]*>&[0-9-]*|<&[0-9-]*|&>", "", lock)
