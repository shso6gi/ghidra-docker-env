# -*- coding: utf-8 -*-
"""Issue #124 PR-124-C: runner の cleanup 順序と、実 supervisor の end-to-end（D15）。

固定している契約:

* runner は `process_authority_cleanup` の**前**に dump 退避状態を確認・記録する。
* 確認を足しても cleanup を skip しない（既存の run-health 契約を変えない）。
* 前回 execution の診断 sidecar は、child を起こす前に捨てる。
* 実 supervisor を通すと、deadline 到達から kill 開始までが 0.5s 以内で、
  取得できた dump が run dir へ退避され、状態 sidecar が残る。
* `bash -n` 4 本。
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.process.stack_dump_diagnostic import (
    DEADLINE_JITTER_ALLOWANCE_SECONDS,
    STACK_DUMP_STATUS_SCHEMA,
    read_stack_dump_status,
)

REPO_ROOT = Path(__file__).resolve().parents[4]
RUNNERS = ["eqbench_run_all_32jobs.sh", "neqbench_run_all_32jobs.sh"]
SHELL_SCRIPTS = RUNNERS + ["rerun_eqbench_errors.sh", "eqbench_run_subset.sh"]


# ---------------------------------------------------------------------------
# D15: `bash -n`
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("script", SHELL_SCRIPTS + ["scripts/validation_matrix_common.sh"])
def test_shell_scripts_parse(script):
    result = subprocess.run(
        ["bash", "-n", str(REPO_ROOT / script)], capture_output=True, timeout=60,
    )
    assert result.returncode == 0, result.stderr.decode("utf-8", "replace")


# ---------------------------------------------------------------------------
# supervisor へ渡す診断引数
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("runner", RUNNERS)
def test_runners_pass_the_diagnostic_arguments_to_the_supervisor(runner):
    source = (REPO_ROOT / runner).read_text(encoding="utf-8")
    supervisor_section = source.split("supervisor_command", 1)[1]
    for flag in (
        "--stage-journal", "--stack-dump-file", "--stack-dump-artifact",
        "--diagnostic-status-output", "--stack-dump-lead-seconds",
    ):
        assert flag in supervisor_section, flag
    assert "stack-dump.status.json" in source


@pytest.mark.parametrize("runner", RUNNERS)
def test_runners_record_the_artifact_state_before_cleanup(runner):
    """`run_pair` の中で、退避確認が cleanup 呼び出しより前にある。"""
    source = (REPO_ROOT / runner).read_text(encoding="utf-8")
    function = _extract_shell_function(source, "run_pair")
    cleanup_call = (
        "cleanup_pair_process_authority_with_run_health"
        if runner.startswith("eq")
        else "reporting.process_authority_cleanup"
    )
    assert function.index("validation_record_stack_dump_state") < function.index(
        cleanup_call
    )


@pytest.mark.parametrize("runner", RUNNERS)
def test_runners_run_the_timeout_hotspot_summary_after_the_gate(runner):
    source = (REPO_ROOT / runner).read_text(encoding="utf-8")
    gate = source.index("validation_run_benchmark_gate \"$OUTPUT_BASE_DIR\"")
    hotspot = source.index("validation_run_timeout_hotspot_summary")
    assert gate < hotspot


# ---------------------------------------------------------------------------
# 実 `run_pair` を stub 環境で走らせる（PR-124-B の harness と同じ作り）
# ---------------------------------------------------------------------------


def _extract_shell_function(source: str, name: str) -> str:
    lines = source.splitlines()
    start = next(
        index for index, line in enumerate(lines) if line.startswith(f"{name}() {{")
    )
    for index in range(start + 1, len(lines)):
        if lines[index] == "}":
            return "\n".join(lines[start:index + 1])
    raise AssertionError(f"unterminated shell function {name}")


_HARNESS = """
set -u
export PATH="__STUBS__:$PATH"

EQBENCH_RUN_TMPDIR="__TMP__/runtmp"
RUN_TMP="__TMP__/runtmp"
SCRIPT_DIR="__TMP__"
OUTPUT_BASE_DIR="__TMP__/out"
PYTHON_BIN="__STUBS__/python-stub"
EQUIV_TIMEOUT=10; DECOMPILE_TIMEOUT=60; PAIRWISE_TIMEOUT=5; PAIRWISE_TIMEOUT_HARD=30
PAIR_PROCESS_TIMEOUT_SECONDS=240; PAIR_PROCESS_KILL_AFTER_SECONDS=30
PAIR_PROCESS_TIMEOUT=240s; PAIR_PROCESS_KILL_AFTER=30s
PAIR_STACK_DUMP_LEAD=2s; PAIR_STACK_DUMP_LEAD_SECONDS=2
PAIR_PROCESS_DEADLINE_POLICY_DIGEST=deadbeef
PROCESS_SUPERVISOR_KEY_ID=k; PROCESS_SUPERVISOR_KEY_FILE=/dev/null
PROCESS_WORKER_KEY_ID=k2; PROCESS_WORKER_KEY_FILE=/dev/null
SUPERVISOR_KEY_ID=k; SUPERVISOR_KEY=/dev/null
WORKER_KEY_ID=k2; WORKER_KEY=/dev/null
PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE=/dev/null
PAIR_STATUS_VERIFICATION_KEY_FILE=/dev/null
PAIR_PRIVATE_KEY=/dev/null; PAIR_PUBLIC_KEY=/dev/null
EQBENCH_DEBUG=0; EQBENCH_PROGRESS_INTERVAL_SECONDS=1
FT_EXPANDER_DEDUP_CASE_LIMIT=0; FT_CALLEE_UNBOUND_REUSE=0
FT_CALLEE_UNBOUND_REUSE_SHADOW=0
EQBENCH_TMPDIR="__TMP__/runtmp"
PROCESS_CLEANUP_FAILURES="__TMP__/cleanup-failures"
PROCESS_AUTHORITY_CLEANUP_FAILURES_FILE="__TMP__/cleanup-failures"
PROCESS_AUTHORITY_CLEANUP_STOP_FILE="__TMP__/cleanup-stop"
STACK_DUMP_ARTIFACT_STATE_FILE="__TMP__/stack-dump-state.tsv"
SOURCE_PAIR_COUNT=1

ORDER_FILE="__TMP__/order.txt"
: > "$ORDER_FILE"

write_pair_progress_receipt() { :; }
supervisor_projection_is_terminal() { return 0; }
validate_current_pair_status() { printf 'UNKNOWN'; }
progress_update() { :; }
validation_record_stack_dump_state() {
    printf 'record_stack_dump_state %s\\n' "$4" >> "$ORDER_FILE"
}
cleanup_pair_process_authority_with_run_health() {
    printf 'cleanup\\n' >> "$ORDER_FILE"
    return 0
}

__FUNCTION__

run_pair __ARGS__ || true
"""

_PYTHON_STUB = """#!/bin/sh
# neq runner は cleanup を `$PYTHON_BIN -m ...process_authority_cleanup` で直接
# 呼ぶので、その呼び出しだけ順序 file に記録する。
case " $* " in
  *process_authority_cleanup*) printf 'cleanup\\n' >> "$ORDER_FILE" ;;
esac
echo stub
exit 0
"""


def _harness(tmp_path, runner, *, pre=None):
    stubs = tmp_path / "stubs"
    stubs.mkdir(exist_ok=True)
    stub = stubs / "python-stub"
    stub.write_text(_PYTHON_STUB, encoding="utf-8")
    stub.chmod(0o755)
    (tmp_path / "runtmp").mkdir(exist_ok=True)
    out_dir = tmp_path / "out" / "sample" / "f"
    out_dir.mkdir(parents=True, exist_ok=True)
    name = "f_B1_B2" if runner.startswith("eq") else "f_N_B1_O_B2"
    if pre is not None:
        pre(out_dir, name)
    source = (REPO_ROOT / runner).read_text(encoding="utf-8")
    function = _extract_shell_function(source, "run_pair")
    if runner.startswith("eq"):
        args = '"sample" "f" "B1" "B2" "/left" "/right" "%s" 1 1 "/target"' % out_dir
    else:
        args = ('"sample" "f" "N_B1" "O_B2" "/left" "/right" "%s" 1 1 "/target" 1 1 1'
                % out_dir)
    script = (
        _HARNESS
        .replace("__STUBS__", str(stubs))
        .replace("__TMP__", str(tmp_path))
        .replace("__FUNCTION__", function)
        .replace("__ARGS__", args)
    )
    env = dict(os.environ)
    env["ORDER_FILE"] = str(tmp_path / "order.txt")
    subprocess.run(["bash", "-c", script], env=env, capture_output=True, timeout=180)
    order = (tmp_path / "order.txt").read_text(encoding="utf-8").splitlines()
    return out_dir, name, order


@pytest.mark.parametrize("runner", RUNNERS)
def test_artifact_state_is_recorded_before_cleanup_runs(tmp_path, runner):
    """D15: 退避確認 -> cleanup の順で、cleanup が skip されない。"""
    out_dir, name, order = _harness(tmp_path, runner)
    steps = [line.split()[0] for line in order]
    assert "cleanup" in steps, order
    assert steps.index("record_stack_dump_state") < steps.index("cleanup"), order
    # 確認は sidecar の path を見ている（checkpoint 側ではない）。
    recorded = next(line for line in order if line.startswith("record_stack_dump_state"))
    assert recorded.endswith(f"{name}.stack-dump.status.json")


@pytest.mark.parametrize("runner", RUNNERS)
def test_previous_status_sidecar_is_dropped_before_the_child_starts(tmp_path, runner):
    """前回 execution の診断 sidecar を current のものとして読ませない。"""
    def _seed(out_dir, name):
        metrics = out_dir / ".runtime-metrics"
        metrics.mkdir(exist_ok=True)
        (metrics / f"{name}.stack-dump.status.json").write_text(
            json.dumps({"schema": STACK_DUMP_STATUS_SCHEMA, "child_pid": 1}),
            encoding="utf-8",
        )

    out_dir, name, _ = _harness(tmp_path, runner, pre=_seed)
    sidecar = out_dir / ".runtime-metrics" / f"{name}.stack-dump.status.json"
    assert not sidecar.exists()


# ---------------------------------------------------------------------------
# `validation_record_stack_dump_state` 自体
# ---------------------------------------------------------------------------


def _record_state(tmp_path, *, status_payload=None, artifact_text=None):
    status = tmp_path / "pair.stack-dump.status.json"
    artifact = tmp_path / "pair.stack-dump.txt"
    if status_payload is not None:
        status.write_text(json.dumps(status_payload), encoding="utf-8")
    if artifact_text is not None:
        artifact.write_text(artifact_text, encoding="utf-8")
    state_file = tmp_path / "state.tsv"
    log = tmp_path / "pair.log"
    log.write_text("", encoding="utf-8")
    script = (
        f'PYTHON_BIN={sys.executable}\n'
        f'source "{REPO_ROOT}/scripts/validation_matrix_common.sh"\n'
        f'validation_record_stack_dump_state "{state_file}" sample pair '
        f'"{status}" "{artifact}" "{log}"\n'
    )
    result = subprocess.run(
        ["bash", "-c", script], capture_output=True, timeout=120,
        cwd=str(REPO_ROOT),
    )
    assert result.returncode == 0, result.stderr.decode("utf-8", "replace")
    rows = state_file.read_text(encoding="utf-8").splitlines()
    return rows[0].split("\t"), log.read_text(encoding="utf-8")


def test_recorded_state_reports_copied_without_touching_the_log(tmp_path):
    row, log = _record_state(
        tmp_path,
        status_payload={"schema": STACK_DUMP_STATUS_SCHEMA, "artifact_status": "copied"},
        artifact_text="Current thread 0x1:\n",
    )
    assert row[:5] == ["sample", "pair", "copied", "yes", "yes"]
    assert log == ""


def test_recorded_state_is_unknown_without_a_sidecar(tmp_path):
    """sidecar が無い = 「退避できた」でも「0 件」でもなく unknown。"""
    row, log = _record_state(tmp_path)
    assert row[2] == "unknown"
    assert row[3] == "no" and row[4] == "no"
    assert "Stack dump artifact state before cleanup: unknown" in log


def test_recorded_state_reports_a_failed_copy(tmp_path):
    row, log = _record_state(
        tmp_path,
        status_payload={
            "schema": STACK_DUMP_STATUS_SCHEMA, "artifact_status": "copy_failed:13",
        },
    )
    assert row[2] == "copy_failed:13"
    assert "copy_failed:13" in log


def test_recorded_state_survives_an_unreadable_sidecar(tmp_path):
    status = tmp_path / "pair.stack-dump.status.json"
    status.write_text("{not json", encoding="utf-8")
    state_file = tmp_path / "state.tsv"
    log = tmp_path / "pair.log"
    log.write_text("", encoding="utf-8")
    script = (
        f'PYTHON_BIN={sys.executable}\n'
        f'source "{REPO_ROOT}/scripts/validation_matrix_common.sh"\n'
        f'validation_record_stack_dump_state "{state_file}" s p '
        f'"{status}" "{tmp_path}/absent.txt" "{log}"\n'
    )
    result = subprocess.run(
        ["bash", "-c", script], capture_output=True, timeout=120, cwd=str(REPO_ROOT),
    )
    assert result.returncode == 0
    assert state_file.read_text(encoding="utf-8").split("\t")[2] == "unreadable"


# ---------------------------------------------------------------------------
# 実 supervisor の end-to-end
# ---------------------------------------------------------------------------


_CHILD = r"""
import os, sys, time
sys.path.insert(0, {repo!r})
from types import SimpleNamespace
from scripts.function_tracer_pcode.cli.pair_diagnostics import install_pair_diagnostics

args = SimpleNamespace(
    stage_journal={journal!r},
    stack_dump_file={dump!r},
    stack_dump_artifact={artifact!r},
)
install_pair_diagnostics(args, context={{"case": "issue124c"}})
time.sleep(30)
"""


def _supervisor_config(tmp_path, child_code, *, timeout, lead):
    """診断つきの supervisor 設定（実 child を起こすための最小構成）。"""
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        SupervisorCommandConfig,
    )

    supervisor_key = tmp_path / "supervisor.key"
    worker_key = tmp_path / "worker.key"
    supervisor_key.write_bytes(b"s" * 32)
    worker_key.write_bytes(b"w" * 32)
    metrics = tmp_path / ".runtime-metrics"
    metrics.mkdir(exist_ok=True)
    return SupervisorCommandConfig(
        checkpoint_root=tmp_path / "checkpoints",
        authority_output=tmp_path / "authority.json",
        working_directory=REPO_ROOT,
        execution_nonce="issue124c-nonce",
        result_occurrence_id="production-pilot-issue124c",
        source_snapshot_fingerprint="f" * 64,
        stream_id="stream-production-pilot-issue124c",
        deadline_policy_digest="issue124c-deadline-policy",
        supervisor_signing_key_id="supervisor-key-v1",
        supervisor_signing_key_file=supervisor_key,
        worker_signing_key_id="worker-key-v1",
        worker_signing_key_file=worker_key,
        timeout_seconds=timeout,
        kill_grace_seconds=1.0,
        child_command=(sys.executable, "-c", child_code),
        stage_journal_path=tmp_path / "pair.stage.jsonl",
        stack_dump_file=tmp_path / "checkpoints" / "stack-dump.txt",
        stack_dump_artifact=metrics / "pair.stack-dump.txt",
        diagnostic_status_output=metrics / "pair.stack-dump.status.json",
        stack_dump_lead_seconds=lead,
    )


def test_real_supervisor_requests_persists_and_records_a_stack_dump(tmp_path):
    """実 child + 実 supervisor: 送信 -> 観測 -> 退避 -> sidecar、kill は期限内。"""
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        ProcessSupervisorCommand,
    )

    config = _supervisor_config(
        tmp_path,
        _CHILD.format(
            repo=str(REPO_ROOT),
            journal=str(tmp_path / "pair.stage.jsonl"),
            dump=str(tmp_path / "checkpoints" / "stack-dump.txt"),
            artifact=str(tmp_path / ".runtime-metrics" / "pair.stack-dump.txt"),
        ),
        timeout=4.0,
        lead=2.0,
    )
    command = ProcessSupervisorCommand(config)
    started = time.monotonic()
    exit_code = command.run()
    elapsed = time.monotonic() - started
    assert exit_code == 124
    projection = json.loads(config.authority_output.read_text(encoding="utf-8"))
    assert projection["status"] == "TIMEOUT"
    assert projection["authority_kind"] == "DurableTimeoutFinalizationBundle"
    # kill 手順（SIGTERM -> grace -> SIGKILL）と disposition は従来どおり。
    assert projection["child_exit_disposition"] in {
        "SIGTERM_AFTER_DEADLINE", "SIGKILL_AFTER_DEADLINE",
    }
    status = read_stack_dump_status(config.diagnostic_status_output)
    assert status is not None, "診断 sidecar が書かれていない"
    assert status["handler_registered"] is True
    assert status["signal_sent"] is True
    assert status["dump_observed"] is True
    assert status["sent_but_unobserved"] is False
    assert status["unavailable_reason"] is None
    assert status["artifact_status"] == "copied"
    assert status["artifact_bytes"] > 0
    # kill 開始は deadline 以降かつ deadline + 0.5s 以内。
    offset = status["kill_start_offset_seconds"]
    assert offset is not None
    assert 0.0 <= offset <= DEADLINE_JITTER_ALLOWANCE_SECONDS, offset
    # 退避先は run dir 側。全 thread の dump が入っている。
    artifact = Path(config.stack_dump_artifact)
    assert artifact.is_file()
    text = artifact.read_text(encoding="utf-8")
    assert "most recent call first" in text
    # deadline の総予算を延ばしていない（kill grace を含めても十分に短い）。
    assert elapsed < config.timeout_seconds + config.kill_grace_seconds + 3.0


def test_real_supervisor_persists_a_dump_from_a_child_that_exits_normally(tmp_path):
    """outcome によらず保存: 診断を要求する前に終わった child の dump も残す。"""
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        ProcessSupervisorCommand,
    )

    child = (
        "import os, sys\n"
        f"sys.path.insert(0, {str(REPO_ROOT)!r})\n"
        "from types import SimpleNamespace\n"
        "from scripts.function_tracer_pcode.cli.pair_diagnostics import "
        "install_pair_diagnostics\n"
        "import faulthandler\n"
        "state = install_pair_diagnostics(SimpleNamespace(\n"
        f"    stage_journal={str(tmp_path / 'pair.stage.jsonl')!r},\n"
        f"    stack_dump_file={str(tmp_path / 'checkpoints' / 'stack-dump.txt')!r},\n"
        f"    stack_dump_artifact={str(tmp_path / '.runtime-metrics' / 'pair.stack-dump.txt')!r},\n"
        "))\n"
        # 子が自分で dump を書いてから普通に終了する（deadline 前）。
        "faulthandler.dump_traceback(file=state.dump_file, all_threads=True)\n"
        "raise SystemExit(0)\n"
    )
    config = _supervisor_config(tmp_path, child, timeout=30.0, lead=2.0)
    ProcessSupervisorCommand(config).run()
    status = read_stack_dump_status(config.diagnostic_status_output)
    assert status is not None
    assert status["requested"] is False       # 診断は要求していない
    assert status["signal_sent"] is False
    assert status["artifact_status"] == "copied"   # それでも保存する
    assert Path(config.stack_dump_artifact).is_file()


def test_a_failing_diagnostic_does_not_change_the_supervisor_exit(tmp_path, monkeypatch):
    """診断の失敗が exit code / projection を変えない（`finally` の中の guard）。"""
    from scripts.function_tracer_pcode.authority.process import supervisor_command

    config = _supervisor_config(
        tmp_path, "import time; time.sleep(30)", timeout=1.0, lead=0.5,
    )
    monkeypatch.setattr(
        supervisor_command.ProcessSupervisorCommand,
        "_child_terminal_timeout_evidence",
        lambda self: (_ for _ in ()).throw(AttributeError("diagnostic exploded")),
    )
    command = supervisor_command.ProcessSupervisorCommand(config)
    assert command.run() == 124
    projection = json.loads(config.authority_output.read_text(encoding="utf-8"))
    assert projection["status"] == "TIMEOUT"
    assert projection["authority_kind"] == "DurableTimeoutFinalizationBundle"


def test_real_supervisor_reports_missing_when_no_dump_was_written(tmp_path):
    """dump 不存在は `missing`。未観測（`sent_but_unobserved`）と別の事実。"""
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        ProcessSupervisorCommand,
    )

    config = _supervisor_config(
        tmp_path, "import sys; raise SystemExit(0)", timeout=30.0, lead=2.0,
    )
    ProcessSupervisorCommand(config).run()
    status = read_stack_dump_status(config.diagnostic_status_output)
    assert status is not None
    assert status["artifact_status"] == "missing"
    assert status["sent_but_unobserved"] is False
    assert not Path(config.stack_dump_artifact).exists()


def test_kill_signal_jitter_is_measured_at_the_signal_not_at_the_path_entry(
    tmp_path, monkeypatch,
):
    """報告する jitter が「termination path へ入った時刻」ではないことを示す。

    `_terminate_exact_process_group` は SIGTERM の前に終了確認と PID /
    start-token の検証を行う。その検証をわざと遅らせると、

    * `deadline_finalization_offset_seconds`（path へ入った時刻）はほぼ 0 のまま
    * `kill_start_offset_seconds`（実際に SIGTERM を送れた時刻）は遅延ぶん増える

    となる。前者だけを見ていると、実際の kill 開始がどれだけ遅れても
    「0.0001s」と報告できてしまう。
    """
    from scripts.function_tracer_pcode.authority.process import supervisor_command

    delay = 0.35
    original = supervisor_command.ProcessSupervisorCommand._same_process

    def _slow_same_process(self, process, start_token):
        time.sleep(delay)
        return original(self, process, start_token)

    monkeypatch.setattr(
        supervisor_command.ProcessSupervisorCommand, "_same_process", _slow_same_process
    )
    config = _supervisor_config(
        tmp_path, "import time; time.sleep(30)", timeout=2.0, lead=1.0,
    )
    assert supervisor_command.ProcessSupervisorCommand(config).run() == 124
    status = read_stack_dump_status(config.diagnostic_status_output)
    assert status is not None
    entry = status["deadline_finalization_offset_seconds"]
    signal_start = status["kill_start_offset_seconds"]
    assert entry is not None and signal_start is not None
    assert status["kill_signal"] == "SIGTERM"
    # path へ入った時刻は遅延の影響を受けない（= これを jitter と呼ぶと誤る）。
    assert 0.0 <= entry < delay
    # 実 signal の時刻は遅延ぶん後ろにある。
    assert signal_start >= delay
    assert signal_start > entry


def test_an_exploding_first_signal_hook_does_not_change_the_disposition(
    tmp_path, monkeypatch,
):
    """診断 hook が例外を投げても kill 手順と disposition は変わらない。"""
    from scripts.function_tracer_pcode.authority.process import supervisor_command
    from scripts.function_tracer_pcode.authority.process.stack_dump_diagnostic import (
        StackDumpDiagnostic,
    )

    def _explode(self, name, monotonic_time):
        raise RuntimeError("diagnostic hook exploded")

    monkeypatch.setattr(StackDumpDiagnostic, "note_kill_signal", _explode)
    config = _supervisor_config(
        tmp_path, "import time; time.sleep(30)", timeout=2.0, lead=1.0,
    )
    assert supervisor_command.ProcessSupervisorCommand(config).run() == 124
    projection = json.loads(config.authority_output.read_text(encoding="utf-8"))
    assert projection["status"] == "TIMEOUT"
    assert projection["authority_kind"] == "DurableTimeoutFinalizationBundle"
    assert projection["child_exit_disposition"] in {
        "SIGTERM_AFTER_DEADLINE", "SIGKILL_AFTER_DEADLINE",
    }


def test_a_diagnostic_that_cannot_be_built_does_not_change_the_outcome(
    tmp_path, monkeypatch,
):
    """診断 object を組めなくても `run()` は通常の deadline 経路を通る。

    組み立ての失敗が `run()` の `except Exception` に落ちると `_resume()` へ
    移り、診断の都合で exit code と projection が変わってしまう。
    """
    from scripts.function_tracer_pcode.authority.process import supervisor_command

    def _explode(self, process, start_token):
        raise RuntimeError("cannot build the diagnostic")

    monkeypatch.setattr(
        supervisor_command.ProcessSupervisorCommand, "_stack_dump_diagnostic", _explode
    )
    config = _supervisor_config(
        tmp_path, "import time; time.sleep(30)", timeout=1.5, lead=0.5,
    )
    assert supervisor_command.ProcessSupervisorCommand(config).run() == 124
    projection = json.loads(config.authority_output.read_text(encoding="utf-8"))
    assert projection["status"] == "TIMEOUT"
    # 無効化された診断でも sidecar は書かれ、送っていないことが読み取れる。
    status = read_stack_dump_status(config.diagnostic_status_output)
    assert status is None or (
        status["signal_sent"] is False and status["enabled"] is False
    )
