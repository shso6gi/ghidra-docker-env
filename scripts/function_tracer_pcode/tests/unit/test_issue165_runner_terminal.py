# -*- coding: utf-8 -*-
"""Issue #165 T18: runner の pair 実行（``run_pair``）で ERROR / TIMEOUT / INVALID が混ざる。

runner（``eqbench_run_all_32jobs.sh``）の ``run_pair`` と、そこから呼ぶ
``supervisor_projection_is_terminal`` / ``validate_current_pair_status`` を
そのまま取り出し、共有の pair scheduler（``scripts/eqbench/pair_scheduler.sh``）
で 4 pair を並べて走らせる。supervisor・分類器・pair-status の封と検証は
production の module。Ghidra の CLI だけを ``runner_child``（harness の worker）へ
差し替える（``PYTHON_BIN`` の wrapper）。

固定する既存の runner policy:

* TIMEOUT pair: supervisor exit 124、pair-status TIMEOUT（``classification_valid``
  true）、``run_pair`` は 0（run を落とさない）。
* canonical ERROR pair: supervisor は RESOLVED（exit 0）、pair-status ERROR
  valid、分類器の CLI は ERROR で 1 を返すので ``run_pair`` は 1。
* envelope の無い終了（runner mode）: supervisor INVALID（exit 2）。runner は
  非終端の projection を 1 回だけ再実行し、それも同じ INVALID。分類は失敗し
  pair-status は ``PAIR_STATUS_AUTHORITY_INVALID``（``classification_valid``
  false）、``run_pair`` は 2。
* scheduler の失敗数は ``run_pair`` が 0 以外だった pair の数。

Issue #226: どの pair が deadline に当たるかを host の速さで決めない。supervisor は runner の
引数のまま ``runner_supervisor`` から起こし、deadline は worker が ``stop`` した瞬間に来る
（supervisor 単体の harness の ``Deadline.AT_CHILD_STOP`` と同じ）。止まる worker は
``timeoutpair`` だけで、ほかの pair は deadline に当たらずに終わる。runner の timer は hang の
上限で、どの pair も timer に当たらなかったことを確かめる。
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess

import pytest

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
    generate_pair_status_keypair,
)

REPO_ROOT = Path(__file__).resolve().parents[4]
RUNNER = REPO_ROOT / "eqbench_run_all_32jobs.sh"
PAIRS = ("timeoutpair", "invalidpair", "errorpair", "unknownpair")

_WRAPPER = """#!/bin/sh
# Issue #165 T18: Ghidra の CLI の呼び出しだけを harness の worker へ差し替える。
# 起動する module（``-m`` の直後）が CLI のときだけ。supervisor の argv も
# child の command を含むので、argv のどこかに現れるかでは判定しない。
if [ "${1:-}" = "-m" ] && [ "${2:-}" = "scripts.function_tracer_pcode.cli.main" ]; then
  exec python3 -B -m scripts.function_tracer_pcode.tests.fixtures.issue165.runner_child "$@"
fi
# Issue #226: supervisor は deadline を worker の stop に結ぶ入口から起こす（引数は runner のまま）
if [ "${1:-}" = "-m" ] && [ "${2:-}" = "scripts.function_tracer_pcode.authority.process.supervisor_command" ]; then
  shift 2
  exec python3 -B -m scripts.function_tracer_pcode.tests.fixtures.issue165.runner_supervisor "$@"
fi
exec python3 -B "$@"
"""

_SCRIPT = """
set -u
source "__REPO__/scripts/eqbench/pair_scheduler.sh"
SCRIPT_DIR="__REPO__"
PYTHON_BIN="__TMP__/python-wrapper"
EQBENCH_RUN_TMPDIR="__TMP__/runtmp"
EQBENCH_TMPDIR="__TMP__/runtmp"
EQUIV_TIMEOUT=10; DECOMPILE_TIMEOUT=60; PAIRWISE_TIMEOUT=5; PAIRWISE_TIMEOUT_HARD=30
# timer は hang の上限（deadline は worker の stop で来る）。supervisor 単体の harness の既定と同じ
PAIR_PROCESS_TIMEOUT_SECONDS=60; PAIR_PROCESS_KILL_AFTER_SECONDS=5
PAIR_PROCESS_TIMEOUT=60s; PAIR_PROCESS_KILL_AFTER=5s
PAIR_STACK_DUMP_LEAD_SECONDS=1
PAIR_PROCESS_DEADLINE_POLICY_DIGEST=issue165-t18-policy
PROCESS_SUPERVISOR_KEY_ID=t18-supervisor; PROCESS_SUPERVISOR_KEY_FILE="__TMP__/keys/supervisor.key"
PROCESS_WORKER_KEY_ID=t18-worker; PROCESS_WORKER_KEY_FILE="__TMP__/keys/worker.key"
PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE="__TMP__/keys/pair-status.key"
PAIR_STATUS_VERIFICATION_KEY_FILE="__TMP__/keys/pair-status-verification-key.json"
EQBENCH_DEBUG=0; EQBENCH_PROGRESS_INTERVAL_SECONDS=1; EQBENCH_IDENTICAL_FAST_PATH=1
FT_EXPANDER_DEDUP_CASE_LIMIT=0; FT_CALLEE_UNBOUND_REUSE=0; FT_CALLEE_UNBOUND_REUSE_SHADOW=0
STACK_DUMP_ARTIFACT_STATE_FILE="__TMP__/stack-dump-state.tsv"
export ISSUE165_HARNESS_RECORDS="__TMP__/harness"

write_pair_progress_receipt() { :; }
validation_record_stack_dump_state() { :; }
cleanup_pair_process_authority_with_run_health() { return 0; }

__FUNCTIONS__

RUN_PAIR_FAILURES=0
group_done() { :; }
pair_scheduler_init 4 group_done RUN_PAIR_FAILURES
pair_scheduler_open_group sample
for function in __PAIRS__; do
    mkdir -p "__TMP__/out/$function"
    (
        run_pair sample "$function" B1 B2 "__TMP__/left.bin" "__TMP__/right.bin" \\
            "__TMP__/out/$function" 1 1 "__TMP__/targets/$function.json"
        rc=$?
        printf '%s\\n' "$rc" > "__TMP__/out/$function/run_pair.rc"
        exit "$rc"
    ) &
    pair_scheduler_start_job sample "$!"
done
pair_scheduler_close_group sample
pair_scheduler_finalize
printf 'RUN_PAIR_FAILURES=%s\\n' "$RUN_PAIR_FAILURES"
"""


def _extract(source: str, name: str) -> str:
    lines = source.splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith(f"{name}() {{"))
    end = next(i for i in range(start + 1, len(lines)) if lines[i] == "}")
    return "\n".join(lines[start:end + 1])


def _target(function: str) -> dict:
    body = {
        "schema": "eqbench-pair-execution-target-v1",
        "authority_kind": "PairExecutionTargetReceipt",
        **{name: f"t18-{name}" for name in (
            "sample_identity", "output_sample_relative_path", "left_binary_id",
            "right_binary_id", "source_path", "source_sha256", "left_binary_path",
            "left_binary_sha256", "right_binary_path", "right_binary_sha256",
            "analysis_source_digest", "analysis_config_digest",
        )},
        "function_name": function,
    }
    return {**body, "target_digest": authority_digest(body)}


@pytest.fixture(scope="module")
def runner_result(tmp_path_factory):
    tmp = tmp_path_factory.mktemp("t18")
    (tmp / "runtmp").mkdir()
    (tmp / "harness").mkdir()
    keys = tmp / "keys"
    keys.mkdir()
    for name, byte in (("supervisor", b"s"), ("worker", b"w")):
        (keys / f"{name}.key").write_bytes(byte * 32)
    generate_pair_status_keypair(
        keys / "pair-status.key", keys / "pair-status-verification-key.json",
    )
    (tmp / "left.bin").write_bytes(b"left")
    (tmp / "right.bin").write_bytes(b"right")
    (tmp / "targets").mkdir()
    for function in PAIRS:
        (tmp / "targets" / f"{function}.json").write_text(
            json.dumps(_target(function), sort_keys=True), encoding="utf-8",
        )
    wrapper = tmp / "python-wrapper"
    wrapper.write_text(_WRAPPER, encoding="utf-8")
    wrapper.chmod(0o755)
    source = RUNNER.read_text(encoding="utf-8")
    functions = "\n\n".join(_extract(source, name) for name in (
        "run_pair", "supervisor_projection_is_terminal", "validate_current_pair_status",
    ))
    script = (
        _SCRIPT.replace("__FUNCTIONS__", functions)
        .replace("__REPO__", str(REPO_ROOT)).replace("__TMP__", str(tmp))
        .replace("__PAIRS__", " ".join(PAIRS))
    )
    completed = subprocess.run(
        ["bash", "-c", script], cwd=REPO_ROOT, capture_output=True, text=True,
        timeout=600, env={**os.environ, "PYTHONPATH": str(REPO_ROOT)},
    )
    return tmp, completed


def _pair(tmp: Path, function: str):
    directory = tmp / "out" / function
    status = json.loads(
        (directory / f"{function}_B1_B2.pair-status.json").read_text(encoding="utf-8")
    )
    rc = int((directory / "run_pair.rc").read_text(encoding="utf-8"))
    log = (directory / f"{function}_B1_B2.log").read_text(encoding="utf-8")
    return status, rc, log


def _status_line(completed, function: str) -> str:
    return next(
        line for line in completed.stdout.splitlines()
        if f"[{function} " in line
    )


def test_t18_runner_counts_only_non_terminal_or_error_pairs_as_failures(runner_result):
    tmp, completed = runner_result
    logs = "\n".join(
        path.read_text(encoding="utf-8")[-3000:] for path in sorted((tmp / "out").glob("*/*.log"))
    )
    assert "RUN_PAIR_FAILURES=2" in completed.stdout, completed.stdout + completed.stderr + logs


def test_t18_timeout_pair_is_a_valid_timeout_that_does_not_fail_the_run(runner_result):
    tmp, completed = runner_result
    status, rc, _log = _pair(tmp, "timeoutpair")
    assert rc == 0
    assert status["classification_valid"] is True
    assert status["canonical_outcome"] == "TIMEOUT"
    assert status["supervisor_status"] == "TIMEOUT"
    assert status["child_exit_disposition"] == "SIGTERM_AFTER_DEADLINE"
    assert status["child_returncode"] == -15
    assert "supervisor_exit=124" in _status_line(completed, "timeoutpair")


def test_t18_canonical_error_pair_is_valid_and_fails_the_run_as_before(runner_result):
    tmp, completed = runner_result
    status, rc, _log = _pair(tmp, "errorpair")
    assert rc == 1
    assert status["classification_valid"] is True
    assert status["canonical_outcome"] == "ERROR"
    assert status["supervisor_status"] == "RESOLVED"
    assert "supervisor_exit=0" in _status_line(completed, "errorpair")


def test_t18_only_the_stopped_worker_reaches_the_deadline_and_none_reaches_the_timer(runner_result):
    """Issue #226: deadline に当たるのは worker が止まる ``timeoutpair`` だけで、どの pair も
    runner の timer には当たらない（pair の結末を host の速さで決めていない）。"""

    from scripts.function_tracer_pcode.tests.fixtures.issue165.runner_supervisor import (
        DEADLINE_CONTROL_RECORD,
    )

    tmp, _completed = runner_result
    lines = (tmp / "harness" / DEADLINE_CONTROL_RECORD).read_text(encoding="utf-8").splitlines()
    paths = {}
    for line in lines:
        entry = json.loads(line)
        paths.setdefault(entry["function"], []).append(entry["deadline"])
    # invalidpair は runner が非終端の projection を 1 回だけ再実行する（resume は worker を起こさない）
    assert paths == {
        "timeoutpair": ["worker-stop"],
        "invalidpair": ["worker-exit"],
        "errorpair": ["worker-exit"],
        "unknownpair": ["worker-exit"],
    }


def test_t18_unknown_pair_is_valid(runner_result):
    tmp, _completed = runner_result
    status, rc, _log = _pair(tmp, "unknownpair")
    assert rc == 0
    assert status["classification_valid"] is True
    assert status["canonical_outcome"] == "UNKNOWN"


def test_t18_exit_without_a_result_is_invalid_after_one_resume(runner_result):
    tmp, completed = runner_result
    status, rc, log = _pair(tmp, "invalidpair")
    assert rc == 2
    assert status["classification_valid"] is False
    assert status["error_kind"] == "PAIR_STATUS_AUTHORITY_INVALID"
    assert "not a terminal authority" in status["detail"]
    assert log.count("Supervisor recovery: resuming non-terminal projection") == 1
    assert "supervisor_exit=2" in _status_line(completed, "invalidpair")
