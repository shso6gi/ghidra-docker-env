# -*- coding: utf-8 -*-
"""中断と確定の境界（評価計画 v2 PR-A）。

全件評価を止めて同じ条件で再開したとき、確定した pair だけが再利用され、中断された
pair は確定した結果に見えないまま再実行される、という契約を固定する。

* **再利用の条件**: 有効な署名・期待する identity（``pair_execution_target`` 全体）・
  正規の終端（RESOLVED、または検証済みの durable TIMEOUT / ERROR）の 3 つを満たす
  status だけを SKIP する。署名欄があっても壊れているもの、target が違うもの、終端の
  証拠が無いもの、署名の無い分類失敗の診断は SCHEDULE。確定した ERROR / TIMEOUT は
  再利用する（上書きしない）。
* **未完了の分類**: 分類に失敗した pair（署名の無い operational diagnostic）は
  ``INCOMPLETE`` で、確定した ``ERROR`` ではない。child の rc は分類器の record から
  読み、原因（OOM など）は推定しない。
* **環境依存の ERROR**: 署名済みの ERROR で error kind が環境依存のものは、ERROR の
  まま分母に残り、別に数えるだけ。
* **停止**: supervisor は TERM / INT / HUP で child の process group を止め、終端の
  projection を書かずに終わる。runner は実行中の pair を止めて待ってから tmp を消す。
* **境界と原子性**: 新しい execution は前回の pair-status を消してから始め、分類器は
  pair-status を atomic に書く。実行記録も atomic に置き換える / 追記する。
"""

from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import textwrap
import time
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.decision import classification_failure as cf
from scripts.function_tracer_pcode.authority.decision.canonical_result import (
    main as canonical_result_main,
)
from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
    PAIR_STATUS_OPERATIONAL_DIAGNOSTIC_STATE,
    error_kind_is_environment_dependent,
    generate_pair_status_keypair,
    pair_status_file_skip_decision,
    seal_pair_status,
)
from scripts.function_tracer_pcode.reporting.result_summary import (
    STATUS_ERROR,
    STATUS_INCOMPLETE,
    aggregate_validation_logs_by_function,
    build_run_health_summary,
    read_validation_log_record,
)
from scripts.function_tracer_pcode.tests.unit.test_issue160_runner_identity import (
    COMMON,
    EQ_RUNNER,
    NEQ_RUNNER,
    REPO_ROOT,
    _BOUNDARY_HARNESS,
    _extract_shell_function,
)
from scripts.function_tracer_pcode.tests.unit.test_outcome_transition_axes_and_reason_sets import (  # noqa: E501
    _status_body,
    write_sealed_pair,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_support import (
    supervisor_case,
)

SCHEDULER = REPO_ROOT / "scripts" / "eqbench" / "pair_scheduler.sh"
OPERATIONAL_DIAGNOSTIC = {
    "classification_valid": False,
    "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
    "detail": "ValueError: supervisor projection is not a terminal authority",
}


# ---------------------------------------------------------------------------
# 1. 再利用の条件（署名・identity・正規の終端）
# ---------------------------------------------------------------------------


def _sealed(tmp_path, outcome="UNKNOWN", *, supervisor_status="RESOLVED", corrupt=None):
    tree = tmp_path / "tree"
    status = write_sealed_pair(
        tree, "sample", "f", "B1", "B2", outcome,
        supervisor_status=supervisor_status, corrupt=corrupt,
    )
    target = tmp_path / "target.json"
    target.write_text(json.dumps(
        _status_body("sample", "f", "B1", "B2", outcome, supervisor_status)[
            "pair_execution_target"
        ]
    ))
    return status, target, tree / "pair-status-verification-key.json"


def _decision(status, target, key, *, mode="NORMAL_RESUME"):
    return pair_status_file_skip_decision(
        status, log_path=status.with_name(status.name.replace(".pair-status.json", ".log")),
        public_key_path=key, expected_pair_target_path=target, mode=mode,
    )


@pytest.mark.parametrize(("outcome", "supervisor_status"), (
    ("EQUIVALENT", "RESOLVED"),
    ("NOT_EQ", "RESOLVED"),
    ("UNKNOWN", "RESOLVED"),
    ("ERROR", "RESOLVED"),
    # 正規の期限到達で確定した TIMEOUT と、durable な ERROR も確定結果として再利用する。
    ("TIMEOUT", "TIMEOUT"),
    ("ERROR", "ERROR"),
))
def test_a_decided_pair_is_reused_whatever_its_outcome(tmp_path, outcome, supervisor_status):
    status, target, key = _sealed(tmp_path, outcome, supervisor_status=supervisor_status)
    assert _decision(status, target, key) == "SKIP"


def _flip_signature(payload):
    signature = payload["pair_status_signature"]
    payload["pair_status_signature"] = ("A" if signature[0] != "A" else "B") + signature[1:]
    return payload


def _rewrite_outcome(payload):
    payload["canonical_outcome"] = "EQUIVALENT"
    return payload


def _sealed_by_another_key(payload):
    # 署名としては正しいが、この run の鍵で作られていない status。
    body = {key: value for key, value in payload.items() if not key.startswith("pair_status_")}
    directory = Path(_sealed_by_another_key.directory)
    private_key, public_key = directory / "other.key", directory / "other.pub.json"
    if not public_key.is_file():
        generate_pair_status_keypair(private_key, public_key)
    return dict(seal_pair_status(body, private_key_path=private_key, public_key_path=public_key))


@pytest.mark.parametrize("corrupt", (
    pytest.param(_flip_signature, id="signature-field-present-but-broken"),
    pytest.param(_rewrite_outcome, id="body-changed-after-sealing"),
    pytest.param(_sealed_by_another_key, id="valid-signature-of-another-key"),
))
def test_a_status_that_only_looks_signed_or_terminal_is_scheduled(tmp_path, corrupt):
    _sealed_by_another_key.directory = str(tmp_path)
    status, target, key = _sealed(
        tmp_path, "TIMEOUT", supervisor_status="TIMEOUT", corrupt=corrupt,
    )
    assert _decision(status, target, key) == "SCHEDULE"


def test_a_validly_signed_status_of_another_target_is_scheduled(tmp_path):
    status, target, key = _sealed(tmp_path, "NOT_EQ")
    other = json.loads(target.read_text())
    other["right_binary_sha256"] = "b" * 64
    target.write_text(json.dumps(other))
    assert _decision(status, target, key) == "SCHEDULE"


@pytest.mark.parametrize("content", (
    json.dumps(OPERATIONAL_DIAGNOSTIC),
    '{"canonical_outcome": "ERROR", "pair_status_sig',  # torn
    "",
))
def test_an_unterminated_or_torn_status_is_scheduled(tmp_path, content):
    status, target, key = _sealed(tmp_path)
    status.write_text(content)
    assert _decision(status, target, key) == "SCHEDULE"


def test_a_status_without_its_log_is_scheduled(tmp_path):
    status, target, key = _sealed(tmp_path)
    status.with_name("f_B1_B2.log").write_text("")
    assert _decision(status, target, key) == "SCHEDULE"


# ---------------------------------------------------------------------------
# 2. 未完了（分類失敗）と環境依存の ERROR の集計
# ---------------------------------------------------------------------------


def _write_failure_record(path: Path, child_returncode) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    cf.write_failure_record(path, {
        "schema": cf.CLASSIFICATION_FAILURE_SCHEMA,
        "detail": "ValueError: not terminal",
        "projection": {"readable": True, "value": {
            "status": "INVALID", "error_code": "CANONICAL_CHILD_RESULT_INVALID",
            "child_returncode": child_returncode,
        }},
        "durable": {"readable": False, "error": "not read"},
    })


def test_an_unterminated_pair_is_incomplete_and_keeps_only_the_recorded_rc(tmp_path):
    log = tmp_path / "f_B1_B2.log"
    log.write_text("Result: TIMEOUT\n")
    log.with_suffix(".pair-status.json").write_text(json.dumps(OPERATIONAL_DIAGNOSTIC))
    _write_failure_record(
        tmp_path / ".runtime-metrics" / "f_B1_B2.classification-failure.json", -9,
    )

    record = read_validation_log_record(log, canonical_only=True)
    summary = aggregate_validation_logs_by_function((log,), canonical_only=True)
    health = build_run_health_summary(summary)

    # 署名済みの終端 status が無いので、log の "Result:" 行にかかわらず未完了。
    assert record.status == STATUS_INCOMPLETE
    assert summary.overall.count(STATUS_ERROR) == 0
    assert summary.overall.count(STATUS_INCOMPLETE) == 1
    assert health["final_result_counts"][STATUS_INCOMPLETE] == 1
    # rc は記録された値だけ（-9 は外からの kill を示すが、OOM とは書かない）。
    assert record.pair_status_metadata["child_returncode"] == -9
    assert health["child_returncode_counts"] == {"-9": 1}
    assert "oom" not in json.dumps(record.pair_status_metadata).lower()


def test_the_validator_reports_the_operational_diagnostic_as_incomplete(tmp_path):
    status = tmp_path / "f_B1_B2.pair-status.json"
    status.write_text(json.dumps(OPERATIONAL_DIAGNOSTIC))
    result = subprocess.run(
        [sys.executable, "-m",
         "scripts.function_tracer_pcode.authority.decision.pair_status_authority",
         "--validate-pair-status", str(status), "--allow-operational-diagnostic"],
        capture_output=True, text=True, check=False, cwd=REPO_ROOT,
    )
    assert result.returncode == 0
    assert result.stdout.strip() == PAIR_STATUS_OPERATIONAL_DIAGNOSTIC_STATE == "INCOMPLETE"


@pytest.mark.parametrize(("record", "expected"), (
    ({"projection": {"readable": True, "value": {"child_returncode": -9}}}, -9),
    ({"projection": {"readable": True, "value": {"child_returncode": 0}}}, 0),
    ({"projection": {"readable": True, "value": {"child_returncode": None}}}, None),
    ({"projection": {"readable": True, "value": {"child_returncode": True}}}, None),
    ({"projection": {"readable": False, "error": "gone"}}, None),
    (None, None),
))
def test_the_recorded_child_returncode_is_read_and_never_guessed(tmp_path, record, expected):
    path = tmp_path / "record.json"
    if record is not None:
        path.write_text(json.dumps(record))
    assert cf.recorded_child_returncode(path) == expected
    printed = subprocess.run(
        [sys.executable, "-m",
         "scripts.function_tracer_pcode.authority.decision.classification_failure",
         "--print-child-returncode", str(path)],
        capture_output=True, text=True, check=True, cwd=REPO_ROOT,
    ).stdout.strip()
    assert printed == ("-" if expected is None else str(expected))


@pytest.mark.parametrize(("error_kind", "environment_dependent"), (
    ("CLI_STARTUP_ERROR", True),
    ("strategy_exception", False),
    ("checker_error", False),
    (None, False),
))
def test_an_environment_dependent_error_stays_a_decided_error(
    tmp_path, error_kind, environment_dependent,
):
    assert error_kind_is_environment_dependent(error_kind) is environment_dependent

    tree = tmp_path / "tree"
    status = write_sealed_pair(tree, "sample", "f", "B1", "B2", "ERROR")
    if error_kind is not None:
        # 封を作り直す（error_kind も署名の対象）。
        body = _status_body("sample", "f", "B1", "B2", "ERROR", "RESOLVED")
        body["error_kind"] = error_kind
        status.write_text(json.dumps(seal_pair_status(
            body, private_key_path=tree / "pair-status-signing.key",
            public_key_path=tree / "pair-status-verification-key.json",
        )))
    log = status.with_name("f_B1_B2.log")
    summary = aggregate_validation_logs_by_function((log,), canonical_only=True)
    health = build_run_health_summary(summary)
    # 環境依存でも確定した ERROR として分母に残る。別の数は内訳だけ。
    assert summary.overall.count(STATUS_ERROR) == 1
    assert health["final_result_counts"][STATUS_ERROR] == 1
    assert health["environment_dependent_error_results"] == int(environment_dependent)


# ---------------------------------------------------------------------------
# 3. 分類器は pair-status を atomic に書く
# ---------------------------------------------------------------------------


def test_the_classifier_publishes_the_pair_status_atomically(tmp_path):
    output = tmp_path / "f_B1_B2.pair-status.json"
    output.write_text("previous execution\n")
    missing = tmp_path / "missing"
    code = canonical_result_main([
        "--classify-pair-log", str(missing / "f.log"),
        "--supervisor-projection", str(missing / "projection.json"),
        "--checkpoint-root", str(missing), "--execution-nonce", "nonce",
        "--supervisor-signing-key-id", "k", "--supervisor-signing-key-file", str(missing / "k"),
        "--worker-signing-key-id", "k", "--worker-signing-key-file", str(missing / "k"),
        "--pair-status-signing-private-key-file", str(missing / "k"),
        "--pair-status-verification-key-file", str(missing / "k"),
        "--pair-execution-target-file", str(missing / "target.json"),
        "--pair-status-output", str(output),
    ])
    assert code == 2
    published = json.loads(output.read_text())
    assert published["classification_valid"] is False
    assert published["error_kind"] == "PAIR_STATUS_AUTHORITY_INVALID"
    # rename だけで公開する（同じ dir に一時 file を残さない）。
    assert sorted(p.name for p in tmp_path.iterdir()) == [output.name]


# ---------------------------------------------------------------------------
# 4. supervisor は止められたら child を止め、終端を書かない
# ---------------------------------------------------------------------------


def _supervisor_argv(config):
    argv = [
        sys.executable, "-m",
        "scripts.function_tracer_pcode.authority.process.supervisor_command",
        "--checkpoint-root", str(config.checkpoint_root),
        "--authority-output", str(config.authority_output),
        "--working-directory", str(config.working_directory),
        "--execution-nonce", config.execution_nonce,
        "--result-occurrence-id", config.result_occurrence_id,
        "--source-snapshot-fingerprint", config.source_snapshot_fingerprint,
        "--stream-id", config.stream_id,
        "--deadline-policy-digest", config.deadline_policy_digest,
        "--supervisor-signing-key-id", config.supervisor_signing_key_id,
        "--supervisor-signing-key-file", str(config.supervisor_signing_key_file),
        "--worker-signing-key-id", config.worker_signing_key_id,
        "--worker-signing-key-file", str(config.worker_signing_key_file),
        "--timeout-seconds", "600", "--kill-grace-seconds", "5",
        "--allow-child-exit-resolution", "--",
    ]
    return argv + list(config.child_command)


def _wait_for(predicate, timeout=30.0):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if predicate():
            return True
        time.sleep(0.05)
    return False


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    stat = Path(f"/proc/{pid}/stat")
    try:
        return stat.read_text().rsplit(")", 1)[1].split()[0] != "Z"
    except (OSError, IndexError):
        return False


@pytest.mark.parametrize("signum", (signal.SIGTERM, signal.SIGINT, signal.SIGHUP))
def test_an_interrupted_supervisor_stops_its_child_and_publishes_no_terminal(tmp_path, signum):
    marker = tmp_path / "child.pid"
    child = (
        sys.executable, "-c",
        "import os, sys, time; open(sys.argv[1], 'w').write(str(os.getpid())); time.sleep(120)",
        str(marker),
    )
    with supervisor_case(tmp_path / "case", child, allow_child_exit_resolution=True) as case:
        process = subprocess.Popen(
            _supervisor_argv(case.config), cwd=REPO_ROOT,
            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
        )
        try:
            assert _wait_for(lambda: marker.is_file() and marker.read_text().strip())
            child_pid = int(marker.read_text())
            process.send_signal(signum)
            returncode = process.wait(timeout=30)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()
        assert returncode == 128 + signum
        assert _wait_for(lambda: not _alive(child_pid), timeout=10)
        # 中断は終端ではない: projection も child の終了の evidence も書かない。
        assert not case.config.authority_output.exists()
        store = case.config.checkpoint_root / case.config.execution_nonce
        assert not any(path.name.startswith("child-exit") for path in store.rglob("*"))


# ---------------------------------------------------------------------------
# 5. runner: 実行中の pair を止めて待ってから片付ける
# ---------------------------------------------------------------------------

_TERMINATE_HARNESS = textwrap.dedent("""\
    set -u
    source "__SCHEDULER__"
    done_group() { :; }
    FAILURES=0
    pair_scheduler_init 4 done_group FAILURES
    pair_scheduler_open_group g
    job() {
        # 子 process（supervisor の代役）が終わったら「分類」する。止めた pair は
        # ここへ来てはならない。
        sh -c 'echo $$ >> "__TMP__/children"; exec sleep 60' &
        wait $!
        echo classified >> "__TMP__/classified-$1"
    }
    for index in 1 2 3; do
        job "$index" &
        pair_scheduler_start_job g "$!"
    done
    while [[ "$(wc -l < "__TMP__/children" 2>/dev/null || echo 0)" -lt 3 ]]; do sleep 0.05; done
    pair_scheduler_terminate_all 5
    echo "active=$PAIR_SCHEDULER_ACTIVE_JOBS failures=$FAILURES"
""")


def test_the_scheduler_stops_running_pairs_before_anything_classifies_them(tmp_path):
    script = (_TERMINATE_HARNESS.replace("__SCHEDULER__", str(SCHEDULER))
              .replace("__TMP__", str(tmp_path)))
    started = time.monotonic()
    result = subprocess.run(["bash", "-c", script], capture_output=True, text=True, timeout=60)
    assert result.returncode == 0, result.stderr
    assert time.monotonic() - started < 30
    assert "active=0 failures=0" in result.stdout
    children = [int(line) for line in (tmp_path / "children").read_text().split()]
    assert len(children) == 3
    assert _wait_for(lambda: not any(_alive(pid) for pid in children), timeout=5)
    assert not list(tmp_path.glob("classified-*"))


def test_terminate_all_is_a_no_op_before_the_scheduler_exists(tmp_path):
    result = subprocess.run(
        ["bash", "-c", f'set -u; source "{SCHEDULER}"; pair_scheduler_terminate_all 1; echo ok'],
        capture_output=True, text=True, timeout=30,
    )
    assert result.returncode == 0 and result.stdout.strip() == "ok", result.stderr


@pytest.mark.parametrize("runner", (EQ_RUNNER, NEQ_RUNNER))
def test_the_runner_stops_pairs_before_it_removes_the_run_tmpdir(runner):
    source = runner.read_text(encoding="utf-8")
    if runner == EQ_RUNNER:
        handler = _extract_shell_function(source, "handle_eqbench_signal")
        cleanup = "cleanup_eqbench_run_tmpdir"
    else:
        handler = _extract_shell_function(source, "handle_neq_signal")
        cleanup = "exit"
    assert "pair_scheduler_terminate_all" in handler
    assert handler.index("pair_scheduler_terminate_all") < handler.index(cleanup)
    for signal_name in ("HUP", "INT", "TERM"):
        assert any(
            line.strip().startswith("trap ") and signal_name in line
            and ("handle_eqbench_signal" in line or "handle_neq_signal" in line)
            for line in source.splitlines()
        ), signal_name


# ---------------------------------------------------------------------------
# 6. 境界: 前回の pair-status を捨ててから実行し、実行記録は atomic に書く
# ---------------------------------------------------------------------------

_STALE_PROBE = """#!/bin/sh
# 新しい execution の最初の interpreter 呼び出しの時点で、前回の pair-status が残っているか。
if [ ! -f "$PROBE_MARKER" ]; then
  if [ -e "$PROBE_STATUS" ] || ls "$PROBE_DIR"/.*.pair-status.json.* >/dev/null 2>&1; then
    echo stale > "$PROBE_MARKER"
  else
    echo clean > "$PROBE_MARKER"
  fi
fi
echo stub
exit 0
"""


@pytest.mark.parametrize("runner", (EQ_RUNNER, NEQ_RUNNER))
def test_run_pair_drops_the_previous_pair_status_at_the_execution_boundary(tmp_path, runner):
    out = tmp_path / "out" / "sample" / "f"
    out.mkdir(parents=True)
    (tmp_path / "runtmp").mkdir()
    stem = "f_B1_B2" if runner == EQ_RUNNER else "f_N_B1_O_B2"
    status = out / f"{stem}.pair-status.json"
    status.write_text('{"note": "previous-execution"}\n')
    (out / f".{stem}.pair-status.json.partial").write_text("torn")
    probe = tmp_path / "python-probe"
    probe.write_text(_STALE_PROBE)
    probe.chmod(0o755)
    function = _extract_shell_function(runner.read_text(encoding="utf-8"), "run_pair")
    if runner == EQ_RUNNER:
        args = f'"sample" "f" "B1" "B2" "/left" "/right" "{out}" 1 1 "/target"'
    else:
        args = f'"sample" "f" "N_B1" "O_B2" "/left" "/right" "{out}" 1 1 "/target" 1 1 1'
    script = (
        _BOUNDARY_HARNESS.replace("__COMMON__", str(COMMON))
        .replace("__TMP__", str(tmp_path)).replace("__FUNCTION__", function)
        .replace("__ARGS__", args)
    )
    marker = tmp_path / "marker"
    subprocess.run(
        ["bash", "-c", script], capture_output=True, timeout=120,
        env={**os.environ, "PROBE_MARKER": str(marker), "PROBE_STATUS": str(status),
             "PROBE_DIR": str(out)},
    )
    assert marker.read_text().strip() == "clean"


@pytest.mark.parametrize("runner", (EQ_RUNNER, NEQ_RUNNER))
def test_the_runner_hands_the_status_path_to_the_classifier_instead_of_redirecting(runner):
    function = _extract_shell_function(runner.read_text(encoding="utf-8"), "run_pair")
    assert "--pair-status-output" in function
    assert '> "$pair_status_file"' not in function and '> "$status_file"' not in function


def _common(script: str, tmp_path: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["bash", "-c", f'set -u; source "{COMMON}"; {script}'],
        capture_output=True, text=True, timeout=60, cwd=tmp_path,
    )


def test_the_run_manifest_is_replaced_and_extended_atomically(tmp_path):
    manifest = tmp_path / "run_manifest.txt"
    candidate = tmp_path / "candidate.txt"
    candidate.write_text("run_kind=x\n")
    result = _common(
        f'validation_install_file_atomically "{candidate}" "{manifest}" && '
        f'printf "end=1\\n" | validation_append_file_atomically "{manifest}"', tmp_path,
    )
    assert result.returncode == 0, result.stderr
    assert manifest.read_text() == "run_kind=x\nend=1\n"
    assert sorted(p.name for p in tmp_path.iterdir()) == ["candidate.txt", "run_manifest.txt"]
    # 置き換え先の dir に書けなければ失敗を返し、元の file を壊さない。
    result = _common(
        f'validation_install_file_atomically "{candidate}" "{tmp_path}/missing/run_manifest.txt"',
        tmp_path,
    )
    assert result.returncode != 0
    assert manifest.read_text() == "run_kind=x\nend=1\n"


def test_the_runners_write_the_run_manifest_only_through_the_atomic_helpers():
    for runner in (EQ_RUNNER, NEQ_RUNNER):
        for line in runner.read_text(encoding="utf-8").splitlines():
            stripped = line.strip()
            if stripped.startswith("#"):
                continue
            for target in ('"$RUN_MANIFEST_FILE"', '"$RUN_MANIFEST"',
                           '"$OUTPUT_BASE_DIR/run_manifest.txt"'):
                assert f"> {target}" not in stripped, (runner.name, line)
                assert f"cp \"$CANDIDATE_RUN_MANIFEST_FILE\" {target}" not in stripped
