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
* **停止**: runner は停止要求を受けたとき、また途中で失敗して抜けるときも、この execution
  が所有する process をすべて凍結し、SIGKILL し、消えたのを確かめてから tmp を消す。所有は
  scheduler への登録や親子関係によらない（runner は owner token を持たせて自分を exec し
  直すので、exec を経ない fork の子も token を持つ）。exec し直しは runner の (pid, 起動時刻)
  に結び付けて 1 回だけで、環境の大きさや受け継いだ owner の値、pipefail に左右されない。
  停止の確認は最新の走査だけで判定し、所有している process も所有かどうかを読めない
  process も 2 回続けて見えないときだけ成功する（確認の途中の出現・交代・可読性の変化を
  含む）。その 2 回は期限より前に終わっていなければならず、期限は成功より先に調べる。成否は
  stop の verdict（CONFIRMED / DEADLINE / UNVERIFIABLE。観測の失敗は例外）だけが決め、最新の
  走査が空でも期限切れは失敗。確かめられなければ tmp を残して exit 75 で失敗を示す（既に失敗の
  exit code ならそれを残す）。停止は時間の設定に依存しない。
  supervisor 単体も TERM / INT / HUP で child の process group を止め、終端の projection を
  書かずに終わる。
* **実行境界**: 新しい execution は前回の pair-status・journal・診断・receipt を消し、消えた
  ことを確かめてから解析を始める。確かめられなければ解析を始めない。
* **結果の確定**: 分類器は pair-status を atomic に公開し、公開できなければ status を残さない。
  runner は、署名・target・正規の終端・**この execution の nonce** が揃った status だけを
  確定とし、それ以外は INCOMPLETE にする（前回の status を今回の結果と取り違えない）。
  実行記録も atomic に置き換える / 追記する。

再現と回帰はどれも実際の signal・子 process・ファイル操作で確かめる（runner は実際の
handler と trap、共有の scheduler と common を使い、解析だけを stand-in に置き換える）。
"""

from __future__ import annotations

import json
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path

import pytest

from scripts.eqbench.runner_processes import StopVerdict
from scripts.function_tracer_pcode.authority.decision import classification_failure as cf
from scripts.function_tracer_pcode.authority.decision.canonical_result import (
    main as canonical_result_main,
)
from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
    PAIR_STATUS_OPERATIONAL_DIAGNOSTIC_STATE,
    error_kind_is_environment_dependent,
    generate_pair_status_keypair,
    pair_status_file_skip_decision,
    resolve_pair_execution,
    seal_pair_status,
    write_pair_status_file,
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
    Checkpoint,
    ChildScript,
    Deadline,
    Envelope,
    Exit,
    Stop,
    classify,
    run_supervisor,
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


def test_a_status_that_cannot_be_published_leaves_no_status(tmp_path):
    if os.geteuid() == 0:
        pytest.skip("directory permissions do not bind root")
    directory = tmp_path / "out"
    directory.mkdir()
    directory.chmod(0o555)
    missing = tmp_path / "missing"
    try:
        result = subprocess.run(
            [sys.executable, "-m",
             "scripts.function_tracer_pcode.authority.decision.canonical_result",
             "--classify-pair-log", str(missing / "f.log"),
             "--supervisor-projection", str(missing / "projection.json"),
             "--checkpoint-root", str(missing), "--execution-nonce", "nonce",
             "--supervisor-signing-key-id", "k", "--supervisor-signing-key-file", str(missing / "k"),
             "--worker-signing-key-id", "k", "--worker-signing-key-file", str(missing / "k"),
             "--pair-status-signing-private-key-file", str(missing / "k"),
             "--pair-status-verification-key-file", str(missing / "k"),
             "--pair-execution-target-file", str(missing / "target.json"),
             "--pair-status-output", str(directory / "f_B1_B2.pair-status.json")],
            capture_output=True, text=True, check=False, cwd=REPO_ROOT,
        )
    finally:
        directory.chmod(0o755)
    assert result.returncode == 2
    assert "Pair-status publication failed" in result.stderr
    assert list(directory.iterdir()) == []


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
        "--timeout-seconds", "600", "--kill-grace-seconds", "0.5",
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
        state = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0]
    except (OSError, IndexError):
        return False
    return state != "Z"


@pytest.mark.parametrize(("signals", "expected"), (
    ((signal.SIGTERM,), signal.SIGTERM),
    ((signal.SIGINT,), signal.SIGINT),
    ((signal.SIGHUP,), signal.SIGHUP),
    # 同時に届いた複数の停止要求: どれか 1 つで終わり、残りは停止を中断しない
    # （Python は保留中の handler を signal 番号順に実行するので、どれで終わるかは決めない）。
    ((signal.SIGTERM, signal.SIGINT, signal.SIGHUP), None),
))
def test_an_interrupted_supervisor_stops_its_child_and_publishes_no_terminal(
    tmp_path, signals, expected,
):
    marker = tmp_path / "child.pid"
    child = (
        sys.executable, "-c",
        "import os, signal, sys, time\n"
        "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"  # TERM を無視する child も止まる
        "open(sys.argv[1], 'w').write(str(os.getpid())); time.sleep(120)",
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
            for signum in signals:
                process.send_signal(signum)
            returncode = process.wait(timeout=30)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()
        if expected is None:
            assert returncode in {128 + signum for signum in signals}
        else:
            assert returncode == 128 + expected
        assert _wait_for(lambda: not _alive(child_pid), timeout=10)
        # 中断は終端ではない: projection も child の終了の evidence も書かない。
        assert not case.config.authority_output.exists()
        store = case.config.checkpoint_root / case.config.execution_nonce
        assert not any(path.name.startswith("child-exit") for path in store.rglob("*"))


# ---------------------------------------------------------------------------
# 5. runner の停止。契約: 中断した pair の process が 1 つも処理を続けていないことを確かめて
#    から run の一時 dir を消す。確かめられなければ一時 dir を残し、失敗（exit 75）を示す。
#    runner の実際の ownership の取得・handler・trap、共有の scheduler と common を使い、
#    pair だけを「子が終わったら分類する」stand-in に置き換える。harness は file として
#    実行する（runner と同じく、所有権の取得で自分を exec し直す）。
# ---------------------------------------------------------------------------

_STOP_HARNESS = """set -u
source "__COMMON__"
validation_claim_process_ownership "$0" "$@"
source "__SCHEDULER__"
PYTHON_BIN="__PYTHON_BIN__"
# runner が受理する小数の猶予（停止はこの値に依存しない）
PAIR_PROCESS_KILL_AFTER=0.5s; PAIR_PROCESS_KILL_AFTER_SECONDS=0.5
EQBENCH_TMPDIR="__TMP__"; EQBENCH_RUN_TMPDIR="__TMP__/runtmp"; RUN_TMP="__TMP__/runtmp"
mkdir -p "$RUN_TMP"
[[ -p "__TMP__/fifo" ]] || mkfifo "__TMP__/fifo"
echo "$$" > "__TMP__/runner.pid"
check_then_remove_tmp() {
    local pid state
    for pid in $(cat "__TMP__/pids" 2>/dev/null); do
        state="$(cut -d')' -f2 "/proc/$pid/stat" 2>/dev/null | awk '{print $1}')"
        if [[ -n "$state" && "$state" != Z ]]; then echo "alive-at-tmp-removal $pid" >> "__TMP__/events"; fi
    done
    echo "tmp-removed" >> "__TMP__/events"
    rm -rf -- "$RUN_TMP"
}
cleanup_eqbench_run_tmpdir() { check_then_remove_tmp; }
cleanup() { check_then_remove_tmp; }
__HANDLERS__
done_group() { :; }
FAILURES=0
pair_scheduler_init 4 done_group FAILURES
pair_scheduler_open_group g
run_pair() {
    # stand-in: 子（supervisor の代役）が終わったら「分類」する。止めた pair はここへ来ない。
    echo "$BASHPID" >> "__TMP__/pids"
    __CHILD__
    echo "classified $1" >> "__TMP__/events"
}
__INJECT__
"""

_CHILDREN = {
    "plain": """sh -c 'echo $$ >> "__TMP__/pids"; exec sleep 30' &
    wait $!""",
    "short": """sh -c 'echo $$ >> "__TMP__/pids"; exit 0' &
    wait $!""",
    # TERM を無視する子孫
    "ignores-term": """sh -c 'trap "" TERM; echo $$ >> "__TMP__/pids"; while :; do sleep 1; done' &
    wait $!""",
    # exec を経て親を失い、runner の process tree から外れる孫
    "exec-orphan": """( setsid sh -c 'echo $$ >> "__TMP__/pids"; exec sleep 30' & )
    sh -c 'echo $$ >> "__TMP__/pids"; exec sleep 30' &
    wait $!""",
    # exec を一度も経ない bash の孫が親を失い、runner の process tree から外れて処理を続ける
    "fork-orphan": """( ( echo "$BASHPID" >> "__TMP__/pids"
        while :; do read -r -t 0.05 _ <> "__TMP__/fifo"; echo tick >> "__TMP__/ticks"; done ) & )
    sh -c 'echo $$ >> "__TMP__/pids"; exec sleep 30' &
    wait $!""",
    # 所有かどうかを読めない（non-dumpable で environ が読めない）孤児
    "unverifiable": """( setsid "__PYTHON__" -c 'import ctypes, os, time
ctypes.CDLL(None).prctl(4, 0, 0, 0, 0)
open("__TMP__/unverifiable", "a").write(str(os.getpid()) + chr(10))
time.sleep(30)' </dev/null >/dev/null 2>&1 & )
    until [ "$(wc -l < "__TMP__/unverifiable" 2>/dev/null || echo 0)" -ge "$1" ]; do sleep 0.05; done
    sh -c 'echo $$ >> "__TMP__/pids"; exec sleep 30' &
    wait $!""",
    # 確かめられない孤児が、停止が pair を凍結した（または消した）のを見てから子を残して終わる（交代）
    "unverifiable-replaced": """( setsid "__PYTHON__" -c 'import ctypes, os, time
ctypes.CDLL(None).prctl(4, 0, 0, 0, 0)
out = "__TMP__/unverifiable"
open(out, "a").write(str(os.getpid()) + chr(10))
def stopping():
    # 停止が始まった: pair の process が凍結された、または消えた
    for pid in open("__TMP__/pids").read().split():
        try:
            state = open("/proc/%s/stat" % pid).read().rsplit(")", 1)[1].split()[0]
        except (OSError, IndexError):
            return True
        if state in ("T", "t", "Z"):
            return True
    return False
limit = time.monotonic() + 60
while not stopping() and time.monotonic() < limit:
    time.sleep(0.002)
if os.fork() == 0:
    open(out, "a").write(str(os.getpid()) + chr(10))
    time.sleep(30)
os._exit(0)' </dev/null >/dev/null 2>&1 & )
    until [ "$(wc -l < "__TMP__/unverifiable" 2>/dev/null || echo 0)" -ge "$1" ]; do sleep 0.05; done
    sh -c 'echo $$ >> "__TMP__/pids"; exec sleep 30' &
    wait $!""",
}

_INJECTIONS = {
    # 起動の直前に停止要求: pair は 1 つも起動しない
    "before-launch": """kill -__SIG__ $$
pair_scheduler_launch_job g run_pair 1
wait""",
    # fork の直後、scheduler への登録の前に停止要求
    "after-fork-before-registration": """eval "$(declare -f pair_scheduler_start_job | sed '1s/pair_scheduler_start_job/_registered_start_job/')"
pair_scheduler_start_job() { kill -__SIG__ $$; _registered_start_job "$@"; }
pair_scheduler_launch_job g run_pair 1
wait""",
    # 登録の後（pair が子を持ってから）に停止要求
    "after-registration": """pair_scheduler_launch_job g run_pair 1
pair_scheduler_launch_job g run_pair 2
until [[ "$(wc -l < "__TMP__/pids" 2>/dev/null || echo 0)" -ge __READY__ ]]; do sleep 0.05; done
kill -__SIG__ $$
wait""",
    # 停止の最中に、この run が所有しない別の process から INT / HUP が届き続ける。
    # 送り手は runner の tree からも token からも外れている（停止で止められない）。
    # pair の子が凍結された（= 停止が始まった）のを見てから送り始める。
    "repeated-signals": """pair_scheduler_launch_job g run_pair 1
until [[ "$(wc -l < "__TMP__/pids" 2>/dev/null || echo 0)" -ge 2 ]]; do sleep 0.05; done
child="$(sed -n 2p "__TMP__/pids")"
( setsid env EQBENCH_PROCESS_OWNER_TOKEN=not-this-run sh -c '
    runner=$1; child=$2
    while :; do
        state=$(cut -d")" -f2 "/proc/$child/stat" 2>/dev/null | cut -d" " -f2)
        case "$state" in T|t|Z|"") break ;; esac
    done
    i=0
    while [ $i -lt 400 ] && kill -INT "$runner" 2>/dev/null; do
        kill -HUP "$runner" 2>/dev/null; echo sent >> "__TMP__/sender"; i=$((i + 1)); sleep 0.002
    done' sender "$$" "$child" & )
kill -__SIG__ $$
wait""",
    # 停止要求ではなく、runner が途中で失敗して抜ける（EXIT の経路）
    "error-exit": """pair_scheduler_launch_job g run_pair 1
until [[ "$(wc -l < "__TMP__/pids" 2>/dev/null || echo 0)" -ge 2 ]]; do sleep 0.05; done
exit 3""",
    # 正常に完了する（停止要求なし）
    "normal": """pair_scheduler_launch_job g run_pair 1
pair_scheduler_close_group g
pair_scheduler_finalize""",
    # 外から停止要求が来るまで待つ（別 run との対照用）
    "wait-external": """pair_scheduler_launch_job g run_pair 1
wait""",
}


def _runner_handlers(runner: Path) -> str:
    source = runner.read_text(encoding="utf-8")
    parts = []
    if runner == EQ_RUNNER:
        parts.append(_extract_shell_function(source, "handle_eqbench_signal"))
    parts.extend(line for line in source.splitlines() if line.startswith("trap "))
    return "\n".join(parts)


def _harness_script(tmp_path, runner, injection, signal_name, child, ready=4, python_bin=None):
    script = (
        _STOP_HARNESS
        .replace("__HANDLERS__", _runner_handlers(runner))
        .replace("__CHILD__", _CHILDREN[child])
        .replace("__INJECT__", _INJECTIONS[injection])
        .replace("__COMMON__", str(COMMON)).replace("__SCHEDULER__", str(SCHEDULER))
        .replace("__PYTHON_BIN__", str(python_bin or sys.executable))
        .replace("__PYTHON__", sys.executable).replace("__SIG__", signal_name)
        .replace("__READY__", str(ready)).replace("__TMP__", str(tmp_path))
    )
    path = tmp_path / "runner-harness.sh"
    path.write_text(script, encoding="utf-8")
    return path


def _lines(path: Path):
    return path.read_text().split() if path.exists() else []


def _run_stop_harness(
    tmp_path, runner, injection, signal_name="TERM", child="plain", ready=4, python_bin=None,
):
    script = _harness_script(tmp_path, runner, injection, signal_name, child, ready, python_bin)
    result = subprocess.run(
        ["bash", str(script)], capture_output=True, text=True, timeout=180, cwd=REPO_ROOT,
    )
    time.sleep(1.0)  # 取りこぼした pair が残っていれば、その間に「分類」まで進む
    events = (tmp_path / "events").read_text() if (tmp_path / "events").exists() else ""
    pids = [int(p) for p in _lines(tmp_path / "pids")]
    return result, events, pids


def _assert_stopped_before_removal(tmp_path, result, events, pids, exit_code):
    assert result.returncode == exit_code, (result.returncode, result.stderr)
    assert "classified" not in events, events
    assert "alive-at-tmp-removal" not in events, events
    assert events.strip().splitlines()[-1] == "tmp-removed"
    assert not (tmp_path / "runtmp").exists()
    assert not [pid for pid in pids if _alive(pid)]


_EXIT = {"TERM": 143, "INT": 130, "HUP": 129}
_RUNNERS = pytest.mark.parametrize("runner", (EQ_RUNNER, NEQ_RUNNER), ids=("eq", "neq"))


@_RUNNERS
@pytest.mark.parametrize("injection", (
    "before-launch", "after-fork-before-registration", "after-registration",
))
@pytest.mark.parametrize("signal_name", ("TERM", "INT", "HUP"))
def test_a_stop_request_stops_every_pair_before_the_tmpdir_is_removed(
    tmp_path, runner, injection, signal_name,
):
    result, events, pids = _run_stop_harness(tmp_path, runner, injection, signal_name)
    _assert_stopped_before_removal(tmp_path, result, events, pids, _EXIT[signal_name])
    if injection == "before-launch":
        assert pids == []


@_RUNNERS
@pytest.mark.parametrize("child", ("ignores-term", "exec-orphan", "fork-orphan"))
def test_descendants_that_ignore_term_or_left_the_tree_are_stopped(tmp_path, runner, child):
    result, events, pids = _run_stop_harness(
        tmp_path, runner, "after-registration", child=child, ready=6 if "orphan" in child else 4,
    )
    _assert_stopped_before_removal(tmp_path, result, events, pids, 143)
    if child == "fork-orphan":
        # exec を経ない孫が、tmp を消した後に処理を続けていない（tick が増えない）。
        before = len(_lines(tmp_path / "ticks"))
        time.sleep(0.5)
        assert len(_lines(tmp_path / "ticks")) == before


@_RUNNERS
@pytest.mark.parametrize("child", ("unverifiable", "unverifiable-replaced"))
def test_an_unverifiable_process_keeps_the_tmpdir_and_fails_the_stop(tmp_path, runner, child):
    try:
        result, events, pids = _run_stop_harness(
            tmp_path, runner, "after-registration", child=child, ready=4,
        )
        # 所有かどうかを読めない process があれば、止めたとは言えない: tmp を残して失敗を示す。
        assert result.returncode == 75, (result.returncode, result.stderr)
        assert "tmp-removed" not in events, events
        assert (tmp_path / "runtmp").is_dir()
        assert "ownership could not be read" in result.stderr
        assert "classified" not in events
        # 所有を確かめられない process には signal を送らない（他人のものかもしれない）。
        unverifiable = [int(p) for p in _lines(tmp_path / "unverifiable")]
        if child == "unverifiable":
            assert len(unverifiable) == 2 and all(_alive(pid) for pid in unverifiable)
        else:
            # 親は終わり、残った子（確かめられない）は止められずに残っている。
            assert len(unverifiable) == 4
            assert len([pid for pid in unverifiable if _alive(pid)]) == 2
    finally:
        for pid in _lines(tmp_path / "unverifiable"):
            try:
                os.kill(int(pid), signal.SIGKILL)
            except ProcessLookupError:
                pass


@_RUNNERS
def test_repeated_stop_requests_end_with_the_first_signal(tmp_path, runner):
    result, events, pids = _run_stop_harness(tmp_path, runner, "repeated-signals", "TERM")
    # 停止の最中に届いた INT / HUP は停止を中断せず、最初の TERM で終わる。
    assert (tmp_path / "sender").exists(), "no signal reached the runner during the stop"
    _assert_stopped_before_removal(tmp_path, result, events, pids, 143)
    assert events.count("tmp-removed") == 1


@_RUNNERS
def test_an_error_exit_also_stops_the_pairs_before_the_tmpdir_is_removed(tmp_path, runner):
    result, events, pids = _run_stop_harness(tmp_path, runner, "error-exit")
    _assert_stopped_before_removal(tmp_path, result, events, pids, 3)


@_RUNNERS
def test_a_normal_completion_classifies_and_removes_the_tmpdir(tmp_path, runner):
    result, events, pids = _run_stop_harness(tmp_path, runner, "normal", child="short")
    assert result.returncode == 0, result.stderr
    assert "classified 1" in events and events.strip().splitlines()[-1] == "tmp-removed"
    assert not (tmp_path / "runtmp").exists()


@_RUNNERS
def test_a_stop_leaves_other_runs_and_unrelated_processes_alive(tmp_path, runner):
    """対照: 同じ user の別の run と無関係な process、runner の呼び出し元は止めない。"""

    first, second = tmp_path / "first", tmp_path / "second"
    first.mkdir()
    second.mkdir()
    unrelated = subprocess.Popen(["sleep", "60"])  # 同じ user、run の開始後に起動、token なし
    runners = []
    try:
        for directory in (first, second):
            script = _harness_script(directory, runner, "wait-external", "TERM", "plain")
            runners.append(subprocess.Popen(
                ["bash", str(script)], cwd=REPO_ROOT,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            ))
        assert _wait_for(lambda: len(_lines(first / "pids")) >= 2 and len(_lines(second / "pids")) >= 2)
        runners[0].send_signal(signal.SIGTERM)
        assert runners[0].wait(timeout=60) == 143
        assert not [pid for pid in map(int, _lines(first / "pids")) if _alive(pid)]
        assert [pid for pid in map(int, _lines(second / "pids")) if _alive(pid)] == list(
            map(int, _lines(second / "pids")))
        assert (second / "runtmp").is_dir()
        assert unrelated.poll() is None
        assert _alive(os.getpid())  # 呼び出し元（この test の process）
        runners[1].send_signal(signal.SIGTERM)
        assert runners[1].wait(timeout=60) == 143
        assert not [pid for pid in map(int, _lines(second / "pids")) if _alive(pid)]
    finally:
        for process in runners:
            if process.poll() is None:
                process.kill()
                process.wait()
        unrelated.kill()
        unrelated.wait()


# 所有権の取得: 判定は pipe を使わず、exec し直しは runner の (pid, 起動時刻) に結び付けて
# 1 回だけ。大きな環境（pipe の容量を超える）、別の runner から受け継いだ owner の値、
# pipefail のどれでも、起動は「元の 1 回 + exec し直し 1 回」で、fork だけの子も token を持つ。
_LARGE_ENVIRONMENT = {f"EQBENCH_TEST_FILLER_{i}": "x" * 8000 for i in range(96)}  # 約 768KiB
_PIPE_CAPACITY = 64 * 1024


def _inherited_owner():
    """別の（生きている）runner の owner の値: この test の process の pid と起動時刻。"""

    start = Path("/proc/self/stat").read_text().rsplit(")", 1)[1].split()[19]
    return {
        "EQBENCH_PROCESS_OWNER_TOKEN": "0123456789abcdef" * 2,
        "EQBENCH_PROCESS_OWNER_ROOT": str(os.getpid()),
        "EQBENCH_PROCESS_OWNER_ROOT_START": start,
    }


def _claim_script(tmp_path: Path, prologue: str = "") -> Path:
    script = tmp_path / "claim.sh"
    script.write_text(
        f'set -euo pipefail\necho run >> "{tmp_path}/runs"\n{prologue}'
        f'source "{COMMON}"\n'
        'validation_claim_process_ownership "$0" "$@" || { echo claim-failed; exit 1; }\n'
        'echo "args=$*"\n'
        '( p=$BASHPID; tr "\\0" "\\n" < /proc/$p/environ | grep -c "^EQBENCH_PROCESS_OWNER_TOKEN=$EQBENCH_PROCESS_OWNER_TOKEN$" )\n'
        'echo "root=$EQBENCH_PROCESS_OWNER_ROOT self=$$ token=$EQBENCH_PROCESS_OWNER_TOKEN"\n'
        # 前提の測定: 自分の初期環境で、token の行の後に続く bytes 数
        f'"{sys.executable}" -c \'import sys; e = open("/proc/%s/environ" % sys.argv[1], "rb").read(); '
        'print("after_token=%d" % (len(e) - e.find(b"EQBENCH_PROCESS_OWNER_TOKEN=")))\' $$\n',
        encoding="utf-8",
    )
    return script


@pytest.mark.parametrize("large", (False, True), ids=("normal-env", "large-env"))
@pytest.mark.parametrize("inherited", (False, True), ids=("no-owner", "inherited-owner"))
def test_the_runner_reexecutes_itself_once_so_fork_only_children_carry_the_owner(
    tmp_path, large, inherited,
):
    """所有権の取得の前提: exec を経ない fork の子も、自分の environ に token を持つ。"""

    # 受け継いだ owner の値は環境の先頭に置く（exec し直しても同じ位置で置き換わるので、
    # 一致する行の後に大きな環境が続く: pipe で読むと読み手が先に終わる配置）。
    env = dict(_inherited_owner()) if inherited else {}
    if large:
        env.update(_LARGE_ENVIRONMENT)
    env.update((k, v) for k, v in os.environ.items() if not k.startswith("EQBENCH_PROCESS_OWNER"))
    result = subprocess.run(
        ["bash", str(_claim_script(tmp_path)), "one", "two words"], capture_output=True,
        text=True, timeout=60, cwd=REPO_ROOT, env=env,
    )
    assert result.returncode == 0, result.stderr
    lines = result.stdout.splitlines()
    assert lines[0] == "args=one two words", result.stderr
    assert lines[1] == "1"
    root, self_pid, token = lines[2].split()
    assert root.split("=")[1] == self_pid.split("=")[1]
    assert token.split("=")[1] != _inherited_owner()["EQBENCH_PROCESS_OWNER_TOKEN"]
    if large and inherited:
        # 前提: token の行の後に pipe の容量を超える環境が続く（pipe で読むと、読み手が一致で
        # 終わった後も書き手が書き続ける配置）。受け継いだ値はその位置で置き換わる。bash は
        # 環境を自分の順に並べ直すので、配置は測って確かめる。
        assert int(lines[3].split("=")[1]) > 2 * _PIPE_CAPACITY, lines[3]
    # 元の起動 1 回 + exec し直し 1 回。
    assert _lines(tmp_path / "runs") == ["run", "run"]


@pytest.mark.parametrize("case", (
    "no-owner", "inherited", "reused-pid", "confirmed", "token-not-initial", "unreadable",
    "malformed-token",
))
def test_the_claim_tells_confirmed_absent_and_unreadable_apart(case):
    """claim の判定（実 process の /proc/<pid>/environ）: exec し直すのは、この pid と起動時刻の
    owner の値が無いときだけ。値があるのに token を確かめられない（無い・読めない・形が違う）
    ときは、exec し直さずに失敗する。"""

    from scripts.eqbench import runner_processes as rp

    token = "e" * 32
    env = _owner_free_env()
    if case in ("confirmed", "unreadable"):
        env[rp.OWNER_TOKEN_ENV] = token
    actor = _Actor(env) if case == "unreadable" else None
    # exec の途中（Popen が戻った直後）は environ が空に読めるので、走り出したのを待ってから読む
    process = actor.process if actor else subprocess.Popen(
        [sys.executable, "-c", "import time; print('ready', flush=True); time.sleep(60)"],
        env=env, stdout=subprocess.PIPE, text=True,
    )
    if not actor:
        assert process.stdout.readline().strip() == "ready"
    try:
        pid = actor.pid if actor else process.pid
        start = rp._stat(pid)[2]
        own = {rp.OWNER_TOKEN_ENV: token, rp.OWNER_ROOT_ENV: str(pid),
               rp.OWNER_ROOT_START_ENV: str(start)}
        environment = {
            "no-owner": {},
            "inherited": {**own, rp.OWNER_ROOT_ENV: str(os.getpid())},
            "reused-pid": {**own, rp.OWNER_ROOT_START_ENV: str(start - 1)},
            "malformed-token": {**own, rp.OWNER_TOKEN_ENV: "not-a-token"},
        }.get(case, own)
        if case in ("no-owner", "inherited", "reused-pid"):
            new_token, new_start = rp.claim(pid, environment)
            assert re.fullmatch(r"[0-9a-f]{32}", new_token) and new_token != token
            assert new_start == start
        elif case == "confirmed":
            assert rp.claim(pid, environment) is None
        else:
            with pytest.raises(rp.OwnershipError):
                rp.claim(pid, environment)
    finally:
        if actor:
            actor.kill_all()
        else:
            process.kill()
            process.wait()


def test_a_reexecuted_runner_that_cannot_confirm_its_token_fails_without_reexecuting(tmp_path):
    # 自分の (pid, 起動時刻) の owner の値を持って exec された image で、token が初期環境に
    # 無い（export しただけ）。もう一度 exec し直しても直らないので、claim は失敗する。
    prologue = (
        'if [[ -z "${EQBENCH_TEST_SELF_EXEC:-}" ]]; then\n'
        '    start=$(cut -d")" -f2 /proc/$$/stat | cut -d" " -f21)\n'
        '    exec env EQBENCH_TEST_SELF_EXEC=1 EQBENCH_PROCESS_OWNER_ROOT=$$ '
        'EQBENCH_PROCESS_OWNER_ROOT_START="$start" bash "$0" "$@"\n'
        'fi\n'
        'export EQBENCH_PROCESS_OWNER_TOKEN=' + "ab" * 16 + '\n'
    )
    env = {k: v for k, v in os.environ.items() if not k.startswith("EQBENCH_PROCESS_OWNER")}
    env.update(_LARGE_ENVIRONMENT)
    result = subprocess.run(
        ["bash", str(_claim_script(tmp_path, prologue))], capture_output=True, text=True,
        timeout=60, cwd=REPO_ROOT, env=env,
    )
    assert result.returncode == 1 and result.stdout.strip() == "claim-failed", result
    assert "ownership claim failed" in result.stderr
    assert _lines(tmp_path / "runs") == ["run", "run"]


def test_ownership_excludes_the_caller_and_its_ancestors(tmp_path):
    from scripts.eqbench import runner_processes as rp

    token = "f" * 32
    env = {**os.environ, rp.OWNER_TOKEN_ENV: token}
    sleeper = subprocess.Popen(["sleep", "30"], env=env)
    try:
        owned = rp.owned_processes(token, os.getpid())
        assert sleeper.pid in owned
        assert os.getpid() not in owned
        result = rp.stop(token, os.getpid(), wait_seconds=10)
        assert result.verdict is rp.StopVerdict.CONFIRMED and result.problems == {}
        sleeper.wait(timeout=10)
        assert sleeper.returncode == -signal.SIGKILL
    finally:
        if sleeper.poll() is None:
            sleeper.kill()
            sleeper.wait()


# 停止の確認の規則（順序を制御）: 最新の走査だけで判定し、所有している process も確かめ
# られない process も 2 回続けて見えないときだけ成功。確認の途中の出現・消滅・親から子への
# 交代・可読性の変化・期限を、走査の間の決まった同期点で起こす（sleep の調整に頼らない）。
# root は別の process（test の process の子孫を所有に含めないため）。

_ACTOR = """import ctypes, os, sys, time
libc = ctypes.CDLL(None)
libc.prctl(4, 0, 0, 0, 0)  # non-dumpable: /proc/<pid>/environ を他から読めない
print("ready", os.getpid(), flush=True)
for line in sys.stdin:
    command = line.strip()
    if command == "fork":
        if os.fork() == 0:
            print("child", os.getpid(), flush=True)
            sys.stdout.close()
            time.sleep(60)
            os._exit(0)
        os._exit(0)
    if command == "readable":
        libc.prctl(4, 1, 0, 0, 0)
        print("readable", flush=True)
    if command == "exit":
        os._exit(0)
time.sleep(60)
"""


class _Actor:
    """non-dumpable な process。stdin の命令で fork して終わる / 読めるようになる / 終わる。"""

    def __init__(self, env=None):
        self.process = subprocess.Popen(
            [sys.executable, "-c", _ACTOR], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            text=True, env=env,
        )
        word, pid = self.process.stdout.readline().split()
        assert word == "ready"
        self.pid = int(pid)
        self.others = []

    def command(self, command):
        self.process.stdin.write(command + "\n")
        self.process.stdin.flush()

    def fork_and_exit(self):
        self.command("fork")
        word, pid = self.process.stdout.readline().split()
        assert word == "child"
        self.others.append(int(pid))
        self.process.wait(timeout=30)
        return int(pid)

    def kill_all(self):
        for pid in [self.pid, *self.others]:
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        self.process.wait(timeout=30)


def _stop_with_step(monkeypatch, token, root, *, when, act, **kwargs):
    """``stop`` の走査のうち、``when(n, 結果)`` が真になった走査の直後（次の走査の前）に
    ``act`` を 1 回だけ起こす。``act`` が起きたかどうかも返す。"""

    from scripts.eqbench import runner_processes as rp

    real = rp.scan
    state = {"calls": 0, "armed": False, "acted": False}

    def scan(*args, **kw):
        if state["armed"] and not state["acted"]:
            state["acted"] = True
            act()
        result = real(*args, **kw)
        state["calls"] += 1
        if not state["acted"] and when(state["calls"], result):
            state["armed"] = True
        return result

    monkeypatch.setattr(rp, "scan", scan)
    return rp.stop(token, root, **kwargs), state["acted"]


@pytest.fixture
def stop_world():
    """root（別の process）と、root の後に起動した無関係な process（対照）。"""

    root = subprocess.Popen(["sleep", "120"])
    time.sleep(0.02)  # 起動時刻（clock tick）を root より後にする
    # 走り出したのを待つ（exec の途中は environ が空に読め、確かめられない process に見える）
    unrelated = subprocess.Popen(
        [sys.executable, "-c", "import time; print('ready', flush=True); time.sleep(120)"],
        stdout=subprocess.PIPE, text=True,
    )
    assert unrelated.stdout.readline().strip() == "ready"
    actors = []
    yield root, unrelated, actors
    for actor in actors:
        actor.kill_all()
    for process in (root, unrelated):
        process.kill()
        process.wait()


_TOKEN_UNDER_TEST = "c" * 32
_CONFIRMED = StopVerdict.CONFIRMED
_UNREADABLE = "process of this user whose ownership could not be read"


def _owner_free_env():
    return {k: v for k, v in os.environ.items() if not k.startswith("EQBENCH_PROCESS_OWNER")}


def test_a_child_left_by_an_exiting_unverifiable_parent_keeps_the_stop_unconfirmed(
    monkeypatch, stop_world,
):
    root, unrelated, actors = stop_world
    parent = _Actor(_owner_free_env())
    actors.append(parent)
    children = []
    seen = []

    def parent_seen_three_times(n, result):
        # 確認の走査の途中で交代させる（最初の観測の直後ではなく、何度か見た後）
        if parent.pid in result[1]:
            seen.append(n)
        return len(seen) >= 3

    result, acted = _stop_with_step(
        monkeypatch, _TOKEN_UNDER_TEST, root.pid,
        when=parent_seen_three_times, act=lambda: children.append(parent.fork_and_exit()),
    )
    assert acted
    # 親は消えたが、残った子は確かめられない: 成功にしない。子には signal を送らない。
    assert result.verdict is not _CONFIRMED and result.problems == {children[0]: _UNREADABLE}
    assert _alive(children[0]) and unrelated.poll() is None and root.poll() is None


def test_an_unverifiable_process_that_appears_after_a_clean_scan_keeps_the_stop_unconfirmed(
    monkeypatch, stop_world,
):
    root, unrelated, actors = stop_world
    result, acted = _stop_with_step(
        monkeypatch, _TOKEN_UNDER_TEST, root.pid,
        when=lambda n, result: n >= 2 and not result[0] and not result[1],
        act=lambda: actors.append(_Actor(_owner_free_env())),
    )
    assert acted
    assert result.verdict is not _CONFIRMED and result.problems == {actors[0].pid: _UNREADABLE}
    assert _alive(actors[0].pid) and unrelated.poll() is None


def test_an_unverifiable_process_that_becomes_readable_as_owned_is_killed(
    monkeypatch, stop_world,
):
    root, unrelated, actors = stop_world
    owned = _Actor({**_owner_free_env(), "EQBENCH_PROCESS_OWNER_TOKEN": _TOKEN_UNDER_TEST})
    actors.append(owned)

    def become_readable():
        owned.command("readable")
        assert owned.process.stdout.readline().strip() == "readable"

    result, acted = _stop_with_step(
        monkeypatch, _TOKEN_UNDER_TEST, root.pid,
        when=lambda n, result: owned.pid in result[1], act=become_readable,
    )
    assert acted
    # 読めるようになって所有と分かった process は止め、消えたのを確かめてから成功する。
    assert result.verdict is _CONFIRMED and result.problems == {}
    assert owned.process.wait(timeout=30) == -signal.SIGKILL
    assert unrelated.poll() is None and root.poll() is None


def test_an_unverifiable_process_that_exits_lets_the_stop_succeed(monkeypatch, stop_world):
    root, unrelated, actors = stop_world
    actor = _Actor(_owner_free_env())
    actors.append(actor)

    def leave():
        actor.command("exit")
        actor.process.wait(timeout=30)

    result, acted = _stop_with_step(
        monkeypatch, _TOKEN_UNDER_TEST, root.pid,
        when=lambda n, result: actor.pid in result[1], act=leave,
    )
    assert acted and result.verdict is _CONFIRMED and result.problems == {}
    assert unrelated.poll() is None and root.poll() is None


@pytest.mark.parametrize(("wait_seconds", "settle_seconds", "verdict"), (
    (0.3, 60.0, "DEADLINE"), (60.0, 0.3, "UNVERIFIABLE"),
), ids=("deadline", "settle"))
def test_an_unverifiable_process_that_stays_fails_the_stop_at_its_deadline(
    stop_world, wait_seconds, settle_seconds, verdict,
):
    from scripts.eqbench import runner_processes as rp

    root, unrelated, actors = stop_world
    actors.append(_Actor(_owner_free_env()))
    started = time.monotonic()
    result = rp.stop(
        _TOKEN_UNDER_TEST, root.pid, wait_seconds=wait_seconds, settle_seconds=settle_seconds,
    )
    assert result.verdict.value == verdict and result.problems == {actors[0].pid: _UNREADABLE}
    assert time.monotonic() - started < 30
    assert _alive(actors[0].pid) and unrelated.poll() is None


# 停止の成功・期限・戻り値の境界（時計と走査の順序を制御）。成功は「期限より前に終わった
# 走査が CLEAN_SCANS 回続けて何も示さない」ときだけ。期限は毎回の走査の後に先に調べ、期限の
# 時刻ちょうど以後に終わった走査は数えない。成否は verdict だけが決め、problems（最新の走査が
# 示したもの）は診断で、空でも成功を意味しない。CLI は CONFIRMED のときだけ 0 を返す。

_GHOST, _GHOST2 = 2 ** 22 + 11, 2 ** 22 + 13  # 存在しない pid（signal は送られない）


class _ScriptedStop:
    """``stop`` の時計と走査を台本どおりに進める。台本の各段は (所要秒, owned, unverifiable)。
    最初の段は凍結の走査。``sleep`` は時計を進めるだけ。"""

    def __init__(self, monkeypatch, steps, *, poll=0.02):
        from scripts.eqbench import runner_processes as rp

        self.now = 1000.0
        self.steps = list(steps)
        self.scans = 0
        test = self

        class Clock:
            @staticmethod
            def monotonic():
                return test.now

            @staticmethod
            def sleep(seconds):
                test.now += seconds

        def scan(token, root, exclude=()):
            if not test.steps:
                raise AssertionError("stop scanned more often than the script allows")
            duration, owned, unverifiable = test.steps.pop(0)
            test.now += duration
            test.scans += 1
            return dict(owned), dict(unverifiable)

        monkeypatch.setattr(rp, "time", Clock)
        monkeypatch.setattr(rp, "scan", scan)
        monkeypatch.setattr(rp, "_POLL_SECONDS", poll)


_FREEZE = (0.0, {}, {})
_CLEAN = (0.0, {}, {})


def _scan_at(seconds, owned=None, unverifiable=None):
    return (seconds, owned or {}, unverifiable or {})


# 期限は呼び出しから 60 秒（stop の既定）。各ケース: 台本、期待する verdict、problems、clean_scans
_BOUNDARY_CASES = {
    # 1. 最初の空の走査が期限ちょうど / 期限の後に終わる
    "first-clean-scan-ends-at-deadline": ([_FREEZE, _scan_at(60.0)], "DEADLINE", {}, 0),
    "first-clean-scan-ends-after-deadline": ([_FREEZE, _scan_at(75.0)], "DEADLINE", {}, 0),
    # 2. 1 回目は期限内、2 回目の前（待ちの間）または 2 回目の走査中に期限
    "deadline-before-second-scan": (
        [_FREEZE, _scan_at(59.99), _scan_at(0.0)], "DEADLINE", {}, 1),
    "second-clean-scan-ends-at-deadline": (
        [_FREEZE, _scan_at(30.0), _scan_at(29.98)], "DEADLINE", {}, 1),
    "freeze-outlasts-deadline": ([_scan_at(61.0), _CLEAN], "DEADLINE", {}, 0),
    # 3. 必要な回数の空の走査が期限内に終わる（境界の直前を含む）
    "two-clean-scans-in-time": ([_FREEZE, _CLEAN, _CLEAN], "CONFIRMED", {}, 2),
    "second-clean-scan-just-before-deadline": (
        [_FREEZE, _scan_at(30.0), _scan_at(29.97)], "CONFIRMED", {}, 2),
    # 4. 所有 process / 確かめられない process が残ったまま期限
    "owned-survives-to-deadline": (
        [_FREEZE] + [_scan_at(20.0, owned={_GHOST: 1})] * 3, "DEADLINE",
        {_GHOST: "owned process still alive after the stop"}, 0),
    "unverifiable-stays-to-deadline": (
        [_FREEZE] + [_scan_at(20.0, unverifiable={_GHOST: 1})] * 3, "DEADLINE",
        {_GHOST: "process of this user whose ownership could not be read"}, 0),
    # 5. 確認の途中の出現・交代・可読性の変化は、数えた空の走査をやり直させ、期限を迂回しない
    "appears-after-a-clean-scan-then-deadline": (
        [_FREEZE, _CLEAN, _scan_at(1.0, unverifiable={_GHOST: 1}), _scan_at(1.0),
         _scan_at(58.0)], "DEADLINE", {}, 1),
    "replaced-by-a-child-then-deadline": (
        [_FREEZE, _scan_at(1.0, unverifiable={_GHOST: 1}), _scan_at(1.0, unverifiable={_GHOST2: 2}),
         _scan_at(58.0)], "DEADLINE", {}, 0),
    "becomes-owned-then-confirmed-in-time": (
        [_FREEZE, _scan_at(1.0, unverifiable={_GHOST: 1}), _scan_at(1.0, owned={_GHOST: 1}),
         _CLEAN, _CLEAN], "CONFIRMED", {}, 2),
    "becomes-owned-then-deadline": (
        [_FREEZE, _scan_at(1.0, unverifiable={_GHOST: 1}), _scan_at(1.0, owned={_GHOST: 1}),
         _CLEAN, _scan_at(58.0)], "DEADLINE", {}, 1),
}


@pytest.mark.parametrize("case", sorted(_BOUNDARY_CASES))
def test_the_stop_succeeds_only_after_enough_clean_scans_before_its_deadline(monkeypatch, case):
    from scripts.eqbench import runner_processes as rp

    steps, verdict, problems, clean = _BOUNDARY_CASES[case]
    script = _ScriptedStop(monkeypatch, steps)
    result = rp.stop("a" * 32, os.getpid(), settle_seconds=10 ** 6)
    assert (result.verdict.value, dict(result.problems), result.clean_scans) == (
        verdict, problems, clean)
    assert result.confirmed is (verdict == "CONFIRMED")
    assert not script.steps  # 台本を使い切った（決着の後に走査しない・決着より前に止まらない）


@pytest.mark.parametrize("case", sorted(_BOUNDARY_CASES))
def test_the_stop_command_exits_zero_only_for_a_confirmed_stop(monkeypatch, capsys, case):
    from scripts.eqbench import runner_processes as rp

    steps, verdict, _problems, _clean = _BOUNDARY_CASES[case]
    # CLI と同じ既定（確かめられない process の連続観測 1 秒を含む）での stop の結果
    _ScriptedStop(monkeypatch, steps)
    expected = rp.stop("a" * 32, os.getpid())
    assert (expected.verdict.value == "CONFIRMED") is (verdict == "CONFIRMED")
    _ScriptedStop(monkeypatch, steps)
    code = rp.main(["stop", "--token", "a" * 32, "--root", str(os.getpid())])
    err = capsys.readouterr().err
    if expected.confirmed:
        assert code == 0 and err == ""
    else:
        assert code == 1 and f"not confirmed ({expected.verdict.value};" in err
        # 診断は最新の走査が示したものだけ（存在しない残存 process を作らない）
        assert err.count("runner_processes: pid ") == len(expected.problems)


def test_unverifiable_processes_seen_without_a_break_end_the_stop(monkeypatch):
    from scripts.eqbench import runner_processes as rp

    seen = _scan_at(0.4, unverifiable={_GHOST: 1})
    _ScriptedStop(monkeypatch, [_FREEZE, seen, seen, seen, seen])
    result = rp.stop("a" * 32, os.getpid(), settle_seconds=1.0)
    assert result.verdict is rp.StopVerdict.UNVERIFIABLE
    assert dict(result.problems) == {_GHOST: "process of this user whose ownership could not be read"}


# 実 runner の handler を通す: stop の CLI だけを、時計が読むたびに飛ぶ python で動かす。
# jump=30 秒なら、凍結・SIGKILL は実際に行われるが、2 回目の空の走査の時点で期限（60 秒）に
# 達して未確認になる。jump=0 は対照（同じ stand-in で確認できる）。
_JUMPING_STOP_PYTHON = """#!/bin/bash
if [[ "$1 $2 $3" == "-B -m scripts.eqbench.runner_processes" && "$4" == stop ]]; then
    shift 3
    exec "__PYTHON__" -B -c 'import itertools, sys
from scripts.eqbench import runner_processes as rp
ticks = itertools.count(0.0, __JUMP__)
class Clock:
    monotonic = staticmethod(lambda: next(ticks))
    sleep = staticmethod(lambda seconds: None)
rp.time = Clock
sys.exit(rp.main(sys.argv[1:]))' "$@"
fi
exec "__PYTHON__" "$@"
"""


def _jumping_python(tmp_path: Path, jump: float) -> Path:
    path = tmp_path / "jumping-python"
    path.write_text(
        _JUMPING_STOP_PYTHON.replace("__PYTHON__", sys.executable).replace("__JUMP__", repr(jump)),
        encoding="utf-8",
    )
    path.chmod(0o755)
    return path


@_RUNNERS
@pytest.mark.parametrize(("injection", "exit_code"), (
    ("after-registration", 75), ("error-exit", 3), ("normal", 75),
))
def test_a_stop_unconfirmed_by_its_deadline_keeps_the_tmpdir(tmp_path, runner, injection, exit_code):
    """期限までに確認できなかった停止は、最新の走査が空でも失敗: tmp を残し、exit 75（既に
    失敗の exit code なら、それを残す）。止めた pair は分類まで進まない。"""

    result, events, pids = _run_stop_harness(
        tmp_path, runner, injection, child="short" if injection == "normal" else "plain",
        python_bin=_jumping_python(tmp_path, 30.0),
    )
    assert result.returncode == exit_code, (result.returncode, result.stderr)
    assert "not confirmed (DEADLINE;" in result.stderr
    assert "runner_processes: pid " not in result.stderr  # 残存 process を作らない
    assert "tmp-removed" not in events
    assert (tmp_path / "runtmp").is_dir()
    if injection != "normal":
        assert "classified" not in events
        assert not [pid for pid in pids if _alive(pid)]  # 凍結と SIGKILL は実際に行われた


@_RUNNERS
def test_a_stop_confirmed_in_time_removes_the_tmpdir(tmp_path, runner):
    result, events, pids = _run_stop_harness(
        tmp_path, runner, "after-registration", python_bin=_jumping_python(tmp_path, 0.001),
    )
    _assert_stopped_before_removal(tmp_path, result, events, pids, 143)


def test_an_exiting_process_or_kernel_thread_is_never_unverifiable(monkeypatch):
    """終了の途中の process は environ が空に読める。kernel thread には environ が無い。
    どちらも「確かめられない」にしない。走査の後で終了を始めたもの（environ を読んだ後の
    stat に PF_EXITING）と、PID が別の process に再利用されたものも同じ。"""

    from scripts.eqbench import runner_processes as rp

    root, start = 10, 1000
    uid = os.getuid()
    table = {  # pid -> stat の列（呼ばれるたびに次へ。最後のものを繰り返す）
        root: [(1, "S", start, 0)],
        11: [(1, "S", start + 1, 0)],                                   # 読めない: 確かめられない
        12: [(1, "R", start + 1, rp._PF_EXITING)],                      # 終了の途中
        13: [(1, "S", start + 1, 0), (1, "R", start + 1, rp._PF_EXITING)],  # 読んだ後に終了
        14: [(2, "S", 5, rp._PF_KTHREAD)],                               # kernel thread
        15: [(1, "S", start + 1, 0), (1, "S", start + 9, 0)],           # PID の再利用
    }
    calls = {}

    def fake_stat(pid):
        if pid not in table:
            return None
        n = calls.get(pid, 0)
        calls[pid] = n + 1
        return table[pid][min(n, len(table[pid]) - 1)]

    monkeypatch.setattr(rp, "_all_pids", lambda: iter(table))
    monkeypatch.setattr(rp, "_stat", fake_stat)
    monkeypatch.setattr(rp, "_environ", lambda pid: b"" if pid in (12, 13) else None)
    monkeypatch.setattr(rp, "_uid", lambda pid: uid)
    owned, unverifiable = rp.scan("d" * 32, root)
    assert owned == {} and set(unverifiable) == {11}


def test_the_stop_handlers_use_no_shell_arithmetic_on_time_settings():
    # 小数を受理する時間の設定（例: PAIR_PROCESS_KILL_AFTER=0.5s）を shell の整数演算に
    # 渡さない。停止の実挙動は、小数の設定のまま上の harness で確かめている。
    for path in (EQ_RUNNER, NEQ_RUNNER, COMMON, SCHEDULER):
        for line in path.read_text(encoding="utf-8").splitlines():
            if "$((" in line or "(( " in line:
                assert "_SECONDS" not in line and "KILL_AFTER" not in line, (path.name, line)


# ---------------------------------------------------------------------------
# 6. 実行境界: 前回の成果物を消し、消えたことを確かめてから解析を始める
# ---------------------------------------------------------------------------

_ARTIFACTS = (
    "{stem}.pair-status.json", "{stem}.stage.jsonl",
    ".runtime-metrics/{stem}.stack-dump.txt", ".runtime-metrics/{stem}.stack-dump.status.json",
    ".runtime-metrics/{stem}.classification-failure.json",
    ".runtime-metrics/{stem}.progress.json", ".runtime-metrics/{stem}.runtime.json",
    ".{stem}.pair-status.json.partial",
)


def _seed_artifacts(directory: Path, stem: str):
    for template in _ARTIFACTS:
        path = directory / template.format(stem=stem)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("previous execution\n")


def _open(directory: Path, stem: str):
    return subprocess.run(
        ["bash", "-c", f'source "{COMMON}"; validation_open_pair_execution "$1" "$2"',
         "bash", str(directory), stem],
        capture_output=True, text=True, timeout=60,
    )


def test_the_boundary_removes_every_artifact_of_the_previous_execution(tmp_path):
    _seed_artifacts(tmp_path, "f_B1_B2")
    (tmp_path / "f_B1_B2.log").write_text("previous log\n")
    result = _open(tmp_path, "f_B1_B2")
    assert result.returncode == 0, result.stderr
    assert sorted(
        str(p.relative_to(tmp_path)) for p in tmp_path.rglob("*") if p.is_file()
    ) == ["f_B1_B2.log"]


def test_the_boundary_fails_when_an_artifact_cannot_be_removed(tmp_path):
    if os.geteuid() == 0:
        pytest.skip("directory permissions do not bind root")
    _seed_artifacts(tmp_path, "f_B1_B2")
    tmp_path.chmod(0o555)
    try:
        result = _open(tmp_path, "f_B1_B2")
    finally:
        tmp_path.chmod(0o755)
    assert result.returncode != 0
    assert "could not remove" in result.stderr
    assert (tmp_path / "f_B1_B2.pair-status.json").read_text() == "previous execution\n"


_PROBE_LOG = """#!/bin/sh
echo "$*" >> "$PROBE_CALLS"
echo stub
exit 0
"""


@pytest.mark.parametrize("runner", (EQ_RUNNER, NEQ_RUNNER), ids=("eq", "neq"))
def test_run_pair_starts_no_analysis_when_the_boundary_cannot_be_opened(tmp_path, runner):
    if os.geteuid() == 0:
        pytest.skip("directory permissions do not bind root")
    out = tmp_path / "out" / "sample" / "f"
    out.mkdir(parents=True)
    (tmp_path / "runtmp").mkdir()
    stem = "f_B1_B2" if runner == EQ_RUNNER else "f_N_B1_O_B2"
    (out / f"{stem}.pair-status.json").write_text('{"note": "previous-execution"}\n')
    probe = tmp_path / "python-probe"
    probe.write_text(_PROBE_LOG)
    probe.chmod(0o755)
    function = _extract_shell_function(runner.read_text(encoding="utf-8"), "run_pair")
    if runner == EQ_RUNNER:
        args = f'"sample" "f" "B1" "B2" "/left" "/right" "{out}" 1 1 "/target"'
    else:
        args = f'"sample" "f" "N_B1" "O_B2" "/left" "/right" "{out}" 1 1 "/target" 1 1 1'
    script = (
        _BOUNDARY_HARNESS.replace("__COMMON__", str(COMMON))
        .replace("__TMP__", str(tmp_path)).replace("__FUNCTION__", function)
        .replace("run_pair __ARGS__ || true", f"run_pair {args}; echo rc=$?")
    )
    out.chmod(0o555)
    try:
        result = subprocess.run(
            ["bash", "-c", script], capture_output=True, text=True, timeout=120,
            env={**os.environ, "PROBE_CALLS": str(tmp_path / "calls")},
        )
    finally:
        out.chmod(0o755)
    assert "BOUNDARY_FAILED" in result.stdout
    assert "rc=1" in result.stdout
    assert not (tmp_path / "calls").exists()  # 解析（python の呼び出し）は 1 つも始まらない
    assert (out / f"{stem}.pair-status.json").read_text() == '{"note": "previous-execution"}\n'


# ---------------------------------------------------------------------------
# 7. 結果の確定: この execution が公開した、署名・target・終端・nonce の揃った status だけ
# ---------------------------------------------------------------------------

_NONCE = "a1b2c3d4e5f60718293a4b5c"
_DISPATCH = """#!/bin/bash
# python の stand-in: 結果の確定（pair_status_authority）だけ本物を使う。
args="$*"
case "$args" in
  *"import secrets"*) echo 0123456789abcdef0123456789abcdef0123456789abcdef; exit 0 ;;
  *production_cutover*) printf 'production-pilot-%s\\tfingerprint\\tstream\\n' "$NONCE"; exit 0 ;;
  *canonical_result*)
    while [ $# -gt 0 ]; do
      case "$1" in
        --pair-status-output) out="$2"; shift ;;
        --classification-failure-output) record="$2"; shift ;;
      esac
      shift
    done
    case "$SCENARIO" in
      stale-status) cp "$STALE_STATUS" "$out"; exit 0 ;;
      decided-error) cp "$DECIDED_STATUS" "$out"; exit 1 ;;
      diagnostic) cp "$DIAGNOSTIC" "$out"; cp "$RECORD" "$record"; exit 2 ;;
      publication-failed) exit 3 ;;
    esac ;;
  *pair_status_authority*) exec "$REAL_PYTHON" "$@" ;;
esac
exit 0
"""


def _signed(tree: Path, outcome: str, *, nonce: str, supervisor_status="RESOLVED"):
    from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
        PAIR_STATUS_PUBLIC_KEY_FILE,
    )
    private_key, public_key = tree / "pair-status.key", tree / PAIR_STATUS_PUBLIC_KEY_FILE
    if not public_key.is_file():
        generate_pair_status_keypair(private_key, public_key)
    body = _status_body("sample", "f", "B1", "B2", outcome, supervisor_status)
    body["execution_nonce"] = nonce
    return seal_pair_status(body, private_key_path=private_key, public_key_path=public_key)


def _run_pair_with_classifier(tmp_path, runner, scenario):
    keys = tmp_path / "keys"
    keys.mkdir()
    stale = tmp_path / "stale.json"
    stale.write_text(json.dumps(_signed(keys, "NOT_EQ", nonce="previous-execution-nonce")))
    decided = tmp_path / "decided.json"
    decided.write_text(json.dumps(_signed(keys, "ERROR", nonce=_NONCE)))
    diagnostic = tmp_path / "diagnostic.json"
    diagnostic.write_text(json.dumps(OPERATIONAL_DIAGNOSTIC))
    record = tmp_path / "record.json"
    _write_failure_record(record, -9)
    target = tmp_path / "target.json"
    target.write_text(json.dumps(
        _status_body("sample", "f", "B1", "B2", "UNKNOWN", "RESOLVED")["pair_execution_target"]
    ))
    out = tmp_path / "out" / "sample" / "f"
    out.mkdir(parents=True)
    (tmp_path / "runtmp").mkdir()
    dispatch = tmp_path / "python-probe"
    dispatch.write_text(_DISPATCH)
    dispatch.chmod(0o755)
    public_key = keys / "pair-status-verification-key.json"
    function = _extract_shell_function(runner.read_text(encoding="utf-8"), "run_pair")
    if runner == EQ_RUNNER:
        args = f'"sample" "f" "B1" "B2" "/left" "/right" "{out}" 1 1 "{target}"'
        stem = "f_B1_B2"
    else:
        args = f'"sample" "f" "N_B1" "O_B2" "/left" "/right" "{out}" 1 1 "{target}" 1 1 1'
        stem = "f_N_B1_O_B2"
    script = (
        _BOUNDARY_HARNESS.replace("__COMMON__", str(COMMON))
        .replace("__TMP__", str(tmp_path)).replace("__FUNCTION__", function)
        .replace("PAIR_STATUS_VERIFICATION_KEY_FILE=/dev/null", f"PAIR_STATUS_VERIFICATION_KEY_FILE={public_key}")
        .replace("PAIR_PUBLIC_KEY=/dev/null", f"PAIR_PUBLIC_KEY={public_key}")
        .replace("run_pair __ARGS__ || true", f"run_pair {args}; echo rc=$?")
    )
    result = subprocess.run(
        ["bash", "-c", script], capture_output=True, text=True, timeout=120, cwd=REPO_ROOT,
        env={**os.environ, "SCENARIO": scenario, "NONCE": _NONCE, "REAL_PYTHON": sys.executable,
             "STALE_STATUS": str(stale), "DECIDED_STATUS": str(decided),
             "DIAGNOSTIC": str(diagnostic), "RECORD": str(record),
             "PYTHONPATH": str(REPO_ROOT)},
    )
    line = next(
        (line for line in result.stdout.splitlines() if "<->" in line), "",
    )
    rc = int(result.stdout.rsplit("rc=", 1)[1].split()[0])
    return line, rc, out / f"{stem}.pair-status.json", result


@pytest.mark.parametrize("runner", (EQ_RUNNER, NEQ_RUNNER), ids=("eq", "neq"))
@pytest.mark.parametrize(("scenario", "state", "eq_rc", "neq_rc"), (
    # 有効に署名された同じ target の status でも、この execution のものでなければ未完了。
    ("stale-status", "INCOMPLETE", 3, 1),
    # 公開に失敗した（status が無い）。
    ("publication-failed", "INCOMPLETE", 3, 1),
    # 分類に失敗した（署名の無い診断）。rc は分類器の record から。
    ("diagnostic", "INCOMPLETE", 2, 1),
    # この execution の確定した ERROR は確定（Eq は既存の policy で pair job の失敗）。
    ("decided-error", "ERROR", 1, 0),
))
def test_run_pair_accepts_only_this_executions_decided_status(
    tmp_path, runner, scenario, state, eq_rc, neq_rc,
):
    line, rc, status, result = _run_pair_with_classifier(tmp_path, runner, scenario)
    assert f": {state}" in line, (line, result.stderr)
    assert rc == (eq_rc if runner == EQ_RUNNER else neq_rc), (line, result.stderr)
    if scenario == "diagnostic" and runner == EQ_RUNNER:
        assert "child_exit=-9" in line


# ---------------------------------------------------------------------------
# 8. 本物の supervisor から公開・確定・再開まで: 確定した ERROR / 期限の TIMEOUT / UNKNOWN は
#    再利用され、止められた pair は未完了で再試行される
# ---------------------------------------------------------------------------


def _publish_and_resume(tmp_path, case, classified):
    keys = tmp_path / "pair-keys"
    keys.mkdir()
    private_key = keys / "pair-status.key"
    public_key = keys / "pair-status-verification-key.json"
    generate_pair_status_keypair(private_key, public_key)
    target = _status_body("sample", "f", "B1", "B2", "UNKNOWN", "RESOLVED")[
        "pair_execution_target"]
    target_path = tmp_path / "target.json"
    target_path.write_text(json.dumps(target))
    status = tmp_path / "f_B1_B2.pair-status.json"
    write_pair_status_file(status, seal_pair_status(
        {**classified, "pair_execution_target": target},
        private_key_path=private_key, public_key_path=public_key,
    ))
    (tmp_path / "f_B1_B2.log").write_text("pair log\n")
    resolved = resolve_pair_execution(
        status, expected_pair_target_path=target_path, public_key_path=public_key,
        execution_nonce=case.config.execution_nonce,
    )
    skip = pair_status_file_skip_decision(
        status, log_path=tmp_path / "f_B1_B2.log", public_key_path=public_key,
        expected_pair_target_path=target_path, mode="NORMAL_RESUME",
    )
    return resolved, skip


def test_a_durable_error_is_decided_and_reused(tmp_path):
    with supervisor_case(tmp_path / "case", ChildScript((Exit(3),))) as case:
        run = run_supervisor(case)
        resolved, skip = _publish_and_resume(tmp_path, case, classify(run))
    assert resolved[0] == "ERROR" and resolved[3] is None
    assert skip == "SKIP"


def test_a_deadline_timeout_is_decided_and_reused(tmp_path):
    with supervisor_case(
        tmp_path / "case", ChildScript((Stop(),)), kill_grace=30.0,
    ) as case:
        run = run_supervisor(case, deadline=Deadline.AT_CHILD_STOP)
        assert run.projection["status"] == "TIMEOUT"
        resolved, skip = _publish_and_resume(tmp_path, case, classify(run))
    assert resolved[0] == "TIMEOUT" and resolved[3] is None
    assert skip == "SKIP"


def test_a_canonical_unknown_is_decided_and_reused(tmp_path):
    script = ChildScript((Checkpoint(), Envelope("UNKNOWN"), Exit()))
    with supervisor_case(tmp_path / "case", script, allow_child_exit_resolution=True) as case:
        run = run_supervisor(case)
        resolved, skip = _publish_and_resume(tmp_path, case, classify(run))
    assert resolved[0] == "UNKNOWN" and resolved[3] is None
    assert skip == "SKIP"


def test_an_interrupted_pair_is_incomplete_and_retried(tmp_path):
    marker = tmp_path / "child.pid"
    child = (
        sys.executable, "-c",
        "import os, sys, time; open(sys.argv[1], 'w').write(str(os.getpid())); time.sleep(120)",
        str(marker),
    )
    keys = tmp_path / "pair-keys"
    keys.mkdir()
    generate_pair_status_keypair(keys / "pair-status.key", keys / "pair-status-verification-key.json")
    target_path = tmp_path / "target.json"
    target_path.write_text(json.dumps(
        _status_body("sample", "f", "B1", "B2", "UNKNOWN", "RESOLVED")["pair_execution_target"]))
    with supervisor_case(tmp_path / "case", child, allow_child_exit_resolution=True) as case:
        process = subprocess.Popen(_supervisor_argv(case.config), cwd=REPO_ROOT,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        assert _wait_for(lambda: marker.is_file() and marker.read_text().strip())
        process.send_signal(signal.SIGTERM)
        assert process.wait(timeout=30) == 143
        config = case.config
        status = tmp_path / "f_B1_B2.pair-status.json"
        log = tmp_path / "f_B1_B2.log"
        log.write_text("pair log\n")
        code = canonical_result_main([
            "--classify-pair-log", str(log),
            "--supervisor-projection", str(config.authority_output),
            "--checkpoint-root", str(config.checkpoint_root),
            "--execution-nonce", config.execution_nonce,
            "--supervisor-signing-key-id", config.supervisor_signing_key_id,
            "--supervisor-signing-key-file", str(config.supervisor_signing_key_file),
            "--worker-signing-key-id", config.worker_signing_key_id,
            "--worker-signing-key-file", str(config.worker_signing_key_file),
            "--pair-status-signing-private-key-file", str(keys / "pair-status.key"),
            "--pair-status-verification-key-file", str(keys / "pair-status-verification-key.json"),
            "--pair-execution-target-file", str(target_path),
            "--pair-status-output", str(status),
        ])
    assert code == 2
    resolved = resolve_pair_execution(
        status, expected_pair_target_path=target_path,
        public_key_path=keys / "pair-status-verification-key.json",
        execution_nonce=config.execution_nonce,
    )
    assert resolved[0] == "INCOMPLETE" and resolved[3] is not None
    assert pair_status_file_skip_decision(
        status, log_path=log, public_key_path=keys / "pair-status-verification-key.json",
        expected_pair_target_path=target_path, mode="NORMAL_RESUME",
    ) == "SCHEDULE"


# ---------------------------------------------------------------------------
# 9. 実行記録は atomic に置き換える / 追記する
# ---------------------------------------------------------------------------


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
    result = _common(
        f'validation_install_file_atomically "{candidate}" "{tmp_path}/missing/run_manifest.txt"',
        tmp_path,
    )
    assert result.returncode != 0
    assert manifest.read_text() == "run_kind=x\nend=1\n"


def test_the_runners_go_through_the_shared_lifecycle_helpers():
    # 2 本の runner が同じ owner を呼ぶことの静的な裏付け（実挙動は上の各 test）。
    for runner in (EQ_RUNNER, NEQ_RUNNER):
        source = runner.read_text(encoding="utf-8")
        run_pair = _extract_shell_function(source, "run_pair")
        assert source.count("validation_claim_process_ownership") == 1
        assert "pair_scheduler_launch_job" in source and "pair_scheduler_start_job" not in source
        calls = [line for line in run_pair.splitlines() if not line.strip().startswith("#")]
        assert sum("validation_open_pair_execution " in line for line in calls) == 1
        assert sum("validation_resolve_pair_execution " in line for line in calls) == 1
        assert "--pair-status-output" in run_pair
        for line in source.splitlines():
            stripped = line.strip()
            for target in ('"$RUN_MANIFEST_FILE"', '"$RUN_MANIFEST"',
                           '"$OUTPUT_BASE_DIR/run_manifest.txt"'):
                assert f"> {target}" not in stripped, (runner.name, line)


# ---------------------------------------------------------------------------
# 10. 所有権の前提: supervisor の子（解析の child）も owner token を受け継ぐ。読めない /proc は
#     「対象なし」ではなく停止の失敗になる。
# ---------------------------------------------------------------------------


def test_the_supervisor_passes_the_owner_token_to_its_child(tmp_path):
    marker = tmp_path / "child-environ"
    child = (
        sys.executable, "-c",
        "import sys\n"
        "env = open('/proc/self/environ', 'rb').read().split(b'\\0')\n"
        "open(sys.argv[1], 'w').write(str(sum(e.startswith(b'EQBENCH_PROCESS_OWNER_TOKEN=abcd') for e in env)))",
        str(marker),
    )
    with supervisor_case(tmp_path / "case", child, allow_child_exit_resolution=True) as case:
        subprocess.run(
            _supervisor_argv(case.config), cwd=REPO_ROOT, capture_output=True, timeout=60,
            env={**os.environ, "EQBENCH_PROCESS_OWNER_TOKEN": "abcd" * 8},
        )
    assert marker.read_text() == "1"


def test_a_stop_that_cannot_read_the_process_table_fails(tmp_path):
    from scripts.eqbench import runner_processes as rp

    dead = subprocess.Popen(["true"])
    dead.wait()
    with pytest.raises(ValueError):
        rp.stop("f" * 32, dead.pid)
    result = subprocess.run(
        [sys.executable, "-m", "scripts.eqbench.runner_processes", "stop",
         "--token", "f" * 32, "--root", str(dead.pid)],
        capture_output=True, text=True, cwd=REPO_ROOT, timeout=60,
    )
    assert result.returncode == 1 and "could not be carried out" in result.stderr
