# -*- coding: utf-8 -*-
"""Issue #204: the supervisor's diagnostic signal must not end a child that already has its result.

Mechanism (reproduced with this file on main before the fix, see the PR): a child that
has written its canonical result is still finishing when the supervisor's stack-dump
lead window opens (deadline - lead).  The supervisor sends SIGUSR1 because the child's
journal says the faulthandler handler was registered.  During interpreter finalization
CPython unloads faulthandler (``_PyFaulthandler_Fini``), which restores the disposition
SIGUSR1 had before the registration.  When that is the default (terminate), the signal
kills the child (rc -10), the exit code no longer joins the canonical outcome's CLI
code, and the terminal rule refuses the result: INVALID
(``CANONICAL_CHILD_RESULT_INVALID``), recorded by the runner as
``PAIR_STATUS_AUTHORITY_INVALID``.

Contract after the fix:

* the child (``cli.pair_diagnostics``) sets SIGUSR1 to "ignore" before registering, so
  the disposition restored at the unload ignores the signal, and declares it in the
  readiness record (``disposition_after_unregister``);
* the supervisor (``authority.process.stack_dump_diagnostic``) sends only to a child
  that declares it.

The waits are on events only: the child blocked in ``pause`` (section 1), or the child
blocking SIGUSR1 and waiting until the supervisor's signal is pending (section 2), so the
order "signal sent, then delivered after the unload" holds by construction, not by timing.
"""
from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.process import store_layout as layout
from scripts.function_tracer_pcode.tests.unit._supervisor_child import (
    AFTER_SIGNAL_EXIT,
    AFTER_SIGNAL_STAY,
    REGISTRATION_DECLARATION_DOES_NOT_HOLD,
    REGISTRATION_PRODUCTION,
    AwaitDiagnosticSignal,
    Checkpoint,
    ChildScript,
    Envelope,
    PairDiagnostics,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_faults import Deadline
from scripts.function_tracer_pcode.tests.unit._supervisor_process import (
    SupervisorEntry,
    start_supervisor,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_support import supervisor_case

REPO = Path(__file__).resolve().parents[4]

# --------------------------------------------------------------------------
# 1. the child: a signal after the handler was unloaded
# --------------------------------------------------------------------------

_CHILD = r"""
import ctypes, faulthandler, signal, sys
from scripts.function_tracer_pcode.cli.pair_diagnostics import (
    PairDiagnostics, register_stack_dump_handler,
)
mode, dump = sys.argv[1], sys.argv[2]
if mode == "earlier_registration":       # a registration that saw the default disposition
    signal.signal(signal.SIGUSR1, signal.SIG_DFL)
    faulthandler.register(signal.SIGUSR1, file=open(dump, "ab", buffering=0))
if mode in ("production", "earlier_registration"):
    state = register_stack_dump_handler(PairDiagnostics(dump_path_tmp=dump))
    assert state.handler_registered, state.registration_error
else:                                    # the registration before the fix, in a fresh process
    signal.signal(signal.SIGUSR1, signal.SIG_DFL)
    faulthandler.register(signal.SIGUSR1, file=open(dump, "ab", buffering=0),
                          all_threads=True, chain=False)
faulthandler.unregister(signal.SIGUSR1)  # what _PyFaulthandler_Fini does at shutdown
print("result printed", flush=True)
ctypes.CDLL(None).pause()                # the sync point: the parent signals once we are here
"""

#: pause(2) (the parent waits until the child is blocked in it)
_PAUSE = {"x86_64": "34"}.get(os.uname().machine)


def _blocked_in_pause(pid: int) -> bool:
    try:
        return Path(f"/proc/{pid}/syscall").read_text().split()[0] == _PAUSE
    except (OSError, IndexError):
        return False


@pytest.mark.skipif(_PAUSE is None, reason="the pause(2) syscall number is pinned for x86_64 only")
@pytest.mark.parametrize("mode, killed", [
    ("production", False), ("earlier_registration", False), ("pre_fix", True),
])
def test_a_signal_after_the_handler_is_unloaded_kills_only_the_pre_fix_child(tmp_path, mode, killed):
    """The production registration leaves SIGUSR1 ignored once faulthandler lets it go; the
    registration before the fix left it at the default, and the child dies by the signal.

    ``earlier_registration``: faulthandler keeps the disposition of the first registration when
    a signal is registered again, so the production registration drops an earlier one first.
    """

    child = subprocess.Popen(
        [sys.executable, "-B", "-c", _CHILD, mode, str(tmp_path / "dump.txt")],
        cwd=REPO, env={**os.environ, "PYTHONPATH": str(REPO)},
        stdout=subprocess.PIPE, text=True,
    )
    try:
        limit = time.monotonic() + 60
        while not _blocked_in_pause(child.pid):
            assert child.poll() is None, child.returncode
            assert time.monotonic() < limit, "the child never reached pause()"
        os.kill(child.pid, signal.SIGUSR1)
        if killed:
            assert child.wait(timeout=30) == -signal.SIGUSR1
        else:
            # an ignored signal does not even wake pause(): the child is still there, blocked
            with pytest.raises(subprocess.TimeoutExpired):
                child.wait(timeout=1.0)
            assert _blocked_in_pause(child.pid)
    finally:
        if child.poll() is None:
            child.kill()
            child.wait()
    assert child.stdout.read().strip() == "result printed"


# --------------------------------------------------------------------------
# 2. the production supervisor: its lead-window send and its terminal rule
# --------------------------------------------------------------------------

#: the lead window opens at 6 s; the child reaches its wait in about 1.5 s (asserted below from
#: the recorded times, so a slow start fails instead of passing on another path)
TIMEOUT = 14.0
LEAD = 8.0


def _classify_with_the_cli(case, run, scratch: Path, failure_output: Path) -> tuple[int, dict]:
    """The runner's classification command (``canonical_result`` main) on ``run``'s projection.

    Only the failure path is exercised here, which returns before the pair-status keys are read.
    """

    from scripts.function_tracer_pcode.authority.decision import canonical_result

    config = case.config
    unused = scratch / "unused-pair-status-key"
    stdout = scratch / "classification.stdout"
    argv = [
        "--classify-pair-log", str(case.pair_log),
        "--supervisor-projection", str(run.records.projection),
        "--checkpoint-root", str(config.checkpoint_root),
        "--execution-nonce", config.execution_nonce,
        "--supervisor-signing-key-id", config.supervisor_signing_key_id,
        "--supervisor-signing-key-file", str(config.supervisor_signing_key_file),
        "--worker-signing-key-id", config.worker_signing_key_id,
        "--worker-signing-key-file", str(config.worker_signing_key_file),
        "--pair-status-signing-private-key-file", str(unused),
        "--pair-status-verification-key-file", str(unused),
        "--pair-execution-target-file", str(unused),
        "--classification-failure-output", str(failure_output),
    ]
    with stdout.open("w", encoding="utf-8") as stream:
        saved, sys.stdout = sys.stdout, stream
        try:
            code = canonical_result.main(argv)
        finally:
            sys.stdout = saved
    return code, json.loads(stdout.read_text(encoding="utf-8"))


def _run(tmp_path, *, finalized: bool, after: str = AFTER_SIGNAL_EXIT,
         registration: str = REGISTRATION_PRODUCTION, classify_failure: bool = False):
    journal = tmp_path / "pair.stage.jsonl"
    dump = tmp_path / "stack-dump.txt"
    status = tmp_path / "stack-dump.status.json"
    script = ChildScript((
        PairDiagnostics(journal=str(journal), dump=str(dump), registration=registration),
        Checkpoint(),
        Envelope("UNKNOWN"),
        AwaitDiagnosticSignal(finalized=finalized, dump=str(dump), after=after),
    ))
    with supervisor_case(
        tmp_path, script, allow_child_exit_resolution=True, timeout=TIMEOUT,
        stage_journal_path=journal, stack_dump_file=dump,
        diagnostic_status_output=status, stack_dump_lead_seconds=LEAD,
    ) as case:
        with start_supervisor(case, entry=SupervisorEntry.FRESH_START, deadline=Deadline.TIMER) as handle:
            run = handle.wait()
            records = case.records.child(handle.child())
        child = {
            name: json.loads((records.directory / file).read_text(encoding="utf-8"))
            if (records.directory / file).is_file() else None
            for name, file in (("waiting", records.stopped.name),
                               ("signal", "diagnostic_signal.json"), ("exiting", "exiting.json"))
        }
        store = case.store_directory
        evidence = {
            name: json.loads((store / path).read_text(encoding="utf-8"))["payload"]
            if (store / path).is_file() else None
            for name, path in (("deadline", layout.DEADLINE), ("child_exit", layout.CHILD_EXIT))
        }
        classified = None
        if classify_failure:
            record_path = tmp_path / "classification-failure.json"
            classified = (*_classify_with_the_cli(case, run, tmp_path, record_path),
                          json.loads(record_path.read_text(encoding="utf-8")))
        return run, json.loads(status.read_text(encoding="utf-8")), evidence, child, classified


def _assert_the_signal_reached_the_waiting_child(status, child):
    """The supervisor's own lead-window send is what the child observed (it waited for it)."""

    assert child["waiting"] is not None, "the child never reached its wait"
    assert child["signal"] is not None, (
        "no SIGUSR1 became pending while the child waited", status)
    assert status["signal_sent"] is True
    assert -LEAD - 1.0 < status["signal_sent_offset_seconds"] < 0
    # the child was waiting before the window opened (the signal did not hit an earlier phase)
    assert child["waiting"]["epoch"] < status["signal_sent_epoch"]


def test_a_child_whose_handler_was_unloaded_keeps_its_result_after_the_diagnostic_signal(tmp_path):
    """The case of the issue: before the fix this ended INVALID with rc -10."""

    run, status, evidence, child, _ = _run(tmp_path, finalized=True)

    _assert_the_signal_reached_the_waiting_child(status, child)
    # the signal was delivered after the unload and ignored: the child ended by itself with its
    # CLI code before the deadline, and its result stands
    # (before the fix: INVALID / CANONICAL_CHILD_RESULT_INVALID, EXIT_CODE_-10)
    assert (run.projection["status"], run.projection.get("error_code"),
            evidence["child_exit"]["child_exit_disposition"]) == ("RESOLVED", None, "EXIT_CODE_2")
    assert evidence["deadline"] is None
    assert child["exiting"]["dump_bytes"] == 0 and status["dump_observed"] is False


def test_a_child_whose_handler_is_still_installed_dumps_and_keeps_its_result(tmp_path):
    run, status, evidence, child, _ = _run(tmp_path, finalized=False)

    _assert_the_signal_reached_the_waiting_child(status, child)
    assert child["signal"]["dump_bytes_before_delivery"] == 0
    assert child["exiting"]["dump_bytes"] > 0 and status["dump_observed"] is True
    assert evidence["deadline"] is None
    assert evidence["child_exit"]["child_exit_disposition"] == "EXIT_CODE_2"
    assert run.projection["status"] == "RESOLVED"


def test_a_child_that_outlives_the_ignored_signal_ends_by_the_deadline(tmp_path):
    """After the deadline: the ignored signal changes nothing, and the deadline rule decides."""

    run, status, evidence, child, _ = _run(tmp_path, finalized=True, after=AFTER_SIGNAL_STAY)

    _assert_the_signal_reached_the_waiting_child(status, child)
    assert child["exiting"] is not None                      # it survived the delivery
    assert evidence["deadline"] is not None
    assert evidence["child_exit"]["child_exit_disposition"] == "SIGTERM_AFTER_DEADLINE"
    assert run.projection["status"] == "TIMEOUT"


def test_a_child_killed_by_the_signal_after_its_result_stays_invalid_and_leaves_the_reason(tmp_path):
    """The control for an abnormal end: the terminal rule is unchanged.

    A child whose declaration does not hold (its disposition after the unload is the default)
    dies by the supervisor's signal after writing its result.  The result is still refused
    (the exit code does not join the canonical outcome), and the classifier leaves the
    supervisor's verdict and the durable evidence in the record the runner keeps.
    """

    run, status, evidence, child, classified = _run(
        tmp_path, finalized=True, registration=REGISTRATION_DECLARATION_DOES_NOT_HOLD,
        classify_failure=True,
    )

    _assert_the_signal_reached_the_waiting_child(status, child)
    assert child["exiting"] is None                          # it died at the delivery
    assert evidence["deadline"] is None
    assert evidence["child_exit"]["child_exit_disposition"] == f"EXIT_CODE_{-signal.SIGUSR1}"
    assert (run.projection["status"], run.projection["error_code"],
            run.projection["child_returncode"]) == (
        "INVALID", "CANONICAL_CHILD_RESULT_INVALID", -signal.SIGUSR1)

    code, pair_status, record = classified
    assert code == 2 and pair_status["classification_valid"] is False
    assert "error_code='CANONICAL_CHILD_RESULT_INVALID'" in pair_status["detail"]
    assert f"child_returncode={-signal.SIGUSR1}" in pair_status["detail"]
    assert record["detail"] == pair_status["detail"]
    assert record["projection"]["value"]["error_code"] == "CANONICAL_CHILD_RESULT_INVALID"
    assert record["durable"]["step"] == {
        "kind": "INVALID", "invalid_code": "CANONICAL_CHILD_RESULT_INVALID",
        "detail": record["durable"]["step"]["detail"],
    }
    snapshot = record["durable"]["snapshot"]
    assert snapshot["child_exit"]["returncode"] == -signal.SIGUSR1
    assert snapshot["deadline"]["presence"] == "ABSENT"
    assert snapshot["canonical"]["envelope"] == "VALID"
