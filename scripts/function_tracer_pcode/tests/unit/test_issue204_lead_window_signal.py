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

The waits are on events (the child blocked in ``pause``, a file the child or the test
writes).  The order "signal sent, then the child exited" is asserted from recorded
times, not assumed from a wait.
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
if mode == "production":
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
@pytest.mark.parametrize("mode, killed", [("production", False), ("pre_fix", True)])
def test_a_signal_after_the_handler_is_unloaded_kills_only_the_pre_fix_child(tmp_path, mode, killed):
    """The production registration leaves SIGUSR1 ignored once faulthandler lets it go; the
    registration before the fix left it at the default, and the child dies by the signal."""

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

#: the lead window opens 10 s before the deadline; the child reaches its wait well before it
TIMEOUT = 25.0
LEAD = 10.0


def _run(tmp_path, *, finalized: bool):
    journal = tmp_path / "pair.stage.jsonl"
    dump = tmp_path / "stack-dump.txt"
    status = tmp_path / "stack-dump.status.json"
    script = ChildScript((
        PairDiagnostics(journal=str(journal), dump=str(dump)),
        Checkpoint(),
        Envelope("UNKNOWN"),
        AwaitDiagnosticSignal(finalized=finalized, dump=str(dump)),
    ))
    exited = None
    with supervisor_case(
        tmp_path, script, allow_child_exit_resolution=True, timeout=TIMEOUT,
        stage_journal_path=journal, stack_dump_file=dump,
        diagnostic_status_output=status, stack_dump_lead_seconds=LEAD,
    ) as case:
        with start_supervisor(case, entry=SupervisorEntry.FRESH_START, deadline=Deadline.TIMER) as handle:
            if finalized:
                started = time.monotonic()
                while handle.child() is None:
                    assert time.monotonic() < started + TIMEOUT, "the child was never started"
                    time.sleep(0.01)
                records = case.records.child(handle.child())
                while not records.stopped.exists():
                    assert time.monotonic() < started + TIMEOUT, "the child never reached its wait"
                    time.sleep(0.01)
                # let the child end inside the lead window, after the send is due; whether the
                # send came first is checked below from the recorded times
                while time.monotonic() < started + TIMEOUT - LEAD / 2:
                    time.sleep(0.05)
                (records.directory / "finish_after_signal").write_text("1", encoding="utf-8")
            run = handle.wait()
            if finalized and (records.directory / "exiting.json").is_file():
                exited = json.loads(
                    (records.directory / "exiting.json").read_text(encoding="utf-8"))["epoch"]
        store = case.store_directory
        evidence = {
            name: json.loads((store / path).read_text(encoding="utf-8"))["payload"]
            if (store / path).is_file() else None
            for name, path in (("deadline", layout.DEADLINE), ("child_exit", layout.CHILD_EXIT))
        }
        return run, json.loads(status.read_text(encoding="utf-8")), evidence, exited


def test_a_child_whose_handler_was_unloaded_keeps_its_result_after_the_diagnostic_signal(tmp_path):
    """The case of the issue: before the fix this ended INVALID with rc -10."""

    run, status, evidence, exited = _run(tmp_path, finalized=True)

    # the child ended by itself with its CLI code before the deadline, and its result stands
    # (before the fix: INVALID / CANONICAL_CHILD_RESULT_INVALID, EXIT_CODE_-10)
    assert (run.projection["status"], run.projection.get("error_code"),
            evidence["child_exit"]["child_exit_disposition"]) == ("RESOLVED", None, "EXIT_CODE_2")
    assert evidence["deadline"] is None
    # the supervisor's own diagnostic sent SIGUSR1 inside the lead window, before the child ended
    assert status["signal_sent"] is True
    assert -LEAD - 1.0 < status["signal_sent_offset_seconds"] < 0
    assert status["signal_sent_epoch"] < exited
    assert status["dump_observed"] is False                    # the handler was already gone


def test_a_child_whose_handler_is_still_installed_dumps_and_keeps_its_result(tmp_path):
    run, status, evidence, _exited = _run(tmp_path, finalized=False)

    assert status["signal_sent"] is True and status["dump_observed"] is True
    assert evidence["deadline"] is None
    assert evidence["child_exit"]["child_exit_disposition"] == "EXIT_CODE_2"
    assert run.projection["status"] == "RESOLVED"
