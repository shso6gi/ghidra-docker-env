# -*- coding: utf-8 -*-
"""Child-process isolation of concrete executors (``ghidra.concrete_worker``).

The parent is pure Python; these tests replace the PyGhidra child with small
scripts that answer, crash, hang, print garbage or refuse, and check that only
the requests a child did not answer become ``EXECUTOR_ERROR``.  No Ghidra.
"""
import json
import sys
import textwrap
import time

from scripts.function_tracer_pcode.concrete.executor import (
    EntryState,
    ExecutionRequest,
    ExecutionResult,
    Termination,
)
from scripts.function_tracer_pcode.concrete.recording import result_to_json
from scripts.function_tracer_pcode.ghidra.concrete_worker import LINE_PREFIX, run_isolated

REQUESTS = tuple(
    ExecutionRequest(0x1000, EntryState((("sp", 0x6FF00000),), 0x6FF00000, 0x7FF00000), ("x0",), 10 + i)
    for i in range(3)
)
RETURNED = json.dumps(result_to_json(ExecutionResult(Termination.RETURNED, 4, detail="child")))


def _child(body: str):
    script = textwrap.dedent(f"""
        import json, os, sys, time
        job = json.loads(sys.stdin.read())
        def emit(message):
            sys.stdout.write({LINE_PREFIX!r} + json.dumps(message) + "\\n"); sys.stdout.flush()
        RESULT = json.loads({RETURNED!r})
    """) + textwrap.dedent(body)
    return [sys.executable, "-c", script]


def test_a_child_that_answers_everything_gives_every_result():
    command = _child("""
        emit({"kind": "opened", "refusal": None, "facts": {"abi_id": "AARCH64_AAPCS64"}})
        emit({"kind": "functions", "entries": {"f": 4096, "g": None}})
        print("ghidra noise on stdout")
        for i, _ in enumerate(job["requests"]):
            emit({"kind": "result", "index": i, "result": RESULT, "trace": {"i": i}})
        emit({"kind": "done"})
    """)
    run = run_isolated("/bin/x", REQUESTS, timeout_seconds=30, command=command, resolve_functions=["f", "g"])
    assert run.exit == "ok" and run.refusal is None
    assert [r.termination for r in run.results] == [Termination.RETURNED] * 3
    assert run.traces == ({"i": 0}, {"i": 1}, {"i": 2})
    assert run.functions == {"f": 4096, "g": None}


def test_a_crash_only_costs_the_unanswered_requests():
    command = _child("""
        emit({"kind": "opened", "refusal": None, "facts": None})
        emit({"kind": "result", "index": 0, "result": RESULT, "trace": None})
        os._exit(134)
    """)
    run = run_isolated("/bin/x", REQUESTS, timeout_seconds=30, command=command)
    assert run.exit == "exit 134"
    assert run.results[0].termination is Termination.RETURNED
    for result in run.results[1:]:
        assert result.termination is Termination.EXECUTOR_ERROR and "exit 134" in result.detail


def test_a_killed_child_is_reported_by_its_signal():
    command = _child("""
        import signal
        os.kill(os.getpid(), signal.SIGKILL)
    """)
    run = run_isolated("/bin/x", REQUESTS, timeout_seconds=30, command=command)
    assert run.exit == "signal 9"
    assert all(r.termination is Termination.EXECUTOR_ERROR for r in run.results)


def test_a_hanging_child_is_killed_at_the_deadline_with_its_process_group():
    command = _child("""
        import subprocess
        subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
        emit({"kind": "opened", "refusal": None, "facts": None})
        emit({"kind": "result", "index": 1, "result": RESULT, "trace": None})
        time.sleep(60)
    """)
    started = time.monotonic()
    run = run_isolated("/bin/x", REQUESTS, timeout_seconds=3, command=command)
    assert time.monotonic() - started < 30
    assert run.exit == "timeout"
    assert run.results[1].termination is Termination.RETURNED
    assert run.results[0].termination is Termination.EXECUTOR_ERROR and "timeout" in run.results[0].detail


def test_damaged_lines_answer_nothing_and_an_unfinished_child_is_not_ok():
    command = _child("""
        sys.stdout.write({prefix!r} + "{{not json\\n")
        emit({{"kind": "result", "index": 7, "result": RESULT, "trace": None}})
        emit({{"kind": "result", "index": 0, "result": {{"termination": "RETURNED"}}, "trace": None}})
        emit({{"kind": "result", "index": 2, "result": RESULT, "trace": None}})
    """.format(prefix=LINE_PREFIX))
    run = run_isolated("/bin/x", REQUESTS, timeout_seconds=30, command=command)
    assert run.exit == "ended without finishing"
    assert run.results[0].termination is Termination.EXECUTOR_ERROR
    assert run.results[1].termination is Termination.EXECUTOR_ERROR
    assert run.results[2].termination is Termination.RETURNED


def test_a_refused_program_answers_every_request_with_the_refusal():
    command = _child("""
        emit({"kind": "opened", "refusal": {"reason": "ABI_DISAGREES_WITH_COMPILER_SPEC", "detail": "X"},
              "facts": None})
        emit({"kind": "done"})
    """)
    run = run_isolated("/bin/x", REQUESTS, timeout_seconds=30, command=command)
    assert run.refusal["reason"] == "ABI_DISAGREES_WITH_COMPILER_SPEC"
    for result in run.results:
        assert result.termination is Termination.EXECUTOR_ERROR
        assert "ABI_DISAGREES_WITH_COMPILER_SPEC" in result.detail


def test_the_job_carries_the_requests_and_options():
    command = _child("""
        emit({"kind": "opened", "refusal": None, "facts": {"job": job}})
        emit({"kind": "done"})
    """)
    run = run_isolated("/bin/x", REQUESTS[:1], timeout_seconds=30, command=command, options={"record": True})
    job = run.facts["job"]
    assert job["binary"] == "/bin/x" and job["options"] == {"record": True}
    assert job["requests"][0]["step_limit"] == 10
