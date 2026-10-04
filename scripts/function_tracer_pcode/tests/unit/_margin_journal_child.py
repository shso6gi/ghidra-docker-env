# -*- coding: utf-8 -*-
"""A pair child for the margin tests (Issue #106 PR-106-B review 4).

It runs the production pieces a real pair child runs around the analysis
deadline -- `cli.pair_diagnostics.install_pair_diagnostics` (the journal, its
seal at exit and the stack-dump handler), a `core.deadline` scope that trips at
a checkpoint (the trip row is written by the deadline itself), the result's
`analysis_deadline` record (`checker.diagnostics.attach_analysis_deadline`) and
the result JSON markers -- and injects a write failure into the real
`StageJournal`'s file:

* ``none``: every write succeeds;
* ``trip``: the write of the ``deadline_tripped`` row fails once (``ENOSPC``);
* ``after_trip``: every write after the trip row fails (the seal included).

``exit`` is ``normal`` (print the result and leave through ``sys.exit``, so the
journal is sealed at exit) or ``killed`` (SIGKILL right after the trip: no
result, no seal).  The deadline's clock jumps 101 s at the trip, so the trip's
``elapsed_seconds`` is 101 s of a 100 s budget; the child prints, on stderr,
the facts a supervisor knows (pid, start token) and the monotonic time the
margin will read as the analysis start, so the test can write the supervisor's
sidecar.

usage: python -m scripts.function_tracer_pcode.tests.unit._margin_journal_child \
           <journal> <dump> <inject> <exit>
"""
from __future__ import annotations

import errno
import json
import os
import signal
import sys
import time
import types

from scripts.function_tracer_pcode.checker.diagnostics import attach_analysis_deadline
from scripts.function_tracer_pcode.cli.pair_diagnostics import install_pair_diagnostics
from scripts.function_tracer_pcode.core import deadline as deadline_module
from scripts.function_tracer_pcode.core.errors import DeadlineExceeded
from scripts.function_tracer_pcode.core.stage_journal import (
    active_stage_journal,
    journal_stage_end,
    journal_stage_start,
)

BUDGET = 100.0
JUMP = 101.0
RESULT_JSON_BEGIN = "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
RESULT_JSON_END = "=== EQUIVALENCE_RESULT_JSON_END ==="


class _FaultyFile:
    """The journal's file, failing the writes ``inject`` names (the writer counts them)."""

    def __init__(self, inner, inject: str) -> None:
        self.inner = inner
        self.inject = inject
        self.tripped = False
        self.failed_once = False

    def write(self, text: str) -> int:
        is_trip = '"deadline_tripped"' in text
        if self.inject == "trip" and is_trip and not self.failed_once:
            self.failed_once = True
            raise OSError(errno.ENOSPC, "No space left on device")
        if self.inject == "after_trip" and self.tripped:
            raise OSError(errno.ENOSPC, "No space left on device")
        written = self.inner.write(text)
        self.tripped = self.tripped or is_trip
        return written

    def flush(self) -> None:
        self.inner.flush()

    def close(self) -> None:
        self.inner.close()


def main(argv) -> None:
    journal_path, dump_path, inject, exit_mode = argv
    state = install_pair_diagnostics(types.SimpleNamespace(
        stage_journal=journal_path, stack_dump_file=dump_path, stack_dump_artifact=dump_path,
    ))
    journal = active_stage_journal()
    journal._handle = _FaultyFile(journal._handle, inject)
    jump = [0.0]
    policy = deadline_module.DeadlinePolicy(
        budget_seconds=BUDGET, clock=lambda: time.monotonic() + jump[0])
    result = types.SimpleNamespace(diagnostics={})
    with deadline_module.deadline_scope(policy) as deadline:
        started = time.monotonic()
        print(json.dumps({
            "pid": os.getpid(),
            "start_token": (state.payload or {}).get("start_token"),
            "analysis_start": started - JUMP,
        }), file=sys.stderr, flush=True)
        journal_stage_start("check")
        jump[0] = JUMP
        try:
            deadline_module.checkpoint("solver")
        except DeadlineExceeded:
            pass
        journal_stage_end("check", time.monotonic() - started)
        attach_analysis_deadline(result, deadline)
    if exit_mode == "killed":
        os.kill(os.getpid(), signal.SIGKILL)
    journal_stage_start("result_emit")
    print(RESULT_JSON_BEGIN)
    print(json.dumps({"diagnostics": result.diagnostics}))
    print(RESULT_JSON_END, flush=True)
    journal_stage_end("result_emit", 0.0)
    sys.exit(0)


if __name__ == "__main__":
    main(sys.argv[1:])
