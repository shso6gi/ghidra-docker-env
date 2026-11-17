# -*- coding: utf-8 -*-
"""Running concrete executors in child processes.

``run_isolated`` runs a batch of ``ExecutionRequest`` s against one binary in a
child process and returns one ``ExecutionResult`` per request.  Whatever
happens to the child -- a JVM crash, an exhausted heap, a hang past the
deadline, garbage on its output -- only the requests it had not answered get
``EXECUTOR_ERROR`` results; the caller, other binaries and other workers are
not affected.  The parent never imports Ghidra.

The child (``python -m scripts.function_tracer_pcode.ghidra.concrete_worker``)
reads one JSON job from stdin, opens the binary with PyGhidra, opens an
executor (``ghidra.concrete_executor.open_executor``) and writes one line per
event to stdout, each prefixed with ``LINE_PREFIX`` so that anything else the
JVM prints is ignored:

* ``{"kind": "opened", "refusal": null | {...}, "facts": {...}}``
* ``{"kind": "functions", "entries": {name: address | null}}`` (when the job
  asks to resolve function names: a non-thunk, non-external function with
  that name, when there is exactly one)
* ``{"kind": "result", "index": i, "result": {...}, "trace": {...} | null,
  "seconds": wall-clock seconds of the run}``
* ``{"kind": "done"}``
"""

from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.concrete.executor import (
    ExecutionRequest,
    ExecutionResult,
    Termination,
)
from scripts.function_tracer_pcode.concrete.recording import (
    request_from_json,
    request_to_json,
    result_from_json,
    result_to_json,
)

LINE_PREFIX = "CONCRETE-WORKER "
CHILD_MODULE = "scripts.function_tracer_pcode.ghidra.concrete_worker"


@dataclass(frozen=True)
class IsolatedRun:
    """What one child process produced for one binary.

    ``refusal`` is the executor's refusal of the program (then every result
    is ``EXECUTOR_ERROR`` with the refusal as detail); ``exit`` describes how
    the child ended (``"ok"``, ``"exit 3"``, ``"signal 9"``, ``"timeout"``).
    """

    results: Tuple[ExecutionResult, ...]
    refusal: Optional[Mapping[str, Any]]
    facts: Optional[Mapping[str, Any]]
    traces: Tuple[Optional[Mapping[str, Any]], ...]
    exit: str
    stderr_tail: str = ""
    functions: Mapping[str, Optional[int]] = field(default_factory=dict)
    # Wall-clock seconds of each answered run (``None`` when unanswered).
    seconds: Tuple[Optional[float], ...] = ()


def _child_command() -> List[str]:
    return [sys.executable, "-B", "-m", CHILD_MODULE]


def _describe_exit(code: Optional[int]) -> str:
    if code is None:
        return "timeout"
    if code == 0:
        return "ok"
    if code < 0:
        return f"signal {-code}"
    return f"exit {code}"


def run_isolated(
    binary: str,
    requests: Sequence[ExecutionRequest],
    *,
    timeout_seconds: float,
    options: Optional[Mapping[str, Any]] = None,
    command: Optional[Sequence[str]] = None,
    cwd: Optional[str] = None,
    env: Optional[Mapping[str, str]] = None,
    resolve_functions: Sequence[str] = (),
) -> IsolatedRun:
    """Run ``requests`` against ``binary`` in a child process."""
    job = {
        "binary": binary,
        "requests": [request_to_json(r) for r in requests],
        "options": dict(options or {}),
        "resolve_functions": list(resolve_functions),
    }
    process = subprocess.Popen(
        list(command or _child_command()),
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=cwd,
        env=None if env is None else dict(env),
        start_new_session=True,
        text=True,
    )
    try:
        stdout, stderr = process.communicate(json.dumps(job), timeout=timeout_seconds)
        code: Optional[int] = process.returncode
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            process.kill()
        stdout, stderr = process.communicate()
        code = None

    results: Dict[int, ExecutionResult] = {}
    traces: Dict[int, Mapping[str, Any]] = {}
    seconds: Dict[int, float] = {}
    refusal = facts = None
    functions: Dict[str, Optional[int]] = {}
    done = False
    for line in (stdout or "").splitlines():
        if not line.startswith(LINE_PREFIX):
            continue
        try:
            message = json.loads(line[len(LINE_PREFIX):])
            kind = message["kind"]
            if kind == "opened":
                refusal, facts = message.get("refusal"), message.get("facts")
            elif kind == "functions":
                functions = {
                    str(name): None if entry is None else int(entry)
                    for name, entry in message["entries"].items()
                }
            elif kind == "result":
                index = int(message["index"])
                if 0 <= index < len(requests):
                    results[index] = result_from_json(message["result"])
                    if message.get("seconds") is not None:
                        seconds[index] = float(message["seconds"])
                    if message.get("trace") is not None:
                        traces[index] = message["trace"]
            elif kind == "done":
                done = True
        except (ValueError, KeyError, TypeError):
            continue   # a damaged line answers nothing

    exit_text = _describe_exit(code)
    if exit_text == "ok" and not done:
        exit_text = "ended without finishing"
    final = []
    for index in range(len(requests)):
        if index in results:
            final.append(results[index])
        elif refusal is not None:
            final.append(ExecutionResult(
                Termination.EXECUTOR_ERROR, 0,
                detail=f"refused: {refusal.get('reason')} {refusal.get('detail', '')}".strip(),
            ))
        else:
            final.append(ExecutionResult(
                Termination.EXECUTOR_ERROR, 0, detail=f"worker {exit_text} before this request"
            ))
    return IsolatedRun(
        tuple(final),
        refusal,
        facts,
        tuple(traces.get(i) for i in range(len(requests))),
        exit_text,
        (stderr or "")[-2000:],
        functions,
        tuple(seconds.get(i) for i in range(len(requests))),
    )


# ------------------------------------------------------------------ child

def _emit(message: Mapping[str, Any]) -> None:
    sys.stdout.write(LINE_PREFIX + json.dumps(message) + "\n")
    sys.stdout.flush()


def _child_main() -> int:
    import tempfile

    job = json.loads(sys.stdin.read())
    options = dict(job.get("options") or {})
    record = bool(options.pop("record", False))
    executor_options = {
        key: options[key] for key in ("time_limit_seconds", "write_page_limit") if key in options
    }

    from scripts.function_tracer_pcode.config import apply_runtime_environment
    from scripts.function_tracer_pcode.ghidra.pyghidra_support import (
        load_pyghidra,
        start_headless_pyghidra,
    )
    from pathlib import Path

    runtime_env = apply_runtime_environment()
    pyghidra = load_pyghidra()
    start_headless_pyghidra(
        pyghidra,
        install_dir=Path(runtime_env.ghidra_install_dir) if runtime_env.ghidra_install_dir else None,
    )
    from scripts.function_tracer_pcode.concrete.abi_conformance import facts_to_json
    from scripts.function_tracer_pcode.ghidra.concrete_executor import (
        ExecutorRefusal,
        open_executor,
    )

    with tempfile.TemporaryDirectory() as temp_dir:
        with pyghidra.open_project(temp_dir, "ConcreteWorker", create=True) as project:
            loader = pyghidra.program_loader().project(project).source(job["binary"])
            with loader.load() as loaded:
                program = loaded.getPrimaryDomainObject()
                pyghidra.analyze(program)
                names = list(job.get("resolve_functions") or ())
                if names:
                    found: Dict[str, List[int]] = {name: [] for name in names}
                    for function in program.getFunctionManager().getFunctions(True):
                        name = str(function.getName())
                        if name in found and not function.isThunk() and not function.isExternal():
                            found[name].append(int(function.getEntryPoint().getOffset()))
                    _emit({"kind": "functions", "entries": {
                        name: entries[0] if len(entries) == 1 else None
                        for name, entries in found.items()
                    }})
                executor = open_executor(program, record=record, **executor_options)
                if isinstance(executor, ExecutorRefusal):
                    _emit({
                        "kind": "opened",
                        "refusal": {"reason": executor.reason.value, "detail": executor.detail},
                        "facts": None if executor.facts is None else {
                            "compiler_spec": facts_to_json(executor.facts),
                        },
                    })
                    _emit({"kind": "done"})
                    return 0
                _emit({"kind": "opened", "refusal": None, "facts": {
                    "abi_id": executor.abi.abi_id.value,
                    "compiler_spec": facts_to_json(executor.facts),
                }})
                for index, raw in enumerate(job["requests"]):
                    started = time.monotonic()
                    result = executor.execute(request_from_json(raw))
                    _emit({
                        "kind": "result",
                        "index": index,
                        "result": result_to_json(result),
                        "trace": executor.last_trace if record else None,
                        "seconds": round(time.monotonic() - started, 4),
                    })
    _emit({"kind": "done"})
    return 0


if __name__ == "__main__":
    sys.exit(_child_main())
