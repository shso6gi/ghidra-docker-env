# -*- coding: utf-8 -*-
"""Recording concrete runs and replaying them without Ghidra.

A *run trace* (schema ``concrete-run-trace-v2``) holds what one live run
produced, as data:

* ``program`` -- identity of the binary and the facts its executor was
  opened with (language, compiler specification, executable format, ABI,
  the result of the run-time ABI check);
* ``setup`` -- the ``RunSetup`` the observer was built with;
* ``request`` -- the ``ExecutionRequest``;
* ``events`` -- every event the executor sent to the observer, in order;
* ``result`` -- the ``ExecutionResult`` the live observer returned.

Replaying feeds ``events`` to a fresh ``RunObserver`` -- the production
observer -- and yields the result again.  A trace is a record of what the
emulator did, never a model of it: replay neither executes nor infers
anything, and a request without a recording is an executor error, not a
guess.

Event encoding (JSON arrays):

====================================  ==========================================
``["I", address]``                    next instruction
``["D", address, [op, ...]]``         P-code of an instruction (first time only);
                                      ``op = [mnemonic, out | null, [in, ...]]``
                                      (``CALLOTHER``: a fourth element, the user
                                      operation's name); a varnode is
                                      ``[space, offset, size]``
``["O", index]``                      operation ``index`` runs
``["O", index, [value, ...]]``        ... with its input values (unsigned, in
                                      input order), when the observer asked
``["P", value]``                      the value the operation wrote, when the
                                      observer asked
``["L", space, address, size]``       the pending LOAD's address
``["S", space, address, size]``       the pending STORE's address
``["U", space, offset, size, d]``     read of a location holding no value
                                      (``d`` = 1 while decoding)
``["X", termination, detail]``        the executor stopped the run
``["R", [[register, value], ...]]``   register values at return
====================================  ==========================================

Version 1 traces (C1, without values) still replay; a run whose monitors
needed values it lacks replays as not monitored.
"""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.concrete.executor import (
    EntryState,
    ExecutionRequest,
    ExecutionResult,
    Hazard,
    HazardKind,
    IntegerOverflow,
    OverflowDisposition,
    Termination,
)
from scripts.function_tracer_pcode.concrete.observation import FpFormat, ObservedRegister
from scripts.function_tracer_pcode.concrete.run_observer import (
    OpDescriptor,
    RegisterFact,
    RunObserver,
    RunSetup,
    Varnode,
)

TRACE_SCHEMA = "concrete-run-trace-v2"
TRACE_SCHEMA_V1 = "concrete-run-trace-v1"
_SCHEMAS = (TRACE_SCHEMA, TRACE_SCHEMA_V1)


# ------------------------------------------------------------- encoding

def _varnode(v: Optional[Varnode]):
    return None if v is None else [v.space, v.offset, v.size]


def _decode_varnode(raw) -> Optional[Varnode]:
    return None if raw is None else Varnode(str(raw[0]), int(raw[1]), int(raw[2]))


def encode_op(op: OpDescriptor) -> list:
    raw = [op.mnemonic, _varnode(op.output), [_varnode(v) for v in op.inputs]]
    if op.userop is not None:
        raw.append(op.userop)
    return raw


def decode_op(raw) -> OpDescriptor:
    return OpDescriptor(
        str(raw[0]), _decode_varnode(raw[1]), tuple(_decode_varnode(v) for v in raw[2]),
        str(raw[3]) if len(raw) > 3 and raw[3] is not None else None,
    )


def setup_to_json(setup: RunSetup) -> Dict[str, Any]:
    return {
        "big_endian": setup.big_endian,
        "memory_space": setup.memory_space,
        "registers": [[r.name, r.offset, r.size] for r in setup.registers],
        "stack_pointer": setup.stack_pointer,
        "code_ranges": [list(r) for r in setup.code_ranges],
        "external_entries": [list(e) for e in setup.external_entries],
        "writable_image_ranges": [list(r) for r in setup.writable_image_ranges],
        "write_page_limit": setup.write_page_limit,
        "processor": setup.processor,
        "zero_initialized_ranges": [list(r) for r in setup.zero_initialized_ranges],
        "c_int_bytes": setup.c_int_bytes,
    }


def setup_from_json(raw: Mapping[str, Any]) -> RunSetup:
    return RunSetup(
        big_endian=bool(raw["big_endian"]),
        memory_space=str(raw["memory_space"]),
        registers=tuple(RegisterFact(str(n), int(o), int(s)) for n, o, s in raw["registers"]),
        stack_pointer=str(raw["stack_pointer"]),
        code_ranges=tuple((int(a), int(b)) for a, b in raw["code_ranges"]),
        external_entries=tuple((int(a), str(n)) for a, n in raw["external_entries"]),
        writable_image_ranges=tuple((int(a), int(b)) for a, b in raw["writable_image_ranges"]),
        write_page_limit=int(raw["write_page_limit"]),
        processor=str(raw.get("processor", "")),
        zero_initialized_ranges=tuple((int(a), int(b)) for a, b in raw.get("zero_initialized_ranges", ())),
        c_int_bytes=int(raw.get("c_int_bytes", 0)),
    )


def request_to_json(request: ExecutionRequest) -> Dict[str, Any]:
    state = request.entry_state
    return {
        "entry_address": request.entry_address,
        "entry_state": {
            "registers": [[n, v] for n, v in state.registers],
            "stack_pointer": state.stack_pointer,
            "return_address": state.return_address,
            "defined_bytes": [[n, c] for n, c in state.defined_bytes],
        },
        "observe_registers": list(request.observe_registers),
        "step_limit": request.step_limit,
    }


def request_from_json(raw: Mapping[str, Any]) -> ExecutionRequest:
    state = raw["entry_state"]
    return ExecutionRequest(
        entry_address=int(raw["entry_address"]),
        entry_state=EntryState(
            tuple((str(n), int(v)) for n, v in state["registers"]),
            int(state["stack_pointer"]),
            int(state["return_address"]),
            tuple((str(n), int(c)) for n, c in state.get("defined_bytes", ())),
        ),
        observe_registers=tuple(str(n) for n in raw["observe_registers"]),
        step_limit=int(raw["step_limit"]),
    )


def result_to_json(result: ExecutionResult) -> Dict[str, Any]:
    return {
        "termination": result.termination.value,
        "steps": result.steps,
        "observed_registers": [
            [name, o.value, o.defined_low_bytes, None if o.value_format is None else o.value_format.value,
             o.reliable_low_bytes, list(o.unreliable)]
            for name, o in result.observed_registers
        ],
        "hazards": [[h.kind.value, h.detail] for h in result.hazards],
        "fp_operations_tracked": result.fp_operations_tracked,
        "integer_ub_operations_tracked": result.integer_ub_operations_tracked,
        "writable_image_reads": [list(r) for r in result.writable_image_reads],
        "operation_counts": [list(c) for c in result.operation_counts],
        "monitor_events": [list(c) for c in result.monitor_events],
        "integer_overflows": [
            [o.address, o.operation, o.width, o.disposition.value, o.count, list(o.uses)]
            for o in result.integer_overflows
        ],
        "detail": result.detail,
    }


def result_from_json(raw: Mapping[str, Any]) -> ExecutionResult:
    return ExecutionResult(
        termination=Termination(raw["termination"]),
        steps=int(raw["steps"]),
        observed_registers=tuple(_observed_from_json(entry) for entry in raw["observed_registers"]),
        hazards=tuple(Hazard(HazardKind(kind), str(detail)) for kind, detail in raw["hazards"]),
        fp_operations_tracked=bool(raw["fp_operations_tracked"]),
        integer_ub_operations_tracked=bool(raw["integer_ub_operations_tracked"]),
        writable_image_reads=tuple((int(a), int(n)) for a, n in raw["writable_image_reads"]),
        operation_counts=tuple((str(m), int(c)) for m, c in raw["operation_counts"]),
        monitor_events=tuple((str(m), int(c)) for m, c in raw.get("monitor_events", ())),
        integer_overflows=tuple(
            IntegerOverflow(int(a), str(m), int(w), OverflowDisposition(d), int(c), tuple(str(x) for x in u))
            for a, m, w, d, c, u in raw.get("integer_overflows", ())
        ),
        detail=str(raw["detail"]),
    )


def _observed_from_json(entry) -> Tuple[str, ObservedRegister]:
    name, value, defined, fmt = entry[:4]
    reliable = entry[4] if len(entry) > 4 else None
    unreliable = tuple(str(k) for k in entry[5]) if len(entry) > 5 else ()
    return str(name), ObservedRegister(
        int(value), int(defined), None if fmt is None else FpFormat(fmt),
        None if reliable is None else int(reliable), unreliable,
    )


# ------------------------------------------------------------ recording

class RecordingObserver:
    """Forwards every event to a ``RunObserver`` and keeps it as trace data."""

    def __init__(self, inner: RunObserver):
        self._inner = inner
        self.events: List[list] = []

    @property
    def stopped(self):
        return self._inner.stopped

    def instruction(self, address):
        self.events.append(["I", address])
        return self._inner.instruction(address)

    def decoded(self, address, ops):
        self.events.append(["D", address, [encode_op(op) for op in ops]])
        return self._inner.decoded(address, ops)

    def value_request(self, index):
        return self._inner.value_request(index)

    def op(self, index, values=None):
        self.events.append(["O", index] if values is None else ["O", index, [int(v) for v in values]])
        return self._inner.op(index, values)

    def op_output(self, value):
        self.events.append(["P", int(value)])
        return self._inner.op_output(value)

    def userop_value(self):
        return self._inner.userop_value()

    def load(self, space, address, size):
        self.events.append(["L", space, address, size])
        return self._inner.load(space, address, size)

    def store(self, space, address, size):
        self.events.append(["S", space, address, size])
        return self._inner.store(space, address, size)

    def uninitialized_read(self, space, offset, size, decoding):
        self.events.append(["U", space, offset, size, 1 if decoding else 0])
        return self._inner.uninitialized_read(space, offset, size, decoding)

    def stopped_by_executor(self, termination, detail):
        self.events.append(["X", str(termination), detail])
        return self._inner.stopped_by_executor(termination, detail)

    def returned(self, values):
        self.events.append(["R", [[n, v] for n, v in values]])
        return self._inner.returned(values)

    def result(self):
        return self._inner.result()


def replay_events(setup: RunSetup, request: ExecutionRequest, events: Iterable[Sequence]) -> ExecutionResult:
    """Feed recorded events to the production observer; return its result."""
    observer = RunObserver(setup, request)
    for event in events:
        kind = event[0]
        if kind == "I":
            observer.instruction(int(event[1]))
        elif kind == "D":
            observer.decoded(int(event[1]), tuple(decode_op(raw) for raw in event[2]))
        elif kind == "O":
            values = tuple(int(v) for v in event[2]) if len(event) > 2 else None
            observer.op(int(event[1]), values)
        elif kind == "P":
            observer.op_output(int(event[1]))
        elif kind == "L":
            observer.load(str(event[1]), int(event[2]), int(event[3]))
        elif kind == "S":
            observer.store(str(event[1]), int(event[2]), int(event[3]))
        elif kind == "U":
            observer.uninitialized_read(str(event[1]), int(event[2]), int(event[3]), bool(event[4]))
        elif kind == "X":
            observer.stopped_by_executor(str(event[1]), str(event[2]))
        elif kind == "R":
            observer.returned(tuple((str(n), int(v)) for n, v in event[1]))
        else:
            raise ValueError(f"unknown trace event {kind!r}")
    return observer.result()


def make_trace(
    program: Mapping[str, Any],
    setup: RunSetup,
    request: ExecutionRequest,
    events: List[list],
    result: ExecutionResult,
    provenance: Optional[Mapping[str, Any]] = None,
) -> Dict[str, Any]:
    return {
        "schema": TRACE_SCHEMA,
        "program": dict(program),
        "setup": setup_to_json(setup),
        "request": request_to_json(request),
        "events": events,
        "result": result_to_json(result),
        "provenance": dict(provenance or {}),
    }


def replay_trace(trace: Mapping[str, Any]) -> Tuple[ExecutionResult, ExecutionResult]:
    """(replayed result, recorded result) of one trace."""
    if trace.get("schema") not in _SCHEMAS:
        raise ValueError(f"not a {TRACE_SCHEMA} trace: {trace.get('schema')!r}")
    setup = setup_from_json(trace["setup"])
    request = request_from_json(trace["request"])
    return replay_events(setup, request, trace["events"]), result_from_json(trace["result"])


class RecordedExecutor:
    """A ``ConcreteExecutor`` over recorded runs of one program.

    ``execute`` replays the trace recorded for an equal request through the
    production observer.  A request that was not recorded is an
    ``EXECUTOR_ERROR`` result.
    """

    def __init__(self, traces: Iterable[Mapping[str, Any]]):
        # Requests are frozen dataclasses: they are their own exact key.
        self._traces: Dict[ExecutionRequest, Mapping[str, Any]] = {}
        program: Optional[str] = None
        for trace in traces:
            if trace.get("schema") not in _SCHEMAS:
                raise ValueError(f"not a {TRACE_SCHEMA} trace: {trace.get('schema')!r}")
            sha256 = trace["program"].get("sha256")
            if program is None:
                program = sha256
            elif sha256 != program:
                raise ValueError("a recorded executor holds the runs of one program")
            self._traces[request_from_json(trace["request"])] = trace

    def execute(self, request: ExecutionRequest) -> ExecutionResult:
        trace = self._traces.get(request)
        if trace is None:
            return ExecutionResult(Termination.EXECUTOR_ERROR, 0, detail="no recorded run for this request")
        replayed, _ = replay_trace(trace)
        return replayed
