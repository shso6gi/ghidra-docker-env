# -*- coding: utf-8 -*-
"""Issue #163: supervisor が起こす worker child（test 専用 program）。

``python -m scripts.function_tracer_pcode.tests.unit._supervisor_child '<spec>'``
として supervisor の barrier から exec される。何をするかは parent が
``ChildScript``（step の列 + 停止点）で決め、child はそれを production の
API で実行する。例外は canonical TIMEOUT の driver で、solver 境界だけを
``execution_authority._PINNED_PARALLEL_RUN_IMPL``（既存 test と同じ差し替え口）で
TIMEOUT に固定する。

* 最初に **launch-before-exec** を child 自身が確かめる: ``launch.json`` が
  既に durable で、``ProcessWorkerRuntime.from_environment()``（署名・PID・
  start token の検証）が通ること。通らなければ本処理に入らず
  ``LAUNCH_EVIDENCE_EXIT`` で終わる。通れば観測をこの child の記録へ書く
  （parent は、child を起こした invocation の記録と突き合わせる）。
* step は ``STEP_HANDLERS`` に 1 つずつ登録する。checkpoint は production の
  decompilation broker、canonical 結果は production connector と
  ``build_canonical_result_finalization_bundle`` / ``persist_canonical_result_envelope``
  を通す。outcome は ``OUTCOME_DRIVERS`` に 1 つずつ登録する（launch 側は
  outcome を知らない）。
* 要求した outcome と違う decision が出たら envelope を書かずに
  ``FIXTURE_FAILURE_EXIT`` で終わる。UNKNOWN を TIMEOUT の代わりに通さない。
* Ghidra の fake と loop の fixture は共有 fixture module
  （``_operational_test_fixtures`` / ``_loop_test_fixtures``）から取る。
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import json
import os
from pathlib import Path
import sys
from typing import Any, Callable, Mapping, Optional

from scripts.function_tracer_pcode.tests.unit._supervisor_faults import (
    Fault,
    install_publication_faults,
    stop_here,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_records import (
    ChildIdentity,
    ChildRecords,
    HarnessRecords,
    write_json,
)
from scripts.function_tracer_pcode.authority.seal_work import SealWorkBudget

MODULE = "scripts.function_tracer_pcode.tests.unit._supervisor_child"
#: harness が予約する exit code（CLI の 0-4 / supervisor の 124 / crash の 86 と別）。
LAUNCH_EVIDENCE_EXIT = 87
FIXTURE_FAILURE_EXIT = 88


# ---------------------------------------------------------------------------
# parent 側: 何をさせるかの宣言
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Checkpoint:
    """broker 経由で関数を 1 つ decompile し、checkpoint を RESOLVED まで進める。"""

    def to_json(self) -> dict[str, Any]:
        return {"step": "checkpoint"}


@dataclass(frozen=True)
class Envelope:
    """production の決定から canonical 結果を作り、envelope を永続化して出力する。"""

    outcome: str
    #: 永続化した envelope の top-level field を 1 つ選び、その digest 値の先頭
    #: 1 文字を書き換える。
    corrupt: Optional[str] = None
    #: 書き換えたあと ``envelope_digest`` を計算し直す（封は正しいまま、中身
    #: だけが食い違う envelope になる）。
    reseal: bool = False
    #: その outcome を作る driver（``None`` なら ``OUTCOME_DRIVERS[outcome]``）。
    #: Issue #106 PR-106-A: ``"deadline"`` は解析の期限の限界で UNKNOWN にする。
    driver: Optional[str] = None

    def to_json(self) -> dict[str, Any]:
        return {
            "step": "envelope", "outcome": self.outcome,
            "corrupt": self.corrupt, "reseal": self.reseal, "driver": self.driver,
        }


@dataclass(frozen=True)
class StuckSolverWorker:
    """Issue #106 PR-106-A（E14）: 止められない solver worker を解析の期限の中で走らせる。

    production の `ParallelSolverRunner.run_parallel` が、中断に応じない backend（能力を
    主張しない adapter）を ``budget`` 秒の期限つきで実行する。runner は止められないと
    検出したら（その事実を child の記録へ書く）worker が自分で返るまで待つので、child は
    結果を出さずに supervisor の deadline を迎える。
    """

    budget: float = 3.0

    def to_json(self) -> dict[str, Any]:
        return {"step": "stuck_solver_worker", "budget": self.budget}


@dataclass(frozen=True)
class Exit:
    """``code`` で終わる。None なら出力した canonical 結果の CLI code（無ければ 0）。"""

    code: Optional[int] = None

    def to_json(self) -> dict[str, Any]:
        return {"step": "exit", "code": self.code}


@dataclass(frozen=True)
class Stop:
    """止まったことを記録して、signal で終了させられるまで待つ。

    ``exit_on_sigterm`` / ``exit_on_sigusr1``（Issue #165）: その signal を受けたら
    自分でその code で終わる（signal 死ではなく通常終了）。
    """

    ignore_sigterm: bool = False
    exit_on_sigterm: Optional[int] = None
    exit_on_sigusr1: Optional[int] = None

    def to_json(self) -> dict[str, Any]:
        return {
            "step": "stop", "ignore_sigterm": self.ignore_sigterm,
            "exit_on_sigterm": self.exit_on_sigterm,
            "exit_on_sigusr1": self.exit_on_sigusr1,
        }


@dataclass(frozen=True)
class ChildScript:
    steps: tuple[Any, ...]
    faults: tuple[Fault, ...] = field(default=())

    def command(
        self, *, case_payload: Mapping[str, Any], occurrence_nonce: str,
        records: Path,
    ) -> tuple[str, ...]:
        spec = {
            "case_payload": dict(case_payload),
            "occurrence_nonce": occurrence_nonce,
            "records": str(records),
            "steps": [step.to_json() for step in self.steps],
            "faults": [fault.to_json() for fault in self.faults],
        }
        return (sys.executable, "-B", "-m", MODULE, json.dumps(spec, sort_keys=True))


# ---------------------------------------------------------------------------
# child 側
# ---------------------------------------------------------------------------


class FixtureFailure(Exception):
    """child の前提・事後条件が崩れた（harness の設定誤りを黙って通さない）。"""


def _prove_launch_before_exec(records: ChildRecords) -> Any:
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        CHILD_ENV_LAUNCH,
    )

    launch_path = Path(os.environ.get(CHILD_ENV_LAUNCH, ""))
    if not os.environ.get(CHILD_ENV_LAUNCH) or not launch_path.is_file():
        print("harness child: launch.json is not durable at child start", file=sys.stderr)
        raise SystemExit(LAUNCH_EVIDENCE_EXIT)
    launch_bytes = launch_path.read_bytes()
    from scripts.function_tracer_pcode.authority.process.worker_runtime import (
        ProcessWorkerRuntime,
    )

    try:
        runtime = ProcessWorkerRuntime.from_environment()
    except (OSError, TypeError, ValueError, KeyError) as exc:
        print(f"harness child: launch authority rejected: {exc!r}", file=sys.stderr)
        raise SystemExit(LAUNCH_EVIDENCE_EXIT) from exc
    if runtime is None:
        print("harness child: worker environment is absent", file=sys.stderr)
        raise SystemExit(LAUNCH_EVIDENCE_EXIT)
    evidence = {
        "pid": os.getpid(),
        "start_token": runtime.worker_start_token,
        "launch_path": str(launch_path),
        "launch_sha256": hashlib.sha256(launch_bytes).hexdigest(),
        "launch_receipt_digest": runtime.launch.receipt_digest,
        "launch_child_pid": runtime.launch.payload["child_pid"],
        "launch_child_start_token": runtime.launch.payload["child_start_token"],
        "state_present_at_start": (runtime.store.directory / "state.json").exists(),
    }
    write_json(records.identity_record, {
        "pid": records.identity.pid, "start_token": records.identity.start_token,
    })
    write_json(records.launch_evidence, evidence)
    return runtime


class _ChildContext:
    def __init__(
        self, spec: Mapping[str, Any], runtime: Any, records: ChildRecords,
    ) -> None:
        self.spec = spec
        self.runtime = runtime
        self.records = records
        self.connector: Any = None
        self._session: Any = None
        self.decompiled = 0
        self.emitted_outcome: Optional[str] = None

    @property
    def session(self) -> Any:
        if self.emitted_outcome is not None:
            raise FixtureFailure("the canonical result closed the session")
        if self._session is None:
            from scripts.function_tracer_pcode.authority.decision.production_cutover import (
                build_default_cutover_connector,
            )

            self.connector = build_default_cutover_connector()
            self._session = self.connector.begin(dict(self.spec["case_payload"]))
        return self._session


def _step_checkpoint(context: _ChildContext, _step: Mapping[str, Any]) -> None:
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.ghidra.decompilation_broker import (
        TOP_LEVEL_SOURCE_CONTRACT,
        decompile_function,
    )
    from scripts.function_tracer_pcode.tests.unit._operational_test_fixtures import (
        BrokerAnalyzer,
        BrokerDecompiler,
        Function,
        Program,
        Result,
    )

    session = context.session
    context.decompiled += 1
    manager = type("Manager", (), {"getFunctions": lambda self, forward: iter(())})()
    program = Program(manager)
    function = Function(
        entry=0x1000 * context.decompiled, name=f"f{context.decompiled}",
        program=program,
    )
    session.domain_signal_state.setdefault(
        "operational_program_binary_identities", {}
    )[id(program)] = "sha256:binary"
    analyzer = BrokerAnalyzer(
        program, BrokerDecompiler(Result(completed=True, function=function))
    )
    with production_signal_scope(session):
        decompile_function(
            analyzer, function, 60, source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )
    # broker は authority の失敗を shadow error として飲み込む。黙って checkpoint
    # 無しの run を試験したことにしない。
    if session.domain_signal_error_kinds:
        raise FixtureFailure(
            f"broker recorded shadow errors: {session.domain_signal_error_details}"
        )
    state = context.runtime.store.read_state().payload["state"]
    if state != "RESOLVED":
        raise FixtureFailure(f"checkpoint ended in {state}, not RESOLVED")


def _loop_signals(session: Any, *, execute_solver: bool) -> None:
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        active_loop_requirement_for_signal,
        emit_loop_recurrence_signal,
        execute_loop_solver_rendered_query,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
        build_input_correspondence_set,
    )
    from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
        render_loop_v2_solver_query,
    )
    from scripts.function_tracer_pcode.tests.unit._loop_test_fixtures import (
        loop_exact_fixture,
    )

    blocker, _, _, _, exact_case, summary_case, left, right = loop_exact_fixture()
    with production_signal_scope(session):
        if emit_loop_recurrence_signal(
            blocker, producer_site_manifest_id="pairwise-pending-loop-blocker",
        ) != 1:
            raise FixtureFailure("loop blocker was not committed")
        if not execute_solver:
            return
        requirement = active_loop_requirement_for_signal(
            blocker, "loop_exact_term_relation"
        )
        rendered = render_loop_v2_solver_query(
            blocker=blocker,
            requirement=requirement,
            analysis1=left,
            analysis2=right,
            input_correspondence=build_input_correspondence_set(left, right),
            case1=exact_case,
            case2=summary_case,
            pair_id="(supervisor-harness,left,right)",
            execution_identity_digest=session.identity.execution_identity_digest,
        )
        if execute_loop_solver_rendered_query(
            blocker, rendered, configured_timeout_ms=1000,
        ) != 1:
            raise FixtureFailure("loop solver execution was not committed")


def _drive_solver_timeout(session: Any) -> bool:
    """solver 境界を TIMEOUT に固定し、loop requirement をその実行で閉じる。"""

    from scripts.function_tracer_pcode.authority.lifecycle import (
        execution_authority as execution_module,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    execution_module._PINNED_PARALLEL_RUN_IMPL = (
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.TIMEOUT, elapsed_time=timeout),
        ])
    )
    _loop_signals(session, execute_solver=True)
    return True


def _drive_open_requirement(session: Any) -> bool:
    """loop requirement を開いたまま終える（solver は実行しない）。"""

    _loop_signals(session, execute_solver=False)
    return False


def _drive_error(session: Any) -> bool:
    """型付きの ERROR event を 1 つ emit する（canonical ERROR、Issue #165）。"""

    from scripts.function_tracer_pcode.authority.contracts import authority_digest
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        ErrorEventAuthority,
        EventIntent,
        EventType,
    )

    session.emit(EventIntent(
        EventType.ERROR,
        ErrorEventAuthority(
            "supervisor_harness_error",
            authority_digest({"harness_error": session.identity.result_occurrence_id}),
        ),
    ))
    return False


def _drive_deadline_limitation(session: Any) -> bool:
    """解析の期限を production の `core.deadline` で切らせ、その限界を production の帰属で
    authority の cause にする（Issue #106 PR-106-A、E6）。"""

    import time

    from scripts.function_tracer_pcode.authority.decision.limitation_attribution import (
        attribute_analysis_limitation,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.core.deadline import (
        DeadlinePolicy,
        checkpoint,
        deadline_scope,
    )
    from scripts.function_tracer_pcode.core.errors import DeadlineExceeded, pair_failure_scope

    offset = [0.0]
    policy = DeadlinePolicy(budget_seconds=1.0, clock=lambda: time.monotonic() + offset[0])
    limitation = None
    with production_signal_scope(session), pair_failure_scope(
        ("supervisor-harness",), session.identity.result_occurrence_id,
    ) as ledger:
        with deadline_scope(policy):
            offset[0] = 10.0
            try:
                checkpoint("solver")
            except DeadlineExceeded as exc:
                limitation = exc
        if limitation is None or ledger.pending_failure() is None:
            raise FixtureFailure("the deadline did not trip")
        attribution = attribute_analysis_limitation(session, limitation)
        if not attribution.is_attributed:
            raise FixtureFailure(f"deadline limitation was not attributed: {attribution.detail}")
    return False


#: canonical outcome -> (session を駆動して legacy の is_timeout を返す関数)。
OUTCOME_DRIVERS: dict[str, Callable[[Any], bool]] = {
    "TIMEOUT": _drive_solver_timeout,
    "UNKNOWN": _drive_open_requirement,
    "ERROR": _drive_error,
}

#: 名前つきの driver（``Envelope(driver=...)``）。outcome は ``Envelope.outcome`` で要求する。
NAMED_OUTCOME_DRIVERS: dict[str, Callable[[Any], bool]] = {
    "deadline": _drive_deadline_limitation,
}


def _step_envelope(context: _ChildContext, step: Mapping[str, Any]) -> None:
    from types import SimpleNamespace

    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        build_canonical_result_finalization_bundle,
        persist_canonical_result_envelope,
    )
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        attach_canonical_decision,
    )
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    requested = step["outcome"]
    named = step.get("driver")
    driver = NAMED_OUTCOME_DRIVERS.get(named) if named else OUTCOME_DRIVERS.get(requested)
    if driver is None:
        raise FixtureFailure(f"no driver produces canonical {requested} ({named})")
    session = context.session
    is_timeout = driver(session)
    evidence = context.connector.finish(
        session,
        SimpleNamespace(
            is_equivalent=None, error_message=None, failure_status=None,
            failure_message=None, unknown_reasons=[], unknown_recovery_actions=[],
            is_timeout=lambda: is_timeout,
        ),
        case_id=str(context.spec["case_payload"]),
    )
    decision = evidence.pilot_result.candidate.decision_receipt
    if decision.outcome.value != requested:
        raise FixtureFailure(
            f"production decided {decision.outcome.value}, not {requested}"
        )
    result = EquivalenceResult(
        is_equivalent=None, function1_name="f", function2_name="f",
        binary1_name="left.bin", binary2_name="right.bin",
        solver_results=ParallelResult(results=[]),
    )
    attach_canonical_decision(result, decision)
    payload = result.to_dict()
    payload["canonical_result_finalization_bundle"] = (
        build_canonical_result_finalization_bundle(
            result_payload_preimage=dict(payload), evidence=evidence, session=session, work=SealWorkBudget.for_result()
        )
    )
    envelope = persist_canonical_result_envelope(payload, work=SealWorkBudget.for_result())
    if envelope is None:
        raise FixtureFailure("canonical envelope was not persisted")
    context.emitted_outcome = requested
    if step["corrupt"] is not None:
        sealed = json.loads(envelope.read_text(encoding="utf-8"))
        value = sealed[step["corrupt"]]
        sealed[step["corrupt"]] = ("0" if value[0] != "0" else "1") + value[1:]
        if step["reseal"]:
            from scripts.function_tracer_pcode.authority.contracts import authority_digest

            sealed["envelope_digest"] = authority_digest({
                key: item for key, item in sealed.items() if key != "envelope_digest"
            })
        envelope.write_text(
            json.dumps(sealed, sort_keys=True, separators=(",", ":")) + "\n",
            encoding="utf-8",
        )
    print("\n".join((
        "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
        json.dumps(payload, ensure_ascii=False, sort_keys=True),
        "=== EQUIVALENCE_RESULT_JSON_END ===",
    )), flush=True)


def _step_exit(context: _ChildContext, step: Mapping[str, Any]) -> None:
    code = step["code"]
    if code is None:
        from scripts.function_tracer_pcode.authority.contracts import (
            CLI_EXIT_CODE_BY_OUTCOME,
            Outcome,
        )

        code = (
            0 if context.emitted_outcome is None
            else CLI_EXIT_CODE_BY_OUTCOME[Outcome(context.emitted_outcome)]
        )
    sys.stdout.flush()
    raise SystemExit(code)


def _step_stop(context: _ChildContext, step: Mapping[str, Any]) -> None:
    sys.stdout.flush()
    stop_here(
        context.records, point="step:stop", ignore_sigterm=step["ignore_sigterm"],
        exit_on_sigterm=step["exit_on_sigterm"], exit_on_sigusr1=step["exit_on_sigusr1"],
    )


def _step_stuck_solver_worker(context: _ChildContext, step: Mapping[str, Any]) -> None:
    import threading

    from scripts.function_tracer_pcode.core.deadline import DeadlinePolicy, deadline_scope
    from scripts.function_tracer_pcode.smt import parallel
    from scripts.function_tracer_pcode.smt.interface import SMTSolver

    records = context.records.directory
    never = threading.Event()

    class _Blocking(SMTSolver):
        @property
        def name(self):
            return "blocking"

        def check_availability(self):
            return True, "harness"

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            write_json(records / "stuck_worker_started.json", {"pid": os.getpid()})
            never.wait()  # 中断にも timeout にも応じない

    def _note(note, payload=None):
        write_json(records / f"{note}.json", dict(payload or {}))

    parallel.journal_note = _note
    runner = parallel.ParallelSolverRunner(timeout=30, solver_classes=[_Blocking])
    with deadline_scope(DeadlinePolicy(budget_seconds=float(step["budget"]), sub_operation_margin_seconds=0.0)):
        runner.run_parallel("(check-sat)")
    raise FixtureFailure("the runner returned while a worker could not be stopped")


STEP_HANDLERS: dict[str, Callable[[_ChildContext, Mapping[str, Any]], None]] = {
    "checkpoint": _step_checkpoint,
    "envelope": _step_envelope,
    "exit": _step_exit,
    "stop": _step_stop,
    "stuck_solver_worker": _step_stuck_solver_worker,
}


def main(arguments: list[str]) -> int:
    from scripts.function_tracer_pcode.authority.process.process_identity import (
        read_process_start_token,
    )

    spec = json.loads(arguments[0])
    # exec しても start time は変わらないので、Popen の直後に supervisor 側が
    # 記録した identity と同じものになる。
    records = HarnessRecords(Path(spec["records"])).child(
        ChildIdentity(os.getpid(), read_process_start_token(os.getpid()))
    )
    runtime = _prove_launch_before_exec(records)
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        RESULT_ENTRY_OCCURRENCE_NONCE_ENV,
    )

    os.environ[RESULT_ENTRY_OCCURRENCE_NONCE_ENV] = spec["occurrence_nonce"]
    install_publication_faults(
        [Fault.from_json(item) for item in spec["faults"]],
        role="child", store_directory=runtime.store.directory, projection=None,
        sink=records.faults, child=records,
    )
    context = _ChildContext(spec, runtime, records)
    try:
        for step in spec["steps"]:
            STEP_HANDLERS[step["step"]](context, step)
    except FixtureFailure as exc:
        print(f"harness child: fixture failure: {exc}", file=sys.stderr)
        return FIXTURE_FAILURE_EXIT
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
