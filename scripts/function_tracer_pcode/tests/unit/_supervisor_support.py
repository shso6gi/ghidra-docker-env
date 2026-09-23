# -*- coding: utf-8 -*-
"""Issue #163: 実 child process を起こす supervisor の共有 test harness。

test が import する入口はこの module だけ（下の module を直接 import しない）。
責務ごとに module を分け、変更の軸が 1 箇所に閉じるようにしている。

================================  =============================================
責務（変わるきっかけ）            置き場所
================================  =============================================
鍵・identity・config              ``supervisor_keys`` / ``supervisor_identity`` /
（config field / identity 規則）  ``supervisor_config``（本 module）
case（pair の寿命の資源）         ``supervisor_case``（context manager、本 module）
invocation（1 回の起動の寿命）    ``_supervisor_process``（``run_supervisor`` /
（起動方式 / 並行起動 / 孤児）    ``restart_supervisor`` / ``SupervisorRun`` /
                                  ``terminate_leftover_workers``）
run identity と記録の置き場所     ``_supervisor_records``（唯一の定義）
worker child が何をするか         ``_supervisor_child``（``ChildScript`` と step、
（checkpoint / canonical outcome）  outcome は ``OUTCOME_DRIVERS`` に 1 つずつ）
停止点（crash / stop / deadline） ``_supervisor_faults``（durable file の公開境界）
durable store の観測              ``_supervisor_store``
分類                              ``classify(run)`` → production の ``classify_pair_status``
================================  =============================================

寿命の契約:

* ``SupervisorCase`` は pair にまたがる資源（config、durable store、pair log、
  harness の記録 root）だけを持つ。「ある invocation が観測した値」は持たない。
* ``SupervisorRun`` は 1 回の invocation だけの immutable な観測で、開始時に
  確保した ``SupervisorInvocationId`` に束縛される。別 invocation の値を
  継承しない（詳細は ``_supervisor_process``）。
* 分類は run を名指す。その run が公開した projection を、その run が終わった
  時点の store / pair log と組にして production の分類器へ渡す。

harness は「状態を作る・観測する」だけで、何を期待するかは test が持つ。
supervisor の判定・store の検証・分類は production をそのまま呼び、ここで
再実装しない。production には test 用の分岐を 1 つも足さない。
"""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator, Mapping, Optional, Sequence, Union

from scripts.function_tracer_pcode.tests.unit._supervisor_child import (
    LAUNCH_EVIDENCE_EXIT,
    Checkpoint,
    ChildScript,
    Envelope,
    Exit,
    Stop,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_faults import (
    ChildStopped,
    Deadline,
    Fault,
    FileBoundary,
    ProjectionWrite,
    crash_at,
    stop_at,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_process import (
    SupervisorRaised,
    SupervisorRun,
    classification_inputs,
    restart_supervisor,
    run_supervisor,
    terminate_leftover_workers,
    worker_alive,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_records import (
    HarnessRecords,
    SupervisorInvocationId,
    read_json,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_store import StoreSnapshot

__all__ = (
    "REPO_ROOT", "SupervisorKeys", "SupervisorIdentity", "SupervisorCase",
    "SupervisorRun", "SupervisorRaised", "SupervisorInvocationId",
    "NoProjectionToClassify", "StaleRunObservation", "supervisor_keys",
    "supervisor_identity", "supervisor_config", "supervisor_case",
    "run_supervisor", "restart_supervisor", "worker_alive",
    "terminate_leftover_workers", "classify", "launch_evidence", "StoreSnapshot",
    "ChildScript", "Checkpoint", "Envelope", "Exit", "Stop", "Fault",
    "FileBoundary", "ProjectionWrite", "ChildStopped", "Deadline", "crash_at",
    "stop_at", "LAUNCH_EVIDENCE_EXIT",
)

REPO_ROOT = Path(__file__).resolve().parents[4]


# ---------------------------------------------------------------------------
# 鍵・identity・config
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SupervisorKeys:
    supervisor_key_id: str
    supervisor_key_file: Path
    worker_key_id: str
    worker_key_file: Path


def supervisor_keys(directory: Path) -> SupervisorKeys:
    """deployment 鍵（supervisor / worker で別 id）を file に置く。"""

    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    supervisor_key = directory / "supervisor.key"
    worker_key = directory / "worker.key"
    supervisor_key.write_bytes(b"s" * 32)
    worker_key.write_bytes(b"w" * 32)
    return SupervisorKeys("supervisor-key-v1", supervisor_key, "worker-key-v1", worker_key)


@dataclass(frozen=True)
class SupervisorIdentity:
    case_payload: Mapping[str, Any]
    occurrence_nonce: str
    execution_nonce: str
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    stream_id: str
    deadline_policy_digest: str


def supervisor_identity(
    case: str, *, occurrence_nonce: Optional[str] = None,
) -> SupervisorIdentity:
    """runner と同じ規則で execution identity を作る。

    child の session は ``connector.begin(case_payload)`` に occurrence nonce を
    足した payload から identity を作る（production の
    ``--print-production-execution-identity`` と同じ）。launch の identity を
    それと一致させないと、canonical 結果は launch に join しない。
    """

    from scripts.function_tracer_pcode.authority.contracts import authority_digest
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        ProductionPilotExecutionIdentity,
    )

    nonce = occurrence_nonce or f"{case}-occurrence"
    payload = {"case": case}
    identity = ProductionPilotExecutionIdentity.create({
        **payload, "result_entry_occurrence_nonce": nonce,
    })
    return SupervisorIdentity(
        case_payload=payload,
        occurrence_nonce=nonce,
        execution_nonce=f"{case}-execution",
        result_occurrence_id=identity.result_occurrence_id,
        source_snapshot_fingerprint=identity.source_snapshot_fingerprint,
        stream_id="stream-" + identity.result_occurrence_id,
        deadline_policy_digest=authority_digest({"harness_deadline_policy": case}),
    )


def supervisor_config(
    directory: Path, child_command: Sequence[str], *,
    keys: SupervisorKeys, identity: SupervisorIdentity,
    timeout: float = 60.0, kill_grace: float = 0.5,
    allow_child_exit_resolution: bool = False, **diagnostic_fields: Any,
) -> Any:
    """``SupervisorCommandConfig``。診断 field（PR-124-C）はそのまま渡す。"""

    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        SupervisorCommandConfig,
    )

    directory = Path(directory)
    return SupervisorCommandConfig(
        checkpoint_root=directory / "checkpoints",
        authority_output=directory / "authority.json",
        working_directory=REPO_ROOT,
        execution_nonce=identity.execution_nonce,
        result_occurrence_id=identity.result_occurrence_id,
        source_snapshot_fingerprint=identity.source_snapshot_fingerprint,
        stream_id=identity.stream_id,
        deadline_policy_digest=identity.deadline_policy_digest,
        supervisor_signing_key_id=keys.supervisor_key_id,
        supervisor_signing_key_file=keys.supervisor_key_file,
        worker_signing_key_id=keys.worker_key_id,
        worker_signing_key_file=keys.worker_key_file,
        timeout_seconds=timeout,
        kill_grace_seconds=kill_grace,
        child_command=tuple(child_command),
        allow_child_exit_resolution=allow_child_exit_resolution,
        **diagnostic_fields,
    )


# ---------------------------------------------------------------------------
# case の配置と後始末
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SupervisorCase:
    """pair 1 つ分の、複数の invocation にまたがる資源。"""

    directory: Path
    keys: SupervisorKeys
    identity: SupervisorIdentity
    config: Any

    @property
    def pair_log(self) -> Path:
        return self.directory / "pair.log"

    @property
    def records(self) -> HarnessRecords:
        """harness だけが読み書きする記録（production は読まない）。"""
        return HarnessRecords(self.directory / "harness")

    @property
    def store_directory(self) -> Path:
        return self.config.checkpoint_root / self.config.execution_nonce


@contextmanager
def supervisor_case(
    directory: Path, child: Union[ChildScript, Sequence[str]], *,
    case: str = "supervisor-harness", **config_fields: Any,
) -> Iterator[SupervisorCase]:
    """1 pair 分の配置を作り、抜けるときに残った worker を必ず止める。

    ``child`` は ``ChildScript``（harness の worker program）か、任意の
    command。supervisor が crash すると worker は孤児になる（#165 はそれを
    restart の前提に使う）ので、止めるのは run ごとではなくここ。
    """

    directory = Path(directory)
    records = HarnessRecords(directory / "harness")
    records.root.mkdir(parents=True, exist_ok=True)
    identity = supervisor_identity(case)
    command = (
        child.command(
            case_payload=identity.case_payload,
            occurrence_nonce=identity.occurrence_nonce,
            records=records.root,
        )
        if isinstance(child, ChildScript) else tuple(child)
    )
    keys = supervisor_keys(directory / "keys")
    config = supervisor_config(
        directory, command, keys=keys, identity=identity, **config_fields,
    )
    value = SupervisorCase(directory, keys, identity, config)
    try:
        yield value
    except BaseException:
        # test 本体の失敗を後始末の失敗で上書きしない。
        try:
            terminate_leftover_workers(value)
        except (AssertionError, OSError, ValueError, KeyError):
            pass
        raise
    terminate_leftover_workers(value)


# ---------------------------------------------------------------------------
# 分類
# ---------------------------------------------------------------------------


class NoProjectionToClassify(AssertionError):
    """分類しようとした invocation は projection を公開していない。"""


class StaleRunObservation(AssertionError):
    """その invocation のあとで durable store か pair log が変わっている。"""


def classify(run: SupervisorRun) -> Mapping[str, Any]:
    """``run`` を runner と同じ production の分類器で分類する（失敗は例外のまま返す）。

    分類器へ渡す projection は ``run`` 自身が公開した bytes で、case の
    ``authority_output`` のいまの値ではない。store と pair log はその run が
    終わった時点のままでなければならない（あとの invocation や test が変えて
    いれば ``StaleRunObservation``）。比べる入力は ``classification_inputs`` が
    決める（store / pair log / 鍵 file）。
    """

    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        classify_pair_status,
    )

    case = run.case
    if run.projection is None:
        raise NoProjectionToClassify(f"{run.invocation} published no projection")
    now = classification_inputs(case)
    changed = sorted(
        name for name in set(now) | set(run.classification_inputs)
        if now.get(name) != run.classification_inputs.get(name)
    )
    if changed:
        raise StaleRunObservation(
            f"classification inputs changed after {run.invocation}: {changed}"
        )
    config = case.config
    return classify_pair_status(
        case.pair_log, run.records.projection,
        checkpoint_root=config.checkpoint_root,
        execution_nonce=config.execution_nonce,
        supervisor_signing_key_id=config.supervisor_signing_key_id,
        supervisor_signing_key_file=config.supervisor_signing_key_file,
        worker_signing_key_id=config.worker_signing_key_id,
        worker_signing_key_file=config.worker_signing_key_file,
    )


def launch_evidence(case: SupervisorCase, pid: int) -> tuple[Mapping[str, Any], ...]:
    """PID の worker が本処理の前に書いた launch の観測（書いた process ごと）。"""

    return tuple(
        evidence for evidence in (
            read_json(records.launch_evidence)
            for records in case.records.children_with_pid(pid)
        )
        if evidence is not None
    )
