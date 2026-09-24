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
（起動方式 / entry の判定 /       ``restart_supervisor`` / ``SupervisorRun`` /
 並行起動 / 孤児）                ``worker_alive`` / 孤児の後始末）
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

公開操作の契約（どの durable state で合法か / 何を保証するか / どこで判定するか）。
条件はそれぞれ 1 箇所だけで判定し、test や別 module に複製しない。

* ``supervisor_case``: いつでも。抜けるとき（例外でも）、case の invocation が
  起こした worker は全部止まっている（``terminate_leftover_workers``）。
* ``run_supervisor``: durable launch が無いときだけ（過去の invocation の有無は
  問わない）。production の FRESH_START を通って worker を起こした run を返す。
  正常に戻った run の worker はもう生きていない（``WorkerOutlivedSupervisor``）。
* ``restart_supervisor``: durable launch があるときだけ（その正しさは production
  が判定する）。production の RESUME を通って worker を起こさなかった run を
  返す。fresh start へ黙って落ちない。
  上の 2 つは、要求と durable state が合わなければ起動せずに
  ``SupervisorEntryRefused``、起動後に別の経路だったと分かれば
  ``SupervisorPathMismatch``（``_check_entry_request`` / ``_observe``）。
* 停止点（``faults`` / ``ChildScript.faults`` / ``deadline``）: crash は両方の
  entry、stop は worker の store file だけ、``ChildStopped`` と
  ``AT_CHILD_STOP`` は FRESH_START だけ。不正な要求は起動前に拒否する。要求した
  停止点に 1 つも着かなかった run と、worker が止まらなかった ``AT_CHILD_STOP``
  の run は ``SupervisorPathMismatch``（``_check_entry_request`` / ``Fault`` /
  ``_observe``）。
* ``classify(run)``: run が projection を公開し、run のあと分類の入力が変わって
  いないときだけ。その run の projection を production 分類器で分類した結果を
  返す（拒否は例外。``classify``）。
* ``worker_alive(run)``: run が worker を起こしたときだけ（起こしていなければ
  ``NoWorkerStarted``）。その worker（PID + start token）がいま生きているか。
* ``launch_evidence(case, pid)``: いつでも。その PID の process が launch 検査を
  通って書いた観測（書かなければ空。``_supervisor_records``）。

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
    pause_at,
    stop_at,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_process import (
    NoWorkerStarted,
    SupervisorEntry,
    SupervisorEntryRefused,
    SupervisorHandle,
    SupervisorPathMismatch,
    SupervisorRaised,
    SupervisorRun,
    WorkerOutlivedSupervisor,
    classification_inputs,
    restart_supervisor,
    run_supervisor,
    start_supervisor,
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
    "run_supervisor", "restart_supervisor", "worker_alive", "SupervisorEntry",
    "SupervisorEntryRefused", "SupervisorPathMismatch", "NoWorkerStarted",
    "WorkerOutlivedSupervisor", "allocate_invocation_ordinal",
    "classify", "launch_evidence", "StoreSnapshot",
    "ChildScript", "Checkpoint", "Envelope", "Exit", "Stop", "Fault",
    "FileBoundary", "ProjectionWrite", "ChildStopped", "Deadline", "crash_at",
    "stop_at", "pause_at", "start_supervisor", "SupervisorHandle",
    "LAUNCH_EVIDENCE_EXIT",
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
    #: worker の command に焼き込んだ停止点（config の一部で、restart でも同じ）。
    child_faults: tuple[Fault, ...] = ()

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
    value = SupervisorCase(
        directory, keys, identity, config,
        child_faults=child.faults if isinstance(child, ChildScript) else (),
    )
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
    _require_unchanged_inputs(run)
    config = case.config
    try:
        return classify_pair_status(
            case.pair_log, run.records.projection,
            checkpoint_root=config.checkpoint_root,
            execution_nonce=config.execution_nonce,
            supervisor_signing_key_id=config.supervisor_signing_key_id,
            supervisor_signing_key_file=config.supervisor_signing_key_file,
            worker_signing_key_id=config.worker_signing_key_id,
            worker_signing_key_file=config.worker_signing_key_file,
        )
    finally:
        # 分類の途中で入力が変わった（crash した run の生き残った worker が
        # store を書いた等）なら、その結果も拒否もこの run のものではない。
        _require_unchanged_inputs(run)


def _require_unchanged_inputs(run: SupervisorRun) -> None:
    now = classification_inputs(run.case)
    changed = sorted(
        name for name in set(now) | set(run.classification_inputs)
        if now.get(name) != run.classification_inputs.get(name)
    )
    if changed:
        raise StaleRunObservation(
            f"classification inputs changed after {run.invocation}: {changed}"
        )


def allocate_invocation_ordinal(root: Path) -> int:
    """harness の記録 root で invocation identity を 1 つ確保し、その番号を返す。

    identity 確保の並行安全性を harness 自身の test が確かめるための入口
    （記録の配置は外へ出さない）。
    """

    return HarnessRecords(Path(root)).allocate_invocation().invocation.ordinal


def launch_evidence(case: SupervisorCase, pid: int) -> tuple[Mapping[str, Any], ...]:
    """PID の worker が本処理の前に書いた launch の観測（書いた process ごと）。"""

    return tuple(
        evidence for evidence in (
            read_json(records.launch_evidence)
            for records in case.records.children_with_pid(pid)
        )
        if evidence is not None
    )
