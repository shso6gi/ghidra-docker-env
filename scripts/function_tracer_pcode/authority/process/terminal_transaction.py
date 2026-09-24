"""Issue #165: store の flock の中で終端処理を 1 手進める（durable 操作の表）。

``TerminalTransaction`` は ``open_transaction``（owner の supervisor として store の
flock を 1 回取る ``DurableCheckpointStore.owned_lock``）の中でだけ作られ、同じ
flock の中で次の順に使う:

1. ``snapshot()``: store を読み直す（``terminal_snapshot``）。
2. 呼び出し側（``terminal_driver``）が ``next_step`` で 1 手を決める。
3. ``execute(step)``: その手を、**同じ読込み**の decode 済み値だけから書く。
   あるいは ``adopt(step)``: 完成した終端を store から再構成して返す。

各 durable 操作は決定的に作れる receipt / bundle だけを書く（時刻などの可変値
を署名し直さない）ので、どの公開境界で落ちても、restart で同じ bytes を書く
か、既にある同じ bytes を確かめるだけになる。操作を 1 つ足すときは
``_EXECUTORS`` に 1 行足す（run / resume の分岐は増えない）。
"""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from typing import Any, Callable, Iterator, Optional

from scripts.function_tracer_pcode.authority.process import store_layout as layout
from scripts.function_tracer_pcode.authority.process import checkpoint_archive as archive
from scripts.function_tracer_pcode.authority.process.checkpoint_vocabulary import (
    SUPERVISOR_EXIT_ERROR_KIND,
    CheckpointState,
)
from scripts.function_tracer_pcode.authority.process import terminal_evidence as evidence
from scripts.function_tracer_pcode.authority.process import terminal_recovery as recovery
from scripts.function_tracer_pcode.authority.process.canonical_envelope import (
    CanonicalEnvelope,
    canonical_resolved_receipt,
)
from scripts.function_tracer_pcode.authority.process.terminal_snapshot import (
    SnapshotContext,
    read_terminal_snapshot,
)



@dataclass(frozen=True)
class TerminalAuthority:
    """採用した終端（projection を作る材料）。"""

    status: str
    launch: Any
    child_exit: Any
    #: TIMEOUT / ERROR の durable bundle。
    bundle: Any = None
    #: RESOLVED の canonical 結果と receipt。
    envelope: Optional[CanonicalEnvelope] = None
    canonical_receipt: Any = None


@contextmanager
def open_transaction(store: Any, ownership: Any) -> Iterator["TerminalTransaction"]:
    """終端処理の 1 手（snapshot の再読・判定・書込み）を 1 回の flock で行う。"""

    with store.owned_lock(ownership):
        yield TerminalTransaction(store, ownership)


class TerminalTransaction:
    def __init__(self, store: Any, ownership: Any) -> None:
        store._assert_locked()
        self.store = store
        self.ownership = ownership

    def snapshot(
        self, *, mode: Optional[recovery.ExitMode],
        process_alive: Callable[[int, str], Optional[bool]],
    ) -> tuple[recovery.TerminalSnapshot, SnapshotContext]:
        self.store._assert_locked()
        return read_terminal_snapshot(self.store, mode=mode, process_alive=process_alive)

    def execute(self, step: recovery.Step, context: SnapshotContext) -> None:
        self.store._assert_locked()
        executor = _EXECUTORS.get(step.kind)
        if executor is None:
            raise ValueError(f"{step.kind.value} is not a durable progress operation")
        executor(self.store, step, context)

    def adopt(self, step: recovery.Step, context: SnapshotContext) -> TerminalAuthority:
        self.store._assert_locked()
        if step.kind is recovery.StepKind.ADOPT_RESOLVED:
            return TerminalAuthority(
                "RESOLVED", context.launch, context.child_exit,
                envelope=context.envelope, canonical_receipt=context.canonical_receipt,
            )
        if step.kind is recovery.StepKind.ADOPT_TIMEOUT:
            bundle = self.store.rematerialize_timeout_bundle(prefix=context.prefix)
            return TerminalAuthority("TIMEOUT", context.launch, context.child_exit, bundle)
        if step.kind is recovery.StepKind.ADOPT_ERROR:
            bundle = self.store._rematerialize_operational_error_bundle_locked(prefix=None)
            return TerminalAuthority("ERROR", context.launch, context.child_exit, bundle)
        raise ValueError(f"{step.kind.value} is not a terminal to adopt")


# ---------------------------------------------------------------------------
# progress の durable 操作（StepKind ごとに 1 つ）
# ---------------------------------------------------------------------------


def _exit_disposition(context: SnapshotContext) -> str:
    return context.child_exit.payload["child_exit_disposition"]


def _commit_pending(store: Any, step: recovery.Step, context: SnapshotContext) -> None:
    store._commit_pending_active_locked()


def _bootstrap(store: Any, step: recovery.Step, context: SnapshotContext) -> None:
    prior = (
        context.state
        if context.state is not None
        and context.state.payload["state"] == CheckpointState.RESOLVED
        else None
    )
    checkpoint, prefix = store.factory.issue_deadline_bootstrap_checkpoint(
        launch=context.launch, prior_resolved=prior,
    )
    store._persist_active_locked(checkpoint, prefix)


def _recover_ready(store: Any, step: recovery.Step, context: SnapshotContext) -> None:
    store._recover_completion_ready_locked(ready=context.state, prefix=context.prefix)


def _close_continuation(store: Any, step: recovery.Step, context: SnapshotContext) -> None:
    store._close_continuation_locked(active=context.state, prefix=context.prefix)


def _claim(store: Any, step: recovery.Step, context: SnapshotContext) -> None:
    store._claim_timeout_locked(
        active=context.state, prefix=context.prefix,
        kill_disposition=_exit_disposition(context),
    )


def _finalize_timeout(store: Any, step: recovery.Step, context: SnapshotContext) -> None:
    timeout, segment = store.factory.issue_supervisor_timeout(
        claimed=context.state, prefix=context.prefix,
    )
    store._finalize_timeout_locked(
        claimed=context.state, timeout=timeout, segment=segment, prefix=context.prefix,
    )


def _issue_canonical_resolved(
    store: Any, step: recovery.Step, context: SnapshotContext,
) -> None:
    receipt = canonical_resolved_receipt(
        context.envelope, launch=context.launch,
        child_returncode=context.child_exit.payload["child_returncode"],
    )
    store._write_json_locked(
        store.directory / layout.CANONICAL_RESOLVED_RECEIPT,
        {name: getattr(receipt, name) for name in receipt.__dataclass_fields__},
    )


def _begin_archive(store: Any, step: recovery.Step, context: SnapshotContext) -> None:
    present = archive.live_chain_members(store.directory)
    chain = store.validate_resolved_chain_members(
        archive.directory_reader(store.directory), present=present,
    )
    roles = {spec.name: spec.role for spec in archive.CHAIN_MEMBERS}
    members = []
    for name in present:
        data = (store.directory / name).read_bytes()
        members.append(evidence.ArchiveMember(
            name, roles[name], len(data), archive.sha256_bytes(data),
        ))
    anchor = evidence.child_exit_anchor(context.child_exit)
    payload = evidence.archive_payload(
        context.launch, child_exit=context.child_exit,
        checkpoint_receipt_digest=chain.checkpoint.receipt_digest,
        resolved_state_receipt_digest=chain.resolved.receipt_digest,
        anchor_state=anchor.state,
        error_kind=SUPERVISOR_EXIT_ERROR_KIND,
        error_stage=step.error_stage,
        destination=archive.history_destination(chain.resolved.receipt_digest),
        members=tuple(members),
    )
    manifest = store.factory.issue_terminal_evidence(evidence.ARCHIVE_MANIFEST_KIND, payload)
    store._atomic_write(
        store.directory / layout.ARCHIVE_INTENT,
        store._bytes(manifest), identical_ok=True,
    )


def _advance_archive(store: Any, step: recovery.Step, context: SnapshotContext) -> None:
    archive.move_remaining(
        store.directory, context.archive.payload["destination"],
        context.archive_inspection,
    )


def _finalize_error(store: Any, step: recovery.Step, context: SnapshotContext) -> None:
    store._finalize_operational_error_locked(
        launch=context.launch, error_kind=SUPERVISOR_EXIT_ERROR_KIND,
        deadline_stage=step.error_stage,
        child_exit_disposition=_exit_disposition(context), prefix=None,
    )


_EXECUTORS: dict = {
    recovery.StepKind.COMMIT_PENDING_ACTIVE: _commit_pending,
    recovery.StepKind.BOOTSTRAP_ACTIVE: _bootstrap,
    recovery.StepKind.RECOVER_READY: _recover_ready,
    recovery.StepKind.CLOSE_CONTINUATION: _close_continuation,
    recovery.StepKind.CLAIM_TIMEOUT: _claim,
    recovery.StepKind.FINALIZE_TIMEOUT: _finalize_timeout,
    recovery.StepKind.ISSUE_CANONICAL_RESOLVED: _issue_canonical_resolved,
    recovery.StepKind.BEGIN_ARCHIVE: _begin_archive,
    recovery.StepKind.ADVANCE_ARCHIVE: _advance_archive,
    recovery.StepKind.FINALIZE_ERROR: _finalize_error,
}
