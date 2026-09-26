"""Issue #165: store を lock の中で読み、終端判断の入力（事実）にする。

``read_terminal_snapshot(store, ...)`` は store の flock を持った状態で呼ぶ
（``terminal_transaction.open_transaction`` の中）。返すのは 2 つ:

* ``TerminalSnapshot``（``terminal_recovery``）: 判断に使う事実だけ。署名・
  schema・launch / D / E / A の join を検証した結果（VALID / INVALID と理由）。
* ``SnapshotContext``: 同じ読込みで得た decode 済みの receipt / prefix。
  書込み（``terminal_transaction``）はこれを使う。書込みが file を読み直す
  ときも同じ lock の中で行い、前の周の観測は使わない。

ここは読むだけで、何も書かない・判断しない（判断は ``next_step``）。読めない
file は例外で止めず、その事実を INVALID と理由にして返す（どの証拠が壊れて
いるかを INVALID の detail に残すため）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import json
from pathlib import Path
from typing import Any, Callable, Mapping, Optional

from scripts.function_tracer_pcode.authority.process import store_layout as layout
from scripts.function_tracer_pcode.authority.process import checkpoint_archive as archive
from scripts.function_tracer_pcode.authority.process.canonical_envelope import (
    CanonicalEnvelope,
    SupervisorCanonicalResultResolvedReceipt,
    canonical_resolved_receipt,
    read_canonical_envelope,
    validate_canonical_envelope,
)
from scripts.function_tracer_pcode.authority.process.checkpoint_vocabulary import (
    BOOTSTRAP_CHECKPOINT_KIND,
    OPERATIONAL_ERROR_RECEIPT_KIND,
    TIMEOUT_STATES,
    CheckpointState,
)
from scripts.function_tracer_pcode.authority.process import terminal_evidence as evidence
from scripts.function_tracer_pcode.authority.process import terminal_recovery as recovery

_READ_ERRORS = (
    OSError, UnicodeDecodeError, KeyError, TypeError, ValueError, AttributeError,
)



def _describe(exc: BaseException) -> str:
    return f"{type(exc).__name__}: {exc}"[:500]


@dataclass
class SnapshotContext:
    """``next_step`` の入力と同じ読込みで得た decode 済みの値（書込みが使う）。"""

    launch: Any = None
    deadline: Any = None
    child_exit: Any = None
    archive: Any = None
    archive_members: tuple = ()
    archive_inspection: Optional[archive.UnionInspection] = None
    pending_checkpoint: Any = None
    state: Any = None
    checkpoint: Any = None
    prefix: Any = None
    envelope: Optional[CanonicalEnvelope] = None
    canonical_receipt: Any = None
    fingerprint: str = ""
    history: dict = field(default_factory=dict)


def store_fingerprint(directory: Path) -> str:
    """store の durable な file 集合（相対 path と bytes）の digest（進捗の判定）。"""

    digest = hashlib.sha256()
    directory = Path(directory)
    for path in sorted(directory.rglob("*")):
        relative = path.relative_to(directory)
        if path.is_file() and not any(part.startswith(".") for part in relative.parts):
            digest.update(relative.as_posix().encode("utf-8") + b"\0")
            digest.update(hashlib.sha256(path.read_bytes()).digest())
    return digest.hexdigest()


def _decode_file(store: Any, path: Path) -> Any:
    return store.factory.decode(json.loads(path.read_text(encoding="utf-8")))


# ---------------------------------------------------------------------------
# canonical 結果
# ---------------------------------------------------------------------------


def _read_canonical(
    store: Any, context: SnapshotContext, exit_fact: recovery.ExitFact,
) -> recovery.CanonicalFact:
    envelope_path = store.directory / layout.RESULT_ENVELOPE
    receipt_path = store.directory / layout.CANONICAL_RESOLVED_RECEIPT
    presence = recovery.Presence
    envelope_presence, sha, cli_rc, detail = presence.ABSENT, None, None, None
    if envelope_path.exists():
        # 検証する bytes と E と照合する digest は同じ 1 回の読込みから取る。契約の上限の外の
        # file は読み切らずに無効（Issue #110）。
        read = read_canonical_envelope(envelope_path)
        sha = read.sha256
        try:
            context.envelope = validate_canonical_envelope(
                read.require_within_contract(), launch=context.launch,
                validate_bundle=store.factory.validate_child_canonical_bundle,
            )
        except _READ_ERRORS as exc:
            envelope_presence, detail = presence.INVALID, _describe(exc)
        else:
            envelope_presence, cli_rc = presence.VALID, context.envelope.cli_returncode
    receipt_presence = presence.ABSENT
    if receipt_path.exists():
        receipt_presence = presence.INVALID
        try:
            stored = json.loads(receipt_path.read_text(encoding="utf-8"))
            receipt = SupervisorCanonicalResultResolvedReceipt(**stored)
            receipt.validate()
            if context.envelope is None or exit_fact.presence is not presence.VALID:
                raise ValueError(
                    "canonical resolved receipt has no valid envelope and exit to join"
                )
            expected = canonical_resolved_receipt(
                context.envelope, launch=context.launch,
                child_returncode=exit_fact.returncode,
            )
            if receipt != expected:
                raise ValueError(
                    "canonical resolved receipt differs from the envelope and the "
                    "observed child exit"
                )
        except _READ_ERRORS as exc:
            detail = _describe(exc)
        else:
            receipt_presence = presence.VALID
            context.canonical_receipt = receipt
    return recovery.CanonicalFact(
        receipt=receipt_presence, envelope=envelope_presence,
        envelope_sha256=sha, envelope_cli_returncode=cli_rc, detail=detail,
    )


# ---------------------------------------------------------------------------
# D / E / A
# ---------------------------------------------------------------------------


def _read_deadline(store: Any, context: SnapshotContext) -> recovery.Fact:
    try:
        receipt = store._read_terminal_evidence_locked(evidence.DEADLINE_RECEIPT_KIND)
        if receipt is None:
            return recovery.Fact()
        evidence.validate_deadline(receipt, context.launch)
    except _READ_ERRORS as exc:
        return recovery.Fact(recovery.Presence.INVALID, detail=_describe(exc))
    context.deadline = receipt
    return recovery.Fact(recovery.Presence.VALID, receipt.receipt_digest)


def _read_child_exit(
    store: Any, context: SnapshotContext, mode: Optional[recovery.ExitMode],
) -> recovery.ExitFact:
    try:
        receipt = store._read_terminal_evidence_locked(evidence.CHILD_EXIT_RECEIPT_KIND)
        if receipt is None:
            return recovery.ExitFact()
        evidence.validate_child_exit(receipt, context.launch, context.deadline)
        if mode is not None and receipt.payload["exit_mode"] != mode.value:
            raise evidence.TerminalEvidenceInvalid(
                "child exit was recorded under a different exit mode"
            )
    except _READ_ERRORS as exc:
        return recovery.ExitFact(recovery.Presence.INVALID, detail=_describe(exc))
    context.child_exit = receipt
    payload = receipt.payload
    return recovery.ExitFact(
        recovery.Presence.VALID, receipt.receipt_digest,
        returncode=payload["child_returncode"],
        disposition=payload["child_exit_disposition"],
        deadline_digest=payload["deadline_receipt_digest"],
        envelope_sha256=payload["envelope_observation"]["sha256"],
        anchor=evidence.child_exit_anchor(receipt),
        mode=payload["exit_mode"],
    )


def _read_archive(store: Any, context: SnapshotContext) -> recovery.ArchiveFact:
    presence = recovery.Presence
    try:
        receipt = store._read_terminal_evidence_locked(evidence.ARCHIVE_MANIFEST_KIND)
        if receipt is None:
            return recovery.ArchiveFact()
        if context.child_exit is None:
            raise ValueError("archive manifest exists without a valid child exit")
        evidence.validate_archive(receipt, context.launch, context.child_exit)
    except _READ_ERRORS as exc:
        return recovery.ArchiveFact(presence.INVALID, detail=_describe(exc))
    context.archive = receipt
    members = evidence.archive_members(receipt)
    context.archive_members = members
    payload = receipt.payload
    fact = dict(
        presence=presence.VALID, digest=receipt.receipt_digest,
        checkpoint_digest=payload["checkpoint_receipt_digest"],
        resolved_digest=payload["resolved_state_receipt_digest"],
        stage=payload["error_stage"],
    )
    destination = payload["destination"]
    try:
        inspection = archive.inspect_union(store.directory, members, destination)
        chain = store.validate_resolved_chain_members(
            archive.union_reader(store.directory, destination, inspection),
            present=tuple(member.name for member in members),
        )
        if (
            chain.checkpoint.receipt_digest != payload["checkpoint_receipt_digest"]
            or chain.resolved.receipt_digest != payload["resolved_state_receipt_digest"]
        ):
            raise archive.ArchiveConflict("archived chain differs from the manifest")
        # A が固定していない live chain（anchor 外の新しい chain）は上書きしない。
        names = {member.name for member in members}
        foreign = [
            name for name in archive.live_chain_members(store.directory)
            if name not in names
        ]
        if foreign or store._pending_active_path.exists():
            raise archive.ArchiveConflict(
                f"a live chain outside the archive manifest exists: {foreign}"
            )
    except _READ_ERRORS as exc:
        return recovery.ArchiveFact(
            **fact, union=recovery.UnionState.CONFLICT, detail=_describe(exc),
        )
    context.archive_inspection = inspection
    return recovery.ArchiveFact(
        **fact,
        union=(
            recovery.UnionState.COMPLETE if inspection.complete
            else recovery.UnionState.PARTIAL
        ),
    )


# ---------------------------------------------------------------------------
# checkpoint chain
# ---------------------------------------------------------------------------


def _read_pending(store: Any, context: SnapshotContext) -> recovery.PendingFact:
    if not store._pending_active_path.exists():
        return recovery.PendingFact()
    try:
        checkpoint, prefix, _stream, _bytes = store._decode_active_transaction_locked()
        transaction = json.loads(
            store._pending_active_path.read_text(encoding="utf-8")
        )["transaction_digest"]
    except _READ_ERRORS as exc:
        return recovery.PendingFact(recovery.Presence.INVALID, detail=_describe(exc))
    context.pending_checkpoint = checkpoint
    return recovery.PendingFact(
        recovery.Presence.VALID, transaction,
        checkpoint_digest=checkpoint.receipt_digest,
        prior_resolved_digest=checkpoint.payload.get("prior_resolved_receipt_digest"),
        is_bootstrap=checkpoint.receipt_kind == BOOTSTRAP_CHECKPOINT_KIND,
    )


def _in_transaction_predecessor(store: Any) -> recovery.LiveChainFact:
    """pending transaction の途中: まだ live にある前任 RESOLVED の identity。"""

    kind = recovery.LiveKind.IN_TRANSACTION
    state_path = store.directory / layout.STATE
    if not state_path.exists():
        return recovery.LiveChainFact(kind)
    try:
        state = store.read_state()
        if state.payload["state"] != CheckpointState.RESOLVED:
            return recovery.LiveChainFact(kind, state=state.payload["state"],
                                          state_digest=state.receipt_digest)
        ready_path = store.directory / layout.READY
        if not ready_path.exists():
            ready_path = (
                store.directory / archive.history_destination(state.receipt_digest)
                / layout.READY
            )
        ready = _decode_file(store, ready_path)
    except _READ_ERRORS:
        return recovery.LiveChainFact(kind)
    return recovery.LiveChainFact(
        kind, checkpoint_digest=ready.payload["prior_state_receipt_digest"],
        state=CheckpointState.RESOLVED.value, state_digest=state.receipt_digest,
    )


def _read_live(store: Any, context: SnapshotContext) -> recovery.LiveChainFact:
    presence = recovery.Presence
    members = archive.live_chain_members(store.directory)
    if layout.STATE not in members:
        if not members:
            return recovery.LiveChainFact()
        return recovery.LiveChainFact(
            recovery.LiveKind.INVALID,
            detail=f"chain members without state: {list(members)}",
        )
    try:
        state = store.read_state()
        checkpoint = _decode_file(store, store.directory / layout.CHECKPOINT)
        prefix = store.rematerialize_active_prefix()
        if checkpoint.payload["launch_receipt_digest"] != context.launch.receipt_digest:
            raise ValueError("live checkpoint does not join the launch")
        value = state.payload["state"]
        continuation = presence.ABSENT
        kill_disposition = None
        if value == CheckpointState.ACTIVE:
            if state.receipt_digest != checkpoint.receipt_digest:
                raise ValueError("ACTIVE state is not the live checkpoint")
            if (store.directory / layout.CONTINUATION).exists():
                durable, _ = store.rematerialize_worker_continuation(prefix=prefix)
                if durable.payload["checkpoint_receipt_digest"] != checkpoint.receipt_digest:
                    raise ValueError("live continuation continues another checkpoint")
                continuation = presence.VALID
            claimed_path = store.directory / layout.CLAIMED
            if claimed_path.exists():
                claimed = _decode_file(store, claimed_path)
                if (
                    claimed.payload["state"] != CheckpointState.TIMED_OUT_CLAIMED
                    or claimed.payload["prior_state_receipt_digest"] != state.receipt_digest
                ):
                    raise ValueError("claimed.json does not claim the live ACTIVE state")
                kill_disposition = claimed.payload["kill_disposition"]
        elif value == CheckpointState.COMPLETION_READY:
            durable, _ = store.rematerialize_worker_continuation(prefix=prefix)
            if (
                state.payload["prior_state_receipt_digest"] != checkpoint.receipt_digest
                or state.payload["continuation_digest"] != durable.receipt_digest
            ):
                raise ValueError("READY state does not close the live checkpoint")
            continuation = presence.VALID
        elif value == CheckpointState.RESOLVED:
            chain = store.validate_resolved_chain_members(
                archive.directory_reader(store.directory), present=members,
            )
            if chain.checkpoint.receipt_digest != checkpoint.receipt_digest:
                raise ValueError("RESOLVED chain differs from the live checkpoint")
            continuation = presence.VALID
        elif value == CheckpointState.TIMED_OUT_CLAIMED:
            claimed = _decode_file(store, store.directory / layout.CLAIMED)
            if (
                state.payload["prior_state_receipt_digest"] != checkpoint.receipt_digest
                or claimed.receipt_digest != state.receipt_digest
            ):
                raise ValueError("claimed state is not the durable claim")
            kill_disposition = state.payload["kill_disposition"]
        elif value == CheckpointState.TIMED_OUT:
            claimed = _decode_file(store, store.directory / layout.CLAIMED)
            if (
                claimed.payload["prior_state_receipt_digest"] != checkpoint.receipt_digest
                or state.payload["prior_state_receipt_digest"] != claimed.receipt_digest
            ):
                raise ValueError("TIMED_OUT state does not close the durable claim")
            kill_disposition = claimed.payload["kill_disposition"]
        else:
            raise ValueError(f"live state {value!r} is not sealed")
    except _READ_ERRORS as exc:
        return recovery.LiveChainFact(recovery.LiveKind.INVALID, detail=_describe(exc))
    context.state, context.checkpoint, context.prefix = state, checkpoint, prefix
    return recovery.LiveChainFact(
        recovery.LiveKind.CHAIN, checkpoint_digest=checkpoint.receipt_digest,
        is_bootstrap=checkpoint.receipt_kind == BOOTSTRAP_CHECKPOINT_KIND,
        prior_resolved_digest=checkpoint.payload.get("prior_resolved_receipt_digest"),
        state=value, state_digest=state.receipt_digest,
        continuation=continuation, kill_disposition=kill_disposition,
    )


def _read_timeout(
    store: Any, context: SnapshotContext, live: recovery.LiveChainFact,
) -> recovery.TimeoutFact:
    members = frozenset(
        name for name in layout.TIMEOUT_MEMBERS if (store.directory / name).exists()
    )
    finalize_members = members - {layout.CLAIMED}
    if finalize_members and live.state not in TIMEOUT_STATES:
        return recovery.TimeoutFact(
            members, detail="timeout members exist before the claim is durable",
        )
    if live.state != CheckpointState.TIMED_OUT:
        return recovery.TimeoutFact(members)
    try:
        bundle = store.rematerialize_timeout_bundle(prefix=context.prefix)
    except _READ_ERRORS as exc:
        return recovery.TimeoutFact(members, detail=_describe(exc))
    return recovery.TimeoutFact(members, complete=True, bundle_digest=bundle.bundle_digest)


def _read_error(store: Any, context: SnapshotContext) -> recovery.ErrorFact:
    members = frozenset(
        name for name in layout.ERROR_MEMBERS if (store.directory / name).exists()
    )
    if not members:
        return recovery.ErrorFact()
    stage = disposition = None
    try:
        if layout.OPERATIONAL_ERROR in members:
            error = _decode_file(store, store.directory / layout.OPERATIONAL_ERROR)
            if (
                error.receipt_kind != OPERATIONAL_ERROR_RECEIPT_KIND
                or error.payload["launch_receipt_digest"] != context.launch.receipt_digest
            ):
                raise ValueError("operational error receipt does not join the launch")
            stage = error.payload["deadline_stage"]
            disposition = error.payload["child_exit_disposition"]
        if members != frozenset(layout.ERROR_MEMBERS):
            return recovery.ErrorFact(members, stage=stage, disposition=disposition)
        bundle = store._rematerialize_operational_error_bundle_locked(prefix=None)
    except _READ_ERRORS as exc:
        return recovery.ErrorFact(members, stage=stage, disposition=disposition,
                                  detail=_describe(exc))
    return recovery.ErrorFact(
        members, complete=True, stage=stage, disposition=disposition,
        bundle_digest=bundle.bundle_digest,
    )


def _read_history(store: Any) -> dict:
    """``checkpoint-history`` の chain（読めたものだけ。無関係な古い chain も含む）。"""

    history: dict = {}
    root = store.directory / layout.HISTORY_DIRECTORY
    if not root.is_dir():
        return history
    for directory in sorted(root.iterdir()):
        try:
            state = _decode_file(store, directory / layout.STATE)
            checkpoint = _decode_file(store, directory / layout.CHECKPOINT)
        except _READ_ERRORS:
            continue
        if state.receipt_digest == directory.name:
            history[directory.name] = checkpoint.receipt_digest
    return history


# ---------------------------------------------------------------------------
# 入口
# ---------------------------------------------------------------------------


def read_terminal_snapshot(
    store: Any, *, mode: Optional[recovery.ExitMode],
    process_alive: Callable[[int, str], Optional[bool]],
) -> tuple[recovery.TerminalSnapshot, SnapshotContext]:
    """``mode`` は supervisor の設定（E の記録と違えば E を INVALID にする）。

    None なら E に記録された mode で読む（分類器: supervisor と同じ判断を、
    mode を推測せずに行う）。E が無い store は mode に依らず INVALID になる。
    """
    store._assert_locked()
    requested_mode = mode
    mode = recovery.ExitMode.CANONICAL_RESULT_REQUIRED if mode is None else mode
    context = SnapshotContext(fingerprint=store_fingerprint(store.directory))
    try:
        context.launch = store._read_launch()
    except _READ_ERRORS as exc:
        invalid = recovery.Fact(recovery.Presence.INVALID, detail=_describe(exc))
        return recovery.TerminalSnapshot(
            mode=mode, launch=invalid, deadline=recovery.Fact(),
            child_exit=recovery.ExitFact(), child_alive=None,
            pending=recovery.PendingFact(), live=recovery.LiveChainFact(),
            timeout=recovery.TimeoutFact(), error=recovery.ErrorFact(),
            archive=recovery.ArchiveFact(), canonical=recovery.CanonicalFact(),
        ), context
    deadline = _read_deadline(store, context)
    child_exit = _read_child_exit(store, context, requested_mode)
    if child_exit.mode is not None:
        mode = recovery.ExitMode(child_exit.mode)
    archive_fact = _read_archive(store, context)
    pending = _read_pending(store, context)
    if archive_fact.presence is recovery.Presence.VALID:
        live = recovery.LiveChainFact(
            recovery.LiveKind.ARCHIVING
            if archive_fact.union is recovery.UnionState.PARTIAL
            else recovery.LiveKind.NONE
        )
    elif pending.presence is recovery.Presence.VALID:
        live = _in_transaction_predecessor(store)
    else:
        live = _read_live(store, context)
    timeout = _read_timeout(store, context, live)
    error = _read_error(store, context)
    canonical = _read_canonical(store, context, child_exit)
    context.history = _read_history(store)
    launch_payload = context.launch.payload
    snapshot = recovery.TerminalSnapshot(
        mode=mode,
        launch=recovery.Fact(recovery.Presence.VALID, context.launch.receipt_digest),
        deadline=deadline, child_exit=child_exit,
        child_alive=process_alive(
            launch_payload["child_pid"], launch_payload["child_start_token"],
        ),
        pending=pending, live=live, timeout=timeout, error=error,
        archive=archive_fact, canonical=canonical, history=dict(context.history),
    )
    return snapshot, context
