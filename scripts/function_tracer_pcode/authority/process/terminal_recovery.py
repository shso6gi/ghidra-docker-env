"""Issue #165: durable snapshot から次の 1 手を決める純関数（終端の復旧判断）。

``next_step(snapshot)`` は I/O をしない。入力は ``terminal_snapshot`` が store の
lock の中で読んだ事実（署名・schema・launch / D / E / A の join は検証済み）で、
出力は「どの終端を採用するか」「どの durable 操作を 1 つ進めるか」
「なぜ INVALID か」のどれか 1 つ。書込みは driver（``terminal_driver``）と
store が行い、その操作は lock の中で前提を読み直す。

判定の順序（計画 v5 §6.4 / §6.5。変えない）:

1. **validation**: 読めない・署名が合わない・schema / join が合わない
   evidence があれば INVALID。
2. **authority conflict**: 並び立たない終端・証拠（ERROR と TIMEOUT、
   RESOLVED と D、D の無い timeout 物件、anchor 外の live chain、
   E と生きている child の矛盾 …）があれば INVALID。**完成した終端が
   あってもここが先**。
3. **existing valid terminal**: 完成した終端を採用する。
4. **progress**: evidence の家族（deadline / 自然終了）と mode ごとに、
   durable state を 1 つ進める操作を返す。
5. それ以外は INVALID（どの証拠が足りないかを code と detail に書く）。

新しい終了の事情を足すときは、ここに行を 1 つ足す（``run`` / ``_resume`` /
deadline の関数へ分岐を複製しない）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Mapping, Optional

from scripts.function_tracer_pcode.authority.process.checkpoint_vocabulary import (
    TIMEOUT_STATES,
    CheckpointState,
    ErrorStage,
)
from scripts.function_tracer_pcode.authority.process.terminal_evidence import (
    EXIT_MODE_CANONICAL_RESULT_REQUIRED,
    EXIT_MODE_SUPERVISOR_ONLY,
    ANCHOR_CHAIN,
    ANCHOR_NONE,
    ANCHOR_PENDING_ACTIVE,
    ANCHOR_UNREADABLE,
    CheckpointAnchor,
)



class Presence(str, Enum):
    ABSENT = "ABSENT"
    VALID = "VALID"
    INVALID = "INVALID"


class ExitMode(str, Enum):
    """child の自然終了をどう終端へ写すか（``allow_child_exit_resolution``）。"""

    #: runner の mode: 検証済み canonical 結果（envelope + CLI join）だけが終端。
    CANONICAL_RESULT_REQUIRED = EXIT_MODE_CANONICAL_RESULT_REQUIRED
    #: supervisor だけで終端を決める mode: child の結果は採用せず ERROR。
    SUPERVISOR_ONLY = EXIT_MODE_SUPERVISOR_ONLY


class LiveKind(str, Enum):
    NONE = "NONE"
    CHAIN = "CHAIN"
    #: pending-active transaction の途中（前の chain の退避・新 chain の書込み）。
    IN_TRANSACTION = "IN_TRANSACTION"
    #: A の archive 途中（live / history に分かれている）。
    ARCHIVING = "ARCHIVING"
    INVALID = "INVALID"


class UnionState(str, Enum):
    PARTIAL = "PARTIAL"
    COMPLETE = "COMPLETE"
    CONFLICT = "CONFLICT"


# ---------------------------------------------------------------------------
# snapshot の事実（``terminal_snapshot`` が作る。検証済みの値だけを持つ）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Fact:
    presence: Presence = Presence.ABSENT
    digest: Optional[str] = None
    detail: Optional[str] = None


@dataclass(frozen=True)
class ExitFact(Fact):
    returncode: Optional[int] = None
    disposition: Optional[str] = None
    deadline_digest: Optional[str] = None
    envelope_sha256: Optional[str] = None
    anchor: Optional[CheckpointAnchor] = None
    #: supervisor が E を書いたときの exit mode（``TerminalSnapshot.mode`` の根拠）。
    mode: Optional[str] = None


@dataclass(frozen=True)
class PendingFact(Fact):
    checkpoint_digest: Optional[str] = None
    prior_resolved_digest: Optional[str] = None
    is_bootstrap: bool = False


@dataclass(frozen=True)
class LiveChainFact:
    """live の checkpoint chain。

    ``IN_TRANSACTION`` のときも、``state.json`` がまだ live にあれば（pending
    transaction が前任の chain を退避している途中）その chain の
    ``checkpoint_digest`` / ``state`` / ``state_digest`` を持つ。
    """

    kind: LiveKind = LiveKind.NONE
    checkpoint_digest: Optional[str] = None
    is_bootstrap: bool = False
    prior_resolved_digest: Optional[str] = None
    state: Optional[str] = None
    state_digest: Optional[str] = None
    continuation: Presence = Presence.ABSENT
    #: TIMED_OUT_CLAIMED / TIMED_OUT の chain が署名した kill disposition。
    kill_disposition: Optional[str] = None
    detail: Optional[str] = None


@dataclass(frozen=True)
class TimeoutFact:
    #: ``claimed.json`` / ``timeout.json`` / ``terminal-*.json`` のうち live にある名前。
    members: frozenset = frozenset()
    #: state が TIMED_OUT で、bundle が store から再構成できる。
    complete: bool = False
    bundle_digest: Optional[str] = None
    detail: Optional[str] = None


@dataclass(frozen=True)
class ErrorFact:
    #: ``operational-error*.json`` のうち live にある名前。
    members: frozenset = frozenset()
    #: 4 member が揃い bundle が再構成できる。
    complete: bool = False
    #: ``operational-error.json`` が読めればその stage / disposition。
    stage: Optional[str] = None
    disposition: Optional[str] = None
    bundle_digest: Optional[str] = None
    detail: Optional[str] = None


@dataclass(frozen=True)
class ArchiveFact(Fact):
    checkpoint_digest: Optional[str] = None
    resolved_digest: Optional[str] = None
    stage: Optional[str] = None
    union: Optional[UnionState] = None


@dataclass(frozen=True)
class CanonicalFact:
    #: ``canonical-resolved-receipt.json``（VALID = envelope・E の rc と join 済み）。
    receipt: Presence = Presence.ABSENT
    #: ``canonical-result-envelope.json``（VALID = 封と bundle 署名、launch join）。
    envelope: Presence = Presence.ABSENT
    envelope_sha256: Optional[str] = None
    #: envelope の outcome に対応する CLI の exit code（envelope VALID のときだけ）。
    envelope_cli_returncode: Optional[int] = None
    detail: Optional[str] = None


@dataclass(frozen=True)
class TerminalSnapshot:
    mode: ExitMode
    launch: Fact
    deadline: Fact
    child_exit: ExitFact
    #: launch の child（PID + start token）が今も生きているか（読めなければ None）。
    child_alive: Optional[bool]
    pending: PendingFact
    live: LiveChainFact
    timeout: TimeoutFact
    error: ErrorFact
    archive: ArchiveFact
    canonical: CanonicalFact
    #: ``checkpoint-history/<resolved digest>`` -> その chain の checkpoint digest。
    history: Mapping[str, str] = field(default_factory=dict)


# ---------------------------------------------------------------------------
# 判定の結果
# ---------------------------------------------------------------------------


class StepKind(str, Enum):
    ADOPT_RESOLVED = "ADOPT_RESOLVED"
    ADOPT_TIMEOUT = "ADOPT_TIMEOUT"
    ADOPT_ERROR = "ADOPT_ERROR"
    INVALID = "INVALID"
    COMMIT_PENDING_ACTIVE = "COMMIT_PENDING_ACTIVE"
    BOOTSTRAP_ACTIVE = "BOOTSTRAP_ACTIVE"
    RECOVER_READY = "RECOVER_READY"
    CLOSE_CONTINUATION = "CLOSE_CONTINUATION"
    CLAIM_TIMEOUT = "CLAIM_TIMEOUT"
    FINALIZE_TIMEOUT = "FINALIZE_TIMEOUT"
    ISSUE_CANONICAL_RESOLVED = "ISSUE_CANONICAL_RESOLVED"
    BEGIN_ARCHIVE = "BEGIN_ARCHIVE"
    ADVANCE_ARCHIVE = "ADVANCE_ARCHIVE"
    FINALIZE_ERROR = "FINALIZE_ERROR"


TERMINAL_STEPS = frozenset({
    StepKind.ADOPT_RESOLVED, StepKind.ADOPT_TIMEOUT, StepKind.ADOPT_ERROR,
    StepKind.INVALID,
})


class InvalidCode(str, Enum):
    """INVALID projection の ``error_code``（どの証拠が足りない / 矛盾するか）。"""

    TERMINAL_EVIDENCE_INVALID = "TERMINAL_EVIDENCE_INVALID"
    TERMINAL_AUTHORITY_CONFLICT = "TERMINAL_AUTHORITY_CONFLICT"
    ANCHOR_OUTSIDE_LIVE_CHAIN = "ANCHOR_OUTSIDE_LIVE_CHAIN"
    ARCHIVE_UNION_CONFLICT = "ARCHIVE_UNION_CONFLICT"
    DEADLINE_WITHOUT_EXIT_OBSERVATION = "DEADLINE_WITHOUT_EXIT_OBSERVATION"
    EXIT_NOT_OBSERVED = "EXIT_NOT_OBSERVED"
    TERMINAL_WITHOUT_EXIT_OBSERVATION = "TERMINAL_WITHOUT_EXIT_OBSERVATION"
    CANONICAL_CHILD_RESULT_INVALID = "CANONICAL_CHILD_RESULT_INVALID"
    ACTIVE_EXIT_STAGE_UNSEALED = "ACTIVE_EXIT_STAGE_UNSEALED"
    DURABLE_STATE_INCOMPLETE = "DURABLE_STATE_INCOMPLETE"


@dataclass(frozen=True)
class Step:
    kind: StepKind
    invalid_code: Optional[InvalidCode] = None
    detail: Optional[str] = None
    #: FINALIZE_ERROR の stage。
    error_stage: Optional[str] = None

    @property
    def terminal(self) -> bool:
        return self.kind in TERMINAL_STEPS


def _invalid(code: InvalidCode, detail: str) -> Step:
    return Step(StepKind.INVALID, invalid_code=code, detail=detail)


def _progress(kind: StepKind, **fields: Optional[str]) -> Step:
    return Step(kind, **fields)


# ---------------------------------------------------------------------------
# 1. validation
# ---------------------------------------------------------------------------


def _validation(s: TerminalSnapshot) -> Optional[Step]:
    checks = (
        ("launch", s.launch.presence is not Presence.VALID, s.launch.detail),
        ("deadline", s.deadline.presence is Presence.INVALID, s.deadline.detail),
        ("child exit", s.child_exit.presence is Presence.INVALID, s.child_exit.detail),
        ("archive manifest", s.archive.presence is Presence.INVALID, s.archive.detail),
        ("pending ACTIVE transaction", s.pending.presence is Presence.INVALID, s.pending.detail),
        ("live checkpoint chain", s.live.kind is LiveKind.INVALID, s.live.detail),
        ("canonical resolved receipt", s.canonical.receipt is Presence.INVALID, s.canonical.detail),
        ("timeout bundle", s.timeout.detail is not None, s.timeout.detail),
        ("error bundle", s.error.detail is not None, s.error.detail),
        (
            "child exit anchor",
            s.child_exit.presence is Presence.VALID
            and s.child_exit.anchor is not None
            and s.child_exit.anchor.kind == ANCHOR_UNREADABLE,
            None if s.child_exit.anchor is None else s.child_exit.anchor.detail,
        ),
    )
    for name, failed, detail in checks:
        if failed:
            return _invalid(
                InvalidCode.TERMINAL_EVIDENCE_INVALID, f"{name}: {detail or 'invalid'}",
            )
    return None


# ---------------------------------------------------------------------------
# 2. authority conflict
# ---------------------------------------------------------------------------


def _has_timeout_artifacts(s: TerminalSnapshot) -> bool:
    return bool(s.timeout.members) or s.live.state in TIMEOUT_STATES


def _has_error_artifacts(s: TerminalSnapshot) -> bool:
    return bool(s.error.members) or s.archive.presence is Presence.VALID


def _has_resolved_artifacts(s: TerminalSnapshot) -> bool:
    return s.canonical.receipt is Presence.VALID


def _supervisor_bootstrap_present(s: TerminalSnapshot) -> bool:
    return (
        (s.live.kind is LiveKind.CHAIN and s.live.is_bootstrap)
        or (s.pending.presence is Presence.VALID and s.pending.is_bootstrap)
    )


def _allowed_bootstrap_priors(s: TerminalSnapshot, anchor: CheckpointAnchor) -> set:
    """anchor の chain が閉じた resolved state（bootstrap の前任として正しいもの）。"""

    if anchor.kind == ANCHOR_NONE:
        return {None}
    if anchor.kind != ANCHOR_CHAIN:
        return set()
    priors = {
        resolved for resolved, checkpoint in s.history.items()
        if checkpoint == anchor.checkpoint_receipt_digest
    }
    # 前任がまだ live にある（bootstrap の commit が前任を退避している途中も含む）。
    if (
        s.live.kind in {LiveKind.CHAIN, LiveKind.IN_TRANSACTION}
        and not s.live.is_bootstrap
        and s.live.checkpoint_digest == anchor.checkpoint_receipt_digest
        and s.live.state == CheckpointState.RESOLVED
    ):
        priors.add(s.live.state_digest)
    return priors


def _attribution(s: TerminalSnapshot, *, deadline_family: bool) -> Optional[Step]:
    """live chain / pending が E の anchor（とその派生）に属すること。"""

    anchor = s.child_exit.anchor
    if anchor is None:
        return None
    anchored = (
        {anchor.checkpoint_receipt_digest}
        if anchor.kind in {ANCHOR_CHAIN, ANCHOR_PENDING_ACTIVE} else set()
    )
    priors = _allowed_bootstrap_priors(s, anchor) if deadline_family else set()

    def belongs(checkpoint: Optional[str], is_bootstrap: bool, prior: Optional[str]) -> bool:
        if is_bootstrap:
            return prior in priors
        return checkpoint in anchored

    if s.pending.presence is Presence.VALID and not belongs(
        s.pending.checkpoint_digest, s.pending.is_bootstrap,
        s.pending.prior_resolved_digest,
    ):
        return _invalid(
            InvalidCode.ANCHOR_OUTSIDE_LIVE_CHAIN,
            "pending ACTIVE transaction is not the chain observed at child exit",
        )
    if (
        anchor.kind == ANCHOR_PENDING_ACTIVE
        and s.pending.presence is Presence.VALID
        and not s.pending.is_bootstrap
        and s.pending.digest != anchor.transaction_digest
    ):
        return _invalid(
            InvalidCode.ANCHOR_OUTSIDE_LIVE_CHAIN,
            "pending ACTIVE transaction differs from the one observed at child exit",
        )
    if s.live.kind is LiveKind.CHAIN and not belongs(
        s.live.checkpoint_digest, s.live.is_bootstrap, s.live.prior_resolved_digest,
    ):
        return _invalid(
            InvalidCode.ANCHOR_OUTSIDE_LIVE_CHAIN,
            "live checkpoint chain is not the chain observed at child exit",
        )
    if (
        s.live.kind is LiveKind.NONE
        and s.pending.presence is Presence.ABSENT
        and anchored
        and s.archive.presence is Presence.ABSENT
        and not _has_error_artifacts(s)
    ):
        return _invalid(
            InvalidCode.DURABLE_STATE_INCOMPLETE,
            "the chain observed at child exit is no longer live and was not archived",
        )
    return None


def _conflict(s: TerminalSnapshot) -> Optional[Step]:
    deadline = s.deadline.presence is Presence.VALID
    exited = s.child_exit.presence is Presence.VALID
    timeout = _has_timeout_artifacts(s) or (deadline and _supervisor_bootstrap_present(s))
    error = _has_error_artifacts(s)
    resolved = _has_resolved_artifacts(s)
    if exited and s.child_alive is True:
        return _invalid(
            InvalidCode.TERMINAL_AUTHORITY_CONFLICT,
            "child exit receipt names a process that is still alive",
        )
    pairs = (
        (timeout and error, "timeout and error authorities coexist"),
        (resolved and error, "canonical RESOLVED and error authorities coexist"),
        (resolved and timeout, "canonical RESOLVED and timeout authorities coexist"),
        (deadline and resolved, "canonical RESOLVED was issued after a durable deadline"),
        # 採用の直前にも CLI join を確かめる（receipt は envelope と E から誰でも
        # 再計算できるので、発行の手前の検査だけに頼らない）。
        (
            resolved
            and s.canonical.envelope_cli_returncode != s.child_exit.returncode,
            "canonical RESOLVED does not join the canonical outcome's CLI code",
        ),
        (deadline and error, "error authority exists for a deadline attempt"),
        # E が「deadline は無かった」と観測したのに timeout の物件がある。E も
        # 無い store（legacy）は progress で「終了観測の無い終端」として扱う。
        (exited and not deadline and timeout,
         "timeout authority exists without deadline evidence"),
        (exited and not deadline and _supervisor_bootstrap_present(s),
         "supervisor bootstrap checkpoint exists without deadline evidence"),
        (
            s.mode is ExitMode.CANONICAL_RESULT_REQUIRED and error,
            "error authority exists where only a canonical result may resolve",
        ),
        (
            s.mode is ExitMode.SUPERVISOR_ONLY and resolved,
            "canonical RESOLVED exists where the supervisor does not adopt child results",
        ),
    )
    for failed, detail in pairs:
        if failed:
            return _invalid(InvalidCode.TERMINAL_AUTHORITY_CONFLICT, detail)
    if not exited:
        return None
    if (
        s.child_exit.envelope_sha256 is not None
        and s.canonical.envelope_sha256 != s.child_exit.envelope_sha256
    ) or (
        s.child_exit.envelope_sha256 is None
        and s.canonical.envelope is not Presence.ABSENT
        and (resolved or s.mode is ExitMode.CANONICAL_RESULT_REQUIRED)
    ):
        return _invalid(
            InvalidCode.TERMINAL_AUTHORITY_CONFLICT,
            "canonical envelope differs from the one observed at child exit",
        )
    if (
        s.live.kill_disposition is not None
        and s.live.kill_disposition != s.child_exit.disposition
    ):
        return _invalid(
            InvalidCode.TERMINAL_AUTHORITY_CONFLICT,
            "timeout claim disposition differs from the observed child exit",
        )
    anchor = s.child_exit.anchor
    if s.archive.presence is Presence.VALID and (
        anchor is None or anchor.kind != ANCHOR_CHAIN
        or s.archive.checkpoint_digest != anchor.checkpoint_receipt_digest
    ):
        return _invalid(
            InvalidCode.TERMINAL_AUTHORITY_CONFLICT,
            "archive manifest does not archive the chain observed at child exit",
        )
    if s.archive.union is UnionState.CONFLICT:
        return _invalid(InvalidCode.ARCHIVE_UNION_CONFLICT, s.archive.detail or "archive union")
    if s.error.stage is not None:
        expected_stage = (
            s.archive.stage if s.archive.presence is Presence.VALID
            else ErrorStage.BEFORE_CHECKPOINT.value
        )
        if s.error.stage != expected_stage or s.error.disposition != s.child_exit.disposition:
            return _invalid(
                InvalidCode.TERMINAL_AUTHORITY_CONFLICT,
                "error authority differs from the archive stage or the observed exit",
            )
    return _attribution(s, deadline_family=deadline)


# ---------------------------------------------------------------------------
# 3. existing terminal
# ---------------------------------------------------------------------------


def _existing_terminal(s: TerminalSnapshot) -> Optional[Step]:
    deadline = s.deadline.presence is Presence.VALID
    exited = s.child_exit.presence is Presence.VALID
    if not exited:
        return None
    if _has_resolved_artifacts(s) and not deadline:
        return Step(StepKind.ADOPT_RESOLVED)
    if s.timeout.complete and deadline:
        return Step(StepKind.ADOPT_TIMEOUT)
    if s.error.complete and not deadline:
        archived = (
            s.archive.presence is Presence.VALID and s.archive.union is UnionState.COMPLETE
        )
        before_checkpoint = (
            s.archive.presence is Presence.ABSENT
            and s.child_exit.anchor is not None
            and s.child_exit.anchor.kind == ANCHOR_NONE
            and s.live.kind is LiveKind.NONE
            and s.pending.presence is Presence.ABSENT
        )
        if archived or before_checkpoint:
            return Step(StepKind.ADOPT_ERROR)
    return None


# ---------------------------------------------------------------------------
# 4. progress
# ---------------------------------------------------------------------------


def _deadline_progress(s: TerminalSnapshot) -> Step:
    if s.pending.presence is Presence.VALID:
        return _progress(StepKind.COMMIT_PENDING_ACTIVE)
    live = s.live
    if live.kind is LiveKind.NONE:
        return _progress(StepKind.BOOTSTRAP_ACTIVE)
    if live.kind is not LiveKind.CHAIN:
        return _invalid(
            InvalidCode.DURABLE_STATE_INCOMPLETE,
            f"deadline recovery found a {live.kind.value} live chain",
        )
    if live.state == CheckpointState.COMPLETION_READY:
        return _progress(StepKind.RECOVER_READY)
    if live.state == CheckpointState.ACTIVE:
        if live.continuation is Presence.VALID:
            return _progress(StepKind.CLOSE_CONTINUATION)
        return _progress(StepKind.CLAIM_TIMEOUT)
    if live.state == CheckpointState.RESOLVED and not live.is_bootstrap:
        return _progress(StepKind.BOOTSTRAP_ACTIVE)
    if live.state == CheckpointState.TIMED_OUT_CLAIMED:
        return _progress(StepKind.FINALIZE_TIMEOUT)
    return _invalid(
        InvalidCode.DURABLE_STATE_INCOMPLETE,
        f"deadline recovery cannot finish a {live.state} chain "
        f"(timeout bundle complete={s.timeout.complete})",
    )


def _canonical_progress(s: TerminalSnapshot) -> Step:
    canonical = s.canonical
    if canonical.envelope is Presence.ABSENT:
        return _invalid(
            InvalidCode.CANONICAL_CHILD_RESULT_INVALID,
            "child exited without a canonical result envelope",
        )
    if canonical.envelope is Presence.INVALID:
        return _invalid(
            InvalidCode.CANONICAL_CHILD_RESULT_INVALID,
            f"canonical result envelope is invalid: {canonical.detail}",
        )
    if canonical.envelope_cli_returncode != s.child_exit.returncode:
        return _invalid(
            InvalidCode.CANONICAL_CHILD_RESULT_INVALID,
            "child return code does not join the canonical outcome's CLI code",
        )
    return _progress(StepKind.ISSUE_CANONICAL_RESOLVED)


def _supervisor_error_progress(s: TerminalSnapshot) -> Step:
    anchor = s.child_exit.anchor
    if s.archive.presence is Presence.VALID:
        if s.archive.union is UnionState.PARTIAL:
            return _progress(StepKind.ADVANCE_ARCHIVE)
        return _progress(StepKind.FINALIZE_ERROR, error_stage=s.archive.stage)
    if s.pending.presence is Presence.VALID:
        return _progress(StepKind.COMMIT_PENDING_ACTIVE)
    live = s.live
    if live.kind is LiveKind.NONE:
        if anchor is not None and anchor.kind == ANCHOR_NONE:
            return _progress(StepKind.FINALIZE_ERROR, error_stage=ErrorStage.BEFORE_CHECKPOINT.value)
        return _invalid(
            InvalidCode.DURABLE_STATE_INCOMPLETE,
            "no live chain, no archive manifest, and the exit observed a checkpoint",
        )
    if live.kind is not LiveKind.CHAIN:
        return _invalid(
            InvalidCode.DURABLE_STATE_INCOMPLETE,
            f"error recovery found a {live.kind.value} live chain without an archive manifest",
        )
    if live.state == CheckpointState.COMPLETION_READY:
        return _progress(StepKind.RECOVER_READY)
    if live.state == CheckpointState.ACTIVE:
        if live.continuation is Presence.VALID:
            return _progress(StepKind.CLOSE_CONTINUATION)
        return _invalid(
            InvalidCode.ACTIVE_EXIT_STAGE_UNSEALED,
            "child exited inside decompilation; DURING_DECOMPILATION is not a sealed "
            "error stage",
        )
    if live.state == CheckpointState.RESOLVED:
        return _progress(StepKind.BEGIN_ARCHIVE)
    return _invalid(
        InvalidCode.DURABLE_STATE_INCOMPLETE,
        f"error recovery cannot finish a {live.state} chain",
    )


def _progress_step(s: TerminalSnapshot) -> Step:
    deadline = s.deadline.presence is Presence.VALID
    exited = s.child_exit.presence is Presence.VALID
    if not exited:
        if deadline:
            return _invalid(
                InvalidCode.DEADLINE_WITHOUT_EXIT_OBSERVATION,
                "deadline evidence is durable but the child exit was never observed",
            )
        supervisor_terminal = (
            _has_timeout_artifacts(s) or _has_error_artifacts(s)
            or _has_resolved_artifacts(s) or _supervisor_bootstrap_present(s)
        )
        if supervisor_terminal:
            return _invalid(
                InvalidCode.TERMINAL_WITHOUT_EXIT_OBSERVATION,
                "terminal authority exists without an observed child exit",
            )
        return _invalid(
            InvalidCode.EXIT_NOT_OBSERVED, "the child exit was never observed durably",
        )
    if deadline:
        return _deadline_progress(s)
    if s.mode is ExitMode.CANONICAL_RESULT_REQUIRED:
        return _canonical_progress(s)
    return _supervisor_error_progress(s)


def next_step(snapshot: TerminalSnapshot) -> Step:
    """validation → conflict → existing terminal → progress → INVALID。"""

    for stage in (_validation, _conflict, _existing_terminal):
        step = stage(snapshot)
        if step is not None:
            return step
    return _progress_step(snapshot)
