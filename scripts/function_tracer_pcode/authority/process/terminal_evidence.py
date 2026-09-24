"""Issue #165: supervisor が観測した終了事実の認証済み evidence（D / E / A）。

この module は 3 種類の evidence の **schema と検証だけ** を持つ（書込み・
復旧判断・終端 bundle は持たない）。

====================  ==============================  ============================
evidence              いつ・何を固定するか            file
====================  ==============================  ============================
D ``SupervisorDeadlineReceipt``   deadline を検知した事実。signal を  ``deadline.json``
                      送る前に durable にする
E ``SupervisorChildExitReceipt``  wait/poll で取った child の終了   ``child-exit.json``
                      （実測 int rc・実際に送った signal・
                      disposition・envelope と checkpoint の観測）
A ``SupervisorArchiveManifestReceipt``  archive する完全な checkpoint   ``archive-intent.json``
                      chain の member 集合（最初の移動より前）
====================  ==============================  ============================

原則:

* 観測した事実しか書かない。rc は ``wait``/``poll`` の返り値そのもの、signal は
  ``killpg`` が戻った送信だけ。deadline 到達・signal 送信・child 終了は別の
  field で、どれかから他を推測しない。
* 署名は既存の supervisor authority（supervisor role の鍵）を使う。runner・
  supervisor・worker・分類器は同じ trusted な実行領域として扱い、発行 process
  の認証（worker からの鍵の隔離）は要求しない。署名・digest・join は、
  改ざん・取り違え（別 launch・別 D・壊れた file）を検出するためにある。
* 検証は ``ProcessSupervisorAuthorityFactory.decode`` の署名検証の後に、ここで
  schema（key 集合・型）と launch / D / E の join を確かめる。署名が正しくても
  別 launch・別 D の evidence は受け付けない。
* disposition・送った signal・rc の対応は ``child_exit``（終了観測の語彙の
  唯一の owner）をそのまま使い、ここで再定義しない。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Optional

from scripts.function_tracer_pcode.authority.process import checkpoint_archive
from scripts.function_tracer_pcode.authority.process.child_exit import (
    LIVE_PROCESS_WAIT,
    SIGNAL_NAMES,
    SIGNAL_RESULTS,
    deadline_signal_actions,
    natural_exit_disposition,
    validate_durable_child_returncode_observation,
)

TERMINAL_EVIDENCE_ISSUER_ID = "decompiler-process-supervisor-terminal-evidence-v1"

DEADLINE_RECEIPT_KIND = "SupervisorDeadlineReceipt"
CHILD_EXIT_RECEIPT_KIND = "SupervisorChildExitReceipt"
ARCHIVE_MANIFEST_KIND = "SupervisorArchiveManifestReceipt"

DEADLINE_FILENAME = "deadline.json"
CHILD_EXIT_FILENAME = "child-exit.json"
ARCHIVE_INTENT_FILENAME = "archive-intent.json"

#: evidence kind -> store 直下の file 名（kind と file の対応はここだけで決める）。
TERMINAL_EVIDENCE_FILES: Mapping[str, str] = {
    DEADLINE_RECEIPT_KIND: DEADLINE_FILENAME,
    CHILD_EXIT_RECEIPT_KIND: CHILD_EXIT_FILENAME,
    ARCHIVE_MANIFEST_KIND: ARCHIVE_INTENT_FILENAME,
}

DEADLINE_SCHEMA = "supervisor-deadline-v1"
CHILD_EXIT_SCHEMA = "supervisor-child-exit-v1"
ARCHIVE_MANIFEST_SCHEMA = "supervisor-archive-manifest-v1"
ARCHIVE_TRANSACTION_VERSION = 1

#: child の自然終了を終端へどう写すかの supervisor の設定（E に固定する）。
#: 分類器は推測せず、E に記録された値で supervisor と同じ判断をする。
EXIT_MODE_CANONICAL_RESULT_REQUIRED = "CANONICAL_RESULT_REQUIRED"
EXIT_MODE_SUPERVISOR_ONLY = "SUPERVISOR_ONLY"
EXIT_MODES = frozenset({EXIT_MODE_CANONICAL_RESULT_REQUIRED, EXIT_MODE_SUPERVISOR_ONLY})

#: E が観測した checkpoint の種類。
ANCHOR_NONE = "NONE"
ANCHOR_PENDING_ACTIVE = "PENDING_ACTIVE"
ANCHOR_CHAIN = "CHAIN"
ANCHOR_UNREADABLE = "UNREADABLE"
ANCHOR_KINDS = frozenset({
    ANCHOR_NONE, ANCHOR_PENDING_ACTIVE, ANCHOR_CHAIN, ANCHOR_UNREADABLE,
})

_LAUNCH_JOIN_FIELDS = (
    "execution_nonce", "result_occurrence_id", "stream_id",
    "deadline_policy_digest", "child_pid", "child_start_token",
)


class TerminalEvidenceInvalid(ValueError):
    """署名は通ったが schema / join が合わない evidence。"""


def _exact_digest(name: str, value: Any, *, nullable: bool = False) -> None:
    if value is None and nullable:
        return
    if type(value) is not str or not value:
        raise TerminalEvidenceInvalid(f"{name} must be a non-empty exact string")


def _exact_keys(name: str, payload: Mapping[str, Any], keys: frozenset[str]) -> None:
    if type(payload) is not dict or set(payload) != keys:
        raise TerminalEvidenceInvalid(f"{name} payload fields differ")


def _launch_identity(launch: Any) -> dict[str, Any]:
    return {
        "launch_receipt_digest": launch.receipt_digest,
        **{name: launch.payload[name] for name in _LAUNCH_JOIN_FIELDS},
    }


def _require_launch_join(name: str, payload: Mapping[str, Any], launch: Any) -> None:
    if launch.receipt_kind != "SupervisorLaunchReceipt":
        raise TerminalEvidenceInvalid(f"{name} requires an exact launch authority")
    for key, value in _launch_identity(launch).items():
        if payload.get(key) != value:
            raise TerminalEvidenceInvalid(f"{name} {key} does not join the launch")


def _require_kind(receipt: Any, kind: str) -> None:
    if receipt.receipt_kind != kind:
        raise TerminalEvidenceInvalid(f"expected {kind}, got {receipt.receipt_kind}")


# ---------------------------------------------------------------------------
# D: deadline
# ---------------------------------------------------------------------------

_DEADLINE_KEYS = frozenset({
    "schema", "launch_receipt_digest", *_LAUNCH_JOIN_FIELDS,
    "configured_timeout_seconds", "deadline_detected_offset_seconds",
    "issuer_id",
})


def deadline_payload(
    launch: Any, *, configured_timeout_seconds: float,
    deadline_detected_offset_seconds: float,
) -> dict[str, Any]:
    """deadline を検知した事実だけの payload（signal も child の状態も含めない）。"""

    for name, value in (
        ("configured_timeout_seconds", configured_timeout_seconds),
        ("deadline_detected_offset_seconds", deadline_detected_offset_seconds),
    ):
        if type(value) not in {int, float} or value < 0:
            raise TerminalEvidenceInvalid(f"{name} must be a non-negative number")
    payload = {
        "schema": DEADLINE_SCHEMA,
        **_launch_identity(launch),
        "configured_timeout_seconds": float(configured_timeout_seconds),
        "deadline_detected_offset_seconds": float(deadline_detected_offset_seconds),
        "issuer_id": TERMINAL_EVIDENCE_ISSUER_ID,
    }
    _require_launch_join("deadline", payload, launch)
    return payload


def validate_deadline(receipt: Any, launch: Any) -> None:
    _require_kind(receipt, DEADLINE_RECEIPT_KIND)
    payload = receipt.payload
    _exact_keys("deadline", payload, _DEADLINE_KEYS)
    if (
        payload["schema"] != DEADLINE_SCHEMA
        or payload["issuer_id"] != TERMINAL_EVIDENCE_ISSUER_ID
        or any(
            type(payload[name]) is not float or payload[name] < 0
            for name in (
                "configured_timeout_seconds", "deadline_detected_offset_seconds",
            )
        )
    ):
        raise TerminalEvidenceInvalid("deadline receipt schema is invalid")
    _require_launch_join("deadline", payload, launch)


# ---------------------------------------------------------------------------
# E: child exit
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SignalAction:
    """supervisor が ``killpg`` を呼んで戻った 1 回分（試行の結果）。"""

    signal: str
    result: str

    def to_json(self) -> dict[str, str]:
        if self.signal not in SIGNAL_NAMES or self.result not in SIGNAL_RESULTS:
            raise TerminalEvidenceInvalid("signal action is not sealed")
        return {"signal": self.signal, "result": self.result}


@dataclass(frozen=True)
class EnvelopeObservation:
    """child 終了を観測した時点の canonical envelope（bytes の digest だけ）。"""

    present: bool
    sha256: Optional[str]

    def to_json(self) -> dict[str, Any]:
        if type(self.present) is not bool or (self.present != (self.sha256 is not None)):
            raise TerminalEvidenceInvalid("envelope observation is inconsistent")
        if self.sha256 is not None:
            _exact_digest("envelope sha256", self.sha256)
        return {"present": self.present, "sha256": self.sha256}


@dataclass(frozen=True)
class CheckpointAnchor:
    """child 終了を観測した時点の live checkpoint（何を terminal 処理するか）。

    * ``NONE``: live chain も pending transaction も無い。
    * ``PENDING_ACTIVE``: worker の ACTIVE transaction が commit 前。
    * ``CHAIN``: live chain（``checkpoint.json`` の ACTIVE checkpoint と
      ``state.json`` の state）。
    * ``UNREADABLE``: live に checkpoint の file があるのに読めなかった（後の
      復旧は INVALID にする。何があったかは ``detail``）。
    """

    kind: str
    checkpoint_receipt_digest: Optional[str] = None
    state_receipt_digest: Optional[str] = None
    state: Optional[str] = None
    transaction_digest: Optional[str] = None
    detail: Optional[str] = None

    def to_json(self) -> dict[str, Any]:
        value = {
            "kind": self.kind,
            "checkpoint_receipt_digest": self.checkpoint_receipt_digest,
            "state_receipt_digest": self.state_receipt_digest,
            "state": self.state,
            "transaction_digest": self.transaction_digest,
            "detail": self.detail,
        }
        validate_checkpoint_anchor(value)
        return value

    @classmethod
    def from_json(cls, value: Mapping[str, Any]) -> "CheckpointAnchor":
        validate_checkpoint_anchor(value)
        return cls(**dict(value))


_ANCHOR_KEYS = frozenset({
    "kind", "checkpoint_receipt_digest", "state_receipt_digest", "state",
    "transaction_digest", "detail",
})


def validate_checkpoint_anchor(value: Mapping[str, Any]) -> None:
    _exact_keys("checkpoint anchor", value, _ANCHOR_KEYS)
    kind = value["kind"]
    if kind not in ANCHOR_KINDS:
        raise TerminalEvidenceInvalid("checkpoint anchor kind is not sealed")
    present = {name for name in _ANCHOR_KEYS - {"kind"} if value[name] is not None}
    expected = {
        ANCHOR_NONE: set(),
        ANCHOR_PENDING_ACTIVE: {"checkpoint_receipt_digest", "transaction_digest"},
        ANCHOR_CHAIN: {"checkpoint_receipt_digest", "state_receipt_digest", "state"},
        ANCHOR_UNREADABLE: {"detail"},
    }[kind]
    if present != expected or any(type(value[name]) is not str or not value[name] for name in present):
        raise TerminalEvidenceInvalid(f"checkpoint anchor {kind} fields differ")


_CHILD_EXIT_KEYS = frozenset({
    "schema", "launch_receipt_digest", *_LAUNCH_JOIN_FIELDS,
    "deadline_receipt_digest", "returncode_observation_kind",
    "child_returncode", "child_exit_disposition", "signal_actions",
    "envelope_observation", "checkpoint_anchor", "exit_mode", "issuer_id",
})


def child_exit_payload(
    launch: Any, *, deadline: Any, child_returncode: int,
    child_exit_disposition: str, signal_actions: tuple[SignalAction, ...],
    envelope: EnvelopeObservation, anchor: CheckpointAnchor, exit_mode: str,
) -> dict[str, Any]:
    payload = {
        "schema": CHILD_EXIT_SCHEMA,
        **_launch_identity(launch),
        "deadline_receipt_digest": (
            None if deadline is None else deadline.receipt_digest
        ),
        "returncode_observation_kind": LIVE_PROCESS_WAIT,
        "child_returncode": child_returncode,
        "child_exit_disposition": child_exit_disposition,
        "signal_actions": [action.to_json() for action in signal_actions],
        "envelope_observation": envelope.to_json(),
        "checkpoint_anchor": anchor.to_json(),
        "exit_mode": exit_mode,
        "issuer_id": TERMINAL_EVIDENCE_ISSUER_ID,
    }
    _validate_child_exit_payload(payload, launch=launch, deadline=deadline)
    return payload


def _validate_child_exit_payload(
    payload: Mapping[str, Any], *, launch: Any, deadline: Any,
) -> None:
    _exact_keys("child exit", payload, _CHILD_EXIT_KEYS)
    if (
        payload["schema"] != CHILD_EXIT_SCHEMA
        or payload["issuer_id"] != TERMINAL_EVIDENCE_ISSUER_ID
        or payload["returncode_observation_kind"] != LIVE_PROCESS_WAIT
        or type(payload["child_returncode"]) is not int
        or type(payload["signal_actions"]) is not list
        or payload["exit_mode"] not in EXIT_MODES
    ):
        raise TerminalEvidenceInvalid("child exit receipt schema is invalid")
    _require_launch_join("child exit", payload, launch)
    try:
        validate_durable_child_returncode_observation(
            child_exit_disposition=payload["child_exit_disposition"],
            child_returncode=payload["child_returncode"],
            observation_kind=LIVE_PROCESS_WAIT,
        )
    except ValueError as exc:
        raise TerminalEvidenceInvalid(str(exc)) from exc
    actions = payload["signal_actions"]
    for action in actions:
        if (
            type(action) is not dict or set(action) != {"signal", "result"}
            or action["signal"] not in SIGNAL_NAMES
            or action["result"] not in SIGNAL_RESULTS
        ):
            raise TerminalEvidenceInvalid("child exit signal action is not sealed")
    envelope = payload["envelope_observation"]
    if (
        type(envelope) is not dict or set(envelope) != {"present", "sha256"}
        or type(envelope["present"]) is not bool
        or envelope["present"] != (envelope["sha256"] is not None)
    ):
        raise TerminalEvidenceInvalid("child exit envelope observation is invalid")
    validate_checkpoint_anchor(payload["checkpoint_anchor"])
    deadline_digest = payload["deadline_receipt_digest"]
    if deadline is None:
        # signal を送らなかった終了: disposition は rc そのもので、signal は無い。
        if (
            deadline_digest is not None
            or actions
            or payload["child_exit_disposition"]
            != natural_exit_disposition(payload["child_returncode"])
        ):
            raise TerminalEvidenceInvalid(
                "child exit without deadline evidence claims deadline facts"
            )
    else:
        if deadline_digest != deadline.receipt_digest:
            raise TerminalEvidenceInvalid("child exit does not join its deadline receipt")
        observed = tuple((action["signal"], action["result"]) for action in actions)
        if observed not in deadline_signal_actions(payload["child_exit_disposition"]):
            raise TerminalEvidenceInvalid(
                "child exit signal actions do not produce its disposition"
            )


def validate_child_exit(receipt: Any, launch: Any, deadline: Any) -> None:
    """E を launch と D（無ければ None）に対して検証する。

    E が D を名指すのに D が無い、D があるのに E が D を名指さない、のどちらも
    拒否する（``_validate_child_exit_payload`` の ``deadline`` 引数で両方向）。
    """

    _require_kind(receipt, CHILD_EXIT_RECEIPT_KIND)
    _validate_child_exit_payload(receipt.payload, launch=launch, deadline=deadline)


def child_exit_anchor(receipt: Any) -> CheckpointAnchor:
    return CheckpointAnchor.from_json(receipt.payload["checkpoint_anchor"])


# ---------------------------------------------------------------------------
# A: archive manifest
# ---------------------------------------------------------------------------

_ARCHIVE_KEYS = frozenset({
    "schema", "transaction_version", "launch_receipt_digest", "execution_nonce",
    "child_exit_receipt_digest", "checkpoint_receipt_digest",
    "resolved_state_receipt_digest", "anchor_state", "error_kind",
    "error_stage", "destination", "members", "issuer_id",
})
_MEMBER_KEYS = frozenset({"name", "role", "size", "sha256"})


@dataclass(frozen=True)
class ArchiveMember:
    name: str
    role: str
    size: int
    sha256: str

    def to_json(self) -> dict[str, Any]:
        return {"name": self.name, "role": self.role, "size": self.size, "sha256": self.sha256}


def archive_payload(
    launch: Any, *, child_exit: Any, checkpoint_receipt_digest: str,
    resolved_state_receipt_digest: str, anchor_state: Optional[str],
    error_kind: str, error_stage: str, destination: str,
    members: tuple[ArchiveMember, ...],
) -> dict[str, Any]:
    payload = {
        "schema": ARCHIVE_MANIFEST_SCHEMA,
        "transaction_version": ARCHIVE_TRANSACTION_VERSION,
        "launch_receipt_digest": launch.receipt_digest,
        "execution_nonce": launch.payload["execution_nonce"],
        "child_exit_receipt_digest": child_exit.receipt_digest,
        "checkpoint_receipt_digest": checkpoint_receipt_digest,
        "resolved_state_receipt_digest": resolved_state_receipt_digest,
        "anchor_state": anchor_state,
        "error_kind": error_kind,
        "error_stage": error_stage,
        "destination": destination,
        "members": [member.to_json() for member in members],
        "issuer_id": TERMINAL_EVIDENCE_ISSUER_ID,
    }
    _validate_archive_payload(payload, launch=launch, child_exit=child_exit)
    return payload


def _validate_archive_payload(
    payload: Mapping[str, Any], *, launch: Any, child_exit: Any,
) -> None:
    _exact_keys("archive manifest", payload, _ARCHIVE_KEYS)
    if (
        payload["schema"] != ARCHIVE_MANIFEST_SCHEMA
        or payload["transaction_version"] != ARCHIVE_TRANSACTION_VERSION
        or payload["issuer_id"] != TERMINAL_EVIDENCE_ISSUER_ID
        or payload["launch_receipt_digest"] != launch.receipt_digest
        or payload["execution_nonce"] != launch.payload["execution_nonce"]
        or payload["child_exit_receipt_digest"] != child_exit.receipt_digest
        or type(payload["members"]) is not list
        or (payload["anchor_state"] is not None and type(payload["anchor_state"]) is not str)
    ):
        raise TerminalEvidenceInvalid("archive manifest does not join launch/exit")
    for name in (
        "checkpoint_receipt_digest", "resolved_state_receipt_digest",
        "error_kind", "error_stage", "destination",
    ):
        _exact_digest(name, payload[name])
    members = []
    for member in payload["members"]:
        if (
            type(member) is not dict or set(member) != _MEMBER_KEYS
            or type(member["size"]) is not int or member["size"] < 0
        ):
            raise TerminalEvidenceInvalid("archive manifest member schema is invalid")
        for name in ("name", "role", "sha256"):
            _exact_digest(f"member {name}", member[name])
        members.append(ArchiveMember(**member))
    try:
        checkpoint_archive.validate_member_set(
            tuple(members), destination=payload["destination"],
            resolved_state_receipt_digest=payload["resolved_state_receipt_digest"],
        )
    except ValueError as exc:
        raise TerminalEvidenceInvalid(str(exc)) from exc


def validate_archive(receipt: Any, launch: Any, child_exit: Any) -> None:
    _require_kind(receipt, ARCHIVE_MANIFEST_KIND)
    _validate_archive_payload(receipt.payload, launch=launch, child_exit=child_exit)


def archive_members(receipt: Any) -> tuple[ArchiveMember, ...]:
    return tuple(ArchiveMember(**member) for member in receipt.payload["members"])
