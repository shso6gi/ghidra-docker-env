# -*- coding: utf-8 -*-
"""Issue #165: 終了観測の evidence（D / E / A）・archive・lock・判断順序の単体契約。

実 process を使わない。production の factory / store / ``next_step`` を直接呼び、

* D / E / A の schema と join（別 launch・別 D・別 E・rc と disposition の不一致を
  拒否。自然終了の E は signal / deadline を名乗れない）
* D / E / A は supervisor role の署名だけを受理する（worker role・署名後の改ざんは拒否）
* chain member 集合と A の union 検証（両側欠落・bytes 不一致・余分な file）
* store の flock / owner lock（入れ子は例外、supervisor 専用の書込みは owner のみ）
* 判断の順序（完成した終端があっても競合が先）

を固定する。
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import replace
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.process import checkpoint_archive as ca
from scripts.function_tracer_pcode.authority.process import child_exit as ce
from scripts.function_tracer_pcode.authority.process.checkpoint_vocabulary import (
    CheckpointState,
    ErrorStage,
)
from scripts.function_tracer_pcode.authority.process import terminal_evidence as te
from scripts.function_tracer_pcode.authority.process import terminal_recovery as tr
from scripts.function_tracer_pcode.authority.process.supervisor import (
    DurableCheckpointStore,
    ProcessSupervisorAuthorityFactory,
    StoreLockReentry,
)

KEYS = dict(
    supervisor_signing_key_id="supervisor-key-v1", supervisor_signing_key=b"s" * 32,
    worker_signing_key_id="worker-key-v1", worker_signing_key=b"w" * 32,
)


def _factory() -> ProcessSupervisorAuthorityFactory:
    return ProcessSupervisorAuthorityFactory(**KEYS)


def _launch(factory, *, nonce="execution-1"):
    return factory.issue_launch(
        result_occurrence_id="occurrence-1", manifest_entry_preimage_digest="manifest",
        execution_nonce=nonce, child_pid=4242, child_start_token="token-1",
        stream_id="stream-1", source_snapshot_fingerprint="fingerprint-1",
        deadline_policy_digest="policy-1",
    )


def _deadline(factory, launch):
    return factory.issue_terminal_evidence(
        te.DEADLINE_RECEIPT_KIND,
        te.deadline_payload(
            launch, configured_timeout_seconds=60.0, deadline_detected_offset_seconds=60.001,
        ),
    )


def _exit(factory, launch, *, deadline=None, rc=-15, disposition="SIGTERM_AFTER_DEADLINE",
          signals=(te.SignalAction("SIGTERM", ce.SIGNAL_SENT),), anchor=None):
    payload = te.child_exit_payload(
        launch, deadline=deadline, child_returncode=rc,
        child_exit_disposition=disposition, signal_actions=signals,
        envelope=te.EnvelopeObservation(False, None),
        anchor=anchor or te.CheckpointAnchor(te.ANCHOR_NONE),
        exit_mode=te.EXIT_MODE_CANONICAL_RESULT_REQUIRED,
    )
    return factory.issue_terminal_evidence(te.CHILD_EXIT_RECEIPT_KIND, payload)


# ---------------------------------------------------------------------------
# 鍵の分離
# ---------------------------------------------------------------------------


def test_terminal_evidence_is_signed_and_decoded_with_the_supervisor_role():
    factory = _factory()
    launch = _launch(factory)
    deadline = _deadline(factory, launch)
    assert deadline.signing_key_id == "supervisor-key-v1"
    assert factory.decode(deadline.to_dict()).payload == deadline.payload


def test_a_worker_role_receipt_cannot_claim_a_terminal_evidence_kind():
    factory = _factory()
    for kind in te.TERMINAL_EVIDENCE_FILES:
        forged = factory._sign(kind, {"x": 1}, signer_role="worker")
        with pytest.raises(ValueError, match="signer role does not match"):
            factory.validate(forged)


def test_a_terminal_evidence_payload_edited_after_signing_is_rejected():
    factory = _factory()
    launch = _launch(factory)
    stored = _deadline(factory, launch).to_dict()
    stored["payload"]["deadline_detected_offset_seconds"] = 99.0
    with pytest.raises(ValueError, match="signature/digest mismatch"):
        factory.decode(stored)


def test_only_sealed_kinds_are_issued_as_terminal_evidence():
    with pytest.raises(ValueError, match="not sealed"):
        _factory().issue_terminal_evidence("SupervisorLaunchReceipt", {"x": 1})


# ---------------------------------------------------------------------------
# D / E / A の schema と join
# ---------------------------------------------------------------------------


def test_deadline_and_exit_join_their_own_launch_only():
    factory = _factory()
    launch = _launch(factory)
    other = _launch(factory, nonce="execution-2")
    deadline = _deadline(factory, launch)
    te.validate_deadline(deadline, launch)
    with pytest.raises(te.TerminalEvidenceInvalid, match="does not join the launch"):
        te.validate_deadline(deadline, other)
    exit_receipt = _exit(factory, launch, deadline=deadline)
    te.validate_child_exit(exit_receipt, launch, deadline)
    with pytest.raises(te.TerminalEvidenceInvalid):
        te.validate_child_exit(exit_receipt, other, deadline)


def test_exit_and_deadline_must_name_each_other_in_both_directions():
    factory = _factory()
    launch = _launch(factory)
    deadline = _deadline(factory, launch)
    with_deadline = _exit(factory, launch, deadline=deadline)
    # E が D を名指すのに D が無い。
    with pytest.raises(te.TerminalEvidenceInvalid):
        te.validate_child_exit(with_deadline, launch, None)
    # D があるのに E は D を名指さない（自然終了の E）。
    natural = _exit(factory, launch, rc=0, disposition="EXIT_CODE_0", signals=())
    with pytest.raises(te.TerminalEvidenceInvalid, match="does not join its deadline"):
        te.validate_child_exit(natural, launch, deadline)


@pytest.mark.parametrize(("rc", "disposition", "signals"), (
    (-15, "SIGTERM_AFTER_DEADLINE", (te.SignalAction("SIGTERM", ce.SIGNAL_SENT),)),
    (2, "EXIT_CODE_2", (te.SignalAction("SIGTERM", ce.SIGNAL_SENT),)),
    (0, "EXITED_0", ()),
))
def test_a_natural_exit_cannot_claim_deadline_facts(rc, disposition, signals):
    factory = _factory()
    launch = _launch(factory)
    with pytest.raises(te.TerminalEvidenceInvalid):
        _exit(factory, launch, rc=rc, disposition=disposition, signals=signals)


@pytest.mark.parametrize(("rc", "disposition"), (
    (-9, "SIGTERM_AFTER_DEADLINE"), (0, "EXITED_3_AFTER_SIGTERM"), (2, "KILLED_SOMEHOW"),
))
def test_exit_rc_must_be_the_one_its_disposition_names(rc, disposition):
    factory = _factory()
    launch = _launch(factory)
    deadline = _deadline(factory, launch)
    with pytest.raises(te.TerminalEvidenceInvalid):
        _exit(factory, launch, deadline=deadline, rc=rc, disposition=disposition)


SENT = te.SignalAction("SIGTERM", ce.SIGNAL_SENT)
KILLED = te.SignalAction("SIGKILL", ce.SIGNAL_SENT)
TERM_ABSENT = te.SignalAction("SIGTERM", ce.SIGNAL_PROCESS_ABSENT)
KILL_ABSENT = te.SignalAction("SIGKILL", ce.SIGNAL_PROCESS_ABSENT)


@pytest.mark.parametrize(("rc", "disposition", "signals"), (
    (2, "EXITED_2", ()),
    (2, "EXITED_2_BEFORE_SIGTERM", (TERM_ABSENT,)),
    (-15, "SIGTERM_AFTER_DEADLINE", (SENT,)),
    (3, "EXITED_3_AFTER_SIGTERM", (SENT,)),
    (3, "EXITED_3_BEFORE_SIGKILL", (SENT,)),
    (3, "EXITED_3_BEFORE_SIGKILL", (SENT, KILL_ABSENT)),
    (-9, "SIGKILL_AFTER_DEADLINE", (SENT, KILLED)),
    (0, "EXITED_0_AFTER_SIGKILL", (SENT, KILLED)),
))
def test_deadline_exit_accepts_every_branch_of_the_termination(rc, disposition, signals):
    factory = _factory()
    launch = _launch(factory)
    _exit(factory, launch, deadline=_deadline(factory, launch), rc=rc,
          disposition=disposition, signals=signals)


@pytest.mark.parametrize(("rc", "disposition", "signals"), (
    (-9, "SIGKILL_AFTER_DEADLINE", ()),              # SIGKILL を送っていない
    (-15, "SIGTERM_AFTER_DEADLINE", ()),             # SIGTERM を送っていない
    (2, "EXITED_2", (SENT,)),                        # 送ったのに送る前の終了
    (3, "EXIT_CODE_3", ()),                          # 自然終了の語彙
    (0, "EXITED_0_AFTER_SIGKILL", (SENT,)),          # SIGKILL の記録が無い
))
def test_deadline_exit_rejects_signals_that_cannot_produce_its_disposition(
    rc, disposition, signals,
):
    factory = _factory()
    launch = _launch(factory)
    with pytest.raises(te.TerminalEvidenceInvalid):
        _exit(factory, launch, deadline=_deadline(factory, launch), rc=rc,
              disposition=disposition, signals=signals)


def test_exit_mode_is_sealed():
    factory = _factory()
    launch = _launch(factory)
    receipt = _exit(factory, launch, rc=0, disposition="EXIT_CODE_0", signals=())
    guessed = factory.issue_terminal_evidence(
        te.CHILD_EXIT_RECEIPT_KIND, {**receipt.payload, "exit_mode": "GUESSED"},
    )
    with pytest.raises(te.TerminalEvidenceInvalid, match="schema"):
        te.validate_child_exit(guessed, launch, None)


def test_exit_records_only_observed_signal_actions():
    factory = _factory()
    launch = _launch(factory)
    deadline = _deadline(factory, launch)
    receipt = _exit(
        factory, launch, deadline=deadline, rc=3,
        disposition="EXITED_3_BEFORE_SIGTERM",
        signals=(te.SignalAction("SIGTERM", ce.SIGNAL_PROCESS_ABSENT),),
    )
    assert receipt.payload["signal_actions"] == [
        {"signal": "SIGTERM", "result": "process_absent"},
    ]
    with pytest.raises(te.TerminalEvidenceInvalid):
        te.SignalAction("SIGHUP", ce.SIGNAL_SENT).to_json()


@pytest.mark.parametrize("value", (
    {"kind": "NONE", "checkpoint_receipt_digest": "c"},
    {"kind": "CHAIN", "checkpoint_receipt_digest": "c"},
    {"kind": "PENDING_ACTIVE", "transaction_digest": "t"},
    {"kind": "UNREADABLE"},
    {"kind": "OTHER"},
))
def test_checkpoint_anchor_fields_are_sealed_per_kind(value):
    full = {key: None for key in (
        "kind", "checkpoint_receipt_digest", "state_receipt_digest", "state",
        "transaction_digest", "detail",
    )}
    with pytest.raises(te.TerminalEvidenceInvalid):
        te.validate_checkpoint_anchor({**full, **value})


def _members(*names):
    roles = {spec.name: spec.role for spec in ca.CHAIN_MEMBERS}
    return tuple(te.ArchiveMember(name, roles.get(name, "x"), 1, "a" * 64) for name in names)


REQUIRED = tuple(spec.name for spec in ca.CHAIN_MEMBERS if spec.required)


def test_archive_member_set_is_the_closed_chain_in_move_order():
    ca.validate_member_set(
        _members(*REQUIRED), destination=ca.history_destination("abc"),
        resolved_state_receipt_digest="abc",
    )
    assert REQUIRED[-1] == "state.json"


@pytest.mark.parametrize("names", (
    REQUIRED[:-1],                                   # state.json 欠落
    REQUIRED + ("state.json",),                      # 重複
    ("state.json",) + REQUIRED[:-1],                 # state.json が先
    REQUIRED + ("claimed.json",),                    # chain 外の member
))
def test_archive_member_set_rejects_partial_or_foreign_members(names):
    with pytest.raises(ca.ArchiveConflict):
        ca.validate_member_set(
            _members(*names), destination=ca.history_destination("abc"),
            resolved_state_receipt_digest="abc",
        )


def test_archive_destination_is_bound_to_the_resolved_chain():
    with pytest.raises(ca.ArchiveConflict):
        ca.validate_member_set(
            _members(*REQUIRED), destination=ca.history_destination("other"),
            resolved_state_receipt_digest="abc",
        )
    with pytest.raises(ca.ArchiveConflict):
        ca.history_destination("../escape")


def _write_members(directory: Path, names):
    members = []
    roles = {spec.name: spec.role for spec in ca.CHAIN_MEMBERS}
    for name in names:
        data = f"{name}-bytes".encode()
        (directory / name).write_bytes(data)
        members.append(te.ArchiveMember(name, roles[name], len(data), hashlib.sha256(data).hexdigest()))
    return tuple(members)


def test_union_is_resumable_from_every_split_and_rejects_corruption(tmp_path):
    members = _write_members(tmp_path, REQUIRED)
    destination = ca.history_destination("abc")
    for count in range(len(members) + 1):
        inspection = ca.inspect_union(tmp_path, members, destination)
        assert inspection.remaining == tuple(m.name for m in members[count:])
        if count < len(members):
            ca.move_member(tmp_path, destination, members[count].name)
    assert ca.inspect_union(tmp_path, members, destination).complete
    history = tmp_path / destination
    target = history / "ready.json"
    original = target.read_bytes()
    target.write_bytes(b"tampered")
    with pytest.raises(ca.ArchiveConflict, match="differs"):
        ca.inspect_union(tmp_path, members, destination)
    target.unlink()
    with pytest.raises(ca.ArchiveConflict, match="missing on both sides"):
        ca.inspect_union(tmp_path, members, destination)
    target.write_bytes(original)
    (history / "stray.json").write_text("{}")
    with pytest.raises(ca.ArchiveConflict, match="unexpected files"):
        ca.inspect_union(tmp_path, members, destination)


# ---------------------------------------------------------------------------
# lock と ownership
# ---------------------------------------------------------------------------


def test_store_flock_and_ownership_are_not_reentrant(tmp_path):
    store = DurableCheckpointStore(tmp_path, _factory(), "execution-1")
    with store._locked():
        with pytest.raises(StoreLockReentry):
            with store._locked():
                pass
    with store.supervisor_ownership() as ownership:
        assert ownership.held
        with pytest.raises(StoreLockReentry):
            with store.supervisor_ownership():
                pass
    assert not ownership.held


def test_another_thread_waits_for_the_store_flock_instead_of_failing(tmp_path):
    import threading

    store = DurableCheckpointStore(tmp_path, _factory(), "execution-1")
    outcome = {}
    started = threading.Event()

    def other():
        started.set()
        try:
            with store._locked():
                outcome["acquired"] = True
        except StoreLockReentry as exc:  # pragma: no cover - the failure mode
            outcome["error"] = exc

    with store._locked():
        thread = threading.Thread(target=other)
        thread.start()
        started.wait(10)
    thread.join(10)
    assert outcome == {"acquired": True}


def test_supervisor_only_writes_require_held_ownership(tmp_path):
    factory = _factory()
    store = DurableCheckpointStore(tmp_path, factory, "execution-1")
    launch = _launch(factory)
    store.persist_launch(launch)
    deadline = _deadline(factory, launch)
    with store.supervisor_ownership() as ownership:
        pass
    with pytest.raises(RuntimeError, match="ownership"):
        store.persist_deadline(ownership, deadline)
    with pytest.raises(RuntimeError, match="ownership"):
        with store.owned_lock(ownership):
            pass
    with store.supervisor_ownership() as ownership:
        store.persist_deadline(ownership, deadline)
        store.persist_deadline(ownership, deadline)  # 同じ bytes の再書込みは冪等
        other = factory.issue_terminal_evidence(
            te.DEADLINE_RECEIPT_KIND,
            {**deadline.payload, "deadline_detected_offset_seconds": 61.0},
        )
        with pytest.raises(ValueError, match="conflicting durable"):
            store.persist_deadline(ownership, other)


def test_child_exit_is_observed_and_written_under_one_flock(tmp_path):
    factory = _factory()
    store = DurableCheckpointStore(tmp_path, factory, "execution-1")
    launch = _launch(factory)
    store.persist_launch(launch)
    seen = {}

    def build(*, launch, deadline, anchor, envelope):
        # build は store の flock の中で呼ばれる（入れ子の取得は例外になる）。
        with pytest.raises(StoreLockReentry):
            with store._locked():
                pass
        seen.update(anchor=anchor, envelope=envelope, deadline=deadline)
        return _exit(factory, launch, rc=3, disposition="EXIT_CODE_3", signals=(), anchor=anchor)

    with store.supervisor_ownership() as ownership:
        receipt = store.record_child_exit(ownership, build)
    assert seen["anchor"].kind == te.ANCHOR_NONE
    assert seen["envelope"] == te.EnvelopeObservation(False, None)
    assert seen["deadline"] is None
    stored = json.loads((store.directory / te.CHILD_EXIT_FILENAME).read_text())
    assert stored["receipt_digest"] == receipt.receipt_digest


# ---------------------------------------------------------------------------
# 判断の順序
# ---------------------------------------------------------------------------


def _complete_timeout_snapshot():
    V = tr.Presence.VALID
    anchor = te.CheckpointAnchor(te.ANCHOR_NONE)
    return tr.TerminalSnapshot(
        mode=tr.ExitMode.CANONICAL_RESULT_REQUIRED,
        launch=tr.Fact(V, "L"), deadline=tr.Fact(V, "D"),
        child_exit=tr.ExitFact(V, "E", returncode=-15, disposition="SIGTERM_AFTER_DEADLINE",
                               deadline_digest="D", anchor=anchor),
        child_alive=False, pending=tr.PendingFact(),
        live=tr.LiveChainFact(tr.LiveKind.CHAIN, checkpoint_digest="B[None]", is_bootstrap=True,
                              state=CheckpointState.TIMED_OUT.value, state_digest="s",
                              kill_disposition="SIGTERM_AFTER_DEADLINE"),
        timeout=tr.TimeoutFact(frozenset({"claimed.json", "timeout.json",
                                          "terminal-segment.json", "terminal-stream.json"}),
                               complete=True, bundle_digest="T"),
        error=tr.ErrorFact(), archive=tr.ArchiveFact(), canonical=tr.CanonicalFact(),
    )


def test_a_complete_terminal_is_adopted_only_without_conflict():
    snapshot = _complete_timeout_snapshot()
    assert tr.next_step(snapshot).kind is tr.StepKind.ADOPT_TIMEOUT
    conflicted = replace(snapshot, error=tr.ErrorFact(
        frozenset({"operational-error.json"}), stage=ErrorStage.BEFORE_CHECKPOINT.value,
        disposition="SIGTERM_AFTER_DEADLINE",
    ))
    step = tr.next_step(conflicted)
    assert step.kind is tr.StepKind.INVALID
    assert step.invalid_code is tr.InvalidCode.TERMINAL_AUTHORITY_CONFLICT


def _resolved_snapshot(*, returncode: int, cli_returncode: int):
    V = tr.Presence.VALID
    return tr.TerminalSnapshot(
        mode=tr.ExitMode.CANONICAL_RESULT_REQUIRED,
        launch=tr.Fact(V, "L"), deadline=tr.Fact(),
        child_exit=tr.ExitFact(V, "E", returncode=returncode,
                               disposition=f"EXIT_CODE_{returncode}",
                               envelope_sha256="env",
                               anchor=te.CheckpointAnchor(te.ANCHOR_NONE)),
        child_alive=False, pending=tr.PendingFact(), live=tr.LiveChainFact(),
        timeout=tr.TimeoutFact(), error=tr.ErrorFact(), archive=tr.ArchiveFact(),
        canonical=tr.CanonicalFact(
            receipt=V, envelope=V, envelope_sha256="env",
            envelope_cli_returncode=cli_returncode,
        ),
    )


def test_canonical_resolved_is_adopted_only_when_the_exit_joins_the_cli_code():
    """receipt は envelope と E から誰でも再計算できる。採用の前にも CLI join を見る。"""

    assert tr.next_step(
        _resolved_snapshot(returncode=0, cli_returncode=0)
    ).kind is tr.StepKind.ADOPT_RESOLVED
    step = tr.next_step(_resolved_snapshot(returncode=1, cli_returncode=0))
    assert step.kind is tr.StepKind.INVALID
    assert step.invalid_code is tr.InvalidCode.TERMINAL_AUTHORITY_CONFLICT
    assert "CLI code" in step.detail


def test_validation_precedes_conflict_and_terminal():
    snapshot = replace(
        _complete_timeout_snapshot(),
        child_exit=tr.ExitFact(tr.Presence.INVALID, detail="signature mismatch"),
    )
    step = tr.next_step(snapshot)
    assert step.invalid_code is tr.InvalidCode.TERMINAL_EVIDENCE_INVALID


def test_an_exit_receipt_contradicted_by_a_live_child_is_a_conflict():
    snapshot = replace(_complete_timeout_snapshot(), child_alive=True)
    assert tr.next_step(snapshot).invalid_code is tr.InvalidCode.TERMINAL_AUTHORITY_CONFLICT


def test_claim_disposition_must_be_the_observed_exit():
    snapshot = _complete_timeout_snapshot()
    snapshot = replace(snapshot, live=replace(snapshot.live, kill_disposition="SIGKILL_AFTER_DEADLINE"))
    assert tr.next_step(snapshot).invalid_code is tr.InvalidCode.TERMINAL_AUTHORITY_CONFLICT


# ---------------------------------------------------------------------------
# store の file 名と progress 操作の表
# ---------------------------------------------------------------------------


def test_store_file_names_are_spelled_only_by_their_owner():
    """store の file 名は ``store_layout`` だけが綴る（写しと drift test を作らない）。"""

    import ast

    from scripts.function_tracer_pcode.authority.process import store_layout

    names = {
        value for key, value in vars(store_layout).items()
        if key.isupper() and isinstance(value, str)
    }
    root = Path(__file__).resolve().parents[2] / "authority"
    offenders = []
    for path in sorted(root.rglob("*.py")):
        if path.name == "store_layout.py":
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        offenders += [
            f"{path.relative_to(root)}:{node.lineno} {node.value}"
            for node in ast.walk(tree)
            if isinstance(node, ast.Constant) and node.value in names
        ]
    assert offenders == []


def test_every_progress_step_has_exactly_one_durable_operation():
    from scripts.function_tracer_pcode.authority.process import terminal_transaction

    assert set(tr.StepKind) - tr.TERMINAL_STEPS == set(terminal_transaction._EXECUTORS)