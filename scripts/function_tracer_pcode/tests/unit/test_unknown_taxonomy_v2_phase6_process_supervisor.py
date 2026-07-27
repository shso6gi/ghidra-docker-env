from dataclasses import replace
import json
import os
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.v2.candidate import (
    build_candidate_projection,
)
from scripts.function_tracer_pcode.equivalence.v2.decision import ErrorReceipt, Outcome

from scripts.function_tracer_pcode.equivalence.v2.operational_extraction import (
    OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST,
    OPERATIONAL_REASON_REGISTRY,
    OPERATIONAL_RECOVERY_REGISTRY,
    OperationalBlockerSignal,
    OperationalCompletionSignal,
    OperationalExtractionPilotEncoder,
)
from scripts.function_tracer_pcode.equivalence.v2.pilot import (
    ProductionDualWritePilotSession,
    ProductionPilotExecutionIdentity,
)
from scripts.function_tracer_pcode.equivalence.v2.phase7_cutover import (
    ActivationDisposition,
)
from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
    runtime_from_audited_manifest,
)
from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
    CheckpointState,
    DurableCheckpointStore,
    ProcessSupervisorAuthorityFactory,
)
from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
    CompositeProductionSignalEncoder,
    production_signal_scope,
)
from scripts.function_tracer_pcode.equivalence.v2.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.equivalence.v2.stream import (
    DecisiveProofEventAuthority,
    EventIntent,
    EventType,
    ProcessExecutionEventAuthority,
)


def _active_process_authority(case="supervisor"):
    identity = ProductionPilotExecutionIdentity.create({"case": case})
    operational = OperationalExtractionPilotEncoder()
    session = ProductionDualWritePilotSession(
        identity,
        ShadowLifecycleReducer(
            reason_registry=OPERATIONAL_REASON_REGISTRY,
            recovery_registry=OPERATIONAL_RECOVERY_REGISTRY,
        ),
        CompositeProductionSignalEncoder({
            OperationalBlockerSignal: operational,
            OperationalCompletionSignal: operational,
        }),
    )
    operational_factory = operational.authority_factory_for_session(session)
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import (
        Function, Program,
    )

    manager = type("Manager", (), {
        "functions": (),
        "getFunctions": lambda self, forward: iter(self.functions),
    })()
    program = Program(manager)
    function = Function(program=program)
    manager.functions = (function,)
    program_seed = operational_factory.issue_program_seed(
        program, binary_content_identity="sha256:binary"
    )
    target = operational_factory.target_from_ghidra(program_seed, function)
    surface = operational_factory.input_surface_from_ghidra(function)
    blocker = OperationalBlockerSignal(
        "function_decompilation_artifact_unavailable", target,
        ("return-analyzer-top-level-decompile-v2",),
        "function-decompilation-artifact-producer-v2",
    )
    if os.environ.get("PHASE7_TIMEOUT_EVIDENCE_PATH"):
        from scripts.function_tracer_pcode.analysis.decompilation_broker import _emit

        root = Path(__file__).resolve().parents[4]
        producer_manifest = json.loads((root / (
            "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
        )).read_text(encoding="utf-8"))
        session.phase7_runtime = runtime_from_audited_manifest(
            producer_manifest, identity,
        )
        with production_signal_scope(session):
            assert _emit(session, blocker) == 1
    else:
        assert session.emit_domain_signal(blocker) == 1
    prefix = session.recorder.prefix_view()
    projection = session.reducer.replay_prefix(prefix)
    supervisor = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id="supervisor-key-v1",
        supervisor_signing_key=b"s" * 32,
        worker_signing_key_id="worker-key-v1",
        worker_signing_key=b"w" * 32,
    )
    assignment = supervisor.issue_live_assignment(
        prefix=prefix, projection=projection,
        reason_id="function_decompilation_artifact_unavailable",
    )
    invocation = operational_factory.issue_invocation(
        target=target, input_surface=surface,
        proof_requirement_id=assignment.payload["proof_requirement_id"],
        invocation_identity="decompile-invocation-1",
        invocation_ordinal=1, configured_timeout_seconds=60,
    )
    launch = supervisor.issue_launch(
        result_occurrence_id=identity.result_occurrence_id,
        manifest_entry_preimage_digest="manifest-preimage",
        execution_nonce="execution-nonce-1", child_pid=4242,
        child_start_token="pid-start-token", stream_id=prefix.stream_id,
        source_snapshot_fingerprint=prefix.source_snapshot_fingerprint,
        deadline_policy_digest="deadline-policy-digest",
    )
    checkpoint = supervisor.issue_active_checkpoint(
        launch=launch, prefix=prefix, projection=projection,
        assignment=assignment, invocation=invocation,
        operational_factory=operational_factory,
        worker_pid=4242, worker_start_token="pid-start-token",
    )
    return {
        "session": session,
        "prefix": prefix,
        "projection": projection,
        "supervisor": supervisor,
        "assignment": assignment,
        "invocation": invocation,
        "operational_factory": operational_factory,
        "launch": launch,
        "checkpoint": checkpoint,
        "blocker": blocker,
        "target": target,
        "surface": surface,
        "function": function,
    }


def _completed_continuation(authority, *, supervisor=None, checkpoint=None):
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import Result

    operational_factory = authority["operational_factory"]
    result = Result(completed=True, function=authority["function"])
    observation = operational_factory.capture_attempt_observation(
        authority["invocation"], result
    )
    attempt = operational_factory.issue_attempt(
        invocation=authority["invocation"], observation=observation,
        target=authority["target"], input_surface=authority["surface"],
    )
    artifact = operational_factory.issue_decompilation_artifact(
        target=authority["target"], input_surface=authority["surface"],
        invocation=authority["invocation"], observation=observation,
        attempt=attempt,
    )
    assert authority["session"].emit_domain_signal(
        OperationalCompletionSignal(authority["blocker"], artifact)
    ) == 1
    stream = authority["session"].recorder.seal()
    continuation = (supervisor or authority["supervisor"]).issue_worker_continuation(
        checkpoint=checkpoint or authority["checkpoint"], prefix=authority["prefix"],
        continuation_stream=stream, attempt=attempt,
        completed_artifact=artifact, operational_factory=operational_factory,
    )
    return continuation, stream


def test_durable_supervisor_timeout_forms_one_same_stream_terminal_event(tmp_path):
    authority = _active_process_authority()
    supervisor = authority["supervisor"]
    store = DurableCheckpointStore(tmp_path, supervisor, "execution-nonce-1")
    store.persist_launch(authority["launch"])
    store.persist_active(authority["checkpoint"], authority["prefix"])
    durable_prefix = store.rematerialize_active_prefix()
    assert durable_prefix.prefix_authority_digest == authority["prefix"].prefix_authority_digest
    claimed = store.supervisor_claim_timeout(
        active=authority["checkpoint"], prefix=authority["prefix"],
        kill_disposition="SIGKILL_AFTER_DEADLINE",
    )
    timeout, segment = supervisor.issue_supervisor_timeout(
        claimed=claimed, prefix=authority["prefix"],
    )
    final = store.finalize_timeout(
        claimed=claimed, timeout=timeout, segment=segment,
        prefix=authority["prefix"],
    )
    bundle = supervisor.issue_timeout_bundle(
        launch=authority["launch"], checkpoint=authority["checkpoint"],
        claimed=claimed, timeout=timeout, segment=segment,
        final_transition=final, prefix=authority["prefix"],
    )
    assert store.read_state().payload["state"] == CheckpointState.TIMED_OUT.value
    assert len(segment.composite_stream.events) == len(authority["prefix"].events) + 1
    terminal = segment.composite_stream.events[-1]
    assert terminal.header.event_type is EventType.PROCESS_TIMEOUT
    assert terminal.header.stream_id == authority["prefix"].stream_id
    assert terminal.header.predecessor_authority_digest == authority["prefix"].events[-1].authority_digest
    assert bundle.proof_requirement_id == authority["assignment"].payload["proof_requirement_id"]
    assert (store.directory / "launch.json").exists()
    assert (store.directory / "timeout.json").exists()
    assert (store.directory / "terminal-segment.json").exists()
    rematerialized = store.rematerialize_timeout_bundle(prefix=authority["prefix"])
    supervisor.validate_timeout_bundle(
        rematerialized, launch=supervisor.decode(authority["launch"].to_dict()),
        checkpoint=supervisor.decode(authority["checkpoint"].to_dict()),
        claimed=supervisor.decode(claimed.to_dict()),
        timeout=supervisor.decode(timeout.to_dict()),
        segment=rematerialized.terminal_segment,
        final_transition=store.read_state(), prefix=authority["prefix"],
    )
    with pytest.raises(TypeError, match="exact factory membership"):
        supervisor.validate_timeout_bundle(
            replace(rematerialized), launch=authority["launch"],
            checkpoint=authority["checkpoint"], claimed=claimed,
            timeout=timeout, segment=segment, final_transition=final,
            prefix=authority["prefix"],
        )


def test_worker_continuation_and_crash_window_forbid_timeout_claim(tmp_path):
    authority = _active_process_authority()
    supervisor = authority["supervisor"]
    store = DurableCheckpointStore(tmp_path, supervisor, "execution-nonce-1")
    store.persist_launch(authority["launch"])
    store.persist_active(authority["checkpoint"], authority["prefix"])
    continuation, continuation_stream = _completed_continuation(authority)
    # Simulate crash after durable continuation publication and before state CAS.
    store.worker_publish_continuation(
        active=authority["checkpoint"], continuation=continuation,
        prefix=authority["prefix"], continuation_stream=continuation_stream,
    )
    recovered = store.supervisor_claim_timeout(
        active=authority["checkpoint"], prefix=authority["prefix"],
        kill_disposition="SIGKILL_AFTER_DEADLINE",
    )
    assert recovered.payload["state"] == CheckpointState.RESOLVED.value
    assert store.read_state().receipt_digest == recovered.receipt_digest
    assert (store.directory / "recovery-resolution.json").exists()


def test_worker_continuation_marker_is_committed_after_stream(
    tmp_path, monkeypatch,
):
    authority = _active_process_authority()
    supervisor = authority["supervisor"]
    store = DurableCheckpointStore(tmp_path, supervisor, "execution-nonce-1")
    store.persist_launch(authority["launch"])
    store.persist_active(authority["checkpoint"], authority["prefix"])
    continuation, continuation_stream = _completed_continuation(authority)
    original_write = store._atomic_write
    member_writes = []

    def interrupt_second_member(path, data, *, identical_ok=False):
        if path.name in {"continuation.json", "continuation-stream.json"}:
            member_writes.append(path.name)
            if len(member_writes) == 2:
                raise RuntimeError("fault injection before continuation commit")
        return original_write(path, data, identical_ok=identical_ok)

    monkeypatch.setattr(store, "_atomic_write", interrupt_second_member)
    with pytest.raises(RuntimeError, match="fault injection"):
        store.worker_publish_continuation(
            active=authority["checkpoint"], continuation=continuation,
            prefix=authority["prefix"], continuation_stream=continuation_stream,
        )

    assert member_writes == [
        "continuation-stream.json",
        "continuation.json",
    ]
    assert (store.directory / "continuation-stream.json").is_file()
    assert not (store.directory / "continuation.json").exists()
    claimed = store.supervisor_claim_timeout(
        active=authority["checkpoint"], prefix=authority["prefix"],
        kill_disposition="SIGKILL_AFTER_DEADLINE",
    )
    assert claimed.payload["state"] == CheckpointState.TIMED_OUT_CLAIMED.value


def test_worker_completion_uses_active_ready_resolved_chain(tmp_path):
    authority = _active_process_authority()
    supervisor = authority["supervisor"]
    store = DurableCheckpointStore(tmp_path, supervisor, "execution-nonce-1")
    store.persist_launch(authority["launch"])
    store.persist_active(authority["checkpoint"], authority["prefix"])
    continuation, continuation_stream = _completed_continuation(authority)
    ready, resolved = store.worker_publish_completion(
        active=authority["checkpoint"], continuation=continuation,
        prefix=authority["prefix"], continuation_stream=continuation_stream,
    )
    assert ready.payload["state"] == CheckpointState.COMPLETION_READY.value
    assert resolved.payload["state"] == CheckpointState.RESOLVED.value
    assert store.read_state().receipt_digest == resolved.receipt_digest
    with pytest.raises(ValueError, match="lost checkpoint CAS"):
        store.supervisor_claim_timeout(
            active=authority["checkpoint"], prefix=authority["prefix"],
            kill_disposition="SIGKILL_AFTER_DEADLINE",
        )


@pytest.mark.parametrize(
    "case,expected_kind",
    (
        ("timeout", "TIMED_OUT_ATTEMPT"),
        ("failed", "ERROR"),
        ("exception", "ERROR"),
    ),
)
def test_worker_noncompletion_continuations_resolve_without_fabricating_timeout(
    tmp_path, case, expected_kind,
):
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import Result

    authority = _active_process_authority(case=f"continuation-{case}")
    supervisor = authority["supervisor"]
    store = DurableCheckpointStore(tmp_path, supervisor, "execution-nonce-1")
    store.persist_launch(authority["launch"])
    store.persist_active(authority["checkpoint"], authority["prefix"])
    factory = authority["operational_factory"]
    attempt = error = None
    if case == "exception":
        error = factory.issue_error(
            error_kind="analysis_exception",
            catch_site_contract_id="return-analyzer-top-level-decompile-v2",
            target=authority["target"],
            exception_class_identity="builtins.RuntimeError",
            invocation=authority["invocation"],
            input_surface=authority["surface"],
        )
        authority["session"].emit(factory.error_event_intent(error))
    else:
        result = Result(
            timed_out=case == "timeout", failed=case == "failed",
            function=authority["function"],
        )
        observation = factory.capture_attempt_observation(
            authority["invocation"], result
        )
        attempt = factory.issue_attempt(
            invocation=authority["invocation"], observation=observation,
            target=authority["target"], input_surface=authority["surface"],
        )
        if case == "timeout":
            authority["session"].emit(EventIntent(
                EventType.PROCESS_TIMEOUT,
                ProcessExecutionEventAuthority(
                    attempt.proof_requirement_id,
                    authority["invocation"].invocation_identity,
                ),
            ))
        else:
            error = factory.issue_error(
                error_kind="decompiler_failed_to_start",
                catch_site_contract_id="return-analyzer-top-level-decompile-v2",
                target=authority["target"], attempt=attempt,
            )
            authority["session"].emit(factory.error_event_intent(error))
    continuation_stream = authority["session"].recorder.seal()
    continuation = supervisor.issue_worker_continuation(
        checkpoint=authority["checkpoint"], prefix=authority["prefix"],
        continuation_stream=continuation_stream,
        operational_factory=factory, attempt=attempt,
        error_artifact=error,
    )
    assert continuation.payload["continuation_kind"] == expected_kind
    _ready, resolved = store.worker_publish_completion(
        active=authority["checkpoint"], continuation=continuation,
        prefix=authority["prefix"], continuation_stream=continuation_stream,
    )
    assert resolved.payload["state"] == CheckpointState.RESOLVED.value
    durable = store.rematerialize_resolved_state(prefix=authority["prefix"])
    assert durable.receipt_digest == resolved.receipt_digest
    assert not (store.directory / "timeout.json").exists()


def test_attemptless_error_rejects_same_result_different_invocation():
    authority = _active_process_authority(case="cross-invocation-error")
    factory = authority["operational_factory"]
    other_invocation = factory.issue_invocation(
        target=authority["target"], input_surface=authority["surface"],
        proof_requirement_id=authority["invocation"].proof_requirement_id,
        invocation_identity="different-invocation", invocation_ordinal=2,
        configured_timeout_seconds=60,
    )
    error = factory.issue_error(
        error_kind="analysis_exception",
        catch_site_contract_id="return-analyzer-top-level-decompile-v2",
        target=authority["target"], exception_class_identity="builtins.RuntimeError",
        invocation=other_invocation, input_surface=authority["surface"],
    )
    authority["session"].emit(factory.error_event_intent(error))
    stream = authority["session"].recorder.seal()
    with pytest.raises(ValueError, match="ERROR continuation authority differs"):
        authority["supervisor"].issue_worker_continuation(
            checkpoint=authority["checkpoint"], prefix=authority["prefix"],
            continuation_stream=stream, operational_factory=factory,
            error_artifact=error,
        )


def test_worker_continuation_rejects_foreign_operational_factory_root():
    from scripts.function_tracer_pcode.equivalence.v2.operational_extraction import OperationalExtractionAuthorityFactory
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import surface, target

    authority = _active_process_authority(case="foreign-root-error")
    foreign = OperationalExtractionAuthorityFactory(
        result_occurrence_id=authority["session"].identity.result_occurrence_id,
        source_snapshot_fingerprint=(
            authority["session"].identity.source_snapshot_fingerprint
        ),
        execution_identity_digest=(
            authority["session"].identity.execution_identity_digest
        ),
        allow_fixture_inputs=True,
    )
    foreign_target = target(factory=foreign)
    foreign_surface = surface(factory=foreign)
    foreign_invocation = foreign.issue_invocation(
        target=foreign_target, input_surface=foreign_surface,
        proof_requirement_id=authority["invocation"].proof_requirement_id,
        invocation_identity="foreign-invocation", invocation_ordinal=1,
        configured_timeout_seconds=60,
    )
    error = foreign.issue_error(
        error_kind="analysis_exception",
        catch_site_contract_id="return-analyzer-top-level-decompile-v2",
        target=foreign_target, exception_class_identity="builtins.RuntimeError",
        invocation=foreign_invocation, input_surface=foreign_surface,
    )
    authority["session"].emit(foreign.error_event_intent(error))
    stream = authority["session"].recorder.seal()
    with pytest.raises(ValueError, match="dependencies do not join checkpoint"):
        authority["supervisor"].issue_worker_continuation(
            checkpoint=authority["checkpoint"], prefix=authority["prefix"],
            continuation_stream=stream, operational_factory=foreign,
            error_artifact=error,
        )


def test_timeout_attempt_rejects_cross_kind_error_event():
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import Result

    authority = _active_process_authority(case="cross-kind-timeout")
    factory = authority["operational_factory"]
    observation = factory.capture_attempt_observation(
        authority["invocation"],
        Result(timed_out=True, function=authority["function"]),
    )
    attempt = factory.issue_attempt(
        invocation=authority["invocation"], observation=observation,
        target=authority["target"], input_surface=authority["surface"],
    )
    error = factory.issue_error(
        error_kind="analysis_exception",
        catch_site_contract_id="return-analyzer-top-level-decompile-v2",
        target=authority["target"], exception_class_identity="builtins.RuntimeError",
        invocation=authority["invocation"], input_surface=authority["surface"],
    )
    authority["session"].emit(factory.error_event_intent(error))
    stream = authority["session"].recorder.seal()
    with pytest.raises(ValueError, match="timeout continuation authority differs"):
        authority["supervisor"].issue_worker_continuation(
            checkpoint=authority["checkpoint"], prefix=authority["prefix"],
            continuation_stream=stream, operational_factory=factory,
            attempt=attempt,
        )


def test_timeout_authority_is_deterministic_and_receipts_are_not_copyable(tmp_path):
    authority = _active_process_authority()
    supervisor = authority["supervisor"]
    store = DurableCheckpointStore(tmp_path, supervisor, "execution-nonce-1")
    store.persist_launch(authority["launch"])
    store.persist_active(authority["checkpoint"], authority["prefix"])
    claimed = store.supervisor_claim_timeout(
        active=authority["checkpoint"], prefix=authority["prefix"],
        kill_disposition="SIGKILL",
    )
    first_timeout, first_segment = supervisor.issue_supervisor_timeout(
        claimed=claimed, prefix=authority["prefix"],
    )
    second_timeout, second_segment = supervisor.issue_supervisor_timeout(
        claimed=claimed, prefix=authority["prefix"],
    )
    assert first_timeout.to_dict() == second_timeout.to_dict()
    assert first_segment.segment_digest == second_segment.segment_digest
    with pytest.raises(TypeError, match="exact factory membership"):
        supervisor.validate(replace(first_timeout))


def test_checkpoint_rejects_wrong_pid_policy_live_q_and_state_edges(tmp_path):
    authority = _active_process_authority()
    supervisor = authority["supervisor"]
    with pytest.raises(ValueError, match="launch/prefix/live Q"):
        supervisor.issue_active_checkpoint(
            launch=authority["launch"], prefix=authority["prefix"],
            projection=authority["projection"], assignment=authority["assignment"],
            invocation=authority["invocation"],
            operational_factory=authority["operational_factory"],
            worker_pid=9999, worker_start_token="pid-start-token",
        )
    assert not hasattr(supervisor, "issue_transition")
    store = DurableCheckpointStore(tmp_path, supervisor, "execution-nonce-1")
    assert not hasattr(store, "cas_transition")
    assert not hasattr(store, "publish_continuation")
    with pytest.raises(ValueError, match="durable launch"):
        store.persist_active(authority["checkpoint"], authority["prefix"])
    store.persist_launch(authority["launch"])
    store.persist_active(authority["checkpoint"], authority["prefix"])
    (store.directory / "state.json").write_text("{torn", encoding="utf-8")
    with pytest.raises(ValueError, match="missing or torn"):
        store.read_state()


def test_wrong_key_and_terminal_predecessor_are_rejected(tmp_path):
    authority = _active_process_authority()
    other = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id="other-supervisor-key",
        supervisor_signing_key=b"o" * 32,
        worker_signing_key_id="other-worker-key",
        worker_signing_key=b"x" * 32,
    )
    with pytest.raises((TypeError, ValueError)):
        other.decode(authority["launch"].to_dict())
    supervisor = authority["supervisor"]
    store = DurableCheckpointStore(tmp_path, supervisor, "execution-nonce-1")
    store.persist_launch(authority["launch"])
    store.persist_active(authority["checkpoint"], authority["prefix"])
    claimed = store.supervisor_claim_timeout(
        active=authority["checkpoint"], prefix=authority["prefix"],
        kill_disposition="SIGKILL",
    )
    timeout, segment = supervisor.issue_supervisor_timeout(
        claimed=claimed, prefix=authority["prefix"],
    )
    forged_event = replace(
        segment.composite_stream.events[-1],
        header=replace(
            segment.composite_stream.events[-1].header,
            predecessor_authority_digest=authority["prefix"].prefix_authority_digest,
        ),
    )
    forged_stream = replace(
        segment.composite_stream,
        events=segment.composite_stream.events[:-1] + (forged_event,),
    )
    with pytest.raises(ValueError):
        replace(segment, composite_stream=forged_stream).validate(
            authority["prefix"], timeout
        )
    store.finalize_timeout(
        claimed=claimed, timeout=timeout, segment=segment,
        prefix=authority["prefix"],
    )
    terminal_path = store.directory / "terminal-stream.json"
    terminal_path.write_text(
        terminal_path.read_text(encoding="utf-8").replace(
            "PROCESS_TIMEOUT", "ERROR", 1
        ),
        encoding="utf-8",
    )
    with pytest.raises(ValueError, match="missing or invalid"):
        store.rematerialize_terminal_segment(authority["prefix"], timeout)


def test_process_assignment_registry_digest_is_pinned():
    authority = _active_process_authority()
    assert authority["assignment"].payload["producer_registry_digest"] == OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST


def test_before_checkpoint_deadline_forms_durable_empty_prefix_error(tmp_path):
    authority = _active_process_authority()
    store = DurableCheckpointStore(
        tmp_path, authority["supervisor"], "execution-nonce-1"
    )
    store.persist_launch(authority["launch"])
    bundle = store.supervisor_finalize_operational_error(
        launch=authority["launch"],
        error_kind="operational_authority_invalid",
        deadline_stage="BEFORE_CHECKPOINT",
        child_exit_disposition="SIGKILL_BEFORE_CHECKPOINT",
    )
    stream = bundle.terminal_segment.composite_stream
    assert len(stream.events) == 1
    assert stream.events[0].header.sequence_number == 1
    assert stream.events[0].header.predecessor_authority_digest == "0" * 64
    assert stream.events[0].header.event_type is EventType.ERROR
    assert bundle.terminal_segment.worker_prefix_kind == "EMPTY"
    reduction = authority["session"].reducer.replay(stream)
    assert reduction.projection.c_active_base == ()
    assert reduction.projection.q_open_base == ()
    error_receipt = ErrorReceipt.create(
        result_occurrence_id=reduction.snapshot.result_occurrence_id,
        lifecycle_projection_digest=(
            reduction.projection.lifecycle_projection_digest
        ),
        error_kind=bundle.error_kind,
        error_artifact_digest=bundle.error_receipt_digest,
    )
    candidate = build_candidate_projection(
        reduction, error_receipts=(error_receipt,)
    )
    assert candidate.decision_receipt.outcome is Outcome.ERROR
    rematerialized = store.rematerialize_operational_error_bundle()
    assert rematerialized.bundle_digest == bundle.bundle_digest


def test_before_checkpoint_error_can_join_verified_nonterminal_prefix(tmp_path):
    authority = _active_process_authority()
    store = DurableCheckpointStore(
        tmp_path, authority["supervisor"], "execution-nonce-1"
    )
    store.persist_launch(authority["launch"])
    bundle = store.supervisor_finalize_operational_error(
        launch=authority["launch"],
        error_kind="operational_authority_invalid",
        deadline_stage="BEFORE_CHECKPOINT",
        child_exit_disposition="SIGKILL_AFTER_PREFIX_BEFORE_CHECKPOINT",
        prefix=authority["prefix"],
    )
    stream = bundle.terminal_segment.composite_stream
    assert stream.events[:-1] == authority["prefix"].events
    assert stream.events[-1].header.predecessor_authority_digest == (
        authority["prefix"].events[-1].authority_digest
    )
    reduction = authority["session"].reducer.replay(stream)
    assert reduction.snapshot.error_event_bindings == ((
        "operational_authority_invalid", bundle.error_receipt_digest,
    ),)
    rematerialized = store.rematerialize_operational_error_bundle()
    assert rematerialized.bundle_digest == bundle.bundle_digest


def test_operational_error_requires_durable_launch_and_no_checkpoint(tmp_path):
    authority = _active_process_authority()
    assert not hasattr(authority["supervisor"], "issue_operational_error")
    assert not hasattr(authority["supervisor"], "issue_operational_error_segment")
    assert not hasattr(authority["supervisor"], "issue_operational_error_bundle")
    wrong_nonce = DurableCheckpointStore(
        tmp_path / "wrong-nonce", authority["supervisor"], "another-nonce"
    )
    with pytest.raises(ValueError, match="execution nonce"):
        wrong_nonce.persist_launch(authority["launch"])
    missing = DurableCheckpointStore(
        tmp_path / "missing", authority["supervisor"], "execution-nonce-1"
    )
    with pytest.raises(ValueError, match="durable launch"):
        missing.supervisor_finalize_operational_error(
            launch=authority["launch"],
            error_kind="operational_authority_invalid",
            deadline_stage="BEFORE_CHECKPOINT",
            child_exit_disposition="SIGKILL",
        )
    active = DurableCheckpointStore(
        tmp_path / "active", authority["supervisor"], "execution-nonce-1"
    )
    active.persist_launch(authority["launch"])
    active.persist_active(authority["checkpoint"], authority["prefix"])
    with pytest.raises(ValueError, match="cannot replace checkpoint"):
        active.supervisor_finalize_operational_error(
            launch=authority["launch"],
            error_kind="operational_authority_invalid",
            deadline_stage="BEFORE_CHECKPOINT",
            child_exit_disposition="SIGKILL",
        )


def test_operational_error_rejects_foreign_prefix_and_persisted_tamper(tmp_path):
    authority = _active_process_authority()
    foreign = _active_process_authority("foreign-operational-error")
    foreign["prefix"].validate()
    store = DurableCheckpointStore(
        tmp_path, authority["supervisor"], "execution-nonce-1"
    )
    store.persist_launch(authority["launch"])
    with pytest.raises(ValueError):
        store.supervisor_finalize_operational_error(
            launch=authority["launch"],
            error_kind="operational_authority_invalid",
            deadline_stage="BEFORE_CHECKPOINT",
            child_exit_disposition="SIGKILL",
            prefix=foreign["prefix"],
        )
    bundle = store.supervisor_finalize_operational_error(
        launch=authority["launch"],
        error_kind="operational_authority_invalid",
        deadline_stage="BEFORE_CHECKPOINT",
        child_exit_disposition="SIGKILL",
    )
    assert bundle.error_kind == "operational_authority_invalid"
    stream_path = store.directory / "operational-error-stream.json"
    stream_path.write_text(
        stream_path.read_text(encoding="utf-8").replace(
            "operational_authority_invalid",
            "forged_operational_error_kind",
            1,
        ),
        encoding="utf-8",
    )
    with pytest.raises(ValueError, match="missing or invalid"):
        store.rematerialize_operational_error_bundle()


def test_operational_error_rejects_torn_signed_launch(tmp_path):
    authority = _active_process_authority()
    store = DurableCheckpointStore(
        tmp_path, authority["supervisor"], "execution-nonce-1"
    )
    store.persist_launch(authority["launch"])
    launch_path = store.directory / "launch.json"
    launch_path.write_text("{torn", encoding="utf-8")
    with pytest.raises(ValueError, match="durable launch"):
        store.supervisor_finalize_operational_error(
            launch=authority["launch"],
            error_kind="operational_authority_invalid",
            deadline_stage="BEFORE_CHECKPOINT",
            child_exit_disposition="SIGKILL",
        )


@pytest.mark.parametrize(
    "terminal_type", (EventType.EQ_CLOSURE, EventType.COUNTEREXAMPLE)
)
def test_operational_error_rejects_already_decisive_prefix(
    tmp_path, terminal_type,
):
    authority = _active_process_authority()
    authority["session"].recorder.append(EventIntent(
        terminal_type, DecisiveProofEventAuthority("decisive-proof-artifact"),
    ))
    decisive_prefix = authority["session"].recorder.prefix_view()
    decisive_prefix.validate()
    store = DurableCheckpointStore(
        tmp_path, authority["supervisor"], "execution-nonce-1"
    )
    store.persist_launch(authority["launch"])
    with pytest.raises(ValueError, match="prefix differs from launch"):
        store.supervisor_finalize_operational_error(
            launch=authority["launch"],
            error_kind="operational_authority_invalid",
            deadline_stage="BEFORE_CHECKPOINT",
            child_exit_disposition="SIGKILL",
            prefix=decisive_prefix,
        )
