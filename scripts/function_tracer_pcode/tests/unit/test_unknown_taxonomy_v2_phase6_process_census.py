from dataclasses import replace

import pytest

from scripts.function_tracer_pcode.equivalence.v2.contracts import authority_digest

from scripts.function_tracer_pcode.equivalence.v2.operational_extraction import (
    OperationalCompletionSignal,
)
from scripts.function_tracer_pcode.equivalence.v2.process_census import (
    ProcessAttemptCensusFactory,
    consume_durable_supervisor_projection,
)
from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
    DurableCheckpointStore,
)
from scripts.function_tracer_pcode.equivalence.v2.process_supervisor_command import (
    COMMAND_SCHEMA,
)
from scripts.function_tracer_pcode.equivalence.v2.stream import (
    EventIntent,
    EventType,
    ProcessExecutionEventAuthority,
)
from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_process_supervisor import (
    _active_process_authority,
)
from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import (
    Result,
)


def _membership(authority, census_factory, invocation=None):
    return census_factory.register_operational(
        invocation or authority["invocation"],
        authority["operational_factory"],
        assignment=authority["assignment"],
        process_authority_factory=authority["supervisor"],
    )


def _attempt(authority, invocation, result):
    operational = authority["operational_factory"]
    observation = operational.capture_attempt_observation(invocation, result)
    attempt = operational.issue_attempt(
        invocation=invocation, observation=observation,
        target=authority["target"], input_surface=authority["surface"],
    )
    return observation, attempt


def test_structured_worker_timeout_with_exact_event_is_terminal_candidate():
    authority = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    membership = _membership(authority, census_factory)
    _, attempt = _attempt(
        authority, authority["invocation"],
        Result(timed_out=True, function=authority["function"]),
    )
    event = authority["session"].recorder.append(EventIntent(
        EventType.PROCESS_TIMEOUT,
        ProcessExecutionEventAuthority(
            membership.proof_requirement_id, membership.invocation_identity,
        ),
    ))
    stream = authority["session"].recorder.seal()
    census_factory.record_attempt(
        membership, attempt=attempt,
        operational_factory=authority["operational_factory"],
        process_timeout_event=event,
        process_timeout_stream=stream,
    )
    census = census_factory.seal()
    final = authority["session"].reducer.replay(stream)
    selection = census_factory.select_terminal_timeout(
        census, final.snapshot, final.projection
    )
    assert selection is not None
    assert selection.selected_proof_requirement_id == membership.proof_requirement_id
    assert selection.selected_event_or_bundle_digest == event.authority_digest
    census_factory.validate_selection(
        selection, census, final.snapshot, final.projection
    )
    with pytest.raises(TypeError, match="exact factory membership"):
        census_factory.validate_selection(
            replace(selection), census, final.snapshot, final.projection
        )


def test_later_success_closes_q_and_suppresses_older_timeout():
    authority = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    first_membership = _membership(authority, census_factory)
    _, first_attempt = _attempt(
        authority, authority["invocation"],
        Result(timed_out=True, function=authority["function"]),
    )
    first_event = authority["session"].recorder.append(EventIntent(
        EventType.PROCESS_TIMEOUT,
        ProcessExecutionEventAuthority(
            first_membership.proof_requirement_id,
            first_membership.invocation_identity,
        ),
    ))
    second = authority["operational_factory"].issue_invocation(
        target=authority["target"], input_surface=authority["surface"],
        proof_requirement_id=first_membership.proof_requirement_id,
        invocation_identity="decompile-invocation-2", invocation_ordinal=2,
        configured_timeout_seconds=60,
    )
    second_membership = _membership(authority, census_factory, second)
    observation, second_attempt = _attempt(
        authority, second,
        Result(completed=True, function=authority["function"]),
    )
    artifact = authority["operational_factory"].issue_decompilation_artifact(
        target=authority["target"], input_surface=authority["surface"],
        invocation=second, observation=observation, attempt=second_attempt,
    )
    census_factory.record_attempt(
        second_membership, attempt=second_attempt,
        operational_factory=authority["operational_factory"],
    )
    authority["session"].emit_domain_signal(
        OperationalCompletionSignal(authority["blocker"], artifact)
    )
    stream = authority["session"].recorder.seal()
    census_factory.record_attempt(
        first_membership, attempt=first_attempt,
        operational_factory=authority["operational_factory"],
        process_timeout_event=first_event,
        process_timeout_stream=stream,
    )
    census = census_factory.seal()
    final = authority["session"].reducer.replay(stream)
    assert final.projection.q_open_base == ()
    assert census_factory.select_terminal_timeout(
        census, final.snapshot, final.projection
    ) is None


def test_later_structured_error_has_precedence_over_older_timeout():
    authority = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    first_membership = _membership(authority, census_factory)
    _, first_attempt = _attempt(
        authority, authority["invocation"],
        Result(timed_out=True, function=authority["function"]),
    )
    first_event = authority["session"].recorder.append(EventIntent(
        EventType.PROCESS_TIMEOUT,
        ProcessExecutionEventAuthority(
            first_membership.proof_requirement_id,
            first_membership.invocation_identity,
        ),
    ))
    second = authority["operational_factory"].issue_invocation(
        target=authority["target"], input_surface=authority["surface"],
        proof_requirement_id=first_membership.proof_requirement_id,
        invocation_identity="decompile-invocation-2", invocation_ordinal=2,
        configured_timeout_seconds=60,
    )
    second_membership = _membership(authority, census_factory, second)
    _, second_attempt = _attempt(
        authority, second,
        Result(failed=True, function=authority["function"]),
    )
    error = authority["operational_factory"].issue_error(
        error_kind="decompiler_failed_to_start",
        catch_site_contract_id="return-analyzer-top-level-decompile-v2",
        target=authority["target"], attempt=second_attempt,
    )
    error_event = authority["session"].recorder.append(
        authority["operational_factory"].error_event_intent(error)
    )
    stream = authority["session"].recorder.seal()
    census_factory.record_error(
        second_membership, error=error, attempt=second_attempt,
        operational_factory=authority["operational_factory"],
        error_event=error_event, error_event_stream=stream,
    )
    census_factory.record_attempt(
        first_membership, attempt=first_attempt,
        operational_factory=authority["operational_factory"],
        process_timeout_event=first_event,
        process_timeout_stream=stream,
    )
    census = census_factory.seal()
    final = authority["session"].reducer.replay(stream)
    assert final.projection.q_open_base
    assert census_factory.select_terminal_timeout(
        census, final.snapshot, final.projection
    ) is None


@pytest.mark.parametrize("entry_kind", ("timeout_without_event", "receiptless"))
def test_noneligible_attempts_never_authorize_terminal_timeout(entry_kind):
    authority = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    membership = _membership(authority, census_factory)
    if entry_kind == "timeout_without_event":
        _, attempt = _attempt(
            authority, authority["invocation"],
            Result(timed_out=True, function=authority["function"]),
        )
        census_factory.record_attempt(
            membership, attempt=attempt,
            operational_factory=authority["operational_factory"],
        )
    else:
        census_factory.record_receiptless(
            membership, reason="worker_exited_without_result",
        )
    census = census_factory.seal()
    final = authority["session"].reducer.replay(
        authority["session"].recorder.seal()
    )
    assert census_factory.select_terminal_timeout(
        census, final.snapshot, final.projection
    ) is None


def test_supervisor_bundle_is_terminal_candidate_and_census_is_complete(tmp_path):
    authority = _active_process_authority()
    worker_stream = authority["session"].recorder.seal()
    worker_final = authority["session"].reducer.replay(worker_stream)
    store = DurableCheckpointStore(
        tmp_path, authority["supervisor"], "execution-nonce-1"
    )
    store.persist_launch(authority["launch"])
    store.persist_active(authority["checkpoint"], authority["prefix"])
    claimed = store.supervisor_claim_timeout(
        active=authority["checkpoint"], prefix=authority["prefix"],
        kill_disposition="SIGKILL",
    )
    timeout, segment = authority["supervisor"].issue_supervisor_timeout(
        claimed=claimed, prefix=authority["prefix"],
    )
    final_state = store.finalize_timeout(
        claimed=claimed, timeout=timeout, segment=segment,
        prefix=authority["prefix"],
    )
    bundle = authority["supervisor"].issue_timeout_bundle(
        launch=authority["launch"], checkpoint=authority["checkpoint"],
        claimed=claimed, timeout=timeout, segment=segment,
        final_transition=final_state, prefix=authority["prefix"],
    )
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    membership = _membership(authority, census_factory)
    projection_body = {
        "status": "TIMEOUT",
        "authority_kind": "DurableTimeoutFinalizationBundle",
        "launch_receipt_digest": authority["launch"].receipt_digest,
        "finalization_bundle_digest": bundle.bundle_digest,
        "event_stream_authority_digest": bundle.composite_stream_authority_digest,
        "proof_requirement_id": bundle.proof_requirement_id,
        "child_returncode": -9,
        "projection_schema": COMMAND_SCHEMA,
    }
    projection = {
        **projection_body,
        "projection_digest": authority_digest(projection_body),
    }
    foreign_assignment_census = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    foreign_assignment_membership = foreign_assignment_census._register(
        authority["invocation"], authority["operational_factory"],
        assignment_receipt_digest="foreign-assignment-receipt",
        terminal_priority=authority["assignment"].payload["terminal_priority"],
        ownership_kind="OPERATIONAL",
    )
    with pytest.raises(ValueError, match="bundle differs from membership"):
        consume_durable_supervisor_projection(
            projection, store=store,
            process_authority_factory=authority["supervisor"],
            census_factory=foreign_assignment_census,
            membership=foreign_assignment_membership,
        )
    consumed = consume_durable_supervisor_projection(
        projection, store=store,
        process_authority_factory=authority["supervisor"],
        census_factory=census_factory, membership=membership,
    )
    assert consumed.status == "TIMEOUT"
    assert consumed.continuation_kind is None
    census = census_factory.seal()
    final = authority["session"].reducer.replay(
        segment.composite_stream
    )
    selection = census_factory.select_terminal_timeout(
        census, final.snapshot, final.projection
    )
    assert selection.selected_event_or_bundle_digest == bundle.bundle_digest
    census_factory.validate_selection(
        selection, census, final.snapshot, final.projection
    )
    with pytest.raises(ValueError, match="FINAL event binding"):
        census_factory.select_terminal_timeout(
            census, worker_final.snapshot, worker_final.projection
        )
    with pytest.raises(TypeError, match="exact sealed census"):
        census_factory.select_terminal_timeout(
            replace(census), final.snapshot, final.projection
        )
    different_invocation = authority["operational_factory"].issue_invocation(
        target=authority["target"], input_surface=authority["surface"],
        proof_requirement_id=authority["invocation"].proof_requirement_id,
        invocation_identity=authority["invocation"].invocation_identity,
        invocation_ordinal=2, configured_timeout_seconds=60,
    )
    different_census = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    different_membership = different_census._register(
        different_invocation, authority["operational_factory"],
        assignment_receipt_digest=authority["assignment"].receipt_digest,
        terminal_priority=authority["assignment"].payload["terminal_priority"],
        ownership_kind="OPERATIONAL",
    )
    with pytest.raises(ValueError, match="bundle differs from membership"):
        consume_durable_supervisor_projection(
            projection, store=store,
            process_authority_factory=authority["supervisor"],
            census_factory=different_census, membership=different_membership,
        )


def test_operational_error_projection_requires_exact_durable_bundle(tmp_path):
    authority = _active_process_authority()
    store = DurableCheckpointStore(
        tmp_path, authority["supervisor"], "execution-nonce-1"
    )
    store.persist_launch(authority["launch"])
    bundle = store.supervisor_finalize_operational_error(
        launch=authority["launch"],
        error_kind="operational_authority_invalid",
        deadline_stage="BEFORE_CHECKPOINT",
        child_exit_disposition="SIGTERM_AFTER_DEADLINE",
    )
    body = {
        "status": "ERROR",
        "authority_kind": "DurableErrorFinalizationBundle",
        "launch_receipt_digest": authority["launch"].receipt_digest,
        "finalization_bundle_digest": bundle.bundle_digest,
        "event_stream_authority_digest": bundle.composite_stream_authority_digest,
        "child_returncode": -15,
        "projection_schema": COMMAND_SCHEMA,
    }
    projection = {**body, "projection_digest": authority_digest(body)}
    consumed = consume_durable_supervisor_projection(
        projection, store=store,
        process_authority_factory=authority["supervisor"],
    )
    assert consumed.status == "ERROR"
    assert consumed.process_census_entry_digest is None
    tampered_body = {**body, "finalization_bundle_digest": "tampered"}
    with pytest.raises(ValueError, match="differs from durable bundle"):
        consume_durable_supervisor_projection(
            {**tampered_body, "projection_digest": authority_digest(tampered_body)},
            store=store, process_authority_factory=authority["supervisor"],
        )


def test_unrecorded_membership_and_duplicate_ordinal_are_invalid():
    authority = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    _membership(authority, census_factory)
    with pytest.raises(ValueError, match="missing registered"):
        census_factory.seal()
    with pytest.raises(ValueError, match="globally unique"):
        _membership(authority, census_factory)


def test_exact_census_entry_digest_is_revalidated_before_selection():
    authority = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    membership = _membership(authority, census_factory)
    entry = census_factory.record_receiptless(
        membership, reason="worker_exited_without_result",
    )
    census = census_factory.seal()
    final = authority["session"].reducer.replay(
        authority["session"].recorder.seal()
    )
    object.__setattr__(entry, "receiptless_reason", "tampered")
    with pytest.raises(ValueError, match="entry digest mismatch"):
        census_factory.select_terminal_timeout(
            census, final.snapshot, final.projection
        )


def test_issued_but_unregistered_invocation_prevents_census_seal():
    authority = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    membership = _membership(authority, census_factory)
    census_factory.record_receiptless(
        membership, reason="worker_exited_without_result",
    )
    authority["operational_factory"].issue_invocation(
        target=authority["target"], input_surface=authority["surface"],
        proof_requirement_id=membership.proof_requirement_id,
        invocation_identity="decompile-invocation-unregistered",
        invocation_ordinal=2, configured_timeout_seconds=60,
    )
    with pytest.raises(ValueError, match="issuer invocation census"):
        census_factory.seal()


def test_invocation_issued_after_seal_invalidates_prior_census():
    authority = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    membership = _membership(authority, census_factory)
    census_factory.record_receiptless(
        membership, reason="worker_exited_without_result",
    )
    census = census_factory.seal()
    authority["operational_factory"].issue_invocation(
        target=authority["target"], input_surface=authority["surface"],
        proof_requirement_id=membership.proof_requirement_id,
        invocation_identity="decompile-invocation-after-seal",
        invocation_ordinal=2, configured_timeout_seconds=60,
    )
    final = authority["session"].reducer.replay(
        authority["session"].recorder.seal()
    )
    with pytest.raises(ValueError, match="stale or invalid"):
        census_factory.select_terminal_timeout(
            census, final.snapshot, final.projection
        )


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("proof_requirement_id", "tampered-q"),
        ("invocation_ordinal", 99),
        ("terminal_priority", 999),
    ),
)
def test_membership_selection_fields_are_digest_revalidated(field, value):
    authority = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    membership = _membership(authority, census_factory)
    object.__setattr__(membership, field, value)
    with pytest.raises(ValueError, match="membership digest mismatch"):
        census_factory.record_receiptless(
            membership, reason="worker_exited_without_result",
        )


def test_nested_supervisor_terminal_segment_tamper_is_rejected(tmp_path):
    authority = _active_process_authority()
    store = DurableCheckpointStore(
        tmp_path, authority["supervisor"], "execution-nonce-1"
    )
    store.persist_launch(authority["launch"])
    store.persist_active(authority["checkpoint"], authority["prefix"])
    claimed = store.supervisor_claim_timeout(
        active=authority["checkpoint"], prefix=authority["prefix"],
        kill_disposition="SIGKILL",
    )
    timeout, segment = authority["supervisor"].issue_supervisor_timeout(
        claimed=claimed, prefix=authority["prefix"],
    )
    final_state = store.finalize_timeout(
        claimed=claimed, timeout=timeout, segment=segment,
        prefix=authority["prefix"],
    )
    bundle = authority["supervisor"].issue_timeout_bundle(
        launch=authority["launch"], checkpoint=authority["checkpoint"],
        claimed=claimed, timeout=timeout, segment=segment,
        final_transition=final_state, prefix=authority["prefix"],
    )
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    membership = _membership(authority, census_factory)
    object.__setattr__(
        bundle.terminal_segment, "terminal_event_sequence",
        bundle.terminal_segment.terminal_event_sequence + 1,
    )
    with pytest.raises(ValueError, match="membership integrity mismatch"):
        census_factory.record_supervisor_timeout(
            membership, checkpoint=authority["checkpoint"], bundle=bundle,
            process_authority_factory=authority["supervisor"],
        )


def test_error_entry_requires_its_exact_published_error_event():
    authority = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    membership = _membership(authority, census_factory)
    _, attempt = _attempt(
        authority, authority["invocation"],
        Result(failed=True, function=authority["function"]),
    )
    error = authority["operational_factory"].issue_error(
        error_kind="decompiler_failed_to_start",
        catch_site_contract_id="return-analyzer-top-level-decompile-v2",
        target=authority["target"], attempt=attempt,
    )
    wrong_error = authority["operational_factory"].issue_error(
        error_kind="decompiler_failed_to_start",
        catch_site_contract_id="pairwise-top-level-decompile-v2",
        target=authority["target"], attempt=attempt,
    )
    wrong_event = authority["session"].recorder.append(
        authority["operational_factory"].error_event_intent(wrong_error)
    )
    stream = authority["session"].recorder.seal()
    with pytest.raises(ValueError, match="error event differs"):
        census_factory.record_error(
            membership, error=error, attempt=attempt,
            operational_factory=authority["operational_factory"],
            error_event=wrong_event, error_event_stream=stream,
        )


def test_process_census_rejects_mixed_operational_issuer_factories():
    authority = _active_process_authority()
    foreign = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    _membership(authority, census_factory)
    with pytest.raises(ValueError, match="mix operational issuer factories"):
        _membership(foreign, census_factory)


def test_record_attempt_rejects_foreign_factory_same_digest_evidence():
    authority = _active_process_authority()
    foreign = _active_process_authority()
    assert (
        authority["invocation"].receipt_digest
        == foreign["invocation"].receipt_digest
    )
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    membership = _membership(authority, census_factory)
    _, foreign_attempt = _attempt(
        foreign, foreign["invocation"],
        Result(timed_out=True, function=foreign["function"]),
    )
    with pytest.raises(ValueError, match="membership operational issuer"):
        census_factory.record_attempt(
            membership, attempt=foreign_attempt,
            operational_factory=foreign["operational_factory"],
        )


def test_record_error_rejects_foreign_factory_same_digest_evidence():
    authority = _active_process_authority()
    foreign = _active_process_authority()
    census_factory = ProcessAttemptCensusFactory(
        authority["session"].identity.result_occurrence_id
    )
    membership = _membership(authority, census_factory)
    _, foreign_attempt = _attempt(
        foreign, foreign["invocation"],
        Result(failed=True, function=foreign["function"]),
    )
    foreign_error = foreign["operational_factory"].issue_error(
        error_kind="decompiler_failed_to_start",
        catch_site_contract_id="return-analyzer-top-level-decompile-v2",
        target=foreign["target"], attempt=foreign_attempt,
    )
    foreign_event = foreign["session"].recorder.append(
        foreign["operational_factory"].error_event_intent(foreign_error)
    )
    foreign_stream = foreign["session"].recorder.seal()
    with pytest.raises(ValueError, match="membership operational issuer"):
        census_factory.record_error(
            membership, error=foreign_error, attempt=foreign_attempt,
            operational_factory=foreign["operational_factory"],
            error_event=foreign_event, error_event_stream=foreign_stream,
        )
