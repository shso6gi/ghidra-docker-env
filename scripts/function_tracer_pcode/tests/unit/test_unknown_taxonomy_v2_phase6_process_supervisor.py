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

