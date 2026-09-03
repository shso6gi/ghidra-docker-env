import json
import os
from dataclasses import replace
from pathlib import Path
import subprocess
import sys
from enum import Enum

import pytest

from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    authority_digest,
)
from scripts.function_tracer_pcode.equivalence.v2.decision import (
    FinalizationAuthority,
    TerminalTimeoutReceipt,
    finalize_decision,
)
from scripts.function_tracer_pcode.equivalence.v2.operational_extraction import (
    OPERATIONAL_REASON_REGISTRY,
    OPERATIONAL_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.equivalence.v2.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.equivalence.v2.stream import EventIntent
from scripts.function_tracer_pcode.equivalence.v2.process_supervisor_command import (
    ProcessSupervisorCommand,
    SupervisorCommandConfig,
    read_process_start_token,
)
from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
    CHECKPOINT_AUTHORITY_FILENAMES,
    CheckpointState,
)
from scripts.function_tracer_pcode.equivalence.v2.canonical_result import (
    classify_pair_status,
)
from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_process_supervisor import (
    _active_process_authority,
    _completed_continuation,
)


def _config(tmp_path, child_command, *, timeout=30.0):
    authority = _active_process_authority()
    supervisor_key = tmp_path / "supervisor.key"
    worker_key = tmp_path / "worker.key"
    supervisor_key.write_bytes(b"s" * 32)
    worker_key.write_bytes(b"w" * 32)
    return authority, SupervisorCommandConfig(
        checkpoint_root=tmp_path / "checkpoints",
        authority_output=tmp_path / "authority.json",
        working_directory=Path.cwd(),
        execution_nonce="execution-nonce-1",
        result_occurrence_id=(
            authority["session"].identity.result_occurrence_id
        ),
        source_snapshot_fingerprint=(
            authority["session"].identity.source_snapshot_fingerprint
        ),
        stream_id=authority["prefix"].stream_id,
        deadline_policy_digest="deadline-policy-digest",
        supervisor_signing_key_id="supervisor-key-v1",
        supervisor_signing_key_file=supervisor_key,
        worker_signing_key_id="worker-key-v1",
        worker_signing_key_file=worker_key,
        timeout_seconds=timeout,
        kill_grace_seconds=0.1,
        child_command=tuple(child_command),
    )


def _projection(path):
    payload = json.loads(path.read_text(encoding="utf-8"))
    digest = payload.pop("projection_digest")
    assert digest == authority_digest(payload)
    return payload


def _classify_durable_projection(command):
    config = command.config
    return classify_pair_status(
        config.working_directory / "unused-terminal-log",
        config.authority_output,
        checkpoint_root=config.checkpoint_root,
        execution_nonce=config.execution_nonce,
        supervisor_signing_key_id=config.supervisor_signing_key_id,
        supervisor_signing_key_file=config.supervisor_signing_key_file,
        worker_signing_key_id=config.worker_signing_key_id,
        worker_signing_key_file=config.worker_signing_key_file,
    )


def _json_authority_value(value):
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, dict):
        return {str(key): _json_authority_value(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [_json_authority_value(item) for item in value]
    return value


def _persistable_authority(value):
    return _json_authority_value({
        name: getattr(value, name)
        for name in value.__dataclass_fields__
        if not name.startswith("_")
    })


def _persist_active_for_command(command, authority):
    launch = command.factory.issue_launch(
        result_occurrence_id=command.config.result_occurrence_id,
        manifest_entry_preimage_digest=command.config.manifest_entry_preimage_digest,
        execution_nonce=command.config.execution_nonce,
        child_pid=4242, child_start_token="pid-start-token",
        stream_id=command.config.stream_id,
        source_snapshot_fingerprint=command.config.source_snapshot_fingerprint,
        deadline_policy_digest=command.config.deadline_policy_digest,
    )
    assignment = command.factory.decode(authority["assignment"].to_dict())
    checkpoint = command.factory.issue_active_checkpoint(
        launch=launch, prefix=authority["prefix"],
        projection=authority["projection"], assignment=assignment,
        invocation=authority["invocation"],
        operational_factory=authority["operational_factory"],
        worker_pid=4242, worker_start_token="pid-start-token",
    )
    command.store.persist_launch(launch)
    command.store.persist_active(checkpoint, authority["prefix"])
    return launch, checkpoint


def _child_persist_active(*, sleep_seconds, ignore_sigterm=False):
    """Subprocess entry used to exercise the real launch/checkpoint boundary."""
    import signal
    import time
    from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
        DurableCheckpointStore,
        ProcessSupervisorAuthorityFactory,
    )

    authority = _active_process_authority()
    supervisor = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id=os.environ[
            "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID"
        ],
        supervisor_signing_key=Path(os.environ[
            "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE"
        ]).read_bytes(),
        worker_signing_key_id=os.environ["UNKNOWN_TAXONOMY_V2_WORKER_KEY_ID"],
        worker_signing_key=Path(os.environ[
            "UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE"
        ]).read_bytes(),
    )
    launch = supervisor.decode(json.loads(Path(os.environ[
        "UNKNOWN_TAXONOMY_V2_LAUNCH_PATH"
    ]).read_text()))
    assignment = supervisor.issue_live_assignment(
        prefix=authority["prefix"], projection=authority["projection"],
        reason_id="function_decompilation_artifact_unavailable",
    )
    checkpoint = supervisor.issue_active_checkpoint(
        launch=launch, prefix=authority["prefix"],
        projection=authority["projection"], assignment=assignment,
        invocation=authority["invocation"],
        operational_factory=authority["operational_factory"],
        worker_pid=os.getpid(),
        worker_start_token=launch.payload["child_start_token"],
    )
    store = DurableCheckpointStore(
        Path(os.environ["UNKNOWN_TAXONOMY_V2_SUPERVISOR_ROOT"]),
        supervisor, os.environ["UNKNOWN_TAXONOMY_V2_EXECUTION_NONCE"],
    )
    store.persist_active(checkpoint, authority["prefix"])
    if ignore_sigterm:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
    if sleep_seconds:
        time.sleep(sleep_seconds)


def _child_persist_canonical_production_loop_timeout():
    """Emit deployment-signed loop TIMEOUT receipts through the child boundary."""
    from types import SimpleNamespace

    from scripts.function_tracer_pcode.equivalence.v2.canonical_result import (
        build_canonical_result_finalization_bundle,
        persist_canonical_result_envelope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        activate_process_worker_execution_authority_deployment,
    )
    from scripts.function_tracer_pcode.equivalence.v2.loop_recurrence import (
        LOOP_REASON_REGISTRY,
        LOOP_RECOVERY_REGISTRY,
        LoopBlockerProductionSignal,
        LoopRecurrencePilotEncoder,
        LoopSolverExecutionBatchSignal,
    )
    from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
        runtime_from_audited_manifest,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        active_loop_requirement_for_signal,
        execute_loop_solver_rendered_query,
        emit_loop_recurrence_signal,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
        render_loop_v2_solver_query,
    )
    from scripts.function_tracer_pcode.smt.interface import (
        SolverResult,
        SolverStatus,
    )
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    import scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_loop_recurrence as loop_fixture

    worker_key_file = Path(os.environ[
        "UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE"
    ])
    activate_process_worker_execution_authority_deployment(
        key_id=os.environ["UNKNOWN_TAXONOMY_V2_WORKER_KEY_ID"],
        key=worker_key_file.read_bytes(),
        key_source_id=str(worker_key_file.resolve()),
    )
    execution_module._PINNED_PARALLEL_RUN_IMPL = (
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.TIMEOUT, elapsed_time=timeout),
        ])
    )

    root = Path(__file__).resolve().parents[4]
    producer_manifest = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    loop_encoder = LoopRecurrencePilotEncoder()
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=LOOP_REASON_REGISTRY,
            recovery_registry=LOOP_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            LoopBlockerProductionSignal: loop_encoder,
            LoopSolverExecutionBatchSignal: loop_encoder,
        }),
        phase7_runtime_factory=lambda identity: runtime_from_audited_manifest(
            producer_manifest, identity
        ),
    )
    raw_payload = {"case": "supervisor-retry-timeout"}
    session = connector.begin(raw_payload)
    blocker, _, _, _, exact_case, summary_case, left, right = (
        loop_fixture._loop_exact_fixture()
    )
    with production_signal_scope(session):
        assert emit_loop_recurrence_signal(
            blocker,
            producer_site_manifest_id="pairwise-pending-loop-blocker",
        ) == 1
        requirement = active_loop_requirement_for_signal(
            blocker, "loop_exact_term_relation"
        )
        rendered = render_loop_v2_solver_query(
            blocker=blocker,
            requirement=requirement,
            analysis1=left,
            analysis2=right,
            case1=exact_case,
            case2=summary_case,
            pair_id="(supervisor,left,right)",
            execution_identity_digest=session.identity.execution_identity_digest,
        )
        assert execute_loop_solver_rendered_query(
            blocker, rendered, configured_timeout_ms=1000
        ) == 1
    legacy = SimpleNamespace(
        is_equivalent=None,
        error_message=None,
        failure_status=None,
        failure_message=None,
        is_timeout=lambda: True,
    )
    evidence = connector.finish(
        session, legacy, case_id="supervisor-retry-timeout"
    )
    preimage = {"final_outcome": "TIMEOUT", "total_time": 0.0}
    bundle = build_canonical_result_finalization_bundle(
        result_payload_preimage=preimage,
        evidence=evidence,
        session=session,
    )
    persist_canonical_result_envelope({
        **preimage,
        "canonical_result_finalization_bundle": bundle,
    })
    raise SystemExit(3)


def _child_persist_canonical_return_abi_authority_error():
    """Cross the real child/supervisor boundary with a typed ABI ERROR."""
    import time

    from scripts.function_tracer_pcode.equivalence.result_factory import (
        create_error_result,
    )
    from scripts.function_tracer_pcode.equivalence.v2.abi_width_readonly import (
        ReturnAbiAuthorityInvalid,
        assess_return_abi_pair,
    )
    from scripts.function_tracer_pcode.equivalence.v2.canonical_result import (
        attach_durable_error_finalization,
        build_canonical_result_finalization_bundle,
        persist_canonical_result_envelope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.contracts import (
        authority_digest,
    )
    from scripts.function_tracer_pcode.model import FunctionReturnAnalysis
    from scripts.function_tracer_pcode.equivalence.return_width_surface import (
        ExtensionEvidenceSource,
        FunctionReturnWidthSeed,
        FunctionReturnWidthTargetId,
        GuardRegionFact,
        GuardRegionTargetId,
    )
    from scripts.function_tracer_pcode.equivalence.return_width_surface import (
        PairReturnObservationSeed,
        PairReturnObservationTargetId,
    )

    def malformed_fixture_width_seed(side, function_identity):
        guard_target = GuardRegionTargetId(
            ("return-member", side), (("guard-slot", side),)
        )
        target = FunctionReturnWidthTargetId(
            function_identity, ("return-member", side), guard_target
        )
        return FunctionReturnWidthSeed(
            target,
            GuardRegionFact("complete", (("guard", side),)),
            64,
            32,
            ("storage", side, 64),
            ("payload", side, 32),
            ("return_type_provenance", ("declared_return_type_width", 32)),
            ExtensionEvidenceSource(
                "zero_extend",
                ("storage-value", side),
                ("payload-value", side),
                (("producer", side),),
                "certified_flow",
            ),
        )

    left_analysis = FunctionReturnAnalysis(
        "f", "0x1000", [], [], binary_id="bin-left"
    )
    right_analysis = FunctionReturnAnalysis(
        "f", "0x2000", [], [], binary_id="bin-right"
    )
    # This is deliberately malformed rather than merely absent.  An absent
    # envelope is a typed MISSING/UNKNOWN surface; a wrong schema remains an
    # authority error across the child/supervisor/classifier boundary.
    left_analysis.return_abi_facts = {"schema_version": 999}
    right_analysis.return_abi_facts = {"schema_version": 999}
    left_seed = malformed_fixture_width_seed(
        "left", function_identity=left_analysis.outcome_function_identity()
    )
    right_seed = malformed_fixture_width_seed(
        "right", function_identity=right_analysis.outcome_function_identity()
    )
    pair_target = PairReturnObservationTargetId(
        "top_level_return", left_seed.target_id, right_seed.target_id,
        (
            left_seed.target_id.function_identity,
            right_seed.target_id.function_identity,
        ),
    )
    pair_seed = PairReturnObservationSeed(
        pair_target, left_seed.digest, right_seed.digest,
        "top_level_return", pair_target.semantic_anchors,
    )
    try:
        assess_return_abi_pair(
            left_analysis, right_analysis, left_seed, right_seed, pair_seed
        )
    except ReturnAbiAuthorityInvalid as exc:
        execution_payload = {"case": "return-abi-authority-invalid"}
        result = create_error_result(
            analysis1=left_analysis,
            analysis2=right_analysis,
            binary1_name="bin-left",
            binary2_name="bin-right",
            error_message=exc.canonical_error_kind,
            start_time=time.time(),
            type_fix_result=None,
            retry_count=0,
            original_signature1=None,
            original_signature2=None,
            failure_status=exc.canonical_error_kind,
            failure_message=str(exc),
        )
        artifact_digest = authority_digest({
            "error_kind": exc.canonical_error_kind,
            "failure_message": str(exc),
        })
        attach_durable_error_finalization(
            result,
            execution_payload=execution_payload,
            error_kind=exc.canonical_error_kind,
            error_artifact_digest=artifact_digest,
        )
        result_payload = result.to_dict()
        evidence, session = result._canonical_finalization_context
        bundle = build_canonical_result_finalization_bundle(
            result_payload_preimage=result_payload,
            evidence=evidence,
            session=session,
        )
        persist_canonical_result_envelope({
            **result_payload,
            "canonical_result_finalization_bundle": bundle,
        })
        raise SystemExit(4)
    raise AssertionError("malformed ABI fixture did not fail closed")


def test_process_start_token_is_bound_to_current_linux_process():
    token = read_process_start_token(os.getpid())
    assert token.startswith("linux-proc-starttime-")
    assert token.removeprefix("linux-proc-starttime-").isascii()
    assert token.removeprefix("linux-proc-starttime-").isdecimal()

