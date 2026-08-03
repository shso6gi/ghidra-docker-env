"""Single production boundary for Ghidra decompilation.

With no active UNKNOWN-taxonomy pilot this is a transparent legacy call.  With
an explicitly registered Phase 6.6 route it dual-writes typed operational
authority while preserving the original result behavior.
"""

from __future__ import annotations

from typing import Any, Optional


TOP_LEVEL_SOURCE_CONTRACT = "return-analyzer-top-level-decompile-v2"
LIFECYCLE_HELPER_SOURCE_CONTRACT = "return-analyzer-lifecycle-helper-decompile-v2"
RECURRENCE_REFRESH_SOURCE_CONTRACT = "structural-recurrence-refresh-decompile-v2"
EFFECT_SUMMARY_SOURCE_CONTRACT = "callee-effect-summary-decompile-v2"
INLINE_REGION_SOURCE_CONTRACT = "inline-region-state-decompile-v2"

SEALED_DECOMPILATION_SOURCE_CONTRACTS = frozenset({
    TOP_LEVEL_SOURCE_CONTRACT,
    LIFECYCLE_HELPER_SOURCE_CONTRACT,
    RECURRENCE_REFRESH_SOURCE_CONTRACT,
    EFFECT_SUMMARY_SOURCE_CONTRACT,
    INLINE_REGION_SOURCE_CONTRACT,
})


def _active_context() -> tuple[Any, Any] | tuple[None, None]:
    from ..equivalence.v2.production_signals import (
        active_operational_authority_factory,
        active_production_pilot_session,
    )

    session = active_production_pilot_session()
    if session is None:
        return None, None
    factory = active_operational_authority_factory()
    if factory is None:
        return None, None
    return session, factory


def _record_shadow_error(exc: Exception) -> None:
    from ..equivalence.v2.production_signals import record_production_pilot_shadow_error

    record_production_pilot_shadow_error(exc)


def _emit(session: Any, signal: Any) -> int:
    from ..equivalence.v2.production_signals import emit_operational_extraction_signal

    return emit_operational_extraction_signal(
        signal, producer_site_manifest_id="decompilation-broker-operational-signal"
    )


def _emit_with_active_checkpoint(
    session: Any, signal: Any, prepared_checkpoint: Any, invocation: Any,
) -> tuple[int, Any]:
    """Commit one blocker and its ACTIVE checkpoint as one transaction."""

    active = None

    def persist_checkpoint() -> None:
        nonlocal active
        active = prepared_checkpoint.persist(invocation)

    def rollback_checkpoint() -> None:
        nonlocal active
        if active is None:
            raise ValueError("ACTIVE checkpoint rollback lacks committed authority")
        active.rollback_initialization()
        active = None

    session.record_phase7_pre_emission_activation(
        "decompilation-broker-operational-signal", signal
    )
    emitted = session._emit_domain_signal_with_commit(
        signal, persist_checkpoint, rollback_checkpoint
    )
    return emitted, active


def _program_seed(session: Any, factory: Any, program: Any) -> Any:
    seeds = session.domain_signal_state.setdefault("operational_program_seeds", {})
    existing = seeds.get(id(program))
    if existing is not None:
        return existing
    identities = session.domain_signal_state.get(
        "operational_program_binary_identities", {}
    )
    binary_identity = identities.get(id(program))
    if type(binary_identity) is not str or not binary_identity:
        raise ValueError("operational program lacks binary content authority")
    seed = factory.issue_program_seed(
        program, binary_content_identity=binary_identity,
    )
    seeds[id(program)] = seed
    return seed


class _BrokeredDecompileResults:
    def __init__(
        self, raw_result: Any, *, session: Any, factory: Any, target: Any,
        input_surface: Any, decompilation_artifact: Any,
    ) -> None:
        self._raw_result = raw_result
        self._session = session
        self._factory = factory
        self._target = target
        self._input_surface = input_surface
        self._decompilation_artifact = decompilation_artifact
        self._high_resolved = False
        self._high_function = None
        self._high_exception = None

    def __getattr__(self, name: str) -> Any:
        return getattr(self._raw_result, name)

    def getHighFunction(self) -> Any:
        if self._high_resolved:
            if self._high_exception is not None:
                raise self._high_exception
            return self._high_function
        self._high_resolved = True

        blocker = high_q = None
        try:
            from ..equivalence.v2.operational_extraction import (
                OperationalBlockerSignal,
            )

            blocker = OperationalBlockerSignal(
                "high_function_ir_unavailable",
                self._target,
                ("completed_decompilation_getHighFunction",),
                "high-function-ir-validator-v2",
                "high-function-ir:" + self._decompilation_artifact.artifact_digest,
            )
            _emit(self._session, blocker)
            authority = self._session.domain_signal_encoder.authority_for_signal(
                self._session, blocker
            )
            high_q = authority.occurrence.proof_requirement_ids[0]
        except Exception as exc:
            _record_shadow_error(exc)

        if blocker is None or high_q is None:
            try:
                self._high_function = self._raw_result.getHighFunction()
            except Exception as exc:
                self._high_exception = exc
                _record_shadow_error(exc)
                raise
            return self._high_function

        try:
            raw_high, capability = self._factory.observe_high_function(
                artifact=self._decompilation_artifact,
                target=self._target,
                input_surface=self._input_surface,
                proof_requirement_id=high_q,
            )
        except Exception as exc:
            self._high_exception = exc
            _record_shadow_error(exc)
            raise

        # Establish the exact legacy return value before any shadow-only IR
        # validation or event emission can fail.
        self._high_function = raw_high
        if capability is None:
            return self._high_function

        try:
            from ..equivalence.v2.operational_extraction import OperationalCompletionSignal

            ir_artifact = self._factory.issue_ir_artifact(
                capability=capability,
                decompilation_artifact=self._decompilation_artifact,
                target=self._target,
                input_surface=self._input_surface,
            )
            _emit(self._session, OperationalCompletionSignal(blocker, ir_artifact))
        except Exception as exc:
            _record_shadow_error(exc)
        return self._high_function


class _AuthorityBlockedDecompileResults:
    """A non-decompiled result used after subordinate authority refusal."""

    def __init__(self, *, diagnostic: Any, error_kind: str | None = None) -> None:
        self.authority_diagnostic = diagnostic
        self.authority_error_kind = error_kind

    def decompileCompleted(self) -> bool:
        return False

    def getHighFunction(self) -> Any:
        return None

    def getErrorMessage(self) -> str:
        return (
            "subordinate decompilation was blocked by parent authority: "
            f"{self.authority_diagnostic.diagnostic_kind}"
        )


_SUBORDINATE_PARENT_PROOF_DIAGNOSTIC_KINDS = frozenset({
    "PARENT_C_Q_AMBIGUOUS",
    "PARENT_C_Q_BINDING_MISMATCH",
})


def _subordinate_decompile(
    decompiler: Any, analyzer: Any, function: Any, timeout: int, monitor: Any,
    *, session: Any, factory: Any, source_contract_id: str,
    parent_binding: Any = None,
) -> Any:
    assignment_factory = assignment = invocation_binding = None
    target = input_surface = invocation = projection = prefix = None
    prepared_checkpoint = active_checkpoint = None
    try:
        from ..equivalence.v2.subordinate_decompilation import (
            SubordinateParentAuthorityError,
            SubordinateParentNotLive,
            SubordinateProcessAssignmentFactory,
        )

        prefix = session.recorder.prefix_view()
        projection = session.reducer.replay_prefix(prefix)
        factories = session.domain_signal_state.setdefault(
            "subordinate_decompilation_assignment_factories", {}
        )
        assignment_factory = factories.get(session.identity.result_occurrence_id)
        if assignment_factory is None:
            assignment_factory = SubordinateProcessAssignmentFactory(
                session.identity.result_occurrence_id
            )
            factories[session.identity.result_occurrence_id] = assignment_factory
        program_seed = _program_seed(session, factory, analyzer.program)
        target = factory.target_from_ghidra(program_seed, function)
        input_surface = factory.input_surface_from_ghidra(function)
        assignment = assignment_factory.issue_for_source(
            projection, prefix, source_contract_id,
            parent_binding=parent_binding,
        )
        from ..equivalence.v2.process_worker_runtime import runtime_for_session

        runtime = runtime_for_session(session)
        if runtime is not None:
            prepared_checkpoint = runtime.prepare_subordinate(
                session=session, operational_factory=factory,
                assignment=assignment, assignment_factory=assignment_factory,
                projection=projection, prefix=prefix,
            )
        attempt_identity = factory.issue_attempt_identity(
            target=target,
            input_surface=input_surface,
            source_contract_id=source_contract_id,
            configured_timeout_seconds=timeout,
        )
        invocation = factory.issue_invocation_for_attempt(
            target=target,
            input_surface=input_surface,
            attempt_identity=attempt_identity,
            proof_requirement_id=assignment.proof_requirement_id,
        )
        invocation_binding = assignment_factory.bind_invocation(
            assignment, projection=projection, prefix=prefix,
            invocation=invocation, operational_factory=factory,
        )
        if prepared_checkpoint is not None:
            active_checkpoint = prepared_checkpoint.persist(invocation)
    except SubordinateParentNotLive:
        return decompile_function(
            analyzer,
            function,
            timeout,
            monitor,
            source_contract_id=source_contract_id,
            semantic_owner="slice6",
        )
    except SubordinateParentAuthorityError as exc:
        diagnostics = session.domain_signal_state.setdefault(
            "subordinate_parent_authority_diagnostics", []
        )
        signed = exc.diagnostic.to_signed_authority_dict()
        if signed not in diagnostics:
            diagnostics.append(signed)
        assignment_factory = assignment = invocation_binding = None
        if target is None:
            raise ValueError(
                "subordinate parent authority failure lacks a typed target"
            )
        if exc.diagnostic.diagnostic_kind in _SUBORDINATE_PARENT_PROOF_DIAGNOSTIC_KINDS:
            from ..equivalence.v2.operational_extraction import (
                OperationalBlockerSignal,
            )

            blocker = OperationalBlockerSignal(
                "subordinate_parent_authority_unproven",
                target,
                (
                    "source_contract_id:" + source_contract_id,
                    "diagnostic_kind:" + exc.diagnostic.diagnostic_kind,
                    "diagnostic_digest:" + exc.diagnostic.diagnostic_digest,
                    "projection_digest:" + exc.diagnostic.projection_digest,
                ),
                "subordinate-parent-authority-producer-v2",
                "subordinate-authority-" + exc.diagnostic.diagnostic_digest[:32],
            )
            emitted = _emit(session, blocker)
            if emitted != 1:
                raise ValueError(
                    "subordinate parent authority UNKNOWN blocker was not canonicalized"
                )
            return _AuthorityBlockedDecompileResults(
                diagnostic=exc.diagnostic,
            )
        error = factory.issue_error(
            error_kind="operational_authority_invalid",
            catch_site_contract_id=source_contract_id,
            target=target,
            exception_class_identity=(
                type(exc).__module__ + "." + type(exc).__qualname__
            ),
        )
        session.emit(factory.error_event_intent(error))
        return _AuthorityBlockedDecompileResults(
            diagnostic=exc.diagnostic,
            error_kind="operational_authority_invalid",
        )
    except Exception as exc:
        _record_shadow_error(exc)
        assignment_factory = assignment = invocation_binding = None

    try:
        result = decompiler.decompileFunction(function, timeout, monitor)
    except Exception as exc:
        if active_checkpoint is not None:
            try:
                error = factory.issue_error(
                    error_kind="analysis_exception",
                    catch_site_contract_id=source_contract_id,
                    target=target, invocation=invocation,
                    input_surface=input_surface,
                    exception_class_identity=(
                        type(exc).__module__ + "." + type(exc).__qualname__
                    ),
                )
                session.emit(factory.error_event_intent(error))
                active_checkpoint.resolve(error_artifact=error)
            except Exception as shadow_exc:
                _record_shadow_error(shadow_exc)
        _record_shadow_error(exc)
        raise

    if invocation_binding is None:
        return result
    try:
        observation = factory.capture_attempt_observation(invocation, result)
        attempt = factory.issue_attempt(
            invocation=invocation, observation=observation,
            target=target, input_surface=input_surface,
        )
        artifact = None
        if observation.disposition.value == "COMPLETED":
            artifact = factory.issue_decompilation_artifact(
                target=target, input_surface=input_surface,
                invocation=invocation, observation=observation, attempt=attempt,
            )
        execution = assignment_factory.bind_execution(
            invocation_binding, assignment=assignment,
            projection=projection, prefix=prefix, attempt=attempt,
            completed_artifact=artifact, operational_factory=factory,
        )
        session.domain_signal_state.setdefault(
            "subordinate_decompilation_executions", []
        ).append((assignment, invocation_binding, execution))
        if active_checkpoint is not None:
            from ..equivalence.v2.operational_extraction import (
                DecompilationDisposition,
            )
            from ..equivalence.v2.stream import (
                EventIntent,
                EventType,
                ProcessCompletionEventAuthority,
                ProcessExecutionEventAuthority,
            )

            disposition = observation.disposition
            if disposition is DecompilationDisposition.COMPLETED:
                session.emit(EventIntent(
                    EventType.PROCESS_COMPLETED,
                    ProcessCompletionEventAuthority(
                        invocation.proof_requirement_id,
                        invocation.invocation_identity,
                        execution.execution_receipt_digest,
                    ),
                ))
                active_checkpoint.resolve(
                    attempt=attempt, completed_artifact=artifact,
                    subordinate_execution=execution,
                )
            elif disposition is DecompilationDisposition.TIMED_OUT:
                session.emit(EventIntent(
                    EventType.PROCESS_TIMEOUT,
                    ProcessExecutionEventAuthority(
                        invocation.proof_requirement_id,
                        invocation.invocation_identity,
                    ),
                ))
                active_checkpoint.resolve(attempt=attempt)
            else:
                error_kind = {
                    DecompilationDisposition.FAILED_TO_START:
                        "decompiler_failed_to_start",
                    DecompilationDisposition.CANCELLED: "decompiler_cancelled",
                    DecompilationDisposition.ABORTED: "decompiler_aborted",
                }[disposition]
                error = factory.issue_error(
                    error_kind=error_kind,
                    catch_site_contract_id=source_contract_id,
                    target=target, attempt=attempt,
                )
                session.emit(factory.error_event_intent(error))
                active_checkpoint.resolve(
                    attempt=attempt, error_artifact=error,
                )
    except Exception as exc:
        _record_shadow_error(exc)
    return result


def decompile_function(
    analyzer: Any,
    function: Any,
    timeout: int,
    monitor: Any = None,
    *,
    source_contract_id: str,
    semantic_owner: str = "slice6",
    parent_binding: Any = None,
) -> Any:
    """Invoke Ghidra exactly once and optionally dual-write Phase 6.6 authority."""

    if source_contract_id not in SEALED_DECOMPILATION_SOURCE_CONTRACTS:
        raise ValueError("decompilation source contract is not sealed")
    if semantic_owner not in {"slice6", "subordinate", "diagnostic"}:
        raise ValueError("decompilation semantic owner is not sealed")
    if semantic_owner != "subordinate" and parent_binding is not None:
        raise ValueError("parent binding is only valid for subordinate decompilation")
    decompiler = analyzer._get_decompiler()
    session, factory = _active_context()
    if session is None or factory is None:
        return decompiler.decompileFunction(function, timeout, monitor)
    if semantic_owner == "subordinate":
        return _subordinate_decompile(
            decompiler, analyzer, function, timeout, monitor,
            session=session, factory=factory,
            source_contract_id=source_contract_id,
            parent_binding=parent_binding,
        )
    if semantic_owner != "slice6":
        return decompiler.decompileFunction(function, timeout, monitor)

    target = input_surface = invocation = blocker = None
    prepared_checkpoint = active_checkpoint = None
    try:
        from ..equivalence.v2.operational_extraction import OperationalBlockerSignal

        with session.domain_signal_transaction():
            program_seed = _program_seed(session, factory, analyzer.program)
            target = factory.target_from_ghidra(program_seed, function)
            input_surface = factory.input_surface_from_ghidra(function)
            attempt_identity = factory.issue_attempt_identity(
                target=target,
                input_surface=input_surface,
                source_contract_id=source_contract_id,
                configured_timeout_seconds=timeout,
            )
            blocker = OperationalBlockerSignal(
                "function_decompilation_artifact_unavailable",
                target,
                (source_contract_id,),
                "function-decompilation-artifact-producer-v2",
                attempt_identity.attempt_id,
            )
            authority = session.domain_signal_encoder.authority_for_signal(
                session, blocker
            )
            decomp_q = authority.occurrence.proof_requirement_ids[0]
            from ..equivalence.v2.process_worker_runtime import runtime_for_session

            runtime = runtime_for_session(session)
            if runtime is not None:
                prepared_checkpoint = runtime.prepare_observation(
                    session=session,
                    operational_factory=factory,
                    occurrence_authority=authority,
                    reason_id="function_decompilation_artifact_unavailable",
                    proof_requirement_id=decomp_q,
                )
                if prepared_checkpoint.assignment.payload[
                    "proof_requirement_id"
                ] != decomp_q:
                    raise ValueError(
                        "process assignment differs from prepared decompilation Q"
                    )
            invocation = factory.issue_invocation_for_attempt(
                target=target,
                input_surface=input_surface,
                attempt_identity=attempt_identity,
                proof_requirement_id=decomp_q,
            )
            if prepared_checkpoint is None:
                emitted = _emit(session, blocker)
            else:
                emitted, active_checkpoint = _emit_with_active_checkpoint(
                    session, blocker, prepared_checkpoint, invocation
                )
            if emitted != 1:
                raise ValueError(
                    "decompilation blocker observation was not committed"
                )
            if (
                prepared_checkpoint is not None
                and active_checkpoint is None
            ):
                raise ValueError(
                    "decompilation ACTIVE checkpoint was not committed"
                )
    except Exception as exc:
        _record_shadow_error(exc)
        target = input_surface = invocation = blocker = None

    try:
        result = decompiler.decompileFunction(function, timeout, monitor)
    except Exception as exc:
        if target is not None and invocation is not None:
            try:
                error = factory.issue_error(
                    error_kind="analysis_exception",
                    catch_site_contract_id=source_contract_id,
                    target=target,
                    invocation=invocation,
                    input_surface=input_surface,
                    exception_class_identity=(
                        type(exc).__module__ + "." + type(exc).__qualname__
                    ),
                )
                session.emit(factory.error_event_intent(error))
                if active_checkpoint is not None:
                    active_checkpoint.resolve(error_artifact=error)
            except Exception as shadow_exc:
                _record_shadow_error(shadow_exc)
        raise

    if invocation is None:
        return result
    try:
        from ..equivalence.v2.operational_extraction import (
            DecompilationDisposition,
            OperationalCompletionSignal,
        )
        from ..equivalence.v2.stream import (
            EventIntent,
            EventType,
            ProcessExecutionEventAuthority,
        )

        observation = factory.capture_attempt_observation(invocation, result)
        attempt = factory.issue_attempt(
            invocation=invocation,
            observation=observation,
            target=target,
            input_surface=input_surface,
        )
        if observation.disposition == DecompilationDisposition.COMPLETED:
            artifact = factory.issue_decompilation_artifact(
                target=target,
                input_surface=input_surface,
                invocation=invocation,
                observation=observation,
                attempt=attempt,
            )
            _emit(session, OperationalCompletionSignal(blocker, artifact))
            if active_checkpoint is not None:
                active_checkpoint.resolve(
                    attempt=attempt, completed_artifact=artifact,
                )
            return _BrokeredDecompileResults(
                result, session=session, factory=factory, target=target,
                input_surface=input_surface, decompilation_artifact=artifact,
            )
        if observation.disposition == DecompilationDisposition.TIMED_OUT:
            session.emit(EventIntent(
                EventType.PROCESS_TIMEOUT,
                ProcessExecutionEventAuthority(
                    invocation.proof_requirement_id,
                    invocation.invocation_identity,
                ),
            ))
            if active_checkpoint is not None:
                active_checkpoint.resolve(attempt=attempt)
        else:
            error_kind = {
                DecompilationDisposition.FAILED_TO_START: "decompiler_failed_to_start",
                DecompilationDisposition.CANCELLED: "decompiler_cancelled",
                DecompilationDisposition.ABORTED: "decompiler_aborted",
            }[observation.disposition]
            error = factory.issue_error(
                error_kind=error_kind,
                catch_site_contract_id=source_contract_id,
                target=target,
                attempt=attempt,
            )
            session.emit(factory.error_event_intent(error))
            if active_checkpoint is not None:
                active_checkpoint.resolve(
                    attempt=attempt, error_artifact=error,
                )
    except Exception as exc:
        _record_shadow_error(exc)
    return result
