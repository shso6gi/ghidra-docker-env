"""Narrow v1-preserving dual-write pilot for explicit v2 lifecycle signals."""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
import os
import secrets
from threading import RLock
from typing import Any, Callable, Dict, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.authority.decision.candidate import (
    CandidateDecisionProjection,
    build_candidate_projection,
)
from scripts.function_tracer_pcode.authority.contracts import (
    Outcome,
    authority_digest,
    canonical_value,
)
from scripts.function_tracer_pcode.authority.decision.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    ErrorReceipt,
    TerminalTimeoutReceipt,
)
from scripts.function_tracer_pcode.authority.lifecycle.reducer import (
    ShadowLifecycleReducer,
    ShadowReductionResult,
)
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
    CauseObservedEventAuthority,
    DecisiveProofEventAuthority,
    ErrorEventAuthority,
    EventType,
    EventRecorder,
    GenericReceiptBoundSolverExecutionEventAuthority,
    ProcessExecutionEventAuthority,
    ReceiptBoundSolverExecutionEventAuthority,
    SealedEventStream,
    SolverExecutionEventAuthority,
)
from scripts.function_tracer_pcode.authority.domains.return_outcome import (
    OUTCOME_STAGE_REASON_MATRIX,
)
from scripts.function_tracer_pcode.authority.domains.call_effect import CALL_EFFECT_REASON_SPECS
from scripts.function_tracer_pcode.authority.domains.loop_recurrence import LOOP_REASON_SPECS
from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
    ABI_WIDTH_READONLY_REASON_SPECS,
)
from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
    ANALYSIS_LIMITATION_REASON_REGISTRY,
)


PILOT_TYPED_CAUSE_KINDS = frozenset({
    "return_coverage_gap",
    "return_coverage_inconclusive",
    "outcome_partition_residual_sat",
    "counterexample_analysis_safety_unproven",
    "counterexample_partition_replay_ambiguous",
    "counterexample_replay_unproven",
    "comparison_equivalence_closure_unproven",
    "pair_process_completion_unavailable",
}) | frozenset(
    reason_id for reason_id in OUTCOME_STAGE_REASON_MATRIX.values()
    if reason_id is not None
) | frozenset(CALL_EFFECT_REASON_SPECS) | frozenset(LOOP_REASON_SPECS) | frozenset(
    ABI_WIDTH_READONLY_REASON_SPECS
) | frozenset({
    "function_decompilation_artifact_unavailable",
    "high_function_ir_unavailable",
    "subordinate_parent_authority_unproven",
}) | frozenset(
    # Issue #125: analysis_limitation domain の sealed reason（現状 1 個）。
    # registry から導くので、domain へ reason を足したら自動で追従する。
    item.reason_id for item in ANALYSIS_LIMITATION_REASON_REGISTRY.snapshot()
)

PILOT_EVENT_TYPES = frozenset({
    EventType.CAUSE_OBSERVED,
    EventType.REQUIREMENT_COMPLETED,
    EventType.CAUSE_TRANSFORMED,
    EventType.OUTCOME_PRODUCER_ATTEMPT,
    EventType.SOLVER_UNKNOWN,
    EventType.SOLVER_TIMEOUT,
    EventType.SOLVER_ERROR,
    EventType.PROCESS_COMPLETED,
    EventType.PROCESS_TIMEOUT,
    EventType.EQ_CLOSURE,
    EventType.COUNTEREXAMPLE,
    EventType.ERROR,
})

RESULT_ENTRY_OCCURRENCE_NONCE_ENV = (
    "UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE"
)


@dataclass(frozen=True)
class TerminalizationIntent:
    """Explicitly promotes one recorded timeout observation to final authority."""

    event_sequence_number: int
    proof_requirement_id: str

    def __post_init__(self) -> None:
        if type(self.event_sequence_number) is not int or self.event_sequence_number <= 0:
            raise TypeError("terminalization sequence must be a positive exact integer")
        if type(self.proof_requirement_id) is not str or not self.proof_requirement_id:
            raise TypeError("terminalization requirement ID must be a non-empty exact string")


@dataclass(frozen=True)
class TerminalCandidateView:
    lifecycle_projection_digest: str
    timeout_candidates: Tuple[Tuple[int, str, str], ...]
    counterexample_event_digests: Tuple[str, ...]
    error_event_digests: Tuple[str, ...]
    competing_decisive_event_digests: Tuple[str, ...]
    view_digest: str

    @classmethod
    def freeze(cls, session: Any, lifecycle_projection: Any) -> "TerminalCandidateView":
        events = (
            session.recorder.prefix_view().events
            if session.recorder.event_count else ()
        )
        open_ids = {
            row.proof_requirement_id for row in lifecycle_projection.q_open_base
        }
        timeout_candidates = tuple(sorted(
            (
                event.header.sequence_number,
                event.authority_payload.proof_requirement_id,
                event.authority_digest,
            )
            for event in events
            if event.header.event_type in {
                EventType.SOLVER_TIMEOUT, EventType.PROCESS_TIMEOUT,
            }
            and getattr(event.authority_payload, "proof_requirement_id", None)
            in open_ids
        ))
        counterexamples = tuple(sorted(
            event.authority_digest for event in events
            if event.header.event_type is EventType.COUNTEREXAMPLE
        ))
        errors = tuple(sorted(
            event.authority_digest for event in events
            if event.header.event_type is EventType.ERROR
        ))
        competing = tuple(sorted(
            event.authority_digest for event in events
            if event.header.event_type is EventType.EQ_CLOSURE
        ))
        payload = {
            "result_occurrence_id": session.identity.result_occurrence_id,
            "lifecycle_projection_digest": (
                getattr(lifecycle_projection, "lifecycle_projection_digest", None)
                or lifecycle_projection.prefix_projection_digest
            ),
            "timeout_candidates": timeout_candidates,
            "counterexample_event_digests": counterexamples,
            "error_event_digests": errors,
            "competing_decisive_event_digests": competing,
        }
        return cls(
            payload["lifecycle_projection_digest"],
            timeout_candidates,
            counterexamples,
            errors,
            competing,
            authority_digest(payload),
        )


@dataclass(frozen=True)
class DualWritePilotResult:
    legacy_outcome_before: Outcome
    legacy_outcome_after: Outcome
    sealed_event_stream: SealedEventStream
    reduction: ShadowReductionResult
    candidate: CandidateDecisionProjection
    attempted_solver_event_count: int
    bound_solver_event_count: int
    observed_nonterminal_timeout_event_count: int
    terminal_timeout_receipt_count: int
    lifecycle_inference_count: int
    pilot_receipt_digest: str
    execution_authority_evidence_digests: Tuple[str, ...] = ()
    decisive_proof_receipts: Tuple[DecisiveProofReceipt, ...] = ()
    terminal_timeout_receipts: Tuple[TerminalTimeoutReceipt, ...] = ()
    error_receipts: Tuple[ErrorReceipt, ...] = ()

    @property
    def decision_delta(self) -> bool:
        return self.legacy_outcome_after != self.candidate.decision_receipt.outcome

    def validate(self) -> None:
        if self.legacy_outcome_before != self.legacy_outcome_after:
            raise ValueError("dual-write pilot changed the v1 final outcome")
        for receipt in (
            *self.decisive_proof_receipts,
            *self.terminal_timeout_receipts,
            *self.error_receipts,
        ):
            receipt.validate()
        self.sealed_event_stream.validate()
        self.reduction.snapshot.validate()
        self.reduction.projection.validate()
        self.candidate.validate()
        if self.candidate.decision_receipt.lifecycle_projection_digest != (
            self.reduction.projection.lifecycle_projection_digest
        ):
            raise ValueError("pilot candidate is not bound to reducer output")
        if self.reduction.snapshot.event_stream_authority_digest != (
            self.sealed_event_stream.envelope.authority_chain_digest
        ):
            raise ValueError("pilot result is not bound to its sealed event stream")
        solver_event_digests = tuple(
            recorded.authority_digest
            for recorded in self.sealed_event_stream.events
            if type(recorded.authority_payload) in (
                SolverExecutionEventAuthority,
                ReceiptBoundSolverExecutionEventAuthority,
                GenericReceiptBoundSolverExecutionEventAuthority,
            )
        )
        bound_solver_event_count = sum(
            digest in set(self.reduction.snapshot.execution_event_digests)
            for digest in solver_event_digests
        )
        timeout_event_digests = {
            recorded.authority_digest
            for recorded in self.sealed_event_stream.events
            if recorded.header.event_type
            in {EventType.SOLVER_TIMEOUT, EventType.PROCESS_TIMEOUT}
        }
        terminal_event_digests = set(
            self.candidate.terminal_execution_event_digests
        )
        if not terminal_event_digests.issubset(timeout_event_digests):
            raise ValueError("pilot terminal receipt does not select a timeout event")
        explicit_occurrence_authorities = tuple(sorted(
            (
                recorded.authority_payload.occurrence_authority
                for recorded in self.sealed_event_stream.events
                if recorded.header.event_type == EventType.CAUSE_OBSERVED
            ),
            key=lambda item: item.occurrence.occurrence_id,
        ))
        inferred = int(
            explicit_occurrence_authorities
            != self.reduction.snapshot.occurrence_authorities
        )
        if self.attempted_solver_event_count != len(solver_event_digests):
            raise ValueError("pilot attempted solver event count differs from stream")
        if self.bound_solver_event_count != bound_solver_event_count:
            raise ValueError("pilot bound solver event count differs from reducer evidence")
        if self.bound_solver_event_count != self.attempted_solver_event_count:
            raise ValueError("solver event requirement identity coverage is incomplete")
        if self.terminal_timeout_receipt_count != len(terminal_event_digests):
            raise ValueError("pilot terminal timeout count differs from receipts")
        if self.observed_nonterminal_timeout_event_count != (
            len(timeout_event_digests) - len(terminal_event_digests)
        ):
            raise ValueError("pilot nonterminal timeout count differs from stream")
        if self.lifecycle_inference_count != inferred or inferred != 0:
            raise ValueError("v2 pilot lifecycle inference is forbidden")
        if self.observed_nonterminal_timeout_event_count < 0:
            raise ValueError("pilot nonterminal timeout count is negative")
        expected = authority_digest({
            "legacy_outcome_before": self.legacy_outcome_before.value,
            "legacy_outcome_after": self.legacy_outcome_after.value,
            "snapshot_digest": self.reduction.snapshot.snapshot_digest,
            "lifecycle_projection_digest": self.reduction.projection.lifecycle_projection_digest,
            "candidate_projection_digest": self.candidate.projection_digest,
            "attempted_solver_event_count": self.attempted_solver_event_count,
            "bound_solver_event_count": self.bound_solver_event_count,
            "observed_nonterminal_timeout_event_count": self.observed_nonterminal_timeout_event_count,
            "terminal_timeout_receipt_count": self.terminal_timeout_receipt_count,
            "lifecycle_inference_count": self.lifecycle_inference_count,
            "execution_authority_evidence_digests": (
                self.execution_authority_evidence_digests
            ),
        })
        if expected != self.pilot_receipt_digest:
            raise ValueError("dual-write pilot receipt digest mismatch")


@dataclass(frozen=True)
class PilotDifferenceEntry:
    case_id: str
    result_occurrence_id: str
    legacy_outcome: Outcome
    candidate_outcome: Outcome
    event_stream_authority_digest: str
    lifecycle_projection_digest: str
    decision_receipt_digest: str
    pilot_receipt_digest: str
    decision_delta: bool
    entry_digest: str

    legacy_outcome_observation_receipt_digest: str

    @classmethod
    def create(
        cls,
        case_id: str,
        result: DualWritePilotResult,
        *,
        legacy_outcome_observation_receipt_digest: str,
    ) -> "PilotDifferenceEntry":
        if type(case_id) is not str or not case_id:
            raise TypeError("pilot difference case ID must be a non-empty exact string")
        if (
            type(legacy_outcome_observation_receipt_digest) is not str
            or not legacy_outcome_observation_receipt_digest
        ):
            raise TypeError("pilot difference requires a legacy observation receipt")
        result.validate()
        values = {
            "case_id": case_id,
            "result_occurrence_id": result.reduction.snapshot.result_occurrence_id,
            "legacy_outcome": result.legacy_outcome_after.value,
            "candidate_outcome": result.candidate.decision_receipt.outcome.value,
            "event_stream_authority_digest": result.reduction.snapshot.event_stream_authority_digest,
            "lifecycle_projection_digest": result.reduction.projection.lifecycle_projection_digest,
            "decision_receipt_digest": result.candidate.decision_receipt.receipt_digest,
            "pilot_receipt_digest": result.pilot_receipt_digest,
            "decision_delta": result.decision_delta,
            "legacy_outcome_observation_receipt_digest": (
                legacy_outcome_observation_receipt_digest
            ),
        }
        return cls(
            case_id,
            values["result_occurrence_id"],
            result.legacy_outcome_after,
            result.candidate.decision_receipt.outcome,
            values["event_stream_authority_digest"],
            values["lifecycle_projection_digest"],
            values["decision_receipt_digest"],
            result.pilot_receipt_digest,
            result.decision_delta,
            authority_digest(values),
            legacy_outcome_observation_receipt_digest,
        )

    def validate(self) -> None:
        expected = authority_digest({
            "case_id": self.case_id,
            "result_occurrence_id": self.result_occurrence_id,
            "legacy_outcome": self.legacy_outcome.value,
            "candidate_outcome": self.candidate_outcome.value,
            "event_stream_authority_digest": self.event_stream_authority_digest,
            "lifecycle_projection_digest": self.lifecycle_projection_digest,
            "decision_receipt_digest": self.decision_receipt_digest,
            "pilot_receipt_digest": self.pilot_receipt_digest,
            "decision_delta": self.decision_delta,
            "legacy_outcome_observation_receipt_digest": (
                self.legacy_outcome_observation_receipt_digest
            ),
        })
        if expected != self.entry_digest:
            raise ValueError("pilot difference entry digest mismatch")

    def to_dict(self) -> Mapping[str, Any]:
        self.validate()
        return {
            "case_id": self.case_id,
            "result_occurrence_id": self.result_occurrence_id,
            "legacy_outcome": self.legacy_outcome.value,
            "candidate_outcome": self.candidate_outcome.value,
            "event_stream_authority_digest": self.event_stream_authority_digest,
            "lifecycle_projection_digest": self.lifecycle_projection_digest,
            "decision_receipt_digest": self.decision_receipt_digest,
            "pilot_receipt_digest": self.pilot_receipt_digest,
            "legacy_outcome_observation_receipt_digest": (
                self.legacy_outcome_observation_receipt_digest
            ),
            "decision_delta": self.decision_delta,
            "entry_digest": self.entry_digest,
        }


@dataclass(frozen=True)
class PilotDifferenceManifest:
    manifest_id: str
    entries: Tuple[PilotDifferenceEntry, ...]
    manifest_digest: str

    @classmethod
    def seal(
        cls, manifest_id: str, entries: Sequence[PilotDifferenceEntry]
    ) -> "PilotDifferenceManifest":
        if type(manifest_id) is not str or not manifest_id:
            raise TypeError("pilot difference manifest ID must be a non-empty exact string")
        rows = tuple(sorted(entries, key=lambda item: item.case_id))
        if not rows:
            raise ValueError("pilot difference manifest cannot be empty")
        for row in rows:
            row.validate()
        if len({row.case_id for row in rows}) != len(rows):
            raise ValueError("duplicate pilot difference case ID")
        if len({row.result_occurrence_id for row in rows}) != len(rows):
            raise ValueError("duplicate pilot difference result occurrence ID")
        digest = authority_digest({
            "manifest_id": manifest_id,
            "entry_digests": tuple(row.entry_digest for row in rows),
        })
        return cls(manifest_id, rows, digest)

    def validate(self) -> None:
        if PilotDifferenceManifest.seal(self.manifest_id, self.entries) != self:
            raise ValueError("pilot difference manifest digest/entries mismatch")

    def to_dict(self) -> Mapping[str, Any]:
        self.validate()
        return {
            "manifest_id": self.manifest_id,
            "entries": [row.to_dict() for row in self.entries],
            "manifest_digest": self.manifest_digest,
        }


@dataclass(frozen=True)
class ProductionPilotExecutionIdentity:
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    execution_identity_digest: str

    @classmethod
    def create(cls, payload: Mapping[str, Any]) -> "ProductionPilotExecutionIdentity":
        canonical = canonical_value(payload)
        digest = authority_digest(canonical)
        return cls(
            f"production-pilot-{digest[:24]}",
            digest,
            authority_digest({"production_execution_identity": canonical}),
        )


@dataclass(frozen=True)
class LegacyOutcomeObservationReceipt:
    result_occurrence_id: str
    before_outcome: Outcome
    after_outcome: Outcome
    before_surface_digest: str
    after_surface_digest: str
    pilot_receipt_digest: str
    receipt_digest: str

    @classmethod
    def seal(
        cls,
        *,
        result_occurrence_id: str,
        before_outcome: Outcome,
        after_outcome: Outcome,
        before_surface_digest: str,
        after_surface_digest: str,
        pilot_receipt_digest: str,
    ) -> "LegacyOutcomeObservationReceipt":
        values = {
            "result_occurrence_id": result_occurrence_id,
            "before_outcome": before_outcome.value,
            "after_outcome": after_outcome.value,
            "before_surface_digest": before_surface_digest,
            "after_surface_digest": after_surface_digest,
            "pilot_receipt_digest": pilot_receipt_digest,
        }
        receipt = cls(
            result_occurrence_id,
            before_outcome,
            after_outcome,
            before_surface_digest,
            after_surface_digest,
            pilot_receipt_digest,
            authority_digest(values),
        )
        receipt.validate()
        return receipt

    def validate(self) -> None:
        if self.before_outcome != self.after_outcome:
            raise ValueError("production pilot changed the observed v1 outcome")
        if self.before_surface_digest != self.after_surface_digest:
            raise ValueError("production pilot mutated the observed v1 decision surface")
        expected = authority_digest({
            "result_occurrence_id": self.result_occurrence_id,
            "before_outcome": self.before_outcome.value,
            "after_outcome": self.after_outcome.value,
            "before_surface_digest": self.before_surface_digest,
            "after_surface_digest": self.after_surface_digest,
            "pilot_receipt_digest": self.pilot_receipt_digest,
        })
        if expected != self.receipt_digest:
            raise ValueError("legacy outcome observation receipt digest mismatch")

    def to_dict(self) -> Mapping[str, Any]:
        self.validate()
        return {
            "result_occurrence_id": self.result_occurrence_id,
            "before_outcome": self.before_outcome.value,
            "after_outcome": self.after_outcome.value,
            "before_surface_digest": self.before_surface_digest,
            "after_surface_digest": self.after_surface_digest,
            "pilot_receipt_digest": self.pilot_receipt_digest,
            "receipt_digest": self.receipt_digest,
        }


class ProductionDualWritePilotSession:
    def __init__(
        self,
        identity: ProductionPilotExecutionIdentity,
        reducer: ShadowLifecycleReducer,
        domain_signal_encoder: Optional[Callable[[Any, Any], Sequence[Any]]] = None,
        phase7_runtime: Any = None,
        execution_payload: Optional[Mapping[str, Any]] = None,
    ) -> None:
        self.identity = identity
        self.execution_payload = canonical_value(execution_payload or {})
        self.reducer = reducer
        self.recorder = EventRecorder(
            stream_id=f"stream-{identity.result_occurrence_id}",
            result_occurrence_id=identity.result_occurrence_id,
            source_snapshot_fingerprint=identity.source_snapshot_fingerprint,
        )
        self.terminalizations: list[TerminalizationIntent] = []
        self.domain_signal_encoder = domain_signal_encoder
        self.domain_signal_state: dict[str, Any] = {}
        self.observed_domain_signal_count = 0
        self.domain_signal_error_kinds: list[str] = []
        self.domain_signal_error_details: list[str] = []
        self.startup_receipts: tuple[Any, ...] = ()
        self.execution_authority_evidence_bundles: list[tuple[Any, Any]] = []
        self.execution_refusal_receipts: list[Any] = []
        self.result_entry_occurrence_receipt: Any = None
        self.closed = False
        self.phase7_runtime = phase7_runtime
        self.phase7_runtime_result: Any = None
        self._phase7_signal_sites: dict[int, str] = {}
        self._phase7_signal_transactions: dict[int, Any] = {}
        self._domain_signal_transaction_lock = RLock()

    @contextmanager
    def domain_signal_transaction(self) -> Any:
        """Serialize one producer transaction across preview and commit."""

        with self._domain_signal_transaction_lock:
            yield

    def emit(self, intent: Any) -> int:
        return self.emit_many((intent,))[0]

    def emit_many(
        self, intents: Sequence[Any], commit_callback: Any = None, *,
        phase7_execution_intents_prebuffered: bool = False,
        transaction_signal: Any = None,
    ) -> tuple[int, ...]:
        with self._domain_signal_transaction_lock:
            return self._emit_many_locked(
                intents,
                commit_callback,
                phase7_execution_intents_prebuffered=(
                    phase7_execution_intents_prebuffered
                ),
                transaction_signal=transaction_signal,
            )

    def _emit_many_locked(
        self, intents: Sequence[Any], commit_callback: Any = None, *,
        phase7_execution_intents_prebuffered: bool = False,
        transaction_signal: Any = None,
    ) -> tuple[int, ...]:
        if self.closed:
            raise ValueError("production dual-write pilot session is closed")
        if type(phase7_execution_intents_prebuffered) is not bool:
            raise TypeError("Phase 7 execution prebuffer flag is not exact")
        batch = tuple(intents)
        if transaction_signal is not None:
            replay_probe = getattr(
                self.domain_signal_encoder, "is_committed_signal_replay", None
            )
            if callable(replay_probe) and replay_probe(
                self, transaction_signal, batch
            ):
                # The source-side wrapper may already have opened and
                # materialized a Phase 7 activation before this shared
                # publication gate sees the semantic replay.  A committed
                # replay is a no-op for the producer ledger and event stream,
                # but it must still close that wrapper transaction by
                # restoring the pre-activation runtime snapshot.  Do not
                # invoke the encoder rollback here: for a committed replay
                # that would discard the already-committed producer state.
                self._rollback_phase7_signal_transaction(transaction_signal)
                return ()
        transaction = None
        if (
            self.phase7_runtime is not None
            and not phase7_execution_intents_prebuffered
        ):
            transaction = self._begin_phase7_transaction()
        try:
            if transaction is not None:
                for intent in batch:
                    if intent.event_type is not EventType.CAUSE_OBSERVED:
                        self.phase7_runtime.buffer_execution_intent(intent)

            def commit_before_publication() -> None:
                nonlocal transaction
                if commit_callback is not None:
                    commit_callback()
                if transaction is not None:
                    self._commit_phase7_transaction(transaction)
                    transaction = None

            recorded = self.recorder.append_many(
                batch, commit_before_publication
            )
            return tuple(item.header.sequence_number for item in recorded)
        except Exception:
            if transaction is not None:
                self._rollback_phase7_transaction(transaction)
            raise

    def _begin_phase7_transaction(self) -> Any:
        if self.phase7_runtime is None:
            return None
        begin = getattr(self.phase7_runtime, "begin_signal_transaction", None)
        if not callable(begin):
            raise TypeError("Phase 7 runtime lacks signal transaction authority")
        return begin()

    def _commit_phase7_transaction(self, transaction: Any) -> None:
        if self.phase7_runtime is None:
            raise ValueError("Phase 7 transaction lacks a runtime")
        commit = getattr(self.phase7_runtime, "commit_signal_transaction", None)
        if not callable(commit):
            raise TypeError("Phase 7 runtime lacks signal commit authority")
        commit(transaction)

    def _rollback_phase7_transaction(self, transaction: Any) -> None:
        if self.phase7_runtime is None:
            raise ValueError("Phase 7 transaction lacks a runtime")
        rollback = getattr(
            self.phase7_runtime, "rollback_signal_transaction", None
        )
        if not callable(rollback):
            raise TypeError("Phase 7 runtime lacks signal rollback authority")
        rollback(transaction)

    def record_phase7_pre_emission_activation(
        self, producer_site_manifest_id: str, signal: Any,
    ) -> None:
        if self.phase7_runtime is not None:
            signal_id = id(signal)
            if (
                signal_id in self._phase7_signal_sites
                or signal_id in self._phase7_signal_transactions
            ):
                raise ValueError("production signal already owns a Phase 7 transaction")
            transaction = self._begin_phase7_transaction()
            try:
                self.phase7_runtime.record_pre_emission_activation(
                    producer_site_manifest_id, signal
                )
            except Exception:
                self._rollback_phase7_transaction(transaction)
                raise
            self._phase7_signal_sites[signal_id] = producer_site_manifest_id
            self._phase7_signal_transactions[signal_id] = transaction

    def _commit_phase7_signal_transaction(self, signal: Any) -> None:
        if self.phase7_runtime is None:
            return
        signal_id = id(signal)
        try:
            transaction = self._phase7_signal_transactions[signal_id]
        except KeyError as exc:
            raise ValueError("production signal lacks a Phase 7 transaction") from exc
        self._commit_phase7_transaction(transaction)
        self._phase7_signal_transactions.pop(signal_id)
        self._phase7_signal_sites.pop(signal_id)

    def _rollback_phase7_signal_transaction(self, signal: Any) -> None:
        if self.phase7_runtime is None:
            return
        signal_id = id(signal)
        transaction = self._phase7_signal_transactions.pop(signal_id, None)
        self._phase7_signal_sites.pop(signal_id, None)
        if transaction is None:
            return
        self._rollback_phase7_transaction(transaction)

    def terminalize(self, event_sequence_number: int, proof_requirement_id: str) -> None:
        if self.closed:
            raise ValueError("production dual-write pilot session is closed")
        self.terminalizations.append(TerminalizationIntent(
            event_sequence_number, proof_requirement_id
        ))

    def emit_domain_signal(self, signal: Any) -> int:
        return self._emit_domain_signal_with_commit(signal)

    def _emit_domain_signal_with_commit(
        self, signal: Any, external_commit: Any = None,
        external_rollback: Any = None,
    ) -> int:
        """Commit one signal together with an optional external authority."""

        if self.closed:
            raise ValueError("production dual-write pilot session is closed")
        if (external_commit is None) != (external_rollback is None):
            raise TypeError(
                "external signal commit and rollback must be supplied together"
            )
        if external_commit is not None and (
            not callable(external_commit) or not callable(external_rollback)
        ):
            raise TypeError("external signal transaction callbacks must be callable")
        self.observed_domain_signal_count += 1
        if self.domain_signal_encoder is None:
            return 0
        external_committed = False
        try:
            intents = tuple(self.domain_signal_encoder(self, signal))
            if self.phase7_runtime is not None:
                try:
                    site_id = self._phase7_signal_sites[id(signal)]
                except KeyError as exc:
                    raise ValueError(
                        "production signal lacks audited pre-emission site"
                    ) from exc
                self.phase7_runtime.buffer_signal_intents(site_id, signal, intents)
                for intent in intents:
                    if intent.event_type is not EventType.CAUSE_OBSERVED:
                        self.phase7_runtime.buffer_execution_intent(intent)
            commit = getattr(
                self.domain_signal_encoder, "commit_emitted_signal", None
            )

            def commit_all() -> None:
                nonlocal external_committed
                if callable(commit):
                    commit(self, signal, intents)
                if external_commit is not None:
                    external_commit()
                    external_committed = True
                self._commit_phase7_signal_transaction(signal)

            emit_kwargs = {
                "phase7_execution_intents_prebuffered": (
                    self.phase7_runtime is not None
                ),
            }
            replay_support = getattr(
                self.domain_signal_encoder, "supports_signal_replay", None
            )
            if callable(replay_support):
                supports_replay = bool(replay_support(self, signal))
            else:
                supports_replay = callable(getattr(
                    self.domain_signal_encoder, "is_committed_signal_replay", None
                ))
            if supports_replay:
                emit_kwargs["transaction_signal"] = signal
            recorded_sequences = self.emit_many(
                intents, commit_all, **emit_kwargs
            )
            return len(recorded_sequences)
        except Exception as exc:
            rollback_failures = []
            if external_committed:
                try:
                    external_rollback()
                except Exception as rollback_exc:
                    rollback_failures.append(
                        "external rollback: "
                        + f"{type(rollback_exc).__name__}: {rollback_exc}"
                    )
            rollback = getattr(
                self.domain_signal_encoder, "rollback_emitted_signal", None
            )
            if callable(rollback):
                try:
                    rollback(self, signal)
                except Exception as rollback_exc:
                    rollback_failures.append(
                        "encoder rollback: "
                        + f"{type(rollback_exc).__name__}: {rollback_exc}"
                    )
            try:
                self._rollback_phase7_signal_transaction(signal)
            except Exception as rollback_exc:
                rollback_failures.append(
                    "Phase 7 rollback: "
                    + f"{type(rollback_exc).__name__}: {rollback_exc}"
                )
            self.domain_signal_error_kinds.append(type(exc).__name__)
            self.domain_signal_error_details.append(
                f"{type(signal).__name__}: {exc}"
                + (
                    " | rollback failures: " + "; ".join(rollback_failures)
                    if rollback_failures else ""
                )
            )
            return 0

    def emit_domain_signal_if_observed(
        self, signal: Any, producer_site_manifest_id: str = None,
    ) -> int:
        if self.domain_signal_encoder is None:
            return 0
        predicate = getattr(self.domain_signal_encoder, "has_observed", None)
        if not callable(predicate) or not predicate(self, signal):
            return 0
        if self.phase7_runtime is not None:
            self.record_phase7_pre_emission_activation(
                producer_site_manifest_id, signal
            )
        return self.emit_domain_signal(signal)

    def preview_lifecycle_projection(self):
        """Reduce an issuer-owned immutable prefix; the recorder remains append-only/open."""

        if self.closed:
            raise ValueError("production dual-write pilot session is closed")
        if self.recorder.event_count == 0:
            from scripts.function_tracer_pcode.authority.contracts import (
                VerifiedLifecycleProjection,
            )

            return VerifiedLifecycleProjection.seal(
                result_occurrence_id=self.identity.result_occurrence_id,
                snapshot_digest=authority_digest({
                    "empty_verified_prefix": self.identity.result_occurrence_id,
                    "execution_identity_digest": (
                        self.identity.execution_identity_digest
                    ),
                }),
                c_active_base=(),
                q_open_base=(),
                blocker_eligibility_base=(),
                satisfaction_projection=(),
            )
        return self.reducer.replay_prefix(self.recorder.prefix_view())


@dataclass(frozen=True)
class ProductionDualWriteEvidence:
    pilot_result: DualWritePilotResult
    legacy_observation_receipt: LegacyOutcomeObservationReceipt
    difference_entry: PilotDifferenceEntry
    execution_authority_evidence_bundles: tuple[tuple[Any, Any], ...] = ()
    execution_refusal_receipts: tuple[Any, ...] = ()
    result_entry_occurrence_receipt: Any = None

    def validate(self) -> None:
        self.pilot_result.validate()
        self.legacy_observation_receipt.validate()
        self.difference_entry.validate()
        if self.difference_entry.legacy_outcome_observation_receipt_digest != (
            self.legacy_observation_receipt.receipt_digest
        ):
            raise ValueError("difference entry lacks matching legacy observation receipt")
        pilot = self.pilot_result
        observation = self.legacy_observation_receipt
        entry = self.difference_entry
        result_occurrence_id = pilot.reduction.snapshot.result_occurrence_id
        if observation.result_occurrence_id != result_occurrence_id:
            raise ValueError("legacy observation result differs from pilot result")
        if entry.result_occurrence_id != result_occurrence_id:
            raise ValueError("difference entry result differs from pilot result")
        if observation.pilot_receipt_digest != pilot.pilot_receipt_digest:
            raise ValueError("legacy observation pilot digest differs from pilot result")
        if entry.pilot_receipt_digest != pilot.pilot_receipt_digest:
            raise ValueError("difference entry pilot digest differs from pilot result")
        if entry.event_stream_authority_digest != (
            pilot.reduction.snapshot.event_stream_authority_digest
        ):
            raise ValueError("difference entry stream digest differs from pilot result")
        if entry.lifecycle_projection_digest != (
            pilot.reduction.projection.lifecycle_projection_digest
        ):
            raise ValueError("difference entry lifecycle digest differs from pilot result")
        if entry.decision_receipt_digest != pilot.candidate.decision_receipt.receipt_digest:
            raise ValueError("difference entry decision digest differs from pilot result")
        if entry.legacy_outcome != observation.after_outcome:
            raise ValueError("difference entry legacy outcome differs from observation")
        if entry.candidate_outcome != pilot.candidate.decision_receipt.outcome:
            raise ValueError("difference entry candidate outcome differs from pilot result")
        if observation.before_outcome != pilot.legacy_outcome_before:
            raise ValueError("legacy observation before outcome differs from pilot result")
        if observation.after_outcome != pilot.legacy_outcome_after:
            raise ValueError("legacy observation after outcome differs from pilot result")
        if entry.decision_delta != pilot.decision_delta:
            raise ValueError("difference entry delta differs from pilot result")
        for registry, bundle in self.execution_authority_evidence_bundles:
            bundle.validate(registry)
            if bundle.census.result_occurrence_id != result_occurrence_id:
                raise ValueError("solver evidence result differs from pilot result")
            if bundle.final_lifecycle_projection_digest != (
                pilot.reduction.projection.lifecycle_projection_digest
            ):
                raise ValueError("solver evidence lifecycle differs from pilot result")
        for refusal in self.execution_refusal_receipts:
            refusal.validate()
            if refusal.result_occurrence_id != result_occurrence_id:
                raise ValueError("execution refusal result differs from pilot result")
        occurrence_digest = None
        if self.result_entry_occurrence_receipt is not None:
            self.result_entry_occurrence_receipt.validate()
            occurrence_digest = self.result_entry_occurrence_receipt.receipt_digest
        expected_execution_evidence_digests = tuple(
            bundle.evidence_digest
            for _registry, bundle in self.execution_authority_evidence_bundles
        ) + tuple(
            refusal.refusal_receipt_digest
            for refusal in self.execution_refusal_receipts
        ) + ((occurrence_digest,) if occurrence_digest is not None else ())
        if pilot.execution_authority_evidence_digests != (
            expected_execution_evidence_digests
        ):
            raise ValueError("pilot receipt lacks exact solver evidence bindings")

    def to_dict(self) -> Mapping[str, Any]:
        self.validate()
        return {
            "non_authoritative_shadow": True,
            "legacy_outcome": self.legacy_observation_receipt.after_outcome.value,
            "candidate_outcome": self.pilot_result.candidate.decision_receipt.outcome.value,
            "legacy_outcome_observation_receipt_digest": (
                self.legacy_observation_receipt.receipt_digest
            ),
            "event_stream_authority_digest": (
                self.pilot_result.reduction.snapshot.event_stream_authority_digest
            ),
            "lifecycle_projection_digest": (
                self.pilot_result.reduction.projection.lifecycle_projection_digest
            ),
            "decision_receipt_digest": (
                self.pilot_result.candidate.decision_receipt.receipt_digest
            ),
            "pilot_receipt_digest": self.pilot_result.pilot_receipt_digest,
            "difference_entry_digest": self.difference_entry.entry_digest,
            "execution_authority_evidence": tuple(
                bundle.to_authority_dict(registry)
                for registry, bundle in self.execution_authority_evidence_bundles
            ),
            "execution_authority_evidence_digests": (
                self.pilot_result.execution_authority_evidence_digests
            ),
            "execution_refusal_receipts": tuple(
                receipt.to_authority_dict()
                for receipt in self.execution_refusal_receipts
            ),
            "result_entry_occurrence_receipt": (
                self.result_entry_occurrence_receipt.to_authority_dict()
                if self.result_entry_occurrence_receipt is not None else None
            ),
        }


class ProductionDualWritePilotConnector:
    """Default-off connector used by the production binary-check boundary."""

    def __init__(
        self,
        reducer: ShadowLifecycleReducer,
        *,
        domain_signal_encoder: Optional[Callable[[Any, Any], Sequence[Any]]] = None,
        phase7_runtime_factory: Optional[Callable[[ProductionPilotExecutionIdentity], Any]] = None,
    ) -> None:
        self._reducer = reducer
        self._domain_signal_encoder = domain_signal_encoder
        self._phase7_runtime_factory = phase7_runtime_factory

    def begin(
        self, execution_payload: Mapping[str, Any]
    ) -> ProductionDualWritePilotSession:
        startup_validator = getattr(self._domain_signal_encoder, "validate_startup", None)
        startup_receipts: tuple[Any, ...] = ()
        if callable(startup_validator):
            validated = startup_validator()
            if validated is None:
                startup_receipts = ()
            elif type(validated) is tuple:
                startup_receipts = validated
            else:
                startup_receipts = (validated,)
        identity_payload = dict(execution_payload)
        occurrence_nonce = os.environ.get(RESULT_ENTRY_OCCURRENCE_NONCE_ENV)
        if occurrence_nonce is not None or startup_receipts:
            occurrence_nonce = occurrence_nonce or secrets.token_hex(24)
            identity_payload["result_entry_occurrence_nonce"] = occurrence_nonce
        identity = ProductionPilotExecutionIdentity.create(identity_payload)
        occurrence_receipt = None
        if startup_receipts:
            assert occurrence_nonce is not None
            startup_digests = tuple(
                sorted(receipt.receipt_digest for receipt in startup_receipts)
            )
            from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
                PINNED_SOLVER_EXECUTION_ISSUER,
            )

            occurrence_receipt = (
                PINNED_SOLVER_EXECUTION_ISSUER.issue_result_entry_occurrence(
                    result_occurrence_id=identity.result_occurrence_id,
                    execution_payload_digest=authority_digest(execution_payload),
                    startup_receipt_digests=startup_digests,
                    occurrence_nonce=occurrence_nonce,
                )
            )
        session = ProductionDualWritePilotSession(
            identity,
            self._reducer,
            self._domain_signal_encoder,
            (
                self._phase7_runtime_factory(identity)
                if self._phase7_runtime_factory is not None else None
            ),
            execution_payload=identity_payload,
        )
        session.startup_receipts = startup_receipts
        session.result_entry_occurrence_receipt = occurrence_receipt
        return session

    @staticmethod
    def _legacy_outcome(result: Any) -> Outcome:
        if getattr(result, "error_message", None):
            return Outcome.ERROR
        if getattr(result, "is_equivalent", None) is True:
            return Outcome.EQUIVALENT
        if getattr(result, "is_equivalent", None) is False:
            return Outcome.NOT_EQ
        is_timeout = getattr(result, "is_timeout", None)
        if callable(is_timeout) and is_timeout():
            return Outcome.TIMEOUT
        return Outcome.UNKNOWN

    @classmethod
    def _legacy_surface(cls, result: Any) -> Mapping[str, Any]:
        return {
            "outcome": cls._legacy_outcome(result).value,
            "is_equivalent": getattr(result, "is_equivalent", None),
            "error_message": getattr(result, "error_message", None),
            "failure_status": getattr(result, "failure_status", None),
            "failure_message": getattr(result, "failure_message", None),
            "is_timeout": bool(
                callable(getattr(result, "is_timeout", None)) and result.is_timeout()
            ),
        }

    def finish(
        self,
        session: ProductionDualWritePilotSession,
        result: Any,
        *,
        case_id: str,
    ) -> ProductionDualWriteEvidence:
        if session.closed:
            raise ValueError("production dual-write pilot session is already closed")
        before_surface = self._legacy_surface(result)
        before_outcome = self._legacy_outcome(result)
        before_digest = authority_digest(before_surface)
        from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
            finalize_deferred_sat_safety_observations,
        )
        finalize_deferred_sat_safety_observations(session)
        execution_history_finalizer = getattr(
            session.domain_signal_encoder,
            "finalize_open_execution_history",
            None,
        )
        if callable(execution_history_finalizer):
            execution_history_finalizer(session)
        # A failed signal encoding leaves its Phase 7 discovery activation
        # deliberately unmaterialized.  Report the original encoding failure
        # before Phase 7 finalization; otherwise the pending-discovery guard
        # masks the actionable authority error whenever an earlier event was
        # recorded successfully.
        if session.domain_signal_error_kinds:
            session.closed = True
            raise ValueError(
                "production domain signal encoding is incomplete: "
                + repr(tuple(zip(
                    session.domain_signal_error_kinds,
                    session.domain_signal_error_details,
                )))
            )
        provisional_projection = session.preview_lifecycle_projection()
        provenance = getattr(result, "call_proof_terminal_provenance", None)
        if (
            before_outcome in {Outcome.UNKNOWN, Outcome.TIMEOUT}
            and not provisional_projection.c_active_base
            and not provisional_projection.q_open_base
            and provenance is not None
        ):
            if not isinstance(provenance, Mapping):
                raise ValueError(
                    "inconclusive comparison lacks receipt-bound provenance"
                )
            from scripts.function_tracer_pcode.authority.domains.comparison_closure import (
                InconclusiveComparisonAuthority,
            )
            comparison_authority = getattr(
                result, "_inconclusive_comparison_authority", None
            )
            if comparison_authority is None:
                dispatch_frame = getattr(
                    result, "_prepared_dispatch_frame", None
                )
                if dispatch_frame is not None:
                    comparison_authority = (
                        InconclusiveComparisonAuthority.issue(dispatch_frame)
                    )
            if (
                type(comparison_authority)
                is not InconclusiveComparisonAuthority
                or not comparison_authority.matches_provenance(provenance)
            ):
                raise ValueError(
                    "inconclusive comparison authority is not canonical"
                )
            terminal = provenance["monolithic_terminal_receipt"]
            from scripts.function_tracer_pcode.authority.lifecycle.production_context import (
                production_pilot_session_scope,
            )
            from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                ComparisonClosureProductionSignal,
                emit_comparison_closure_signal,
            )
            signal = ComparisonClosureProductionSignal(
                comparison_receipt_id=provenance["comparison_receipt_id"],
                terminal_receipt_digest=terminal["receipt_digest"],
                branch_id=provenance["terminal_branch_id"],
                runtime_premise_digest=provenance[
                    "terminal_runtime_premise_digest"
                ],
                runtime_view_id=provenance["terminal_runtime_view_id"],
                query_receipt_digests=(
                    comparison_authority.query_receipt_digests
                ),
            )
            with production_pilot_session_scope(session):
                emitted = emit_comparison_closure_signal(
                    signal,
                    producer_site_manifest_id=(
                        "comparison-inconclusive-terminal"
                    ),
                )
            if emitted != 1:
                raise ValueError(
                    "inconclusive comparison C/Q was not materialized"
                )
        pre_closure_projection = session.preview_lifecycle_projection()
        terminal_candidate_view = TerminalCandidateView.freeze(
            session, pre_closure_projection
        )
        from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
            finalize_pending_eq_authorities,
        )

        for intent in finalize_pending_eq_authorities(
            session, pre_closure_projection, terminal_candidate_view
        ):
            session.emit(intent)
        session.domain_signal_state["terminal_candidate_view"] = (
            terminal_candidate_view
        )
        live_pending = tuple(
            nonce for nonce, entry in session.domain_signal_state.get(
                "pending_eq_authorities", {}
            ).items()
            if entry.get("state") == "PENDING"
        )
        if live_pending:
            session.closed = True
            raise ValueError("production session cannot seal with live pending EQ")
        timeout_selection_stream = (
            session.recorder.prefix_view().to_sealed_stream()
        )
        terminal_resolver = getattr(
            session.domain_signal_encoder,
            "finalize_terminal_timeout_bindings",
            None,
        )
        timeout_selection_was_resolved = callable(terminal_resolver)
        terminal_bindings = (
            tuple(terminal_resolver(session, timeout_selection_stream))
            if callable(terminal_resolver) else ()
        )
        if len(terminal_bindings) > 1:
            session.closed = True
            raise ValueError("terminal timeout resolver selected multiple executions")
        frozen_timeout_bindings = {
            (sequence_number, requirement_id)
            for sequence_number, requirement_id, _event_digest
            in terminal_candidate_view.timeout_candidates
        }
        if any(
            binding not in frozen_timeout_bindings
            for binding in terminal_bindings
        ):
            session.closed = True
            raise ValueError(
                "timeout resolver selected an unfrozen candidate"
            )
        terminal_timeout_candidate_selection = None
        if terminal_bindings:
            from scripts.function_tracer_pcode.authority.sites.activation import (
                TerminalTimeoutCandidateSelectionReceipt,
            )

            sequence_number, requirement_id = terminal_bindings[0]
            resolver_candidate_bindings = tuple(
                session.domain_signal_state.get(
                    "terminal_timeout_domain_candidate_bindings",
                    terminal_bindings,
                )
            )
            terminal_timeout_candidate_selection = (
                TerminalTimeoutCandidateSelectionReceipt.issue(
                    timeout_selection_stream,
                    terminal_candidate_view,
                    event_sequence_number=sequence_number,
                    proof_requirement_id=requirement_id,
                    resolver_candidate_bindings=resolver_candidate_bindings,
                )
            )
            session.domain_signal_state[
                "terminal_timeout_candidate_selection"
            ] = terminal_timeout_candidate_selection
            session.terminalize(sequence_number, requirement_id)
        if session.phase7_runtime is not None:
            session.phase7_runtime_result = session.phase7_runtime.finalize(
                stream_id=f"phase7-{session.identity.result_occurrence_id}",
                result_occurrence_id=session.identity.result_occurrence_id,
                source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
                terminal_timeout_candidate_selection=(
                    terminal_timeout_candidate_selection
                ),
                terminal_timeout_selection_stream=timeout_selection_stream,
                terminal_candidate_view=terminal_candidate_view,
                terminal_timeout_selection_resolved=(
                    timeout_selection_was_resolved
                ),
            )
            from scripts.function_tracer_pcode.checker.unknown_reason import (
                make_production_unknown_reason,
            )

            from scripts.function_tracer_pcode.checker.unknown_reason import (
                build_projection_diagnostic,
            )

            result.legacy_unknown_reasons = list(
                getattr(result, "unknown_reasons", ()) or ()
            )
            occurrences = _recorded_cause_occurrences(session)
            function_names = {
                "function1": getattr(result, "function1_name", None),
                "function2": getattr(result, "function2_name", None),
            }
            binary_names = {
                "binary1": getattr(result, "binary1_name", None),
                "binary2": getattr(result, "binary2_name", None),
            }
            projection_receipts = tuple(
                session.phase7_runtime_result.projection_receipts
            )
            projected_reason_counts: Dict[str, int] = {}
            for receipt in projection_receipts:
                projected_reason_counts[receipt.reason_id] = (
                    projected_reason_counts.get(receipt.reason_id, 0) + 1
                )
            result.unknown_reasons = [
                make_production_unknown_reason(
                    receipt,
                    projection_factory=(
                        session.phase7_runtime_result.projection_factory
                    ),
                    diagnostic=_safe_projection_diagnostic(
                        build_projection_diagnostic,
                        receipt,
                        cause_occurrence=occurrences.get(receipt.occurrence_id),
                        legacy_reasons=result.legacy_unknown_reasons,
                        function_names=function_names,
                        binary_names=binary_names,
                        projected_reason_counts=projected_reason_counts,
                    ),
                )
                for receipt in projection_receipts
            ]
            result.unknown_reason_projection_mode = "V2_CANONICAL"
        stream = session.recorder.seal()
        if session.domain_signal_error_kinds:
            session.closed = True
            raise ValueError(
                "production domain signal encoding is incomplete: "
                + repr(tuple(zip(
                    session.domain_signal_error_kinds,
                    session.domain_signal_error_details,
                )))
            )
        pilot_result = run_dual_write_pilot(
            legacy_outcome=before_outcome,
            reducer=session.reducer,
            stream=stream,
            terminalizations=tuple(session.terminalizations),
            execution_authority_evidence_digests=tuple(
                bundle.evidence_digest
                for _registry, bundle
                in session.execution_authority_evidence_bundles
            ) + tuple(
                receipt.refusal_receipt_digest
                for receipt in session.execution_refusal_receipts
            ) + (
                (session.result_entry_occurrence_receipt.receipt_digest,)
                if session.result_entry_occurrence_receipt is not None else ()
            ),
        )
        after_surface = self._legacy_surface(result)
        after_outcome = self._legacy_outcome(result)
        after_digest = authority_digest(after_surface)
        session.closed = True
        observation = LegacyOutcomeObservationReceipt.seal(
            result_occurrence_id=session.identity.result_occurrence_id,
            before_outcome=before_outcome,
            after_outcome=after_outcome,
            before_surface_digest=before_digest,
            after_surface_digest=after_digest,
            pilot_receipt_digest=pilot_result.pilot_receipt_digest,
        )
        entry = PilotDifferenceEntry.create(
            case_id,
            pilot_result,
            legacy_outcome_observation_receipt_digest=observation.receipt_digest,
        )
        evidence = ProductionDualWriteEvidence(
            pilot_result,
            observation,
            entry,
            tuple(session.execution_authority_evidence_bundles),
            tuple(session.execution_refusal_receipts),
            session.result_entry_occurrence_receipt,
        )
        evidence.validate()
        return evidence


def run_dual_write_pilot(
    *,
    legacy_outcome: Outcome,
    reducer: ShadowLifecycleReducer,
    stream: SealedEventStream,
    terminalizations: Sequence[TerminalizationIntent] = (),
    retry_fallback_projection: Any = (),
    cli_batch_projection: Any = (),
    execution_authority_evidence_digests: Sequence[str] = (),
) -> DualWritePilotResult:
    """Replay only explicit signals and retain the supplied v1 decision verbatim."""

    legacy = Outcome(legacy_outcome)
    stream.validate()
    for recorded in stream.events:
        if recorded.header.event_type not in PILOT_EVENT_TYPES:
            raise ValueError("event type is outside the narrow dual-write pilot")
        if recorded.header.event_type == EventType.CAUSE_OBSERVED:
            reason_id = recorded.authority_payload.occurrence_authority.occurrence.reason_id
            if reason_id not in PILOT_TYPED_CAUSE_KINDS:
                raise ValueError("semantic reason is outside the narrow dual-write pilot")
    reduction = reducer.replay(stream)
    projection_digest = reduction.projection.lifecycle_projection_digest
    decisive_receipts = []
    error_receipts = []
    attempted_solver = 0
    observed_timeout_sequences: dict[int, tuple[str, str]] = {}
    explicit_cause_observations = 0
    for recorded in stream.events:
        payload = recorded.authority_payload
        event_type = recorded.header.event_type
        if event_type == EventType.CAUSE_OBSERVED:
            if type(payload) is not CauseObservedEventAuthority:
                raise TypeError("pilot cause observation payload is not exact")
            explicit_cause_observations += 1
        if type(payload) in (
            SolverExecutionEventAuthority,
            ReceiptBoundSolverExecutionEventAuthority,
            GenericReceiptBoundSolverExecutionEventAuthority,
        ):
            attempted_solver += 1
        if event_type in {EventType.SOLVER_TIMEOUT, EventType.PROCESS_TIMEOUT}:
            if not isinstance(
                payload, (
                    SolverExecutionEventAuthority,
                    ReceiptBoundSolverExecutionEventAuthority,
                    GenericReceiptBoundSolverExecutionEventAuthority,
                    ProcessExecutionEventAuthority,
                )
            ):
                raise TypeError("pilot timeout payload is not exact")
            observed_timeout_sequences[recorded.header.sequence_number] = (
                recorded.authority_digest,
                payload.proof_requirement_id,
            )
        if event_type in {EventType.EQ_CLOSURE, EventType.COUNTEREXAMPLE}:
            if type(payload) is not DecisiveProofEventAuthority:
                raise TypeError("pilot decisive proof payload is not exact")
            proof_kind = (
                DecisiveProofKind.EQ_CLOSURE
                if event_type == EventType.EQ_CLOSURE
                else DecisiveProofKind.SAFE_COUNTEREXAMPLE
            )
            decisive_receipts.append(DecisiveProofReceipt.create(
                result_occurrence_id=stream.envelope.result_occurrence_id,
                lifecycle_projection_digest=projection_digest,
                proof_kind=proof_kind,
                proof_artifact_digest=payload.proof_artifact_digest,
            ))
        if event_type == EventType.ERROR:
            if type(payload) is not ErrorEventAuthority:
                raise TypeError("pilot error payload is not exact")
            error_receipts.append(ErrorReceipt.create(
                result_occurrence_id=stream.envelope.result_occurrence_id,
                lifecycle_projection_digest=projection_digest,
                error_kind=payload.error_kind,
                error_artifact_digest=payload.error_artifact_digest,
            ))

    intents = tuple(terminalizations)
    if len({item.event_sequence_number for item in intents}) != len(intents):
        raise ValueError("duplicate terminalization event sequence")
    timeout_receipts = []
    for intent in intents:
        binding = observed_timeout_sequences.get(intent.event_sequence_number)
        if binding is None:
            raise ValueError("terminalization does not reference a timeout event")
        event_digest, requirement_id = binding
        if requirement_id != intent.proof_requirement_id:
            raise ValueError("terminalization requirement differs from timeout event")
        timeout_receipts.append(TerminalTimeoutReceipt.create(
            result_occurrence_id=stream.envelope.result_occurrence_id,
            lifecycle_projection_digest=projection_digest,
            proof_requirement_id=requirement_id,
            execution_event_digest=event_digest,
        ))

    candidate = build_candidate_projection(
        reduction,
        decisive_proof_receipts=tuple(decisive_receipts),
        terminal_timeout_receipts=tuple(timeout_receipts),
        error_receipts=tuple(error_receipts),
        retry_fallback_projection=retry_fallback_projection,
        cli_batch_projection=cli_batch_projection,
    )
    lifecycle_inference_count = (
        len(reduction.snapshot.occurrence_authorities) - explicit_cause_observations
    )
    values = {
        "legacy_outcome_before": legacy.value,
        "legacy_outcome_after": legacy.value,
        "snapshot_digest": reduction.snapshot.snapshot_digest,
        "lifecycle_projection_digest": projection_digest,
        "candidate_projection_digest": candidate.projection_digest,
        "attempted_solver_event_count": attempted_solver,
        "bound_solver_event_count": attempted_solver,
        "observed_nonterminal_timeout_event_count": (
            len(observed_timeout_sequences)
            - len(candidate.terminal_execution_event_digests)
        ),
        "terminal_timeout_receipt_count": len(
            candidate.terminal_execution_event_digests
        ),
        "lifecycle_inference_count": lifecycle_inference_count,
        "execution_authority_evidence_digests": tuple(
            execution_authority_evidence_digests
        ),
    }
    result = DualWritePilotResult(
        legacy,
        legacy,
        stream,
        reduction,
        candidate,
        attempted_solver,
        attempted_solver,
        values["observed_nonterminal_timeout_event_count"],
        values["terminal_timeout_receipt_count"],
        lifecycle_inference_count,
        authority_digest(values),
        tuple(execution_authority_evidence_digests),
        tuple(decisive_receipts),
        tuple(timeout_receipts),
        tuple(error_receipts),
    )
    result.validate()
    return result


def _recorded_cause_occurrences(session: Any) -> Dict[str, Any]:
    """occurrence_id -> CauseOccurrence for every CAUSE_OBSERVED event so far.

    Diagnostic lookup only (Issue #17): the projected compatibility reasons
    borrow the typed missing fact / target kind of their cause occurrence.
    """
    from scripts.function_tracer_pcode.authority.lifecycle.stream import EventType

    recorder = getattr(session, "recorder", None)
    events = getattr(recorder, "recorded_events", None)
    occurrences: Dict[str, Any] = {}
    for event in tuple(events or ()):
        header = getattr(event, "header", None)
        if getattr(header, "event_type", None) is not EventType.CAUSE_OBSERVED:
            continue
        authority = getattr(event.authority_payload, "occurrence_authority", None)
        occurrence = getattr(authority, "occurrence", None)
        occurrence_id = getattr(occurrence, "occurrence_id", None)
        if occurrence_id and occurrence_id not in occurrences:
            occurrences[occurrence_id] = occurrence
    return occurrences


def _safe_projection_diagnostic(builder: Any, receipt: Any, **kwargs: Any) -> Optional[Dict[str, Any]]:
    """Diagnostics are best effort: a failure here must not touch the verdict."""
    try:
        return builder(receipt, **kwargs)
    except Exception as exc:
        return {
            "schema": "unknown-reason-diagnostic-v1",
            "reason_id": getattr(receipt, "reason_id", None),
            "error": f"{type(exc).__name__}: {exc}"[:200],
        }
