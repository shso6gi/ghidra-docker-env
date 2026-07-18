"""Explicit bridge from production proof producers to canonical v2 sessions."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Iterator, Mapping, Optional

from .contracts import CauseOccurrenceAuthority, authority_digest, canonical_value
from .production_context import (
    active_production_pilot_session,
    comparison_receipt_authority,
    production_pilot_session_scope,
)
from .stream import CauseObservedEventAuthority, EventIntent, EventType


@dataclass(frozen=True)
class OutcomePartitionProductionSignal:
    stage: str
    producer_status: str
    proof_requirement_identity: Mapping[str, Any]
    function_identity: Any
    outcome_seed_digest: str
    producer_evidence: Mapping[str, Any]
    outcome_seed_revision: Optional[int] = None
    function_snapshot_fingerprint: Optional[str] = None
    premise_digest: Optional[str] = None
    producer_attempt_identity: Optional[str] = None
    producer_attempt_ordinal: Optional[int] = None
    execution_identity_digest: Optional[str] = None
    execution_receipts: tuple[Any, ...] = ()
    witness_artifact: Optional[Any] = None
    validated_artifact_authority: Optional[Mapping[str, Any]] = None

    def __post_init__(self) -> None:
        if type(self.stage) is not str or not self.stage:
            raise TypeError("outcome partition signal stage must be a non-empty string")
        if type(self.producer_status) is not str or not self.producer_status:
            raise TypeError("outcome partition signal status must be a non-empty string")
        canonical_value(self.proof_requirement_identity)
        canonical_value(self.function_identity)
        canonical_value(self.producer_evidence)
        object.__setattr__(self, "execution_receipts", tuple(self.execution_receipts))
        if self.validated_artifact_authority is not None:
            canonical_value(self.validated_artifact_authority)
        if self.outcome_seed_revision is not None and (
            type(self.outcome_seed_revision) is not int
            or self.outcome_seed_revision < 0
        ):
            raise TypeError("outcome partition signal seed revision is invalid")
        for value in (self.function_snapshot_fingerprint, self.premise_digest):
            if value is not None and (type(value) is not str or not value):
                raise TypeError("outcome partition signal authority is incomplete")
        if self.producer_attempt_identity is not None and (
            type(self.producer_attempt_identity) is not str
            or not self.producer_attempt_identity
        ):
            raise TypeError("outcome producer attempt identity is invalid")
        if self.execution_identity_digest is not None and (
            type(self.execution_identity_digest) is not str
            or not self.execution_identity_digest
        ):
            raise TypeError("outcome producer execution identity is invalid")
        if self.producer_attempt_ordinal is not None and (
            type(self.producer_attempt_ordinal) is not int
            or self.producer_attempt_ordinal <= 0
        ):
            raise TypeError("outcome producer attempt ordinal is invalid")
        if type(self.outcome_seed_digest) is not str or not self.outcome_seed_digest:
            raise TypeError("outcome partition signal seed digest must be non-empty")


SAT_SAFETY_TYPED_REASON_IDS = frozenset({
    "counterexample_analysis_safety_unproven",
    "counterexample_partition_replay_ambiguous",
    "counterexample_same_function_replay_unproven",
})


@dataclass(frozen=True)
class SatSafetyBlockerProductionSignal:
    action: str
    reason_id: str
    canonical_target_key: Any
    missing_semantic_fact: Any
    evidence_refs: tuple[str, ...]
    producer_id: str
    proof_artifact_digest: Optional[str] = None

    def __post_init__(self) -> None:
        if self.action not in {"OBSERVED", "COMPLETED"}:
            raise ValueError("SAT safety blocker signal action is invalid")
        if self.reason_id not in SAT_SAFETY_TYPED_REASON_IDS:
            raise ValueError("SAT safety blocker signal reason is not sealed")
        if type(self.producer_id) is not str or not self.producer_id:
            raise TypeError("SAT safety blocker producer identity is incomplete")
        object.__setattr__(self, "canonical_target_key", canonical_value(self.canonical_target_key))
        object.__setattr__(self, "missing_semantic_fact", canonical_value(self.missing_semantic_fact))
        object.__setattr__(self, "evidence_refs", tuple(self.evidence_refs))
        if any(type(item) is not str or not item for item in self.evidence_refs):
            raise TypeError("SAT safety evidence references must be exact strings")
        if self.action == "COMPLETED" and not self.proof_artifact_digest:
            raise ValueError("SAT safety completion lacks proof artifact authority")


@dataclass(frozen=True)
class SafeCounterexampleProductionSignal:
    proof_artifact_digest: str
    formula_digest: str
    model_digest: str
    premise_digest: str
    pair_key: tuple[int, int]

    def __post_init__(self) -> None:
        for value in (
            self.proof_artifact_digest, self.formula_digest,
            self.model_digest, self.premise_digest,
        ):
            if type(value) is not str or not value:
                raise TypeError("safe counterexample signal authority is incomplete")
        if (
            type(self.pair_key) is not tuple
            or len(self.pair_key) != 2
            or any(type(item) is not int for item in self.pair_key)
        ):
            raise TypeError("safe counterexample signal pair key is invalid")


_EQ_CLOSURE_SIGNAL_TOKEN = object()


@dataclass(frozen=True, init=False)
class EqClosureProductionSignal:
    proof_artifact_digest: str
    comparison_receipt_id: str
    producer_id: str = "verified_comparison_receipt"

    def __init__(
        self,
        proof_artifact_digest: str,
        comparison_receipt_id: str,
        *,
        _token: object,
    ) -> None:
        if _token is not _EQ_CLOSURE_SIGNAL_TOKEN:
            raise TypeError("EQ closure signal requires its verifier-owned issuer")
        for value in (
            proof_artifact_digest,
            comparison_receipt_id,
        ):
            if type(value) is not str or not value:
                raise TypeError("EQ closure signal authority is incomplete")
        object.__setattr__(self, "proof_artifact_digest", proof_artifact_digest)
        object.__setattr__(self, "comparison_receipt_id", comparison_receipt_id)
        object.__setattr__(self, "producer_id", "verified_comparison_receipt")


def issue_eq_closure_signal(
    session: Any, comparison_receipt: Any, dispatch_frame: Any,
) -> EqClosureProductionSignal:
    """Issue one-shot EQ authority from an exact trusted comparison receipt."""

    if getattr(dispatch_frame, "receipt", None) is not comparison_receipt:
        raise ValueError("EQ closure receipt is not the dispatch-frame receipt")
    authority = comparison_receipt_authority(comparison_receipt, dispatch_frame)
    if authority is None:
        raise TypeError("EQ closure requires an exact issuer-owned comparison receipt")
    if not comparison_receipt.is_trusted_for(dispatch_frame):
        raise ValueError("EQ closure comparison receipt is not trusted")
    bound_session = authority[2]
    if bound_session is not session:
        raise ValueError("EQ closure receipt belongs to a different production session")
    if (
        getattr(getattr(bound_session, "identity", None), "result_occurrence_id", None)
        != getattr(getattr(session, "identity", None), "result_occurrence_id", None)
        or getattr(
            getattr(bound_session, "identity", None),
            "execution_identity_digest",
            None,
        )
        != getattr(
            getattr(session, "identity", None),
            "execution_identity_digest",
            None,
        )
    ):
        raise ValueError("EQ closure production execution identity changed")
    proof_digest = authority_digest({
        "comparison_receipt": comparison_receipt,
        "result_occurrence_id": session.identity.result_occurrence_id,
        "execution_identity_digest": session.identity.execution_identity_digest,
        "comparison_session_id": dispatch_frame.comparison_session_id,
        "branch_id": dispatch_frame.branch_id,
        "generation": dispatch_frame.generation,
    })
    signal = EqClosureProductionSignal(
        proof_digest,
        comparison_receipt.receipt_id,
        _token=_EQ_CLOSURE_SIGNAL_TOKEN,
    )
    owned = session.domain_signal_state.setdefault("eq_closure_signal_authority", {})
    owned[id(signal)] = (signal, comparison_receipt, dispatch_frame, session)
    return signal


def consume_verified_eq_closure_signal(session: Any, signal: Any) -> str:
    """Revalidate and consume exact-object EQ authority at the encoder boundary."""

    if type(signal) is not EqClosureProductionSignal:
        raise TypeError("EQ closure encoder requires its exact signal type")
    owned = session.domain_signal_state.setdefault("eq_closure_signal_authority", {})
    authority = owned.pop(id(signal), None)
    if authority is None or authority[0] is not signal:
        raise ValueError("EQ closure signal is copied, forged, or already consumed")
    _owned_signal, receipt, frame, bound_session = authority
    if bound_session is not session:
        raise ValueError("EQ closure signal belongs to a different production session")
    if getattr(frame, "receipt", None) is not receipt:
        raise ValueError("EQ closure dispatch-frame receipt changed")
    if receipt.receipt_id != signal.comparison_receipt_id:
        raise ValueError("EQ closure receipt identity changed")
    if not receipt.is_trusted_for(frame):
        raise ValueError("EQ closure receipt no longer validates")
    expected = authority_digest({
        "comparison_receipt": receipt,
        "result_occurrence_id": session.identity.result_occurrence_id,
        "execution_identity_digest": session.identity.execution_identity_digest,
        "comparison_session_id": frame.comparison_session_id,
        "branch_id": frame.branch_id,
        "generation": frame.generation,
    })
    if signal.proof_artifact_digest != expected:
        raise ValueError("EQ closure proof digest changed")
    return expected


_CALL_EFFECT_BLOCKER_SIGNAL_TOKEN = object()


@dataclass(frozen=True, init=False)
class CallEffectBlockerProductionSignal:
    """Object-derived relational blocker input; reason is registry-classified."""

    source_contract: str
    failure_code: str
    obligation_id: str
    observation_contract_id: str
    left_fact_id: str
    right_fact_id: str
    semantic_arm: str
    structural_certificate_id: str
    producer_id: str
    effect_stage_required: bool

    def __init__(
        self,
        source_contract: str,
        failure_code: str,
        obligation_id: str,
        observation_contract_id: str,
        left_fact_id: str,
        right_fact_id: str,
        semantic_arm: str,
        structural_certificate_id: str,
        producer_id: str,
        effect_stage_required: bool = False,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _CALL_EFFECT_BLOCKER_SIGNAL_TOKEN:
            raise TypeError("call/effect blocker signal must be proof-input factory issued")
        for name, value in (
            ("source_contract", source_contract),
            ("failure_code", failure_code),
            ("obligation_id", obligation_id),
            ("observation_contract_id", observation_contract_id),
            ("left_fact_id", left_fact_id),
            ("right_fact_id", right_fact_id),
            ("semantic_arm", semantic_arm),
            ("structural_certificate_id", structural_certificate_id),
            ("producer_id", producer_id),
            ("effect_stage_required", effect_stage_required),
        ):
            object.__setattr__(self, name, value)
        for value in (
            self.source_contract, self.failure_code, self.obligation_id,
            self.observation_contract_id, self.left_fact_id, self.right_fact_id,
            self.semantic_arm, self.structural_certificate_id, self.producer_id,
        ):
            if type(value) is not str or not value:
                raise TypeError("call/effect blocker signal identity is incomplete")
        if self.semantic_arm not in {
            "inline_region_semantic_proof", "callee_summary_semantic_proof"
        }:
            raise ValueError("call/effect blocker semantic arm is not sealed")
        if type(self.effect_stage_required) is not bool:
            raise TypeError("call/effect effect-stage predicate must be exact bool")

    @classmethod
    def from_proof_input(cls, proof_input: Any) -> "CallEffectBlockerProductionSignal":
        from ..call_effect_producer import (
            PureCallRegionProofInput,
            PureDirectCallProofInput,
            _PRODUCER_KIND,
        )

        if type(proof_input) is PureCallRegionProofInput:
            semantic_arm = "inline_region_semantic_proof"
        elif type(proof_input) is PureDirectCallProofInput:
            semantic_arm = "callee_summary_semantic_proof"
        else:
            raise TypeError("call/effect blocker membership requires exact typed proof input")
        memory_stage_required = (
            bool(proof_input.region_effects or proof_input.call_effect.memory_effects)
            if type(proof_input) is PureCallRegionProofInput
            else bool(
                proof_input.left_effect.memory_effects
                or proof_input.right_effect.memory_effects
            )
        )
        caller_memory_stage_required = bool(
            proof_input.left_caller_effects
            or proof_input.right_caller_effects
            or int(getattr(proof_input.left_caller_profile, "store_count", 0) or 0)
            or int(getattr(proof_input.right_caller_profile, "store_count", 0) or 0)
            or any(
                int(getattr(evidence, "memory_effect_count", 0) or 0) > 0
                for evidence in (
                    *proof_input.left_caller_call_effects,
                    *proof_input.right_caller_call_effects,
                )
            )
        )
        return cls(
            "primary_proof_stage",
            "relational_call_effect_stage_proofs_missing",
            proof_input.obligation_id,
            proof_input.observation_contract_id,
            proof_input.left_fact_id,
            proof_input.right_fact_id,
            semantic_arm,
            proof_input.structural_certificate_id,
            _PRODUCER_KIND,
            memory_stage_required or caller_memory_stage_required,
            _factory_token=_CALL_EFFECT_BLOCKER_SIGNAL_TOKEN,
        )


@dataclass(frozen=True)
class CallEffectProofBatchProductionSignal:
    blocker: CallEffectBlockerProductionSignal
    artifacts: tuple[Any, ...]

    def __post_init__(self) -> None:
        if type(self.blocker) is not CallEffectBlockerProductionSignal:
            raise TypeError("call/effect proof batch lacks exact blocker signal")
        object.__setattr__(self, "artifacts", tuple(self.artifacts))
        if not self.artifacts:
            raise ValueError("call/effect proof batch cannot be empty")


class OutcomePartitionPilotEncoder:
    """Typed production encoder; registry-issued cause creation stays injectable."""

    def __init__(
        self,
        blocker_authority_factory: Callable[
            [Any, OutcomePartitionProductionSignal], CauseOccurrenceAuthority
        ],
    ) -> None:
        if not callable(blocker_authority_factory):
            raise TypeError("outcome partition blocker authority factory must be callable")
        self._blocker_authority_factory = blocker_authority_factory

    def __call__(
        self, session: Any, signal: OutcomePartitionProductionSignal
    ) -> tuple[EventIntent, ...]:
        if type(signal) is not OutcomePartitionProductionSignal:
            raise TypeError("outcome partition encoder requires an exact typed signal")
        if signal.producer_status == "proved":
            return ()
        authority = self._blocker_authority_factory(session, signal)
        if type(authority) is not CauseOccurrenceAuthority:
            raise TypeError("outcome partition factory returned non-authority")
        if authority.occurrence.source_snapshot_fingerprint != (
            session.identity.source_snapshot_fingerprint
        ):
            raise ValueError("outcome partition authority snapshot differs from session")
        return (EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(authority),
        ),)


class CompositeProductionSignalEncoder:
    """Exact-type router; an unregistered producer signal fails closed."""

    def __init__(self, routes: Mapping[type, Callable[[Any, Any], Any]]) -> None:
        if not routes or any(type(key) is not type or not callable(value) for key, value in routes.items()):
            raise TypeError("production signal routes must map exact types to encoders")
        self._routes = dict(routes)

    def __call__(self, session: Any, signal: Any) -> Any:
        encoder = self._routes.get(type(signal))
        if encoder is None:
            raise TypeError("production signal type has no registered encoder")
        return encoder(session, signal)

    def accepts_signal_type(self, signal_type: type) -> bool:
        return type(signal_type) is type and signal_type in self._routes

    def operational_authority_factory_for_session(self, session: Any) -> Any:
        factories = []
        for encoder in {id(value): value for value in self._routes.values()}.values():
            resolver = getattr(encoder, "authority_factory_for_session", None)
            if callable(resolver):
                factories.append(resolver(session))
        if not factories:
            return None
        if len(factories) != 1:
            raise ValueError("operational authority factory route is not unique")
        return factories[0]

    def has_observed(self, session: Any, signal: Any) -> bool:
        """Delegate conditional completion checks to the exact routed encoder."""

        encoder = self._routes.get(type(signal))
        if encoder is None:
            raise TypeError("production signal type has no registered encoder")
        predicate = getattr(encoder, "has_observed", None)
        if not callable(predicate):
            return False
        return bool(predicate(session, signal))

    def authority_for_signal(self, session: Any, signal: Any) -> Any:
        """Resolve exact routed occurrence authority without emitting an event."""

        encoder = self._routes.get(type(signal))
        resolver = getattr(encoder, "authority_for_signal", None)
        if not callable(resolver):
            raise TypeError("production signal route lacks occurrence authority")
        return resolver(session, signal)

    def finalize_terminal_timeout_bindings(
        self, session: Any, stream: Any
    ) -> tuple[tuple[int, str], ...]:
        bindings = []
        encoders = tuple({id(value): value for value in self._routes.values()}.values())
        for encoder in encoders:
            resolver = getattr(encoder, "finalize_terminal_timeout_bindings", None)
            if callable(resolver):
                bindings.extend(resolver(session, stream))
        if len({sequence for sequence, _ in bindings}) != len(bindings):
            raise ValueError("duplicate production terminal timeout selection")
        return tuple(sorted(bindings))

    def finalize_open_execution_history(self, session: Any) -> None:
        encoders = tuple({id(value): value for value in self._routes.values()}.values())
        for encoder in encoders:
            finalizer = getattr(encoder, "finalize_open_execution_history", None)
            if callable(finalizer):
                finalizer(session)

    def validate_startup(self) -> tuple[Any, ...]:
        encoders = tuple({id(value): value for value in self._routes.values()}.values())
        receipts = []
        for encoder in encoders:
            validator = getattr(encoder, "validate_startup", None)
            if callable(validator):
                receipt = validator()
                if receipt is not None:
                    receipts.append(receipt)
        return tuple(receipts)

    def build_call_effect_execution_context(
        self, session: Any, signals: tuple[Any, ...], registry: Any
    ) -> Any:
        encoders = {
            self._routes.get(type(signal)) for signal in signals
        }
        encoders.discard(None)
        if len(encoders) != 1:
            raise ValueError("call/effect signals do not have one exact encoder")
        encoder = next(iter(encoders))
        builder = getattr(encoder, "build_execution_context", None)
        if not callable(builder):
            raise TypeError("call/effect encoder lacks execution-context authority")
        return builder(session, signals, registry)

    def loop_requirement_for_signal(
        self, session: Any, blocker: Any, proof_kind: str
    ) -> Any:
        encoder = self._routes.get(type(blocker))
        resolver = getattr(encoder, "requirement_for_signal", None)
        if not callable(resolver):
            raise TypeError("loop blocker route lacks requirement authority")
        return resolver(session, blocker, proof_kind)

    def build_loop_execution_context(
        self, session: Any, blocker: Any, queries: tuple[Any, ...]
    ) -> Any:
        encoder = self._routes.get(type(blocker))
        builder = getattr(encoder, "build_execution_context", None)
        if not callable(builder):
            raise TypeError("loop blocker route lacks execution-context authority")
        return builder(session, blocker, queries)

    def register_readonly_promotion(self, session: Any, seed: Any) -> None:
        from .abi_width_readonly import AbiWidthReadonlyBlockerSignal

        encoder = self._routes.get(AbiWidthReadonlyBlockerSignal)
        registrar = getattr(encoder, "register_readonly_promotion", None)
        if not callable(registrar):
            raise TypeError("ABI/width route lacks readonly promotion authority")
        registrar(session, seed)

    def register_abi_width_solver_candidate(
        self, session: Any, blocker: Any, seed: Any
    ) -> None:
        from .abi_width_readonly import AbiWidthReadonlyBlockerSignal

        encoder = self._routes.get(AbiWidthReadonlyBlockerSignal)
        registrar = getattr(encoder, "register_solver_candidate", None)
        if not callable(registrar):
            raise TypeError("ABI/width route lacks solver scheduler authority")
        registrar(session, blocker, seed)

    def build_abi_width_execution_context(
        self, session: Any, blocker: Any, query: Any
    ) -> Any:
        from .abi_width_readonly import AbiWidthReadonlyBlockerSignal

        encoder = self._routes.get(AbiWidthReadonlyBlockerSignal)
        builder = getattr(encoder, "build_execution_context", None)
        if not callable(builder):
            raise TypeError("ABI/width route lacks execution-context authority")
        return builder(session, blocker, query)


def active_operational_authority_factory() -> Optional[Any]:
    session = active_production_pilot_session()
    if session is None:
        return None
    resolver = getattr(
        session.domain_signal_encoder,
        "operational_authority_factory_for_session",
        None,
    )
    if not callable(resolver):
        return None
    return resolver(session)


def record_production_pilot_shadow_error(exc: Exception) -> None:
    session = active_production_pilot_session()
    if session is not None:
        error_kinds = getattr(session, "domain_signal_error_kinds", None)
        if isinstance(error_kinds, list):
            error_kinds.append(type(exc).__name__)
        details = getattr(session, "domain_signal_error_details", None)
        if isinstance(details, list):
            details.append(str(exc))


def production_signal_scope(session: Any) -> Iterator[None]:
    return production_pilot_session_scope(session)


def emit_outcome_partition_signal(
    signal: OutcomePartitionProductionSignal,
    *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    """Return emitted event count; remain a strict no-op when pilot is disabled."""

    session = active_production_pilot_session()
    if session is None:
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def emit_sat_safety_signal(
    signal: (
        SatSafetyBlockerProductionSignal
        | SafeCounterexampleProductionSignal
        | EqClosureProductionSignal
    ),
    *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    session = active_production_pilot_session()
    if session is None:
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def emit_sat_safety_completion_if_observed(
    signal: SatSafetyBlockerProductionSignal,
    *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    if signal.action != "COMPLETED":
        raise ValueError("conditional SAT safety emission requires completion")
    session = active_production_pilot_session()
    if session is None:
        return 0
    emit = getattr(session, "emit_domain_signal_if_observed", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks conditional signal authority")
    return int(emit(signal, producer_site_manifest_id))


def emit_call_effect_signal(
    signal: Any, *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    session = active_production_pilot_session()
    if session is None:
        return 0
    accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
    if callable(accepts) and not accepts(type(signal)):
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def emit_loop_recurrence_signal(
    signal: Any, *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    """Emit an exact slice4 signal; remain inert for pilots without its route."""

    from .loop_recurrence import (
        LoopBlockerProductionSignal,
        LoopExactGuardPartitionCompletionSignal,
        LoopExactTermRelationCompletionSignal,
        LoopSolverExecutionBatchSignal,
        RecurrenceValidationCompletionSignal,
    )

    if type(signal) not in {
        LoopBlockerProductionSignal,
        LoopExactGuardPartitionCompletionSignal,
        LoopExactTermRelationCompletionSignal,
        LoopSolverExecutionBatchSignal,
        RecurrenceValidationCompletionSignal,
    }:
        raise TypeError("loop/recurrence emission requires an exact typed signal")
    session = active_production_pilot_session()
    if session is None:
        return 0
    accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
    if callable(accepts) and not accepts(type(signal)):
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def emit_abi_width_readonly_signal(
    signal: Any, *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    """Emit one exact slice5 blocker; remain inert when its route is absent."""

    from .abi_width_readonly import AbiWidthReadonlyBlockerSignal

    if type(signal) is not AbiWidthReadonlyBlockerSignal:
        raise TypeError("ABI/width/readonly emission requires an exact blocker signal")
    session = active_production_pilot_session()
    if session is None:
        return 0
    accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
    if callable(accepts) and not accepts(type(signal)):
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def emit_operational_extraction_signal(
    signal: Any, *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    """Emit only when the active composite explicitly registers the exact type."""

    session = active_production_pilot_session()
    if session is None:
        return 0
    accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
    if not callable(accepts) or not accepts(type(signal)):
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def register_readonly_promotion(seed: Any) -> None:
    """Register a typed readonly base seed for pre-seal relational promotion."""

    from .abi_width_readonly import ReadonlyReductionObjectSetSeed

    if type(seed) is not ReadonlyReductionObjectSetSeed:
        raise TypeError("readonly promotion registration requires an exact base seed")
    session = active_production_pilot_session()
    if session is None:
        return
    registrar = getattr(session.domain_signal_encoder, "register_readonly_promotion", None)
    if not callable(registrar):
        return
    registrar(session, seed)


def register_abi_width_solver_candidate(blocker: Any, seed: Any) -> None:
    """Register one exact dependency-gated semantic solver candidate."""

    from .abi_width_readonly import AbiWidthReadonlyBlockerSignal

    if type(blocker) is not AbiWidthReadonlyBlockerSignal:
        raise TypeError("ABI/width scheduler registration requires exact blocker")
    session = active_production_pilot_session()
    if session is None:
        return
    registrar = getattr(
        session.domain_signal_encoder,
        "register_abi_width_solver_candidate",
        None,
    )
    if not callable(registrar):
        return
    registrar(session, blocker, seed)


def execute_abi_width_readonly_solver_query(
    blocker: Any,
    query: Any,
    proof_seed: Any,
    dependency_artifacts: tuple[Any, ...],
    *,
    configured_timeout_ms: int,
) -> int:
    """Execute one exact slice-5 semantic query through the signed issuer."""

    from .abi_width_readonly import (
        ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY,
        AbiWidthReadonlySolverExecutionBatchSignal,
        AbiWidthReadonlySolverQueryAuthority,
    )
    from .execution_authority import PINNED_SOLVER_EXECUTION_ISSUER

    if type(query) is not AbiWidthReadonlySolverQueryAuthority:
        raise TypeError("ABI/width execution requires exact semantic query")
    session = active_production_pilot_session()
    if session is None:
        return 0
    builder = getattr(
        session.domain_signal_encoder, "build_abi_width_execution_context", None
    )
    if not callable(builder):
        return 0
    context = builder(session, blocker, query)
    membership = context.membership_for(query)
    first_invocation_ordinal = int(session.domain_signal_state.get(
        "abi_width_next_invocation_ordinal", 1
    ))
    receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
        registry=ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY,
        result_occurrence_id=session.identity.result_occurrence_id,
        membership=membership,
        invocation_identity=(
            session.identity.result_occurrence_id
            + ":" + query.obligation_id + ":" + query.proof_stage
        ),
        first_invocation_ordinal=first_invocation_ordinal,
        query=query.query_text,
        configured_timeout_ms=configured_timeout_ms,
        query_authority=query,
        lifecycle_projection=context.lifecycle_projection,
    )
    session.domain_signal_state["abi_width_next_invocation_ordinal"] = (
        max(receipt.invocation_ordinal for receipt in receipts) + 1
    )
    emitted = int(session.emit_domain_signal(
        AbiWidthReadonlySolverExecutionBatchSignal.from_issuer_results(
            blocker, query, proof_seed, dependency_artifacts,
            membership, receipts, context.lifecycle_projection,
        )
    ))
    pending = tuple(session.domain_signal_state.pop(
        "abi_width_sat_safety_handoffs", ()
    ))
    if pending:
        accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
        if not callable(accepts) or not accepts(SatSafetyBlockerProductionSignal):
            raise ValueError("ABI/width SAT lacks counterexample-safety route")
        for handoff in pending:
            emitted += int(session.emit_domain_signal(handoff))
    return emitted


def active_loop_requirement_for_signal(
    blocker: Any, proof_kind: str
) -> Any:
    """Resolve exact live-Q identity only while an opted-in pilot is active."""

    session = active_production_pilot_session()
    if session is None:
        return None
    resolver = getattr(
        session.domain_signal_encoder, "loop_requirement_for_signal", None
    )
    if not callable(resolver):
        return None
    return resolver(session, blocker, proof_kind)


def active_production_execution_identity_digest() -> Optional[str]:
    session = active_production_pilot_session()
    if session is None:
        return None
    return str(session.identity.execution_identity_digest)


def execute_loop_solver_rendered_query(
    blocker: Any,
    rendered: Any,
    *,
    configured_timeout_ms: int,
) -> int:
    """Execute a typed rendered loop query through the common signed issuer."""

    from .execution_authority import PINNED_SOLVER_EXECUTION_ISSUER
    from .loop_recurrence import (
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        LoopSolverExecutionBatchSignal,
        _issue_loop_solver_query_authority,
    )

    session = active_production_pilot_session()
    if session is None:
        return 0
    query = _issue_loop_solver_query_authority(rendered)
    builder = getattr(
        session.domain_signal_encoder, "build_loop_execution_context", None
    )
    if not callable(builder):
        return 0
    context = builder(session, blocker, (query,))
    membership = context.membership_for(query)
    receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
        registry=LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        result_occurrence_id=session.identity.result_occurrence_id,
        membership=membership,
        invocation_identity=(
            session.identity.result_occurrence_id
            + ":"
            + query.obligation_id
            + ":"
            + query.stage
        ),
        first_invocation_ordinal=1,
        query=query.query_text,
        configured_timeout_ms=configured_timeout_ms,
        query_authority=query,
        lifecycle_projection=context.lifecycle_projection,
    )
    emitted = int(session.emit_domain_signal(
        LoopSolverExecutionBatchSignal.from_issuer_results(
            blocker, query, membership, receipts, context.lifecycle_projection
        )
    ))
    pending_handoffs = tuple(
        session.domain_signal_state.pop("loop_sat_safety_handoffs", ())
    )
    if pending_handoffs:
        accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
        if not callable(accepts) or not accepts(SatSafetyBlockerProductionSignal):
            raise ValueError(
                "loop SAT refutation lacks Phase 6.1 counterexample-safety route"
            )
        for handoff in pending_handoffs:
            if type(handoff) is not SatSafetyBlockerProductionSignal:
                raise TypeError("loop SAT handoff signal is not exact")
            emitted += int(session.emit_domain_signal(handoff))
    return emitted


def build_active_call_effect_execution_context(
    signals: tuple[CallEffectBlockerProductionSignal, ...], registry: Any
) -> Any:
    session = active_production_pilot_session()
    if session is None:
        return None
    accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
    if callable(accepts) and (
        not signals or not all(accepts(type(signal)) for signal in signals)
    ):
        return None
    builder = getattr(session.domain_signal_encoder, "build_call_effect_execution_context", None)
    if not callable(builder):
        return None
    return builder(session, tuple(signals), registry)
