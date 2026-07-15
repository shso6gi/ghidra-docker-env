"""Validated, generation-bound authority for logical pair disposition."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
import hashlib
import hmac
import inspect
import secrets
from threading import Lock
from typing import Any, ClassVar, Dict, Mapping, Optional, Tuple, Union

from .guard_overlap import GuardDisjointArtifact


_CLOSURE_ARTIFACT_AUTHORITY_KEY = secrets.token_bytes(32)


def _closure_artifact_seal(payload: Tuple[Any, ...]) -> str:
    return hmac.new(
        _CLOSURE_ARTIFACT_AUTHORITY_KEY,
        repr(payload).encode("utf-8"),
        hashlib.sha256,
    ).hexdigest()


class PairDisposition(str, Enum):
    UNSAT = "unsat"
    SAT = "sat"
    UNKNOWN = "unknown"
    ERROR = "error"
    SKIPPED = "skipped_after_terminal_decision"


class PairClosureKind(str, Enum):
    GUARD_QUERY = "guard_query"
    VALUE_QUERY = "value_query"
    CACHE = "cache"
    RECOVERY = "recovery"
    RETURN_WIDTH = "return_width"
    AGGREGATE = "aggregate"


class LedgerLifecycle(str, Enum):
    OPEN = "open"
    SEALED = "sealed"
    SUPERSEDED = "superseded"


@dataclass(frozen=True)
class PairLedgerBinding:
    comparison_session_id: str
    branch_id: str
    prepared_surface_digest: str
    projection_id: str
    frame_generation: int
    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    graph_generation: int
    schema_version: str = "pair_disposition_ledger_v2"

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version, self.comparison_session_id, self.branch_id,
            self.prepared_surface_digest, self.projection_id, self.frame_generation,
            self.derived_view_id, self.premise_digest, self.graph_generation,
        )


@dataclass(frozen=True)
class PairLedgerSuccessorPlan:
    """Replan identity known before the replacement projection is prepared.

    The prepared-surface and projection identities are deliberately absent.
    They are authority-bearing properties of the replacement dispatch and can
    only be bound after that dispatch has rebuilt its call-effect projection.
    """

    comparison_session_id: str
    branch_id: str
    frame_generation: int
    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    graph_generation: int
    expected_pairs: int
    predecessor_projection_id: str
    projection_refresh_required: bool = False
    schema_version: str = "pair_ledger_successor_plan_v1"

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version,
            self.comparison_session_id,
            self.branch_id,
            self.frame_generation,
            self.derived_view_id,
            self.premise_digest,
            self.graph_generation,
            self.expected_pairs,
            self.predecessor_projection_id,
            self.projection_refresh_required,
        )

    def accepts(self, binding: PairLedgerBinding, expected_pairs: int) -> bool:
        return (
            binding.comparison_session_id == self.comparison_session_id
            and binding.branch_id == self.branch_id
            and binding.frame_generation == self.frame_generation
            and binding.derived_view_id == self.derived_view_id
            and binding.premise_digest == self.premise_digest
            and binding.graph_generation == self.graph_generation
            and int(expected_pairs) == self.expected_pairs
            and (
                not self.projection_refresh_required
                or binding.projection_id != self.predecessor_projection_id
            )
        )


@dataclass(frozen=True)
class SolverUnsatClosureArtifact:
    formula_digest: str
    premise_digest: str
    query_label: str
    producer_kind: str
    authority_digest: str = ""
    solver_status: str = "unsat"
    schema_version: str = "solver_unsat_closure_v1"

    @classmethod
    def from_validated_result(
        cls, query: str, premise_digest: str, query_label: str,
        producer_kind: str, result: Any,
    ) -> "SolverUnsatClosureArtifact":
        if getattr(result, "is_equivalent", None) is not True:
            raise ValueError("solver closure requires a validated UNSAT result")
        formula_digest = hashlib.sha256(query.encode()).hexdigest()
        payload = (
            formula_digest, premise_digest, query_label, producer_kind, "unsat",
        )
        return cls(
            formula_digest, premise_digest, query_label, producer_kind,
            _closure_artifact_seal(payload),
        )

    @classmethod
    def from_terminal_record(
        cls, query: str, premise_digest: str, query_label: str,
        producer_kind: str, disposition: PairDisposition,
    ) -> "SolverUnsatClosureArtifact":
        if disposition == PairDisposition.UNSAT:
            raise ValueError("UNSAT requires validated solver authority")
        formula_digest = hashlib.sha256(query.encode()).hexdigest()
        status = disposition.value
        payload = (
            formula_digest, premise_digest, query_label, producer_kind, status,
        )
        return cls(
            formula_digest, premise_digest, query_label, producer_kind,
            _closure_artifact_seal(payload), solver_status=status,
        )

    def validates(
        self,
        expected_status: str = "unsat",
        expected_premise_digest: Optional[str] = None,
    ) -> bool:
        return (
            self.solver_status == expected_status
            and len(self.formula_digest) == 64
            and bool(self.premise_digest)
            and (
                expected_premise_digest is None
                or self.premise_digest == expected_premise_digest
            )
            and bool(self.query_label)
            and self.producer_kind in {"value_query", "return_width", "recovery", "aggregate"}
            and hmac.compare_digest(
                self.authority_digest,
                _closure_artifact_seal((
                    self.formula_digest, self.premise_digest, self.query_label,
                    self.producer_kind, self.solver_status,
                )),
            )
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return tuple(self.__dict__.values())


@dataclass(frozen=True)
class GuardUnsatClosureArtifact:
    artifact: GuardDisjointArtifact

    def validates(self, binding: PairLedgerBinding) -> bool:
        return (
            self.artifact.validates()
            and
            self.artifact.derived_view_id == binding.derived_view_id
            and self.artifact.premise_digest == binding.premise_digest
            and self.artifact.graph_generation == binding.graph_generation
            and len(self.artifact.query_digest) == 64
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "guard_unsat_closure_v1",
            self.artifact.requirement_key,
            self.artifact.query_digest,
            self.artifact.derived_view_id,
            self.artifact.premise_digest,
            self.artifact.graph_generation,
            self.artifact.query_execution_digest,
            self.artifact.query_issuer_identity,
            self.artifact.authority_digest,
            "validated" if self.artifact.validates() else "invalid",
        )


@dataclass(frozen=True)
class CounterexampleSafetyReceipt:
    formula_digest: str
    model_digest: str
    premise_digest: str
    pair_key: Tuple[int, int]
    validation_steps: Tuple[str, ...]
    authority_digest: str
    schema_version: str = "counterexample_safety_receipt_v1"

    @classmethod
    def from_pairwise_validation(
        cls, *, query: str, model: Any, premise_digest: str,
        pair_key: Tuple[int, int], analysis_safe: bool,
        global_case_replay_safe: bool, same_function_replay_safe: bool,
    ) -> "CounterexampleSafetyReceipt":
        if not (analysis_safe and global_case_replay_safe and same_function_replay_safe):
            raise ValueError("counterexample safety validation is incomplete")
        formula_digest = hashlib.sha256(query.encode()).hexdigest()
        model_digest = hashlib.sha256(repr(model).encode()).hexdigest()
        steps = (
            "analysis_summary_safe", "global_case_replay_safe",
            "same_function_replay_safe",
        )
        payload = (formula_digest, model_digest, premise_digest, pair_key, steps)
        return cls(
            formula_digest, model_digest, premise_digest, pair_key, steps,
            _closure_artifact_seal(payload),
        )

    def validates(self, binding: PairLedgerBinding, pair_key: Tuple[int, int]) -> bool:
        payload = (
            self.formula_digest, self.model_digest, self.premise_digest,
            self.pair_key, self.validation_steps,
        )
        return (
            len(self.formula_digest) == 64
            and len(self.model_digest) == 64
            and self.premise_digest == binding.premise_digest
            and self.pair_key == pair_key
            and self.validation_steps == (
                "analysis_summary_safe", "global_case_replay_safe",
                "same_function_replay_safe",
            )
            and hmac.compare_digest(
                self.authority_digest, _closure_artifact_seal(payload)
            )
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return tuple(self.__dict__.values())


@dataclass(frozen=True)
class TerminalPairArtifact:
    terminal_record: SolverUnsatClosureArtifact
    safety_receipt: Optional[CounterexampleSafetyReceipt] = None

    def validates(
        self, binding: PairLedgerBinding, pair_key: Tuple[int, int],
        disposition: PairDisposition,
    ) -> bool:
        return (
            self.terminal_record.validates(disposition.value, binding.premise_digest)
            and (
                disposition != PairDisposition.SAT
                or (
                    self.safety_receipt is not None
                    and self.safety_receipt.validates(binding, pair_key)
                    and self.safety_receipt.formula_digest
                    == self.terminal_record.formula_digest
                )
            )
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "terminal_pair_artifact_v1",
            self.terminal_record.stable_key(),
            self.safety_receipt.stable_key() if self.safety_receipt else (),
        )


@dataclass(frozen=True)
class ProducerValidatedClosureArtifact:
    """Sealed output issued only after a producer-specific candidate check."""

    proposition_digest: str
    evidence_digest: str
    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    graph_generation: int
    authority_digest: str
    validation_status: str = "validated"
    schema_version: str = "producer_validated_closure_v2"

    PRODUCER_KIND: ClassVar[str] = "abstract"

    def validates(self, binding: PairLedgerBinding) -> bool:
        payload = (
            self.PRODUCER_KIND, self.proposition_digest, self.evidence_digest,
            self.derived_view_id, self.premise_digest,
            self.graph_generation, self.validation_status, self.schema_version,
        )
        return (
            self.PRODUCER_KIND != "abstract"
            and self.validation_status == "validated"
            and len(self.proposition_digest) == 64
            and len(self.evidence_digest) == 64
            and self.derived_view_id == binding.derived_view_id
            and self.premise_digest == binding.premise_digest
            and self.graph_generation == binding.graph_generation
            and hmac.compare_digest(
                self.authority_digest, _closure_artifact_seal(payload)
            )
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return (self.PRODUCER_KIND,) + tuple(self.__dict__.values())


class RuntimeReductionClosureArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "runtime_reduction_v2"


class CountedLoopClosedExpressionArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "counted_loop_closed_expression_v2"


class MethodBClosureArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "method_b_closure_v2"


class ReadonlyIdentityClosureArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "readonly_identity_closure_v2"


class CountedLoopValueRelationArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "counted_loop_value_relation_v2"


class AggregatePartitionClosureArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "aggregate_partition_closure_v2"


_TRUSTED_PRODUCER_VALIDATOR_CODES: Dict[str, Any] = {}


def issue_producer_validated_closure(
    artifact_type: type[ProducerValidatedClosureArtifact],
    binding: PairLedgerBinding,
    proposition: Any,
    evidence: Any,
) -> ProducerValidatedClosureArtifact:
    """Issue authority only from an import-time registered validator."""

    current = inspect.currentframe()
    caller = current.f_back if current is not None else None
    try:
        if (
            caller is None
            or _TRUSTED_PRODUCER_VALIDATOR_CODES.get(
                artifact_type.PRODUCER_KIND
            ) is not caller.f_code
        ):
            raise RuntimeError("producer closure issuer is not trusted")
    finally:
        del caller
        del current
    proposition_digest = hashlib.sha256(repr(proposition).encode()).hexdigest()
    evidence_digest = hashlib.sha256(repr(evidence).encode()).hexdigest()
    payload = (
        artifact_type.PRODUCER_KIND, proposition_digest, evidence_digest,
        binding.derived_view_id, binding.premise_digest,
        binding.graph_generation, "validated",
        artifact_type.schema_version,
    )
    return artifact_type(
        proposition_digest, evidence_digest, binding.derived_view_id,
        binding.premise_digest, binding.graph_generation,
        _closure_artifact_seal(payload),
    )


def register_producer_closure_validator(
    artifact_type: type[ProducerValidatedClosureArtifact],
    validator: Any,
) -> None:
    """Pin one import-time validator code object per artifact variant."""

    if artifact_type.PRODUCER_KIND in _TRUSTED_PRODUCER_VALIDATOR_CODES:
        raise RuntimeError("producer closure validator already registered")
    _TRUSTED_PRODUCER_VALIDATOR_CODES[
        artifact_type.PRODUCER_KIND
    ] = validator.__code__


ValidatedClosureArtifact = Union[
    GuardUnsatClosureArtifact,
    SolverUnsatClosureArtifact,
    TerminalPairArtifact,
    ProducerValidatedClosureArtifact,
]


@dataclass(frozen=True)
class PairClosureEvidence:
    pair_key: Tuple[int, int]
    disposition: PairDisposition
    closure_kind: PairClosureKind
    binding_key: Tuple[Any, ...]
    artifact: ValidatedClosureArtifact
    evidence_digest: str
    required_binding_uses: Tuple[str, ...] = ()
    consumed_binding_uses: Tuple[str, ...] = ()
    excluded_binding_uses: Tuple[str, ...] = ()

    @classmethod
    def validated(
        cls, pair_key: Tuple[int, int], closure_kind: PairClosureKind,
        binding: PairLedgerBinding, artifact: ValidatedClosureArtifact, *,
        required_binding_uses: Tuple[str, ...] = (),
        consumed_binding_uses: Tuple[str, ...] = (),
    ) -> "PairClosureEvidence":
        valid = (
            artifact.validates(binding)
            if isinstance(
                artifact,
                (GuardUnsatClosureArtifact, ProducerValidatedClosureArtifact),
            )
            else artifact.validates("unsat", binding.premise_digest)
        )
        if not valid:
            raise ValueError("pair closure artifact failed validation")
        required = tuple(sorted(set(required_binding_uses)))
        consumed = tuple(sorted(set(consumed_binding_uses)))
        if not set(consumed).issubset(required):
            raise ValueError("consumed binding use is not required by pair")
        excluded = tuple(sorted(set(required) - set(consumed)))
        digest = hashlib.sha256(repr((
            binding.stable_key(), artifact.stable_key(), required, consumed, excluded,
        )).encode()).hexdigest()
        return cls(
            pair_key, PairDisposition.UNSAT, closure_kind, binding.stable_key(),
            artifact, digest, required, consumed, excluded,
        )

    def validates(self, binding: PairLedgerBinding) -> bool:
        if self.binding_key != binding.stable_key() or self.disposition != PairDisposition.UNSAT:
            return False
        valid = (
            self.artifact.validates(binding)
            if isinstance(
                self.artifact,
                (GuardUnsatClosureArtifact, ProducerValidatedClosureArtifact),
            )
            else self.artifact.validates("unsat", binding.premise_digest)
        )
        if (
            tuple(sorted(set(self.required_binding_uses))) != self.required_binding_uses
            or tuple(sorted(set(self.consumed_binding_uses))) != self.consumed_binding_uses
            or self.excluded_binding_uses != tuple(sorted(
                set(self.required_binding_uses) - set(self.consumed_binding_uses)
            ))
        ):
            return False
        expected = hashlib.sha256(repr((
            binding.stable_key(), self.artifact.stable_key(),
            self.required_binding_uses, self.consumed_binding_uses,
            self.excluded_binding_uses,
        )).encode()).hexdigest()
        return valid and self.evidence_digest == expected

    def snapshot_key(self) -> Tuple[Any, ...]:
        artifact = self.artifact
        return (
            "pair_closure_snapshot_v2",
            self.pair_key,
            self.disposition.value,
            self.closure_kind.value,
            self.binding_key,
            type(artifact).__name__,
            artifact.stable_key(),
            "validated" if self.disposition == PairDisposition.UNSAT else "terminal",
            self.required_binding_uses,
            self.consumed_binding_uses,
            self.excluded_binding_uses,
            self.evidence_digest,
        )


@dataclass(frozen=True)
class InconclusivePairRecord:
    pair_key: Tuple[int, int]
    reason_id: str
    binding_key: Tuple[Any, ...]
    evidence_digest: str


@dataclass(frozen=True)
class RuntimeQuiescenceCertificate:
    binding_key: Tuple[Any, ...]
    expected_pairs: int
    closed_pairs: int
    pending_work_items: int
    provisional_pairs: int
    runtime_view_id: Tuple[Any, ...]
    runtime_premise_digest: str
    pending_work: Tuple[Tuple[str, str], ...] = ()
    active_owner_work: Tuple[Any, ...] = ()

    @property
    def is_quiescent(self) -> bool:
        return self.closed_pairs == self.expected_pairs and self.pending_work_items == 0 and self.provisional_pairs == 0


@dataclass
class PairDispositionLedger:
    binding: PairLedgerBinding
    expected_pairs: int
    lifecycle: LedgerLifecycle = LedgerLifecycle.OPEN
    closures: Dict[Tuple[int, int], PairClosureEvidence] = field(default_factory=dict)
    provisional: Dict[Tuple[int, int], InconclusivePairRecord] = field(default_factory=dict)
    _lock: Lock = field(default_factory=Lock, repr=False, compare=False)

    def close(self, evidence: PairClosureEvidence) -> None:
        with self._lock:
            if self.lifecycle != LedgerLifecycle.OPEN or not evidence.validates(self.binding):
                raise ValueError("invalid closure for current open ledger")
            if evidence.pair_key in self.provisional:
                raise RuntimeError("pair already has provisional disposition")
            previous = self.closures.get(evidence.pair_key)
            if previous is not None:
                raise RuntimeError("duplicate pair closure")
            self.closures[evidence.pair_key] = evidence

    def record_inconclusive(self, pair_key: Tuple[int, int], reason_id: str, evidence: Any) -> None:
        with self._lock:
            if self.lifecycle != LedgerLifecycle.OPEN or pair_key in self.closures:
                raise RuntimeError("cannot record provisional pair")
            self.provisional[pair_key] = InconclusivePairRecord(
                pair_key, str(reason_id), self.binding.stable_key(),
                hashlib.sha256(repr(evidence).encode()).hexdigest(),
            )

    def record_terminal_query(
        self, pair_key: Tuple[int, int], disposition: PairDisposition,
        query: str, producer_kind: str, *,
        safety_receipt: Optional[CounterexampleSafetyReceipt] = None,
    ) -> None:
        if disposition == PairDisposition.UNSAT:
            raise ValueError("UNSAT requires validated closure path")
        with self._lock:
            if self.lifecycle != LedgerLifecycle.OPEN or pair_key in self.provisional:
                raise RuntimeError("cannot record terminal pair")
            terminal_record = SolverUnsatClosureArtifact.from_terminal_record(
                query or repr((pair_key, disposition.value)),
                self.binding.premise_digest,
                repr(pair_key), producer_kind, disposition,
            )
            artifact = TerminalPairArtifact(terminal_record, safety_receipt)
            if not artifact.validates(self.binding, pair_key, disposition):
                raise ValueError("terminal pair artifact failed validation")
            digest = hashlib.sha256(repr((
                self.binding.stable_key(), artifact.stable_key(), (), (), (),
            )).encode()).hexdigest()
            evidence = PairClosureEvidence(
                pair_key, disposition, PairClosureKind.VALUE_QUERY,
                self.binding.stable_key(), artifact, digest,
            )
            previous = self.closures.get(pair_key)
            if previous is not None:
                raise RuntimeError("duplicate pair closure")
            self.closures[pair_key] = evidence

    def finalize_inconclusive(self) -> None:
        with self._lock:
            for pair_key, record in tuple(self.provisional.items()):
                artifact = TerminalPairArtifact(
                    SolverUnsatClosureArtifact.from_terminal_record(
                        record.evidence_digest, self.binding.premise_digest,
                        repr(pair_key), "aggregate", PairDisposition.UNKNOWN,
                    )
                )
                # UNKNOWN is a terminal record, not a proof closure.
                digest = hashlib.sha256(repr((
                    self.binding.stable_key(), artifact.stable_key(), (), (), (),
                )).encode()).hexdigest()
                self.closures[pair_key] = PairClosureEvidence(
                    pair_key, PairDisposition.UNKNOWN, PairClosureKind.AGGREGATE,
                    self.binding.stable_key(), artifact, digest,
                )
            self.provisional.clear()

    def counts(self) -> Mapping[str, int]:
        counts = {item.value: 0 for item in PairDisposition}
        for closure in self.closures.values():
            counts[closure.disposition.value] += 1
        counts["total"] = self.expected_pairs
        return counts

    def closure_snapshot(self) -> Tuple[Tuple[Any, ...], ...]:
        return tuple(self.closures[key].snapshot_key() for key in sorted(self.closures))

    def binding_use_partitions(
        self,
    ) -> Tuple[Tuple[str, ...], Tuple[str, ...], Tuple[str, ...]]:
        """Aggregate binding use from the validated closure snapshot."""

        required = {
            use
            for closure in self.closures.values()
            for use in closure.required_binding_uses
        }
        consumed = {
            use
            for closure in self.closures.values()
            for use in closure.consumed_binding_uses
        }
        excluded = {
            use
            for closure in self.closures.values()
            for use in closure.excluded_binding_uses
        } - consumed
        return (
            tuple(sorted(required)),
            tuple(sorted(consumed)),
            tuple(sorted(excluded)),
        )

    def validates_complete_snapshot(self) -> bool:
        if len(self.closures) != self.expected_pairs or self.provisional:
            return False
        for evidence in self.closures.values():
            if evidence.disposition == PairDisposition.UNSAT:
                if not evidence.validates(self.binding):
                    return False
            else:
                if (
                    evidence.binding_key != self.binding.stable_key()
                    or not isinstance(evidence.artifact, TerminalPairArtifact)
                    or not evidence.artifact.validates(
                        self.binding, evidence.pair_key, evidence.disposition
                    )
                ):
                    return False
                expected = hashlib.sha256(repr((
                    self.binding.stable_key(), evidence.artifact.stable_key(),
                    evidence.required_binding_uses, evidence.consumed_binding_uses,
                    evidence.excluded_binding_uses,
                )).encode()).hexdigest()
                if evidence.evidence_digest != expected:
                    return False
        return True

    def seal(self, certificate: RuntimeQuiescenceCertificate) -> None:
        with self._lock:
            if self.lifecycle != LedgerLifecycle.OPEN:
                raise RuntimeError("pair ledger is not open")
            if certificate.binding_key != self.binding.stable_key():
                raise ValueError("quiescence certificate binding mismatch")
            if not certificate.is_quiescent:
                raise RuntimeError(
                    "pair ledger cannot seal before runtime quiescence: "
                    f"closed={certificate.closed_pairs}/{certificate.expected_pairs}, "
                    f"pending={certificate.pending_work_items}, "
                    f"provisional={certificate.provisional_pairs}, "
                    f"work={certificate.pending_work!r}"
                )
            if not self.validates_complete_snapshot():
                raise RuntimeError("pair ledger closure snapshot is incomplete or invalid")
            if certificate.runtime_view_id != self.binding.derived_view_id or certificate.runtime_premise_digest != self.binding.premise_digest:
                raise RuntimeError("runtime generation changed before seal")
            self.lifecycle = LedgerLifecycle.SEALED

    def supersede(self) -> None:
        with self._lock:
            if self.lifecycle == LedgerLifecycle.OPEN:
                self.lifecycle = LedgerLifecycle.SUPERSEDED


@dataclass
class PairLedgerManager:
    current: Optional[PairDispositionLedger] = None
    history: list[PairDispositionLedger] = field(default_factory=list)
    pending_successor: Optional[PairLedgerSuccessorPlan] = None

    def open(self, binding: PairLedgerBinding, expected_pairs: int) -> PairDispositionLedger:
        if self.pending_successor is not None:
            plan = self.pending_successor
            if self.current is not None:
                raise RuntimeError("pending successor conflicts with current ledger")
            if not plan.accepts(binding, expected_pairs):
                raise RuntimeError("replacement ledger does not match successor plan")
            self.current = PairDispositionLedger(binding, expected_pairs)
            self.pending_successor = None
            return self.current
        if self.current is not None and (
            self.current.binding.stable_key() != binding.stable_key()
            or self.current.lifecycle != LedgerLifecycle.OPEN
        ):
            self.current.supersede()
            self.history.append(self.current)
            self.current = None
        if self.current is None:
            self.current = PairDispositionLedger(binding, expected_pairs)
        elif self.current.expected_pairs != expected_pairs:
            raise RuntimeError("successor ledger pair plan changed during replan")
        return self.current

    def supersede_current(self) -> None:
        if self.current is not None:
            self.current.supersede()
            self.history.append(self.current)
            self.current = None

    def plan_successor(
        self,
        derived_view_id: Tuple[Any, ...],
        premise_digest: str,
        *,
        projection_refresh_required: bool = False,
    ) -> Optional[PairLedgerSuccessorPlan]:
        """Supersede the old ledger and defer final binding until projection rebuild."""

        previous = self.current
        if previous is None:
            pending = self.pending_successor
            if pending is None:
                return None
            successor = PairLedgerSuccessorPlan(
                pending.comparison_session_id,
                pending.branch_id,
                pending.frame_generation,
                tuple(derived_view_id),
                str(premise_digest),
                pending.graph_generation,
                pending.expected_pairs,
                pending.predecessor_projection_id,
                bool(
                    pending.projection_refresh_required
                    or projection_refresh_required
                ),
            )
            self.pending_successor = successor
            return successor
        self.supersede_current()
        old = previous.binding
        successor = PairLedgerSuccessorPlan(
            old.comparison_session_id,
            old.branch_id,
            old.frame_generation,
            tuple(derived_view_id),
            str(premise_digest),
            old.graph_generation + 1,
            previous.expected_pairs,
            old.projection_id,
            bool(projection_refresh_required),
        )
        self.pending_successor = successor
        return successor
