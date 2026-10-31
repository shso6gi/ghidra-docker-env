"""Central ordered event recorder and hash-chain validation."""

from __future__ import annotations

import weakref
from dataclasses import dataclass, field
from enum import Enum
from types import MappingProxyType
from typing import Any, Callable, Dict, Iterable, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.authority.contracts import (
    SCHEMA_VERSION,
    VALIDATED_ONCE,
    assert_deep_immutable,
    authority_digest,
    canonical_value,
    freeze_authority_value,
)
from scripts.function_tracer_pcode.authority.contracts import (
    CauseOccurrenceAuthority,
    CauseTransformationEvent,
    CauseTransformationProofReceipt,
    RequirementCompletionReceipt,
)


class EventType(str, Enum):
    CAUSE_OBSERVED = "CAUSE_OBSERVED"
    REQUIREMENT_COMPLETED = "REQUIREMENT_COMPLETED"
    CAUSE_TRANSFORMED = "CAUSE_TRANSFORMED"
    OUTCOME_PRODUCER_ATTEMPT = "OUTCOME_PRODUCER_ATTEMPT"
    SOLVER_UNKNOWN = "SOLVER_UNKNOWN"
    SOLVER_TIMEOUT = "SOLVER_TIMEOUT"
    SOLVER_ERROR = "SOLVER_ERROR"
    PROCESS_COMPLETED = "PROCESS_COMPLETED"
    PROCESS_TIMEOUT = "PROCESS_TIMEOUT"
    CANCELLED = "CANCELLED"
    NORMALIZATION_NO_CHANGE = "NORMALIZATION_NO_CHANGE"
    REWRITE_NO_CHANGE = "REWRITE_NO_CHANGE"
    EQ_CLOSURE = "EQ_CLOSURE"
    COUNTEREXAMPLE = "COUNTEREXAMPLE"
    ERROR = "ERROR"


@dataclass(frozen=True)
class EventIntent:
    event_type: EventType
    authority_payload: Any
    diagnostic_payload: Any = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "event_type", EventType(self.event_type))
        validate_event_authority_payload(self.event_type, self.authority_payload)


def _require_exact_strings(*values: str) -> None:
    if not all(type(value) is str and value for value in values):
        raise TypeError("event authority identifiers must be non-empty exact strings")


@dataclass(frozen=True)
class CauseObservedEventAuthority:
    occurrence_authority: CauseOccurrenceAuthority

    def __post_init__(self) -> None:
        if type(self.occurrence_authority) is not CauseOccurrenceAuthority:
            raise TypeError("cause-observed payload requires exact occurrence authority")


@dataclass(frozen=True)
class RequirementCompletedEventAuthority:
    completion_receipt: RequirementCompletionReceipt

    def __post_init__(self) -> None:
        if type(self.completion_receipt) is not RequirementCompletionReceipt:
            raise TypeError("requirement-completed payload requires exact completion receipt")


@dataclass(frozen=True)
class CauseTransformedEventAuthority:
    transformation_event: CauseTransformationEvent
    proof_receipt: CauseTransformationProofReceipt

    def __post_init__(self) -> None:
        self.proof_receipt.validate_event(self.transformation_event)


@dataclass(frozen=True)
class SolverExecutionEventAuthority:
    proof_requirement_id: str
    solver_invocation_id: str
    observed_status: str
    configured_timeout_ms: Optional[int] = None

    def __post_init__(self) -> None:
        _require_exact_strings(
            self.proof_requirement_id, self.solver_invocation_id, self.observed_status
        )
        if self.configured_timeout_ms is not None and (
            type(self.configured_timeout_ms) is not int or self.configured_timeout_ms <= 0
        ):
            raise TypeError("solver timeout budget must be a positive exact integer")


def outcome_stage_requirement_id(authority: Mapping[str, Any]) -> str:
    """Derive the lifecycle requirement from the exact outcome-stage authority."""

    return "outcome-stage-" + authority_digest({
        "typed_requirement": canonical_value(
            authority["proof_requirement_identity"]
        ),
        "function_identity": canonical_value(authority["function_identity"]),
        "function_snapshot_fingerprint": authority[
            "function_snapshot_fingerprint"
        ],
        "outcome_seed_digest": authority["outcome_seed_digest"],
        "outcome_seed_revision": authority["outcome_seed_revision"],
        "premise_digest": authority["premise_digest"],
        "stage": authority["stage"],
    })[:32]


@dataclass(frozen=True)
class ReceiptBoundSolverExecutionEventAuthority:
    proof_requirement_id: str
    execution_receipt_authority: Mapping[str, Any]
    terminal_candidate: bool

    def __post_init__(self) -> None:
        _require_exact_strings(self.proof_requirement_id)
        if type(self.terminal_candidate) is not bool:
            raise TypeError("solver terminal candidate must be an exact boolean")
        receipt = validate_outcome_execution_receipt_authority(
            self.execution_receipt_authority
        )
        # 記録後に呼び出し側の dict を書き換えても event の内容が変わらないよう、
        # 不変コピーへ置き換える（digest は不変）。
        object.__setattr__(
            self,
            "execution_receipt_authority",
            freeze_authority_value(self.execution_receipt_authority),
        )
        status = receipt["observed_status"]
        if self.terminal_candidate and status != "timeout":
            raise ValueError("only a TIMEOUT receipt may be a terminal candidate")
        expected_requirement_id = outcome_stage_requirement_id(receipt)
        if self.proof_requirement_id != expected_requirement_id:
            raise ValueError("solver event v2/typed requirement join differs")

    @property
    def solver_invocation_id(self) -> str:
        return self.execution_receipt_authority["invocation_identity"]

    @property
    def observed_status(self) -> str:
        return self.execution_receipt_authority["observed_status"].upper()

    @property
    def configured_timeout_ms(self) -> Optional[int]:
        return self.execution_receipt_authority["configured_timeout_ms"]

    @property
    def execution_receipt_digest(self) -> str:
        return self.execution_receipt_authority["receipt_digest"]

    @property
    def query_digest(self) -> str:
        return self.execution_receipt_authority["query_digest"]

    @property
    def elapsed_ms(self) -> int:
        return self.execution_receipt_authority["elapsed_ms"]


@dataclass(frozen=True)
class GenericReceiptBoundSolverExecutionEventAuthority:
    proof_requirement_id: str
    execution_receipt_authority: Mapping[str, Any]
    terminal_candidate: bool

    def __post_init__(self) -> None:
        _require_exact_strings(self.proof_requirement_id)
        if type(self.terminal_candidate) is not bool:
            raise TypeError("generic solver terminal candidate must be exact boolean")
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            decode_persisted_execution_receipt,
        )
        receipt = decode_persisted_execution_receipt(self.execution_receipt_authority)
        object.__setattr__(
            self,
            "execution_receipt_authority",
            freeze_authority_value(receipt.to_authority_dict()),
        )
        if receipt.proof_requirement_id != self.proof_requirement_id:
            raise ValueError("generic solver event requirement differs from receipt")
        if self.terminal_candidate and receipt.observed_status != "timeout":
            raise ValueError("only a generic TIMEOUT receipt may be terminal candidate")

    @property
    def solver_invocation_id(self) -> str:
        return self.execution_receipt_authority["invocation_identity"]

    @property
    def observed_status(self) -> str:
        return self.execution_receipt_authority["observed_status"].upper()

    @property
    def configured_timeout_ms(self) -> Optional[int]:
        return self.execution_receipt_authority["configured_timeout_ms"]

    @property
    def execution_receipt_digest(self) -> str:
        return self.execution_receipt_authority["receipt_digest"]

    @property
    def query_digest(self) -> str:
        return self.execution_receipt_authority["query_digest"]

    @property
    def elapsed_ms(self) -> int:
        return self.execution_receipt_authority["elapsed_ms"]


@dataclass(frozen=True)
class OutcomeProducerAttemptEventAuthority:
    proof_requirement_id: str
    stage: str
    producer_status: str
    producer_attempt_identity: str
    producer_attempt_ordinal: int
    execution_identity_digest: str

    def __post_init__(self) -> None:
        _require_exact_strings(
            self.proof_requirement_id,
            self.stage,
            self.producer_status,
            self.producer_attempt_identity,
            self.execution_identity_digest,
        )
        if type(self.producer_attempt_ordinal) is not int or self.producer_attempt_ordinal <= 0:
            raise TypeError("outcome producer attempt ordinal is invalid")
        allowed_statuses = sealed_outcome_stage_statuses()
        if (
            self.stage not in allowed_statuses
            or self.producer_status not in allowed_statuses[self.stage]
        ):
            raise ValueError("outcome producer attempt stage/status pair is not sealed")


_SEALED_OUTCOME_STAGE_STATUSES: Optional[Mapping[str, frozenset]] = None


def sealed_outcome_stage_statuses() -> Mapping[str, frozenset]:
    """封印済みの outcome stage/status を stage ごとの集合として返す。

    唯一の出所は ``OUTCOME_STAGE_REASON_MATRIX``。ここで表を二重に持つと、行列へ
    status を足したときに ingress 側だけ取り残される（Issue #131 の
    ``case_budget_exceeded`` で実際に起きた）。``domains`` は本 module を import
    するので、循環を避けて呼び出し時に 1 度だけ組み立てる。
    """

    global _SEALED_OUTCOME_STAGE_STATUSES
    if _SEALED_OUTCOME_STAGE_STATUSES is None:
        from scripts.function_tracer_pcode.authority.domains.return_outcome import (
            OUTCOME_STAGE_REASON_MATRIX,
        )

        table: dict[str, set] = {}
        for stage, status in OUTCOME_STAGE_REASON_MATRIX:
            table.setdefault(stage, set()).add(status)
        _SEALED_OUTCOME_STAGE_STATUSES = MappingProxyType({
            stage: frozenset(statuses) for stage, statuses in sorted(table.items())
        })
    return _SEALED_OUTCOME_STAGE_STATUSES


def validate_outcome_execution_receipt_authority(
    authority: Mapping[str, Any],
) -> Mapping[str, Any]:
    """Strict persisted-form validator shared by event ingress and receipt tests."""

    if not isinstance(authority, Mapping):
        raise TypeError("solver event requires recomputable receipt authority")
    receipt = dict(authority)
    required = {
        "stage", "proof_requirement_identity", "premise_digest",
        "function_snapshot_fingerprint", "outcome_seed_digest",
        "outcome_seed_revision", "function_identity",
        "input_domain_contract", "extraction_schema_version",
        "outcome_encoding_version", "query_digest", "model_digest",
        "solver_output_digest", "solver_identity",
        "execution_identity_digest", "producer_attempt_identity",
        "producer_attempt_ordinal", "invocation_identity",
        "invocation_ordinal", "configured_timeout_ms", "elapsed_ms",
        "observed_status", "receipt_digest",
    }
    if set(receipt) != required:
        raise ValueError("solver event receipt authority fields are not exact")
    digest = receipt.pop("receipt_digest")
    if type(digest) is not str or authority_digest(receipt) != digest:
        raise ValueError("solver event receipt authority digest mismatch")
    string_fields = (
        "stage", "premise_digest", "function_snapshot_fingerprint",
        "outcome_seed_digest", "outcome_encoding_version", "query_digest",
        "solver_output_digest", "solver_identity", "execution_identity_digest",
        "producer_attempt_identity", "invocation_identity", "observed_status",
    )
    _require_exact_strings(*(receipt[field] for field in string_fields))
    if receipt["stage"] not in {
        "termination_classification", "cfg_reachability",
        "path_region_completeness", "member_classification",
        "same_kind_consistency", "cross_kind_disjointness",
        "residual_totality", "partition_complete",
    }:
        raise ValueError("solver event receipt stage is not sealed")
    status = receipt["observed_status"]
    if status not in {"sat", "unsat", "unknown", "timeout", "error"}:
        raise ValueError("solver event receipt status is not sealed")
    model_digest = receipt["model_digest"]
    if status == "sat":
        _require_exact_strings(model_digest)
    elif model_digest is not None:
        raise ValueError("solver event receipt model/status authority differs")
    for field, lower_bound in (
        ("outcome_seed_revision", 0),
        ("extraction_schema_version", 1),
        ("producer_attempt_ordinal", 1),
        ("invocation_ordinal", 1),
        ("elapsed_ms", 0),
    ):
        value = receipt[field]
        if type(value) is not int or value < lower_bound:
            raise TypeError(f"solver event receipt {field} authority is invalid")
    timeout_ms = receipt["configured_timeout_ms"]
    if timeout_ms is not None and (
        type(timeout_ms) is not int or timeout_ms <= 0
    ):
        raise TypeError("solver event receipt timeout budget is invalid")
    function_identity = receipt["function_identity"]
    input_domain = receipt["input_domain_contract"]
    if (
        not isinstance(function_identity, (list, tuple))
        or not function_identity
        or not isinstance(input_domain, (list, tuple))
        or not input_domain
    ):
        raise ValueError("solver event receipt function/domain authority is incomplete")
    typed_requirement = receipt["proof_requirement_identity"]
    if not isinstance(typed_requirement, Mapping) or set(typed_requirement) != {
        "schema_version", "proof_kind", "proof_target_key", "proof_contract_key"
    }:
        raise TypeError("solver event typed requirement authority is missing")
    stage = receipt["stage"]
    if (
        type(typed_requirement["schema_version"]) is not int
        or typed_requirement["schema_version"] != 1
        or typed_requirement["proof_kind"] != f"unary_outcome_{stage}"
    ):
        raise ValueError("solver event receipt stage/requirement authority differs")
    expected_target = (
        "function_outcome_seed",
        function_identity,
        receipt["outcome_seed_digest"],
        receipt["outcome_seed_revision"],
    )
    expected_contract = (
        1,
        f"reachable outcome {stage}",
        "unary",
        (
            input_domain,
            receipt["extraction_schema_version"],
            receipt["outcome_encoding_version"],
        ),
        ("function_input_domain",),
    )
    if (
        canonical_value(typed_requirement["proof_target_key"])
        != canonical_value(expected_target)
        or canonical_value(typed_requirement["proof_contract_key"])
        != canonical_value(expected_contract)
    ):
        raise ValueError("solver event typed requirement semantic join differs")
    return {**receipt, "receipt_digest": digest}

@dataclass(frozen=True)
class ProcessExecutionEventAuthority:
    proof_requirement_id: str
    process_invocation_id: str

    def __post_init__(self) -> None:
        _require_exact_strings(self.proof_requirement_id, self.process_invocation_id)


@dataclass(frozen=True)
class ProcessCompletionEventAuthority:
    proof_requirement_id: str
    process_invocation_id: str
    execution_receipt_digest: str

    def __post_init__(self) -> None:
        _require_exact_strings(
            self.proof_requirement_id,
            self.process_invocation_id,
            self.execution_receipt_digest,
        )


@dataclass(frozen=True)
class StageObservationEventAuthority:
    stage_id: str
    observation_artifact_digest: str

    def __post_init__(self) -> None:
        _require_exact_strings(self.stage_id, self.observation_artifact_digest)


@dataclass(frozen=True)
class DecisiveProofEventAuthority:
    proof_artifact_digest: str

    def __post_init__(self) -> None:
        _require_exact_strings(self.proof_artifact_digest)


@dataclass(frozen=True)
class ErrorEventAuthority:
    error_kind: str
    error_artifact_digest: str

    def __post_init__(self) -> None:
        _require_exact_strings(self.error_kind, self.error_artifact_digest)


_EVENT_PAYLOAD_TYPES = MappingProxyType({
    EventType.CAUSE_OBSERVED: CauseObservedEventAuthority,
    EventType.REQUIREMENT_COMPLETED: RequirementCompletedEventAuthority,
    EventType.CAUSE_TRANSFORMED: CauseTransformedEventAuthority,
    EventType.OUTCOME_PRODUCER_ATTEMPT: OutcomeProducerAttemptEventAuthority,
    EventType.SOLVER_UNKNOWN: (SolverExecutionEventAuthority, ReceiptBoundSolverExecutionEventAuthority, GenericReceiptBoundSolverExecutionEventAuthority),
    EventType.SOLVER_TIMEOUT: (SolverExecutionEventAuthority, ReceiptBoundSolverExecutionEventAuthority, GenericReceiptBoundSolverExecutionEventAuthority),
    EventType.SOLVER_ERROR: (SolverExecutionEventAuthority, ReceiptBoundSolverExecutionEventAuthority, GenericReceiptBoundSolverExecutionEventAuthority),
    EventType.PROCESS_COMPLETED: ProcessCompletionEventAuthority,
    EventType.PROCESS_TIMEOUT: ProcessExecutionEventAuthority,
    EventType.CANCELLED: ProcessExecutionEventAuthority,
    EventType.NORMALIZATION_NO_CHANGE: StageObservationEventAuthority,
    EventType.REWRITE_NO_CHANGE: StageObservationEventAuthority,
    EventType.EQ_CLOSURE: DecisiveProofEventAuthority,
    EventType.COUNTEREXAMPLE: DecisiveProofEventAuthority,
    EventType.ERROR: ErrorEventAuthority,
})


def validate_event_authority_payload(event_type: EventType, payload: Any) -> None:
    expected = _EVENT_PAYLOAD_TYPES[EventType(event_type)]
    expected_types = expected if type(expected) is tuple else (expected,)
    if type(payload) not in expected_types:
        expected_label = (
            expected.__name__
            if type(expected) is not tuple
            else "registered authority payload"
        )
        raise TypeError(
            f"{EventType(event_type).value} requires exact {expected_label} authority payload"
        )
    if type(payload) in (
        SolverExecutionEventAuthority,
        ReceiptBoundSolverExecutionEventAuthority,
        GenericReceiptBoundSolverExecutionEventAuthority,
    ):
        expected_status = {
            EventType.SOLVER_UNKNOWN: "UNKNOWN",
            EventType.SOLVER_TIMEOUT: "TIMEOUT",
            EventType.SOLVER_ERROR: "ERROR",
        }[EventType(event_type)]
        if payload.observed_status != expected_status:
            raise ValueError("solver event type and observed status differ")


@dataclass(frozen=True)
class EventHeader:
    stream_id: str
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    sequence_number: int
    predecessor_authority_digest: str
    authority_payload_digest: str
    event_type: EventType
    schema_version: int = SCHEMA_VERSION


@dataclass(frozen=True)
class RecordedEvent:
    header: EventHeader
    authority_payload: Any
    diagnostic_payload: Any
    authority_digest: str


class _VerifiedEventRegistry:
    """記録された event 自身だけで決まる検証の結果を、同じ event object についてプロセス内で 1 回にする。

    event 自身だけで決まる検証は 3 つ: header の `authority_payload_digest` が payload の digest と等しい、
    `authority_digest` が header と payload の digest と等しい、payload が event type の型に合う。どれも
    stream の中の位置（順番・前の event の digest）に依らない。位置の検証（連番・連鎖）は stream ごとに行う。

    stream の検証は、prefix view・封印した stream・replay の内部の stream を作るたびに全 event を
    再ダイジェストしていた。finalize は return の ABI 関係を 1 つ完成させるたびに stream 全体を再生するので、
    費用が「関係の数 × event の数」になっていた（Issue #281 review 5: factln の pair が 600 秒を超えた）。

    記録できるのは header と authority payload が深く不変（`assert_deep_immutable`）な event だけ
    （diagnostic payload は digest に入らないので問わない）。event は弱参照で追跡し、回収されれば記録も消える
    ので id の再利用で誤判定しない（`VALIDATED_ONCE` と同じ規則。event 全体は diagnostic payload の dict の
    ために深く不変ではないので、別の記録にする）。
    """

    def __init__(self) -> None:
        self._refs: Dict[int, weakref.ref] = {}

    def is_verified(self, event: "RecordedEvent") -> bool:
        ref = self._refs.get(id(event))
        return ref is not None and ref() is event

    def mark(self, event: "RecordedEvent") -> None:
        try:
            assert_deep_immutable(event.header)
            assert_deep_immutable(event.authority_payload)
        except TypeError:
            return
        key = id(event)
        try:
            self._refs[key] = weakref.ref(event, lambda _ref, key=key: self._refs.pop(key, None))
        except TypeError:
            return

    def __len__(self) -> int:
        return len(self._refs)


_VERIFIED_EVENTS = _VerifiedEventRegistry()


@dataclass(frozen=True)
class EventStreamEnvelope:
    stream_id: str
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    first_sequence: int
    last_sequence: int
    event_count: int
    authority_chain_digest: str
    sealed: bool
    schema_version: int = SCHEMA_VERSION


@dataclass(frozen=True)
class SealedEventStream:
    envelope: EventStreamEnvelope
    events: Tuple[RecordedEvent, ...]

    def validate(self) -> None:
        if VALIDATED_ONCE.is_validated(self):
            return
        if not self.envelope.sealed or not self.events:
            raise ValueError("event stream is empty or unsealed")
        if type(self.envelope.schema_version) is not int or self.envelope.schema_version != SCHEMA_VERSION:
            raise ValueError("event envelope schema is not exact v2")
        if type(self.envelope.sealed) is not bool or not self.envelope.sealed:
            raise TypeError("event envelope sealed flag must be exact true")
        _require_exact_strings(
            self.envelope.stream_id,
            self.envelope.result_occurrence_id,
            self.envelope.source_snapshot_fingerprint,
            self.envelope.authority_chain_digest,
        )
        for value in (
            self.envelope.first_sequence,
            self.envelope.last_sequence,
            self.envelope.event_count,
        ):
            if type(value) is not int:
                raise TypeError("event envelope sequence/count fields must be exact integers")
        predecessor = "0" * 64
        for expected_sequence, event in enumerate(self.events, 1):
            header = event.header
            if type(header.schema_version) is not int or header.schema_version != SCHEMA_VERSION:
                raise ValueError("event header schema is not exact v2")
            if type(header.sequence_number) is not int:
                raise TypeError("event sequence number must be an exact integer")
            _require_exact_strings(
                header.stream_id,
                header.result_occurrence_id,
                header.source_snapshot_fingerprint,
                header.predecessor_authority_digest,
                header.authority_payload_digest,
                event.authority_digest,
            )
            if header.stream_id != self.envelope.stream_id:
                raise ValueError("mixed stream IDs")
            if header.result_occurrence_id != self.envelope.result_occurrence_id:
                raise ValueError("event result occurrence differs from envelope")
            if header.source_snapshot_fingerprint != self.envelope.source_snapshot_fingerprint:
                raise ValueError("event source snapshot differs from envelope")
            if header.sequence_number != expected_sequence:
                raise ValueError("event sequence is not continuous")
            if header.predecessor_authority_digest != predecessor:
                raise ValueError("event predecessor digest mismatch")
            if not _VERIFIED_EVENTS.is_verified(event):
                if header.authority_payload_digest != authority_digest(event.authority_payload):
                    raise ValueError("event authority payload digest mismatch")
                validate_event_authority_payload(header.event_type, event.authority_payload)
                expected_digest = _event_digest(header, event.authority_payload)
                if event.authority_digest != expected_digest:
                    raise ValueError("event authority digest mismatch")
                _VERIFIED_EVENTS.mark(event)
            predecessor = event.authority_digest
        if self.envelope.first_sequence != 1:
            raise ValueError("event stream must begin at sequence one")
        if self.envelope.last_sequence != len(self.events):
            raise ValueError("event stream last sequence mismatch")
        if self.envelope.event_count != len(self.events):
            raise ValueError("event stream count mismatch")
        if self.envelope.authority_chain_digest != predecessor:
            raise ValueError("event stream chain digest mismatch")
        VALIDATED_ONCE.mark(self)


_PREFIX_STREAM_VIEW_TOKEN = object()


@dataclass(frozen=True)
class EventStreamPrefixView:
    stream_id: str
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    events: Tuple[RecordedEvent, ...]
    prefix_chain_digest: str
    finality: str = "PREFIX"
    _factory_token: object = field(default=None, repr=False, compare=False)

    @property
    def prefix_authority_digest(self) -> str:
        self.validate()
        return authority_digest({
            "finality": "PREFIX",
            "stream_id": self.stream_id,
            "result_occurrence_id": self.result_occurrence_id,
            "source_snapshot_fingerprint": self.source_snapshot_fingerprint,
            "event_count": len(self.events),
            "last_event_authority_digest": self.prefix_chain_digest,
        })

    def __post_init__(self) -> None:
        if self._factory_token is not _PREFIX_STREAM_VIEW_TOKEN:
            raise TypeError("event-stream prefix view must be recorder issued")
        object.__setattr__(self, "events", tuple(self.events))
        self.validate()

    @classmethod
    def from_sealed_stream(
        cls, stream: SealedEventStream,
    ) -> "EventStreamPrefixView":
        if type(stream) is not SealedEventStream:
            raise TypeError("persisted prefix requires exact sealed stream authority")
        stream.validate()
        return cls(
            stream.envelope.stream_id,
            stream.envelope.result_occurrence_id,
            stream.envelope.source_snapshot_fingerprint,
            stream.events,
            stream.envelope.authority_chain_digest,
            _factory_token=_PREFIX_STREAM_VIEW_TOKEN,
        )

    def to_sealed_stream(self) -> SealedEventStream:
        """Materialize an immutable snapshot without sealing the live recorder."""
        self.validate()
        stream = SealedEventStream(
            EventStreamEnvelope(
                self.stream_id,
                self.result_occurrence_id,
                self.source_snapshot_fingerprint,
                1,
                len(self.events),
                len(self.events),
                self.prefix_chain_digest,
                True,
            ),
            self.events,
        )
        stream.validate()
        return stream

    def validate(self) -> None:
        if self.finality != "PREFIX" or not self.events:
            raise ValueError("event-stream prefix finality is invalid")
        _require_exact_strings(
            self.stream_id,
            self.result_occurrence_id,
            self.source_snapshot_fingerprint,
            self.prefix_chain_digest,
        )
        predecessor = "0" * 64
        for expected_sequence, event in enumerate(self.events, 1):
            header = event.header
            if (
                header.stream_id != self.stream_id
                or header.result_occurrence_id != self.result_occurrence_id
                or header.source_snapshot_fingerprint
                != self.source_snapshot_fingerprint
                or header.sequence_number != expected_sequence
                or header.predecessor_authority_digest != predecessor
            ):
                raise ValueError("event-stream prefix chain is invalid")
            if not _VERIFIED_EVENTS.is_verified(event):
                if (
                    header.authority_payload_digest
                    != authority_digest(event.authority_payload)
                    or event.authority_digest
                    != _event_digest(header, event.authority_payload)
                ):
                    raise ValueError("event-stream prefix chain is invalid")
                validate_event_authority_payload(
                    header.event_type, event.authority_payload
                )
                _VERIFIED_EVENTS.mark(event)
            predecessor = event.authority_digest
        if self.prefix_chain_digest != predecessor:
            raise ValueError("event-stream prefix digest mismatch")


class EventRecorder:
    def __init__(
        self, *, stream_id: str, result_occurrence_id: str, source_snapshot_fingerprint: str
    ) -> None:
        if not stream_id or not result_occurrence_id or not source_snapshot_fingerprint:
            raise ValueError("event recorder identity is incomplete")
        self._stream_id = stream_id
        self._result_occurrence_id = result_occurrence_id
        self._source_snapshot_fingerprint = source_snapshot_fingerprint
        self._events: list[RecordedEvent] = []
        self._sealed = False

    @classmethod
    def continue_from_prefix(
        cls, prefix: EventStreamPrefixView,
    ) -> "EventRecorder":
        """Continue one verified logical stream without rewriting its source file."""

        if type(prefix) is not EventStreamPrefixView:
            raise TypeError("event continuation requires exact PREFIX authority")
        prefix.validate()
        recorder = cls(
            stream_id=prefix.stream_id,
            result_occurrence_id=prefix.result_occurrence_id,
            source_snapshot_fingerprint=prefix.source_snapshot_fingerprint,
        )
        recorder._events = list(prefix.events)
        return recorder

    @property
    def event_count(self) -> int:
        return len(self._events)

    @property
    def recorded_events(self) -> Tuple[RecordedEvent, ...]:
        """Read-only view of the events recorded so far (diagnostics only)."""
        return tuple(self._events)

    def append(self, intent: EventIntent) -> RecordedEvent:
        return self.append_many((intent,))[0]

    def append_many(
        self,
        intents: Iterable[EventIntent],
        commit_callback: Optional[Callable[[], None]] = None,
    ) -> Tuple[RecordedEvent, ...]:
        """Validate, commit producer state, and append one atomic transaction."""

        if self._sealed:
            raise ValueError("sealed event recorder is immutable")
        batch = tuple(intents)
        if not batch:
            if commit_callback is not None:
                if not callable(commit_callback):
                    raise TypeError(
                        "event transaction commit callback is not callable"
                    )
                commit_callback()
            return ()
        staged: list[RecordedEvent] = []
        predecessor = self._events[-1].authority_digest if self._events else "0" * 64
        for offset, intent in enumerate(batch, 1):
            if type(intent) is not EventIntent:
                raise TypeError("event transaction requires exact EventIntent rows")
            validate_event_authority_payload(
                intent.event_type, intent.authority_payload
            )
            # 生の dict / list / set を含む payload は不変コピーへ置き換える
            # （digest は不変）。dataclass payload は同一オブジェクトのまま
            # （各クラスの __post_init__ がコンテナ型フィールドを凍結する）。
            # ここでは深い不変性を「要求」しない: 記録時の例外は producer 側で
            # 握り潰されてイベントが黙って失われるため、封印後の validate-once
            # キャッシュ側（VALIDATED_ONCE.mark）が深く不変な場合にだけ記録する。
            payload = freeze_authority_value(intent.authority_payload)
            header = EventHeader(
                stream_id=self._stream_id,
                result_occurrence_id=self._result_occurrence_id,
                source_snapshot_fingerprint=self._source_snapshot_fingerprint,
                sequence_number=len(self._events) + offset,
                predecessor_authority_digest=predecessor,
                authority_payload_digest=authority_digest(payload),
                event_type=intent.event_type,
            )
            event = RecordedEvent(
                header=header,
                authority_payload=payload,
                diagnostic_payload=canonical_value(intent.diagnostic_payload),
                authority_digest=_event_digest(header, payload),
            )
            staged.append(event)
            predecessor = event.authority_digest
        # The producer callback runs only after every event has been staged and
        # validated, but before the stream becomes observable.  A callback
        # failure therefore leaves both the event stream and producer ledger at
        # their pre-transaction state (the caller owns ledger rollback).
        if commit_callback is not None:
            if not callable(commit_callback):
                raise TypeError("event transaction commit callback is not callable")
            commit_callback()
        self._events.extend(staged)
        return tuple(staged)

    def seal(self) -> SealedEventStream:
        if self._sealed:
            raise ValueError("event recorder is already sealed")
        if not self._events:
            raise ValueError("cannot seal an empty event stream")
        self._sealed = True
        envelope = EventStreamEnvelope(
            stream_id=self._stream_id,
            result_occurrence_id=self._result_occurrence_id,
            source_snapshot_fingerprint=self._source_snapshot_fingerprint,
            first_sequence=1,
            last_sequence=len(self._events),
            event_count=len(self._events),
            authority_chain_digest=self._events[-1].authority_digest,
            sealed=True,
        )
        stream = SealedEventStream(envelope, tuple(self._events))
        stream.validate()
        return stream

    def prefix_view(self) -> EventStreamPrefixView:
        """Issue a PREFIX-only immutable view without closing append authority."""

        if self._sealed:
            raise ValueError("sealed event recorder has no open prefix view")
        if not self._events:
            raise ValueError("cannot issue an empty event-stream prefix view")
        return EventStreamPrefixView(
            self._stream_id,
            self._result_occurrence_id,
            self._source_snapshot_fingerprint,
            tuple(self._events),
            self._events[-1].authority_digest,
            _factory_token=_PREFIX_STREAM_VIEW_TOKEN,
        )


def _event_digest(header: EventHeader, authority_payload: Any) -> str:
    return authority_digest(
        {
            "schema_version": header.schema_version,
            "stream_id": header.stream_id,
            "result_occurrence_id": header.result_occurrence_id,
            "source_snapshot_fingerprint": header.source_snapshot_fingerprint,
            "sequence_number": header.sequence_number,
            "predecessor_authority_digest": header.predecessor_authority_digest,
            "authority_payload_digest": header.authority_payload_digest,
            "event_type": header.event_type.value,
            "authority_payload": authority_payload,
        }
    )
