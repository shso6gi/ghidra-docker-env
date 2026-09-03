"""Domain-independent execution, replay, and terminal-timeout authority."""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import hmac
import secrets
import re
import threading
from types import MappingProxyType
from typing import Any, Iterable, Mapping, Optional, Sequence

from .contracts import (
    QOpenBaseRow,
    VerifiedLifecyclePrefixProjection,
    authority_digest,
    canonical_value,
)
from ...smt.interface import SolverResult
from ...smt.parallel import ParallelResult, ParallelSolverRunner


_APPROVED_PRODUCTION_SOLVER_CLASSES = tuple(ParallelSolverRunner.DEFAULT_SOLVERS)
_PINNED_PARALLEL_RUN_IMPL = ParallelSolverRunner.run_parallel


_EXECUTION_RECEIPT_TOKEN = object()
_EXECUTION_RECEIPT_CODEC_TOKEN = object()
_REPLAY_RECEIPT_TOKEN = object()
_REPLAY_RECEIPT_CODEC_TOKEN = object()
_REFUTATION_TOKEN = object()
_REFUTATION_CODEC_TOKEN = object()
_SELECTION_FACTORY_TOKEN = object()
_SELECTION_CODEC_TOKEN = object()
_PINNED_VERIFIER_TOKEN = object()
_RUNNER_ISSUER_TOKEN = object()
_RESULT_ENTRY_OCCURRENCE_CODEC_TOKEN = object()
_SOLVER_LEDGER_TOKEN = object()
_RECEIPTLESS_ATTEMPT_TOKEN = object()
_KEYRING_LOCK = threading.RLock()
_EXECUTION_AUTHORITY_KEYS: dict[str, bytes] = {
    "process-ephemeral-v1": secrets.token_bytes(32)
}
_ACTIVE_EXECUTION_AUTHORITY_KEY_ID = "process-ephemeral-v1"
_ACTIVE_EXECUTION_AUTHORITY_DEPLOYMENT_POLICY: Optional[
    "ExecutionAuthorityDeploymentPolicy"
] = None


def install_execution_authority_signing_key(
    key_id: str, secret: bytes, *, activate: bool = False
) -> None:
    """Install/rotate a deployment-protected key before issuing/decoding receipts."""

    global _ACTIVE_EXECUTION_AUTHORITY_KEY_ID
    _exact_string(key_id, "execution signing key ID")
    if type(secret) is not bytes or len(secret) < 32:
        raise TypeError("execution signing key must contain at least 256 bits")
    with _KEYRING_LOCK:
        if (
            activate
            and _ACTIVE_EXECUTION_AUTHORITY_DEPLOYMENT_POLICY is not None
            and key_id
            != _ACTIVE_EXECUTION_AUTHORITY_DEPLOYMENT_POLICY.active_key_id
        ):
            raise ValueError("active deployment key changes require policy activation")
        existing = _EXECUTION_AUTHORITY_KEYS.get(key_id)
        if existing is not None and not hmac.compare_digest(existing, secret):
            raise ValueError("execution signing key ID cannot be rebound")
        _EXECUTION_AUTHORITY_KEYS[key_id] = secret
        if activate:
            _ACTIVE_EXECUTION_AUTHORITY_KEY_ID = key_id


def _seal(value: Any, key_id: str) -> str:
    with _KEYRING_LOCK:
        policy = _ACTIVE_EXECUTION_AUTHORITY_DEPLOYMENT_POLICY
        if (
            policy is not None
            and key_id != "process-ephemeral-v1"
            and key_id not in policy.verification_key_ids
        ):
            raise ValueError("execution receipt signing key is outside retention policy")
        try:
            secret = _EXECUTION_AUTHORITY_KEYS[key_id]
        except KeyError as exc:
            raise ValueError("execution receipt signing key is unavailable") from exc
    return hmac.new(
        secret,
        repr(canonical_value(value)).encode("utf-8"),
        hashlib.sha256,
    ).hexdigest()


def _exact_string(value: Any, label: str) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{label} must be an exact non-empty string")
    return value


@dataclass(frozen=True)
class ExecutionAuthorityDeploymentPolicy:
    """Operator-owned startup/rotation contract; secret material is never bound."""

    policy_id: str
    policy_version: int
    key_owner_id: str
    key_source_id: str
    active_key_id: str
    retained_verification_key_ids: tuple[str, ...]
    retention_window_seconds: int
    revocation_policy_id: str
    normalized_policy_digest: str = field(init=False)

    def __post_init__(self) -> None:
        for label, value in (
            ("deployment policy", self.policy_id),
            ("key owner", self.key_owner_id),
            ("key source", self.key_source_id),
            ("active key", self.active_key_id),
            ("revocation policy", self.revocation_policy_id),
        ):
            _exact_string(value, label)
        if type(self.policy_version) is not int or self.policy_version < 1:
            raise TypeError("deployment policy version must be positive")
        if (
            type(self.retention_window_seconds) is not int
            or self.retention_window_seconds < 1
        ):
            raise TypeError("deployment retention window must be positive")
        retained = tuple(sorted(self.retained_verification_key_ids))
        if (
            any(type(item) is not str or not item for item in retained)
            or len(retained) != len(set(retained))
            or self.active_key_id in retained
        ):
            raise ValueError("deployment retained-key set is invalid")
        if self.active_key_id == "process-ephemeral-v1":
            raise ValueError("deployment policy cannot activate the ephemeral process key")
        object.__setattr__(self, "retained_verification_key_ids", retained)
        object.__setattr__(self, "normalized_policy_digest", authority_digest({
            "policy_id": self.policy_id,
            "policy_version": self.policy_version,
            "key_owner_id": self.key_owner_id,
            "key_source_id": self.key_source_id,
            "active_key_id": self.active_key_id,
            "retained_verification_key_ids": retained,
            "retention_window_seconds": self.retention_window_seconds,
            "revocation_policy_id": self.revocation_policy_id,
            "startup_mode": "fail_closed",
        }))

    @property
    def verification_key_ids(self) -> frozenset[str]:
        return frozenset((self.active_key_id, *self.retained_verification_key_ids))


@dataclass(frozen=True)
class ExecutionAuthorityStartupReceipt:
    policy_id: str
    policy_version: int
    normalized_policy_digest: str
    active_key_id: str
    retained_verification_key_ids: tuple[str, ...]
    startup_mode: str
    receipt_digest: str

    def validate(self) -> None:
        payload = {
            "policy_id": self.policy_id,
            "policy_version": self.policy_version,
            "normalized_policy_digest": self.normalized_policy_digest,
            "active_key_id": self.active_key_id,
            "retained_verification_key_ids": self.retained_verification_key_ids,
            "startup_mode": self.startup_mode,
        }
        if (
            type(self.policy_version) is not int
            or self.policy_version < 1
            or self.startup_mode != "fail_closed"
            or self.active_key_id == "process-ephemeral-v1"
            or self.receipt_digest != authority_digest(payload)
        ):
            raise ValueError("execution authority startup receipt is invalid")

    def validate_against(self, policy: ExecutionAuthorityDeploymentPolicy) -> None:
        self.validate()
        payload = {
            "policy_id": policy.policy_id,
            "policy_version": policy.policy_version,
            "normalized_policy_digest": policy.normalized_policy_digest,
            "active_key_id": policy.active_key_id,
            "retained_verification_key_ids": policy.retained_verification_key_ids,
            "startup_mode": "fail_closed",
        }
        if (
            self.policy_id != payload["policy_id"]
            or self.policy_version != payload["policy_version"]
            or self.normalized_policy_digest != payload["normalized_policy_digest"]
            or self.active_key_id != payload["active_key_id"]
            or self.retained_verification_key_ids
            != payload["retained_verification_key_ids"]
            or self.startup_mode != "fail_closed"
            or self.receipt_digest != authority_digest(payload)
        ):
            raise ValueError("execution authority startup receipt differs from policy")


@dataclass(frozen=True, init=False)
class SolverResultEntryOccurrenceReceipt:
    execution_payload_digest: str
    startup_receipt_digests: tuple[str, ...]
    occurrence_nonce: str
    result_entry_occurrence_id: str
    receipt_digest: str
    _factory_token: object = field(default=None, init=False, repr=False, compare=False)

    def __init__(self, *, _factory_token: object = None, **payload: Any) -> None:
        _initialize_factory_value(
            self,
            payload,
            expected_token=(
                _RUNNER_ISSUER_TOKEN,
                _RESULT_ENTRY_OCCURRENCE_CODEC_TOKEN,
            ),
            supplied_token=_factory_token,
        )

    def validate(self) -> None:
        payload = {
            "execution_payload_digest": self.execution_payload_digest,
            "startup_receipt_digests": self.startup_receipt_digests,
            "occurrence_nonce": self.occurrence_nonce,
            "result_entry_occurrence_id": self.result_entry_occurrence_id,
        }
        if (
            self._factory_token not in {
                _RUNNER_ISSUER_TOKEN,
                _RESULT_ENTRY_OCCURRENCE_CODEC_TOKEN,
            }
            or not self.occurrence_nonce
            or self.startup_receipt_digests
            != tuple(sorted(self.startup_receipt_digests))
            or type(self.result_entry_occurrence_id) is not str
            or not self.result_entry_occurrence_id
            or self.receipt_digest != authority_digest(payload)
        ):
            raise ValueError("solver result-entry occurrence receipt is invalid")

    def to_authority_dict(self) -> Mapping[str, Any]:
        self.validate()
        return {
            name: getattr(self, name) for name in self.__dataclass_fields__
            if name != "_factory_token"
        }

    @classmethod
    def from_persisted(
        cls, payload: Mapping[str, Any]
    ) -> "SolverResultEntryOccurrenceReceipt":
        values = dict(payload)
        values["startup_receipt_digests"] = tuple(
            values["startup_receipt_digests"]
        )
        receipt = cls(
            **values,
            _factory_token=_RESULT_ENTRY_OCCURRENCE_CODEC_TOKEN,
        )
        receipt.validate()
        return receipt


def activate_execution_authority_deployment(
    policy: ExecutionAuthorityDeploymentPolicy,
) -> ExecutionAuthorityStartupReceipt:
    """Atomically validate all verification keys and activate the startup policy."""

    global _ACTIVE_EXECUTION_AUTHORITY_KEY_ID
    global _ACTIVE_EXECUTION_AUTHORITY_DEPLOYMENT_POLICY
    if type(policy) is not ExecutionAuthorityDeploymentPolicy:
        raise TypeError("execution authority deployment requires an exact policy")
    with _KEYRING_LOCK:
        missing = tuple(sorted(
            key_id for key_id in policy.verification_key_ids
            if key_id not in _EXECUTION_AUTHORITY_KEYS
        ))
        if missing:
            raise ValueError("deployment policy references unavailable signing keys")
        if any(len(_EXECUTION_AUTHORITY_KEYS[key_id]) < 32 for key_id in policy.verification_key_ids):
            raise ValueError("deployment policy references a weak signing key")
        _ACTIVE_EXECUTION_AUTHORITY_DEPLOYMENT_POLICY = policy
        _ACTIVE_EXECUTION_AUTHORITY_KEY_ID = policy.active_key_id
    payload = {
        "policy_id": policy.policy_id,
        "policy_version": policy.policy_version,
        "normalized_policy_digest": policy.normalized_policy_digest,
        "active_key_id": policy.active_key_id,
        "retained_verification_key_ids": policy.retained_verification_key_ids,
        "startup_mode": "fail_closed",
    }
    receipt = ExecutionAuthorityStartupReceipt(
        **payload, receipt_digest=authority_digest(payload)
    )
    receipt.validate_against(policy)
    return receipt


def validate_execution_authority_deployment() -> ExecutionAuthorityStartupReceipt:
    with _KEYRING_LOCK:
        policy = _ACTIVE_EXECUTION_AUTHORITY_DEPLOYMENT_POLICY
        active_key_id = _ACTIVE_EXECUTION_AUTHORITY_KEY_ID
    if policy is None or active_key_id != policy.active_key_id:
        raise ValueError("production execution authority startup is not healthy")
    return activate_execution_authority_deployment(policy)


def activate_process_worker_execution_authority_deployment(
    *, key_id: str, key: bytes, key_source_id: str,
) -> ExecutionAuthorityStartupReceipt:
    """Install the EqBench worker key under the shared process deployment policy."""

    _exact_string(key_source_id, "process worker execution key source")
    install_execution_authority_signing_key(key_id, key)
    return activate_execution_authority_deployment(
        ExecutionAuthorityDeploymentPolicy(
            "phase8-process-worker-execution-authority",
            1,
            "eqbench-process-supervisor",
            key_source_id,
            key_id,
            (),
            86400,
            "phase8-process-worker-revocation",
        )
    )


def _initialize_factory_value(
    instance: Any,
    payload: Mapping[str, Any],
    *,
    expected_token: object,
    supplied_token: object,
) -> None:
    expected_fields = {
        name for name, definition in instance.__dataclass_fields__.items()
        if name != "_factory_token" and definition.init
    }
    allowed_tokens = expected_token if isinstance(expected_token, tuple) else (expected_token,)
    if not any(supplied_token is item for item in allowed_tokens):
        raise TypeError(f"{type(instance).__name__} must be factory/codec issued")
    if set(payload) != expected_fields:
        raise TypeError(f"{type(instance).__name__} fields are not exact")
    for name, value in payload.items():
        object.__setattr__(instance, name, value)
    object.__setattr__(instance, "_factory_token", supplied_token)


@dataclass(frozen=True)
class ProducerStageContract:
    domain_contract_id: str
    producer_contract_id: str
    producer_version: str
    proof_stage: str
    execution_issuer_id: str
    allowed_statuses: frozenset[str]
    terminal_eligible_statuses: frozenset[str]
    terminal_priority: int

    def __post_init__(self) -> None:
        for label, value in (
            ("domain contract", self.domain_contract_id),
            ("producer contract", self.producer_contract_id),
            ("producer version", self.producer_version),
            ("proof stage", self.proof_stage),
            ("execution issuer", self.execution_issuer_id),
        ):
            _exact_string(value, label)
        object.__setattr__(self, "allowed_statuses", frozenset(self.allowed_statuses))
        object.__setattr__(
            self, "terminal_eligible_statuses", frozenset(self.terminal_eligible_statuses)
        )
        if not self.allowed_statuses or any(
            type(value) is not str or not value for value in self.allowed_statuses
        ):
            raise TypeError("producer stage statuses must be exact strings")
        if not self.terminal_eligible_statuses.issubset(self.allowed_statuses):
            raise ValueError("terminal-eligible statuses differ from allowed statuses")
        if type(self.terminal_priority) is not int or self.terminal_priority < 0:
            raise TypeError("terminal priority must be an exact nonnegative integer")

    @property
    def key(self) -> tuple[str, str, str, str]:
        return (
            self.domain_contract_id,
            self.producer_contract_id,
            self.producer_version,
            self.proof_stage,
        )


@dataclass(frozen=True)
class ProducerStageRegistry:
    registry_version: int
    contracts: tuple[ProducerStageContract, ...]
    normalized_registry_digest: str = field(init=False)
    _by_key: Mapping[tuple[str, str, str, str], ProducerStageContract] = field(
        init=False, repr=False
    )

    def __post_init__(self) -> None:
        if type(self.registry_version) is not int or self.registry_version < 1:
            raise TypeError("producer registry version must be positive")
        ordered = tuple(sorted(self.contracts, key=lambda item: item.key))
        if not ordered or any(type(item) is not ProducerStageContract for item in ordered):
            raise TypeError("producer registry requires exact stage contracts")
        if len({item.key for item in ordered}) != len(ordered):
            raise ValueError("duplicate producer stage contract")
        priorities = tuple(item.terminal_priority for item in ordered)
        if len(priorities) != len(set(priorities)):
            raise ValueError("terminal timeout priority must be a total order")
        object.__setattr__(self, "contracts", ordered)
        object.__setattr__(self, "_by_key", MappingProxyType({item.key: item for item in ordered}))
        object.__setattr__(self, "normalized_registry_digest", authority_digest({
            "registry_version": self.registry_version,
            "contracts": tuple(
                (
                    item.key,
                    item.execution_issuer_id,
                    tuple(sorted(item.allowed_statuses)),
                    tuple(sorted(item.terminal_eligible_statuses)),
                    item.terminal_priority,
                )
                for item in ordered
            ),
        }))

    def get(self, *key: str) -> ProducerStageContract:
        if len(key) != 4:
            raise TypeError("producer stage lookup requires the full registry key")
        try:
            return self._by_key[tuple(key)]
        except KeyError as exc:
            raise KeyError("unregistered producer proof stage") from exc


@dataclass(frozen=True)
class LiveRequirementAssignmentReceipt:
    result_occurrence_id: str
    lifecycle_prefix_projection_digest: str
    q_open_base_digest: str
    occurrence_id: str
    cause_id: str
    proof_requirement_id: str
    proof_kind: str
    semantic_target_digest: str
    obligation_id: str
    observation_contract_id: str
    proof_stage: str
    assignment_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def validate_integrity(self) -> None:
        if self._factory_token is not _SOLVER_LEDGER_TOKEN:
            raise TypeError("requirement assignment must be authority issued")
        payload = {
            name: getattr(self, name) for name in self.__dataclass_fields__
            if name not in {"assignment_digest", "_factory_token"}
        }
        if self.assignment_digest != authority_digest(payload):
            raise ValueError("requirement assignment digest mismatch")

    def validate_against(self, projection: VerifiedLifecyclePrefixProjection) -> None:
        self.validate_integrity()
        if type(projection) is not VerifiedLifecyclePrefixProjection:
            raise TypeError("requirement assignment requires PREFIX lifecycle authority")
        projection.validate()
        row = QOpenBaseRow(
            self.result_occurrence_id, self.occurrence_id, self.cause_id,
            self.proof_requirement_id, self.proof_kind,
            self.semantic_target_digest,
        )
        if (
            self._factory_token is not _SOLVER_LEDGER_TOKEN
            or self.result_occurrence_id != projection.result_occurrence_id
            or self.lifecycle_prefix_projection_digest
            != projection.prefix_projection_digest
            or self.q_open_base_digest != projection.q_open_base_digest
            or row not in projection.q_open_base
        ):
            raise ValueError("requirement assignment is not in current Q_open authority")

    def to_authority_dict(self) -> Mapping[str, Any]:
        self.validate_integrity()
        return {
            name: getattr(self, name) for name in self.__dataclass_fields__
            if name != "_factory_token"
        }


def issue_call_effect_requirement_assignment(
    *, projection: VerifiedLifecyclePrefixProjection, q_open_row: QOpenBaseRow,
    query_authority: Any,
) -> LiveRequirementAssignmentReceipt:
    if type(projection) is not VerifiedLifecyclePrefixProjection:
        raise TypeError("requirement assignment requires PREFIX lifecycle authority")
    projection.validate()
    if q_open_row not in projection.q_open_base:
        raise ValueError("requirement assignment row is not live in Q_open")
    stage_to_kind = {
        "guard_relation": "call_guard_relation",
        "argument_relation": "call_argument_relation",
        "return_relation": "call_return_relation",
        "memory_relation": "memory_final_state_correspondence",
        "caller_memory_relation": "memory_final_state_correspondence",
    }
    if (
        stage_to_kind.get(query_authority.stage) != q_open_row.proof_kind
        or q_open_row.semantic_target_digest != authority_digest({
            "semantic_target": canonical_value((
                "call_effect_solver_stage",
                query_authority.obligation_id,
                query_authority.observation_contract_id,
                query_authority.stage,
            ))
        })
    ):
        raise ValueError("requirement assignment semantic target does not join query stage")
    payload = {
        "result_occurrence_id": projection.result_occurrence_id,
        "lifecycle_prefix_projection_digest": projection.prefix_projection_digest,
        "q_open_base_digest": projection.q_open_base_digest,
        "occurrence_id": q_open_row.occurrence_id,
        "cause_id": q_open_row.cause_id,
        "proof_requirement_id": q_open_row.proof_requirement_id,
        "proof_kind": q_open_row.proof_kind,
        "semantic_target_digest": q_open_row.semantic_target_digest,
        "obligation_id": query_authority.obligation_id,
        "observation_contract_id": query_authority.observation_contract_id,
        "proof_stage": query_authority.stage,
    }
    return LiveRequirementAssignmentReceipt(
        **payload,
        assignment_digest=authority_digest(payload),
        _factory_token=_SOLVER_LEDGER_TOKEN,
    )


def issue_loop_requirement_assignment(
    *, projection: VerifiedLifecyclePrefixProjection, q_open_row: QOpenBaseRow,
    query_authority: Any,
) -> LiveRequirementAssignmentReceipt:
    """Bind one exact slice4 typed query to its current live requirement."""

    from .loop_recurrence import LoopSolverQueryAuthority

    if type(projection) is not VerifiedLifecyclePrefixProjection:
        raise TypeError("loop requirement assignment requires PREFIX lifecycle authority")
    projection.validate()
    if q_open_row not in projection.q_open_base:
        raise ValueError("loop requirement assignment row is not live in Q_open")
    if type(query_authority) is not LoopSolverQueryAuthority:
        raise TypeError("loop requirement assignment requires exact query authority")
    query_authority.validate()
    if (
        q_open_row.proof_kind != query_authority.proof_kind
        or q_open_row.semantic_target_digest
        != query_authority.semantic_target_digest
    ):
        raise ValueError("loop requirement assignment semantic target differs from query")
    payload = {
        "result_occurrence_id": projection.result_occurrence_id,
        "lifecycle_prefix_projection_digest": projection.prefix_projection_digest,
        "q_open_base_digest": projection.q_open_base_digest,
        "occurrence_id": q_open_row.occurrence_id,
        "cause_id": q_open_row.cause_id,
        "proof_requirement_id": q_open_row.proof_requirement_id,
        "proof_kind": q_open_row.proof_kind,
        "semantic_target_digest": q_open_row.semantic_target_digest,
        "obligation_id": query_authority.obligation_id,
        "observation_contract_id": query_authority.observation_contract_id,
        "proof_stage": query_authority.stage,
    }
    return LiveRequirementAssignmentReceipt(
        **payload,
        assignment_digest=authority_digest(payload),
        _factory_token=_SOLVER_LEDGER_TOKEN,
    )


def issue_abi_width_readonly_requirement_assignment(
    *, projection: VerifiedLifecyclePrefixProjection, q_open_row: QOpenBaseRow,
    query_authority: Any,
) -> LiveRequirementAssignmentReceipt:
    """Bind one exact slice-5 semantic query to its current live Q."""

    from .abi_width_readonly import AbiWidthReadonlySolverQueryAuthority

    if type(projection) is not VerifiedLifecyclePrefixProjection:
        raise TypeError("ABI/width assignment requires PREFIX lifecycle authority")
    projection.validate()
    if q_open_row not in projection.q_open_base:
        raise ValueError("ABI/width assignment row is not live in Q_open")
    if type(query_authority) is not AbiWidthReadonlySolverQueryAuthority:
        raise TypeError("ABI/width assignment requires exact query authority")
    query_authority.validate()
    if (
        q_open_row.proof_kind != query_authority.proof_kind
        or q_open_row.semantic_target_digest
        != query_authority.semantic_target_digest
    ):
        raise ValueError("ABI/width assignment semantic target differs from query")
    payload = {
        "result_occurrence_id": projection.result_occurrence_id,
        "lifecycle_prefix_projection_digest": projection.prefix_projection_digest,
        "q_open_base_digest": projection.q_open_base_digest,
        "occurrence_id": q_open_row.occurrence_id,
        "cause_id": q_open_row.cause_id,
        "proof_requirement_id": q_open_row.proof_requirement_id,
        "proof_kind": q_open_row.proof_kind,
        "semantic_target_digest": q_open_row.semantic_target_digest,
        "obligation_id": query_authority.obligation_id,
        "observation_contract_id": query_authority.observation_contract_id,
        "proof_stage": query_authority.proof_stage,
    }
    return LiveRequirementAssignmentReceipt(
        **payload,
        assignment_digest=authority_digest(payload),
        _factory_token=_SOLVER_LEDGER_TOKEN,
    )


_EXECUTION_REFUSAL_TOKEN = object()


@dataclass(frozen=True, init=False)
class CallEffectExecutionRefusalReceipt:
    result_occurrence_id: str
    lifecycle_prefix_projection_digest: str
    obligation_id: str
    proof_stage: str
    candidate_requirement_ids: tuple[str, ...]
    refusal_kind: str
    refusal_receipt_digest: str
    _factory_token: object = field(default=None, init=False, repr=False, compare=False)

    def __init__(self, *, _factory_token: object = None, **payload: Any) -> None:
        _initialize_factory_value(
            self,
            payload,
            expected_token=_EXECUTION_REFUSAL_TOKEN,
            supplied_token=_factory_token,
        )

    @classmethod
    def ambiguous_q_open(
        cls,
        *,
        projection: VerifiedLifecyclePrefixProjection,
        query_authority: Any,
        candidates: Sequence[QOpenBaseRow],
    ) -> "CallEffectExecutionRefusalReceipt":
        if type(projection) is not VerifiedLifecyclePrefixProjection:
            raise TypeError("execution refusal requires PREFIX lifecycle authority")
        projection.validate()
        rows = tuple(candidates)
        if len(rows) < 2 or any(row not in projection.q_open_base for row in rows):
            raise ValueError("execution refusal lacks ambiguous live Q_open rows")
        requirement_ids = tuple(sorted(row.proof_requirement_id for row in rows))
        payload = {
            "result_occurrence_id": projection.result_occurrence_id,
            "lifecycle_prefix_projection_digest": projection.prefix_projection_digest,
            "obligation_id": query_authority.obligation_id,
            "proof_stage": query_authority.stage,
            "candidate_requirement_ids": requirement_ids,
            "refusal_kind": "ambiguous_live_q_open_assignment",
        }
        return cls(
            **payload,
            refusal_receipt_digest=authority_digest(payload),
            _factory_token=_EXECUTION_REFUSAL_TOKEN,
        )

    def validate(self) -> None:
        payload = {
            "result_occurrence_id": self.result_occurrence_id,
            "lifecycle_prefix_projection_digest": self.lifecycle_prefix_projection_digest,
            "obligation_id": self.obligation_id,
            "proof_stage": self.proof_stage,
            "candidate_requirement_ids": self.candidate_requirement_ids,
            "refusal_kind": self.refusal_kind,
        }
        if (
            self._factory_token is not _EXECUTION_REFUSAL_TOKEN
            or self.refusal_kind != "ambiguous_live_q_open_assignment"
            or len(self.candidate_requirement_ids) < 2
            or self.candidate_requirement_ids
            != tuple(sorted(self.candidate_requirement_ids))
            or self.refusal_receipt_digest != authority_digest(payload)
        ):
            raise ValueError("call/effect execution refusal receipt is invalid")

    def to_authority_dict(self) -> Mapping[str, Any]:
        self.validate()
        return {
            name: getattr(self, name) for name in self.__dataclass_fields__
            if name != "_factory_token"
        }


@dataclass(frozen=True)
class ProducerAttemptMembership:
    domain_contract_id: str
    producer_contract_id: str
    producer_version: str
    proof_stage: str
    proof_requirement_id: str
    obligation_id: str
    observation_contract_id: str
    producer_status: str
    attempt_group_identity: str
    attempt_ordinal: int
    execution_identity_digest: str
    requirement_assignment: Optional[LiveRequirementAssignmentReceipt] = None

    @property
    def registry_key(self) -> tuple[str, str, str, str]:
        return (
            self.domain_contract_id,
            self.producer_contract_id,
            self.producer_version,
            self.proof_stage,
        )

    def validate_against(self, registry: ProducerStageRegistry) -> None:
        contract = registry.get(*self.registry_key)
        if (
            contract.execution_issuer_id == "parallel-solver-runner-v1"
            and type(self.requirement_assignment) is not LiveRequirementAssignmentReceipt
        ):
            raise ValueError("production membership lacks sealed Q_open assignment")
        if self.requirement_assignment is not None:
            self.requirement_assignment.validate_integrity()
        if self.producer_status not in contract.allowed_statuses:
            raise ValueError("producer attempt status is not sealed for the stage")
        for label, value in (
            ("proof requirement", self.proof_requirement_id),
            ("obligation", self.obligation_id),
            ("observation contract", self.observation_contract_id),
            ("attempt group", self.attempt_group_identity),
            ("execution identity", self.execution_identity_digest),
        ):
            _exact_string(value, label)
        if type(self.attempt_ordinal) is not int or self.attempt_ordinal < 1:
            raise TypeError("attempt ordinal must be a positive exact integer")


@dataclass(frozen=True, init=False)
class GenericSolverExecutionReceipt:
    result_occurrence_id: str
    registry_version: int
    normalized_registry_digest: str
    registry_key: tuple[str, str, str, str]
    proof_requirement_id: str
    obligation_id: str
    observation_contract_id: str
    attempt_group_identity: str
    attempt_ordinal: int
    execution_identity_digest: str
    invocation_identity: str
    invocation_ordinal: int
    normalized_query: str
    query_digest: str
    query_authority_digest: str
    configured_timeout_ms: Optional[int]
    elapsed_ms: int
    observed_status: str
    solver_identity: str
    solver_output_authority: Mapping[str, Any]
    solver_output_digest: str
    model_authority: Optional[Mapping[str, Any]]
    model_digest: Optional[str]
    runner_issuer_id: str
    signing_key_id: str
    runner_result_seal: str
    receipt_digest: str
    _factory_token: object = field(default=None, init=False, repr=False, compare=False)

    def __init__(self, *, _factory_token: object = None, **payload: Any) -> None:
        _initialize_factory_value(
            self,
            payload,
            expected_token=(_EXECUTION_RECEIPT_TOKEN, _EXECUTION_RECEIPT_CODEC_TOKEN),
            supplied_token=_factory_token,
        )

    def __post_init__(self) -> None:
        if self._factory_token is not _EXECUTION_RECEIPT_TOKEN:
            raise TypeError("generic execution receipt must be factory/codec issued")

    @classmethod
    def _issue_from_runner_result(
        cls,
        *,
        registry: ProducerStageRegistry,
        result_occurrence_id: str,
        membership: ProducerAttemptMembership,
        invocation_identity: str,
        invocation_ordinal: int,
        query: str,
        configured_timeout_ms: Optional[int],
        solver_result: SolverResult,
        runner_issuer_id: str,
        query_authority_digest: str,
        _issuer_token: object = None,
    ) -> "GenericSolverExecutionReceipt":
        if _issuer_token is not _RUNNER_ISSUER_TOKEN:
            raise TypeError("execution receipt requires pinned runner issuance")
        membership.validate_against(registry)
        if type(solver_result) is not SolverResult:
            raise TypeError("runner result must be an exact SolverResult")
        observed_status = solver_result.status.name.lower()
        model = solver_result.model
        solver_output = {
            "solver_name": solver_result.solver_name,
            "status": observed_status,
            "elapsed_time": solver_result.elapsed_time,
            "model": model,
            "error_message": solver_result.error_message,
            "raw_output": solver_result.raw_output,
        }
        with _KEYRING_LOCK:
            signing_key_id = _ACTIVE_EXECUTION_AUTHORITY_KEY_ID
        payload = {
            "result_occurrence_id": result_occurrence_id,
            "registry_version": registry.registry_version,
            "normalized_registry_digest": registry.normalized_registry_digest,
            "registry_key": membership.registry_key,
            "proof_requirement_id": membership.proof_requirement_id,
            "obligation_id": membership.obligation_id,
            "observation_contract_id": membership.observation_contract_id,
            "attempt_group_identity": membership.attempt_group_identity,
            "attempt_ordinal": membership.attempt_ordinal,
            "execution_identity_digest": membership.execution_identity_digest,
            "invocation_identity": invocation_identity,
            "invocation_ordinal": invocation_ordinal,
            "normalized_query": query,
            "query_digest": authority_digest({"normalized_solver_query": query}),
            "query_authority_digest": query_authority_digest,
            "configured_timeout_ms": configured_timeout_ms,
            "elapsed_ms": max(0, int(float(solver_result.elapsed_time) * 1000)),
            "observed_status": observed_status,
            "solver_identity": solver_result.solver_name,
            "solver_output_authority": dict(solver_output),
            "solver_output_digest": authority_digest({
                "solver_output": canonical_value(solver_output)
            }),
            "model_authority": None if model is None else dict(model),
            "model_digest": (
                authority_digest({"solver_model": canonical_value(model)})
                if model is not None else None
            ),
            "runner_issuer_id": runner_issuer_id,
            "signing_key_id": signing_key_id,
        }
        payload["runner_result_seal"] = _seal((
            "generic-solver-runner-result-v1", authority_digest(payload)
        ), signing_key_id)
        value = cls(
            **payload,
            receipt_digest=authority_digest(payload),
            _factory_token=_EXECUTION_RECEIPT_TOKEN,
        )
        value.validate()
        return value

    def _payload(self) -> Mapping[str, Any]:
        return {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
            if name not in {"receipt_digest", "_factory_token"}
        }

    def to_authority_dict(self) -> Mapping[str, Any]:
        self.validate()
        return {**self._payload(), "receipt_digest": self.receipt_digest}

    @classmethod
    def from_persisted(
        cls, payload: Mapping[str, Any], *, _codec_token: object = None
    ) -> "GenericSolverExecutionReceipt":
        if _codec_token is not _EXECUTION_RECEIPT_CODEC_TOKEN:
            raise TypeError("persisted execution receipt requires the strict codec")
        normalized = dict(payload)
        normalized["registry_key"] = tuple(normalized["registry_key"])
        normalized["solver_output_authority"] = dict(
            normalized["solver_output_authority"]
        )
        if normalized.get("model_authority") is not None:
            normalized["model_authority"] = dict(normalized["model_authority"])
        value = cls(**normalized, _factory_token=_EXECUTION_RECEIPT_CODEC_TOKEN)
        value.validate()
        return value

    def validate(self) -> None:
        for label, value in (
            ("result occurrence", self.result_occurrence_id),
            ("proof requirement", self.proof_requirement_id),
            ("obligation", self.obligation_id),
            ("observation contract", self.observation_contract_id),
            ("attempt group", self.attempt_group_identity),
            ("execution identity", self.execution_identity_digest),
            ("invocation identity", self.invocation_identity),
            ("normalized query", self.normalized_query),
            ("registry digest", self.normalized_registry_digest),
            ("query digest", self.query_digest),
            ("query authority digest", self.query_authority_digest),
            ("solver identity", self.solver_identity),
            ("solver output digest", self.solver_output_digest),
            ("receipt digest", self.receipt_digest),
            ("runner issuer", self.runner_issuer_id),
            ("signing key ID", self.signing_key_id),
            ("runner result seal", self.runner_result_seal),
        ):
            _exact_string(value, label)
        if len(self.registry_key) != 4 or any(
            type(item) is not str or not item for item in self.registry_key
        ):
            raise TypeError("execution receipt registry key is incomplete")
        if type(self.registry_version) is not int or self.registry_version < 1:
            raise TypeError("execution receipt registry version is invalid")
        if type(self.attempt_ordinal) is not int or self.attempt_ordinal < 1:
            raise TypeError("execution receipt attempt ordinal is invalid")
        if type(self.invocation_ordinal) is not int or self.invocation_ordinal < 1:
            raise TypeError("execution receipt invocation ordinal is invalid")
        if type(self.elapsed_ms) is not int or self.elapsed_ms < 0:
            raise TypeError("execution receipt elapsed time is invalid")
        if self.configured_timeout_ms is not None and (
            type(self.configured_timeout_ms) is not int or self.configured_timeout_ms <= 0
        ):
            raise TypeError("execution receipt timeout budget is invalid")
        if self.observed_status not in {"sat", "unsat", "unknown", "timeout", "error"}:
            raise ValueError("execution receipt status is not sealed")
        if not isinstance(self.solver_output_authority, Mapping):
            raise TypeError("execution receipt solver output authority is not typed")
        if self.solver_output_authority.get("status") != self.observed_status:
            raise ValueError("execution receipt solver output/status differ")
        if canonical_value(self.solver_output_authority.get("model")) != canonical_value(
            self.model_authority
        ):
            raise ValueError("execution receipt solver output/model differ")
        if self.query_digest != authority_digest({
            "normalized_solver_query": self.normalized_query
        }):
            raise ValueError("execution receipt query digest mismatch")
        if self.solver_output_digest != authority_digest({
            "solver_output": canonical_value(self.solver_output_authority)
        }):
            raise ValueError("execution receipt solver output digest mismatch")
        expected_model_digest = (
            authority_digest({"solver_model": canonical_value(self.model_authority)})
            if self.model_authority is not None else None
        )
        if self.model_digest != expected_model_digest:
            raise ValueError("execution receipt model digest mismatch")
        unsealed = dict(self._payload())
        unsealed.pop("runner_result_seal")
        expected_seal = _seal((
            "generic-solver-runner-result-v1", authority_digest(unsealed)
        ), self.signing_key_id)
        if not hmac.compare_digest(self.runner_result_seal, expected_seal):
            raise ValueError("execution receipt runner result seal mismatch")
        if (self.observed_status == "sat") != (self.model_digest is not None):
            raise ValueError("execution receipt model/status authority differs")
        if self.receipt_digest != authority_digest(self._payload()):
            raise ValueError("generic execution receipt digest mismatch")

    def validate_join(
        self,
        registry: ProducerStageRegistry,
        membership: ProducerAttemptMembership,
    ) -> None:
        self.validate()
        membership.validate_against(registry)
        contract = registry.get(*membership.registry_key)
        if (
            self.registry_version != registry.registry_version
            or self.normalized_registry_digest != registry.normalized_registry_digest
            or self.registry_key != membership.registry_key
            or self.proof_requirement_id != membership.proof_requirement_id
            or self.obligation_id != membership.obligation_id
            or self.observation_contract_id != membership.observation_contract_id
            or self.attempt_group_identity != membership.attempt_group_identity
            or self.attempt_ordinal != membership.attempt_ordinal
            or self.execution_identity_digest != membership.execution_identity_digest
        ):
            raise ValueError("execution receipt does not exactly join producer attempt")
        if self.runner_issuer_id != contract.execution_issuer_id:
            raise ValueError("execution receipt issuer is not sealed for producer stage")


class PinnedSolverExecutionIssuer:
    issuer_id = "parallel-solver-runner-v1"

    def __init__(self, *, _factory_token: object = None) -> None:
        if _factory_token is not _RUNNER_ISSUER_TOKEN:
            raise TypeError("solver execution issuer is pinned by this module")
        self._ledgers: dict[tuple[int, str, str], SolverExecutionLedger] = {}
        self._sealed_results: set[tuple[int, str, str]] = set()
        self._ledger_lock = threading.RLock()

    def issue_result_entry_occurrence(
        self,
        *,
        result_occurrence_id: str,
        execution_payload_digest: str,
        startup_receipt_digests: Sequence[str],
        occurrence_nonce: Optional[str] = None,
    ) -> SolverResultEntryOccurrenceReceipt:
        startup = tuple(sorted(startup_receipt_digests))
        nonce = secrets.token_hex(24) if occurrence_nonce is None else occurrence_nonce
        _exact_string(nonce, "result-entry occurrence nonce")
        _exact_string(result_occurrence_id, "canonical result occurrence ID")
        payload = {
            "execution_payload_digest": execution_payload_digest,
            "startup_receipt_digests": startup,
            "occurrence_nonce": nonce,
            "result_entry_occurrence_id": result_occurrence_id,
        }
        receipt = SolverResultEntryOccurrenceReceipt(
            **payload,
            receipt_digest=authority_digest(payload),
            _factory_token=_RUNNER_ISSUER_TOKEN,
        )
        receipt.validate()
        return receipt

    def has_open_result_ledger(
        self, registry: ProducerStageRegistry, result_occurrence_id: str
    ) -> bool:
        key = (
            registry.registry_version,
            registry.normalized_registry_digest,
            result_occurrence_id,
        )
        with self._ledger_lock:
            return key in self._ledgers

    def _ledger_for(
        self, registry: ProducerStageRegistry, result_occurrence_id: str,
        startup_receipt_digest: Optional[str] = None,
    ) -> "SolverExecutionLedger":
        key = (
            registry.registry_version,
            registry.normalized_registry_digest,
            result_occurrence_id,
        )
        with self._ledger_lock:
            if key in self._sealed_results:
                raise ValueError("solver result occurrence census is already sealed")
            ledger = self._ledgers.get(key)
            if ledger is None:
                ledger = SolverExecutionLedger(
                    registry, result_occurrence_id,
                    startup_receipt_digest=startup_receipt_digest,
                    _factory_token=_SOLVER_LEDGER_TOKEN,
                )
                self._ledgers[key] = ledger
            elif startup_receipt_digest is not None:
                ledger.bind_startup_receipt(startup_receipt_digest)
            return ledger

    def seal_result_census(
        self, registry: ProducerStageRegistry, result_occurrence_id: str
    ) -> "SolverExecutionCensusAuthority":
        key = (
            registry.registry_version,
            registry.normalized_registry_digest,
            result_occurrence_id,
        )
        with self._ledger_lock:
            try:
                ledger = self._ledgers[key]
            except KeyError as exc:
                raise ValueError("solver result occurrence has no execution ledger") from exc
            census = ledger.seal()
            self._ledgers.pop(key)
            self._sealed_results.add(key)
            return census

    def execute(
        self,
        *,
        registry: ProducerStageRegistry,
        result_occurrence_id: str,
        membership: ProducerAttemptMembership,
        invocation_identity: str,
        first_invocation_ordinal: int,
        query: str,
        configured_timeout_ms: int,
        query_authority: Any = None,
        lifecycle_projection: Optional[VerifiedLifecyclePrefixProjection] = None,
        _verifier_token: object = None,
    ) -> tuple[GenericSolverExecutionReceipt, ...]:
        membership.validate_against(registry)
        if registry.get(*membership.registry_key).execution_issuer_id != self.issuer_id:
            raise ValueError("production issuer is not registered for producer stage")
        startup_receipt = validate_execution_authority_deployment()
        if startup_receipt.active_key_id == "process-ephemeral-v1":
            raise ValueError("production execution requires a deployment signing key")
        if lifecycle_projection is None:
            raise ValueError("production execution requires current lifecycle projection")
        membership.requirement_assignment.validate_against(lifecycle_projection)
        if (
            lifecycle_projection.result_occurrence_id != result_occurrence_id
            or membership.requirement_assignment.proof_requirement_id
            != membership.proof_requirement_id
            or membership.requirement_assignment.obligation_id != membership.obligation_id
            or membership.requirement_assignment.proof_stage != membership.proof_stage
        ):
            raise ValueError("producer membership does not exactly join live Q_open assignment")
        if _verifier_token is _PINNED_VERIFIER_TOKEN:
            if not isinstance(query_authority, Mapping):
                raise TypeError("replay execution requires bound parent query authority")
            query_authority_digest = authority_digest(query_authority)
        else:
            from ..call_effect_producer import CallEffectSolverQueryAuthority
            from .loop_recurrence import LoopSolverQueryAuthority
            from .abi_width_readonly import AbiWidthReadonlySolverQueryAuthority
            if type(query_authority) not in {
                CallEffectSolverQueryAuthority,
                LoopSolverQueryAuthority,
                AbiWidthReadonlySolverQueryAuthority,
            }:
                raise TypeError("production execution requires typed renderer query authority")
            query_authority.validate()
            if query_authority.query_text != query:
                raise ValueError("typed query authority and execution query differ")
            if (
                query_authority.stage != membership.proof_stage
                or query_authority.obligation_id != membership.obligation_id
                or query_authority.observation_contract_id
                != membership.observation_contract_id
                or query_authority.execution_identity_digest
                != membership.execution_identity_digest
            ):
                raise ValueError("typed query authority does not exactly join producer membership")
            query_authority_digest = authority_digest({
                "renderer_query_authority_digest": query_authority.authority_digest,
                "result_occurrence_id": result_occurrence_id,
                "proof_requirement_id": membership.proof_requirement_id,
                "obligation_id": membership.obligation_id,
                "observation_contract_id": membership.observation_contract_id,
                "producer_stage": membership.proof_stage,
                "execution_identity_digest": membership.execution_identity_digest,
            })
        runner = ParallelSolverRunner(
            timeout=max(1, int(configured_timeout_ms / 1000)),
            solver_classes=list(_APPROVED_PRODUCTION_SOLVER_CLASSES),
        )
        ledger = self._ledger_for(
            registry, result_occurrence_id, startup_receipt.receipt_digest
        )
        try:
            parallel = _PINNED_PARALLEL_RUN_IMPL(
                runner,
                query, timeout=max(1, int(configured_timeout_ms / 1000))
            )
            if type(parallel) is not ParallelResult:
                raise TypeError("parallel solver runner returned an untyped result")
            results = tuple(parallel.results)
            if not results:
                raise ValueError("parallel solver runner returned no invocation result")
        except Exception as exc:
            attempt = ReceiptlessSolverAttemptAuthority._issue(
                result_occurrence_id=result_occurrence_id,
                invocation_identity=f"{invocation_identity}:receiptless",
                invocation_ordinal=first_invocation_ordinal,
                membership=membership,
                query=query,
                query_authority_digest=query_authority_digest,
                failure_kind=type(exc).__name__,
                _issuer_token=_RUNNER_ISSUER_TOKEN,
            )
            ledger._append_receiptless_from_issuer(
                membership, attempt, _issuer_token=_RUNNER_ISSUER_TOKEN
            )
            raise
        receipts = tuple(
            GenericSolverExecutionReceipt._issue_from_runner_result(
                registry=registry,
                result_occurrence_id=result_occurrence_id,
                membership=membership,
                invocation_identity=f"{invocation_identity}:{index}",
                invocation_ordinal=first_invocation_ordinal + index - 1,
                query=query,
                configured_timeout_ms=configured_timeout_ms,
                solver_result=result,
                runner_issuer_id=self.issuer_id,
                query_authority_digest=query_authority_digest,
                _issuer_token=_RUNNER_ISSUER_TOKEN,
            )
            for index, result in enumerate(results, 1)
        )
        for receipt in receipts:
            ledger._append_from_issuer(
                membership, receipt, _issuer_token=_RUNNER_ISSUER_TOKEN
            )
        return receipts


PINNED_SOLVER_EXECUTION_ISSUER = PinnedSolverExecutionIssuer(
    _factory_token=_RUNNER_ISSUER_TOKEN
)


class NonProductionTestSolverExecutionIssuer:
    """Fixture issuer accepted only by an explicitly test-owned stage registry."""

    issuer_id = "nonproduction-test-solver-results-v1"

    def issue_results(
        self, *, registry: ProducerStageRegistry, result_occurrence_id: str,
        membership: ProducerAttemptMembership, invocation_identity: str,
        first_invocation_ordinal: int, query: str, configured_timeout_ms: int,
        results: tuple[SolverResult, ...],
    ) -> tuple[GenericSolverExecutionReceipt, ...]:
        membership.validate_against(registry)
        if registry.get(*membership.registry_key).execution_issuer_id != self.issuer_id:
            raise ValueError("test issuer is not registered for producer stage")
        if not results or any(type(item) is not SolverResult for item in results):
            raise TypeError("test issuer requires exact SolverResult fixtures")
        return tuple(
            GenericSolverExecutionReceipt._issue_from_runner_result(
                registry=registry,
                result_occurrence_id=result_occurrence_id,
                membership=membership,
                invocation_identity=f"{invocation_identity}:{index}",
                invocation_ordinal=first_invocation_ordinal + index - 1,
                query=query,
                configured_timeout_ms=configured_timeout_ms,
                solver_result=result,
                runner_issuer_id=self.issuer_id,
                query_authority_digest=authority_digest({
                    "nonproduction_test_query": query,
                }),
                _issuer_token=_RUNNER_ISSUER_TOKEN,
            )
            for index, result in enumerate(results, 1)
        )


NONPRODUCTION_TEST_SOLVER_EXECUTION_ISSUER = NonProductionTestSolverExecutionIssuer()


@dataclass(frozen=True)
class TerminalLifecycleProjectionAuthority:
    result_occurrence_id: str
    live_requirement_ids: tuple[str, ...]
    lifecycle_projection_digest: str

    @classmethod
    def create(
        cls, result_occurrence_id: str, live_requirement_ids: Iterable[str]
    ) -> "TerminalLifecycleProjectionAuthority":
        _exact_string(result_occurrence_id, "result occurrence")
        ordered = tuple(sorted(set(live_requirement_ids)))
        if any(type(item) is not str or not item for item in ordered):
            raise TypeError("live requirement IDs must be exact strings")
        digest = authority_digest({
            "result_occurrence_id": result_occurrence_id,
            "live_requirement_ids": ordered,
        })
        return cls(result_occurrence_id, ordered, digest)

    def validate(self) -> None:
        if tuple(sorted(set(self.live_requirement_ids))) != self.live_requirement_ids:
            raise ValueError("lifecycle live requirements are not canonical")
        expected = authority_digest({
            "result_occurrence_id": self.result_occurrence_id,
            "live_requirement_ids": self.live_requirement_ids,
        })
        if self.lifecycle_projection_digest != expected:
            raise ValueError("lifecycle projection digest mismatch")


@dataclass(frozen=True)
class TerminalTimeoutCandidate:
    membership: ProducerAttemptMembership
    execution_receipt: GenericSolverExecutionReceipt
    solver_event_sequence: int

    def validate_against(
        self,
        registry: ProducerStageRegistry,
        projection: TerminalLifecycleProjectionAuthority,
    ) -> None:
        projection.validate()
        self.membership.validate_against(registry)
        self.execution_receipt.validate_join(registry, self.membership)
        contract = registry.get(*self.membership.registry_key)
        if self.membership.producer_status not in contract.terminal_eligible_statuses:
            raise ValueError("producer attempt status is not terminal-timeout eligible")
        if self.execution_receipt.observed_status != "timeout":
            raise ValueError("terminal candidate receipt is not an observed timeout")
        if self.execution_receipt.result_occurrence_id != projection.result_occurrence_id:
            raise ValueError("terminal candidate result occurrence differs from projection")
        if self.membership.proof_requirement_id not in projection.live_requirement_ids:
            raise ValueError("terminal candidate requirement is not live in Q_open")
        if type(self.solver_event_sequence) is not int or self.solver_event_sequence < 1:
            raise TypeError("terminal candidate event sequence is invalid")

    def identity_tuple(self) -> tuple[Any, ...]:
        return (
            self.membership.registry_key,
            self.membership.proof_requirement_id,
            self.membership.attempt_group_identity,
            self.membership.attempt_ordinal,
            self.execution_receipt.receipt_digest,
            self.solver_event_sequence,
        )


@dataclass(frozen=True, init=False)
class ReceiptlessSolverAttemptAuthority:
    result_occurrence_id: str
    membership_digest: str
    invocation_identity: str
    invocation_ordinal: int
    normalized_query_digest: str
    query_authority_digest: str
    failure_kind: str
    attempt_digest: str

    def __init__(self, *, _factory_token: object = None, **payload: Any) -> None:
        if _factory_token not in {_RUNNER_ISSUER_TOKEN, _RECEIPTLESS_ATTEMPT_TOKEN}:
            raise TypeError("receiptless solver attempt is issuer/codec owned")
        expected = set(self.__dataclass_fields__)
        if set(payload) != expected:
            raise TypeError("receiptless solver attempt fields are not exact")
        for name, value in payload.items():
            object.__setattr__(self, name, value)

    @classmethod
    def _issue(
        cls, *, result_occurrence_id: str, invocation_identity: str,
        invocation_ordinal: int, membership: ProducerAttemptMembership,
        query: str, query_authority_digest: str,
        failure_kind: str, _issuer_token: object = None,
    ) -> "ReceiptlessSolverAttemptAuthority":
        if _issuer_token is not _RUNNER_ISSUER_TOKEN:
            raise TypeError("receiptless solver attempt is issuer-owned")
        payload = {
            "result_occurrence_id": result_occurrence_id,
            "membership_digest": authority_digest(membership),
            "invocation_identity": invocation_identity,
            "invocation_ordinal": invocation_ordinal,
            "normalized_query_digest": authority_digest({
                "normalized_solver_query": query
            }),
            "query_authority_digest": query_authority_digest,
            "failure_kind": failure_kind,
        }
        value = cls(
            **payload, attempt_digest=authority_digest(payload),
            _factory_token=_RUNNER_ISSUER_TOKEN,
        )
        value.validate()
        return value

    def validate(self) -> None:
        for value in (
            self.result_occurrence_id, self.membership_digest,
            self.invocation_identity,
            self.normalized_query_digest, self.query_authority_digest,
            self.failure_kind, self.attempt_digest,
        ):
            _exact_string(value, "receiptless attempt authority")
        if type(self.invocation_ordinal) is not int or self.invocation_ordinal < 1:
            raise TypeError("receiptless attempt invocation ordinal is invalid")
        payload = {
            name: getattr(self, name)
            for name in self.__dataclass_fields__ if name != "attempt_digest"
        }
        if self.attempt_digest != authority_digest(payload):
            raise ValueError("receiptless attempt digest mismatch")

    def to_authority_dict(self) -> Mapping[str, Any]:
        self.validate()
        return {
            name: getattr(self, name) for name in self.__dataclass_fields__
        }


@dataclass(frozen=True)
class SolverExecutionEvent:
    sequence_number: int
    membership: ProducerAttemptMembership
    execution_receipt: Optional[GenericSolverExecutionReceipt]
    receiptless_attempt: Optional[ReceiptlessSolverAttemptAuthority] = None

    def validate_against(
        self, registry: ProducerStageRegistry, result_occurrence_id: str
    ) -> None:
        if type(self.sequence_number) is not int or self.sequence_number < 1:
            raise TypeError("solver execution sequence is invalid")
        if (self.execution_receipt is None) == (self.receiptless_attempt is None):
            raise ValueError("solver event must contain exactly one attempt authority")
        if self.execution_receipt is not None:
            self.execution_receipt.validate_join(registry, self.membership)
            event_result_occurrence_id = self.execution_receipt.result_occurrence_id
        else:
            self.receiptless_attempt.validate()
            if self.receiptless_attempt.membership_digest != authority_digest(
                self.membership
            ):
                raise ValueError("receiptless solver attempt membership differs")
            event_result_occurrence_id = self.receiptless_attempt.result_occurrence_id
        if event_result_occurrence_id != result_occurrence_id:
            raise ValueError("solver execution event result occurrence differs")

    def identity_tuple(self) -> tuple[Any, ...]:
        return (
            self.sequence_number,
            self.membership.registry_key,
            self.membership.proof_requirement_id,
            self.membership.producer_status,
            self.membership.attempt_group_identity,
            self.membership.attempt_ordinal,
            self.membership.execution_identity_digest,
            (
                self.membership.requirement_assignment.assignment_digest
                if self.membership.requirement_assignment is not None
                else None
            ),
            (
                "execution_receipt", self.execution_receipt.receipt_digest
            ) if self.execution_receipt is not None else (
                "receiptless_attempt", self.receiptless_attempt.attempt_digest
            ),
        )


@dataclass(frozen=True, init=False)
class SolverExecutionCensusAuthority:
    registry_version: int
    normalized_registry_digest: str
    result_occurrence_id: str
    execution_authority_startup_receipt_digest: Optional[str]
    events: tuple[SolverExecutionEvent, ...]
    event_stream_digest: str
    _factory_token: object = field(default=None, init=False, repr=False, compare=False)

    def __init__(self, *, _factory_token: object = None, **payload: Any) -> None:
        if _factory_token is not _SOLVER_LEDGER_TOKEN:
            raise TypeError("solver execution census must be ledger-issued")
        for name, value in payload.items():
            object.__setattr__(self, name, value)
        object.__setattr__(self, "_factory_token", _factory_token)

    def validate(self, registry: ProducerStageRegistry) -> None:
        if (
            self.registry_version != registry.registry_version
            or self.normalized_registry_digest != registry.normalized_registry_digest
        ):
            raise ValueError("solver census registry authority differs")
        if tuple(event.sequence_number for event in self.events) != tuple(
            range(1, len(self.events) + 1)
        ):
            raise ValueError("solver census sequence is not contiguous")
        for event in self.events:
            if type(event) is not SolverExecutionEvent:
                raise TypeError("solver census event type is not exact")
            event.validate_against(registry, self.result_occurrence_id)
        expected = authority_digest({
            "registry_version": self.registry_version,
            "normalized_registry_digest": self.normalized_registry_digest,
            "result_occurrence_id": self.result_occurrence_id,
            "execution_authority_startup_receipt_digest": (
                self.execution_authority_startup_receipt_digest
            ),
            "events": tuple(event.identity_tuple() for event in self.events),
        })
        if self.event_stream_digest != expected:
            raise ValueError("solver census event stream digest mismatch")

    def to_authority_dict(self, registry: ProducerStageRegistry) -> Mapping[str, Any]:
        self.validate(registry)
        return {
            "registry_version": self.registry_version,
            "normalized_registry_digest": self.normalized_registry_digest,
            "result_occurrence_id": self.result_occurrence_id,
            "execution_authority_startup_receipt_digest": (
                self.execution_authority_startup_receipt_digest
            ),
            "events": tuple({
                "sequence_number": event.sequence_number,
                "membership": {
                    "domain_contract_id": event.membership.domain_contract_id,
                    "producer_contract_id": event.membership.producer_contract_id,
                    "producer_version": event.membership.producer_version,
                    "proof_stage": event.membership.proof_stage,
                    "proof_requirement_id": event.membership.proof_requirement_id,
                    "obligation_id": event.membership.obligation_id,
                    "observation_contract_id": event.membership.observation_contract_id,
                    "producer_status": event.membership.producer_status,
                    "attempt_group_identity": event.membership.attempt_group_identity,
                    "attempt_ordinal": event.membership.attempt_ordinal,
                    "execution_identity_digest": event.membership.execution_identity_digest,
                    "requirement_assignment": (
                        event.membership.requirement_assignment.to_authority_dict()
                        if event.membership.requirement_assignment is not None
                        else None
                    ),
                },
                "execution_receipt": (
                    event.execution_receipt.to_authority_dict()
                    if event.execution_receipt is not None else None
                ),
                "receiptless_attempt": (
                    event.receiptless_attempt.to_authority_dict()
                    if event.receiptless_attempt is not None else None
                ),
            } for event in self.events),
            "event_stream_digest": self.event_stream_digest,
        }


class SolverExecutionLedger:
    def __init__(
        self, registry: ProducerStageRegistry, result_occurrence_id: str,
        startup_receipt_digest: Optional[str] = None,
        *, _factory_token: object = None,
    ) -> None:
        if _factory_token is not _SOLVER_LEDGER_TOKEN:
            raise TypeError("solver execution ledger must be authority-factory issued")
        _exact_string(result_occurrence_id, "result occurrence")
        self._registry = registry
        self._result_occurrence_id = result_occurrence_id
        self._startup_receipt_digest = startup_receipt_digest
        self._events: list[SolverExecutionEvent] = []
        self._sealed = False
        self._lock = threading.RLock()
        self._open_replays = 0
        receipt_issuer_ids = {
            item.execution_issuer_id
            for item in registry.contracts
            if item.execution_issuer_id in {
                "parallel-solver-runner-v1",
                "nonproduction-test-solver-results-v1",
            }
        }
        if len(receipt_issuer_ids) != 1:
            raise ValueError(
                "solver ledger registry must have one solver-receipt issuer owner"
            )
        self._execution_issuer_id = next(iter(receipt_issuer_ids))

    def bind_startup_receipt(self, startup_receipt_digest: str) -> None:
        _exact_string(startup_receipt_digest, "startup receipt digest")
        with self._lock:
            if self._sealed:
                raise ValueError("sealed solver ledger startup binding is immutable")
            if (
                self._startup_receipt_digest is not None
                and self._startup_receipt_digest != startup_receipt_digest
            ):
                raise ValueError("solver ledger startup receipt changed")
            self._startup_receipt_digest = startup_receipt_digest

    def _append_from_issuer(
        self, membership: ProducerAttemptMembership,
        execution_receipt: GenericSolverExecutionReceipt,
        *, _issuer_token: object = None,
    ) -> SolverExecutionEvent:
        if _issuer_token is not _RUNNER_ISSUER_TOKEN:
            raise TypeError("production solver ledger is issuer-append-only")
        with self._lock:
            if self._sealed:
                raise ValueError("solver execution ledger is sealed")
            event = SolverExecutionEvent(
                len(self._events) + 1, membership, execution_receipt
            )
            event.validate_against(self._registry, self._result_occurrence_id)
            self._events.append(event)
            return event

    def _append_receiptless_from_issuer(
        self, membership: ProducerAttemptMembership,
        attempt: ReceiptlessSolverAttemptAuthority,
        *, _issuer_token: object = None,
    ) -> SolverExecutionEvent:
        if _issuer_token is not _RUNNER_ISSUER_TOKEN:
            raise TypeError("production solver ledger is issuer-append-only")
        with self._lock:
            if self._sealed:
                raise ValueError("solver execution ledger is sealed")
            membership.validate_against(self._registry)
            attempt.validate()
            event = SolverExecutionEvent(
                len(self._events) + 1, membership, None, attempt
            )
            event.validate_against(self._registry, self._result_occurrence_id)
            self._events.append(event)
            return event

    def _begin_replay(self, *, _verifier_token: object = None) -> None:
        if _verifier_token is not _PINNED_VERIFIER_TOKEN:
            raise TypeError("replay lifecycle is pinned-verifier owned")
        with self._lock:
            if self._sealed:
                raise ValueError("solver execution ledger is sealed")
            self._open_replays += 1

    def _end_replay(self, *, _verifier_token: object = None) -> None:
        if _verifier_token is not _PINNED_VERIFIER_TOKEN:
            raise TypeError("replay lifecycle is pinned-verifier owned")
        with self._lock:
            if self._open_replays < 1:
                raise ValueError("solver replay lifecycle is unbalanced")
            self._open_replays -= 1

    def seal(self) -> SolverExecutionCensusAuthority:
        with self._lock:
            if self._sealed:
                raise ValueError("solver execution ledger is already sealed")
            if self._open_replays:
                raise ValueError("solver census cannot seal before replay completion")
            self._sealed = True
            payload = {
                "registry_version": self._registry.registry_version,
                "normalized_registry_digest": self._registry.normalized_registry_digest,
                "result_occurrence_id": self._result_occurrence_id,
                "execution_authority_startup_receipt_digest": (
                    self._startup_receipt_digest
                ),
                "events": tuple(self._events),
            }
            payload["event_stream_digest"] = authority_digest({
                **{key: value for key, value in payload.items() if key != "events"},
                "events": tuple(event.identity_tuple() for event in self._events),
            })
            census = SolverExecutionCensusAuthority(
                **payload, _factory_token=_SOLVER_LEDGER_TOKEN
            )
            census.validate(self._registry)
            return census


@dataclass(frozen=True, init=False)
class TerminalTimeoutSelectionReceipt:
    registry_version: int
    normalized_registry_digest: str
    result_occurrence_id: str
    lifecycle_projection_digest: str
    event_stream_digest: str
    candidate_set_digest: str
    selected_registry_key: tuple[str, str, str, str]
    selected_priority: int
    proof_requirement_id: str
    attempt_group_identity: str
    attempt_ordinal: int
    solver_event_sequence: int
    execution_receipt_digest: str
    selection_receipt_digest: str
    _factory_token: object = field(default=None, init=False, repr=False, compare=False)

    def __init__(self, *, _factory_token: object = None, **payload: Any) -> None:
        if _factory_token not in {_SELECTION_FACTORY_TOKEN, _SELECTION_CODEC_TOKEN}:
            raise TypeError("TerminalTimeoutSelectionReceipt must be factory/codec issued")
        expected_fields = {
            name for name, definition in self.__dataclass_fields__.items()
            if name != "_factory_token" and definition.init
        }
        if set(payload) != expected_fields:
            raise TypeError("TerminalTimeoutSelectionReceipt fields are not exact")
        for name, value in payload.items():
            object.__setattr__(self, name, value)
        object.__setattr__(self, "_factory_token", _factory_token)

    def __post_init__(self) -> None:
        if self._factory_token not in {_SELECTION_FACTORY_TOKEN, _SELECTION_CODEC_TOKEN}:
            raise TypeError("terminal timeout selection must be factory/codec issued")

    @classmethod
    def select(
        cls,
        registry: ProducerStageRegistry,
        census: SolverExecutionCensusAuthority,
        projection: TerminalLifecycleProjectionAuthority,
    ) -> Optional["TerminalTimeoutSelectionReceipt"]:
        projection.validate()
        census.validate(registry)
        if census.result_occurrence_id != projection.result_occurrence_id:
            raise ValueError("solver census and lifecycle projection differ")
        latest_by_requirement: dict[tuple[Any, ...], SolverExecutionEvent] = {}
        for event in census.events:
            key = (
                event.membership.registry_key,
                event.membership.proof_requirement_id,
            )
            previous = latest_by_requirement.get(key)
            if previous is None or (
                event.membership.attempt_ordinal, event.sequence_number
            ) > (
                previous.membership.attempt_ordinal, previous.sequence_number
            ):
                latest_by_requirement[key] = event
        values = tuple(
            TerminalTimeoutCandidate(
                event.membership, event.execution_receipt, event.sequence_number
            )
            for event in latest_by_requirement.values()
            if event.execution_receipt is not None
            and event.execution_receipt.observed_status == "timeout"
            and event.membership.producer_status in registry.get(
                *event.membership.registry_key
            ).terminal_eligible_statuses
            and event.membership.proof_requirement_id in projection.live_requirement_ids
        )
        if not values:
            return None
        latest_by_attempt: dict[tuple[Any, ...], TerminalTimeoutCandidate] = {}
        for candidate in values:
            candidate.validate_against(registry, projection)
            attempt_key = (
                candidate.membership.registry_key,
                candidate.membership.proof_requirement_id,
                candidate.membership.attempt_group_identity,
                candidate.membership.attempt_ordinal,
            )
            previous = latest_by_attempt.get(attempt_key)
            if previous is None or (
                candidate.solver_event_sequence,
                candidate.execution_receipt.receipt_digest,
            ) > (
                previous.solver_event_sequence,
                previous.execution_receipt.receipt_digest,
            ):
                latest_by_attempt[attempt_key] = candidate
        normalized = tuple(latest_by_attempt.values())
        ranked = []
        for candidate in normalized:
            priority = registry.get(*candidate.membership.registry_key).terminal_priority
            ranked.append((
                priority,
                authority_digest(candidate.membership.proof_requirement_id),
                -candidate.solver_event_sequence,
                candidate.execution_receipt.receipt_digest,
                candidate,
            ))
        _priority, _requirement_key, _sequence, _receipt_key, selected = min(ranked)
        selected_priority = registry.get(*selected.membership.registry_key).terminal_priority
        candidate_set_digest = authority_digest(tuple(sorted(
            (candidate.identity_tuple() for candidate in normalized), key=authority_digest
        )))
        payload = {
            "registry_version": registry.registry_version,
            "normalized_registry_digest": registry.normalized_registry_digest,
            "result_occurrence_id": projection.result_occurrence_id,
            "lifecycle_projection_digest": projection.lifecycle_projection_digest,
            "event_stream_digest": census.event_stream_digest,
            "candidate_set_digest": candidate_set_digest,
            "selected_registry_key": selected.membership.registry_key,
            "selected_priority": selected_priority,
            "proof_requirement_id": selected.membership.proof_requirement_id,
            "attempt_group_identity": selected.membership.attempt_group_identity,
            "attempt_ordinal": selected.membership.attempt_ordinal,
            "solver_event_sequence": selected.solver_event_sequence,
            "execution_receipt_digest": selected.execution_receipt.receipt_digest,
        }
        return cls(
            **payload,
            selection_receipt_digest=authority_digest(payload),
            _factory_token=_SELECTION_FACTORY_TOKEN,
        )

    def validate_against(
        self,
        registry: ProducerStageRegistry,
        census: SolverExecutionCensusAuthority,
        projection: TerminalLifecycleProjectionAuthority,
    ) -> None:
        if (
            self.registry_version != registry.registry_version
            or self.normalized_registry_digest != registry.normalized_registry_digest
        ):
            raise ValueError("terminal timeout selection registry authority differs")
        recomputed = self.select(registry, census, projection)
        if recomputed is None:
            raise ValueError("terminal selection has no current eligible candidate")
        own = {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
            if name != "_factory_token"
        }
        expected = {
            name: getattr(recomputed, name)
            for name in recomputed.__dataclass_fields__
            if name != "_factory_token"
        }
        if own != expected:
            raise ValueError("terminal timeout selection differs from current authority")

    def to_authority_dict(self) -> Mapping[str, Any]:
        return {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
            if name != "_factory_token"
        }

    @classmethod
    def from_persisted(
        cls,
        payload: Mapping[str, Any],
        *,
        registry: ProducerStageRegistry,
        census: SolverExecutionCensusAuthority,
        projection: TerminalLifecycleProjectionAuthority,
        _codec_token: object = None,
    ) -> "TerminalTimeoutSelectionReceipt":
        if _codec_token is not _SELECTION_CODEC_TOKEN:
            raise TypeError("persisted terminal selection requires the strict codec")
        values = dict(payload)
        values["selected_registry_key"] = tuple(values["selected_registry_key"])
        value = cls(**values, _factory_token=_SELECTION_CODEC_TOKEN)
        value.validate_against(registry, census, projection)
        return value


@dataclass(frozen=True)
class SolverExecutionEvidenceBundle:
    """Persistable authority body for one result's complete solver history."""

    startup_receipt: ExecutionAuthorityStartupReceipt
    census: SolverExecutionCensusAuthority
    terminal_projection: TerminalLifecycleProjectionAuthority
    terminal_selection: Optional[TerminalTimeoutSelectionReceipt]
    final_lifecycle_projection_digest: str
    observed_stream_receipt_digests: tuple[str, ...]
    evidence_digest: str

    @classmethod
    def seal(
        cls,
        *,
        registry: ProducerStageRegistry,
        startup_receipt: ExecutionAuthorityStartupReceipt,
        census: SolverExecutionCensusAuthority,
        terminal_projection: TerminalLifecycleProjectionAuthority,
        terminal_selection: Optional[TerminalTimeoutSelectionReceipt],
        final_lifecycle_projection_digest: str,
        observed_stream_receipt_digests: Iterable[str],
    ) -> "SolverExecutionEvidenceBundle":
        observed = tuple(sorted(observed_stream_receipt_digests))
        selection_digest = (
            terminal_selection.selection_receipt_digest
            if terminal_selection is not None else None
        )
        payload = {
            "startup_receipt_digest": startup_receipt.receipt_digest,
            "registry_digest": registry.normalized_registry_digest,
            "census_event_stream_digest": census.event_stream_digest,
            "terminal_projection_digest": terminal_projection.lifecycle_projection_digest,
            "terminal_selection_digest": selection_digest,
            "final_lifecycle_projection_digest": final_lifecycle_projection_digest,
            "observed_stream_receipt_digests": observed,
        }
        value = cls(
            startup_receipt,
            census,
            terminal_projection,
            terminal_selection,
            final_lifecycle_projection_digest,
            observed,
            authority_digest(payload),
        )
        value.validate(registry)
        return value

    def validate(self, registry: ProducerStageRegistry) -> None:
        self.startup_receipt.validate()
        self.census.validate(registry)
        if self.census.execution_authority_startup_receipt_digest != (
            self.startup_receipt.receipt_digest
        ):
            raise ValueError("solver census is not bound to startup receipt")
        self.terminal_projection.validate()
        if self.census.result_occurrence_id != self.terminal_projection.result_occurrence_id:
            raise ValueError("solver evidence result authorities differ")
        expected_observed = tuple(sorted(
            event.execution_receipt.receipt_digest
            for event in self.census.events
            if event.execution_receipt is not None
            and event.execution_receipt.observed_status in {"unknown", "timeout", "error"}
        ))
        if self.observed_stream_receipt_digests != expected_observed:
            raise ValueError("solver evidence stream omits or invents observed execution history")
        recomputed = TerminalTimeoutSelectionReceipt.select(
            registry, self.census, self.terminal_projection
        )
        if (recomputed is None) != (self.terminal_selection is None):
            raise ValueError("solver evidence terminal selection presence differs")
        if self.terminal_selection is not None:
            self.terminal_selection.validate_against(
                registry, self.census, self.terminal_projection
            )
        selection_digest = (
            self.terminal_selection.selection_receipt_digest
            if self.terminal_selection is not None else None
        )
        expected = authority_digest({
            "startup_receipt_digest": self.startup_receipt.receipt_digest,
            "registry_digest": registry.normalized_registry_digest,
            "census_event_stream_digest": self.census.event_stream_digest,
            "terminal_projection_digest": self.terminal_projection.lifecycle_projection_digest,
            "terminal_selection_digest": selection_digest,
            "final_lifecycle_projection_digest": self.final_lifecycle_projection_digest,
            "observed_stream_receipt_digests": self.observed_stream_receipt_digests,
        })
        if self.evidence_digest != expected:
            raise ValueError("solver execution evidence digest mismatch")

    def to_authority_dict(self, registry: ProducerStageRegistry) -> Mapping[str, Any]:
        self.validate(registry)
        startup = {
            name: getattr(self.startup_receipt, name)
            for name in self.startup_receipt.__dataclass_fields__
        }
        return {
            "startup_receipt": startup,
            "registry_version": registry.registry_version,
            "normalized_registry_digest": registry.normalized_registry_digest,
            "census": self.census.to_authority_dict(registry),
            "terminal_projection": {
                "result_occurrence_id": self.terminal_projection.result_occurrence_id,
                "live_requirement_ids": self.terminal_projection.live_requirement_ids,
                "lifecycle_projection_digest": (
                    self.terminal_projection.lifecycle_projection_digest
                ),
            },
            "terminal_selection": (
                self.terminal_selection.to_authority_dict()
                if self.terminal_selection is not None else None
            ),
            "final_lifecycle_projection_digest": self.final_lifecycle_projection_digest,
            "observed_stream_receipt_digests": self.observed_stream_receipt_digests,
            "evidence_digest": self.evidence_digest,
        }

    @classmethod
    def from_persisted(
        cls,
        payload: Mapping[str, Any],
        *,
        registry: ProducerStageRegistry,
    ) -> "SolverExecutionEvidenceBundle":
        expected_keys = {
            "startup_receipt", "registry_version", "normalized_registry_digest",
            "census", "terminal_projection", "terminal_selection",
            "final_lifecycle_projection_digest",
            "observed_stream_receipt_digests", "evidence_digest",
        }
        if type(payload) is not dict or set(payload) != expected_keys:
            raise TypeError("persisted solver evidence fields are not exact")
        if (
            payload["registry_version"] != registry.registry_version
            or payload["normalized_registry_digest"]
            != registry.normalized_registry_digest
        ):
            raise ValueError("persisted solver evidence registry differs")
        startup_body = payload["startup_receipt"]
        startup_keys = set(ExecutionAuthorityStartupReceipt.__dataclass_fields__)
        if type(startup_body) is not dict or set(startup_body) != startup_keys:
            raise TypeError("persisted startup receipt fields are not exact")
        startup_values = dict(startup_body)
        startup_values["retained_verification_key_ids"] = tuple(
            startup_values["retained_verification_key_ids"]
        )
        startup = ExecutionAuthorityStartupReceipt(**startup_values)
        startup.validate()

        census_body = payload["census"]
        if type(census_body) is not dict or set(census_body) != {
            "registry_version", "normalized_registry_digest",
            "result_occurrence_id", "execution_authority_startup_receipt_digest",
            "events", "event_stream_digest",
        }:
            raise TypeError("persisted solver census fields are not exact")
        events = []
        membership_keys = {
            "domain_contract_id", "producer_contract_id", "producer_version",
            "proof_stage", "proof_requirement_id", "obligation_id",
            "observation_contract_id", "producer_status",
            "attempt_group_identity", "attempt_ordinal",
            "execution_identity_digest", "requirement_assignment",
        }
        assignment_keys = {
            name for name in LiveRequirementAssignmentReceipt.__dataclass_fields__
            if name != "_factory_token"
        }
        for event_body in census_body["events"]:
            if type(event_body) is not dict or set(event_body) not in ({
                "sequence_number", "membership", "execution_receipt"
            }, {
                "sequence_number", "membership", "execution_receipt",
                "receiptless_attempt",
            }):
                raise TypeError("persisted solver census event fields are not exact")
            membership_body = event_body["membership"]
            if type(membership_body) is not dict or set(membership_body) != membership_keys:
                raise TypeError("persisted producer membership fields are not exact")
            membership_values = dict(membership_body)
            assignment_body = membership_values.pop("requirement_assignment")
            assignment = None
            if assignment_body is not None:
                if type(assignment_body) is not dict or set(assignment_body) != assignment_keys:
                    raise TypeError("persisted requirement assignment fields are not exact")
                assignment = LiveRequirementAssignmentReceipt(
                    **assignment_body, _factory_token=_SOLVER_LEDGER_TOKEN
                )
                assignment.validate_integrity()
            membership = ProducerAttemptMembership(
                **membership_values, requirement_assignment=assignment
            )
            membership.validate_against(registry)
            receipt_body = event_body["execution_receipt"]
            execution_receipt = (
                decode_persisted_execution_receipt(receipt_body)
                if receipt_body is not None else None
            )
            attempt_body = event_body.get("receiptless_attempt")
            receiptless_attempt = None
            if attempt_body is not None:
                attempt_keys = set(
                    ReceiptlessSolverAttemptAuthority.__dataclass_fields__
                )
                if type(attempt_body) is not dict or set(attempt_body) != attempt_keys:
                    raise TypeError("persisted receiptless attempt fields are not exact")
                receiptless_attempt = ReceiptlessSolverAttemptAuthority(
                    **attempt_body, _factory_token=_RECEIPTLESS_ATTEMPT_TOKEN
                )
                receiptless_attempt.validate()
            events.append(SolverExecutionEvent(
                event_body["sequence_number"], membership, execution_receipt,
                receiptless_attempt,
            ))
        census = SolverExecutionCensusAuthority(
            registry_version=census_body["registry_version"],
            normalized_registry_digest=census_body["normalized_registry_digest"],
            result_occurrence_id=census_body["result_occurrence_id"],
            execution_authority_startup_receipt_digest=(
                census_body["execution_authority_startup_receipt_digest"]
            ),
            events=tuple(events),
            event_stream_digest=census_body["event_stream_digest"],
            _factory_token=_SOLVER_LEDGER_TOKEN,
        )
        census.validate(registry)

        terminal_body = payload["terminal_projection"]
        if type(terminal_body) is not dict or set(terminal_body) != {
            "result_occurrence_id", "live_requirement_ids",
            "lifecycle_projection_digest",
        }:
            raise TypeError("persisted terminal projection fields are not exact")
        terminal_projection = TerminalLifecycleProjectionAuthority.create(
            terminal_body["result_occurrence_id"],
            tuple(terminal_body["live_requirement_ids"]),
        )
        if terminal_projection.lifecycle_projection_digest != (
            terminal_body["lifecycle_projection_digest"]
        ):
            raise ValueError("persisted terminal projection digest differs")
        selection_body = payload["terminal_selection"]
        selection = None
        if selection_body is not None:
            selection = TerminalTimeoutSelectionReceipt.from_persisted(
                selection_body,
                registry=registry,
                census=census,
                projection=terminal_projection,
                _codec_token=_SELECTION_CODEC_TOKEN,
            )
        value = cls(
            startup,
            census,
            terminal_projection,
            selection,
            payload["final_lifecycle_projection_digest"],
            tuple(payload["observed_stream_receipt_digests"]),
            payload["evidence_digest"],
        )
        value.validate(registry)
        return value


@dataclass(frozen=True, init=False)
class RelationalWitnessReplayReceipt:
    proof_requirement_id: str
    obligation_id: str
    prepared_surface_digest: str
    observation_contract_id: str
    query_digest: str
    model_digest: str
    normalized_assertion_digest: str
    premise_digest: str
    stage_input_digest: str
    replay_execution_receipt: GenericSolverExecutionReceipt
    applicability_authority: Mapping[str, Any]
    applicability_digest: str
    verifier_id: str
    verifier_version: str
    replay_status: str
    replay_receipt_digest: str
    _factory_token: object = field(default=None, init=False, repr=False, compare=False)

    def __init__(self, *, _factory_token: object = None, **payload: Any) -> None:
        _initialize_factory_value(
            self,
            payload,
            expected_token=(_REPLAY_RECEIPT_TOKEN, _REPLAY_RECEIPT_CODEC_TOKEN),
            supplied_token=_factory_token,
        )

    def __post_init__(self) -> None:
        if self._factory_token is not _REPLAY_RECEIPT_TOKEN:
            raise TypeError("witness replay receipt must be pinned-verifier issued")

    def _payload(self) -> Mapping[str, Any]:
        return {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
            if name not in {"replay_receipt_digest", "_factory_token"}
        }

    def to_authority_dict(self) -> Mapping[str, Any]:
        payload = dict(self._payload())
        payload["replay_execution_receipt"] = (
            self.replay_execution_receipt.to_authority_dict()
        )
        payload["replay_receipt_digest"] = self.replay_receipt_digest
        return payload

    @classmethod
    def from_persisted(
        cls,
        payload: Mapping[str, Any],
        *,
        execution_receipt: GenericSolverExecutionReceipt,
        registry: ProducerStageRegistry,
        membership: ProducerAttemptMembership,
        verifier: "PinnedRelationalWitnessVerifier",
        _codec_token: object = None,
    ) -> "RelationalWitnessReplayReceipt":
        if _codec_token is not _REPLAY_RECEIPT_CODEC_TOKEN:
            raise TypeError("persisted replay receipt requires the strict codec")
        values = dict(payload)
        replay_execution = GenericSolverExecutionReceipt.from_persisted(
            values.pop("replay_execution_receipt"),
            _codec_token=_EXECUTION_RECEIPT_CODEC_TOKEN,
        )
        value = cls(
            **values,
            replay_execution_receipt=replay_execution,
            _factory_token=_REPLAY_RECEIPT_CODEC_TOKEN,
        )
        verifier.validate(value, execution_receipt, registry, membership)
        return value


class PinnedRelationalWitnessVerifier:
    verifier_id = "typed-relational-witness-replay"
    verifier_version = "1"

    def __init__(self, *, _factory_token: object = None) -> None:
        if _factory_token is not _PINNED_VERIFIER_TOKEN:
            raise TypeError("witness verifier is pinned by the execution authority module")

    def issue(
        self,
        execution_receipt: GenericSolverExecutionReceipt,
        *,
        registry: ProducerStageRegistry,
        membership: ProducerAttemptMembership,
        obligation_id: str,
        prepared_surface_digest: str,
        observation_contract_id: str,
        normalized_assertion: str,
        premise: Mapping[str, Any],
        stage_input: Mapping[str, Any],
        model: Mapping[str, Any],
        configured_timeout_ms: int,
        nonproduction_replay_results: tuple[SolverResult, ...] = (),
        lifecycle_projection: Optional[VerifiedLifecyclePrefixProjection] = None,
    ) -> RelationalWitnessReplayReceipt:
        execution_receipt.validate_join(registry, membership)
        if execution_receipt.observed_status != "sat":
            raise ValueError("witness replay requires a SAT execution receipt")
        model_digest = authority_digest({"solver_model": canonical_value(model)})
        if model_digest != execution_receipt.model_digest:
            raise ValueError("witness replay model differs from SAT execution")
        required_stage_keys = {"declarations"}
        if set(stage_input) != required_stage_keys:
            raise ValueError("witness replay stage input is not the sealed SMT surface")
        declarations = tuple(stage_input["declarations"])
        premise_assertions = tuple(premise.get("assertions", ()))
        for row in declarations + premise_assertions:
            _exact_string(row, "witness replay SMT row")
        _exact_string(normalized_assertion, "normalized assertion")
        expected_original_query = "\n".join(
            declarations
            + premise_assertions
            + (f"(assert {normalized_assertion})", "(check-sat)")
        )
        if execution_receipt.normalized_query != expected_original_query:
            raise ValueError("replay surface does not exactly decompose original query")
        declaration_pattern = re.compile(
            r"^\(declare-const\s+([^\s()]+)\s+(.+)\)$"
        )
        declared: dict[str, str] = {}
        for row in declarations:
            match = declaration_pattern.match(row)
            if match is None or match.group(1) in declared:
                raise ValueError("replay declaration surface is not exact")
            declared[match.group(1)] = match.group(2)
        if set(model) != set(declared):
            raise ValueError("SAT model does not completely bind declared replay inputs")

        def model_literal(name: str, sort: str) -> str:
            value = model[name]
            if sort == "Bool" and type(value) is bool:
                return "true" if value else "false"
            if sort == "Int" and type(value) is int:
                return str(value)
            bitvec = re.fullmatch(r"\(_ BitVec ([1-9][0-9]*)\)", sort)
            if bitvec is not None and type(value) is int and value >= 0:
                width = int(bitvec.group(1))
                if value < (1 << width):
                    return f"(_ bv{value} {width})"
            raise ValueError("SAT model value cannot be exactly rendered for replay")

        model_assertions = tuple(
            f"(assert (= {name} {model_literal(name, declared[name])}))"
            for name in sorted(declared)
        )
        replay_query = "\n".join(
            declarations
            + premise_assertions
            + model_assertions
            + (f"(assert {normalized_assertion})", "(check-sat)")
        )
        replay_membership = ProducerAttemptMembership(
            membership.domain_contract_id,
            membership.producer_contract_id,
            membership.producer_version,
            membership.proof_stage,
            membership.proof_requirement_id,
            membership.obligation_id,
            membership.observation_contract_id,
            membership.producer_status,
            membership.attempt_group_identity,
            membership.attempt_ordinal,
            membership.execution_identity_digest,
            membership.requirement_assignment,
        )
        issuer_id = registry.get(*membership.registry_key).execution_issuer_id
        if issuer_id == PINNED_SOLVER_EXECUTION_ISSUER.issuer_id:
            if nonproduction_replay_results:
                raise ValueError("production replay cannot accept fixture solver results")
            replay_ledger = PINNED_SOLVER_EXECUTION_ISSUER._ledger_for(
                registry, execution_receipt.result_occurrence_id
            )
            replay_ledger._begin_replay(_verifier_token=_PINNED_VERIFIER_TOKEN)
            try:
                replay_receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
                    registry=registry,
                    result_occurrence_id=execution_receipt.result_occurrence_id,
                    membership=replay_membership,
                    invocation_identity="independent-model-replay",
                    first_invocation_ordinal=1,
                    query=replay_query,
                    configured_timeout_ms=configured_timeout_ms,
                    query_authority={
                        "parent_execution_receipt_digest": execution_receipt.receipt_digest,
                        "normalized_assertion": normalized_assertion,
                        "premise": canonical_value(premise),
                        "stage_input": canonical_value(stage_input),
                        "complete_model": canonical_value(model),
                    },
                    lifecycle_projection=lifecycle_projection,
                    _verifier_token=_PINNED_VERIFIER_TOKEN,
                )
            finally:
                replay_ledger._end_replay(_verifier_token=_PINNED_VERIFIER_TOKEN)
        elif issuer_id == NONPRODUCTION_TEST_SOLVER_EXECUTION_ISSUER.issuer_id:
            replay_receipts = NONPRODUCTION_TEST_SOLVER_EXECUTION_ISSUER.issue_results(
                registry=registry,
                result_occurrence_id=execution_receipt.result_occurrence_id,
                membership=replay_membership,
                invocation_identity="independent-model-replay",
                first_invocation_ordinal=1,
                query=replay_query,
                configured_timeout_ms=configured_timeout_ms,
                results=nonproduction_replay_results,
            )
        else:
            raise ValueError("replay execution issuer is not sealed")
        sat_replays = tuple(item for item in replay_receipts if item.observed_status == "sat")
        if not sat_replays:
            raise ValueError("independent fixed-model replay was not SAT")
        replay_execution = min(sat_replays, key=lambda item: item.invocation_ordinal)
        expected_applicability = {
            "proof_requirement_id": execution_receipt.proof_requirement_id,
            "obligation_id": obligation_id,
            "prepared_surface_digest": prepared_surface_digest,
            "observation_contract_id": observation_contract_id,
            "model": canonical_value(model),
            "replay_execution_receipt_digest": replay_execution.receipt_digest,
        }
        normalized_assertion_digest = authority_digest(
            {"normalized_assertion": normalized_assertion}
        )
        premise_digest = authority_digest({"premise": canonical_value(premise)})
        stage_input_digest = authority_digest(
            {"stage_input": canonical_value(stage_input)}
        )
        payload = {
            "proof_requirement_id": execution_receipt.proof_requirement_id,
            "obligation_id": obligation_id,
            "prepared_surface_digest": prepared_surface_digest,
            "observation_contract_id": observation_contract_id,
            "query_digest": execution_receipt.query_digest,
            "model_digest": model_digest,
            "normalized_assertion_digest": normalized_assertion_digest,
            "premise_digest": premise_digest,
            "stage_input_digest": stage_input_digest,
            "replay_execution_receipt": replay_execution,
            "applicability_authority": expected_applicability,
            "applicability_digest": authority_digest({
                "applicability": canonical_value(expected_applicability)
            }),
            "verifier_id": self.verifier_id,
            "verifier_version": self.verifier_version,
            "replay_status": "witness_validated",
        }
        return RelationalWitnessReplayReceipt(
            **payload,
            replay_receipt_digest=authority_digest(payload),
            _factory_token=_REPLAY_RECEIPT_TOKEN,
        )

    def validate(
        self,
        receipt: RelationalWitnessReplayReceipt,
        execution_receipt: GenericSolverExecutionReceipt,
        registry: ProducerStageRegistry,
        membership: ProducerAttemptMembership,
    ) -> None:
        if receipt.replay_status != "witness_validated":
            raise ValueError("witness replay status is not validated")
        expected_applicability = {
            "proof_requirement_id": execution_receipt.proof_requirement_id,
            "obligation_id": receipt.obligation_id,
            "prepared_surface_digest": receipt.prepared_surface_digest,
            "observation_contract_id": receipt.observation_contract_id,
            "model": canonical_value(execution_receipt.model_authority),
            "replay_execution_receipt_digest": (
                receipt.replay_execution_receipt.receipt_digest
            ),
        }
        execution_receipt.validate_join(registry, membership)
        receipt.replay_execution_receipt.validate_join(registry, membership)
        if (
            receipt.verifier_id != self.verifier_id
            or receipt.verifier_version != self.verifier_version
            or receipt.proof_requirement_id != execution_receipt.proof_requirement_id
            or receipt.query_digest != execution_receipt.query_digest
            or receipt.model_digest != execution_receipt.model_digest
            or receipt.replay_execution_receipt.observed_status != "sat"
            or canonical_value(receipt.applicability_authority)
            != canonical_value(expected_applicability)
            or receipt.applicability_digest != authority_digest({
                "applicability": canonical_value(receipt.applicability_authority)
            })
            or receipt.replay_receipt_digest != authority_digest(receipt._payload())
        ):
            raise ValueError("witness replay receipt does not join pinned SAT execution")


PINNED_RELATIONAL_WITNESS_VERIFIER = PinnedRelationalWitnessVerifier(
    _factory_token=_PINNED_VERIFIER_TOKEN
)


@dataclass(frozen=True, init=False)
class ModelBoundRelationalRefutationArtifact:
    proof_requirement_id: str
    obligation_id: str
    source_snapshot_digests: tuple[str, str]
    prepared_surface_digest: str
    observation_contract_id: str
    normalized_assertion_authority: str
    normalized_assertion_digest: str
    premise_authority: Any
    premise_digest: str
    stage_input_authority: Any
    stage_input_digest: str
    applicability_digest: str
    producer_version: str
    encoding_version: str
    dependency_proof_ids: tuple[str, ...]
    sat_execution_receipt: GenericSolverExecutionReceipt
    replay_receipt: RelationalWitnessReplayReceipt
    artifact_digest: str
    _factory_token: object = field(default=None, init=False, repr=False, compare=False)

    def __init__(self, *, _factory_token: object = None, **payload: Any) -> None:
        _initialize_factory_value(
            self,
            payload,
            expected_token=(_REFUTATION_TOKEN, _REFUTATION_CODEC_TOKEN),
            supplied_token=_factory_token,
        )

    def __post_init__(self) -> None:
        if self._factory_token is not _REFUTATION_TOKEN:
            raise TypeError("relational refutation artifact must be factory-issued")

    @classmethod
    def create(
        cls,
        *,
        obligation_id: str,
        source_snapshot_digests: tuple[str, str],
        prepared_surface_digest: str,
        observation_contract_id: str,
        normalized_assertion: str,
        premise: Any,
        stage_input: Any,
        applicability: Mapping[str, Any],
        producer_version: str,
        encoding_version: str,
        dependency_proof_ids: tuple[str, ...],
        sat_execution_receipt: GenericSolverExecutionReceipt,
        replay_receipt: RelationalWitnessReplayReceipt,
        registry: ProducerStageRegistry,
        membership: ProducerAttemptMembership,
        verifier: PinnedRelationalWitnessVerifier = PINNED_RELATIONAL_WITNESS_VERIFIER,
    ) -> "ModelBoundRelationalRefutationArtifact":
        verifier.validate(replay_receipt, sat_execution_receipt, registry, membership)
        if (
            replay_receipt.obligation_id != obligation_id
            or replay_receipt.prepared_surface_digest != prepared_surface_digest
            or replay_receipt.observation_contract_id != observation_contract_id
        ):
            raise ValueError("refutation replay scope differs from artifact scope")
        applicability_digest = authority_digest({
            "applicability": canonical_value(applicability)
        })
        if applicability_digest != replay_receipt.applicability_digest:
            raise ValueError("refutation applicability differs from pinned replay")
        if (
            replay_receipt.normalized_assertion_digest
            != authority_digest({"normalized_assertion": normalized_assertion})
            or replay_receipt.premise_digest
            != authority_digest({"premise": canonical_value(premise)})
            or replay_receipt.stage_input_digest
            != authority_digest({"stage_input": canonical_value(stage_input)})
        ):
            raise ValueError("refutation semantic input differs from independent replay")
        payload = {
            "proof_requirement_id": sat_execution_receipt.proof_requirement_id,
            "obligation_id": obligation_id,
            "source_snapshot_digests": tuple(source_snapshot_digests),
            "prepared_surface_digest": prepared_surface_digest,
            "observation_contract_id": observation_contract_id,
            "normalized_assertion_authority": normalized_assertion,
            "normalized_assertion_digest": authority_digest({
                "normalized_assertion": normalized_assertion
            }),
            "premise_authority": canonical_value(premise),
            "premise_digest": authority_digest({"premise": canonical_value(premise)}),
            "stage_input_authority": canonical_value(stage_input),
            "stage_input_digest": authority_digest({
                "stage_input": canonical_value(stage_input)
            }),
            "applicability_digest": applicability_digest,
            "producer_version": producer_version,
            "encoding_version": encoding_version,
            "dependency_proof_ids": tuple(dependency_proof_ids),
            "sat_execution_receipt": sat_execution_receipt,
            "replay_receipt": replay_receipt,
        }
        value = cls(
            **payload,
            artifact_digest=authority_digest(payload),
            _factory_token=_REFUTATION_TOKEN,
        )
        value.validate(verifier, registry, membership)
        return value

    def _payload(self) -> Mapping[str, Any]:
        return {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
            if name not in {"artifact_digest", "_factory_token"}
        }

    def to_authority_dict(self) -> Mapping[str, Any]:
        payload = dict(self._payload())
        payload["sat_execution_receipt"] = self.sat_execution_receipt.to_authority_dict()
        payload["replay_receipt"] = self.replay_receipt.to_authority_dict()
        payload["artifact_digest"] = self.artifact_digest
        return payload

    @classmethod
    def from_persisted(
        cls,
        payload: Mapping[str, Any],
        *,
        verifier: PinnedRelationalWitnessVerifier = PINNED_RELATIONAL_WITNESS_VERIFIER,
        registry: ProducerStageRegistry,
        membership: ProducerAttemptMembership,
        _codec_token: object = None,
    ) -> "ModelBoundRelationalRefutationArtifact":
        if _codec_token is not _REFUTATION_CODEC_TOKEN:
            raise TypeError("persisted refutation artifact requires the strict codec")
        values = dict(payload)
        execution = GenericSolverExecutionReceipt.from_persisted(
            values.pop("sat_execution_receipt"),
            _codec_token=_EXECUTION_RECEIPT_CODEC_TOKEN,
        )
        replay = RelationalWitnessReplayReceipt.from_persisted(
            values.pop("replay_receipt"),
            execution_receipt=execution,
            registry=registry,
            membership=membership,
            verifier=verifier,
            _codec_token=_REPLAY_RECEIPT_CODEC_TOKEN,
        )
        value = cls(
            **values,
            sat_execution_receipt=execution,
            replay_receipt=replay,
            _factory_token=_REFUTATION_CODEC_TOKEN,
        )
        value.validate(verifier, registry, membership)
        return value

    def validate(
        self,
        verifier: PinnedRelationalWitnessVerifier = PINNED_RELATIONAL_WITNESS_VERIFIER,
        registry: Optional[ProducerStageRegistry] = None,
        membership: Optional[ProducerAttemptMembership] = None,
    ) -> None:
        for value in (
            self.proof_requirement_id,
            self.obligation_id,
            self.prepared_surface_digest,
            self.observation_contract_id,
            self.normalized_assertion_digest,
            self.premise_digest,
            self.stage_input_digest,
            self.applicability_digest,
            self.producer_version,
            self.encoding_version,
            self.artifact_digest,
        ):
            _exact_string(value, "refutation authority")
        if len(self.source_snapshot_digests) != 2 or any(
            type(item) is not str or not item for item in self.source_snapshot_digests
        ):
            raise TypeError("refutation requires two source snapshots")
        if any(type(item) is not str or not item for item in self.dependency_proof_ids):
            raise TypeError("refutation dependency identity is invalid")
        self.sat_execution_receipt.validate()
        if (registry is None) != (membership is None):
            raise ValueError("registry and membership must be supplied together")
        if registry is not None and membership is not None:
            verifier.validate(
                self.replay_receipt, self.sat_execution_receipt, registry, membership
            )
        else:
            self.sat_execution_receipt.validate()
            self.replay_receipt.replay_execution_receipt.validate()
        if (
            self.proof_requirement_id != self.sat_execution_receipt.proof_requirement_id
            or self.proof_requirement_id != self.replay_receipt.proof_requirement_id
            or self.obligation_id != self.replay_receipt.obligation_id
            or self.prepared_surface_digest != self.replay_receipt.prepared_surface_digest
            or self.observation_contract_id != self.replay_receipt.observation_contract_id
            or self.applicability_digest != self.replay_receipt.applicability_digest
        ):
            raise ValueError("refutation artifact semantic authorities do not exactly join")
        if self.normalized_assertion_digest != authority_digest({
            "normalized_assertion": self.normalized_assertion_authority
        }):
            raise ValueError("refutation assertion digest mismatch")
        if self.premise_digest != authority_digest({
            "premise": canonical_value(self.premise_authority)
        }):
            raise ValueError("refutation premise digest mismatch")
        if self.stage_input_digest != authority_digest({
            "stage_input": canonical_value(self.stage_input_authority)
        }):
            raise ValueError("refutation stage input digest mismatch")
        if self.artifact_digest != authority_digest(self._payload()):
            raise ValueError("relational refutation artifact digest mismatch")


def decode_persisted_execution_receipt(
    payload: Mapping[str, Any]
) -> GenericSolverExecutionReceipt:
    """Strict execution-receipt ingress using the installed key-id keyring."""

    return GenericSolverExecutionReceipt.from_persisted(
        payload, _codec_token=_EXECUTION_RECEIPT_CODEC_TOKEN
    )

