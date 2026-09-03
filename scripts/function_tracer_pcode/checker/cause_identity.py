# -*- coding: utf-8 -*-
"""Typed identities for UNKNOWN root causes and proof requirements.

These models deliberately contain semantic identity only.  Run ids, paths,
elapsed time, and diagnostic labels belong to validation provenance records.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict, Mapping, Tuple, Union


CAUSE_IDENTITY_SCHEMA_VERSION = 1
PROOF_REQUIREMENT_SCHEMA_VERSION = 1


def _tuple(value: Any) -> Tuple[Any, ...]:
    if value is None:
        return ()
    if isinstance(value, tuple):
        return tuple(_tuple_item(item) for item in value)
    if isinstance(value, list):
        return tuple(_tuple_item(item) for item in value)
    return (_tuple_item(value),)


def _tuple_item(value: Any) -> Any:
    if isinstance(value, (tuple, list)):
        return tuple(_tuple_item(item) for item in value)
    if isinstance(value, Mapping):
        return tuple(
            (str(key), _tuple_item(item))
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        )
    return value


class IdentityScope(str, Enum):
    UNARY = "unary"
    RELATIONAL = "relational"
    EXECUTION = "execution"


@dataclass(frozen=True)
class UnaryCauseKey:
    cause_kind: str
    binary_content_identity: Tuple[Any, ...]
    function_ir_identity: Tuple[Any, ...]
    semantic_object_identity: Tuple[Any, ...]
    schema_version: int = CAUSE_IDENTITY_SCHEMA_VERSION
    identity_scope: str = IdentityScope.UNARY.value

    def to_dict(self) -> Dict[str, Any]:
        return _cause_to_dict(self)


@dataclass(frozen=True)
class RelationalCauseKey:
    cause_kind: str
    comparison_domain: Tuple[Any, ...]
    left_semantic_object: Tuple[Any, ...]
    right_semantic_object: Tuple[Any, ...]
    correspondence_contract: Tuple[Any, ...]
    schema_version: int = CAUSE_IDENTITY_SCHEMA_VERSION
    identity_scope: str = IdentityScope.RELATIONAL.value

    def to_dict(self) -> Dict[str, Any]:
        return _cause_to_dict(self)


@dataclass(frozen=True)
class ExecutionCauseKey:
    cause_kind: str
    comparison_domain: Tuple[Any, ...]
    logical_query_identity: Tuple[Any, ...]
    execution_semantics_identity: Tuple[Any, ...]
    schema_version: int = CAUSE_IDENTITY_SCHEMA_VERSION
    identity_scope: str = IdentityScope.EXECUTION.value

    def to_dict(self) -> Dict[str, Any]:
        return _cause_to_dict(self)


CauseKey = Union[UnaryCauseKey, RelationalCauseKey, ExecutionCauseKey]


def _cause_to_dict(value: CauseKey) -> Dict[str, Any]:
    payload = dict(value.__dict__)
    return payload


def cause_key_from_dict(payload: Mapping[str, Any]) -> CauseKey:
    scope = str(payload.get("identity_scope") or "")
    version = int(payload.get("schema_version") or 0)
    if version != CAUSE_IDENTITY_SCHEMA_VERSION:
        raise ValueError(f"unsupported typed cause schema: {version}")
    common = {
        "cause_kind": str(payload.get("cause_kind") or ""),
        "schema_version": version,
    }
    if not common["cause_kind"]:
        raise ValueError("typed cause key requires cause_kind")
    if scope == IdentityScope.UNARY.value:
        value = UnaryCauseKey(
            **common,
            binary_content_identity=_tuple(payload.get("binary_content_identity")),
            function_ir_identity=_tuple(payload.get("function_ir_identity")),
            semantic_object_identity=_tuple(payload.get("semantic_object_identity")),
        )
        required = (
            value.binary_content_identity,
            value.function_ir_identity,
            value.semantic_object_identity,
        )
    elif scope == IdentityScope.RELATIONAL.value:
        value = RelationalCauseKey(
            **common,
            comparison_domain=_tuple(payload.get("comparison_domain")),
            left_semantic_object=_tuple(payload.get("left_semantic_object")),
            right_semantic_object=_tuple(payload.get("right_semantic_object")),
            correspondence_contract=_tuple(payload.get("correspondence_contract")),
        )
        required = (
            value.comparison_domain,
            value.left_semantic_object,
            value.right_semantic_object,
            value.correspondence_contract,
        )
    elif scope == IdentityScope.EXECUTION.value:
        value = ExecutionCauseKey(
            **common,
            comparison_domain=_tuple(payload.get("comparison_domain")),
            logical_query_identity=_tuple(payload.get("logical_query_identity")),
            execution_semantics_identity=_tuple(payload.get("execution_semantics_identity")),
        )
        required = (
            value.comparison_domain,
            value.logical_query_identity,
            value.execution_semantics_identity,
        )
    else:
        raise ValueError(f"unsupported identity scope: {scope}")
    if not all(required):
        raise ValueError(f"incomplete {scope} typed cause key")
    return value


def canonical_cause_tuple(value: CauseKey) -> Tuple[Any, ...]:
    payload = value.to_dict()
    return tuple(
        (key, _tuple_item(item))
        for key, item in sorted(payload.items(), key=lambda pair: pair[0])
    )


@dataclass(frozen=True)
class ProofRequirementContract:
    proposition: str
    relation_direction: str = "ordered"
    observation_surface: Tuple[Any, ...] = ()
    active_precondition: Tuple[Any, ...] = ()
    schema_version: int = PROOF_REQUIREMENT_SCHEMA_VERSION

    def to_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version,
            self.proposition,
            self.relation_direction,
            _tuple(self.observation_surface),
            _tuple(self.active_precondition),
        )


@dataclass(frozen=True)
class ProofRequirementId:
    proof_kind: str
    proof_target_key: Tuple[Any, ...]
    proof_contract_key: Tuple[Any, ...]
    schema_version: int = PROOF_REQUIREMENT_SCHEMA_VERSION

    @classmethod
    def create(
        cls,
        proof_kind: Any,
        proof_target_key: Any,
        proof_contract: Union[ProofRequirementContract, Any],
    ) -> "ProofRequirementId":
        contract_key = (
            proof_contract.to_key()
            if isinstance(proof_contract, ProofRequirementContract)
            else _tuple(proof_contract)
        )
        target = _tuple(proof_target_key)
        if not str(proof_kind or "") or not target or not contract_key:
            raise ValueError("proof requirement requires kind, target, and contract")
        return cls(str(proof_kind), target, contract_key)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "proof_kind": self.proof_kind,
            "proof_target_key": self.proof_target_key,
            "proof_contract_key": self.proof_contract_key,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "ProofRequirementId":
        version = int(payload.get("schema_version") or 0)
        if version != PROOF_REQUIREMENT_SCHEMA_VERSION:
            raise ValueError(f"unsupported proof requirement schema: {version}")
        return cls.create(
            payload.get("proof_kind"),
            payload.get("proof_target_key"),
            payload.get("proof_contract_key"),
        )

    def to_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version,
            self.proof_kind,
            self.proof_target_key,
            self.proof_contract_key,
        )


LegacyProofObligationId = Tuple[Any, ...]
