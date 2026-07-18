"""Sealed v2 registries and the only production-facing identity factories."""

from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Iterable, Mapping

from .contracts import (
    BoundSatisfactionContract,
    CauseIdV2,
    IdentityScope,
    ProofRequirement,
    ReasonDefinition,
    SatisfactionContractDefinition,
    _CAUSE_ID_FACTORY_TOKEN,
    _SATISFACTION_BINDING_FACTORY_TOKEN,
    bind_satisfaction_contract,
)


_REASON_REGISTRY_FACTORY_TOKEN = object()
_RECOVERY_REGISTRY_FACTORY_TOKEN = object()


@dataclass(frozen=True, init=False)
class SealedReasonRegistry:
    _definitions: Mapping[str, ReasonDefinition]

    def __init__(self, definitions: Mapping[str, ReasonDefinition], *, _factory_token=None):
        if _factory_token is not _REASON_REGISTRY_FACTORY_TOKEN:
            raise ValueError("sealed reason registries are factory-issued")
        object.__setattr__(self, "_definitions", MappingProxyType(dict(definitions)))

    @classmethod
    def build(cls, definitions: Iterable[ReasonDefinition]) -> "SealedReasonRegistry":
        indexed: dict[str, ReasonDefinition] = {}
        for definition in definitions:
            if type(definition) is not ReasonDefinition:
                raise TypeError("sealed reason registry accepts exact definitions only")
            if definition.reason_id in indexed:
                raise ValueError(f"duplicate v2 reason ID: {definition.reason_id}")
            indexed[definition.reason_id] = definition
        if not indexed:
            raise ValueError("v2 reason registry cannot be empty")
        return cls(
            dict(sorted(indexed.items())),
            _factory_token=_REASON_REGISTRY_FACTORY_TOKEN,
        )

    def get(self, reason_id: str) -> ReasonDefinition:
        if not isinstance(reason_id, str) or reason_id not in self._definitions:
            raise KeyError(f"unknown exact v2 reason ID: {reason_id!r}")
        return self._definitions[reason_id]

    def snapshot(self) -> tuple[ReasonDefinition, ...]:
        return tuple(self._definitions[key] for key in sorted(self._definitions))


@dataclass(frozen=True, init=False)
class SealedRecoveryRegistry:
    _definitions: Mapping[tuple[str, int], SatisfactionContractDefinition]

    def __init__(
        self,
        definitions: Mapping[tuple[str, int], SatisfactionContractDefinition],
        *,
        _factory_token=None,
    ):
        if _factory_token is not _RECOVERY_REGISTRY_FACTORY_TOKEN:
            raise ValueError("sealed recovery registries are factory-issued")
        object.__setattr__(self, "_definitions", MappingProxyType(dict(definitions)))

    @classmethod
    def build(
        cls, definitions: Iterable[SatisfactionContractDefinition]
    ) -> "SealedRecoveryRegistry":
        indexed: dict[tuple[str, int], SatisfactionContractDefinition] = {}
        for definition in definitions:
            if type(definition) is not SatisfactionContractDefinition:
                raise TypeError("sealed recovery registry accepts exact definitions only")
            key = (definition.contract_definition_id, definition.contract_version)
            if key in indexed:
                raise ValueError(f"duplicate satisfaction contract: {key!r}")
            indexed[key] = definition
        if not indexed:
            raise ValueError("v2 recovery registry cannot be empty")
        return cls(
            dict(sorted(indexed.items())),
            _factory_token=_RECOVERY_REGISTRY_FACTORY_TOKEN,
        )

    def get(self, contract_definition_id: str, contract_version: int) -> SatisfactionContractDefinition:
        key = (contract_definition_id, contract_version)
        if key not in self._definitions:
            raise KeyError(f"unknown exact satisfaction contract: {key!r}")
        return self._definitions[key]

    def snapshot(self) -> tuple[SatisfactionContractDefinition, ...]:
        return tuple(self._definitions[key] for key in sorted(self._definitions))


@dataclass(frozen=True)
class SemanticCauseIdentityFactory:
    registry: SealedReasonRegistry

    def create(
        self,
        *,
        reason_id: str,
        identity_scope: IdentityScope,
        target_kind: str,
        canonical_target_key: Any,
        missing_semantic_fact: Any,
        semantic_proposition: Any,
        observation_surface: Any,
        active_semantic_precondition: Any,
        correspondence_contract: Any,
    ) -> CauseIdV2:
        definition = self.registry.get(reason_id)
        if target_kind not in definition.allowed_target_kinds:
            raise ValueError("cause target kind is not allowed by sealed reason registry")
        return CauseIdV2.create(
            identity_scope=identity_scope,
            reason_id=reason_id,
            canonical_target_key=canonical_target_key,
            missing_semantic_fact=missing_semantic_fact,
            semantic_proposition=semantic_proposition,
            observation_surface=observation_surface,
            active_semantic_precondition=active_semantic_precondition,
            correspondence_contract=correspondence_contract,
            _factory_token=_CAUSE_ID_FACTORY_TOKEN,
        )


@dataclass(frozen=True)
class SatisfactionBindingFactory:
    registry: SealedRecoveryRegistry

    def bind(
        self,
        *,
        contract_definition_id: str,
        contract_version: int,
        bindings: Mapping[str, ProofRequirement],
    ) -> BoundSatisfactionContract:
        definition = self.registry.get(contract_definition_id, contract_version)
        bound = bind_satisfaction_contract(
            definition,
            bindings,
            _factory_token=_SATISFACTION_BINDING_FACTORY_TOKEN,
        )
        bound.validate_against(definition)
        return bound
