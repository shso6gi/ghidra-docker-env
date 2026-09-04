"""Immutable UNKNOWN Taxonomy v2 data and identity contracts."""

from __future__ import annotations

import hashlib
import json
import weakref
from collections.abc import Mapping as _AbcMapping
from types import MappingProxyType
from dataclasses import dataclass, field, fields, is_dataclass
from enum import Enum
from typing import Any, Iterable, Mapping, Optional, Sequence, Tuple


SCHEMA_VERSION = 2

# canonical_value の fast path 用。Enum は str/int のサブクラスになり得るので、
# 型が「ちょうど」これらのときだけ即返す（Enum は type が一致しない）。
_PRIMITIVE_TYPES = frozenset({str, int, float, bool})


def canonical_value(value: Any) -> Any:
    if value is None or type(value) in _PRIMITIVE_TYPES:
        return value
    if isinstance(value, Enum):
        return value.value
    if hasattr(value, "to_authority_dict"):
        return canonical_value(value.to_authority_dict())
    if is_dataclass(value):
        return tuple(
            (item.name, canonical_value(getattr(value, item.name))) for item in fields(value)
        )
    if isinstance(value, _AbcMapping):
        return tuple(
            (str(key), canonical_value(child))
            for key, child in sorted(value.items(), key=lambda item: str(item[0]))
        )
    if isinstance(value, (list, tuple)):
        return tuple(canonical_value(child) for child in value)
    if isinstance(value, (set, frozenset)):
        children = [canonical_value(child) for child in value]
        return tuple(sorted(children, key=authority_digest))
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    raise TypeError(f"unsupported authority value: {type(value).__name__}")


def authority_digest(value: Any) -> str:
    encoded = json.dumps(
        canonical_value(value), sort_keys=True, separators=(",", ":"), ensure_ascii=False
    )
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def freeze_authority_value(value: Any) -> Any:
    """authority ペイロード内の可変コンテナを不変な等価物へ再帰的に変換する。

    dict / Mapping → 新しいコピーの ``MappingProxyType``、list / tuple → tuple、
    set / frozenset → frozenset。``canonical_value`` の出力（したがって
    digest）は変わらない。frozen dataclass は同一オブジェクトのまま返す
    （factory の所有権チェックは同一性で行われるため）。各 dataclass は自分の
    コンテナ型フィールドを ``__post_init__`` で凍結する責任を持つ。
    """
    if value is None or type(value) in _PRIMITIVE_TYPES or isinstance(value, Enum):
        return value
    if isinstance(value, _AbcMapping):
        return MappingProxyType({
            key: freeze_authority_value(child) for key, child in value.items()
        })
    if isinstance(value, (list, tuple)):
        return tuple(freeze_authority_value(child) for child in value)
    if isinstance(value, (set, frozenset)):
        return frozenset(freeze_authority_value(child) for child in value)
    return value


def assert_deep_immutable(value: Any, path: str = "$") -> None:
    """``value`` が深く不変（プリミティブ / Enum / MappingProxyType / tuple /
    frozenset / frozen dataclass の入れ子のみ）でなければ ``TypeError``。

    封印済み authority オブジェクトの validate() 結果をプロセス内でキャッシュ
    してよいかを判定する不変条件。frozen=True はトップレベルの再代入しか防が
    ないので、内部に dict / list / set が残っていればここで弾く。
    """
    if value is None or isinstance(value, (str, int, float, bool, Enum)):
        # str/int/float/bool のサブクラス（JPype の JInt など）も不変。
        return
    if isinstance(value, MappingProxyType):
        for key, child in value.items():
            assert_deep_immutable(child, f"{path}.{key}")
        return
    if type(value) is tuple:
        for index, child in enumerate(value):
            assert_deep_immutable(child, f"{path}[{index}]")
        return
    if type(value) is frozenset:
        for child in value:
            assert_deep_immutable(child, f"{path}{{}}")
        return
    if is_dataclass(value) and not isinstance(value, type):
        params = getattr(value, "__dataclass_params__", None)
        if params is None or not params.frozen:
            raise TypeError(f"authority value is a mutable dataclass at {path}: {type(value).__name__}")
        for item in fields(value):
            assert_deep_immutable(getattr(value, item.name), f"{path}.{item.name}")
        return
    raise TypeError(f"authority value is mutable at {path}: {type(value).__name__}")


class ValidatedOnceRegistry:
    """封印済み（frozen）authority オブジェクトの validate() 結果をプロセス内で
    1 回だけ有効にする識別子ベースの記録（Issue #14）。

    記録できるのは ``assert_deep_immutable`` を満たすオブジェクトだけ。frozen
    dataclass でも内部の dict などが後から書き換えられると、以前は validate()
    が digest 不一致で検出していた改変を見逃すため、深い不変性を記録の前提に
    する。

    ``SealedEventStream`` / ``CauseLifecycleSnapshot`` /
    ``VerifiedLifecycleProjection`` は封印後に変化しない値オブジェクトだが、
    producer-site の projection を発行するたびに全イベントを再ダイジェストして
    いたため、finalize が O(sites × events) になっていた。同一オブジェクトの
    2 回目以降の validate() を O(1) にする。オブジェクトは弱参照で追跡し、回収
    されれば記録も消えるので id の再利用で誤判定しない。
    """

    def __init__(self) -> None:
        self._refs: dict[int, weakref.ref] = {}

    def is_validated(self, obj: Any) -> bool:
        ref = self._refs.get(id(obj))
        return ref is not None and ref() is obj

    def mark(self, obj: Any) -> bool:
        """検証済みとして記録する。深く不変でないオブジェクト（内部に dict /
        list / set が残る）や弱参照を取れないものは記録せず ``False`` を返し、
        以後も毎回検証される。"""
        try:
            assert_deep_immutable(obj)
        except TypeError:
            return False
        key = id(obj)
        try:
            self._refs[key] = weakref.ref(obj, lambda _ref, key=key: self._refs.pop(key, None))
        except TypeError:
            return False
        return True

    def __len__(self) -> int:
        return len(self._refs)


VALIDATED_ONCE = ValidatedOnceRegistry()


class IdentityScope(str, Enum):
    UNARY = "UNARY"
    RELATIONAL = "RELATIONAL"


class RecoveryAddressability(str, Enum):
    REQUIREMENT_REQUIRED = "REQUIREMENT_REQUIRED"
    REQUIREMENT_OPTIONAL = "REQUIREMENT_OPTIONAL"
    NO_PROOF_RECOVERY = "NO_PROOF_RECOVERY"


class ExpressionKind(str, Enum):
    REQUIREMENT_SLOT = "REQUIREMENT_SLOT"
    ALL_OF = "ALL_OF"
    ANY_OF = "ANY_OF"


class TransformationKind(str, Enum):
    REPLACEMENT = "REPLACEMENT"
    REFINEMENT = "REFINEMENT"
    COALESCENCE = "COALESCENCE"


class Outcome(str, Enum):
    EQUIVALENT = "EQUIVALENT"
    NOT_EQ = "NOT_EQ"
    UNKNOWN = "UNKNOWN"
    TIMEOUT = "TIMEOUT"
    ERROR = "ERROR"


# Single public authority for the process exit associated with each canonical
# outcome.  Compatibility surfaces may alias this mapping, but must not copy it.
CLI_EXIT_CODE_BY_OUTCOME: Mapping[Outcome, int] = {
    Outcome.EQUIVALENT: 0,
    Outcome.NOT_EQ: 1,
    Outcome.UNKNOWN: 2,
    Outcome.TIMEOUT: 3,
    Outcome.ERROR: 4,
}

BATCH_RESUME_DISPOSITION_BY_OUTCOME: Mapping[Outcome, str] = {
    Outcome.EQUIVALENT: "COMPLETE_EQ",
    Outcome.NOT_EQ: "COMPLETE_NOT_EQ",
    Outcome.UNKNOWN: "RESUMABLE_SEMANTIC_BACKLOG",
    Outcome.TIMEOUT: "RESUMABLE_DEADLINE_BACKLOG",
    Outcome.ERROR: "FAILED_INFRASTRUCTURE",
}


class CensusMode(str, Enum):
    V2_CANONICAL = "V2_CANONICAL"
    LEGACY_DIAGNOSTIC = "LEGACY_DIAGNOSTIC"
    MIGRATION_COMPARISON = "MIGRATION_COMPARISON"


class ResultKind(str, Enum):
    V2_NATIVE = "V2_NATIVE"
    LEGACY = "LEGACY"


@dataclass(frozen=True)
class ReasonDefinition:
    reason_id: str
    domain: str
    reason_class: str
    decision_effect: str
    allowed_target_kinds: frozenset[str]
    required_evidence_contract: Tuple[str, ...]
    allowed_proof_kinds: frozenset[str]
    terminal_eligibility: bool
    canonicalization_policy_id: str
    recovery_addressability: RecoveryAddressability
    schema_version: int = SCHEMA_VERSION

    def __post_init__(self) -> None:
        object.__setattr__(
            self, "recovery_addressability", RecoveryAddressability(self.recovery_addressability)
        )
        object.__setattr__(self, "allowed_target_kinds", frozenset(self.allowed_target_kinds))
        object.__setattr__(self, "required_evidence_contract", tuple(self.required_evidence_contract))
        object.__setattr__(self, "allowed_proof_kinds", frozenset(self.allowed_proof_kinds))
        if type(self.schema_version) is not int or self.schema_version != SCHEMA_VERSION:
            raise ValueError("unsupported reason definition schema")
        if not all(type(value) is str and value for value in (
            self.reason_id,
            self.domain,
            self.reason_class,
            self.decision_effect,
            self.canonicalization_policy_id,
        )):
            raise TypeError("reason definition identity fields must be non-empty exact strings")
        if type(self.terminal_eligibility) is not bool:
            raise TypeError("reason terminal eligibility must be an exact boolean")
        for name, values in (
            ("allowed target kinds", self.allowed_target_kinds),
            ("required evidence", self.required_evidence_contract),
            ("allowed proof kinds", self.allowed_proof_kinds),
        ):
            if any(type(value) is not str or not value for value in values):
                raise TypeError(f"reason {name} must contain non-empty exact strings")
        if not self.allowed_target_kinds:
            raise ValueError("reason definition needs an allowed target kind")
        if (
            self.recovery_addressability == RecoveryAddressability.NO_PROOF_RECOVERY
            and self.allowed_proof_kinds
        ):
            raise ValueError("NO_PROOF_RECOVERY cannot allow proof kinds")


_CAUSE_ID_FACTORY_TOKEN = object()
_CAUSE_ID_CODEC_TOKEN = object()


@dataclass(frozen=True, init=False)
class CauseIdV2:
    identity_scope: IdentityScope
    reason_id: str
    canonical_target_key: Any
    missing_semantic_fact: Any
    semantic_proposition_digest: str
    value: str
    schema_version: int = SCHEMA_VERSION

    def __init__(
        self,
        identity_scope: IdentityScope,
        reason_id: str,
        canonical_target_key: Any,
        missing_semantic_fact: Any,
        semantic_proposition_digest: str,
        value: str,
        schema_version: int = SCHEMA_VERSION,
        *,
        _factory_token: object = None,
        _codec_token: object = None,
    ) -> None:
        if (
            _factory_token is not _CAUSE_ID_FACTORY_TOKEN
            and _codec_token is not _CAUSE_ID_CODEC_TOKEN
        ):
            raise ValueError("cause identities are registry-factory or strict-codec issued")
        object.__setattr__(self, "identity_scope", IdentityScope(identity_scope))
        object.__setattr__(self, "reason_id", reason_id)
        object.__setattr__(self, "canonical_target_key", canonical_target_key)
        object.__setattr__(self, "missing_semantic_fact", missing_semantic_fact)
        object.__setattr__(self, "semantic_proposition_digest", semantic_proposition_digest)
        object.__setattr__(self, "value", value)
        object.__setattr__(self, "schema_version", schema_version)
        if type(self.schema_version) is not int or self.schema_version != SCHEMA_VERSION:
            raise ValueError("unsupported cause identity schema")
        target = canonical_value(self.canonical_target_key)
        missing = canonical_value(self.missing_semantic_fact)
        object.__setattr__(self, "canonical_target_key", target)
        object.__setattr__(self, "missing_semantic_fact", missing)
        expected = authority_digest(
            {
                "schema_version": self.schema_version,
                "identity_scope": self.identity_scope.value,
                "reason_id": self.reason_id,
                "canonical_target_key": target,
                "missing_semantic_fact": missing,
                "semantic_proposition_digest": self.semantic_proposition_digest,
            }
        )
        if self.value != expected:
            raise ValueError("cause ID value does not match semantic identity fields")

    @classmethod
    def create(
        cls,
        *,
        identity_scope: IdentityScope,
        reason_id: str,
        canonical_target_key: Any,
        missing_semantic_fact: Any,
        semantic_proposition: Any,
        observation_surface: Any,
        active_semantic_precondition: Any,
        correspondence_contract: Any,
        _factory_token: object = None,
    ) -> "CauseIdV2":
        if _factory_token is not _CAUSE_ID_FACTORY_TOKEN:
            raise ValueError("cause identities are issued only by the sealed registry factory")
        target = canonical_value(canonical_target_key)
        missing = canonical_value(missing_semantic_fact)
        proposition = {
            "semantic_proposition": semantic_proposition,
            "observation_surface": observation_surface,
            "active_semantic_precondition": active_semantic_precondition,
            "identity_scope": identity_scope.value,
            "canonical_target_key": target,
            "correspondence_contract": correspondence_contract,
        }
        proposition_digest = authority_digest(proposition)
        value = authority_digest(
            {
                "schema_version": SCHEMA_VERSION,
                "identity_scope": identity_scope.value,
                "reason_id": reason_id,
                "canonical_target_key": target,
                "missing_semantic_fact": missing,
                "semantic_proposition_digest": proposition_digest,
            }
        )
        return cls(
            identity_scope=identity_scope,
            reason_id=reason_id,
            canonical_target_key=target,
            missing_semantic_fact=missing,
            semantic_proposition_digest=proposition_digest,
            value=value,
            _factory_token=_CAUSE_ID_FACTORY_TOKEN,
        )

    @classmethod
    def from_persisted(cls, *, _codec_token: object = None, **payload: Any) -> "CauseIdV2":
        if _codec_token is not _CAUSE_ID_CODEC_TOKEN:
            raise ValueError("persisted cause identities require the strict codec")
        return cls(**payload, _codec_token=_CAUSE_ID_CODEC_TOKEN)


@dataclass(frozen=True)
class RequirementSlotDefinition:
    name: str
    allowed_proof_kinds: frozenset[str]

    def __post_init__(self) -> None:
        object.__setattr__(self, "allowed_proof_kinds", frozenset(self.allowed_proof_kinds))
        if type(self.name) is not str or not self.name or not self.allowed_proof_kinds:
            raise ValueError("requirement slot needs a name and compatible proof kind")
        if any(type(value) is not str or not value for value in self.allowed_proof_kinds):
            raise TypeError("requirement slot proof kinds must be non-empty exact strings")


_EXPRESSION_FACTORY_TOKEN = object()


@dataclass(frozen=True, init=False)
class SatisfactionExpression:
    kind: ExpressionKind
    slot_name: Optional[str] = None
    children: Tuple["SatisfactionExpression", ...] = ()

    def __init__(
        self,
        kind: ExpressionKind,
        *,
        slot_name: Optional[str] = None,
        children: Sequence["SatisfactionExpression"] = (),
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _EXPRESSION_FACTORY_TOKEN:
            raise ValueError("satisfaction expressions are issued only by typed factories")
        object.__setattr__(self, "kind", ExpressionKind(kind))
        object.__setattr__(self, "slot_name", slot_name)
        object.__setattr__(self, "children", tuple(children))
        if self.kind == ExpressionKind.REQUIREMENT_SLOT:
            if not self.slot_name or self.children:
                raise ValueError("slot expression requires only slot_name")
        elif self.slot_name is not None or len(self.children) < 2:
            raise ValueError("ALL_OF/ANY_OF require at least two children")
        elif any(child.kind == self.kind for child in self.children):
            raise ValueError("same-operator nesting must be flattened by the factory")
        elif tuple(child.digest for child in self.children) != tuple(
            sorted({child.digest for child in self.children})
        ):
            raise ValueError("operator children must be sorted and deduplicated")

    @property
    def digest(self) -> str:
        return authority_digest(self.to_authority_dict())

    def to_authority_dict(self) -> Mapping[str, Any]:
        if self.kind == ExpressionKind.REQUIREMENT_SLOT:
            return {"kind": self.kind.value, "slot_name": self.slot_name}
        return {
            "kind": self.kind.value,
            "children": tuple(child.to_authority_dict() for child in self.children),
        }

    def slot_names(self) -> frozenset[str]:
        if self.kind == ExpressionKind.REQUIREMENT_SLOT:
            return frozenset((str(self.slot_name),))
        return frozenset(name for child in self.children for name in child.slot_names())


def requirement_slot(name: str) -> SatisfactionExpression:
    return SatisfactionExpression(
        ExpressionKind.REQUIREMENT_SLOT,
        slot_name=name,
        _factory_token=_EXPRESSION_FACTORY_TOKEN,
    )


def _operator_expression(
    kind: ExpressionKind, children: Iterable[SatisfactionExpression]
) -> SatisfactionExpression:
    flattened = []
    for child in children:
        if child.kind == kind:
            flattened.extend(child.children)
        else:
            flattened.append(child)
    by_digest = {child.digest: child for child in flattened}
    normalized = tuple(by_digest[key] for key in sorted(by_digest))
    if not normalized:
        raise ValueError("empty satisfaction operator is forbidden")
    if len(normalized) == 1:
        return normalized[0]
    return SatisfactionExpression(
        kind, children=normalized, _factory_token=_EXPRESSION_FACTORY_TOKEN
    )


def all_of(*children: SatisfactionExpression) -> SatisfactionExpression:
    return _operator_expression(ExpressionKind.ALL_OF, children)


def any_of(*children: SatisfactionExpression) -> SatisfactionExpression:
    return _operator_expression(ExpressionKind.ANY_OF, children)


@dataclass(frozen=True)
class SatisfactionContractDefinition:
    contract_definition_id: str
    contract_version: int
    requirement_slots: Tuple[RequirementSlotDefinition, ...]
    normalized_expression_template: SatisfactionExpression
    normalized_expression_digest: str = field(init=False)
    schema_version: int = SCHEMA_VERSION

    def __post_init__(self) -> None:
        object.__setattr__(self, "requirement_slots", tuple(self.requirement_slots))
        if type(self.schema_version) is not int or self.schema_version != SCHEMA_VERSION:
            raise ValueError("unsupported satisfaction contract schema")
        if type(self.contract_definition_id) is not str or not self.contract_definition_id:
            raise ValueError("invalid satisfaction contract identity")
        if type(self.contract_version) is not int or self.contract_version < 1:
            raise TypeError("satisfaction contract version must be a positive exact integer")
        if any(type(slot) is not RequirementSlotDefinition for slot in self.requirement_slots):
            raise TypeError("satisfaction contract slots must be exact typed definitions")
        if type(self.normalized_expression_template) is not SatisfactionExpression:
            raise TypeError("satisfaction contract expression must be factory-issued")
        names = tuple(slot.name for slot in self.requirement_slots)
        if len(names) != len(set(names)):
            raise ValueError("duplicate requirement slot")
        if frozenset(names) != self.normalized_expression_template.slot_names():
            raise ValueError("expression slots differ from declared requirement slots")
        object.__setattr__(
            self,
            "normalized_expression_digest",
            self.normalized_expression_template.digest,
        )


@dataclass(frozen=True)
class ProofRequirement:
    requirement_id: str
    proof_kind: str
    semantic_target_key: Any

    def __post_init__(self) -> None:
        if not all(type(value) is str and value for value in (
            self.requirement_id, self.proof_kind,
        )):
            raise ValueError("proof requirement identity is incomplete")
        object.__setattr__(self, "semantic_target_key", canonical_value(self.semantic_target_key))


_BOUND_CONTRACT_FACTORY_TOKEN = object()


@dataclass(frozen=True, init=False)
class BoundSatisfactionContract:
    contract_definition_id: str
    contract_version: int
    normalized_expression_digest: str
    slot_bindings: Tuple[Tuple[str, ProofRequirement], ...]
    bound_expression_digest: str

    def __init__(
        self,
        contract_definition_id: str,
        contract_version: int,
        normalized_expression_digest: str,
        slot_bindings: Sequence[Tuple[str, ProofRequirement]],
        bound_expression_digest: str,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _BOUND_CONTRACT_FACTORY_TOKEN:
            raise ValueError("bound satisfaction contracts are registry-factory issued")
        ordered = tuple(slot_bindings)
        object.__setattr__(self, "contract_definition_id", contract_definition_id)
        object.__setattr__(self, "contract_version", int(contract_version))
        object.__setattr__(self, "normalized_expression_digest", normalized_expression_digest)
        object.__setattr__(self, "slot_bindings", ordered)
        object.__setattr__(self, "bound_expression_digest", bound_expression_digest)
        if tuple(name for name, _ in ordered) != tuple(sorted(name for name, _ in ordered)):
            raise ValueError("bound slots are not canonically ordered")
        if len({name for name, _ in ordered}) != len(ordered):
            raise ValueError("duplicate bound slot")
        if len({item.requirement_id for _, item in ordered}) != len(ordered):
            raise ValueError("duplicate bound proof requirement")
        if self.bound_expression_digest != self.recompute_bound_expression_digest():
            raise ValueError("bound expression digest mismatch")

    def requirement_ids(self) -> frozenset[str]:
        return frozenset(requirement.requirement_id for _, requirement in self.slot_bindings)

    def recompute_bound_expression_digest(self) -> str:
        return authority_digest(
            {
                "contract_definition_id": self.contract_definition_id,
                "contract_version": self.contract_version,
                "normalized_expression_digest": self.normalized_expression_digest,
                "slot_bindings": tuple(
                    (name, requirement.requirement_id, requirement.proof_kind)
                    for name, requirement in self.slot_bindings
                ),
            }
        )

    def validate_against(self, definition: SatisfactionContractDefinition) -> None:
        if (
            self.contract_definition_id != definition.contract_definition_id
            or self.contract_version != definition.contract_version
            or self.normalized_expression_digest != definition.normalized_expression_digest
        ):
            raise ValueError("bound satisfaction contract does not match registry definition")
        declared = {slot.name: slot for slot in definition.requirement_slots}
        if set(declared) != {name for name, _ in self.slot_bindings}:
            raise ValueError("bound slots differ from registry definition")
        for name, requirement in self.slot_bindings:
            if requirement.proof_kind not in declared[name].allowed_proof_kinds:
                raise ValueError("bound proof kind is incompatible with registry slot")
        if self.bound_expression_digest != self.recompute_bound_expression_digest():
            raise ValueError("bound expression digest mismatch")


def bind_satisfaction_contract(
    definition: SatisfactionContractDefinition,
    bindings: Mapping[str, ProofRequirement],
    *,
    _factory_token: object = None,
) -> BoundSatisfactionContract:
    if _factory_token is not _SATISFACTION_BINDING_FACTORY_TOKEN:
        raise ValueError("satisfaction bindings are issued only by the sealed registry factory")
    declared = {slot.name: slot for slot in definition.requirement_slots}
    if set(bindings) != set(declared):
        raise ValueError("missing or extra satisfaction slot binding")
    requirement_ids = [requirement.requirement_id for requirement in bindings.values()]
    if len(requirement_ids) != len(set(requirement_ids)):
        raise ValueError("duplicate proof requirement binding")
    for name, requirement in bindings.items():
        if requirement.proof_kind not in declared[name].allowed_proof_kinds:
            raise ValueError(f"incompatible proof kind for slot {name}")
    ordered = tuple((name, bindings[name]) for name in sorted(bindings))
    bound_digest = authority_digest(
        {
            "contract_definition_id": definition.contract_definition_id,
            "contract_version": definition.contract_version,
            "normalized_expression_digest": definition.normalized_expression_digest,
            "slot_bindings": tuple(
                (name, requirement.requirement_id, requirement.proof_kind)
                for name, requirement in ordered
            ),
        }
    )
    return BoundSatisfactionContract(
        definition.contract_definition_id,
        definition.contract_version,
        definition.normalized_expression_digest,
        ordered,
        bound_digest,
        _factory_token=_BOUND_CONTRACT_FACTORY_TOKEN,
    )


_SATISFACTION_BINDING_FACTORY_TOKEN = object()


@dataclass(frozen=True)
class CauseOccurrence:
    occurrence_id: str
    cause_id: CauseIdV2
    reason_id: str
    target_id: str
    target_kind: str
    identity_scope: IdentityScope
    bound_satisfaction_contract_id: Optional[str]
    bound_satisfaction_contract_version: Optional[int]
    normalized_expression_digest: Optional[str]
    bound_expression_digest: Optional[str]
    proof_requirement_ids: Tuple[str, ...]
    evidence_refs: Tuple[str, ...]
    evidence_kind: str
    source_snapshot_fingerprint: str
    producer_id: str
    attempt_id: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "identity_scope", IdentityScope(self.identity_scope))
        object.__setattr__(self, "proof_requirement_ids", tuple(self.proof_requirement_ids))
        object.__setattr__(self, "evidence_refs", tuple(self.evidence_refs))
        if self.reason_id != self.cause_id.reason_id:
            raise ValueError("occurrence reason differs from cause identity")
        if self.identity_scope != self.cause_id.identity_scope:
            raise ValueError("occurrence identity scope differs from cause identity")
        if len(self.proof_requirement_ids) != len(set(self.proof_requirement_ids)):
            raise ValueError("duplicate occurrence proof requirement")
        bound_fields = (
            self.bound_satisfaction_contract_id,
            self.bound_satisfaction_contract_version,
            self.normalized_expression_digest,
            self.bound_expression_digest,
        )
        if any(value is None for value in bound_fields) != all(
            value is None for value in bound_fields
        ):
            raise ValueError("partial satisfaction contract binding")
        if all(value is None for value in bound_fields) and self.proof_requirement_ids:
            raise ValueError("unbound occurrence cannot declare proof requirements")

    def validate_against(
        self,
        reason_definition: ReasonDefinition,
        bound_contract: Optional[BoundSatisfactionContract],
    ) -> None:
        if reason_definition.reason_id != self.reason_id:
            raise ValueError("occurrence reason is not the registry definition")
        if self.target_kind not in reason_definition.allowed_target_kinds:
            raise ValueError("occurrence target kind is not allowed by registry")
        if reason_definition.recovery_addressability == RecoveryAddressability.REQUIREMENT_REQUIRED:
            if bound_contract is None:
                raise ValueError("required occurrence lacks satisfaction binding")
        if reason_definition.recovery_addressability == RecoveryAddressability.NO_PROOF_RECOVERY:
            if bound_contract is not None or self.proof_requirement_ids:
                raise ValueError("NO_PROOF_RECOVERY occurrence cannot bind proof work")
        if bound_contract is None:
            if self.bound_satisfaction_contract_id is not None:
                raise ValueError("occurrence claims a missing bound contract")
            return
        expected = (
            bound_contract.contract_definition_id,
            bound_contract.contract_version,
            bound_contract.normalized_expression_digest,
            bound_contract.bound_expression_digest,
        )
        observed = (
            self.bound_satisfaction_contract_id,
            self.bound_satisfaction_contract_version,
            self.normalized_expression_digest,
            self.bound_expression_digest,
        )
        if observed != expected:
            raise ValueError("occurrence satisfaction fields differ from bound contract")
        if frozenset(self.proof_requirement_ids) != bound_contract.requirement_ids():
            raise ValueError("occurrence proof requirements differ from bound contract")


@dataclass(frozen=True)
class RequirementCompletionReceipt:
    cause_id: str
    occurrence_id: str
    proof_requirement_id: str
    bound_satisfaction_contract_id: str
    bound_satisfaction_contract_version: int
    bound_expression_digest: str
    proof_artifact_digest: str
    applicability_receipt: str

    def __post_init__(self) -> None:
        if not all(type(value) is str and value for value in (
            self.cause_id, self.occurrence_id, self.proof_requirement_id,
            self.bound_satisfaction_contract_id, self.bound_expression_digest,
            self.proof_artifact_digest, self.applicability_receipt,
        )):
            raise TypeError("completion receipt identities must be non-empty exact strings")
        if (
            type(self.bound_satisfaction_contract_version) is not int
            or self.bound_satisfaction_contract_version < 1
        ):
            raise TypeError("completion receipt contract version must be a positive exact integer")

    def validate_against(
        self,
        occurrence: CauseOccurrence,
        bound_contract: BoundSatisfactionContract,
        live_requirement_ids: Iterable[str],
    ) -> None:
        if self.cause_id != occurrence.cause_id.value or self.occurrence_id != occurrence.occurrence_id:
            raise ValueError("completion receipt cause/occurrence mismatch")
        if self.proof_requirement_id not in bound_contract.requirement_ids():
            raise ValueError("completion receipt requirement is undeclared")
        if self.proof_requirement_id not in frozenset(live_requirement_ids):
            raise ValueError("completion receipt requirement is not live")
        expected = (
            bound_contract.contract_definition_id,
            bound_contract.contract_version,
            bound_contract.bound_expression_digest,
        )
        observed = (
            self.bound_satisfaction_contract_id,
            self.bound_satisfaction_contract_version,
            self.bound_expression_digest,
        )
        if observed != expected:
            raise ValueError("completion receipt satisfaction binding mismatch")
        if not self.proof_artifact_digest or not self.applicability_receipt:
            raise ValueError("completion receipt lacks proof/applicability authority")


@dataclass(frozen=True)
class CauseOccurrenceAuthority:
    occurrence: CauseOccurrence
    bound_contract: Optional[BoundSatisfactionContract]

    def __post_init__(self) -> None:
        bound = self.bound_contract
        if bound is None:
            if self.occurrence.bound_satisfaction_contract_id is not None:
                raise ValueError("occurrence authority lacks its claimed bound contract")
            return
        expected = (
            bound.contract_definition_id,
            bound.contract_version,
            bound.normalized_expression_digest,
            bound.bound_expression_digest,
            bound.requirement_ids(),
        )
        observed = (
            self.occurrence.bound_satisfaction_contract_id,
            self.occurrence.bound_satisfaction_contract_version,
            self.occurrence.normalized_expression_digest,
            self.occurrence.bound_expression_digest,
            frozenset(self.occurrence.proof_requirement_ids),
        )
        if observed != expected:
            raise ValueError("occurrence authority differs from bound satisfaction contract")


@dataclass(frozen=True)
class CauseTransformationEvent:
    transformation_kind: TransformationKind
    replaced_occurrence_ids: Tuple[str, ...]
    replacement_occurrence_ids: Tuple[str, ...]
    transformation_proof_receipt_id: str
    recognizing_stage: str
    source_snapshot_fingerprint: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "replaced_occurrence_ids", tuple(self.replaced_occurrence_ids))
        object.__setattr__(self, "replacement_occurrence_ids", tuple(self.replacement_occurrence_ids))
        old = self.replaced_occurrence_ids
        new = self.replacement_occurrence_ids
        if not old or not new or len(old) != len(set(old)) or len(new) != len(set(new)):
            raise ValueError("transformation sets must be non-empty and duplicate-free")
        if set(old).intersection(new):
            raise ValueError("transformation old/new sets must be disjoint")


@dataclass(frozen=True)
class CauseTransformationProofReceipt:
    receipt_id: str
    replaced_occurrence_bindings: Tuple[Tuple[str, str], ...]
    replacement_occurrence_bindings: Tuple[Tuple[str, str], ...]
    requirement_mapping: Tuple[Tuple[str, str], ...]
    source_snapshot_fingerprint: str
    exact_completion_transfer: bool

    def __post_init__(self) -> None:
        object.__setattr__(self, "replaced_occurrence_bindings", tuple(tuple(item) for item in self.replaced_occurrence_bindings))
        object.__setattr__(self, "replacement_occurrence_bindings", tuple(tuple(item) for item in self.replacement_occurrence_bindings))
        object.__setattr__(self, "requirement_mapping", tuple(tuple(item) for item in self.requirement_mapping))

    def validate_event(self, event: CauseTransformationEvent) -> None:
        if self.receipt_id != event.transformation_proof_receipt_id:
            raise ValueError("transformation proof receipt identity mismatch")
        old_ids = tuple(binding[0] for binding in self.replaced_occurrence_bindings)
        new_ids = tuple(binding[0] for binding in self.replacement_occurrence_bindings)
        if set(old_ids) != set(event.replaced_occurrence_ids):
            raise ValueError("transformation receipt does not bind every replaced occurrence")
        if set(new_ids) != set(event.replacement_occurrence_ids):
            raise ValueError("transformation receipt does not bind every replacement occurrence")
        if len(old_ids) != len(set(old_ids)) or len(new_ids) != len(set(new_ids)):
            raise ValueError("transformation receipt contains duplicate occurrence bindings")
        if self.source_snapshot_fingerprint != event.source_snapshot_fingerprint:
            raise ValueError("transformation snapshot mismatch")
        if self.exact_completion_transfer:
            old_requirements = [old for old, _ in self.requirement_mapping]
            new_requirements = [new for _, new in self.requirement_mapping]
            if (
                not self.requirement_mapping
                or len(old_requirements) != len(set(old_requirements))
                or len(new_requirements) != len(set(new_requirements))
            ):
                raise ValueError("completion transfer requires an exact one-to-one mapping")


@dataclass(frozen=True, order=True)
class CActiveBaseRow:
    result_occurrence_id: str
    occurrence_id: str
    cause_id: str
    reason_id: str
    domain: str
    decision_effect: str
    target_kind: str

    def __post_init__(self) -> None:
        if not all(type(value) is str and value for value in (
            self.result_occurrence_id, self.occurrence_id, self.cause_id,
            self.reason_id, self.domain, self.decision_effect, self.target_kind,
        )):
            raise TypeError("active-cause relation fields must be non-empty exact strings")


@dataclass(frozen=True, order=True)
class QOpenBaseRow:
    result_occurrence_id: str
    occurrence_id: str
    cause_id: str
    proof_requirement_id: str
    proof_kind: str
    semantic_target_digest: str

    def __post_init__(self) -> None:
        if not all(type(value) is str and value for value in (
            self.result_occurrence_id, self.occurrence_id, self.cause_id,
            self.proof_requirement_id, self.proof_kind,
            self.semantic_target_digest,
        )):
            raise TypeError("open-requirement relation fields must be non-empty exact strings")


@dataclass(frozen=True, order=True)
class BlockerEligibilityBaseRow:
    """One blocker-eligible observation; cause_id is absent until typed."""

    result_occurrence_id: str
    blocker_occurrence_id: str
    cause_id: Optional[str]

    def __post_init__(self) -> None:
        if not all(type(value) is str and value for value in (
            self.result_occurrence_id, self.blocker_occurrence_id,
        )):
            raise TypeError("blocker eligibility identity must use exact strings")
        if self.cause_id is not None and (type(self.cause_id) is not str or not self.cause_id):
            raise TypeError("typed cause identity must be a non-empty exact string")


@dataclass(frozen=True)
class VerifiedLifecycleProjection:
    result_occurrence_id: str
    snapshot_digest: str
    c_active_base: Tuple[CActiveBaseRow, ...]
    q_open_base: Tuple[QOpenBaseRow, ...]
    blocker_eligibility_base: Tuple[BlockerEligibilityBaseRow, ...]
    c_active_base_digest: str
    q_open_base_digest: str
    blocker_eligibility_base_digest: str
    semantic_cause_projection_digest: str
    satisfaction_projection: Any
    satisfaction_projection_digest: str
    lifecycle_projection_digest: str

    @classmethod
    def seal(
        cls,
        *,
        result_occurrence_id: str,
        snapshot_digest: str,
        c_active_base: Sequence[CActiveBaseRow],
        q_open_base: Sequence[QOpenBaseRow],
        blocker_eligibility_base: Sequence[BlockerEligibilityBaseRow],
        satisfaction_projection: Any,
    ) -> "VerifiedLifecycleProjection":
        if type(result_occurrence_id) is not str or not result_occurrence_id:
            raise TypeError("lifecycle result occurrence ID must be a non-empty exact string")
        if type(snapshot_digest) is not str or not snapshot_digest:
            raise TypeError("lifecycle snapshot digest must be a non-empty exact string")
        causes = tuple(sorted(c_active_base))
        requirements = tuple(sorted(q_open_base))
        eligibility = tuple(sorted(
            blocker_eligibility_base,
            key=lambda row: (
                row.result_occurrence_id,
                row.blocker_occurrence_id,
                row.cause_id or "",
            ),
        ))
        cause_keys = [
            (row.result_occurrence_id, row.occurrence_id, row.cause_id) for row in causes
        ]
        requirement_keys = [
            (
                row.result_occurrence_id,
                row.occurrence_id,
                row.cause_id,
                row.proof_requirement_id,
            )
            for row in requirements
        ]
        eligibility_keys = [
            (row.result_occurrence_id, row.blocker_occurrence_id) for row in eligibility
        ]
        if len(cause_keys) != len(set(cause_keys)):
            raise ValueError("duplicate active-cause relation key")
        if len(requirement_keys) != len(set(requirement_keys)):
            raise ValueError("duplicate open-requirement relation key")
        if len(eligibility_keys) != len(set(eligibility_keys)):
            raise ValueError("duplicate blocker-eligibility relation key")
        if any(
            row.result_occurrence_id != result_occurrence_id
            for row in (*causes, *requirements, *eligibility)
        ):
            raise ValueError("base relation row belongs to a different result occurrence")
        cause_key_set = set(cause_keys)
        for row in requirements:
            if (row.result_occurrence_id, row.occurrence_id, row.cause_id) not in cause_key_set:
                raise ValueError("open requirement lacks matching active cause occurrence")
            if not row.proof_requirement_id:
                raise ValueError("NULL/empty proof requirement row is forbidden")
        eligibility_by_occurrence = {
            (row.result_occurrence_id, row.blocker_occurrence_id): row.cause_id
            for row in eligibility
        }
        for row in causes:
            if eligibility_by_occurrence.get(
                (row.result_occurrence_id, row.occurrence_id)
            ) != row.cause_id:
                raise ValueError("active cause lacks matching typed blocker eligibility row")
        c_digest = authority_digest(causes)
        q_digest = authority_digest(requirements)
        eligibility_digest = authority_digest(eligibility)
        semantic_digest = authority_digest(
            tuple((row.occurrence_id, row.cause_id, row.reason_id) for row in causes)
        )
        canonical_satisfaction = canonical_value(satisfaction_projection)
        satisfaction_digest = authority_digest(canonical_satisfaction)
        lifecycle_digest = authority_digest(
            {
                "snapshot_digest": snapshot_digest,
                "result_occurrence_id": result_occurrence_id,
                "c_active_base_digest": c_digest,
                "q_open_base_digest": q_digest,
                "blocker_eligibility_base_digest": eligibility_digest,
                "semantic_cause_projection_digest": semantic_digest,
                "satisfaction_projection_digest": satisfaction_digest,
            }
        )
        return cls(
            result_occurrence_id,
            snapshot_digest,
            causes,
            requirements,
            eligibility,
            c_digest,
            q_digest,
            eligibility_digest,
            semantic_digest,
            canonical_satisfaction,
            satisfaction_digest,
            lifecycle_digest,
        )

    def validate(self) -> None:
        if VALIDATED_ONCE.is_validated(self):
            return
        rebuilt = VerifiedLifecycleProjection.seal(
            result_occurrence_id=self.result_occurrence_id,
            snapshot_digest=self.snapshot_digest,
            c_active_base=self.c_active_base,
            q_open_base=self.q_open_base,
            blocker_eligibility_base=self.blocker_eligibility_base,
            satisfaction_projection=self.satisfaction_projection,
        )
        if rebuilt != self:
            raise ValueError("verified lifecycle projection digest or relation mismatch")
        VALIDATED_ONCE.mark(self)


_PREFIX_PROJECTION_FACTORY_TOKEN = object()


@dataclass(frozen=True)
class VerifiedLifecyclePrefixProjection:
    result_occurrence_id: str
    snapshot_digest: str
    c_active_base: Tuple[CActiveBaseRow, ...]
    q_open_base: Tuple[QOpenBaseRow, ...]
    blocker_eligibility_base: Tuple[BlockerEligibilityBaseRow, ...]
    q_open_base_digest: str
    satisfaction_projection: Any
    event_stream_prefix_digest: str
    prefix_projection_digest: str
    finality: str = "PREFIX"
    _factory_token: object = field(default=None, repr=False, compare=False)

    @classmethod
    def _issue(
        cls,
        projection: VerifiedLifecycleProjection,
        event_stream_prefix_digest: str,
        *,
        _factory_token: object = None,
    ) -> "VerifiedLifecyclePrefixProjection":
        if _factory_token is not _PREFIX_PROJECTION_FACTORY_TOKEN:
            raise TypeError("lifecycle prefix projection must be reducer issued")
        projection.validate()
        if type(event_stream_prefix_digest) is not str or not event_stream_prefix_digest:
            raise TypeError("lifecycle prefix stream digest is incomplete")
        digest = authority_digest({
            "finality": "PREFIX",
            "event_stream_prefix_digest": event_stream_prefix_digest,
            "result_occurrence_id": projection.result_occurrence_id,
            "snapshot_digest": projection.snapshot_digest,
            "c_active_base_digest": projection.c_active_base_digest,
            "q_open_base_digest": projection.q_open_base_digest,
            "blocker_eligibility_base_digest": (
                projection.blocker_eligibility_base_digest
            ),
            "satisfaction_projection_digest": (
                projection.satisfaction_projection_digest
            ),
        })
        return cls(
            projection.result_occurrence_id,
            projection.snapshot_digest,
            projection.c_active_base,
            projection.q_open_base,
            projection.blocker_eligibility_base,
            projection.q_open_base_digest,
            projection.satisfaction_projection,
            event_stream_prefix_digest,
            digest,
            _factory_token=_factory_token,
        )

    def validate(self) -> None:
        if (
            self._factory_token is not _PREFIX_PROJECTION_FACTORY_TOKEN
            or self.finality != "PREFIX"
        ):
            raise TypeError("lifecycle prefix projection is not reducer issued")
        rebuilt = VerifiedLifecycleProjection.seal(
            result_occurrence_id=self.result_occurrence_id,
            snapshot_digest=self.snapshot_digest,
            c_active_base=self.c_active_base,
            q_open_base=self.q_open_base,
            blocker_eligibility_base=self.blocker_eligibility_base,
            satisfaction_projection=self.satisfaction_projection,
        )
        expected = authority_digest({
            "finality": "PREFIX",
            "event_stream_prefix_digest": self.event_stream_prefix_digest,
            "result_occurrence_id": rebuilt.result_occurrence_id,
            "snapshot_digest": rebuilt.snapshot_digest,
            "c_active_base_digest": rebuilt.c_active_base_digest,
            "q_open_base_digest": rebuilt.q_open_base_digest,
            "blocker_eligibility_base_digest": rebuilt.blocker_eligibility_base_digest,
            "satisfaction_projection_digest": rebuilt.satisfaction_projection_digest,
        })
        if (
            self.q_open_base_digest != rebuilt.q_open_base_digest
            or self.prefix_projection_digest != expected
        ):
            raise ValueError("lifecycle prefix projection digest mismatch")
