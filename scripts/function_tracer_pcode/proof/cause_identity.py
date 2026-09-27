# -*- coding: utf-8 -*-
"""Typed identities for UNKNOWN root causes and proof requirements.

These models deliberately contain semantic identity only.  Run ids, paths,
elapsed time, and diagnostic labels belong to validation provenance records.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict, Mapping, Tuple, Union

import scripts.function_tracer_pcode.core.live_values as live_values


CAUSE_IDENTITY_SCHEMA_VERSION = 1
PROOF_REQUIREMENT_SCHEMA_VERSION = 1


# pure layer: project の module は、live な値を読む唯一の規則（`core.live_values`。標準 library だけに
# 依る最下層）だけを import する。値は組み込みの振る舞いの容器・scalar として読み、それ以外（読み方を
# 上書きした容器・組み込みでない mapping）は葉として identity に入れる（その値の code を呼ばない）


def _tuple(value: Any) -> Tuple[Any, ...]:
    if value is None:
        return ()
    if (type(value) is tuple or type(value) is list) or live_values.builtin_sequence(value):
        return tuple(_tuple_item(item) for item in live_values.elements_of(value))
    return (_tuple_item(value),)


def _tuple_item(value: Any) -> Any:
    kind = type(value)
    if kind is tuple or kind is list or live_values.builtin_sequence(value):
        return tuple(_tuple_item(item) for item in live_values.elements_of(value))
    if kind is dict or live_values.builtin_mapping(value) is not None:
        # key の文字列で整列する（同じ文字列の key は元の順。安定な sort）
        texts = []
        items = []
        for key, item in live_values.items_of(value):
            texts.append(_key_text(key))
            items.append(item)
        order = sorted(range(len(texts)), key=texts.__getitem__)
        return tuple((texts[index], _tuple_item(items[index])) for index in order)
    return value


def _key_text(key: Any) -> str:
    """mapping の key の `str(key)`（scalar と組み込みのままの enum。それ以外は型名の印）。"""

    if type(key) is str:
        return key
    try:
        return live_values.as_str(key)
    except TypeError:
        return "<" + live_values.type_name(type(key)) + ">"


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

    def json_items(self):
        # 固定個数の field（値は既存の key への参照。dataclass の field の順）
        yield "cause_kind", self.cause_kind
        yield "binary_content_identity", self.binary_content_identity
        yield "function_ir_identity", self.function_ir_identity
        yield "semantic_object_identity", self.semantic_object_identity
        yield "schema_version", self.schema_version
        yield "identity_scope", self.identity_scope

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

    def json_items(self):
        # 固定個数の field（値は既存の key への参照。dataclass の field の順）
        yield "cause_kind", self.cause_kind
        yield "comparison_domain", self.comparison_domain
        yield "left_semantic_object", self.left_semantic_object
        yield "right_semantic_object", self.right_semantic_object
        yield "correspondence_contract", self.correspondence_contract
        yield "schema_version", self.schema_version
        yield "identity_scope", self.identity_scope

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

    def json_items(self):
        # 固定個数の field（値は既存の key への参照。dataclass の field の順）
        yield "cause_kind", self.cause_kind
        yield "comparison_domain", self.comparison_domain
        yield "logical_query_identity", self.logical_query_identity
        yield "execution_semantics_identity", self.execution_semantics_identity
        yield "schema_version", self.schema_version
        yield "identity_scope", self.identity_scope

    def to_dict(self) -> Dict[str, Any]:
        return _cause_to_dict(self)


CauseKey = Union[UnaryCauseKey, RelationalCauseKey, ExecutionCauseKey]


def _cause_to_dict(value: CauseKey) -> Dict[str, Any]:
    payload = dict(value.__dict__)
    return payload


def cause_key_from_dict(payload: Mapping[str, Any]) -> CauseKey:
    scope = _kind_text(_item(payload, "identity_scope"))
    version = _int_or_zero(_item(payload, "schema_version"))
    if version != CAUSE_IDENTITY_SCHEMA_VERSION:
        raise ValueError(f"unsupported typed cause schema: {version}")
    common = {
        "cause_kind": _kind_text(_item(payload, "cause_kind")),
        "schema_version": version,
    }
    if not common["cause_kind"]:
        raise ValueError("typed cause key requires cause_kind")
    if scope == IdentityScope.UNARY.value:
        value = UnaryCauseKey(
            **common,
            binary_content_identity=_tuple(_item(payload, "binary_content_identity")),
            function_ir_identity=_tuple(_item(payload, "function_ir_identity")),
            semantic_object_identity=_tuple(_item(payload, "semantic_object_identity")),
        )
        required = (
            value.binary_content_identity,
            value.function_ir_identity,
            value.semantic_object_identity,
        )
    elif scope == IdentityScope.RELATIONAL.value:
        value = RelationalCauseKey(
            **common,
            comparison_domain=_tuple(_item(payload, "comparison_domain")),
            left_semantic_object=_tuple(_item(payload, "left_semantic_object")),
            right_semantic_object=_tuple(_item(payload, "right_semantic_object")),
            correspondence_contract=_tuple(_item(payload, "correspondence_contract")),
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
            comparison_domain=_tuple(_item(payload, "comparison_domain")),
            logical_query_identity=_tuple(_item(payload, "logical_query_identity")),
            execution_semantics_identity=_tuple(_item(payload, "execution_semantics_identity")),
        )
        required = (
            value.comparison_domain,
            value.logical_query_identity,
            value.execution_semantics_identity,
        )
    else:
        raise ValueError(f"unsupported identity scope: {scope}")
    # 各 field は `_tuple` が作った組み込みの tuple（空かどうかは組み込みの tuple の長さ）
    for part in required:
        if type(part) is tuple:
            if part:
                continue
        raise ValueError(f"incomplete {scope} typed cause key")
    return value


def canonical_cause_tuple(value: CauseKey) -> Tuple[Any, ...]:
    # field は exact な型の `json_items`（dataclass の field の順）で読む（`to_dict()` を呼ばない）
    if type(value) is UnaryCauseKey:
        pairs = value.json_items()
    elif type(value) is RelationalCauseKey:
        pairs = value.json_items()
    elif type(value) is ExecutionCauseKey:
        pairs = value.json_items()
    else:
        raise TypeError(f"{live_values.type_name(type(value))} is not a typed cause key")
    names = []
    items = []
    for name, item in pairs:
        names.append(live_values.as_str(name))
        items.append(item)
    order = sorted(range(len(names)), key=names.__getitem__)
    return tuple((names[index], _tuple_item(items[index])) for index in order)


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
            if type(proof_contract) is ProofRequirementContract
            else _tuple(proof_contract)
        )
        target = _tuple(proof_target_key)
        kind = _kind_text(proof_kind)
        if not kind or not target or not contract_key:
            raise ValueError("proof requirement requires kind, target, and contract")
        return cls(kind, target, contract_key)

    def json_items(self):
        yield "schema_version", self.schema_version
        yield "proof_kind", self.proof_kind
        yield "proof_target_key", self.proof_target_key
        yield "proof_contract_key", self.proof_contract_key

    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "proof_kind": self.proof_kind,
            "proof_target_key": self.proof_target_key,
            "proof_contract_key": self.proof_contract_key,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "ProofRequirementId":
        version = _int_or_zero(_item(payload, "schema_version"))
        if version != PROOF_REQUIREMENT_SCHEMA_VERSION:
            raise ValueError(f"unsupported proof requirement schema: {version}")
        return cls.create(
            _item(payload, "proof_kind"),
            _item(payload, "proof_target_key"),
            _item(payload, "proof_contract_key"),
        )

    def to_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version,
            self.proof_kind,
            self.proof_target_key,
            self.proof_contract_key,
        )


def _item(payload: Any, key: str) -> Any:
    """`payload.get(key)`（組み込みの振る舞いの mapping の基底型の `get`）。"""

    return live_values.lookup(payload, key)


def _int_or_zero(value: Any) -> int:
    """`int(value or 0)`（基底型の slot で読む）。"""

    if type(value) is int:
        return value
    if value is None or not live_values.as_bool(value):
        return 0
    return live_values.as_int(value)


def _kind_text(value: Any) -> str:
    """`str(value or "")`（scalar と組み込みのままの enum を基底型の slot で読む）。"""

    if type(value) is str:
        return value
    if value is None or not live_values.as_bool(value):
        return ""
    return live_values.as_str(value)


LegacyProofObligationId = Tuple[Any, ...]
