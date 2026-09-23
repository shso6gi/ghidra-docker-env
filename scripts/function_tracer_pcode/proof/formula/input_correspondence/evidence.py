# -*- coding: utf-8 -*-
"""InputExtensionEvidence（IEE）の contract と validator（Issue #167、v5 §4.4）。

IEE は ABI 規約・信頼済みの元の宣言型・物理 storage の 3 命題を同じ
binary / function / parameter に結び付けたときだけ存在する。値は validator
（``validate_input_extension_evidence``）だけが作る。出所（provider）は
``checker/arch/input_extension.py`` が持ち、新しい出所を足しても validator と
relation 規則は変えない。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, List, Optional, Tuple

from scripts.function_tracer_pcode.semantics.rewrite_contract import ExtensionKind


_IEE_TOKEN = object()
_TRUSTED_CLASSIFICATION_TOKEN = object()


@dataclass(frozen=True)
class ParameterBinding:
    """証拠が指す binary / function / parameter。3 命題はこれが一致して初めて結合する。"""

    binary_id: str
    function_identity: str
    parameter_index: int

    def __post_init__(self) -> None:
        if not self.binary_id or not self.function_identity or int(self.parameter_index) < 0:
            raise ValueError("parameter binding requires binary, function and index")


@dataclass(frozen=True)
class AbiExtensionRule:
    """ABI 規約: その ABI では、この register class の引数がこの形で拡張される。

    規約だけでは「この parameter の元の宣言幅」は分からない（v5 §0.1）。
    ``logical_bits`` / ``is_signed`` はこの規則が適用される宣言型の条件であり、
    parameter がその型であることは ``TrustedParameterClassification`` が別に示す。
    """

    abi_id: str
    binary_id: str
    register_class: str
    storage_bits: int
    logical_bits: int
    is_signed: Optional[bool]
    kind: ExtensionKind
    source_reference: str

    def applies_to(self, logical_bits: int, is_signed: bool) -> bool:
        if int(logical_bits) != int(self.logical_bits):
            return False
        return self.is_signed is None or bool(is_signed) == self.is_signed


@dataclass(frozen=True, init=False)
class TrustedParameterClassification:
    """build identity に結び付いた信頼済み signature から得た parameter の元の宣言型。

    Ghidra の推論型、usage hint、返却幅の証明、手動で付けた未検証型は **これに
    ならない**。production にはまだこれを発行する経路が無い（v5 §4.4）ので、
    値は封印 token を持つ trusted adapter からしか作れない。
    """

    binding: ParameterBinding
    logical_bits: int
    is_signed: bool
    type_class: str
    provenance_kind: str
    provenance_digest: str

    def __init__(
        self,
        binding: ParameterBinding,
        logical_bits: int,
        is_signed: bool,
        type_class: str,
        provenance_kind: str,
        provenance_digest: str,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _TRUSTED_CLASSIFICATION_TOKEN:
            raise ValueError("trusted parameter classifications are adapter-issued")
        if not provenance_kind or not provenance_digest:
            raise ValueError("trusted parameter classification requires provenance")
        object.__setattr__(self, "binding", binding)
        object.__setattr__(self, "logical_bits", int(logical_bits))
        object.__setattr__(self, "is_signed", bool(is_signed))
        object.__setattr__(self, "type_class", str(type_class))
        object.__setattr__(self, "provenance_kind", str(provenance_kind))
        object.__setattr__(self, "provenance_digest", str(provenance_digest))


@dataclass(frozen=True)
class StorageObservation:
    """当該 parameter の物理 storage（register slice）の観測。"""

    binding: ParameterBinding
    register_name: str
    register_class: str
    bit_offset: int
    storage_bits: int
    base_register_bits: int


@dataclass(frozen=True, init=False)
class InputExtensionEvidence:
    """validator が 3 命題を同じ parameter に結合できたときだけ存在する証拠。

    意味: parameter（幅 ``storage_bits``）の値は常に
    ``ext_kind(low_{logical_bits}(value))``。
    """

    binding: ParameterBinding
    logical_bits: int
    storage_bits: int
    kind: ExtensionKind
    abi_id: str
    classification_provenance_digest: str
    storage_register: str

    def __init__(self, *args: Any, _factory_token: object = None, **kwargs: Any) -> None:
        if _factory_token is not _IEE_TOKEN:
            raise ValueError("input extension evidence is issued only by the validator")
        values = dict(zip(
            (
                "binding", "logical_bits", "storage_bits", "kind", "abi_id",
                "classification_provenance_digest", "storage_register",
            ),
            args,
        ))
        values.update(kwargs)
        for name, value in values.items():
            object.__setattr__(self, name, value)

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "input_extension_evidence_v1",
            self.binding.binary_id,
            self.binding.function_identity,
            int(self.binding.parameter_index),
            int(self.logical_bits),
            int(self.storage_bits),
            self.kind.value,
            self.abi_id,
            self.classification_provenance_digest,
            self.storage_register,
        )


@dataclass(frozen=True)
class InputExtensionRefusal:
    """IEE を発行しなかった理由（どの命題が欠けた / 食い違ったか）。"""

    binding: Optional[ParameterBinding]
    reasons: Tuple[str, ...]


def validate_input_extension_evidence(
    rule: Optional[AbiExtensionRule],
    classification: Optional[TrustedParameterClassification],
    storage: Optional[StorageObservation],
) -> Tuple[Optional[InputExtensionEvidence], Tuple[str, ...]]:
    """3 命題を独立に検査し、全部が同じ parameter に結合できたときだけ IEE を返す。"""

    reasons: List[str] = []
    if rule is None:
        reasons.append("abi_rule_missing")
    if classification is None:
        reasons.append("trusted_classification_missing")
    elif type(classification) is not TrustedParameterClassification:
        reasons.append("classification_not_trusted")
    if storage is None:
        reasons.append("storage_observation_missing")
    if reasons:
        return None, tuple(reasons)

    if classification.binding != storage.binding:
        reasons.append("classification_storage_binding_mismatch")
    if rule.binary_id != storage.binding.binary_id:
        reasons.append("abi_rule_binary_mismatch")
    if rule.register_class != storage.register_class:
        reasons.append("register_class_mismatch")
    if storage.bit_offset != 0:
        reasons.append("storage_not_low_slice")
    if storage.storage_bits != rule.storage_bits or storage.base_register_bits != rule.storage_bits:
        reasons.append("storage_width_mismatch")
    if classification.type_class != "int":
        reasons.append("classification_not_integral")
    if not (0 < classification.logical_bits < storage.storage_bits):
        reasons.append("no_extension_between_logical_and_storage")
    if not rule.applies_to(classification.logical_bits, classification.is_signed):
        reasons.append("abi_rule_not_applicable_to_declared_type")
    if reasons:
        return None, tuple(reasons)

    evidence = InputExtensionEvidence(
        storage.binding,
        classification.logical_bits,
        storage.storage_bits,
        rule.kind,
        rule.abi_id,
        classification.provenance_digest,
        storage.register_name,
        _factory_token=_IEE_TOKEN,
    )
    return evidence, ()


def analysis_parameter_binding(analysis: Any, parameter_index: int) -> Optional[ParameterBinding]:
    """analysis の binary / function identity に parameter を結び付ける。"""

    binary_id = getattr(analysis, "binary_id", None)
    function_ref = getattr(analysis, "function_ref", None)
    function_identity = None
    if function_ref is not None:
        stable_key = getattr(function_ref, "stable_key", None)
        function_identity = repr(stable_key()) if callable(stable_key) else None
    if not binary_id or not function_identity or int(parameter_index) < 0:
        return None
    return ParameterBinding(str(binary_id), function_identity, int(parameter_index))
