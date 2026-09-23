# -*- coding: utf-8 -*-
"""Production の InputExtensionEvidence provider（Issue #167、v5 §4.4）。

IEE は 3 つの独立した命題を同じ binary / function / parameter に結び付けた
ときだけ発行する（検査は ``proof/formula/input_correspondence.validate_input_extension_evidence``）:

1. ABI 規約: 対象 binary の ABI・calling convention が確定し、引数位置と
   register class が規約に合う。
2. logical width: build identity に結び付いた信頼済み signature から得た、
   parameter の元の宣言型。
3. storage: 当該引数の register slice・幅。

現在の production で得られるのは 3 だけである:

* 1 について、strategy 段の analysis は ABI identity（compiler spec / calling
  convention の検証結果）を持たない。arch 名や register 名だけでは不十分。
* 2 について、parameter の型は Ghidra の decompiler が推論したもので、信頼済み
  signature（debug 情報・prototype 等）を build identity と結び付けて受理する
  経路は存在しない。Ghidra の推論型（``int 4`` / ``long 8`` / ``undefined8`` …）、
  usage hint、返却幅の証明は logical width の証拠にならない。

したがってこの provider は **IEE を発行しない**。欠けている命題を理由として
返すだけで、EQ の件数を保つために弱い証拠を IEE 化することはしない。信頼済み
signature の取得基盤ができたら、2 の adapter をここに足す（N64 の規約表と一次
資料の参照もそのとき一緒に置く）。
"""

from __future__ import annotations

from typing import Any, Optional, Tuple

from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    InputCorrespondenceSet,
    InputExtensionEvidence,
    InputExtensionRefusal,
    StorageObservation,
    analysis_parameter_binding,
    build_input_correspondence_set,
    validate_input_extension_evidence,
)
from scripts.function_tracer_pcode.core.storage import coerce_storage_info as _coerce_storage_info


#: 信頼済み signature の出所。現在は 1 つも無い（Ghidra の推論型は含めない）。
TRUSTED_SIGNATURE_SOURCES: Tuple[str, ...] = ()


def observe_parameter_storage(analysis: Any, descriptor: Any) -> Tuple[Optional[StorageObservation], Tuple[str, ...]]:
    """parameter descriptor の storage から register slice を観測する。"""

    try:
        index = int(descriptor.get("index"))
    except (TypeError, ValueError, AttributeError):
        return None, ("parameter_index_missing",)
    binding = analysis_parameter_binding(analysis, index)
    if binding is None:
        return None, ("parameter_binding_unavailable",)
    storage = _coerce_storage_info(descriptor.get("storage_info", descriptor.get("storage")))
    if storage is None:
        return None, ("storage_missing",)
    if not getattr(storage, "is_register", False):
        return None, ("storage_not_register",)
    register_name = str(getattr(storage, "register_name", "") or "")
    if not register_name:
        return None, ("storage_register_name_missing",)
    size_bits = int(getattr(storage, "size_bits", 0) or 0)
    base_bits = int(getattr(storage, "base_register_size_bits", 0) or 0) or size_bits
    if size_bits <= 0:
        return None, ("storage_width_missing",)
    return (
        StorageObservation(
            binding=binding,
            register_name=register_name,
            register_class=str(getattr(storage, "space_name", "") or "register"),
            bit_offset=int(getattr(storage, "bit_offset_in_base", 0) or 0),
            storage_bits=size_bits,
            base_register_bits=base_bits,
        ),
        (),
    )


def _verified_abi_rule(analysis: Any, storage: Optional[StorageObservation]):
    """ABI 規約の命題。analysis に検証済み ABI identity が無いので常に None。"""

    del analysis, storage
    return None, ("abi_identity_unverified",)


def _trusted_classification(analysis: Any, descriptor: Any):
    """信頼済み signature の命題。受理できる出所が無いので常に None。"""

    del analysis, descriptor
    if not TRUSTED_SIGNATURE_SOURCES:
        return None, ("trusted_signature_source_unavailable",)
    return None, ("trusted_signature_not_found",)


def explain_input_extension_evidence(
    analysis: Any,
) -> Tuple[Tuple[Optional[InputExtensionEvidence], InputExtensionRefusal], ...]:
    """parameter ごとに、IEE（あれば）と発行しなかった理由を返す。"""

    decisions = []
    for descriptor in getattr(analysis, "parameters", None) or ():
        storage, storage_reasons = observe_parameter_storage(analysis, descriptor)
        rule, rule_reasons = _verified_abi_rule(analysis, storage)
        classification, classification_reasons = _trusted_classification(analysis, descriptor)
        evidence, validator_reasons = validate_input_extension_evidence(rule, classification, storage)
        binding = storage.binding if storage is not None else None
        decisions.append(
            (
                evidence,
                InputExtensionRefusal(
                    binding,
                    () if evidence is not None else tuple(
                        dict.fromkeys(
                            (*storage_reasons, *rule_reasons, *classification_reasons, *validator_reasons)
                        )
                    ),
                ),
            )
        )
    return tuple(decisions)


def provide_input_extension_evidence(*analyses: Any) -> Tuple[InputExtensionEvidence, ...]:
    """``StrategySourceAnalysisPair.create`` へ渡す IEE（validator を通ったものだけ）。"""

    return tuple(
        evidence
        for analysis in analyses
        for evidence, _refusal in explain_input_extension_evidence(analysis)
        if evidence is not None
    )


def produce_final_input_correspondence(raw1: Any, raw2: Any) -> InputCorrespondenceSet:
    """checker 層が raw pair から最終 relation を作る入口（provider の IEE を渡す）。

    strategy の dispatch frame を通らない raw 直接比較（ABI retry など）はここを
    使い、結果を FormulaBuilder へ渡す。builder 自身は relation を作らない。
    """

    return build_input_correspondence_set(
        raw1,
        raw2,
        input_extension_evidence=provide_input_extension_evidence(raw1, raw2),
    )
