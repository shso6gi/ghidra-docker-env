"""Dependency-neutral typed inputs shared by call/effect producers and v2 signals."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.analysis.effects.summary import (
    CallArgumentEvidence,
    CallSiteEffectSummaryEvidence,
    StoreEffect,
)
from scripts.function_tracer_pcode.core import ReturnInfo
from scripts.function_tracer_pcode.core.semantic_freeze import publish_semantic_values


CALL_EFFECT_PRODUCER_KIND = "internal_typed_pure_direct_call_stage_producer"


@dataclass(frozen=True)
class PureDirectCallProofInput:
    obligation_id: str
    observation_contract_id: str
    left_fact_id: str
    right_fact_id: str
    structural_certificate_id: str
    left_fact_payload: Mapping[str, Any]
    right_fact_payload: Mapping[str, Any]
    left_arguments: CallArgumentEvidence
    right_arguments: CallArgumentEvidence
    left_effect: CallSiteEffectSummaryEvidence
    right_effect: CallSiteEffectSummaryEvidence
    left_parameters: Tuple[Mapping[str, Any], ...]
    right_parameters: Tuple[Mapping[str, Any], ...]
    left_caller_observation_bit_width: Optional[int]
    right_caller_observation_bit_width: Optional[int]
    left_caller_effects: Tuple[StoreEffect, ...]
    right_caller_effects: Tuple[StoreEffect, ...]
    left_caller_profile: Any
    right_caller_profile: Any
    left_caller_call_effects: Tuple[CallSiteEffectSummaryEvidence, ...]
    right_caller_call_effects: Tuple[CallSiteEffectSummaryEvidence, ...]

    def __post_init__(self) -> None:
        """組み立て完了点。この入力が抱える意味値をここで公開する。

        proof の入力は解析結果から組み上げた **この証明のための値** で、
        作り終えた時点が確定点。consumer（SMT 生成）側で公開すると「描画したから
        確定」という順序になってしまうので、carrier 自身が宣言する。
        """

        publish_semantic_values(self)


@dataclass(frozen=True)
class PureCallRegionProofInput:
    obligation_id: str
    observation_contract_id: str
    left_fact_id: str
    right_fact_id: str
    structural_certificate_id: str
    left_fact_payload: Mapping[str, Any]
    right_fact_payload: Mapping[str, Any]
    call_on_left: bool
    call_arguments: CallArgumentEvidence
    call_effect: CallSiteEffectSummaryEvidence
    region_returns: Tuple[ReturnInfo, ...]
    region_effects: Tuple[StoreEffect, ...]
    left_parameters: Tuple[Mapping[str, Any], ...]
    right_parameters: Tuple[Mapping[str, Any], ...]
    left_caller_observation_bit_width: Optional[int]
    right_caller_observation_bit_width: Optional[int]
    region_return_signed: Optional[bool]
    left_caller_effects: Tuple[StoreEffect, ...]
    right_caller_effects: Tuple[StoreEffect, ...]
    left_caller_profile: Any
    right_caller_profile: Any
    left_caller_call_effects: Tuple[CallSiteEffectSummaryEvidence, ...]
    right_caller_call_effects: Tuple[CallSiteEffectSummaryEvidence, ...]

    def __post_init__(self) -> None:
        """組み立て完了点。この入力が抱える意味値をここで公開する。"""

        publish_semantic_values(self)
