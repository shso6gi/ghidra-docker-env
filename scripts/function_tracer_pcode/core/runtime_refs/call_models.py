"""Decision-neutral call-model candidate metadata (Issue #20 PR-B1).

``CallModelCandidateRef`` は「この callsite は explicit-assumption model の
**候補になり得る**」という分類結果だけを運ぶ neutral な DTO である。

この DTO が主張しないこと（重要）:

* callee が pure である / メモリを書かない
* 左右の callee が同一の関数である
* 呼び出しの効果が既知である

したがって candidate の有無は ``DeferredCallInfo.effect_class`` を変えない。
仮定の下で意味を与える（canonical CALL / uninterpreted function、no-write
premise）のは proof 層の conditional view の責務であり、そこでは
``AssumptionPremise`` が明示的に付随する。analysis 層は candidate を
「pure である証拠」として扱ってはならない。

``core`` は本 DTO の**形**だけを所有する。candidate をどう作るか（catalog
lookup / alias resolution / provenance validation / signature validation）は
``analysis/effects/pure_function_catalog.py`` が所有し、``core`` から catalog を
lookup することはない。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple
from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record, runtime_ref_key
from scripts.function_tracer_pcode.core.json_encoding import (as_list, each, inline, is_json_record, mapping_of, materialize, nested, raw, source_converter)
from scripts.function_tracer_pcode.core.live_values import exact_scalar, exact_tree, is_kind


CALL_MODEL_CANDIDATE_KIND = "call_model_candidate"


def _required_text(value: Any, field_name: str) -> str:
    if not is_kind(value, str):
        raise TypeError(f"call model candidate {field_name} must be a str")
    text = value.strip()
    if not text:
        raise ValueError(f"call model candidate {field_name} must be non-empty")
    return text


def _frozen_key(value: Any, field_name: str) -> Tuple[Any, ...]:
    """list / tuple を再帰的に tuple 化した決定的キーを返す（葉の scalar は基底型の値。Issue #242）。"""
    if not is_kind(value, (tuple, list)):
        raise TypeError(f"call model candidate {field_name} must be a tuple")
    frozen = tuple(
        _frozen_key(item, field_name) if is_kind(item, (tuple, list)) else exact_tree(item)
        for item in value
    )
    if not frozen:
        raise ValueError(f"call model candidate {field_name} must be non-empty")
    return frozen


@dataclass(frozen=True)
@runtime_ref_record
class CallModelCandidateRef:
    """One callsite's decision-neutral call-model candidate classification.

    ``candidate_key`` は与えられた入力から **決定的に導出**される。呼び出し側が
    値を渡すこともできるが、導出結果と一致しなければ construction 時に reject
    する（後から key だけを差し替えて別物にできないようにするため）。
    """

    provider: str
    canonical_symbol: str
    signature_key: Tuple[Any, ...]
    provenance_key: Tuple[Any, ...]
    candidate_key: Optional[Tuple[Any, ...]] = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "provider", _required_text(self.provider, "provider"))
        object.__setattr__(
            self,
            "canonical_symbol",
            _required_text(self.canonical_symbol, "canonical_symbol"),
        )
        object.__setattr__(
            self,
            "signature_key",
            _frozen_key(self.signature_key, "signature_key"),
        )
        object.__setattr__(
            self,
            "provenance_key",
            _frozen_key(self.provenance_key, "provenance_key"),
        )
        derived = (
            CALL_MODEL_CANDIDATE_KIND,
            self.provider,
            self.canonical_symbol,
            self.signature_key,
            self.provenance_key,
        )
        supplied = self.candidate_key
        if supplied is not None:
            if not is_kind(supplied, (tuple, list)):
                raise TypeError("call model candidate candidate_key must be a tuple")
            if _frozen_key(supplied, "candidate_key") != derived:
                raise ValueError(
                    "call model candidate candidate_key does not match its derivation"
                )
        object.__setattr__(self, "candidate_key", derived)

    @runtime_ref_key
    def stable_key(self) -> Tuple[Any, ...]:
        return self.candidate_key

    def json_items(self):
        yield "kind", CALL_MODEL_CANDIDATE_KIND
        yield "provider", self.provider
        yield "candidate_key", _jsonable_key_source(self.candidate_key)
        yield "canonical_symbol", self.canonical_symbol
        yield "signature_key", _jsonable_key_source(self.signature_key)
        yield "provenance_key", _jsonable_key_source(self.provenance_key)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@source_converter
def _jsonable_key_source(value: Any) -> Any:
    """`_jsonable_key` と同じ値を 1 要素ずつ作らせる source（tuple は配列、それ以外はそのまま）。"""

    if is_kind(value, tuple):
        return each(value, _jsonable_key_source)
    if value is None or is_kind(value, (bool, int, float, str)):
        return value
    return raw(value)


def _jsonable_key(value: Any) -> Any:
    if is_kind(value, tuple):
        return [_jsonable_key(item) for item in value]
    return value
