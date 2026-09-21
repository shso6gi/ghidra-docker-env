"""Value containers and P-code ref helpers shared by the expression expander and its mixins."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Hashable, List, Optional, Tuple, Any
from scripts.function_tracer_pcode.core import Expression, Condition, CanonicalLocation, PcodeOpRef
from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.debug import summarize_conditions, summarize_expression


def _pcode_op_stable_key(pcode_op) -> Tuple[Any, ...]:
    ref = PcodeOpRef.from_pcode_op(pcode_op)
    if ref is None:
        return ("pcode_op", None, None, None, None, None)
    return ref.stable_key()


def _pcode_op_ref_from_tracer(tracer: Any, pcode_op: Any) -> Optional[PcodeOpRef]:
    make_ref = getattr(tracer, "_make_pcode_op_ref", None)
    if callable(make_ref):
        try:
            ref = make_ref(pcode_op)
        except Exception:
            ref = None
        if ref is not None:
            return ref
    return PcodeOpRef.from_pcode_op(pcode_op)


def resized_expanded_values(values, output_size: int):
    """幅が決まっていない展開値に P-code 出力幅を与えた列を返す。

    値そのものは書き換えない。展開値は tracer の cache と同じ式 object を指して
    いることがあり、その場で幅を書き込むと「この演算の出力幅」が cache 側の
    別の文脈へ漏れてしまう（凍結の有無に関わらず）。`derive_with` は常に新しい
    式を作るので、幅はこの展開値だけに付く。
    """

    if not output_size or output_size <= 0:
        return values
    resized = []
    changed = False
    for expanded in values:
        value = expanded.value
        if getattr(value, "size", 0) == 0:
            updated = value.derive_with(size=output_size)
            if updated is not value:
                changed = True
                resized.append(ExpandedValue(updated, expanded.conditions))
                continue
        resized.append(expanded)
    return resized if changed else values


class ExpandedValue:
    """展開された値と条件のペア"""
    
    def __init__(self, value: Expression, conditions: List[Condition]):
        self.value = value
        self.conditions = conditions
    
    def is_valid(self) -> bool:
        """条件が矛盾していないかチェック"""
        return not (
            ConditionSimplifier.object_centric_is_contradiction(self.conditions)
            or ConditionSimplifier.is_contradiction(self.conditions)
        )
    
    def get_condition_signature(self) -> Hashable:
        """
        条件のシグネチャを取得（重複排除用）
        
        条件を正規化して、ソート済みの文字列として返す
        """
        return ConditionSimplifier.object_centric_conditions_signature(self.conditions)
    
    def __repr__(self):
        # ``repr()`` は logging / 例外 / デバッガから暗黙に呼ばれる。full render
        # だと debug を切っていても巨大 DAG を展開しうるので、有界サマリーを返す
        # （Issue #22）。
        return (
            f"ExpandedValue(value={summarize_expression(self.value)}, "
            f"conds={summarize_conditions(self.conditions)})"
        )


@dataclass(frozen=True)
class MultiequalBranchObservation:
    """Object-centric branch observation for a MULTIEQUAL input edge."""

    value: Expression
    conditions: Tuple[Condition, ...]
    observed_location: Optional[CanonicalLocation]
