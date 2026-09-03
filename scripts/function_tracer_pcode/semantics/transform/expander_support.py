"""Value containers and P-code ref helpers shared by the expression expander and its mixins."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Hashable, List, Optional, Tuple, Any
from scripts.function_tracer_pcode.core import Expression, Condition, CanonicalLocation, PcodeOpRef
from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier


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
        conds = [c.to_string() for c in self.conditions]
        return f"ExpandedValue(value={self.value.to_string()}, conds={conds})"


@dataclass(frozen=True)
class MultiequalBranchObservation:
    """Object-centric branch observation for a MULTIEQUAL input edge."""

    value: Expression
    conditions: Tuple[Condition, ...]
    observed_location: Optional[CanonicalLocation]
