# -*- coding: utf-8 -*-
"""Pairwise strategy helper models."""

from typing import Dict, List, Optional

from ...model import Condition, ReturnInfo
from ..formula.returns import coerce_value_to_bitvec_width


class ReturnCase:
    """ReturnInfo から抽出した 1 つの分岐ケース"""

    def __init__(
        self,
        index: int,
        conditions: List[Condition],
        value_expr,
        return_info: ReturnInfo,
        return_type: Optional[str] = None,
        source_indices: Optional[List[int]] = None,
    ):
        self.index = index
        self.conditions = conditions
        self.value_expr = value_expr
        self.return_info = return_info
        self.return_type = return_type
        self.source_indices = source_indices or [index]
        self.conditions_smt: Optional[List[str]] = None
        self._value_smt_cache: Dict[tuple, str] = {}

    def get_conditions_smt(self, param_replace_fn) -> List[str]:
        if self.conditions_smt is None:
            self.conditions_smt = []
            for cond in self.conditions:
                cond_str = cond.to_smt()
                cond_str = param_replace_fn(cond_str)
                self.conditions_smt.append(cond_str)
        return self.conditions_smt

    def get_value_smt(
        self,
        param_replace_fn,
        target_bits: Optional[int] = None,
        use_sign_extension: bool = False,
    ) -> str:
        cache_key = (target_bits, use_sign_extension)
        result = self._value_smt_cache.get(cache_key)
        if result is not None:
            return result

        result = str(self.value_expr.to_smt())
        result = param_replace_fn(result)
        if target_bits is not None:
            result = coerce_value_to_bitvec_width(
                self.value_expr,
                result,
                target_bits,
                use_sign_extension=use_sign_extension,
            )
        self._value_smt_cache[cache_key] = result
        return result

    def get_condition_summary(self) -> str:
        if not self.conditions:
            return "unconditional"

        cond_strs = []
        for cond in self.conditions[:3]:
            cond_str = str(cond)
            if cond_str:
                cond_strs.append(cond_str)

        if not cond_strs:
            return "unconditional"
        return " AND ".join(cond_strs)


class QueryResult:
    """1 クエリ分の実行結果"""

    def __init__(
        self,
        is_equivalent: Optional[bool],
        counterexample_raw: Optional[Dict] = None
    ):
        self.is_equivalent = is_equivalent
        self.counterexample_raw = counterexample_raw
        self.last_query: Optional[str] = None
        self.normalization_rules: List = []
        self.pair_stage: Optional[str] = None
