# -*- coding: utf-8 -*-
"""Condition model separated from Expression."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, TYPE_CHECKING, Mapping

from scripts.function_tracer_pcode.core.storage import StorageInfo

if TYPE_CHECKING:
    from scripts.function_tracer_pcode.core.expression import Expression


#: 凍結後に書き換えてはいけない意味 field。
SEMANTIC_FIELDS = frozenset({"expression", "negated"})

_freeze_condition = None


def _freeze(condition: "Condition") -> None:
    """条件と式を凍結する（`core/semantic_freeze.py` を遅延解決して呼ぶ）。"""

    global _freeze_condition
    if _freeze_condition is None:
        from scripts.function_tracer_pcode.core.semantic_freeze import (
            freeze_condition as _resolved,
        )

        _freeze_condition = _resolved
    _freeze_condition(condition)


class Condition:
    """条件式を表現するクラス

    `Condition` は **構築と同時に凍結される**。条件は「この式がこの向きで成り
    立つ」という 1 つの意味の単位で、後から式や向きを差し替えられると、その
    条件を key にした cache・dedup・PHI の branch がすべて意味を変えてしまう。
    向きを変えたいときは `negate()` が新しい条件を返す。
    """

    _frozen: bool = False

    def __init__(self, expression: Optional["Expression"], negated: bool = False):
        if expression is None:
            raise ValueError("Condition expression must not be None")
        self.__dict__["expression"] = expression
        self.__dict__["negated"] = negated
        _freeze(self)

    def __setattr__(self, name: str, value: Any) -> None:
        if name in SEMANTIC_FIELDS and self.__dict__.get("_frozen", False):
            from scripts.function_tracer_pcode.core.semantic_freeze import (
                frozen_mutation_error,
            )

            raise frozen_mutation_error(self, name)
        object.__setattr__(self, name, value)

    @property
    def is_frozen(self) -> bool:
        return bool(self.__dict__.get("_frozen", False))

    def negate(self) -> "Condition":
        return Condition(self.expression, not self.negated)

    def to_string(self) -> str:
        expr_str = self.expression.to_string()
        if self.negated:
            return f"(not {expr_str})"
        return expr_str

    def to_smt(
        self,
        *,
        symbol_name_mapping: Optional[Mapping[str, str]] = None,
        float_mode: str = "uf",
    ) -> str:
        from scripts.function_tracer_pcode.core.render_smt import _coerce_expr_to_bool

        expr_smt = self.expression.to_smt(
            symbol_name_mapping=symbol_name_mapping,
            float_mode=float_mode,
        )
        expr_smt = _coerce_expr_to_bool(self.expression, expr_smt)
        if self.negated:
            return f"(not {expr_smt})"
        return expr_smt

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Condition):
            return False
        return self.equals(other)

    def __hash__(self) -> int:
        """candidate hash に基づく bucket 値。

        等価の確定には使わない（`equals` が完全比較する）。`equals` が真なら
        構造が同じなので hash も同じ、という向きだけを守る。
        """

        from scripts.function_tracer_pcode.core.structural import candidate_hash

        digest = candidate_hash(self.expression)
        if digest is None:
            return hash(("uncomparable_condition", id(self)))
        return hash((digest, bool(self.negated)))

    def equals(self, other: "Condition") -> bool:
        """条件が等価かどうかを判定（DAG-aware な完全比較）。

        hash はあくまで候補の絞り込みで、一致は構造の完全比較で決める。共有
        部分木は distinct な node 組として 1 回だけ比較するので、同じ部分式を
        親ごとに展開し直さない。
        """
        if not isinstance(other, Condition):
            return False
        if self is other:
            return True
        if bool(self.negated) != bool(other.negated):
            return False

        from scripts.function_tracer_pcode.core.structural import structural_equals

        return structural_equals(self.expression, other.expression)

    def structural_key(self, *, budget: int = 256):
        from scripts.function_tracer_pcode.core.structural import condition_key

        return condition_key(self, budget=budget)

    def _safe_structural_key(self, *, budget: int = 256):
        """Comparison-safe structural key.

        If the key contains placeholders (truncated/cycle/opaque), we intentionally
        return None to avoid treating those expressions as equal by construction.
        """

        from scripts.function_tracer_pcode.core.structural import (
            condition_key,
            key_contains_placeholder,
        )

        key = condition_key(self, budget=budget)
        if key_contains_placeholder(key):
            return None
        return key

    @classmethod
    def combine_and(cls, conditions: List[Optional["Condition"]]) -> Optional["Condition"]:
        """複数の条件を AND で結合する。"""
        if not conditions:
            return None

        unique: List[Condition] = []
        for cond in conditions:
            if cond is None:
                continue
            is_dup = False
            for existing in unique:
                if cond.equals(existing):
                    is_dup = True
                    break
            if not is_dup:
                unique.append(cond)

        if len(unique) == 0:
            return None
        if len(unique) == 1:
            return unique[0]

        from scripts.function_tracer_pcode.core.expression import Expression

        def to_expr(condition: Condition) -> "Expression":
            if condition.negated:
                return Expression.unary_op("BOOL_NEGATE", condition.expression)
            return condition.expression

        combined = Expression.binary_op("BOOL_AND", to_expr(unique[0]), to_expr(unique[1]))
        for cond in unique[2:]:
            combined = Expression.binary_op("BOOL_AND", combined, to_expr(cond))

        return Condition(combined, False)

    def get_all_variables(self):
        """条件式に含まれる全ての変数名を取得"""
        return self.expression.get_all_variables()

    def get_all_variables_with_storage(self) -> Dict[str, Optional[StorageInfo]]:
        """条件式に含まれる全ての変数名とストレージ情報を取得"""
        return self.expression.get_all_variables_with_storage()

    def to_dict(self) -> Dict[str, Any]:
        """辞書形式に変換"""
        return {
            "expression": self.expression.to_dict(),
            "negated": self.negated,
        }
