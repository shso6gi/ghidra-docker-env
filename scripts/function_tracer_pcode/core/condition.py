# -*- coding: utf-8 -*-
"""Condition model separated from Expression."""

from __future__ import annotations

import copy
from typing import Any, Dict, List, Optional, TYPE_CHECKING, Mapping

from scripts.function_tracer_pcode.core.json_encoding import materialize
from scripts.function_tracer_pcode.core.semantic_lifecycle import (
    SemanticLifecycle,
    attribute_mutation_allowed,
    state_of,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo

if TYPE_CHECKING:
    from scripts.function_tracer_pcode.core.expression import Expression


#: 凍結後に書き換えてはいけない意味 field。
SEMANTIC_FIELDS = frozenset({"expression", "negated"})

_freeze_condition = None
_publish_condition = None


def _freeze(condition: "Condition") -> None:
    """条件と式を凍結する（`core/semantic_freeze.py` を遅延解決して呼ぶ）。"""

    global _freeze_condition
    if _freeze_condition is None:
        from scripts.function_tracer_pcode.core.semantic_freeze import (
            freeze_condition as _resolved,
        )

        _freeze_condition = _resolved
    _freeze_condition(condition)


def _publish(condition: "Condition") -> "Condition":
    """条件を公開する（`core/semantic_freeze.py` を遅延解決して呼ぶ）。"""

    global _publish_condition
    if _publish_condition is None:
        from scripts.function_tracer_pcode.core.semantic_freeze import (
            publish_condition as _resolved,
        )

        _publish_condition = _resolved
    return _publish_condition(condition)


class Condition:
    """条件式を表現するクラス

    `Condition` は **構築と同時に検証・凍結される**。条件は「この式がこの向きで
    成り立つ」という 1 つの意味の単位で、後から式や向きを差し替えられると、その
    条件を key にした cache・dedup・PHI の branch がすべて意味を変えてしまう。
    向きを変えたいときは `negate()` が新しい条件を返す。

    凍結は **公開ではない**（`core/semantic_lifecycle.py`）。式と同じく、solver
    へ渡せるのは producer が `publish()` で宣言したものだけ。

    したがって条件の lifecycle は式より短い:

    * 構築した時点で **VALIDATED**（CONSTRUCTION に留まる時間が無い）
    * `publish()` で **PUBLISHED**
    * `negate()` が返す新しい条件も構築と同時に VALIDATED で、元が PUBLISHED
      なら PUBLISHED で始まる（反転には仕上げる余地が残らないため。詳細は
      `negate()` の docstring）
    * `copy` / `deepcopy` は構築と同じ道を通る新しい条件で、**公開は引き継が
      ない**（`__deepcopy__` の docstring）
    """

    _frozen: bool = False
    _published: bool = False
    #: LEGACY 表現が不変な状態だけの関数か（Issue #219 C-RS2。凍結時に式から決まる派生値で、
    #: 複製・反転は引き継がずに自分の式から決め直す。意味は `core/semantic_lifecycle.py`）
    _serialization_closed: bool = False
    _serialization_pending: bool = False

    def __init__(self, expression: Optional["Expression"], negated: bool = False):
        if expression is None:
            raise ValueError("Condition expression must not be None")
        self._assemble(expression, negated)

    def _assemble(self, expression: "Expression", negated: bool) -> None:
        """意味 field を置いて検証する。**条件が出来上がる唯一の道**。

        構築（`__init__`）と複製（`__deepcopy__`）が共有する。複製が別経路で
        field を置くと、「構築した条件は必ず VALIDATED」という不変条件が複製に
        だけ効かない、という形の食い違いが生まれる。
        """

        self.__dict__["expression"] = expression
        self.__dict__["negated"] = negated
        _freeze(self)

    def __setattr__(self, name: str, value: Any) -> None:
        if not attribute_mutation_allowed(self, name, SEMANTIC_FIELDS):
            from scripts.function_tracer_pcode.core.semantic_freeze import (
                frozen_mutation_error,
            )

            raise frozen_mutation_error(self, name)
        object.__setattr__(self, name, value)

    def __delattr__(self, name: str) -> None:
        """削除も代入と同じ規則で拒否する（`core/semantic_lifecycle.attribute_mutation_allowed`）。"""

        if not attribute_mutation_allowed(self, name, SEMANTIC_FIELDS):
            from scripts.function_tracer_pcode.core.semantic_freeze import (
                frozen_mutation_error,
            )

            raise frozen_mutation_error(self, name)
        object.__delattr__(self, name)

    @property
    def lifecycle(self) -> SemanticLifecycle:
        """今どの段階に居るか（`core/semantic_lifecycle.py` が定義）。"""

        return state_of(self.__dict__)

    @property
    def is_frozen(self) -> bool:
        """検証済みか。公開済みかは問わない。"""

        return self.lifecycle >= SemanticLifecycle.VALIDATED

    @property
    def is_published(self) -> bool:
        """producer が完成を宣言済みか。"""

        return self.lifecycle is SemanticLifecycle.PUBLISHED

    def __copy__(self) -> "Condition":
        """浅い複製。**新しい条件は VALIDATED、式 object は元と共有する**。

        独立した複製ではない（式は同じ object）。独立が要るときは
        `copy.deepcopy`。構築と同じ道を通るので検証までは済んでいるが、
        **公開は引き継がない**: 元が公開済みでも、複製の完成を宣言できるのは
        複製を作った側だけ。
        """

        return Condition(self.expression, self.negated)

    def __deepcopy__(self, memo: Dict[int, Any]) -> "Condition":
        """式まで複製する deep copy。**公開は引き継がない**。

        既定の deepcopy に任せると `__dict__` がそのまま写り、`_published` を
        持った条件の下に **未公開の複製式** がぶら下がる。外側だけ公開済みに
        見えるので、(a) 公開走査はその条件で早期 return して式へ降りず、
        (b) solver renderer は条件の公開だけ見て内部の式を描いてしまう。
        つまり「PUBLISHED な値から未公開の意味値へ到達できない」という closure
        の不変条件が、複製 1 回で破れていた。

        複製した式で **新しい条件を組み立て直す**ので、条件と式の状態が食い違う
        形を作れない。producer が必要なら複製に対して `publish()` を呼ぶ。

        式を複製する前に memo へ載せるのは、同じ条件が 2 度現れたとき（例:
        `ReturnCase.conditions` と PHI の branch）に 1 つの複製を共有するため。
        """

        cls = self.__class__
        copied = cls.__new__(cls)
        memo[id(self)] = copied
        copied._assemble(copy.deepcopy(self.expression, memo), self.negated)
        return copied

    def negate(self) -> "Condition":
        """向きを反転した **新しい条件**。

        公開済みの条件を反転したものは公開済みで始まる。条件には「あとで仕上げ
        る」段階が無く（構築と同時に凍結される）、反転は同じ確定済みの式の向き
        を変えただけなので、producer が宣言し直すものが何も残らない。

        式の複製（`clone_with` / `derive_with` / `copy` / `deepcopy`）や条件の
        複製（`__copy__` / `__deepcopy__`）が公開を引き継がないのとは事情が
        違う: あちらは **これから仕上げる材料** で、仕上げた結果を宣言できるの
        は作った側だけ。

        **closure は保たれる**: 反転は元の式 object を**そのまま**持つので、
        元が PUBLISHED なら式とその子孫もすでに PUBLISHED。新しい条件へ印を
        付けても、未公開の意味値がぶら下がることはない（複製はここが違う。
        式まで作り直すので、公開を引き継ぐと closure が壊れる）。
        """

        negated = Condition(self.expression, not self.negated)
        if self.is_published:
            _publish(negated)
        return negated

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
        """solver へ渡す SMT-LIB 文字列（公開済みの条件だけ受け取る）。"""

        from scripts.function_tracer_pcode.core.render_smt import condition_to_smt

        return condition_to_smt(
            self,
            symbol_name_mapping=symbol_name_mapping,
            float_mode=float_mode,
        )

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

        # 重複の判定は bucket（`__hash__` = candidate hash）→ 完全比較（`__eq__` =
        # `equals`）。条件どうしの総当たりにしない（Issue #105）。先に出た条件を残す。
        unique: List[Condition] = []
        seen: set = set()
        for cond in conditions:
            if cond is None or cond in seen:
                continue
            seen.add(cond)
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

    def json_items(self):
        yield "expression", self.expression
        yield "negated", self.negated

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)
