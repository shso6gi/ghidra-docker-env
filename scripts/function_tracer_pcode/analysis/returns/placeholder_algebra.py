"""Placeholder +/- unit and zero recognition under conditions."""

from __future__ import annotations

from typing import Any, Callable, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.analysis.returns._shared import ConditionNormalizer
from scripts.function_tracer_pcode.analysis.session import AnalysisSession
from scripts.function_tracer_pcode.analysis.returns.stack_protector import StackProtectorService
from scripts.function_tracer_pcode.analysis.returns.divergence_proofs import condition_identity_key
from scripts.function_tracer_pcode.analysis.returns.condition_logic import ConditionLogicService


class PlaceholderAlgebraService:
    """ReturnAnalyzer から切り出した placeholder 代数（param-1 / +0 / +1 形の判定と単位進行ガード鍵）の collaborator。

    per-analysis state: ``AnalysisSession`` を返す ``session`` supplier を 1 本保持し、呼び出し時に
    ``self.session().parameters`` を読む（nested ``_analysis_context`` の push/pop に追随する）。
    条件論理は ``ConditionLogicService``、定数値抽出は ``StackProtectorService`` を直接依存として受け取り、
    条件 identity 鍵は ``divergence_proofs.condition_identity_key``（純関数）を import する。
    未抽出 family が所有する ``branch_guarded_expression_is_param_minus_one`` は facade 経由で遅延 dispatch する
    callable として注入する。
    """

    def __init__(
        self,
        *,
        session: Callable[[], "AnalysisSession"],
        condition_logic: ConditionLogicService,
        stack_protector: StackProtectorService,
        branch_guarded_expression_is_param_minus_one: Callable[..., Any],
    ) -> None:
        self.session = session
        self.condition_logic = condition_logic
        self.stack_protector = stack_protector
        self.branch_guarded_expression_is_param_minus_one = branch_guarded_expression_is_param_minus_one

    def expression_is_placeholder_plus_one(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
    ) -> bool:
        return self.expression_is_placeholder_plus_constant(expr, placeholder, 1)

    def expression_is_placeholder_minus_one(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
    ) -> bool:
        return self.expression_is_placeholder_plus_constant(expr, placeholder, -1)

    def expression_is_placeholder_plus_one_under_conditions(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> bool:
        if self.expression_is_placeholder_plus_one(expr, placeholder):
            return True
        if self.expression_is_placeholder_plus_unit_condition(expr, placeholder, conditions):
            return True
        expected = Expression.binary_op(
            "INT_ADD",
            placeholder,
            Expression.constant(1, size=max(1, int(getattr(placeholder, "size", 0) or 4))),
        )
        expected.size = max(1, int(getattr(placeholder, "size", 0) or 4))
        return self.condition_logic.expressions_equal_under_conditions_smt(
            expr,
            expected,
            tuple(conditions or ()),
            self.session().parameters or (),
        )

    def expression_is_placeholder_minus_one_under_conditions(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> bool:
        if self.expression_is_placeholder_minus_one(expr, placeholder):
            return True
        if self.expression_is_placeholder_minus_one_unit_condition(expr, placeholder, conditions):
            return True
        expected = Expression.binary_op(
            "INT_SUB",
            placeholder,
            Expression.constant(1, size=max(1, int(getattr(placeholder, "size", 0) or 4))),
        )
        expected.size = max(1, int(getattr(placeholder, "size", 0) or 4))
        return self.condition_logic.expressions_equal_under_conditions_smt(
            expr,
            expected,
            tuple(conditions or ()),
            self.session().parameters or (),
        )

    def expression_is_placeholder_plus_zero_under_conditions(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> bool:
        current = self.strip_transparent_unary(expr)
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        if getattr(current, "operator", None) not in {"INT_ADD", "INT_SUB"}:
            return False
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return False
        left, right = operands
        if self.condition_logic.expressions_same_key(left, placeholder):
            delta = right
            if getattr(current, "operator", None) == "INT_ADD":
                return self.expression_is_zero_under_conditions(delta, conditions)
            return self.expression_is_zero_under_conditions(delta, conditions)
        if getattr(current, "operator", None) == "INT_ADD" and self.condition_logic.expressions_same_key(right, placeholder):
            return self.expression_is_zero_under_conditions(left, conditions)
        return False

    def expression_is_zero_under_conditions(
        self,
        expr: Optional[Expression],
        conditions: Sequence[Condition],
    ) -> bool:
        if self.stack_protector.constant_int_value(expr) == 0:
            return True
        current = self.strip_transparent_unary(expr)
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        as_condition = Condition(current, False)
        if self.condition_logic.conditions_imply(tuple(conditions or ()), (as_condition.negate(),)):
            return True
        operator = getattr(current, "operator", None)
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return False
        if operator == "INT_SLESS":
            left, right = operands
            if self.stack_protector.constant_int_value(right) == 1 and getattr(left, "expr_type", None) == ExpressionType.PARAMETER:
                if any(
                    self.condition_logic.condition_is_signed_positive_of_param(condition, left)
                    for condition in conditions or ()
                ):
                    return True
        if operator == "INT_SUB":
            left, right = operands
            if self.expression_is_one_under_conditions(left, conditions) and self.stack_protector.constant_int_value(right) == 1:
                return True
        return self.condition_logic.expressions_equal_under_conditions_smt(
            current,
            Expression.constant(0, size=max(1, int(getattr(current, "size", 0) or 4))),
            tuple(conditions or ()),
            self.session().parameters or (),
        )

    # ------------------------------------------------------------------
    # 照合（recognition）と命名（identity）を分ける
    #
    # 「この式が置換子 ± 単位条件の形か」を **見付ける**のは SMT 裏付けの照合で、
    # 条件にどれだけ細かい名前を付けられるかとは無関係。一方、証明鍵に載せる
    # ときは **厳密に名前を付けられること**が要る（付けられないなら証明を
    # 出さない）。
    #
    # 1 つの関数で両方を返すと、名前を付けられない条件（Ghidra 由来の opaque な
    # 値を含むものなど）で **照合そのものが失敗したことになり**、解析が別の式を
    # 作ってしまう。実際にそうなっていた（固定 subset の 1 pair で、組み立て
    # られる式が変わった）。だから照合を primitive にして、鍵はそこから導く。
    # ------------------------------------------------------------------

    def expression_is_placeholder_minus_one_unit_condition(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> bool:
        return (
            self.placeholder_minus_one_unit_condition(expr, placeholder, conditions)
            is not None
        )

    def placeholder_minus_one_unit_condition(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> Optional[Condition]:
        """置換子 - 1 の形を作っている条件そのもの（照合）。"""

        current = self.strip_transparent_unary(expr)
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return None
        if getattr(current, "operator", None) == "INT_ADD":
            operands = tuple(getattr(current, "operands", ()) or ())
            if len(operands) != 2:
                return None
            left, right = operands
            if self.condition_logic.expressions_same_key(left, placeholder):
                return self.negated_unit_condition_for_expression(right, conditions)
            if self.condition_logic.expressions_same_key(right, placeholder):
                return self.negated_unit_condition_for_expression(left, conditions)
            return None
        if getattr(current, "operator", None) != "INT_SUB":
            return None
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return None
        if not self.condition_logic.expressions_same_key(operands[0], placeholder):
            return None
        return self.unit_condition_for_expression(
            operands[1], conditions
        ) or self.negated_unit_condition_for_expression(operands[1], conditions)

    def placeholder_minus_one_unit_condition_guard_key(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> Optional[Tuple[Any, ...]]:
        """証明鍵に載せる **保存形式**（plain data）。付けられないなら `None`。"""

        return condition_identity_key(
            self.placeholder_minus_one_unit_condition(expr, placeholder, conditions)
        )

    def expression_is_placeholder_plus_unit_condition(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> bool:
        return (
            self.placeholder_plus_unit_condition(expr, placeholder, conditions) is not None
        )

    def placeholder_plus_unit_condition(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> Optional[Condition]:
        """置換子 + 単位条件の形を作っている条件そのもの（照合）。"""

        current = self.strip_transparent_unary(expr)
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return None
        if getattr(current, "operator", None) != "INT_ADD":
            return None
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return None
        left, right = operands
        if self.condition_logic.expressions_same_key(left, placeholder):
            return self.unit_condition_for_expression(right, conditions)
        if self.condition_logic.expressions_same_key(right, placeholder):
            return self.unit_condition_for_expression(left, conditions)
        return None

    def placeholder_plus_unit_condition_guard_key(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> Optional[Tuple[Any, ...]]:
        """証明鍵に載せる **保存形式**（plain data）。付けられないなら `None`。"""

        return condition_identity_key(
            self.placeholder_plus_unit_condition(expr, placeholder, conditions)
        )

    def unit_condition_for_expression(
        self,
        expr: Optional[Expression],
        conditions: Sequence[Condition],
    ) -> Optional[Condition]:
        """`expr` が 1 になる条件そのもの（照合）。"""

        current = self.strip_transparent_unary(expr)
        if current is None:
            return None
        for condition in conditions or ():
            if condition is None:
                continue
            if self.expression_is_one_under_conditions(current, (condition,)):
                return condition
        return None

    def unit_condition_key_for_expression(
        self,
        expr: Optional[Expression],
        conditions: Sequence[Condition],
    ) -> Optional[Tuple[Any, ...]]:
        """照合した条件の厳密な identity（載せられないなら `None`）。"""

        return condition_identity_key(self.unit_condition_for_expression(expr, conditions))

    def negated_unit_condition_for_expression(
        self,
        expr: Optional[Expression],
        conditions: Sequence[Condition],
    ) -> Optional[Condition]:
        """`expr` が「旗 - 1」の形になる条件そのもの（照合）。"""

        current = self.strip_transparent_unary(expr)
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return None
        if getattr(current, "operator", None) != "INT_SUB":
            return None
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2 or self.stack_protector.constant_int_value(operands[1]) != 1:
            return None
        flag_expr = self.strip_transparent_unary(operands[0])
        if flag_expr is None:
            return None
        for condition in conditions or ():
            if condition is None:
                continue
            if self.expression_is_zero_under_conditions(
                flag_expr, (condition,)
            ) and self.expression_is_one_under_conditions(flag_expr, (condition.negate(),)):
                return condition
        return None

    def negated_unit_condition_key_for_expression(
        self,
        expr: Optional[Expression],
        conditions: Sequence[Condition],
    ) -> Optional[Tuple[Any, ...]]:
        """照合した条件の厳密な identity（載せられないなら `None`）。"""

        return condition_identity_key(
            self.negated_unit_condition_for_expression(expr, conditions)
        )

    @staticmethod
    def strip_transparent_unary(expr: Optional[Expression]) -> Optional[Expression]:
        current = expr
        while (
            current is not None
            and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
            and getattr(current, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}
            and len(tuple(getattr(current, "operands", ()) or ())) == 1
        ):
            current = tuple(getattr(current, "operands", ()) or ())[0]
        return current

    def expression_is_placeholder_plus_constant(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        constant: int,
    ) -> bool:
        current = expr
        while (
            current is not None
            and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
            and getattr(current, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}
            and len(tuple(getattr(current, "operands", ()) or ())) == 1
        ):
            current = tuple(getattr(current, "operands", ()) or ())[0]
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return False
        operator = getattr(current, "operator", None)
        left, right = operands
        if operator == "INT_ADD":
            if self.condition_logic.expressions_same_key(left, placeholder) and self.stack_protector.constant_int_value(right) == constant:
                return True
            if self.condition_logic.expressions_same_key(right, placeholder) and self.stack_protector.constant_int_value(left) == constant:
                return True
            wrapped = self.stack_protector.constant_int_value(right)
            if self.condition_logic.expressions_same_key(left, placeholder) and wrapped is not None:
                return self.signed_unit_constant_matches(wrapped, constant, getattr(current, "size", None))
        if operator == "INT_SUB":
            if self.condition_logic.expressions_same_key(left, placeholder) and self.stack_protector.constant_int_value(right) == -constant:
                return True
        return False

    def signed_unit_constant_matches(self, value: int, expected: int, size: Optional[int]) -> bool:
        if value == expected:
            return True
        bits = max(1, int(size or 4)) * 8
        mask = (1 << bits) - 1
        return (int(value) & mask) == (int(expected) & mask)

    def condition_is_param_minus_one_nonpositive(
        self,
        condition: Condition,
        param: Expression,
        target_conditions: Sequence[Condition] = (),
    ) -> bool:
        if condition is None:
            return False
        expr = getattr(condition, "expression", None)
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        operands = tuple(getattr(expr, "operands", ()) or ())
        if len(operands) != 2:
            return False
        operator = getattr(expr, "operator", None)
        if operator == "INT_SLESSEQUAL" and not getattr(condition, "negated", False):
            return self.branch_guarded_expression_is_param_minus_one(operands[0], param, target_conditions) and self.stack_protector.constant_int_value(operands[1]) == 0
        if operator == "INT_SLESS" and getattr(condition, "negated", False):
            return self.stack_protector.constant_int_value(operands[0]) == 0 and self.branch_guarded_expression_is_param_minus_one(operands[1], param, target_conditions)
        return False

    def expression_is_one_under_conditions(
        self,
        expr: Optional[Expression],
        target_conditions: Sequence[Condition],
    ) -> bool:
        if self.stack_protector.constant_int_value(expr) == 1:
            return True
        current = expr
        while (
            current is not None
            and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
            and getattr(current, "operator", None) in {"INT_ZEXT", "INT_SEXT", "CAST", "COPY"}
            and len(tuple(getattr(current, "operands", ()) or ())) == 1
        ):
            current = tuple(getattr(current, "operands", ()) or ())[0]
        if current is None:
            return False
        if getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        if getattr(current, "operator", None) == "INT_SLESS":
            operands = tuple(getattr(current, "operands", ()) or ())
            if (
                len(operands) == 2
                and self.stack_protector.constant_int_value(operands[1]) == 1
                and getattr(operands[0], "expr_type", None) == ExpressionType.PARAMETER
                and any(
                    self.condition_logic.condition_is_signed_nonpositive_of_param(condition, operands[0])
                    for condition in target_conditions or ()
                )
            ):
                return True
        as_condition = Condition(current, False)
        if any(
            existing is not None
            and (
                existing.equals(as_condition)
                or ConditionNormalizer.are_equivalent(existing, as_condition)
            )
            for existing in target_conditions or ()
        ):
            return True
        return self.condition_logic.conditions_imply(tuple(target_conditions or ()), (as_condition,))

    def expression_is_param_minus_one(self, expr: Expression, param: Expression) -> bool:
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator not in {"INT_ADD", "INT_SUB"}:
            return False
        if len(expr.operands or ()) != 2:
            return False
        left, right = expr.operands
        if not self.condition_logic.expression_is_same_parameter(left, param):
            return False
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        try:
            value = int(right.value)
        except (TypeError, ValueError):
            return False
        bits = max(1, int(getattr(left, "size", 0) or getattr(expr, "size", 0) or 4)) * 8
        mask = (1 << bits) - 1
        if expr.operator == "INT_SUB":
            return value == 1
        return (value & mask) == mask

