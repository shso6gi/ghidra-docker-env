# -*- coding: utf-8 -*-
"""条件の簡略化・矛盾検出モジュール（強化版）"""

from typing import Any, List, Dict, Set, Optional, Tuple
from ...model import Expression, Condition, ExpressionType
from ..debug import summarize_expression, summarize_condition
from .bitvector import eval_constant_raw, normalize_raw_value, to_signed_value
from .normalizer import ConditionNormalizer
from .scalar import ScalarConstraint, extract_scalar_constraint


class ConditionSimplifier:
    """
    条件の簡略化と矛盾検出を行うクラス
    """
    
    # デバッグフラグ（外部から設定可能）
    DEBUG: bool = False
    _DEBUG_MESSAGE_LIMIT: int = 2000
    _debug_message_count: int = 0
    _debug_suppressed: bool = False
    _DEBUG_REPEAT_LIMIT: int = 8
    _debug_repeat_counts: Dict[Tuple[str, str], int] = {}
    
    @classmethod
    def reset_debug_state(cls) -> None:
        cls._debug_message_count = 0
        cls._debug_suppressed = False
        cls._debug_repeat_counts.clear()

    @classmethod
    def _debug_available(cls) -> bool:
        return cls.DEBUG and cls._debug_message_count < cls._DEBUG_MESSAGE_LIMIT

    @classmethod
    def _debug_print(cls, msg: str, indent: int = 0):
        if not cls.DEBUG:
            return
        if cls._debug_message_count >= cls._DEBUG_MESSAGE_LIMIT:
            if not cls._debug_suppressed:
                prefix = "  " * indent
                print(
                    f"{prefix}[CondSimplifier] debug output suppressed after "
                    f"{cls._DEBUG_MESSAGE_LIMIT} messages"
                )
                cls._debug_suppressed = True
            return
        cls._debug_message_count += 1
        prefix = "  " * indent
        print(f"{prefix}[CondSimplifier] {msg}")

    @classmethod
    def _debug_expr_summary(cls, expr: Optional[Expression], max_depth: int = 4) -> str:
        if not cls._debug_available():
            return "<debug-suppressed>"
        return summarize_expression(expr, max_depth=max_depth)

    @classmethod
    def _debug_condition_summary(cls, condition: Optional[Condition], max_depth: int = 4) -> str:
        if not cls._debug_available():
            return "<debug-suppressed>"
        return summarize_condition(condition, max_depth=max_depth)

    @classmethod
    def _debug_condition_event(
        cls,
        event: str,
        condition: Condition,
        indent: int = 0,
    ) -> None:
        if not cls._debug_available():
            return

        summary = cls._debug_condition_summary(condition)
        key = (event, summary)
        count = cls._debug_repeat_counts.get(key, 0) + 1
        if len(cls._debug_repeat_counts) > 4096:
            cls._debug_repeat_counts.clear()
        cls._debug_repeat_counts[key] = count

        if count <= cls._DEBUG_REPEAT_LIMIT:
            cls._debug_print(f"{event}: {summary}", indent)
        elif count == cls._DEBUG_REPEAT_LIMIT + 1:
            cls._debug_print(
                f"{event}: {summary} (further repeats suppressed)",
                indent,
            )

    @classmethod
    def _conditions_structurally_equal(cls, left: Condition, right: Condition) -> bool:
        if left.negated != right.negated:
            return False
        if left.expression is right.expression:
            return True
        return left.expression.equals(right.expression)
    
    @classmethod
    def normalize_to_canonical(
        cls, condition: Condition
    ) -> Tuple[object, str, object, bool]:
        """
        条件を正規形に変換（normalizer に委譲、表示用）
        
        Returns: (left_operand, operator, right_operand, is_positive)
        """
        return ConditionNormalizer.normalize(condition)

    @classmethod
    def _normalize_raw_value(cls, value: int, bits: int) -> int:
        return normalize_raw_value(value, bits)

    @classmethod
    def _to_signed_value(cls, value: int, bits: int) -> int:
        return to_signed_value(value, bits)

    @classmethod
    def _eval_constant_raw(cls, expr: Expression) -> Optional[Tuple[int, int]]:
        return eval_constant_raw(expr)

    @classmethod
    def evaluate_condition_truth(cls, condition: Condition) -> Optional[bool]:
        expr = condition.expression
        negated = condition.negated

        while expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE":
            negated = not negated
            if expr.operands:
                expr = expr.operands[0]
            else:
                break

        evaluated = cls._eval_constant_raw(expr)
        if evaluated is None:
            return None

        raw_value, _bits = evaluated
        truth = raw_value != 0
        return not truth if negated else truth

    @classmethod
    def _extract_scalar_constraint(
        cls,
        condition: Condition,
    ) -> Optional[ScalarConstraint]:
        return extract_scalar_constraint(condition)

    @classmethod
    def extract_scalar_constraint(
        cls,
        condition: Condition,
    ) -> Optional[ScalarConstraint]:
        """条件を単一のスカラ制約として解釈する公開ラッパー"""
        return cls._extract_scalar_constraint(condition)

    @classmethod
    def _effective_lower_bound(
        cls,
        value: int,
        inclusive: bool,
        signed: bool,
        bits: int,
    ) -> int:
        minimum = -(1 << (bits - 1)) if signed else 0
        return max(minimum, value if inclusive else value + 1)

    @classmethod
    def _effective_upper_bound(
        cls,
        value: int,
        inclusive: bool,
        signed: bool,
        bits: int,
    ) -> int:
        maximum = (1 << (bits - 1)) - 1 if signed else (1 << bits) - 1
        return min(maximum, value if inclusive else value - 1)

    @classmethod
    def _bounds_contradict(
        cls,
        lower: Optional[Tuple[int, bool]],
        upper: Optional[Tuple[int, bool]],
        signed: bool,
        bits: int,
    ) -> bool:
        if lower is None or upper is None:
            return False
        lower_effective = cls._effective_lower_bound(lower[0], lower[1], signed, bits)
        upper_effective = cls._effective_upper_bound(upper[0], upper[1], signed, bits)
        return lower_effective > upper_effective

    @classmethod
    def _select_stronger_lower(
        cls,
        current: Optional[Tuple[int, bool, int]],
        candidate: Tuple[int, bool, int],
    ) -> Tuple[int, bool, int]:
        if current is None:
            return candidate

        current_effective = cls._effective_lower_bound(
            current[0],
            current[1],
            signed=False,
            bits=128,
        )
        candidate_effective = cls._effective_lower_bound(
            candidate[0],
            candidate[1],
            signed=False,
            bits=128,
        )

        if candidate_effective > current_effective:
            return candidate
        if candidate_effective < current_effective:
            return current
        return candidate if candidate[2] < current[2] else current

    @classmethod
    def _select_stronger_upper(
        cls,
        current: Optional[Tuple[int, bool, int]],
        candidate: Tuple[int, bool, int],
    ) -> Tuple[int, bool, int]:
        if current is None:
            return candidate

        current_effective = cls._effective_upper_bound(
            current[0],
            current[1],
            signed=False,
            bits=128,
        )
        candidate_effective = cls._effective_upper_bound(
            candidate[0],
            candidate[1],
            signed=False,
            bits=128,
        )

        if candidate_effective < current_effective:
            return candidate
        if candidate_effective > current_effective:
            return current
        return candidate if candidate[2] < current[2] else current

    @classmethod
    def _has_scalar_contradiction(cls, conditions: List[Condition]) -> bool:
        grouped: Dict[Tuple[str, int], Dict[str, Any]] = {}

        for index, cond in enumerate(conditions):
            fact = cls._extract_scalar_constraint(cond)
            if fact is None:
                continue

            group = grouped.setdefault(
                fact.key,
                {
                    "eq_raw_values": set(),
                    "ne_raw_values": set(),
                    "lower": {False: None, True: None},
                    "upper": {False: None, True: None},
                },
            )

            if fact.kind == "eq":
                group["eq_raw_values"].add(fact.raw_value)
            elif fact.kind == "ne":
                group["ne_raw_values"].add(fact.raw_value)
            elif fact.kind == "lower":
                signed = fact.signed
                current = group["lower"][signed]
                if fact.value is None or fact.inclusive is None:
                    continue
                candidate = (fact.value, fact.inclusive, index)
                if current is None:
                    group["lower"][signed] = candidate
                else:
                    current_effective = cls._effective_lower_bound(
                        current[0],
                        current[1],
                        signed=signed,
                        bits=fact.key[1],
                    )
                    candidate_effective = cls._effective_lower_bound(
                        candidate[0],
                        candidate[1],
                        signed=signed,
                        bits=fact.key[1],
                    )
                    if (
                        candidate_effective > current_effective
                        or (
                            candidate_effective == current_effective
                            and candidate[2] < current[2]
                        )
                    ):
                        group["lower"][signed] = candidate
            elif fact.kind == "upper":
                signed = fact.signed
                current = group["upper"][signed]
                if fact.value is None or fact.inclusive is None:
                    continue
                candidate = (fact.value, fact.inclusive, index)
                if current is None:
                    group["upper"][signed] = candidate
                else:
                    current_effective = cls._effective_upper_bound(
                        current[0],
                        current[1],
                        signed=signed,
                        bits=fact.key[1],
                    )
                    candidate_effective = cls._effective_upper_bound(
                        candidate[0],
                        candidate[1],
                        signed=signed,
                        bits=fact.key[1],
                    )
                    if (
                        candidate_effective < current_effective
                        or (
                            candidate_effective == current_effective
                            and candidate[2] < current[2]
                        )
                    ):
                        group["upper"][signed] = candidate

        for key, group in grouped.items():
            bits = key[1]
            eq_raw_values = group["eq_raw_values"]
            ne_raw_values = group["ne_raw_values"]

            if len(eq_raw_values) > 1:
                cls._debug_print(
                    f"  CONTRADICTION DETECTED: multiple equality constants for {key[0]} -> {sorted(eq_raw_values)}",
                    1,
                )
                return True

            if eq_raw_values:
                eq_raw_value = next(iter(eq_raw_values))
                if eq_raw_value in ne_raw_values:
                    cls._debug_print(
                        f"  CONTRADICTION DETECTED: {key[0]} == {eq_raw_value} and != {eq_raw_value}",
                        1,
                    )
                    return True
            for signed in (False, True):
                lower = group["lower"][signed]
                upper = group["upper"][signed]

                if cls._bounds_contradict(
                    (lower[0], lower[1]) if lower is not None else None,
                    (upper[0], upper[1]) if upper is not None else None,
                    signed,
                    bits,
                ):
                    cls._debug_print(
                        f"  CONTRADICTION DETECTED: incompatible bounds for {key[0]}",
                        1,
                    )
                    return True

                if eq_raw_values:
                    eq_value = (
                        cls._to_signed_value(eq_raw_value, bits)
                        if signed
                        else eq_raw_value
                    )
                    if lower is not None:
                        lower_effective = cls._effective_lower_bound(lower[0], lower[1], signed, bits)
                        if eq_value < lower_effective:
                            cls._debug_print(
                                f"  CONTRADICTION DETECTED: {key[0]} == {eq_value} violates lower bound",
                                1,
                            )
                            return True
                    if upper is not None:
                        upper_effective = cls._effective_upper_bound(upper[0], upper[1], signed, bits)
                        if eq_value > upper_effective:
                            cls._debug_print(
                                f"  CONTRADICTION DETECTED: {key[0]} == {eq_value} violates upper bound",
                                1,
                            )
                            return True
                    continue

                if lower is not None and upper is not None:
                    lower_effective = cls._effective_lower_bound(lower[0], lower[1], signed, bits)
                    upper_effective = cls._effective_upper_bound(upper[0], upper[1], signed, bits)
                    if lower_effective == upper_effective:
                        collapsed_raw = cls._normalize_raw_value(lower_effective, bits)
                        if collapsed_raw in ne_raw_values:
                            cls._debug_print(
                                f"  CONTRADICTION DETECTED: {key[0]} forced to excluded value {lower_effective}",
                                1,
                            )
                            return True

        return False
    
    @classmethod
    def flatten_condition(cls, condition: Condition) -> List[Condition]:
        """
        条件を平坦化（論理演算を展開）
        
        Examples:
            not (A or B) -> [not A, not B]
            not (A and B) -> [not A] or [not B] (CNF化が必要なので、この場合は展開しない)
            A or B -> そのまま（単一の選言なので分解不可）
        
        Returns:
            展開された条件のリスト（AND結合）、または元の条件
        """
        expr = condition.expression
        negated = condition.negated
        
        cls._debug_condition_event("flatten_condition", Condition(expr, negated), 1)
        
        # 二重否定を解消
        while expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE":
            negated = not negated
            if expr.operands:
                expr = expr.operands[0]
            else:
                break
        
        # not (A or B) -> (not A) and (not B)（ド・モルガンの法則）
        if negated and expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "BOOL_OR":
            cls._debug_print(f"  Detected: not (A or B)", 2)
            results = []
            for operand in expr.operands:
                # 各オペランドを否定
                results.append(Condition(operand, negated=True))
            cls._debug_print(f"  -> Flattened to {len(results)} conditions", 2)
            return results
        
        # not (A and B) -> (not A) or (not B)
        # これはCNF化が必要なので、ここでは扱わず元のまま返す
        if negated and expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "BOOL_AND":
            cls._debug_print(f"  Detected: not (A and B) - keeping as-is", 2)
            return [Condition(expr, negated=True)]
        
        # A and B -> [A, B]
        if not negated and expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "BOOL_AND":
            cls._debug_print(f"  Detected: A and B", 2)
            results = []
            for operand in expr.operands:
                results.append(Condition(operand, negated=False))
            cls._debug_print(f"  -> Flattened to {len(results)} conditions", 2)
            return results
        
        # それ以外はそのまま
        cls._debug_print(f"  -> No flattening", 2)
        return [Condition(expr, negated=negated)]

    @classmethod
    def _collect_implied_condition_norms(cls, conditions: List[Condition]) -> Set[Tuple[str, str, str, bool]]:
        implied: Set[Tuple[str, str, str, bool]] = set()
        stack = list(conditions or [])
        while stack:
            condition = stack.pop()
            if condition is None:
                continue
            normalized = ConditionNormalizer.normalize_for_contradiction(condition)
            implied.add(normalized)

            expr = condition.expression
            if (
                not condition.negated
                and expr is not None
                and expr.expr_type == ExpressionType.BINARY_OP
                and expr.operator == "BOOL_AND"
            ):
                stack.append(Condition(expr.operands[0], False))
                stack.append(Condition(expr.operands[1], False))

        return implied

    @classmethod
    def _condition_is_implied(
        cls,
        condition: Condition,
        implied_conditions: Set[Tuple[str, str, str, bool]],
    ) -> bool:
        normalized = ConditionNormalizer.normalize_for_contradiction(condition)
        if normalized in implied_conditions:
            return True

        expr = condition.expression
        if (
            not condition.negated
            and expr is not None
            and expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "BOOL_AND"
        ):
            stack = [Condition(expr.operands[0], False), Condition(expr.operands[1], False)]
            while stack:
                current = stack.pop()
                current_expr = current.expression
                if (
                    not current.negated
                    and current_expr is not None
                    and current_expr.expr_type == ExpressionType.BINARY_OP
                    and current_expr.operator == "BOOL_AND"
                ):
                    stack.append(Condition(current_expr.operands[0], False))
                    stack.append(Condition(current_expr.operands[1], False))
                    continue
                if ConditionNormalizer.normalize_for_contradiction(current) not in implied_conditions:
                    return False
            return True

        return False

    @classmethod
    def _condition_is_contradicted(
        cls,
        condition: Condition,
        context_conditions: List[Condition],
        implied_conditions: Optional[Set[Tuple[str, str, str, bool]]] = None,
    ) -> bool:
        implied = implied_conditions if implied_conditions is not None else cls._collect_implied_condition_norms(context_conditions)
        if cls._condition_is_implied(condition.negate(), implied):
            return True
        return any(
            ConditionNormalizer.are_contradictory(condition, context)
            for context in context_conditions
        )

    @classmethod
    def _reduce_expression_under_conditions(
        cls,
        expr: Expression,
        conditions: List[Condition],
    ) -> Expression:
        if expr is None:
            return expr

        if expr.expr_type == ExpressionType.PHI and expr.value:
            implied = cls._collect_implied_condition_norms(conditions)

            for cond, value in expr.value:
                if cond is None:
                    continue
                if cls._condition_is_implied(cond, implied):
                    return cls._reduce_expression_under_conditions(value, list(conditions) + [cond])

            surviving = []
            for cond, value in expr.value:
                if cond is not None and cls._condition_is_contradicted(cond, conditions, implied):
                    continue
                combined = list(conditions)
                if cond is not None:
                    combined.append(cond)
                reduced_value = cls._reduce_expression_under_conditions(value, combined)
                surviving.append((cond, reduced_value))

            if not surviving:
                return expr
            if len(surviving) == 1:
                return surviving[0][1]

            changed = len(surviving) != len(expr.value)
            if not changed:
                for (orig_cond, orig_value), (new_cond, new_value) in zip(expr.value, surviving):
                    if orig_cond != new_cond or orig_value is not new_value:
                        changed = True
                        break
            if not changed:
                return expr

            rebuilt = Expression.phi(surviving)
            rebuilt.size = expr.size
            return rebuilt

        if expr.expr_type in (
            ExpressionType.BINARY_OP,
            ExpressionType.UNARY_OP,
            ExpressionType.CALL,
            ExpressionType.MEMORY,
        ):
            new_operands = [cls._reduce_expression_under_conditions(op, conditions) for op in expr.operands]
            if all(new is old for new, old in zip(new_operands, expr.operands)):
                return expr
            rebuilt = Expression(
                expr_type=expr.expr_type,
                value=expr.value,
                operator=expr.operator,
                operands=new_operands,
                size=expr.size,
                name=expr.name,
                data_type=expr.data_type,
                data_type_obj=getattr(expr, "data_type_obj", None),
                storage_info=expr.storage_info,
                read_order_key=expr.read_order_key,
                runtime_ref=getattr(expr, "runtime_ref", None),
            )
            return rebuilt

        return expr

    @classmethod
    def _contextually_reduce_conditions(cls, conditions: List[Condition]) -> List[Condition]:
        current = list(conditions)
        for _ in range(4):
            reduced: List[Condition] = []
            changed = False
            for index, cond in enumerate(current):
                context = current[:index] + current[index + 1:]
                reduced_expr = cls._reduce_expression_under_conditions(cond.expression, context)
                rewritten = Condition(reduced_expr, cond.negated)
                flattened = cls.flatten_condition(rewritten)
                reduced.extend(flattened)
                if len(flattened) != 1 or not cls._conditions_structurally_equal(flattened[0], cond):
                    changed = True
            if not changed:
                return current
            current = reduced
        return current
    
    @classmethod
    def is_contradiction(cls, conditions: List[Condition]) -> bool:
        """
        条件リストが矛盾しているかチェック（強化版）
        
        normalize_for_contradiction() を使用することで、
        swap型の矛盾も確��に検出できる。
        """
        if not conditions:
            return False
        
        cls._debug_print("=" * 60)
        cls._debug_print("Checking contradiction (enhanced)")
        cls._debug_print(f"Input conditions ({len(conditions)}):")
        for i, cond in enumerate(conditions):
            cls._debug_print(f"  [{i}] {cls._debug_condition_summary(cond)}", 1)

        for i, cond in enumerate(conditions):
            truth_value = cls.evaluate_condition_truth(cond)
            if truth_value is False:
                cls._debug_print(
                    f"  CONTRADICTION DETECTED: condition {i} is constant false",
                    1
                )
                cls._debug_print(f"    {i}: {cls._debug_condition_summary(cond)}", 2)
                cls._debug_print("=" * 60)
                return True

        # Step 1: 条件を平坦化（論理演算を展開）
        flattened = []
        for cond in conditions:
            expanded = cls.flatten_condition(cond)
            flattened.extend(expanded)
        
        cls._debug_print(f"After flattening ({len(flattened)} conditions):")
        for i, cond in enumerate(flattened):
            cls._debug_print(f"  [{i}] {cls._debug_condition_summary(cond)}", 1)
        
        flattened = cls._contextually_reduce_conditions(flattened)

        cls._debug_print(f"After contextual reduction ({len(flattened)} conditions):")
        for i, cond in enumerate(flattened):
            cls._debug_print(f"  [{i}] {cls._debug_condition_summary(cond)}", 1)

        # Step 2: 矛盾判定専用の正規化を使用
        # key: (left, op, right), value: {True, False} (polarities)
        comparison_map: Dict[Tuple[str, str, str], Set[bool]] = {}
        unique_canonicals: Dict[Tuple[str, str, str, bool], Tuple[int, Condition]] = {}
        fallback_conditions: List[Tuple[int, Condition]] = []
        
        for index, cond in enumerate(flattened):
            canonical = ConditionNormalizer.normalize_for_contradiction(cond)
            if canonical in unique_canonicals:
                continue
            unique_canonicals[canonical] = (index, cond)

            left, op, right, polarity = canonical
            
            if cls.DEBUG:
                pol_str = "pos" if polarity else "neg"
                cls._debug_print(
                    f"  Canonical: ({left} {op} {right}) [{pol_str}]",
                    2
                )
            
            if op:  # 比較演算
                key = (left, op, right)
                if key not in comparison_map:
                    comparison_map[key] = set()
                comparison_map[key].add(polarity)
            else:
                fallback_conditions.append((index, cond))
        
        if cls.DEBUG:
            cls._debug_print(f"Comparison map ({len(comparison_map)} unique keys):")
            for (left, op, right), polarities in comparison_map.items():
                pol_str = ", ".join("pos" if p else "neg" for p in polarities)
                cls._debug_print(f"  ({left} {op} {right}): [{pol_str}]", 1)
        
        # Step 3: 同じkeyにTrueとFalseが両方ある場合は矛盾
        for key, polarities in comparison_map.items():
            if True in polarities and False in polarities:
                left, op, right = key
                cls._debug_print(
                    f"  CONTRADICTION DETECTED: ({left} {op} {right}) has both positive and negative",
                    1
                )
                cls._debug_print("=" * 60)
                return True
        
        # Step 4: ペア間の矛盾チェック（補助的）
        # normalize_for_contradiction() が同じkeyにマップしない矛盾もチェック
        for i in range(len(fallback_conditions)):
            for j in range(i + 1, len(fallback_conditions)):
                index_i, cond_i = fallback_conditions[i]
                index_j, cond_j = fallback_conditions[j]
                
                if ConditionNormalizer.are_contradictory(cond_i, cond_j):
                    cls._debug_print(
                        f"  CONTRADICTION: condition {index_i} and {index_j} are contradictory",
                        1
                    )
                    cls._debug_print(f"    {index_i}: {cls._debug_condition_summary(cond_i)}", 2)
                    cls._debug_print(f"    {index_j}: {cls._debug_condition_summary(cond_j)}", 2)
                    cls._debug_print("=" * 60)
                    return True

        unique_flattened = [cond for _index, cond in unique_canonicals.values()]

        if cls._has_scalar_contradiction(unique_flattened):
            cls._debug_print("=" * 60)
            return True
        
        cls._debug_print("  -> No contradiction detected")
        cls._debug_print("=" * 60)
        return False
    
    @classmethod
    def are_equivalent_conditions(cls, cond1: Condition, cond2: Condition) -> bool:
        """
        2つの条件が等価かチェック（normalizer に委譲）
        """
        return ConditionNormalizer.are_equivalent(cond1, cond2)
    
    @classmethod
    def are_contradictory_conditions(cls, cond1: Condition, cond2: Condition) -> bool:
        """
        2つの条件が矛盾するかチェック（normalizer に委譲）
        """
        return ConditionNormalizer.are_contradictory(cond1, cond2)
    
    @classmethod
    def simplify_conditions(cls, conditions: List[Condition]) -> List[Condition]:
        """
        条件リストを簡略化
        - 重複を削除
        - 等価な条件をまとめる
        """
        if not conditions:
            return []
        
        flattened = []
        for cond in conditions:
            truth_value = cls.evaluate_condition_truth(cond)
            if truth_value is True:
                continue
            flattened.extend(cls.flatten_condition(cond))

        flattened = cls._contextually_reduce_conditions(flattened)

        result = []
        seen: Set[Tuple[str, str, str, bool]] = set()
        scalar_groups: Dict[Tuple[str, int], Dict[str, Any]] = {}
        unsupported_indices: List[int] = []

        for index, cond in enumerate(flattened):
            truth_value = cls.evaluate_condition_truth(cond)
            if truth_value is True:
                continue

            canonical = ConditionNormalizer.normalize_for_contradiction(cond)

            if canonical in seen:
                continue
            
            seen.add(canonical)
            result.append(cond)

            fact = cls._extract_scalar_constraint(cond)
            if fact is None:
                unsupported_indices.append(len(result) - 1)
                continue

            group = scalar_groups.setdefault(
                fact.key,
                {
                    "eq": {},
                    "ne": {},
                    "lower": {False: None, True: None},
                    "upper": {False: None, True: None},
                },
            )
            current_index = len(result) - 1

            if fact.kind == "eq":
                group["eq"].setdefault(fact.raw_value, current_index)
            elif fact.kind == "ne":
                group["ne"].setdefault(fact.raw_value, current_index)
            elif fact.kind == "lower":
                signed = fact.signed
                if fact.value is None or fact.inclusive is None:
                    continue
                candidate = (fact.value, fact.inclusive, current_index)
                current = group["lower"][signed]
                if current is None:
                    group["lower"][signed] = candidate
                else:
                    current_effective = cls._effective_lower_bound(
                        current[0],
                        current[1],
                        signed=signed,
                        bits=fact.key[1],
                    )
                    candidate_effective = cls._effective_lower_bound(
                        candidate[0],
                        candidate[1],
                        signed=signed,
                        bits=fact.key[1],
                    )
                    if (
                        candidate_effective > current_effective
                        or (
                            candidate_effective == current_effective
                            and candidate[2] < current[2]
                        )
                    ):
                        group["lower"][signed] = candidate
            elif fact.kind == "upper":
                signed = fact.signed
                if fact.value is None or fact.inclusive is None:
                    continue
                candidate = (fact.value, fact.inclusive, current_index)
                current = group["upper"][signed]
                if current is None:
                    group["upper"][signed] = candidate
                else:
                    current_effective = cls._effective_upper_bound(
                        current[0],
                        current[1],
                        signed=signed,
                        bits=fact.key[1],
                    )
                    candidate_effective = cls._effective_upper_bound(
                        candidate[0],
                        candidate[1],
                        signed=signed,
                        bits=fact.key[1],
                    )
                    if (
                        candidate_effective < current_effective
                        or (
                            candidate_effective == current_effective
                            and candidate[2] < current[2]
                        )
                    ):
                        group["upper"][signed] = candidate

        keep_indices: Set[int] = set(unsupported_indices)
        for group in scalar_groups.values():
            if group["eq"]:
                keep_indices.add(min(group["eq"].values()))
                continue

            keep_indices.update(group["ne"].values())
            for signed in (False, True):
                if group["lower"][signed] is not None:
                    keep_indices.add(group["lower"][signed][2])
                if group["upper"][signed] is not None:
                    keep_indices.add(group["upper"][signed][2])

        return [cond for idx, cond in enumerate(result) if idx in keep_indices]
    
    @classmethod
    def get_simplified_condition_string(cls, condition: Condition) -> str:
        """
        条件を簡略化した文字列で返す（normalizer に委譲）
        """
        return ConditionNormalizer.get_simplified_string(condition)
