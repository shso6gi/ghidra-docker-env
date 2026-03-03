# -*- coding: utf-8 -*-
"""条件の簡略化・矛盾検出モジュール（強化版）"""

from typing import List, Dict, Set, Optional, Tuple
from ...model import Expression, Condition, ExpressionType
from .normalizer import ConditionNormalizer


class ConditionSimplifier:
    """
    条件の簡略化と矛盾検出を行うクラス
    """
    
    # デバッグフラグ（外部から設定可能）
    DEBUG: bool = False
    
    @classmethod
    def _debug_print(cls, msg: str, indent: int = 0):
        if cls.DEBUG:
            prefix = "  " * indent
            print(f"{prefix}[CondSimplifier] {msg}")
    
    @classmethod
    def normalize_to_canonical(cls, condition: Condition) -> Tuple[str, str, str, bool]:
        """
        条件を正規形に変換（normalizer に委譲、表示用）
        
        Returns: (left_operand, operator, right_operand, is_positive)
        """
        return ConditionNormalizer.normalize(condition)
    
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
        
        cls._debug_print(f"flatten_condition: expr={expr.to_string()}, negated={negated}", 1)
        
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
            cls._debug_print(f"  [{i}] {cond.to_string()}", 1)
        
        # Step 1: 条件を平坦化（論理演算を展開）
        flattened = []
        for cond in conditions:
            expanded = cls.flatten_condition(cond)
            flattened.extend(expanded)
        
        cls._debug_print(f"After flattening ({len(flattened)} conditions):")
        for i, cond in enumerate(flattened):
            cls._debug_print(f"  [{i}] {cond.to_string()}", 1)
        
        # Step 2: 矛盾判定専用の正規化を使用
        # key: (left, op, right), value: {True, False} (polarities)
        comparison_map: Dict[Tuple[str, str, str], Set[bool]] = {}
        
        for cond in flattened:
            left, op, right, polarity = ConditionNormalizer.normalize_for_contradiction(cond)
            
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
        flattened_pairs = [(i, flattened[i]) for i in range(len(flattened))]
        for i in range(len(flattened_pairs)):
            for j in range(i + 1, len(flattened_pairs)):
                cond_i = flattened_pairs[i][1]
                cond_j = flattened_pairs[j][1]
                
                if ConditionNormalizer.are_contradictory(cond_i, cond_j):
                    cls._debug_print(
                        f"  CONTRADICTION: condition {i} and {j} are contradictory",
                        1
                    )
                    cls._debug_print(f"    {i}: {cond_i.to_string()}", 2)
                    cls._debug_print(f"    {j}: {cond_j.to_string()}", 2)
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
        
        result = []
        seen: Set[Tuple[str, str, str, bool]] = set()
        
        for cond in conditions:
            canonical = ConditionNormalizer.normalize_for_contradiction(cond)
            
            if canonical in seen:
                continue
            
            seen.add(canonical)
            result.append(cond)
        
        return result
    
    @classmethod
    def get_simplified_condition_string(cls, condition: Condition) -> str:
        """
        条件を簡略化した文字列で返す（normalizer に委譲）
        """
        return ConditionNormalizer.get_simplified_string(condition)