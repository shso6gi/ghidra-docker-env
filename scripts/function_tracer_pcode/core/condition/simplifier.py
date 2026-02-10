# -*- coding: utf-8 -*-
"""条件の簡略化・矛盾検出モジュール"""

from typing import List, Dict, Set, Optional, Tuple
from ...model import Expression, Condition, ExpressionType


class ConditionSimplifier:
    """
    条件の簡略化と矛盾検出を行うクラス
    """
    
    # 比較演算子の否定対応
    NEGATION_MAP = {
        "INT_EQUAL": "INT_NOTEQUAL",
        "INT_NOTEQUAL": "INT_EQUAL",
        "INT_LESS": "INT_SLESSEQUAL",  # !(a < b) => a >= b (近似)
        "INT_SLESS": "INT_SLESSEQUAL",
        "INT_LESSEQUAL": "INT_SLESS",  # !(a <= b) => a > b (近似)
        "INT_SLESSEQUAL": "INT_SLESS",
    }
    
    @classmethod
    def normalize_to_canonical(cls, condition: Condition) -> Tuple[str, str, str, bool]:
        """
        条件を正規形に変換
        Returns: (left_operand, operator, right_operand, is_positive)
        例: (not (param_2 == 0)) -> ("param_2", "!=", "0", True)
        """
        expr = condition.expression
        negated = condition.negated
        
        # 二重否定の解消とBOOL_NEGATEの処理
        while expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE":
            negated = not negated
            if expr.operands:
                expr = expr.operands[0]
            else:
                break
        
        # 二項比較演算の場合
        if expr.expr_type == ExpressionType.BINARY_OP:
            op = expr.operator
            if op in ("INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_SLESS", 
                      "INT_LESSEQUAL", "INT_SLESSEQUAL"):
                left = expr.operands[0].to_string() if expr.operands else ""
                right = expr.operands[1].to_string() if len(expr.operands) > 1 else ""
                
                # 否定されている場合は演算子を反転
                if negated:
                    op = cls.NEGATION_MAP.get(op, op)
                    negated = False
                
                return (left, op, right, not negated)
        
        # その他の場合は文字列として返す
        return (expr.to_string(), "", "", not negated)
    
    @classmethod
    def is_contradiction(cls, conditions: List[Condition]) -> bool:
        """
        条件リストが矛盾しているかチェック
        """
        if not conditions:
            return False
        
        # 正規化した条件を収集
        # (left, right) -> set of (operator, is_positive)
        comparisons: Dict[Tuple[str, str], Set[Tuple[str, bool]]] = {}
        
        for cond in conditions:
            left, op, right, is_positive = cls.normalize_to_canonical(cond)
            
            if op:  # 比較演算
                key = (left, right)
                if key not in comparisons:
                    comparisons[key] = set()
                comparisons[key].add((op, is_positive))
        
        # 矛盾チェック
        for (left, right), ops in comparisons.items():
            # 同じオペランドに対する比較を確認
            has_equal = ("INT_EQUAL", True) in ops
            has_notequal = ("INT_NOTEQUAL", True) in ops
            
            # (x == y) と (x != y) が両方ある
            if has_equal and has_notequal:
                return True
            
            # INT_EQUAL(positive) と INT_EQUAL(negative) が両方ある
            if ("INT_EQUAL", True) in ops and ("INT_EQUAL", False) in ops:
                return True
            if ("INT_NOTEQUAL", True) in ops and ("INT_NOTEQUAL", False) in ops:
                return True
        
        # 文字列ベースの矛盾チェック（補助）
        positive_exprs: Set[str] = set()
        negative_exprs: Set[str] = set()
        
        for cond in conditions:
            expr_str = cond.expression.to_string()
            if cond.negated:
                negative_exprs.add(expr_str)
            else:
                positive_exprs.add(expr_str)
        
        # 同じ式が肯定と否定で存在
        if positive_exprs & negative_exprs:
            return True
        
        return False
    
    @classmethod
    def are_equivalent_conditions(cls, cond1: Condition, cond2: Condition) -> bool:
        """
        2つの条件が等価かチェック
        例: (not (param_2 == 0)) と (param_2 != 0) は等価
        """
        norm1 = cls.normalize_to_canonical(cond1)
        norm2 = cls.normalize_to_canonical(cond2)
        
        return norm1 == norm2
    
    @classmethod
    def are_contradictory_conditions(cls, cond1: Condition, cond2: Condition) -> bool:
        """
        2つの条件が矛盾するかチェック
        例: (param_2 == 0) と (param_2 != 0) は矛盾
        """
        left1, op1, right1, pos1 = cls.normalize_to_canonical(cond1)
        left2, op2, right2, pos2 = cls.normalize_to_canonical(cond2)
        
        # 同じオペランドの比較
        if left1 == left2 and right1 == right2:
            # (x == y) と (x != y)
            if op1 == "INT_EQUAL" and op2 == "INT_NOTEQUAL" and pos1 == pos2:
                return True
            if op1 == "INT_NOTEQUAL" and op2 == "INT_EQUAL" and pos1 == pos2:
                return True
            # 同じ演算子で肯定/否定が異なる
            if op1 == op2 and pos1 != pos2:
                return True
        
        return False
    
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
            canonical = cls.normalize_to_canonical(cond)
            
            if canonical in seen:
                continue
            
            seen.add(canonical)
            result.append(cond)
        
        return result
    
    @classmethod
    def get_simplified_condition_string(cls, condition: Condition) -> str:
        """
        条件を簡略化した文字列で返す
        例: (not (param_2 == 0)) -> (param_2 != 0)
        """
        left, op, right, is_positive = cls.normalize_to_canonical(condition)
        
        if op:
            op_str = cls._operator_to_symbol(op)
            if is_positive:
                return f"({left} {op_str} {right})"
            else:
                return f"(not ({left} {op_str} {right}))"
        else:
            if is_positive:
                return left
            else:
                return f"(not {left})"
    
    @staticmethod
    def _operator_to_symbol(op: str) -> str:
        """演算子をシンボルに変換"""
        symbols = {
            "INT_EQUAL": "==",
            "INT_NOTEQUAL": "!=",
            "INT_LESS": "<",
            "INT_SLESS": "<",
            "INT_LESSEQUAL": "<=",
            "INT_SLESSEQUAL": "<=",
        }
        return symbols.get(op, op)