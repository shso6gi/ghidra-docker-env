# -*- coding: utf-8 -*-
"""条件の正規化モジュール（Expression構造ベース改善版）"""

from typing import Dict, Optional, Tuple
from weakref import WeakKeyDictionary
from ...model import (
    Expression,
    Condition,
    ExpressionType,
    StructuralKey,
    expression_key,
    key_is_comparable,
    expression_key_or_identity,
)


class ConditionNormalizer:
    """
    条件を正規化（canonical form）に変換するクラス
    
    否定を含む条件を正しく処理し、比較演算の場合はオペランド順序も考慮する。
    Expression構造を直接解析することで、より正確な正規化を実現。
    """

    _EXPR_KEY_MAX_NODES = 48
    _EXPR_KEY_CACHE_LIMIT = 4096
    _CONTRADICTION_CACHE_LIMIT = 8192
    # Keep the cache tied to the actual Expression object lifetime.  A plain
    # id(expr)-keyed dict can return stale structural keys after Python reuses
    # an object id for a new expression, which corrupts later condition
    # normalization and display.
    _expr_key_cache: WeakKeyDictionary = WeakKeyDictionary()
    _contradiction_cache: Dict[Tuple[Expression, bool], Tuple[StructuralKey, str, StructuralKey, bool]] = {}

    @classmethod
    def expression_signature(
        cls,
        expr: Optional[Expression],
        *,
        include_memory_read_order: bool = True,
    ) -> StructuralKey:
        """Stable structural key suitable for caches and deduplication."""
        if expr is None:
            return ("none",)
        return cls._condition_expr_key(
            expr,
            include_memory_read_order=include_memory_read_order,
        )

    @classmethod
    def conditions_signature(cls, conditions):
        canonical = []
        for cond in conditions or []:
            normalized = cls.normalize_for_contradiction(cond)
            canonical.append(normalized)
        canonical.sort()
        return tuple(canonical)
    
    @staticmethod
    def normalize(condition: Condition) -> Tuple[object, str, object, bool]:
        """
        条件を正規形に変換（表示用）
        
        Returns:
            (left_operand, operator, right_operand, is_positive)
            
        Examples:
            (param_1 < 0, negated=False) -> ("param_1", "INT_SLESS", "0", True)
            (param_1 < 0, negated=True) -> ("0", "INT_SLESSEQUAL", "param_1", True)
        """
        expr = condition.expression
        negated = condition.negated
        
        # 二重否定とBOOL_NEGATEの解消
        while expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE":
            negated = not negated
            if expr.operands:
                expr = expr.operands[0]
            else:
                break
        
        # 二項比較演算の場合
        if expr.expr_type == ExpressionType.BINARY_OP:
            op = expr.operator
            
            if op in ("INT_EQUAL", "INT_NOTEQUAL"):
                # 等価性比較：否定で反転
                left_key = ConditionNormalizer._condition_expr_key(
                    expr.operands[0] if expr.operands else None
                )
                right_key = ConditionNormalizer._condition_expr_key(
                    expr.operands[1] if len(expr.operands) > 1 else None
                )
                
                if negated:
                    # not (a == b) -> (a != b)
                    # not (a != b) -> (a == b)
                    if op == "INT_EQUAL":
                        return (left_key, "INT_NOTEQUAL", right_key, True)
                    else:
                        return (left_key, "INT_EQUAL", right_key, True)
                else:
                    return (left_key, op, right_key, True)
            
            elif op in ("INT_LESS", "INT_SLESS", "INT_LESSEQUAL", "INT_SLESSEQUAL"):
                # 不等式比較：否定でswapと演算子変換
                left_key = ConditionNormalizer._condition_expr_key(
                    expr.operands[0] if expr.operands else None
                )
                right_key = ConditionNormalizer._condition_expr_key(
                    expr.operands[1] if len(expr.operands) > 1 else None
                )
                if negated:
                    # not (a < b) -> (a >= b) = (b <= a) with swap
                    # not (a <= b) -> (a > b) = (b < a) with swap
                    new_op = ConditionNormalizer._negate_comparison_op(op)
                    return (right_key, new_op, left_key, True)
                else:
                    return (left_key, op, right_key, True)
        
        # その他の場合は構造キーとして返す
        return (ConditionNormalizer._condition_expr_key(expr), "", ("none",), negated)
    
    @staticmethod
    def _normalized_term_to_string(term: object) -> str:
        """正規化トークンを表示文字列へ変換（to_string 非依存）。"""
        if isinstance(term, str):
            return term
        if isinstance(term, tuple):
            rendered = ConditionNormalizer._structural_key_to_string(term)
            if rendered is not None:
                return rendered
        return repr(term)

    @staticmethod
    def _atom_to_string(atom: object) -> Optional[str]:
        if not isinstance(atom, tuple) or not atom:
            return None
        tag = atom[0]
        if tag == "int" and len(atom) >= 2:
            return str(atom[1])
        if tag == "str" and len(atom) >= 2:
            return str(atom[1])
        if tag == "none":
            return ""
        return None

    @staticmethod
    def _structural_key_to_string(key: StructuralKey) -> Optional[str]:
        if not isinstance(key, tuple) or not key:
            return None
        tag = key[0]
        if tag == "const" and len(key) >= 2:
            return ConditionNormalizer._atom_to_string(key[1])
        if tag in {"parameter", "variable", "unknown"} and len(key) >= 2:
            name = key[1]
            return str(name) if name else tag
        if tag == "none":
            return ""
        if tag == "unary" and len(key) >= 4:
            operand = ConditionNormalizer._structural_key_to_string(key[3])
            if operand is None:
                return None
            op = key[1]
            if op == "INT_NEGATE":
                return f"(~{operand})"
            if op == "INT_2COMP":
                return f"(-{operand})"
            if op == "BOOL_NEGATE":
                return f"(not {operand})"
            return f"{op}({operand})"
        if tag == "binary" and len(key) >= 5:
            left = ConditionNormalizer._structural_key_to_string(key[3])
            right = ConditionNormalizer._structural_key_to_string(key[4])
            if left is None or right is None:
                return None
            op = key[1]
            symbol = ConditionNormalizer._operator_to_symbol(op)
            if symbol != op:
                return f"({left} {symbol} {right})"
            return f"{op}({left}, {right})"
        if tag == "memory" and len(key) >= 3:
            address = ConditionNormalizer._structural_key_to_string(key[2])
            if address is None:
                return None
            return f"MEM[{address}]"
        return None
    
    @staticmethod
    def normalize_for_contradiction(condition: Condition) -> Tuple[StructuralKey, str, StructuralKey, bool]:
        """
        矛盾判定専用の正規化（Expression構造ベース改善版）
        
        同じ (left, op, right) に対して polarity (True/False) で表現することで、
        swap型の矛盾を確実に検出できるようにする。
        
        改善点：
        1. (-x) == 0 ↔ x == 0 の正規化（BitVec意味論）
        2. Expression構造を直接見る定数判定
        3. より正確なswap判定
        
        Returns:
            (left_operand, operator, right_operand, polarity)
            
        Examples:
            (param_1 < 0, negated=False) 
                -> ("param_1", "INT_SLESS", "0", True)
            
            (param_1 < 0, negated=True) = (param_1 >= 0)
                -> ("param_1", "INT_SLESS", "0", False)
            
            ((-param_2) == 0, negated=False)
                -> ("param_2", "INT_EQUAL", "0", True)  # INT_2COMP を剥がす
            
            (param_2 != 0, negated=False)
                -> ("param_2", "INT_EQUAL", "0", False)  # INT_EQUAL に統一
        """
        cache_key = (condition.expression, condition.negated)
        cached = ConditionNormalizer._contradiction_cache.get(cache_key)
        if cached is not None:
            return cached

        expr = condition.expression
        negated = condition.negated
        
        # 二重否定とBOOL_NEGATEの解消
        while expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE":
            negated = not negated
            if expr.operands:
                expr = expr.operands[0]
            else:
                break
        
        if expr.expr_type == ExpressionType.BINARY_OP:
            op = expr.operator
            left_expr = expr.operands[0] if expr.operands else None
            right_expr = expr.operands[1] if len(expr.operands) > 1 else None
            
            # 等価性比較
            if op in ("INT_EQUAL", "INT_NOTEQUAL"):
                # ★★★ 改善1: (-x) == 0 ↔ x == 0 の正規化 ★★★
                normalized_left, normalized_right = ConditionNormalizer._normalize_zero_comparison(
                    left_expr, right_expr
                )
                
                left_key = ConditionNormalizer._condition_expr_key(normalized_left)
                right_key = ConditionNormalizer._condition_expr_key(normalized_right)
                
                # 左右を辞書順にソート（順序依存性を排除）
                if ConditionNormalizer._should_swap_operands(normalized_left, normalized_right):
                    left_key, right_key = right_key, left_key
                
                # INT_EQUAL に統一
                if op == "INT_EQUAL":
                    polarity = not negated
                else:  # INT_NOTEQUAL は INT_EQUAL の否定
                    polarity = negated

                result = (left_key, "INT_EQUAL", right_key, polarity)
                ConditionNormalizer._remember_contradiction_key(cache_key, result)
                return result
            
            # 不等式比較
            elif op in ("INT_SLESS", "INT_SLESSEQUAL", "INT_LESS", "INT_LESSEQUAL"):
                left_key = ConditionNormalizer._condition_expr_key(left_expr)
                right_key = ConditionNormalizer._condition_expr_key(right_expr)
                
                # ★★★ 改善2: Expression構造ベースのswap判定 ★★★
                need_swap = ConditionNormalizer._should_swap_operands(left_expr, right_expr)
                
                if need_swap:
                    # swap してオペランドを入れ替え
                    left_key, right_key = right_key, left_key
                    new_op, final_negated = ConditionNormalizer._swap_comparison(op, negated)
                else:
                    new_op = op
                    final_negated = negated
                
                polarity = not final_negated
                result = (left_key, new_op, right_key, polarity)
                ConditionNormalizer._remember_contradiction_key(cache_key, result)
                return result
        
        # その他の場合
        result = (ConditionNormalizer._condition_expr_key(expr), "", "", not negated)
        ConditionNormalizer._remember_contradiction_key(cache_key, result)
        return result
    
    @staticmethod
    def _normalize_zero_comparison(
        left_expr: Optional[Expression],
        right_expr: Optional[Expression]
    ) -> Tuple[Optional[Expression], Optional[Expression]]:
        """
        0との比較において、(-x) を x に正規化
        
        BitVec意味論では (-x) == 0 ⟺ x == 0 が成り立つため、
        INT_2COMP や INT_NEGATE を剥がすことができる。
        
        Args:
            left_expr: 左辺のExpression
            right_expr: 右辺のExpression
        
        Returns:
            正規化された (left_expr, right_expr)
        
        Examples:
            (INT_2COMP(param_2), 0) -> (param_2, 0)
            (0, INT_2COMP(param_2)) -> (0, param_2)
        """
        if not left_expr or not right_expr:
            return (left_expr, right_expr)
        
        # 右辺が0の場合、左辺の INT_2COMP/INT_NEGATE を剥がす
        if ConditionNormalizer._is_zero(right_expr):
            if left_expr.expr_type == ExpressionType.UNARY_OP:
                if left_expr.operator in ("INT_2COMP", "INT_NEGATE"):
                    # (-x) == 0 → x == 0
                    if left_expr.operands:
                        return (left_expr.operands[0], right_expr)
        
        # 左辺が0の場合、右辺の INT_2COMP/INT_NEGATE を剥がす
        if ConditionNormalizer._is_zero(left_expr):
            if right_expr.expr_type == ExpressionType.UNARY_OP:
                if right_expr.operator in ("INT_2COMP", "INT_NEGATE"):
                    # 0 == (-x) → 0 == x
                    if right_expr.operands:
                        return (left_expr, right_expr.operands[0])
        
        return (left_expr, right_expr)
    
    @staticmethod
    def _is_zero(expr: Optional[Expression]) -> bool:
        """
        Expressionが0を表すかチェック（構造ベース）
        
        Args:
            expr: チェック対象のExpression
        
        Returns:
            0の場合True
        """
        if not expr:
            return False

        if expr.expr_type == ExpressionType.CONSTANT:
            return expr.value == 0

        if expr.expr_type == ExpressionType.LITERAL:
            # リテラルの場合、値をチェック
            try:
                value = int(expr.value, 0)  # 0プレフィックスで基数自動判定
                return value == 0
            except (ValueError, TypeError, AttributeError):
                pass

        # -0 は 0 と同値
        if expr.expr_type == ExpressionType.UNARY_OP:
            if expr.operator in ("INT_2COMP", "INT_NEGATE") and expr.operands:
                return ConditionNormalizer._is_zero(expr.operands[0])
        
        return False
    
    @staticmethod
    def _should_swap_operands(
        left_expr: Optional[Expression],
        right_expr: Optional[Expression]
    ) -> bool:
        """
        オペランドをswapすべきかどうか判定（Expression構造ベース）
        
        方針：
        1. 変数を左に、定数を右に配置
        2. 両方変数または両方定数の場合、文字列の辞書順で決定
        
        Args:
            left_expr: 左辺のExpression
            right_expr: 右辺のExpression
        
        Returns:
            swapすべき場合True
        """
        if not left_expr or not right_expr:
            return False
        
        left_is_const = ConditionNormalizer._is_constant_expr(left_expr)
        right_is_const = ConditionNormalizer._is_constant_expr(right_expr)
        
        # 左が定数で右が変数 → swap
        if left_is_const and not right_is_const:
            return True
        # 左が変数で右が定数 → swap不要
        if not left_is_const and right_is_const:
            return False
        
        # 両方変数または両方定数の場合、辞書順で小さい方を左に
        left_str = ConditionNormalizer._condition_expr_key(left_expr)
        right_str = ConditionNormalizer._condition_expr_key(right_expr)
        return left_str > right_str

    @classmethod
    def _remember_contradiction_key(
        cls,
        key: Tuple[Expression, bool],
        value: Tuple[StructuralKey, str, StructuralKey, bool],
    ) -> None:
        if len(cls._contradiction_cache) >= cls._CONTRADICTION_CACHE_LIMIT:
            cls._contradiction_cache.clear()
        cls._contradiction_cache[key] = value

    @classmethod
    def _expr_key(
        cls,
        expr: Optional[Expression],
        *,
        include_memory_read_order: bool = True,
    ) -> StructuralKey:
        if expr is None:
            return ("none",)

        cache_mode = bool(include_memory_read_order)
        cached_by_mode = cls._expr_key_cache.get(expr)
        if cached_by_mode is not None and cache_mode in cached_by_mode:
            return cached_by_mode[cache_mode]

        rendered = expression_key(
            expr,
            budget=cls._EXPR_KEY_MAX_NODES,
            normalize_commutative=True,
            include_memory_read_order=include_memory_read_order,
        )
        if len(cls._expr_key_cache) >= cls._EXPR_KEY_CACHE_LIMIT:
            cls._expr_key_cache.clear()
        if cached_by_mode is None:
            cached_by_mode = {}
            cls._expr_key_cache[expr] = cached_by_mode
        cached_by_mode[cache_mode] = rendered
        return rendered

    @staticmethod
    def _condition_expr_key(
        expr: Optional[Expression],
        *,
        include_memory_read_order: bool = True,
    ) -> StructuralKey:
        if expr is None:
            return ("none",)
        key = ConditionNormalizer._expr_key(
            expr,
            include_memory_read_order=include_memory_read_order,
        )
        if key_is_comparable(key):
            return key
        return expression_key_or_identity(expr)
    
    @staticmethod
    def _is_constant_expr(expr: Expression) -> bool:
        """
        Expressionが定数かどうか判定（構造ベース）
        
        Args:
            expr: チェック対象のExpression
        
        Returns:
            定数の場合True
        """
        if expr.expr_type in (ExpressionType.CONSTANT, ExpressionType.LITERAL):
            return True
        
        # INT_2COMP や INT_NEGATE の内部が定数の場合も定数扱い
        if expr.expr_type == ExpressionType.UNARY_OP:
            if expr.operator in ("INT_2COMP", "INT_NEGATE"):
                if expr.operands:
                    return ConditionNormalizer._is_constant_expr(expr.operands[0])
        
        return False
    
    @staticmethod
    def _swap_comparison(op: str, negated: bool) -> Tuple[str, bool]:
        """
        比較演算子を swap する
        
        a op b (negated) を b op' a (final_negated) に変換
        
        変換規則：
        - (a < b) → (b > a) = not (b <= a)
        - (a <= b) → (b >= a) = not (b < a)
        - not (a < b) = (a >= b) → (b <= a)
        - not (a <= b) = (a > b) → (b < a)
        
        Returns:
            (new_op, final_negated)
        """
        if op == "INT_SLESS":
            # a < b → b > a = not (b <= a)
            # not (a < b) → b <= a
            return ("INT_SLESSEQUAL", negated)
        elif op == "INT_SLESSEQUAL":
            # a <= b → b >= a = not (b < a)
            # not (a <= b) → b < a
            return ("INT_SLESS", negated)
        elif op == "INT_LESS":
            # unsigned版
            return ("INT_LESSEQUAL", negated)
        elif op == "INT_LESSEQUAL":
            # unsigned版
            return ("INT_LESS", negated)
        else:
            return (op, negated)
    
    @staticmethod
    def _negate_comparison_op(op: str) -> str:
        """
        比較演算子の否定を返す（swap前提、表示用）
        
        not (a < b) = (a >= b) = (b <= a) → swap後は <=
        not (a <= b) = (a > b) = (b < a) → swap後は <
        """
        negation_map = {
            # not (a < b) = (b <= a)
            "INT_LESS": "INT_LESSEQUAL",
            "INT_SLESS": "INT_SLESSEQUAL",
            # not (a <= b) = (b < a)
            "INT_LESSEQUAL": "INT_LESS",
            "INT_SLESSEQUAL": "INT_SLESS",
        }
        return negation_map.get(op, op)
    
    @staticmethod
    def get_simplified_string(condition: Condition) -> str:
        """
        条件を簡略化した文字列で返す（表示用）
        
        Examples:
            (param_1 < 0, negated=False) -> "(param_1 < 0)"
            (param_1 < 0, negated=True) -> "(param_1 >= 0)" = "(0 <= param_1)"
        """
        left, op, right, is_positive = ConditionNormalizer.normalize(condition)
        
        left_display = ConditionNormalizer._normalized_term_to_string(left)
        right_display = ConditionNormalizer._normalized_term_to_string(right)
        if op:
            op_str = ConditionNormalizer._operator_to_symbol(op)
            if is_positive:
                return f"({left_display} {op_str} {right_display})"
            else:
                return f"(not ({left_display} {op_str} {right_display}))"
        else:
            if not is_positive:
                return left_display
            else:
                return f"(not {left_display})"
    
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
    
    @staticmethod
    def are_equivalent(cond1: Condition, cond2: Condition) -> bool:
        """
        2つの条件が等価かチェック
        
        Examples:
            (param_1 < 0, negated=True) と (param_1 >= 0, negated=False) は等価
        """
        norm1 = ConditionNormalizer.normalize_for_contradiction(cond1)
        norm2 = ConditionNormalizer.normalize_for_contradiction(cond2)
        
        return norm1 == norm2
    
    @staticmethod
    def are_contradictory(cond1: Condition, cond2: Condition) -> bool:
        """
        2つの条件が矛盾するかチェック
        
        Examples:
            (param_1 == 0) と (param_1 != 0) は矛盾
            (param_1 < 0) と (param_1 >= 0) は矛盾
            (param_1 < 0) と (0 <= param_1) は矛盾
            (param_2 != 0) と ((-param_2) == 0) は矛盾
        """
        left1, op1, right1, pol1 = ConditionNormalizer.normalize_for_contradiction(cond1)
        left2, op2, right2, pol2 = ConditionNormalizer.normalize_for_contradiction(cond2)
        
        # 同じ (left, op, right) で polarity が異なる場合は矛盾
        if left1 == left2 and op1 == op2 and right1 == right2:
            if pol1 != pol2:
                return True
        
        return False
