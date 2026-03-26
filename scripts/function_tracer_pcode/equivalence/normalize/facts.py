# -*- coding: utf-8 -*-
"""条件式から符号・範囲 facts を抽出"""

from typing import Dict, List, Set, Optional
from dataclasses import dataclass

from ...model import Condition, Expression, ExpressionType


@dataclass
class SignFacts:
    """符号・範囲に関する facts"""
    nonneg_vars: Set[str]  # 0 <= x が保証される変数
    pos_vars: Set[str]      # 0 < x が保証される変数
    neg_vars: Set[str]      # x < 0 が保証される変数
    nonzero_vars: Set[str]  # x != 0 が保証される変数
    nonneg_exprs: Set[str]  # 0 <= expr が保証される式
    pos_exprs: Set[str]      # 0 < expr が保証される式
    neg_exprs: Set[str]      # expr < 0 が保証される式
    nonzero_exprs: Set[str]  # expr != 0 が保証される式
    upper_bounds: Dict[str, int]  # x < C が保証される変数
    
    def __init__(self):
        self.nonneg_vars = set()
        self.pos_vars = set()
        self.neg_vars = set()
        self.nonzero_vars = set()
        self.nonneg_exprs = set()
        self.pos_exprs = set()
        self.neg_exprs = set()
        self.nonzero_exprs = set()
        self.upper_bounds = {}
    
    def merge(self, other: 'SignFacts') -> None:
        """他の facts をマージ"""
        self.nonneg_vars.update(other.nonneg_vars)
        self.pos_vars.update(other.pos_vars)
        self.neg_vars.update(other.neg_vars)
        self.nonzero_vars.update(other.nonzero_vars)
        self.nonneg_exprs.update(other.nonneg_exprs)
        self.pos_exprs.update(other.pos_exprs)
        self.neg_exprs.update(other.neg_exprs)
        self.nonzero_exprs.update(other.nonzero_exprs)
        for var_name, bound in other.upper_bounds.items():
            current = self.upper_bounds.get(var_name)
            if current is None or bound < current:
                self.upper_bounds[var_name] = bound
    
    def is_nonneg(self, var_name: str) -> bool:
        """変数が非負か"""
        return var_name in self.nonneg_vars or var_name in self.pos_vars
    
    def is_pos(self, var_name: str) -> bool:
        """変数が正か"""
        return var_name in self.pos_vars
    
    def is_neg(self, var_name: str) -> bool:
        """変数が負か"""
        return var_name in self.neg_vars
    
    def is_nonzero(self, var_name: str) -> bool:
        """変数が非ゼロか"""
        return var_name in self.nonzero_vars or var_name in self.pos_vars or var_name in self.neg_vars

    def is_expr_nonneg(self, expr: Expression) -> bool:
        key = _expr_key(expr)
        return key in self.nonneg_exprs or key in self.pos_exprs

    def is_expr_pos(self, expr: Expression) -> bool:
        return _expr_key(expr) in self.pos_exprs

    def is_expr_neg(self, expr: Expression) -> bool:
        return _expr_key(expr) in self.neg_exprs

    def is_expr_nonzero(self, expr: Expression) -> bool:
        key = _expr_key(expr)
        return key in self.nonzero_exprs or key in self.pos_exprs or key in self.neg_exprs

    def get_upper_bound(self, var_name: str) -> Optional[int]:
        """変数の既知の上限（排他的）を取得"""
        return self.upper_bounds.get(var_name)


def extract_sign_facts(
    conditions: List[Condition],
    debug: bool = False
) -> SignFacts:
    """
    条件式から符号・範囲 facts を抽出
    
    対応パターン:
    - param >= 0  -> nonneg
    - param > 0   -> pos (and nonneg, nonzero)
    - param < 0   -> neg (and nonzero)
    - param <= -1 -> neg (同上)
    - param != 0  -> nonzero
    - param < C  -> upper_bound=C （C>=0 の定数）
    - param <= C -> upper_bound=C+1 （C>=0 の定数）
    - (param & other) >= 0 と param < 0 -> other is nonneg
    - (param & other) < 0 -> both are neg
    
    Args:
        conditions: 条件のリスト
        debug: デバッグ出力
    
    Returns:
        SignFacts
    """
    facts = SignFacts()
    
    # 第1パス：基本的な比較から facts を収集
    for cond in conditions:
        # 否定されている場合はスキップ（保守的）
        if cond.negated:
            continue
        
        expr = cond.expression
        
        # 二項演算のみ対象
        if expr.expr_type != ExpressionType.BINARY_OP:
            continue
        
        if len(expr.operands) < 2:
            continue
        
        left = _normalize_fact_expr(expr.operands[0])
        right = _normalize_fact_expr(expr.operands[1])
        
        # 基本的な比較パターン
        _extract_from_comparison(expr.operator, left, right, facts, debug)
    
    # 第2パス：AND演算を含む複雑なパターンから推論
    for cond in conditions:
        if cond.negated:
            continue
        
        expr = cond.expression
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            continue
        
        if len(expr.operands) < 2:
            continue
        
        left = _normalize_fact_expr(expr.operands[0])
        right = _normalize_fact_expr(expr.operands[1])
        
        # AND演算を含む比較パターン
        _extract_from_and_comparison(expr.operator, left, right, facts, debug)
    
    return facts


def _extract_from_comparison(
    operator: Optional[str],
    left: Expression,
    right: Expression,
    facts: SignFacts,
    debug: bool
) -> None:
    """基本的な比較演算から facts を抽出"""
    
    # param >= 0 または 0 <= param
    if operator == "INT_SLESSEQUAL":  # <=
        # left <= right
        if _is_zero(left):
            # 0 <= param -> nonneg
            var_name = _get_var_name(right)
            if var_name:
                facts.nonneg_vars.add(var_name)
                if debug:
                    print(f"[Facts] {var_name} is nonneg (0 <= {var_name})")
            _record_expr_fact(facts.nonneg_exprs, right, debug, "expr is nonneg (0 <= expr)")
        
        elif _is_zero(right):
            # param <= 0 -> nonpos（今は使わない）
            pass

        elif _is_nonneg_constant(right):
            # param <= C -> param < C+1
            var_name = _get_integral_var_name(left)
            if var_name:
                _record_upper_bound(facts, var_name, right.value + 1, debug, "<=")
        
        elif _is_minus_one(right):
            # param <= -1 -> neg
            var_name = _get_var_name(left)
            if var_name:
                facts.neg_vars.add(var_name)
                facts.nonzero_vars.add(var_name)
                if debug:
                    print(f"[Facts] {var_name} is neg ({var_name} <= -1)")
            _record_expr_fact(facts.neg_exprs, left, debug, "expr is neg (expr <= -1)")
            _record_expr_fact(facts.nonzero_exprs, left, debug, "expr is nonzero (expr <= -1)")
    
    # param > 0 または 0 < param
    elif operator == "INT_SLESS":  # <
        # left < right
        if _is_zero(left):
            # 0 < param -> pos
            var_name = _get_var_name(right)
            if var_name:
                facts.pos_vars.add(var_name)
                facts.nonneg_vars.add(var_name)
                facts.nonzero_vars.add(var_name)
                if debug:
                    print(f"[Facts] {var_name} is pos (0 < {var_name})")
            _record_expr_fact(facts.pos_exprs, right, debug, "expr is pos (0 < expr)")
            _record_expr_fact(facts.nonneg_exprs, right, debug, "expr is nonneg (0 < expr)")
            _record_expr_fact(facts.nonzero_exprs, right, debug, "expr is nonzero (0 < expr)")
        
        elif _is_zero(right):
            # param < 0 -> neg
            var_name = _get_var_name(left)
            if var_name:
                facts.neg_vars.add(var_name)
                facts.nonzero_vars.add(var_name)
                if debug:
                    print(f"[Facts] {var_name} is neg ({var_name} < 0)")
            _record_expr_fact(facts.neg_exprs, left, debug, "expr is neg (expr < 0)")
            _record_expr_fact(facts.nonzero_exprs, left, debug, "expr is nonzero (expr < 0)")

        elif _is_nonneg_constant(right):
            # param < C -> upper_bound=C
            var_name = _get_integral_var_name(left)
            if var_name:
                _record_upper_bound(facts, var_name, right.value, debug, "<")

        elif _is_minus_one(left):
            # -1 < param -> param >= 0
            var_name = _get_integral_var_name(right)
            if var_name:
                facts.nonneg_vars.add(var_name)
                if debug:
                    print(f"[Facts] {var_name} is nonneg (-1 < {var_name}, integral)")
            _record_integral_expr_fact(
                facts.nonneg_exprs,
                right,
                debug,
                "expr is nonneg (-1 < expr, integral)",
            )
    
    # param != 0 または 0 != param
    elif operator in ("INT_NOTEQUAL", "distinct"):
        if _is_zero(left):
            var_name = _get_var_name(right)
            if var_name:
                facts.nonzero_vars.add(var_name)
                if debug:
                    print(f"[Facts] {var_name} is nonzero (0 != {var_name})")
            _record_expr_fact(facts.nonzero_exprs, right, debug, "expr is nonzero (0 != expr)")
        elif _is_zero(right):
            var_name = _get_var_name(left)
            if var_name:
                facts.nonzero_vars.add(var_name)
                if debug:
                    print(f"[Facts] {var_name} is nonzero ({var_name} != 0)")
            _record_expr_fact(facts.nonzero_exprs, left, debug, "expr is nonzero (expr != 0)")


def _extract_from_and_comparison(
    operator: Optional[str],
    left: Expression,
    right: Expression,
    facts: SignFacts,
    debug: bool
) -> None:
    """AND演算を含む比較から facts を推論"""
    
    # 0 <= (x & y) のパターン
    if operator == "INT_SLESSEQUAL":  # <=
        if _is_zero(left):
            # 0 <= (x & y)
            and_expr = right
            if _is_and_operation(and_expr):
                operands = and_expr.operands
                if len(operands) >= 2:
                    var1_name = _get_var_name(operands[0])
                    var2_name = _get_var_name(operands[1])
                    
                    # x < 0 が既知なら y >= 0
                    if var1_name and var2_name:
                        if facts.is_neg(var1_name):
                            facts.nonneg_vars.add(var2_name)
                            if debug:
                                print(f"[Facts] {var2_name} is nonneg (0 <= ({var1_name} & {var2_name}) and {var1_name} < 0)")
                        
                        if facts.is_neg(var2_name):
                            facts.nonneg_vars.add(var1_name)
                            if debug:
                                print(f"[Facts] {var1_name} is nonneg (0 <= ({var1_name} & {var2_name}) and {var2_name} < 0)")
    
    # (x & y) < 0 のパターン
    elif operator == "INT_SLESS":  # <
        if _is_and_operation(left) and _is_zero(right):
            # (x & y) < 0 -> both x and y have msb=1 -> both negative
            operands = left.operands
            if len(operands) >= 2:
                var1_name = _get_var_name(operands[0])
                var2_name = _get_var_name(operands[1])
                
                if var1_name:
                    facts.neg_vars.add(var1_name)
                    facts.nonzero_vars.add(var1_name)
                    if debug:
                        print(f"[Facts] {var1_name} is neg (({var1_name} & ...) < 0)")
                
                if var2_name:
                    facts.neg_vars.add(var2_name)
                    facts.nonzero_vars.add(var2_name)
                    if debug:
                        print(f"[Facts] {var2_name} is neg ((... & {var2_name}) < 0)")


def _is_zero(expr: Expression) -> bool:
    """式が定数0か"""
    return expr.expr_type == ExpressionType.CONSTANT and expr.value == 0


def _is_minus_one(expr: Expression) -> bool:
    """式が定数-1か"""
    return expr.expr_type == ExpressionType.CONSTANT and expr.value == -1


def _is_nonneg_constant(expr: Expression) -> bool:
    """式が0以上の定数か"""
    return expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int) and expr.value >= 0


def _is_and_operation(expr: Expression) -> bool:
    """式がAND演算（INT_AND）か"""
    return (expr.expr_type == ExpressionType.BINARY_OP and 
            expr.operator == "INT_AND")


def _get_var_name(expr: Expression) -> Optional[str]:
    """
    式からパラメータ/変数名を取得
    
    対応パターン:
    - PARAMETER/VARIABLE: そのまま
    
    保守的に、単純な PARAMETER/VARIABLE のみ対象
    bvneg(param) は扱わない（符号が反転するため）
    """
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        return expr.name
    
    return None


def _get_integral_var_name(expr: Expression) -> Optional[str]:
    """
    整数として扱ってよい PARAMETER/VARIABLE 名を取得

    `(-1) < x` を `0 <= x` とみなせるのは整数比較に限る。
    FLOAT 系を誤って符号 facts に入れないよう、data_type に float/double
    が見えている場合は保守的に除外する。
    """
    var_name = _get_var_name(expr)
    if not var_name:
        return None

    data_type = (expr.data_type or "").lower()
    if "float" in data_type or "double" in data_type:
        return None

    return var_name


def _normalize_fact_expr(expr: Expression) -> Expression:
    from .core import normalize_expression
    from .context import NormalizationContext

    return normalize_expression(expr, NormalizationContext())


def _record_expr_fact(
    target: Set[str],
    expr: Expression,
    debug: bool,
    message: str,
) -> None:
    key = _expr_key(expr)
    if not key:
        return
    target.add(key)
    if debug:
        print(f"[Facts] {message}: {key}")


def _record_integral_expr_fact(
    target: Set[str],
    expr: Expression,
    debug: bool,
    message: str,
) -> None:
    if not _is_integral_expression(expr):
        return
    _record_expr_fact(target, expr, debug, message)


def _is_integral_expression(expr: Expression) -> bool:
    data_type = (expr.data_type or "").lower()
    if "float" in data_type or "double" in data_type:
        return False
    return True


def _expr_key(expr: Expression) -> str:
    try:
        return expr.to_smt()
    except Exception:
        return ""


def _record_upper_bound(
    facts: SignFacts,
    var_name: str,
    bound: int,
    debug: bool,
    source: str
) -> None:
    """上限 facts を最小値優先で記録"""
    current = facts.upper_bounds.get(var_name)
    if current is None or bound < current:
        facts.upper_bounds[var_name] = bound
        if debug:
            print(f"[Facts] {var_name} has upper bound {bound} (source {source})")
