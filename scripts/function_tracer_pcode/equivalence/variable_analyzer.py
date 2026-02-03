# -*- coding: utf-8 -*-
"""追加変数の分析モジュール

パラメータ以外の変数（in_a1_hi等）を検出・分析し、
安全に0制約できるかを判定する。
"""

import re
from typing import List, Dict, Set, Optional
from dataclasses import dataclass, field
from enum import Enum, auto

from ..expression import Expression, ExpressionType, Condition
from ..return_analyzer import FunctionReturnAnalysis


class VariableUsageType(Enum):
    """変数の使用タイプ"""
    CONDITION_ONLY = auto()      # 条件式でのみ使用
    RETURN_VALUE = auto()        # 戻り値計算で使用
    BOTH = auto()                # 両方で使用
    UNKNOWN = auto()             # 不明


class ConstraintRecommendation(Enum):
    """制約の推奨"""
    SAFE_TO_ZERO = auto()        # 安全に0制約可能
    UNSAFE = auto()              # 0制約すべきでない
    NEEDS_MANUAL_REVIEW = auto() # 手動確認が必要


@dataclass
class VariableUsageInfo:
    """変数の使用情報"""
    in_condition: bool = False
    in_return_value: bool = False
    in_piece_upper: bool = False  # PIECE演算の上位部分として使用
    piece_contexts: List[str] = field(default_factory=list)  # PIECE使用のコンテキスト


@dataclass
class ExtraVariableAnalysis:
    """追加変数の分析結果"""
    name: str
    bit_width: int
    usage: VariableUsageInfo
    is_upper_bits_pattern: bool
    recommendation: ConstraintRecommendation
    reason: str
    
    def can_safely_constrain_to_zero(self) -> bool:
        """安全に0制約できるか"""
        return self.recommendation == ConstraintRecommendation.SAFE_TO_ZERO
    
    def to_dict(self) -> Dict:
        return {
            "name": self.name,
            "bit_width": self.bit_width,
            "is_upper_bits_pattern": self.is_upper_bits_pattern,
            "used_in_condition": self.usage.in_condition,
            "used_in_return_value": self.usage.in_return_value,
            "used_in_piece_upper": self.usage.in_piece_upper,
            "recommendation": self.recommendation.name,
            "reason": self.reason,
        }


class VariableAnalyzer:
    """追加変数を分析するクラス"""
    
    # 上位ビット変数のパターン
    UPPER_BITS_PATTERNS = [
        r'^in_[a-z]\d+_hi$',     # in_a0_hi, in_a1_hi, in_v0_hi 等
        r'^[a-z]\d+_hi$',        # a0_hi, a1_hi, v0_hi 等
        r'^in_.*_hi$',           # その他の in_*_hi パターン
        r'^.*_hi$',              # その他の *_hi パターン
    ]
    
    def __init__(self, debug: bool = False):
        self.debug = debug
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[VariableAnalyzer] {msg}")
    
    def is_upper_bits_pattern(self, var_name: str) -> bool:
        """変数名が上位ビットパターンに一致するか"""
        for pattern in self.UPPER_BITS_PATTERNS:
            if re.match(pattern, var_name):
                return True
        return False
    
    def analyze_variable_usage(
        self,
        var_name: str,
        analysis: FunctionReturnAnalysis
    ) -> VariableUsageInfo:
        """変数の使用パターンを分析"""
        usage = VariableUsageInfo()
        
        for ret in analysis.returns:
            # 戻り値での使用をチェック
            if hasattr(ret.value, 'get_all_variables'):
                if var_name in ret.value.get_all_variables():
                    usage.in_return_value = True
                    # PIECE演算の上位部分としての使用をチェック
                    self._check_piece_usage(ret.value, var_name, usage)
            
            # 条件式での使用をチェック
            for cond in ret.conditions:
                if hasattr(cond, 'get_all_variables'):
                    if var_name in cond.get_all_variables():
                        usage.in_condition = True
                        # 条件式内のPIECE使用もチェック
                        if hasattr(cond, 'expression'):
                            self._check_piece_usage(cond.expression, var_name, usage)
        
        return usage
    
    def _check_piece_usage(
        self,
        expr: Expression,
        var_name: str,
        usage: VariableUsageInfo
    ) -> None:
        """PIECE演算での使用パターンをチェック"""
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "PIECE":
            # 上位部分（第1オペランド）をチェック
            high = expr.operands[0]
            if self._expr_contains_variable(high, var_name):
                usage.in_piece_upper = True
                # コンテキストを記録
                low = expr.operands[1]
                context = f"PIECE({high.to_string()}, {low.to_string()})"
                if context not in usage.piece_contexts:
                    usage.piece_contexts.append(context)
        
        # 再帰的にチェック
        for operand in expr.operands:
            self._check_piece_usage(operand, var_name, usage)
        
        # PHIノードもチェック
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, val in expr.value:
                if hasattr(val, 'operands'):
                    self._check_piece_usage(val, var_name, usage)
    
    def _expr_contains_variable(self, expr: Expression, var_name: str) -> bool:
        """式が指定した変数を含むか"""
        if expr.expr_type in (ExpressionType.VARIABLE, ExpressionType.PARAMETER):
            return expr.name == var_name
        
        for operand in expr.operands:
            if self._expr_contains_variable(operand, var_name):
                return True
        
        return False
    
    def analyze_extra_variable(
        self,
        var_name: str,
        bit_width: int,
        analysis: FunctionReturnAnalysis,
        return_bit_width: int
    ) -> ExtraVariableAnalysis:
        """
        追加変数を分析し、0制約の安全性を判定
        
        Args:
            var_name: 変数名
            bit_width: 変数のビット幅
            analysis: 関数解析結果
            return_bit_width: 戻り値のビット幅
        
        Returns:
            ExtraVariableAnalysis: 分析結果
        """
        is_upper = self.is_upper_bits_pattern(var_name)
        usage = self.analyze_variable_usage(var_name, analysis)
        
        self._debug_print(f"Analyzing '{var_name}':")
        self._debug_print(f"  - Is upper bits pattern: {is_upper}")
        self._debug_print(f"  - Used in condition: {usage.in_condition}")
        self._debug_print(f"  - Used in return value: {usage.in_return_value}")
        self._debug_print(f"  - Used in PIECE upper: {usage.in_piece_upper}")
        self._debug_print(f"  - Return bit width: {return_bit_width}")
        
        # 安全性の判定
        recommendation, reason = self._determine_recommendation(
            var_name, bit_width, is_upper, usage, return_bit_width
        )
        
        self._debug_print(f"  - Recommendation: {recommendation.name}")
        self._debug_print(f"  - Reason: {reason}")
        
        return ExtraVariableAnalysis(
            name=var_name,
            bit_width=bit_width,
            usage=usage,
            is_upper_bits_pattern=is_upper,
            recommendation=recommendation,
            reason=reason
        )
    
    def _determine_recommendation(
        self,
        var_name: str,
        bit_width: int,
        is_upper: bool,
        usage: VariableUsageInfo,
        return_bit_width: int
    ) -> tuple:
        """
        0制約の推奨を決定
        
        安全に0制約できる条件:
        1. 上位ビットパターン（in_*_hi等）である
        2. 戻り値のビット幅が変数のビット幅以下（32ビット以下）
        3. 以下のいずれか:
           a) 戻り値計算に使用されていない
           b) PIECE演算の上位部分としてのみ使用されている
        
        Returns:
            (ConstraintRecommendation, reason)
        """
        # 条件1: 上位ビットパターンでなければ安全でない
        if not is_upper:
            return (
                ConstraintRecommendation.NEEDS_MANUAL_REVIEW,
                f"Variable '{var_name}' does not match upper-bits pattern"
            )
        
        # 条件2: 戻り値のビット幅が変数のビット幅より大きければ、上位ビットが影響する可能性
        if return_bit_width > bit_width:
            return (
                ConstraintRecommendation.UNSAFE,
                f"Return type ({return_bit_width}bit) is wider than variable ({bit_width}bit)"
            )
        
        # 条件3a: 戻り値計算に使用されていない場合は安全
        if not usage.in_return_value:
            return (
                ConstraintRecommendation.SAFE_TO_ZERO,
                f"Upper-bits variable not used in return value calculation"
            )
        
        # 条件3b: PIECE演算の上位部分としてのみ使用されている場合
        # かつ戻り値のビット幅が32ビット以下なら安全
        if usage.in_piece_upper and return_bit_width <= 32:
            return (
                ConstraintRecommendation.SAFE_TO_ZERO,
                f"Used only as upper bits in PIECE, return type is {return_bit_width}bit"
            )
        
        # 条件式でのみ使用されている場合
        if usage.in_condition and not usage.in_return_value:
            if usage.in_piece_upper:
                return (
                    ConstraintRecommendation.SAFE_TO_ZERO,
                    f"Used in condition as PIECE upper bits, represents 32-bit comparison"
                )
            else:
                return (
                    ConstraintRecommendation.NEEDS_MANUAL_REVIEW,
                    f"Used in condition but not as PIECE upper bits"
                )
        
        # その他のケースは安全でない
        return (
            ConstraintRecommendation.UNSAFE,
            f"Variable may affect return value"
        )
    
    def analyze_all_extra_variables(
        self,
        analysis: FunctionReturnAnalysis,
        param_names: Set[str],
        return_bit_width: int
    ) -> Dict[str, ExtraVariableAnalysis]:
        """
        全ての追加変数を分析
        
        Args:
            analysis: 関数解析結果
            param_names: パラメータ名のセット
            return_bit_width: 戻り値のビット幅
        
        Returns:
            変数名 -> 分析結果 のマッピング
        """
        # 全変数を収集
        all_vars: Set[str] = set()
        var_sizes: Dict[str, int] = {}
        
        for ret in analysis.returns:
            if hasattr(ret.value, 'get_all_variables'):
                vars_in_expr = ret.value.get_all_variables()
                all_vars.update(vars_in_expr)
                self._collect_variable_sizes(ret.value, var_sizes)
            
            for cond in ret.conditions:
                if hasattr(cond, 'get_all_variables'):
                    vars_in_cond = cond.get_all_variables()
                    all_vars.update(vars_in_cond)
                    if hasattr(cond, 'expression'):
                        self._collect_variable_sizes(cond.expression, var_sizes)
        
        # パラメータ以外の変数を抽出
        extra_var_names = all_vars - param_names
        
        # 各変数を分析
        results = {}
        for var_name in sorted(extra_var_names):
            bit_width = var_sizes.get(var_name, 32)
            results[var_name] = self.analyze_extra_variable(
                var_name, bit_width, analysis, return_bit_width
            )
        
        return results
    
    def _collect_variable_sizes(
        self,
        expr: Expression,
        var_sizes: Dict[str, int]
    ) -> None:
        """式から変数のサイズを収集"""
        if expr.expr_type in (ExpressionType.VARIABLE, ExpressionType.PARAMETER):
            if expr.name and expr.name not in var_sizes:
                if expr.size and expr.size > 0:
                    var_sizes[expr.name] = expr.size * 8
                else:
                    var_sizes[expr.name] = expr.get_bit_width()
        
        for operand in expr.operands:
            self._collect_variable_sizes(operand, var_sizes)
        
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, val in expr.value:
                if hasattr(val, 'expr_type'):
                    self._collect_variable_sizes(val, var_sizes)


def get_safe_zero_constraints(
    analyses: Dict[str, ExtraVariableAnalysis]
) -> List[str]:
    """
    安全に0制約できる変数名のリストを取得
    
    Args:
        analyses: 変数名 -> 分析結果 のマッピング
    
    Returns:
        安全に0制約できる変数名のリスト
    """
    return [
        name for name, analysis in analyses.items()
        if analysis.can_safely_constrain_to_zero()
    ]