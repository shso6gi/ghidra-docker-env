# -*- coding: utf-8 -*-
"""式のリライト機能モジュール

SMTソルバーがタイムアウトする複雑な式を、等価な単純な形式に変換する。

主なリライトルール:
1. 剰余展開: (a - ((a / b) * b)) → (a % b)
2. Magic number変換: x / 3 → magic multiplication
3. Power-of-two最適化: x / 2^k → x >> k
4. 正規化: 可換演算のソート、型統一

リライト条件の妥当性:
- 整数除算の定義より: a = (a / b) * b + (a % b)
- したがって: a % b = a - (a / b) * b
- 符号付き/符号なしの区別を保持
"""

from typing import List, Tuple, TYPE_CHECKING

from .rules import (
    RewriteResult,
    RewriteRule,
    ModuloExpansionRule,
    ModuloToExpansionRule,
    DivSimplificationRule,
    SignedDivBy3Rule,
    UnsignedDivBy3Rule,
    DivByPowerOfTwoUnsignedRule,
    DivByPowerOfTwoSignedRule,
    RemByPowerOfTwoUnsignedRule,
    RemByPowerOfTwoSignedRule,
    CommutativeNormalizationRule,
    ShiftConstantNormalizationRule,
)

if TYPE_CHECKING:
    from ...model import Expression, ReturnInfo, FunctionReturnAnalysis


class ExpressionRewriter:
    """
    式のリライトを管理するクラス
    
    使用例:
        rewriter = ExpressionRewriter(debug=True)
        result = rewriter.rewrite(original_expr)
        
        if result.was_rewritten:
            print(result.get_summary())
            new_expr = result.expression
    
    デフォルトのリライト戦略:
        - 剰余の展開形式を剰余演算子に正規化
        - これによりSMTソルバーの負荷を軽減
    """
    
    # リライト方向の定数
    NORMALIZE_TO_MODULO = "to_modulo"      # (a - ((a/b)*b)) -> (a % b)
    NORMALIZE_TO_EXPANSION = "to_expansion" # (a % b) -> (a - ((a/b)*b))
    
    def __init__(
        self, 
        debug: bool = False,
        direction: str = "to_modulo"
    ):
        """
        Args:
            debug: デバッグ出力を有効にする
            direction: リライト方向
                - "to_modulo": 展開形式を剰余演算子に変換（デフォルト）
                - "to_expansion": 剰余演算子を展開形式に変換
        """
        self.debug = debug
        self.direction = direction
        self.rules: List[RewriteRule] = []
        self._rewrite_history: List[Tuple[str, str, str]] = []
        self._noop_count: int = 0  # no-op カウンタ（デバッグ用）
        
        # 方向に応じたルールを設定
        self._setup_rules(direction)
    
    def _setup_rules(self, direction: str):
        """リライト方向に応じたルールを設定"""
        self.rules.clear()
        
        if direction == self.NORMALIZE_TO_MODULO:
            # 優先順位:
            # 1. シフト定数正規化（最優先：後続ルールに影響）
            # 2. 簡約
            # 3. /3最適化（magic number変換）
            # 4. power-of-two最適化
            # 5. 剰余展開
            # 6. 可換演算正規化（最後：全体を整える）
            self.rules.append(ShiftConstantNormalizationRule())
            self.rules.append(DivSimplificationRule())
            self.rules.append(SignedDivBy3Rule())
            self.rules.append(UnsignedDivBy3Rule())
            self.rules.append(DivByPowerOfTwoUnsignedRule())
            self.rules.append(DivByPowerOfTwoSignedRule())
            self.rules.append(RemByPowerOfTwoUnsignedRule())
            self.rules.append(RemByPowerOfTwoSignedRule())
            self.rules.append(ModuloExpansionRule())
            self.rules.append(CommutativeNormalizationRule())
        elif direction == self.NORMALIZE_TO_EXPANSION:
            self.rules.append(ShiftConstantNormalizationRule())
            self.rules.append(ModuloToExpansionRule())
            self.rules.append(CommutativeNormalizationRule())
        else:
            # デフォルト
            self.rules.append(ShiftConstantNormalizationRule())
            self.rules.append(DivSimplificationRule())
            self.rules.append(SignedDivBy3Rule())
            self.rules.append(UnsignedDivBy3Rule())
            self.rules.append(DivByPowerOfTwoUnsignedRule())
            self.rules.append(DivByPowerOfTwoSignedRule())
            self.rules.append(ModuloExpansionRule())
            self.rules.append(CommutativeNormalizationRule())
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[ExpressionRewriter] {msg}")
    
    def add_rule(self, rule: RewriteRule):
        """カスタムリライトルールを追加"""
        self.rules.append(rule)
    
    def rewrite(self, expr: 'Expression') -> RewriteResult:
        """
        式をリライトする（再帰的に子要素にも適用）
        
        Args:
            expr: リライト対象の式
        
        Returns:
            RewriteResult: リライト結果
        """
        self._rewrite_history.clear()
        self._noop_count = 0  # カウンタをリセット
        
        self._debug_print(f"Starting rewrite of: {expr.to_string()}")
        
        rewritten = self._rewrite_recursive(expr, depth=0)
        
        was_rewritten = len(self._rewrite_history) > 0
        
        if was_rewritten:
            self._debug_print(f"Rewrite complete: {rewritten.to_string()}")
        else:
            self._debug_print("No rewrite applied")
        
        # デバッグモードで no-op 統計を報告
        if self.debug and self._noop_count > 0:
            self._debug_print(f"Total no-op rules skipped: {self._noop_count}")
        
        return RewriteResult(
            expression=rewritten,
            was_rewritten=was_rewritten,
            history=self._rewrite_history.copy()
        )
    
    def _rewrite_recursive(self, expr: 'Expression', depth: int = 0) -> 'Expression':
        """再帰的にリライトを適用"""
        if depth > 50:  # 深すぎる再帰を防止
            self._debug_print(f"Max depth reached at depth {depth}")
            return expr
        
        # まず子要素をリライト
        new_expr = self._rewrite_children(expr, depth)
        
        # 次にルールを適用
        for rule in self.rules:
            if rule.matches(new_expr):
                rewritten = rule.apply(new_expr)
                
                # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                # no-op チェック：同一オブジェクト参照なら変更なし
                # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                # 背景：
                #   - ほとんどのルールは「変更不要なら元のexprを返す」設計
                #   - to_string()比較は危険（内部属性sizeなどが反映されない）
                #   - オブジェクト参照による判定が最も安全で高速
                # 
                # 例：
                #   CommutativeNormalizationRule.apply():
                #     if sorted_operands == operands:
                #         return expr  # ← 同一オブジェクトを返す
                # 
                # 注意：
                #   ShiftConstantNormalizationRuleなど、内部属性だけを変えるルールは
                #   新しいExpressionオブジェクトを作るため、is チェックで False になり
                #   正しく適用される
                if rewritten is new_expr:
                    self._noop_count += 1
                    # no-op の場合は文字列化もログ出力もスキップ（高速化）
                    continue
                
                # 実際に変更があった場合のみ文字列化してログ出力＆履歴追加
                before_str = new_expr.to_string()
                after_str = rewritten.to_string()
                
                self._debug_print(f"Rule '{rule.name}' matched at depth {depth}")
                self._debug_print(f"  Before: {before_str}")
                self._debug_print(f"  After:  {after_str}")
                
                self._rewrite_history.append((rule.name, before_str, after_str))
                
                # リライト後の式にも再帰的にルールを適用（連鎖的な変換対応）
                return self._rewrite_recursive(rewritten, depth + 1)
        
        return new_expr
    
    def _rewrite_children(self, expr: 'Expression', depth: int) -> 'Expression':
        """子要素をリライトして新しい式を返す"""
        from ...model import Expression, ExpressionType
        
        if expr.expr_type == ExpressionType.BINARY_OP:
            if expr.operands and len(expr.operands) >= 2:
                new_left = self._rewrite_recursive(expr.operands[0], depth + 1)
                new_right = self._rewrite_recursive(expr.operands[1], depth + 1)
                
                # 変更があった場合のみ新しい式を作成
                if new_left is not expr.operands[0] or new_right is not expr.operands[1]:
                    if not hasattr(expr, 'operator') or expr.operator is None:
                        return expr
                    result = Expression.binary_op(expr.operator, new_left, new_right)
                    result.size = getattr(expr, 'size', 4)
                    return result
        
        elif expr.expr_type == ExpressionType.UNARY_OP:
            if expr.operands and len(expr.operands) >= 1:
                new_operand = self._rewrite_recursive(expr.operands[0], depth + 1)
                
                if new_operand is not expr.operands[0]:
                    if not hasattr(expr, 'operator') or expr.operator is None:
                        return expr
                    result = Expression.unary_op(expr.operator, new_operand)
                    result.size = getattr(expr, 'size', 4)
                    return result
        
        elif expr.expr_type == ExpressionType.CALL:
            if expr.operands:
                new_args = [self._rewrite_recursive(arg, depth + 1) for arg in expr.operands]
                
                if any(new_arg is not old_arg for new_arg, old_arg in zip(new_args, expr.operands)):
                    if not hasattr(expr, 'name') or expr.name is None:
                        return expr
                    result = Expression.call(expr.name, new_args)
                    result.size = getattr(expr, 'size', 4)
                    return result

        elif expr.expr_type == ExpressionType.INTRINSIC:
            if expr.operands:
                new_args = [self._rewrite_recursive(arg, depth + 1) for arg in expr.operands]

                if any(new_arg is not old_arg for new_arg, old_arg in zip(new_args, expr.operands)):
                    if not hasattr(expr, 'name') or expr.name is None:
                        return expr
                    result = Expression.intrinsic(
                        expr.name,
                        new_args,
                        size=getattr(expr, 'size', 4),
                        opcode=getattr(expr, 'opcode', None),
                    )
                    return result
        
        elif expr.expr_type == ExpressionType.PHI:
            if expr.operands:
                new_operands = [self._rewrite_recursive(op, depth + 1) for op in expr.operands]
                
                if any(new_op is not old_op for new_op, old_op in zip(new_operands, expr.operands)):
                    if hasattr(expr, 'phi_branches') and getattr(expr, 'phi_branches', None):
                        phi_branches = getattr(expr, 'phi_branches', [])
                        new_branches = list(
                            zip([b[0] for b in phi_branches],
                            new_operands
                        ))
                        result = Expression.phi(new_branches)
                    else:
                        result = Expression.phi([
                            (f"branch_{i}", op) for i, op in enumerate(new_operands)
                        ])
                    result.size = getattr(expr, 'size', 4)
                    return result
        
        elif expr.expr_type == ExpressionType.MEMORY:
            if expr.operands and len(expr.operands) >= 1:
                new_addr = self._rewrite_recursive(expr.operands[0], depth + 1)
                
                if new_addr is not expr.operands[0]:
                    result = Expression.memory(new_addr, getattr(expr, 'size', 4))
                    return result
        
        return expr
    
    def get_rewrite_history(self) -> List[Tuple[str, str, str]]:
        """
        リライトの履歴を取得
        
        Returns:
            [(rule_name, before_string, after_string), ...]
        """
        return self._rewrite_history.copy()
    
    def was_rewritten(self) -> bool:
        """リライトが適用されたかどうか"""
        return len(self._rewrite_history) > 0


def rewrite_analysis_returns(
    analysis: 'FunctionReturnAnalysis',
    rewriter: ExpressionRewriter
) -> Tuple['FunctionReturnAnalysis', List[RewriteResult]]:
    """
    FunctionReturnAnalysisの全return値をリライト
    
    Args:
        analysis: 解析結果
        rewriter: リライター
    
    Returns:
        (リライトされた解析結果, 各return値のリライト結果リスト)
    """
    from ...model import Condition, ReturnInfo, FunctionReturnAnalysis
    
    rewrite_results = []
    new_returns = []
    
    for ret_info in analysis.returns:
        value_result = rewriter.rewrite(ret_info.value)
        combined_history = list(value_result.history)
        new_conditions = []

        for cond_index, condition in enumerate(ret_info.conditions):
            condition_result = rewriter.rewrite(condition.expression)
            if condition_result.was_rewritten:
                combined_history.extend(
                    (
                        f"condition[{cond_index}]:{rule_name}",
                        before,
                        after,
                    )
                    for rule_name, before, after in condition_result.history
                )
            new_conditions.append(
                Condition(
                    expression=condition_result.expression,
                    negated=condition.negated,
                )
            )

        rewrite_results.append(
            RewriteResult(
                expression=value_result.expression,
                was_rewritten=bool(combined_history),
                history=combined_history,
            )
        )
        
        # 新しいReturnInfoを作成
        new_ret = ReturnInfo(
            address=ret_info.address,
            value=value_result.expression,
            conditions=new_conditions,
            branch_index=ret_info.branch_index,
            pcode_identity=ret_info.pcode_identity,
            pcode_order=ret_info.pcode_order,
            pcode_time=ret_info.pcode_time,
            pcode_op_ref=getattr(ret_info, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(
                getattr(ret_info, "return_value_pcode_op_refs", ()) or ()
            ),
            return_value_flow_certificate=getattr(
                ret_info, "return_value_flow_certificate", None
            ),
        )
        new_returns.append(new_ret)
    
    # 新しいFunctionReturnAnalysisを作成
    new_analysis = FunctionReturnAnalysis(
        function_name=analysis.function_name,
        entry_point=analysis.entry_point,
        parameters=analysis.parameters,
        returns=new_returns,
        function_ref=analysis.function_ref,
        return_type=analysis.return_type,
        return_type_obj=analysis.return_type_obj,
        signedness_result=analysis.signedness_result,
        unknown_event_count=analysis.unknown_event_count,
        unknown_event_reasons=list(analysis.unknown_event_reasons),
        analysis_notes=list(analysis.analysis_notes),
        recovered_from_decompiler=analysis.recovered_from_decompiler,
        incomplete_control_flow=analysis.incomplete_control_flow,
        deferred_calls=dict(analysis.deferred_calls),
        effect_summary=analysis.effect_summary,
        comparison_surface=analysis.comparison_surface,
        program_is_big_endian=analysis.program_is_big_endian,
    )
    
    return new_analysis, rewrite_results
