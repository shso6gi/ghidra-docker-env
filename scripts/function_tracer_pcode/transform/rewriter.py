# -*- coding: utf-8 -*-
"""式のリライト機能モジュール

SMTソルバーがタイムアウトする複雑な式を、等価な単純な形式に変換する。

主なリライトルール:
1. 剰余展開: (a - ((a / b) * b)) → (a % b)

リライト条件の妥当性:
- 整数除算の定義より: a = (a / b) * b + (a % b)
- したがって: a % b = a - (a / b) * b
- 符号付き/符号なしの区別を保持
"""

from typing import Optional, List, Tuple, TYPE_CHECKING
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from .magic_division import MagicDivisionCalculator, is_power_of_two, log2_exact, MagicConstants

if TYPE_CHECKING:
    from ..model import Expression, ReturnInfo, FunctionReturnAnalysis


@dataclass
class RewriteResult:
    """リライト結果"""
    expression: 'Expression'
    was_rewritten: bool
    history: List[Tuple[str, str, str]] = field(default_factory=list)
    
    def get_summary(self) -> str:
        """リライトの概要を取得"""
        if not self.was_rewritten:
            return "No rewrite applied"
        
        lines = [f"Applied {len(self.history)} rewrite(s):"]
        for rule_name, before, after in self.history:
            lines.append(f"  [{rule_name}] {before} -> {after}")
        return "\n".join(lines)


class RewriteRule(ABC):
    """リライトルールの抽象基底クラス"""
    
    def __init__(self, name: str, description: str):
        self.name = name
        self.description = description
    
    @abstractmethod
    def matches(self, expr: 'Expression') -> bool:
        """式がこのルールにマッチするかチェック"""
        pass
    
    @abstractmethod
    def apply(self, expr: 'Expression') -> 'Expression':
        """ルールを適用して新しい式を返す"""
        pass


class ModuloExpansionRule(RewriteRule):
    """
    剰余の展開形式を剰余演算子に変換するルール
    
    パターン: (a - ((a / b) * b))
    変換先: (a % b)
    
    数学的根拠:
        整数除算の定義より、a = (a / b) * b + (a % b)
        したがって、a % b = a - (a / b) * b
    
    注意点:
        - 符号付き除算(SDIV/INT_SDIV)の場合は符号付き剰余(SREM/INT_SREM)に変換
        - 符号なし除算(DIV/INT_DIV)の場合は符号なし剰余(REM/INT_REM)に変換
        - オーバーフローの挙動は除算と剰余で一致するため変換は安全
    """
    
    def __init__(self):
        super().__init__(
            "modulo_expansion",
            "Convert (a - ((a / b) * b)) to (a % b)"
        )
        
        # 演算子のグループ
        self.signed_div_ops = frozenset({"INT_SDIV", "SDIV", "//"})
        self.unsigned_div_ops = frozenset({"INT_DIV", "DIV", "/"})
        self.all_div_ops = self.signed_div_ops | self.unsigned_div_ops
        self.mult_ops = frozenset({"INT_MULT", "MULT", "*"})
        self.sub_ops = frozenset({"INT_SUB", "SUB", "-"})
    
    def matches(self, expr: 'Expression') -> bool:
        """
        パターンにマッチするかチェック
        
        期待される構造:
            SUB(a, MULT(DIV(a', b), b'))
            where a == a' and b == b'
        
        または:
            SUB(a, MULT(b', DIV(a', b)))
            where a == a' and b == b' (乗算の順序が逆)
        """
        from ..model import ExpressionType
        
        # トップレベルがSUBかチェック
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False

        if expr.operator is None or expr.operator not in self.sub_ops:
            return False
        
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        a = expr.operands[0]
        mult_expr = expr.operands[1]
        
        # 第2オペランドがMULTかチェック
        if mult_expr.expr_type != ExpressionType.BINARY_OP:
            return False

        if mult_expr.operator is None or mult_expr.operator not in self.mult_ops:
            return False
        
        if not mult_expr.operands or len(mult_expr.operands) != 2:
            return False
        
        # MULT内から除算式とbを抽出
        # パターン1: MULT(DIV(a, b), b) 
        # パターン2: MULT(b, DIV(a, b))
        div_expr, b_in_mult = self._extract_div_and_operand(mult_expr)
        
        if div_expr is None or b_in_mult is None:
            return False
        
        if not div_expr.operands or len(div_expr.operands) != 2:
            return False
        
        a_in_div = div_expr.operands[0]
        b_in_div = div_expr.operands[1]
        
        # a == a_in_div かつ b_in_mult == b_in_div かチェック
        if not self._expressions_structurally_equal(a, a_in_div):
            return False
        
        if not self._expressions_structurally_equal(b_in_mult, b_in_div):
            return False
        
        return True
    
    def _extract_div_and_operand(self, mult_expr: 'Expression') -> Tuple[Optional['Expression'], Optional['Expression']]:
        from ..model import ExpressionType

        for i, op in enumerate(mult_expr.operands):
            if (
                op.expr_type == ExpressionType.BINARY_OP
                and op.operator is not None
                and op.operator in self.all_div_ops
            ):
                return op, mult_expr.operands[1 - i]

        return None, None
    
    def _expressions_structurally_equal(self, expr1: 'Expression', expr2: 'Expression') -> bool:
        """
        2つの式が構造的に等しいかチェック
        
        SMT表現で比較することで、変数名や演算子の表記ゆれを吸収
        """
        try:
            return expr1.to_smt() == expr2.to_smt()
        except:
            # フォールバック: 文字列表現で比較
            return expr1.to_string() == expr2.to_string()
    
    def apply(self, expr: 'Expression') -> 'Expression':
        """
        (a - ((a / b) * b)) を (a % b) に変換
        """
        from ..model import Expression
        
        a = expr.operands[0]
        mult_expr = expr.operands[1]
        
        # div_exprとbを抽出
        div_expr, b = self._extract_div_and_operand(mult_expr)
        
        # 符号付き除算かどうかで剰余演算子を決定
        if div_expr is None or b is None or div_expr.operator is None:
            return expr

        if div_expr.operator in self.signed_div_ops:
            mod_operator = "INT_SREM"
        else:
            mod_operator = "INT_REM"
        
        # 新しい剰余式を作成
        result = Expression.binary_op(mod_operator, a, b)
        result.size = expr.size if hasattr(expr, 'size') else 4
        return result


class ModuloToExpansionRule(RewriteRule):
    """
    剰余演算子を展開形式に変換するルール（逆方向）
    
    パターン: (a % b) または INT_SREM(a, b) / INT_REM(a, b)
    変換先: (a - ((a / b) * b))
    
    用途: G3形式をG1形式に変換する場合に使用
    
    注意: 通常はModuloExpansionRule（逆方向）を使用するため、
          このルールはデフォルトでは無効
    """
    
    def __init__(self):
        super().__init__(
            "modulo_to_expansion",
            "Convert (a % b) to (a - ((a / b) * b))"
        )
        
        self.signed_mod_ops = frozenset({"INT_SREM", "SREM"})
        self.unsigned_mod_ops = frozenset({"INT_REM", "REM", "%"})
        self.all_mod_ops = self.signed_mod_ops | self.unsigned_mod_ops
    
    def matches(self, expr: 'Expression') -> bool:
        """剰余演算かチェック"""
        from ..model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        
        if expr.operator not in self.all_mod_ops:
            return False
        
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        return True
    
    def apply(self, expr: 'Expression') -> 'Expression':
        """
        (a % b) を (a - ((a / b) * b)) に変換
        """
        from ..model import Expression
        
        a = expr.operands[0]
        b = expr.operands[1]
        
        # 符号付きかどうかで除算演算子を決定
        if expr.operator in self.signed_mod_ops:
            div_operator = "INT_SDIV"
        else:
            div_operator = "INT_DIV"
        
        # (a / b)
        div_expr = Expression.binary_op(div_operator, a, b)
        div_expr.size = expr.size if hasattr(expr, 'size') else 4
        
        # (a / b) * b
        mult_expr = Expression.binary_op("INT_MULT", div_expr, b)
        mult_expr.size = expr.size if hasattr(expr, 'size') else 4
        
        # a - ((a / b) * b)
        result = Expression.binary_op("INT_SUB", a, mult_expr)
        result.size = expr.size if hasattr(expr, 'size') else 4
        
        return result


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
        
        # 方向に応じたルールを設定
        self._setup_rules(direction)
    
    def _setup_rules(self, direction: str):
        """リライト方向に応じたルールを設定"""
        self.rules.clear()
        
        if direction == self.NORMALIZE_TO_MODULO:
            # 優先順位: 簡約 → /3最適化 → power-of-two → 剰余展開
            self.rules.append(DivSimplificationRule())
            # Magic number変換（/3専用）を最優先
            self.rules.append(SignedDivBy3Rule())
            self.rules.append(UnsignedDivBy3Rule())
            # Power-of-two変換
            self.rules.append(DivByPowerOfTwoUnsignedRule())
            self.rules.append(DivByPowerOfTwoSignedRule())
            self.rules.append(RemByPowerOfTwoUnsignedRule())
            self.rules.append(RemByPowerOfTwoSignedRule())
            # 剰余展開
            self.rules.append(ModuloExpansionRule())
        elif direction == self.NORMALIZE_TO_EXPANSION:
            self.rules.append(ModuloToExpansionRule())
        else:
            # デフォルト
            self.rules.append(DivSimplificationRule())
            self.rules.append(SignedDivBy3Rule())
            self.rules.append(UnsignedDivBy3Rule())
            self.rules.append(DivByPowerOfTwoUnsignedRule())
            self.rules.append(DivByPowerOfTwoSignedRule())
            self.rules.append(ModuloExpansionRule())
    
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
        
        self._debug_print(f"Starting rewrite of: {expr.to_string()}")
        
        rewritten = self._rewrite_recursive(expr, depth=0)
        
        was_rewritten = len(self._rewrite_history) > 0
        
        if was_rewritten:
            self._debug_print(f"Rewrite complete: {rewritten.to_string()}")
        else:
            self._debug_print("No rewrite applied")
        
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
                before_str = new_expr.to_string()
                rewritten = rule.apply(new_expr)
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
        from ..model import Expression, ExpressionType
        
        if expr.expr_type == ExpressionType.BINARY_OP:
            if expr.operands and len(expr.operands) >= 2:
                new_left = self._rewrite_recursive(expr.operands[0], depth + 1)
                new_right = self._rewrite_recursive(expr.operands[1], depth + 1)
                
                # 変更があった場合のみ新しい式を作成
                if new_left is not expr.operands[0] or new_right is not expr.operands[1]:
                    # operatorがNoneでないことをチェック
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
        
        elif expr.expr_type == ExpressionType.PHI:
            if expr.operands:
                new_operands = [self._rewrite_recursive(op, depth + 1) for op in expr.operands]
                
                if any(new_op is not old_op for new_op, old_op in zip(new_operands, expr.operands)):
                    # PHI式を再構築
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
    from ..model import ReturnInfo, FunctionReturnAnalysis
    
    rewrite_results = []
    new_returns = []
    
    for ret_info in analysis.returns:
        result = rewriter.rewrite(ret_info.value)
        rewrite_results.append(result)
        
        # 新しいReturnInfoを作成
        new_ret = ReturnInfo(
            address=ret_info.address,
            value=result.expression,
            conditions=ret_info.conditions,
            branch_index=ret_info.branch_index
        )
        new_returns.append(new_ret)
    
    # 新しいFunctionReturnAnalysisを作成
    new_analysis = FunctionReturnAnalysis(
        function_name=analysis.function_name,
        entry_point=analysis.entry_point,
        parameters=analysis.parameters,
        returns=new_returns,
        return_type=analysis.return_type
    )
    
    return new_analysis, rewrite_results

class DivByConstantRuleBase(RewriteRule):
    """定数除算リライトの基底クラス"""
    
    def __init__(self, name: str, description: str, signed: bool):
        super().__init__(name, description)
        self.signed = signed
        self.div_ops = frozenset(["INT_SDIV", "SDIV"]) if signed else frozenset(["INT_DIV", "DIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        from ..model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.div_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        # 右オペランドが定数かチェック
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        divisor = right.value
        
        # 0除算は対象外
        if divisor == 0:
            return False
        
        # 1, -1は簡約ルールで処理
        if divisor == 1 or divisor == -1:
            return False
        
        return True
    
    def _get_divisor_and_bits(self, expr: 'Expression') -> Tuple[int, int]:
        """除数とビット幅を取得"""
        divisor = expr.operands[1].value
        n_bits = expr.operands[0].get_bit_width()
        return divisor, n_bits


class DivByPowerOfTwoUnsignedRule(DivByConstantRuleBase):
    """
    unsigned除算 x / 2^k → x >> k
    
    厳密性: logical shiftは常に正しい
    """
    
    def __init__(self):
        super().__init__(
            "div_pow2_unsigned",
            "Convert x / 2^k to x >> k (unsigned)",
            signed=False
        )
        self.signed = False
        self.div_ops = frozenset(["INT_DIV", "DIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        if not super().matches(expr):
            return False
        
        divisor = expr.operands[1].value
        return is_power_of_two(divisor)
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ..model import Expression
        
        x = expr.operands[0]
        divisor = expr.operands[1].value
        k = log2_exact(divisor)
        
        # x >> k (logical shift)
        shift_amount = Expression.constant(k, size=x.size)
        result = Expression.binary_op("INT_RIGHT", x, shift_amount)
        result.size = x.size
        
        return result


class DivByPowerOfTwoSignedRule(DivByConstantRuleBase):
    """
    signed除算 x sdiv 2^k → (x + bias) >> k
    
    bias = (x >> (n-1)) & (2^k - 1)
    
    これはround-to-zeroを実現する標準的な変換
    
    厳密性: x >= 0 なら bias=0、x < 0 なら bias=(2^k - 1)
           これにより0方向への丸めが保証される
    """
    
    def __init__(self):
        super().__init__(
            "div_pow2_signed",
            "Convert x sdiv 2^k to (x + bias) >> k (signed)",
            signed=False
        )
        self.signed = True
        self.div_ops = frozenset(["INT_SDIV", "SDIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        if not super().matches(expr):
            return False
        
        divisor = expr.operands[1].value
        # 負の2の累乗も処理
        return is_power_of_two(abs(divisor))
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ..model import Expression
        
        x = expr.operands[0]
        divisor = expr.operands[1].value
        n_bits = x.get_bit_width()
        
        # 負の除数の場合
        if divisor < 0:
            # x sdiv (-2^k) = -(x sdiv 2^k)
            k = log2_exact(abs(divisor))
            
            # bias = (x >> (n-1)) & (2^k - 1)
            sign_shift = Expression.constant(n_bits - 1, size=x.size)
            sign_bit_ext = Expression.binary_op("INT_SRIGHT", x, sign_shift)
            sign_bit_ext.size = x.size
            
            mask = Expression.constant((1 << k) - 1, size=x.size)
            bias = Expression.binary_op("INT_AND", sign_bit_ext, mask)
            bias.size = x.size
            
            # x + bias
            x_plus_bias = Expression.binary_op("INT_ADD", x, bias)
            x_plus_bias.size = x.size
            
            # >> k (arithmetic shift)
            shift_amount = Expression.constant(k, size=x.size)
            shifted = Expression.binary_op("INT_SRIGHT", x_plus_bias, shift_amount)
            shifted.size = x.size
            
            # 2の補数（negate）
            result = Expression.unary_op("INT_2COMP", shifted)
            result.size = x.size
            
            return result
        
        else:
            k = log2_exact(divisor)
            
            # bias = (x >> (n-1)) & (2^k - 1)
            sign_shift = Expression.constant(n_bits - 1, size=x.size)
            sign_bit_ext = Expression.binary_op("INT_SRIGHT", x, sign_shift)
            sign_bit_ext.size = x.size
            
            mask = Expression.constant((1 << k) - 1, size=x.size)
            bias = Expression.binary_op("INT_AND", sign_bit_ext, mask)
            bias.size = x.size
            
            # x + bias
            x_plus_bias = Expression.binary_op("INT_ADD", x, bias)
            x_plus_bias.size = x.size
            
            # >> k (arithmetic shift)
            shift_amount = Expression.constant(k, size=x.size)
            result = Expression.binary_op("INT_SRIGHT", x_plus_bias, shift_amount)
            result.size = x.size
            
            return result


class DivSimplificationRule(RewriteRule):
    """
    除算の簡約
    - x / 1 → x
    - x / -1 → -x
    """
    
    def __init__(self):
        super().__init__(
            "div_simplification",
            "Simplify x/1 and x/(-1)"
        )
        self.all_div_ops = frozenset(["INT_DIV", "DIV", "INT_SDIV", "SDIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        from ..model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.all_div_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        return right.value == 1 or right.value == -1
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ..model import Expression
        
        x = expr.operands[0]
        divisor = expr.operands[1].value
        
        if divisor == 1:
            return x
        else:  # divisor == -1
            result = Expression.unary_op("INT_2COMP", x)
            result.size = x.size
            return result


class RemByPowerOfTwoUnsignedRule(RewriteRule):
    """
    unsigned余り x % 2^k → x & (2^k - 1)
    """
    
    def __init__(self):
        super().__init__(
            "rem_pow2_unsigned",
            "Convert x % 2^k to x & (2^k - 1) (unsigned)"
        )
        self.rem_ops = frozenset(["INT_REM", "REM"])
    
    def matches(self, expr: 'Expression') -> bool:
        from ..model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.rem_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        divisor = right.value
        if divisor <= 0:
            return False
        
        return is_power_of_two(divisor)
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ..model import Expression
        
        x = expr.operands[0]
        divisor = expr.operands[1].value
        
        mask = Expression.constant(divisor - 1, size=x.size)
        result = Expression.binary_op("INT_AND", x, mask)
        result.size = x.size
        
        return result


class RemByPowerOfTwoSignedRule(RewriteRule):
    """
    signed余り x srem 2^k の変換
    
    srem は x - (x sdiv d) * d で定義される
    x sdiv 2^k は既に他のルールで変換されるので、
    ここでは展開形に戻してから除算を置換
    """
    
    def __init__(self):
        super().__init__(
            "rem_pow2_signed",
            "Convert x srem 2^k using expansion (signed)"
        )
        self.rem_ops = frozenset(["INT_SREM", "SREM"])
    
    def matches(self, expr: 'Expression') -> bool:
        from ..model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.rem_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        divisor = right.value
        if divisor == 0:
            return False
        
        return is_power_of_two(abs(divisor))
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ..model import Expression
        
        x = expr.operands[0]
        d = expr.operands[1]
        
        # x - (x sdiv d) * d
        div_expr = Expression.binary_op("INT_SDIV", x, d)
        div_expr.size = x.size
        
        mult_expr = Expression.binary_op("INT_MULT", div_expr, d)
        mult_expr.size = x.size
        
        result = Expression.binary_op("INT_SUB", x, mult_expr)
        result.size = x.size
        
        # この結果は次のリライトパスでdiv_exprが変換される
        return result
    
class SignedDivBy3Rule(RewriteRule):
    """
    signed除算 x sdiv 3 のmagic number変換
    
    アルゴリズム（clangと同一）:
        sum = (a + b + c)
        mulhi = upper64(sign_extend(sum, 128) * sign_extend(m, 128))
        result = mulhi - (mulhi >> 63)
    
    where:
        m = 0x5555555555555556 (magic multiplier for /3)
    
    BV意味論の厳密性:
        - mulhi抽出は SUBPIECE で厳密に実装
        - 符号補正 (mulhi >> 63) は負数の丸め補正
        - clangが生成するコードと完全一致
    """
    
    def __init__(self):
        super().__init__(
            "sdiv_by_3_magic",
            "Convert x sdiv 3 to magic multiplication (clang-compatible)"
        )
        self.div_ops = frozenset(["INT_SDIV", "SDIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        from ..model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.div_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        # 右オペランドが定数3かチェック
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        return right.value == 3
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ..model import Expression
        
        x = expr.operands[0]
        n_bits = x.get_bit_width()
        n_bytes = x.size
        
        # 64-bitと32-bitのみサポート
        if n_bits == 64:
            magic_info = MagicConstants.SIGNED_64_DIV_3
        elif n_bits == 32:
            magic_info = MagicConstants.SIGNED_32_DIV_3
        else:
            # 他のビット幅は未サポート（そのまま返す）
            return expr
        
        # magic multiplierを定数として作成（unsigned表現）
        m_unsigned = magic_info['multiplier_unsigned']
        m_const = Expression.constant(m_unsigned, size=n_bytes)
        
        # === mulhi の計算 ===
        # 1. x を 2n-bit に sign-extend
        x_ext = Expression.unary_op("INT_SEXT", x)
        x_ext.size = n_bytes * 2  # 重要！128bit = 16 bytes
        
        # 2. m を 2n-bit に sign-extend
        m_ext = Expression.unary_op("INT_SEXT", m_const)
        m_ext.size = n_bytes * 2
        
        # 3. 乗算（128-bit結果）
        prod = Expression.binary_op("INT_MULT", x_ext, m_ext)
        prod.size = n_bytes * 2
        
        # 4. 上位n-bit抽出（SUBPIECE(prod, n_bytes)）
        # SUBPIECE(prod, 8) = bits [127:64]
        offset = Expression.constant(n_bytes, size=n_bytes)
        mulhi = Expression.binary_op("SUBPIECE", prod, offset)
        mulhi.size = n_bytes  # 重要！64bit = 8 bytes
        
        # === 符号補正 ===
        # 5. mulhi >> (n-1) : 符号ビットを全体に伝播
        # これは負数の場合の丸め補正
        sign_shift = Expression.constant(n_bits - 1, size=n_bytes)
        sign_correction = Expression.binary_op("INT_SRIGHT", mulhi, sign_shift)
        sign_correction.size = n_bytes
        
        # 6. mulhi - sign_correction
        result = Expression.binary_op("INT_SUB", mulhi, sign_correction)
        result.size = n_bytes
        
        return result


class UnsignedDivBy3Rule(RewriteRule):
    """
    unsigned除算 x udiv 3 のmagic number変換
    
    アルゴリズム:
        mulhi = upper64(zero_extend(x, 128) * zero_extend(m, 128))
        result = mulhi >> 1
    
    where:
        m = 0xAAAAAAAAAAAAAAAB, shift = 1
    """
    
    def __init__(self):
        super().__init__(
            "udiv_by_3_magic",
            "Convert x udiv 3 to magic multiplication"
        )
        self.div_ops = frozenset(["INT_DIV", "DIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        from ..model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.div_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        return right.value == 3
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ..model import Expression
        
        x = expr.operands[0]
        n_bits = x.get_bit_width()
        n_bytes = x.size
        
        # 64-bit unsigned /3: m = 0xAAAAAAAAAAAAAAAB, shift = 1
        # 32-bit unsigned /3: m = 0xAAAAAAAB, shift = 1
        if n_bits == 64:
            m_value = 0xAAAAAAAAAAAAAAAB
            shift = 1
        elif n_bits == 32:
            m_value = 0xAAAAAAAB
            shift = 1
        else:
            return expr
        
        m_const = Expression.constant(m_value, size=n_bytes)
        
        # 1. x を 2n-bit に zero-extend
        x_ext = Expression.unary_op("INT_ZEXT", x)
        x_ext.size = n_bytes * 2
        
        # 2. m を 2n-bit に zero-extend
        m_ext = Expression.unary_op("INT_ZEXT", m_const)
        m_ext.size = n_bytes * 2
        
        # 3. 乗算
        prod = Expression.binary_op("INT_MULT", x_ext, m_ext)
        prod.size = n_bytes * 2
        
        # 4. 上位n-bit抽出
        offset = Expression.constant(n_bytes, size=n_bytes)
        mulhi = Expression.binary_op("SUBPIECE", prod, offset)
        mulhi.size = n_bytes
        
        # 5. 右シフト
        if shift > 0:
            shift_amount = Expression.constant(shift, size=n_bytes)
            result = Expression.binary_op("INT_RIGHT", mulhi, shift_amount)
            result.size = n_bytes
        else:
            result = mulhi
        
        return result