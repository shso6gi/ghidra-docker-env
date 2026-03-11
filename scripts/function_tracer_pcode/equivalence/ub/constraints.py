# -*- coding: utf-8 -*-
"""
C言語の未定義動作（UB）を除外するSMT制約を生成するモジュール

現在サポートされているUB:
1. 符号付き整数の -MIN_INT オーバーフロー (bvneg on INT_MIN)
2. シフト量がビット幅以上になるシフト演算

将来拡張予定:
- INT_MIN / -1 オーバーフロー
- signed left shift の表現不能オーバーフロー
- ポインタ演算のUB
"""

from typing import Callable, Set, List, Optional, TYPE_CHECKING, Tuple

from ...model import FunctionReturnAnalysis, Expression, ExpressionType, Condition

# 型チェック用のインポート（循環参照を避けるため）
if TYPE_CHECKING:
    from ..formula.builder import ParameterInfo


class UbConstraintBuilder:
    """未定義動作（UB）を除外するSMT制約を生成するクラス"""
    
    def __init__(self, debug: bool = False):
        self.debug = debug
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[UbConstraintBuilder] {msg}")
    
    def build_constraints(
        self,
        analysis: FunctionReturnAnalysis,
        param_infos: List['ParameterInfo'],
        constraint_types: Optional[Set[str]] = None,
        symbol_replace_fn: Optional[Callable[[str], str]] = None,
    ) -> List[str]:
        """
        UB除外制約を生成
        
        Args:
            analysis: 関数解析結果
            param_infos: パラメータ情報（SMT名・ビット幅付き）
            constraint_types: 生成する制約タイプのセット
                None の場合は全タイプを生成
                例: {"negate_min", "shift_count"}
            symbol_replace_fn: Expression.to_smt() で得た元名を
                SMT変数名へ置換する関数
        
        Returns:
            SMT-LIB形式の制約行のリスト
        """
        if constraint_types is None:
            constraint_types = {"negate_min", "shift_count"}
        
        all_constraints = []
        
        # 1. -MIN_INT 制約
        if "negate_min" in constraint_types:
            negate_min_constraints = self._build_negate_min_constraints(
                analysis, param_infos
            )
            if negate_min_constraints:
                all_constraints.extend(negate_min_constraints)

        if "shift_count" in constraint_types:
            shift_constraints = self._build_shift_count_constraints(
                analysis,
                symbol_replace_fn=symbol_replace_fn,
            )
            if shift_constraints:
                all_constraints.extend(shift_constraints)

        return all_constraints

    def _build_shift_count_constraints(
        self,
        analysis: FunctionReturnAnalysis,
        symbol_replace_fn: Optional[Callable[[str], str]] = None,
    ) -> List[str]:
        """
        シフト量がビット幅未満であることを要求する制約を生成

        Cでは左右シフトともに、shift count が負または
        左オペランドのビット幅以上だと未定義動作。
        BV上では負値も大きな unsigned 値として表現されるため、
        `bvult rhs width` を課すことで両方を除外できる。
        """
        shift_sites = self._collect_shift_sites(analysis)
        if not shift_sites:
            self._debug_print("No shift operations found for UB constraints")
            return []

        constraints: List[str] = []
        seen: Set[Tuple[str, int, int, str]] = set()

        for operator, shift_expr in shift_sites:
            if len(shift_expr.operands) < 2:
                continue

            left = shift_expr.operands[0]
            right = shift_expr.operands[1]
            left_bits = left.get_bit_width()
            right_bits = right.get_bit_width()

            if left_bits <= 0 or right_bits <= 0:
                continue

            if self._is_shift_count_statically_safe(right, left_bits):
                continue

            right_smt = right.to_smt()
            if symbol_replace_fn is not None:
                right_smt = symbol_replace_fn(right_smt)

            key = (right_smt, left_bits, right_bits, operator)
            if key in seen:
                continue
            seen.add(key)

            comment = (
                f"; Exclude UB: {operator} shift amount must be < {left_bits} bits"
            )
            constraint = (
                f"(assert (bvult {right_smt} (_ bv{left_bits} {right_bits})))"
            )
            constraints.append(comment)
            constraints.append(constraint)

            self._debug_print(
                f"Added shift-count UB constraint for {operator}: {right_smt} < {left_bits}"
            )

        return constraints
    
    def _build_negate_min_constraints(
        self,
        analysis: FunctionReturnAnalysis,
        param_infos: List['ParameterInfo']
    ) -> List[str]:
        """
        -MIN_INT オーバーフローを除外する制約を生成
        
        検出対象:
        - Expression内の INT_2COMP (bvneg) 演算子
        - そのオペランドがパラメータである場合
        
        生成制約:
        - (assert (not (= param_x (_ bvMIN_VAL WIDTH))))
        """
        # Step 1: bvneg(param) を検出
        negated_params = self._collect_negated_params(analysis)
        
        if not negated_params:
            self._debug_print("No negated parameters found")
            return []
        
        self._debug_print(f"Found {len(negated_params)} negated parameter(s): {negated_params}")
        
        # Step 2: 各パラメータに対して制約を生成
        constraints = []
        
        for param_name in negated_params:
            # パラメータ情報を検索
            param_info = self._find_param_info(param_name, param_infos)
            
            if param_info is None:
                self._debug_print(f"Warning: Parameter '{param_name}' not found in param_infos")
                continue
            
            # MIN値を計算（符号付き整数の最小値）
            # 例: 64bit -> 2^63 = 9223372036854775808
            min_val = 2 ** (param_info.bit_width - 1)
            
            # 制約を生成
            comment = (
                f"; Exclude UB: -{param_info.smt_name} when "
                f"{param_info.smt_name} = INT{param_info.bit_width}_MIN"
            )
            constraint = (
                f"(assert (not (= {param_info.smt_name} "
                f"(_ bv{min_val} {param_info.bit_width}))))"
            )
            
            constraints.append(comment)
            constraints.append(constraint)
            
            self._debug_print(
                f"Added constraint: {param_info.smt_name} != {min_val} "
                f"({param_info.bit_width}bit MIN)"
            )
        
        return constraints
    
    def _collect_negated_params(
        self,
        analysis: FunctionReturnAnalysis
    ) -> Set[str]:
        """
        Expression中の bvneg のオペランドであるパラメータを収集
        
        Args:
            analysis: 関数解析結果
        
        Returns:
            bvnegされているパラメータ名のセット（元の名前: "param_1" など）
        """
        negated = set()
        
        # 各returnのvalueとconditionを走査
        for ret in analysis.returns:
            # 戻り値の式を走査
            self._walk_expression(ret.value, negated)
            
            # 条件式も走査（条件内でbvnegが使われる可能性）
            for cond in ret.conditions:
                # Condition も Expression のサブクラスまたは同等の構造を持つ
                self._walk_condition(cond, negated)
        
        return negated

    def _collect_shift_sites(
        self,
        analysis: FunctionReturnAnalysis
    ) -> List[Tuple[str, Expression]]:
        """Expression中のシフト演算を収集"""
        shift_sites: List[Tuple[str, Expression]] = []

        for ret in analysis.returns:
            self._walk_expression_for_shift(ret.value, shift_sites)
            for cond in ret.conditions:
                self._walk_expression_for_shift(cond.expression, shift_sites)

        return shift_sites

    def _walk_expression_for_shift(
        self,
        expr: Optional[Expression],
        shift_sites: List[Tuple[str, Expression]]
    ) -> None:
        """Expressionツリーを再帰走査してシフト演算を収集"""
        if expr is None:
            return

        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator in {"INT_LEFT", "INT_RIGHT", "INT_SRIGHT"}
        ):
            shift_sites.append((expr.operator, expr))

        if hasattr(expr, "operands") and expr.operands:
            for operand in expr.operands:
                self._walk_expression_for_shift(operand, shift_sites)

    def _is_shift_count_statically_safe(
        self,
        expr: Expression,
        width_bits: int
    ) -> bool:
        """定数シフト量が自明に安全かチェック"""
        if expr.expr_type != ExpressionType.CONSTANT:
            return False

        return 0 <= expr.value < width_bits
    
    def _walk_condition(
        self,
        cond: Condition,
        negated: Set[str]
    ):
        """
        Conditionを走査してbvneg(param)を検出
        
        Args:
            cond: 走査するCondition
            negated: 検出されたパラメータ名を追加するセット
        """
        # Conditionの左辺と右辺を走査（getattr で安全にアクセス）
        left_expr = getattr(cond, 'left', None)
        if left_expr is not None:
            self._walk_expression(left_expr, negated)
        
        right_expr = getattr(cond, 'right', None)
        if right_expr is not None:
            self._walk_expression(right_expr, negated)
    
    def _walk_expression(
        self,
        expr: Expression,
        negated: Set[str]
    ):
        """
        Expressionツリーを再帰的に走査してbvneg(param)を検出
        
        Args:
            expr: 走査するExpression
            negated: 検出されたパラメータ名を追加するセット
        """
        if expr is None:
            return
        
        # UNARY_OP かつ INT_2COMP (bvneg) をチェック（getattr で安全にアクセス）
        expr_type = getattr(expr, 'expr_type', None)
        if expr_type is None:
            expr_type = getattr(expr, 'type', None)
        
        if expr_type is None:
            return
        
        if expr_type == ExpressionType.UNARY_OP:
            operator = getattr(expr, 'operator', None)
            if operator == "INT_2COMP":
                # オペランドがパラメータかチェック
                operands = getattr(expr, 'operands', None)
                if operands and len(operands) > 0:
                    operand = operands[0]
                    
                    operand_type = getattr(operand, 'expr_type', None)
                    if operand_type is None:
                        operand_type = getattr(operand, 'type', None)
                    
                    if operand_type == ExpressionType.PARAMETER:
                        param_name = getattr(operand, 'name', None)
                        if param_name is not None:
                            negated.add(param_name)
        
        # 再帰的に子ノードを探索
        if hasattr(expr, 'operands') and expr.operands:
            for operand in expr.operands:
                if operand is not None:
                    self._walk_expression(operand, negated)
    
    def _find_param_info(
        self,
        param_name: str,
        param_infos: List['ParameterInfo']
    ) -> Optional['ParameterInfo']:
        """
        パラメータ名からParameterInfoを検索
        
        Args:
            param_name: 元のパラメータ名（"param_1" など）
            param_infos: ParameterInfoのリスト
        
        Returns:
            見つかったParameterInfo、見つからなければNone
        """
        for info in param_infos:
            if info.original_name == param_name:
                return info
        return None
