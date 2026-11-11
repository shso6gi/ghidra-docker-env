# -*- coding: utf-8 -*-
"""
C言語の未定義動作（UB）を除外する SMT 制約（obligation）を生成するモジュール

現在サポートされているUB:
1. 符号付き整数の -MIN_INT オーバーフロー (bvneg on INT_MIN)
2. シフト量がビット幅以上になるシフト演算
3. signed left shift の表現不能オーバーフロー（guarded subset）

Issue #298: 制約は「その演算が実行されたときにだけ課す」もの（``exec(o) ⇒ ok(o)``）。
このモジュールは演算 o ごとの ``ok(o)`` を :class:`UbObligation` として作るだけで、
どこで課すか（経路への結び付け）は :mod:`proof.ub.premise` が決める。

- 幅は binary の演算（P-code の出力 varnode の大きさ）から取る。型の仮説が引数の葉の幅を
  変えても、演算の UB の条件は変えない（仮説が作った制約を EQ の根拠にしない）。
- 幅が binary の演算から決まらない obligation は ``eq_admissible=False`` にする。EQ の
  前提には使わず、反例の領域（NOT_EQ の側）だけに残す。

将来拡張予定:
- INT_MIN / -1 オーバーフロー
- ポインタ演算のUB
"""

from dataclasses import dataclass
from typing import Callable, Iterable, Set, List, Optional, TYPE_CHECKING, Tuple

from scripts.function_tracer_pcode.core import (
    FunctionReturnAnalysis,
    Expression,
    ExpressionType,
)
from scripts.function_tracer_pcode.analysis.debug import summarize_expression

# 型チェック用のインポート（循環参照を避けるため）
if TYPE_CHECKING:
    from scripts.function_tracer_pcode.proof.formula.builder import ParameterInfo


ALL_UB_CONSTRAINT_TYPES = frozenset({
    "negate_min",
    "shift_count",
    "signed_left_shift_overflow",
})


@dataclass(frozen=True)
class UbObligation:
    """演算 1 つの UB 除外条件 ``ok(o)``（SMT の Bool 項）。

    ``eq_admissible`` は、条件の幅・意味が binary の演算から決まったか。False のものは
    EQ の前提に使わない（反例の領域にだけ使う）。
    """

    kind: str
    operator: str
    term: str
    comment: str
    eq_admissible: bool = True

    def assertion_lines(self) -> Tuple[str, str]:
        return (f"; {self.comment}", f"(assert {self.term})")


def obligation_lines(obligations: Iterable[UbObligation]) -> List[str]:
    """obligation を SMT の行（comment + assert）に並べる。"""
    lines: List[str] = []
    for obligation in obligations:
        lines.extend(obligation.assertion_lines())
    return lines


def analysis_expressions(analysis: FunctionReturnAnalysis) -> List[Expression]:
    """解析の全 return の値と条件の式（関数全体の obligation を集める範囲）。"""
    expressions: List[Expression] = []
    for ret in analysis.returns or ():
        if ret.value is not None:
            expressions.append(ret.value)
        for cond in ret.conditions or ():
            expr = getattr(cond, "expression", None)
            if expr is not None:
                expressions.append(expr)
    return expressions


class UbConstraintBuilder:
    """未定義動作（UB）を除外する obligation を生成するクラス"""

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
        関数全体（全 return の値と条件）の UB 除外制約を SMT の行で返す

        経路に結び付けない形なので、反例の領域（全ての演算が UB を起こさない入力）を
        表す。EQ の前提には :mod:`proof.ub.premise` の経路に結び付けた形を使う。

        Args:
            analysis: 関数解析結果
            param_infos: パラメータ情報（SMT名・ビット幅付き）
            constraint_types: 生成する制約タイプのセット（None なら全タイプ）
            symbol_replace_fn: Expression.to_smt() で得た元名を SMT 変数名へ置換する関数

        Returns:
            SMT-LIB形式の制約行のリスト
        """
        return obligation_lines(
            self.collect_obligations(
                analysis_expressions(analysis),
                param_infos,
                constraint_types=constraint_types,
                symbol_replace_fn=symbol_replace_fn,
            )
        )

    def collect_obligations(
        self,
        expressions: Iterable[Optional[Expression]],
        param_infos: List['ParameterInfo'],
        *,
        constraint_types: Optional[Set[str]] = None,
        symbol_replace_fn: Optional[Callable[[str], str]] = None,
    ) -> List[UbObligation]:
        """与えた式の中の演算の obligation（同じ条件は 1 つにまとめる）。"""
        if constraint_types is None:
            constraint_types = set(ALL_UB_CONSTRAINT_TYPES)
        roots = [expr for expr in expressions if expr is not None]

        obligations: List[UbObligation] = []
        if "negate_min" in constraint_types:
            obligations.extend(
                self._negate_min_obligations(roots, param_infos, symbol_replace_fn)
            )
        if "shift_count" in constraint_types:
            obligations.extend(self._shift_count_obligations(roots, symbol_replace_fn))
        if "signed_left_shift_overflow" in constraint_types:
            obligations.extend(
                self._signed_left_shift_obligations(roots, symbol_replace_fn)
            )

        unique: List[UbObligation] = []
        seen: Set[str] = set()
        for obligation in obligations:
            if obligation.term in seen:
                continue
            seen.add(obligation.term)
            unique.append(obligation)
        return unique

    @staticmethod
    def _render(expr: Expression, symbol_replace_fn: Optional[Callable]) -> str:
        rendered = expr.to_smt()
        if symbol_replace_fn is not None:
            try:
                rendered = symbol_replace_fn(expr)
            except TypeError:
                rendered = symbol_replace_fn(rendered)
        return rendered

    @staticmethod
    def _binary_op_bits(op_expr: Expression, operand: Expression) -> Tuple[int, bool]:
        """演算の幅（binary の出力 varnode の大きさ）と、それが被演算子の幅と一致するか。

        P-code の shift・負号は、出力と第 1 入力の大きさが同じ。型の仮説で引数の葉だけが
        狭くなっても、演算の node は binary の大きさを保つ（Issue #298）。
        """
        operand_bits = int(operand.get_bit_width() or 0)
        op_size = int(getattr(op_expr, "size", 0) or 0)
        if op_size > 0:
            op_bits = op_size * 8
            return op_bits, op_bits == operand_bits
        return operand_bits, True

    def _shift_count_obligations(
        self,
        roots: List[Expression],
        symbol_replace_fn: Optional[Callable],
    ) -> List[UbObligation]:
        """
        シフト量がビット幅未満であることを要求する obligation

        Cでは左右シフトともに、shift count が負または演算のビット幅以上だと未定義動作。
        BV上では負値も大きな unsigned 値として表現されるため、`bvult rhs width` で両方を
        除外できる。幅は binary の演算の幅。
        """
        shift_sites: List[Tuple[str, Expression]] = []
        for root in roots:
            self._walk_expression_for_shift(root, shift_sites)
        if not shift_sites:
            self._debug_print("No shift operations found for UB constraints")
            return []

        obligations: List[UbObligation] = []
        for operator, shift_expr in shift_sites:
            if len(shift_expr.operands) < 2:
                continue
            left = shift_expr.operands[0]
            right = shift_expr.operands[1]
            op_bits, _same = self._binary_op_bits(shift_expr, left)
            right_bits = right.get_bit_width()
            if op_bits <= 0 or right_bits <= 0:
                continue
            if self._is_shift_count_statically_safe(right, op_bits):
                continue
            right_smt = self._render(right, symbol_replace_fn)
            obligations.append(
                UbObligation(
                    kind="shift_count",
                    operator=operator,
                    term=f"(bvult {right_smt} (_ bv{op_bits} {right_bits}))",
                    comment=f"Exclude UB: {operator} shift amount must be < {op_bits} bits",
                )
            )
            self._debug_print(
                f"Added shift-count UB constraint for {operator}: {right_smt} < {op_bits}"
            )
        return obligations

    def _signed_left_shift_obligations(
        self,
        roots: List[Expression],
        symbol_replace_fn: Optional[Callable],
    ) -> List[UbObligation]:
        """
        signed left shift overflow を guarded に除外する obligation

        対象は次の保守的 subset のみ:
        - INT_LEFT(lhs, rhs)
        - lhs が正の定数
        - shift 結果が signed 演算文脈で使われている

        これにより unsigned left shift まで誤って制約しないようにする。
        """
        signed_shift_sites: List[Expression] = []
        for root in roots:
            self._walk_expression_for_signed_left_shift(
                root, signed_shift_sites, signed_context=False
            )
        if not signed_shift_sites:
            self._debug_print("No guarded signed-left-shift sites found")
            return []

        obligations: List[UbObligation] = []
        for shift_expr in signed_shift_sites:
            if len(shift_expr.operands) < 2:
                continue
            left = shift_expr.operands[0]
            right = shift_expr.operands[1]
            bound = self._get_signed_left_shift_safe_bound(left, shift_expr.get_bit_width())
            if bound is None:
                continue
            if self._is_shift_count_statically_safe(right, bound):
                continue
            right_smt = self._render(right, symbol_replace_fn)
            right_bits = right.get_bit_width()
            obligations.append(
                UbObligation(
                    kind="signed_left_shift_overflow",
                    operator="INT_LEFT",
                    term=f"(bvult {right_smt} (_ bv{bound} {right_bits}))",
                    comment=(
                        "Exclude UB: signed left shift overflow requires "
                        f"shift < {bound}"
                    ),
                )
            )
            self._debug_print(
                f"Added signed-left-shift UB constraint: {right_smt} < {bound}"
            )
        return obligations

    def _negate_min_obligations(
        self,
        roots: List[Expression],
        param_infos: List['ParameterInfo'],
        symbol_replace_fn: Optional[Callable],
    ) -> List[UbObligation]:
        """
        -INT_MIN オーバーフローを除外する obligation

        検出対象:
        - 式の中の INT_2COMP (bvneg)
        - オペランドがパラメータなら、そのパラメータが signed のとき
        - オペランドが任意の式なら、signed 演算文脈（INT_SLESS 等）の下にあるとき
          （unsigned の負号は C で定義済みなので除外しない）

        生成制約:
        - (not (= <operand> (_ bvINT_MIN WIDTH)))

        被演算子の幅が演算の幅と違う（型の仮説で葉だけが狭くなった）ときは、INT_MIN の
        位置が binary の演算と一致しないので ``eq_admissible=False`` にする。
        """
        negation_sites: List[Tuple[Expression, bool]] = []
        for root in roots:
            self._walk_expression_for_negation(root, negation_sites, signed_context=False)
        if not negation_sites:
            self._debug_print("No negation sites found")
            return []

        obligations: List[UbObligation] = []
        for site, signed_context in negation_sites:
            operand = site.operands[0] if getattr(site, "operands", None) else None
            if operand is None or operand.expr_type == ExpressionType.CONSTANT:
                continue

            if operand.expr_type == ExpressionType.PARAMETER:
                param_info = self._find_param_info(getattr(operand, "name", None), param_infos)
                if param_info is None:
                    self._debug_print(
                        f"Warning: Parameter '{getattr(operand, 'name', None)}' not found in param_infos"
                    )
                    continue
                if not getattr(param_info, "is_signed", True):
                    self._debug_print(
                        f"Skipping unsigned negation of {param_info.smt_name} (defined behaviour)"
                    )
                    continue
                operand_smt = param_info.smt_name
                width = int(param_info.bit_width)
            else:
                if not signed_context:
                    if self.debug:
                        self._debug_print(
                            "Skipping negation outside signed context: "
                            f"{summarize_expression(operand)}"
                        )
                    continue
                width = int(operand.get_bit_width() or 0)
                if width <= 0:
                    continue
                operand_smt = self._render(operand, symbol_replace_fn)

            op_bits = int(getattr(site, "size", 0) or 0) * 8
            min_val = 2 ** (width - 1)
            obligations.append(
                UbObligation(
                    kind="negate_min",
                    operator="INT_2COMP",
                    term=f"(not (= {operand_smt} (_ bv{min_val} {width})))",
                    comment=f"Exclude UB: -({operand_smt}) when {operand_smt} = INT{width}_MIN",
                    eq_admissible=(op_bits <= 0 or op_bits == width),
                )
            )
            self._debug_print(
                f"Added constraint: {operand_smt} != {min_val} ({width}bit MIN)"
            )
        return obligations

    def _walk_expression_for_negation(
        self,
        expr: Optional[Expression],
        sites: List[Tuple[Expression, bool]],
        signed_context: bool,
    ) -> None:
        if expr is None:
            return
        next_signed_context = signed_context or self._is_signed_operation(expr)
        if (
            getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP
            and getattr(expr, "operator", None) == "INT_2COMP"
        ):
            sites.append((expr, next_signed_context))
        if hasattr(expr, "operands") and expr.operands:
            for operand in expr.operands:
                if operand is not None:
                    self._walk_expression_for_negation(operand, sites, next_signed_context)

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

    def _walk_expression_for_signed_left_shift(
        self,
        expr: Optional[Expression],
        shift_sites: List[Expression],
        signed_context: bool
    ) -> None:
        """signed 文脈を伝播しながら INT_LEFT を収集"""
        if expr is None:
            return

        next_signed_context = signed_context or self._is_signed_operation(expr)

        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "INT_LEFT"
            and next_signed_context
        ):
            shift_sites.append(expr)

        if hasattr(expr, "operands") and expr.operands:
            for operand in expr.operands:
                self._walk_expression_for_signed_left_shift(
                    operand,
                    shift_sites,
                    signed_context=next_signed_context,
                )

    def _is_shift_count_statically_safe(
        self,
        expr: Expression,
        width_bits: int
    ) -> bool:
        """定数シフト量が自明に安全かチェック"""
        if expr.expr_type != ExpressionType.CONSTANT:
            return False

        return 0 <= expr.value < width_bits

    def _get_signed_left_shift_safe_bound(
        self,
        left: Expression,
        result_bits: int
    ) -> Optional[int]:
        """正の定数 lhs に対して overflow しない shift 上限（排他的）を返す"""
        if left.expr_type != ExpressionType.CONSTANT:
            return None

        value = left.value
        if not isinstance(value, int) or value <= 0:
            return None

        if result_bits <= 1:
            return None

        signed_max = (1 << (result_bits - 1)) - 1
        if value > signed_max:
            return None

        bound = result_bits - value.bit_length()
        if bound <= 0:
            return None

        return bound

    def _is_signed_operation(self, expr: Expression) -> bool:
        """式ノードが signed 演算文脈を作るか"""
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False

        return expr.operator in {
            "INT_SDIV",
            "INT_SREM",
            "INT_SLESS",
            "INT_SLESSEQUAL",
            "INT_SRIGHT",
        }

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
