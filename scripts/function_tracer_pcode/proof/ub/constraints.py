# -*- coding: utf-8 -*-
"""
C の未定義動作（UB）を起こし得る入力を表す SMT 制約（obligation）を作るモジュール

扱う UB の種類:
1. 負号の -INT_MIN オーバーフロー（INT_2COMP の被演算子が最小値）
2. シフト量が演算の幅以上のシフト
3. 符号付きの左シフト（被演算子が負、または結果が表せない。signed left shift overflow）

Issue #298: obligation の使い道は **反例の領域** だけ（:mod:`proof.ub.domain`）。
NOT_EQ の witness は、どちらの関数の source でも UB を起こさない入力でなければならない。
binary の演算から source の演算・その符号・実行条件は示せないので、ここは UB を起こし得る
入力を **上から近似** する:

- 式の graph の全ての node（被演算子・PHI の条件と値・call / memory の被演算子）を、
  共有の走査（``core.semantic_snapshot.traverse_semantic_graph``）で辿る。経路の条件は
  付けない（どの演算がどの入力で実行されるかを binary から示せない）。
- 符号を推測で除外しない。引数が unsigned と宣言されていても ``-(int)x`` はあり得るので、
  負号・左シフトは被演算子の型・文脈に依らず制約にする（#31 の保護を包む）。

扱わない UB（反例の領域に入らない）: 整数の加算・減算・乗算の符号付き overflow、除算の
0 除算・INT_MIN / -1、ポインタ演算。これらの UB だけで違う関数は NOT_EQ になり得る
（既知の制約。PR #312 の本文と Issue に記録）。
- 幅は演算と被演算子の小さい方（被演算子の幅が演算と違う形は描画が拒否する:
  ``core.render_smt`` の ``UnsupportedSmtOperatorError``）。

EQ の前提には使わない。P-code の演算は全ての入力で定義されていて、binary の演算 1 つは
source の UB の根拠にならない（UB 制約を EQ の前提に課すと、正当な入力を除き得る）。

runtime ref（loop summary など）の内部の演算は、式の graph の辺に現れないのでここでは
数えない（整数の加算・乗算の overflow と同じく、この model の範囲外。Issue #309）。
"""

from dataclasses import dataclass
from typing import Callable, Iterable, List, Optional, Set, TYPE_CHECKING, Tuple

from scripts.function_tracer_pcode.core import (
    FunctionReturnAnalysis,
    Expression,
    ExpressionType,
)
from scripts.function_tracer_pcode.core.render_smt.widths import constant_value_at_width
from scripts.function_tracer_pcode.core.semantic_snapshot import traverse_semantic_graph

if TYPE_CHECKING:
    from scripts.function_tracer_pcode.proof.formula.builder import ParameterInfo


ALL_UB_CONSTRAINT_TYPES = frozenset({
    "negate_min",
    "shift_count",
    "signed_left_shift_overflow",
})

_SHIFT_OPERATORS = frozenset({"INT_LEFT", "INT_RIGHT", "INT_SRIGHT"})


@dataclass(frozen=True)
class UbObligation:
    """演算 1 つについて「UB を起こさない」ことの SMT の Bool 項 ``ok(o)``。"""

    kind: str
    operator: str
    term: str
    comment: str

    def assertion_lines(self) -> Tuple[str, str]:
        return (f"; {self.comment}", f"(assert {self.term})")


def obligation_lines(obligations: Iterable[UbObligation]) -> List[str]:
    """obligation を SMT の行（comment + assert）に並べる。"""
    lines: List[str] = []
    for obligation in obligations:
        lines.extend(obligation.assertion_lines())
    return lines


def analysis_expressions(analysis: FunctionReturnAnalysis) -> List[Expression]:
    """解析の全 return の値と条件の式（関数全体の obligation を集める根）。"""
    expressions: List[Expression] = []
    for ret in analysis.returns or ():
        if ret.value is not None:
            expressions.append(ret.value)
        for cond in ret.conditions or ():
            expr = getattr(cond, "expression", None)
            if expr is not None:
                expressions.append(expr)
    return expressions


def iter_operation_nodes(roots: Iterable[Optional[Expression]]) -> List[Expression]:
    """根から辿れる **program の演算** の node（共有は 1 回、決定的な順）。

    走査は ``traverse_semantic_graph``（PHI の条件と値・call / memory の被演算子を含む
    唯一の実装）に任せ、ここで辺の種類を選ばない。

    store の観測の番地（``core.observation_index``）に依存する node は除く。観測の番地は
    入力ではなく、左右の書き込みを同じ番地で比べるための記号で、それに依存する演算（書いた
    値の byte を取り出す shift など）は解析が作った比べる面の一部で、program の演算ではない
    （``analysis.effects.observation_surface``。範囲の判定の下でだけ使う）。書いた値そのものの
    演算は番地に依存しないので残る。
    """
    from scripts.function_tracer_pcode.core.observation_index import is_observation_index
    from scripts.function_tracer_pcode.core.semantic_snapshot import ordered_semantic_edges

    nodes: List[Expression] = []
    seen: Set[int] = set()
    depends_on_index: dict = {}
    for root in roots:
        if root is None:
            continue
        traversal = traverse_semantic_graph(root)
        for node in traversal.post_order:
            if id(node) in depends_on_index:
                continue
            depends_on_index[id(node)] = is_observation_index(node) or any(
                depends_on_index.get(id(edge.child), False)
                for edge in ordered_semantic_edges(node)
                if edge.child is not None
            )
        for node in traversal.entry_order:
            if id(node) in seen or depends_on_index.get(id(node), False):
                continue
            seen.add(id(node))
            nodes.append(node)
    return nodes


def _bits(expr: Optional[Expression]) -> int:
    """描画での値の幅（``core.render_smt`` と同じ規則。比較・bool は size byte の 0 / 1）。"""
    if expr is None:
        return 0
    from scripts.function_tracer_pcode.core.render_smt import expression_smt_bit_width

    return int(expression_smt_bit_width(expr) or 0)


def operation_bits(op_expr: Expression, operand: Expression) -> int:
    """演算の UB の幅: 演算（P-code の出力）と第 1 被演算子の幅の小さい方（上から近似）。"""
    op_bits = int(getattr(op_expr, "size", 0) or 0) * 8
    operand_bits = _bits(operand)
    widths = [bits for bits in (op_bits, operand_bits) if bits > 0]
    return min(widths) if widths else 0


class UbConstraintBuilder:
    """UB を起こし得る入力を除く obligation を作るクラス"""

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
        symbol_replace_fn: Optional[Callable] = None,
    ) -> List[str]:
        """関数全体の obligation を SMT の行で返す（反例の領域の片側）。"""
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
        symbol_replace_fn: Optional[Callable] = None,
    ) -> List[UbObligation]:
        """与えた式から辿れる全ての演算の obligation（同じ条件は 1 つにまとめる）。

        ``param_infos`` は互換のために受け取るだけで使わない（引数の宣言の符号では除外しない）。
        描画が拒否する式（``SMT_SEMANTICS_REFUSALS``）はそのまま送出する。呼び手は領域を
        作れなかったものとして扱う（witness にしない）。
        """
        del param_infos
        if constraint_types is None:
            constraint_types = set(ALL_UB_CONSTRAINT_TYPES)
        unique: List[UbObligation] = []
        seen: Set[str] = set()
        for node in iter_operation_nodes(expressions):
            for obligation in self._node_obligations(node, constraint_types, symbol_replace_fn):
                if obligation.term in seen:
                    continue
                seen.add(obligation.term)
                unique.append(obligation)
        return unique

    @staticmethod
    def _render(expr: Expression, symbol_replace_fn: Optional[Callable], bits: int) -> str:
        """``bits`` 幅の bitvector として描く（bool は 0 / 1、広い値は下位を取る）。"""
        from scripts.function_tracer_pcode.proof.formula.returns import coerce_value_to_bitvec_width

        if symbol_replace_fn is None:
            rendered = expr.to_smt()
        else:
            try:
                rendered = symbol_replace_fn(expr)
            except TypeError:
                rendered = symbol_replace_fn(expr.to_smt())
        return coerce_value_to_bitvec_width(expr, rendered, bits)

    def _node_obligations(
        self,
        node: Expression,
        constraint_types: Set[str],
        symbol_replace_fn: Optional[Callable],
    ) -> List[UbObligation]:
        expr_type = getattr(node, "expr_type", None)
        operator = getattr(node, "operator", None)
        operands = list(getattr(node, "operands", None) or ())
        if expr_type == ExpressionType.UNARY_OP and operator == "INT_2COMP" and operands:
            if "negate_min" in constraint_types:
                return self._negate_min(node, operands[0], symbol_replace_fn)
            return []
        if expr_type == ExpressionType.BINARY_OP and operator in _SHIFT_OPERATORS and len(operands) >= 2:
            result: List[UbObligation] = []
            if "shift_count" in constraint_types:
                result.extend(self._shift_count(node, operands[0], operands[1], symbol_replace_fn))
            if operator == "INT_LEFT" and "signed_left_shift_overflow" in constraint_types:
                result.extend(
                    self._signed_left_shift(node, operands[0], operands[1], symbol_replace_fn)
                )
            return result
        return []

    def _shift_count(self, node, left, right, symbol_replace_fn) -> List[UbObligation]:
        """シフト量が演算の幅未満（C では左右とも、量が負・幅以上なら UB）。"""
        op_bits = operation_bits(node, left)
        right_bits = _bits(right)
        if op_bits <= 0 or right_bits <= 0 or op_bits >= (1 << right_bits):
            return []  # 量の幅で表せる値は全て上限未満（制約は真）
        if self._constant_below(right, op_bits):
            return []
        right_smt = self._render(right, symbol_replace_fn, right_bits)
        self._debug_print(f"shift-count obligation for {node.operator}: {right_smt} < {op_bits}")
        return [UbObligation(
            kind="shift_count",
            operator=str(node.operator),
            term=f"(bvult {right_smt} (_ bv{op_bits} {right_bits}))",
            comment=f"Exclude UB: {node.operator} shift amount must be < {op_bits} bits",
        )]

    def _signed_left_shift(self, node, left, right, symbol_replace_fn) -> List[UbObligation]:
        """符号付きの左シフトの UB（C: E1 が負、または E1·2^E2 が表せない）を除く（上から近似）。

        binary の左シフトから source の符号は示せない（unsigned なら定義済み、source の乗算
        ``x * 2`` の符号付きの overflow でもあり得る）ので、被演算子の型・文脈に依らず課す:
        ``E1 <u 2^(w-1) >> E2``（E1 が非負で、E1 << E2 が符号付きで表せる）。量 E2 >= w は
        ``shift_count`` の制約が除く。E1 が定数 0 なら UB は無い。
        """
        width = operation_bits(node, left)
        right_bits = _bits(right)
        if width <= 1 or right_bits <= 0:
            return []
        lhs_value = constant_value_at_width(left, width)
        if lhs_value == 0:
            return []
        count_value = constant_value_at_width(right, right_bits)
        if count_value is not None and count_value >= width:
            return []  # 量が幅以上（shift_count の制約が除く）
        if lhs_value is not None and count_value is not None:
            if lhs_value < (1 << (width - 1)) >> count_value:
                return []  # 定数どうしで表せる
            term = "false"
        elif count_value is not None:
            bound = (1 << (width - 1)) >> count_value
            lhs_smt = self._render(left, symbol_replace_fn, width)
            term = f"(bvult {lhs_smt} (_ bv{bound} {width}))"
        else:
            lhs_smt = (
                f"(_ bv{lhs_value} {width})" if lhs_value is not None
                else self._render(left, symbol_replace_fn, width)
            )
            count_smt = self._render(right, symbol_replace_fn, right_bits)
            if right_bits < width:
                count_smt = f"((_ zero_extend {width - right_bits}) {count_smt})"
            elif right_bits > width:
                count_smt = f"((_ extract {width - 1} 0) {count_smt})"
            term = f"(bvult {lhs_smt} (bvlshr (_ bv{1 << (width - 1)} {width}) {count_smt}))"
        self._debug_print(f"signed-left-shift obligation: {term}")
        return [UbObligation(
            kind="signed_left_shift_overflow",
            operator="INT_LEFT",
            term=term,
            comment=f"Exclude UB: signed left shift of a negative or overflowing {width}-bit value",
        )]

    def _negate_min(self, node, operand, symbol_replace_fn) -> List[UbObligation]:
        """負号の被演算子が最小値でない（被演算子の符号・文脈では除外しない）。"""
        width = operation_bits(node, operand)
        if width <= 1:
            return []
        min_val = 1 << (width - 1)
        operand_value = constant_value_at_width(operand, width)
        if operand_value is not None and operand_value != min_val:
            return []
        operand_smt = self._render(operand, symbol_replace_fn, width)
        self._debug_print(f"negation obligation: {operand_smt} != {min_val} ({width} bits)")
        return [UbObligation(
            kind="negate_min",
            operator="INT_2COMP",
            term=f"(not (= {operand_smt} (_ bv{min_val} {width})))",
            comment=f"Exclude UB: -({operand_smt}) when {operand_smt} = INT{width}_MIN",
        )]

    @staticmethod
    def _constant_below(expr: Expression, bound: int) -> bool:
        """定数が描画で表す値（幅の剰余）が ``bound`` 未満か。"""
        value = constant_value_at_width(expr)
        return value is not None and value < bound
