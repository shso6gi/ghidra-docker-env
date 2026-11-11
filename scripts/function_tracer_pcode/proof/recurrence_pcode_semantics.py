"""Issue #297: P-code の写し（``PcodeDataflowSnapshot``）の値を、proof が自分で式にする。

return binding の proof は、producer（builder・tracer）が作った式を信じない。start / limit / 初期値と、
ループ 1 回分の accumulator の更新は、ここで写しの op から直接作り、候補の式とは SMT で照合する。

- 作れるのは、意味が P-code の定義どおりに決まる純粋な整数演算・比較・bool 演算だけ
  （``LOWERABLE_MNEMONICS``）。memory・call・除算（trap）・LZCOUNT などの op、識別できない入力に
  着いたら :class:`LoweringFailure` で止める（推測で埋めない）。
- 定数は値と幅のまま。関数の引数は、写しの引数の表（Ghidra の prototype の置き場所）と照合できた入力
  だけを、その番号の全幅の ``PARAMETER`` にする（SMT の symbol は番号で決まる）。置き場所が引数の
  storage の一部なら、byte order に従う ``SUBPIECE`` にする。引数でない・表と照合できない・複数の
  storage の引数の ``free`` な入力は作れない。
- シフトは量の幅が値と違ってもよい（量が値の bit 数以上なら 0、算術右シフトは符号で埋める）。この意味は
  共有の SMT 描画（``core.render_smt``）が持つ。
- 分岐の条件と bool 演算の入力は、比較・bool 演算の結果（と 0 / 1 の定数）に限る（1 byte の整数を
  真偽として読む規則を持ち込まない）。
- ループの値: header の帰納変数・accumulator の PHI は呼び出し側が渡す placeholder にする。header の
  他の PHI（別のループ運搬値）は作れない。header を除いた region は循環が無い（呼び出し側が T6 で
  確かめる）ので、body の MULTIEQUAL は、入辺の **経路条件**（header からその辺までの分岐条件の論理積の
  論理和）で選ぶ PHI 式にする。どの入辺の条件も作れないときは止める（経路を落とさない）。
"""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.core import Condition, Expression
from scripts.function_tracer_pcode.core.recurrence_return_binding import (
    PcodeDataflowSnapshot,
    PcodeFactInput,
    PcodeFactOp,
)

#: 式にする op（Ghidra の P-code の定義どおりの意味。CAST は同幅の bit の写し）。
_UNARY = frozenset({"INT_ZEXT", "INT_SEXT", "INT_NEGATE", "INT_2COMP", "BOOL_NEGATE"})
_BINARY = frozenset({
    "INT_ADD", "INT_SUB", "INT_MULT", "INT_AND", "INT_OR", "INT_XOR",
    "INT_LEFT", "INT_RIGHT", "INT_SRIGHT", "PIECE",
    "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_LESSEQUAL", "INT_SLESS", "INT_SLESSEQUAL",
    "BOOL_AND", "BOOL_OR", "BOOL_XOR",
})
_BOOLEAN_RESULT = frozenset({
    "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_LESSEQUAL", "INT_SLESS", "INT_SLESSEQUAL",
    "BOOL_AND", "BOOL_OR", "BOOL_XOR", "BOOL_NEGATE",
})
_BOOLEAN_OPERATORS = frozenset({"BOOL_AND", "BOOL_OR", "BOOL_XOR"})
LOWERABLE_MNEMONICS = frozenset({"COPY", "CAST", "SUBPIECE", "MULTIEQUAL"}) | _UNARY | _BINARY
#: 1 つの値を作るときに辿る op の数の上限（超えたら作らない）。
LOWERING_MAX_OPS = 256


class LoweringFailure(ValueError):
    """写しの値を式にできない（``reason`` が理由）。"""

    def __init__(self, reason: str) -> None:
        self.reason = reason
        super().__init__(reason)


class SnapshotLowering:
    """1 つのループ（header・region）の文脈で、写しの値を式にする。

    ``leaves`` は op の key → その出力の代わりの式（帰納変数・accumulator の placeholder）。
    ``region`` の外の op はループに入る前に決まった値（SSA で定義が使用を支配する）として作る。
    同じ op は 1 回だけ作り、式は共有する（DAG）。
    """

    def __init__(
        self,
        snapshot: PcodeDataflowSnapshot,
        *,
        header_index: int,
        region: frozenset,
        leaves: Optional[Mapping[Tuple[Any, ...], Expression]] = None,
        max_ops: int = LOWERING_MAX_OPS,
    ) -> None:
        self._snapshot = snapshot
        self._header = header_index
        self._region = frozenset(region)
        self._leaves = dict(leaves or {})
        self._max_ops = max_ops
        self._values: Dict[Tuple[Any, ...], Expression] = {}
        self._active: set = set()
        self._path_conditions: Dict[int, Optional[Expression]] = {}
        self._path_active: set = set()

    # -- 値 -----------------------------------------------------------------

    def value(self, item: PcodeFactInput) -> Expression:
        if item.kind == "constant":
            return Expression.constant(int(item.constant), size=item.size)
        if item.kind == "free":
            return self._parameter_input(item)
        return self._op_value(item.producer_key, item.size)

    def condition(self, item: PcodeFactInput) -> Expression:
        """真偽として読む入力（分岐の条件・bool 演算の被演算子）。比較・bool 演算の結果に限る。"""

        if not self._is_boolean(item):
            raise LoweringFailure("non_boolean_condition")
        return self.value(item)

    def _is_boolean(self, item: PcodeFactInput) -> bool:
        if item.size != 1:
            return False
        if item.kind == "constant":
            return int(item.constant) in (0, 1)
        if item.kind != "op":
            return False
        op = self._snapshot.op(item.producer_key)
        while op is not None and op.mnemonic == "COPY" and len(op.inputs) == 1 and op.inputs[0].kind == "op":
            op = self._snapshot.op(op.inputs[0].producer_key)
        return op is not None and op.mnemonic in _BOOLEAN_RESULT

    def _parameter_input(self, item: PcodeFactInput) -> Expression:
        if item.parameter_index is None:
            raise LoweringFailure(f"free_input_not_parameter:{item.storage[0]}")
        fact = self._snapshot.parameter(item.parameter_index)
        if fact is None:
            raise LoweringFailure("parameter_not_in_prototype")
        offset = fact.value_slice(item.storage, item.size, big_endian=self._snapshot.big_endian)
        if offset is None:
            raise LoweringFailure(
                "parameter_multi_storage" if len(fact.pieces) != 1 else "parameter_storage_mismatch"
            )
        whole = Expression.parameter(f"param_{fact.index + 1}", index=fact.index, size=fact.size)
        if item.size == fact.size:
            return whole
        piece = Expression.binary_op("SUBPIECE", whole, Expression.constant(offset, size=4))
        piece.size = item.size
        return piece

    def _op_value(self, key: Tuple[Any, ...], size: int) -> Expression:
        if key in self._leaves:
            leaf = self._leaves[key]
            if int(leaf.size or 0) != size:
                raise LoweringFailure("leaf_width")
            return leaf
        cached = self._values.get(key)
        if cached is not None:
            return cached
        if key in self._active:
            raise LoweringFailure("cycle")
        if len(self._values) + len(self._active) >= self._max_ops:
            raise LoweringFailure("op_bound_exceeded")
        op = self._snapshot.op(key)
        if op is None:
            raise LoweringFailure("unknown_op")
        if op.output_size != size:
            raise LoweringFailure(f"width:{op.mnemonic}")
        self._active.add(key)
        try:
            expr = self._lower(op)
        finally:
            self._active.discard(key)
        self._values[key] = expr
        return expr

    def _lower(self, op: PcodeFactOp) -> Expression:
        name = op.mnemonic
        size = int(op.output_size)
        if name not in LOWERABLE_MNEMONICS:
            raise LoweringFailure(f"unsupported:{name}")
        inputs = op.inputs
        if name in {"COPY", "CAST"}:
            if len(inputs) != 1 or inputs[0].size != size:
                raise LoweringFailure(f"shape:{name}")
            return self.value(inputs[0])
        if name == "MULTIEQUAL":
            return self._phi(op)
        if name == "SUBPIECE":
            if len(inputs) != 2 or inputs[1].kind != "constant" or inputs[1].constant + size > inputs[0].size:
                raise LoweringFailure("shape:SUBPIECE")
            expr = Expression.binary_op("SUBPIECE", self.value(inputs[0]), self.value(inputs[1]))
        elif name == "BOOL_NEGATE":
            if len(inputs) != 1 or size != 1:
                raise LoweringFailure("shape:BOOL_NEGATE")
            expr = Expression.unary_op(name, self.condition(inputs[0]))
        elif name in _UNARY:
            if len(inputs) != 1:
                raise LoweringFailure(f"shape:{name}")
            if name in {"INT_ZEXT", "INT_SEXT"} and inputs[0].size >= size:
                raise LoweringFailure(f"shape:{name}")
            if name not in {"INT_ZEXT", "INT_SEXT"} and inputs[0].size != size:
                raise LoweringFailure(f"shape:{name}")
            expr = Expression.unary_op(name, self.value(inputs[0]))
        else:
            if len(inputs) != 2:
                raise LoweringFailure(f"shape:{name}")
            if name == "PIECE":
                if inputs[0].size + inputs[1].size != size:
                    raise LoweringFailure("shape:PIECE")
            elif name in _BOOLEAN_RESULT:
                if size != 1 or inputs[0].size != inputs[1].size:
                    raise LoweringFailure(f"shape:{name}")
            elif name not in {"INT_LEFT", "INT_RIGHT", "INT_SRIGHT"} and (
                inputs[0].size != size or inputs[1].size != size
            ):
                raise LoweringFailure(f"shape:{name}")
            elif name in {"INT_LEFT", "INT_RIGHT", "INT_SRIGHT"} and inputs[0].size != size:
                raise LoweringFailure(f"shape:{name}")
            if name in _BOOLEAN_OPERATORS:
                expr = Expression.binary_op(name, self.condition(inputs[0]), self.condition(inputs[1]))
            else:
                expr = Expression.binary_op(name, self.value(inputs[0]), self.value(inputs[1]))
        expr.size = size
        return expr

    # -- 経路条件と PHI -------------------------------------------------------

    def _phi(self, op: PcodeFactOp) -> Expression:
        block_index = op.block_index
        if block_index == self._header:
            raise LoweringFailure("loop_carried_value")
        if block_index not in self._region:
            raise LoweringFailure("multiequal_outside_loop")
        block = self._snapshot.block(block_index)
        if len(op.inputs) != len(block.predecessors) or not op.inputs:
            raise LoweringFailure("shape:MULTIEQUAL")
        branches = [
            (self.edge_condition(predecessor, block_index), self.value(item))
            for predecessor, item in zip(block.predecessors, op.inputs)
        ]
        return self.select(branches, int(op.output_size))

    def select(self, branches: List[Tuple[Optional[Expression], Expression]], size: int) -> Expression:
        """入辺の条件で選ぶ値（条件は互いに排他で、いずれかが成り立つ。最後の値が既定）。"""

        if len(branches) == 1:
            return branches[0][1]
        phi = Expression.phi([
            (_condition(condition), value) for condition, value in branches
        ])
        phi.size = size
        return phi

    def edge_condition(self, source: int, target: int) -> Optional[Expression]:
        """region の中の辺 ``source → target`` を通る条件（header から。``None`` は恒真）。"""

        return _conjoin(self.path_condition(source), self.branch_condition(source, target))

    def path_condition(self, index: int) -> Optional[Expression]:
        """header（1 回分の反復の始まり）から block ``index`` に着く条件。"""

        if index == self._header:
            return None
        if index in self._path_conditions:
            return self._path_conditions[index]
        if index not in self._region:
            raise LoweringFailure("path_outside_loop")
        if index in self._path_active:
            raise LoweringFailure("inner_cycle")
        block = self._snapshot.block(index)
        self._path_active.add(index)
        try:
            terms = []
            for predecessor in block.predecessors:
                if predecessor not in self._region:
                    raise LoweringFailure("irreducible_loop_entry")
                terms.append(self.edge_condition(predecessor, index))
        finally:
            self._path_active.discard(index)
        condition = None
        if all(term is not None for term in terms):
            for term in terms:
                condition = term if condition is None else _boolean("BOOL_OR", condition, term)
        self._path_conditions[index] = condition
        return condition

    def branch_condition(self, source: int, target: int) -> Optional[Expression]:
        """block ``source`` の終わりの分岐で ``target`` へ進む条件（``None`` は恒真）。"""

        block = self._snapshot.block(source)
        successors = tuple(block.successors)
        if target not in successors:
            raise LoweringFailure("not_an_edge")
        if len(set(successors)) == 1:
            return None
        if len(successors) != 2 or block.true_successor is None or block.false_successor is None:
            raise LoweringFailure("multiway_branch")
        cbranches = [
            self._snapshot.op(key) for key in block.op_keys
            if self._snapshot.op(key).mnemonic == "CBRANCH"
        ]
        if len(cbranches) != 1 or len(cbranches[0].inputs) < 2 or cbranches[0].inputs[1].size != 1:
            raise LoweringFailure("branch_condition_shape")
        condition = self.condition(cbranches[0].inputs[1])
        if target == block.true_successor:
            return condition
        negated = Expression.unary_op("BOOL_NEGATE", condition)
        negated.size = 1
        return negated


def _boolean(operator: str, left: Expression, right: Expression) -> Expression:
    expr = Expression.binary_op(operator, left, right)
    expr.size = 1
    return expr


def _conjoin(left: Optional[Expression], right: Optional[Expression]) -> Optional[Expression]:
    if left is None:
        return right
    if right is None:
        return left
    return _boolean("BOOL_AND", left, right)


def _condition(expr: Optional[Expression]) -> Optional[Condition]:
    return None if expr is None else Condition(expr, False)
