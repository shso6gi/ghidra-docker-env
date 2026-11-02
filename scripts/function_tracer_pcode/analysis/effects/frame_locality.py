# -*- coding: utf-8 -*-
"""frame の中の store を観測から外してよいことの、関数ごとの証拠（Issue #282 AC 9, I11）。

**entry SP より下というだけでは局所としない**。`location_relation.frame_local_range`（entry SP を起点とする
定数の範囲で `hi <= 0`）は候補を選ぶだけで、局所と認めるのはこの module の証拠がそろったときだけ:

* E1（frame の番地が外へ出ない）: frame の番地（SP / frame pointer の register を根に持つ値）が、呼び出しの
  引数・memory へ書く値・戻り値・分岐の条件のどれにも、**番地として読む位置（`MEMORY` の番地）以外で**
  現れない。外へ出た番地（callee・global への保存・戻り値）は後の呼び出しや caller から読まれ得る。条件の
  中の比較（`p == sp - 16`）も、入口の pointer が frame の slot を指す経路を作るので外へ出たとみなす。
* E2（callee が frame を読まない）: 関数に呼び出し（`CALL` / `CALLIND` / `CALLOTHER`）が無い。stack で渡す
  引数の領域（caller の frame の底）は callee が読む。callee がどの範囲を読むかは呼び出しの op の入力
  （decompiler の推定した prototype）からは証明できないので、呼び出しのある関数の frame の store は局所に
  しない。

確保された frame の範囲: high P-code には SP の更新が残らず、frame の大きさを示す証拠が無い。E1 と E2 が
成り立てば、entry SP より下のどの番地への store も関数の外から読まれない（読めるのは呼び出しと外へ出た番地
だけ）ので、範囲の上限 `hi <= 0` 以外の下限は要らない。

証拠が足りないとき（追跡の失敗・走査の上限超過を含む）は `proven=False` で、consumer（`store_effect`）は
frame の store を位置の分からない store（`effect_store_location_unmodeled`）として EQ を止める。
`location_relation` は、この証拠が無ければ frame と parameter・global の位置の関係を `UNKNOWN` にする。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Optional, Tuple

from scripts.function_tracer_pcode.core import Expression, ExpressionType

#: 1 つの関数で調べる式の node の上限。超えたら証拠が無い（局所にしない）
_MAX_ESCAPE_NODES = 1 << 16

_CALL_MNEMONICS = frozenset({"CALL", "CALLIND", "CALLOTHER"})

REASON_CALL_MAY_READ_FRAME = "call_may_read_frame"
REASON_FRAME_ADDRESS_ESCAPES = "frame_address_escapes"
REASON_TRACE_FAILED = "frame_escape_trace_failed"
REASON_BUDGET_EXCEEDED = "frame_escape_budget_exceeded"


@dataclass(frozen=True)
class FrameLocality:
    """関数の frame の store を局所と認めてよいか。`reasons` は認めない理由（診断用、registry の理由ではない）。"""

    proven: bool
    reasons: Tuple[str, ...] = ()


class _BudgetExceeded(Exception):
    pass


def _trace_failures():
    from scripts.function_tracer_pcode.core.operand_derivation import OperandDerivationRefused

    return (OperandDerivationRefused, ArithmeticError, LookupError, TypeError, ValueError, AttributeError, RecursionError)


def is_frame_address_term(node) -> bool:
    """`node` が frame の番地の根（SP / frame pointer の register、frame を基底にする位置の ref）か。

    frame pointer は名前だけでは frame ではない（`constant_folding._impl__is_stack_frame_base_expression`）が、
    ここは「外へ出たかもしれない」の判定なので広く取る（広いほど安全）。stack 空間の varnode の値は frame の
    slot の**中身**で、番地ではない。
    """

    from scripts.function_tracer_pcode.analysis.effects._api import _coerce_storage_info
    from scripts.function_tracer_pcode.core.runtime_refs import LocationBaseRef

    runtime_ref = getattr(node, "runtime_ref", None)
    if isinstance(runtime_ref, LocationBaseRef) and runtime_ref.is_stack_frame():
        return True
    storage = _coerce_storage_info(getattr(node, "storage_info", None))
    if storage is None:
        return False
    return bool(storage.is_stack_pointer or storage.is_frame_pointer)


def frame_address_escapes(expr: Optional[Expression], *, budget: Optional[list] = None) -> bool:
    """`expr` の値に frame の番地が（番地として読む位置以外で）入り得るか。

    `MEMORY` の番地の部分木は辿らない（そこでの frame の番地は読み出しの位置で、値は slot の中身）。`budget` は
    残りの node 数を持つ 1 要素の list（呼び出し側で共有する）。尽きたら `_BudgetExceeded`。
    """

    if expr is None:
        return False
    if budget is None:
        budget = [_MAX_ESCAPE_NODES]
    pending = [expr]
    seen = set()
    while pending:
        node = pending.pop()
        if node is None or id(node) in seen:
            continue
        seen.add(id(node))
        budget[0] -= 1
        if budget[0] < 0:
            raise _BudgetExceeded()
        if is_frame_address_term(node):
            return True
        expr_type = getattr(node, "expr_type", None)
        if expr_type == ExpressionType.MEMORY:
            continue
        if expr_type == ExpressionType.PHI:
            for cond, value in list(getattr(node, "value", None) or ()):
                pending.append(value)
                pending.append(getattr(cond, "expression", None) if cond is not None else None)
            continue
        pending.extend(operand for operand in list(getattr(node, "operands", None) or ()) if operand is not None)
    return False


def conditions_mention_frame_address(conditions: Iterable) -> bool:
    """経路の条件に frame の番地が値として現れるか（`p == sp - 16` のような比較）。上限超過は True。"""

    budget = [_MAX_ESCAPE_NODES]
    try:
        return any(
            frame_address_escapes(getattr(cond, "expression", None), budget=budget) for cond in list(conditions or ())
        )
    except _BudgetExceeded:
        return True


def _escape_sinks(op):
    """frame の番地が値として外へ出得る op の入力（呼び出しの引数・store の値・戻り値・分岐の条件）。"""

    mnemonic = op.getMnemonic()
    count = int(op.getNumInputs())
    if mnemonic == "STORE":
        return [op.getInput(2)] if count >= 3 else []
    if mnemonic == "RETURN":
        return [op.getInput(index) for index in range(1, count)]
    if mnemonic == "CBRANCH":
        return [op.getInput(1)] if count >= 2 else []
    return []


def collect_frame_locality(block_infos: Iterable, tracer) -> FrameLocality:
    """関数のすべての block の op から E1 / E2 を調べる（到達しない block も含める: 広いほど安全）。"""

    budget = [_MAX_ESCAPE_NODES]
    try:
        for block_info in list(block_infos or ()):
            for op in list(getattr(block_info, "pcode_ops", None) or ()):
                if op.getMnemonic() in _CALL_MNEMONICS:
                    return FrameLocality(proven=False, reasons=(REASON_CALL_MAY_READ_FRAME,))
                for varnode in _escape_sinks(op):
                    if varnode is None:
                        continue
                    if frame_address_escapes(tracer.trace_varnode(varnode), budget=budget):
                        return FrameLocality(proven=False, reasons=(REASON_FRAME_ADDRESS_ESCAPES,))
    except _BudgetExceeded:
        return FrameLocality(proven=False, reasons=(REASON_BUDGET_EXCEEDED,))
    except _trace_failures():
        return FrameLocality(proven=False, reasons=(REASON_TRACE_FAILED,))
    return FrameLocality(proven=True)
