# -*- coding: utf-8 -*-
"""operand を差し替えた式の派生（Issue #281）。**field と runtime ref の扱いの唯一の owner**。

`Expression.derive_with_operands(operands)` の本体。派生した node は「同じ演算を、同じ program 上の
位置で、別の operand の値に適用したもの」を表す（例: bounded refinement が caller の node の部分木に
callee の戻り値を入れた値）。この契約の下で、node が持つ field と runtime ref を次の 4 通りに分ける。

========================  ==========================================================================
扱い                       対象
========================  ==========================================================================
保つ                       operand に依存しない field（`expr_type`・`opcode`・`operator`・`name`・
                           `size`・`value`・型・`storage_info`・`read_order_key`・
                           `call_argument_width_evidence`）。#281 は `opcode` を落としていた
無効化する                 `_recurrence_semantic_key`（operand の key を含む）。PTRADD / PTRSUB の
                           `AddressValueRef`（operand から計算した値。consumer は ref が無ければ
                           operand から計算し直す。古い ref を残すと古い番地に解決される）
番地が変わらなければ保つ   MEMORY の位置つきの ref（`location` / `snapshot_ref` を持つ
                           `ObservedMemoryReadRef`、`PostStateReadRef`、`PostStateValueRef`、
                           `CanonicalLocation`）。番地が変わったら **拒否**（`None` にすると
                           post-state の読み出しが pre-state の読み出しに化ける）
拒否する                   値の node の `LocationBaseRef`（「この値は parameter / storage / stack /
                           global の基底そのもの」という主張。operand が変われば主張が古く、core では
                           計算し直せない。落とすと location の照合が別の基底に化け、store と読み出しの
                           対応を失い得る）。表に無い ref（loop / readonly の要約など、中身が operand と
                           同じ式）も拒否する
========================  ==========================================================================

位置だけを持つ `ObservedMemoryReadRef`（`order_key` / `pcode_op_ref`）は load の位置なので保つ。

**番地が変わったかは、この module が自分で確かめる**（呼び出し側の申告を受け取らない）。同じ object、
または予算の無い厳密な構造 identity（`exact_structural_identity`。識別できない部分を含めば何とも
等しくならない）が等しいときだけ「変わらない」とする。確かめられなければ変わったとみなす（fail-closed）。
identity の計算は式の lifecycle を進めない（構築中の operand を凍結しない）。

拒否は `OperandDerivationRefused`（理由つき）。呼び出し側は派生をあきらめ、元の式（ref と operand が
producer の作ったとおりに整合している値）を使う。拒否した派生の一部だけを捨ててはいけない（他の候補だけが
残ると、到達可能な値が黙って消える）。
"""

from __future__ import annotations

from typing import Any, Callable, Dict, Sequence

from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.intrinsics import PTRADD_OPCODE, PTRSUB_OPCODE
from scripts.function_tracer_pcode.core.runtime_refs import (
    AddressValueRef,
    CanonicalLocation,
    LocationBaseRef,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateValueRef,
)


class OperandDerivationRefused(Exception):
    """operand を差し替えると、node の runtime ref を正しく保てない（Issue #281）。

    `TypeError` / `ValueError` の派生にしないのは、「回復可能」な例外 tuple に吸収されて
    派生した値が黙って使われるのを防ぐため。呼び出し側はこの型だけを捕まえて、元の式に戻る。
    """

    def __init__(self, reason: str, *, expr_type: str, ref_type: str) -> None:
        super().__init__(f"{reason} (expr_type={expr_type}, runtime_ref={ref_type})")
        self.reason = reason
        self.expr_type = expr_type
        self.ref_type = ref_type


#: 拒否の理由（計測と test が参照する語彙）
REFUSED_ADDRESS_CHANGED = "located_memory_ref_address_changed"
REFUSED_OPERAND_DEPENDENT_REF = "operand_dependent_runtime_ref"


def _same_operand(old: Expression, new: Expression) -> bool:
    """`new` が `old` と同じ値か（同じ object、または予算の無い厳密な構造 identity が等しい）。"""

    if new is old:
        return True
    from scripts.function_tracer_pcode.core.structural import exact_structural_identity

    return exact_structural_identity(old) == exact_structural_identity(new)


def _observed_read_is_located(ref: ObservedMemoryReadRef) -> bool:
    return ref.location is not None or ref.snapshot_ref is not None


# --- runtime ref の扱い ----------------------------------------------------------------------------
#
# 各 handler は (元の式, 新しい operand) を受け取り、派生した式に付ける ref を返すか、拒否する。
# 表に無い型の ref は拒否する（`_refuse_operand_dependent`）。ref の型は exact type で引く
# （subclass は別の意味を持ち得る）。

_KEEP = object()


def _keep(expr: Expression, operands: Sequence[Expression]) -> Any:
    return _KEEP


def _address_value(expr: Expression, operands: Sequence[Expression]) -> Any:
    # PTRADD / PTRSUB の見分け方は consumer（`_resolve_concrete_address_offset`）と同じ: opcode か名前
    if expr.expr_type is ExpressionType.INTRINSIC and (
        getattr(expr, "opcode", None) in (PTRADD_OPCODE, PTRSUB_OPCODE) or expr.name in ("PTRADD", "PTRSUB")
    ):
        return None
    return _refuse_operand_dependent(expr, operands)


def _bound_to_address(expr: Expression, operands: Sequence[Expression]) -> Any:
    if expr.expr_type is not ExpressionType.MEMORY or len(operands) != 1 or len(expr.operands) != 1:
        return _refuse_operand_dependent(expr, operands)
    if _same_operand(expr.operands[0], operands[0]):
        return _KEEP
    raise OperandDerivationRefused(
        REFUSED_ADDRESS_CHANGED,
        expr_type=expr.expr_type.name,
        ref_type=type(expr.runtime_ref).__name__,
    )


def _observed_read(expr: Expression, operands: Sequence[Expression]) -> Any:
    if _observed_read_is_located(expr.runtime_ref):
        return _bound_to_address(expr, operands)
    if expr.expr_type is not ExpressionType.MEMORY:
        return _refuse_operand_dependent(expr, operands)
    # load の位置（order_key / pcode_op_ref）だけの ref: 同じ load の別の番地の値として保つ
    return _KEEP


def _refuse_operand_dependent(expr: Expression, operands: Sequence[Expression]) -> Any:
    raise OperandDerivationRefused(
        REFUSED_OPERAND_DEPENDENT_REF,
        expr_type=getattr(expr.expr_type, "name", str(expr.expr_type)),
        ref_type=type(expr.runtime_ref).__name__,
    )


RUNTIME_REF_POLICY: Dict[type, Callable[[Expression, Sequence[Expression]], Any]] = {
    type(None): _keep,
    AddressValueRef: _address_value,
    ObservedMemoryReadRef: _observed_read,
    PostStateReadRef: _bound_to_address,
    PostStateValueRef: _bound_to_address,
    CanonicalLocation: _bound_to_address,
    LocationBaseRef: _refuse_operand_dependent,
}


def derive_with_operands(expr: Expression, operands: Sequence[Expression]) -> Expression:
    """`expr` の operand を `operands` にした派生を返す（扱いは module の docstring の表）。

    operand がすべて同じ object なら `expr` 自身を返す（派生は要らない）。operand の数は変えられない
    （変えるのは別の演算を作ることで、この API の対象ではない）。
    """

    new_operands = list(operands)
    old_operands = list(expr.operands or ())
    if len(new_operands) != len(old_operands):
        raise ValueError(
            f"derive_with_operands keeps the arity: {len(old_operands)} operands, got {len(new_operands)}"
        )
    if all(new is old for new, old in zip(new_operands, old_operands)):
        return expr
    if expr.expr_type is ExpressionType.PHI:
        # PHI の子は operand ではなく value の枝（`Expression.phi` で作り直す）
        raise ValueError("derive_with_operands does not rebuild PHI branches")

    runtime_ref = getattr(expr, "runtime_ref", None)
    handler = RUNTIME_REF_POLICY.get(type(runtime_ref), _refuse_operand_dependent)
    decided = handler(expr, new_operands)
    derived_ref = runtime_ref if decided is _KEEP else decided
    return Expression(
        expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=new_operands,
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
        runtime_ref=derived_ref,
        opcode=getattr(expr, "opcode", None),
        call_argument_width_evidence=getattr(expr, "call_argument_width_evidence", None),
        # `_recurrence_semantic_key` は operand の key を含むので持ち越さない
    )
