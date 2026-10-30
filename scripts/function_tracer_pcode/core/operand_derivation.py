# -*- coding: utf-8 -*-
"""operand を差し替えた式の派生（Issue #281）。**field と runtime ref の扱いの唯一の owner**。

`Expression.derive_with_operands(operands)` の本体。派生した node は「同じ演算を、同じ program 上の
位置で、別の operand の値に適用したもの」を表す（例: bounded refinement が caller の node の部分木に
callee の戻り値を入れた値）。この契約の下で、node が持つ field と runtime ref を次の 4 通りに分ける。

========================  ==========================================================================
扱い                       対象
========================  ==========================================================================
保つ                       operand に依存しない field（`expr_type`・`opcode`・`operator`・`name`・
                           `size`・`value`・型・`read_order_key`・`call_argument_width_evidence`）。
                           #281 は `opcode` を落としていた
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
                           同じ式）も拒否する。operand を持つ node の `storage_info`（「この値はこの
                           register / stack に在る」という主張。tracer は引数の幅の adapter に
                           `LocationBaseRef` と一緒に付ける）も同じ理由で拒否する:
                           `_address_root_is_stack_frame` は途中の node の `storage_info` を読み、
                           stack と言われれば store を観測不能とする
========================  ==========================================================================

位置だけを持つ `ObservedMemoryReadRef`（`order_key` / `pcode_op_ref`）は load の位置なので保つ。consumer は
`order_key` を effect との順序と「観測した load」の印にだけ使い、`pcode_op_ref` から番地・location を
導く consumer は無い（Issue #281 の review で production の読み手を棚卸しした）。番地は operand から読まれる。

**番地が変わったかは、この module が自分で確かめる**（呼び出し側の申告を受け取らない）。「変わらない」は
**新しい番地の operand が元の operand と同じ object** のときだけで、そのとき MEMORY（operand は番地 1 つ）は
派生せず元の式そのものを返す。それ以外は変わったとみなす（fail-closed）。

構造の比較（`exact_structural_identity` など）を使わない理由: 番地を読む consumer は、番地の部分木の
node の field のうち構造 key が見ないものを読む。VARIABLE / CONSTANT / PTRADD の `AddressValueRef`
（`_resolve_concrete_address_offset` は ref を operand より先に読む。VARIABLE は ref だけが番地の値）、
PARAMETER / VARIABLE / 値の node の `LocationBaseRef` と `storage_info`（基底と stack の判定）、
入れ子の MEMORY の ref などで、既定の構造 key はこれらを持たない（Issue #281 の review: 同名の
VARIABLE に `AddressValueRef(0x1000)` / `(0x2000)` が付いても等しい）。consumer が読む field を全部
並べた identity は、consumer が増えるたびに足し忘れ得る。

同じ object なら十分である理由: 使われる node の (ref, 番地の operand) の組は元の node の組と object
として同じなので、その組から何を読む consumer も元の node と同じ答えを得る（ref は Expression を
持たない frozen な値: `core/runtime_refs/locations.py`）。operand が構築中で後から書き換わっても、
元と派生は同じ object を共有するので、派生が元より食い違うことは無い。費用: 番地を作り直したが値は
同じ、という派生は拒否になる（元の式に戻るので意味は失わない）。V281 の probe で数える。

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
REFUSED_OPERAND_DEPENDENT_STORAGE = "operand_dependent_storage_info"


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
    # MEMORY の operand は番地 1 つなので、ここへ来たときは番地が同じ object ではない（同じなら
    # `derive_with_operands` が元の式を返す）。同じ object 以外を「同じ番地」としない理由は module の docstring
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

    if getattr(expr, "storage_info", None) is not None:
        # ここへ来るのは operand のどれかが変わったとき（同じなら上で自分を返す）
        raise OperandDerivationRefused(
            REFUSED_OPERAND_DEPENDENT_STORAGE,
            expr_type=expr.expr_type.name,
            ref_type=type(getattr(expr, "runtime_ref", None)).__name__,
        )
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
        read_order_key=expr.read_order_key,
        runtime_ref=derived_ref,
        opcode=getattr(expr, "opcode", None),
        call_argument_width_evidence=getattr(expr, "call_argument_width_evidence", None),
        # `_recurrence_semantic_key` は operand の key を含むので持ち越さない
    )
