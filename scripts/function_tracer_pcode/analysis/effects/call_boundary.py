# -*- coding: utf-8 -*-
"""callee の式を caller の時間軸へ移す境界（Issue #281）。**関数をまたぐ memory 読み出しの扱いの唯一の owner**。

callee の解析が作った式の memory 読み出しは、**callee の時間軸**の上の読み出しである:

* `read_order_key` / `ObservedMemoryReadRef.order_key` は callee の P-code op の順序（callee の op の
  `SequenceNumber.getOrder()`）。
* 順序を持たない読み出しは、読む consumer の文脈で時点が決まる（戻り値の文脈では effect の書き換えが
  callee の全 effect の後と読み、effect の値の文脈ではその effect の前と読む）。
* `location` / `CanonicalLocation` は callee の parameter を基底にした位置、`snapshot_ref` /
  `PostStateReadRef` / `PostStateValueRef` は callee の effect の後の状態。

caller の consumer はこれらを **caller の** effect・順序と比べる。そのまま渡すと、callee の順序の番号を
caller の effect の順序と比べてしまう（Issue #281 の review: callee が `*p` を読み、caller が呼び出しの後で
`*p = 2` とすると、読み出しが `2` に化け得る）。operand が変わらない置き換え・引数で特殊化済みの callee
（置き換えが空）でも同じなので、派生（`derive_with_operands`）ではなく、callee の結果が caller へ入る
境界で扱う。

**移す規則**: callee の読み出しは、**その時点より前に callee の書き込みが無い** と言えるときだけ、
「caller の呼び出し位置での読み出し」に置き換える。そのとき読み出しの値は callee の入口の値、つまり
caller の呼び出し位置の memory の値に等しい。順序は caller の呼び出しの op の読み出しの順序
（caller 自身の読み出しと同じ単位: `read_order_key_for_op`）にし、callee の位置（`location`）は落とす
（番地の operand から caller の parameter で計算し直される）。caller の consumer は、caller 自身が呼び出しの
位置で読んだのと同じ扱いをする。

「前に callee の書き込みが無い」の判定:

* callee の effect 要約が完全（`has_unsupported_call` が無く `incomplete_reasons` が空）でなければ、書き込みは
  分からない → 拒否。
* 読み出しの順序は effect の順序と比べない。読み出しの順序（op の `getOrder()`）と effect の順序
  （`(番地 << 8) | getOrder()`）は単位が違い、比べられない（関数の中の問題として別 Issue）。比べるのは
  effect どうしの順序だけ:
  - 戻り値・条件・deferred call の引数の文脈: callee に effect が 1 つでもあれば拒否。
  - effect `e` の値・条件の文脈: `e` より前（順序が不明な effect を含む）の effect があれば拒否。値は `e` の
    書き込みの前に読まれているので、`e` より前に書き込みが無ければ callee の入口の値。
* callee の stack frame の読み出しは拒否（effect 要約は frame の書き込みを数えない。caller の memory でもない）。
* callee の書き込みの後の状態（`snapshot_ref` / `PostStateReadRef` / `PostStateValueRef`）は、callee の effect を
  持ち込まないと caller の言葉で表せない → 拒否。表に無い ref も拒否。

effect の値・条件の文脈で順序を持たない読み出しは順序を付けない（caller へ入る effect の順序が呼び出しの
位置になり、consumer は値をその effect の前と読むので、時点はそのまま移る）。位置だけを落とす。

拒否は `CallBoundaryRefused`（`OperandDerivationRefused` の派生）。呼び出し側は、置き換えの拒否と同じ境界で
扱う: 呼び出しの展開をまるごとやめるか、その呼び出しの effect をまるごと「分からない呼び出し」にする。
callee の元の式を caller へ渡してはいけない。

限界（未確認のもの）: callee の frame の書き込みを effect 要約が持たないことに依存して frame の読み出しを
拒否している。frame 以外の callee 局所の記憶域（`unresolved` の番地）は caller の memory として読む。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateValueRef,
)
from scripts.function_tracer_pcode.core.operand_derivation import OperandDerivationRefused

REFUSED_CALLEE_EFFECTS_UNKNOWN = "callee_effects_unknown"
REFUSED_CALLEE_WRITE_MAY_PRECEDE_READ = "callee_write_may_precede_read"
REFUSED_CALLEE_STATE_READ = "callee_post_write_state_read"
REFUSED_CALLEE_FRAME_READ = "callee_frame_read"
REFUSED_CALL_SITE_ORDER_UNKNOWN = "call_site_order_unknown"
REFUSED_UNKNOWN_MEMORY_REF = "callee_memory_ref_unsupported"

#: 順序が分からない effect（`_UNKNOWN_EFFECT_ORDER_KEY`）。どの読み出しより前にあり得るとみなす
_UNKNOWN_EFFECT_ORDER = -1


class CallBoundaryRefused(OperandDerivationRefused):
    """callee の式の memory 読み出しを、caller の時間軸へ正しく移せない（Issue #281）。"""


def read_order_key_for_op(pcode_op) -> Optional[int]:
    """op の読み出しの順序（`read_order_key`）。tracer が LOAD に付ける値と同じ規則の唯一の実装。"""

    if pcode_op is None:
        return None
    seqnum = getattr(pcode_op, "getSeqnum", lambda: None)()
    if seqnum is not None:
        order = _coerce_order(getattr(seqnum, "getOrder", lambda: None)())
        if order is not None:
            return order
    return _coerce_order(getattr(pcode_op, "getOrder", lambda: None)())


def _coerce_order(value) -> Optional[int]:
    if value is None:
        return None
    try:
        return int(value)
    except (TypeError, ValueError):
        return None


@dataclass(frozen=True)
class CallSite:
    """caller の中の呼び出しの位置。`read_order_key` は caller の読み出しと同じ単位（不明なら None）。"""

    read_order_key: Optional[int]

    @classmethod
    def for_op(cls, pcode_op) -> "CallSite":
        return cls(read_order_key_for_op(pcode_op))

    @classmethod
    def for_deferred_call(cls, deferred_call_ref, caller_entry_offset: Optional[int]) -> "CallSite":
        """deferred call の位置。caller 自身の op のときだけ順序を使う。

        callee の展開から caller へ合流した deferred call は、op が callee のもの（順序は callee の時間軸）。
        その位置は caller の時間軸では外側の呼び出しの位置だが、ここからは分からないので不明にする。
        """

        if deferred_call_ref is None or caller_entry_offset is None:
            return cls(None)
        if getattr(deferred_call_ref, "caller_entry_offset", None) != caller_entry_offset:
            return cls(None)
        op_ref = getattr(deferred_call_ref, "pcode_op_ref", None)
        return cls(_coerce_order(getattr(op_ref, "seq_order", None)))


@dataclass(frozen=True)
class CalleeTimeline:
    """callee の書き込みの順序。`effect_orders` が None なら書き込みが分からない。"""

    effect_orders: Optional[Tuple[int, ...]]
    parameters: Tuple[Dict, ...] = ()

    @classmethod
    def from_effect_summary(cls, summary, parameters: Optional[Sequence[Dict]] = None) -> "CalleeTimeline":
        params = tuple(parameters or ())
        if summary is None or getattr(summary, "has_unsupported_call", False):
            return cls(None, params)
        reasons = getattr(summary, "incomplete_reasons", ()) or ()
        if reasons:
            return cls(None, params)
        orders = []
        for effect in getattr(summary, "effects", None) or ():
            order = _coerce_order(getattr(effect, "order_key", None))
            orders.append(_UNKNOWN_EFFECT_ORDER if order is None else order)
        return cls(tuple(orders), params)

    @classmethod
    def unknown(cls, parameters: Optional[Sequence[Dict]] = None) -> "CalleeTimeline":
        return cls(None, tuple(parameters or ()))

    def write_may_precede(self, context_order: Optional[int]) -> bool:
        """文脈の時点（None = callee の出口）より前に書き込みがあり得るか。"""

        if self.effect_orders is None:
            return True
        if context_order is None:
            return bool(self.effect_orders)
        return any(order == _UNKNOWN_EFFECT_ORDER or order < context_order for order in self.effect_orders)


def import_callee_expression(
    expr: Optional[Expression],
    site: CallSite,
    timeline: CalleeTimeline,
    *,
    context_order: Optional[int] = None,
) -> Optional[Expression]:
    """callee の式を caller の時間軸へ移す。`context_order` は effect の値の文脈ならその effect の順序。"""

    if expr is None:
        return None
    return _Importer(site, timeline, context_order).expression(expr)


def import_callee_condition(
    condition: Optional[Condition],
    site: CallSite,
    timeline: CalleeTimeline,
    *,
    context_order: Optional[int] = None,
) -> Optional[Condition]:
    if condition is None:
        return None
    return _Importer(site, timeline, context_order).condition(condition)


class _Importer:
    def __init__(self, site: CallSite, timeline: CalleeTimeline, context_order: Optional[int]) -> None:
        self.site = site
        self.timeline = timeline
        self.context_order = context_order
        self._memo: Dict[int, Expression] = {}

    def condition(self, condition: Condition) -> Condition:
        imported = self.expression(condition.expression)
        if imported is condition.expression:
            return condition
        return Condition(imported, condition.negated)

    def expression(self, expr: Expression) -> Expression:
        cached = self._memo.get(id(expr))
        if cached is not None:
            return cached
        result = self._import(expr)
        self._memo[id(expr)] = result
        return result

    def _import(self, expr: Expression) -> Expression:
        if expr.expr_type == ExpressionType.MEMORY and expr.operands:
            return self._memory(expr)
        if expr.expr_type == ExpressionType.PHI and expr.value:
            branches = []
            changed = False
            for cond, value in expr.value:
                new_cond = self.condition(cond) if cond is not None else None
                new_value = self.expression(value)
                branches.append((new_cond, new_value))
                changed = changed or new_cond is not cond or new_value is not value
            if not changed:
                return expr
            rebuilt = Expression.phi(branches)
            rebuilt.size = expr.size
            return rebuilt
        operands = list(expr.operands or ())
        if not operands:
            return expr
        new_operands = [self.expression(operand) for operand in operands]
        if all(new is old for new, old in zip(new_operands, operands)):
            return expr
        return expr.derive_with_operands(new_operands)

    def _memory(self, expr: Expression) -> Expression:
        ref = getattr(expr, "runtime_ref", None)
        if isinstance(ref, (PostStateReadRef, PostStateValueRef)) or (
            isinstance(ref, ObservedMemoryReadRef) and ref.snapshot_ref is not None
        ):
            raise CallBoundaryRefused(REFUSED_CALLEE_STATE_READ, expr_type="MEMORY", ref_type=type(ref).__name__)
        if ref is not None and not isinstance(ref, (ObservedMemoryReadRef, CanonicalLocation)):
            raise CallBoundaryRefused(REFUSED_UNKNOWN_MEMORY_REF, expr_type="MEMORY", ref_type=type(ref).__name__)
        if self.timeline.effect_orders is None:
            raise CallBoundaryRefused(REFUSED_CALLEE_EFFECTS_UNKNOWN, expr_type="MEMORY", ref_type=type(ref).__name__)
        if self.timeline.write_may_precede(self.context_order):
            raise CallBoundaryRefused(REFUSED_CALLEE_WRITE_MAY_PRECEDE_READ, expr_type="MEMORY", ref_type=type(ref).__name__)
        if self._reads_callee_frame(expr):
            raise CallBoundaryRefused(REFUSED_CALLEE_FRAME_READ, expr_type="MEMORY", ref_type=type(ref).__name__)

        address = expr.operands[0]
        new_address = self.expression(address)
        timed = expr.read_order_key is not None or (
            isinstance(ref, ObservedMemoryReadRef) and ref.order_key is not None
        )
        if timed or self.context_order is None:
            # 戻り値の文脈の読み出し・順序つきの読み出しは、caller の呼び出し位置の読み出しにする
            if self.site.read_order_key is None:
                raise CallBoundaryRefused(REFUSED_CALL_SITE_ORDER_UNKNOWN, expr_type="MEMORY", ref_type=type(ref).__name__)
            order = self.site.read_order_key
            moved = expr.derive_with(
                read_order_key=order,
                runtime_ref=ObservedMemoryReadRef(
                    order_key=order,
                    pcode_op_ref=ref.pcode_op_ref if isinstance(ref, ObservedMemoryReadRef) else None,
                    source=ref.source if isinstance(ref, ObservedMemoryReadRef) else "call_site_read",
                ),
            )
        elif ref is None or (isinstance(ref, ObservedMemoryReadRef) and ref.location is None):
            moved = expr
        else:
            # effect の値の文脈の順序なしの読み出し: 時点はそのまま移る。callee の位置だけを落とす
            moved = expr.derive_with(
                runtime_ref=(
                    ObservedMemoryReadRef(
                        order_key=ref.order_key,
                        pcode_op_ref=ref.pcode_op_ref,
                        source=ref.source,
                    )
                    if isinstance(ref, ObservedMemoryReadRef)
                    else None
                ),
            )
        if new_address is address:
            return moved
        return moved.derive_with_operands([new_address])

    def _reads_callee_frame(self, expr: Expression) -> bool:
        from scripts.function_tracer_pcode.analysis.effects.location import _impl_classify_store_address as classify_store_address

        kind, _location = classify_store_address(expr.operands[0], list(self.timeline.parameters), size=expr.size)
        return kind == "stack_frame"
