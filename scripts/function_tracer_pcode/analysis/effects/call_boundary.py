# -*- coding: utf-8 -*-
"""callee の式を caller の時間軸へ移す境界（Issue #281）。**関数をまたぐ memory 読み出しの扱いの唯一の owner**。

callee の解析が作った式の memory 読み出しは、**callee の時間軸**の上の読み出しである:

* `read_order_key` / `ObservedMemoryReadRef.order_key` は callee の program point の key（callee の
  `core.program_order`。callee の effect の `order_key` と同じ key で比べられる）。
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
caller の呼び出し位置の memory の値に等しい。順序は caller の呼び出しの op の key（`CallSite`。caller 自身の
読み出し・effect と同じ `core.program_order` の key）にし、callee の位置（`location`）は落とす
（番地の operand から caller の parameter で計算し直される）。caller の consumer は、caller 自身が呼び出しの
位置で読んだのと同じ扱いをする。呼び出しで caller へ入る callee の effect の key も呼び出しの位置なので、
移した読み出し（`effect.order_key >= 読み出しの key` を除く）はそれらを見ない。

「前に callee の書き込みが無い」の判定（`CalleeTimeline.write_may_precede`）:

* callee の effect 要約が完全（`has_unsupported_call` が無く `incomplete_reasons` が空）でなければ、書き込みは
  分からない → 拒否。loop の中の書き込みは effect 要約が不完全にする（key で前後を表せない）。
* 順序つきの読み出し: その key より前（順序が不明な effect を含む）の callee の effect があれば拒否。key は
  callee の CFG の線形拡大なので、key が後の effect はどの実行でも読み出しより前に実行されない。
* 順序の無い読み出し: 文脈の時点で決める。
  - 戻り値・条件・deferred call の引数の文脈（時点は callee の出口）: callee に effect が 1 つでもあれば拒否。
  - effect `e` の値・条件の文脈: `e` より前の effect があれば拒否。値は `e` の書き込みの前に読まれているので、
    `e` より前に書き込みが無ければ callee の入口の値。
* callee の stack frame の読み出しは拒否（effect 要約は frame の書き込みを数えない。caller の memory でもない）。
* callee の書き込みの後の状態（`snapshot_ref` / `PostStateReadRef` / `PostStateValueRef`）の読み出しは、callee の
  effect を持ち込まないと caller の言葉で表せない → 拒否。表に無い ref も拒否。

effect の値・条件の文脈で順序を持たない読み出しは順序を付けない（caller へ入る effect の順序が呼び出しの
位置になり、consumer は値をその effect の前と読むので、時点はそのまま移る）。位置だけを落とす。

**値の node（MEMORY 以外）の ref**: VARIABLE・定数・複合式・PHI にも callee の時点・位置の主張が付く
（`PostStateValueRef`「この値は callee の出口の状態の location の値と等しい」、`poststate_*` の変数の
`PostStateReadRef` / `CanonicalLocation`、callee の基底の `LocationBaseRef`、callee の stack の `storage_info`）。
caller の consumer はこれらを caller の出口の状態・caller の基底と読むので、表（`_value_ref_is_callee_claim`）で
落とすか拒否する（review 4: callee が `*p = 5` の後に返す 5 が、caller が `q` を渡して呼んだ後の `*p = 9` の
9 に化けた）。値の同一性だけの ref（`CALLEE_VALUE_REFS_KEPT`）は保つ。

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
    LocationBaseRef,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateValueRef,
)
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.operand_derivation import OperandDerivationRefused
from scripts.function_tracer_pcode.core.runtime_refs import (
    AbiArgumentSlotRef,
    AddressValueRef,
    CallModelCandidateRef,
    DeferredCallRef,
    FreshCallArgumentRef,
    UnknownValueRef,
)

REFUSED_CALLEE_EFFECTS_UNKNOWN = "callee_effects_unknown"
REFUSED_CALLEE_WRITE_MAY_PRECEDE_READ = "callee_write_may_precede_read"
REFUSED_CALLEE_STATE_READ = "callee_post_write_state_read"
REFUSED_CALLEE_FRAME_READ = "callee_frame_read"
REFUSED_CALL_SITE_ORDER_UNKNOWN = "call_site_order_unknown"
REFUSED_UNKNOWN_MEMORY_REF = "callee_memory_ref_unsupported"
REFUSED_CALLEE_PLACE = "callee_place_claim"
REFUSED_CALLEE_SUMMARY_REF = "callee_summary_ref_unsupported"

#: 値の node に付いたまま caller へ持ち込める ref（値の同一性だけを表し、callee の時点・位置を持たない）。
#: exact type で引く（subclass は別の意味を持ち得る）。ここに無い ref は `_value_ref_is_callee_claim` の表
CALLEE_VALUE_REFS_KEPT = frozenset(
    {
        AddressValueRef,
        CallTargetRef,
        CallModelCandidateRef,
        UnknownValueRef,
        DeferredCallRef,
        AbiArgumentSlotRef,
        FreshCallArgumentRef,
    }
)

#: 順序が分からない effect（`_UNKNOWN_EFFECT_ORDER_KEY`）。どの読み出しより前にあり得るとみなす
_UNKNOWN_EFFECT_ORDER = -1


class CallBoundaryRefused(OperandDerivationRefused):
    """callee の式の memory 読み出しを、caller の時間軸へ正しく移せない（Issue #281）。"""


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
    def for_deferred_call(cls, deferred_call, caller_entry_offset: Optional[int]) -> "CallSite":
        """deferred call（`DeferredCallInfo`）の位置。caller 自身の op のときだけ、記録した key を使う。

        key は deferred call を記録したときに caller の `ProgramOrder` で作った値（`call_site_order_key`）。
        callee の展開から caller へ合流した deferred call は、op が callee のもの（key は callee の時間軸）。
        その位置は caller の時間軸では外側の呼び出しの位置だが、ここからは分からないので不明にする。
        """

        deferred_call_ref = getattr(deferred_call, "deferred_call_ref", None)
        if deferred_call_ref is None or caller_entry_offset is None:
            return cls(None)
        if getattr(deferred_call_ref, "caller_entry_offset", None) != caller_entry_offset:
            return cls(None)
        return cls(_coerce_order(getattr(deferred_call, "call_site_order_key", None)))


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
        # 値の node（MEMORY 以外）の ref を、子より先に決める（拒否なら子を辿る費用も要らない）
        drop_ref = self._value_ref_is_callee_claim(expr)
        if expr.expr_type == ExpressionType.PHI and expr.value:
            branches = []
            changed = False
            for cond, value in expr.value:
                new_cond = self.condition(cond) if cond is not None else None
                new_value = self.expression(value)
                branches.append((new_cond, new_value))
                changed = changed or new_cond is not cond or new_value is not value
            if not changed and not drop_ref:
                return expr
            if not drop_ref and getattr(expr, "runtime_ref", None) is not None:
                # 枝を作り直した PHI に元の ref を写すと、ref が新しい枝と食い違い得る（写しの owner は
                # `core.operand_derivation` で、PHI の枝は扱わない）。持ち込めないので拒否する
                raise CallBoundaryRefused(
                    REFUSED_CALLEE_SUMMARY_REF, expr_type=expr.expr_type.name, ref_type=type(expr.runtime_ref).__name__
                )
            rebuilt = Expression.phi(branches)
            rebuilt.size = expr.size
            return rebuilt
        # 落とす主張は operand の派生より先に落とす（派生は位置つきの ref を持つ値の node を拒否する）
        base = expr.derive_with(runtime_ref=None) if drop_ref else expr
        operands = list(base.operands or ())
        new_operands = [self.expression(operand) for operand in operands]
        if all(new is old for new, old in zip(new_operands, operands)):
            return base
        return base.derive_with_operands(new_operands)

    def _value_ref_is_callee_claim(self, expr: Expression) -> bool:
        """値の node の ref を caller へ持ち込めるか。持ち込めない主張なら True（落とす）、表せなければ拒否。

        ================================  ===========================================================
        ref                               扱い
        ================================  ===========================================================
        無し・値の同一性だけの ref         保つ（`CALLEE_VALUE_REFS_KEPT`: 番地の定数、呼び出し先、
                                          UNKNOWN の出自。callee の時点・位置を持たない）
        `PostStateValueRef`               **落とす**。「この値は callee の出口の状態の location の値と
                                          等しい」という主張で、caller の consumer は caller の出口の
                                          状態と読む（review: callee が `*p = 5` の後に返す 5 が、caller
                                          の `*p = 9` の後の 9 に化けた）。値そのもの（operand）は
                                          callee の入口の値で表されていて、境界を通って移る
        `PostStateReadRef` /              拒否。値が callee の出口の状態の読み出しそのもの
        `CanonicalLocation`               （`poststate_*` の変数）で、caller の言葉に無い
        `ObservedMemoryReadRef`           拒否（読み出しの ref が MEMORY 以外に付く形は知らない）
        `LocationBaseRef`                 global の基底は保つ。parameter の基底は PARAMETER の node だけ
                                          保つ（境界の後の置き換えが caller の引数にする）。それ以外
                                          （callee の stack / register の基底、parameter の基底を主張する
                                          値の node）は拒否: caller の consumer は caller の基底と読む
        その他（loop / readonly の要約など） 拒否。中に callee の式（callee の読み出し・parameter）を
                                          持ち、境界はその中を書き換えられない
        ================================  ===========================================================

        `storage_info` が callee の stack を指す node も拒否（`_address_root_is_stack_frame` は caller の
        stack と読む）。
        """

        storage = getattr(expr, "storage_info", None)
        if storage is not None and getattr(storage, "is_stack_pointer", False):
            raise CallBoundaryRefused(
                REFUSED_CALLEE_PLACE, expr_type=expr.expr_type.name, ref_type="storage_info"
            )
        ref = getattr(expr, "runtime_ref", None)
        kind = type(ref)
        if ref is None or kind in CALLEE_VALUE_REFS_KEPT:
            return False
        if kind is PostStateValueRef:
            return True
        if kind in (PostStateReadRef, CanonicalLocation):
            raise CallBoundaryRefused(REFUSED_CALLEE_STATE_READ, expr_type=expr.expr_type.name, ref_type=kind.__name__)
        if kind is LocationBaseRef:
            base_kind = str(getattr(ref, "kind", "") or "")
            if base_kind == "global":
                return False
            if base_kind == "parameter" and expr.expr_type == ExpressionType.PARAMETER:
                return False
            raise CallBoundaryRefused(REFUSED_CALLEE_PLACE, expr_type=expr.expr_type.name, ref_type=kind.__name__)
        if kind is ObservedMemoryReadRef:
            raise CallBoundaryRefused(REFUSED_UNKNOWN_MEMORY_REF, expr_type=expr.expr_type.name, ref_type=kind.__name__)
        raise CallBoundaryRefused(REFUSED_CALLEE_SUMMARY_REF, expr_type=expr.expr_type.name, ref_type=kind.__name__)

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
        read_order = expr.read_order_key
        if read_order is None and isinstance(ref, ObservedMemoryReadRef):
            read_order = ref.order_key
        # 順序つきの読み出しは自分の point より前の書き込みだけを見る（callee の effect と同じ key: Issue #285）。
        # 順序の無い読み出しは文脈の時点（戻り値なら callee の出口、effect の値ならその effect の前）
        if self.timeline.write_may_precede(read_order if read_order is not None else self.context_order):
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
