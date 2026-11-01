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
位置で読んだのと同じ扱いをする。呼び出しで caller へ入る callee の effect は、呼び出しの op の key の中の
slot（`CallSite.effect_key`、callee の順）を持つので、移した読み出し（key は呼び出しの key）より後になり、
その読み出しはそれらを見ない（`effect.order_key >= 読み出しの key` を除く）。

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

**parameter の置き換え（review 5）**: 境界は同じ走査で callee の parameter を caller の引数へ置き換える
（`CalleeBinding`）。順序は (1) 値の node の ref の表、(2) parameter の置き換え、(3) 記憶域。post-state の
読み出しは parameter の key を持ち得る（`*param_1` の post-state は param_1 の基底）ので、(1) を先に見る。
置き換えた値は caller の値なので、境界の規則を当てない。置き換えの無い parameter を指す node（引数が足りない・
幅を合わせられない）は `callee_parameter_unbound` で拒否する。callee の解析へ束縛してよいのは文脈を持たない値
（定数: `is_context_free_value`）だけで、束縛済みの callee も同じく全 parameter を置き換える（束縛済みの
parameter には同じ定数が入る）。以前は caller の parameter・読み出し・frame の番地も callee の解析へ束縛し、
束縛が 1 つでもある解析を「特殊化済み」として置き換えを飛ばしていた: caller の値が callee の時間軸・frame と
比べられ、引数の無い callee の parameter が caller の同じ番号の parameter として残り得た。
置き換えるのは callee の parameter の入口の値を表す `PARAMETER` の node だけで、所有者・index・記憶域が
callee の parameter のただ 1 つと合うときだけ（`CalleeBinding.resolve`。review 6: 所有者の違う同じ index、
同じ記憶域にある別の値・post-state の確定値が引数に化けた）。

**記憶域**: `storage_info` が frame を指す node（`StorageInfo.claims_frame`: stack / frame pointer の
register、stack 空間）と、register を指す `PARAMETER` 以外の node（callee のある時点の register の値）は
拒否する。callee の stack / register で渡る parameter は (2) で caller の引数になっている。

**memo**: `CalleeImporter` は共有の部分木の変換を 1 回にする memo を持つ。memo は元の node を生かしておき
（id の再利用で別の node に古い結果を返さない）、呼び出しをまたいで持つのは凍結済みの node だけ（review 6）。

**入れ子の呼び出し**: callee の式の中の deferred call（callee の引数・時間軸の上にある）は、callee の文脈で
展開してから結果をまるごと境界へ通す（`bounded_refinement`）。境界を通した後に callee の文脈で展開すると、
入れ子の結果が境界を通らずに caller へ入る。

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
from scripts.function_tracer_pcode.core.program_order import call_effect_key
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
REFUSED_CALLEE_PARAMETER_UNBOUND = "callee_parameter_unbound"
REFUSED_CALLEE_EFFECT_ORDER = "callee_effect_order_unavailable"
REFUSED_CALLEE_FOREIGN_PARAMETER = "callee_foreign_parameter"
REFUSED_CALLEE_PARAMETER_IDENTITY = "callee_parameter_identity_mismatch"
REFUSED_CALLEE_REGISTER_VALUE = "callee_register_value"

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

    def effect_key(self, slot: Optional[int]) -> Optional[int]:
        """呼び出しの中で `slot` 番目に起きる callee の書き込みの、caller の key（`core.program_order`）。"""

        if slot is None:
            return None
        return call_effect_key(self.read_order_key, slot)


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

    def effect_slots(self) -> Optional[Dict[int, int]]:
        """callee の書き込みの key → 呼び出しの中の slot（1 から、key の順。同じ key は同じ slot）。

        書き込みが分からない・順序の分からない書き込みがあれば None（caller の key を付けられない）。
        key は callee の CFG の線形拡大なので、順位を付け直しても callee の中の前後は保たれる。
        """

        if self.effect_orders is None or any(order == _UNKNOWN_EFFECT_ORDER for order in self.effect_orders):
            return None
        return {order: slot for slot, order in enumerate(sorted(set(self.effect_orders)), start=1)}

    def write_may_precede(self, context_order: Optional[int]) -> bool:
        """文脈の時点（None = callee の出口）より前に書き込みがあり得るか。"""

        if self.effect_orders is None:
            return True
        if context_order is None:
            return bool(self.effect_orders)
        return any(order == _UNKNOWN_EFFECT_ORDER or order < context_order for order in self.effect_orders)


@dataclass(frozen=True)
class CalleeParameter:
    """callee の parameter 1 つ。`value` は caller の引数を parameter の幅へ合わせた値（引数が無ければ None）。"""

    index: Optional[int]
    ref: Optional[LocationBaseRef]
    storage: Optional[object]
    value: Optional[Expression]


@dataclass(frozen=True)
class CalleeBinding:
    """callee の parameter → caller の引数。**callee の式の node と callee の parameter の対応の唯一の owner**。

    境界は parameter の置き換えも同じ走査で行う（Issue #281 review 5）。node が callee の parameter の
    **入口の値** を表すと言えるのは、次をすべて満たすときだけ（`resolve`。review 6）:

    * 所有者: node は `PARAMETER` で、ref が無いか、callee の parameter の `LocationBaseRef`（`kind=parameter`）。
      ref に所有者（program・関数の入口）があれば、callee の parameter の所有者と一致する
      （`_callee_location_base_matches_ref`。所有者の無い側は index だけで比べる）。所有者の違う parameter
      （別の関数の parameter）は caller の言葉に無いので拒否する。
    * 時点: 値の node の時点・位置の主張は、境界が先に落とすか拒否している（`_value_ref_is_callee_claim`）。
      `PARAMETER` 以外の node（同じ register / stack の記憶域にある callee の別の値、post-state の確定値など）は、
      記憶域や index が parameter と同じでも入口の値ではないので、置き換えない（記憶域の主張は境界が拒否する）。
    * 値: index が callee の parameter のただ 1 つに決まり、node に記憶域があれば parameter の記憶域に
      含まれる（`_storage_matches_parameter`）。食い違えば拒否する。

    以前は node の identity key（所有者の無い index・記憶域・**caller の** descriptor で引いた key）の
    どれか 1 つが置き換えの表に当たれば置き換えていた: 所有者の違う同じ index の parameter、同じ register に
    ある callee の別の値・post-state の確定値が、引数に化け得た。

    `simplify_parameters` は置き換えの後の簡約（`_simplify_substituted_expression`）が使う descriptor で、
    parameter の対応には使わない。
    """

    parameters: Tuple[CalleeParameter, ...] = ()
    simplify_parameters: Tuple[object, ...] = ()

    @classmethod
    def for_arguments(
        cls,
        callee_parameters: Sequence[object],
        args: Sequence[Expression],
        *,
        simplify_parameters: Optional[Sequence[object]] = None,
    ) -> "CalleeBinding":
        from scripts.function_tracer_pcode.analysis.effects.call_argument import (
            _impl__coerce_argument_to_callee_parameter as coerce_argument_to_callee_parameter,
            _impl__coerce_callee_parameter_refs as coerce_callee_parameter_refs,
            _impl__coerce_storage_info as coerce_storage_info,
            _impl__normalize_parameter_index as normalize_parameter_index,
        )

        params = list(callee_parameters or ())
        arguments = list(args or ())
        entries = []
        for position, (param, ref) in enumerate(zip(params, coerce_callee_parameter_refs(params))):
            index = None
            if ref is not None and ref.is_parameter():
                index = normalize_parameter_index(ref.parameter_index)
            storage = coerce_storage_info(param.get("storage")) if isinstance(param, dict) else None
            if storage is None and ref is not None and ref.is_storage():
                from scripts.function_tracer_pcode.analysis.effects.call_argument import (
                    _impl__storage_info_from_base_ref as storage_info_from_base_ref,
                )

                storage = storage_info_from_base_ref(ref)
            value = None
            if position < len(arguments):
                value = coerce_argument_to_callee_parameter(arguments[position], param)
            entries.append(CalleeParameter(index=index, ref=ref, storage=storage, value=value))
        return cls(
            parameters=tuple(entries),
            simplify_parameters=tuple(params if simplify_parameters is None else simplify_parameters),
        )

    def resolve(self, node: Expression) -> Optional[Expression]:
        """node が callee の parameter の入口の値なら caller の値。parameter でなければ None。対応できなければ拒否。"""

        if node.expr_type is not ExpressionType.PARAMETER:
            return None
        parameter = self._parameter_of(node)
        if parameter.value is None:
            raise CallBoundaryRefused(
                REFUSED_CALLEE_PARAMETER_UNBOUND, expr_type=node.expr_type.name, ref_type=type(node.runtime_ref).__name__
            )
        return parameter.value

    def _parameter_of(self, node: Expression) -> CalleeParameter:
        from scripts.function_tracer_pcode.analysis.effects.call_argument import (
            _impl__coerce_storage_info as coerce_storage_info,
            _impl__normalize_parameter_index as normalize_parameter_index,
            _impl__storage_matches_parameter as storage_matches_parameter,
        )
        from scripts.function_tracer_pcode.analysis.effects.location import (
            _impl__callee_location_base_matches_ref as location_base_matches_ref,
        )

        ref = node.runtime_ref
        ref_type = type(ref).__name__
        if type(ref) is PostStateValueRef:
            # 境界が落とす主張（「callee の出口の状態の値と等しい」）。値そのものは node が表す
            ref = None
        if ref is not None and not (type(ref) is LocationBaseRef and ref.is_parameter()):
            raise CallBoundaryRefused(REFUSED_CALLEE_PARAMETER_IDENTITY, expr_type="PARAMETER", ref_type=ref_type)
        if ref is not None:
            index = normalize_parameter_index(ref.parameter_index)
            candidates = [
                parameter
                for parameter in self.parameters
                if parameter.index is not None
                and parameter.index == index
                and parameter.ref is not None
                and location_base_matches_ref(ref, parameter.ref)
            ]
            if not candidates and (ref.owner_program_id is not None or ref.owner_entry_offset is not None):
                raise CallBoundaryRefused(REFUSED_CALLEE_FOREIGN_PARAMETER, expr_type="PARAMETER", ref_type=ref_type)
        else:
            index = normalize_parameter_index(getattr(node, "value", None))
            candidates = [
                parameter for parameter in self.parameters if parameter.index is not None and parameter.index == index
            ]
        if len(candidates) != 1:
            # callee の parameter のどれでもない（loop の placeholder・index の分からない parameter など）か、決まらない
            raise CallBoundaryRefused(REFUSED_CALLEE_PARAMETER_UNBOUND, expr_type="PARAMETER", ref_type=ref_type)
        parameter = candidates[0]
        node_storage = coerce_storage_info(getattr(node, "storage_info", None))
        parameter_storage = coerce_storage_info(parameter.storage)
        if (
            node_storage is not None
            and parameter_storage is not None
            and not storage_matches_parameter(node_storage, parameter_storage)
        ):
            raise CallBoundaryRefused(REFUSED_CALLEE_PARAMETER_IDENTITY, expr_type="PARAMETER", ref_type="storage_info")
        return parameter


def is_context_free_value(expr: Optional[Expression]) -> bool:
    """関数の時点・場所・parameter を持たない値か（定数と、定数だけの演算）。

    callee の解析へ引数を束縛してよいのはこの値だけ（`_bound_parameter_values_from_call_args`）。それ以外の
    caller の値（caller の parameter・memory の読み出し・caller の frame の番地）を束縛すると、caller の順序の
    読み出しが callee の effect と比べられ、caller の parameter が callee の parameter と同じ key で置き換えられ、
    caller の frame の番地が callee の frame に分類される（Issue #281 review 5）。束縛しない引数は境界の置き換えで
    caller の値になる（意味は同じ）。
    """

    if expr is None:
        return False
    stack = [expr]
    seen = set()
    while stack:
        node = stack.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        if node.expr_type not in (ExpressionType.CONSTANT, ExpressionType.UNARY_OP, ExpressionType.BINARY_OP):
            return False
        ref = getattr(node, "runtime_ref", None)
        if ref is not None and type(ref) is not AddressValueRef:
            return False
        if getattr(node, "storage_info", None) is not None or getattr(node, "read_order_key", None) is not None:
            return False
        stack.extend(node.operands or ())
    return True


def import_callee_expression(
    expr: Optional[Expression],
    site: CallSite,
    timeline: CalleeTimeline,
    *,
    context_order: Optional[int] = None,
    binding: Optional[CalleeBinding] = None,
) -> Optional[Expression]:
    """callee の式を caller の値にする。`context_order` は effect の値の文脈ならその effect の順序。

    `binding` を渡すと callee の parameter を caller の引数へ置き換える（production の境界はすべて渡す）。
    渡さなければ parameter はそのまま（parameter を持たない展開・test 用）。
    """

    if expr is None:
        return None
    return CalleeImporter(site, timeline, context_order=context_order, binding=binding).expression(expr)


def import_callee_condition(
    condition: Optional[Condition],
    site: CallSite,
    timeline: CalleeTimeline,
    *,
    context_order: Optional[int] = None,
    binding: Optional[CalleeBinding] = None,
) -> Optional[Condition]:
    if condition is None:
        return None
    return CalleeImporter(site, timeline, context_order=context_order, binding=binding).condition(condition)


class CalleeImporter:
    """1 つの呼び出しの境界（`site`・`timeline`・`binding` が同じ）で、callee の式を caller の値にする。

    同じ境界で多くの式を移す呼び出し側（bounded refinement の展開の組み合わせ）は、1 つを使い回して
    共有の部分木の変換を 1 回にする。
    """

    def __init__(
        self,
        site: CallSite,
        timeline: CalleeTimeline,
        *,
        context_order: Optional[int] = None,
        binding: Optional[CalleeBinding] = None,
    ) -> None:
        self.site = site
        self.timeline = timeline
        self.context_order = context_order
        self.binding = binding
        # memo（review 6）: 値は (元の node, 結果)。元の node を生かしておくので、解放された node の id を別の
        # node が再利用して古い結果を引くことはない（引くときも `is` で確かめる）。呼び出しをまたいで持つのは
        # 凍結済み（`is_frozen`: 意味の field が変わらない）の node だけ。組み立て中の node は呼び出し側が後で
        # 書き換え得るので、1 回の `expression` / `condition` の走査の中だけで memo する（`_transient`）
        self._memo: Dict[int, Tuple[Expression, Expression]] = {}
        self._transient: Optional[Dict[int, Tuple[Expression, Expression]]] = None
        if binding is not None:
            from scripts.function_tracer_pcode.analysis.effects.location import (
                _impl__simplify_substituted_expression,
            )

            self._simplify = _impl__simplify_substituted_expression
            self._simplify_parameters = list(binding.simplify_parameters)

    def condition(self, condition: Condition) -> Condition:
        return self._top_level(self._condition, condition)

    def expression(self, expr: Expression) -> Expression:
        return self._top_level(self._expression, expr)

    def _top_level(self, convert, value):
        if self._transient is not None:
            return convert(value)
        self._transient = {}
        try:
            return convert(value)
        finally:
            self._transient = None

    def _condition(self, condition: Condition) -> Condition:
        imported = self._expression(condition.expression)
        if imported is condition.expression:
            return condition
        return Condition(imported, condition.negated)

    def _expression(self, expr: Expression) -> Expression:
        memo = self._memo if getattr(expr, "is_frozen", False) else self._transient
        cached = memo.get(id(expr))
        if cached is not None and cached[0] is expr:
            return cached[1]
        result = self._import(expr)
        if self.binding is not None:
            # 置き換えと同じ後処理（`substitute_expression` は置き換えた node と辿った node を簡約する）
            result = self._simplify(result, self._simplify_parameters)
        memo[id(expr)] = (expr, result)
        return result

    def _parameter(self, expr: Expression) -> Optional[Expression]:
        """callee の parameter の入口の値を表す node なら caller の値（`CalleeBinding.resolve`）。それ以外は None。"""

        if self.binding is None:
            return None
        # caller の値なので、境界の規則（callee の時点・位置の主張）を当てない
        return self.binding.resolve(expr)

    def _import(self, expr: Expression) -> Expression:
        if expr.expr_type == ExpressionType.MEMORY and expr.operands:
            return self._memory(expr)
        # 1. 値の node（MEMORY 以外）の ref を、置き換え・子より先に決める。post-state の読み出し・位置の
        #    主張は parameter の key を持ち得る（`*param_1` の post-state は param_1 の基底）が、parameter の値
        #    ではないので、置き換えてはいけない（拒否なら子を辿る費用も要らない）
        drop_ref = self._value_ref_is_callee_claim(expr)
        # 2. callee の parameter を指す node は caller の値（置き換えが無ければ拒否）
        replacement = self._parameter(expr)
        if replacement is not None:
            return replacement
        # 3. callee の記憶域（frame・register。callee の stack / register で渡る parameter は 2 で caller の値に
        #    なっている）
        self._refuse_callee_storage(expr)
        if expr.expr_type == ExpressionType.PHI and expr.value:
            branches = []
            changed = False
            for cond, value in expr.value:
                new_cond = self._condition(cond) if cond is not None else None
                new_value = self._expression(value)
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
        new_operands = [self._expression(operand) for operand in operands]
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

        `storage_info` が callee の frame を指す node（`StorageInfo.claims_frame`: stack / frame pointer、stack
        空間）も拒否（`_address_root_is_stack_frame` は caller の frame と読む）。
        """

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

    def _refuse_callee_storage(self, expr: Expression) -> None:
        """callee の記憶域を持つ node は拒否する（callee の parameter の入口の値は `_parameter` で置き換え済み）。

        * frame（`StorageInfo.claims_frame`: stack / frame pointer、stack 空間）: caller の consumer は caller の
          frame と読む（`_address_root_is_stack_frame`）。
        * register（`PARAMETER` 以外の node）: callee のある時点の register の値で、caller の言葉に無い。
          parameter と同じ register にあっても入口の値とは限らない（review 6: 同じ記憶域の別の値・post-state の
          確定値が引数に化けた）。
        """

        storage = getattr(expr, "storage_info", None)
        claims_frame = getattr(storage, "claims_frame", None)
        if callable(claims_frame) and claims_frame():
            raise CallBoundaryRefused(
                REFUSED_CALLEE_PLACE, expr_type=expr.expr_type.name, ref_type="storage_info"
            )
        if (
            storage is not None
            and getattr(storage, "is_register", False)
            and expr.expr_type is not ExpressionType.PARAMETER
        ):
            raise CallBoundaryRefused(
                REFUSED_CALLEE_REGISTER_VALUE, expr_type=expr.expr_type.name, ref_type="storage_info"
            )

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
        new_address = self._expression(address)
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
