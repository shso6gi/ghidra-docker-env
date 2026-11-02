# -*- coding: utf-8 -*-
"""式の node と parameter の入口の値の対応（Issue #281 review 8）。

**node が「どの関数の、どの parameter の、入口の値の、どの bit」を表すかの唯一の owner**。node を
parameter の値として扱う経路（関数をまたぐ置き換え `CalleeBinding`、条件 `x == v` による同じ関数の中の
置き換え、呼び出しの引数の正規化、varnode からの parameter の回復、条件の下の parameter の等しさ）は、
すべてここで node の主張を読む。

**不変条件（node の側）**: parameter の入口の値を表す node は `PARAMETER` の node だけで、

* 所有者: ref が無いか、parameter の `LocationBaseRef`（`kind=parameter`）。所有者（program・関数の入口）の
  ある ref は、その関数の parameter を表す。所有者の無い node は、その node を作った解析の関数の parameter
  （以前からの約束。所有者を持つ側とは index で比べる: `same_parameter`）。
* 時点: 入口の値。callee の出口の状態・memory の読み出し・ある時点の register の値（`PostStateReadRef` /
  `CanonicalLocation` / `ObservedMemoryReadRef` などの ref を持つ node、`MEMORY` / `VARIABLE` の node）は、
  記憶域・index・位置の基底が parameter と同じでも入口の値ではない。`PostStateValueRef`（「値は出口の状態の
  location の値とも等しい」）は値そのものを変えないので、入口の値の主張を妨げない。
* bit: `storage_info` があれば、node の bit はちょうどその記憶域にある（parameter の記憶域の一部なら、その
  位置の bit）。`storage_info` が無ければ parameter の値そのもの（幅は parameter の幅）。parameter の一部を
  記憶域なしで表すときは `SUBPIECE(parameter, 位置)` にする（位置は p-code と同じく significance の低い側から
  数えた byte）。

以前は node の identity key（所有者の無い index・記憶域・位置の基底・descriptor）のどれかが当たれば
parameter とみなしていた: `p == 0x1000` の下で `MEM[p]`（位置の基底が p）や p の出口の状態、所有者の違う
同じ index の parameter が 0x1000 に化け、varnode から回復した parameter の一部（上位 32 bit）が parameter の
記憶域全体を持つ 32 bit の node（下位 32 bit と読まれる）になっていた。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from scripts.function_tracer_pcode.core import (
    Expression,
    ExpressionType,
    LocationBaseRef,
    PostStateValueRef,
)


@dataclass(frozen=True)
class EntryClaim:
    """node の「parameter の入口の値」の主張。`ref` は parameter の `LocationBaseRef`（無ければ None）。"""

    index: int
    ref: Optional[LocationBaseRef]
    storage: Optional[object]
    bits: int


def entry_claim(node: Optional[Expression]) -> Optional[EntryClaim]:
    """node が parameter の入口の値を表すと主張するなら、その主張。主張しない node は None。"""

    from scripts.function_tracer_pcode.analysis.effects.call_argument import (
        _impl__coerce_storage_info as coerce_storage_info,
        _impl__normalize_parameter_index as normalize_parameter_index,
    )

    if node is None or node.expr_type is not ExpressionType.PARAMETER:
        return None
    ref = getattr(node, "runtime_ref", None)
    if type(ref) is PostStateValueRef:
        ref = None
    if ref is not None and not (type(ref) is LocationBaseRef and ref.is_parameter()):
        return None
    index = normalize_parameter_index(ref.parameter_index if ref is not None else getattr(node, "value", None))
    if index is None:
        return None
    return EntryClaim(
        index=index,
        ref=ref,
        storage=coerce_storage_info(getattr(node, "storage_info", None)),
        bits=expression_bits(node),
    )


def is_entry_value(node: Optional[Expression]) -> bool:
    """node が parameter の入口の値を表すか（index の分からない、記憶域の基底の parameter も含む）。

    `entry_claim` は index で parameter を引ける主張だけを返す。位置の基底を決めるだけの consumer
    （`_resolve_location_base_with_offset`）は、記憶域の基底（`LocationBaseRef.storage`）で表した入口の値も読む。
    """

    if node is None or node.expr_type is not ExpressionType.PARAMETER:
        return False
    ref = getattr(node, "runtime_ref", None)
    return ref is None or type(ref) is PostStateValueRef or (
        type(ref) is LocationBaseRef and (ref.is_parameter() or ref.is_storage())
    )


def is_register_entry_variable(node: Optional[Expression]) -> bool:
    """node が register の入口の値を表す `VARIABLE` の葉か。

    tracer は定義の無い varnode（関数の入力）だけを ref の無い `VARIABLE` の葉にする（`_trace_varnode_internal`:
    定義のある varnode は定義の op を辿る）。register の記憶域を持つその葉は、解析している関数の入口の、その
    register の値。callee の register の値は関数をまたぐ境界が拒否する（`CalleeImporter._refuse_callee_storage`）
    ので、caller の式には入らない。ref を持つ `VARIABLE`（出口の状態の読み出し `poststate_*`、loop の変数など）は
    入口の値ではない。
    """

    if node is None or node.expr_type is not ExpressionType.VARIABLE or node.operands:
        return False
    if getattr(node, "runtime_ref", None) is not None:
        return False
    storage = getattr(node, "storage_info", None)
    return storage is not None and bool(getattr(storage, "is_register", False))


def whole_parameter_descriptor(node: Optional[Expression], parameters):
    """node が parameter の入口の値の **全体** を表すなら、その parameter の descriptor。それ以外は None。

    入口の値（`PARAMETER` の主張、または register の入口の値の葉）で、bit が parameter の値とちょうど同じ
    （幅が同じで、記憶域が parameter の記憶域と同じ範囲。記憶域の無い `PARAMETER` は index で引いた parameter
    そのもの）ときだけ。parameter の一部・別の時点の値・memory の読み出しを parameter にしない（review 8）。
    """

    from scripts.function_tracer_pcode.analysis.effects.call_argument import (
        MemoryRelation,
        _impl__coerce_storage_info as coerce_storage_info,
        _impl__parameter_expression_from_descriptor as parameter_expression_from_descriptor,
        _impl__resolve_parameter_descriptor as resolve_parameter_descriptor,
        _impl__storage_match_rank as storage_match_rank,
    )

    if not (is_entry_value(node) or is_register_entry_variable(node)):
        return None
    descriptor = resolve_parameter_descriptor(node, parameters)
    if descriptor is None:
        return None
    whole = parameter_expression_from_descriptor(descriptor)
    if whole is None or expression_bits(node) <= 0 or expression_bits(node) != expression_bits(whole):
        return None
    claim = entry_claim(node)
    if claim is not None:
        whole_claim = entry_claim(whole)
        if whole_claim is None or not same_parameter(claim, whole_claim):
            return None
    node_storage = coerce_storage_info(getattr(node, "storage_info", None))
    parameter_storage = coerce_storage_info(descriptor.get("storage"))
    if node_storage is None or parameter_storage is None:
        # 記憶域で位置を比べられない: index で引いた `PARAMETER` の主張（幅は上で同じと確かめた）だけ
        return descriptor if claim is not None else None
    if storage_match_rank(node_storage, parameter_storage) != MemoryRelation.SAME:
        return None
    return descriptor


def ref_has_owner(ref: Optional[LocationBaseRef]) -> bool:
    return ref is not None and (ref.owner_program_id is not None or ref.owner_entry_offset is not None)


def same_parameter(left: EntryClaim, right: EntryClaim) -> bool:
    """2 つの主張が同じ関数の同じ parameter か。所有者がどちらにもあれば一致が要る。"""

    from scripts.function_tracer_pcode.analysis.effects.location import (
        _impl__callee_location_base_matches_ref as location_base_matches_ref,
    )

    if left.index != right.index:
        return False
    if ref_has_owner(left.ref) and ref_has_owner(right.ref):
        return location_base_matches_ref(left.ref, right.ref)
    return True


def same_entry_bits(node: Optional[Expression], source: Optional[Expression]) -> bool:
    """2 つの node が同じ関数の同じ parameter の入口の値の、同じ bit を表すか。

    幅が同じ（分かっている）で、記憶域がどちらにも無いか同じ範囲（`MemoryRelation.SAME`）。記憶域の
    片方だけがある組は、記憶域の無い側が parameter の値そのもので、ある側が記憶域の一部かもしれないので
    同じとは言わない。
    """

    from scripts.function_tracer_pcode.analysis.effects.call_argument import (
        MemoryRelation,
        _impl__storage_match_rank as storage_match_rank,
    )

    left, right = entry_claim(node), entry_claim(source)
    if left is None or right is None or not same_parameter(left, right):
        return False
    if left.bits <= 0 or left.bits != right.bits:
        return False
    if left.storage is None or right.storage is None:
        return left.storage is None and right.storage is None
    return storage_match_rank(left.storage, right.storage) == MemoryRelation.SAME


def bit_offset_in_parameter(
    node_storage,
    node_bits: int,
    parameter_storage,
    parameter_bits: int,
    big_endian: Optional[bool],
) -> Optional[int]:
    """node の bit の、parameter の値の中での最下位の位置（値の LSB を 0 とする）。決められなければ None。

    * 記憶域の無い node は parameter の値そのもの: 幅が値と同じときだけ位置 0。幅が違えば、どの bit かを
      node が言っていないので決めない（以前は下位の bit と読んでいた: review 8）。
    * parameter の記憶域が分からない: `_register_low_end`。
    * node の記憶域が parameter の記憶域と同じ範囲（同じ基底の register・同じ空間。以前は範囲の数だけを比べ、
      別の register の同じ位置も位置 0 にしていた: review 9）なら位置 0。register の一部（parameter の記憶域に含まれる
      範囲）なら、番地の順の位置を byte order で significance の位置へ直す（big endian では番地の小さい側が上位）。
    """

    if node_storage is None:
        return 0 if node_bits > 0 and node_bits == parameter_bits else None
    if parameter_storage is None:
        return _register_low_end(node_storage, node_bits, parameter_bits, big_endian)
    node_range = storage_byte_range(node_storage)
    parameter_range = storage_byte_range(parameter_storage)
    if node_range is None or parameter_range is None:
        return None
    if node_range == parameter_range and _same_location(node_storage, parameter_storage):
        return 0
    if not (node_storage.is_register and parameter_storage.is_register) or big_endian is None:
        return None
    if not node_storage.shares_base_register_with(parameter_storage):
        return None
    (node_low, node_size), (parameter_low, parameter_size) = node_range, parameter_range
    if node_low < parameter_low or node_low + node_size > parameter_low + parameter_size:
        return None
    if big_endian:
        return ((parameter_low + parameter_size) - (node_low + node_size)) * 8
    return (node_low - parameter_low) * 8


def significance_low_offset(storage, reference, big_endian: Optional[bool]) -> Optional[int]:
    """記憶域 `storage` の significance の低い端が、記憶域 `reference` の低い端から何 bit 上にあるか（負もあり得る）。

    範囲が同じなら 0（byte order は要らない）。違えば、同じ基底の register どうしで byte order が分かるときだけ
    決める（big endian では番地の大きい側が下位）。memory・別の register・byte order が分からないなら None。
    `StorageInfo.bit_offset_in_base` は番地の順の位置で significance の位置ではないので、ここを通して直す
    （review 9）。
    """

    if storage is None or reference is None:
        return None
    storage_range = storage_byte_range(storage)
    reference_range = storage_byte_range(reference)
    if storage_range is None or reference_range is None or not _same_location(storage, reference):
        return None
    if storage_range == reference_range:
        return 0
    if not (storage.is_register and reference.is_register) or big_endian is None:
        return None
    (low, size), (reference_low, reference_size) = storage_range, reference_range
    if big_endian:
        return ((reference_low + reference_size) - (low + size)) * 8
    return (low - reference_low) * 8


def _same_location(storage, reference) -> bool:
    """`storage_byte_range` の位置を比べてよい組か（同じ基底の register、または同じ空間の memory）。

    基底の分からない register は、番地と幅がちょうど同じ（同じ register）ときだけ。
    """

    if storage.is_register and reference.is_register:
        if storage.shares_base_register_with(reference):
            return True
        return (
            getattr(storage, "space_id", None) == getattr(reference, "space_id", None)
            and int(getattr(storage, "offset", -1)) == int(getattr(reference, "offset", -2))
            and int(getattr(storage, "size", 0) or 0) == int(getattr(reference, "size", 0) or 0)
        )
    if storage.is_register or reference.is_register:
        return False
    return getattr(storage, "space_id", None) == getattr(reference, "space_id", None)


def entry_value_in_storage(
    whole: Expression,
    parameter_storage,
    known_bits: int,
    storage,
    bits: int,
    big_endian: Optional[bool],
) -> Optional[Tuple[Expression, int]]:
    """記憶域 `storage` の significance の低い側 `bits` bit に、parameter の入口の値が何を置いているか（review 9）。

    **parameter の入口の値を「別の記憶域の値」として読む producer の唯一の owner**（live-in の引数の回復）。
    parameter は記憶域 `parameter_storage` の低い側 `known_bits` bit（宣言の値。ABI）を決めている。戻り値は
    (式, 式が決めている `storage` の低い側の bit 数):

    * 要る範囲が parameter の決めている範囲に収まる: その位置の値（`parameter_piece`）。位置 0 なら parameter の
      決めている範囲そのもの（要る幅より広くてよい。引数の正規化が下位を取る）。
    * 要る範囲の低い端が parameter の低い端と同じで、parameter が狭い: parameter の値（決めている bit は
      `known_bits`。残りは呼び出し側が `CallArgumentWidthEvidence` で部分的な幅と記録する）。
    * それ以外（parameter が要る範囲の上位にしかない・範囲の外・位置を決められない）: None。

    以前の live-in の回復は、記憶域の包含だけで descriptor を選んで parameter を丸ごと返し、幅が違えば下位の
    bit を取っていた: 64 bit の parameter の上位 32 bit が要る呼び出しに下位 32 bit が渡った
    （`0x0000000200000001` の上位の 2 が 1 になる）。
    """

    whole_bits = expression_bits(whole)
    known_bits = min(int(known_bits or 0), whole_bits)
    if known_bits <= 0 or bits <= 0:
        return None
    parameter_range = storage_byte_range(parameter_storage) if parameter_storage is not None else None
    storage_range = storage_byte_range(storage) if storage is not None else None
    if parameter_range is None or storage_range is None:
        return None
    if known_bits > parameter_range[1] * 8 or bits > storage_range[1] * 8:
        return None
    offset = significance_low_offset(storage, parameter_storage, big_endian)
    if offset is None or offset < 0:
        return None
    if offset == 0:
        extracted = parameter_piece(whole, 0, known_bits)
        return None if extracted is None else (extracted, min(bits, known_bits))
    if offset + bits > known_bits:
        return None
    extracted = parameter_piece(whole, offset, bits)
    return None if extracted is None else (extracted, bits)


def _register_low_end(node_storage, node_bits: int, parameter_bits: int, big_endian: Optional[bool]) -> Optional[int]:
    """parameter の記憶域が分からない（effect 要約の `LocationBaseRef` だけの束縛）ときの node の位置。

    register で渡る parameter の値は register の下位から始まる（ABI）。node が register の下位の端
    （byte order で直した significance の位置が 0）にあり、幅が値と同じときだけ、値そのもの（位置 0）とする。
    幅が違う（register の組で渡る値の一部かもしれない）・下位の端でない・byte order が分からないなら None。
    """

    if not node_storage.is_register or big_endian is None:
        return None
    if node_bits != parameter_bits:
        return None
    node_range = storage_byte_range(node_storage)
    base_size = int(getattr(node_storage, "base_register_size_bits", 0) or 0)
    if node_range is None or base_size <= 0 or base_size % 8:
        return None
    node_low, node_size = node_range
    significance = (base_size // 8 - (node_low + node_size)) if big_endian else node_low
    return 0 if significance == 0 else None


def parameter_piece(whole: Expression, low_bit: int, bits: int) -> Optional[Expression]:
    """parameter の値 `whole` の、位置 `low_bit` から `bits` bit の値（範囲が値と同じなら `whole` そのもの）。"""

    whole_bits = expression_bits(whole)
    if low_bit < 0 or bits <= 0 or low_bit + bits > whole_bits:
        return None
    if low_bit == 0 and bits == whole_bits:
        return whole
    if low_bit % 8 or bits % 8:
        return None
    extracted = Expression.binary_op(
        "SUBPIECE",
        whole,
        Expression.constant(low_bit // 8, size=max(1, int(whole.size or 0))),
    )
    extracted.size = bits // 8
    return extracted


def expression_bits(expr: Optional[Expression]) -> int:
    try:
        return max(0, int(getattr(expr, "size", 0) or 0)) * 8
    except (TypeError, ValueError):
        return 0


def storage_byte_range(storage) -> Optional[Tuple[int, int]]:
    """記憶域の (番地の順の byte の位置, byte 数)。register は基底の register の中の位置。分からなければ None。"""

    try:
        if storage.is_register:
            bit_offset = int(getattr(storage, "bit_offset_in_base", 0) or 0)
            size_bits = int(getattr(storage, "size_bits", 0) or 0) or int(storage.size or 0) * 8
            if bit_offset % 8 or size_bits <= 0 or size_bits % 8:
                return None
            return bit_offset // 8, size_bits // 8
        size = int(storage.size or 0)
        return (int(storage.offset), size) if size > 0 else None
    except (TypeError, ValueError, AttributeError):
        return None
