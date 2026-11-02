# -*- coding: utf-8 -*-
"""同じ関数の中の 2 つの memory の位置の関係と、frame の局所性（Issue #282）。

**同じ側の中の、書き込みと読み出しの関係（I3）と、store を観測しなくてよいか（I11）の唯一の owner**。

* `location_relation(left, right, conditions)`: 2 つの `CanonicalLocation` の関係（`MemoryRelation`）。
  `DISJOINT` / `SAME` は **証明できたときだけ** 返す。分からなければ `UNKNOWN`（重なり得る）。consumer は
  `DISJOINT` 以外を「読み出しの値が store に依存し得る」と読む。以前は `locations_match`（must-alias だけ）が
  False を返した組（別の parameter、重なる別の offset、幅の違う store）を「別の場所」と読み、may-alias の
  store を無視して入口の memory を読んでいた（偽 EQ の形）。
* `frame_local_range(location)`: store を観測から外す**候補**の範囲（entry SP を起点とする定数 offset で、範囲が
  entry SP より下 `hi <= 0`）。entry SP より下というだけでは局所にしない（AC 9）: 局所と認めるのは関数ごとの証拠
  `frame_locality.FrameLocality`（frame の番地が外へ出ない・呼び出しが frame を読まない）がそろったときだけで、
  その判定は `store_effect` が持つ。

parameter の判定（位置の基底が parameter か、2 つの parameter が条件の下で等しいか）は自分で決めない:
前者は `_resolve_location_base_with_offset`（= `parameter_entry.whole_parameter_descriptor`）が作った基底を
読み、後者は `_collect_param_equalities`（= `parameter_entry.entry_claim`）を使う（#281 review 8 と同じ規則）。

**意味領域の前提**（#188 が所有する D の条項）:

* D-S: caller の生きた object は entry SP より下に無い。parameter の pointer と、入口で caller から届く値
  （global の番地）は、この関数の frame（entry SP より下）を指さない。
* D-S だけでは frame と parameter・global を DISJOINT にしない（AC 9）。frame の番地が外へ出ない証拠
  （`FrameLocality.proven`）が渡され、経路の条件に frame の番地が値として現れない（`p == sp - 16` の下では
  入口の pointer が frame の slot と同じ番地になる経路がある）ときだけ。それ以外は `UNKNOWN`。
* memory から読んだ pointer を基底に持つ位置（deref の step）は、frame の番地が外へ出た後の値かもしれないので
  `UNKNOWN`。
"""

from __future__ import annotations

from typing import Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core import CanonicalLocation, Condition
from scripts.function_tracer_pcode.core.memory_relation import MemoryRelation


def _normalized(location: CanonicalLocation) -> CanonicalLocation:
    from scripts.function_tracer_pcode.analysis.effects._api import _normalize_canonical_location

    return _normalize_canonical_location(location)


#: 番地の offset は 64 bit の剰余で表される（`sp + 0xfffffffffffffff0` は `sp - 16`）。符号付きに直して比べる。
#: 絶対値がこれを超える offset は回り込みを否定できないので、関係を決めない
_ADDRESS_BITS = 64
_MAX_OFFSET_MAGNITUDE = 1 << 62


def _signed_offset(value: int) -> Optional[int]:
    value = int(value) & ((1 << _ADDRESS_BITS) - 1)
    if value >= 1 << (_ADDRESS_BITS - 1):
        value -= 1 << _ADDRESS_BITS
    if abs(value) > _MAX_OFFSET_MAGNITUDE:
        return None
    return value


def _has_deref(location: CanonicalLocation) -> bool:
    return any(str(step.kind) == "deref" for step in (location.steps or ()))


def frame_local_range(location: Optional[CanonicalLocation]) -> Optional[Tuple[int, int]]:
    """store を観測しなくてよい frame の範囲 `[lo, hi)`（entry SP からの byte）。それ以外は None。

    位置の基底 `stack_frame` は「entry SP を起点とする番地」だけ（stack 空間の varnode の offset、または
    SP の register の入口の値。`_is_stack_frame_base_expression`）。step が残る（index・deref を含む）位置、
    範囲が entry SP 以上に届く位置（caller の frame、stack で渡る引数の領域）は None。
    """

    if location is None:
        return None
    location = _normalized(location)
    if not location.base_ref.is_stack_frame() or location.steps:
        return None
    size = int(location.size or 0)
    lo = _signed_offset(location.offset)
    if size <= 0 or lo is None:
        return None
    hi = lo + size
    if hi > 0:
        return None
    return lo, hi


def _interval_relation(left_offset: int, left_size: int, right_offset: int, right_size: int) -> MemoryRelation:
    if left_size <= 0 or right_size <= 0:
        return MemoryRelation.UNKNOWN
    if left_offset == right_offset and left_size == right_size:
        return MemoryRelation.SAME
    if left_offset + left_size <= right_offset or right_offset + right_size <= left_offset:
        return MemoryRelation.DISJOINT
    return MemoryRelation.OVERLAP


def _same_base(left: CanonicalLocation, right: CanonicalLocation, conditions: Sequence[Condition]) -> bool:
    if left.base_ref == right.base_ref:
        return True
    if not left.base_ref.is_parameter() or not right.base_ref.is_parameter():
        return False
    from scripts.function_tracer_pcode.analysis.effects._api import (
        _collect_param_equalities,
        _parameter_identity_key_from_base_ref,
    )

    left_key = _parameter_identity_key_from_base_ref(left.base_ref)
    right_key = _parameter_identity_key_from_base_ref(right.base_ref)
    if left_key is None or right_key is None:
        return False
    return frozenset((left_key, right_key)) in _collect_param_equalities(list(conditions or ()))


def _frame_is_proven_local(frame_locality, conditions: Sequence[Condition]) -> bool:
    from scripts.function_tracer_pcode.analysis.effects.frame_locality import conditions_mention_frame_address

    if frame_locality is None or not bool(getattr(frame_locality, "proven", False)):
        return False
    return not conditions_mention_frame_address(conditions)


def location_relation(
    left: Optional[CanonicalLocation],
    right: Optional[CanonicalLocation],
    conditions: Sequence[Condition] = (),
    *,
    frame_locality=None,
) -> MemoryRelation:
    """2 つの位置の関係。`conditions` は両方のアクセスが起きる経路の条件（parameter の等しさと、frame の番地が
    値として現れるかを読む）。`frame_locality` はその関数の `FrameLocality`（無ければ frame と parameter・global
    の関係を決めない）。"""

    if left is None or right is None:
        return MemoryRelation.UNKNOWN
    left = _normalized(left)
    right = _normalized(right)

    left_frame = frame_local_range(left)
    right_frame = frame_local_range(right)
    if (left_frame is None) != (right_frame is None):
        # D-S: 入口の値（parameter・global の番地）を起点とする位置は、この関数の frame を指さない。
        # memory から読んだ pointer（deref の step）は frame の番地が外へ出た後の値かもしれない
        other = right if left_frame is not None else left
        if (
            _frame_is_proven_local(frame_locality, conditions)
            and not _has_deref(other)
            and (other.base_ref.is_parameter() or other.base_ref.is_global())
        ):
            return MemoryRelation.DISJOINT
        return MemoryRelation.UNKNOWN

    if _has_deref(left) or _has_deref(right):
        # 同じ step の列でも、間の store で pointer の値が変わり得る（2 回の読み出しは同じ cell を指すとは限らない）
        return MemoryRelation.UNKNOWN
    if left.steps or right.steps:
        return MemoryRelation.UNKNOWN
    if not _same_base(left, right, conditions):
        return MemoryRelation.UNKNOWN
    if left.base_ref.is_storage():
        # register などの記憶域を基底にする位置: 値の時点が分からない
        return MemoryRelation.UNKNOWN
    left_offset = _signed_offset(left.offset)
    right_offset = _signed_offset(right.offset)
    if left_offset is None or right_offset is None:
        return MemoryRelation.UNKNOWN
    return _interval_relation(left_offset, int(left.size or 0), right_offset, int(right.size or 0))
