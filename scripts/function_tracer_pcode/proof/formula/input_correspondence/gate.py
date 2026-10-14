# -*- coding: utf-8 -*-
"""owner を含まない key による左右の同一視を許す条件の唯一の owner（plan v4 PR-P、I3・Q3）。

左右の値を **owner を含まない key**（parameter の index・名前、``("parameter", i)``・
``("loop_limit_parameter", i)``、Method-B key、構造 key の名前の一致など）で同じとみなす
計算は、最終 ``InputCorrespondence`` を通らない。relation が index を入れ替えると、別の入力を
同じものとして扱い、誤った EQ になる（例: 左 ``f(n, m)`` の n と右 ``g(m, n)`` の n は relation
では対応するが、index 0 どうしは別の入力）。

この module は、その同一視が relation の下の同一視と一致する条件を、relation と比べる値から
機械的に決める:

* :func:`positional_identity_gate` — pair 全体の述語。relation が decisive に十分で、全ての組が
  ``FULL_REGISTER_EQUALITY``・同じ index・同じ名前・同じ幅で、両側の表がその組と同じ行を持つ。
  このとき index / 名前が同じ parameter は対応する入力で、全 bit が等しい。ref が parameter を
  Expression でなく数値（``parameter_index``）で持っていても成り立つ（読みを集めない）。
* :func:`closure_reads_are_full` — closure が比べる値の局所の検査。到達できる PARAMETER の leaf が
  全て表の行の幅で読み、名前と index が同じ行を指す。index だけの key は読みの幅を持たないので、
  狭い読み・広い読みがあれば拒否する。式の graph に入力 VARIABLE（builder が側ごとの extra var
  として宣言する入力）があれば拒否する（名前の一致は対応の証明でない。#248 で scope へ移す）。
* :func:`owner_free_identity_gate` — 上の 2 つの組。owner を含まない同一視をする site はこれだけを
  呼ぶ。relation を渡さなければ現在の比較の relation（``binding.current_relation``）を読み、
  比較の外では通さない（fail-closed）。

拒否は「証明できない」であって、反証ではない。site は計算をせず、保守的な答え（closure を
発行しない、併合しない、lowering しない）へ戻る。最終の EQ gate は、owner を含まない方法で
閉じた比較にこの gate を課す（``proof/obligations/pair_disposition.CrossSideIdentification``）。
PR-H は、この gate を relation を通した翻訳（``CorrespondenceScope``）に置き換える。
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Iterable, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.semantic_freeze import reachable_semantic_values
from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import current_relation
from scripts.function_tracer_pcode.proof.formula.input_correspondence.model import (
    LEFT,
    RIGHT,
    InputCorrespondenceSet,
    InputRelationKind,
)
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo


#: 拒否の evidence ref の接頭辞（reason の evidence と debug の唯一の語彙）。
CROSS_SIDE_IDENTITY_REF = "cross_side_identity"

#: 1 回の拒否で evidence に載せる理由の数（先頭から）。
_EVIDENCE_REF_ITEMS = 4

#: ``owner_free_identity_gate`` の ``ics`` の既定（現在の比較の relation を読む）。明示の
#: ``None`` は「relation が無い」で、現在の比較へ退避しない。
_CURRENT_RELATION = object()


class CrossSideIdentification(str, Enum):
    """closure が左右の値をどう同じとみなしたか（plan v4 PR-P、I3）。

    * ``CORRESPONDENCE``: 左右の記号は側ごと（``_1`` / ``_2``）で、左右を結ぶのは最終
      ``InputCorrespondence`` の premise だけ（SMT の UNSAT）。
    * ``OWNER_FREE``: index・名前・owner を含まない key で左右を同一視した（SMT を使わない
      closure、構造の等価、owner を含まない等式を足した query）。最終の EQ gate は、この
      closure を含む比較に ``positional_identity_gate`` を課す。

    pair の closure は種類が下限を決め（``pair_disposition.closure_identification_floor``）、
    呼び手は下限より保守的な値（``OWNER_FREE``）にしか変えられない。比較の証拠（completed
    recovery proof）は書いた producer が申告し（``binding.store_comparison_evidence``）、申告の
    無い record は ``OWNER_FREE`` として扱う。
    """

    CORRESPONDENCE = "correspondence"
    OWNER_FREE = "owner_free"


@dataclass(frozen=True)
class CrossSideIdentityGate:
    """gate の答え。``passed`` が偽なら ``evidence_refs`` が拒否の理由を持つ。"""

    passed: bool
    evidence_refs: Tuple[str, ...] = ()

    def __bool__(self) -> bool:  # pragma: no cover - 誤用の防止
        raise TypeError("read CrossSideIdentityGate.passed explicitly")

    @classmethod
    def accept(cls) -> "CrossSideIdentityGate":
        return cls(True, ())

    @classmethod
    def refuse(cls, refs: Iterable[str]) -> "CrossSideIdentityGate":
        items = tuple(dict.fromkeys(f"{CROSS_SIDE_IDENTITY_REF}:{ref}" for ref in refs))
        if not items:
            items = (f"{CROSS_SIDE_IDENTITY_REF}:refused",)
        return cls(False, items[:_EVIDENCE_REF_ITEMS])


def _row_key(row: ParameterInfo) -> Tuple[int, str, int]:
    return (int(row.index), str(row.original_name), int(row.bit_width))


def positional_identity_gate(ics: Any) -> CrossSideIdentityGate:
    """relation が「位置どおり・同じ名前・全幅の等式」だけからなるか（pair 全体の述語）。

    通す条件（すべて）:

    1. ``ics`` が ``InputCorrespondenceSet`` で decisive に十分（構造の欠陥・入力領域の欠陥なし）。
    2. ``positional_pairing_gate`` が通る（組と表が位置どおり・同じ名前・全幅の等式）。
    """

    if type(ics) is not InputCorrespondenceSet:
        return CrossSideIdentityGate.refuse(("relation_unavailable",))
    if not ics.decisive_sufficient:
        return CrossSideIdentityGate.refuse(("relation_insufficient",))
    return positional_pairing_gate(ics)


def positional_pairing_gate(ics: Any) -> CrossSideIdentityGate:
    """組と表が位置どおり・同じ名前・全幅の等式か（relation の十分性は問わない）。

    * 全ての組が ``FULL_REGISTER_EQUALITY`` で、左の (index, 名前, 幅) = 右の (index, 名前, 幅)。
      ``MISSING_SIDE`` の組は無い。
    * 両側の表（``left_parameters`` / ``right_parameters``）が組と同じ行の集合で、index が一意。
      owner を含まない key（index・名前）は表の行で解決されるので、組だけでなく表も照合する。

    比較の最終 relation には ``positional_identity_gate``（十分性も要る）を使う。これを直接使うのは、
    比較の中の局所の証明が自分で作る tie だけの relation（``build_tie_only_correspondence_set``。入力
    領域の正本を持たないので常に不十分）の上で、parameter を index で同一視する site だけ。
    """

    if type(ics) is not InputCorrespondenceSet:
        return CrossSideIdentityGate.refuse(("relation_unavailable",))
    refs = []
    # 両側の parameter の数の違いは ``MISSING_SIDE`` の組か表の照合で必ず現れる（別に数えない）。
    pair_rows = {LEFT: [], RIGHT: []}
    for item in ics.correspondences:
        if item.left is None or item.right is None:
            refs.append(f"missing_side:{item.label}")
            continue
        left = (int(item.left.index), str(item.left.name), int(item.left.bit_width))
        right = (int(item.right.index), str(item.right.name), int(item.right.bit_width))
        pair_rows[LEFT].append(left)
        pair_rows[RIGHT].append(right)
        if item.kind is not InputRelationKind.FULL_REGISTER_EQUALITY:
            refs.append(f"not_full_register_equality:{item.label}:{item.kind.value}")
        elif left != right:
            refs.append(f"not_positional:{item.label}:{left[1]}~{right[1]}")
    for side, rows in ((LEFT, ics.left_parameters), (RIGHT, ics.right_parameters)):
        keys = [_row_key(row) for row in rows]
        if len({key[0] for key in keys}) != len(keys) or sorted(keys) != sorted(pair_rows[side]):
            refs.append(f"table_differs_from_relation:{side}")
    if refs:
        return CrossSideIdentityGate.refuse(refs)
    return CrossSideIdentityGate.accept()


def positional_parameter_identity_gate(ics: Any, index: Any) -> CrossSideIdentityGate:
    """index ``index`` の parameter を owner を含まない key で左右同一視してよいか。

    ``positional_identity_gate`` に加えて、その index が両側の表の行であること（表に無い index の
    key は、どの入力とも対応しない）。key が parameter を数値の index だけで持つ site 用。
    """

    positional = positional_identity_gate(ics)
    if not positional.passed:
        return positional
    exact = _exact_int(index)
    if exact is None or any(exact not in _side_rows(ics, side) for side in (LEFT, RIGHT)):
        return CrossSideIdentityGate.refuse((f"parameter_not_in_table:idx{index}",))
    return positional


def _side_rows(ics: InputCorrespondenceSet, side: str) -> Mapping[int, ParameterInfo]:
    rows = ics.left_parameters if side == LEFT else ics.right_parameters
    return {int(row.index): row for row in rows}


def _exact_int(value: Any) -> Optional[int]:
    if isinstance(value, bool) or not isinstance(value, int):
        return None
    return int(value)


def _parameter_read_refusal(expr: Expression, rows: Mapping[int, ParameterInfo], side: str) -> Optional[str]:
    index = _exact_int(expr.value)
    if index is None or index < 0:
        return f"parameter_unbound:{side}:{expr.name}"
    row = rows.get(index)
    if row is None:
        return f"parameter_not_in_table:{side}:idx{index}"
    if str(row.original_name) != str(expr.name):
        return f"parameter_name_differs_from_row:{side}:idx{index}:{expr.name}"
    size = _exact_int(expr.size)
    if size is None or size * 8 != int(row.bit_width):
        return f"parameter_read_not_full:{side}:idx{index}:{size}B/{int(row.bit_width)}b"
    return None


def _side_refusals(values: Sequence[Any], rows: Mapping[int, ParameterInfo], side: str) -> Tuple[str, ...]:
    refs = []
    for value in reachable_semantic_values(tuple(values), through_runtime_refs=True):
        if isinstance(value, Expression) and value.expr_type is ExpressionType.PARAMETER:
            refusal = _parameter_read_refusal(value, rows, side)
            if refusal is not None:
                refs.append(refusal)
    for value in reachable_semantic_values(tuple(values), through_runtime_refs=False):
        if isinstance(value, Expression) and value.expr_type is ExpressionType.VARIABLE:
            refs.append(f"input_variable:{side}:{value.name}")
    return tuple(refs)


def closure_reads_are_full(
    ics: Any,
    left_values: Sequence[Any],
    right_values: Sequence[Any],
) -> CrossSideIdentityGate:
    """closure が比べる値の PARAMETER の読みが全て行の幅で、入力 VARIABLE が無いか。

    ``left_values`` / ``right_values`` は closure が比べる側ごとの値（式・条件・case・ref を
    含む入れ物）。到達は ``reachable_semantic_values``（公開と同じ規則）で、PARAMETER は runtime
    ref の中まで、入力 VARIABLE は式の graph（builder が extra var を集める範囲）で数える。
    """

    if type(ics) is not InputCorrespondenceSet:
        return CrossSideIdentityGate.refuse(("relation_unavailable",))
    refs = _side_refusals(left_values, _side_rows(ics, LEFT), LEFT) + _side_refusals(
        right_values, _side_rows(ics, RIGHT), RIGHT
    )
    if refs:
        return CrossSideIdentityGate.refuse(refs)
    return CrossSideIdentityGate.accept()


def owner_free_identity_gate(
    left_values: Sequence[Any],
    right_values: Sequence[Any],
    *,
    ics: Any = _CURRENT_RELATION,
) -> CrossSideIdentityGate:
    """owner を含まない key で ``left_values`` と ``right_values`` を同一視してよいか。

    site が呼ぶ唯一の入口。``ics`` を省くと現在の比較の最終 relation を使う（比較の外では
    relation が無いので拒否）。pair 全体の述語が先で、通ったときだけ局所の読みを数える。
    """

    relation = current_relation() if ics is _CURRENT_RELATION else ics
    positional = positional_identity_gate(relation)
    if not positional.passed:
        return positional
    return closure_reads_are_full(relation, left_values, right_values)


def final_equivalence_identity_gate(
    owner_free_sources: Sequence[str],
    ics: Any,
) -> CrossSideIdentityGate:
    """最終の EQ gate（backstop）: owner を含まない方法で閉じた部分がある比較に pair 全体の述語を課す。

    ``owner_free_sources`` は EQ の根拠のうち owner を含まない方法で左右を同一視したもの
    （ledger の ``owner_free_closures`` の pair など）。無ければ全て relation の premise の下の
    SMT なので通す。あれば ``positional_identity_gate`` が通るときだけ通す。site の gate を
    漏らした経路も、ここで最終判定の前に止まる。
    """

    sources = tuple(str(item) for item in owner_free_sources)
    if not sources:
        return CrossSideIdentityGate.accept()
    positional = positional_identity_gate(ics)
    if positional.passed:
        return positional
    return CrossSideIdentityGate.refuse(
        tuple(f"owner_free_source:{item}" for item in sources[:1])
        + tuple(ref[len(CROSS_SIDE_IDENTITY_REF) + 1:] for ref in positional.evidence_refs)
    )


__all__ = (
    "CROSS_SIDE_IDENTITY_REF",
    "CrossSideIdentification",
    "CrossSideIdentityGate",
    "closure_reads_are_full",
    "final_equivalence_identity_gate",
    "owner_free_identity_gate",
    "positional_identity_gate",
    "positional_pairing_gate",
    "positional_parameter_identity_gate",
)
