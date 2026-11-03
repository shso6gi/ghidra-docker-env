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
  狭い読み・広い読みがあれば拒否する。自由な入力 VARIABLE があれば拒否する（名前の一致は対応の証明で
  ない。#248 で scope へ移す）。
* :func:`owner_free_identity_gate` — 上の 2 つの組（pair 全体の述語が先。適用は ``_owner_free_reading``
  の 1 つ）。relation を渡さなければ現在の比較の relation を読み、比較の外では通さない（fail-closed）。
* :func:`certify_owner_free_identity` — owner を含まない同一視を **発行する** site が呼ぶ唯一の入口。
  同じ規則で検査し、通れば証明書（``certificates.CrossSideIdentityCertificate``）を出す。証明書は比較・
  relation・発行物の対象と、**読んだ値そのもの**（不変の意味値の列）を記録し、発行物を作る側・証拠を
  読む側が示す値を ``attests`` で照合する。持ち主は比較の実行の session で、実行が終わると失効する。

**loop 変数の束縛**は名前・型・「ref の中にある」ことでは決めない。束縛を持つ ref（loop の case・状態
遷移の summary）が ``loop_binder_scope()`` で binder と、それが効く field を宣言し、走査
（``core/semantic_freeze.reachable_semantic_values_in_binder_scope``）は宣言した field を通って届いた
位置にだけ束縛の文脈を渡す（外側の文脈は内側でも有効）。VARIABLE は、loop 変数の型を持ち、その位置で
有効な binder と ``equals`` で一致するときだけ束縛された変数。それ以外（別の loop の placeholder・
束縛の外の field・漏れた placeholder）は自由な入力として拒否する。

拒否は「証明できない」であって、反証ではない。site は計算をせず、保守的な答え（closure を
発行しない、併合しない、lowering しない）へ戻る。

この規則が判定に効く面は 3 つで、どれも証明書を要求する（呼び手の注意に頼らない）:

* pair の closure: producer の closure・名前で比べる構造の等価は、その pair の証明書と、証明が読んだ
  値（``checked_values``）なしに発行できない。owner を含まない query の等式は、証明書が検査した値から
  ``derive_owner_free_pair_assertions`` だけが作る。ledger（``PairClosureEvidence``・
  ``record_pair_closed``）が証明書を封印・照合し、最終の EQ gate（``orchestration.
  veto_unproven_cross_side_identity``）が relation と証明書をもう一度照合する。
* 比較の証拠（completed recovery proof）: owner を含まない証拠は、その証拠を作った値を検査した証明書と
  一緒にだけ束縛でき、採用（``binding.evidence_authority_holds``）は読む側が示した値（``binding.
  owner_free_evidence_values``）を証明書が検査したときだけ。同じ ``object_target_key`` でも別の pair・
  別の branch の値には使えない。値を示さない読み手は採用しない。
* site の検査: 計算そのものを始めない（無駄を避け、拒否したときの保守的な答えを決める）。

PR-H は、この gate を relation を通した翻訳（``CorrespondenceScope``）に置き換える。
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Iterable, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopVariableIdentityRef
from scripts.function_tracer_pcode.core.semantic_freeze import reachable_semantic_values_in_binder_scope
from scripts.function_tracer_pcode.core.semantic_lifecycle import is_validated
from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import (
    current_comparison,
    current_relation,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence.certificates import (
    CrossSideIdentityCertificate,
    issue_certificate,
    issued_certificate,
)
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
    無い・知らない値の record は採用しない。
    """

    CORRESPONDENCE = "correspondence"
    OWNER_FREE = "owner_free"


@dataclass(frozen=True)
class CrossSideIdentityGate:
    """gate の答え。``passed`` が偽なら ``evidence_refs`` が拒否の理由を持つ。

    ``certify_owner_free_identity`` が通したときだけ ``certificate`` を持つ。
    """

    passed: bool
    evidence_refs: Tuple[str, ...] = ()
    certificate: Optional[CrossSideIdentityCertificate] = None

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


def _is_bound_loop_variable(expr: Expression, frame: Any) -> bool:
    """この位置で有効な束縛の binder か（自由な入力ではない）。

    束縛は名前・型・「ref の中にある」ことでは決めない: loop 変数の型（``LoopVariableIdentityRef``）を
    持ち、届いた位置で有効な binder（宣言した ref の scope の field を通って届いたときだけ有効。
    ``runtime_refs.loops`` の ``loop_binder_scope``）のどれかと同じ binder のときだけ束縛。

    同じ binder とは、``equals`` で一致し（consumer が placeholder を置き換えるときの規則）、**型の object が
    同じ**こと: producer は loop ごとに ``LoopVariableIdentityRef`` を 1 つ作り、その loop の placeholder は
    全てそれを持つ。key（``varnode_key`` など）は左右の summary を alpha-renaming で突き合わせるための値で、
    同じ場所が作った別の loop の placeholder とも一致し得るので、束縛の根拠にしない。
    """

    tag = expr.__dict__.get("runtime_ref")
    if not isinstance(tag, LoopVariableIdentityRef):
        return False
    return any(
        binder is expr
        or (
            isinstance(binder, Expression)
            and binder.__dict__.get("runtime_ref") is tag
            and binder.equals(expr)
        )
        for binder in frame.binders_in_scope()
    )


def _side_state_ref_types() -> Tuple[type, ...]:
    from scripts.function_tracer_pcode.core.runtime_refs import (
        ObservedMemoryReadRef,
        PostStateReadRef,
        ReadonlyReductionRef,
        ReadonlyReductionTermRef,
    )

    return (ObservedMemoryReadRef, PostStateReadRef, ReadonlyReductionRef, ReadonlyReductionTermRef)


def side_state_kinds(value: Expression) -> Tuple[str, ...]:
    """node 1 つが表す、側ごとの状態の種類（`proof.formula.memory_state` と同じ規則）。"""

    from scripts.function_tracer_pcode.proof.formula.memory_state import _node_kinds

    return tuple(_node_kinds(value))


def _read_side(values: Sequence[Any], rows: Mapping[int, ParameterInfo], side: str) -> Tuple[Tuple[str, ...], Tuple[Any, ...]]:
    """比べる値の読み（1 回の走査。runtime ref の中と束縛の文脈を含む）の拒否と、読んだ値の列。

    * PARAMETER: 行の index・名前・全幅で読む。
    * VARIABLE: その位置で有効な束縛の binder のほかは全て自由な入力で、名前の一致は対応の証明でない
      （``in_stack_*``・post-state・未解決の varnode・別の loop の placeholder）。
    読んだ値と、その位置で有効な binder の組の列（走査の順）は証明書が記録し、``attests`` が同じ走査で
    照合する。
    """

    refs = []
    surface = []
    for value, frame in reachable_semantic_values_in_binder_scope(tuple(values)):
        surface.append((value, frame.binders_in_scope()))
        if not isinstance(value, Expression):
            if isinstance(value, _SIDE_STATE_REF_TYPES):
                refs.append(f"memory_uncorresponded:{side}:{type(value).__name__}")
            continue
        if value.expr_type is ExpressionType.PARAMETER:
            refusal = _parameter_read_refusal(value, rows, side)
            if refusal is not None:
                refs.append(refusal)
        elif value.expr_type is ExpressionType.VARIABLE and not _is_bound_loop_variable(value, frame):
            refs.append(f"input_variable:{side}:{value.name}")
        else:
            # Issue #282 (I1): その側の memory・image の object の番地・memory に依存する関数の値は、左右で同じ
            # 構造でも同じ値とは言えない（owner の表に対応の根拠が無い）
            for kind in side_state_kinds(value):
                refs.append(f"memory_uncorresponded:{side}:{kind}")
    return tuple(refs), tuple(surface)


_SIDE_STATE_REF_TYPES = _side_state_ref_types()


def checked_surface(values: Sequence[Any]) -> Tuple[Tuple[Any, Tuple[Any, ...]], ...]:
    """gate が ``values`` から読む意味値と、その位置で有効な binder の組の列（証明書の ``attests`` が使う。
    ``_read_side`` と同じ走査）。同じ値でも束縛の文脈が違えば別の読み（束縛された変数と自由な入力）。"""

    return tuple(
        (value, frame.binders_in_scope())
        for value, frame in reachable_semantic_values_in_binder_scope(tuple(values))
    )


def closure_reads_are_full(
    ics: Any,
    left_values: Sequence[Any],
    right_values: Sequence[Any],
) -> CrossSideIdentityGate:
    """closure が比べる値の PARAMETER の読みが全て行の幅で、入力 VARIABLE が無いか。

    ``left_values`` / ``right_values`` は closure が比べる側ごとの値（式・条件・case・ref を
    含む入れ物）。到達は ``reachable_semantic_values_in_binder_scope``（公開と同じ規則に束縛の文脈を
    足したもの）で、PARAMETER も自由な入力 VARIABLE も runtime ref の中まで数える。
    """

    if type(ics) is not InputCorrespondenceSet:
        return CrossSideIdentityGate.refuse(("relation_unavailable",))
    left_refs, _left_surface = _read_side(left_values, _side_rows(ics, LEFT), LEFT)
    right_refs, _right_surface = _read_side(right_values, _side_rows(ics, RIGHT), RIGHT)
    if left_refs or right_refs:
        return CrossSideIdentityGate.refuse(left_refs + right_refs)
    return CrossSideIdentityGate.accept()


def _owner_free_reading(
    relation: Any, left_values: Sequence[Any], right_values: Sequence[Any],
) -> Tuple[Tuple[str, ...], Tuple[Any, ...], Tuple[Any, ...]]:
    """owner を含まない同一視の規則の唯一の適用: pair 全体の述語が先で、通ったときだけ局所の読み。

    返すのは（拒否の理由, 左で読んだ値の列, 右で読んだ値の列）。
    """

    positional = positional_identity_gate(relation)
    if not positional.passed:
        return tuple(ref[len(CROSS_SIDE_IDENTITY_REF) + 1:] for ref in positional.evidence_refs), (), ()
    left_refs, left_surface = _read_side(left_values, _side_rows(relation, LEFT), LEFT)
    right_refs, right_surface = _read_side(right_values, _side_rows(relation, RIGHT), RIGHT)
    return left_refs + right_refs, left_surface, right_surface


def owner_free_identity_gate(
    left_values: Sequence[Any],
    right_values: Sequence[Any],
    *,
    ics: Any = _CURRENT_RELATION,
) -> CrossSideIdentityGate:
    """owner を含まない key で ``left_values`` と ``right_values`` を同一視してよいか（判定だけ）。

    ``ics`` を省くと現在の比較の最終 relation を使う（比較の外では relation が無いので拒否）。
    発行物を作る site はこれでなく ``certify_owner_free_identity`` を呼ぶ。
    """

    relation = current_relation() if ics is _CURRENT_RELATION else ics
    refs, _left, _right = _owner_free_reading(relation, left_values, right_values)
    if refs:
        return CrossSideIdentityGate.refuse(refs)
    return CrossSideIdentityGate.accept()


def certify_owner_free_identity(
    left_values: Sequence[Any],
    right_values: Sequence[Any],
    *,
    subject: Tuple[Any, ...],
) -> CrossSideIdentityGate:
    """現在の比較の relation で ``left_values`` / ``right_values`` を検査し、通れば証明書を発行する。

    owner を含まない closure・証拠・query の等式を **発行する** site が呼ぶ唯一の入口。証明書は
    比較・relation・``subject`` と、ここで読んだ値の列を記録する（``certificates``）。発行物を作る側は、
    発行物の入力そのものを ``attests`` で照合させる（同じ ``subject`` でも別の値には使えない）。
    比較の外・証明書の session の外では発行しない。
    """

    comparison = current_comparison()
    if comparison is None:
        return CrossSideIdentityGate.refuse(("relation_unavailable",))
    refs, left_surface, right_surface = _owner_free_reading(comparison.relation, left_values, right_values)
    if refs:
        return CrossSideIdentityGate.refuse(refs)
    # 証明書は読んだ値そのものを記録する。検査の後で変わり得る値（不変でない意味値）は記録できない。
    mutable = tuple(
        f"checked_value_not_frozen:{side}"
        for side, surface in ((LEFT, left_surface), (RIGHT, right_surface))
        if any(isinstance(value, (Expression, Condition)) and not is_validated(value) for value, _binders in surface)
    )
    if mutable:
        return CrossSideIdentityGate.refuse(mutable)
    certificate = issue_certificate(
        comparison_digest=comparison.digest,
        relation_digest=comparison.input_correspondence_digest,
        subject=subject,
        checked=(left_surface, right_surface),
        surface_of=checked_surface,
    )
    if certificate is None:
        return CrossSideIdentityGate.refuse(("certificate_session_unavailable",))
    return CrossSideIdentityGate(True, (), certificate)


def final_equivalence_identity_gate(
    owner_free_sources: Sequence[Tuple[str, Any]],
    ics: Any,
) -> CrossSideIdentityGate:
    """最終の EQ gate（backstop）: owner を含まない方法で閉じた部分がある比較を検査し直す。

    ``owner_free_sources`` は EQ の根拠のうち owner を含まない方法で左右を同一視したものと、その
    検査の証明書の組（ledger の ``owner_free_closures``）。無ければ全て relation の premise の下の
    SMT なので通す。あれば、比較の relation が pair 全体の述語を満たし、全ての証明書が発行済みで
    同じ relation の下で発行されたときだけ通す。site の gate を漏らした closure も、ここで止まる。
    """

    sources = tuple(owner_free_sources)
    if not sources:
        return CrossSideIdentityGate.accept()
    labels = tuple(str(label) for label, _certificate in sources)
    positional = positional_identity_gate(ics)
    refs = [] if positional.passed else [
        ref[len(CROSS_SIDE_IDENTITY_REF) + 1:] for ref in positional.evidence_refs
    ]
    relation_digest = getattr(ics, "digest", None) if type(ics) is InputCorrespondenceSet else None
    for label, certificate in sources:
        if (
            type(certificate) is not CrossSideIdentityCertificate
            or not certificate.is_issued()
            or certificate.relation_digest != relation_digest
        ):
            refs.append(f"certificate_missing:{label}")
    if not refs:
        return CrossSideIdentityGate.accept()
    return CrossSideIdentityGate.refuse((f"owner_free_source:{labels[0]}", *refs))


__all__ = (
    "CROSS_SIDE_IDENTITY_REF",
    "CrossSideIdentification",
    "CrossSideIdentityCertificate",
    "CrossSideIdentityGate",
    "certify_owner_free_identity",
    "checked_surface",
    "issued_certificate",
    "closure_reads_are_full",
    "final_equivalence_identity_gate",
    "owner_free_identity_gate",
    "positional_identity_gate",
    "positional_pairing_gate",
    "positional_parameter_identity_gate",
)
