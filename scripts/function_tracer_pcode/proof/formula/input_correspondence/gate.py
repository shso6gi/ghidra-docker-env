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
  狭い読み・広い読みがあれば拒否する。自由な入力 VARIABLE（束縛された loop 変数以外。graph でも
  runtime ref の中でも）があれば拒否する（名前の一致は対応の証明でない。#248 で scope へ移す）。
* :func:`owner_free_identity_gate` — 上の 2 つの組。owner を含まない同一視をする site はこれだけを
  呼ぶ。relation を渡さなければ現在の比較の relation（``binding.current_relation``）を読み、
  比較の外では通さない（fail-closed）。

拒否は「証明できない」であって、反証ではない。site は計算をせず、保守的な答え（closure を
発行しない、併合しない、lowering しない）へ戻る。

この規則が判定に効く面は 3 つで、どれもここの関数を読む:

* pair の closure: ledger が closure ごとに ``CrossSideIdentification`` を封印し、最終の EQ gate
  （``checker/preflight_gate``）が owner を含まない closure を含む比較に ``final_equivalence_identity_gate``
  を課す（site の gate を漏らした closure の backstop）。
* 比較の証拠（completed recovery proof）: producer が申告し、採用の規則（``binding.evidence_authority_holds``）
  が owner を含まない証拠を位置どおりの relation の下でだけ採用する。blocker の解消（gate の producer・
  ``DecisionAggregator``・replan）は証拠を通してしか起きないので、この採用の規則がそれらの関所になる。
* site の gate: 計算そのものを始めない（無駄を避け、拒否したときの保守的な答えを決める）。

PR-H は、この gate を relation を通した翻訳（``CorrespondenceScope``）に置き換える。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
import hashlib
import secrets
from threading import Lock
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopVariableIdentityRef
from scripts.function_tracer_pcode.core.semantic_freeze import reachable_semantic_values_by_origin
from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import (
    current_comparison,
    current_relation,
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
    無い record は ``OWNER_FREE`` として扱う。
    """

    CORRESPONDENCE = "correspondence"
    OWNER_FREE = "owner_free"


_CERTIFICATE_TOKEN = object()
#: 発行した証明書（process の中だけ）。証拠の record は証明書の id しか持たないので、採用の側は
#: ここで発行済みの証明書を引く。id は乱数を含み、record から作り直せない。
_ISSUED_CERTIFICATES: Dict[str, "CrossSideIdentityCertificate"] = {}
_ISSUED_LOCK = Lock()


@dataclass(frozen=True)
class CrossSideIdentityCertificate:
    """owner を含まない同一視を検査した結果（``certify_owner_free_identity`` だけが発行する）。

    何を検査したか（``subject``）・どの比較（``comparison_digest``）・どの relation
    （``relation_digest``）の下で検査したかを持つ。owner を含まない closure・証拠・query の等式は、
    これを持たないと発行も採用もされない（申告の enum だけでは検査済みにならない）。
    """

    certificate_id: str
    comparison_digest: str
    relation_digest: str
    subject: Tuple[Any, ...]
    _token: Any = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._token is not _CERTIFICATE_TOKEN:
            raise TypeError("cross-side identity certificates are issued only by certify_owner_free_identity")

    def is_issued(self) -> bool:
        with _ISSUED_LOCK:
            return _ISSUED_CERTIFICATES.get(self.certificate_id) is self

    def covers(self, subject: Any, *, comparison_digest: Any, relation_digest: Any = None) -> bool:
        """この証明書が ``subject`` を、その比較（と relation）の下で検査したものか。"""

        return bool(
            self.is_issued()
            and self.subject == subject
            and self.comparison_digest == comparison_digest
            and (relation_digest is None or self.relation_digest == relation_digest)
        )


def issued_certificate(certificate_id: Any) -> Optional[CrossSideIdentityCertificate]:
    """id から発行済みの証明書を引く（無ければ None）。"""

    if type(certificate_id) is not str:
        return None
    with _ISSUED_LOCK:
        return _ISSUED_CERTIFICATES.get(certificate_id)


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


def _is_bound_loop_variable(expr: Expression, inside_runtime_ref: bool) -> bool:
    """loop の summary が束縛した placeholder か（自由な入力ではない）。

    束縛は名前でなく型で表す: recurrence の summarizer は loop の placeholder の VARIABLE に
    ``LoopVariableIdentityRef`` を付け、summary の ref の中にだけ置く。式の graph に現れた
    placeholder は束縛の外へ漏れた値なので、束縛とみなさない。
    """

    return inside_runtime_ref and isinstance(expr.__dict__.get("runtime_ref"), LoopVariableIdentityRef)


def _side_refusals(values: Sequence[Any], rows: Mapping[int, ParameterInfo], side: str) -> Tuple[str, ...]:
    """比べる値に到達できる入力の読み（1 回の走査。runtime ref の中を含む）。

    * PARAMETER: 行の index・名前・全幅で読む。
    * VARIABLE: 束縛された loop 変数のほかは全て自由な入力で、名前の一致は対応の証明でない
      （``in_stack_*``・post-state・未解決の varnode）。graph でも runtime ref の中でも拒否する。
    """

    refs = []
    for value, inside in reachable_semantic_values_by_origin(tuple(values)):
        if not isinstance(value, Expression):
            continue
        if value.expr_type is ExpressionType.PARAMETER:
            refusal = _parameter_read_refusal(value, rows, side)
            if refusal is not None:
                refs.append(refusal)
        elif value.expr_type is ExpressionType.VARIABLE and not _is_bound_loop_variable(value, inside):
            refs.append(f"input_variable:{side}:{value.name}")
    return tuple(refs)


def closure_reads_are_full(
    ics: Any,
    left_values: Sequence[Any],
    right_values: Sequence[Any],
) -> CrossSideIdentityGate:
    """closure が比べる値の PARAMETER の読みが全て行の幅で、入力 VARIABLE が無いか。

    ``left_values`` / ``right_values`` は closure が比べる側ごとの値（式・条件・case・ref を
    含む入れ物）。到達は ``reachable_semantic_values_by_origin``（公開と同じ規則）で、PARAMETER も
    自由な入力 VARIABLE も runtime ref の中まで数える。
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


def certify_owner_free_identity(
    left_values: Sequence[Any],
    right_values: Sequence[Any],
    *,
    subject: Tuple[Any, ...],
) -> CrossSideIdentityGate:
    """``owner_free_identity_gate`` を現在の比較の relation で検査し、通れば証明書を発行する。

    owner を含まない closure・証拠・query の等式を **発行する** site はこれを呼び、結果の証明書を
    発行物に付ける（ledger と証拠の採用が証明書を要求する）。``subject`` は発行物を指す値
    （``("pair_closure", pair_key)``・``("pair_query_assertions", pair_id)``・
    ``("comparison_evidence", object_target_key)``）。比較の外では発行しない。
    """

    comparison = current_comparison()
    if comparison is None:
        return CrossSideIdentityGate.refuse(("relation_unavailable",))
    verdict = owner_free_identity_gate(left_values, right_values, ics=comparison.relation)
    if not verdict.passed:
        return verdict
    if type(subject) is not tuple or not subject:
        raise TypeError("cross-side identity certificate requires a subject tuple")
    nonce = secrets.token_hex(16)
    certificate_id = hashlib.sha256(repr((
        "cross_side_identity_certificate_v1", comparison.digest,
        comparison.input_correspondence_digest, subject, nonce,
    )).encode("utf-8")).hexdigest()
    certificate = CrossSideIdentityCertificate(
        certificate_id, comparison.digest, comparison.input_correspondence_digest, subject,
        _token=_CERTIFICATE_TOKEN,
    )
    with _ISSUED_LOCK:
        _ISSUED_CERTIFICATES[certificate_id] = certificate
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
    "issued_certificate",
    "closure_reads_are_full",
    "final_equivalence_identity_gate",
    "owner_free_identity_gate",
    "positional_identity_gate",
    "positional_pairing_gate",
    "positional_parameter_identity_gate",
)
