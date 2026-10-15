# -*- coding: utf-8 -*-
"""比較に依存する authority の identity と lifetime（Issue #167）。

**Comparison authority 契約**

比較（comparison）に依存する authority（比較の中で作った recovery 証拠、proof
artifact、obligation と gate outcome、pair ledger の closure）は、それが成立した

* raw pair（``StrategySourceAnalysisPair.comparison_digest``: 左右の raw analysis の
  fingerprint。proof 証拠と、比較自身が raw analysis に書き戻す観測の note は入らない）と
* その raw pair に対する最終 ``InputCorrespondence``（``InputCorrespondenceSet.digest``）

の組 ``ComparisonAuthorityBinding`` を値で持ち、採用する側はこの組を値で照合する。

* 同じ raw pair・同じ relation → 共有してよい（pairwise・loop template・monolithic・
  replan の branch どうし）。
* 同じ raw pair・違う relation → 共有しない。
* 違う raw pair（再帰抽象化の抽象 pair、recurrence promotion の後継 pair、型仮説
  後の再解析）・同じ relation → 共有しない。relation の digest は parameter 対応の値
  なので、違う raw pair でも一致し得る。relation digest 単独を比較の identity にしない。

比較ごとの乱数 nonce にはしない（同じ raw pair・同じ relation の branch 間共有を壊す）。

**owner と経路**

* raw pair の identity の規則は ``proof/obligations/snapshot.py`` の
  ``comparison_pair_identity``（左右の ``comparison_fingerprint``）だけで、raw pair の owner
  （``StrategySourceAnalysisPair.comparison_digest``）と obligation runtime（``raw_pair_digest``）
  はこれを使う。それと relation の組 ``ComparisonAuthorityBinding`` の生成と照合はこの module だけが
  行う。比較が raw analysis に書き戻す観測（``record_comparison_annotation``）は raw pair
  の identity を変えない。それ以外の変化で raw pair が変われば、以後は別の比較になる。
* 比較の範囲: ``comparison_scope(binding)`` が 1 つの比較の間だけ現在の binding を
  与える。開くのは dispatch 境界（``checker/strategy_execution.run_strategy_branch``）
  と、branch の結果をその結果を作った比較で扱う境界（``proof/obligations/stage_runner``
  の gate と集約、``checker/attempts`` の完了記録）。strategy は入口で frame の binding
  と範囲の binding の一致を確かめる（互換の直接呼び出しは自分の binding の範囲を開いて
  実行し直す）。入れ子の比較は自分の binding を push し、抜けると戻る。
* 証拠: record は authority scope を明示する（``core/evidence_authority.py``）。
  proof 層は ``store_comparison_evidence`` だけで書き、比較の中で増えた record は
  ``comparison`` scope とその比較の binding digest を持つ。gate は
  ``comparison_evidence`` を通してだけ読み、``function_unary`` の record と、binding が
  現在の比較と一致する ``comparison`` の record だけを採用する。scope の無い record、
  比較の外で作った record は採用しない（fail-closed）。
* 後で実行する仕事: worklist の producer / replanner は ``run_in_current_comparison`` で
  登録時の範囲を持ち運ぶ。
* obligation runtime: 1 つの runtime は 1 つの binding の比較だけに仕える
  （``ObligationRuntimeSession.claim_comparison``）。stage runner の runtime は runner 自身の
  raw pair の比較のために予約する（``reserve_for_its_raw_pair``）。artifact・view・dependency・producer・
  replanner・outcome・cache は runtime の state なので、binding が違う比較とは共有されない。
  gate の計画・完了証拠の適用・outcome の読み出しは仕える比較の中でだけ行う。別の比較は
  自分の runtime を使い（``prepare_strategy_runtime``）、stage runner はその結果の runtime で
  gate と集約を行い、replan は runner 自身の比較の結果だけに行う。
* pair ledger: ``PairLedgerBinding.comparison_authority_digest`` が ledger の closure の
  前提になった binding で、validator と closure の検証は現在の比較と照合する。
"""

from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
import hashlib
from typing import Any, Callable, Iterable, Iterator, List, Mapping, MutableMapping, Optional, Tuple

from scripts.function_tracer_pcode.core.evidence_authority import (
    AUTHORITY_SCOPE_KEY,
    COMPARISON,
    COMPARISON_AUTHORITY_KEY,
    FUNCTION_UNARY,
    evidence_authority_scope,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence.model import (
    InputCorrespondenceSet,
)


#: 比較の外で作った comparison record の印（どの binding の digest とも一致しない）。
OUTSIDE_COMPARISON = "outside_comparison"

#: 比較の証拠が左右の値をどう同一視したか（``gate.CrossSideIdentification`` の値）。書いた
#: producer が申告する。申告の無い record・知らない値の record は採用しない（plan v4 PR-P）。
CROSS_SIDE_IDENTIFICATION_KEY = "cross_side_identification"
#: owner を含まない証拠が持つ、検査の証明書（``gate.CrossSideIdentityCertificate``）の id。
CROSS_SIDE_IDENTITY_CERTIFICATE_KEY = "cross_side_identity_certificate"


def comparison_evidence_subject(object_target_key: Any) -> Tuple[Any, ...]:
    """対象 ``object_target_key`` の証拠の左右の同一視を検査した証明書が指す値。"""

    return ("comparison_evidence", object_target_key)


def evidence_identity_subject(record: Mapping[str, Any]) -> Tuple[Any, ...]:
    """証拠 ``record`` の左右の同一視を検査した証明書が指す値（record の対象）。"""

    return comparison_evidence_subject(record.get("object_target_key"))


def _is_digest(value: Any) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(ch in "0123456789abcdef" for ch in value)


@dataclass(frozen=True)
class ComparisonAuthorityBinding:
    """比較に依存する authority の identity: raw pair と、その最終 relation の組。"""

    #: 比べている raw pair の identity（``StrategySourceAnalysisPair.comparison_digest``）。
    raw_pair_digest: str
    input_correspondence_digest: str
    #: 照合には使わない（値は digest が表す）。gate が relation から値を導き直すために持つ。
    relation: InputCorrespondenceSet = field(compare=False, repr=False)

    def __post_init__(self) -> None:
        if not _is_digest(self.raw_pair_digest):
            raise ValueError("comparison authority requires the raw pair digest")
        if type(self.relation) is not InputCorrespondenceSet:
            raise TypeError("comparison authority requires the final InputCorrespondenceSet")
        if self.input_correspondence_digest != self.relation.digest:
            raise ValueError("comparison authority relation digest does not match the relation")

    @classmethod
    def of(cls, source_pair: Any, relation: InputCorrespondenceSet) -> "ComparisonAuthorityBinding":
        """raw pair（``StrategySourceAnalysisPair``）とその最終 relation の binding。"""

        if type(relation) is not InputCorrespondenceSet:
            raise TypeError("comparison authority requires the final InputCorrespondenceSet")
        return cls(str(getattr(source_pair, "comparison_digest", "")), relation.digest, relation)

    @property
    def digest(self) -> str:
        return hashlib.sha256(repr((
            "comparison_authority_v1",
            self.raw_pair_digest,
            self.input_correspondence_digest,
        )).encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class _ComparisonScope:
    """1 つの比較の範囲（``binding`` が None なら、binding を与えられない比較）。"""

    binding: Optional[ComparisonAuthorityBinding]


_CURRENT_COMPARISON: ContextVar[Optional[_ComparisonScope]] = ContextVar(
    "current_comparison_authority", default=None
)


@contextmanager
def comparison_scope(binding: Optional[ComparisonAuthorityBinding]) -> Iterator[None]:
    """1 つの比較の間、``binding`` をその比較の authority にする。

    ``None`` は「比較の binding を確定できない」範囲で、comparison の証拠をどれも
    採用しない（外側の比較の binding も引き継がない）。
    """

    if binding is not None and type(binding) is not ComparisonAuthorityBinding:
        raise TypeError("comparison scope requires a ComparisonAuthorityBinding")
    token = _CURRENT_COMPARISON.set(_ComparisonScope(binding))
    try:
        yield
    finally:
        _CURRENT_COMPARISON.reset(token)


class ComparisonBoundCallable:
    """登録した比較の範囲の下で実行する callable（``run_in_current_comparison``）。"""

    __slots__ = ("_callback", "_scope")

    def __init__(self, callback: Callable[..., Any], scope: Optional[_ComparisonScope]) -> None:
        self._callback = callback
        self._scope = scope

    @property
    def binding(self) -> Optional[ComparisonAuthorityBinding]:
        return None if self._scope is None else self._scope.binding

    def __call__(self, *args: Any, **kwargs: Any) -> Any:
        token = _CURRENT_COMPARISON.set(self._scope)
        try:
            return self._callback(*args, **kwargs)
        finally:
            _CURRENT_COMPARISON.reset(token)


def run_in_current_comparison(callback: Callable[..., Any]) -> ComparisonBoundCallable:
    """後で実行する ``callback`` を、登録した比較の範囲の下で実行する形にする。

    worklist の producer や replanner は、それを作った比較が終わった後に別の範囲から
    実行されることがある。実行時の範囲ではなく登録時の範囲で照合する。既に束縛済みなら
    そのまま（最初に登録した比較を保つ）。
    """

    if isinstance(callback, ComparisonBoundCallable):
        return callback
    return ComparisonBoundCallable(callback, _CURRENT_COMPARISON.get())


def current_comparison() -> Optional[ComparisonAuthorityBinding]:
    """現在の比較の binding（比較の外、binding の無い比較では None）。"""

    scope = _CURRENT_COMPARISON.get()
    return None if scope is None else scope.binding


def current_relation() -> Optional[InputCorrespondenceSet]:
    """現在の比較の最終 relation（比較の外、binding の無い比較では None）。"""

    binding = current_comparison()
    return None if binding is None else binding.relation


def comparison_is_current(binding: Optional[ComparisonAuthorityBinding]) -> bool:
    """``binding`` が現在の比較の binding と値で一致するか（どちらかが無ければ偽）。"""

    current = current_comparison()
    return current is not None and binding is not None and binding == current


def comparison_digest_is_current(digest: Any) -> bool:
    """``digest``（``ComparisonAuthorityBinding.digest``）が現在の比較のものか。"""

    current = current_comparison()
    return current is not None and isinstance(digest, str) and digest == current.digest


def relation_digest_is_current(digest: Any) -> bool:
    """``digest`` が現在の比較の最終 relation の digest と値で一致するか。"""

    current = current_comparison()
    return current is not None and isinstance(digest, str) and digest == current.input_correspondence_digest


def comparison_authority_digest() -> str:
    """現在の比較の binding digest（比較の外・binding の無い比較では、どれとも一致しない値）。"""

    binding = current_comparison()
    return OUTSIDE_COMPARISON if binding is None else binding.digest


def _identification_value(identification: Any) -> Optional[str]:
    if identification is None:
        return None
    from scripts.function_tracer_pcode.proof.formula.input_correspondence.gate import (
        CrossSideIdentification,
    )

    if type(identification) is not CrossSideIdentification:
        raise TypeError("comparison evidence identification must be a CrossSideIdentification")
    return identification.value


def bind_evidence_to_comparison(
    record: MutableMapping[str, Any],
    binding: Optional[ComparisonAuthorityBinding] = None,
    *,
    identification: Any = None,
    certificate: Any = None,
) -> MutableMapping[str, Any]:
    """比較の中で作った証拠 ``record`` を、その比較（既定は現在の比較）に束縛する。

    ``identification``（``gate.CrossSideIdentification``）は record が左右の値をどう同一視
    したかの申告。``None`` は申告なしで、採用されない（関数単体の事実は ``mark_function_unary``）。
    ``OWNER_FREE`` は、この比較で record の対象（``evidence_identity_subject``）を検査した証明書
    （``certificate``）を必須にする。
    """

    if record.get(AUTHORITY_SCOPE_KEY) == FUNCTION_UNARY:
        raise ValueError("a function-unary record cannot be bound to a comparison")
    binding = binding if binding is not None else current_comparison()
    value = _identification_value(identification)
    certificate_id = _certificate_id_for(record, binding, value, certificate)
    record[AUTHORITY_SCOPE_KEY] = COMPARISON
    record[COMPARISON_AUTHORITY_KEY] = OUTSIDE_COMPARISON if binding is None else binding.digest
    record.pop(CROSS_SIDE_IDENTIFICATION_KEY, None)
    record.pop(CROSS_SIDE_IDENTITY_CERTIFICATE_KEY, None)
    if value is not None:
        record[CROSS_SIDE_IDENTIFICATION_KEY] = value
    if certificate_id is not None:
        record[CROSS_SIDE_IDENTITY_CERTIFICATE_KEY] = certificate_id
    return record


def _certificate_id_for(
    record: Mapping[str, Any],
    binding: Optional[ComparisonAuthorityBinding],
    value: Optional[str],
    certificate: Any,
) -> Optional[str]:
    from scripts.function_tracer_pcode.proof.formula.input_correspondence.gate import (
        CrossSideIdentification,
        CrossSideIdentityCertificate,
    )

    if value != CrossSideIdentification.OWNER_FREE.value:
        if certificate is not None:
            raise ValueError("only owner-free comparison evidence carries a cross-side identity certificate")
        return None
    if (
        type(certificate) is not CrossSideIdentityCertificate
        or binding is None
        or not certificate.covers(
            evidence_identity_subject(record),
            comparison_digest=binding.digest,
            relation_digest=binding.input_correspondence_digest,
        )
    ):
        raise ValueError("owner-free comparison evidence requires the certificate of its own subject")
    return certificate.certificate_id


def store_comparison_evidence(
    analysis: Any, records: Iterable[Any], *, identification: Any, certificate: Any = None,
) -> None:
    """比較の中で ``analysis`` の証拠列を ``records`` に置き換える（proof 層の唯一の書き込み口）。

    それまでの列に無かった record で authority scope を持たないものは、現在の比較に
    束縛する（producer が束縛を忘れても、比較の中で増えた証拠は必ず束縛される）。
    それまでの列にあった record（関数単体の事実や、別の比較の証拠）はそのまま残す。

    ``identification`` は producer の申告（必須の引数。新しく束縛する record にだけ付く）。
    左右の値を owner を含まない key で比べて作った証拠は ``OWNER_FREE`` で、その比較で
    ``certify_owner_free_identity`` が record の対象に発行した ``certificate`` を必須にする（無ければ
    束縛せずに ``ValueError``）。片側だけの証明や relation の premise の下の SMT は
    ``CORRESPONDENCE``。別の場所で作った record を運ぶだけの呼び手は ``None``（申告なし ⇒ 採用
    されない）を明示する。
    """

    existing = tuple(getattr(analysis, "completed_recovery_proof_evidence", ()) or ())
    stored = []
    for record in records or ():
        if (
            isinstance(record, MutableMapping)
            and evidence_authority_scope(record) is None
            and record not in existing
        ):
            bind_evidence_to_comparison(record, identification=identification, certificate=certificate)
        stored.append(record)
    analysis.completed_recovery_proof_evidence = tuple(stored)


def evidence_authority_holds(record: Any) -> bool:
    """証拠 ``record`` を現在の比較で採用してよいか（照合の唯一の実装）。

    関数単体の事実はどの比較でも採用する。比較の証拠は、束縛した binding が現在の比較と
    値で一致するときだけ採用する。scope の無い record は採用しない。
    """

    scope = evidence_authority_scope(record)
    if scope == FUNCTION_UNARY:
        return True
    if scope == COMPARISON:
        if not comparison_digest_is_current(record.get(COMPARISON_AUTHORITY_KEY)):
            return False
        return _identification_is_justified(record)
    return False


def _identification_is_justified(record: Mapping[str, Any]) -> bool:
    """比較の証拠の左右の同一視が、現在の比較の relation の下で成り立つか（plan v4 PR-P）。

    relation の premise の下の証拠（``CORRESPONDENCE``）はそのまま採用する。owner を含まない
    証拠は、この比較・この relation の下で record の対象を検査した、発行済みの証明書を持つときだけ
    採用する（申告だけ・申告なし・知らない値は採用しない）。証拠を読む全ての gate（blocker の解消・
    recovery closure の検証・replan）はこの採用規則を通る。
    """

    from scripts.function_tracer_pcode.proof.formula.input_correspondence.gate import (
        CrossSideIdentification,
        issued_certificate,
        positional_identity_gate,
    )

    value = record.get(CROSS_SIDE_IDENTIFICATION_KEY)
    if value == CrossSideIdentification.CORRESPONDENCE.value:
        return True
    if value != CrossSideIdentification.OWNER_FREE.value:
        return False
    current = current_comparison()
    certificate = issued_certificate(record.get(CROSS_SIDE_IDENTITY_CERTIFICATE_KEY))
    return bool(
        current is not None
        and certificate is not None
        and certificate.covers(
            evidence_identity_subject(record),
            comparison_digest=current.digest,
            relation_digest=current.input_correspondence_digest,
        )
        and positional_identity_gate(current.relation).passed
    )


def comparison_evidence(records: Iterable[Any]) -> Tuple[Mapping[str, Any], ...]:
    """``records`` のうち、現在の比較で採用してよい証拠。"""

    return tuple(record for record in records or () if evidence_authority_holds(record))


def _frozen(value: Any) -> Any:
    if isinstance(value, (list, tuple)):
        return tuple(_frozen(item) for item in value)
    return value


def _merge_identity(record: Mapping[str, Any]) -> Tuple[Any, Any, Any]:
    """証拠を合流するときの同一性（同じ proof でも authority が違えば別の証拠）。"""

    return (
        _frozen(record.get("proof_obligation_id")),
        record.get(AUTHORITY_SCOPE_KEY),
        record.get(COMPARISON_AUTHORITY_KEY),
    )


def merge_new_evidence(
    existing: Iterable[Any], incoming: Iterable[Any]
) -> Optional[List[dict]]:
    """``existing`` に ``incoming`` の新しい証拠を足した列（増えなければ None）。

    record の authority（scope と binding）はそのまま持ち込む。
    """

    records = [dict(record) for record in existing or () if isinstance(record, Mapping)]
    seen = {
        _merge_identity(record)
        for record in records
        if record.get("proof_obligation_id") is not None
    }
    changed = False
    for record in incoming or ():
        if not isinstance(record, Mapping):
            continue
        identity = _merge_identity(record)
        if identity[0] is not None and identity in seen:
            continue
        records.append(dict(record))
        if identity[0] is not None:
            seen.add(identity)
        changed = True
    return records if changed else None
