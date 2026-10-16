# -*- coding: utf-8 -*-
"""左右の同一視の検査の証明書: 何を検査したか・誰が持つか・いつ失効するか（plan v4 PR-P）。

``gate.certify_owner_free_identity`` が検査に通した値に対して発行する。規則（何を検査するか）は
``gate.py``、証明書の発行・照合・寿命はこの module が持つ（変更の軸が違う）。

* **何を検査したか**: 証明書は、比較の digest・relation の digest・発行物の対象（``subject``）と、
  側ごとに gate が読んだ意味値とその位置で有効な loop 変数の binder の組の列（object の identity。
  証明書が強参照で持つ）を記録する。読んだ値は全て不変（VALIDATED / PUBLISHED）でなければ発行しない。
  ``attests(left, right)`` は、同じ走査で ``left`` / ``right`` から届く列が記録と同じ object・同じ
  束縛の文脈・同じ並びかを確かめる。別の pair・別の
  branch の analysis・付け替えた case の属性・別の view の値は、同じ ``subject`` でも通らない。digest は
  id と封印にだけ使い、検査対象の一致には使わない。
* **誰が持つか**: 証明書は ``CertificateSession`` が持つ。session は 1 つの pair の比較の実行の間だけ
  開く（持ち主は workflow の ``run_check_from_binaries``（全 phase・retry・branch・最終 gate を含む）。
  checker を直接呼ぶ経路は strategy の branch（``run_strategy_branch`` / ``run_legacy_strategy``）、
  strategy を直接呼ぶ経路は frame の無い pairwise の check。いちばん外側が持ち主）。
  入れ子の実行は外側の session を使う（再入）。後で実行する仕事
  （worklist の producer / replanner）は ``binding.run_in_current_comparison`` が session も一緒に運ぶ。
* **いつ失効するか**: いちばん外側の実行が終わると session を閉じ、全ての証明書を失効させて台帳を
  空にする。閉じた session・今の実行でない session（複製を含む）の証明書は、無い証明書と同じに
  拒否される。

証明書を作れるのは ``issue_certificate`` だけで、これを呼ぶのは ``gate.certify_owner_free_identity``
だけ（静的 test が固定する）。``dataclasses.replace``・``copy`` で作り直した object は台帳に載らないので
通らない（fail-closed）。
"""

from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
import hashlib
import secrets
from typing import Any, Callable, Dict, Iterator, Optional, Sequence, Tuple


_CERTIFICATE_TOKEN = object()


class CertificateSession:
    """1 つの比較の実行の間、発行した証明書を持つ owner。"""

    __slots__ = ("_registry", "_open")

    def __init__(self) -> None:
        self._registry: Dict[str, "CrossSideIdentityCertificate"] = {}
        self._open = True

    @property
    def is_open(self) -> bool:
        return self._open

    def __len__(self) -> int:
        return len(self._registry)

    def holds(self, certificate: Any) -> bool:
        return (
            self._open
            and type(certificate) is CrossSideIdentityCertificate
            and self._registry.get(certificate.certificate_id) is certificate
        )

    def lookup(self, certificate_id: Any) -> Optional["CrossSideIdentityCertificate"]:
        if not self._open or type(certificate_id) is not str:
            return None
        return self._registry.get(certificate_id)

    def _register(self, certificate: "CrossSideIdentityCertificate") -> None:
        if not self._open:
            raise RuntimeError("certificate session is closed")
        self._registry[certificate.certificate_id] = certificate

    def close(self) -> None:
        """全ての証明書を失効させ、台帳を空にする（強参照を手放す）。"""

        self._open = False
        self._registry.clear()


_CURRENT_SESSION: ContextVar[Optional[CertificateSession]] = ContextVar(
    "cross_side_identity_certificate_session", default=None
)


@contextmanager
def certificate_session() -> Iterator[CertificateSession]:
    """証明書の session を開く。既に開いていればそれを使う（入れ子の実行は外側と共有する）。"""

    current = _CURRENT_SESSION.get()
    if current is not None and current.is_open:
        yield current
        return
    session = CertificateSession()
    token = _CURRENT_SESSION.set(session)
    try:
        yield session
    finally:
        _CURRENT_SESSION.reset(token)
        session.close()


def current_certificate_session() -> Optional[CertificateSession]:
    session = _CURRENT_SESSION.get()
    return session if session is not None and session.is_open else None


@contextmanager
def entered_certificate_session(session: Optional[CertificateSession]) -> Iterator[None]:
    """後で実行する仕事が、登録したときの session の下で動くための入口（``binding`` が使う）。"""

    token = _CURRENT_SESSION.set(session)
    try:
        yield
    finally:
        _CURRENT_SESSION.reset(token)


#: gate が読んだ値（不変）と、その位置で有効な loop 変数の binder の組を、読んだ順に並べたもの。
CheckedSurface = Tuple[Tuple[Any, Tuple[Any, ...]], ...]


@dataclass(frozen=True, eq=False)
class CrossSideIdentityCertificate:
    """owner を含まない同一視を検査した結果。

    ``checked`` は側ごとに gate が読んだ意味値の列（identity で比べる）。``surface_of`` は
    発行した gate の走査で、``attests`` が同じ走査を値に当てる（走査を 2 つにしない）。
    """

    certificate_id: str
    comparison_digest: str
    relation_digest: str
    subject: Tuple[Any, ...]
    checked: Tuple[CheckedSurface, CheckedSurface] = field(repr=False)
    surface_of: Callable[[Sequence[Any]], Optional[CheckedSurface]] = field(repr=False)
    session: CertificateSession = field(repr=False)
    _token: Any = field(default=None, repr=False)

    def __post_init__(self) -> None:
        if self._token is not _CERTIFICATE_TOKEN:
            raise TypeError("cross-side identity certificates are issued only by certify_owner_free_identity")

    def is_issued(self) -> bool:
        """今の実行の session が発行し、その台帳に載っているこの object か。

        session は identity で比べる（複製した session・別の実行の session の証明書は通らない）。
        """

        session = current_certificate_session()
        return session is not None and session is self.session and session.holds(self)

    def covers(self, subject: Any, *, comparison_digest: Any, relation_digest: Any = None) -> bool:
        """``subject`` を、その比較（と relation）の下で検査したものか（値の一致は ``attests``）。"""

        return bool(
            self.is_issued()
            and self.subject == subject
            and self.comparison_digest == comparison_digest
            and (relation_digest is None or self.relation_digest == relation_digest)
        )

    def attests(self, left_values: Sequence[Any], right_values: Sequence[Any]) -> bool:
        """``left_values`` / ``right_values`` が、検査した値そのもの（同じ object の同じ並び）か。"""

        if not self.is_issued():
            return False
        left = self.surface_of(tuple(left_values))
        right = self.surface_of(tuple(right_values))
        if left is None or right is None:
            return False
        return _same_objects(left, self.checked[0]) and _same_objects(right, self.checked[1])


def _same_objects(observed: CheckedSurface, recorded: CheckedSurface) -> bool:
    """同じ値を同じ束縛の文脈で読んだか（値も binder も object の identity で比べる）。"""

    return len(observed) == len(recorded) and all(
        value is recorded_value
        and len(binders) == len(recorded_binders)
        and all(binder is recorded_binder for binder, recorded_binder in zip(binders, recorded_binders))
        for (value, binders), (recorded_value, recorded_binders) in zip(observed, recorded)
    )


def certificate_attests(
    certificate: Any,
    subject: Any,
    checked_values: Any,
    *,
    comparison_digest: Any = None,
    relation_digest: Any = None,
) -> bool:
    """発行物を作る側の照合の唯一の実装: 有効な証明書が ``subject`` について、発行物の入力
    ``checked_values``（``(left, right)``）そのものを、（与えれば）その比較・relation の下で検査したか。"""

    if type(certificate) is not CrossSideIdentityCertificate:
        return False
    if comparison_digest is not None and certificate.comparison_digest != comparison_digest:
        return False
    if relation_digest is not None and certificate.relation_digest != relation_digest:
        return False
    return bool(
        certificate.is_issued()
        and certificate.subject == subject
        and type(checked_values) is tuple
        and len(checked_values) == 2
        and certificate.attests(checked_values[0], checked_values[1])
    )


_PAIR_ASSERTIONS_TOKEN = object()


@dataclass(frozen=True, eq=False)
class OwnerFreePairAssertions:
    """pair の query に足す、owner を含まない key で左右を同一視した等式と、その検査の証明書。

    ``derive_owner_free_pair_assertions`` だけが作る: 証明書が ``checked_values`` そのものを検査した
    ことを確かめてから、その値から等式を組み立てる。登録（``_register_pairwise_extra_assertions``）は
    証明書が登録先の pair・比較のもので、``checked_values`` をもう一度 ``attests`` するときだけ受け付ける。
    """

    lines: Tuple[str, ...]
    identity_certificate: CrossSideIdentityCertificate
    checked_values: Tuple[Tuple[Any, ...], Tuple[Any, ...]] = field(repr=False)
    _token: Any = field(default=None, repr=False)

    def __post_init__(self) -> None:
        if self._token is not _PAIR_ASSERTIONS_TOKEN:
            raise TypeError("owner-free pair assertions are built only by derive_owner_free_pair_assertions")


def derive_owner_free_pair_assertions(
    certificate: Any,
    left_values: Sequence[Any],
    right_values: Sequence[Any],
    build: Callable[[Tuple[Any, ...], Tuple[Any, ...]], Sequence[str]],
) -> OwnerFreePairAssertions:
    """証明書が検査した値から、owner を含まない等式を作る（作る側の唯一の入口）。

    ``build`` は検査した値（``left_values`` / ``right_values``）を受け取り、等式の行を返す。証明書が
    この値を検査していなければ ``ValueError``（全幅で得た証明書を狭い読みの等式に使わせない）。
    等式をその値から組み立てるのは site の責務で（API は値を渡すだけ）、site は build の中で受け取った
    値を使うか、組み立てに使った object と同じであることを確かめる。
    """

    left = tuple(left_values)
    right = tuple(right_values)
    if type(certificate) is not CrossSideIdentityCertificate or not certificate.attests(left, right):
        raise ValueError("owner-free pair assertions require a certificate of the values they are built from")
    lines = tuple(str(line) for line in build(left, right))
    return OwnerFreePairAssertions(lines, certificate, (left, right), _token=_PAIR_ASSERTIONS_TOKEN)


def issue_certificate(
    *,
    comparison_digest: str,
    relation_digest: str,
    subject: Tuple[Any, ...],
    checked: Tuple[CheckedSurface, CheckedSurface],
    surface_of: Callable[[Sequence[Any]], Optional[CheckedSurface]],
) -> Optional[CrossSideIdentityCertificate]:
    """開いている session に証明書を 1 つ発行する（``gate.certify_owner_free_identity`` 専用）。

    session が無ければ発行しない（``None``）。id は比較・relation・対象と乱数から作り、台帳の鍵にだけ
    使う（照合には使わない）。
    """

    session = current_certificate_session()
    if session is None:
        return None
    if type(subject) is not tuple or not subject:
        raise TypeError("cross-side identity certificate requires a subject tuple")
    certificate_id = hashlib.sha256(repr((
        "cross_side_identity_certificate_v2", comparison_digest, relation_digest, subject,
        secrets.token_hex(16),
    )).encode("utf-8")).hexdigest()
    certificate = CrossSideIdentityCertificate(
        certificate_id, comparison_digest, relation_digest, subject,
        (tuple(checked[0]), tuple(checked[1])), surface_of, session, _token=_CERTIFICATE_TOKEN,
    )
    session._register(certificate)
    return certificate


def issued_certificate(certificate_id: Any) -> Optional[CrossSideIdentityCertificate]:
    """id から、現在の session が発行した証明書を引く（無ければ ``None``）。"""

    session = current_certificate_session()
    return None if session is None else session.lookup(certificate_id)


__all__ = (
    "CertificateSession",
    "CrossSideIdentityCertificate",
    "OwnerFreePairAssertions",
    "derive_owner_free_pair_assertions",
    "certificate_attests",
    "certificate_session",
    "current_certificate_session",
    "entered_certificate_session",
    "issue_certificate",
    "issued_certificate",
)
