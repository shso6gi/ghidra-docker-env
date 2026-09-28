# -*- coding: utf-8 -*-
"""入力領域の正本（Issue #185）: provenance ≠ proof。

比較の入力（parameter）の幅と符号について「元の関数の入力がそうである」と言えるのは、
解析の公開境界で **その解析の parameter 表から封印した raw baseline** だけ。封印の後に
parameter 表が変わる経路（型仮説の overlay、abstraction が足す synthetic parameter、
作り直し・複製・手書きの差し替え）は、どれも「どこから来たか」（provenance）を
持つだけで、元の入力領域についての証明（proof）ではない。

この module が持つもの（事実だけ。十分性の判定はしない）:

* ``parameter_descriptor_index`` / ``parameter_descriptor_bits`` /
  ``parameter_descriptor_signed``: parameter 記述子の (index, 幅, 符号) の **唯一の読み方**。
  SMT の parameter 表（``proof/formula/params.collect_param_info``）と封印が同じ読み方を
  使うので、「式が使う幅」と「封印した幅」が別の規則で読まれることは無い。
* ``synthetic_parameter_kind``: 記述子が自分で名乗る synthetic の出所（登録制）。
  出所の名乗りは十分性を **与えない**（減らす方向にだけ使える）。
* ``RawParameterDomains``: 封印した baseline。index ごとに「ちょうど 1 つの記述子が
  明示的な index で読めた」ときだけ領域を認証し、それ以外（重複・index 無し・負・
  読めない）は認証しない index として記録する。封印の印の無い値は作れない。
* ``ParameterDomainHypothesis``: 封印の後に parameter 表を変えた仮説の台帳の 1 件。
* ``ParameterDomainAudit``: 1 つの解析について、封印した baseline・台帳・現在の表から
  導かれる欠陥（``ParameterDomainDefect``）。欠陥が 1 つでもある parameter を十分と
  認めるかどうかは consumer（最終 relation）が決める。

封印を呼べるのは解析の公開境界（``core.analysis.publish_raw_function_analysis``）だけ
（``tests/unit/test_issue185_type_hypothesis_domain.py`` の静的 guard）。
"""

from __future__ import annotations

import operator
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.json_encoding import as_list, nested


#: 記述子が synthetic の出所を名乗る key（登録制。増やすときはここに足すだけで、pairing・
#: SMT の型 class・監査の label が同じ集合を使う）。値が真の key の最初の 1 つが出所の種類。
SYNTHETIC_PARAMETER_KINDS: Tuple[str, ...] = ("synthetic_recursive_summary",)

#: 監査が報告する欠陥の種類（evidence ref の先頭）。consumer は種類で分岐しない:
#: どの欠陥も「その parameter の入力領域は証明されていない」を意味する。
DEFECT_ORIGIN_UNAVAILABLE = "parameter_domain_origin_unavailable"
DEFECT_ORIGIN_UNMATCHED = "parameter_domain_origin_unmatched"
DEFECT_ORIGIN_DROPPED = "parameter_domain_origin_dropped"
DEFECT_SYNTHETIC_UNPROVEN = "synthetic_parameter_correspondence_unproven"
DEFECT_CHANGED = "parameter_domain_changed"
DEFECT_HYPOTHESIS = "parameter_domain_hypothesis"


class ParameterDomainSealError(ValueError):
    """封印の契約違反（二重封印・仮説の載った解析・封印の印の無い baseline）。"""


# ---------------------------------------------------------------------------
# 記述子の読み方（唯一の規則）
# ---------------------------------------------------------------------------


def parameter_descriptor_index(descriptor: Mapping[str, Any]) -> Any:
    """記述子の index（生の値）。記述子に無ければ 0 と読む（SMT の parameter 表と同じ）。"""

    return descriptor.get("index", 0)


def parameter_descriptor_bits(descriptor: Mapping[str, Any]) -> Any:
    """記述子の幅（bit）。``size`` が無ければ 4 byte と読む（SMT の parameter 表と同じ）。"""

    return descriptor.get("size", 4) * 8


def parameter_descriptor_signed(descriptor: Mapping[str, Any]) -> Any:
    """記述子の符号（生の値）。無ければ signed と読む（SMT の parameter 表と同じ）。"""

    return descriptor.get("is_signed", True)


def synthetic_parameter_kind(descriptor: Mapping[str, Any]) -> Optional[str]:
    """記述子が名乗る synthetic の出所。名乗っていなければ None。"""

    for kind in SYNTHETIC_PARAMETER_KINDS:
        if descriptor.get(kind):
            return kind
    return None


def _normalized_index(value: Any) -> Optional[int]:
    """index として読める整数（bool は index ではない）。読めなければ None。"""

    if isinstance(value, bool):
        return None
    try:
        return operator.index(value)
    except TypeError:
        return None


@dataclass(frozen=True, order=True)
class ParameterDomain:
    """入力 1 つの領域: 幅（bit）と符号。"""

    bits: int
    signed: bool

    @classmethod
    def of(cls, bits: Any, signed: Any) -> "ParameterDomain":
        return cls(int(bits), bool(signed))

    @property
    def label(self) -> str:
        return f"{'s' if self.signed else 'u'}{self.bits}"


def _domain_label(domain: Optional[ParameterDomain]) -> str:
    return "none" if domain is None else domain.label


@dataclass(frozen=True)
class _DescriptorReading:
    index: Optional[int]
    explicit_index: bool
    domain: Optional[ParameterDomain]


def _read_descriptor(descriptor: Any) -> _DescriptorReading:
    if not isinstance(descriptor, Mapping):
        return _DescriptorReading(None, False, None)
    index = _normalized_index(parameter_descriptor_index(descriptor))
    try:
        domain: Optional[ParameterDomain] = ParameterDomain.of(
            parameter_descriptor_bits(descriptor), parameter_descriptor_signed(descriptor)
        )
    except (TypeError, ValueError):
        domain = None
    return _DescriptorReading(index, "index" in descriptor, domain)


def _readings(parameters: Optional[Iterable[Any]]) -> List[_DescriptorReading]:
    return [_read_descriptor(descriptor) for descriptor in (parameters or ())]


def _domains_by_index(readings: Sequence[_DescriptorReading]) -> Dict[Optional[int], List[Optional[ParameterDomain]]]:
    grouped: Dict[Optional[int], List[Optional[ParameterDomain]]] = {}
    for reading in readings:
        grouped.setdefault(reading.index, []).append(reading.domain)
    return grouped


# ---------------------------------------------------------------------------
# 封印した raw baseline
# ---------------------------------------------------------------------------

#: 封印の印。``seal_parameter_table`` だけが立てる（module の外で参照しない: 静的 guard）。
_SEAL = object()
#: ``seal_parameter_table`` の実行中だけ印を置く場所（constructor の引数で渡さない）
_SEALING: Dict[str, Any] = {}


def is_sealed_baseline(value: Any) -> bool:
    """``value`` が封印の印を持つ baseline か（型だけでなく印も確かめる）。"""

    return type(value) is RawParameterDomains and value._seal is _SEAL


@dataclass(frozen=True)
class RawParameterDomains:
    """公開境界で封印した入力領域の baseline。

    ``certified`` は「その index の記述子がちょうど 1 つあり、明示的な非負の整数 index と
    読める幅・符号を持っていた」index の領域。``uncertified`` はそれ以外の index（重複・
    index の書かれていない記述子が 0 と読まれる・読めない幅）で、どの parameter にも
    十分性を与えない。``unindexed`` は index を整数として読めなかった記述子の数。
    """

    certified: Tuple[Tuple[int, ParameterDomain], ...]
    uncertified: Tuple[int, ...] = ()
    unindexed: int = 0
    #: 封印の印。constructor の引数ではない（``replace`` や引数の写しで持ち越せない）。
    #: ``seal_parameter_table`` が作った値だけが持ち、監査はこの印を確かめる
    _seal: Any = field(default=None, init=False, repr=False, compare=False)
    #: 出力の行（(index, bits, signed)）。封印したときに 1 度だけ作る
    certified_rows: Tuple[Tuple[int, int, bool], ...] = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        if _SEALING.get("token") is not _SEAL:
            raise ParameterDomainSealError("raw_parameter_domains_are_sealed_only_at_publication")
        object.__setattr__(self, "_seal", _SEAL)
        object.__setattr__(
            self,
            "certified_rows",
            tuple((int(index), int(domain.bits), bool(domain.signed)) for index, domain in self.certified),
        )

    def json_items(self):
        yield "certified", nested(self.certified_rows)
        yield "uncertified", as_list(self.uncertified)
        yield "unindexed", self.unindexed

    def domain_of(self, index: int) -> Optional[ParameterDomain]:
        """認証済みの領域。認証していない index（欠落・曖昧）は None。"""

        for certified_index, domain in self.certified:
            if certified_index == index:
                return domain
        return None

    @property
    def indices(self) -> Tuple[int, ...]:
        return tuple(sorted({index for index, _ in self.certified} | set(self.uncertified)))

    def certifies(self, parameters: Optional[Iterable[Any]]) -> bool:
        """現在の表が baseline そのもの（全 index 認証済み・同じ領域・同じ index 集合）か。"""

        if self.uncertified or self.unindexed:
            return False
        readings = _readings(parameters)
        grouped = _domains_by_index(readings)
        if set(grouped) != {index for index, _ in self.certified}:
            return False
        return all(grouped[index] == [domain] for index, domain in self.certified)


def seal_parameter_table(parameters: Optional[Iterable[Any]]) -> RawParameterDomains:
    """parameter 表を baseline として封印する（``FunctionReturnAnalysis`` の封印だけが呼ぶ）。

    形の悪い表でも例外にしない: 実 Ghidra の raw 表には index の無い参照記述子（-1）や
    重複があり得るので、そういう index は **認証しない** と記録し、最終 relation で
    UNKNOWN 側に倒す（解析を ERROR にしない）。
    """

    readings = _readings(parameters)
    counts: Dict[int, int] = {}
    certified: Dict[int, ParameterDomain] = {}
    uncertified: set = set()
    unindexed = 0
    for reading in readings:
        if reading.index is None:
            unindexed += 1
            continue
        counts[reading.index] = counts.get(reading.index, 0) + 1
        if reading.index < 0 or not reading.explicit_index or reading.domain is None:
            uncertified.add(reading.index)
        else:
            certified[reading.index] = reading.domain
    for index, count in counts.items():
        if count != 1:
            uncertified.add(index)
    _SEALING["token"] = _SEAL
    try:
        return RawParameterDomains(
            certified=tuple(sorted((index, domain) for index, domain in certified.items() if index not in uncertified)),
            uncertified=tuple(sorted(uncertified)),
            unindexed=unindexed,
        )
    finally:
        _SEALING.clear()


# ---------------------------------------------------------------------------
# 仮説の台帳
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ParameterDomainHypothesis:
    """封印の後に 1 つの index の領域を変えた仮説（``before`` / ``after`` は曖昧なら None）。"""

    index: int
    before: Optional[ParameterDomain]
    after: Optional[ParameterDomain]
    phase: str
    source: str
    before_label: Optional[str] = field(init=False, repr=False, compare=False)
    after_label: Optional[str] = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "before_label", None if self.before is None else self.before.label)
        object.__setattr__(self, "after_label", None if self.after is None else self.after.label)

    def json_items(self):
        yield "index", self.index
        yield "before", self.before_label
        yield "after", self.after_label
        yield "phase", self.phase
        yield "source", self.source

    @property
    def label(self) -> str:
        return f"{self.phase or 'unknown'}:{_domain_label(self.before)}->{_domain_label(self.after)}"


def parameter_domain_hypotheses_between(
    before: Optional[Iterable[Any]],
    after: Optional[Iterable[Any]],
    *,
    phase: str,
    source_of: Callable[[int], str],
) -> Tuple[ParameterDomainHypothesis, ...]:
    """表 ``before`` → ``after`` で領域の変わった index ごとの台帳の記録。

    位置ではなく index で比べる（override の位置 → index の変換はここで閉じる）。
    同じ index の記述子の並び・数が変わったもの（付け替え・追加・削除）も記録する。
    """

    before_grouped = _domains_by_index(_readings(before))
    after_grouped = _domains_by_index(_readings(after))
    entries: List[ParameterDomainHypothesis] = []
    for index in sorted(
        {key for key in set(before_grouped) | set(after_grouped) if key is not None}
    ):
        old = before_grouped.get(index, [])
        new = after_grouped.get(index, [])
        if old == new:
            continue
        entries.append(
            ParameterDomainHypothesis(
                index=index,
                before=old[0] if len(old) == 1 else None,
                after=new[0] if len(new) == 1 else None,
                phase=str(phase or ""),
                source=str(source_of(index) or ""),
            )
        )
    return tuple(entries)


# ---------------------------------------------------------------------------
# 出力（serialization）用の plain な写し
# ---------------------------------------------------------------------------

#: 正本の無い解析の出力（``raw_parameter_domains`` の値）
UNSEALED_MARKER = "unsealed"
#: 写しを作り直す field（どれかを書いたら作り直す）
PARAMETER_DOMAIN_VIEW_INPUTS = frozenset({"parameters", "raw_parameter_domains", "parameter_domain_hypotheses"})
#: 写しを置く instance の属性（dataclass の field ではない: 等しさ・repr・snapshot の field に出ない）
_DIVERGENCE_ATTRIBUTE = "_raw_parameter_domains_divergence"
_LEDGER_ATTRIBUTE = "_parameter_domain_hypotheses_payload"
_NO_VIEW = object()


def record_parameter_domain_view(record: Any, name: str) -> None:
    """field ``name`` を書いた後、出力する入力領域の写しを **書いたとき** に作る。

    出力の bounded path は live な値の code を呼ばないので（``core/live_values``）、
    ``to_dict`` が読むのはここで決めた値だけ（どちらも不変な record で、``json_items`` で写される）:

    * 正本が現在の表を認証しない（仮説・abstraction）ときだけ正本の写し。正本が無い解析
      （封印の無い作り直し・複製）は ``"unsealed"``。production の raw 解析（正本 = 現在の表）
      では出さない。
    * 台帳が空でないときだけ台帳の写し。

    表の変更は field への代入（``semantic_successor`` / ``replace`` を含む）で行う。代入せずに
    list / dict をその場で書き換えると写しは古いまま（十分性の判定は live の表を監査するので
    影響しない。影響するのは出力の差分だけ）。
    """

    if name not in PARAMETER_DOMAIN_VIEW_INPUTS:
        return
    state = record.__dict__
    baseline = state.get("raw_parameter_domains")
    divergence = None
    if baseline is None:
        # 正本の無い解析（封印の無い作り直し・複製・公開境界を通らない解析）は、正本が現在の表と
        # 同じ raw 解析と同じ前提ではない（十分性が違う）。同一性に入れる
        divergence = UNSEALED_MARKER
    elif not is_sealed_baseline(baseline) or not baseline.certifies(state.get("parameters")):
        divergence = baseline
    ledger = state.get("parameter_domain_hypotheses")
    ledger_view = (
        tuple(ledger)
        if type(ledger) is tuple and ledger and all(type(entry) is ParameterDomainHypothesis for entry in ledger)
        else None
    )
    object.__setattr__(record, _DIVERGENCE_ATTRIBUTE, divergence)
    object.__setattr__(record, _LEDGER_ATTRIBUTE, ledger_view)


def raw_parameter_domains_divergence_of(record: Any) -> Any:
    """書いたときに決めた、出力する正本（不変な record。正本が現在の表そのものなら None）。"""

    from scripts.function_tracer_pcode.core import live_values

    value = live_values.instance_state(record, _DIVERGENCE_ATTRIBUTE, _NO_VIEW)
    return None if value is _NO_VIEW else value


def parameter_domain_hypotheses_payload_of(record: Any) -> Any:
    """書いたときに決めた、出力する台帳（不変な record の tuple。台帳が空なら None）。"""

    from scripts.function_tracer_pcode.core import live_values

    value = live_values.instance_state(record, _LEDGER_ATTRIBUTE, _NO_VIEW)
    return None if value is _NO_VIEW else value


# ---------------------------------------------------------------------------
# 監査（事実。判定は consumer）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ParameterDomainDefect:
    kind: str
    detail: str = ""

    def as_evidence_ref(self) -> str:
        return f"{self.kind}:{self.detail}" if self.detail else self.kind


@dataclass(frozen=True)
class ParameterDomainAudit:
    """1 つの解析の入力領域の監査。``of`` だけで作る。

    ``baseline`` が None なのは「封印の印付きの baseline が無い」こと（封印の無い作り直し・
    複製・fake・analysis の無い補助 relation）。そのとき全 parameter が欠陥を持つ。
    """

    baseline: Optional[RawParameterDomains]
    hypotheses: Tuple[ParameterDomainHypothesis, ...]
    ledger_readable: bool
    current: Mapping[Optional[int], Tuple[Optional[ParameterDomain], ...]]

    @classmethod
    def of(cls, analysis: Any) -> "ParameterDomainAudit":
        if analysis is None:
            return cls(None, (), True, {})
        baseline = getattr(analysis, "raw_parameter_domains", None)
        if not is_sealed_baseline(baseline):
            baseline = None
        raw_ledger = getattr(analysis, "parameter_domain_hypotheses", ())
        ledger_readable = type(raw_ledger) is tuple and all(
            type(entry) is ParameterDomainHypothesis for entry in raw_ledger
        )
        hypotheses = tuple(raw_ledger) if ledger_readable else ()
        parameters = getattr(analysis, "parameters", None)
        grouped = _domains_by_index(_readings(parameters if isinstance(parameters, (list, tuple)) else ()))
        return cls(
            baseline,
            hypotheses,
            ledger_readable,
            {index: tuple(domains) for index, domains in grouped.items()},
        )

    def table_defects(self) -> Tuple[ParameterDomainDefect, ...]:
        """表全体の欠陥: baseline が無い、読めない台帳、baseline の index が表から消えた。"""

        if self.baseline is None:
            return (ParameterDomainDefect(DEFECT_ORIGIN_UNAVAILABLE),)
        defects: List[ParameterDomainDefect] = []
        if not self.ledger_readable:
            defects.append(ParameterDomainDefect(DEFECT_HYPOTHESIS, "ledger_unreadable"))
        for index in self.baseline.indices:
            if index not in self.current:
                defects.append(ParameterDomainDefect(DEFECT_ORIGIN_DROPPED, str(index)))
        return tuple(defects)

    def parameter_defects(
        self,
        *,
        index: Any,
        bits: Any,
        signed: Any,
        synthetic_kind: Optional[str],
    ) -> Tuple[ParameterDomainDefect, ...]:
        """SMT が使う parameter（index, 幅, 符号, 名乗った出所）の欠陥。空なら証明済み。"""

        if self.baseline is None:
            return (ParameterDomainDefect(DEFECT_ORIGIN_UNAVAILABLE),)
        normalized = _normalized_index(index)
        try:
            claimed: Optional[ParameterDomain] = ParameterDomain.of(bits, signed)
        except (TypeError, ValueError):
            claimed = None
        raw = None if normalized is None else self.baseline.domain_of(normalized)
        defects: List[ParameterDomainDefect] = []
        label_index = str(normalized if normalized is not None else index)
        if synthetic_kind is not None:
            # 出所の名乗りは証明ではない。名乗った記述子は raw の入力ではないと自分で言っている
            defects.append(ParameterDomainDefect(DEFECT_SYNTHETIC_UNPROVEN, f"{synthetic_kind}:{label_index}"))
        if raw is None or len(self.current.get(normalized, ())) != 1:
            if synthetic_kind is None:
                defects.append(ParameterDomainDefect(DEFECT_ORIGIN_UNMATCHED, label_index))
            return tuple(defects)
        live = self.current.get(normalized, (None,))[0]
        if claimed != raw:
            defects.append(ParameterDomainDefect(DEFECT_CHANGED, f"{raw.label}->{_domain_label(claimed)}"))
        elif live != raw:
            # 式が使う値は正本と同じでも、いまの表は違う（作り直した relation が古い表を使った）
            defects.append(ParameterDomainDefect(DEFECT_CHANGED, f"{raw.label}->{_domain_label(live)}"))
        for entry in self.hypotheses:
            if entry.index == normalized:
                defects.append(ParameterDomainDefect(DEFECT_HYPOTHESIS, entry.label))
        return tuple(defects)


__all__ = [
    "DEFECT_CHANGED",
    "DEFECT_HYPOTHESIS",
    "DEFECT_ORIGIN_DROPPED",
    "DEFECT_ORIGIN_UNAVAILABLE",
    "DEFECT_ORIGIN_UNMATCHED",
    "DEFECT_SYNTHETIC_UNPROVEN",
    "ParameterDomain",
    "ParameterDomainAudit",
    "ParameterDomainDefect",
    "ParameterDomainHypothesis",
    "ParameterDomainSealError",
    "RawParameterDomains",
    "UNSEALED_MARKER",
    "is_sealed_baseline",
    "SYNTHETIC_PARAMETER_KINDS",
    "parameter_descriptor_bits",
    "parameter_descriptor_index",
    "parameter_descriptor_signed",
    "parameter_domain_hypotheses_between",
    "parameter_domain_hypotheses_payload_of",
    "raw_parameter_domains_divergence_of",
    "record_parameter_domain_view",
    "seal_parameter_table",
    "synthetic_parameter_kind",
]
