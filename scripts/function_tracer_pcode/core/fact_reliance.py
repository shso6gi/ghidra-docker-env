# -*- coding: utf-8 -*-
"""証拠が依存した事実の語彙と、その推移閉包（Issue #325, E1）。

判定の authority は、active な cause の行がある証拠を阻むかを、次の 2 つの交わりで決める
（`authority.decision.obligation_scope`）:

* 行の reason の **guards**: その義務が保証する事実の種類（registry の静的な宣言）。
* 証拠の **relies_on**: その証拠が実際に依存した事実（この module の `ReliesOn`）。

この module はその共通の語彙だけを持つ。証拠を作る producer（proof 層）も、評価する authority も
これを import するので、最下層の core に置く（import は下向きのまま）。

規則（fail-closed）:

* 事実の種類は閉じた `FactKind` だけ。新しい種類は enum に足さないと作れない。
* 事実 handle（`FactHandle`）は **由来**（`FactProvenance`）を constructor の必須引数に持つ。
  由来は「葉」（raw な事実か、記録済みの解析段）、「上流の handle から導いた」、「記録していない」
  のどれか。由来を書かない handle は作れない。
* `ReliesOn.closure_of(handles)` は上流をたどった推移閉包を作る。閉包のどこかに「記録していない」
  由来があれば、その証拠は **全事実に依存** する（`UNKNOWN_PROVENANCE`）。
* 狭い（全事実でない）`ReliesOn` は `closure_of` からしか作れない。証拠が自分の依存を
  自己申告で狭めることはできない。
* 等しさは値（`FactRef` の組）で決める。digest は記録・照合の手がかりで、identity に使わない。
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import Any, FrozenSet, Iterable, Mapping, Tuple

RELIES_ON_SCHEMA = "fact-reliance-v1"


class FactKind(str, Enum):
    """義務が保証し、証拠が依存し得る事実の種類（閉じた語彙）。

    初期の一覧は、production の producer が実際に読む事実と、registry の reason が保証する事実から
    選んだ（根拠は PR #325-E1 の本文）。種類を足すときはここに 1 行足す。
    """

    #: 戻り値の式の payload 幅（return-width の provenance）
    RETURN_PAYLOAD_WIDTH = "RETURN_PAYLOAD_WIDTH"
    #: ABI の戻り値の幅（呼出規約が定める register の幅）
    RETURN_ABI_WIDTH = "RETURN_ABI_WIDTH"
    #: 戻り値の位置（storage。register / stack の piece）
    RETURN_LOCATION = "RETURN_LOCATION"
    #: 戻り値の class（整数 / pointer / 浮動小数点）
    RETURN_VALUE_CLASS = "RETURN_VALUE_CLASS"
    #: 同じ binary の呼び出し側が、call の後に戻り register のどの bit を実際に要求するか
    #: （Issue #327 E-b。callee の解析・decompiler から独立に、命令の raw P-code から作る）
    RETURN_CALLER_DEMAND = "RETURN_CALLER_DEMAND"
    #: 引数の storage（どの register / stack の piece が何番目の引数か）
    PARAMETER_STORAGE = "PARAMETER_STORAGE"
    #: ABI model（呼出規約・cspec）
    ABI_MODEL = "ABI_MODEL"
    #: program の image（byte・section・読み取り専用領域）
    PROGRAM_IMAGE = "PROGRAM_IMAGE"
    #: SMT の model が実在の挙動であること（SAT-safety が守る事実）
    SMT_MODEL_REALIZABILITY = "SMT_MODEL_REALIZABILITY"
    #: ループ要約（recurrence）の妥当性
    LOOP_SUMMARY_VALIDITY = "LOOP_SUMMARY_VALIDITY"
    #: call effect の要約（外部 call の意味・callsite の対応）
    CALL_EFFECT_SUMMARY = "CALL_EFFECT_SUMMARY"
    #: 型の仮説（signature を変える再解析の phase）
    TYPE_HYPOTHESIS = "TYPE_HYPOTHESIS"
    #: 由来の分からない事実（全事実とみなす。fail-closed の葉）
    UNKNOWN_PROVENANCE = "UNKNOWN_PROVENANCE"


#: 宣言・照合に使える具体的な事実の種類（`UNKNOWN_PROVENANCE` は「全部」の印で、具体的な種類ではない）
CONCRETE_FACT_KINDS: FrozenSet[FactKind] = frozenset(
    kind for kind in FactKind if kind is not FactKind.UNKNOWN_PROVENANCE
)


class FactSide(str, Enum):
    """事実がどちらの関数のものか。"""

    LEFT = "LEFT"
    RIGHT = "RIGHT"
    #: 両側に共通（ABI model など）か、pair 全体の事実
    PAIR = "PAIR"


class FactSlot(str, Enum):
    """事実が関数のどこに付くか。"""

    FUNCTION = "FUNCTION"
    RETURN = "RETURN"
    PARAMETERS = "PARAMETERS"
    PROGRAM = "PROGRAM"


@dataclass(frozen=True, order=True)
class FactTarget:
    """事実の対象（関数の側 × slot）。"""

    side: FactSide
    slot: FactSlot

    def __post_init__(self) -> None:
        if type(self.side) is not FactSide or type(self.slot) is not FactSlot:
            raise TypeError("a fact target is an exact FactSide x FactSlot")

    def to_json(self) -> list:
        return [self.side.value, self.slot.value]


@dataclass(frozen=True, order=True)
class FactRef:
    """事実の参照 ``(事実の種類, 対象)``。閉包と guards の照合の単位。"""

    kind: FactKind
    target: FactTarget

    def __post_init__(self) -> None:
        if type(self.kind) is not FactKind:
            raise TypeError("a fact reference names an exact FactKind")
        if type(self.target) is not FactTarget:
            raise TypeError("a fact reference names an exact FactTarget")

    def to_json(self) -> list:
        return [self.kind.value, *self.target.to_json()]


class ProvenanceKind(str, Enum):
    #: raw な事実（program の byte・cspec・ELF・decompiler の prototype）か、記録済みの解析段
    LEAF = "LEAF"
    #: 上流の handle から導いた
    DERIVED = "DERIVED"
    #: どこから来たかを記録していない（閉包は全事実）
    UNRECORDED = "UNRECORDED"


_HANDLE_FACTORY_TOKEN = object()


@dataclass(frozen=True, init=False)
class FactProvenance:
    """事実の由来: 作った producer site と、葉の出所 / 上流の handle / 記録していない理由。

    constructor は直接呼ばない（`leaf` / `derived` / `unrecorded`）。
    """

    kind: ProvenanceKind
    producer_site: str
    detail: str
    upstream: Tuple["FactHandle", ...]

    def __init__(self, kind, producer_site, detail, upstream, *, _token=None):
        if _token is not _HANDLE_FACTORY_TOKEN:
            raise ValueError("fact provenance is built by FactProvenance.leaf / derived / unrecorded")
        object.__setattr__(self, "kind", kind)
        object.__setattr__(self, "producer_site", producer_site)
        object.__setattr__(self, "detail", detail)
        object.__setattr__(self, "upstream", upstream)

    @staticmethod
    def _site(producer_site: Any, detail: Any) -> None:
        if type(producer_site) is not str or not producer_site:
            raise TypeError("a fact provenance names its producer site")
        if type(detail) is not str or not detail:
            raise TypeError("a fact provenance states its origin")

    @classmethod
    def leaf(cls, *, producer_site: str, origin: str) -> "FactProvenance":
        """raw な事実か、記録済みの解析段（``origin`` はその出所の名前と版）。"""
        cls._site(producer_site, origin)
        return cls(ProvenanceKind.LEAF, producer_site, origin, (), _token=_HANDLE_FACTORY_TOKEN)

    @classmethod
    def derived(cls, *, producer_site: str, rule: str, upstream: Iterable["FactHandle"]) -> "FactProvenance":
        """上流の handle から ``rule`` で導いた事実。上流は 1 つ以上要る。"""
        cls._site(producer_site, rule)
        parents = tuple(upstream)
        if not parents or any(type(parent) is not FactHandle for parent in parents):
            raise TypeError("a derived fact names its upstream FactHandle(s)")
        return cls(ProvenanceKind.DERIVED, producer_site, rule, parents, _token=_HANDLE_FACTORY_TOKEN)

    @classmethod
    def unrecorded(cls, *, producer_site: str, reason: str) -> "FactProvenance":
        """どの解析段・仮説から来たかを記録していない事実（閉包は全事実）。"""
        cls._site(producer_site, reason)
        return cls(ProvenanceKind.UNRECORDED, producer_site, reason, (), _token=_HANDLE_FACTORY_TOKEN)


def _freeze(value: Any) -> Any:
    """handle の値を読み取り専用の写しにする（組み込みの dict は MappingProxyType、list / tuple は
    tuple）。組み込みでない値（JVM の object など）はそのまま持つ（読み方を変えない）。"""

    if type(value) is dict or type(value) is MappingProxyType:
        return MappingProxyType({key: _freeze(item) for key, item in value.items()})
    if type(value) is list or type(value) is tuple:
        return tuple(_freeze(item) for item in value)
    return value


@dataclass(frozen=True, init=False)
class FactHandle:
    """由来つきの事実 1 つ。証拠の producer が事実を受け取る唯一の形。

    ``value`` は事実の値の読み取り専用の写し（producer が読む）。``ref`` と ``provenance`` が
    閉包を決める。class は閉じている（subclass を作れない）。
    """

    ref: FactRef
    provenance: FactProvenance
    value: Any

    def __init_subclass__(cls, **kwargs):  # pragma: no cover - 閉じた型
        raise TypeError("FactHandle is a closed type")

    def __init__(self, kind: FactKind, target: FactTarget, *, provenance: FactProvenance, value: Any = None):
        if type(provenance) is not FactProvenance:
            raise TypeError("a fact handle requires its FactProvenance")
        if kind is FactKind.UNKNOWN_PROVENANCE:
            raise ValueError("UNKNOWN_PROVENANCE marks an unknown origin; it is not a fact to hold")
        object.__setattr__(self, "ref", FactRef(kind, target))
        object.__setattr__(self, "provenance", provenance)
        object.__setattr__(self, "value", _freeze(value))


class RelianceBasis(str, Enum):
    """証拠の relies_on の決まり方。"""

    #: 証明方式の規則で全事実（SMT の証拠）
    ALL_FACTS = "ALL_FACTS"
    #: 閉包に記録していない由来があった / 由来を渡されなかった（全事実）
    UNKNOWN_PROVENANCE = "UNKNOWN_PROVENANCE"
    #: 由来が完全に分かった閉包（狭い）
    CLOSURE = "CLOSURE"


_RELIES_ON_FACTORY_TOKEN = object()


def _digest(payload: Any) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


@dataclass(frozen=True, init=False)
class ReliesOn:
    """証拠が依存した事実の集合（閉包）。

    ``universal`` なら全事実に依存する（どの guards とも交わる）。``refs`` は閉包でたどれた
    参照（universal でも、分かった範囲の記録として残す）。
    """

    basis: RelianceBasis
    refs: FrozenSet[FactRef]
    unrecorded_sites: Tuple[str, ...]

    def __init__(self, basis, refs, unrecorded_sites, *, _token=None):
        if _token is not _RELIES_ON_FACTORY_TOKEN:
            raise ValueError("ReliesOn is built by all_facts / unknown_provenance / closure_of")
        object.__setattr__(self, "basis", basis)
        object.__setattr__(self, "refs", frozenset(refs))
        object.__setattr__(self, "unrecorded_sites", tuple(unrecorded_sites))

    @property
    def universal(self) -> bool:
        return self.basis is not RelianceBasis.CLOSURE

    @classmethod
    def all_facts(cls) -> "ReliesOn":
        """証明方式の規則で全事実に依存する証拠（SMT の EQ / 反例）。"""
        return cls(RelianceBasis.ALL_FACTS, (), (), _token=_RELIES_ON_FACTORY_TOKEN)

    @classmethod
    def unknown_provenance(cls, *, reason: str) -> "ReliesOn":
        """依存を記録していない証拠（全事実）。``reason`` は記録していない理由。"""
        if type(reason) is not str or not reason:
            raise TypeError("an unknown reliance states why it is unknown")
        return cls(RelianceBasis.UNKNOWN_PROVENANCE, (), (reason,), _token=_RELIES_ON_FACTORY_TOKEN)

    @classmethod
    def closure_of(cls, handles: Iterable[FactHandle]) -> "ReliesOn":
        """``handles`` から上流をたどった推移閉包。

        記録していない由来が 1 つでもあれば全事実（`UNKNOWN_PROVENANCE`）。handle が 1 つも
        無いときも全事実（何に依存したかを示していない）。
        """
        refs = set()
        unrecorded = set()
        seen = set()
        stack = list(handles)
        if not stack:
            return cls.unknown_provenance(reason="no fact handle was supplied")
        while stack:
            handle = stack.pop()
            if type(handle) is not FactHandle:
                raise TypeError(f"a reliance closure reads FactHandle only: {type(handle).__name__}")
            if id(handle) in seen:
                continue
            seen.add(id(handle))
            refs.add(handle.ref)
            provenance = handle.provenance
            if provenance.kind is ProvenanceKind.UNRECORDED:
                unrecorded.add(f"{provenance.producer_site}:{provenance.detail}")
            stack.extend(provenance.upstream)
        basis = RelianceBasis.UNKNOWN_PROVENANCE if unrecorded else RelianceBasis.CLOSURE
        return cls(basis, refs, sorted(unrecorded), _token=_RELIES_ON_FACTORY_TOKEN)

    def kinds_by_target(self) -> Mapping[FactTarget, FrozenSet[FactKind]]:
        by_target: dict = {}
        for ref in self.refs:
            by_target.setdefault(ref.target, set()).add(ref.kind)
        return {target: frozenset(kinds) for target, kinds in by_target.items()}

    def to_json(self) -> Mapping[str, Any]:
        return {
            "schema": RELIES_ON_SCHEMA,
            "basis": self.basis.value,
            "refs": sorted(ref.to_json() for ref in self.refs),
            "unrecorded_sites": list(self.unrecorded_sites),
        }

    @property
    def digest(self) -> str:
        """閉包の digest（記録・照合用。等しさは ``refs`` と ``basis`` で決める）。"""
        return _digest(self.to_json())


__all__ = [
    "CONCRETE_FACT_KINDS",
    "FactHandle",
    "FactKind",
    "FactProvenance",
    "FactRef",
    "FactSide",
    "FactSlot",
    "FactTarget",
    "ProvenanceKind",
    "RELIES_ON_SCHEMA",
    "RelianceBasis",
    "ReliesOn",
]
