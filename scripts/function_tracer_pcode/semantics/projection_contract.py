# -*- coding: utf-8 -*-
"""Semantic-width 書き換えと raw closure の protocol 型（Issue #167）。

この module は **型だけ** を持つ。値を作るのは次の 2 箇所に限る。

* ``ProjectionClosure``: ``semantics/projection_closure.py`` の raw 走査。
* ``RewriteAuthorization``: ``proof/formula/input_correspondence.py`` が最終
  ``InputCorrespondence`` から導出する。normalizer はこれを受け取るだけで、
  自分で仮定を足さない。

型は semantics が所有し、proof/formula が構築して semantics へ渡す（依存は
proof → semantics の下向きだけ）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
import hashlib
from typing import Optional, Tuple


class ExtensionKind(str, Enum):
    """``p == ext_kind(low_N(p))`` の ext の種類。"""

    SIGN = "sign"
    ZERO = "zero"

    @property
    def smt_operator(self) -> str:
        return "sign_extend" if self is ExtensionKind.SIGN else "zero_extend"


@dataclass(frozen=True)
class RewriteAssumption:
    """最終 premise が含意する 1 つの入力 extension 仮定。

    意味: 幅 ``parameter_bits`` の parameter ``parameter_index`` について
    ``p == ext_kind(low_{narrow_bits}(p))``。
    """

    parameter_index: int
    parameter_bits: int
    narrow_bits: int
    kind: ExtensionKind

    def __post_init__(self) -> None:
        if type(self.kind) is not ExtensionKind:
            raise TypeError("rewrite assumption kind must be an ExtensionKind")
        if not (0 < int(self.narrow_bits) < int(self.parameter_bits)):
            raise ValueError("rewrite assumption requires 0 < narrow_bits < parameter_bits")
        if int(self.parameter_index) < 0:
            raise ValueError("rewrite assumption requires a real parameter index")

    def stable_key(self) -> Tuple[object, ...]:
        return (
            "rewrite_assumption_v1",
            int(self.parameter_index),
            int(self.parameter_bits),
            int(self.narrow_bits),
            self.kind.value,
        )


@dataclass(frozen=True)
class RewriteAuthorization:
    """片側 analysis に許された条件付き書き換えの前提集合。

    ``assumptions`` が空なら、恒等（無条件に意味を保存する）規則だけが使える。
    空の authorization は常に健全なので、既定値として使える。
    ``source_digest`` は導出元の最終 relation set の digest で、二重 normalize が
    同じ authorization を使ったことを certificate で照合するためにある。
    """

    assumptions: Tuple[RewriteAssumption, ...] = ()
    source_digest: str = "no_input_correspondence"

    def __post_init__(self) -> None:
        ordered = tuple(sorted(self.assumptions, key=lambda item: item.stable_key()))
        indices = [item.parameter_index for item in ordered]
        if len(indices) != len(set(indices)):
            raise ValueError("rewrite authorization holds at most one assumption per parameter")
        object.__setattr__(self, "assumptions", ordered)

    def assumption_for(self, parameter_index: int, parameter_bits: int) -> Optional[RewriteAssumption]:
        for item in self.assumptions:
            if item.parameter_index == parameter_index and item.parameter_bits == parameter_bits:
                return item
        return None

    @property
    def digest(self) -> str:
        payload = repr(
            (
                "rewrite_authorization_v1",
                self.source_digest,
                tuple(item.stable_key() for item in self.assumptions),
            )
        )
        return hashlib.sha256(payload.encode("utf-8")).hexdigest()


EMPTY_REWRITE_AUTHORIZATION = RewriteAuthorization()


@dataclass(frozen=True)
class ClosureWitness:
    """closure が成立しない理由を 1 つ、観測 surface の位置付きで記録する。"""

    surface: str
    location: str
    reason: str
    detail: str = ""

    def as_evidence_ref(self) -> str:
        suffix = f":{self.detail}" if self.detail else ""
        return f"{self.surface}@{self.location}:{self.reason}{suffix}"


@dataclass(frozen=True)
class ProjectionClosure:
    """raw surface 上で parameter の bit ``[N, W)`` が観測に届かないかの判定。

    ``closed`` は「走査できた全 surface で、parameter の全 occurrence が
    ``[0, narrow_bits)`` の explicit extract の下にあり、同じ register を別名で
    読む変数も無い」ときだけ真。幅ごとに独立（N で閉じても M で閉じるとは
    限らない）。
    """

    parameter_index: int
    parameter_bits: int
    narrow_bits: int
    witnesses: Tuple[ClosureWitness, ...] = field(default_factory=tuple)

    @property
    def closed(self) -> bool:
        return not self.witnesses

    def evidence_refs(self) -> Tuple[str, ...]:
        return tuple(item.as_evidence_ref() for item in self.witnesses)
