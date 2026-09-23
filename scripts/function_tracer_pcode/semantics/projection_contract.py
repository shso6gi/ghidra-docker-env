# -*- coding: utf-8 -*-
"""raw closure の protocol 型（Issue #167）。

値を作るのは ``semantics/projection_closure.py`` の raw 走査だけ。消費するのは
最終 ``InputCorrespondence``（``proof/formula/input_correspondence``）で、依存は
proof → semantics の下向きだけ。書き換えの契約（規則表・入力仮定・
authorization）は ``semantics/rewrite_contract.py`` が持つ。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Tuple


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
