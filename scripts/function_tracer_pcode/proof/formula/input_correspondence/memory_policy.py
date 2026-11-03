# -*- coding: utf-8 -*-
"""左右の memory の同一視に使う前提の方針表（Issue #282, I12）。

比べる状態の組（意味領域 D。#188 が所有）のうち、memory についての条項と、それを EQ の根拠に使ってよいかを
1 つの表にする。EQ の経路（同一 binary の fast path（P12）・SMT の経路）は、使った前提をこの表で引き、すべてが
`ADMITTED_BY_D` のときだけ無条件の EQ にする。D の判断が変わったときは、この表の 1 点を変える（P12 と SMT の
経路が別々の D を前提にしない）。

| 前提 | 内容 | 根拠 |
|---|---|---|
| `IMAGE_IDENTITY` | 左右の program の image の byte が同一（同じ loader で読み込んだ） | 証拠: 入力の sha256 の一致（`checker.identical_fast_path`） |
| `CALLER_STATE_SAME` | 左右で同じ object である memory は、呼び出し時点の内容が同じ（D-M1） | #188 の条項。2026-11-02 の判断（J1-D）で D に入れる |

`CALLER_STATE_SAME` は「pointer の指す先が caller 所有の memory」とは仮定しない: 同じ object であることの根拠
（image の identity・どちらの image の外にもある番地・global の identity）は前提ごとに別に要る。PR-282-A の
SMT の経路は左右の memory を共有しない（どの前提も使わない）ので、この表を読むのは P12 だけ。
"""

from __future__ import annotations

from enum import Enum
from typing import Iterable, Mapping, Tuple


class MemoryPremise(str, Enum):
    IMAGE_IDENTITY = "image_identity"
    CALLER_STATE_SAME = "caller_state_same"


class PremiseAdmission(str, Enum):
    ADMITTED_BY_D = "admitted_by_d"
    CONDITIONAL = "conditional"


MEMORY_CORRESPONDENCE_POLICY: Mapping[MemoryPremise, PremiseAdmission] = {
    MemoryPremise.IMAGE_IDENTITY: PremiseAdmission.ADMITTED_BY_D,
    MemoryPremise.CALLER_STATE_SAME: PremiseAdmission.ADMITTED_BY_D,
}

#: 同一 binary の fast path（P12）の EQ が使う前提
IDENTICAL_BINARY_PREMISES: Tuple[MemoryPremise, ...] = (
    MemoryPremise.IMAGE_IDENTITY,
    MemoryPremise.CALLER_STATE_SAME,
)


def premises_admit_unconditional_eq(
    premises: Iterable[MemoryPremise],
    policy: Mapping[MemoryPremise, PremiseAdmission] = MEMORY_CORRESPONDENCE_POLICY,
) -> bool:
    """前提がすべて D に入っている（無条件の EQ の根拠にしてよい）か。表に無い前提は認めない。"""

    return all(policy.get(premise) is PremiseAdmission.ADMITTED_BY_D for premise in premises)


def premise_record(
    premises: Iterable[MemoryPremise],
    policy: Mapping[MemoryPremise, PremiseAdmission] = MEMORY_CORRESPONDENCE_POLICY,
) -> Tuple[Tuple[str, str], ...]:
    """結果の provenance に残す前提の記録（前提, 方針表の扱い）。"""

    return tuple(
        (premise.value, policy.get(premise, PremiseAdmission.CONDITIONAL).value) for premise in premises
    )
