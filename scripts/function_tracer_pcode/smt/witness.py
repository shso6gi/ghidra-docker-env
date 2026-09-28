# -*- coding: utf-8 -*-
"""SAT の witness を **script の意味だけ** で決める（Issue #161）。

solver が SAT のときに返す model は、同じ論理式の解のうちどれか 1 つで、どれを
返すかは solver の内部状態（z3 なら同じ context に先に parse した式の履歴など）で
変わる。反例の replay・NaN の拒否・partition の曖昧さの判定はその 1 つの model を
見るので、判定（NOT_EQ / UNKNOWN）まで solver の履歴で揺れていた。

ここでは witness を次の値に固定する:

    script が宣言する scalar の入力（bit-vector / Bool の定数）を宣言順に並べ、
    各値を unsigned の整数として見たときに **辞書式で最小** の model

これは script の assertion の集合と宣言順だけで決まる（solver の種類・呼び出しの
順序・先に解いた query・最初に見つかった model に依らない）。求め方は最上位 bit から
「この bit を 0 にしても充足可能か」を順に問う greedy で、現在の model の bit が既に
0 の位置は問わない（model-guided）。1 の bit では先に「この bit から下を全部 0 に
できるか」を問い、できればその成分はそこで確定する。

問いの立て方は値を変えない（辞書式最小は 1 つしかない）ので、ここは費用だけの選択。
浮動小数点を含む式では SAT の答えが高く UNSAT の答えが安い（tsafe/normAngle の実測で
SAT 1 回 0.2〜0.8 秒、UNSAT は 900 回で 0.03 秒）ので、SAT になる問いを減らす順に問う:
今の model が既に満たしている preference は問わずに確定し、下位を一度に 0 にする問いで
bit ごとの SAT の列を 1 回にまとめる。

**witness の優先（preference）**: 何を「受け入れられる witness」とみなすかは、
witness を使う側（replay の規則。例: 浮動小数点の引数が NaN の反例は証拠にしない）が
決める。使う側は script に nullary な Bool の `define-fun |witness-preference:<k>|`
を置く（assert しないので論理式の意味は変わらない）。witness は k の小さい順に
「その preference を満たせるなら満たす」を確定してから辞書式最小を取る。満たせる
witness があるのに満たさない witness を返すことは無い。

backend ごとの違い（制約の作り方・一時的な仮定・model の読み方）は `WitnessSession`
の実装が持ち、探索の規則はここ 1 箇所にある。判定不能（timeout / unknown）や予算切れ
は `WitnessUnavailable` で、呼ぶ側は model を持たない SAT として扱う（replay は model の
無い SAT を反例として受け入れない = fail closed）。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Mapping, Optional, Protocol, Sequence, Tuple


#: 宣言の sort のうち witness の成分になるもの
BITVEC = "bitvec"
BOOL = "bool"

#: script が witness の優先を宣言する `define-fun` の名前の接頭辞（使う側との契約）
WITNESS_PREFERENCE_PREFIX = "witness-preference:"


def witness_preference_name(order: int) -> str:
    """`order` 番目（小さいほど優先）の preference の SMT-LIB 名（`|` で囲んだ symbol）。"""

    return f"|{WITNESS_PREFERENCE_PREFIX}{int(order)}|"


@dataclass(frozen=True)
class WitnessTarget:
    """witness の成分（宣言された scalar の定数）。Bool は幅 1（false < true）。"""

    name: str
    width: int
    sort: str = BITVEC


@dataclass(frozen=True)
class Constraint:
    """探索が solver に足す制約（backend が自分の項へ訳す）。

    * `kind="bit"`: `target` の `bit` 番目が `value`（0 / 1）
    * `kind="low_zero"`: `target` の `bit` 番目から下（`bit`..0）がすべて 0
    * `kind="preference"`: script の preference（`preference` はその名前）が成り立つ
    """

    kind: str
    target: Optional[WitnessTarget]
    value: int = 0
    bit: int = 0
    preference: str = ""


class WitnessUnavailable(Exception):
    """canonical な witness を決められなかった（判定不能・予算切れ）。"""


class WitnessSession(Protocol):
    """1 つの SAT の論理式の上で witness を探す backend 側の窓口。

    session は「現在の model」を 1 つ持つ（最初は元の論理式の SAT の model、以後は
    `check_with` が SAT で返した最後の model）。

    * `values()` — 現在の model での各 target の値（未割当は model completion）
    * `holds(constraint)` — 現在の model で `constraint` が成り立つか（solver に問わない）
    * `check_with(constraint)` — これまで `fix` した制約に `constraint` を **一時的に**
      足して解く。SAT ならその model が現在の model になり、その各 target の値を返す。
      UNSAT なら `None`（現在の model は変わらない）、判定不能なら `WitnessUnavailable`
    * `fix(constraint)` — 制約を以後ずっと足す
    """

    def values(self) -> Mapping[str, int]: ...

    def holds(self, constraint: Constraint) -> bool: ...

    def check_with(self, constraint: Constraint) -> Optional[Mapping[str, int]]: ...

    def fix(self, constraint: Constraint) -> None: ...


def canonical_witness(
    session: WitnessSession,
    targets: Sequence[WitnessTarget],
    preferences: Sequence[str] = (),
) -> Dict[str, int]:
    """`targets`（宣言順）について辞書式最小の model を返す。

    まず `preferences` を順に「満たせるなら満たす」と確定し、その中で最上位 bit から
    順に「0 にできるなら 0」を確定する。不変条件: `values` は常に「元の論理式 ∧ これまで
    fix した制約」の model（= session の現在の model）。終わったときの `values` は、元の
    論理式の model のうち（満たせる preference をすべて満たし）`targets` の値の列が
    辞書式最小のもの。
    """

    values: Dict[str, int] = {target.name: int(session.values()[target.name]) for target in targets}

    def adopt(model: Mapping[str, int]) -> None:
        values.update({name: int(model[name]) for name in values})

    for name in preferences:
        preference = Constraint("preference", None, preference=name)
        if not session.holds(preference):
            satisfied = session.check_with(preference)
            if satisfied is None:
                continue
            adopt(satisfied)
        session.fix(preference)
    for target in targets:
        for bit in reversed(range(target.width)):
            current = values[target.name]
            if not (current >> bit) & 1:
                session.fix(Constraint("bit", target, 0, bit))
                continue
            # 上位は確定済み。この bit から下を全部 0 にできるなら、それがこの成分の最小
            cleared = session.check_with(Constraint("low_zero", target, bit=bit))
            if cleared is not None:
                adopt(cleared)
                session.fix(Constraint("low_zero", target, bit=bit))
                break
            if bit == 0:
                # 最下位では「この bit を 0」は今の問いと同じ: 1 に決まる
                session.fix(Constraint("bit", target, 1, bit))
                continue
            alternative = session.check_with(Constraint("bit", target, 0, bit))
            if alternative is None:
                session.fix(Constraint("bit", target, 1, bit))
                continue
            adopt(alternative)
            session.fix(Constraint("bit", target, 0, bit))
    return dict(values)


def targets_in_declaration_order(
    declarations: Sequence[Tuple[str, str]],
) -> Tuple[WitnessTarget, ...]:
    """`(name, sort text)` の宣言列から witness の成分を宣言順に取り出す。

    bit-vector と Bool だけが成分になる。配列・関数・実数などの解釈は witness に含めない
    （値としての最小が定まらず、replay も使わない）。
    """

    import re

    targets = []
    for name, sort_text in declarations:
        sort_text = sort_text.strip()
        if sort_text == "Bool":
            targets.append(WitnessTarget(name, 1, BOOL))
            continue
        match = re.fullmatch(r"\(_ BitVec ([1-9][0-9]*)\)", sort_text)
        if match is not None:
            targets.append(WitnessTarget(name, int(match.group(1)), BITVEC))
    return tuple(targets)


__all__ = [
    "BITVEC",
    "BOOL",
    "WITNESS_PREFERENCE_PREFIX",
    "witness_preference_name",
    "Constraint",
    "WitnessSession",
    "WitnessTarget",
    "WitnessUnavailable",
    "canonical_witness",
    "targets_in_declaration_order",
]
