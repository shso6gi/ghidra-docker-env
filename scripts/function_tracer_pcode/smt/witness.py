# -*- coding: utf-8 -*-
"""SAT の witness を **script の意味だけ** で決める（Issue #161）。

solver が SAT のときに返す model は、同じ論理式の解のうちどれか 1 つで、どれを
返すかは solver の内部状態（z3 なら同じ context に先に parse した式の履歴など）で
変わる。反例の replay・NaN の拒否・partition の曖昧さの判定はその 1 つの model を
見るので、判定（NOT_EQ / UNKNOWN）まで solver の履歴で揺れていた。

ここでは witness を次の値に固定する（**canonical witness**）:

    script が宣言する scalar の入力（bit-vector / Bool / Int の定数）を宣言順に並べ、
    成分ごとの順序で **辞書式に最小** の model

成分の順序は、bit-vector が unsigned の整数、Bool が false < true、Int が
「絶対値が小さい順、同じ絶対値なら非負が先」（0, 1, -1, 2, -2, …。Int は下に
有界でないので絶対値で並べる）。値は宣言の sort の Python 型で返す（Bool は `bool`、
bit-vector と Int は `int`）。配列・関数・実数・浮動小数点 sort などの定数は成分に
含めない（最小が定まらない / replay が値として使わない）。

これは script の assertion の集合と宣言順だけで決まる（solver の種類・呼び出しの
順序・先に解いた query・最初に見つかった model に依らない）。求め方は成分ごとの
greedy で、今の model の値から出発する（model-guided）。bit-vector は最上位 bit から
「この bit を 0 にしても充足可能か」を問い、既に 0 の bit は問わない。1 の bit では
先に「この bit から下を全部 0 にできるか」を問い、できればその成分はそこで確定する。
Int は絶対値の上限を二分探索で下げ、最後に符号を決める。

問いの立て方は値を変えない（辞書式最小は 1 つしかない）ので、ここは費用だけの選択。
浮動小数点を含む式では SAT の答えが高く UNSAT の答えが安い（tsafe/normAngle の実測で
SAT 1 回 0.035〜0.8 秒、UNSAT は 1332 回で 0.24 秒）ので、SAT になる問いを減らす順に
問う。費用の改善は #205 が扱う。

**witness の優先（preference）**: 何を「受け入れられる witness」とみなすかは、
witness を使う側（replay の規則。例: 浮動小数点の引数が NaN の反例は証拠にしない）が
決める。使う側は script に nullary な Bool の `define-fun |witness-preference:<k>|`
を置く（assert しないので論理式の意味は変わらない）。witness は k の小さい順に
「その preference を満たせるなら満たす」を確定してから辞書式最小を取る。満たせる
witness があるのに満たさない witness を返すことは無い。

**責務の分け方**: 探索の規則（何が canonical か・どう問うか）はここ 1 箇所。backend
ごとの違い（制約の作り方・一時的な仮定・model の読み方）は `WitnessSession` の実装が
持つ。実行の期限と中止は `smt.execution.ExecutionBudget` が持ち、SAT を確定するまでの
手順（探索の前後の中断確認を含む）は `smt.interface.sat_with_canonical_witness` が持つ。
witness を決められないときは `WitnessUnavailable`（`kind` が予算切れ / 判定不能 / 中止
のどれか）で、それを solver の結果の status へどう写すかは `smt.interface` が決める。
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Dict, Mapping, Optional, Protocol, Sequence, Tuple, Union

from scripts.function_tracer_pcode.smt.execution import BUDGET_EXHAUSTED, CANCELLED


#: 宣言の sort のうち witness の成分になるもの
BITVEC = "bitvec"
BOOL = "bool"
INT = "int"

#: script が witness の優先を宣言する `define-fun` の名前の接頭辞（使う側との契約）
WITNESS_PREFERENCE_PREFIX = "witness-preference:"

#: witness の値（宣言の sort の Python 型: Bool は bool、bit-vector と Int は int）
WitnessValue = Union[bool, int]


def witness_preference_name(order: int) -> str:
    """`order` 番目（小さいほど優先）の preference の SMT-LIB 名（`|` で囲んだ symbol）。"""

    return f"|{WITNESS_PREFERENCE_PREFIX}{int(order)}|"


@dataclass(frozen=True)
class WitnessTarget:
    """witness の成分（宣言された scalar の定数）。

    `name` は宣言に書かれた字面（model の key）、`symbol` は solver の中の名前
    （quoted symbol `|x|` なら `x`）。Bool は幅 1（false < true）、Int は幅を持たない。
    """

    name: str
    width: int
    sort: str = BITVEC
    symbol: str = ""

    @property
    def solver_symbol(self) -> str:
        return self.symbol or self.name


@dataclass(frozen=True)
class Constraint:
    """探索が solver に足す制約（backend が自分の項へ訳す）。

    * `kind="bit"`: bit-vector / Bool の `target` の `bit` 番目が `value`（0 / 1）
    * `kind="low_zero"`: bit-vector / Bool の `target` の `bit` 番目から下がすべて 0
    * `kind="abs_le"`: Int の `target` の絶対値が `value` 以下
    * `kind="eq"`: Int の `target` が `value`
    * `kind="preference"`: script の preference（`preference` はその名前）が成り立つ
    """

    kind: str
    target: Optional[WitnessTarget]
    value: int = 0
    bit: int = 0
    preference: str = ""


#: `WitnessUnavailable.kind`: 中断（`CANCELLED` / `BUDGET_EXHAUSTED`）は実行の状態の owner
#: （`smt.execution`）が定義し、witness の探索に固有なのは判定不能（`INCONCLUSIVE`）だけ
INCONCLUSIVE = "inconclusive"


class WitnessUnavailable(Exception):
    """canonical な witness を決められなかった。

    `kind` は理由の種類（`CANCELLED` / `BUDGET_EXHAUSTED` = 実行が中断された、
    `smt.execution`。`INCONCLUSIVE` = 探索の問いに solver が判定不能を返した）。これを
    受けた backend は SAT を返さず、`smt.interface.interrupted_result` の結果
    （TIMEOUT / UNKNOWN）を返す（`SolverResult.model` の契約）。
    """

    def __init__(self, kind: str, detail: str) -> None:
        if kind not in (BUDGET_EXHAUSTED, INCONCLUSIVE, CANCELLED):
            raise ValueError(f"unknown witness failure kind: {kind}")
        super().__init__(f"{kind}: {detail}")
        self.kind = kind
        self.detail = detail


class WitnessSession(Protocol):
    """1 つの SAT の論理式の上で witness を探す backend 側の窓口。

    session は「現在の model」を 1 つ持つ（最初は元の論理式の SAT の model、以後は
    `check_with` が SAT で返した最後の model）。値は探索用の整数（Bool は 0 / 1）。

    * `values()` — 現在の model での各 target の値（未割当は model completion）
    * `holds(constraint)` — 現在の model で `constraint` が成り立つか（solver に問わない）
    * `check_with(constraint)` — これまで `fix` した制約に `constraint` を **一時的に**
      足して解く。SAT ならその model が現在の model になり、その各 target の値を返す。
      UNSAT なら `None`（現在の model は変わらない）。判定不能・予算切れ・中止は
      `WitnessUnavailable`（問いごとの中断の確認は session が実行の `ExecutionBudget` で行う。
      探索の前後の確認は `smt.interface.sat_with_canonical_witness` が行うので、問いが 0 回
      でも中断をすり抜けない）
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
) -> Dict[str, WitnessValue]:
    """`targets`（宣言順）について辞書式最小の model を返す（値は sort の Python 型）。

    まず `preferences` を順に「満たせるなら満たす」と確定し、その中で成分を宣言順に
    最小へ確定する。不変条件: `values` は常に「元の論理式 ∧ これまで fix した制約」の
    model（= session の現在の model）。終わったときの `values` は、元の論理式の model
    のうち（満たせる preference をすべて満たし）`targets` の値の列が辞書式最小のもの。
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
        if target.sort == INT:
            _minimize_int(session, target, values, adopt)
        else:
            _minimize_bits(session, target, values, adopt)
    return {target.name: witness_value(target, values[target.name]) for target in targets}


def _minimize_bits(session, target, values, adopt) -> None:
    """bit-vector / Bool の成分を unsigned の最小へ確定する（上位 bit から）。"""

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
            return
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


def _minimize_int(session, target, values, adopt) -> None:
    """Int の成分を (絶対値, 負か) の最小へ確定する。

    今の値の絶対値を上限として、「絶対値が m 以下」を二分探索で下げる（SAT なら
    その model の絶対値まで一気に下げる）。上限 m が決まったら、m 未満は充足不能
    なので値は m か -m で、非負を優先する。
    """

    low, high = 0, abs(values[target.name])
    while low < high:
        middle = (low + high) // 2
        smaller = session.check_with(Constraint("abs_le", target, middle))
        if smaller is None:
            low = middle + 1
            continue
        adopt(smaller)
        high = abs(values[target.name])
    session.fix(Constraint("abs_le", target, high))
    if values[target.name] != high:
        positive = session.check_with(Constraint("eq", target, high))
        if positive is not None:
            adopt(positive)
    session.fix(Constraint("eq", target, values[target.name]))


def witness_value(target: WitnessTarget, value: int) -> WitnessValue:
    """探索用の整数を、宣言の sort の Python 型にする。"""

    if target.sort == BOOL:
        return bool(value)
    return int(value)


def unquoted_symbol(name: str) -> str:
    """SMT-LIB の quoted symbol（`|x|`）を solver の中の名前（`x`）にする。"""

    if len(name) >= 2 and name.startswith("|") and name.endswith("|"):
        return name[1:-1]
    return name


_BITVEC_SORT = re.compile(r"\(_ BitVec ([1-9][0-9]*)\)")


def targets_in_declaration_order(
    declarations: Sequence[Tuple[str, str]],
) -> Tuple[WitnessTarget, ...]:
    """`(name, sort text)` の宣言列から witness の成分を宣言順に取り出す。

    bit-vector・Bool・Int だけが成分になる。配列・関数・実数・浮動小数点 sort などの
    解釈は witness に含めない（値としての最小が定まらず、replay も使わない）。
    """

    targets = []
    for name, sort_text in declarations:
        sort_text = sort_text.strip()
        symbol = unquoted_symbol(name)
        if sort_text == "Bool":
            targets.append(WitnessTarget(name, 1, BOOL, symbol))
            continue
        if sort_text == "Int":
            targets.append(WitnessTarget(name, 0, INT, symbol))
            continue
        match = _BITVEC_SORT.fullmatch(sort_text)
        if match is not None:
            targets.append(WitnessTarget(name, int(match.group(1)), BITVEC, symbol))
    return tuple(targets)


def witness_targets(smt_script: str) -> Tuple[WitnessTarget, ...]:
    """script が宣言する witness の成分（宣言順）。SMT-LIB の字面だけを読む（backend 非依存）。"""

    return targets_in_declaration_order(_declared_sorts(smt_script))


def witness_preferences(smt_script: str) -> Tuple[str, ...]:
    """script が宣言する witness の preference の名前（優先順）。"""

    return _declared_preferences(smt_script)


def witness_contract_violation(
    targets: Sequence[WitnessTarget], model: Optional[Mapping[str, object]],
) -> Optional[str]:
    """`model` が canonical witness の **形** を満たさなければ理由を返す（満たせば None）。

    形: `targets` のすべてを、ちょうどそれだけ束縛し、値が sort の Python 型と範囲に
    収まる（Bool は bool、Int は int、bit-vector は 0 以上 2**幅 未満の int）。最小性は
    ここでは検査しない（同じ query を解いた canonical backend どうしの一致は
    `smt.aggregation` が検査する）。
    """

    if model is None:
        return "a SAT from a canonical witness provider carries no witness"
    names = [target.name for target in targets]
    if set(model) != set(names):
        missing = sorted(set(names) - set(model))
        extra = sorted(set(model) - set(names))
        return f"the witness does not bind exactly the declared inputs (missing={missing}, extra={extra})"
    for target in targets:
        value = model[target.name]
        if target.sort == BOOL:
            if type(value) is not bool:
                return f"{target.name} is Bool but the witness value is {type(value).__name__}"
            continue
        if type(value) is not int:
            return f"{target.name} needs an int but the witness value is {type(value).__name__}"
        if target.sort == BITVEC and not 0 <= value < (1 << target.width):
            return f"{target.name} is out of range for (_ BitVec {target.width})"
    return None


#: SMT-LIB の symbol（quoted symbol `|...|` は空白を含み得るので 1 つの名前として読む）
_SYMBOL = r"(?:\|[^|]*\||[^\s()|]+)"
_DECLARATION_RE = re.compile(
    r"^\(declare-(?:const\s+(" + _SYMBOL + r")|fun\s+(" + _SYMBOL + r")\s+\(\))\s+(.+)\)$",
    re.DOTALL,
)


def _top_level_smt_commands(smt_script: str) -> tuple[str, ...]:
    """Split SMT-LIB into top-level commands without parsing rendered terms."""

    commands = []
    start = None
    depth = 0
    in_string = False
    in_quoted_symbol = False
    in_comment = False
    escaped = False
    for index, char in enumerate(smt_script):
        if in_comment:
            if char == "\n":
                in_comment = False
            continue
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue
        if in_quoted_symbol:
            if char == "|":
                in_quoted_symbol = False
            continue
        if char == ";":
            in_comment = True
        elif char == '"':
            in_string = True
        elif char == "|":
            in_quoted_symbol = True
        elif char == "(":
            if depth == 0:
                start = index
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                raise ValueError("SMT-LIB command parentheses are unbalanced")
            if depth == 0 and start is not None:
                commands.append(smt_script[start:index + 1])
                start = None
    if depth or in_string or in_quoted_symbol:
        raise ValueError("SMT-LIB command surface is incomplete")
    return tuple(commands)


def _declared_sorts(smt_script: str) -> tuple:
    """script の定数宣言を宣言順に ``(name, sort text)`` で返す（重複は拒否）。"""

    declarations = []
    declared_names = set()
    for command in _top_level_smt_commands(smt_script):
        match = _DECLARATION_RE.fullmatch(command.strip())
        if match is None:
            continue
        name = match.group(1) or match.group(2)
        if name in declared_names:
            raise ValueError(f"duplicate SMT declaration: {name}")
        declared_names.add(name)
        declarations.append((name, match.group(3).strip()))
    return tuple(declarations)


_PREFERENCE_RE = re.compile(
    r"^\(define-fun\s+(\|" + re.escape(WITNESS_PREFERENCE_PREFIX) + r"([0-9]+)\|)\s+\(\)\s+Bool\s",
    re.DOTALL,
)


def _declared_preferences(smt_script: str) -> tuple:
    """script が宣言する witness の preference の名前（優先順）。"""

    found = []
    for command in _top_level_smt_commands(smt_script):
        match = _PREFERENCE_RE.match(command.strip())
        if match is not None:
            found.append((int(match.group(2)), match.group(1)))
    return tuple(name for _order, name in sorted(found))


__all__ = [
    "BITVEC",
    "BOOL",
    "INT",
    "BUDGET_EXHAUSTED",
    "CANCELLED",
    "INCONCLUSIVE",
    "WITNESS_PREFERENCE_PREFIX",
    "witness_preference_name",
    "Constraint",
    "WitnessSession",
    "WitnessTarget",
    "WitnessUnavailable",
    "WitnessValue",
    "canonical_witness",
    "targets_in_declaration_order",
    "unquoted_symbol",
    "witness_contract_violation",
    "witness_preferences",
    "witness_targets",
    "witness_value",
]
