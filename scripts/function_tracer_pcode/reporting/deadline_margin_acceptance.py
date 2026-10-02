# -*- coding: utf-8 -*-
"""ANALYSIS_TIMEOUT_MARGIN の受理判定: 計測集合の適格性・採用式・3 値の判定（Issue #106 PR-106-B）。

`deadline_margin_summary` が run の出力から作った観測（終了の分類・期限で打ち切ったか・区間と
欠測の理由）を受け取り、ある runner profile の margin が足りるかを決める。判定にも runner の
policy にも入力を渡さない（報告だけを作る）。規則はこの module にだけある:

## 計測集合（pool）と適格性（集計の前に決まる）

run 単位の規則。満たさない run を pool に渡すと判定不能になる（黙って除外しない）。

* ``P``（profile の計測。``pre`` ``overrun`` ``post_trip`` ``tail`` ``lead`` を使う）:
  期限の機構が評価対象と同じ code（`MarginProfile.machinery_commits` のどれかの commit の clean な
  tree）、process の期限が profile と同じ、解析の期限が profile の期限 **以上**、pair の sample が
  profile の母集団（固定 subset なら `eqbench_subset.json` の Eq / Neq の source）の中。並列度は
  問わない。
* ``L``（負荷の pool。``pre`` ``overrun`` を使う）: 期限の機構が同じ code（clean な tree）の、
  期限つきの run。profile・期限の長さ・並列度・負荷は問わない。
* ``F``（固定費の pool。``pre`` だけを使う）: 期限つきの run。code を問わない（``pre`` は期限の
  機構に依らない）。
* どの pool でも、解析の期限を持たない run（OFF）は入れられない。

* ``post_trip`` / ``tail`` は打ち切るまでに解析が作った状態の大きさで伸びる。だから profile の
  期限 **以上** の期限の run から取れば上界になる（期限の短い run は過小評価になるので入れない）。
* ``pre`` / ``overrun`` は負荷と checkpoint の無い区間の長さで決まり、期限の長さには依らない。
  共有 host では runner が負荷を制限しないので、観測した高負荷の値も除かない。並列度の高い run も
  低い run も入れる（最大を取るので、高い負荷を入れて過小評価になることは無い）。

## 採用式

``required = max_{P∪L∪F} pre + max_{P∪L} overrun + max_P post_trip + max_P tail + max_P lead``

## 3 値の判定（判定不能を PASS にしない）

* ``holds``: 全 pool が適格で、各 pool の期限で打ち切った pair すべてについて、その pool が使う
  区間が観測でき、採用式の各項に標本があり、``required <= margin`` で、``P`` の pair の
  ``needed + lead`` がすべて margin 以下。
* ``violated``: margin が足りない証拠がある: ``P`` / ``L`` に process の TIMEOUT（supervisor の
  wall clock、`timeout_kind`）、lead window に入った pair、``required > margin``、margin を越えた
  ``P`` の pair。
* ``undetermined``: 証拠が足りない: profile の情報の欠け、適格でない run、``P`` / ``L`` の
  `timeout_kind` が確かめられない TIMEOUT や終了の証拠の壊れた pair、打ち切ったかどうか読めない
  pair、区間の欠測、打ち切った pair の無い pool、標本の無い項。

違反の理由（``violations``）と証拠の足りない理由（``undetermined``）は、件数を潰さずにすべて返す。checker 自身の
solver の terminal timeout（`child_solver_timeout`）は process の TIMEOUT と区別して扱う（margin の
事象ではない）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

POOL_P = "P"
POOL_L = "L"
POOL_F = "F"
POOLS = (POOL_P, POOL_L, POOL_F)

#: 採用式の項と、最大を取る pool
TERM_POOLS: Mapping[str, Tuple[str, ...]] = {
    "pre": (POOL_P, POOL_L, POOL_F),
    "overrun": (POOL_P, POOL_L),
    "post_trip": (POOL_P,),
    "tail": (POOL_P,),
}
#: pool が使う区間（= その pool の打ち切った pair で観測が必須の区間）
POOL_INTERVALS: Mapping[str, Tuple[str, ...]] = {
    pool: tuple(term for term, pools in TERM_POOLS.items() if pool in pools) for pool in POOLS
}

STATUS_HOLDS = "holds"
STATUS_VIOLATED = "violated"
STATUS_UNDETERMINED = "undetermined"

#: 終了の分類（`deadline_margin_summary` が `timeout_kind` から作る語彙）
TERMINATION_RESOLVED = "resolved"
TERMINATION_PROCESS_TIMEOUT = "process_timeout"
TERMINATION_SOLVER_TIMEOUT = "solver_timeout"
TERMINATION_TIMEOUT_UNCLASSIFIED = "timeout_unclassified"
TERMINATION_INVALID = "termination_invalid"


@dataclass(frozen=True)
class MarginProfile:
    """margin を判定する runner profile（値が ``None`` の項目は判定不能の理由になる）。"""

    name: str
    deadline_seconds: Optional[float]
    margin_seconds: Optional[float]
    pair_process_timeout_seconds: Optional[float]
    #: 母集団の sample identity（``None`` は EqBench 全体）
    population: Optional[frozenset] = None
    #: 期限の機構（`core/deadline.py`・solver の停止・checkpoint の配置）が対象と同じ code の commit
    machinery_commits: Optional[frozenset] = None


@dataclass
class MarginVerdict:
    status: str
    required_margin_seconds: Optional[float]
    terms: Dict[str, Dict[str, Any]]
    pairs_over_margin: List[str] = field(default_factory=list)
    violations: List[str] = field(default_factory=list)
    undetermined: List[str] = field(default_factory=list)

    @property
    def holds(self) -> bool:
        return self.status == STATUS_HOLDS

    def to_dict(self) -> Dict[str, Any]:
        return {
            "status": self.status,
            "required_margin_seconds": self.required_margin_seconds,
            "terms": self.terms,
            "pairs_over_margin": list(self.pairs_over_margin),
            "violations": list(self.violations),
            "undetermined": list(self.undetermined),
        }


def _commit_listed(commit: Optional[str], listed: Iterable[str]) -> bool:
    """``commit``（manifest の完全な SHA）が一覧のどれか（完全な SHA か 8 桁以上の接頭辞）か。"""

    if not commit:
        return False
    return any(len(entry) >= 8 and commit.startswith(entry) for entry in listed)


def run_eligibility_problems(pool: str, run: Any, profile: MarginProfile) -> List[str]:
    """``run``（`deadline_margin_summary.RunObservation`）が ``pool`` に入れない理由（空なら適格）。"""

    facts = run.facts
    where = f"pool {pool}: run {facts.root}"
    problems: List[str] = []
    if facts.deadline_off:
        problems.append(f"{where}: ran without the analysis deadline")
        return problems
    if facts.deadline_seconds is None:
        problems.append(f"{where}: its analysis deadline is not recorded ({facts.deadline_note})")
    if pool in (POOL_P, POOL_L):
        if profile.machinery_commits is None:
            problems.append(f"{where}: the deadline machinery commits are not given")
        elif not _commit_listed(facts.git_commit, profile.machinery_commits):
            problems.append(
                f"{where}: commit {facts.git_commit} does not have the deadline machinery "
                "under evaluation"
            )
        elif facts.git_dirty is not False:
            problems.append(
                f"{where}: the tree was not clean (git_dirty={facts.git_dirty}), so its deadline "
                "machinery is not the listed commit's"
            )
    if pool == POOL_P:
        if profile.deadline_seconds is None or profile.pair_process_timeout_seconds is None:
            problems.append(f"{where}: the profile deadline / process timeout are not given")
        else:
            if facts.deadline_seconds is not None and facts.deadline_seconds < profile.deadline_seconds:
                problems.append(
                    f"{where}: deadline {facts.deadline_seconds:g}s is shorter than the "
                    f"profile's {profile.deadline_seconds:g}s"
                )
            if facts.pair_process_timeout_seconds != profile.pair_process_timeout_seconds:
                problems.append(
                    f"{where}: process timeout {facts.pair_process_timeout_seconds} is not the "
                    f"profile's {profile.pair_process_timeout_seconds:g}s"
                )
        if profile.population is not None:
            outside = sorted(set(facts.samples) - set(profile.population))
            if outside:
                problems.append(f"{where}: {len(outside)} sample(s) outside the profile, e.g. {outside[0]}")
    return problems


def _pair_findings(
    pool: str, pair: Any,
) -> Tuple[List[str], List[str]]:
    """1 pair の (violations, undetermined)。"""

    violations: List[str] = []
    undetermined: List[str] = []
    where = f"pool {pool}: pair {pair.key}"
    if pool in (POOL_P, POOL_L):
        if pair.termination == TERMINATION_PROCESS_TIMEOUT:
            violations.append(f"{where}: process TIMEOUT in a run with the deadline")
        elif pair.termination == TERMINATION_TIMEOUT_UNCLASSIFIED:
            undetermined.append(f"{where}: timeout_unclassified (timeout_kind not established)")
        elif pair.termination == TERMINATION_INVALID:
            undetermined.append(f"{where}: termination evidence invalid")
        if pair.entered_lead_window:
            violations.append(f"{where}: still running when the stack-dump send started")
    if pair.cut is None:
        undetermined.append(f"{where}: cannot tell whether the deadline cut it ({pair.cut_unknown_reason})")
        return violations, undetermined
    if pair.cut:
        for interval in POOL_INTERVALS[pool]:
            if interval in pair.missing:
                undetermined.append(f"{where}: {interval} unobserved ({pair.missing[interval]})")
        if pool == POOL_P and pair.lead_seconds is None:
            undetermined.append(f"{where}: lead unobserved (no stack-dump status sidecar)")
    return violations, undetermined


def evaluate_margin(
    profile: MarginProfile, pools: Mapping[str, Sequence[Any]],
) -> MarginVerdict:
    """``pools`` = pool 名 → `RunObservation` の列。判定の唯一の規則（module docstring）。"""

    violations: List[str] = []
    undetermined: List[str] = []
    if profile.margin_seconds is None:
        undetermined.append("profile: the margin under evaluation is not given")
    elif (profile.deadline_seconds is not None and profile.pair_process_timeout_seconds is not None
          and profile.deadline_seconds + profile.margin_seconds
          > profile.pair_process_timeout_seconds):
        undetermined.append(
            "profile: deadline + margin exceeds the process timeout (the runner refuses it)"
        )
    if not pools.get(POOL_P):
        undetermined.append("pool P: no run given")
    samples: Dict[str, List[Tuple[float, str]]] = {term: [] for term in TERM_POOLS}
    leads: List[float] = []
    p_pairs: List[Any] = []
    for pool in POOLS:
        runs = list(pools.get(pool) or ())
        if not runs:
            continue
        cut_pairs = 0
        for run in runs:
            undetermined.extend(run_eligibility_problems(pool, run, profile))
            for pair in run.pairs:
                pair_violations, pair_undetermined = _pair_findings(pool, pair)
                violations.extend(pair_violations)
                undetermined.extend(pair_undetermined)
                if not pair.cut:
                    continue
                cut_pairs += 1
                for term, term_pools in TERM_POOLS.items():
                    if pool in term_pools and term in pair.values:
                        samples[term].append((pair.values[term], pair.key))
                if pool == POOL_P:
                    p_pairs.append(pair)
                    if pair.lead_seconds is not None:
                        leads.append(pair.lead_seconds)
        if cut_pairs == 0:
            undetermined.append(f"pool {pool}: no deadline-cut pair (nothing measured)")
    terms: Dict[str, Dict[str, Any]] = {}
    for term, values in samples.items():
        if not values:
            undetermined.append(f"term {term}: no sample")
            terms[term] = {"n": 0}
            continue
        value, key = max(values)
        terms[term] = {"n": len(values), "max": round(value, 3), "max_pair": key}
    terms["lead"] = (
        {"n": len(leads), "max": round(max(leads), 3)} if leads else {"n": 0}
    )
    if not leads:
        undetermined.append("term lead: no sample")
    required = None
    if all(terms[term].get("n") for term in (*TERM_POOLS, "lead")):
        required = round(sum(terms[term]["max"] for term in (*TERM_POOLS, "lead")), 3)
    over: List[str] = []
    if profile.margin_seconds is not None:
        for pair in p_pairs:
            needed = pair.needed
            if needed is not None and pair.lead_seconds is not None \
                    and needed + pair.lead_seconds > profile.margin_seconds:
                over.append(pair.key)
        if over:
            violations.append(f"{len(over)} profile pair(s) needed more than the margin")
        if required is not None and required > profile.margin_seconds:
            violations.append(
                f"required {required:g}s exceeds the margin {profile.margin_seconds:g}s"
            )
    if violations:
        status = STATUS_VIOLATED
    elif undetermined:
        status = STATUS_UNDETERMINED
    else:
        status = STATUS_HOLDS
    return MarginVerdict(
        status=status, required_margin_seconds=required, terms=terms,
        pairs_over_margin=over, violations=violations, undetermined=undetermined,
    )
