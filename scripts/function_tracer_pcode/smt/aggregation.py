# -*- coding: utf-8 -*-
"""**1 つの query** を複数の backend で解いた結果を、1 つの判定にまとめる（Issue #161）。

この規則が扱うのは「同じ query を、設定された backend それぞれで 1 回ずつ解いた行」
だけである。異なる query / region / case の結果を合わせた証拠（monolithic の region
集約、pairwise の case 集約など）は、それを作る producer が自分の判定を明示する
（`ParallelResult` を直接構築する）。ここを通すのは `ParallelResult.from_backend_results`
だけで、runner と単一 query の実行（monolithic の共有 session）が使う。

判定は **backend の結果の集合だけ** で決まる。どの backend が先に終わったか・runner が
どの順で結果を受け取ったかには依らない（行は設定された backend の順に渡される）。

規則（fail closed）:

* backend が `SolverResult.model` の契約を破った行（`witness_contract_violation`）がある:
  判定しない（`CONTRACT_VIOLATION`。その backend は SAT を主張したので、他の UNSAT を
  黙って採らない）
* SAT と UNSAT が両方ある（backend の食い違い）: 判定しない（`SAT_UNSAT_CONFLICT`）
* witness 付きの SAT が複数あり、witness が一致しない: 判定しない
  （`WITNESS_DISAGREEMENT`。canonical witness は query の意味だけで一意に決まるので、
  不一致はどれかの backend の契約違反である）
* UNSAT だけがある: 等価。代表結果は設定順で最初の UNSAT
* SAT だけがある: 非等価。代表結果は設定順で最初の witness 付きの SAT、無ければ設定順で
  最初の SAT（canonical witness を作れない backend の SAT。反例は持たない）
* SAT も UNSAT も無い（TIMEOUT / UNKNOWN / ERROR だけ）: 判定しない

判定しないときは代表結果も反例も無く、`is_equivalent` は None。witness の無い SAT も
食い違いの検出には数える（UNSAT を黙って採らない）。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Sequence

from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus


CONTRACT_VIOLATION = "witness_contract_violation"
SAT_UNSAT_CONFLICT = "sat_unsat_conflict"
WITNESS_DISAGREEMENT = "witness_disagreement"


@dataclass(frozen=True)
class BackendAggregate:
    """1 query の backend 結果の集約。`representative` は判定の根拠になった 1 行。"""

    representative: Optional[SolverResult]
    is_equivalent: Optional[bool]
    #: 判定しなかった理由が backend の食い違い・契約違反なら、その種類
    #: （`CONTRACT_VIOLATION` / `SAT_UNSAT_CONFLICT` / `WITNESS_DISAGREEMENT`）。無ければ None
    conflict: Optional[str] = None

    @property
    def counterexample(self) -> Optional[Dict[str, Any]]:
        """判定の根拠が SAT のときの canonical witness（無ければ None）。"""

        representative = self.representative
        if representative is None or representative.status != SolverStatus.SAT:
            return None
        return representative.model


def aggregate_backend_results(results: Sequence[SolverResult]) -> BackendAggregate:
    """同じ query の `results`（設定された backend の順）を 1 つの判定にまとめる。"""

    if any(result.witness_contract_violation is not None for result in results):
        return BackendAggregate(None, None, CONTRACT_VIOLATION)
    sats = [result for result in results if result.status == SolverStatus.SAT]
    unsats = [result for result in results if result.status == SolverStatus.UNSAT]
    if sats and unsats:
        return BackendAggregate(None, None, SAT_UNSAT_CONFLICT)
    if unsats:
        return BackendAggregate(unsats[0], True)
    if sats:
        witnessed = [result for result in sats if result.model is not None]
        if any(result.model != witnessed[0].model for result in witnessed[1:]):
            return BackendAggregate(None, None, WITNESS_DISAGREEMENT)
        return BackendAggregate((witnessed or sats)[0], False)
    return BackendAggregate(None, None)


__all__ = [
    "BackendAggregate",
    "CONTRACT_VIOLATION",
    "SAT_UNSAT_CONFLICT",
    "WITNESS_DISAGREEMENT",
    "aggregate_backend_results",
]
