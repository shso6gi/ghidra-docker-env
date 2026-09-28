# -*- coding: utf-8 -*-
"""1 つの query に対する backend の結果を 1 つの判定にまとめる（Issue #161）。

複数の backend で同じ query を解くとき、判定は **backend の結果の集合だけ** で決まる。
どの backend が先に終わったか・runner がどの順で結果を受け取ったかには依らない
（runner は全 backend の結果を、設定された backend の順に並べて渡す）。

規則（fail closed）:

* SAT と UNSAT が両方ある（backend の食い違い）: 判定しない。代表結果も反例も無く、
  `is_equivalent` は None（等価にも非等価にもしない）
* UNSAT だけがある: 等価。代表結果は設定順で最初の UNSAT
* SAT だけがある: 非等価。代表結果は設定順で最初の **canonical witness 付き** の SAT、
  無ければ設定順で最初の SAT（canonical witness を作れない backend の SAT。反例は
  持たないので、反例を要る consumer は受け入れない = fail closed）
* SAT も UNSAT も無い（TIMEOUT / UNKNOWN / ERROR だけ）: 判定しない

witness の無い SAT も食い違いの検出には数える（UNSAT を黙って採らない）。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Sequence

from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus


@dataclass(frozen=True)
class BackendAggregate:
    """backend の結果の集約。`representative` は判定の根拠になった 1 行。"""

    representative: Optional[SolverResult]
    is_equivalent: Optional[bool]
    conflict: bool = False


def aggregate_backend_results(results: Sequence[SolverResult]) -> BackendAggregate:
    """`results`（設定された backend の順）を 1 つの判定にまとめる。"""

    sats = [result for result in results if result.status == SolverStatus.SAT]
    unsats = [result for result in results if result.status == SolverStatus.UNSAT]
    if sats and unsats:
        return BackendAggregate(None, None, conflict=True)
    if unsats:
        return BackendAggregate(unsats[0], True)
    if sats:
        witnessed = [result for result in sats if result.model is not None]
        return BackendAggregate((witnessed or sats)[0], False)
    return BackendAggregate(None, None)


__all__ = ["BackendAggregate", "aggregate_backend_results"]
