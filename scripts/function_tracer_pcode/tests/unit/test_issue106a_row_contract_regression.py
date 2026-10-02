# -*- coding: utf-8 -*-
"""Issue #106 PR-106-A（レビュー 5 巡目）の回帰: 修正前の head（c1eb5a05）にもある API だけで書く。

再現: UNSAT + observed_failure → 期限超過 → KEEP_FAILURE → 答えを外す変換で、故障の事実
（`observed_failure`・`failure_observed`）が消えた。witness の検査（非 canonical の SAT から model を
外す変換）でも同じく、field を写して作り直すので故障・実行の事実が落ちた。

契約（`SolverResult.__post_init__`）: 独立した故障は答えと同居しない（境界で拒む）。答えを
持たない行の故障・実行の事実は、どの変換でも残る。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.core.deadline import Adoption
from scripts.function_tracer_pcode.smt.interface import (
    BackendTermination,
    SolverResult,
    SolverStatus,
    apply_adoption,
    enforce_witness_contract,
    execution_fact,
)

QUERY = "(declare-const x (_ BitVec 8))\n(assert (bvugt x #x00))\n(check-sat)"


@pytest.mark.parametrize("transform", ["withheld", "noncanonical_witness_check"])
@pytest.mark.parametrize("status", [SolverStatus.UNSAT, SolverStatus.SAT])
def test_an_answer_with_an_observed_failure_is_refused_instead_of_losing_the_failure(status, transform):
    """修正前: 行は作れて、変換の後に故障が消えた（failure_observed True → False）。"""
    try:
        row = SolverResult("b", status, model={"x": 1} if status is SolverStatus.SAT else None,
                           observed_failure="RuntimeError: boom")
    except ValueError:
        return  # 契約: 境界で拒む
    after = (
        apply_adoption([row], Adoption.WITHHELD)[0] if transform == "withheld"
        else enforce_witness_contract(row, QUERY, canonical=False)
    )
    assert execution_fact(after).failure_observed is execution_fact(row).failure_observed


def test_the_witness_check_keeps_the_execution_facts_of_the_row_it_changes():
    """修正前: 非 canonical の SAT から model を外す変換が、行の終わり方・期限の事実を落とした。"""
    row = SolverResult(
        "b", SolverStatus.SAT, model={"x": 9}, raw_output="sat",
        termination=BackendTermination.STOPPED, deadline_limited=True,
    )
    checked = enforce_witness_contract(row, QUERY, canonical=False)
    assert checked.model is None
    assert (checked.termination, checked.deadline_limited, checked.raw_output) == (
        BackendTermination.STOPPED, True, "sat",
    )


def test_the_canonical_witness_check_keeps_the_execution_facts_of_the_row_it_changes():
    row = SolverResult(
        "b", SolverStatus.SAT, model=None, termination=BackendTermination.STOPPED, deadline_limited=True,
    )
    checked = enforce_witness_contract(row, QUERY, canonical=True)
    assert checked.status is SolverStatus.ERROR and checked.witness_contract_violation is not None
    assert (checked.termination, checked.deadline_limited) == (BackendTermination.STOPPED, True)
