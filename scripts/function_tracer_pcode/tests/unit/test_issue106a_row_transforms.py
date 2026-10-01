# -*- coding: utf-8 -*-
"""Issue #106 PR-106-A（レビュー 5 巡目）: 行を変えても、受理した事実を黙って落とさない。

行（`SolverResult`）を生成・複製・置換する地点はすべて `derive_row`（変える field だけを
指定し、他は引き継ぐ）を通し、答えを外すのは `without_answer` の 1 つの規則だけにした。
ここでは次を固定する:

* 行の状態の契約: 独立した故障（`observed_failure`）は答えと同居しない。witness の契約違反は
  ERROR の行だけ。採用しなかった答えは TIMEOUT の行の `withheld_status`（作った時点で拒む）
* どの変換地点でも、故障・契約違反とその詳細・終わり方・期限の事実は残り、答えを外す変換では
  model と raw_output（query receipt へ写る答えの中身）が残らない（不変条件。期待値は変換の
  実装からではなく、この契約から決める）
* `derive_row` / `without_answer` は、明示的に変える field 以外の **すべての field** を引き継ぐ
  （`dataclasses.fields` で列挙する。field を足しても、転記漏れはこの test が見つける）
* field を 1 つずつ写して行を作り直すコードを production に書かない（静的な検査）
"""

from __future__ import annotations

import ast
import concurrent.futures
import dataclasses
import pathlib

import pytest

from scripts.function_tracer_pcode.core.deadline import Adoption, ExecutionEnd
from scripts.function_tracer_pcode.smt.execution import CANCELLED
from scripts.function_tracer_pcode.smt.interface import (
    BackendTermination,
    SolverResult,
    SolverStatus,
    apply_adoption,
    derive_row,
    enforce_witness_contract,
    execution_end,
    execution_fact,
    interrupted_result,
    without_answer,
)
from scripts.function_tracer_pcode.smt.parallel import collected_after_stop


PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]
QUERY = "(declare-const x (_ BitVec 8))\n(assert (bvugt x #x00))\n(check-sat)"
ANSWERS = (SolverStatus.SAT, SolverStatus.UNSAT)


# ---------------------------------------------------------------------------
# 1. 行の状態の契約（境界で拒む）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("status", ANSWERS)
def test_an_answer_cannot_carry_an_independent_failure(status):
    """レビュー 5 巡目の再現の入口: UNSAT + observed_failure は作れない（黙って落とすのではなく拒む）。

    根拠: `observed_failure` を作るのは `interrupted_result(failure=...)`（中止の UNKNOWN）だけで、
    独立した故障を観測した実行の答えは信頼できない（故障を伝える backend は ERROR を返す）。
    """
    with pytest.raises(ValueError, match="observed failure"):
        SolverResult("b", status, observed_failure="RuntimeError: boom")
    row = SolverResult("b", status)
    with pytest.raises(ValueError, match="observed failure"):
        derive_row(row, observed_failure="RuntimeError: boom")


@pytest.mark.parametrize("status", [SolverStatus.SAT, SolverStatus.UNSAT, SolverStatus.UNKNOWN, SolverStatus.TIMEOUT])
def test_a_contract_violation_is_reported_only_by_an_error_row(status):
    with pytest.raises(ValueError, match="witness contract violation"):
        SolverResult("b", status, witness_contract_violation="missing witness")


@pytest.mark.parametrize("status,withheld", [
    (SolverStatus.UNKNOWN, SolverStatus.UNSAT),   # 行は TIMEOUT でなければならない
    (SolverStatus.TIMEOUT, SolverStatus.ERROR),   # 採用しなかったのは答えだけ
])
def test_a_withheld_answer_is_an_answer_kept_on_a_timeout_row(status, withheld):
    with pytest.raises(ValueError, match="withheld answer"):
        SolverResult("b", status, withheld_status=withheld)


def test_failures_are_still_carried_by_the_rows_that_may_carry_them():
    cancelled = interrupted_result("b", CANCELLED, "token", 0.1, failure="RuntimeError: boom")
    assert cancelled.status is SolverStatus.UNKNOWN and cancelled.observed_failure == "RuntimeError: boom"
    assert execution_fact(cancelled).failure_observed


# ---------------------------------------------------------------------------
# 2. 変換地点ごとの不変条件
# ---------------------------------------------------------------------------


def _done(row=None, *, raises=None):
    future = concurrent.futures.Future()
    if raises is not None:
        future.set_exception(raises)
    else:
        future.set_result(row)
    return future


#: 変換の前の行（取り得る状態を契約の語彙で並べる）
_INPUTS = {
    "error": SolverResult(
        "b", SolverStatus.ERROR, elapsed_time=0.4, error_message="Parse error: x",
        raw_output="(error x)", termination=BackendTermination.COMPLETED, deadline_limited=True,
    ),
    "violation": SolverResult(
        "b", SolverStatus.ERROR, elapsed_time=0.4, error_message="canonical witness contract violated: m",
        witness_contract_violation="m", cause=ExecutionEnd.CONTRACT_VIOLATION, deadline_limited=True,
    ),
    "cancelled_with_failure": interrupted_result("b", CANCELLED, "token", 0.4, failure="RuntimeError: boom"),
    "cancelled": interrupted_result("b", CANCELLED, "token", 0.4),
    "inconclusive": SolverResult("b", SolverStatus.UNKNOWN, elapsed_time=0.4, error_message="incomplete"),
    "timeout": SolverResult("b", SolverStatus.TIMEOUT, elapsed_time=0.4, deadline_limited=True),
    "sat": SolverResult("b", SolverStatus.SAT, elapsed_time=0.4, model={"x": 1}, raw_output="sat\n(model)"),
    "sat_no_witness": SolverResult("b", SolverStatus.SAT, elapsed_time=0.4, model=None, raw_output="sat"),
    "sat_noncanonical": SolverResult("b", SolverStatus.SAT, elapsed_time=0.4, model={"x": 9}, raw_output="sat"),
    # 形の違う witness（宣言されていない入力）: canonical の検査で契約違反になる
    "sat_malformed_witness": SolverResult("b", SolverStatus.SAT, elapsed_time=0.4, model={"y": 1}, raw_output="sat"),
    "unsat": SolverResult("b", SolverStatus.UNSAT, elapsed_time=0.4, raw_output="unsat", deadline_limited=True),
}


def _failure_text(row):
    return " ".join(text for text in (row.error_message, row.observed_failure) if text)


def _failure_detail(row):
    """故障の詳細: 独立した故障の要約があればそれ、無ければ ERROR の行の message。"""
    return row.observed_failure or row.error_message


#: 変換地点（production の関数をそのまま呼ぶ）
_TRANSFORMS = {
    "witness_check_canonical": lambda row: enforce_witness_contract(row, QUERY, canonical=True),
    "witness_check_noncanonical": lambda row: enforce_witness_contract(row, QUERY, canonical=False),
    "adoption_withheld": lambda row: apply_adoption([row], Adoption.WITHHELD)[0],
    "adoption_adoptable": lambda row: apply_adoption([row], Adoption.ADOPTABLE)[0],
    "collected_after_stop": lambda row: collected_after_stop(
        row.solver_name, _done(row), BackendTermination.STOPPED, elapsed=9.0, wait_limited=True,
    ),
}

#: 答えを採用しない変換（期限が打ち切った問い・待つのをやめた実行）
_NOT_ADOPTING = {"adoption_withheld", "collected_after_stop"}


@pytest.mark.parametrize("transform", sorted(_TRANSFORMS))
@pytest.mark.parametrize("state", sorted(_INPUTS))
def test_no_transformation_drops_a_failure_or_leaks_an_answer(transform, state):
    before = _INPUTS[state]
    after = _TRANSFORMS[transform](before)
    # 故障・契約違反の事実とその詳細は残る
    if execution_fact(before).failure_observed:
        assert execution_fact(after).failure_observed, (state, transform)
        assert _failure_detail(before) in _failure_text(after), (state, transform)
    if before.witness_contract_violation is not None:
        assert after.witness_contract_violation == before.witness_contract_violation
    # 契約違反の行は形の違う witness を運ばない（query receipt へ写るので反例として漏れる）
    if after.witness_contract_violation is not None:
        assert after.model is None
    # 答えを採用しない変換は、答え（status・model・raw_output）を残さない。答えだった行は
    # 何を返したかを `withheld_status` に残す
    if transform in _NOT_ADOPTING:
        assert after.status not in ANSWERS
        if before.status in ANSWERS:
            assert after.model is None and after.raw_output is None
            assert after.withheld_status is before.status
    # 誰の行かは変わらない
    assert after.solver_name == before.solver_name


def test_the_witness_check_keeps_the_execution_facts_of_the_row():
    """契約の検査で行を変えても、実行の窓と終わり方（`_keep_window` で写していたもの）が残る。"""
    row = derive_row(_INPUTS["sat_no_witness"], deadline_limited=True, termination=BackendTermination.STOPPED)
    checked = enforce_witness_contract(row, QUERY, canonical=True)
    assert checked.status is SolverStatus.ERROR
    assert (checked.deadline_limited, checked.termination) == (True, BackendTermination.STOPPED)
    assert checked.raw_output == "sat"  # backend の出力は契約違反の詳細として残る


def test_a_worker_exception_after_the_stop_is_kept_as_a_failure():
    row = collected_after_stop(
        "b", _done(raises=RuntimeError("worker died")), BackendTermination.NOT_STOPPABLE,
        elapsed=9.0, wait_limited=True,
    )
    assert row.status is SolverStatus.ERROR and "worker died" in row.error_message
    assert row.termination is BackendTermination.NOT_STOPPABLE and row.deadline_limited is True


# ---------------------------------------------------------------------------
# 3. 変換は明示した field 以外をすべて引き継ぐ（field を足しても転記漏れを検出する）
# ---------------------------------------------------------------------------


def _distinct_values(status):
    """status と両立する、既定と違う値を全 field に入れた行（新しい field は既定の型から作る）。"""

    values = {
        "solver_name": "backend-x",
        "status": status,
        "elapsed_time": 1.25,
        "model": {"x": 3} if status is SolverStatus.SAT else None,
        "error_message": "detail",
        "raw_output": "raw",
        "witness_contract_violation": None,
        "termination": BackendTermination.STOPPED,
        "deadline_limited": True,
        "cause": None,
        "observed_failure": "RuntimeError: boom" if status not in ANSWERS else None,
        "withheld_status": None,
    }
    names = {field.name for field in dataclasses.fields(SolverResult)}
    assert set(values) == names, f"classify the new SolverResult fields: {sorted(names ^ set(values))}"
    return SolverResult(**values)


#: `without_answer` が意図して変える field（ここに無い field は必ず引き継ぐ）
_WITHOUT_ANSWER_RESETS = {
    "status", "cause", "model", "raw_output", "error_message", "deadline_limited",
    "termination", "elapsed_time", "withheld_status",
}


@pytest.mark.parametrize("status", [SolverStatus.UNSAT, SolverStatus.SAT, SolverStatus.UNKNOWN, SolverStatus.TIMEOUT])
def test_without_answer_carries_every_field_it_does_not_reset(status):
    before = _distinct_values(status)
    after = without_answer(before, detail="withheld", deadline_limited=True)
    for field in dataclasses.fields(SolverResult):
        if field.name not in _WITHOUT_ANSWER_RESETS:
            assert getattr(after, field.name) == getattr(before, field.name), field.name


def test_derive_row_carries_every_field_it_is_not_told_to_change():
    before = _distinct_values(SolverStatus.UNKNOWN)
    after = derive_row(before, error_message="changed")
    for field in dataclasses.fields(SolverResult):
        if field.name != "error_message":
            assert getattr(after, field.name) == getattr(before, field.name), field.name


# ---------------------------------------------------------------------------
# 4. 静的: 行を field ごとに写して作り直さない
# ---------------------------------------------------------------------------

_ROW_FIELDS = {field.name for field in dataclasses.fields(SolverResult)}


def test_production_code_never_rebuilds_a_row_field_by_field():
    """`SolverResult(...)` の引数に、別の行の field（``x.solver_name`` など）を写さない。

    別の行から作るなら `derive_row`（変える field だけを指定）か `without_answer` を使う。
    写し直すと、後から足した field を黙って落とす（レビュー 5 巡目: `observed_failure`）。
    """
    offenders = []
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        if "tests" in path.relative_to(PACKAGE_ROOT).parts:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if not (isinstance(node, ast.Call) and getattr(node.func, "id", getattr(node.func, "attr", None)) == "SolverResult"):
                continue
            for keyword in node.keywords:
                value = keyword.value
                if (
                    isinstance(value, ast.Attribute)
                    and value.attr in _ROW_FIELDS
                    and not (isinstance(value.value, ast.Name) and value.value.id == "self")
                ):
                    offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}: {keyword.arg}={ast.unparse(value)}")
    assert offenders == []
