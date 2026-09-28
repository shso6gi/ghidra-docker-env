# -*- coding: utf-8 -*-
"""Issue #161: 1 回の solver 実行の状態（期限と中止）は、SAT を確定するまでのどの段でも抜けない。

固定する契約（`smt.execution` / `smt.interface.sat_with_canonical_witness` / z3 backend /
monolithic の共有 session）:

* 中断の規則は全経路で同じ: 明示の中止 → UNKNOWN（中止が期限切れより優先）、実行の期限
  切れ → TIMEOUT。探索の問いの判定不能 → UNKNOWN
* SAT は canonical witness の生成の **前と後** に中断を確かめてから確定する。探索の問いの
  回数（0 回 / 1 回 / 複数回）にも、witness の成分の数（0 個を含む）にも依らない
* UNSAT は初回の check だけで完結する。明示の中止は優先する（中止された実行の確定結果を
  返さない）。期限は従来どおり z3 の timeout が強制する（初回の check が返した UNSAT は
  そのまま）
* unknown は、中断なら中断の規則、そうでなければ各経路の従来の判定
* standalone の `Z3Solver` と monolithic の共有 session の両方で同じ
"""

from __future__ import annotations

import ast
import pathlib
import time

import pytest
import z3

from scripts.function_tracer_pcode.smt.execution import (
    BUDGET_EXHAUSTED,
    CANCELLED,
    ExecutionBudget,
)
from scripts.function_tracer_pcode.smt.interface import SolverStatus
from scripts.function_tracer_pcode.smt.solvers import z3 as z3_backend
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
from scripts.function_tracer_pcode.tests.unit.test_issue161_canonical_witness import (
    SCRIPT as MANY_QUESTIONS,
    _shared_session,
)


PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]
SAT, UNSAT, UNKNOWN, TIMEOUT = (
    SolverStatus.SAT, SolverStatus.UNSAT, SolverStatus.UNKNOWN, SolverStatus.TIMEOUT,
)

#: witness の成分が 0 個（配列だけ）
NO_TARGETS = """(declare-const m (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= (select m #x00) #x01))
(check-sat)
"""
#: 最初の model が既に canonical（x = 0 に決まる。探索の問いは 0 回）
ALREADY_CANONICAL = """(declare-const x (_ BitVec 8))
(assert (= x #x00))
(check-sat)
"""
#: 探索の問いがちょうど 1 回（x = 1 に決まる。最下位 bit の low_zero が UNSAT）
ONE_QUESTION = """(declare-const x (_ BitVec 8))
(assert (= x #x01))
(check-sat)
"""
UNSATISFIABLE = """(declare-const x (_ BitVec 8))
(assert (= x #x01))
(assert (= x #x02))
(check-sat)
"""

SAT_SCRIPTS = {
    "no targets": (NO_TARGETS, 0),
    "already canonical": (ALREADY_CANONICAL, 0),
    "one question": (ONE_QUESTION, 1),
    "many questions": (MANY_QUESTIONS, None),  # 2 回以上
}


class _Token:
    def __init__(self, cancelled=False):
        self.cancelled = cancelled

    def is_cancelled(self):
        return self.cancelled

    def cancel(self):
        self.cancelled = True


class _ScriptedSolver:
    """z3 の solver を包み、最初の `check()` の間に遅延・中止・unknown を起こす。"""

    def __init__(self, inner, *, delay=0.0, during_first_check=None, unknown_reason=None):
        self._inner = inner
        self._delay = delay
        self._during = during_first_check
        self._unknown_reason = unknown_reason
        self.first_check_done = False

    def check(self, *args):
        if self.first_check_done:
            return self._inner.check(*args)
        self.first_check_done = True
        if self._during is not None:
            self._during()
        if self._delay:
            time.sleep(self._delay)
        if self._unknown_reason is not None:
            return z3.unknown
        return self._inner.check(*args)

    def reason_unknown(self):
        if self._unknown_reason is not None:
            return self._unknown_reason
        return self._inner.reason_unknown()

    def __getattr__(self, name):
        return getattr(self._inner, name)


def _script_solvers(monkeypatch, **behaviour):
    made = []
    real_solver = z3.Solver

    def _factory(*args, **kwargs):
        made.append(_ScriptedSolver(real_solver(*args, **kwargs), **behaviour))
        return made[-1]

    monkeypatch.setattr(z3, "Solver", _factory)
    return made


def _count_questions(monkeypatch, on_question=None):
    asked = []
    original = z3_backend._Z3WitnessSession.check_with

    def _counted(self, constraint):
        asked.append(constraint.kind)
        if on_question is not None:
            on_question(len(asked))
        return original(self, constraint)

    monkeypatch.setattr(z3_backend._Z3WitnessSession, "check_with", _counted)
    return asked


def _standalone(script, *, timeout=1, token=None):
    solver = Z3Solver(timeout=timeout)
    assert solver.check_availability()[0]
    return solver.check_equivalence_direct(script, token)


# ---------------------------------------------------------------------------
# 中断の規則（優先順位）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "cancelled, deadline_offset, reason, expected",
    [
        (False, 5.0, None, None),
        (True, 5.0, None, CANCELLED),
        (False, -1.0, None, BUDGET_EXHAUSTED),
        (True, -1.0, None, CANCELLED),            # 両方成り立てば中止が優先
        (False, 5.0, "timeout", BUDGET_EXHAUSTED),
        (False, 5.0, "canceled", None),           # z3 自身の打ち切り（期限内・中止なし）は中断ではない
        (True, 5.0, "timeout", CANCELLED),
        (False, -1.0, "incomplete", BUDGET_EXHAUSTED),
    ],
)
def test_the_interruption_rule_is_one_ordered_rule(cancelled, deadline_offset, reason, expected):
    budget = ExecutionBudget(time.monotonic() + deadline_offset, _Token(cancelled))
    observed = budget.interruption() if reason is None else budget.interruption_after_unknown(reason)
    assert observed == expected


# ---------------------------------------------------------------------------
# 確定経路の分類（何もしなければ SAT で、探索の問いの回数がこうなる）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("case", sorted(SAT_SCRIPTS))
def test_the_sat_paths_cover_zero_one_and_many_witness_questions(monkeypatch, case):
    script, questions = SAT_SCRIPTS[case]
    asked = _count_questions(monkeypatch)
    result = _standalone(script, timeout=10)
    assert result.status == SAT and result.model is not None
    if questions is None:
        assert len(asked) >= 2
    else:
        assert len(asked) == questions


# ---------------------------------------------------------------------------
# standalone Z3: 初回の check の間・後の中断
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("case", sorted(SAT_SCRIPTS))
def test_a_sat_found_after_the_deadline_is_a_timeout_whatever_the_witness_needs(monkeypatch, case):
    script, _questions = SAT_SCRIPTS[case]
    _script_solvers(monkeypatch, delay=1.2)
    asked = _count_questions(monkeypatch)
    result = _standalone(script, timeout=1)
    assert result.status == TIMEOUT
    assert result.model is None
    assert asked == []  # 期限の後に探索を始めない


@pytest.mark.parametrize("case", sorted(SAT_SCRIPTS))
def test_a_sat_found_while_the_execution_was_cancelled_is_unknown(monkeypatch, case):
    script, _questions = SAT_SCRIPTS[case]
    token = _Token()
    _script_solvers(monkeypatch, during_first_check=token.cancel)
    asked = _count_questions(monkeypatch)
    result = _standalone(script, timeout=10, token=token)
    assert result.status == UNKNOWN
    assert result.model is None and CANCELLED in result.error_message
    assert asked == []


@pytest.mark.parametrize("case", sorted(SAT_SCRIPTS))
def test_cancellation_wins_over_the_deadline(monkeypatch, case):
    script, _questions = SAT_SCRIPTS[case]
    token = _Token()
    _script_solvers(monkeypatch, delay=1.2, during_first_check=token.cancel)
    result = _standalone(script, timeout=1, token=token)
    assert result.status == UNKNOWN and CANCELLED in result.error_message


@pytest.mark.parametrize("stop", ["deadline", "cancel"])
def test_the_sat_is_not_finalized_after_the_witness_if_the_execution_stopped(monkeypatch, stop):
    """探索が問い 0 回で終わっても、確定の直前の確認で中断を拾う。"""

    token = _Token()
    original = z3_backend.canonical_declared_model

    def _then_stop(*args, **kwargs):
        witness = original(*args, **kwargs)
        if stop == "cancel":
            token.cancel()
        else:
            time.sleep(1.1)
        return witness

    monkeypatch.setattr(z3_backend, "canonical_declared_model", _then_stop)
    result = _standalone(ALREADY_CANONICAL, timeout=1, token=token)
    assert result.model is None
    assert result.status == (UNKNOWN if stop == "cancel" else TIMEOUT)


def _solver_checks_after(monkeypatch, moment):
    """`moment()` が真になった後に z3 の `check()` が呼ばれた回数を数える。"""

    made = _script_solvers(monkeypatch)
    late = []
    original = _ScriptedSolver.check

    def _check(self, *args):
        if moment():
            late.append(1)
        return original(self, *args)

    monkeypatch.setattr(_ScriptedSolver, "check", _check)
    return made, late


def test_a_cancellation_during_the_witness_search_is_unknown_and_asks_no_more(monkeypatch):
    token = _Token()
    _made, late = _solver_checks_after(monkeypatch, token.is_cancelled)
    _count_questions(monkeypatch, on_question=lambda n: token.cancel() if n == 1 else None)
    result = _standalone(MANY_QUESTIONS, timeout=10, token=token)
    assert result.status == UNKNOWN and CANCELLED in result.error_message
    assert late == []  # 中止の後に solver へ問いを投げない


def test_a_deadline_during_the_witness_search_is_a_timeout_and_asks_no_more(monkeypatch):
    passed = []
    _made, late = _solver_checks_after(monkeypatch, lambda: bool(passed))

    def _pass_the_deadline(n):
        if n == 1:
            time.sleep(1.1)
            passed.append(1)

    _count_questions(monkeypatch, on_question=_pass_the_deadline)
    result = _standalone(MANY_QUESTIONS, timeout=1)
    assert result.status == TIMEOUT and BUDGET_EXHAUSTED in result.error_message
    assert late == []  # 期限の後に solver へ問いを投げない


def test_an_unsat_is_not_returned_from_a_cancelled_execution(monkeypatch):
    token = _Token()
    _script_solvers(monkeypatch, during_first_check=token.cancel)
    result = _standalone(UNSATISFIABLE, timeout=10, token=token)
    assert result.status == UNKNOWN and CANCELLED in result.error_message


def test_an_unsat_the_first_check_returned_keeps_the_existing_timeout_meaning(monkeypatch):
    """UNSAT には初回の check の後の段が無い。期限は z3 の timeout が強制する（従来どおり）。"""

    _script_solvers(monkeypatch, delay=1.2)
    assert _standalone(UNSATISFIABLE, timeout=1).status == UNSAT


@pytest.mark.parametrize(
    "reason, cancel, delay, expected",
    [
        ("canceled", True, 0.95, UNKNOWN),   # 中止: 経過が予算の 90% を越えても TIMEOUT にしない
        ("timeout", False, 0.0, TIMEOUT),
        ("incomplete", False, 0.0, UNKNOWN),
        ("incomplete", False, 1.1, TIMEOUT),  # 期限切れ
    ],
)
def test_an_unknown_first_check_follows_the_interruption_rule(monkeypatch, reason, cancel, delay, expected):
    token = _Token()
    _script_solvers(
        monkeypatch, delay=delay, unknown_reason=reason,
        during_first_check=token.cancel if cancel else None,
    )
    assert _standalone(ALREADY_CANONICAL, timeout=1, token=token).status == expected


# ---------------------------------------------------------------------------
# monolithic の共有 session も同じ規則（中止の入力は無いので期限だけ）
# ---------------------------------------------------------------------------


class _SlowFirstCheck:
    def __init__(self, inner, delay, unknown_reason=None):
        self._inner = inner
        self._delay = delay
        self._unknown_reason = unknown_reason
        self._first = True

    def check(self, *args):
        if self._first:
            self._first = False
            time.sleep(self._delay)
            if self._unknown_reason is not None:
                return z3.unknown
        return self._inner.check(*args)

    def reason_unknown(self):
        return self._unknown_reason or self._inner.reason_unknown()

    def __getattr__(self, name):
        return getattr(self._inner, name)


@pytest.mark.parametrize("case", ["no targets", "already canonical", "one question"])
def test_the_shared_session_does_not_finalize_a_sat_found_after_the_deadline(monkeypatch, case):
    script, _questions = SAT_SCRIPTS[case]
    session = _shared_session([script])
    session._solver = _SlowFirstCheck(session._solver, 1.2)
    asked = _count_questions(monkeypatch)
    item = session.execute(script, 1).results[0]
    assert item.status == TIMEOUT and item.model is None
    assert asked == []


def test_the_shared_session_checks_the_execution_again_before_finalizing(monkeypatch):
    original = z3_backend.canonical_declared_model

    def _then_late(*args, **kwargs):
        witness = original(*args, **kwargs)
        time.sleep(1.1)
        return witness

    monkeypatch.setattr(z3_backend, "canonical_declared_model", _then_late)
    session = _shared_session([ALREADY_CANONICAL])
    item = session.execute(ALREADY_CANONICAL, 1).results[0]
    assert item.status == TIMEOUT and item.model is None


def test_the_shared_session_counts_an_unknown_after_the_deadline_as_a_timeout():
    session = _shared_session([ALREADY_CANONICAL])
    session._solver = _SlowFirstCheck(session._solver, 1.1, unknown_reason="incomplete")
    assert session.execute(ALREADY_CANONICAL, 1).results[0].status == TIMEOUT


def test_the_shared_session_sat_path_is_unchanged_when_nothing_stops(monkeypatch):
    for case in ("no targets", "already canonical", "one question"):
        script, questions = SAT_SCRIPTS[case]
        asked = _count_questions(monkeypatch)
        session = _shared_session([script])
        item = session.execute(script, 10).results[0]
        assert item.status == SAT and item.model is not None
        assert len(asked) == questions
        monkeypatch.undo()


# ---------------------------------------------------------------------------
# 規則: canonical witness を作る経路は、SAT を確定の手順でだけ返す
# ---------------------------------------------------------------------------


def _direct_sat_results(tree):
    """`SolverResult(...)` を status SAT で直接作る呼び出しの行番号。"""

    lines = []
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Call) and getattr(node.func, "id", None) == "SolverResult"):
            continue
        arguments = list(node.args) + [keyword.value for keyword in node.keywords if keyword.arg == "status"]
        for argument in arguments:
            if isinstance(argument, ast.Attribute) and argument.attr == "SAT":
                lines.append(node.lineno)
    return lines


def test_sat_is_finalized_only_by_the_shared_lifecycle():
    """SAT の SolverResult を直接作るのは、確定の手順（`smt/interface.py`）と、canonical
    witness を作らない backend（model は境界で落とす）だけ。"""

    offenders = {}
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        relative = path.relative_to(PACKAGE_ROOT)
        if "tests" in relative.parts:
            continue
        lines = _direct_sat_results(ast.parse(path.read_text(encoding="utf-8")))
        if lines:
            offenders[str(relative)] = lines
    allowed = {"smt/interface.py", "smt/solvers/cvc5.py", "smt/solvers/yices2.py", "smt/solvers/boolector.py"}
    assert set(offenders) <= allowed, offenders
    # 確定の手順の中では、SAT を作るのは sat_with_canonical_witness と契約の写し直しだけ
    interface_tree = ast.parse((PACKAGE_ROOT / "smt" / "interface.py").read_text(encoding="utf-8"))
    owners = {
        function.name for function in ast.walk(interface_tree)
        if isinstance(function, ast.FunctionDef) and _direct_sat_results(function)
    }
    assert owners <= {"sat_with_canonical_witness", "enforce_witness_contract"}, owners


def test_the_static_rule_detects_a_direct_sat():
    tree = ast.parse("SolverResult('z3', SolverStatus.SAT, model={})\nSolverResult(solver_name='z', status=SolverStatus.SAT)\n")
    assert _direct_sat_results(tree) == [1, 2]
