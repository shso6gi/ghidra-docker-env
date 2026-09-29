# -*- coding: utf-8 -*-
"""Issue #105 PR-105-B: 条件簡約の予算（三値）（計画 v5 §6.B-2、D1-B・D5〜D7・D10・D14）。

固定する契約:

* DPLL の答えは三値の `SatVerdict`。`INDETERMINATE`（決定回数の予算で打ち切った）は
  真偽値にならず、「充足不能か」へ写すと `None`（判定できない）で、`True` にならない
* 決定回数の予算は最上位の問い合わせ 1 回に 1 つで、再帰の枝で共有する（枝ごとに戻さない）
* 条件 oracle の query 予算は pair に 1 つ。solver へ発行する地点だけで使い、cache hit は
  使わない。尽きたら solver を呼ばずに `None`（覚えない）
* 予算が尽きても限界・UNKNOWN の reason にはならず、元の条件を残す。診断
  （`diagnostics.condition_simplify.budget_events`）に残るだけで判定へ戻らない
* 予算の値は `BudgetPolicy` だけが持ち、`None`（無制限）でも三値の構造は残る
"""

from __future__ import annotations

import ast
import pathlib
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.analysis.condition import simplifier_cnf
from scripts.function_tracer_pcode.analysis.condition.condition_cache import (
    cache_lookup,
    condition_cache_scope,
)
from scripts.function_tracer_pcode.analysis.condition.query_identity import SolverQueryIdentity
from scripts.function_tracer_pcode.analysis.condition.simplifier import (
    ConditionSimplifier,
    ConditionSMTOracle,
)
from scripts.function_tracer_pcode.analysis.condition import smt_oracle
from scripts.function_tracer_pcode.analysis.condition.simplifier_cnf import (
    SatVerdict,
    SatVerdictTruthinessError,
)
from scripts.function_tracer_pcode.core import Condition, Expression, LocationBaseRef
from scripts.function_tracer_pcode.core.budget_policy import (
    BudgetKind,
    BudgetPolicy,
    FallbackBudgetKind,
    FallbackBudgetMeter,
    budget_policy_scope,
    enforce_budget,
    pair_fallback_meter,
)
from scripts.function_tracer_pcode.core.condition_metrics import (
    MAX_BUDGET_EVENTS,
    condition_metrics_scope,
    pairwise_debug_counters,
)


PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]
DPLL = FallbackBudgetKind.DPLL_DECISIONS
ORACLE = FallbackBudgetKind.ORACLE_QUERIES


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------


def _meter(limit):
    return FallbackBudgetMeter(DPLL, limit)


def _lit(name, polarity=True):
    """命題 atom `name` の literal（項は文字列: 並べ替え key は名前順）。"""

    return ((name, "==", 1), polarity)


def _clause(*literals):
    return tuple(sorted(literals, key=ConditionSimplifier._literal_sort_key))


def _sat(clauses, budget):
    return ConditionSimplifier._clauses_satisfiability(
        [_clause(*clause) for clause in clauses], None, budget
    )


def _record_calls(monkeypatch):
    """`_clauses_satisfiability` の呼び出し（割当と予算 object）を記録する。"""

    calls = []
    original = ConditionSimplifier._clauses_satisfiability.__func__

    def _recording(cls, clauses, assignments, budget):
        calls.append((dict(assignments or {}), budget))
        return original(cls, clauses, assignments, budget)

    monkeypatch.setattr(ConditionSimplifier, "_clauses_satisfiability", classmethod(_recording))
    return calls


def _param(name, index, size=4):
    return Expression.parameter(
        name, index=index, size=size,
        runtime_ref=LocationBaseRef.parameter(name, index=index),
    )


_ATOMS = {
    name: Expression.binary_op("INT_EQUAL", _param(f"param_{name}", index), Expression.constant(1, size=4))
    for index, name in enumerate("abcw")
}


def _expr_literal(name, polarity):
    atom = _ATOMS[name]
    return atom if polarity else Expression.unary_op("BOOL_NEGATE", atom)


def _three_variable_contradiction():
    """a, b, c の 8 通りの符号の節（充足不能）。反駁に DPLL の決定が 3 つ要る。

    a で分岐 → 各枝で b で分岐 → c が unit 同士で矛盾。決定は a, b(a=真), b(a=偽) の 3 つ。
    """

    conditions = []
    for sa in (True, False):
        for sb in (True, False):
            for sc in (True, False):
                left = Expression.binary_op("BOOL_OR", _expr_literal("a", sa), _expr_literal("b", sb))
                conditions.append(Condition(Expression.binary_op("BOOL_OR", left, _expr_literal("c", sc))))
    return conditions


@pytest.fixture
def scoped():
    with condition_cache_scope() as store, condition_metrics_scope() as metrics:
        yield SimpleNamespace(store=store, metrics=metrics)


@pytest.fixture
def dpll_only(monkeypatch):
    """solver を使わず CNF + DPLL だけで答える（DPLL の予算の効き方を見るため）。"""

    monkeypatch.setattr(
        ConditionSimplifier, "_should_use_solver_reasoning", classmethod(lambda cls, conds: False)
    )


# ---------------------------------------------------------------------------
# SatVerdict: 真偽値にならない / 写し方は 1 つ
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("verdict", list(SatVerdict))
def test_d1b_a_verdict_has_no_truth_value(verdict):
    """`not verdict` / `if verdict:` / `bool(verdict)` は INDETERMINATE を二値に化かすので禁止。"""

    with pytest.raises(SatVerdictTruthinessError):
        bool(verdict)
    with pytest.raises(SatVerdictTruthinessError):
        not verdict  # noqa: B015 - 評価そのものが禁止されていることを確かめる
    # 条件簡約の回復可能な例外（`TypeError` / `ValueError` ...）ではない: 握り潰されない
    assert not issubclass(SatVerdictTruthinessError, simplifier_cnf._CONDITION_RECOVERABLE_ERRORS)


def test_d1b_the_unsat_answer_of_each_verdict():
    assert SatVerdict.UNSAT.as_unsat_answer() is True
    assert SatVerdict.SAT.as_unsat_answer() is False
    assert SatVerdict.INDETERMINATE.as_unsat_answer() is None


def _calls_named(tree, name):
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == name:
            yield node


def _package_sources():
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        if "tests" in path.relative_to(PACKAGE_ROOT).parts:
            continue
        yield path, ast.parse(path.read_text(encoding="utf-8"))


def test_d1b_no_verdict_is_read_as_a_boolean_anywhere():
    """D1-B（AST）: DPLL の答えを真偽値の文脈に置かない（`not` / `if` / `while` / `bool()` /
    `and` / `or` / 条件式）。旧二値 API（`_clauses_are_satisfiable`）も残っていない。"""

    offenders = []
    for path, tree in _package_sources():
        boolean_contexts = []
        for node in ast.walk(tree):
            if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
                boolean_contexts.append(node.operand)
            elif isinstance(node, (ast.If, ast.While, ast.IfExp, ast.Assert)):
                boolean_contexts.append(node.test)
            elif isinstance(node, ast.BoolOp):
                boolean_contexts.extend(node.values)
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "bool":
                boolean_contexts.extend(node.args)
        for expr in boolean_contexts:
            if (
                isinstance(expr, ast.Call)
                and isinstance(expr.func, ast.Attribute)
                and expr.func.attr == "_clauses_satisfiability"
            ):
                offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{expr.lineno}")
        for node in ast.walk(tree):
            if isinstance(node, (ast.Attribute, ast.Name)) and getattr(node, "attr", getattr(node, "id", None)) == "_clauses_are_satisfiable":
                offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno} (old binary API)")
    assert offenders == []


def test_d1b_the_verdict_has_one_owner_and_one_projection():
    """`SatVerdict` の定義は `simplifier_cnf` だけ、「充足不能か」への写し（`as_unsat_answer`）は
    DPLL の最上位（`_clause_set_is_unsat`）だけ。"""

    definitions, projections = [], []
    for path, tree in _package_sources():
        relative = str(path.relative_to(PACKAGE_ROOT))
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef) and node.name == "SatVerdict":
                definitions.append(relative)
        for function in ast.walk(tree):
            if isinstance(function, ast.FunctionDef):
                for call in _calls_named(function, "as_unsat_answer"):
                    projections.append((relative, function.name))
    assert definitions == ["analysis/condition/simplifier_cnf.py"]
    assert projections == [("analysis/condition/simplifier_cnf.py", "_clause_set_is_unsat")]


def test_d5_the_recursion_passes_the_same_budget_object():
    """AST: 再帰の呼び出しは受け取った `budget` をそのまま渡す（枝ごとに予算を作り直さない）。
    DPLL の予算を作るのは最上位（`_clause_set_is_unsat`）だけ。"""

    tree = ast.parse((PACKAGE_ROOT / "analysis" / "condition" / "simplifier_cnf.py").read_text(encoding="utf-8"))
    functions = {node.name: node for node in ast.walk(tree) if isinstance(node, ast.FunctionDef)}
    recursive = list(_calls_named(functions["_clauses_satisfiability"], "_clauses_satisfiability"))
    assert len(recursive) == 2
    for call in recursive:
        assert len(call.args) == 3 and isinstance(call.args[2], ast.Name) and call.args[2].id == "budget"

    creators = []
    for path, source_tree in _package_sources():
        for function in ast.walk(source_tree):
            if isinstance(function, ast.FunctionDef):
                for call in _calls_named(function, "for_active_policy"):
                    creators.append((str(path.relative_to(PACKAGE_ROOT)), function.name))
    assert creators == [("analysis/condition/simplifier_cnf.py", "_clause_set_is_unsat")]


# ---------------------------------------------------------------------------
# D5: DPLL の三値の伝搬
# ---------------------------------------------------------------------------

#: p で分岐。p=真 は unit propagation で矛盾（r と ¬r）、p=偽 は q が unit になり、残る
#: (s ∨ t) / (¬s ∨ t) の充足にもう 1 つ決定が要る（全体は充足可能）
_TRUE_UNSAT_FALSE_NEEDS_DECISION = [
    (_lit("p"), _lit("q")),
    (_lit("p", False), _lit("r")),
    (_lit("p", False), _lit("r", False)),
    (_lit("s"), _lit("t")),
    (_lit("s", False), _lit("t")),
]

#: p で分岐。p=真 は残る節の充足にもう 1 つ決定が要る、p=偽 は unit propagation で矛盾
_TRUE_NEEDS_DECISION_FALSE_UNSAT = [
    (_lit("p"), _lit("q")),
    (_lit("p"), _lit("q", False)),
    (_lit("p", False), _lit("s"), _lit("t")),
    (_lit("p", False), _lit("s", False), _lit("t")),
]


def test_d5_left_unsat_right_budget_is_indeterminate_not_unsat(monkeypatch):
    """true 側 UNSAT + false 側が予算切れ → INDETERMINATE（UNSAT に化けない）。"""

    calls = _record_calls(monkeypatch)
    assert _sat(_TRUE_UNSAT_FALSE_NEEDS_DECISION, _meter(1)) is SatVerdict.INDETERMINATE
    # 両方の枝を見た（true 側は UNSAT だったので false 側を試した）
    assert {tuple(sorted(a.items())) for a, _b in calls[1:]} == {
        ((("p", "==", 1), True),),
        ((("p", "==", 1), False),),
    }
    # 無制限なら本当の答え（充足可能）
    assert _sat(_TRUE_UNSAT_FALSE_NEEDS_DECISION, _meter(None)) is SatVerdict.SAT


def test_d5_left_budget_does_not_try_the_right_branch(monkeypatch):
    """true 側が予算切れ → false 側（ここでは UNSAT）を試さず INDETERMINATE。"""

    calls = _record_calls(monkeypatch)
    assert _sat(_TRUE_NEEDS_DECISION_FALSE_UNSAT, _meter(1)) is SatVerdict.INDETERMINATE
    assert all(assignments.get(("p", "==", 1)) is not False for assignments, _budget in calls)
    assert _sat(_TRUE_NEEDS_DECISION_FALSE_UNSAT, _meter(None)) is SatVerdict.SAT


def test_d5_both_branches_over_budget_is_indeterminate(monkeypatch):
    """全体が充足不能でも、反駁に要る決定（3）より予算（2）が小さければ INDETERMINATE。"""

    clauses = [
        (_lit("a", sa), _lit("b", sb), _lit("c", sc))
        for sa in (True, False) for sb in (True, False) for sc in (True, False)
    ]
    for limit in (1, 2):
        assert _sat(clauses, _meter(limit)) is SatVerdict.INDETERMINATE
    assert _sat(clauses, _meter(3)) is SatVerdict.UNSAT
    assert _sat(clauses, _meter(None)) is SatVerdict.UNSAT


def test_d5_one_side_sat_wins_over_the_other_side_budget():
    """一方が SAT なら（他方の予算切れに関係なく）SAT。true 側 SAT は false 側を試さない。"""

    # p=真 で全節が充足（決定 1 つ）。false 側は予算が無くても関係ない
    true_sat = [(_lit("p"), _lit("q")), (_lit("p"), _lit("r"))]
    assert _sat(true_sat, _meter(1)) is SatVerdict.SAT
    # p=真 は矛盾、p=偽 で全節が充足（決定は p の 1 つだけ）
    false_sat = [(_lit("p"), _lit("q")), (_lit("p", False), _lit("r")), (_lit("p", False), _lit("r", False))]
    assert _sat(false_sat, _meter(1)) is SatVerdict.SAT


def test_d5_trivial_verdicts_need_no_decision():
    assert _sat([], _meter(1)) is SatVerdict.SAT
    assert _sat([(_lit("p"),), (_lit("p", False),)], _meter(1)) is SatVerdict.UNSAT
    budget = _meter(1)
    assert _sat([(_lit("p"),), (_lit("q"),)], budget) is SatVerdict.SAT
    assert budget.consumed == 0


def test_d5_the_budget_is_shared_by_every_branch():
    """1 回の問い合わせの決定は枝の合計で数える（枝ごとに戻さない）。"""

    clauses = [
        (_lit("a", sa), _lit("b", sb), _lit("c", sc))
        for sa in (True, False) for sb in (True, False) for sc in (True, False)
    ]
    budget = _meter(None)
    assert _sat(clauses, budget) is SatVerdict.UNSAT
    assert budget.consumed == 3


def test_d5_implication_under_budget_is_not_proven(scoped, dpll_only):
    """含意（文脈 ∧ ¬条件 の充足不能性）の途中で予算切れ → `None`（含意を主張しない）。"""

    context = _three_variable_contradiction()
    goal = Condition(_ATOMS["w"])
    with budget_policy_scope(BudgetPolicy(dpll_decisions=2)):
        assert ConditionSimplifier._formula_implies(context, goal) is None
        assert ConditionSimplifier._condition_is_implied(goal, context) is False
    with condition_cache_scope(), budget_policy_scope(BudgetPolicy(dpll_decisions=3)):
        assert ConditionSimplifier._formula_implies(context, goal) is True


def test_d5_contradiction_under_budget_is_not_proven(scoped, dpll_only):
    """矛盾判定の途中で予算切れ → `None` / 矛盾とは言わない（`not` で UNSAT に化けない）。"""

    conditions = _three_variable_contradiction()
    goal = Condition(_ATOMS["w"])
    with budget_policy_scope(BudgetPolicy(dpll_decisions=2)):
        assert ConditionSimplifier._clause_set_is_unsat(conditions) is None
        assert ConditionSimplifier._formula_is_unsat(conditions) is None
        assert ConditionSimplifier._condition_is_contradicted(goal, conditions) is False
    with condition_cache_scope(), budget_policy_scope(BudgetPolicy(dpll_decisions=3)):
        assert ConditionSimplifier._formula_is_unsat(conditions) is True
        assert ConditionSimplifier._condition_is_contradicted(goal, conditions) is True


# ---------------------------------------------------------------------------
# D6: 予算切れでは元の条件を残し、記録だけ残す
# ---------------------------------------------------------------------------


def test_d6_budget_keeps_the_original_conditions_and_records_the_event(scoped, dpll_only):
    """文脈（充足不能）の下での式の簡約: 予算が足りれば定数へ畳み、足りなければ元の式を残す。

    `is_contradiction` のような集合全体の判定は、文脈で書き換えた後の小さな問い（予算内で
    本当に証明できる）でも答えが出るので、予算の効き方を見るには caller 単位で比べる。
    """

    conditions = _three_variable_contradiction()
    expr = _ATOMS["w"]
    with condition_cache_scope(), budget_policy_scope(BudgetPolicy(dpll_decisions=3)):
        collapsed = ConditionSimplifier.reduce_expression_under_conditions(expr, conditions)
        assert ConditionSimplifier._condition_is_implied(Condition(expr), conditions) is True
    assert collapsed is not expr and collapsed.value == 1
    with budget_policy_scope(BudgetPolicy(dpll_decisions=2)):
        kept = ConditionSimplifier.reduce_expression_under_conditions(expr, conditions)
        assert ConditionSimplifier._condition_is_implied(Condition(expr), conditions) is False
    # 予算切れ: 簡約しない（同じ式 object をそのまま返す。近似しない）
    assert kept is expr

    snapshot = scoped.metrics.snapshot()
    events = snapshot["budget_events"]
    assert events and events[0] == {
        "budget_type": "dpll_decisions",
        "site": simplifier_cnf.DPLL_BUDGET_SITE,
        "limit": 2,
        "consumed": 2,
        "fallback_taken": "indeterminate",
    }
    assert snapshot["counters"]["budget.dpll_decisions.exceeded"] == snapshot["budget_events_total"]
    assert pairwise_debug_counters(snapshot)["simplify_budget_exceeded"] == snapshot["budget_events_total"]


def test_d6_a_budget_weakened_answer_is_not_remembered(scoped, dpll_only):
    """予算で打ち切った答え（`None`）は conjunction の表に覚えない（後の問いが履歴で変わらない）。"""

    conditions = _three_variable_contradiction()
    key = SolverQueryIdentity.from_conditions(conditions)
    with budget_policy_scope(BudgetPolicy(dpll_decisions=2)):
        assert ConditionSimplifier._formula_is_unsat(conditions) is None
    assert cache_lookup(ConditionSimplifier.CONJUNCTION_UNSAT_TABLE, key, limit=8192) == (False, None)
    # 予算が足りる問いの答えは従来どおり覚える
    assert ConditionSimplifier._formula_is_unsat(conditions) is True
    assert cache_lookup(ConditionSimplifier.CONJUNCTION_UNSAT_TABLE, key, limit=8192) == (True, True)


def test_d6_the_event_list_is_bounded_and_counts_the_rest(scoped):
    meter = FallbackBudgetMeter(ORACLE, 3)
    meter.consumed = 3
    for _ in range(MAX_BUDGET_EVENTS + 7):
        simplifier_cnf.note_budget_fallback(meter, site="test.site", fallback_taken="oracle_none", history_dependent=False)
    snapshot = scoped.metrics.snapshot()
    assert len(snapshot["budget_events"]) == MAX_BUDGET_EVENTS
    assert snapshot["budget_events_total"] == MAX_BUDGET_EVENTS + 7
    assert snapshot["budget_events_dropped"] == 7


def test_d6_no_event_block_without_a_fallback(scoped, dpll_only):
    conditions = _three_variable_contradiction()
    with budget_policy_scope(BudgetPolicy(dpll_decisions=64)):
        assert ConditionSimplifier._formula_is_unsat(conditions) is True
    snapshot = scoped.metrics.snapshot()
    assert "budget_events" not in snapshot
    assert "simplify_budget_exceeded" not in pairwise_debug_counters(snapshot)


def test_d6_budget_events_reach_the_result_json(scoped):
    from scripts.function_tracer_pcode.checker import output_preparation
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult

    meter = FallbackBudgetMeter(ORACLE, 5)
    meter.consumed = 5
    simplifier_cnf.note_budget_fallback(
        meter, site="smt_oracle.conjunction_is_unsat", fallback_taken="oracle_none", history_dependent=False
    )
    result = EquivalenceResult(
        is_equivalent=None, function1_name="l", function2_name="r",
        binary1_name="L", binary2_name="R", solver_results=None,
    )
    prepared = SimpleNamespace(plan=SimpleNamespace(to_diagnostic=lambda: {}))
    output_preparation._attach_budget_diagnostics(result, prepared, BudgetPolicy(oracle_queries=5))
    payload = result.to_dict()
    block = payload["diagnostics"]["condition_simplify"]
    assert block["budget_events"] == [{
        "budget_type": "oracle_queries", "site": "smt_oracle.conjunction_is_unsat",
        "limit": 5, "consumed": 5, "fallback_taken": "oracle_none",
    }]
    assert payload["pairwise_debug_stats"]["simplify_budget_exceeded"] == 1
    assert payload["diagnostics"]["expression_budget"]["policy"]["oracle_queries"] == 5


# ---------------------------------------------------------------------------
# D7: oracle の query 予算
# ---------------------------------------------------------------------------


class _FakeZ3:
    sat = object()
    unsat = object()

    def __init__(self):
        self.checks = 0

    def Context(self):
        return object()

    def Solver(self, ctx=None):
        fake = self

        class _Solver:
            def set(self, *_args):
                return None

            def add(self, *_args):
                return None

            def check(self):
                fake.checks += 1
                return fake.unsat

            def reason_unknown(self):
                return ""

        return _Solver()

    def parse_smt2_string(self, _script, ctx=None):
        return []


@pytest.fixture
def fake_z3(monkeypatch):
    fake = _FakeZ3()
    monkeypatch.setattr(ConditionSMTOracle, "_z3", fake)
    monkeypatch.setattr(ConditionSMTOracle, "_available", True)
    monkeypatch.setattr(ConditionSMTOracle, "_availability_checked", True)
    return fake


def _slt(index, value):
    return Condition(Expression.binary_op("INT_SLESS", _param(f"param_{index}", index), Expression.constant(value, size=4)))


def test_d7_after_the_budget_no_solver_is_called_and_the_answer_is_none(scoped, fake_z3, monkeypatch):
    built = []
    original_build = ConditionSMTOracle._build_script.__func__
    monkeypatch.setattr(
        ConditionSMTOracle, "_build_script",
        classmethod(lambda cls, conds, **kw: built.append(len(conds)) or original_build(cls, conds, **kw)),
    )
    solvers = []
    original_solver = smt_oracle.isolated_solver
    monkeypatch.setattr(smt_oracle, "isolated_solver", lambda *a, **k: solvers.append(1) or original_solver(*a, **k))

    with budget_policy_scope(BudgetPolicy(oracle_queries=2)):
        assert ConditionSMTOracle.conjunction_is_unsat([_slt(0, 1)]) is True
        assert ConditionSMTOracle.conjunction_is_unsat([_slt(1, 2)]) is True
        assert fake_z3.checks == 2 and len(solvers) == 2 and len(built) == 2
        # 3 つ目の新しい query: solver を呼ばない・script も組まない・`None`
        assert ConditionSMTOracle.conjunction_is_unsat([_slt(2, 3)]) is None
        assert fake_z3.checks == 2 and len(solvers) == 2 and len(built) == 2
        assert pair_fallback_meter(ORACLE).consumed == 2
    events = scoped.metrics.snapshot()["budget_events"]
    assert events == [{
        "budget_type": "oracle_queries", "site": ConditionSMTOracle.QUERY_BUDGET_SITE,
        "limit": 2, "consumed": 2, "fallback_taken": "oracle_none",
    }]
    # 予算切れの `None` は覚えない（次の pair では solver に聞く）
    key = SolverQueryIdentity.from_conditions([_slt(2, 3)])
    assert cache_lookup(ConditionSMTOracle.VERDICT_TABLE, key, limit=4096) == (False, None)


def test_d7_the_issue_point_itself_refuses_when_the_budget_ran_out_meanwhile(scoped, fake_z3, monkeypatch):
    """尽きたかの確認（script を組む前）の後に別の問い合わせが最後の 1 つを使った場合も、発行の
    直前の `take()` が断り、solver を呼ばない（消費は発行の地点でだけ数える）。"""

    class _RanOutMeanwhile(FallbackBudgetMeter):
        @property
        def exhausted(self):
            return False

        def take(self, amount=1):
            return False

    meter = _RanOutMeanwhile(ORACLE, 1)
    monkeypatch.setattr(smt_oracle, "pair_fallback_meter", lambda kind: meter)
    assert ConditionSMTOracle.conjunction_is_unsat([_slt(0, 1)]) is None
    assert fake_z3.checks == 0
    assert scoped.metrics.snapshot()["budget_events_total"] == 1


def test_d7_a_cache_hit_does_not_use_the_budget(scoped, fake_z3):
    with budget_policy_scope(BudgetPolicy(oracle_queries=1)):
        assert ConditionSMTOracle.conjunction_is_unsat([_slt(0, 1)]) is True
        for _ in range(5):
            # 覚えた答えは予算が尽きた後も返る（solver は呼ばない・予算も使わない）
            assert ConditionSMTOracle.conjunction_is_unsat([_slt(0, 1)]) is True
        assert fake_z3.checks == 1
        assert pair_fallback_meter(ORACLE).consumed == 1
    assert "budget_events" not in scoped.metrics.snapshot()


def test_d7_the_budget_does_not_carry_over_to_the_next_pair(fake_z3):
    for _pair in range(3):
        with condition_cache_scope(), condition_metrics_scope(), budget_policy_scope(BudgetPolicy(oracle_queries=1)):
            assert pair_fallback_meter(ORACLE).consumed == 0
            assert ConditionSMTOracle.conjunction_is_unsat([_slt(0, 1)]) is True
            assert ConditionSMTOracle.conjunction_is_unsat([_slt(1, 2)]) is None
    assert fake_z3.checks == 3


def test_d7_a_nested_pair_scope_has_its_own_budget(fake_z3):
    with condition_cache_scope(), condition_metrics_scope(), budget_policy_scope(BudgetPolicy(oracle_queries=1)):
        assert ConditionSMTOracle.conjunction_is_unsat([_slt(0, 1)]) is True
        with budget_policy_scope(BudgetPolicy(oracle_queries=1)):
            assert ConditionSMTOracle.conjunction_is_unsat([_slt(1, 2)]) is True
        # 外側へ戻ると外側の消費（尽きている）
        assert ConditionSMTOracle.conjunction_is_unsat([_slt(2, 3)]) is None


def test_d7_answers_after_the_oracle_budget_are_remembered(scoped, fake_z3, monkeypatch):
    """oracle の予算は pair の中で尽きたままなので、尽きた後に DPLL が作った答えは覚えてよい
    （作り直しても同じ）。覚えないと尽きた後の pair の残りで cache が効かなくなる。"""

    monkeypatch.setattr(
        ConditionSimplifier, "_should_use_solver_reasoning", classmethod(lambda cls, conds: True)
    )
    conditions = [_slt(0, 1), _slt(1, 2)]
    key = SolverQueryIdentity.from_conditions(conditions)
    with budget_policy_scope(BudgetPolicy(oracle_queries=1)):
        assert ConditionSMTOracle.conjunction_is_unsat([_slt(5, 6)]) is True  # 予算を使い切る
        assert ConditionSimplifier._formula_is_unsat(conditions) is False  # DPLL の答え
        assert fake_z3.checks == 1
        assert cache_lookup(ConditionSimplifier.CONJUNCTION_UNSAT_TABLE, key, limit=8192) == (True, False)
    assert scoped.metrics.snapshot()["counters"].get("simplifier.guard_tainted_not_stored", 0) == 0


# ---------------------------------------------------------------------------
# budget OFF（無制限）: 制限だけが無効で、三値の構造は残る
# ---------------------------------------------------------------------------


def test_budget_off_is_unlimited_but_still_three_valued(scoped, fake_z3, dpll_only):
    with budget_policy_scope(BudgetPolicy(dpll_decisions=None, oracle_queries=None)):
        assert ConditionSimplifier._clause_set_is_unsat(_three_variable_contradiction()) is True
        for index in range(20):
            assert ConditionSMTOracle.conjunction_is_unsat([_slt(index, index + 1)]) is True
        assert pair_fallback_meter(ORACLE).consumed == 20
    assert fake_z3.checks == 20
    assert "budget_events" not in scoped.metrics.snapshot()
    # 無制限でも答えは三値（`as_unsat_answer` を通る）
    assert _sat([(_lit("p"),)], _meter(None)) is SatVerdict.SAT


def test_outside_a_pair_scope_nothing_is_limited_or_kept(fake_z3):
    assert pair_fallback_meter(ORACLE).limit is None
    for index in range(3):
        assert ConditionSMTOracle.conjunction_is_unsat([_slt(index, index + 1)]) is True
    assert pair_fallback_meter(ORACLE).consumed == 0


def test_fallback_budgets_are_not_limitations():
    """fallback の予算は `enforce_budget`（限界の入口）へ渡せない（型で分けてある）。"""

    with pytest.raises(ValueError):
        enforce_budget(DPLL, 10, site="x", target_key=None)
    assert {kind.value for kind in FallbackBudgetKind}.isdisjoint({kind.value for kind in BudgetKind})
    with pytest.raises(ValueError):
        BudgetPolicy(dpll_decisions=0)
    with pytest.raises(ValueError):
        BudgetPolicy(oracle_queries=-1)


def test_meter_take_allows_exactly_limit_units():
    meter = _meter(2)
    assert [meter.take() for _ in range(4)] == [True, True, False, False]
    assert meter.consumed == 2 and meter.exhausted
    unlimited = _meter(None)
    assert all(unlimited.take() for _ in range(1000)) and not unlimited.exhausted


# ---------------------------------------------------------------------------
# M-1: 予算の値は config と BudgetPolicy だけ
# ---------------------------------------------------------------------------


def test_the_default_values_come_from_config_and_can_be_turned_off():
    from scripts.function_tracer_pcode.config.settings import (
        EXPRESSION_BUDGET_DEFAULTS,
        expression_budget_policy,
    )

    table = {name: (env, default) for name, env, default in EXPRESSION_BUDGET_DEFAULTS}
    # 既定では有効（有限）。無制限は `off` を明示したときだけ
    assert type(table["dpll_decisions"][1]) is int and type(table["oracle_queries"][1]) is int
    policy = expression_budget_policy({})
    assert policy.dpll_decisions == table["dpll_decisions"][1]
    assert policy.oracle_queries == table["oracle_queries"][1]
    off = expression_budget_policy({
        table["dpll_decisions"][0]: "off", table["oracle_queries"][0]: "unlimited",
    })
    assert off.dpll_decisions is None and off.oracle_queries is None
    tuned = expression_budget_policy({table["dpll_decisions"][0]: "7", table["oracle_queries"][0]: "9"})
    assert (tuned.dpll_decisions, tuned.oracle_queries) == (7, 9)


def test_no_module_reads_the_fallback_budget_fields_directly():
    """深い module は fallback の予算の policy field（`dpll_decisions` / `oracle_queries`）を
    属性として直接参照しない（上限は `BudgetPolicy.limit(kind)` と `FallbackBudgetMeter` 経由だけ）。

    保証するのはこの field の参照が 0 であることで、数値 literal 一般の禁止ではない（既定値は
    `config/settings.py` の表が field 名の文字列で持つ）。
    """

    readers = []
    for path, tree in _package_sources():
        relative = str(path.relative_to(PACKAGE_ROOT))
        for node in ast.walk(tree):
            if isinstance(node, ast.Attribute) and node.attr in {"dpll_decisions", "oracle_queries"}:
                readers.append(relative)
    assert sorted(set(readers)) == []


# ---------------------------------------------------------------------------
# D14: decision gate の記録様式（budget hit と遷移の表）
# ---------------------------------------------------------------------------


def _write_result_pair(tree, sample, function, left, right, outcome, *, reasons=(), budget_hits=None, payload=True):
    import json

    directory = tree / sample / function
    directory.mkdir(parents=True, exist_ok=True)
    name = f"{function}_{left}_{right}"
    (directory / f"{name}.pair-status.json").write_text(json.dumps({
        "canonical_outcome": outcome,
        "supervisor_status": "RESOLVED",
        "pair_execution_target": {
            "sample_identity": sample, "function_name": function,
            "left_binary_id": left, "right_binary_id": right,
        },
    }), encoding="utf-8")
    counters = {"oracle.queries": 12}
    for budget, count in (budget_hits or {}).items():
        counters[f"budget.{budget}.exceeded"] = count
    body = json.dumps({
        "unknown_reasons": [{"reason_id": value} for value in reasons],
        "diagnostics": {"condition_simplify": {"schema": "condition-simplify-metrics-v1", "counters": counters}},
    })
    (directory / f"{name}.log").write_text(
        (f"=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n{body}\n=== EQUIVALENCE_RESULT_JSON_END ===\n")
        if payload else "killed\n",
        encoding="utf-8",
    )


def test_d14_the_decision_gate_table_lists_budget_hits_next_to_the_transition(tmp_path):
    from scripts.function_tracer_pcode.reporting import outcome_transition as ot

    before, after = tmp_path / "before", tmp_path / "after"
    sample = "optimization/wood/Neq/newV-oldV"
    # 予算で答えなくなって UNKNOWN の reason が変わった pair
    _write_result_pair(before, sample, "wood", "N_B2", "O_B4", "UNKNOWN", reasons=("r_a",))
    _write_result_pair(after, sample, "wood", "N_B2", "O_B4", "UNKNOWN", reasons=("r_b",),
                       budget_hits={"oracle_queries": 40, "dpll_decisions": 1})
    # TIMEOUT（payload 無し）→ 予算で打ち切って理由付き UNKNOWN
    _write_result_pair(before, sample, "wood", "N_B3", "O_B7", "TIMEOUT", payload=False)
    _write_result_pair(after, sample, "wood", "N_B3", "O_B7", "UNKNOWN", reasons=("r_a",),
                       budget_hits={"oracle_queries": 3})
    # 予算に当たらなかった pair は表に出ない
    _write_result_pair(before, sample, "wood", "N_B5", "O_B7", "NOT_EQ")
    _write_result_pair(after, sample, "wood", "N_B5", "O_B7", "NOT_EQ")

    _report, sections = ot.build_report_sections(before, after, budget_events=True)
    table = sections["budget_events"]
    assert ot.format_budget_events(table) == [
        "",
        "Condition-simplification budget fallbacks (informational only -- a fallback is never an UNKNOWN reason):",
        "  pairs: 3; unreadable payloads: before 1, after 0 (not counted as zero fallbacks)",
        "  pairs with a fallback: before 0, after 2",
        "  fallbacks by budget: before {}, after {'dpll_decisions': 1, 'oracle_queries': 43}",
        f"  {sample} wood N_B2_O_B4: UNKNOWN -> UNKNOWN | fallbacks - -> dpll_decisions=1,oracle_queries=40 | reasons changed",
        f"  {sample} wood N_B3_O_B7: TIMEOUT -> UNKNOWN | fallbacks unreadable -> oracle_queries=3",
    ]
    serialized = ot.sections_as_dict(sections)["budget_events"]
    assert {key: serialized[key] for key in serialized if key != "rows"} == {
        "pairs": 3,
        "before_unreadable_payloads": 1,
        "after_unreadable_payloads": 0,
        "before_pairs_with_fallback": 0,
        "after_pairs_with_fallback": 2,
        "before_fallbacks_by_budget": {},
        "after_fallbacks_by_budget": {"dpll_decisions": 1, "oracle_queries": 43},
        "rows_with_outcome_change": 1,
        "informational_only": True,
    }
    assert [row["pair_id"] for row in serialized["rows"]] == ["N_B2_O_B4", "N_B3_O_B7"]
    assert serialized["rows"][1]["before_budget_fallbacks"] is None  # 読めない ≠ 0 件


def test_d14_the_section_is_opt_in_and_never_moves_the_exit_code(tmp_path):
    from scripts.function_tracer_pcode.reporting import outcome_transition as ot

    before, after = tmp_path / "before", tmp_path / "after"
    _write_result_pair(before, "s/Eq/x", "f", "B1", "B2", "EQUIVALENT")
    _write_result_pair(after, "s/Eq/x", "f", "B1", "B2", "EQUIVALENT", budget_hits={"oracle_queries": 1})
    _report, sections = ot.build_report_sections(before, after)
    assert "budget_events" not in sections
    assert ot.main(["--before", str(before), "--after", str(after), "--budget-events", "--fail-on-change"]) == 0


# ---------------------------------------------------------------------------
# decision gate の設計変更: basis の重複計算を除く（順序を含む identity、位置だけを覚える）
# ---------------------------------------------------------------------------


def _x():
    return _param("param_x", 7)


def _x_lt(value):
    return Condition(Expression.binary_op("INT_SLESS", _x(), Expression.constant(value, size=4)))


def _x_le(value):
    return Condition(Expression.binary_op("INT_SLESSEQUAL", _x(), Expression.constant(value, size=4)))


def _fresh_basis(conditions):
    """cache の scope の外（何も覚えない）で求めた basis。"""

    return ConditionSimplifier.build_object_centric_condition_basis(conditions)


def _shape(conditions):
    return [(c.expression.operator, c.negated) for c in conditions]


def test_basis_memo_matches_a_fresh_computation_for_each_order():
    """同じ多重集合でも順序が違えば別の key（同じ複雑さの同値な条件は先に来た方を残す）。"""

    orders = [[_x_lt(5), _x_le(4)], [_x_le(4), _x_lt(5)]]
    expected = [_shape(_fresh_basis(order)) for order in orders]
    assert expected[0] != expected[1]  # 入力順で答えが変わる計算であること
    with condition_cache_scope(), condition_metrics_scope():
        for _repeat in range(2):
            for order, shape in zip(orders, expected):
                assert _shape(ConditionSimplifier.build_object_centric_condition_basis(order)) == shape


def test_basis_memo_does_not_transfer_positions_across_orders():
    """位置だけを覚えるので、順序に依らない key だと逆順の入力で別の条件を返してしまう。

    `x < 5`（単純）は `x + 1 < 11`（複雑）を含意する。basis は単純な方から見るので、どちらの
    順でも残るのは `x < 5` だが、その位置は順で違う（0 と 1）。
    """

    simple = _x_lt(5)
    complex_ = Condition(Expression.binary_op(
        "INT_SLESS",
        Expression.binary_op("INT_ADD", _x(), Expression.constant(1, size=4)),
        Expression.constant(11, size=4),
    ))
    orders = [[simple, complex_], [complex_, simple]]
    expected = [_shape(_fresh_basis(order)) for order in orders]
    assert expected == [[("INT_SLESS", False)], [("INT_SLESS", False)]]
    with condition_cache_scope(), condition_metrics_scope():
        for order in orders:
            basis = ConditionSimplifier.build_object_centric_condition_basis(order)
            assert len(basis) == 1
            assert basis[0].expression.operands[0].expr_type == _x().expr_type  # `x < 5` の方


def test_basis_memo_returns_this_calls_own_objects(monkeypatch):
    """覚えるのは残す位置だけ。2 回目の呼び出しの答えは、その呼び出しの入力の object。"""

    implied_calls = []
    original = ConditionSimplifier._condition_is_implied.__func__

    def _counting(cls, *args, **kwargs):
        implied_calls.append(1)
        return original(cls, *args, **kwargs)

    monkeypatch.setattr(ConditionSimplifier, "_condition_is_implied", classmethod(_counting))
    with condition_cache_scope(), condition_metrics_scope() as metrics:
        first_input = [_x_lt(5), _x_le(4), _slt(3, 9)]
        first = ConditionSimplifier.build_object_centric_condition_basis(first_input)
        calls_after_first = len(implied_calls)
        second_input = [_x_lt(5), _x_le(4), _slt(3, 9)]  # 構造は同じ、object は別
        second = ConditionSimplifier.build_object_centric_condition_basis(second_input)
        assert len(implied_calls) == calls_after_first  # 含意を聞き直さない
        assert _shape(first) == _shape(second)
        assert all(a is not b for a, b in zip(first, second))
        # 答えの object は、この呼び出しの入力を平坦化した object（別の入力の object ではない）
        own = {
            id(flat)
            for condition in second_input
            for flat in simplifier_cnf.root_memo(
                ConditionSimplifier.FLATTEN_MEMO, condition, ConditionSimplifier._flattened_nontrivial
            )
        }
        assert all(id(c) in own for c in second)
        counters = metrics.snapshot()["counters"]
        assert counters["cache.simplifier.basis.hit"] == 1
        assert counters["cache.simplifier.basis.miss"] == 1


def test_basis_memo_does_not_remember_a_truncated_selection(monkeypatch):
    """打ち切り（再入 guard・予算）を材料にした選び方は覚えない。"""

    from scripts.function_tracer_pcode.analysis.condition import simplifier as simplifier_module

    original = ConditionSimplifier._condition_is_implied.__func__

    def _truncating(cls, *args, **kwargs):
        simplifier_module.note_reentry_guard_hit()
        return original(cls, *args, **kwargs)

    conditions = [_x_lt(5), _x_le(4)]
    with condition_cache_scope(), condition_metrics_scope() as metrics:
        monkeypatch.setattr(ConditionSimplifier, "_condition_is_implied", classmethod(_truncating))
        ConditionSimplifier.build_object_centric_condition_basis(conditions)
        monkeypatch.setattr(ConditionSimplifier, "_condition_is_implied", classmethod(original))
        ConditionSimplifier.build_object_centric_condition_basis(conditions)
        counters = metrics.snapshot()["counters"]
    assert counters.get("cache.simplifier.basis.hit", 0) == 0
    assert counters["cache.simplifier.basis.miss"] == 2


def test_flatten_memo_gives_the_same_objects_for_the_same_condition():
    conjunction = Condition(Expression.binary_op("BOOL_AND", _x_lt(5).expression, _slt(3, 9).expression))
    with condition_cache_scope():
        first = ConditionSimplifier._flattened_nontrivial(conjunction)
        memo_first = simplifier_cnf.root_memo(ConditionSimplifier.FLATTEN_MEMO, conjunction, ConditionSimplifier._flattened_nontrivial)
        memo_again = simplifier_cnf.root_memo(ConditionSimplifier.FLATTEN_MEMO, conjunction, ConditionSimplifier._flattened_nontrivial)
    assert len(first) == 2 and memo_first is memo_again
    assert _shape(memo_first) == _shape(first)


def test_the_basis_key_is_order_sensitive_and_rejects_uncomparable_graphs():
    from scripts.function_tracer_pcode.analysis.condition.query_identity import OrderedConditionsIdentity

    a, b = _x_lt(5), _slt(3, 9)
    assert OrderedConditionsIdentity.of([a, b]) == OrderedConditionsIdentity.of([_x_lt(5), _slt(3, 9)])
    assert OrderedConditionsIdentity.of([a, b]) != OrderedConditionsIdentity.of([b, a])
    # 順序に依らない conjunction の identity では同じ（別の型: 相互に代用しない）
    assert SolverQueryIdentity.from_conditions([a, b]) == SolverQueryIdentity.from_conditions([b, a])
    assert OrderedConditionsIdentity.of([a, b]) != SolverQueryIdentity.from_conditions([a, b])


# ---------------------------------------------------------------------------
# 並び単位の memo（同じ条件 object を同じ順で持つ並びだけに使い回す）
# ---------------------------------------------------------------------------


def test_sequence_memo_hits_only_the_same_objects_in_the_same_order():
    from scripts.function_tracer_pcode.analysis.condition.condition_cache import (
        sequence_lookup,
        sequence_store,
    )

    a, b = _x_lt(5), _slt(3, 9)
    with condition_cache_scope(), condition_metrics_scope():
        sequence_store("test.kind", (a, b), "answer")
        assert sequence_lookup("test.kind", (a, b)) == (True, "answer")
        assert sequence_lookup("test.kind", (b, a)) == (False, None)
        # 構造が同じ別の object の並びには使い回さない
        assert sequence_lookup("test.kind", (_x_lt(5), _slt(3, 9))) == (False, None)
        assert sequence_lookup("test.kind", (a,)) == (False, None)
    # scope の外では何も覚えない
    sequence_store("test.kind", (a, b), "answer")
    assert sequence_lookup("test.kind", (a, b)) == (False, None)


def test_sequence_memo_forgets_an_entry_whose_element_was_collected():
    import gc

    from scripts.function_tracer_pcode.analysis.condition.condition_cache import (
        active_condition_cache,
        sequence_lookup,
        sequence_store,
    )

    keep = _x_lt(5)
    with condition_cache_scope(), condition_metrics_scope():
        store = active_condition_cache()
        transient = _slt(3, 9)
        sequence_store("test.kind", (keep, transient), "answer")
        assert len(store._sequences["test.kind"]) == 1
        del transient
        gc.collect()
        assert len(store._sequences["test.kind"]) == 0
        assert sequence_lookup("test.kind", (keep,)) == (False, None)


def test_public_entries_reuse_answers_for_the_same_objects(monkeypatch):
    conditions = [_x_lt(5), _x_le(4), _slt(3, 9)]
    calls = []
    original = ConditionSimplifier._compute_condition_basis.__func__
    monkeypatch.setattr(
        ConditionSimplifier, "_compute_condition_basis",
        classmethod(lambda cls, items: calls.append(len(items)) or original(cls, items)),
    )
    with condition_cache_scope(), condition_metrics_scope() as metrics:
        first = ConditionSimplifier.build_object_centric_condition_basis(conditions)
        again = ConditionSimplifier.build_object_centric_condition_basis(list(conditions))
        assert calls == [3]  # 同じ object の並び: 作り直さない
        assert [c is d for c, d in zip(first, again)] == [True] * len(first)
        contradiction = ConditionSimplifier.object_centric_is_contradiction(conditions)
        assert ConditionSimplifier.object_centric_is_contradiction(conditions) is contradiction
        assert ConditionSimplifier.is_contradiction(conditions) is ConditionSimplifier.is_contradiction(conditions)
        counters = metrics.snapshot()["counters"]
    assert counters["memo.simplifier.basis_by_objects.hit"] >= 1
    assert counters["memo.simplifier.object_centric_contradiction_by_objects.hit"] == 1
    assert counters["memo.simplifier.contradiction_by_objects.hit"] == 1
    # scope の外（何も覚えない）と同じ答え
    assert _shape(first) == _shape(_fresh_basis(conditions))
    assert contradiction is ConditionSimplifier.object_centric_is_contradiction(conditions)


def test_public_entries_do_not_remember_a_truncated_answer(monkeypatch):
    from scripts.function_tracer_pcode.analysis.condition import simplifier as simplifier_module

    conditions = [_x_lt(5), _slt(3, 9)]
    original = ConditionSimplifier._compute_object_centric_is_contradiction.__func__

    def _truncating(cls, items):
        simplifier_module.note_reentry_guard_hit()
        return original(cls, items)

    with condition_cache_scope(), condition_metrics_scope() as metrics:
        monkeypatch.setattr(ConditionSimplifier, "_compute_object_centric_is_contradiction", classmethod(_truncating))
        ConditionSimplifier.object_centric_is_contradiction(conditions)
        ConditionSimplifier.object_centric_is_contradiction(conditions)
        counters = metrics.snapshot()["counters"]
    assert counters.get("memo.simplifier.object_centric_contradiction_by_objects.hit", 0) == 0


def test_the_fallback_key_of_a_large_expression_is_built_once_per_object(monkeypatch):
    """小さい予算で比べられない式の key（`expression_key_or_identity`）は式 object ごとに 1 回。"""

    from scripts.function_tracer_pcode.analysis.condition import normalizer as normalizer_module
    from scripts.function_tracer_pcode.analysis.condition.normalizer import ConditionNormalizer

    large = _x()
    for step in range(60):
        large = Expression.binary_op("INT_ADD", large, _param(f"param_s{step}", 20 + step))
    built = []
    original = normalizer_module.expression_key_or_identity
    monkeypatch.setattr(normalizer_module, "expression_key_or_identity", lambda e: built.append(1) or original(e))
    with condition_cache_scope():
        first = ConditionNormalizer.expression_signature(large)
        again = ConditionNormalizer.expression_signature(large)
    assert first == again and len(built) == 1
    # scope の外では従来どおり毎回作る（値は同じ）
    assert ConditionNormalizer.expression_signature(large) == first and len(built) == 2
