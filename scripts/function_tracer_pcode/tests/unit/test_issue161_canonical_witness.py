# -*- coding: utf-8 -*-
"""Issue #161: SAT の witness は script の意味だけで決まる（solver の履歴に依らない）。

固定する契約:

* `canonical_witness` の結果は、元の論理式の model のうち（満たせる preference を満たし）
  宣言順の値の列が辞書式最小のもの（bit-vector は unsigned、Bool は false < true、
  Int は (絶対値, 負か)）。**最初に渡された model にも solver の答えの順にも依らない**
* 値は宣言の sort の Python 型（Bool は bool）で、宣言した scalar 入力（bit-vector /
  Bool / Int）をすべて束縛する。quoted symbol も solver の中の同じ定数を指す。
  authority の witness replay（`RelationalWitnessReplayReceipt`）がそのまま受け入れる
* z3 backend が返す SAT の model は、同じ process で先に何を解いたか・z3 の random
  seed・assertion の並べ方・同じ意味の別の書き方に依らない
* 浮動小数点の引数が NaN でない witness が存在すれば、NaN の witness は返らない
  （NaN の規則の定義は `proof.formula.witness_domain` の 1 箇所）
* canonical witness を作れる backend は witness の無い SAT を返さない。決められない
  ときは予算切れが TIMEOUT、判定不能・中止が UNKNOWN（`smt.interface`）
* 時間予算は 1 回の実行に 1 つ: 初回の check と witness の探索が同じ期限を共有する
  （`Z3Solver` と monolithic の共有 session の両方）
* production の z3 利用は process 共有の main context を使わない

race / 結果の集約は `test_issue161_backend_aggregation.py`。
"""

from __future__ import annotations

import ast
import itertools
import pathlib
import random

import pytest
import z3

from scripts.function_tracer_pcode.proof.formula.witness_domain import (
    NON_NAN_FP_PREFERENCE,
    is_nan_bit_pattern,
    witness_preference_lines,
)
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.smt.interface import SolverStatus
from scripts.function_tracer_pcode.smt.solvers import z3 as z3_backend
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
from scripts.function_tracer_pcode.smt.witness import (
    BOOL,
    BUDGET_EXHAUSTED,
    CANCELLED,
    INCONCLUSIVE,
    INT,
    WitnessTarget,
    WitnessUnavailable,
    canonical_witness,
)


PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]


# ---------------------------------------------------------------------------
# 探索の規則（backend に依らない）
# ---------------------------------------------------------------------------


class _EnumeratedSession:
    """小さな論理式を全列挙で解く session（brute force の基準）。"""

    def __init__(self, models, start, preferences=None):
        self._models = list(models)
        self._fixed = []
        self._preferences = dict(preferences or {})
        self._current = start
        self.checks = 0
        self.sat_answers = 0

    def _holds(self, constraint, model):
        if constraint.kind == "preference":
            return self._preferences[constraint.preference](model)
        value = model[constraint.target.name]
        if constraint.kind == "bit":
            return ((value >> constraint.bit) & 1) == constraint.value
        if constraint.kind == "abs_le":
            return abs(value) <= constraint.value
        if constraint.kind == "eq":
            return value == constraint.value
        assert constraint.kind == "low_zero", constraint
        return value & ((1 << (constraint.bit + 1)) - 1) == 0

    def values(self):
        return dict(self._current)

    def holds(self, constraint):
        return self._holds(constraint, self._current)

    def check_with(self, constraint):
        self.checks += 1
        for model in self._models:
            if all(self._holds(c, model) for c in self._fixed) and self._holds(constraint, model):
                self.sat_answers += 1
                self._current = dict(model)
                return dict(model)
        return None

    def fix(self, constraint):
        assert self._holds(constraint, self._current), "fix() must keep the current model valid"
        self._fixed.append(constraint)


TARGETS = (WitnessTarget("a", 4), WitnessTarget("b", 4))


def _models(predicate):
    return [
        {"a": a, "b": b}
        for a, b in itertools.product(range(16), repeat=2)
        if predicate(a, b)
    ]


@pytest.mark.parametrize(
    "predicate",
    [
        lambda a, b: a + b == 17,
        lambda a, b: (a ^ b) == 9 and a > 3,
        lambda a, b: a * b % 16 == 6,
        lambda a, b: b == 5,
    ],
)
def test_the_witness_is_the_least_model_whatever_model_the_solver_found_first(predicate):
    models = _models(predicate)
    expected = min(models, key=lambda m: (m["a"], m["b"]))
    for start in models:
        # 探索の中の問い合わせが返す model も毎回ばらばらにする（solver の任意性）
        shuffled = list(models)
        random.Random(start["a"] * 16 + start["b"]).shuffle(shuffled)
        session = _EnumeratedSession(shuffled, start)
        assert canonical_witness(session, TARGETS) == expected


def test_the_witness_is_the_least_model_for_random_solution_sets():
    rng = random.Random(161)
    universe = [{"a": a, "b": b} for a, b in itertools.product(range(16), repeat=2)]
    for _ in range(300):
        models = rng.sample(universe, rng.randint(1, 12))
        expected = min(models, key=lambda m: (m["a"], m["b"]))
        start = rng.choice(models)
        shuffled = list(models)
        rng.shuffle(shuffled)
        assert canonical_witness(_EnumeratedSession(shuffled, start), TARGETS) == expected


def _int_order(value):
    return (abs(value), value < 0)


def test_an_int_component_is_the_least_by_magnitude_then_sign():
    rng = random.Random(1610)
    targets = (WitnessTarget("i", 0, INT), WitnessTarget("j", 0, INT))
    universe = [{"i": i, "j": j} for i, j in itertools.product(range(-9, 10), repeat=2)]
    for _ in range(300):
        models = rng.sample(universe, rng.randint(1, 10))
        expected = min(models, key=lambda m: (_int_order(m["i"]), _int_order(m["j"])))
        shuffled = list(models)
        rng.shuffle(shuffled)
        session = _EnumeratedSession(shuffled, rng.choice(models))
        assert canonical_witness(session, targets) == expected


def test_mixed_sorts_follow_declaration_order_and_come_back_as_their_python_types():
    rng = random.Random(16100)
    targets = (WitnessTarget("f", 1, BOOL), WitnessTarget("n", 0, INT), WitnessTarget("v", 3))
    universe = [
        {"f": f, "n": n, "v": v}
        for f, n, v in itertools.product((0, 1), range(-4, 5), range(8))
    ]
    for _ in range(300):
        models = rng.sample(universe, rng.randint(1, 10))
        expected = min(models, key=lambda m: (m["f"], _int_order(m["n"]), m["v"]))
        shuffled = list(models)
        rng.shuffle(shuffled)
        witness = canonical_witness(_EnumeratedSession(shuffled, rng.choice(models)), targets)
        assert witness == {"f": bool(expected["f"]), "n": expected["n"], "v": expected["v"]}
        assert type(witness["f"]) is bool and type(witness["n"]) is int


def test_a_satisfiable_preference_is_always_satisfied_by_the_witness():
    models = _models(lambda a, b: a + b == 17)
    preferred = {"|p:0|": lambda m: m["a"] >= 8}
    expected = min((m for m in models if m["a"] >= 8), key=lambda m: (m["a"], m["b"]))
    for start in models:
        session = _EnumeratedSession(models, start, preferred)
        assert canonical_witness(session, TARGETS, ["|p:0|"]) == expected


def test_an_unsatisfiable_preference_is_skipped_not_forced():
    models = _models(lambda a, b: b == 5)
    impossible = {"|p:0|": lambda m: m["b"] == 6}
    session = _EnumeratedSession(models, models[-1], impossible)
    assert canonical_witness(session, TARGETS, ["|p:0|"]) == {"a": 0, "b": 5}


# 費用の契約: 浮動小数点の式では SAT の答えが高く UNSAT の答えが安いので、探索は SAT に
# なる問いを減らす（値は問いの立て方に依らない。上の brute force が固定する）。


def test_a_value_fixed_by_the_formula_is_found_without_a_sat_answer():
    models = _models(lambda a, b: a == 15 and b == 15)
    session = _EnumeratedSession(models, models[0])
    assert canonical_witness(session, TARGETS) == {"a": 15, "b": 15}
    assert session.sat_answers == 0


def test_a_component_that_can_be_zero_costs_one_sat_answer():
    models = _models(lambda a, b: b == 5)
    session = _EnumeratedSession(models, {"a": 15, "b": 5})
    assert canonical_witness(session, TARGETS) == {"a": 0, "b": 5}
    assert session.sat_answers == 1


def test_a_preference_the_current_model_satisfies_is_not_asked():
    models = _models(lambda a, b: a + b == 17)
    preferred = {"|p:0|": lambda m: m["a"] >= 8}
    asked = []
    session = _EnumeratedSession(models, {"a": 9, "b": 8}, preferred)
    original = session.check_with
    session.check_with = lambda constraint: (asked.append(constraint.kind), original(constraint))[1]
    assert canonical_witness(session, TARGETS, ["|p:0|"]) == {"a": 8, "b": 9}
    assert "preference" not in asked


def test_an_inconclusive_question_is_not_turned_into_an_answer():
    class _Inconclusive(_EnumeratedSession):
        def check_with(self, constraint):
            raise WitnessUnavailable(INCONCLUSIVE, "unknown")

    models = _models(lambda a, b: a + b == 17)
    with pytest.raises(WitnessUnavailable):
        canonical_witness(_Inconclusive(models, models[0]), TARGETS)


# ---------------------------------------------------------------------------
# z3 backend: 返す model は script の意味だけで決まる
# ---------------------------------------------------------------------------


SCRIPT = """(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(assert (= (bvadd (bvmul x #x00000003) y) #x0000abcd))
(assert (bvugt y #x00000100))
(check-sat)
"""

REORDERED = """(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(assert (bvult #x00000100 y))
(assert (= #x0000abcd (bvadd y (bvmul #x00000003 x))))
(check-sat)
"""


def _solve(script):
    solver = Z3Solver(timeout=10)
    assert solver.check_availability()[0]
    result = solver.check_equivalence_direct(script)
    assert result.status == SolverStatus.SAT
    return result.model


def _pollute_main_context(count):
    rng = random.Random(count)
    for index in range(count):
        left, right = z3.BitVec(f"pollute{index}_a", 32), z3.BitVec(f"pollute{index}_b", 32)
        solver = z3.Solver()
        solver.add(left * rng.randint(3, 99) + right == rng.randint(0, 1 << 30), left != right)
        solver.check()


def test_the_backend_model_is_the_least_model():
    model = _solve(SCRIPT)
    assert model == {"x": 0, "y": 0xABCD}


def test_the_backend_model_does_not_depend_on_what_was_solved_before():
    reference = _solve(SCRIPT)
    _pollute_main_context(300)
    assert _solve(SCRIPT) == reference
    for seed in (1, 7, 12345):
        z3.set_param("smt.random_seed", seed)
        z3.set_param("sat.random_seed", seed)
        try:
            assert _solve(SCRIPT) == reference
        finally:
            z3.set_param("smt.random_seed", 0)
            z3.set_param("sat.random_seed", 0)


def test_the_same_meaning_written_differently_gives_the_same_model():
    assert _solve(REORDERED) == _solve(SCRIPT)


def test_only_declared_scalar_inputs_are_part_of_the_witness():
    script = """(set-logic QF_AUFBV)
(declare-const mem64 (Array (_ BitVec 64) (_ BitVec 64)))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const p (_ BitVec 8))
(assert (= (f p) #x05))
(assert (= (select mem64 ((_ zero_extend 56) p)) #x0000000000000007))
(check-sat)
"""
    assert _solve(script) == {"p": 0}


@pytest.mark.parametrize(
    "kind, status",
    [
        (BUDGET_EXHAUSTED, SolverStatus.TIMEOUT),
        (INCONCLUSIVE, SolverStatus.UNKNOWN),
        (CANCELLED, SolverStatus.UNKNOWN),
    ],
)
def test_a_sat_whose_witness_cannot_be_determined_is_not_reported_as_sat(monkeypatch, kind, status):
    """witness の無い SAT は返さない: 既存の「判定できなかった」経路（TIMEOUT / UNKNOWN）へ。"""

    def _unavailable(*_args, **_kwargs):
        raise WitnessUnavailable(kind, "test")

    monkeypatch.setattr(z3_backend, "canonical_declared_model", _unavailable)
    solver = Z3Solver(timeout=10)
    solver.check_availability()
    result = solver.check_equivalence_direct(SCRIPT)
    assert result.status == status
    assert result.model is None
    assert "SAT without canonical witness" in (result.error_message or "")


SORTS = """(set-logic ALL)
(declare-const flag Bool)
(declare-const count Int)
(declare-const |odd name| (_ BitVec 8))
(declare-fun late () (_ BitVec 4))
(declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
(assert (=> flag (> count 3)))
(assert (or flag (< count (- 2))))
(assert (= (select mem |odd name|) #x07))
(assert (bvugt |odd name| #x10))
(assert (= late #x3))
(check-sat)
"""


def test_every_declared_scalar_input_is_bound_with_its_python_type():
    model = _solve(SORTS)
    # 宣言順・成分ごとの最小: flag=false が最小 → count は < -2 のうち絶対値最小の -3
    assert model == {"flag": False, "count": -3, "|odd name|": 0x11, "late": 3}
    assert type(model["flag"]) is bool and type(model["count"]) is int
    assert "mem" not in model


def test_a_quoted_symbol_names_the_constant_the_formula_uses():
    script = """(declare-const |a b| (_ BitVec 8))
(assert (= |a b| #x2a))
(check-sat)
"""
    assert _solve(script) == {"|a b|": 0x2A}


def test_the_authority_witness_replay_accepts_the_backend_witness():
    """z3 の SAT の witness を、authority の witness replay の契約（全宣言の束縛・sort
    どおりの値）がそのまま受け入れる。fixture の model ではなく実 backend の model で見る。"""

    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        NONPRODUCTION_TEST_SOLVER_EXECUTION_ISSUER,
        PINNED_RELATIONAL_WITNESS_VERIFIER,
        ProducerAttemptMembership,
        ProducerStageContract,
        ProducerStageRegistry,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult

    declarations = (
        "(declare-const flag Bool)",
        "(declare-const count Int)",
        "(declare-const v (_ BitVec 8))",
    )
    premise = ("(assert (=> flag (> count 3)))", "(assert (bvugt v #x10))")
    normalized = "(or flag (< count 0))"
    query = "\n".join(declarations + premise + (f"(assert {normalized})", "(check-sat)"))
    backend = Z3Solver(timeout=10)
    backend.check_availability()
    sat = backend.check_equivalence_direct(query)
    assert sat.status == SolverStatus.SAT and sat.model is not None

    stage = ProducerStageContract(
        "call-effect-domain-v1", "typed-call-effect-solver-v1", "1", "guard_relation",
        "nonproduction-test-solver-results-v1",
        frozenset(("proved", "unknown", "timeout", "error", "refuted")), frozenset(("timeout",)), 10,
    )
    registry = ProducerStageRegistry(1, (stage,))
    membership = ProducerAttemptMembership(
        "call-effect-domain-v1", "typed-call-effect-solver-v1", "1", "guard_relation", "req-guard",
        "obligation-1", "observation-contract", "refuted", "attempt-1", 1, "execution-identity",
    )
    execution = NONPRODUCTION_TEST_SOLVER_EXECUTION_ISSUER.issue_results(
        registry=registry, result_occurrence_id="result-1", membership=membership,
        invocation_identity="invocation-1", first_invocation_ordinal=1, query=query,
        configured_timeout_ms=10000, results=(sat,),
    )[0]
    replay = PINNED_RELATIONAL_WITNESS_VERIFIER.issue(
        execution, registry=registry, membership=membership, obligation_id="obligation-1",
        prepared_surface_digest="prepared-surface", observation_contract_id="observation-contract",
        normalized_assertion=normalized, premise={"assertions": premise},
        stage_input={"declarations": declarations}, model=execution.model_authority,
        configured_timeout_ms=10000,
        nonproduction_replay_results=(SolverResult("fixture", SolverStatus.SAT, model=dict(sat.model)),),
    )
    assert replay is not None


# ---------------------------------------------------------------------------
# 時間予算: 1 回の実行に 1 つの期限（初回の check と witness の探索で共有）
# ---------------------------------------------------------------------------


class _RecordingSolver:
    """z3 の solver を包み、最初の `check()` を `delay` 秒遅らせ、timeout の設定を記録する。"""

    def __init__(self, inner, delay=0.0):
        self._inner = inner
        self._delay = delay
        self._first = True
        self.timeouts_ms = []

    def check(self, *args):
        if self._first:
            self._first = False
            import time

            time.sleep(self._delay)
        return self._inner.check(*args)

    def set(self, *args, **kwargs):
        if args and args[0] == "timeout":
            self.timeouts_ms.append(args[1])
        if "timeout" in kwargs:
            self.timeouts_ms.append(kwargs["timeout"])
        return self._inner.set(*args, **kwargs)

    def __getattr__(self, name):
        return getattr(self._inner, name)


def _wrap_z3_solvers(monkeypatch, delay):
    made = []
    real_solver = z3.Solver

    def _factory(*args, **kwargs):
        made.append(_RecordingSolver(real_solver(*args, **kwargs), delay))
        return made[-1]

    monkeypatch.setattr(z3, "Solver", _factory)
    return made


def _capture_witness_deadline(monkeypatch):
    import time

    seen = {}
    original = z3_backend.canonical_declared_model

    def _capture(z3_module, solver, prepared, *, budget):
        seen["remaining"] = budget.deadline - time.monotonic()
        return original(z3_module, solver, prepared, budget=budget)

    monkeypatch.setattr(z3_backend, "canonical_declared_model", _capture)
    return seen


def _count_parses(monkeypatch):
    calls = []
    real_parse = z3.parse_smt2_string

    def _parse(*args, **kwargs):
        calls.append(args[0])
        return real_parse(*args, **kwargs)

    monkeypatch.setattr(z3, "parse_smt2_string", _parse)
    return calls


def test_the_witness_search_gets_only_what_the_first_check_left(monkeypatch):
    seen = _capture_witness_deadline(monkeypatch)
    _wrap_z3_solvers(monkeypatch, 1.5)
    solver = Z3Solver(timeout=3)
    solver.check_availability()
    assert solver.check_equivalence_direct(SCRIPT).status == SolverStatus.SAT
    assert seen["remaining"] <= 3 - 1.5 + 0.05


def test_query_preparation_is_part_of_the_execution_budget(monkeypatch):
    """parse と witness の優先の項の用意も期限に数える（初回の check には残りだけ）。"""

    import time

    seen = _capture_witness_deadline(monkeypatch)
    made = _wrap_z3_solvers(monkeypatch, 0.0)
    original_prepare = z3_backend.prepare_witness_query

    def _slow_prepare(*args, **kwargs):
        time.sleep(1.5)
        return original_prepare(*args, **kwargs)

    monkeypatch.setattr(z3_backend, "prepare_witness_query", _slow_prepare)
    solver = Z3Solver(timeout=3)
    solver.check_availability()
    assert solver.check_equivalence_direct(SCRIPT).status == SolverStatus.SAT
    assert made and made[0].timeouts_ms[0] <= 1500 + 50
    assert seen["remaining"] <= 3 - 1.5 + 0.05


def test_a_preparation_that_uses_the_whole_budget_never_checks(monkeypatch):
    import time

    made = _wrap_z3_solvers(monkeypatch, 0.0)
    original_prepare = z3_backend.prepare_witness_query

    def _slow_prepare(*args, **kwargs):
        time.sleep(1.1)
        return original_prepare(*args, **kwargs)

    monkeypatch.setattr(z3_backend, "prepare_witness_query", _slow_prepare)
    solver = Z3Solver(timeout=1)
    solver.check_availability()
    result = solver.check_equivalence_direct(SCRIPT)
    assert result.status == SolverStatus.TIMEOUT
    assert made[0]._first is True  # check は呼ばれていない


def test_one_execution_never_uses_more_than_its_budget(monkeypatch):
    import time

    _wrap_z3_solvers(monkeypatch, 1.2)
    original_check_with = z3_backend._Z3WitnessSession.check_with

    def _slow_check_with(self, constraint):
        time.sleep(0.3)
        return original_check_with(self, constraint)

    monkeypatch.setattr(z3_backend._Z3WitnessSession, "check_with", _slow_check_with)
    solver = Z3Solver(timeout=2)
    solver.check_availability()
    started = time.monotonic()
    result = solver.check_equivalence_direct(SCRIPT)
    elapsed = time.monotonic() - started
    # 探索が期限で打ち切られ、SAT ではなく TIMEOUT（予算切れ）になる
    assert result.status == SolverStatus.TIMEOUT
    assert result.model is None
    assert elapsed <= 2 + 0.4


def test_the_witness_search_does_not_parse_the_script_again(monkeypatch):
    """preference の項は実行の最初の 1 回の parse で用意する（witness 段で読み直さない）。"""

    preference = "\n".join(witness_preference_lines([_fp_param("p")], [_fp_param("q")]))
    script = NAN_FIRST.format(preference=preference)
    calls = _count_parses(monkeypatch)
    model = _solve(script)
    assert model == {"p": 0x8000000000000000, "q": 0}
    assert len(calls) == 1


def test_the_shared_region_session_shares_one_budget_between_check_and_witness(monkeypatch):
    from scripts.function_tracer_pcode.proof import monolithic_authority

    seen = _capture_witness_deadline(monkeypatch)
    formula = "(declare-const x (_ BitVec 16))\n(assert (bvugt x #x0010))\n(check-sat)"
    session = _shared_session([formula])
    session._solver = _RecordingSolver(session._solver, 1.5)
    assert isinstance(session, monolithic_authority.SharedZ3RegionSession)
    calls = _count_parses(monkeypatch)
    result = session.execute(formula, 3)
    item = result.results[0]
    assert item.status == SolverStatus.SAT and item.model == {"x": 0x11}
    assert seen["remaining"] <= 3 - 1.5 + 0.05
    assert calls == []  # execute の中で script を parse しない
    assert result.backend_aggregate is not None  # 1 query の結果として集約されている


# 中止と期限切れの規則・SAT の確定の手順は test_issue161_execution_lifecycle.py


# ---------------------------------------------------------------------------
# NaN: 規則の定義は 1 箇所、NaN でない witness があれば NaN は返らない
# ---------------------------------------------------------------------------


def _fp_param(name):
    return ParameterInfo(
        original_name=name, smt_name=name, bit_width=64, index=0, is_signed=True, type_class="fp",
    )


NAN_FIRST = """(set-logic QF_BV)
(declare-const p (_ BitVec 64))
(declare-const q (_ BitVec 64))
{preference}
(assert (or (= p #x7ff0000000000001) (bvslt p #x0000000000000000)))
(assert (= q #x0000000000000000))
(check-sat)
"""


def test_without_a_preference_the_least_model_can_be_a_nan():
    model = _solve(NAN_FIRST.format(preference=""))
    assert is_nan_bit_pattern(model["p"], 64)


def test_the_non_nan_preference_returns_a_non_nan_witness_when_one_exists():
    preference = "\n".join(witness_preference_lines([_fp_param("p")], [_fp_param("q")]))
    model = _solve(NAN_FIRST.format(preference=preference))
    assert not is_nan_bit_pattern(model["p"], 64)
    assert model == {"p": 0x8000000000000000, "q": 0}


def test_the_preference_is_not_an_assertion():
    """preference を置いても論理式の意味（充足可能性）は変わらない。"""

    only_nan = NAN_FIRST.replace(
        "(assert (or (= p #x7ff0000000000001) (bvslt p #x0000000000000000)))",
        "(assert (= p #x7ff0000000000001))",
    )
    preference = "\n".join(witness_preference_lines([_fp_param("p")], []))
    model = _solve(only_nan.format(preference=preference))
    assert model["p"] == 0x7FF0000000000001


@pytest.mark.parametrize("width", [32, 64])
def test_the_smt_nan_predicate_and_the_replay_rule_agree(width):
    rng = random.Random(width)
    exponent_bits, mantissa_bits = (8, 23) if width == 32 else (11, 52)
    samples = [0, 1, (1 << width) - 1]
    exp_all = ((1 << exponent_bits) - 1) << mantissa_bits
    samples += [exp_all, exp_all | 1, exp_all | (1 << (width - 1)), exp_all | 1 | (1 << (width - 1))]
    samples += [rng.getrandbits(width) for _ in range(200)]
    param = ParameterInfo(
        original_name="v", smt_name="v", bit_width=width, index=0, is_signed=True, type_class="fp",
    )
    body = witness_preference_lines([param], [])[-1]
    for value in samples:
        script = (
            f"(declare-const v (_ BitVec {width}))\n{body}\n"
            f"(assert (= v (_ bv{value} {width})))\n(assert {NON_NAN_FP_PREFERENCE})"
        )
        solver = z3.Solver(ctx=z3.Context())
        solver.add(z3.parse_smt2_string(script, ctx=solver.ctx))
        smt_says_not_nan = solver.check() == z3.sat
        assert smt_says_not_nan == (not is_nan_bit_pattern(value, width)), hex(value)


def test_non_fp_parameters_declare_no_preference():
    integer = ParameterInfo(
        original_name="i", smt_name="i", bit_width=64, index=0, is_signed=True, type_class="int",
    )
    assert witness_preference_lines([integer], [integer]) == []


def test_the_formula_header_carries_the_preference():
    source = (PACKAGE_ROOT / "proof" / "formula" / "builder.py").read_text(encoding="utf-8")
    assert "lines.extend(witness_preference_lines(params1, params2))" in source
    executor = (PACKAGE_ROOT / "proof" / "strategies" / "pairwise_query_executor.py").read_text(
        encoding="utf-8"
    )
    assert "from scripts.function_tracer_pcode.proof.formula.witness_domain import" in executor


# ---------------------------------------------------------------------------
# monolithic の共有 session も同じ規則
# ---------------------------------------------------------------------------


class _Query:
    def __init__(self, formula):
        import hashlib

        self.formula = formula
        self.contract = type("C", (), {"formula_digest": hashlib.sha256(formula.encode()).hexdigest()})()


def _shared_session(formulas):
    """`SharedZ3RegionSession` を region query の集合だけから組む（本番と同じ準備を使う）。"""

    from scripts.function_tracer_pcode.proof import monolithic_authority

    session = monolithic_authority.SharedZ3RegionSession.__new__(
        monolithic_authority.SharedZ3RegionSession
    )
    session._z3 = z3
    session._ctx = z3.Context()
    session._solver = z3.Solver(ctx=session._ctx)
    # 本番と同じく region の formula の文字列で引く（#218 PR-D）
    session._prepared = {
        query.formula: z3_backend.prepare_witness_query(z3, query.formula, session._ctx)
        for query in map(_Query, formulas)
    }
    session._specific = {formula: prepared.assertions for formula, prepared in session._prepared.items()}
    session.check_count = 0
    return session


def test_the_shared_region_session_returns_the_same_witness_in_any_region_order():
    common = "(declare-const x (_ BitVec 16))\n(declare-const y (_ BitVec 16))\n(assert (bvugt x #x0010))\n"
    region_a = common + "(assert (= (bvadd x y) #x0100))\n(check-sat)"
    region_b = common + "(assert (= (bvxor x y) #x00ff))\n(check-sat)"

    def _run(order):
        session = _shared_session([region_a, region_b])
        return {formula: session.execute(formula, 5).results[0].model for formula in order}

    forward = _run([region_a, region_b])
    backward = _run([region_b, region_a])
    assert forward == backward
    assert forward[region_a] == {"x": 0x11, "y": 0xEF}


# ---------------------------------------------------------------------------
# production の z3 利用は main context を共有しない
# ---------------------------------------------------------------------------


def _z3_calls_without_context(tree):
    offenders = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Attribute):
            continue
        if node.func.attr not in {"Solver", "parse_smt2_string"}:
            continue
        receiver = node.func.value
        receiver_name = getattr(receiver, "id", None) or getattr(receiver, "attr", None)
        if receiver_name not in {"z3", "_z3"}:
            continue
        if not any(keyword.arg == "ctx" for keyword in node.keywords):
            offenders.append(node.lineno)
    return offenders


def test_production_z3_solvers_and_parses_name_their_context():
    """z3 の Solver / parse は明示した context で作る（process 共有の main context に履歴を残さない）。"""

    offenders = {}
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        if "tests" in path.relative_to(PACKAGE_ROOT).parts:
            continue
        lines = _z3_calls_without_context(ast.parse(path.read_text(encoding="utf-8")))
        if lines:
            offenders[str(path.relative_to(PACKAGE_ROOT))] = lines
    assert offenders == {}


def test_the_static_rule_detects_a_context_free_solver():
    tree = ast.parse("import z3\ns = z3.Solver()\nz3.parse_smt2_string('x', ctx=c)\n")
    assert _z3_calls_without_context(tree) == [2]
