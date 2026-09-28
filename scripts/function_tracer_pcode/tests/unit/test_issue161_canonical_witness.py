# -*- coding: utf-8 -*-
"""Issue #161: SAT の witness は script の意味だけで決まる（solver の履歴に依らない）。

固定する契約:

* `canonical_witness` の結果は、元の論理式の model のうち（満たせる preference を満たし）
  宣言順の値の列が辞書式最小のもの。**最初に渡された model に依らない**
* z3 backend が返す SAT の model は、同じ process で先に何を解いたか・z3 の random
  seed・assertion の並べ方・同じ意味の別の書き方に依らない
* 浮動小数点の引数が NaN でない witness が存在すれば、NaN の witness は返らない
  （NaN の規則の定義は `proof.formula.witness_domain` の 1 箇所）
* witness を決められない SAT は model 無し（replay は受け入れない = fail closed）
* production の z3 利用は process 共有の main context を使わない
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
    Constraint,
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

    def _holds(self, constraint, model):
        if constraint.kind == "preference":
            return self._preferences[constraint.preference](model)
        value = model[constraint.target.name]
        if constraint.kind == "bit":
            return ((value >> constraint.bit) & 1) == constraint.value
        if constraint.kind == "eq":
            return value == constraint.value
        return value != constraint.value

    def values(self):
        return dict(self._current)

    def check_with(self, constraint):
        self.checks += 1
        for model in self._models:
            if all(self._holds(c, model) for c in self._fixed) and self._holds(constraint, model):
                return dict(model)
        return None

    def fix(self, constraint):
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


def test_a_value_fixed_by_the_formula_costs_one_question():
    models = _models(lambda a, b: a == 15 and b == 15)
    session = _EnumeratedSession(models, models[0])
    assert canonical_witness(session, TARGETS) == {"a": 15, "b": 15}
    assert session.checks == 2


def test_an_inconclusive_question_is_not_turned_into_an_answer():
    class _Inconclusive(_EnumeratedSession):
        def check_with(self, constraint):
            raise WitnessUnavailable("timeout")

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


def test_a_witness_that_cannot_be_determined_leaves_the_sat_without_a_model(monkeypatch):
    def _unavailable(*_args, **_kwargs):
        raise WitnessUnavailable("budget")

    monkeypatch.setattr(z3_backend, "canonical_declared_model", _unavailable)
    solver = Z3Solver(timeout=10)
    solver.check_availability()
    result = solver.check_equivalence_direct(SCRIPT)
    assert result.status == SolverStatus.SAT
    assert result.model is None
    assert "canonical witness unavailable" in (result.error_message or "")


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


def test_the_shared_region_session_returns_the_same_witness_in_any_region_order():
    from scripts.function_tracer_pcode.proof import monolithic_authority

    common = "(declare-const x (_ BitVec 16))\n(declare-const y (_ BitVec 16))\n(assert (bvugt x #x0010))\n"
    region_a = common + "(assert (= (bvadd x y) #x0100))\n(check-sat)"
    region_b = common + "(assert (= (bvxor x y) #x00ff))\n(check-sat)"

    class _Query:
        def __init__(self, formula):
            import hashlib

            self.formula = formula
            self.contract = type("C", (), {"formula_digest": hashlib.sha256(formula.encode()).hexdigest()})()

    def _session(order):
        session = monolithic_authority.SharedZ3RegionSession.__new__(
            monolithic_authority.SharedZ3RegionSession
        )
        session._z3 = z3
        session._ctx = z3.Context()
        session._solver = z3.Solver(ctx=session._ctx)
        session._specific = {
            query.contract.formula_digest: tuple(z3.parse_smt2_string(query.formula, ctx=session._ctx))
            for query in (_Query(region_a), _Query(region_b))
        }
        session.check_count = 0
        results = {}
        for formula in order:
            parallel = session.execute(formula, 5)
            results[formula] = parallel.results[0].model
        return results

    forward = _session([region_a, region_b])
    backward = _session([region_b, region_a])
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


# ---------------------------------------------------------------------------
# runner: canonical な witness を作れない backend の model は採らない
# ---------------------------------------------------------------------------


def test_the_runner_drops_a_model_from_a_backend_without_the_witness_contract():
    from scripts.function_tracer_pcode.smt.interface import SMTSolver, SolverResult
    from scripts.function_tracer_pcode.smt.parallel import ParallelSolverRunner

    class _ArbitraryModelBackend(SMTSolver):
        @property
        def name(self):
            return "arbitrary"

        def check_availability(self):
            return True, "test"

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            return SolverResult(self.name, SolverStatus.SAT, model={"x": 42})

    class _CanonicalBackend(_ArbitraryModelBackend):
        PROVIDES_CANONICAL_WITNESS = True

    arbitrary = ParallelSolverRunner(timeout=1, solver_classes=[_ArbitraryModelBackend])
    result = arbitrary.run_sequential("(check-sat)")
    assert result.is_equivalent is False
    assert result.get_counterexample() is None
    assert "canonical witness unavailable" in result.results[0].error_message

    canonical = ParallelSolverRunner(timeout=1, solver_classes=[_CanonicalBackend])
    assert canonical.run_sequential("(check-sat)").get_counterexample() == {"x": 42}
    assert Z3Solver.PROVIDES_CANONICAL_WITNESS is True
