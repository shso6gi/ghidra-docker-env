"""Replay one recorded pair repeatedly in ONE process under different solver histories (Issue #161).

Invoked as a subprocess by `test_issue161_solver_history_independence.py`.
Each run records the outcome, the canonical reasons and every SAT witness the
backend returned, so the test can assert that none of them depends on what
the condition oracle (or anything else in the process) solved before.
"""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path


def main(argv) -> int:
    case_id, output = argv
    import z3

    from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
    from scripts.function_tracer_pcode.smt.solvers import z3 as z3_backend
    from scripts.function_tracer_pcode.tests.fixtures.pcode import replay_worker

    witnesses = []
    original_direct = z3_backend.Z3Solver.check_equivalence_direct

    def _recording_direct(self, script, token=None):
        result = original_direct(self, script, token)
        if result.status.name == "SAT":
            witnesses.append(json.dumps(result.model, sort_keys=True))
        return result

    z3_backend.Z3Solver.check_equivalence_direct = _recording_direct

    original_oracle = ConditionSMTOracle.conjunction_is_unsat.__func__
    mode = {"name": "baseline"}

    def _oracle(cls, conditions, **kwargs):
        name = mode["name"]
        if name == "oracle_off":
            return None
        if name == "oracle_twice":
            original_oracle(cls, conditions, **kwargs)
        if name == "oracle_reversed":
            conditions = list(reversed(list(conditions or [])))
        if name == "oracle_uncached":
            kwargs = dict(kwargs, use_cache=False)
        return original_oracle(cls, conditions, **kwargs)

    ConditionSMTOracle.conjunction_is_unsat = classmethod(_oracle)

    def _pollute_main_context(count: int) -> None:
        rng = random.Random(count)
        for index in range(count):
            left, right = z3.BitVec(f"h{index}_a", 64), z3.BitVec(f"h{index}_b", 64)
            solver = z3.Solver()
            solver.add(left * rng.randint(3, 999) + right == rng.randint(0, 1 << 60), left != right)
            solver.check()

    schedule = [
        ("baseline", 0, None), ("baseline", 0, None),
        ("pollute_main_context", 500, None),
        ("oracle_off", 0, None), ("oracle_twice", 0, None),
        ("oracle_reversed", 0, None), ("oracle_uncached", 0, None),
        ("z3_random_seed", 0, 7), ("z3_random_seed", 0, 12345),
    ]
    case_dir = Path(replay_worker.__file__).resolve().parent / case_id
    runs = []
    for name, pollution, seed in schedule:
        mode["name"] = name
        if pollution:
            _pollute_main_context(pollution)
        if seed is not None:
            z3.set_param("smt.random_seed", seed)
            z3.set_param("sat.random_seed", seed)
        first = len(witnesses)
        report = replay_worker.run(
            case_dir, case_id=case_id, variant="recorded", fast_path=False, forbid_solver=False,
        )
        payload = report.get("payload") or {}
        runs.append({
            "mode": name,
            "failure": report.get("failure"),
            "outcome": payload.get("final_outcome"),
            "reasons": sorted(row.get("reason_id") for row in payload.get("unknown_reasons", [])),
            "missing": {side: len(rows) for side, rows in report["missing_accesses"].items()},
            "witnesses": witnesses[first:],
        })
        if seed is not None:
            z3.set_param("smt.random_seed", 0)
            z3.set_param("sat.random_seed", 0)
    Path(output).write_text(json.dumps(runs), encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
