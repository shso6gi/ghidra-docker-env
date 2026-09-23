# -*- coding: utf-8 -*-
"""M-3（出力 schema の局所性）の再生 driver（Issue #22 PR-22-D）。

1 process で 1 回だけ記録済み pair を再生し（recorded-pair test と同じ process
条件）、solver へ渡った SMT script の digest を記録する。`extra` を渡すと、
再生の前に判定に関わらない診断 field を出力の表へ 1 行だけ足す — 足したのが
出力層の 1 行だけで、意味の経路（solver query・判定・reason）が動かないことを
親の test が比べる。
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path


def main(argv) -> int:
    case_id, mode, output = argv
    from scripts.function_tracer_pcode.analysis.condition.smt_oracle import (
        ConditionSMTOracle,
    )
    from scripts.function_tracer_pcode.checker import output_preparation
    from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
    from scripts.function_tracer_pcode.tests.fixtures.pcode import replay_worker

    queries = []
    original_direct = Z3Solver.check_equivalence_direct
    original_build = ConditionSMTOracle._build_script.__func__

    def _logged_direct(self, smt_script, *args, **kwargs):
        queries.append(("pairwise", hashlib.sha256(smt_script.encode()).hexdigest()))
        return original_direct(self, smt_script, *args, **kwargs)

    def _logged_build(cls, conditions):
        usable, script = original_build(cls, conditions)
        if script is not None:
            queries.append(("oracle", hashlib.sha256(script.encode()).hexdigest()))
        return usable, script

    Z3Solver.check_equivalence_direct = _logged_direct
    ConditionSMTOracle._build_script = classmethod(_logged_build)
    if mode == "extra":
        output_preparation.RESULT_FIELDS = output_preparation.RESULT_FIELDS + (
            output_preparation.OutputField(
                "m3_extra_diagnostic",
                output_preparation.FieldOwner.METADATA,
                lambda result, options: (True, {"observed": 1}),
                output_preparation.Overflow.TRUNCATE,
            ),
        )
    case_dir = Path(replay_worker.__file__).resolve().parent / case_id
    report_path = Path(output + ".report.json")
    code = replay_worker.main([
        "--case-dir", str(case_dir), "--case-id", case_id,
        "--variant", "recorded", "--fast-path", "recorded",
        "--output", str(report_path),
    ])
    report = json.loads(report_path.read_text(encoding="utf-8"))
    report["solver_queries"] = sorted(queries)
    Path(output).write_text(json.dumps(report, default=str), encoding="utf-8")
    return code


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
