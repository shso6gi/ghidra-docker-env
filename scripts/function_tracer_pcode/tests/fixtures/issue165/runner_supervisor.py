# -*- coding: utf-8 -*-
"""Issue #226: runner が起こす production の supervisor の代わりの入口（test 専用）。

T18 の ``PYTHON_BIN`` wrapper は、runner の ``python -m
scripts.function_tracer_pcode.authority.process.supervisor_command ...`` をこの module へ
差し替える。ここは deadline を worker の ``stop`` に結ぶ制御
（``_supervisor_faults.install_runner_deadline_at_worker_stop``）を入れてから、同じ引数で
production の supervisor の ``main`` を呼ぶ。supervisor の監視・signal・終端の規則は production の
まま。
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

from scripts.function_tracer_pcode.authority.process.supervisor_command import main
from scripts.function_tracer_pcode.tests.unit._supervisor_faults import (
    install_runner_deadline_at_worker_stop,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_records import HarnessRecords

#: どの pair がどの経路で deadline を迎えたか（test が読む。``ISSUE165_HARNESS_RECORDS`` の下）
DEADLINE_CONTROL_RECORD = "runner-deadline-control.jsonl"


if __name__ == "__main__":
    root = Path(os.environ["ISSUE165_HARNESS_RECORDS"])
    install_runner_deadline_at_worker_stop(HarnessRecords(root), sink=root / DEADLINE_CONTROL_RECORD)
    raise SystemExit(main(sys.argv[1:]))
