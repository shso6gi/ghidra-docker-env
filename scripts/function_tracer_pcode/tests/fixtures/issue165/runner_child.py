# -*- coding: utf-8 -*-
"""Issue #165 T18: runner の ``run_pair`` から起動される child の代役（test 専用）。

runner は supervisor の下で ``python -m scripts.function_tracer_pcode.cli.main
--equiv L R --binary-ids A B -f F ...`` を起こす。test の ``PYTHON_BIN`` wrapper は
その呼び出しだけをこの module に差し替える。ここは Ghidra を使わず、PR #193 の
harness の worker（``_supervisor_child``）を、runner が launch に焼いたのと同じ
execution identity（binary の中身・id・関数名・観測契約・occurrence nonce）で
動かす。何をするかは関数名で決める（``SCRIPTS``）。
"""

from __future__ import annotations

import hashlib
import json
import os
import sys

#: runner が ``env`` で渡す occurrence nonce。production の import が環境から
#: 取り去る（1 回だけ読む）ので、何も import しないうちに読んでおく。
_OCCURRENCE_NONCE = os.environ.get("UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE")

from scripts.function_tracer_pcode.tests.unit._supervisor_child import (  # noqa: E402
    Checkpoint,
    Envelope,
    Exit,
    Stop,
    main as child_main,
)

#: 関数名 -> worker の step（runner の pair を 1 つの終わり方に対応させる）。
SCRIPTS = {
    "timeoutpair": (Checkpoint(), Stop()),
    "invalidpair": (Checkpoint(), Exit(0)),
    "errorpair": (Checkpoint(), Envelope("ERROR"), Exit()),
    "unknownpair": (Checkpoint(), Envelope("UNKNOWN"), Exit()),
}


def _value(arguments: list[str], flag: str, count: int = 1) -> list[str]:
    index = arguments.index(flag)
    return arguments[index + 1:index + 1 + count]


def execution_payload(arguments: list[str]) -> dict:
    """``production_cutover --print-production-execution-identity`` と同じ payload。"""

    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        EquivalenceObservationContract,
    )

    left, right = _value(arguments, "--equiv", 2)
    left_id, right_id = _value(arguments, "--binary-ids", 2)
    (function,) = _value(arguments, "-f")

    def content(path: str) -> tuple[str, str]:
        with open(path, "rb") as handle:
            return ("sha256", hashlib.sha256(handle.read()).hexdigest())

    return {
        "binary1_id": left_id,
        "binary2_id": right_id,
        "binary1_content_identity": content(left),
        "binary2_content_identity": content(right),
        "function_name1": function,
        "function_name2": function,
        "observation_contract_id": EquivalenceObservationContract().contract_id,
    }


def main(arguments: list[str]) -> int:
    if not _OCCURRENCE_NONCE:
        raise SystemExit("runner child: the runner passed no occurrence nonce")
    (function,) = _value(arguments, "-f")
    spec = {
        "case_payload": execution_payload(arguments),
        "occurrence_nonce": _OCCURRENCE_NONCE,
        "records": os.environ["ISSUE165_HARNESS_RECORDS"],
        "steps": [step.to_json() for step in SCRIPTS[function]],
        "faults": [],
    }
    return child_main([json.dumps(spec, sort_keys=True)])


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
