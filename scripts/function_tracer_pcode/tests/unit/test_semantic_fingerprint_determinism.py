# -*- coding: utf-8 -*-
"""semantic fingerprint / analysis scope key の決定性（Issue #22 PR-22-A、AC A1）。

`AnalysisSnapshot` の `semantic_fingerprint` は proof cache と証明の前提を結ぶ
identity なので、**同じ意味には同じ値**でなければならない。#22 が
`Expression` の freeze と structural hash を入れる前に、現在の決定性を先に
固定しておくための test。

固定する 3 つの性質:

1. 同じ analysis を 2 回 snapshot しても fingerprint / snapshot_id が同じ
   （snapshot 生成が解析 object を書き換えない、時刻や採番に依存しない）。
2. 容器の反復順が fingerprint に漏れない（mapping の挿入順、set の構築順、
   さらに **process をまたいで** `PYTHONHASHSEED` が変わっても同じ）。
   set の反復順は hash 順なので、これは同一 process 内では観測できない。
3. `analysis_scope_key` が storage map の挿入順に依存しない。

どれも「今の実装がそうである」ことの記録であって、値そのもの（digest 文字列）は
固定しない。表現が変われば digest は変わってよい。
"""

from __future__ import annotations

import subprocess
import sys
import textwrap
from pathlib import Path

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.proof.obligations.snapshot import (
    AnalysisSnapshot,
    SnapshotFingerprintCodec,
)
from scripts.function_tracer_pcode.tests.conftest import MockProgram, create_mock_analysis


REPO_ROOT = Path(__file__).resolve().parents[4]

#: subprocess 側で digest を 1 つ出すだけの script。set を含む payload を使う。
_SUBPROCESS_DIGEST_SCRIPT = textwrap.dedent(
    """
    import sys
    sys.path.insert(0, sys.argv[1])
    from scripts.function_tracer_pcode.proof.obligations.snapshot import (
        SnapshotFingerprintCodec,
    )

    payload = {
        "notes": {"beta", "alpha", "gamma", "delta"},
        "ids": frozenset({"b2", "b1", "b10"}),
        "mapping": {"z": 1, "a": 2, "m": 3},
    }
    print(SnapshotFingerprintCodec.digest(payload))
    """
)


def _analysis(function_name: str = "f"):
    return create_mock_analysis(
        function_name,
        "int",
        [
            {"name": "param_1", "data_type": "int"},
            {"name": "param_2", "data_type": "int"},
        ],
    )


def _digest_in_subprocess(hash_seed: str) -> str:
    completed = subprocess.run(
        [sys.executable, "-B", "-c", _SUBPROCESS_DIGEST_SCRIPT, str(REPO_ROOT)],
        capture_output=True,
        text=True,
        check=True,
        env={"PYTHONHASHSEED": hash_seed, "PATH": "/usr/bin:/bin"},
    )
    return completed.stdout.strip()


def test_snapshot_fingerprint_is_stable_for_the_same_analysis():
    analysis = _analysis()

    first = AnalysisSnapshot.from_function_analysis(analysis)
    second = AnalysisSnapshot.from_function_analysis(analysis)

    assert first.semantic_fingerprint == second.semantic_fingerprint
    assert first.snapshot_id == second.snapshot_id
    # 別 object でも意味が同じなら同じ fingerprint（object identity に依存しない）。
    rebuilt = AnalysisSnapshot.from_function_analysis(_analysis())
    assert rebuilt.semantic_fingerprint == first.semantic_fingerprint


def test_snapshot_fingerprint_ignores_container_iteration_order():
    forward = AnalysisSnapshot.create(
        ("fingerprint_determinism",),
        {"notes": {"alpha", "beta", "gamma"}, "mapping": {"a": 1, "b": 2, "c": 3}},
    )
    reversed_insertion = AnalysisSnapshot.create(
        ("fingerprint_determinism",),
        {"notes": {"gamma", "beta", "alpha"}, "mapping": {"c": 3, "b": 2, "a": 1}},
    )
    assert forward.semantic_fingerprint == reversed_insertion.semantic_fingerprint

    # mapping の挿入順は同一 process でも観測できる（dict は挿入順を保つ）。
    assert SnapshotFingerprintCodec.freeze({"b": 1, "a": 2}) == SnapshotFingerprintCodec.freeze(
        {"a": 2, "b": 1}
    )

    # set の反復順は hash 順なので、process をまたいで確認する。
    digests = {_digest_in_subprocess(seed) for seed in ("0", "1", "424242")}
    assert len(digests) == 1, f"set iteration order leaked into the digest: {sorted(digests)}"


def test_analysis_scope_key_ignores_storage_map_insertion_order():
    analyzer = ReturnAnalyzer(program=MockProgram(name="mock"), debug=False, binary_id="B1")

    first_value = Expression.parameter("param_1", 0, "int", None, 4)
    second_value = Expression.parameter("param_2", 1, "int", None, 4)
    third_value = Expression.constant(7, 4)

    bound_values = {0: first_value, 1: second_value}
    storage_entries = [
        (("register", "a0", 4), first_value),
        (("stack", 0x10, 8), second_value),
        (("register", "a1", 4), third_value),
    ]

    forward = analyzer._analysis_scope_key(
        None,
        dict(bound_values),
        dict(storage_entries),
    )
    backward = analyzer._analysis_scope_key(
        None,
        dict(reversed(list(bound_values.items()))),
        dict(reversed(storage_entries)),
    )

    # storage signature を実際に通っていること（空 tuple 同士の一致ではない）。
    assert len(forward[3]) == len(storage_entries)
    assert forward == backward
