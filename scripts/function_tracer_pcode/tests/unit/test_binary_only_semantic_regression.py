# -*- coding: utf-8 -*-
"""Issue #122: 意味判定はバイナリ隣接 `.c` に依存しない。

`run_equivalence_check` から実 `check_from_binaries` → workflow → reanalysis →
実 `_run_stage_plan` → 実 `check` → 実 `assemble_equivalence_result` までを通し、
偽装した `pairwise_strategy.check` だけを差し替える。判定に効く入力が 2 バイナリ
だけであることを、(i) `.c` なし / (ii) 正しい `.c` / (iii) 戻り値型を偽った `.c`
の 3 条件で固定する。

旧実装では (iii) で `P0_SOURCE_DECLARATION` 仮説が両側に適用され、
`with_signature_hypothesis` が return value を `void` に潰して比較面が
effect-only に変わったため、この test は感度を持つ。
"""

import inspect
import json
import os
import shutil
import subprocess
from pathlib import Path
from types import SimpleNamespace

import pytest

import scripts.function_tracer_pcode.analysis as analysis_layer
import scripts.function_tracer_pcode.checker as checker_layer
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.cli.args import build_parser
from scripts.function_tracer_pcode.cli.commands import equivalence as equivalence_cli
from scripts.function_tracer_pcode.core import Expression, ReturnInfo
from scripts.function_tracer_pcode.proof.strategies import StrategyResult
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus

from conftest import MockProgram, create_mock_analysis


_CORRECT_SOURCE = "long f(long a) { return a; }\n"
_FALSE_SOURCE = "void f(long a) { (void)a; }\n"

# 同じ入力・同じレイアウトで 2 回走らせても必ず変わる leaf だけを列挙する
# （乱数のセッション id と実時間）。`debug_trace` / `diagnostics` を丸ごと落とすと
# `effective_function*_signature` のような判定に効く field まで比較対象から外れ、
# AC4 の保証が弱くなるので、key 名で厳密に指定して再帰的に取り除く。
_VOLATILE_KEYS = frozenset({
    "analysis_seconds",
    "analysis_time",
    "comparison_session_id",
    "elapsed_seconds",
    "elapsed_time",
    "process_age_at_start_seconds",
    "solver_time",
    "stage_timing",
    "timings",
    "total_time",
})


def _drop_volatile(value):
    """run ごとに必ず変わる時刻・セッション id だけを再帰的に取り除く。"""
    if isinstance(value, dict):
        return {
            key: _drop_volatile(item)
            for key, item in value.items()
            if key not in _VOLATILE_KEYS
        }
    if isinstance(value, list):
        return [_drop_volatile(item) for item in value]
    return value


def _mock_analysis():
    return create_mock_analysis(
        function_name="f",
        return_type="long",
        parameters=[{"name": "a", "data_type": "long"}],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression.parameter("a", index=0, size=8),
            )
        ],
    )


class _FakeReturnAnalyzer:
    """`analyze_function_by_name` が両側同一の binary-only 解析を返す。"""

    def __init__(self, program, **kwargs):
        self.program = program

    def analyze_function_by_name(self, function_name, timeout=None):
        return _mock_analysis()

    def refresh_structural_recurrence_summary(self, analysis, timeout=None):
        return analysis

    def get_last_analysis_failure(self):
        return None

    def get_last_function_lookup_error(self):
        return None

    def dispose(self):
        return None


def _strategy_result(is_equivalent):
    status = SolverStatus.UNSAT if is_equivalent else SolverStatus.SAT
    return StrategyResult(
        is_equivalent=is_equivalent,
        solver_results=ParallelResult(
            results=[
                SolverResult(
                    solver_name="mock",
                    status=status,
                    elapsed_time=0.0,
                )
            ]
        ),
        total_pairs=1,
        unsat_pairs=1 if is_equivalent else 0,
        sat_pairs=0 if is_equivalent else 1,
    )


def _make_recording_checker_class(observations):
    """比較面に感応する fake strategy を持つ test 用 checker。"""

    class _RecordingChecker(EquivalenceChecker):
        def __init__(self, *args, **kwargs):
            kwargs["canonical_decision_cutover"] = False
            kwargs["call_proof_decision_mode"] = "legacy_post_pairwise"
            super().__init__(*args, **kwargs)
            self.solver_runner.get_available_solvers = lambda: ["mock"]
            self.pairwise_strategy.check = self._fake_pairwise_check

        def _fake_pairwise_check(self, analysis1, analysis2, save_formula=False):
            surface_kinds = (
                analysis1.get_comparison_surface().kind,
                analysis2.get_comparison_surface().kind,
            )
            observations["surface_kinds"] = surface_kinds
            observations["return_type_provenance"] = (
                dict(analysis1.return_type_provenance or {}),
                dict(analysis2.return_type_provenance or {}),
            )
            observations["return_types"] = (
                analysis1.return_type,
                analysis2.return_type,
            )
            return _strategy_result(surface_kinds == ("return_value", "return_value"))

        def check_from_binaries(self, *args, **kwargs):
            result = super().check_from_binaries(*args, **kwargs)
            observations["result"] = result
            return result

    return _RecordingChecker


class _FakeProgramContext:
    def __init__(self, program):
        self._program = program

    def getPrimaryDomainObject(self):
        return self._program

    def __enter__(self):
        return self

    def __exit__(self, *exc_info):
        return False


class _FakeProjectContext:
    def __enter__(self):
        return SimpleNamespace(name="EquivCheckProject")

    def __exit__(self, *exc_info):
        return False


class _FakePyGhidra:
    def open_project(self, *args, **kwargs):
        return _FakeProjectContext()

    def analyze(self, program):
        return None


def _run_cli(monkeypatch, directory, observations):
    binary1 = directory / "newV-arm64-clang-O0"
    binary2 = directory / "newV-mips64-clang-O0"
    binary1.write_bytes(b"\x7fELF-binary-1")
    binary2.write_bytes(b"\x7fELF-binary-2")
    output = directory / "result.txt"
    # production の `write_to_file()` は append で開くので、直前の run の出力が
    # 残っていると `_semantic_projection()` が 1 回目の JSON を読み続けてしまう。
    # 1 CLI 実行 = 1 出力ファイル にしてから走らせる。
    if output.exists():
        output.unlink()

    args = build_parser().parse_args([
        "--equiv", str(binary1), str(binary2),
        "-f", "f",
        "--binary-ids", "B1", "B2",
        "--quiet",
        "--emit-result-json",
        "--output", str(output),
    ])

    monkeypatch.setattr(equivalence_cli, "start_headless_pyghidra", lambda *a, **k: None)
    monkeypatch.setattr(
        equivalence_cli,
        "apply_runtime_environment",
        lambda *a, **k: SimpleNamespace(ghidra_install_dir=None),
    )
    monkeypatch.setattr(equivalence_cli, "load_pyghidra", lambda: _FakePyGhidra())

    programs = iter((
        MockProgram(name="binary1"),
        MockProgram(name="binary2"),
    ))

    def _fake_load_program_context(pyghidra, project, binary_path, import_name, *, quiet):
        context = _FakeProgramContext(next(programs))
        return context, context

    monkeypatch.setattr(equivalence_cli, "_load_program_context", _fake_load_program_context)
    monkeypatch.setattr(analysis_layer, "ReturnAnalyzer", _FakeReturnAnalyzer)
    monkeypatch.setattr(
        checker_layer,
        "EquivalenceChecker",
        _make_recording_checker_class(observations),
    )

    with pytest.raises(SystemExit):
        equivalence_cli.run_equivalence_check(args)

    return output.read_text(encoding="utf-8")


def _semantic_projection(observations, output_text):
    result = observations["result"]
    # この run の JSON だけが入っていること（append で混ざっていないこと）。
    assert output_text.count("=== EQUIVALENCE_RESULT_JSON_BEGIN ===") == 1
    payload = _drop_volatile(json.loads(
        output_text.split("=== EQUIVALENCE_RESULT_JSON_BEGIN ===")[1]
        .split("=== EQUIVALENCE_RESULT_JSON_END ===")[0]
        .strip()
    ))
    return {
        "is_equivalent": result.is_equivalent,
        "function1_signature_hypotheses": list(result.function1_signature_hypotheses),
        "function2_signature_hypotheses": list(result.function2_signature_hypotheses),
        "return_type_provenance": observations["return_type_provenance"],
        "return_types": observations["return_types"],
        "surface_kinds": observations["surface_kinds"],
        "result_json": payload,
    }


def _run_layout(monkeypatch, tmp_path, source_text):
    """同一ディレクトリ・同一バイナリ対のまま隣接 `.c` だけを差し替えて 1 回判定する。

    レイアウトごとにディレクトリを分けると入力パスまで変わってしまい、
    「バイナリ対は同一で `.c` だけが違う」という条件にならない。
    """
    directory = tmp_path / "pair"
    directory.mkdir(exist_ok=True)
    adjacent_source = directory / "newV.c"
    if source_text is None:
        if adjacent_source.exists():
            adjacent_source.unlink()
    else:
        adjacent_source.write_text(source_text, encoding="utf-8")

    observations = {}
    output_text = _run_cli(monkeypatch, directory, observations)
    return _semantic_projection(observations, output_text)


def test_semantic_result_is_identical_without_correct_and_false_adjacent_source(
    monkeypatch, tmp_path
):
    absent = _run_layout(monkeypatch, tmp_path, None)
    correct = _run_layout(monkeypatch, tmp_path, _CORRECT_SOURCE)
    false = _run_layout(monkeypatch, tmp_path, _FALSE_SOURCE)

    assert absent == correct == false
    assert absent["surface_kinds"] == ("return_value", "return_value")
    assert absent["is_equivalent"] is True
    assert absent["function1_signature_hypotheses"] == []
    assert absent["function2_signature_hypotheses"] == []
    # 揮発 leaf の除去が、偽 `.c` の void override で実際に変化する field まで
    # 落としていないことを確認する（落としていれば比較が骨抜きになる）。
    assert absent["result_json"]["effective_function1_signature"]
    assert absent["result_json"]["effective_function2_signature"]


def test_no_source_declared_provenance_or_hypothesis_phase_remains(monkeypatch, tmp_path):
    false = _run_layout(monkeypatch, tmp_path, _FALSE_SOURCE)

    for provenance in false["return_type_provenance"]:
        assert not [key for key in provenance if "source_declared" in str(key)]
    for hypotheses in (
        false["function1_signature_hypotheses"],
        false["function2_signature_hypotheses"],
    ):
        assert not [h for h in hypotheses if h.get("phase") == "P0_SOURCE_DECLARATION"]
    assert false["return_types"] == ("long", "long")


def test_check_from_binaries_public_contract_has_no_source_declaration_inputs():
    parameters = inspect.signature(EquivalenceChecker.check_from_binaries).parameters

    assert "declared_return_type1" not in parameters
    assert "declared_return_type2" not in parameters


# ---------------------------------------------------------------------------
# opt-in real-binary regression (plan section 3.6)
# ---------------------------------------------------------------------------


class _RealBinaryChecker(EquivalenceChecker):
    """実 PyGhidra 経路用。authority cutover だけ切り、判定本体は本物を使う。"""

    last_observation = None

    def __init__(self, *args, **kwargs):
        kwargs["canonical_decision_cutover"] = False
        super().__init__(*args, **kwargs)

    def check(self, analysis1, analysis2, *args, **kwargs):
        result = super().check(analysis1, analysis2, *args, **kwargs)
        type(self).last_observation = {
            "return_type_provenance": (
                dict(analysis1.return_type_provenance or {}),
                dict(analysis2.return_type_provenance or {}),
            ),
            "surface_kinds": (
                analysis1.get_comparison_surface().kind,
                analysis2.get_comparison_surface().kind,
            ),
            "is_equivalent": result.is_equivalent,
            "function1_signature_hypotheses": list(result.function1_signature_hypotheses),
            "function2_signature_hypotheses": list(result.function2_signature_hypotheses),
        }
        return result


@pytest.mark.skipif(
    os.environ.get("RUN_PYGHIDRA_REGRESSIONS") != "1",
    reason="real PyGhidra regression is opt-in; set RUN_PYGHIDRA_REGRESSIONS=1",
)
def test_real_binary_semantic_result_ignores_adjacent_c_layouts(monkeypatch, tmp_path):
    """同一 ELF 対を 3 レイアウトで判定し、判定面が変わらないことを確認する。

    runner の supervisor / execution-identity harness の外では v2 authority の
    ``final_outcome`` が設計上 ERROR 固定なので（CLAUDE.md）、比較対象は authority
    より手前の ``EquivalenceResult`` と解析 provenance に限る。
    """
    pytest.importorskip("pyghidra")
    compiler = shutil.which("cc") or shutil.which("gcc")
    if compiler is None:
        pytest.skip("no C compiler available")

    fixture = Path(__file__).resolve().parents[1] / "fixtures" / "phase7_sat_left.c"
    if not fixture.is_file():
        pytest.skip(f"fixture source not found: {fixture}")

    object_file = tmp_path / "phase7_sat_left.o"
    compiled = subprocess.run(
        [compiler, "-c", "-O0", str(fixture), "-o", str(object_file)],
        capture_output=True,
    )
    if compiled.returncode != 0:
        pytest.skip(f"fixture compilation failed: {compiled.stderr.decode(errors='ignore')}")

    monkeypatch.setattr(checker_layer, "EquivalenceChecker", _RealBinaryChecker)

    def run(layout_name, source_text):
        directory = tmp_path / layout_name
        directory.mkdir()
        for name in ("newV-a", "newV-b"):
            shutil.copyfile(object_file, directory / name)
        if source_text is not None:
            (directory / "newV.c").write_text(source_text, encoding="utf-8")
        args = build_parser().parse_args([
            "--equiv", str(directory / "newV-a"), str(directory / "newV-b"),
            "-f", "phase7_sat_witness",
            "--binary-ids", "A", "B",
            "--quiet",
        ])
        _RealBinaryChecker.last_observation = None
        with pytest.raises(SystemExit):
            equivalence_cli.run_equivalence_check(args)
        observation = _RealBinaryChecker.last_observation
        assert observation is not None, "checker.check() was never reached"
        return observation

    absent = run("real-absent", None)
    correct = run("real-correct", "int phase7_sat_witness(void) { return 7; }\n")
    false = run("real-false", "void phase7_sat_witness(void) { }\n")

    assert absent == correct == false
    # Ghidra が非 void を復元している前提を固定する。偽 `.c` の `void` 宣言が
    # 比較面を effect-only に落としていれば、ここで気付ける。
    assert absent["surface_kinds"] == ("return_value", "return_value")
    for provenance in absent["return_type_provenance"]:
        assert not [key for key in provenance if "source_declared" in str(key)]
        assert provenance.get("declared_return_type_width")
