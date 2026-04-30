# -*- coding: utf-8 -*-
"""PyGhidra-backed recurrence-summary regression fixtures."""

from contextlib import contextmanager
from pathlib import Path
import shutil
import subprocess
import tempfile

import pytest

from scripts.function_tracer_pcode.analysis import PcodeTracer
from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.recurrence_summary import StructuralRecurrenceSummarizer
from scripts.function_tracer_pcode.cli._pyghidra_support import load_pyghidra, start_headless_pyghidra
from scripts.function_tracer_pcode.config import apply_runtime_environment
from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker


_REPRO_SOURCE = (
    Path(__file__).resolve().parents[4]
    / "targets"
    / "cate1"
    / "zext_or_repro"
    / "zext_or_repro.c"
)
_FUNCTION_NAME = "zext_or_repro_tail_index_probe"
_HIGH_BIT_DELTA = 1 << 40
_LOOP_METHOD_B_ARM64_GCC_O3 = (
    Path(__file__).resolve().parents[4]
    / "targets"
    / "cate1"
    / "loop_method_b_test"
    / "loop_method_b_test-arm64-gcc-O3"
)
_LOOP_METHOD_B_ARM64_CLANG_O1 = (
    Path(__file__).resolve().parents[4]
    / "targets"
    / "cate1"
    / "loop_method_b_test"
    / "loop_method_b_test-arm64-clang-O1"
)
_LOOP_METHOD_B_ARM64_CLANG_O2 = (
    Path(__file__).resolve().parents[4]
    / "targets"
    / "cate1"
    / "loop_method_b_test"
    / "loop_method_b_test-arm64-clang-O2"
)
_LOOP_METHOD_B_ARM64_CLANG_O3 = (
    Path(__file__).resolve().parents[4]
    / "targets"
    / "cate1"
    / "loop_method_b_test"
    / "loop_method_b_test-arm64-clang-O3"
)
_LOOP_METHOD_B_MIPS64_CLANG_O1 = (
    Path(__file__).resolve().parents[4]
    / "targets"
    / "cate1"
    / "loop_method_b_test"
    / "loop_method_b_test-mips64-clang-O1"
)
_LOOP_METHOD_B_MIPS64_CLANG_O2 = (
    Path(__file__).resolve().parents[4]
    / "targets"
    / "cate1"
    / "loop_method_b_test"
    / "loop_method_b_test-mips64-clang-O2"
)
_LOOP_METHOD_B_MIPS64_GCC_O1 = (
    Path(__file__).resolve().parents[4]
    / "targets"
    / "cate1"
    / "loop_method_b_test"
    / "loop_method_b_test-mips64-gcc-O1"
)
_LOOP_METHOD_B_FUNCTION = "lmb_sum_prefix_peeled3_tail"


@pytest.fixture(scope="session")
def _zext_or_repro_binary(tmp_path_factory):
    source = _REPRO_SOURCE
    if not source.is_file():
        pytest.skip(f"repro source file not found: {source}")

    binary = tmp_path_factory.mktemp("zext_or_repro") / "zext_or_repro.bin"
    compiler = shutil.which("gcc")
    if compiler is None:
        pytest.skip("gcc is required to build zext_or_repro fixture binary")

    compile_result = subprocess.run(
        [compiler, str(source), "-O0", "-o", str(binary)],
        capture_output=True,
        text=True,
    )
    if compile_result.returncode != 0:
        pytest.skip(
            "failed to compile zext_or_repro fixture:\n"
            f"{compile_result.stdout}\n{compile_result.stderr}"
        )

    return binary


@pytest.fixture(scope="session")
def _running_pyghidra():
    pytest.importorskip("pyghidra")
    runtime = apply_runtime_environment()
    pyghidra = load_pyghidra()
    try:
        start_headless_pyghidra(
            pyghidra,
            install_dir=Path(runtime.ghidra_install_dir) if runtime.ghidra_install_dir else None,
        )
    except Exception as exc:  # pragma: no cover - environment-dependent startup failure
        pytest.skip(f"PyGhidra startup failed: {exc}")
    return pyghidra


@contextmanager
def _load_program(pyghidra, binary_path: Path):
    with tempfile.TemporaryDirectory() as temp_dir:
        with pyghidra.open_project(temp_dir, "repro-zext-or", create=True) as project:
            loader = pyghidra.program_loader().project(project).source(str(binary_path))
            with loader.load() as loaded:
                yield loaded.getPrimaryDomainObject()


def _find_function_by_name(program, function_name: str):
    function_manager = program.getFunctionManager()
    for function in function_manager.getFunctions(True):
        if function.getName() == function_name:
            return function
    return None


def test_zext_or_high_bit_or_delta_is_rejected_with_real_pcode(_running_pyghidra, _zext_or_repro_binary):
    pyghidra = _running_pyghidra
    with _load_program(pyghidra, _zext_or_repro_binary) as program:
        function = _find_function_by_name(program, _FUNCTION_NAME)
        if function is None:
            pytest.fail(f"missing function {_FUNCTION_NAME} in repro binary")

        from ghidra.app.decompiler import DecompInterface  # type: ignore[import]

        decompiler = DecompInterface()
        try:
            decompiler.openProgram(program)
            decompile_results = decompiler.decompileFunction(function, 60, None)
            if not decompile_results.decompileCompleted():
                pytest.fail("decompilation did not complete for repro function")
            high_function = decompile_results.getHighFunction()
        finally:
            decompiler.closeProgram()

        if high_function is None:
            pytest.fail("high function is None for repro function")

        tracer = PcodeTracer(program, high_function, debug=False)
        summarizer = StructuralRecurrenceSummarizer(tracer, debug=False)

        found_counter = None
        for op in tracer.get_all_pcode_ops():
            if op.getMnemonic() != "INT_OR":
                continue
            if int(op.getNumInputs() or 0) < 2:
                continue

            left = summarizer._follow_passthrough_varnode(op.getInput(0))
            right = summarizer._follow_passthrough_varnode(op.getInput(1))
            left_const = summarizer._varnode_unsigned_constant_value(left)
            right_const = summarizer._varnode_unsigned_constant_value(right)

            if left_const == _HIGH_BIT_DELTA and right_const is None:
                candidate = right
            elif right_const == _HIGH_BIT_DELTA and left_const is None:
                candidate = left
            else:
                continue

            candidate_def = candidate.getDef()
            if candidate_def is None or candidate_def.getMnemonic() != "INT_AND":
                continue
            found_counter = candidate
            break

        if found_counter is None:
            pytest.fail("failed to locate INT_OR( INT_AND( INT_ZEXT(count32) ... ), (1<<40) ) pattern")

        assert summarizer._counter_low_bits_clear_for_or_delta(found_counter, _HIGH_BIT_DELTA) is False
        assert summarizer._counter_low_bits_clear_for_or_delta(found_counter, 1) is True


def test_loop_method_b_vectorized_prefix_sum_recovers_object_proof(_running_pyghidra):
    pyghidra = _running_pyghidra
    binary_path = _LOOP_METHOD_B_ARM64_GCC_O3
    if not binary_path.is_file():
        pytest.skip(f"loop_method_b binary not found: {binary_path}")

    with _load_program(pyghidra, binary_path) as program:
        pyghidra.analyze(program)
        analyzer = ReturnAnalyzer(program, debug=False)
        result = analyzer.analyze_function_by_name(_LOOP_METHOD_B_FUNCTION, timeout=60)
        if result is None:
            pytest.fail("analysis did not produce a result for loop_method_b regression")

        readonly_returns = [
            ret for ret in result.returns
            if getattr(
                getattr(getattr(ret, "value", None), "runtime_ref", None),
                "accumulator_proof",
                None,
            )
            is not None
        ]
        if not readonly_returns:
            pytest.fail("missing readonly reduction summary for loop_method_b regression")

        proof = readonly_returns[0].value.runtime_ref.accumulator_proof
        assert proof is not None
        assert proof.start_offset == 12
        assert proof.start_index == 3
        assert proof.seed_term_count is None
        assert tuple(term.byte_offset for term in proof.seed_terms) == (0, 4, 8)
        assert tuple(proof.lane_terms) == ((0, 4), (4, 4), (8, 4), (12, 4))
        assert tuple(term.byte_offset for term in (proof.full_terms_for_count_value(4) or ())) == (0, 4, 8, 12)


@pytest.mark.parametrize(
    ("left_binary", "right_binary"),
    [
        (_LOOP_METHOD_B_ARM64_CLANG_O1, _LOOP_METHOD_B_ARM64_CLANG_O2),
        (_LOOP_METHOD_B_ARM64_CLANG_O2, _LOOP_METHOD_B_ARM64_GCC_O3),
        (_LOOP_METHOD_B_ARM64_CLANG_O3, _LOOP_METHOD_B_ARM64_GCC_O3),
        (_LOOP_METHOD_B_MIPS64_GCC_O1, _LOOP_METHOD_B_ARM64_CLANG_O2),
        (_LOOP_METHOD_B_MIPS64_GCC_O1, _LOOP_METHOD_B_ARM64_CLANG_O3),
        (_LOOP_METHOD_B_MIPS64_GCC_O1, _LOOP_METHOD_B_ARM64_GCC_O3),
        (_LOOP_METHOD_B_MIPS64_CLANG_O1, _LOOP_METHOD_B_MIPS64_CLANG_O2),
        (_LOOP_METHOD_B_MIPS64_CLANG_O1, _LOOP_METHOD_B_ARM64_CLANG_O1),
    ],
    ids=[
        "arm64-clang-O1_vs_O2",
        "arm64-clang-O2_vs_arm64-gcc-O3",
        "arm64-clang-O3_vs_arm64-gcc-O3",
        "mips64-gcc-O1_vs_arm64-clang-O2",
        "mips64-gcc-O1_vs_arm64-clang-O3",
        "mips64-gcc-O1_vs_arm64-gcc-O3",
        "mips64-clang-O1_vs_O2",
        "mips64-clang-O1_vs_arm64-clang-O1",
    ],
)
def test_loop_method_b_tail_pairs_are_equivalent_end_to_end(
    _running_pyghidra,
    left_binary: Path,
    right_binary: Path,
):
    pyghidra = _running_pyghidra
    if not left_binary.is_file():
        pytest.skip(f"loop_method_b binary not found: {left_binary}")
    if not right_binary.is_file():
        pytest.skip(f"loop_method_b binary not found: {right_binary}")

    with tempfile.TemporaryDirectory() as temp_dir:
        with pyghidra.open_project(temp_dir, "loop-method-b-equiv", create=True) as project:
            left_loader = pyghidra.program_loader().project(project).source(str(left_binary))
            with left_loader.load() as left_loaded:
                left_program = left_loaded.getPrimaryDomainObject()
                pyghidra.analyze(left_program)

                right_loader = pyghidra.program_loader().project(project).source(str(right_binary))
                with right_loader.load() as right_loaded:
                    right_program = right_loaded.getPrimaryDomainObject()
                    pyghidra.analyze(right_program)

                    checker = EquivalenceChecker(
                        debug=False,
                        strategy="pairwise",
                        timeout=10,
                        pairwise_timeout=5,
                        pairwise_timeout_hard=30,
                    )
                    result = checker.check_from_binaries(
                        left_program,
                        right_program,
                        _LOOP_METHOD_B_FUNCTION,
                        _LOOP_METHOD_B_FUNCTION,
                        decompile_timeout=60,
                        retry_with_type_fix=True,
                    )

                    assert result.is_equivalent is True
