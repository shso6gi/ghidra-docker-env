# -*- coding: utf-8 -*-
"""Regression tests for source-adjacent declaration evidence."""

from pathlib import Path

from scripts.function_tracer_pcode.equivalence.reanalysis import (
    _apply_declared_return_type_hypothesis,
)
from scripts.function_tracer_pcode.equivalence.source_declarations import (
    extract_c_return_type,
    infer_adjacent_c_return_type,
)
from scripts.function_tracer_pcode.model import Expression, ReturnInfo

from conftest import create_mock_analysis


class _Checker:
    debug = False
    type_fixer_config = None

    @staticmethod
    def _debug_print(_msg):
        return None


def test_extract_c_return_type_finds_void_definition_without_matching_calls():
    source = """
    double sqrt(double x);

    void sphbes(int n, double x) {
        sqrt(x);
    }

    int caller(void) {
        sphbes(1, 2.0);
        return 0;
    }
    """

    assert extract_c_return_type(source, "sphbes") == "void"
    assert extract_c_return_type(source, "sqrt") == "double"


def test_infer_adjacent_c_return_type_uses_newv_source_next_to_binary(tmp_path):
    binary = tmp_path / "newV-arm64-clang-O3"
    binary.write_bytes(b"not a real binary")
    (tmp_path / "newV.c").write_text("void sphbes(int n, double x) {}\n", encoding="utf-8")

    assert infer_adjacent_c_return_type(binary, "sphbes") == "void"


def test_infer_adjacent_c_return_type_rejects_unrelated_single_c_file(tmp_path):
    binary = tmp_path / "actual-binary-no-source"
    binary.write_bytes(b"not a real binary")
    (tmp_path / "unrelated.c").write_text("void target(void) {}\n", encoding="utf-8")

    assert infer_adjacent_c_return_type(binary, "target") is None


def test_declared_void_overlay_normalizes_artifact_return_values(mock_program_x86):
    analysis = create_mock_analysis(
        function_name="sphbes",
        return_type="ulong",
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression.parameter("param_2", index=1, size=8),
            ),
            ReturnInfo(
                address="0x00401010",
                conditions=[],
                value=Expression.unknown("puts@0x401010"),
            ),
        ],
    )

    updated = _apply_declared_return_type_hypothesis(
        checker=_Checker(),
        analysis=analysis,
        program=mock_program_x86,
        binary_name="newV-arm64-clang-O3",
        declared_return_type="void",
    )

    assert updated.return_type == "void"
    assert updated.signature_hypotheses
    assert all(getattr(ret.value.expr_type, "name", None) == "UNKNOWN" for ret in updated.returns)
    assert all(getattr(ret.value, "name", None) == "void" for ret in updated.returns)


def test_declared_nonvoid_overlay_is_not_applied(mock_program_x86):
    analysis = create_mock_analysis(
        function_name="sphbes",
        return_type="ulong",
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression.parameter("param_2", index=1, size=8),
            ),
        ],
    )

    updated = _apply_declared_return_type_hypothesis(
        checker=_Checker(),
        analysis=analysis,
        program=mock_program_x86,
        binary_name="newV-arm64-clang-O3",
        declared_return_type="int",
    )

    assert updated is analysis
    assert not updated.signature_hypotheses
