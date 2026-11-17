# -*- coding: utf-8 -*-
"""The concrete layer and its executor take nothing but the binary and the ABI tables.

Source code, expected verdicts (the EqBench Eq/Neq labels, the ground-truth
table), and the evaluation oracles (qemu, UBSan) are for evaluation only.
This test pins that no module of ``concrete/`` and no concrete executor
module of ``ghidra/`` imports anything that could carry them, and that none
of them names them.
"""
import ast
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[2]
MODULES = sorted(PACKAGE.glob("concrete/*.py")) + sorted(PACKAGE.glob("ghidra/concrete_*.py"))

ALLOWED_PROJECT = (
    "scripts.function_tracer_pcode.core",
    "scripts.function_tracer_pcode.concrete",
    "scripts.function_tracer_pcode.config",
    "scripts.function_tracer_pcode.ghidra.pyghidra_support",
    "scripts.function_tracer_pcode.ghidra.concrete_executor",
)
ALLOWED_EXTERNAL = {
    "__future__", "dataclasses", "enum", "typing", "json", "os", "signal", "subprocess", "sys",
    "time", "tempfile", "pathlib", "xml", "jpype",
    # exact arithmetic for the IEEE 754 model and the ELF section table
    "fractions", "math", "struct",
}
FORBIDDEN_TEXT = ("qemu", "ubsan", "ground_truth", "eqbench", "newv", "/eq/", "/neq/", "expected_verdict")


def _imports(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                yield alias.name
        elif isinstance(node, ast.ImportFrom):
            yield node.module or ""


def test_the_modules_exist():
    names = {p.name for p in MODULES}
    assert {
        "run_observer.py", "abi_conformance.py", "recording.py", "concrete_executor.py", "concrete_worker.py",
        "value_monitor.py", "ieee.py", "userops.py", "elf_sections.py",
    } <= names


def test_only_the_binary_boundary_and_the_abi_tables_are_imported():
    for path in MODULES:
        for module in _imports(path):
            if module.startswith("scripts."):
                assert module.startswith(ALLOWED_PROJECT), (path.name, module)
            else:
                assert module.split(".")[0] in ALLOWED_EXTERNAL, (path.name, module)


def test_no_module_names_sources_labels_or_oracles():
    for path in MODULES:
        text = path.read_text().lower()
        for word in FORBIDDEN_TEXT:
            assert word not in text, (path.name, word)
