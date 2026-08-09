from __future__ import annotations

import sys
from pathlib import Path

import pytest


EQBENCH_SCRIPTS = Path(__file__).resolve().parents[3] / "eqbench"
if str(EQBENCH_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(EQBENCH_SCRIPTS))

from select_neq_functions import select_functions  # noqa: E402


def test_selection_keeps_changed_function_and_recursive_callers(tmp_path):
    old_source = tmp_path / "oldV.c"
    new_source = tmp_path / "newV.c"
    old_source.write_text(
        """
int unchanged(int x) { return x; }
int string_only(int x) { const char *s = "callee("; return x + (s != 0); }
int callee(int x) { return x + 1; }
int caller(int x) { return callee(x); }
""",
        encoding="utf-8",
    )
    new_source.write_text(
        """
int unchanged(int x) { return x; }
int string_only(int x) { const char *s = "callee("; return x + (s != 0); }
int callee(int x) { return x + 2; } // benchmark change
int caller(int x) { return callee(x); }
""",
        encoding="utf-8",
    )

    all_names, changed, caller_closure, selected = select_functions(
        new_source, old_source
    )

    assert all_names == ["unchanged", "string_only", "callee", "caller"]
    assert changed == ["callee"]
    assert caller_closure == ["caller"]
    assert selected == ["callee", "caller"]


def test_selection_finds_nested_changed_function_before_entry_caller():
    root = Path("targets/EqBench/benchmarks/REVE/triangularMod/Neq")

    all_names, changed, caller_closure, selected = select_functions(
        root / "newV.c", root / "oldV.c"
    )

    assert all_names == ["tr", "f"]
    assert changed == ["tr"]
    assert caller_closure == ["f"]
    assert selected == ["tr", "f"]


def test_selection_rejects_function_census_mismatch(tmp_path):
    old_source = tmp_path / "oldV.c"
    new_source = tmp_path / "newV.c"
    old_source.write_text("int old_name(int x) { return x; }\n", encoding="utf-8")
    new_source.write_text("int new_name(int x) { return x + 1; }\n", encoding="utf-8")

    with pytest.raises(ValueError, match="function census differs"):
        select_functions(new_source, old_source)
