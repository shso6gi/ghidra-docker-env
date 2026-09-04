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


# REVE/triangularMod/Neq from EqBench, inlined so the test does not depend on
# the git-ignored benchmark checkout (oldV drops the loop increment).
_TRIANGULAR_NEW = """
int tr(int n) {
    int result;
    int i;
    i = 0;
    result = 0;
    while (i < n) {
        result = result + i;
        i = i +1;
    }
    return result;
}
int f(int m) {
    int result;
    if (m > 0) {
        result = tr(m - 1);
        result = result + m;
    } else {
        result = 0;
    }
    return result;
}
"""
_TRIANGULAR_OLD = _TRIANGULAR_NEW.replace("        i = i +1;\n", "")


def test_selection_finds_nested_changed_function_before_entry_caller(tmp_path):
    new_source = tmp_path / "newV.c"
    old_source = tmp_path / "oldV.c"
    new_source.write_text(_TRIANGULAR_NEW, encoding="utf-8")
    old_source.write_text(_TRIANGULAR_OLD, encoding="utf-8")
    assert _TRIANGULAR_OLD != _TRIANGULAR_NEW

    all_names, changed, caller_closure, selected = select_functions(
        new_source, old_source
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
