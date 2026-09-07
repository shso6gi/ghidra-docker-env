"""scripts/eqbench/function_diff_manifest.py (Issue #104, runner benchmark gate oracle)."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest


EQBENCH_SCRIPTS = Path(__file__).resolve().parents[3] / "eqbench"
if str(EQBENCH_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(EQBENCH_SCRIPTS))

import function_diff_manifest as fdm  # noqa: E402
from select_neq_functions import select_functions  # noqa: E402


def _write(path: Path, text: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def _neq_pair(root: Path, program: str, old: str, new: str, *, base: str = "newV", c_desc=None) -> Path:
    neq_dir = root / program / "Neq"
    old_name = "oldV" if base == "newV" else "old"
    _write(neq_dir / f"{old_name}.c", old)
    _write(neq_dir / f"{base}.c", new)
    if c_desc is not None:
        _write(neq_dir / "C-Desc.json", json.dumps(c_desc))
    return neq_dir


OLD = """
int g = 1;
static int helper(int x) { return x + g; }
int changed(int x) { return x * 2; }
int caller(int x) { return changed(x) + 1; }
int caller2(int x) { return caller(x); }
int untouched(int x) { /* comment */ return x; }
int main(void) { return changed(1); }
"""
NEW = """
int g = 1;
static int helper(int x) { return x + g; }
int changed(int x) { return x * 3; }
int caller(int x) { return changed(x) + 1; }
int caller2(int x) { return caller(x); }
int untouched(int x) {
    return x;   // whitespace / comment only
}
int main(void) { return changed(2); }
"""


def test_neq_classification_direct_callers_and_identical(tmp_path):
    _neq_pair(tmp_path, "fam/prog", OLD, NEW, c_desc={"function name": "changed"})
    manifest = fdm.build_manifest(tmp_path)
    sample = manifest["samples"]["fam/prog/Neq/newV-oldV"]
    assert sample["lane"] == "Neq"
    assert sample["parse_status"] == "ok"
    functions = sample["functions"]
    assert functions["changed"]["source_relation"] == fdm.RELATION_CHANGED
    assert functions["changed"]["source_impact"] == fdm.IMPACT_DIRECT
    assert functions["caller"]["source_relation"] == fdm.RELATION_IDENTICAL
    assert functions["caller"]["source_impact"] == fdm.IMPACT_CALLS
    assert functions["caller2"]["source_impact"] == fdm.IMPACT_CALLS  # transitive
    assert functions["untouched"]["source_relation"] == fdm.RELATION_IDENTICAL
    assert functions["untouched"]["source_impact"] == fdm.IMPACT_NONE
    assert functions["helper"]["source_impact"] == fdm.IMPACT_NONE
    # main() is driver code, not file-scope context: its change must not leak.
    assert sample["top_level_context_changed"] is False
    assert sample["changed_context_identifiers"] == []
    # A source change never becomes a semantic verdict.
    assert {entry["semantic_ground_truth"] for entry in functions.values()} == {fdm.TRUTH_UNKNOWN}
    assert sample["c_desc"]["agreement"] == fdm.C_DESC_MATCH_UNIQUE


def test_neq_classification_agrees_with_runner_selection(tmp_path):
    neq_dir = _neq_pair(tmp_path, "fam/prog", OLD, NEW)
    _, changed, closure, _ = select_functions(neq_dir / "newV.c", neq_dir / "oldV.c")
    functions = fdm.build_manifest(tmp_path)["samples"]["fam/prog/Neq/newV-oldV"]["functions"]
    assert sorted(n for n, e in functions.items() if e["source_impact"] == fdm.IMPACT_DIRECT) == sorted(changed)
    assert sorted(n for n, e in functions.items() if e["source_impact"] == fdm.IMPACT_CALLS) == sorted(closure)


def test_changed_global_and_signature_context_are_attributed(tmp_path):
    old = """
#define LIMIT 10
typedef struct { int a; } rec_t;
int table[4] = {1, 2, 3, 4};
int uses_macro(int x) { return x < LIMIT; }
int uses_table(int i) { return table[i]; }
int takes_rec(rec_t r) { return 1; }
int plain(int x) { return x; }
"""
    new = """
#define LIMIT 20
typedef struct { int a; int b; } rec_t;
int table[4] = {1, 2, 3, 5};
int uses_macro(int x) { return x < LIMIT; }
int uses_table(int i) { return table[i]; }
int takes_rec(rec_t r) { return 1; }
int plain(int x) { return x; }
"""
    _neq_pair(tmp_path, "fam/ctx", old, new)
    sample = fdm.build_manifest(tmp_path)["samples"]["fam/ctx/Neq/newV-oldV"]
    assert sample["top_level_context_changed"] is True
    assert {"LIMIT", "table", "rec_t"} <= set(sample["changed_context_identifiers"])
    functions = sample["functions"]
    assert functions["uses_macro"]["source_impact"] == fdm.IMPACT_GLOBAL
    assert functions["uses_table"]["source_impact"] == fdm.IMPACT_GLOBAL
    assert functions["takes_rec"]["source_impact"] == fdm.IMPACT_SIGNATURE
    assert functions["plain"]["source_impact"] == fdm.IMPACT_NONE


def test_unattributable_context_change_marks_impact_unknown(tmp_path):
    old = "#pragma pack(4)\nint f(int x) { return x; }\n"
    new = "#pragma pack(8)\nint f(int x) { return x; }\n"
    _neq_pair(tmp_path, "fam/pragma", old, new)
    sample = fdm.build_manifest(tmp_path)["samples"]["fam/pragma/Neq/newV-oldV"]
    assert sample["top_level_context_changed"] is True
    assert sample["functions"]["f"]["source_impact"] == fdm.IMPACT_UNKNOWN


def test_added_and_removed_functions(tmp_path):
    old = "int gone(int x) { return x; }\nint keep(int x) { return x; }\n"
    new = "int keep(int x) { return x; }\nint fresh(int x) { return x + 1; }\n"
    _neq_pair(tmp_path, "fam/census", old, new)
    functions = fdm.build_manifest(tmp_path)["samples"]["fam/census/Neq/newV-oldV"]["functions"]
    assert functions["gone"]["source_relation"] == fdm.RELATION_REMOVED
    assert functions["fresh"]["source_relation"] == fdm.RELATION_ADDED
    assert functions["gone"]["source_impact"] == fdm.IMPACT_DIRECT
    assert functions["fresh"]["source_impact"] == fdm.IMPACT_DIRECT
    assert functions["keep"]["source_impact"] == fdm.IMPACT_NONE


def test_eq_samples_are_confirmed_eq_by_construction(tmp_path):
    eq_dir = tmp_path / "fam/prog/Eq"
    _write(eq_dir / "newV.c", "int f(int x) { return x; }\nint g(int x) { return f(x); }\n")
    _write(eq_dir / "oldV.c", "int f(int x) { return x; }\n")  # unused by the Eq runner
    manifest = fdm.build_manifest(tmp_path)
    assert list(manifest["samples"]) == ["fam/prog/Eq/newV"]
    functions = manifest["samples"]["fam/prog/Eq/newV"]["functions"]
    assert set(functions) == {"f", "g"}
    for entry in functions.values():
        assert entry["semantic_ground_truth"] == fdm.TRUTH_EQ
        assert entry["ground_truth_evidence"] == fdm.EVIDENCE_EQ_SAME_SOURCE
        assert entry["source_impact"] == fdm.IMPACT_NONE


def test_new_old_naming_variant_and_c_desc_discrepancy(tmp_path):
    old = "int tr(int n) { return n; }\nint f(int m) { return tr(m); }\n"
    new = "int tr(int n) { return n + 1; }\nint f(int m) { return tr(m); }\n"
    _neq_pair(tmp_path, "REVE/triangularMod", old, new, base="new", c_desc={"function name": "f"})
    sample = fdm.build_manifest(tmp_path)["samples"]["REVE/triangularMod/Neq/new-old"]
    assert sample["c_desc"]["agreement"] == fdm.C_DESC_SOURCE_IDENTICAL
    assert sample["c_desc"]["source_changed_functions"] == ["tr"]
    assert sample["functions"]["f"]["source_impact"] == fdm.IMPACT_CALLS
    assert sample["functions"]["f"]["source_relation"] == fdm.RELATION_IDENTICAL


def test_parse_failure_is_recorded_not_raised(tmp_path):
    _neq_pair(tmp_path, "fam/broken", "int f(int x) { return x; }\n", "/* no function */\n")
    sample = fdm.build_manifest(tmp_path)["samples"]["fam/broken/Neq/newV-oldV"]
    assert sample["parse_status"] == "failed"
    assert "no non-main function definitions" in sample["parse_error"]
    assert sample["functions"] == {}


def test_ground_truth_annotations_apply_and_validate(tmp_path):
    _neq_pair(tmp_path, "fam/prog", OLD, NEW)
    truth = _write(
        tmp_path / "truth.tsv",
        "# comment\nsample\tfunction\tverdict\tevidence\n"
        "fam/prog/Neq/newV-oldV\tchanged\tCONFIRMED_NOT_EQ\tcounter-example x=1\n"
        "fam/prog/Neq/newV-oldV\tuntouched\tCONFIRMED_EQ\tidentical body\n",
    )
    manifest = fdm.build_manifest(tmp_path, ground_truth=truth)
    functions = manifest["samples"]["fam/prog/Neq/newV-oldV"]["functions"]
    assert functions["changed"]["semantic_ground_truth"] == fdm.TRUTH_NOT_EQ
    assert functions["changed"]["ground_truth_evidence"] == "counter-example x=1"
    assert functions["untouched"]["semantic_ground_truth"] == fdm.TRUTH_EQ
    assert functions["caller"]["semantic_ground_truth"] == fdm.TRUTH_UNKNOWN
    assert manifest["ground_truth"]["entries"] == 2
    assert manifest["ground_truth"]["unresolved_annotations"] == []

    bad = _write(tmp_path / "bad.tsv", "fam/prog/Neq/newV-oldV\tchanged\tSOURCE_CHANGED\tx\n")
    with pytest.raises(ValueError, match="verdict must be"):
        fdm.load_ground_truth(bad)
    dup = _write(
        tmp_path / "dup.tsv",
        "a\tf\tCONFIRMED_EQ\tx\na\tf\tCONFIRMED_NOT_EQ\ty\n",
    )
    with pytest.raises(ValueError, match="duplicate"):
        fdm.load_ground_truth(dup)


def test_stale_annotation_fails_closed_unless_explicitly_allowed(tmp_path):
    _neq_pair(tmp_path, "fam/prog", OLD, NEW)
    truth = _write(
        tmp_path / "truth.tsv",
        "fam/prog/Neq/newV-oldV\tchanged\tCONFIRMED_NOT_EQ\tcex\n"
        "fam/prog/Neq/newV-oldV\tchagned\tCONFIRMED_NOT_EQ\ttypo in function name\n"
        "fam/other/Neq/newV-oldV\tnope\tCONFIRMED_NOT_EQ\tstale sample\n",
    )
    with pytest.raises(ValueError, match="do not resolve") as excinfo:
        fdm.build_manifest(tmp_path, ground_truth=truth)
    assert "chagned" in str(excinfo.value) and "nope" in str(excinfo.value)
    manifest = fdm.build_manifest(tmp_path, ground_truth=truth, allow_unresolved=True)
    assert manifest["ground_truth"]["unresolved_annotations"] == [
        "fam/other/Neq/newV-oldV\tnope",
        "fam/prog/Neq/newV-oldV\tchagned",
    ]
    assert manifest["samples"]["fam/prog/Neq/newV-oldV"]["functions"]["changed"]["semantic_ground_truth"] == fdm.TRUTH_NOT_EQ

    output = tmp_path / "m.json"
    base = [sys.executable, "-B", str(EQBENCH_SCRIPTS / "function_diff_manifest.py"),
            "--benchmark-root", str(tmp_path), "--output", str(output), "--ground-truth", str(truth)]
    failed = subprocess.run(base, check=False, text=True, capture_output=True)
    assert failed.returncode == 2 and "do not resolve" in failed.stderr
    assert not output.exists()
    allowed = subprocess.run(base + ["--allow-unresolved-annotations"], check=False, text=True, capture_output=True)
    assert allowed.returncode == 0, allowed.stderr
    assert "unresolved=2" in allowed.stdout


def test_changed_include_is_unattributable(tmp_path):
    old = '#include "config_a.h"\nint f(int x) { return x; }\nint g(int x) { return 2; }\n'
    new = '#include "config_b.h"\nint f(int x) { return x; }\nint g(int x) { return 2; }\n'
    _neq_pair(tmp_path, "fam/inc", old, new)
    sample = fdm.build_manifest(tmp_path)["samples"]["fam/inc/Neq/newV-oldV"]
    assert sample["top_level_context_changed"] is True
    assert sample["functions"]["f"]["source_impact"] == fdm.IMPACT_UNKNOWN
    assert sample["functions"]["g"]["source_impact"] == fdm.IMPACT_UNKNOWN


def test_tracked_default_ground_truth_file_is_loadable():
    path = fdm.DEFAULT_GROUND_TRUTH_FILE
    assert path.is_file()
    annotations = fdm.load_ground_truth(path)
    assert annotations, "the tracked file must carry the reviewed initial ground truth"
    for annotation in annotations:
        assert annotation.verdict in (fdm.TRUTH_EQ, fdm.TRUTH_NOT_EQ)
        assert "/Neq/" in annotation.sample
        assert len(annotation.evidence) > 40  # input, outputs and argument, not a bare label


def test_cli_writes_manifest_and_summary(tmp_path):
    _neq_pair(tmp_path / "bench", "fam/prog", OLD, NEW)
    output = tmp_path / "out" / "function_diff_manifest.json"
    result = subprocess.run(
        [sys.executable, "-B", str(EQBENCH_SCRIPTS / "function_diff_manifest.py"),
         "--benchmark-root", str(tmp_path / "bench"), "--output", str(output), "--no-ground-truth"],
        check=False, text=True, capture_output=True,
    )
    assert result.returncode == 0, result.stderr
    assert "function diff manifest: 1 samples" in result.stdout
    payload = json.loads(output.read_text())
    assert payload["schema"] == fdm.MANIFEST_SCHEMA
    assert payload["summary"]["by_lane"]["Neq"]["source_impact:DIRECTLY_CHANGED"] == 1
    missing = subprocess.run(
        [sys.executable, "-B", str(EQBENCH_SCRIPTS / "function_diff_manifest.py"),
         "--benchmark-root", str(tmp_path / "nope"), "--output", str(output)],
        check=False, text=True, capture_output=True,
    )
    assert missing.returncode == 2
