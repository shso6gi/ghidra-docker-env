"""Import-layer guardrail (refactoring Phase 3).

The package is layered (CLAUDE.md, "Architecture"): imports must point
downward only.  A number of upward edges exist today and are tracked as
tech debt; they are listed explicitly below as the baseline.  This test
fails when

* a module imports a *higher* layer and that (module, layer) pair is not in
  the baseline  -> a new upward dependency was introduced, or
* a baseline entry is no longer needed  -> remove it here so the baseline
  only shrinks.

Imports are collected with ``ast`` over every module of the package
(tests excluded), including imports inside functions (lazy imports avoid
runtime cycles but are still layer dependencies).
"""
from __future__ import annotations

import ast
from pathlib import Path

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
PACKAGE_PREFIX = "scripts.function_tracer_pcode."

# Bottom -> top.  Same-layer and downward imports are always allowed.
LAYERS = (
    "core", "smt", "config", "ghidra", "analysis", "semantics",
    "proof", "authority", "checker", "reporting", "cli",
)
RANK = {layer: index for index, layer in enumerate(LAYERS)}

# Existing upward dependencies: (importing module, imported layer).
# Every entry is tech debt.  Do not add entries to make a new import pass;
# move the code to the layer that owns it instead.
UPWARD_BASELINE = frozenset({
    # core -> analysis
    ("core.analysis", "analysis"),
    # ghidra -> authority
    ("ghidra.decompilation_broker", "authority"),
    # ghidra -> cli
    ("ghidra.ghidra_runtime", "cli"),
    ("ghidra.pyghidra_runtime", "cli"),
    # analysis -> semantics
    ("analysis.condition.tracker", "semantics"),
    ("analysis.effects.store_effect", "semantics"),
    ("analysis.recurrence._shared", "semantics"),
    ("analysis.returns.call_recovery", "semantics"),
    ("analysis.returns.control_recovery", "semantics"),
    ("analysis.returns.return_extraction", "semantics"),
    # analysis -> proof
    ("analysis.recurrence._shared", "proof"),
    # analysis -> authority
    ("analysis.returns.analyze_function", "authority"),
    # proof -> authority
    ("proof.call_effect.preflight", "authority"),
    ("proof.call_effect.producer", "authority"),
    ("proof.obligations.outcome_partition", "authority"),
    ("proof.obligations.pair_disposition", "authority"),
    ("proof.obligations.stage_runner", "authority"),
    ("proof.recurrence_promotion", "authority"),
    ("proof.return_width.pipeline", "authority"),
    ("proof.return_width.surface", "authority"),
    ("proof.strategies.monolithic", "authority"),
    ("proof.strategies.pairwise_query_executor", "authority"),
    ("proof.strategies.pairwise_services.auxiliary_smt", "authority"),
    ("proof.strategies.pairwise_services.loop_summary", "authority"),
    ("proof.strategies.pairwise_services.method_b_closure", "authority"),
    ("proof.strategies.pairwise_services.orchestration", "authority"),
    ("proof.strategies.proof_gates.call_effect", "authority"),
    ("proof.strategies.proof_gates.recovery", "authority"),
    ("proof.strategies.proof_gates.return_coverage", "authority"),
    ("proof.strategies.proof_gates.sat_safety", "authority"),
    # proof -> checker
    ("proof.call_effect.preflight", "checker"),
    ("proof.obligations.decision", "checker"),
    ("proof.obligations.model", "checker"),
    ("proof.obligations.outcome_partition", "checker"),
    ("proof.obligations.recurrence", "checker"),
    ("proof.obligations.return_width", "checker"),
    ("proof.obligations.runtime", "checker"),
    ("proof.obligations.stage_runner", "checker"),
    ("proof.strategies.monolithic", "checker"),
    ("proof.strategies.pairwise_query_executor", "checker"),
    ("proof.strategies.pairwise_services._shared", "checker"),
    ("proof.strategies.pairwise_services.orchestration", "checker"),
    ("proof.strategies.proof_gates._shared", "checker"),
    ("proof.strategies.proof_gates.call_effect", "checker"),
    # proof -> reporting
    ("proof.obligations.shadow", "reporting"),
    # authority -> checker
    ("authority.codecs", "checker"),
    ("authority.decision.production_cutover", "checker"),
    ("authority.domains.return_outcome", "checker"),
    ("authority.lifecycle.pilot", "checker"),
    ("authority.lifecycle.production_boundary", "checker"),
})


def _module_name(path: Path, root: Path = PACKAGE_ROOT) -> str:
    rel = path.relative_to(root).with_suffix("").as_posix().replace("/", ".")
    return rel[: -len(".__init__")] if rel.endswith(".__init__") else rel


def _imported_package_modules(tree: ast.AST):
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            if node.module and node.module.startswith(PACKAGE_PREFIX):
                yield node.module[len(PACKAGE_PREFIX):]
        elif isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name.startswith(PACKAGE_PREFIX):
                    yield alias.name[len(PACKAGE_PREFIX):]


def collect_upward_edges(root: Path = PACKAGE_ROOT) -> set[tuple[str, str]]:
    edges: set[tuple[str, str]] = set()
    for path in sorted(root.rglob("*.py")):
        module = _module_name(path, root)
        if module.startswith("tests") or module == "__init__":
            continue
        source_layer = module.split(".")[0]
        if source_layer not in RANK:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for target in _imported_package_modules(tree):
            target_layer = target.split(".")[0]
            if target_layer in RANK and RANK[target_layer] > RANK[source_layer]:
                edges.add((module, target_layer))
    return edges


def test_every_package_directory_is_a_known_layer():
    unknown = sorted(
        child.name for child in PACKAGE_ROOT.iterdir()
        if child.is_dir() and not child.name.startswith(("_", ".")) and child.name != "tests"
        and child.name not in RANK
    )
    assert unknown == [], f"directories without a layer assignment: {unknown}"


def test_no_new_upward_layer_dependencies():
    edges = collect_upward_edges()
    new_edges = sorted(edges - UPWARD_BASELINE)
    assert new_edges == [], (
        "new upward layer dependencies (importing module -> higher layer); "
        "move the code to the owning layer instead of extending the baseline: "
        f"{new_edges}"
    )


def test_upward_baseline_has_no_stale_entries():
    edges = collect_upward_edges()
    stale = sorted(UPWARD_BASELINE - edges)
    assert stale == [], f"baseline entries no longer needed, remove them: {stale}"


def test_collector_detects_upward_and_ignores_downward_and_lazy_placement(tmp_path):
    # A miniature package: core imports proof (upward, also inside a function),
    # proof imports core (downward), cli imports nothing upward.
    (tmp_path / "core").mkdir(); (tmp_path / "proof").mkdir(); (tmp_path / "cli").mkdir()
    (tmp_path / "core" / "__init__.py").write_text("")
    (tmp_path / "core" / "thing.py").write_text(
        "def f():\n    from scripts.function_tracer_pcode.proof import x\n"
    )
    (tmp_path / "proof" / "__init__.py").write_text(
        "from scripts.function_tracer_pcode.core import thing\n"
    )
    (tmp_path / "cli" / "__init__.py").write_text("import scripts.function_tracer_pcode.core\n")
    assert collect_upward_edges(tmp_path) == {("core.thing", "proof")}
