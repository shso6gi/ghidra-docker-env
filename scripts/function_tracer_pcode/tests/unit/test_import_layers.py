"""Import-layer guardrail (refactoring Phase 3).

The package is layered (CLAUDE.md, "Architecture"): imports must point
downward only.  A number of upward edges exist today and are tracked as
tech debt; they are listed explicitly below as the baseline.  This test
fails when

* a module imports a *higher* layer and that (module, layer) pair is not in
  the baseline  -> a new upward dependency was introduced, or
* a baseline entry is no longer needed  -> remove it here so the baseline
  only shrinks, or
* a top-level module or directory of the package has no layer assignment.

Imports are collected with ``ast`` over every module of the package
(tests excluded), including imports inside functions (lazy imports avoid
runtime cycles but are still layer dependencies) and relative imports
(``from ..authority import x`` is resolved against the importing module's
package before the layer check).

Granularity: the baseline pins (importing module, imported *layer*), not
(importing module, imported module).  It therefore guarantees that no new
(module -> higher layer) pair appears; additional imports from the same
higher layer inside an already-listed module are not detected.  Tighten
to module-level pairs when the _shared/facade migrations need it.
"""
from __future__ import annotations

import ast
from pathlib import Path

import pytest

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


def resolve_import_from(current_module: str, is_package: bool, node: ast.ImportFrom):
    """Return the package-relative target of an ``ImportFrom`` (``None`` when
    it points outside the package).  Relative imports are resolved with
    ``node.level`` against the importing module's package."""
    if node.level == 0:
        if node.module and node.module.startswith(PACKAGE_PREFIX):
            return node.module[len(PACKAGE_PREFIX):]
        return None
    package_parts = current_module.split(".") if is_package else current_module.split(".")[:-1]
    drop = node.level - 1
    if drop > len(package_parts):
        return None
    base = package_parts[: len(package_parts) - drop] if drop else package_parts
    if node.module:
        base = base + node.module.split(".")
    return ".".join(base) if base else None


def _imported_package_modules(tree: ast.AST, current_module: str, is_package: bool):
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            target = resolve_import_from(current_module, is_package, node)
            if target is not None:
                yield target
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
            raise AssertionError(f"module outside every layer: {module}")
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for target in _imported_package_modules(tree, module, path.name == "__init__.py"):
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


def test_collector_resolves_relative_imports(tmp_path):
    # proof/sub/mod.py: `from ...authority import y` (upward, relative),
    # `from ._shared import z` (same layer), `from .. import base` (same
    # layer, package-relative); proof/__init__.py: `from .sub import mod`.
    for name in ("proof", "proof/sub", "authority"):
        (tmp_path / name).mkdir(parents=True)
        (tmp_path / name / "__init__.py").write_text("")
    (tmp_path / "proof" / "__init__.py").write_text("from .sub import mod\n")
    (tmp_path / "proof" / "sub" / "mod.py").write_text(
        "from ...authority import y\nfrom ._shared import z\nfrom .. import base\n"
    )
    (tmp_path / "authority" / "__init__.py").write_text("from ..core import w\n")  # downward
    (tmp_path / "core").mkdir(); (tmp_path / "core" / "__init__.py").write_text("")
    assert collect_upward_edges(tmp_path) == {("proof.sub.mod", "authority")}


def test_collector_rejects_modules_outside_every_layer(tmp_path):
    (tmp_path / "core").mkdir(); (tmp_path / "core" / "__init__.py").write_text("")
    (tmp_path / "helper.py").write_text("x = 1\n")
    with pytest.raises(AssertionError, match="outside every layer: helper"):
        collect_upward_edges(tmp_path)


def test_resolve_import_from_levels():
    import ast as _ast

    node = _ast.parse("from ...authority.lifecycle import x").body[0]
    assert resolve_import_from("proof.sub.mod", False, node) == "authority.lifecycle"
    # `from . import sibling` resolves to the importing package (the layer of
    # `sibling` is the package's layer either way)
    node = _ast.parse("from . import sibling").body[0]
    assert resolve_import_from("proof.sub.mod", False, node) == "proof.sub"
    assert resolve_import_from("proof.sub", True, node) == "proof.sub"
    node = _ast.parse("from ....far import x").body[0]   # beyond the package root
    assert resolve_import_from("proof.sub.mod", False, node) is None
