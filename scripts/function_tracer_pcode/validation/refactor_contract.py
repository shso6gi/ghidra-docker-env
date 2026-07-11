"""Static and runtime contracts used while decomposing the analysis modules.

The refactoring deliberately keeps this checker independent from pytest so it
can be run before imports, focused tests, or a real-binary matrix.  The checked
manifest is an immutable description of the compatibility surface at the
refactoring baseline; size and dependency metrics are ratchets rather than
exact snapshots because the implementation is expected to move between
modules.
"""

from __future__ import annotations

import argparse
import ast
from dataclasses import MISSING, fields, is_dataclass
import hashlib
import importlib
import inspect
import json
from pathlib import Path
import subprocess
from typing import Any, Dict, Iterable, Mapping, MutableMapping, Optional, Sequence, Tuple


REPOSITORY_ROOT = Path(__file__).resolve().parents[3]
PACKAGE_ROOT = REPOSITORY_ROOT / "scripts" / "function_tracer_pcode"
DEFAULT_MANIFEST_PATH = (
    REPOSITORY_ROOT
    / "artifacts"
    / "refactor"
    / "current-head-fc11037"
    / "contract.json"
)

PUBLIC_SYMBOLS: Mapping[str, Tuple[str, ...]] = {
    "scripts.function_tracer_pcode.analysis.analyzer": ("ReturnAnalyzer",),
    "scripts.function_tracer_pcode.analysis.recurrence_summary": (
        "StructuralRecurrenceSummarizer",
        "CountedLoopInduction",
        "CountedLoopAccumulator",
        "CountedLoopGuard",
        "CountedLoopUpdateCase",
        "ReadonlyRoundedCountCandidate",
        "ResidueLoopCase",
        "StateTransitionLoopModel",
    ),
    "scripts.function_tracer_pcode.analysis.effect_summary": (
        "EffectSummary",
        "StoreEffect",
        "StoreEffectProvenance",
        "CanonicalLocation",
        "CallArgumentEvidence",
        "CallArgumentWidthEvidence",
        "CallSiteEffectSummaryEvidence",
        "CallTargetResolutionEvidence",
        "FunctionControlEffectProfile",
        "UnsupportedCallEffectRef",
    ),
    "scripts.function_tracer_pcode.equivalence.strategies.base": (
        "CheckStrategy",
        "StrategyResult",
        "ReturnCoverageCheckResult",
    ),
    "scripts.function_tracer_pcode.equivalence.strategies.pairwise": (
        "PairwiseStrategy",
        "QueryResult",
        "ReturnCase",
    ),
    "scripts.function_tracer_pcode.equivalence.strategies.monolithic": (
        "MonolithicStrategy",
    ),
    "scripts.function_tracer_pcode.equivalence.strategies.loop_template": (
        "LoopTemplatePairwiseStrategy",
    ),
}

# These are production dispatch points, not merely conveniences used by tests.
PRODUCTION_HOOKS: Mapping[str, Tuple[str, ...]] = {
    "scripts.function_tracer_pcode.equivalence.strategies.pairwise.PairwiseStrategy": (
        "check",
        "_solve_query_internal",
        "_try_normalization_equivalence",
    ),
    "scripts.function_tracer_pcode.equivalence.strategies.loop_template.LoopTemplatePairwiseStrategy": (
        "_try_normalization_equivalence",
    ),
    "scripts.function_tracer_pcode.equivalence.strategies.monolithic.MonolithicStrategy": (
        "_build_validation_analyses",
        "_counterexample_is_decisive_across_case_split",
    ),
    "scripts.function_tracer_pcode.analysis.analyzer.ReturnAnalyzer": (
        "dispose",
        "analyze_function",
        "analyze_function_by_name",
    ),
    "scripts.function_tracer_pcode.analysis.recurrence_summary.StructuralRecurrenceSummarizer": (
        "has_summary_candidate",
        "try_summarize_function",
        "try_summarize_pre_return_counted_scalar_loop",
        "_find_cbranch_op",
        "_safe_pcode_input_count",
        "_build_pcode_expression",
        "_canonicalize_expression",
    ),
}

SIZE_RATCHET_BASELINE: Mapping[str, int] = {
    "analysis/analyzer.py": 15568,
    "analysis/effect_summary.py": 9610,
    "analysis/recurrence_summary.py": 22351,
    "equivalence/strategies/base.py": 10608,
    "equivalence/strategies/pairwise.py": 11481,
}

NEW_FILE_SOFT_LIMIT = 2000
NEW_FILE_HARD_LIMIT = 3000

SERVICE_INTERNAL_PREFIXES = (
    "scripts.function_tracer_pcode.analysis.analyzer_services",
    "scripts.function_tracer_pcode.analysis.effect_services",
    "scripts.function_tracer_pcode.analysis.recurrence",
    "scripts.function_tracer_pcode.equivalence.strategies.pairwise_services",
    "scripts.function_tracer_pcode.equivalence.strategies.proof_gates",
)


def _qualified_name(value: Any) -> str:
    return f"{value.__module__}.{value.__qualname__}"


def _json_value(value: Any) -> Any:
    if value is MISSING:
        return {"kind": "missing"}
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, (tuple, list)):
        return [_json_value(item) for item in value]
    if isinstance(value, dict):
        return {
            str(key): _json_value(item)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        }
    if inspect.isclass(value) or inspect.isfunction(value):
        return {"kind": "reference", "name": _qualified_name(value)}
    return {"kind": "repr", "type": _qualified_name(type(value)), "value": repr(value)}


def _callable_contract(value: Any) -> Optional[Dict[str, Any]]:
    if not callable(value):
        return None
    try:
        signature = str(inspect.signature(value))
    except (TypeError, ValueError):
        signature = None
    return {
        "signature": signature,
        "is_abstract": bool(getattr(value, "__isabstractmethod__", False)),
        "is_coroutine": bool(inspect.iscoroutinefunction(value)),
    }


def _dataclass_contract(value: Any) -> Optional[Dict[str, Any]]:
    if not inspect.isclass(value) or not is_dataclass(value):
        return None
    params = getattr(value, "__dataclass_params__", None)
    return {
        "frozen": bool(getattr(params, "frozen", False)),
        "fields": [
            {
                "name": field.name,
                "default": _json_value(field.default),
                "default_factory": _json_value(field.default_factory),
                "init": bool(field.init),
                "repr": bool(field.repr),
                "compare": bool(field.compare),
            }
            for field in fields(value)
        ],
    }


def symbol_contract(module_name: str, symbol_name: str) -> Dict[str, Any]:
    module = importlib.import_module(module_name)
    value = getattr(module, symbol_name)
    contract: Dict[str, Any] = {
        "module": module_name,
        "symbol": symbol_name,
        "defined_as": _qualified_name(value),
        "callable": _callable_contract(value),
        "dataclass": _dataclass_contract(value),
    }
    if inspect.isclass(value):
        contract["mro"] = [_qualified_name(base) for base in value.__mro__]
    return contract


def hook_contract(qualified_class_name: str, method_name: str) -> Dict[str, Any]:
    module_name, class_name = qualified_class_name.rsplit(".", 1)
    cls = getattr(importlib.import_module(module_name), class_name)
    value = getattr(cls, method_name)
    defining_class = next(
        base for base in cls.__mro__ if method_name in getattr(base, "__dict__", {})
    )
    return {
        "class": qualified_class_name,
        "method": method_name,
        "defined_on": _qualified_name(defining_class),
        "callable": _callable_contract(value),
    }


def _python_files() -> Tuple[Path, ...]:
    return tuple(sorted(PACKAGE_ROOT.rglob("*.py")))


def _module_name(path: Path) -> str:
    relative = path.relative_to(REPOSITORY_ROOT).with_suffix("")
    return ".".join(relative.parts)


def _resolve_import(current_module: str, node: ast.ImportFrom) -> Optional[str]:
    if node.level == 0:
        return node.module
    package_parts = current_module.split(".")[:-1]
    keep = max(0, len(package_parts) - node.level + 1)
    prefix = package_parts[:keep]
    if node.module:
        prefix.extend(node.module.split("."))
    return ".".join(prefix) or None


def dependency_snapshot() -> Dict[str, Any]:
    package_prefix = "scripts.function_tracer_pcode"
    graph: Dict[str, set] = {}
    private_imports = []
    for path in _python_files():
        module_name = _module_name(path)
        graph.setdefault(module_name, set())
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom):
                imported_module = _resolve_import(module_name, node)
                if imported_module and imported_module.startswith(package_prefix):
                    graph[module_name].add(imported_module)
                for alias in node.names:
                    same_service_boundary = any(
                        module_name.startswith(prefix + ".")
                        and (imported_module or "").startswith(prefix + ".")
                        for prefix in SERVICE_INTERNAL_PREFIXES
                    )
                    if (
                        alias.name.startswith("_")
                        and alias.name != "*"
                        and not same_service_boundary
                    ):
                        private_imports.append(
                            (module_name, imported_module or "", alias.name, node.lineno)
                        )
            elif isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name.startswith(package_prefix):
                        graph[module_name].add(alias.name)

    components = _strongly_connected_components(graph)
    cycles = sorted(
        [sorted(component) for component in components if len(component) > 1],
        key=lambda component: (len(component), component),
    )
    return {
        "private_import_count": len(private_imports),
        "private_imports": [list(item) for item in sorted(private_imports)],
        "cycles": cycles,
        "edges": {
            module: sorted(targets)
            for module, targets in sorted(graph.items())
            if targets
        },
    }


def _strongly_connected_components(graph: Mapping[str, set]) -> Tuple[Tuple[str, ...], ...]:
    index = 0
    indices: Dict[str, int] = {}
    lowlinks: Dict[str, int] = {}
    stack = []
    on_stack = set()
    components = []

    def visit(node: str) -> None:
        nonlocal index
        indices[node] = index
        lowlinks[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)
        for target in graph.get(node, set()):
            if target not in graph:
                continue
            if target not in indices:
                visit(target)
                lowlinks[node] = min(lowlinks[node], lowlinks[target])
            elif target in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[target])
        if lowlinks[node] != indices[node]:
            return
        component = []
        while stack:
            member = stack.pop()
            on_stack.remove(member)
            component.append(member)
            if member == node:
                break
        components.append(tuple(sorted(component)))

    for node in sorted(graph):
        if node not in indices:
            visit(node)
    return tuple(components)


def size_snapshot() -> Dict[str, int]:
    return {
        str(path.relative_to(PACKAGE_ROOT)): len(
            path.read_text(encoding="utf-8").splitlines()
        )
        for path in _python_files()
    }


def source_tree_hash() -> str:
    digest = hashlib.sha256()
    for path in _python_files():
        relative = path.relative_to(REPOSITORY_ROOT).as_posix().encode("utf-8")
        digest.update(len(relative).to_bytes(4, "big"))
        digest.update(relative)
        content = path.read_bytes()
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return digest.hexdigest()


def _git(args: Sequence[str]) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=REPOSITORY_ROOT, text=True
    ).strip()


def capture_contract() -> Dict[str, Any]:
    symbols = [
        symbol_contract(module_name, symbol_name)
        for module_name, names in PUBLIC_SYMBOLS.items()
        for symbol_name in names
    ]
    hooks = [
        hook_contract(class_name, method_name)
        for class_name, names in PRODUCTION_HOOKS.items()
        for method_name in names
    ]
    dependencies = dependency_snapshot()
    return {
        "schema_version": 1,
        "git_commit": _git(("rev-parse", "HEAD")),
        "tracked_dirty": bool(_git(("status", "--porcelain", "--untracked-files=no"))),
        "source_tree_hash": source_tree_hash(),
        "symbols": symbols,
        "hooks": hooks,
        "size_ratchet_baseline": dict(SIZE_RATCHET_BASELINE),
        "private_import_count": dependencies["private_import_count"],
        "dependency_cycles": dependencies["cycles"],
    }


def compare_contract(baseline: Mapping[str, Any]) -> Tuple[str, ...]:
    current = capture_contract()
    failures = []
    baseline_symbols = [_export_normalized_symbol(item) for item in baseline.get("symbols", ())]
    current_symbols = [_export_normalized_symbol(item) for item in current["symbols"]]
    if current_symbols != baseline_symbols:
        failures.append("symbols_changed")
    if _normalize_moved_type_paths(current["hooks"]) != _normalize_moved_type_paths(
        baseline.get("hooks")
    ):
        failures.append("hooks_changed")

    current_sizes = size_snapshot()
    for relative, maximum in baseline.get("size_ratchet_baseline", {}).items():
        if current_sizes.get(relative, 0) > int(maximum):
            failures.append(f"size_increased:{relative}")
    added_paths = set(
        _git(("diff", "--name-only", "--diff-filter=A", "HEAD")).splitlines()
    )
    added_paths.update(
        _git(("ls-files", "--others", "--exclude-standard")).splitlines()
    )
    package_prefix = "scripts/function_tracer_pcode/"
    for repository_path in sorted(added_paths):
        if not repository_path.startswith(package_prefix) or not repository_path.endswith(".py"):
            continue
        relative = repository_path[len(package_prefix) :]
        if current_sizes.get(relative, 0) > NEW_FILE_HARD_LIMIT:
            failures.append(f"new_file_hard_limit_exceeded:{relative}")
    baseline_private = int(baseline.get("private_import_count", 0))
    if int(current["private_import_count"]) > baseline_private:
        failures.append("private_import_count_increased")
    baseline_cycles = [set(item) for item in baseline.get("dependency_cycles", ())]
    for cycle in current["dependency_cycles"]:
        current_cycle = set(cycle)
        if not any(current_cycle <= baseline_cycle for baseline_cycle in baseline_cycles):
            failures.append("new_dependency_cycle:" + ",".join(cycle))
    return tuple(failures)


def _export_normalized_symbol(contract: Mapping[str, Any]) -> Dict[str, Any]:
    """Compare the public export path without mutating runtime ``__module__``."""
    normalized = dict(contract)
    export_name = f"{contract.get('module')}.{contract.get('symbol')}"
    normalized["defined_as"] = export_name
    mro = list(normalized.get("mro") or ())
    if mro:
        mro[0] = export_name
        normalized["mro"] = mro
    callable_contract = normalized.get("callable")
    if isinstance(callable_contract, Mapping):
        callable_normalized = dict(callable_contract)
        signature = callable_normalized.get("signature")
        if isinstance(signature, str):
            callable_normalized["signature"] = signature.replace(
                "scripts.function_tracer_pcode.equivalence.strategies.proof_gates._shared.StrategyResult",
                "scripts.function_tracer_pcode.equivalence.strategies.base.StrategyResult",
            )
        normalized["callable"] = callable_normalized
    return normalized


def _normalize_moved_type_paths(value: Any) -> Any:
    if isinstance(value, str):
        return value.replace(
            "scripts.function_tracer_pcode.equivalence.strategies.proof_gates._shared.StrategyResult",
            "scripts.function_tracer_pcode.equivalence.strategies.base.StrategyResult",
        )
    if isinstance(value, Mapping):
        return {key: _normalize_moved_type_paths(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_normalize_moved_type_paths(item) for item in value]
    return value


def write_manifest(path: Path = DEFAULT_MANIFEST_PATH) -> None:
    payload = capture_contract()
    if payload["tracked_dirty"]:
        raise RuntimeError("refusing to capture a contract from a tracked-dirty worktree")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST_PATH)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)
    if args.write:
        write_manifest(args.manifest)
        print(args.manifest)
        return 0
    baseline = json.loads(args.manifest.read_text(encoding="utf-8"))
    failures = compare_contract(baseline)
    if failures:
        for failure in failures:
            print(failure)
        return 1
    print("refactor contract: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
