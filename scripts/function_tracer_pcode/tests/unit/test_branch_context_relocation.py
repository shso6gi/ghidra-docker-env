"""Phase 7-2 (#97): checker/branch_context.py → proof/obligations/branch_context.py の relocation。"""

import ast
import inspect
import pathlib
import subprocess
import sys

from scripts.function_tracer_pcode.checker import branch_context as shim
from scripts.function_tracer_pcode.proof.obligations import branch_context as canonical

CANONICAL = "scripts.function_tracer_pcode.proof.obligations.branch_context"


def test_shim_re_exports_the_identical_objects_and_nothing_else():
    assert shim.BranchCheckContext is canonical.BranchCheckContext
    assert shim.build_branch_check_context is canonical.build_branch_check_context
    assert shim.__all__ == ["BranchCheckContext", "build_branch_check_context"]
    tree = ast.parse(inspect.getsource(shim))
    assert not [n for n in tree.body if isinstance(n, (ast.ClassDef, ast.FunctionDef))]
    imports = [n for n in tree.body if isinstance(n, ast.ImportFrom)]
    assert len(imports) == 1 and imports[0].module == CANONICAL


def test_canonical_module_identity_and_dependencies():
    assert canonical.BranchCheckContext.__module__ == CANONICAL
    assert canonical.build_branch_check_context.__module__ == CANONICAL
    tree = ast.parse(inspect.getsource(canonical))
    mods = [n.module for n in ast.walk(tree) if isinstance(n, ast.ImportFrom) and (n.module or "").startswith("scripts.")]
    assert mods == ["scripts.function_tracer_pcode.proof.call_effect.preflight"]  # CallProofDecisionMode のみ、上位 layer なし
    assert [f.name for f in canonical.BranchCheckContext.__dataclass_fields__.values()] == [
        "strategy", "replan_plan", "generation", "comparison_session_id", "branch_id", "decision_mode", "production_branch_authority_lease"]
    sig = inspect.signature(canonical.build_branch_check_context)
    assert list(sig.parameters) == ["strategy", "replan_plan", "call_proof_generation", "active_comparison_generation",
                                    "active_comparison_session_id", "active_call_proof_branch_id", "decision_mode",
                                    "production_branch_authority_lease", "session_id_factory"]


def test_production_code_uses_only_the_canonical_path():
    from scripts import function_tracer_pcode as pkg
    root = pathlib.Path(pkg.__file__).parent
    offenders = []
    for path in root.rglob("*.py"):
        rel = str(path.relative_to(root))
        if "tests" in path.parts or rel == "checker/branch_context.py":
            continue
        if "checker.branch_context" in path.read_text(encoding="utf-8"):
            offenders.append(rel)
    assert offenders == []
    for rel in ("checker/checker.py", "checker/strategy_execution.py", "checker/result_assembly.py", "proof/obligations/stage_runner.py"):
        assert CANONICAL in (root / rel).read_text(encoding="utf-8"), rel


def test_no_pickle_importlib_or_qualified_name_dependency_on_the_module_path():
    from scripts import function_tracer_pcode as pkg
    root = pathlib.Path(pkg.__file__).parent
    hits = []
    for path in root.rglob("*.py"):
        if path.name == "test_branch_context_relocation.py":
            continue
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if "branch_context" in line and any(k in line for k in ("pickle", "importlib", "__module__", "__qualname__", 'patch("scripts', "setattr(\"scripts")):
                hits.append(f"{path.relative_to(root)}:{i}")
    assert hits == []


def test_checker_checker_namespace_patch_seam_is_preserved():
    from scripts.function_tracer_pcode.checker import checker as checker_module
    assert checker_module.build_branch_check_context is canonical.build_branch_check_context
    src = inspect.getsource(checker_module)
    assert f"from {CANONICAL} import (" in src or f"from {CANONICAL} import BranchCheckContext, build_branch_check_context" in src


def test_stage_runner_keeps_the_local_import_before_lease_issuance():
    from scripts.function_tracer_pcode.proof.obligations import stage_runner as runner_module
    module = ast.parse(inspect.getsource(runner_module))
    fn = next(n for n in ast.walk(module) if isinstance(n, ast.FunctionDef) and n.name == "execute_branch")
    body = fn.body
    imports = [i for i, st in enumerate(body) if isinstance(st, ast.ImportFrom)]
    issue = next(i for i, st in enumerate(body) if isinstance(st, ast.Assign) and isinstance(st.value, ast.Call)
                 and ast.unparse(st.value.func) == "issue_production_branch_authority")
    assert imports and max(imports) < issue  # import は lease issue より前（local import のまま、top へ hoist していない）
    assert [st.module for st in body if isinstance(st, ast.ImportFrom)] == [
        "scripts.function_tracer_pcode.proof.monolithic_authority", CANONICAL]
    assert isinstance(body[issue + 1], ast.Try)
    assert "from scripts.function_tracer_pcode.proof.obligations.branch_context" not in "\n".join(
        l for l in inspect.getsource(runner_module).splitlines() if l.startswith("from "))  # module top には無い


def test_fresh_interpreter_imports_without_circularity():
    code = ("import importlib, sys\n"
            "for m in ['scripts.function_tracer_pcode.proof.obligations.branch_context', 'scripts.function_tracer_pcode.checker.branch_context',"
            " 'scripts.function_tracer_pcode.checker.checker', 'scripts.function_tracer_pcode.proof.obligations.stage_runner']:\n"
            "    for k in [k for k in list(sys.modules) if k.startswith('scripts.')]: del sys.modules[k]\n"
            "    importlib.import_module(m)\n"
            "print('ok')\n")
    root = pathlib.Path(__file__).resolve().parents[4]
    out = subprocess.run([sys.executable, "-B", "-c", code], cwd=root, capture_output=True, text=True, timeout=300)
    assert out.returncode == 0 and out.stdout.strip() == "ok", out.stderr[-800:]
