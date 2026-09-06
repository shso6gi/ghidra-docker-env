"""Phase 7-2 / 7-4 (#97): BranchCheckContext の canonical ownership は proof/obligations/branch_context.py。
旧 path `checker.branch_context` の thin shim は 7-4 で削除済み（fresh interpreter で import 不能）。"""

import ast
import inspect
import pathlib
import subprocess
import sys

from scripts.function_tracer_pcode.proof.obligations import branch_context as canonical

CANONICAL = "scripts.function_tracer_pcode.proof.obligations.branch_context"
OLD_PATH = "scripts.function_tracer_pcode.checker.branch_context"
REPO_ROOT = pathlib.Path(__file__).resolve().parents[4]


def test_canonical_module_identity_and_dependencies():
    assert canonical.BranchCheckContext.__module__ == CANONICAL
    assert canonical.build_branch_check_context.__module__ == CANONICAL
    tree = ast.parse(inspect.getsource(canonical))
    mods = [n.module for n in ast.walk(tree) if isinstance(n, ast.ImportFrom) and (n.module or "").startswith("scripts.")]
    assert mods == ["scripts.function_tracer_pcode.proof.call_effect.preflight"]
    assert [f.name for f in canonical.BranchCheckContext.__dataclass_fields__.values()] == [
        "strategy", "replan_plan", "generation", "comparison_session_id", "branch_id", "decision_mode", "production_branch_authority_lease"]
    sig = inspect.signature(canonical.build_branch_check_context)
    assert list(sig.parameters) == ["strategy", "replan_plan", "call_proof_generation", "active_comparison_generation",
                                    "active_comparison_session_id", "active_call_proof_branch_id", "decision_mode",
                                    "production_branch_authority_lease", "session_id_factory"]


def test_old_shim_path_is_gone_from_the_repository():
    from scripts import function_tracer_pcode as pkg
    root = pathlib.Path(pkg.__file__).parent
    assert not (root / "checker" / "branch_context.py").exists()
    offenders = []
    for path in list(root.rglob("*.py")) + list((REPO_ROOT / "docs").rglob("*.md")) + [REPO_ROOT / "README.md"]:
        if path.name in ("test_cause_identity_relocation.py", "test_branch_context_relocation.py", "test_checker_lazy_exports_ownership.py") or not path.exists() or "issues" in path.parts:  # negative test 内の文字列は許容
            continue
        text = path.read_text(encoding="utf-8", errors="ignore")
        if "checker.branch_context" in text or "checker/branch_context" in text:
            offenders.append(str(path))
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
            if "branch_context" in line and any(k in line for k in ("pickle", "importlib", "__module__", "__qualname__", 'patch("scripts', 'setattr("scripts')):
                hits.append(f"{path.relative_to(root)}:{i}")
    assert hits == []


def test_checker_checker_namespace_patch_seam_is_preserved():
    from scripts.function_tracer_pcode.checker import checker as checker_module
    assert checker_module.build_branch_check_context is canonical.build_branch_check_context


def test_stage_runner_keeps_the_local_import_before_lease_issuance():
    from scripts.function_tracer_pcode.proof.obligations import stage_runner as runner_module
    module = ast.parse(inspect.getsource(runner_module))
    fn = next(n for n in ast.walk(module) if isinstance(n, ast.FunctionDef) and n.name == "execute_branch")
    body = fn.body
    imports = [i for i, st in enumerate(body) if isinstance(st, ast.ImportFrom)]
    issue = next(i for i, st in enumerate(body) if isinstance(st, ast.Assign) and isinstance(st.value, ast.Call)
                 and ast.unparse(st.value.func) == "issue_production_branch_authority")
    assert imports and max(imports) < issue
    assert [st.module for st in body if isinstance(st, ast.ImportFrom)] == ["scripts.function_tracer_pcode.proof.monolithic_authority", CANONICAL]
    assert isinstance(body[issue + 1], ast.Try)
    assert [ast.unparse(st) for st in body[issue + 1].finalbody] == ["revoke_production_branch_authority(branch_lease)"]
    assert not any(l.startswith(f"from {CANONICAL}") for l in inspect.getsource(runner_module).splitlines())


def test_fresh_interpreter_old_path_fails_and_canonical_paths_import_without_circularity():
    code = (
        "import importlib, sys\n"
        "for m in ['scripts.function_tracer_pcode.proof.obligations.branch_context', 'scripts.function_tracer_pcode.proof.cause_identity',"
        " 'scripts.function_tracer_pcode.proof.unknown_reason', 'scripts.function_tracer_pcode.checker.checker',"
        " 'scripts.function_tracer_pcode.checker.unknown_reason', 'scripts.function_tracer_pcode.proof.obligations.stage_runner',"
        " 'scripts.function_tracer_pcode.reporting.result_summary', 'scripts.function_tracer_pcode.cli.main']:\n"
        "    for k in [k for k in list(sys.modules) if k.startswith('scripts.')]: del sys.modules[k]\n"
        "    importlib.import_module(m)\n"
        f"for old in ['{OLD_PATH}', 'scripts.function_tracer_pcode.checker.cause_identity']:\n"
        "    try:\n"
        "        importlib.import_module(old)\n"
        "    except ModuleNotFoundError as e:\n"
        "        assert e.name == old, e.name\n"
        "    else:\n"
        "        raise SystemExit('old path still importable: ' + old)\n"
        "print('ok')\n")
    out = subprocess.run([sys.executable, "-B", "-c", code], cwd=REPO_ROOT, capture_output=True, text=True, timeout=300)
    assert out.returncode == 0 and out.stdout.strip() == "ok", out.stderr[-800:]
