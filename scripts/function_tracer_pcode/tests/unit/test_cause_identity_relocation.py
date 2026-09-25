"""Phase 7-1a / 7-4 (#97): cause_identity の canonical ownership は proof/cause_identity.py。
旧 path `checker.cause_identity` の thin shim は 7-4 で削除済み（fresh interpreter で import 不能）。"""

import ast
import inspect
import pathlib
import subprocess
import sys

from scripts.function_tracer_pcode.proof import cause_identity as canonical

CANONICAL = "scripts.function_tracer_pcode.proof.cause_identity"
OLD_PATH = "scripts.function_tracer_pcode.checker.cause_identity"
PUBLIC_NAMES = (
    "CAUSE_IDENTITY_SCHEMA_VERSION", "PROOF_REQUIREMENT_SCHEMA_VERSION", "CauseKey", "ExecutionCauseKey",
    "IdentityScope", "LegacyProofObligationId", "ProofRequirementContract", "ProofRequirementId", "RelationalCauseKey",
    "UnaryCauseKey", "canonical_cause_tuple", "cause_key_from_dict",
)
REPO_ROOT = pathlib.Path(__file__).resolve().parents[4]



LIVE_VALUES = "scripts.function_tracer_pcode.core.live_values"


def _imports_only_the_standard_library(module_name):
    import importlib

    tree = ast.parse(inspect.getsource(importlib.import_module(module_name)))
    mods = [n.module or "" for n in ast.walk(tree) if isinstance(n, ast.ImportFrom)]
    mods += [a.name for n in ast.walk(tree) if isinstance(n, ast.Import) for a in n.names]
    return not [m for m in mods if m.startswith("scripts")]

def _canonical_public_names():
    tree = ast.parse(inspect.getsource(canonical)); names = set()
    for node in tree.body:
        if isinstance(node, (ast.ClassDef, ast.FunctionDef)): names.add(node.name)
        elif isinstance(node, ast.Assign): names.update(t.id for t in node.targets if isinstance(t, ast.Name))
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name): names.add(node.target.id)
    return {n for n in names if not n.startswith("_")}


def test_public_surface_and_module_identity_are_canonical():
    assert set(PUBLIC_NAMES) == _canonical_public_names() and len(PUBLIC_NAMES) == 12
    for name in ("ProofRequirementId", "ProofRequirementContract", "UnaryCauseKey", "RelationalCauseKey", "ExecutionCauseKey", "IdentityScope"):
        assert getattr(canonical, name).__module__ == CANONICAL
    assert canonical.CAUSE_IDENTITY_SCHEMA_VERSION == 1 and canonical.PROOF_REQUIREMENT_SCHEMA_VERSION == 1
    tree = ast.parse(inspect.getsource(canonical))
    mods = [n.module or "" for n in ast.walk(tree) if isinstance(n, ast.ImportFrom)] + \
           [a.name for n in ast.walk(tree) if isinstance(n, ast.Import) for a in n.names]
    assert not [m for m in mods if m.startswith("scripts.") and m != LIVE_VALUES]
    # 例外は live な値を読む唯一の規則（`core.live_values`。標準 library だけに依る最下層）
    assert _imports_only_the_standard_library(LIVE_VALUES)


def test_serialization_round_trip():
    contract = canonical.ProofRequirementContract("return coverage complete")
    rid = canonical.ProofRequirementId.create("return_coverage_completion", ("coverage", "f"), contract)
    payload = rid.to_dict()
    assert payload["schema_version"] == 1 and canonical.ProofRequirementId.from_dict(payload) == rid


def test_old_shim_path_is_gone_from_the_repository():
    from scripts import function_tracer_pcode as pkg
    root = pathlib.Path(pkg.__file__).parent
    assert not (root / "checker" / "cause_identity.py").exists()
    offenders = []
    for path in list(root.rglob("*.py")) + list((REPO_ROOT / "docs").rglob("*.md")) + [REPO_ROOT / "README.md"]:
        if path.name in ("test_cause_identity_relocation.py", "test_branch_context_relocation.py", "test_checker_lazy_exports_ownership.py") or not path.exists() or "issues" in path.parts:  # negative test 内の文字列は許容
            continue
        if "checker.cause_identity" in path.read_text(encoding="utf-8", errors="ignore") or "checker/cause_identity" in path.read_text(encoding="utf-8", errors="ignore"):
            offenders.append(str(path))
    assert offenders == []


def test_fresh_interpreter_old_path_fails_and_canonical_imports():
    code = (
        "import importlib\n"
        f"m = importlib.import_module('{CANONICAL}')\n"
        f"assert m.ProofRequirementId.__module__ == '{CANONICAL}'\n"
        "try:\n"
        f"    importlib.import_module('{OLD_PATH}')\n"
        "except ModuleNotFoundError as e:\n"
        "    print('gone:', e.name)\n"
        "else:\n"
        "    raise SystemExit('old path still importable')\n")
    out = subprocess.run([sys.executable, "-B", "-c", code], cwd=REPO_ROOT, capture_output=True, text=True, timeout=300)
    assert out.returncode == 0, out.stderr[-800:]
    assert out.stdout.strip() == f"gone: {OLD_PATH}"
