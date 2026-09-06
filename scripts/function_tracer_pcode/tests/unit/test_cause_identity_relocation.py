"""Phase 7-1a (#97): checker/cause_identity.py → proof/cause_identity.py の relocation。
shim は同一 object を再輸出し、canonical module は上位層を import せず、内部 import は canonical path のみ。"""

import ast
import importlib
import inspect
import pathlib

import pytest

from scripts.function_tracer_pcode.proof import cause_identity as canonical
from scripts.function_tracer_pcode.checker import cause_identity as shim

PUBLIC_NAMES = (
    "CAUSE_IDENTITY_SCHEMA_VERSION", "PROOF_REQUIREMENT_SCHEMA_VERSION", "CauseKey", "ExecutionCauseKey",
    "IdentityScope", "LegacyProofObligationId", "ProofRequirementContract", "ProofRequirementId", "RelationalCauseKey",
    "UnaryCauseKey", "canonical_cause_tuple", "cause_key_from_dict",
)


def _canonical_public_names():
    """canonical module の top-level で定義・代入される非 private 名（型 alias を含む）を AST から集める。
    手書きの PUBLIC_NAMES の漏れ（#98 レビューの LegacyProofObligationId）を防ぐ。"""
    tree = ast.parse(inspect.getsource(canonical))
    names = set()
    for node in tree.body:
        if isinstance(node, (ast.ClassDef, ast.FunctionDef)):
            names.add(node.name)
        elif isinstance(node, ast.Assign):
            names.update(t.id for t in node.targets if isinstance(t, ast.Name))
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            names.add(node.target.id)
    return {n for n in names if not n.startswith("_")}


def test_public_name_list_matches_every_public_top_level_name_of_the_canonical_module():
    assert set(PUBLIC_NAMES) == _canonical_public_names()
    assert len(PUBLIC_NAMES) == 12


@pytest.mark.parametrize("name", PUBLIC_NAMES)
def test_shim_re_exports_the_identical_canonical_object(name):
    assert getattr(shim, name) is getattr(canonical, name)


def test_old_and_new_import_paths_yield_the_same_class_objects():
    from scripts.function_tracer_pcode.checker.cause_identity import ProofRequirementId as Old
    from scripts.function_tracer_pcode.proof.cause_identity import ProofRequirementId as New
    assert Old is New
    from scripts.function_tracer_pcode.checker.cause_identity import ProofRequirementContract as OldC, UnaryCauseKey as OldU
    from scripts.function_tracer_pcode.proof.cause_identity import ProofRequirementContract as NewC, UnaryCauseKey as NewU
    assert OldC is NewC and OldU is NewU
    assert New.__module__ == "scripts.function_tracer_pcode.proof.cause_identity"


def test_shim_defines_nothing_of_its_own():
    tree = ast.parse(inspect.getsource(shim))
    assert not [n for n in tree.body if isinstance(n, (ast.ClassDef, ast.FunctionDef))]
    imports = [n for n in tree.body if isinstance(n, ast.ImportFrom)]
    assert len(imports) == 1 and imports[0].module == "scripts.function_tracer_pcode.proof.cause_identity"
    assert set(shim.__all__) == set(PUBLIC_NAMES)


def test_canonical_module_has_only_stdlib_imports_and_unchanged_schema_versions():
    tree = ast.parse(inspect.getsource(canonical))
    mods = [n.module or "" for n in ast.walk(tree) if isinstance(n, ast.ImportFrom)] + \
           [a.name for n in ast.walk(tree) if isinstance(n, ast.Import) for a in n.names]
    assert not [m for m in mods if m.startswith("scripts.")]
    assert canonical.CAUSE_IDENTITY_SCHEMA_VERSION == 1 and canonical.PROOF_REQUIREMENT_SCHEMA_VERSION == 1
    # class 名と公開 API の集合は relocation 前と同じ
    assert {n.name for n in tree.body if isinstance(n, ast.ClassDef)} == {
        "IdentityScope", "UnaryCauseKey", "RelationalCauseKey", "ExecutionCauseKey", "ProofRequirementContract", "ProofRequirementId"}


def test_internal_imports_use_the_canonical_path_only():
    from scripts import function_tracer_pcode as pkg
    root = pathlib.Path(pkg.__file__).parent
    offenders = []
    for path in root.rglob("*.py"):
        rel = str(path.relative_to(root))
        if rel in ("checker/cause_identity.py", "tests/unit/test_cause_identity_relocation.py"):
            continue
        if "checker.cause_identity" in path.read_text(encoding="utf-8"):
            offenders.append(rel)
    assert offenders == []


def test_serialization_round_trip_is_unchanged_across_paths():
    contract = shim.ProofRequirementContract("return coverage complete")
    rid = shim.ProofRequirementId.create("return_coverage_completion", ("coverage", "f"), contract)
    payload = rid.to_dict()
    assert payload["schema_version"] == 1
    assert canonical.ProofRequirementId.from_dict(payload) == rid
    assert importlib.import_module("scripts.function_tracer_pcode.checker.cause_identity").ProofRequirementId.from_dict(payload) == rid
