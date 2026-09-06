"""Phase 7-4 (#97): checker package の lazy export は名前を維持したまま、pure な UNKNOWN 名は canonical
proof.unknown_reason へ、record / adapter 名は checker.unknown_reason へ解決する。"""

import ast
import inspect

from scripts import function_tracer_pcode
from scripts.function_tracer_pcode import checker as checker_pkg
from scripts.function_tracer_pcode.checker import unknown_reason as adapter
from scripts.function_tracer_pcode.proof import unknown_reason as canonical

PURE_EXPORTS = ("UNKNOWN_TUPLE_MISSING", "UnknownAggregationUnit", "UnknownCountKind", "UnknownDecisionEffect", "UnknownReasonClass",
                "UnknownReasonId", "UnknownReasonScope", "UnknownRecoveryActionStatus", "UnknownRecoveryPlan", "UnknownRecoveryProofKind",
                "UnknownRecoveryProofObligation", "build_proof_obligation_id", "get_unknown_recovery_plan")
ADAPTER_EXPORTS = ("UnknownReasonRecord", "UnknownRecoveryAction", "build_unknown_recovery_actions", "summarize_unknown_recovery_backlog")


def _canonical_public_names():
    tree = ast.parse(inspect.getsource(canonical)); names = set()
    for n in tree.body:
        if isinstance(n, (ast.ClassDef, ast.FunctionDef)): names.add(n.name)
        elif isinstance(n, ast.Assign): names.update(t.id for t in n.targets if isinstance(t, ast.Name))
    return {n for n in names if not n.startswith("_")}


def test_public_surface_is_unchanged():
    assert set(PURE_EXPORTS) | set(ADAPTER_EXPORTS) <= set(checker_pkg.__all__)
    assert checker_pkg.__all__ == sorted(checker_pkg._LAZY)
    unknown_related = {k for k in checker_pkg._LAZY if k.startswith("Unknown") or k in ("UNKNOWN_TUPLE_MISSING", "build_proof_obligation_id", "build_unknown_recovery_actions", "get_unknown_recovery_plan", "summarize_unknown_recovery_backlog")}
    assert unknown_related == set(PURE_EXPORTS) | set(ADAPTER_EXPORTS)


def test_lazy_targets_follow_canonical_ownership():
    pure_names = _canonical_public_names()
    for name, (module, attr) in checker_pkg._LAZY.items():
        if name in PURE_EXPORTS:
            assert module == "scripts.function_tracer_pcode.proof.unknown_reason" and attr in pure_names, name
        elif name in ADAPTER_EXPORTS:
            assert module == "scripts.function_tracer_pcode.checker.unknown_reason" and attr not in pure_names, name
    # 削除した shim を target にする entry は無い
    assert not [n for n, (m, _) in checker_pkg._LAZY.items() if m.endswith(("checker.cause_identity", "checker.branch_context"))]


def test_resolved_objects_are_the_owners_objects():
    for name in PURE_EXPORTS:
        assert getattr(checker_pkg, name) is getattr(canonical, name), name
        assert getattr(checker_pkg, name) is getattr(adapter, name)  # adapter の再輸出も同一 object
    for name in ADAPTER_EXPORTS:
        obj = getattr(checker_pkg, name)
        assert obj is getattr(adapter, name) and not hasattr(canonical, name), name
        assert getattr(obj, "__module__", "scripts.function_tracer_pcode.checker.unknown_reason") == "scripts.function_tracer_pcode.checker.unknown_reason"
