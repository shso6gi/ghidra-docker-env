"""Phase 7-1b-1 (#97): checker/unknown_reason.py の provably pure な定義層を proof/unknown_reason.py へ移す。
record / deserialization / authority compatibility cluster は checker 側に残し、現行 behavior を完全維持する。"""

import ast
import dataclasses
import inspect
import json
import pathlib
import re

import pytest

from scripts.function_tracer_pcode.checker import unknown_reason as checker_ur
from scripts.function_tracer_pcode.proof import unknown_reason as proof_ur

PURE_PUBLIC = (
    "UNKNOWN_TUPLE_MISSING", "UnknownCountKind", "UnknownReasonId", "UnknownReasonClass", "UnknownDecisionEffect",
    "UnknownReasonScope", "UnknownAggregationUnit", "UnknownRecoveryProofKind", "UnknownRecoveryActionStatus",
    "UnknownReasonDefinition", "UnknownRecoveryPlan", "UnknownRecoveryProofObligation",
    "register_unknown_reason", "register_unknown_recovery_plan", "get_unknown_reason_definition", "get_unknown_recovery_plan",
    "normalize_unknown_reason_id", "normalize_recovery_proof_kind", "build_proof_obligation_id",
    "coerce_unknown_recovery_proof_obligation", "coerce_unknown_recovery_proof_obligations", "format_projection_detail",
)
CHECKER_OWNED = (
    "UnknownReasonRecord", "UnknownRecoveryAction", "make_unknown_reason", "make_internal_v2_reason_diagnostic",
    "make_production_unknown_reason", "build_projection_diagnostic", "coerce_unknown_reason_record",
    "coerce_unknown_reason_records", "coerce_unknown_recovery_action", "coerce_unknown_recovery_actions",
    "build_unknown_recovery_actions", "summarize_unknown_reason_counts", "summarize_unknown_recovery_backlog",
    # Issue #22 PR-22-D: 行の schema・有界化（B5）・集計の出力 source（checker の所有）
    "VOCAB_MAX_CHARS", "ID_MAX_CHARS", "LABEL_MAX_CHARS", "DETAIL_MAX_CHARS",
    "UNKNOWN_REASON_ROW", "UNKNOWN_RECOVERY_ACTION_ROW", "RECOVERY_BACKLOG_ENTRY_ROW",
    "LEGACY_REASON_EVIDENCE_ROW", "LegacyReasonEvidence",
    "MATCH_AUTHORITY_DIGEST", "MATCH_CANONICAL_STR_DIGEST", "bounded_match_evidence", "match_digest",
    "finitize_unknown_reason_record", "finitize_unknown_recovery_action",
    "iter_unknown_recovery_actions", "unknown_reason_counts_source", "recovery_backlog_source",
    "EVIDENCE_REF_MAX_CHARS", "EVIDENCE_REFS_MAX_COUNT", "PROJECTION_DIAGNOSTIC_LEGACY_ROWS",
    "TYPED_CAUSE_KEY_INLINE_BYTES",
)
SNAPSHOT = pathlib.Path(__file__).resolve().parents[1] / "fixtures" / "unknown_reason_registry_snapshot.json"


def _top_level_public(module):
    tree = ast.parse(inspect.getsource(module)); names = set()
    for n in tree.body:
        if isinstance(n, (ast.ClassDef, ast.FunctionDef)): names.add(n.name)
        elif isinstance(n, ast.Assign): names.update(t.id for t in n.targets if isinstance(t, ast.Name))
        elif isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Name): names.add(n.target.id)
    return {n for n in names if not n.startswith("_")}


# 1. canonical pure module は上位 layer を import しない（静的 + 局所 import）
def test_canonical_pure_module_imports_no_upper_layer():
    tree = ast.parse(inspect.getsource(proof_ur))
    mods = [n.module or "" for n in ast.walk(tree) if isinstance(n, ast.ImportFrom)]
    mods += [a.name for n in ast.walk(tree) if isinstance(n, ast.Import) for a in n.names]
    assert not [m for m in mods if m.startswith("scripts.")], mods
    src = inspect.getsource(proof_ur)
    for layer in ("authority", "checker", "reporting"):
        assert f"function_tracer_pcode.{layer}" not in src


# 2 / 3. checker re-export と canonical object の identity、公開 pure surface の整合
@pytest.mark.parametrize("name", PURE_PUBLIC)
def test_checker_re_exports_the_identical_pure_object(name):
    assert getattr(checker_ur, name) is getattr(proof_ur, name)
    obj = getattr(proof_ur, name)
    if inspect.isclass(obj) or inspect.isfunction(obj):
        assert obj.__module__ == "scripts.function_tracer_pcode.proof.unknown_reason"


def test_pure_surface_and_checker_ownership_are_exactly_as_planned():
    assert _top_level_public(proof_ur) == set(PURE_PUBLIC)
    assert _top_level_public(checker_ur) == set(CHECKER_OWNED)
    # checker 側は pure 名を再定義しない（import による束縛のみ）
    tree = ast.parse(inspect.getsource(checker_ur))
    defined = {n.name for n in tree.body if isinstance(n, (ast.ClassDef, ast.FunctionDef))}
    assert not (defined & set(PURE_PUBLIC))
    # 旧 path から import されていた private registry 2 つは互換のため同一 object で再輸出
    assert checker_ur._UNKNOWN_REASON_REGISTRY is proof_ur._UNKNOWN_REASON_REGISTRY
    assert checker_ur._UNKNOWN_RECOVERY_PLAN_REGISTRY is proof_ur._UNKNOWN_RECOVERY_PLAN_REGISTRY


# 4 / 5. registry の before / after 完全一致（snapshot は 7546597 = 移動前の module から生成）
def _snapshot():
    return json.loads(SNAPSHOT.read_text(encoding="utf-8"))


# 分割後に新しく登録された reason（snapshot は移動前の module から生成したもの
# なので、追加分はここに明示して pre-split 分の parity と区別する）。
_POST_SPLIT_REASON_ADDITIONS = {
    "expansion_case_budget_exceeded",  # Issue #131
}


def test_reason_definition_registry_matches_the_pre_split_snapshot():
    snap = _snapshot()
    current = {k: dataclasses.asdict(v) for k, v in proof_ur._UNKNOWN_REASON_REGISTRY.items()}
    assert set(snap["definitions"]) - set(current) == set()
    assert set(current) - set(snap["definitions"]) == _POST_SPLIT_REASON_ADDITIONS
    pre_split = {k: v for k, v in current.items() if k in snap["definitions"]}
    assert json.loads(json.dumps(pre_split, sort_keys=True, default=str)) == snap["definitions"]
    assert len(current) == 37 + len(_POST_SPLIT_REASON_ADDITIONS)


def test_recovery_plan_registry_matches_the_pre_split_snapshot():
    snap = _snapshot()
    current = {k: v.to_dict() for k, v in proof_ur._UNKNOWN_RECOVERY_PLAN_REGISTRY.items()}
    assert set(current) == set(snap["plans"])
    assert json.loads(json.dumps(current, sort_keys=True, default=str)) == snap["plans"]
    assert len(current) == 29


# 6 / 7 / 8. normalization / build_proof_obligation_id / plan lookup の parity
def test_pure_function_outputs_match_the_pre_split_snapshot():
    probe = _snapshot()["probe"]
    ids = ["unknown", "x:return_coverage_inconclusive", "return_coverage_inconclusive", "nonexistent_reason", "S_PAIRWISE:unknown",
           "expression_semantics_unsupported", "", None]
    assert {str(x): proof_ur.normalize_unknown_reason_id(x) for x in ids} == probe["normalize"]
    kinds = ["none", "return_coverage_completion", "bogus", None, proof_ur.UnknownRecoveryProofKind.NONE]
    assert {str(x): proof_ur.normalize_recovery_proof_kind(x) for x in kinds} == probe["proof_kind"]
    assert list(proof_ur._registered_recovery_proof_kind_values()) == probe["proof_kind_values"]
    args = [("return_coverage_inconclusive", "S_PAIRWISE", "return_coverage_completion", "coverage", ("coverage", "f")),
            ("nonexistent", None, None, None, None), ("unknown", "", "bogus", "", ())]
    assert [json.loads(json.dumps(list(proof_ur.build_proof_obligation_id(*a)), default=str)) for a in args] == probe["obligation_ids"]
    assert {x: proof_ur.get_unknown_recovery_plan(x).to_dict() for x in ["return_coverage_inconclusive", "nonexistent_reason", "unknown"]} == probe["plan_lookup"]
    assert {x: json.loads(json.dumps(dataclasses.asdict(proof_ur.get_unknown_reason_definition(x)), default=str))
            for x in ["return_coverage_inconclusive", "nonexistent_reason"]} == probe["definition_lookup"]
    assert proof_ur.coerce_unknown_recovery_proof_obligation({"reason_id": "return_coverage_inconclusive", "proof_stage": "S_PAIRWISE"}).to_dict() == probe["coerce_obligation"]
    # 両 path で同じ関数 object なので checker 経由も同一結果
    assert checker_ur.build_proof_obligation_id(*args[0]) == proof_ur.build_proof_obligation_id(*args[0])


# 9 / 10. 既存の direct from_dict behavior が無変更（class は checker 側のまま）
def test_direct_from_dict_paths_stay_in_the_checker_module_and_round_trip():
    assert checker_ur.UnknownReasonRecord.__module__ == "scripts.function_tracer_pcode.checker.unknown_reason"
    assert checker_ur.UnknownRecoveryAction.__module__ == "scripts.function_tracer_pcode.checker.unknown_reason"
    record = checker_ur.make_unknown_reason("return_coverage_inconclusive", detail="d", proof_stage="S_PAIRWISE")
    assert checker_ur.UnknownReasonRecord.from_dict(record.to_dict()) == record
    action = checker_ur.UnknownRecoveryAction.from_dict({"reason_id": "return_coverage_inconclusive", "proof_stage": "S_PAIRWISE"})
    assert action.reason_id == "return_coverage_inconclusive"
    assert checker_ur.UnknownRecoveryAction.from_dict({"proof_stage": "unspecified"}).reason_id == proof_ur.UnknownReasonId.UNKNOWN.value
    src = inspect.getsource(checker_ur.UnknownReasonRecord.from_dict) + inspect.getsource(checker_ur.UnknownRecoveryAction.from_dict)
    assert src.count("PROCESS_DURABLE_REASON_REGISTRY") == 4  # 2 import + 2 lookup: registry fallback は現状のまま


# 11 / 12 / 13. v2-only reason deserialization / retired umbrella rejection / registry mismatch の parity
def test_v2_compatibility_semantics_are_unchanged():
    from scripts.function_tracer_pcode.authority.process.supervisor import PROCESS_DURABLE_REASON_REGISTRY
    from scripts.function_tracer_pcode.authority.sites.activation import RETIRED_UMBRELLA_REASON_IDS
    record = checker_ur.make_internal_v2_reason_diagnostic("expression_semantics_unsupported", stage="S_PAIRWISE",
                                                           evidence_refs=("unsupported_smt_operator",), detail="x")
    assert record.reason_id == "expression_semantics_unsupported"
    assert "expression_semantics_unsupported" not in proof_ur._UNKNOWN_REASON_REGISTRY  # v2-only: local registry には無い
    roundtrip = checker_ur.UnknownReasonRecord.from_dict(record.to_dict())
    assert roundtrip == record and roundtrip.reason_id == "expression_semantics_unsupported"
    retired = next(iter(RETIRED_UMBRELLA_REASON_IDS))
    with pytest.raises(ValueError, match="retired UNKNOWN umbrella is reader-only"):
        checker_ur.make_internal_v2_reason_diagnostic(retired, stage="S_PAIRWISE")
    definition = PROCESS_DURABLE_REASON_REGISTRY.get("expression_semantics_unsupported")
    wrong_class = next(c for c in proof_ur.UnknownReasonClass if c.value != definition.reason_class)
    with pytest.raises(ValueError, match="typed compatibility reason class differs from v2 registry"):
        checker_ur.make_internal_v2_reason_diagnostic("expression_semantics_unsupported", stage="S_PAIRWISE", reason_class=wrong_class)


# 14. proof importer が matrix どおりの import path
def test_proof_importers_follow_the_symbol_matrix():
    from scripts import function_tracer_pcode as pkg
    root = pathlib.Path(pkg.__file__).parent
    pat = re.compile(r"from scripts\.function_tracer_pcode\.(checker|proof)\.unknown_reason import (\([^)]*\)|[^\n]+)")
    seen = {}
    for path in (root / "proof").rglob("*.py"):
        for m in pat.finditer(path.read_text(encoding="utf-8")):
            names = {s.strip() for s in m.group(2).strip("()").replace("\n", ",").split(",") if s.strip()}
            seen.setdefault(str(path.relative_to(root)), {}).setdefault(m.group(1), set()).update(names)
    for module, by_layer in seen.items():
        assert by_layer.get("proof", set()) <= set(PURE_PUBLIC), module
        assert not (by_layer.get("checker", set()) & set(PURE_PUBLIC)), module  # pure 名は checker 経由で import しない
    assert seen["proof/strategies/pairwise_query_executor.py"] == {"proof": {"UnknownRecoveryActionStatus"}}
    assert set(seen["proof/strategies/monolithic.py"]["checker"]) == {"make_internal_v2_reason_diagnostic", "make_unknown_reason"}
    assert seen["proof/obligations/decision.py"] == {"checker": {"build_unknown_recovery_actions"}}
    assert "proof" not in seen["proof/obligations/stage_runner.py"]


# 15. baseline は削除のみ（pairwise_query_executor の 1 本）
def test_import_layer_baseline_dropped_only_the_pairwise_query_executor_edge():
    src = pathlib.Path(__file__).with_name("test_import_layers.py").read_text(encoding="utf-8")
    assert '("proof.strategies.pairwise_query_executor", "checker")' not in src
    for kept in ("proof.obligations.decision", "proof.obligations.stage_runner", "proof.strategies.monolithic",
                 "proof.strategies.pairwise_services._shared", "proof.strategies.proof_gates._shared"):
        assert f'("{kept}", "checker")' in src, kept
    assert '"proof.unknown_reason"' not in src  # 新規 exception なし
