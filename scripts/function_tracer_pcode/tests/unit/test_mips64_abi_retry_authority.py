# -*- coding: utf-8 -*-
"""MIPS64 Phase 4-B（ABI retry）は撤去した（#184）。入力の仮定の owner は InputCorrespondence だけ。

Phase 4-B は SAT model・usage hint・宣言型から ``(= wide (ext (extract narrow)))`` を足して solver を
直接呼んでいた（最終 InputCorrespondence が含意しない入力の仮定。#167 の不変条件の例外）。撤去の後に
固定すること:

1. 撤去した名前（retry の本体・適格判定・偽反例の検出・ABI 制約の組み立て）への production からの
   参照が 0。Phase 4-B の module（``checker/abi_retry.py``）は無い。
2. 非同一関数の EQ closure を発行する経路は ``proof/obligations/stage_runner.py`` の
   ``issue_pending_eq_closure_authority`` だけで、そこは dispatch frame の信頼済み comparison receipt を
   要求する。残る MIPS64 の module（P4A の引数型の修正）はその経路にも NOT_EQ の decisive proof にも触れない。
3. v2 の最終判定は EQ_CLOSURE receipt が無ければ EQUIVALENT を出さず、legacy EQ と候補 NOT_EQ の
   食い違いは ``DECISIVE_OUTCOME_DISAGREEMENT`` の ERROR になる（legacy の再試行が作る EQ の backstop）。
"""

from __future__ import annotations

import ast
from pathlib import Path
from unittest.mock import Mock

from scripts.function_tracer_pcode.authority.contracts import Outcome
from scripts.function_tracer_pcode.authority.decision.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    FinalizationAuthority,
    finalize_decision,
)
from scripts.function_tracer_pcode.authority.lifecycle import production_boundary
from scripts.function_tracer_pcode.tests.unit._issue125_support import (
    SAT_SAFETY_CONTRACT,
    SAT_SAFETY_PROOF_KIND,
    LifecycleHarness,
    sat_safety_cause_inputs,
)


PACKAGE = Path(__file__).resolve().parents[2]



def _python_sources():
    for path in sorted(PACKAGE.rglob("*.py")):
        if "tests" in path.relative_to(PACKAGE).parts:
            continue
        yield path, ast.parse(path.read_text(encoding="utf-8"))


def _referenced_names(tree: ast.AST):
    for node in ast.walk(tree):
        if isinstance(node, ast.Name):
            yield node.id
        elif isinstance(node, ast.Attribute):
            yield node.attr
        elif isinstance(node, ast.alias):
            yield node.name.split(".")[-1]


#: 撤去した Phase 4-B の名前（#184）。
REMOVED_PHASE4B_NAMES = frozenset({
    "AbiRetryMixin",
    "_retry_with_abi_constraints",
    "_retry_with_iterative_abi_constraints",
    "run_phase4_mips64_retry",
    "should_run_phase4_retry",
    "detect_spurious_counterexample",
    "build_abi_constraints",
    "build_abi_assertion_section",
    "build_with_abi_constraints",
    "will_try_phase4b",
})


def test_phase4b_is_removed_from_production():
    assert not (PACKAGE / "checker" / "abi_retry.py").exists()
    referencing = sorted(
        (str(path.relative_to(PACKAGE)), name)
        for path, tree in _python_sources()
        for name in set(_referenced_names(tree)) | {
            node.name for node in ast.walk(tree)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        } | {node.arg for node in ast.walk(tree) if isinstance(node, ast.arg)}
        if name in REMOVED_PHASE4B_NAMES
    )
    assert referencing == []


def test_only_the_prepared_frame_stage_runner_issues_non_identical_eq_closure():
    issuers = sorted(
        str(path.relative_to(PACKAGE))
        for path, tree in _python_sources()
        if any(
            isinstance(node, ast.Call)
            and getattr(node.func, "id", getattr(node.func, "attr", None))
            == "issue_pending_eq_closure_authority"
            for node in ast.walk(tree)
        )
    )
    assert issuers == ["proof/obligations/stage_runner.py"]

    for module in ("checker/arch/mips64.py",):
        tree = ast.parse((PACKAGE / module).read_text(encoding="utf-8"))
        names = set(_referenced_names(tree))
        assert not names & {
            "issue_pending_eq_closure_authority",
            "PendingEqClosureAuthority",
            "EQ_CLOSURE",
            "PreparedDispatchFrame",
            "issue_builtin_comparison_receipt",
            # NOT_EQ 側の decisive proof（SAFE_COUNTEREXAMPLE）の発行経路。
            "SafeCounterexampleProductionSignal",
            "complete_observed_sat_safety_for_counterexample",
            "DecisiveProofReceipt",
            "COUNTEREXAMPLE",
        }, module


def _projection(*, with_active_sat_safety_cause: bool):
    harness = LifecycleHarness()
    authority, requirement = harness.build_occurrence(
        sat_safety_cause_inputs(), contract=SAT_SAFETY_CONTRACT, proof_kind=SAT_SAFETY_PROOF_KIND,
    )
    harness.observe(authority)
    if not with_active_sat_safety_cause:
        harness.complete(authority, requirement)
    return harness, harness.final_projection()


def test_final_decision_without_eq_closure_is_never_equivalent():
    for active in (False, True):
        harness, projection = _projection(with_active_sat_safety_cause=active)
        receipt = finalize_decision(FinalizationAuthority(harness.identity.result_occurrence_id, projection))
        assert receipt.outcome not in {Outcome.EQUIVALENT, Outcome.NOT_EQ}
        assert receipt.outcome is (Outcome.UNKNOWN if active else Outcome.ERROR)


def test_legacy_retry_eq_disagreeing_with_a_canonical_not_eq_is_an_error():
    harness, projection = _projection(with_active_sat_safety_cause=False)
    result_id = harness.identity.result_occurrence_id
    not_eq = finalize_decision(FinalizationAuthority(
        result_id, projection,
        (DecisiveProofReceipt.create(
            result_occurrence_id=result_id,
            lifecycle_projection_digest=projection.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.SAFE_COUNTEREXAMPLE,
            proof_artifact_digest="issue167-counterexample",
        ),),
    ))
    assert not_eq.outcome is Outcome.NOT_EQ

    session = Mock()
    session.identity.result_occurrence_id = result_id
    reconciled, error_kind = production_boundary._reconcile_legacy_and_canonical_candidate(
        session=session, legacy_outcome=Outcome.EQUIVALENT.value, candidate_receipt=not_eq,
    )
    assert error_kind == "DECISIVE_OUTCOME_DISAGREEMENT"
    assert reconciled.outcome is Outcome.ERROR


#: MIPS64 の側（Phase 4-B の入口条件だった architecture）。
_MIPS64 = "MIPS:BE:64:64-32addr"


def _mips64_production(case_id, left, right):
    from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check

    return run_production_check(case_id, left, right, left_architecture=_MIPS64, debug=True)


def _attempt_phases(result):
    return [attempt.get("phase") for attempt in (result.get("debug_trace") or {}).get("attempts") or ()]


def test_mips64_sat_with_a_committed_witness_ends_through_the_normal_gate():
    """MIPS64 の P0 の SAT（安全な counterexample を commit、blocker 無し）は NOT_EQ で、再試行の attempt は無い。"""

    from scripts.function_tracer_pcode.core import Expression
    from scripts.function_tracer_pcode.tests.unit.test_unpaired_input_sat_gate import _param, _side

    result = _mips64_production(
        "p184-mips64-not-eq",
        _side("f", _param()),
        _side("g", Expression.binary_op("INT_ADD", _param(), Expression.constant(1, 4))),
    )
    assert result["final_outcome"] == "NOT_EQ"
    assert _attempt_phases(result) == ["P0_BASE"], _attempt_phases(result)


def test_mips64_sat_without_a_commit_is_unknown():
    """MIPS64 の SAT でも、gate が NOT_EQ を確定させない（commit が無い）ときは UNKNOWN のまま。"""

    from scripts.function_tracer_pcode.tests.unit.test_unpaired_input_sat_gate import _UNPAIRED_CASES, _side

    left, right = _UNPAIRED_CASES["stack_input"]()
    result = _mips64_production("p184-mips64-unknown", _side("f", left), _side("g", right))
    assert result["final_outcome"] == "UNKNOWN"
    assert "P4B_MIPS64_SPURIOUS" not in _attempt_phases(result)
