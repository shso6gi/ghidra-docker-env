# -*- coding: utf-8 -*-
"""Issue #167: MIPS64 Phase 4-B の ABI retry の UNSAT は最終 EQ authority に届かない。

Phase 4-B（``checker/abi_retry.py``）は SAT model・usage hint・宣言型から
``(= wide (ext (extract narrow)))`` を足して solver を直接呼ぶ。この入力仮定は
最終 InputCorrespondence が含意したものではない。本 PR は Phase 4-B の production
code を変えないので、その UNSAT が最終 EQUIVALENT にならないことをここで固定する
（v5 F-8 / §4.11-6）:

1. retry は legacy の ``is_equivalent=True`` を返すが、comparison receipt も
   prepared dispatch frame も持たない。
2. 非同一関数の EQ closure を発行する経路は ``proof/obligations/stage_runner.py``
   の ``issue_pending_eq_closure_authority`` だけで、そこは dispatch frame の信頼済み
   comparison receipt を要求する。retry の module はその経路に触れない。
3. v2 の最終判定は EQ_CLOSURE receipt が無ければ EQUIVALENT を出さず、legacy EQ と
   候補 NOT_EQ の食い違いは ``DECISIVE_OUTCOME_DISAGREEMENT`` の ERROR になる。
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
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.checker.phases.handler import PhaseContext
from scripts.function_tracer_pcode.core import Expression, ExpressionType, ReturnInfo
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
from scripts.function_tracer_pcode.tests.unit._issue125_support import (
    SAT_SAFETY_CONTRACT,
    SAT_SAFETY_PROOF_KIND,
    LifecycleHarness,
    sat_safety_cause_inputs,
)


PACKAGE = Path(__file__).resolve().parents[2]


def _context() -> PhaseContext:
    x_wide = Expression(ExpressionType.PARAMETER, name="param_1", value=0, size=8)
    x_narrow = Expression(ExpressionType.PARAMETER, name="param_1", value=0, size=4)
    return PhaseContext(
        program1=Mock(),
        program2=Mock(),
        function_name1="f",
        function_name2="f",
        binary1_name="mips64-bin",
        binary2_name="arm64-bin",
        decompile_timeout=60,
        save_formula=True,
        type_fix_result=TypeFixResult(),
        original_signature1=None,
        original_signature2=None,
        analysis1=create_mock_analysis(
            "f",
            parameters=[{"name": "param_1", "data_type": "long", "size": 8, "index": 0}],
            returns=[ReturnInfo(address="0x1000", conditions=[], value=Expression(
                ExpressionType.BINARY_OP, operator="SUBPIECE",
                operands=[x_wide, Expression(ExpressionType.CONSTANT, value=0, size=8)], size=4,
            ))],
        ),
        analysis2=create_mock_analysis(
            "f",
            parameters=[{"name": "param_1", "data_type": "int", "size": 4, "index": 0}],
            returns=[ReturnInfo(address="0x2000", conditions=[], value=x_narrow)],
        ),
    )


class _UnsatRunner:
    def run_parallel(self, _query, **_kwargs):
        return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT, elapsed_time=0.01)])

    run_sequential = run_parallel


def test_abi_retry_unsat_is_only_a_legacy_verdict_without_comparison_authority():
    checker = EquivalenceChecker(debug=False)
    checker.solver_runner = _UnsatRunner()

    result = checker._retry_with_abi_constraints(_context(), {"param_1_1": ("signed", 32)}, retry_count=1)

    assert result.is_equivalent is True
    assert "sign_extend" in result.smt_formula
    assert getattr(result, "comparison_execution_receipt", None) is None
    assert getattr(result, "_prepared_dispatch_frame", None) is None


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

    for module in ("checker/abi_retry.py", "checker/arch/mips64.py"):
        tree = ast.parse((PACKAGE / module).read_text(encoding="utf-8"))
        names = set(_referenced_names(tree))
        assert not names & {
            "issue_pending_eq_closure_authority",
            "PendingEqClosureAuthority",
            "EQ_CLOSURE",
            "PreparedDispatchFrame",
            "issue_builtin_comparison_receipt",
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
        assert receipt.outcome is not Outcome.EQUIVALENT
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
