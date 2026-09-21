# -*- coding: utf-8 -*-
"""Tests for solver-proven rewrite fallback in pairwise execution."""

import hashlib
import sys
from pathlib import Path


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult, ReturnCase
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    solve_query_twostage,
)
from scripts.function_tracer_pcode.proof.strategies import (
    pairwise_solver_proven_rewrite as rewrite_module,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_solver_proven_rewrite import (
    _build_rewrite_proof_query,
    _build_rewrite_candidate,
    try_solver_proven_rewrite_equivalence,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    build_unknown_recovery_actions,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.proof.call_effect.preflight import (
    projection_binding_evidence_from_query,
)
from scripts.function_tracer_pcode.semantics.normalize import NormalizationSettings
from scripts.function_tracer_pcode.proof.obligations import (
    SolverQueryExecutionReceipt,
    StructuralEqualityReceipt,
)
from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType, ReturnInfo
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.tests.unit._publication import published


def _unsat_query_result(query: str, pair_id: str, stage: str) -> QueryResult:
    parallel_result = ParallelResult(
        results=[SolverResult("fake", SolverStatus.UNSAT)]
    )
    result = QueryResult(
        is_equivalent=True,
        solver_results=parallel_result,
    )
    result.last_query = query
    result.solver_query_execution_receipt = (
        SolverQueryExecutionReceipt.from_execution(
            query=query,
            query_label=pair_id,
            proof_stage=stage,
            parallel_result=parallel_result,
            solver_identity=("unit", "fake", ("fake",)),
            timeout_budget=5.0,
            use_hard_timeout=False,
        )
    )
    return result


def _param(name: str) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=8)


def _const(value: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=8)


def _cond(operator: str, left: Expression, right: Expression) -> Condition:
    return Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator=operator,
            operands=[left, right],
            size=1,
        )
    )


def _case(index: int, value_expr: Expression) -> ReturnCase:
    return ReturnCase(
        index=index,
        conditions=[_cond("INT_NOTEQUAL", _param("param_2"), _const(0))],
        value_expr=value_expr,
        return_info=ReturnInfo(address=f"0x10{index}", value=value_expr),
        return_type="long",
    )


def _base_ctx():
    return {
        "header_lines": [
            "(declare-fun param_1 () (_ BitVec 64))",
            "(declare-fun param_2 () (_ BitVec 64))",
        ],
        "return_size1": 64,
        "return_size2": 64,
    }


def test_solver_proven_rewrite_equivalence_proves_and_retries(monkeypatch):
    param1 = _param("param_1")
    param2 = _param("param_2")
    half_b = Expression.binary_op("INT_SDIV", param2, _const(2))
    canonical = Expression.binary_op("INT_ADD", param1, half_b)
    commuted = Expression.binary_op("INT_ADD", half_b, param1)
    nontrivial_rewrite = Expression.binary_op("INT_SUB", canonical, _const(0))

    case1 = _case(0, canonical)
    case2 = _case(1, commuted)

    def fake_candidate(expr, settings):
        if expr is commuted:
            return nontrivial_rewrite
        return expr

    monkeypatch.setattr(rewrite_module, "_build_rewrite_candidate", fake_candidate)

    class FakeStrategy:
        def __init__(self):
            self.stages = []

        def _solve_query_internal(self, query, pair_id, stage="full", use_hard_timeout=False):
            self.stages.append((stage, use_hard_timeout, query))
            if stage == "rewrite-proof-2":
                assert "(assert (not (= " in query
                return _unsat_query_result(query, pair_id, stage)
            if stage == "rewrite-ineq":
                assert use_hard_timeout is True
                return _unsat_query_result(query, pair_id, stage)
            raise AssertionError(f"unexpected stage: {stage}")

    strategy = FakeStrategy()
    result = try_solver_proven_rewrite_equivalence(
        strategy,
        _base_ctx(),
        case1,
        case2,
        lambda obj: published(obj).to_smt(),
        lambda obj: published(obj).to_smt(),
        "(0,0)",
    )

    assert result.is_equivalent is True
    assert result.pair_stage == "rewrite-ineq"
    assert [stage for stage, _, _ in strategy.stages] == ["rewrite-proof-2", "rewrite-ineq"]


def test_solver_proven_rewrite_returns_after_structural_match(monkeypatch):
    param1 = _param("param_1")
    param2 = _param("param_2")
    half_b = Expression.binary_op("INT_SDIV", param2, _const(2))
    canonical = Expression.binary_op("INT_ADD", param1, half_b)
    commuted = Expression.binary_op("INT_ADD", half_b, param1)

    case1 = _case(0, canonical)
    case2 = _case(1, commuted)

    def fake_candidate(expr, settings):
        if expr is commuted:
            return canonical
        return expr

    monkeypatch.setattr(rewrite_module, "_build_rewrite_candidate", fake_candidate)

    class FakeStrategy:
        debug = False

        def __init__(self):
            self.stages = []

        def _solve_query_internal(self, query, pair_id, stage="full", use_hard_timeout=False):
            self.stages.append(stage)
            if stage == "rewrite-proof-2":
                assert "(assert (not (= " in query
                return _unsat_query_result(query, pair_id, stage)
            raise AssertionError(f"unexpected stage: {stage}")

    strategy = FakeStrategy()
    result = try_solver_proven_rewrite_equivalence(
        strategy,
        _base_ctx(),
        case1,
        case2,
        lambda obj: published(obj).to_smt(),
        lambda obj: published(obj).to_smt(),
        "(0,0)",
    )

    assert result.is_equivalent is True
    assert result.pair_stage == "rewrite-structural"
    assert type(result.structural_equality_receipt) is StructuralEqualityReceipt
    assert result.structural_equality_receipt.validates(
        expected_query_label="(0,0)"
    )
    assert strategy.stages == ["rewrite-proof-2"]


def test_structural_rewrite_executes_full_query_for_projection_binding(monkeypatch):
    param1 = _param("param_1")
    param2 = _param("param_2")
    half_b = Expression.binary_op("INT_SDIV", param2, _const(2))
    canonical = Expression.binary_op("INT_ADD", param1, half_b)
    commuted = Expression.binary_op("INT_ADD", half_b, param1)
    case1 = _case(0, canonical)
    case2 = _case(1, commuted)

    monkeypatch.setattr(
        rewrite_module,
        "_build_rewrite_candidate",
        lambda expr, settings: canonical if expr is commuted else expr,
    )
    assertion = "(assert true)"
    assertion_digest = hashlib.sha256(assertion.encode("utf-8")).hexdigest()
    binding_id = "a" * 64
    base_ctx = _base_ctx()
    base_ctx["call_projection_binding_ids_by_pair"] = {
        "(0,0)": (binding_id,),
    }
    base_ctx["call_projection_binding_digests_by_pair"] = {
        "(0,0)": {binding_id: assertion_digest},
    }
    base_ctx["call_projection_assertions_by_pair"] = {
        "(0,0)": (
            f"; call_projection_binding {binding_id} "
            f"assertion_sha256={assertion_digest}",
            assertion,
            f"; call_projection_binding_end {binding_id}",
        ),
    }

    class FakeStrategy:
        debug = False

        def __init__(self):
            self.stages = []

        def _solve_query_internal(self, query, pair_id, stage="full", use_hard_timeout=False):
            self.stages.append(stage)
            return _unsat_query_result(query, pair_id, stage)

    strategy = FakeStrategy()
    result = try_solver_proven_rewrite_equivalence(
        strategy,
        base_ctx,
        case1,
        case2,
        lambda obj: published(obj).to_smt(),
        lambda obj: published(obj).to_smt(),
        "(0,0)",
    )

    assert result.is_equivalent is True
    assert result.pair_stage == "rewrite-structural-projection"
    assert strategy.stages == ["rewrite-proof-2", "rewrite-structural-projection"]
    assert projection_binding_evidence_from_query(result.last_query) == {
        binding_id: assertion_digest,
    }
    assert len(result.structural_equality_receipt.supporting_solver_receipts) == 2


def test_solve_query_twostage_uses_solver_proven_rewrite_after_timeout():
    param1 = _param("param_1")
    param2 = _param("param_2")
    case1 = _case(0, Expression.binary_op("INT_ADD", param1, param2))
    case2 = _case(1, Expression.binary_op("INT_ADD", param2, param1))

    class FakeStrategy:
        def __init__(self):
            self.enable_solver_proven_rewrite_fallback = True
            self.enable_normalization_fallback = False
            self._active_normalization_stats = {
                "solver_proven_rewrite_attempts": 0,
                "solver_proven_rewrite_successes": 0,
                "solver_proven_rewrite_failures": 0,
            }
            self.calls = []

        def _build_condition_only_query(self, *args, **kwargs):
            return "conds"

        def _build_pair_query(self, *args, **kwargs):
            return "full"

        def _solve_query_internal(self, query, pair_id, stage="full", use_hard_timeout=False):
            self.calls.append((stage, query))
            if stage == "conds-only":
                return QueryResult(is_equivalent=False)
            if stage == "with-ineq":
                return QueryResult(is_equivalent=None)
            raise AssertionError(f"unexpected stage: {stage}")

        def _try_solver_proven_rewrite_equivalence(self, *args, **kwargs):
            result = QueryResult(is_equivalent=True)
            result.last_query = "rewritten"
            result.pair_stage = "rewrite-ineq"
            return result

        def _debug_print(self, message):
            return None

    strategy = FakeStrategy()
    result = solve_query_twostage(
        strategy,
        _base_ctx(),
        case1,
        case2,
        lambda obj: published(obj).to_smt(),
        lambda obj: published(obj).to_smt(),
        "(0,1)",
    )

    assert result.is_equivalent is True
    assert result.pair_stage == "rewrite-ineq"
    assert strategy._active_normalization_stats["solver_proven_rewrite_attempts"] == 1
    assert strategy._active_normalization_stats["solver_proven_rewrite_successes"] == 1


def test_solver_rewrite_no_change_carries_object_target_and_proof_id():
    param1 = _param("param_1")
    param2 = _param("param_2")
    case1 = _case(0, Expression.binary_op("INT_ADD", param1, param2))
    case2 = _case(1, Expression.binary_op("INT_ADD", param1, param2))
    target_key = (
        "solver_rewrite_candidate",
        ("pair", "(0,1)"),
        ("rewrite_stage", "rewrite_candidate_generation"),
        ("solver_rewrite_side", "left", ("function_ref", ("function", "B1", 0x1000))),
        ("solver_rewrite_side", "right", ("function_ref", ("function", "B2", 0x2000))),
    )

    class FakeStrategy:
        solver_proven_rewrite_settings = NormalizationSettings.safe()

        def _solver_rewrite_candidate_object_target_key(self, **kwargs):
            assert kwargs["pair_id"] == "(0,1)"
            return target_key

    result = try_solver_proven_rewrite_equivalence(
        FakeStrategy(),
        _base_ctx(),
        case1,
        case2,
        lambda obj: published(obj).to_smt(),
        lambda obj: published(obj).to_smt(),
        "(0,1)",
    )

    assert result.is_equivalent is None
    assert result.blocking_reason == "solver_proven_rewrite_no_change"
    assert result.evidence_kind == "pre_normalized_query"
    assert result.object_target_key == target_key

    record = make_unknown_reason(
        result.blocking_reason,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_refs=(result.pair_stage, result.blocking_detail),
        evidence_kind=result.evidence_kind,
        object_target_key=result.object_target_key,
        detail=result.blocking_detail,
    )
    actions = build_unknown_recovery_actions([record])
    assert record.proof_obligation_id is not None
    assert len(actions) == 1
    assert actions[0].proof_obligation_id == record.proof_obligation_id
    assert actions[0].proof_stage == "rewrite_candidate_generation"


def test_solver_rewrite_proof_failed_carries_object_target_to_both_actions(monkeypatch):
    param1 = _param("param_1")
    param2 = _param("param_2")
    half_b = Expression.binary_op("INT_SDIV", param2, _const(2))
    canonical = Expression.binary_op("INT_ADD", param1, half_b)
    commuted = Expression.binary_op("INT_ADD", half_b, param1)
    case1 = _case(0, commuted)
    case2 = _case(1, canonical)
    target_key = (
        "solver_rewrite_proof",
        ("pair", "(0,1)"),
        ("rewrite_side", "left"),
        ("rewrite_stage", "rewrite-proof-1"),
        ("solver_rewrite_side", "left", ("function_ref", ("function", "B1", 0x1000))),
        ("solver_rewrite_side", "right", ("function_ref", ("function", "B2", 0x2000))),
        ("original_expression", ("expression", ("binary", "INT_ADD"))),
        ("rewritten_expression", ("expression", ("binary", "INT_ADD"))),
    )

    def fake_candidate(expr, settings):
        if expr is commuted:
            return canonical
        return expr

    monkeypatch.setattr(rewrite_module, "_build_rewrite_candidate", fake_candidate)

    class FakeStrategy:
        solver_proven_rewrite_settings = NormalizationSettings.safe()

        def _solve_query_internal(self, query, pair_id, stage="full", use_hard_timeout=False):
            assert stage == "rewrite-proof-1"
            return QueryResult(is_equivalent=None)

        def _solver_rewrite_proof_object_target_key(self, **kwargs):
            assert kwargs["pair_id"] == "(0,1)"
            assert kwargs["rewrite_side"] == "left"
            assert kwargs["rewrite_label"] == "rewrite-proof-1"
            return target_key

    result = try_solver_proven_rewrite_equivalence(
        FakeStrategy(),
        _base_ctx(),
        case1,
        case2,
        lambda obj: published(obj).to_smt(),
        lambda obj: published(obj).to_smt(),
        "(0,1)",
    )

    assert result.is_equivalent is None
    assert result.blocking_reason == "solver_proven_rewrite_proof_failed"
    assert result.object_target_key == target_key

    record = make_unknown_reason(
        result.blocking_reason,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_refs=(result.pair_stage, result.blocking_detail),
        object_target_key=result.object_target_key,
        detail=result.blocking_detail,
    )
    actions = build_unknown_recovery_actions([record])
    assert record.proof_obligation_id is None
    assert len(actions) == 2
    assert {action.proof_stage for action in actions} == {
        "rewrite_proof_recheck",
        "solver_retry",
    }
    assert all(action.object_target_key == target_key for action in actions)
    assert all(action.proof_obligation_id is not None for action in actions)


def test_solve_query_twostage_propagates_solver_rewrite_object_target():
    param1 = _param("param_1")
    param2 = _param("param_2")
    case1 = _case(0, Expression.binary_op("INT_ADD", param1, param2))
    case2 = _case(1, Expression.binary_op("INT_ADD", param2, param1))
    target_key = ("solver_rewrite_candidate", ("pair", "(0,1)"))

    class FakeStrategy:
        def __init__(self):
            self.enable_solver_proven_rewrite_fallback = True
            self.enable_normalization_fallback = False
            self._active_normalization_stats = {
                "solver_proven_rewrite_attempts": 0,
                "solver_proven_rewrite_successes": 0,
                "solver_proven_rewrite_failures": 0,
            }

        def _build_condition_only_query(self, *args, **kwargs):
            return "conds"

        def _build_pair_query(self, *args, **kwargs):
            return "full"

        def _solve_query_internal(self, query, pair_id, stage="full", use_hard_timeout=False):
            if stage == "conds-only":
                return QueryResult(is_equivalent=False)
            if stage == "with-ineq":
                return QueryResult(is_equivalent=None)
            raise AssertionError(f"unexpected stage: {stage}")

        def _try_solver_proven_rewrite_equivalence(self, *args, **kwargs):
            result = QueryResult(is_equivalent=None)
            result.blocking_reason = "solver_proven_rewrite_no_change"
            result.blocking_detail = "solver-proven rewrite produced no candidate rewrite"
            result.evidence_kind = "pre_normalized_query"
            result.object_target_key = target_key
            result.pair_stage = "rewrite-no-change"
            return result

        def _debug_print(self, message):
            return None

    result = solve_query_twostage(
        FakeStrategy(),
        _base_ctx(),
        case1,
        case2,
        lambda obj: published(obj).to_smt(),
        lambda obj: published(obj).to_smt(),
        "(0,1)",
    )

    assert result.is_equivalent is None
    assert result.blocking_reason == "solver_proven_rewrite_no_change"
    assert result.evidence_kind == "pre_normalized_query"
    assert result.object_target_key == target_key


def test_build_rewrite_candidate_canonicalizes_commuted_add_for_solver():
    param1 = _param("param_1")
    param2 = _param("param_2")
    half_b = Expression.binary_op("INT_SDIV", param2, _const(2))
    canonical = Expression.binary_op("INT_ADD", param1, half_b)
    commuted = Expression.binary_op("INT_ADD", half_b, param1)

    rewritten_canonical = _build_rewrite_candidate(canonical, NormalizationSettings.safe())
    rewritten_commuted = _build_rewrite_candidate(commuted, NormalizationSettings.safe())

    assert published(rewritten_canonical).to_smt() == published(rewritten_commuted).to_smt()


def test_build_rewrite_candidate_collapses_division_remainder_expansion():
    a = _param("param_1")
    b = _param("param_2")
    quotient = Expression.binary_op("INT_SDIV", a, b)
    expanded = Expression.binary_op("INT_SUB", a, Expression.binary_op("INT_MULT", quotient, b))

    rewritten = _build_rewrite_candidate(expanded, NormalizationSettings.safe())

    assert rewritten.operator == "INT_SREM"
    assert [published(operand).to_smt() for operand in rewritten.operands] == [published(a).to_smt(), published(b).to_smt()]


def test_rewrite_proof_query_targets_minimal_changed_subexpression():
    param1 = _param("param_1")
    param2 = _param("param_2")
    half_b = Expression.binary_op("INT_SDIV", param2, _const(2))
    original = Expression.binary_op("INT_SDIV", Expression.binary_op("INT_ADD", param1, half_b), param2)
    rewritten = Expression.binary_op("INT_SDIV", Expression.binary_op("INT_ADD", half_b, param1), param2)
    case = _case(0, original)

    query = _build_rewrite_proof_query(
        _base_ctx(),
        case,
        lambda obj: published(obj).to_smt(),
        rewritten,
        "rewrite-proof-1",
    )

    assert "(assert (not (= (bvadd param_1" in query
    assert " (bvsdiv (bvadd " not in query
