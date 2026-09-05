"""Phase 6b-1 (#82): BranchCheckContext の builder と、check() に残した generation increment の条件を固定する。"""

import ast
import inspect
from types import SimpleNamespace
from unittest.mock import patch

import pytest

from scripts.function_tracer_pcode.checker import checker as checker_module
from scripts.function_tracer_pcode.checker.branch_context import BranchCheckContext, build_branch_check_context
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.core.render_smt import UnknownSmtExtensionWidthError
from scripts.function_tracer_pcode.proof.call_effect.preflight import CallProofDecisionMode
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


class _Strategy:
    pass


def _build(**over):
    kw = dict(strategy=_Strategy(), replan_plan=None, call_proof_generation=3, active_comparison_generation=None,
              active_comparison_session_id=None, active_call_proof_branch_id=None,
              decision_mode=CallProofDecisionMode.PREFLIGHT_PROJECTION, production_branch_authority_lease=None,
              session_id_factory=lambda: "fresh-session")
    kw.update(over)
    return build_branch_check_context(**kw)


def test_without_replan_plan_falls_back_to_generation_uuid_and_strategy_class_name():
    ctx = _build()
    assert ctx.generation == 3 and ctx.comparison_session_id == "fresh-session" and ctx.branch_id == "_Strategy"
    assert ctx.replan_plan is None and ctx.decision_mode is CallProofDecisionMode.PREFLIGHT_PROJECTION


def test_without_replan_plan_prefers_the_active_stage_runner_values():
    lease = object()
    ctx = _build(active_comparison_generation=9, active_comparison_session_id="S", active_call_proof_branch_id="S_PAIRWISE",
                 production_branch_authority_lease=lease)
    assert (ctx.generation, ctx.comparison_session_id, ctx.branch_id) == (9, "S", "S_PAIRWISE")
    assert ctx.production_branch_authority_lease is lease


def test_replan_plan_wins_over_active_values_and_the_counter():
    plan = SimpleNamespace(frame_generation=7, comparison_session_id="R", branch_id="S_MONOLITHIC_FALLBACK")
    ctx = _build(replan_plan=plan, active_comparison_generation=1, active_comparison_session_id="ignored", active_call_proof_branch_id="ignored")
    assert (ctx.generation, ctx.comparison_session_id, ctx.branch_id) == (7, "R", "S_MONOLITHIC_FALLBACK")
    assert ctx.replan_plan is plan


def test_context_is_frozen():
    ctx = _build()
    with pytest.raises(Exception):
        ctx.generation = 99  # type: ignore[misc]


def _checker():
    return EquivalenceChecker(strategy="pairwise", timeout=5, monolithic_timeout=5)


def _run_check_until_first_collaborator(checker, analysis):
    """A 段の直後（try 内の最初の collaborator 呼び出し）で停止させ、error 経路で返す。"""
    def reject(*_a, **_k):
        raise UnknownSmtExtensionWidthError(operator="INT_ZEXT", operand_bits=32)
    with patch.object(checker, "_call_effect_shadow_manifest", reject):
        return checker.check(analysis, analysis)


def test_generation_increments_only_when_no_replan_plan_is_active():
    analysis = create_mock_analysis("f", [])
    checker = _checker()
    before = checker._call_proof_generation
    _run_check_until_first_collaborator(checker, analysis)
    assert checker._call_proof_generation == before + 1
    checker._active_pair_replan_plan = SimpleNamespace(frame_generation=5, comparison_session_id="R", branch_id="S_PAIRWISE")
    try:
        _run_check_until_first_collaborator(checker, analysis)
    finally:
        del checker._active_pair_replan_plan
    assert checker._call_proof_generation == before + 1  # replan 中は increment しない


def test_check_reads_the_lease_and_active_values_through_the_context_builder():
    analysis = create_mock_analysis("f", [])
    checker = _checker()
    lease = object()
    checker._active_production_branch_authority_lease = lease
    checker._active_comparison_session_id = "S-active"
    captured = {}
    real = checker_module.build_branch_check_context

    def spy(**kw):
        ctx = real(**kw)
        captured["ctx"] = ctx
        return ctx

    try:
        with patch.object(checker_module, "build_branch_check_context", spy):
            _run_check_until_first_collaborator(checker, analysis)
    finally:
        del checker._active_production_branch_authority_lease
        del checker._active_comparison_session_id
    ctx = captured["ctx"]
    assert isinstance(ctx, BranchCheckContext)
    assert ctx.production_branch_authority_lease is lease
    assert ctx.comparison_session_id == "S-active"
    assert ctx.generation == checker._call_proof_generation


def test_check_source_keeps_the_increment_inside_the_no_replan_branch_only():
    src = inspect.getsource(EquivalenceChecker.check)
    tree = ast.parse("class _C:\n" + "\n".join("    " + l for l in src.splitlines()))
    fn = tree.body[0].body[0]
    increments = [n for n in ast.walk(fn) if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Attribute) and n.target.attr == "_call_proof_generation"]
    assert len(increments) == 1
    guards = [n for n in ast.walk(fn) if isinstance(n, ast.If) and "replan_plan is None" in ast.unparse(n.test)
              and any(isinstance(b, ast.AugAssign) for b in n.body)]
    assert len(guards) == 1 and not guards[0].orelse
    assert "uuid4" not in src and "_active_comparison_generation" in src  # 読み取りは builder 呼び出しの引数としてのみ
    assert src.count("_active_production_branch_authority_lease") == 1
