"""Branch check context of :meth:`EquivalenceChecker.check` (Phase 6b-1 #82, relocated in Phase 7-2 #97).

canonical path は ``proof.obligations.branch_context``。checker 配下の旧 path の同名 module は一時的な re-export shim。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Optional
from uuid import uuid4

from scripts.function_tracer_pcode.proof.call_effect.preflight import CallProofDecisionMode


@dataclass(frozen=True)
class BranchCheckContext:
    """One ``check()`` invocation's branch context.

    The stage runner (``proof.obligations.stage_runner.execute_branch``) builds this object with
    :func:`build_branch_check_context` from the values it issued (session id, generation, branch id,
    production branch authority lease) and the replan plan, and passes it explicitly to
    ``EquivalenceChecker.check(..., branch_context=...)`` (Phase 6c, #93).  The legacy handoff through
    the checker's ``_active_*`` attributes has been removed.  A direct ``check()`` call without a
    context builds a direct-checker context instead (fresh session id, strategy-class branch id, no
    lease).  The builder never mutates the checker: the ``_call_proof_generation`` increment stays in
    ``check()``.
    """

    strategy: Any
    replan_plan: Optional[Any]
    generation: int
    comparison_session_id: str
    branch_id: str
    decision_mode: CallProofDecisionMode
    production_branch_authority_lease: Optional[Any]


def build_branch_check_context(
    *,
    strategy: Any,
    replan_plan: Optional[Any],
    call_proof_generation: int,
    active_comparison_generation: Optional[Any],
    active_comparison_session_id: Optional[Any],
    active_call_proof_branch_id: Optional[Any],
    decision_mode: CallProofDecisionMode,
    production_branch_authority_lease: Optional[Any],
    session_id_factory: Callable[[], str] = lambda: uuid4().hex,
) -> BranchCheckContext:
    """旧 ``check()`` A 段と同じ規則で文脈を組み立てる（純関数）。

    ``replan_plan`` が無い場合: generation は active 値 or 呼び出し側が increment 済みの
    ``call_proof_generation``、session id は active 値 or 新規 uuid、branch id は active 値 or strategy の
    class 名。``replan_plan`` がある場合はその frame_generation / comparison_session_id / branch_id。
    """
    if replan_plan is None:
        generation = int(active_comparison_generation or call_proof_generation)
        comparison_session_id = str(active_comparison_session_id or session_id_factory())
        branch_id = str(active_call_proof_branch_id or strategy.__class__.__name__)
    else:
        generation = int(replan_plan.frame_generation)
        comparison_session_id = str(replan_plan.comparison_session_id)
        branch_id = str(replan_plan.branch_id)
    return BranchCheckContext(
        strategy=strategy,
        replan_plan=replan_plan,
        generation=generation,
        comparison_session_id=comparison_session_id,
        branch_id=branch_id,
        decision_mode=decision_mode,
        production_branch_authority_lease=production_branch_authority_lease,
    )
