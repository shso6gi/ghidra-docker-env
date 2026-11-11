"""Issue #297: 実 binary で、本物の promotion（patch しない）を通す opt-in の回帰 test。

``RUN_PYGHIDRA_REGRESSIONS=1`` で、runner が作った EqBench の binary（``targets/EqBench``）がある
ときだけ走る（CI では skip。Ghidra 無しの規則の test は ``test_recurrence_return_binding.py``）。

- UnchLoop の Eq ``new``（``c = 0; …; return c + 1``）の O0: RETURN は ``c + 1`` で accumulator PHI に
  結び付かない。修正前は promotion が成立して偽 NOT_EQ の根拠になった。修正後は拒否され、元の解析・
  proposal・process 全体の artifact cache は変わらず、pair は ABORTED で元の解析を返す。
- loop2 の Eq ``newV``（``return`` が accumulator そのもの）の O0: promotion が成立し、artifact の
  検証の証拠に ``return_binding`` の subproof が入る。写しの ``free`` な入力は引数の番号を持つ。
- 別の解析の証拠を差し替えた proposal は、本物の promotion で拒否される（EV）。
"""

from __future__ import annotations

import copy
import os
from dataclasses import replace
from pathlib import Path

import pytest

pytestmark = pytest.mark.skipif(
    os.environ.get("RUN_PYGHIDRA_REGRESSIONS") != "1",
    reason="real PyGhidra promotion regression is opt-in; set RUN_PYGHIDRA_REGRESSIONS=1",
)

REPO_ROOT = Path(__file__).resolve().parents[4]
BENCHMARKS = REPO_ROOT / "targets" / "EqBench" / "benchmarks"
UNCHLOOP_NEW_O0 = BENCHMARKS / "CLEVER" / "UnchLoop" / "Eq" / "source" / "new-arm64-clang-O0"
LOOP2_O0 = BENCHMARKS / "REVE" / "loop2" / "Eq" / "source" / "newV-arm64-clang-O0"


@pytest.fixture(scope="module")
def analyses(tmp_path_factory):
    for binary in (UNCHLOOP_NEW_O0, LOOP2_O0):
        if not binary.is_file():
            pytest.skip(f"fixture binary not found: {binary}")
    pyghidra = pytest.importorskip("pyghidra")
    pyghidra.start()
    from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        activate_process_worker_execution_authority_deployment,
    )

    activate_process_worker_execution_authority_deployment(
        key_id="issue297-regression", key=b"issue297-regression-key-0123456789"[:32],
        key_source_id=str(tmp_path_factory.mktemp("authority")),
    )
    out = {}
    project_dir = tmp_path_factory.mktemp("ghidra")
    with pyghidra.open_project(str(project_dir), "Issue297", create=True) as project:
        for name, binary, function in (("unchloop", UNCHLOOP_NEW_O0, "foo"), ("loop2", LOOP2_O0, "f")):
            with pyghidra.program_loader().project(project).source(str(binary)).name(binary.name).load() as loaded:
                program = loaded.getPrimaryDomainObject()
                pyghidra.analyze(program)
                analysis = ReturnAnalyzer(program, debug=False, binary_id=f"{name}-{binary.name}") \
                    .analyze_function_by_name(function)
                out[name] = analysis
    return out


def _counted_proposal(analysis):
    proposals = [
        item for item in analysis.quarantined_recurrence_proposals
        if item.pattern_kind == "counted_scalar_loop_summary"
    ]
    assert len(proposals) == 1, analysis.quarantined_recurrence_proposals
    return proposals[0]


def test_unbound_return_summary_is_rejected_without_side_effects(analyses):
    from scripts.function_tracer_pcode.proof import recurrence_promotion as promotion
    from scripts.function_tracer_pcode.proof.obligations.runtime import GLOBAL_VALIDATED_UNARY_ARTIFACT_CACHE
    from scripts.function_tracer_pcode.proof.recurrence_promotion import (
        PairPromotionState,
        PairRecurrencePromotionAuthority,
    )

    analysis = analyses["unchloop"]
    proposal = _counted_proposal(analysis)
    before_returns = copy.deepcopy([item.to_dict() for item in analysis.returns])
    before_proposals = tuple(analysis.quarantined_recurrence_proposals)
    before_cache = len(GLOBAL_VALIDATED_UNARY_ARTIFACT_CACHE._entries)

    with pytest.raises(ValueError, match="recurrence return binding unproven") as info:
        promotion._prepare_side_for_proposal(analysis, "left", proposal)
    assert "R:blocked_by:INT_ADD/4" in str(info.value)

    assert [item.to_dict() for item in analysis.returns] == before_returns
    assert tuple(analysis.quarantined_recurrence_proposals) == before_proposals
    assert len(GLOBAL_VALIDATED_UNARY_ARTIFACT_CACHE._entries) == before_cache

    peer = analyses["loop2"]
    authority = PairRecurrencePromotionAuthority(
        "issue297-session", "branch-0",
        ((proposal.digest,), (_counted_proposal(peer).digest,)),
    )
    left, right, _runtime, attempt = promotion.promote_recurrence_pair(analysis, peer, authority)
    assert attempt.state == PairPromotionState.ABORTED
    assert "recurrence return binding unproven" in attempt.failure
    assert left is analysis and right is peer


def test_accumulator_return_summary_is_promoted_with_a_return_binding_subproof(analyses):
    from scripts.function_tracer_pcode.proof import recurrence_promotion as promotion

    analysis = analyses["loop2"]
    proposal = _counted_proposal(analysis)
    assert getattr(proposal, "return_binding_evidence", None) is not None
    side = promotion._prepare_side_for_proposal(analysis, "left", proposal)
    validation = side.entry.artifact.payload["recurrence_validation_evidence"]
    kinds = [item["proof_kind"] for item in validation["subproofs"]]
    assert kinds[-1] == "return_binding"
    assert validation["schema_version"] == "recurrence_validation_evidence_v3"
    rules = [item["proposition_key"] for item in validation["subproofs"] if item["proof_kind"] == "return_binding"]
    from scripts.function_tracer_pcode.core.recurrence_contracts import RETURN_BINDING_RULES

    assert tuple(rules[0][4]) == RETURN_BINDING_RULES
    snapshot = proposal.return_binding_evidence.snapshot
    parameters = {item.parameter_index for op in snapshot.ops for item in op.inputs if item.kind == "free"}
    assert 0 in parameters  # limit `n` は引数 0
    # 引数の表は Ghidra の prototype の置き場所で、写しの引数の入力はその置き場所と一致する
    fact = snapshot.parameter(0)
    assert fact is not None and len(fact.pieces) == 1
    inputs = {(item.storage, item.size) for op in snapshot.ops for item in op.inputs
              if item.kind == "free" and item.parameter_index == 0}
    assert inputs == {(fact.pieces[0][:2], fact.size)}


def test_evidence_of_another_analysis_is_rejected_by_the_real_promotion(analyses):
    from scripts.function_tracer_pcode.proof import recurrence_promotion as promotion

    loop2, unchloop = analyses["loop2"], analyses["unchloop"]
    swapped = replace(
        _counted_proposal(loop2), return_binding_evidence=_counted_proposal(unchloop).return_binding_evidence,
    )
    with pytest.raises(ValueError, match="recurrence return binding unproven") as info:
        promotion._prepare_side_for_proposal(loop2, "left", swapped)
    assert "EV:" in str(info.value)
