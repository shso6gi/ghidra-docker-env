# -*- coding: utf-8 -*-
"""plan v4 PR-C: seed の無い解析の被覆の gap / inconclusive を、``return_coverage`` domain の cause にする。

* domain: 2 つの sealed reason（``return_coverage_gap`` / ``return_coverage_inconclusive``）は durable な
  registry・pilot の typed cause・Phase 7 manifest の site に載り、identity scope は UNARY、効果は
  ``blocks_equivalence``。signal は domain の外の reason を受け付けない。encoder は同じ関数・reason の
  再観測を 1 つの cause にする。
* producer（``_observe_seedless_return_coverage_blocker``）: cause を出すのは seed の無い解析の gap /
  inconclusive だけ。seed のある解析（outcome partition の段が cause を出す）・covered・完了の証明が
  inconclusive を解消した場合は出さない。
* 経路: gate（``_collect_return_coverage_unsafety_reasons``）は outcome partition が決めなかった側の判定を
  producer へ渡す。

最終判定（ERROR でなく UNKNOWN）は ``test_stack_protector_conditions_kept.py`` の production の行列が固定する。
"""

from __future__ import annotations

from types import SimpleNamespace
from typing import Any, List

import pytest

from scripts.function_tracer_pcode.authority.domains.return_coverage import (
    RETURN_COVERAGE_GAP_REASON_ID,
    RETURN_COVERAGE_IDENTITY_SCOPE,
    RETURN_COVERAGE_INCONCLUSIVE_REASON_ID,
    RETURN_COVERAGE_REASON_IDS,
    RETURN_COVERAGE_REASON_REGISTRY,
    RETURN_COVERAGE_SITE_ID,
    ReturnCoverageBlockerSignal,
    ReturnCoveragePilotEncoder,
)
from scripts.function_tracer_pcode.authority.contracts import IdentityScope
from scripts.function_tracer_pcode.proof.strategies.proof_gates import return_coverage as gate
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import ReturnCoverageCheckResult


_IDENTITY = ("function_identity_v1", "bin-f", None, "0x1000")


def _signal(reason_id: str = RETURN_COVERAGE_GAP_REASON_ID, identity: Any = _IDENTITY) -> ReturnCoverageBlockerSignal:
    return ReturnCoverageBlockerSignal(
        declared_reason_id=reason_id, function_identity=identity, coverage_check="gap",
        evidence_refs=("coverage_label:function1",),
    )


# ---------------------------------------------------------------------------
# domain
# ---------------------------------------------------------------------------


def test_the_two_reasons_are_sealed_unary_equivalence_blockers():
    definitions = {item.reason_id: item for item in RETURN_COVERAGE_REASON_REGISTRY.snapshot()}
    assert set(definitions) == {RETURN_COVERAGE_GAP_REASON_ID, RETURN_COVERAGE_INCONCLUSIVE_REASON_ID}
    for definition in definitions.values():
        assert definition.decision_effect == "blocks_equivalence"
        assert definition.domain == "return_coverage"
    assert RETURN_COVERAGE_IDENTITY_SCOPE is IdentityScope.UNARY


def test_the_reasons_are_registered_where_the_authority_reads_them():
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import PILOT_TYPED_CAUSE_KINDS
    from scripts.function_tracer_pcode.authority.process.supervisor import PROCESS_DURABLE_REASON_REGISTRY

    for reason_id in RETURN_COVERAGE_REASON_IDS:
        assert reason_id in PILOT_TYPED_CAUSE_KINDS
        assert PROCESS_DURABLE_REASON_REGISTRY.get(reason_id).domain == "return_coverage"


def test_the_producer_site_is_in_the_tracked_manifest_with_both_reasons():
    import json
    from pathlib import Path

    manifest = json.loads(
        (Path(__file__).resolve().parents[4] / "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json").read_text()
    )
    (site,) = [item for item in manifest["sites"] if item["producer_site_manifest_id"] == RETURN_COVERAGE_SITE_ID]
    assert site["enclosing_function"] == "_observe_seedless_return_coverage_blocker"
    assert site["path"].endswith("proof/strategies/proof_gates/return_coverage.py")
    assert sorted(
        reason for slot in site["expected_cause_slots"] for reason in slot["allowed_reason_ids"]
    ) == sorted(RETURN_COVERAGE_REASON_IDS)
    assert {slot["expected_identity_scope"] for slot in site["expected_cause_slots"]} == {"UNARY"}


def test_a_signal_refuses_a_reason_the_domain_does_not_own():
    with pytest.raises(ValueError):
        _signal("outcome_cfg_reachability_unproven")
    with pytest.raises(TypeError):
        ReturnCoverageBlockerSignal(
            declared_reason_id=RETURN_COVERAGE_GAP_REASON_ID, function_identity=_IDENTITY, coverage_check="",
        )


class _Session:
    def __init__(self) -> None:
        self.domain_signal_state = {}
        self.identity = SimpleNamespace(
            result_occurrence_id="occ-1", source_snapshot_fingerprint="fp", execution_identity_digest="d" * 64,
        )


def test_the_encoder_observes_one_cause_per_function_and_reason():
    encoder = ReturnCoveragePilotEncoder()
    session = _Session()

    first = encoder(session, _signal())
    assert len(first) == 1
    encoder.commit_emitted_signal(session, _signal(), first)

    assert encoder.has_observed(session, _signal())
    assert encoder(session, _signal()) == ()
    # 別の reason・別の関数は別の cause。
    assert not encoder.has_observed(session, _signal(RETURN_COVERAGE_INCONCLUSIVE_REASON_ID))
    assert len(encoder(session, _signal(RETURN_COVERAGE_INCONCLUSIVE_REASON_ID))) == 1
    assert len(encoder(session, _signal(identity=("function_identity_v1", "bin-g", None, "0x2000")))) == 1


def test_the_cause_carries_the_domain_reason_and_unary_scope():
    authority = ReturnCoveragePilotEncoder().authority_for_signal(_Session(), _signal())
    occurrence = authority.occurrence
    assert occurrence.reason_id == RETURN_COVERAGE_GAP_REASON_ID
    assert occurrence.identity_scope is IdentityScope.UNARY


# ---------------------------------------------------------------------------
# producer の条件
# ---------------------------------------------------------------------------


class _Gate:
    """``_observe_seedless_return_coverage_blocker`` が strategy から読む面だけ。"""

    def __init__(self, *, discharged: bool = False) -> None:
        self.discharged = discharged
        self.checked: List[str] = []

    def _make_blocking_unsafety_unknown_reason(self, reason, _analysis1, _analysis2, *, stage):
        self.checked.append(reason)
        return SimpleNamespace(reason=reason, stage=stage)

    def _return_coverage_proof_is_complete(self, _record, _analysis1, _analysis2):
        return self.discharged


def _analysis(*, seeded: bool) -> Any:
    return SimpleNamespace(
        outcome_seed=object() if seeded else None,
        outcome_function_identity=lambda: _IDENTITY,
    )


@pytest.fixture
def emitted(monkeypatch):
    from scripts.function_tracer_pcode.authority.lifecycle import production_signals

    signals: List[Any] = []

    def emit(signal, *, producer_site_manifest_id=None):
        assert producer_site_manifest_id == RETURN_COVERAGE_SITE_ID
        signals.append(signal)
        return 1

    monkeypatch.setattr(production_signals, "emit_return_coverage_signal", emit)
    return signals


def _observe(strategy, analysis, result) -> None:
    gate._observe_seedless_return_coverage_blocker(strategy, "function1", analysis, result, analysis, analysis)


@pytest.mark.parametrize(
    "result, reason_id",
    (
        (ReturnCoverageCheckResult(status="gap"), RETURN_COVERAGE_GAP_REASON_ID),
        (ReturnCoverageCheckResult(status="inconclusive", inconclusive_cause="expression_translation_incomplete"),
         RETURN_COVERAGE_INCONCLUSIVE_REASON_ID),
    ),
    ids=("gap", "inconclusive"),
)
def test_a_seedless_gap_or_inconclusive_verdict_becomes_a_cause(emitted, result, reason_id):
    _observe(_Gate(), _analysis(seeded=False), result)

    (signal,) = emitted
    assert signal.declared_reason_id == reason_id
    assert signal.function_identity == _IDENTITY
    assert signal.coverage_check == (result.inconclusive_cause or result.status)


@pytest.mark.parametrize("status", ("gap", "inconclusive"))
def test_a_seeded_analysis_leaves_the_cause_to_the_outcome_partition(emitted, status):
    _observe(_Gate(), _analysis(seeded=True), ReturnCoverageCheckResult(status=status))
    assert emitted == []


def test_a_covered_verdict_is_not_a_cause(emitted):
    _observe(_Gate(), _analysis(seeded=False), ReturnCoverageCheckResult(status="covered"))
    assert emitted == []


def test_an_inconclusive_verdict_discharged_by_a_completed_coverage_proof_is_not_a_cause(emitted):
    strategy = _Gate(discharged=True)
    _observe(strategy, _analysis(seeded=False), ReturnCoverageCheckResult(status="inconclusive"))

    assert emitted == []
    assert strategy.checked == ["function1:return_coverage_inconclusive"]


def test_the_gate_hands_only_unpartitioned_verdicts_to_the_producer(monkeypatch):
    """outcome partition が決めた側（covered / inconclusive の label）は producer へ渡らない。"""

    observed: List[Any] = []
    monkeypatch.setattr(
        gate, "_observe_seedless_return_coverage_blocker",
        lambda _self, label, analysis, result, *_args: observed.append((label, result.status)),
    )

    class _Strategy:
        enable_completed_recovery_proofs = False

        def _outcome_partition_covered_labels(self, *_args):
            return {"function1"}

        def _outcome_partition_inconclusive_labels(self, *_args):
            return set()

        def _check_return_case_coverage_gap(self, *_args):
            return ReturnCoverageCheckResult(status="gap")

        def _summary_return_candidate_blocker_reason_ids(self, _analysis):
            return ()

        def _debug_print(self, *_args):
            return None

        def _analysis_requires_completed_return_coverage_proof(self, *_args, **_kwargs):
            return None

    analysis1, analysis2 = (
        SimpleNamespace(has_expansion_budget_truncation=lambda: False) for _ in range(2)
    )
    reasons = gate._impl__collect_return_coverage_unsafety_reasons(
        _Strategy(), {}, [], [], None, None, analysis1, analysis2,
    )

    assert observed == [("function2", "gap")]
    assert reasons == ["function2:return_coverage_gap"]
