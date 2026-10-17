# -*- coding: utf-8 -*-
"""plan v4 PR-C: seed の無い解析の被覆の gap / inconclusive を、``return_coverage`` domain の cause にする。

* domain: 2 つの sealed reason（``return_coverage_gap`` / ``return_coverage_inconclusive``）は durable な
  registry・pilot の typed cause・Phase 7 manifest の site に載り、identity scope は UNARY、効果は
  ``blocks_equivalence``。signal は domain の外の reason を受け付けない。encoder は同じ関数・reason の
  再観測を 1 つの cause にする。
* producer（``stage_runner._observe_unsealed_seedless_return_coverage``）: runner が raw pair の被覆の印で
  monolithic fallback を止めたときに、seed の無い側の印（gap / inconclusive）だけを cause にする。seed のある
  解析（outcome partition の段が cause を出す）・印の無い側は出さない。

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
from scripts.function_tracer_pcode.proof.obligations import stage_runner


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
    assert site["enclosing_function"] == "_observe_unsealed_seedless_return_coverage"
    assert site["path"].endswith("proof/obligations/stage_runner.py")
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


def _analysis(*, seeded: bool, notes=(), identity=_IDENTITY) -> Any:
    return SimpleNamespace(
        outcome_seed=object() if seeded else None,
        analysis_notes=list(notes),
        outcome_function_identity=lambda: identity,
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


@pytest.mark.parametrize(
    "note, reason_id",
    (
        ("return_case_coverage_gap", RETURN_COVERAGE_GAP_REASON_ID),
        ("return_case_coverage_inconclusive", RETURN_COVERAGE_INCONCLUSIVE_REASON_ID),
    ),
    ids=("gap", "inconclusive"),
)
def test_a_seedless_coverage_note_that_stopped_the_fallback_becomes_a_cause(emitted, note, reason_id):
    stage_runner._observe_unsealed_seedless_return_coverage(
        _analysis(seeded=False, notes=(note,)), _analysis(seeded=False, identity=("other",)),
    )

    (signal,) = emitted
    assert signal.declared_reason_id == reason_id
    assert signal.function_identity == _IDENTITY
    assert signal.coverage_check == note
    assert signal.evidence_refs == ("coverage_label:function1", "monolithic_fallback_skipped")


def test_both_sides_and_both_notes_are_observed(emitted):
    both = ("return_case_coverage_gap", "return_case_coverage_inconclusive")
    stage_runner._observe_unsealed_seedless_return_coverage(
        _analysis(seeded=False, notes=both), _analysis(seeded=False, notes=both[:1], identity=("right",)),
    )

    assert [(item.declared_reason_id, item.function_identity) for item in emitted] == [
        (RETURN_COVERAGE_GAP_REASON_ID, _IDENTITY),
        (RETURN_COVERAGE_INCONCLUSIVE_REASON_ID, _IDENTITY),
        (RETURN_COVERAGE_GAP_REASON_ID, ("right",)),
    ]


def test_a_seeded_analysis_leaves_the_cause_to_the_outcome_partition(emitted):
    stage_runner._observe_unsealed_seedless_return_coverage(
        _analysis(seeded=True, notes=("return_case_coverage_gap",)),
        _analysis(seeded=True, notes=("return_case_coverage_inconclusive",)),
    )
    assert emitted == []


def test_a_side_without_a_coverage_note_is_not_a_cause(emitted):
    stage_runner._observe_unsealed_seedless_return_coverage(
        _analysis(seeded=False, notes=("bounded_call_refinement",)), _analysis(seeded=False),
    )
    assert emitted == []


def test_the_runner_notes_are_the_registered_comparison_annotations():
    from scripts.function_tracer_pcode.proof.obligations.snapshot import COMPARISON_ANNOTATION_NOTES

    assert {note for note, _reason in stage_runner._SEEDLESS_COVERAGE_NOTE_REASONS} == set(COMPARISON_ANNOTATION_NOTES)
    assert tuple(reason for _note, reason in stage_runner._SEEDLESS_COVERAGE_NOTE_REASONS) == RETURN_COVERAGE_REASON_IDS
