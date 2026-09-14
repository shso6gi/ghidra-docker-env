# -*- coding: utf-8 -*-
"""Issue #125 PR-125-A: 解析の限界を active cause へ帰属させる契約（A1〜A9）。

帰属は cause を**追加も強化もしない**。「その cause が解消されたなら今回の限界も
解消された」と言える対応関係だけを帰属とみなし、言えないものは fail-closed で
ERROR に落とす。`reason_id` 一致だけで既存 cause に相乗りしないこと、曖昧一致を
fail-open しないことがこの file の主題。
"""

import ast
import inspect

import pytest

from scripts.function_tracer_pcode.authority.contracts import (
    IdentityScope,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    requirement_slot,
)
from scripts.function_tracer_pcode.authority.decision import limitation_attribution as la
from scripts.function_tracer_pcode.authority.decision.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    FinalizationAuthority,
    finalize_decision,
)
from scripts.function_tracer_pcode.authority.contracts import Outcome
from scripts.function_tracer_pcode.authority.registry import (
    SealedReasonRegistry,
    SealedRecoveryRegistry,
)
from scripts.function_tracer_pcode.core.errors import (
    AnalysisLimitation,
    CauseAttributionKey,
    DeadlineExceeded,
)
from scripts.function_tracer_pcode.tests.unit._issue125_support import (
    OUTCOME_CONTRACT,
    OUTCOME_PROOF_KIND,
    SAT_SAFETY_CONTRACT,
    SAT_SAFETY_PROOF_KIND,
    SAT_SAFETY_REASON_ID,
    LifecycleHarness,
    attribution_key,
    outcome_cause_inputs,
    sat_safety_cause_inputs,
)


def _limitation(reason_id=SAT_SAFETY_REASON_ID, *, attribution=None, site="analysis.tracer.trace"):
    return AnalysisLimitation(
        reason_id, "analysis stopped", site=site, attribution=attribution,
    )


def _observed(harness, cause_inputs, *, contract=SAT_SAFETY_CONTRACT,
              proof_kind=SAT_SAFETY_PROOF_KIND, suffix="a",
              occurrence_target_kind=None):
    authority, requirement = harness.build_occurrence(
        cause_inputs, contract=contract, proof_kind=proof_kind,
        suffix=suffix, occurrence_target_kind=occurrence_target_kind,
    )
    harness.observe(authority)
    return authority, requirement


# --- A1: 同じ reason でも別 target の cause には相乗りしない --------------------

def test_same_reason_different_target_is_not_attributed():
    harness = LifecycleHarness()
    observed_inputs = sat_safety_cause_inputs(
        canonical_target_key=("pair", "left", "right"),
    )
    _observed(harness, observed_inputs)
    # 同じ reason・同じ scope・同じ欠落事実だが、対象（関数対）が違う。
    other_inputs = sat_safety_cause_inputs(
        canonical_target_key=("pair", "other", "target"),
    )
    key = attribution_key(other_inputs, ("issue125-q-absent",))

    attribution = la.attribute_analysis_limitation(harness, _limitation(attribution=key))

    assert attribution.disposition == la.UNATTRIBUTED
    assert attribution.failure_status == "limitation_unattributed"
    assert attribution.cause_id is None


# --- A2: scope / 欠落事実 / target_kind の違いを無視しない ----------------------

def test_same_reason_different_scope_is_not_attributed():
    harness = LifecycleHarness()
    observed_inputs = sat_safety_cause_inputs()
    _, requirement = _observed(harness, observed_inputs)
    key = attribution_key(
        observed_inputs, (requirement.requirement_id,), identity_scope="UNARY",
    )

    attribution = la.attribute_analysis_limitation(harness, _limitation(attribution=key))

    assert attribution.disposition == la.UNATTRIBUTED


def test_same_reason_different_missing_fact_is_not_attributed():
    harness = LifecycleHarness()
    observed_inputs = sat_safety_cause_inputs()
    _, requirement = _observed(harness, observed_inputs)
    other_inputs = sat_safety_cause_inputs(
        missing_semantic_fact=("counterexample_safety_gate_unproven", "replay"),
    )
    key = attribution_key(other_inputs, (requirement.requirement_id,))

    attribution = la.attribute_analysis_limitation(harness, _limitation(attribution=key))

    assert attribution.disposition == la.UNATTRIBUTED


def test_target_kind_is_matched_independently_of_the_cause_digest(monkeypatch):
    """`target_kind` は `CauseIdV2` に入らないので独立に照合する（A2 / A9）。

    現在の sealed registry は reason ごとに target kind を 1 つしか許さないので、
    2 つ許す reason を持つ registry を使って「digest は完全一致だが target_kind
    だけ違う」状態を作る。digest 一致だけで帰属していれば、この test は通らない。
    """
    from scripts.function_tracer_pcode.authority.process import supervisor

    reason_id = "issue125_two_target_kinds"
    reason_registry = SealedReasonRegistry.build((
        ReasonDefinition(
            reason_id, "issue125_probe", "proof_obligation", "blocks_decision",
            frozenset(("kind_a", "kind_b")), ("probe",),
            frozenset(("issue125_probe_proof",)), True, "issue125_probe_v1",
            RecoveryAddressability.REQUIREMENT_REQUIRED,
        ),
    ))
    recovery_registry = SealedRecoveryRegistry.build((
        SatisfactionContractDefinition(
            "issue125-probe-recovery", 1,
            (RequirementSlotDefinition(
                "probe", frozenset(("issue125_probe_proof",)),
            ),),
            requirement_slot("probe"),
        ),
    ))
    monkeypatch.setattr(
        supervisor, "PROCESS_DURABLE_REASON_REGISTRY", reason_registry,
    )
    harness = LifecycleHarness(
        reason_registry=reason_registry, recovery_registry=recovery_registry,
    )
    cause_inputs = dict(
        reason_id=reason_id,
        identity_scope=IdentityScope.UNARY,
        target_kind="kind_a",
        canonical_target_key=("probe", "one"),
        missing_semantic_fact=("probe_fact",),
        semantic_proposition=("probe_holds",),
        observation_surface=("probe",),
        active_semantic_precondition=("probe_observed", True),
        correspondence_contract=None,
    )
    # occurrence は kind_b、帰属キーは kind_a。cause identity（digest）は同一。
    _, requirement = _observed(
        harness, cause_inputs, contract=("issue125-probe-recovery", 1, "probe"),
        proof_kind="issue125_probe_proof", occurrence_target_kind="kind_b",
    )
    key = attribution_key(cause_inputs, (requirement.requirement_id,))
    assert key.target_kind == "kind_a"

    attribution = la.attribute_analysis_limitation(
        harness, _limitation(reason_id, attribution=key),
    )
    assert attribution.disposition == la.UNATTRIBUTED

    # 同じ digest・同じ target_kind なら帰属できる（differentia が target_kind だけ）。
    matching_key = attribution_key(
        cause_inputs, (requirement.requirement_id,), target_kind="kind_b",
    )
    matched = la.attribute_analysis_limitation(
        harness, _limitation(reason_id, attribution=matching_key),
    )
    assert matched.disposition == la.ATTRIBUTED_EXISTING_CAUSE
    assert matched.decision_effect == "blocks_decision"


# --- A3 / A4: 対応する cause の解消と、別 cause の解消を区別する ---------------

def test_attributed_cause_resolution_resolves_the_limitation():
    harness = LifecycleHarness()
    observed_inputs = sat_safety_cause_inputs()
    authority, requirement = _observed(harness, observed_inputs)
    key = attribution_key(observed_inputs, (requirement.requirement_id,))
    before = la.attribute_analysis_limitation(harness, _limitation(attribution=key))
    assert before.disposition == la.ATTRIBUTED_EXISTING_CAUSE

    harness.complete(authority, requirement)

    # 帰属先 cause が active から外れたので、同じ限界はもう帰属先を持たない。
    after = la.attribute_analysis_limitation(harness, _limitation(attribution=key))
    assert after.disposition == la.UNATTRIBUTED
    assert harness.active_reason_ids() == []

    # 他に blocker が無ければ decisive outcome が成立する（= 限界も解消扱い）。
    projection = harness.final_projection()
    receipt = finalize_decision(FinalizationAuthority(
        harness.identity.result_occurrence_id,
        projection,
        (DecisiveProofReceipt.create(
            result_occurrence_id=harness.identity.result_occurrence_id,
            lifecycle_projection_digest=projection.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.SAFE_COUNTEREXAMPLE,
            proof_artifact_digest="issue125-counterexample",
        ),),
    ))
    assert receipt.outcome is Outcome.NOT_EQ


def test_resolving_another_cause_leaves_the_limitation_active():
    harness = LifecycleHarness()
    attributed_inputs = sat_safety_cause_inputs(
        canonical_target_key=("pair", "left", "right"),
    )
    other_inputs = sat_safety_cause_inputs(
        canonical_target_key=("pair", "other", "pair"),
    )
    _, attributed_requirement = _observed(harness, attributed_inputs, suffix="a")
    other_authority, other_requirement = _observed(harness, other_inputs, suffix="b")
    key = attribution_key(attributed_inputs, (attributed_requirement.requirement_id,))

    # 同じ reason の *別* cause だけを完了させる。
    harness.complete(other_authority, other_requirement)

    attribution = la.attribute_analysis_limitation(harness, _limitation(attribution=key))
    assert attribution.disposition == la.ATTRIBUTED_EXISTING_CAUSE
    assert attribution.decision_effect == "blocks_disequivalence"

    projection = harness.final_projection()
    receipt = finalize_decision(FinalizationAuthority(
        harness.identity.result_occurrence_id,
        projection,
        (DecisiveProofReceipt.create(
            result_occurrence_id=harness.identity.result_occurrence_id,
            lifecycle_projection_digest=projection.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.SAFE_COUNTEREXAMPLE,
            proof_artifact_digest="issue125-counterexample",
        ),),
    ))
    # 帰属先 cause は active のままなので NOT_EQ は成立しない。
    assert receipt.outcome is Outcome.UNKNOWN


# --- A5: 帰属で effect を強化しない ------------------------------------------

def test_attributed_blocks_equivalence_cause_does_not_block_not_eq():
    """`blocks_equivalence` の cause に帰属した限界は EQ だけを塞ぐ。"""
    harness = LifecycleHarness()
    observed_inputs = outcome_cause_inputs()
    _, requirement = _observed(
        harness, observed_inputs,
        contract=OUTCOME_CONTRACT, proof_kind=OUTCOME_PROOF_KIND,
    )
    key = attribution_key(observed_inputs, (requirement.requirement_id,))

    attribution = la.attribute_analysis_limitation(
        harness, _limitation(observed_inputs["reason_id"], attribution=key),
    )
    assert attribution.disposition == la.ATTRIBUTED_EXISTING_CAUSE
    # 帰属で `blocks_decision` へ強化しない。
    assert attribution.decision_effect == "blocks_equivalence"

    projection = harness.final_projection()
    result_id = harness.identity.result_occurrence_id
    not_eq = finalize_decision(FinalizationAuthority(
        result_id, projection,
        (DecisiveProofReceipt.create(
            result_occurrence_id=result_id,
            lifecycle_projection_digest=projection.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.SAFE_COUNTEREXAMPLE,
            proof_artifact_digest="issue125-counterexample",
        ),),
    ))
    assert not_eq.outcome is Outcome.NOT_EQ

    eq = finalize_decision(FinalizationAuthority(
        result_id, projection,
        (DecisiveProofReceipt.create(
            result_occurrence_id=result_id,
            lifecycle_projection_digest=projection.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.EQ_CLOSURE,
            proof_artifact_digest="issue125-eq-closure",
        ),),
    ))
    assert eq.outcome is Outcome.UNKNOWN


# --- A6: 帰属不能（無し / 0 件 / 2 件以上）は ERROR ---------------------------

def test_unattributable_limitation_without_a_key_is_error():
    harness = LifecycleHarness()
    _observed(harness, sat_safety_cause_inputs())

    attribution = la.attribute_analysis_limitation(harness, _limitation())

    assert attribution.disposition == la.UNATTRIBUTED
    assert attribution.failure_status == "limitation_unattributed"


def test_unattributable_limitation_with_zero_matches_is_error():
    harness = LifecycleHarness()
    inputs = sat_safety_cause_inputs()
    key = attribution_key(inputs, ("issue125-q-never-observed",))

    attribution = la.attribute_analysis_limitation(harness, _limitation(attribution=key))

    assert attribution.disposition == la.UNATTRIBUTED


def test_ambiguous_limitation_with_two_matches_is_error():
    """同一 cause identity・同一 requirement 集合の occurrence が 2 件 active。

    どちらが解消されれば限界が解消されるか決められないので、fail-open しない。
    """
    harness = LifecycleHarness()
    inputs = sat_safety_cause_inputs()
    authority_a, requirement_a = harness.build_occurrence(
        inputs, contract=SAT_SAFETY_CONTRACT,
        proof_kind=SAT_SAFETY_PROOF_KIND, suffix="a",
    )
    harness.observe(authority_a)
    # 同じ cause identity・同じ requirement id を、別 occurrence id で観測する。
    authority_b = _clone_with_occurrence_id(authority_a, "issue125-occ-duplicate")
    harness.observe(authority_b)
    key = attribution_key(inputs, (requirement_a.requirement_id,))

    attribution = la.attribute_analysis_limitation(harness, _limitation(attribution=key))

    assert attribution.disposition == la.UNATTRIBUTED
    assert "not exactly one" in attribution.detail


def _clone_with_occurrence_id(authority, occurrence_id):
    from dataclasses import replace

    from scripts.function_tracer_pcode.authority.contracts import (
        CauseOccurrenceAuthority,
    )

    return CauseOccurrenceAuthority(
        replace(authority.occurrence, occurrence_id=occurrence_id),
        authority.bound_contract,
    )


# --- A7: 新規 cause 経路と既存帰属経路は別契約 --------------------------------

def test_owned_producer_path_creates_a_new_blocking_cause(monkeypatch):
    from scripts.function_tracer_pcode.authority.decision import limitation_attribution

    emitted = {}

    def fake_observe(**kwargs):
        emitted.update(kwargs)
        return 1

    monkeypatch.setattr(
        limitation_attribution, "observe_analysis_limitation", fake_observe,
    )
    attribution = la.attribute_analysis_limitation(
        None, DeadlineExceeded("budget", site="checker.checker.EquivalenceChecker.check"),
    )

    assert attribution.disposition == la.ATTRIBUTED_NEW_CAUSE
    assert attribution.decision_effect == "blocks_decision"
    assert attribution.cause_id is None and attribution.occurrence_id is None
    assert emitted["reason_id"] == "analysis_budget_exceeded"
    assert emitted["limitation_site"] == "checker.checker.EquivalenceChecker.check"


def test_owned_producer_path_without_activation_is_unattributed():
    # pilot session が無いので emit は strict no-op（0）。fail-open しない。
    attribution = la.attribute_analysis_limitation(
        None, DeadlineExceeded("budget", site="checker.checker.EquivalenceChecker.check"),
    )
    assert attribution.disposition == la.UNATTRIBUTED
    assert attribution.failure_status == "limitation_unattributed"


def test_existing_cause_path_creates_no_new_cause():
    harness = LifecycleHarness()
    inputs = sat_safety_cause_inputs()
    _, requirement = _observed(harness, inputs)
    before = len(harness.recorder.recorded_events)
    key = attribution_key(inputs, (requirement.requirement_id,))

    attribution = la.attribute_analysis_limitation(harness, _limitation(attribution=key))

    assert attribution.disposition == la.ATTRIBUTED_EXISTING_CAUSE
    assert len(harness.recorder.recorded_events) == before
    assert harness.active_reason_ids() == [SAT_SAFETY_REASON_ID]


# --- A8: requirement 集合は完全一致 ------------------------------------------

@pytest.mark.parametrize("requirement_ids", [
    (),                                     # 片側だけ空
    ("issue125-q-unrelated",),              # 別 id
])
def test_attribution_requirement_set_must_match_exactly(requirement_ids):
    harness = LifecycleHarness()
    inputs = sat_safety_cause_inputs()
    _observed(harness, inputs)
    key = attribution_key(inputs, requirement_ids)

    attribution = la.attribute_analysis_limitation(harness, _limitation(attribution=key))

    assert attribution.disposition == la.UNATTRIBUTED


def test_attribution_requirement_superset_is_not_a_match():
    harness = LifecycleHarness()
    inputs = sat_safety_cause_inputs()
    _, requirement = _observed(harness, inputs)
    key = attribution_key(
        inputs, (requirement.requirement_id, "issue125-q-extra"),
    )

    attribution = la.attribute_analysis_limitation(harness, _limitation(attribution=key))

    assert attribution.disposition == la.UNATTRIBUTED


def test_attribution_requirement_order_does_not_matter():
    """順序違いは一致（集合として比較する）。"""
    source = inspect.getsource(la._matching_active_rows)
    assert "frozenset(occurrence.proof_requirement_ids) != requirement_ids" in source
    assert "len(occurrence.proof_requirement_ids) != len(requirement_ids)" in source


# --- A9: 例外の reason と帰属キーの reason の一致 ------------------------------

def test_limitation_reason_must_match_the_attribution_key_reason():
    harness = LifecycleHarness()
    inputs = sat_safety_cause_inputs()
    _, requirement = _observed(harness, inputs)
    key = attribution_key(inputs, (requirement.requirement_id,))

    # 例外は別 reason を主張している。digest は一致するが帰属させない。
    limitation = _limitation("counterexample_replay_unproven", attribution=key)
    attribution = la.attribute_analysis_limitation(harness, limitation)

    assert attribution.disposition == la.UNATTRIBUTED
    assert "reason" in attribution.detail


# --- 未登録 / retired reason ---------------------------------------------------

def test_unregistered_reason_is_a_typed_error():
    attribution = la.attribute_analysis_limitation(
        None, _limitation("not_a_sealed_reason_at_all"),
    )
    assert attribution.disposition == la.UNREGISTERED
    assert attribution.failure_status == "unregistered_reason"


def test_retired_umbrella_reason_is_a_typed_error():
    from scripts.function_tracer_pcode.authority.sites.activation import (
        RETIRED_UMBRELLA_REASON_IDS,
    )

    retired = sorted(RETIRED_UMBRELLA_REASON_IDS)[0]
    attribution = la.attribute_analysis_limitation(None, _limitation(retired))
    assert attribution.disposition == la.UNREGISTERED


# --- 静的: reason_id 一致だけの帰属になっていない -------------------------------

def test_attribution_reads_one_prefix_for_projection_and_occurrences():
    """projection と occurrence 写像は同じ prefix から作る（別々に取らない）。"""
    source = inspect.getsource(la._matching_active_rows)
    assert source.count("prefix_view()") == 1
    assert "replay_prefix(prefix)" in source
    assert "_observed_occurrences(prefix)" in source


def test_attribution_never_matches_on_reason_id_alone():
    source = inspect.getsource(la._matching_active_rows)
    tree = ast.parse(source)
    compared = {
        ast.unparse(node.left)
        for node in ast.walk(tree)
        if isinstance(node, ast.Compare)
    }
    # row と occurrence の両方で target_kind / cause_id を照合している。
    for expected in (
        "row.reason_id", "row.target_kind", "row.cause_id",
        "occurrence.reason_id", "occurrence.target_kind",
        "occurrence.identity_scope.value", "cause_id.value",
        "cause_id.canonical_target_key", "cause_id.missing_semantic_fact",
        "cause_id.semantic_proposition_digest",
    ):
        assert expected in compared, expected


def test_attribution_result_never_carries_a_foreign_decision_effect():
    """帰属した場合の effect は、その cause の `decision_effect` そのもの。"""
    source = inspect.getsource(la.attribute_analysis_limitation)
    assert "decision_effect=row.decision_effect" in source
    assert "decision_effect=definition.decision_effect" in source
    assert '"blocks_decision"' not in source


def test_attribution_requires_an_exact_limitation_type():
    with pytest.raises(TypeError):
        la.attribute_analysis_limitation(None, ValueError("not a limitation"))


def test_attribution_key_rejects_unknown_identity_scope():
    with pytest.raises(ValueError):
        CauseAttributionKey(
            "r", "NEITHER", "t", ("a",), ("b",), ("c",), ("q",),
        )
