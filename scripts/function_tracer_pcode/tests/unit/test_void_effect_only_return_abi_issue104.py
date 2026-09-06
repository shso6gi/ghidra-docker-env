"""Issue #104 Gap 6: a ``void`` function with a complete, non-empty observable
effect surface is not blocked by the missing return-storage ABI slot.

The return storage descriptor of a void function does not exist; when the
comparison surface is the (complete) memory-effect surface, that slot is not
part of the observation contract.  The eligibility is sealed into the ABI
seed once (``FunctionReturnAbiSeed.surface_fact``) and the existing
``return_abi_provenance_unavailable`` obligation is *completed* by a
structural proof (``ReturnAbiProvenanceArtifact.from_void_effect_surface``)
at finalization.  Everything else (non-void, extra missing slots, incomplete
or unsupported effects, zero effects) keeps failing closed.

Synthetic unit fixtures; not EqBench ground truth.
"""
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary, StoreEffect
from scripts.function_tracer_pcode.analysis.effects.summary import build_void_effect_summary_expr
from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
    ABI_WIDTH_READONLY_REASON_REGISTRY,
    ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
    AbiWidthReadonlyBlockerSignal,
    AbiWidthReadonlyPilotEncoder,
    FunctionReturnAbiSeed,
    ReturnAbiProvenanceArtifact,
    assess_return_abi_pair,
)
from scripts.function_tracer_pcode.authority.lifecycle.pilot import ProductionDualWritePilotConnector
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    CompositeProductionSignalEncoder,
    production_signal_scope,
)
from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
    DecisiveProofEventAuthority,
    EventIntent,
    EventType,
)
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    ComparisonSurface,
    Expression,
    FunctionReturnAnalysis,
    LocationBaseRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.proof.return_width.pipeline import (
    PreparedFunctionReturnWidths,
    build_pair_return_observation_seed,
    prepare_pair_return_observation,
)
from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_abi_width_readonly import (
    _width_seed,
)


# --------------------------------------------------------------------------
# fixtures
# --------------------------------------------------------------------------

def _abi_facts(*, return_type="/void", type_length=0, storage="MISSING", calling="PRESENT"):
    facts = {
        "schema_version": 1,
        "calling_convention": {
            "status": calling,
            "value": ("ghidra_calling_convention_v1", "default") if calling == "PRESENT" else None,
            "source": "getModelName",
        },
        "declared_or_effective_return_type": {
            "status": "PRESENT",
            "value": ("ghidra_return_type_v1", return_type, type_length),
            "source": "getReturnType",
        },
        "return_storage_descriptor": {
            "status": storage,
            "value": (
                ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "register", 0, 8),))
                if storage == "PRESENT" else None
            ),
            "source": "getReturnStorage",
        },
    }
    return facts


def _global_effect(value, order=1):
    location = CanonicalLocation(base_ref=LocationBaseRef.global_object("g", 4, space_name="ram"), offset=0, size=4)
    return StoreEffect(location=location, value=value, conditions=[], order_key=order)


def _void_analysis(side, *, effects=None, incomplete=(), unsupported=False, surface=True, facts=None):
    analysis = FunctionReturnAnalysis(
        f"fn-{side}", f"0x{10 if side == 'left' else 20}00", [], [], binary_id=f"bin-{side}",
    )
    if effects is None:
        effects = [_global_effect(Expression.parameter("param_1", 0, data_type="int", size=4))]
    summary = EffectSummary(parameter_names=["param_1"], effects=list(effects))
    summary.incomplete_reasons = tuple(incomplete)
    summary.has_unsupported_call = unsupported
    summary.synthetic_expr = build_void_effect_summary_expr(list(effects))
    analysis.effect_summary = summary
    if surface and summary.synthetic_expr is not None:
        analysis.returns = [ReturnInfo(f"0x{10 if side == 'left' else 20}10", summary.synthetic_expr, [])]
        analysis.comparison_surface = ComparisonSurface(
            kind="memory_effect",
            explicit_bit_width=max(1, summary.synthetic_expr.get_bit_width()),
            use_sign_extension=False,
            evidence={"source": "effect_summary.synthetic_expr", "effect_count": len(effects)},
        )
    analysis.return_abi_facts = _abi_facts() if facts is None else facts
    return analysis


def _seed_for(analysis, side):
    return FunctionReturnAbiSeed.from_analysis_and_width_seed(
        analysis, _width_seed(side, function_identity=analysis.outcome_function_identity())
    )


def _session(case_id):
    encoder = AbiWidthReadonlyPilotEncoder()
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({AbiWidthReadonlyBlockerSignal: encoder}),
    )
    return connector, encoder, connector.begin({"case": case_id})


def _run_pair(case_id, left_analysis, right_analysis, *, decisive):
    """Drive the return-width ABI producer for one pair inside a pilot session,
    finalise the domain, then finish with the given decisive event."""
    connector, encoder, session = _session(case_id)
    left_seed = _width_seed("left", function_identity=left_analysis.outcome_function_identity())
    right_seed = _width_seed("right", function_identity=right_analysis.outcome_function_identity())
    left_case, right_case = object(), object()
    incomplete_proof = SimpleNamespace(complete=False, blocker_kind="test-stop")
    with production_signal_scope(session):
        prepare_pair_return_observation(
            left_analysis, right_analysis, left_case, right_case,
            PreparedFunctionReturnWidths({id(left_case): left_seed}, {id(left_case): incomplete_proof}),
            PreparedFunctionReturnWidths({id(right_case): right_seed}, {id(right_case): incomplete_proof}),
            return_coverage_ids=(),
        )
        encoder.finalize_open_execution_history(session)
    projection = session.preview_lifecycle_projection()
    active = tuple(row.reason_id for row in projection.c_active_base)
    if decisive == "eq":
        session.emit(EventIntent(EventType.EQ_CLOSURE, DecisiveProofEventAuthority("gap6-eq-proof")))
        legacy = True
    elif decisive == "not_eq":
        session.emit(EventIntent(EventType.COUNTEREXAMPLE, DecisiveProofEventAuthority("gap6-counterexample")))
        legacy = False
    else:
        legacy = None
    evidence = connector.finish(
        session,
        SimpleNamespace(error_message=None, is_equivalent=legacy, failure_status=None,
                        failure_message=None, is_timeout=lambda: False),
        case_id=case_id,
    )
    outcome = evidence.pilot_result.candidate.decision_receipt.outcome.value
    return active, outcome, session


# --------------------------------------------------------------------------
# seed eligibility (sealed fact)
# --------------------------------------------------------------------------

def test_void_complete_effect_surface_seed_is_eligible_and_sealed():
    analysis = _void_analysis("left")
    seed = _seed_for(analysis, "left")
    assert seed.missing_slots == ("return_storage_descriptor",)
    assert seed.complete is False
    assert seed.void_effect_only_surface is True
    assert seed.observation_complete is True
    assert seed.surface_fact[0] == "void_effect_surface_fact_v1"
    assert seed.surface_fact[1] == "memory_effect"
    assert seed.surface_fact[3] == 1  # effect count
    # the fact is part of the digest: a different surface shape changes the
    # seed identity (values are the solver's business, the shape is the ABI's)
    other = _void_analysis("left", effects=[
        _global_effect(Expression.constant(7, size=4), 1),
        StoreEffect(location=CanonicalLocation(base_ref=LocationBaseRef.global_object("h", 8, space_name="ram"), offset=0, size=8),
                    value=Expression.constant(9, size=8), conditions=[], order_key=2),
    ])
    assert _seed_for(other, "left").surface_fact[3] == 2
    assert _seed_for(other, "left").seed_digest != seed.seed_digest


@pytest.mark.parametrize(
    ("kwargs", "label"),
    [
        (dict(incomplete=("effect_store_location_unmodeled",)), "incomplete effect summary"),
        (dict(unsupported=True), "unsupported call"),
        (dict(effects=[], surface=False), "zero effects (proven-empty is a separate follow-up)"),
        (dict(facts=_abi_facts(calling="MISSING")), "another ABI slot missing"),
        (dict(facts=_abi_facts(return_type="/int", type_length=4)), "non-void return type"),
    ],
)
def test_void_effect_only_eligibility_is_denied_outside_the_exact_shape(kwargs, label):
    analysis = _void_analysis("left", **kwargs)
    seed = _seed_for(analysis, "left")
    assert seed.void_effect_only_surface is False, label
    assert seed.observation_complete is False, label


def test_non_void_seed_behaviour_is_unchanged():
    present = _void_analysis("left", facts=_abi_facts(return_type="/int", type_length=4, storage="PRESENT"))
    present.comparison_surface = None
    seed = _seed_for(present, "left")
    assert seed.complete is True and seed.observation_complete is True
    assert seed.void_effect_only_surface is False


# --------------------------------------------------------------------------
# 1 / 2: complete void effects reach EQ / NOT_EQ through the authority
# --------------------------------------------------------------------------

def test_same_complete_void_effects_reach_equivalent():
    left = _void_analysis("left")
    right = _void_analysis("right")
    active, outcome, session = _run_pair("gap6-void-eq", left, right, decisive="eq")
    assert "return_abi_provenance_unavailable" not in active
    assert outcome == "EQUIVALENT"
    completed = session.domain_signal_state.get("void_effect_only_return_abi_completed", set())
    assert len(completed) == 2


def test_different_complete_void_effects_reach_not_eq():
    left = _void_analysis("left")
    right = _void_analysis("right", effects=[_global_effect(Expression.constant(7, size=4))])
    active, outcome, _session = _run_pair("gap6-void-neq", left, right, decisive="not_eq")
    assert "return_abi_provenance_unavailable" not in active
    assert outcome == "NOT_EQ"


# --------------------------------------------------------------------------
# 3 / 4 / 5 / 6: everything else keeps the blocker
# --------------------------------------------------------------------------

@pytest.mark.parametrize(
    ("right_kwargs", "label"),
    [
        (dict(incomplete=("effect_store_location_unmodeled",)), "incomplete effect summary"),
        (dict(unsupported=True), "unsupported call"),
        (dict(effects=[], surface=False), "zero effects"),
        (dict(facts=_abi_facts(calling="MISSING")), "calling convention also missing"),
        (dict(facts=_abi_facts(return_type="/int", type_length=4)), "non-void with missing storage"),
    ],
)
def test_ineligible_void_side_keeps_the_terminal_abi_blocker(right_kwargs, label):
    left = _void_analysis("left")
    right = _void_analysis("right", **right_kwargs)
    active, outcome, _session = _run_pair("gap6-blocked-" + label.replace(" ", "-"), left, right, decisive="eq")
    assert "return_abi_provenance_unavailable" in active, label
    assert outcome == "UNKNOWN", label


def test_relation_assessment_still_rejects_incomplete_non_void_seeds():
    left = _void_analysis("left", facts=_abi_facts(return_type="/int", type_length=4, storage="PRESENT"))
    right = _void_analysis("right", facts=_abi_facts(return_type="/int", type_length=4))
    left.comparison_surface = None
    right.comparison_surface = None
    lw = _width_seed("left", function_identity=left.outcome_function_identity())
    rw = _width_seed("right", function_identity=right.outcome_function_identity())
    assessment = assess_return_abi_pair(left, right, lw, rw, build_pair_return_observation_seed(lw, rw))
    assert [s.reason_id for s in assessment.signals] == ["return_abi_provenance_unavailable"]
    assert assessment.relation_assessment is None


def test_void_pair_forms_the_relation_assessment():
    left = _void_analysis("left")
    right = _void_analysis("right")
    lw = _width_seed("left", function_identity=left.outcome_function_identity())
    rw = _width_seed("right", function_identity=right.outcome_function_identity())
    assessment = assess_return_abi_pair(left, right, lw, rw, build_pair_return_observation_seed(lw, rw))
    assert sorted(s.reason_id for s in assessment.signals) == [
        "return_abi_provenance_unavailable", "return_abi_provenance_unavailable", "return_abi_relation_unproven",
    ]
    assert assessment.relation_assessment is not None
    assert assessment.relation_assessment.status.value == "PROVED"


# --------------------------------------------------------------------------
# 7: digest / tamper detection
# --------------------------------------------------------------------------

def test_seed_surface_fact_is_tamper_evident():
    analysis = _void_analysis("left")
    seed = _seed_for(analysis, "left")
    values = {name: getattr(seed, name) for name in seed.__dataclass_fields__ if name != "seed_digest"}
    forged_fact = list(seed.surface_fact)
    forged_fact[3] = 99  # pretend a different effect census
    values["surface_fact"] = tuple(forged_fact)
    with pytest.raises(ValueError, match="digest mismatch"):
        FunctionReturnAbiSeed(**values, seed_digest=seed.seed_digest,
                              _factory_token=_factory_token())


def _factory_token():
    from scripts.function_tracer_pcode.authority.domains import abi_width_readonly as module

    return module._RETURN_ABI_SEED_TOKEN


def test_void_artifact_requires_the_exact_eligible_seed_and_blocker():
    eligible = _seed_for(_void_analysis("left"), "left")
    blocker = AbiWidthReadonlyBlockerSignal.from_return_abi_seed(eligible, "return_storage_descriptor")
    artifact = ReturnAbiProvenanceArtifact.from_void_effect_surface(
        blocker, eligible, source_snapshot_fingerprint="snapshot-1",
    )
    assert artifact.reason_id == "return_abi_provenance_unavailable"
    assert artifact.proof_body[0] == "void_effect_only_return_abi_v1"
    assert artifact.source_seed_digest == eligible.seed_digest

    ineligible = _seed_for(_void_analysis("left", unsupported=True), "left")
    with pytest.raises(ValueError, match="not a void effect-only surface"):
        ReturnAbiProvenanceArtifact.from_void_effect_surface(
            AbiWidthReadonlyBlockerSignal.from_return_abi_seed(ineligible, "return_storage_descriptor"),
            ineligible, source_snapshot_fingerprint="snapshot-1",
        )
    with pytest.raises(ValueError, match="differs from its blocker"):
        ReturnAbiProvenanceArtifact.from_void_effect_surface(
            AbiWidthReadonlyBlockerSignal.from_return_abi_seed(ineligible, "return_storage_descriptor"),
            eligible, source_snapshot_fingerprint="snapshot-1",
        )
    values = {name: getattr(artifact, name) for name in artifact.__dataclass_fields__ if name != "artifact_digest"}
    values["proof_body"] = ("void_effect_only_return_abi_v1", "forged")
    from scripts.function_tracer_pcode.authority.domains import abi_width_readonly as module

    with pytest.raises(ValueError, match="digest mismatch"):
        ReturnAbiProvenanceArtifact(**values, artifact_digest=artifact.artifact_digest,
                                    _factory_token=module._COMPLETION_ARTIFACT_TOKEN)


def test_encoder_refuses_to_register_an_ineligible_seed():
    _connector, encoder, session = _session("gap6-register")
    ineligible = _seed_for(_void_analysis("left", unsupported=True), "left")
    with pytest.raises(TypeError):
        encoder.register_void_effect_only_return_abi_seed(session, ineligible)
    eligible = _seed_for(_void_analysis("left"), "left")
    encoder.register_void_effect_only_return_abi_seed(session, eligible)
    # idempotent for the same exact seed
    encoder.register_void_effect_only_return_abi_seed(session, eligible)
    assert list(session.domain_signal_state["void_effect_only_return_abi_seeds"]) == [eligible.seed_digest]
