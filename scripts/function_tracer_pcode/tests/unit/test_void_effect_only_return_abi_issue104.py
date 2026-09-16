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


# --------------------------------------------------------------------------
# exact-type sealing: malformed evidence never becomes eligible
# --------------------------------------------------------------------------

@pytest.mark.parametrize(
    ("mutate", "label"),
    [
        (lambda a: setattr(a, "comparison_surface", SimpleNamespace(kind="memory_effect", explicit_bit_width="40")), "width as numeric string"),
        (lambda a: setattr(a, "comparison_surface", SimpleNamespace(kind="memory_effect", explicit_bit_width=True)), "width as bool"),
        (lambda a: setattr(a, "comparison_surface", SimpleNamespace(kind="memory_effect", explicit_bit_width=None)), "width None"),
        (lambda a: setattr(a, "comparison_surface", SimpleNamespace(kind=None, explicit_bit_width=40)), "kind None"),
        (lambda a: setattr(a, "comparison_surface", SimpleNamespace(kind=b"memory_effect", explicit_bit_width=40)), "kind bytes"),
        (lambda a: setattr(a.effect_summary, "incomplete_reasons", None), "reasons None"),
        (lambda a: setattr(a.effect_summary, "incomplete_reasons", ("",)), "empty reason string"),
        (lambda a: setattr(a.effect_summary, "incomplete_reasons", (None,)), "None reason"),
        (lambda a: setattr(a.effect_summary, "has_unsupported_call", 0), "unsupported as int 0"),
        (lambda a: setattr(a.effect_summary, "has_unsupported_call", None), "unsupported None"),
        (lambda a: setattr(a.effect_summary, "has_unsupported_call", "False"), "unsupported as string"),
        (lambda a: setattr(a.effect_summary, "effects", None), "effects None"),
        (lambda a: setattr(a, "effect_summary", None), "effect summary None"),
    ],
)
def test_malformed_surface_evidence_is_sealed_malformed_and_never_eligible(mutate, label):
    analysis = _void_analysis("left")
    assert _seed_for(analysis, "left").void_effect_only_surface is True
    mutate(analysis)
    seed = _seed_for(analysis, "left")
    assert seed.void_effect_only_surface is False, label
    assert seed.observation_complete is False, label
    if label not in {"effect summary None"}:
        assert seed.surface_fact[1] == "malformed" or seed.surface_fact[1] != "memory_effect", label


def test_surface_fact_components_keep_their_exact_types():
    seed = _seed_for(_void_analysis("left"), "left")
    _schema, kind, bits, count, reasons, unsupported, is_void, has_summary = seed.surface_fact
    assert type(kind) is str and type(bits) is int and type(bits) is not bool
    assert type(count) is int and type(reasons) is tuple
    assert type(unsupported) is bool and type(is_void) is bool and has_summary is True


# --------------------------------------------------------------------------
# end to end: effect surface -> formula -> solver -> production decision
# --------------------------------------------------------------------------

def _z3_available():
    import shutil

    return shutil.which("z3") is not None


class _Program:
    def __init__(self, name):
        self._name = name

    def getName(self):
        return self._name


def _run_production_check(case_id, left, right):
    """Run the real phase workflow, pairwise strategy, z3 and the production
    cutover connector; only the Ghidra analysis step is replaced.

    The analyzer goes in through ``EquivalenceChecker(analyzer_factory=...)``
    (Issue #109), which is the collaborator production itself builds analyzers
    with -- not a package attribute swapped underneath it."""
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        build_default_cutover_connector,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        activate_process_worker_execution_authority_deployment,
    )
    from scripts.function_tracer_pcode.checker import EquivalenceChecker

    if not _z3_available():
        pytest.skip("z3 is not available in PATH")
    activate_process_worker_execution_authority_deployment(
        key_id="gap6-e2e-" + case_id, key=(case_id.encode() * 32)[:32], key_source_id="/tmp/gap6-" + case_id,
    )
    table = {"left": left, "right": right}

    class FakeReturnAnalyzer:
        def __init__(self, program, **_kwargs):
            self._program = program

        def analyze_function_by_name(self, _name, _timeout):
            return table[self._program.getName()]

        def get_last_analysis_failure(self):
            return None

        def get_last_function_lookup_error(self):
            return None

        def dispose(self):
            pass

    checker = EquivalenceChecker(debug=False, analyzer_factory=FakeReturnAnalyzer)
    checker.v2_dual_write_pilot_connector = build_default_cutover_connector()
    result = checker.check_from_binaries(
        _Program("left"), _Program("right"), "f", "f",
        binary1_id="left-id", binary2_id="right-id",
        binary1_content_identity=("sha256", "a" * 64), binary2_content_identity=("sha256", "b" * 64),
    )
    return result.to_dict()


def _param_x():
    return Expression.parameter("param_1", 0, data_type="int", size=4)


def _e2e_void(side, value, **kwargs):
    analysis = _void_analysis(side, effects=[_global_effect(value)], **kwargs)
    analysis.parameters = [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}]
    return analysis


def test_e2e_same_void_global_effect_is_equivalent():
    result = _run_production_check("same", _e2e_void("left", _param_x()), _e2e_void("right", _param_x()))
    assert result["final_outcome"] == "EQUIVALENT", result.get("unknown_reasons")
    assert result["is_equivalent"] is True
    assert result["stage_path"] == ["S_PAIRWISE"]


def test_e2e_different_void_global_effect_is_not_equivalent():
    other = Expression.binary_op("INT_ADD", _param_x(), Expression.constant(1, size=4))
    result = _run_production_check("diff", _e2e_void("left", _param_x()), _e2e_void("right", other))
    assert result["final_outcome"] == "NOT_EQ"
    assert result["is_equivalent"] is False


def test_e2e_incomplete_void_effect_stays_unknown_with_the_abi_blocker():
    right = _e2e_void("right", _param_x(), incomplete=("effect_store_location_unmodeled",))
    result = _run_production_check("incomplete", _e2e_void("left", _param_x()), right)
    assert result["final_outcome"] == "UNKNOWN"
    assert "return_abi_provenance_unavailable" in {r.get("reason_id") for r in result["unknown_reasons"]}


def test_e2e_void_effect_only_versus_complete_non_void_is_never_equivalent():
    """Mixed pair: a void effect-only surface (40-bit effect) against an int
    function with a real return storage (32-bit value).  The observation
    widths cannot be joined, so the pair must not close as EQUIVALENT."""
    left = _e2e_void("left", _param_x())
    right = FunctionReturnAnalysis(
        "fn-right", "0x2000", [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ReturnInfo("0x2010", _param_x(), [])], return_type="int", binary_id="bin-right",
    )
    right.return_abi_facts = _abi_facts(return_type="/int", type_length=4, storage="PRESENT")
    result = _run_production_check("mixed", left, right)
    assert result["final_outcome"] != "EQUIVALENT"
    assert result["is_equivalent"] is not True
    assert result["final_outcome"] in {"UNKNOWN", "NOT_EQ"}


def _matching_width_non_void(side="right"):
    """``undefined5 f(int x)`` returning the 40-bit value ``concat(0x01, x)``:
    bit-for-bit the same solver term as the void side's effect surface
    (presence flag 1 ⊕ stored ``x``), with a real return storage."""
    x = _param_x()
    value = Expression.binary_op("PIECE", Expression.constant(1, size=1), x)
    value.size = 5
    analysis = FunctionReturnAnalysis(
        f"fn-{side}", "0x2000", [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ReturnInfo("0x2010", value, [])], return_type="undefined5", binary_id=f"bin-{side}",
    )
    analysis.return_abi_facts = {
        "schema_version": 1,
        "calling_convention": {"status": "PRESENT", "value": ("ghidra_calling_convention_v1", "default"), "source": "getModelName"},
        "declared_or_effective_return_type": {"status": "PRESENT", "value": ("ghidra_return_type_v1", "/undefined5", 5), "source": "getReturnType"},
        "return_storage_descriptor": {"status": "PRESENT", "value": ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "register", 0, 5),)), "source": "getReturnStorage"},
    }
    return analysis


def test_e2e_matching_width_void_effect_versus_non_void_value_is_never_equivalent():
    """Adversarial mixed pair: the void side's memory-effect surface and the
    non-void side's return value are the same 40-bit solver term.  Ignoring
    the surface kind would make the pair EQUIVALENT although one function
    writes a global and the other returns a value: the observation contract
    must refuse to compare a memory-effect surface against a return value."""
    left = _e2e_void("left", _param_x())
    right = _matching_width_non_void()
    assert left.comparison_surface.explicit_bit_width == 40
    assert right.returns[0].value.get_bit_width() == 40
    result = _run_production_check("mixed-width", left, right)
    assert result["final_outcome"] != "EQUIVALENT", result.get("unknown_reasons")
    assert result["is_equivalent"] is not True
    reasons = {r.get("reason_id") for r in result["unknown_reasons"]}
    assert "return_abi_relation_unproven" in reasons


def test_relation_assessment_refuses_mixed_observation_surface_kinds():
    left = _void_analysis("left")
    right = _matching_width_non_void()
    lw = _width_seed("left", function_identity=left.outcome_function_identity())
    rw = _width_seed("right", function_identity=right.outcome_function_identity())
    assessment = assess_return_abi_pair(left, right, lw, rw, build_pair_return_observation_seed(lw, rw))
    relation = assessment.relation_assessment
    assert relation is not None
    assert relation.status.value == "UNPROVEN"
    assert ("observation_surface_kinds_compatible", False) in relation.predicate_body


def _non_void_with_global_store(side="left"):
    """``int f(int x) { g = x; return 0; }``: stores ⊕ return = 8 + 32 + 32 bits,
    comparison surface kind ``memory_effect`` on a non-void function."""
    from unittest.mock import Mock

    from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
    from conftest import resolve_mock_data_type

    analysis = FunctionReturnAnalysis(
        f"fn-{side}", "0x1000", [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ReturnInfo("0x1010", Expression.constant(0, size=4), [])], return_type="int",
        return_type_obj=resolve_mock_data_type("int"), binary_id=f"bin-{side}",
    )
    effects = [_global_effect(_param_x())]
    analysis.effect_summary = EffectSummary(parameter_names=["param_1"], effects=effects)
    analysis.effect_summary.synthetic_expr = build_void_effect_summary_expr(effects)
    analyzer = ReturnAnalyzer(Mock(), debug=False)
    analyzer._parameters.is_void_type = lambda dtype: str(dtype) == "void"
    assert analyzer._apply_observable_effect_surface(analysis, analysis.return_type_obj, "int") is True
    assert analysis.comparison_surface.kind == "memory_effect"
    assert analysis.comparison_surface.explicit_bit_width == 72
    analysis.return_abi_facts = _abi_facts(return_type="/int", type_length=4, storage="PRESENT")
    return analysis


def _matching_width_non_void_value(side="right", *, width_bytes=9):
    """``undefined9 f(int x)`` returning ``concat(0x01, x, 0x00000000)``: the same
    72-bit solver term as the stores ⊕ return surface of the left side."""
    x = _param_x()
    inner = Expression.binary_op("PIECE", Expression.constant(1, size=1), x)
    inner.size = 5
    value = Expression.binary_op("PIECE", inner, Expression.constant(0, size=4))
    value.size = width_bytes
    analysis = FunctionReturnAnalysis(
        f"fn-{side}", "0x2000", [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        [ReturnInfo("0x2010", value, [])], return_type=f"undefined{width_bytes}", binary_id=f"bin-{side}",
    )
    analysis.return_abi_facts = {
        "schema_version": 1,
        "calling_convention": {"status": "PRESENT", "value": ("ghidra_calling_convention_v1", "default"), "source": "getModelName"},
        "declared_or_effective_return_type": {"status": "PRESENT", "value": ("ghidra_return_type_v1", f"/undefined{width_bytes}", width_bytes), "source": "getReturnType"},
        "return_storage_descriptor": {"status": "PRESENT", "value": ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "register", 0, width_bytes),)), "source": "getReturnStorage"},
    }
    return analysis


def test_e2e_matching_width_non_void_memory_effect_versus_return_value_is_never_equivalent():
    """Adversarial mixed pair on two *non-void* functions: ``int f(int x){ g = x;
    return 0; }`` (stores ⊕ return, 72 bit) against ``undefined9 f(int x)``
    returning the identical 72-bit term.  Both ABI seeds are complete, so the
    void effect-only path is not involved; the surface kinds still differ."""
    left = _non_void_with_global_store("left")
    right = _matching_width_non_void_value("right")
    assert right.returns[0].value.get_bit_width() == 72
    result = _run_production_check("mixed-nonvoid", left, right)
    assert result["final_outcome"] != "EQUIVALENT", result.get("unknown_reasons")
    assert result["is_equivalent"] is not True


def test_effective_surface_kind_follows_the_sealed_fact():
    assert _seed_for(_void_analysis("left"), "left").effective_surface_kind == "memory_effect"
    assert _seed_for(_non_void_with_global_store("left"), "left").effective_surface_kind == "memory_effect"
    assert _seed_for(_matching_width_non_void_value("right"), "right").effective_surface_kind == "return_value"
    malformed = _void_analysis("left")
    malformed.comparison_surface = SimpleNamespace(kind=b"memory_effect", explicit_bit_width=40)
    assert _seed_for(malformed, "left").effective_surface_kind is None


def test_relation_assessment_refuses_non_void_memory_effect_against_return_value():
    left = _non_void_with_global_store("left")
    right = _matching_width_non_void_value("right")
    lw = _width_seed("left", function_identity=left.outcome_function_identity())
    rw = _width_seed("right", function_identity=right.outcome_function_identity())
    assessment = assess_return_abi_pair(left, right, lw, rw, build_pair_return_observation_seed(lw, rw))
    assert assessment.left_seed.complete and assessment.right_seed.complete
    relation = assessment.relation_assessment
    assert relation is not None and relation.status.value == "UNPROVEN"
    assert ("observation_surface_kinds_compatible", False) in relation.predicate_body
    # same kind on both sides (stores ⊕ return vs stores ⊕ return) stays PROVED
    other = _non_void_with_global_store("right")
    ow = _width_seed("right", function_identity=other.outcome_function_identity())
    same = assess_return_abi_pair(left, other, lw, ow, build_pair_return_observation_seed(lw, ow))
    assert same.relation_assessment.status.value == "PROVED"


def test_relation_assessment_refuses_malformed_surface_kind():
    left = _non_void_with_global_store("left")
    right = _non_void_with_global_store("right")
    right.comparison_surface = SimpleNamespace(kind=b"memory_effect", explicit_bit_width=72)
    lw = _width_seed("left", function_identity=left.outcome_function_identity())
    rw = _width_seed("right", function_identity=right.outcome_function_identity())
    assessment = assess_return_abi_pair(left, right, lw, rw, build_pair_return_observation_seed(lw, rw))
    assert assessment.relation_assessment.status.value == "UNPROVEN"


def test_e2e_same_non_void_memory_effect_surfaces_are_equivalent():
    result = _run_production_check("nonvoid-same", _non_void_with_global_store("left"), _non_void_with_global_store("right"))
    assert result["final_outcome"] == "EQUIVALENT", result.get("unknown_reasons")


# --------------------------------------------------------------------------
# the surface fact follows the canonical accessor, not the raw field
# --------------------------------------------------------------------------

def _derived_memory_effect_void(side="left"):
    """Void analysis with a *derived* surface: the raw ``comparison_surface``
    field is ``None`` and ``get_comparison_surface()`` derives ``memory_effect``
    from the synthetic effect expression."""
    from conftest import resolve_mock_data_type

    analysis = _void_analysis(side, surface=False)
    analysis.return_type = "void"
    analysis.return_type_obj = resolve_mock_data_type("void")
    analysis.returns = [ReturnInfo(f"0x{10 if side == 'left' else 20}10", analysis.effect_summary.synthetic_expr, [])]
    analysis.parameters = [{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}]
    assert analysis.comparison_surface is None
    assert analysis.get_comparison_surface().kind == "memory_effect"
    return analysis


def test_seed_reads_the_canonical_comparison_surface_not_the_raw_field():
    analysis = _derived_memory_effect_void("left")
    seed = _seed_for(analysis, "left")
    assert seed.effective_surface_kind == "memory_effect"
    assert seed.surface_fact[2] == analysis.get_comparison_surface().explicit_bit_width
    assert seed.void_effect_only_surface is True


def test_derived_memory_effect_against_matching_width_return_value_is_unproven():
    left = _derived_memory_effect_void("left")
    width_bits = left.get_comparison_surface().explicit_bit_width
    assert width_bits % 8 == 0
    right = _matching_width_non_void_value("right", width_bytes=width_bits // 8)
    lw = _width_seed("left", function_identity=left.outcome_function_identity())
    rw = _width_seed("right", function_identity=right.outcome_function_identity())
    assessment = assess_return_abi_pair(left, right, lw, rw, build_pair_return_observation_seed(lw, rw))
    assert assessment.relation_assessment.status.value == "UNPROVEN"
    assert ("observation_surface_kinds_compatible", False) in assessment.relation_assessment.predicate_body


def test_two_derived_memory_effect_surfaces_are_surface_kind_compatible():
    left = _derived_memory_effect_void("left")
    right = _derived_memory_effect_void("right")
    lw = _width_seed("left", function_identity=left.outcome_function_identity())
    rw = _width_seed("right", function_identity=right.outcome_function_identity())
    assessment = assess_return_abi_pair(left, right, lw, rw, build_pair_return_observation_seed(lw, rw))
    relation = assessment.relation_assessment
    assert ("observation_surface_kinds_compatible", True) in relation.predicate_body
    assert relation.status.value == "PROVED"
    assert relation.predicate_body[0] == "return_abi_semantic_projection_predicates_v5"


@pytest.mark.parametrize(
    "kind",
    ["future_unknown_surface_kind", "", "MEMORY_EFFECT", "memory effect"],
)
def test_unknown_surface_kinds_are_never_compatible(kind):
    left = _void_analysis("left")
    left.comparison_surface = SimpleNamespace(kind=kind, explicit_bit_width=40)
    left.get_comparison_surface = lambda: left.comparison_surface
    seed = _seed_for(left, "left")
    assert seed.effective_surface_kind is None
    assert seed.void_effect_only_surface is False
    right = _void_analysis("right")
    lw = _width_seed("left", function_identity=left.outcome_function_identity())
    rw = _width_seed("right", function_identity=right.outcome_function_identity())
    assessment = assess_return_abi_pair(left, right, lw, rw, build_pair_return_observation_seed(lw, rw))
    relation = assessment.relation_assessment
    assert relation is None or relation.status.value in {"UNPROVEN", "INVALID"}


def test_effect_summary_facts_and_surface_kind_stay_separate():
    """A plain return-value analysis without any effect summary keeps its
    authoritative surface kind; only the eligibility facts are empty."""
    right = _matching_width_non_void_value("right")
    assert getattr(right, "effect_summary", None) is None
    seed = _seed_for(right, "right")
    assert seed.effective_surface_kind == "return_value"
    assert seed.void_effect_only_surface is False
    assert seed.surface_fact[3] == 0 and seed.surface_fact[4] == ()
