from types import SimpleNamespace
from dataclasses import fields

import pytest

from scripts.function_tracer_pcode.equivalence.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
)
from scripts.function_tracer_pcode.equivalence.obligations import (
    ActivationState,
    AnalysisSnapshot,
    AttemptCache,
    AttemptCacheEntry,
    AttemptKey,
    BranchActivationController,
    BranchSpec,
    DerivedAnalysisView,
    FunctionProofOutcome,
    ProofArtifact,
    ProofCache,
    ProofExpression,
    ProofExpressionEvaluator,
    ProofNodeKind,
    ProofWorklist,
    SemanticFactProvenance,
    SnapshotFingerprintCodec,
    ViewPremiseRecord,
    WorkItem,
    ObligationInstanceId,
    validate_artifact_applicability,
    validate_proof_closure,
)
from scripts.function_tracer_pcode.equivalence.obligations.snapshot import (
    FUNCTION_ANALYSIS_FIELD_CLASSIFICATION,
)


def _requirement(name="value_relation"):
    return ProofRequirementId.create(
        name,
        ("pair", ("left", 1), ("right", 2)),
        ProofRequirementContract(
            proposition="equal_on_region",
            relation_direction="bidirectional",
            observation_surface=("return",),
            active_precondition=("guard", "g0"),
        ),
    )


def _attempt_key(*, budget=5.0, premise="p0"):
    return AttemptKey(
        obligation_instance_id=("obligation", premise),
        producer_id="test",
        producer_version="1",
        encoding_version="1",
        solver_identity=("z3",),
        timeout_budget=budget,
    )


def test_attempt_cache_lookup_excludes_attempt_generation():
    cache = AttemptCache()
    key = _attempt_key()
    cache.put(key, AttemptCacheEntry("timeout", "digest", 10, 1.2, retry_eligible=True))
    assert cache.get(_attempt_key()).outcome == "timeout"
    assert cache.get(_attempt_key(budget=30.0)) is None
    assert cache.get(_attempt_key(premise="p1")) is None


def test_attempt_cache_evicts_least_recently_used_entry():
    cache = AttemptCache(max_entries=2)
    cache.put(_attempt_key(premise="p0"), AttemptCacheEntry("p0", "d0", 1, 0))
    cache.put(_attempt_key(premise="p1"), AttemptCacheEntry("p1", "d1", 1, 0))
    assert cache.get(_attempt_key(premise="p0")).outcome == "p0"
    cache.put(_attempt_key(premise="p2"), AttemptCacheEntry("p2", "d2", 1, 0))
    assert cache.get(_attempt_key(premise="p1")) is None


def test_snapshot_fingerprint_ignores_diagnostic_refs_and_rejects_opaque_objects():
    first = AnalysisSnapshot.create(("binary", "function"), {"returns": ((1, 32),)}, diagnostic_refs={"obj": object()})
    second = AnalysisSnapshot.create(("binary", "function"), {"returns": ((1, 32),)}, diagnostic_refs={})
    assert first.semantic_fingerprint == second.semantic_fingerprint
    with pytest.raises(TypeError, match="opaque object"):
        SnapshotFingerprintCodec.digest(object())


def test_snapshot_fingerprint_rejects_opaque_mapping_keys():
    with pytest.raises(TypeError, match="opaque object"):
        SnapshotFingerprintCodec.digest({object(): 1})


def test_snapshot_fingerprint_canonicalizes_stable_mapping_keys():
    class StableKey:
        def __init__(self, value):
            self.value = value

        def stable_key(self):
            return ("stable", self.value)

    first = SnapshotFingerprintCodec.digest({StableKey(2): "b", StableKey(1): "a"})
    second = SnapshotFingerprintCodec.digest({StableKey(1): "a", StableKey(2): "b"})
    assert first == second


def test_function_analysis_snapshot_ignores_later_completed_proof_mutation():
    from scripts.function_tracer_pcode.model.analysis import FunctionReturnAnalysis

    analysis = FunctionReturnAnalysis("f", "0x1000", [], [], binary_id="B1")
    before = AnalysisSnapshot.from_function_analysis(analysis)
    analysis.completed_recovery_proof_ids = (("proof", 1),)
    analysis.completed_recovery_proof_evidence = ({"status": "complete"},)
    analysis.analysis_notes.append("diagnostic:only")
    after = AnalysisSnapshot.from_function_analysis(analysis)
    assert before.semantic_fingerprint == after.semantic_fingerprint


def test_function_analysis_snapshot_includes_semantic_notes_and_effect_summary():
    from scripts.function_tracer_pcode.analysis.effect_models import EffectSummary
    from scripts.function_tracer_pcode.model.analysis import FunctionReturnAnalysis

    analysis = FunctionReturnAnalysis("f", "0x1000", [], [], binary_id="B1")
    base = AnalysisSnapshot.from_function_analysis(analysis)
    analysis.analysis_notes.append("return_case_coverage_gap")
    with_note = AnalysisSnapshot.from_function_analysis(analysis)
    assert base.semantic_fingerprint != with_note.semantic_fingerprint
    analysis.effect_summary = EffectSummary([], [], incomplete_reasons=("effect_path_gap",))
    with_effect = AnalysisSnapshot.from_function_analysis(analysis)
    assert with_note.semantic_fingerprint != with_effect.semantic_fingerprint


def test_snapshot_semantic_fields_are_deeply_immutable():
    snapshot = AnalysisSnapshot.create(
        ("binary", "function"), {"parameters": [{"storage": {"size": 4}}]}
    )
    with pytest.raises(TypeError):
        snapshot.semantic_fields["parameters"] = ()
    with pytest.raises(TypeError):
        snapshot.semantic_fields["parameters"][0]["storage"]["size"] = 8


def test_function_analysis_snapshot_field_inventory_is_complete():
    from scripts.function_tracer_pcode.model.analysis import FunctionReturnAnalysis

    assert {item.name for item in fields(FunctionReturnAnalysis)} == set(
        FUNCTION_ANALYSIS_FIELD_CLASSIFICATION
    )


def test_derived_view_tracks_artifact_independent_facts():
    artifact_id = ("artifact", 1)
    base_fact = ("guard", "g0")
    derived_fact = ("guard", "g1")
    view = DerivedAnalysisView.create(
        snapshot_id=("snapshot",),
        parent_view_id=None,
        validated_proof_closure_id=("closure",),
        normalization_policy_digest="policy",
        view_builder_version="1",
        semantic_surface={"guards": ("g0", "g1")},
        fact_provenance={
            base_fact: SemanticFactProvenance(base_fact, source_snapshot_fact_ids=(base_fact,)),
            derived_fact: SemanticFactProvenance(derived_fact, source_artifact_ids=(artifact_id,)),
        },
    )
    assert view.artifact_independent_fact_ids(artifact_id) == (base_fact,)


def test_proof_closure_rejects_direct_and_transitive_cycles():
    requirement = _requirement()
    views = {("v0",): ViewPremiseRecord(("v0",), "p", (("a",), ("b",)))}
    direct = ProofArtifact(("a",), requirement, ("v0",), "p", dependency_artifact_ids=(("a",),), artifact_validation_status="validated")
    with pytest.raises(ValueError, match="self-justifying"):
        validate_proof_closure([direct], [("a",)], views)

    a = ProofArtifact(("a",), requirement, ("v0",), "p", dependency_artifact_ids=(("b",),), artifact_validation_status="validated")
    b = ProofArtifact(("b",), requirement, ("v0",), "p", dependency_artifact_ids=(("a",),), artifact_validation_status="validated")
    with pytest.raises(ValueError, match="cyclic"):
        validate_proof_closure([a, b], [("a",)], views)


def test_proof_closure_rejects_unknown_view_premise_and_unavailable_dependency():
    requirement = _requirement()
    artifact = ProofArtifact(("a",), requirement, ("missing",), "p", artifact_validation_status="validated")
    with pytest.raises(ValueError, match="unknown proof source view"):
        validate_proof_closure([artifact], [("a",)], {})
    artifact = ProofArtifact(("a",), requirement, ("v0",), "wrong", artifact_validation_status="validated")
    with pytest.raises(ValueError, match="premise mismatch"):
        validate_proof_closure([artifact], [("a",)], {("v0",): ViewPremiseRecord(("v0",), "p")})


def test_proof_closure_rejects_duplicate_artifact_ids():
    first = ProofArtifact(
        ("same",), _requirement("first"), ("v0",), "p", artifact_validation_status="validated"
    )
    second = ProofArtifact(
        ("same",), _requirement("second"), ("v0",), "p", artifact_validation_status="validated"
    )
    with pytest.raises(ValueError, match="duplicate proof artifact ids"):
        validate_proof_closure(
            [first, second],
            [("same",)],
            {("v0",): ViewPremiseRecord(("v0",), "p")},
        )


def test_proof_cache_rejects_unvalidated_artifact():
    artifact = ProofArtifact(("a",), _requirement(), ("v0",), "p")
    with pytest.raises(ValueError, match="validated"):
        ProofCache().put(
            artifact,
            artifacts=[artifact],
            root_artifact_ids=[("a",)],
            view_records={("v0",): ViewPremiseRecord(("v0",), "p")},
            target_view=ViewPremiseRecord(("v1",), "p1"),
            candidate_independent_premise_digest="p1",
        )


def test_proof_cache_requires_candidate_independent_applicability():
    requirement = _requirement()
    artifact = ProofArtifact(("a",), requirement, ("v0",), "p", artifact_validation_status="validated")
    with pytest.raises(ValueError, match="candidate-independent"):
        ProofCache().put(
            artifact,
            artifacts=[artifact],
            root_artifact_ids=[("a",)],
            view_records={("v0",): ViewPremiseRecord(("v0",), "p")},
            target_view=ViewPremiseRecord(("v1",), "p1"),
            candidate_independent_premise_digest="different",
        )


def test_proof_cache_keys_validated_artifact_to_target_view_and_premise():
    artifact = ProofArtifact(
        ("a",), _requirement(), ("v0",), "p0", artifact_validation_status="validated"
    )
    source = ViewPremiseRecord(("v0",), "p0")
    cache = ProofCache()
    entry = cache.put(
        artifact,
        artifacts=[artifact],
        root_artifact_ids=[("a",)],
        view_records={("v0",): source},
        target_view=ViewPremiseRecord(("v1",), "p1"),
        candidate_independent_premise_digest="p1",
    )
    assert cache.get(ProofCache.key(entry)) is entry


def test_replaced_applicability_record_cannot_be_supplied_to_proof_cache():
    from dataclasses import replace

    artifact = ProofArtifact(
        ("a",), _requirement(), ("v0",), "p0", artifact_validation_status="validated"
    )
    source = ViewPremiseRecord(("v0",), "p0")
    closure = validate_proof_closure([artifact], [("a",)], {("v0",): source})
    rejected = validate_artifact_applicability(
        artifact,
        source_view=source,
        target_view=ViewPremiseRecord(("v1",), "p1"),
        candidate_independent_premise_digest="different",
        validated_closure_id=closure.closure_id,
    )
    forged = replace(rejected, candidate_independent=True, status="applicable")
    assert forged.status == "applicable"
    # ProofCache.put has no parameter accepting an applicability record or closure.
    with pytest.raises(TypeError):
        ProofCache().put(forged, closure)


def test_proof_cache_recomputes_closure_and_rejects_unrelated_roots():
    artifact = ProofArtifact(
        ("a",), _requirement(), ("v0",), "p0", artifact_validation_status="validated"
    )
    source = ViewPremiseRecord(("v0",), "p0")
    other = ProofArtifact(
        ("b",), _requirement("other"), ("v0",), "p0", artifact_validation_status="validated"
    )
    with pytest.raises(ValueError, match="absent from validated closure"):
        ProofCache().put(
            artifact,
            artifacts=[artifact, other],
            root_artifact_ids=[("b",)],
            view_records={("v0",): source},
            target_view=ViewPremiseRecord(("v1",), "p1"),
            candidate_independent_premise_digest="p1",
        )


def test_proof_cache_rejects_different_artifact_with_same_id():
    good = ProofArtifact(
        ("same",), _requirement("good"), ("v0",), "p0", artifact_validation_status="validated"
    )
    bad = ProofArtifact(
        ("same",),
        _requirement("bad"),
        ("v0",),
        "p0",
        dependency_artifact_ids=(("missing",),),
        artifact_validation_status="validated",
        payload={"proof": "different"},
    )
    with pytest.raises(ValueError, match="exact process-local artifact"):
        ProofCache().put(
            bad,
            artifacts=[good],
            root_artifact_ids=[("same",)],
            view_records={("v0",): ViewPremiseRecord(("v0",), "p0")},
            target_view=ViewPremiseRecord(("v1",), "p1"),
            candidate_independent_premise_digest="p1",
        )


def test_proof_cache_rejects_duplicate_target_id_collection():
    first = ProofArtifact(
        ("same",), _requirement("first"), ("v0",), "p0", artifact_validation_status="validated"
    )
    second = ProofArtifact(
        ("same",), _requirement("second"), ("v0",), "p0", artifact_validation_status="validated"
    )
    with pytest.raises(ValueError, match="exactly one validated artifact"):
        ProofCache().put(
            first,
            artifacts=[first, second],
            root_artifact_ids=[("same",)],
            view_records={("v0",): ViewPremiseRecord(("v0",), "p0")},
            target_view=ViewPremiseRecord(("v1",), "p1"),
            candidate_independent_premise_digest="p1",
        )


def test_closure_digest_covers_every_semantic_field():
    from dataclasses import replace

    artifact = ProofArtifact(
        ("a",), _requirement(), ("v0",), "p0", artifact_validation_status="validated"
    )
    closure = validate_proof_closure(
        [artifact], [("a",)], {("v0",): ViewPremiseRecord(("v0",), "p0")}
    )
    assert closure.is_internally_consistent
    assert not replace(closure, closure_id=("forged",)).is_internally_consistent
    assert not replace(closure, transitive_dependency_ids=(("forged",),)).is_internally_consistent


def test_artifact_applicability_checks_candidate_independent_premise():
    artifact = ProofArtifact(("a",), _requirement(), ("v0",), "p0", artifact_validation_status="validated")
    record = validate_artifact_applicability(
        artifact,
        source_view=ViewPremiseRecord(("v0",), "p0"),
        target_view=ViewPremiseRecord(("v1",), "p1"),
        candidate_independent_premise_digest="different",
        validated_closure_id=("closure",),
    )
    assert record.status == "requires_reproof"


def test_branch_activation_short_circuits_after_terminal_result():
    controller = BranchActivationController(
        [BranchSpec("pairwise"), BranchSpec("recursive"), BranchSpec("monolithic")]
    )
    assert controller.next_branch({}) == "pairwise"
    controller.record("pairwise", FunctionProofOutcome.EQUIVALENT)
    assert controller.next_branch({"pairwise": FunctionProofOutcome.EQUIVALENT}) is None
    assert controller.states["recursive"] == ActivationState.SHORT_CIRCUITED
    assert controller.states["monolithic"] == ActivationState.SHORT_CIRCUITED


def test_dormant_branch_outcome_cannot_short_circuit_active_order():
    controller = BranchActivationController([BranchSpec("pairwise"), BranchSpec("monolithic")])
    assert controller.next_branch({"monolithic": FunctionProofOutcome.NOT_EQUIVALENT}) == "pairwise"
    assert controller.outcomes == {}


def test_inapplicable_branch_is_not_a_proof_blocker():
    controller = BranchActivationController(
        [
            BranchSpec("pairwise"),
            BranchSpec("loop", eligibility=lambda outcomes: False),
            BranchSpec("recursive"),
        ]
    )
    assert controller.next_branch({}) == "pairwise"
    controller.record("pairwise", FunctionProofOutcome.INCONCLUSIVE)
    assert controller.next_branch({"pairwise": FunctionProofOutcome.INCONCLUSIVE}) == "recursive"
    assert controller.states["loop"] == ActivationState.INAPPLICABLE


def test_proof_expression_all_of_and_any_of():
    eq = ProofExpression("eq", ProofNodeKind.LEAF_OBLIGATION, leaf_outcome=FunctionProofOutcome.EQUIVALENT)
    unknown = ProofExpression("unknown", ProofNodeKind.LEAF_OBLIGATION)
    assert ProofExpressionEvaluator.evaluate(ProofExpression("all", ProofNodeKind.ALL_OF, (eq, unknown))).outcome == FunctionProofOutcome.INCONCLUSIVE
    assert ProofExpressionEvaluator.evaluate(ProofExpression("any", ProofNodeKind.ANY_OF, (unknown, eq))).outcome == FunctionProofOutcome.EQUIVALENT


def test_proof_expression_conflict_prefers_not_equivalent():
    eq = ProofExpression("eq", ProofNodeKind.LEAF_OBLIGATION, leaf_outcome=FunctionProofOutcome.EQUIVALENT)
    not_eq = ProofExpression("cex", ProofNodeKind.DECISIVE, leaf_outcome=FunctionProofOutcome.NOT_EQUIVALENT)
    result = ProofExpressionEvaluator.evaluate(ProofExpression("root", ProofNodeKind.ANY_OF, (eq, not_eq)))
    assert result.outcome == FunctionProofOutcome.NOT_EQUIVALENT
    assert result.conflict_detected is True


def test_supersede_view_invalidates_completed_obligations():
    worklist = ProofWorklist()
    obligation = ObligationInstanceId(_requirement(), ("v0",), "p")
    item = WorkItem(obligation, "guard")
    assert worklist.add(item)
    assert worklist.pop() is item
    worklist.complete(item)
    assert worklist.supersede_view(("v0",)) == 1
    assert item.state.value == "superseded"


def test_pairwise_solver_attempt_cache_reuses_identical_query(monkeypatch):
    from scripts.function_tracer_pcode.equivalence.strategies import pairwise_query_executor as executor

    calls = []
    parallel = SimpleNamespace(
        is_equivalent=True,
        results=[SimpleNamespace(elapsed_time=0.25, status="unsat", error_message=None)],
        get_counterexample=lambda: None,
    )

    def fake_run(_runner, _query, timeout):
        calls.append(timeout)
        return parallel

    monkeypatch.setattr(executor, "_run_query_with_timeout", fake_run)
    strategy = SimpleNamespace(
        per_query_timeout=5,
        per_query_timeout_hard=30,
        solver_runner=SimpleNamespace(solvers=[]),
        save_unknown_queries=False,
        _exact_query_attempt_cache=AttemptCache(),
        _active_normalization_stats={},
        _debug_print=lambda _message: None,
    )
    first = executor.solve_query_internal(strategy, "(check-sat)", "(0,0)", "conds-only")
    second = executor.solve_query_internal(strategy, "(check-sat)", "(4,7)", "conds-only")
    assert first.is_equivalent is True and second.is_equivalent is True
    assert calls == [5]
    assert strategy._active_normalization_stats["exact_query_attempt_cache_hits"] == 1
