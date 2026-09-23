from types import SimpleNamespace
from dataclasses import fields

import pytest

from scripts.function_tracer_pcode.proof.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
)
from scripts.function_tracer_pcode.proof.obligations import (
    ActivationState,
    AnalysisSnapshot,
    AttemptCache,
    AttemptCacheEntry,
    AttemptKey,
    BranchActivationController,
    BranchSpec,
    DerivedAnalysisView,
    DecisionAggregator,
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
    ObligationRuntimeSession,
    SolverQueryExecutionReceipt,
    validate_artifact_applicability,
    validate_proof_closure,
    UnaryProducerResult,
    prove_unary_partition,
)
from scripts.function_tracer_pcode.proof.obligations.snapshot import (
    FUNCTION_ANALYSIS_FIELD_CLASSIFICATION,
)


@pytest.fixture(autouse=True)
def _runtime_work_belongs_to_one_comparison():
    """runtime の仕事は 1 つの比較（raw pair と最終 relation）の中で行う（Issue #167）。

    この module は runtime の仕組み（view・再計画・cache）を確かめる。比較の authority の
    規則そのものは ``test_input_correspondence_binding.py``。
    """

    from scripts.function_tracer_pcode.proof.formula.input_correspondence import comparison_scope
    from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import fixed_test_comparison

    with comparison_scope(fixed_test_comparison()):
        yield


def _apply_in_comparison(runtime, wrappers, **kwargs):
    """この比較の中で作った完了証拠として runtime に渡す。"""

    from scripts.function_tracer_pcode.core.evidence_authority import evidence_authority_scope
    from scripts.function_tracer_pcode.proof.formula.input_correspondence import bind_evidence_to_comparison

    bound = []
    for wrapper in wrappers:
        evidence = dict(wrapper.get("evidence", wrapper))
        if evidence_authority_scope(evidence) is None:
            bind_evidence_to_comparison(evidence)
        bound.append({**wrapper, "evidence": evidence} if "evidence" in wrapper else evidence)
    return runtime.apply_completed_evidence(tuple(bound), **kwargs)


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
    from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis

    analysis = FunctionReturnAnalysis("f", "0x1000", [], [], binary_id="B1")
    before = AnalysisSnapshot.from_function_analysis(analysis)
    analysis.completed_recovery_proof_ids = (("proof", 1),)
    analysis.completed_recovery_proof_evidence = ({"status": "complete"},)
    analysis.analysis_notes.append("diagnostic:only")
    after = AnalysisSnapshot.from_function_analysis(analysis)
    assert before.semantic_fingerprint == after.semantic_fingerprint


def test_function_analysis_snapshot_includes_semantic_notes_and_effect_summary():
    from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary
    from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis

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
    from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis

    assert {item.name for item in fields(FunctionReturnAnalysis)} == set(
        FUNCTION_ANALYSIS_FIELD_CLASSIFICATION
    )


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


def test_unary_view_identity_excludes_pair_peer():
    analysis = SimpleNamespace(function_name="left", entry_point="0x1", binary_id="bin", outcome_seed=None)
    first = ObligationRuntimeSession.create_unary(
        analysis,
        domain_contract=("all_inputs",),
        normalization_policy_digest="norm-v1",
    )
    second = ObligationRuntimeSession.create_unary(
        analysis,
        domain_contract=("all_inputs",),
        normalization_policy_digest="norm-v1",
    )
    assert first.premise_digest == second.premise_digest
    assert first.current_view.snapshot_id == second.current_view.snapshot_id


def test_unary_view_changes_with_function_snapshot():
    first = ObligationRuntimeSession.create_unary(
        SimpleNamespace(function_name="left", entry_point="0x1", binary_id="bin", outcome_seed=None),
        domain_contract=("all_inputs",),
        normalization_policy_digest="norm-v1",
    )
    second = ObligationRuntimeSession.create_unary(
        SimpleNamespace(function_name="other", entry_point="0x2", binary_id="bin", outcome_seed=None),
        domain_contract=("all_inputs",),
        normalization_policy_digest="norm-v1",
    )
    assert first.premise_digest != second.premise_digest


class _UnarySeed:
    function_identity = ("function", "bin-a", 0x1000)
    input_domain_contract = ("all_inputs",)
    partition_revision = 1
    extraction_schema_version = 1

    def stable_key(self):
        return ("unary_seed", self.function_identity, self.partition_revision)


def _unary_analysis(name="f", seed=None):
    return SimpleNamespace(
        function_name=name,
        entry_point="0x1000",
        binary_id="bin-a",
        outcome_seed=seed or _UnarySeed(),
    )


def _proved_unary_producers(counter=None):
    def producer():
        if counter is not None:
            counter[0] += 1
        return UnaryProducerResult("proved")
    return {
        stage: producer
        for stage in (
            "termination_classification", "cfg_reachability", "path_region_completeness", "member_classification",
            "same_kind_consistency", "cross_kind_disjointness", "residual_totality",
            "partition_complete",
        )
    }


def test_validated_unary_artifact_cache_reuses_exact_function_premise():
    counter = [0]
    first = prove_unary_partition(
        _unary_analysis(),
        domain_contract=("all_inputs",),
        normalization_policy_digest="norm-v1",
        producers=_proved_unary_producers(counter),
    )
    assert first.complete
    assert len(first.cache_entry.closure_artifacts) == 8
    assert counter[0] == 8
    second = prove_unary_partition(
        _unary_analysis(),
        domain_contract=("all_inputs",),
        normalization_policy_digest="norm-v1",
        producers=_proved_unary_producers(counter),
    )
    assert second.complete
    assert second.final_artifact.artifact_id == first.final_artifact.artifact_id
    assert counter[0] == 8


def test_imported_unary_artifact_preserves_source_closure_dependency():
    left = _unary_analysis()
    proof = prove_unary_partition(
        left,
        domain_contract=("all_inputs",),
        normalization_policy_digest="norm-import-v1",
        producers=_proved_unary_producers(),
    )
    pair = ObligationRuntimeSession.create(
        left,
        SimpleNamespace(function_name="g", entry_point="0x2000", binary_id="bin-b"),
    )
    pair.import_unary_artifact_for_analysis(
        proof.cache_entry,
        analysis=left,
        pair_side="left",
        domain_contract=("all_inputs",),
        normalization_policy_digest="norm-import-v1",
    )
    imported = pair.artifacts[-1]
    assert proof.final_artifact.artifact_id in imported.dependency_artifact_ids
    validate_proof_closure(pair.artifacts, (imported.artifact_id,), pair.view_records)


def test_unary_artifact_cache_rejects_stale_seed_surface():
    left = _unary_analysis()
    proof = prove_unary_partition(
        left,
        domain_contract=("all_inputs",),
        normalization_policy_digest="norm-stale-v1",
        producers=_proved_unary_producers(),
    )
    pair = ObligationRuntimeSession.create(
        left,
        SimpleNamespace(function_name="g", entry_point="0x2000", binary_id="bin-b"),
    )
    left.outcome_seed = SimpleNamespace(
        stable_key=lambda: ("changed_seed",),
        input_domain_contract=("all_inputs",),
    )
    with pytest.raises(ValueError, match="function premise mismatch"):
        pair.import_unary_artifact_for_analysis(
            proof.cache_entry,
            analysis=left,
            pair_side="left",
            domain_contract=("all_inputs",),
            normalization_policy_digest="norm-stale-v1",
        )


def test_unary_artifact_import_rejects_different_pair_side_analysis():
    left = _unary_analysis()
    other = SimpleNamespace(function_name="x", entry_point="0x9000", binary_id="bin-x", outcome_seed=_UnarySeed())
    proof = prove_unary_partition(
        left,
        domain_contract=("all_inputs",),
        normalization_policy_digest="norm-wrong-side-v1",
        producers=_proved_unary_producers(),
    )
    pair = ObligationRuntimeSession.create(left, other)
    with pytest.raises(ValueError, match="function premise mismatch"):
        pair.import_unary_artifact_for_analysis(
            proof.cache_entry,
            analysis=other,
            pair_side="right",
            domain_contract=("all_inputs",),
            normalization_policy_digest="norm-wrong-side-v1",
        )


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


def test_runtime_completed_proof_builds_derived_view_and_reschedules_only_dependents():
    left = SimpleNamespace(binary_id="B1", function_name="f", entry_point="0x1000")
    right = SimpleNamespace(binary_id="B2", function_name="f", entry_point="0x1000")
    runtime = ObligationRuntimeSession.create(left, right)
    coverage = _requirement("return_coverage")
    related = _requirement("guard_overlap")
    unrelated = _requirement("call_effect")
    calls = {"related": 0, "unrelated": 0}

    def run_related():
        calls["related"] += 1
        return "new_guard_result"

    def run_unrelated():
        calls["unrelated"] += 1
        return "unrelated_result"

    old_related = runtime.schedule(
        related, "guard_overlap", run_related, depends_on=(coverage,)
    )
    old_unrelated = runtime.schedule(unrelated, "call_effect", run_unrelated)

    evidence = {
        "proof_requirement_id": coverage.to_dict(),
        "status": "complete",
        "proof_source": "test_coverage_producer",
        "proof_content": {"coverage": "proven"},
    }
    runtime.proof_outcomes[coverage.to_key()] = FunctionProofOutcome.EQUIVALENT
    views = _apply_in_comparison(runtime, ({"evidence": evidence},))

    assert len(views) == 1
    assert views[0].parent_view_id == runtime.base_view.view_id
    assert views[0].validated_proof_closure_id != ("proof_closure", ())
    assert runtime.view_records[views[0].view_id].premise_digest != (
        runtime.view_records[runtime.base_view.view_id].premise_digest
    )
    assert old_related.state.value == "superseded"
    assert old_unrelated.state.value == "superseded"
    new_items = [
        item for item in runtime.worklist.items()
        if item.obligation_id.derived_view_id == views[0].view_id
    ]
    assert [item.kind for item in new_items] == ["guard_overlap"]
    while runtime.run_next()[0] is not None:
        pass
    assert calls == {"related": 1, "unrelated": 0}


def test_runtime_rejects_untyped_completion_and_does_not_change_view():
    runtime = ObligationRuntimeSession.create(
        SimpleNamespace(binary_id="B1", function_name="f", entry_point="0x1000"),
        SimpleNamespace(binary_id="B2", function_name="f", entry_point="0x1000"),
    )
    before = runtime.current_view
    assert _apply_in_comparison(runtime, ({
        "evidence": {"status": "complete", "proof_obligation_id": ("legacy",)},
    },)) == ()
    assert runtime.current_view is before


def test_runtime_rejects_typed_status_without_producer_validation():
    runtime = ObligationRuntimeSession.create(
        SimpleNamespace(binary_id="B1", function_name="f", entry_point="0x1000"),
        SimpleNamespace(binary_id="B2", function_name="f", entry_point="0x1000"),
    )
    requirement = _requirement("return_coverage")
    assert _apply_in_comparison(runtime, ({"evidence": {
        "proof_requirement_id": requirement.to_dict(),
        "status": "complete",
    }},)) == ()
    assert runtime.artifacts == []


def test_runtime_resolves_unique_legacy_obligation_to_typed_requirement():
    runtime = ObligationRuntimeSession.create(
        SimpleNamespace(binary_id="B1", function_name="f", entry_point="0x1000"),
        SimpleNamespace(binary_id="B2", function_name="f", entry_point="0x1000"),
    )
    requirement = _requirement("return_width")
    reason = SimpleNamespace(
        proof_obligation_id=("legacy", "width"),
        proof_requirement_ids=(requirement.to_dict(),),
    )
    runtime.proof_outcomes[requirement.to_key()] = FunctionProofOutcome.EQUIVALENT
    views = _apply_in_comparison(runtime, ({
        "evidence": {
            "status": "complete",
            "proof_obligation_id": ("legacy", "width"),
            "proof_source": "width_producer",
        },
    },), reasons=(reason,))
    assert len(views) == 1
    assert runtime.artifacts[0].requirement_id == requirement


def test_runtime_rejects_ambiguous_legacy_obligation_mapping():
    runtime = ObligationRuntimeSession.create(
        SimpleNamespace(binary_id="B1", function_name="f", entry_point="0x1000"),
        SimpleNamespace(binary_id="B2", function_name="f", entry_point="0x1000"),
    )
    reason = SimpleNamespace(
        proof_obligation_id=("legacy", "shared"),
        proof_requirement_ids=(
            _requirement("return_width").to_dict(),
            _requirement("value_relation").to_dict(),
        ),
    )
    assert _apply_in_comparison(runtime, ({
        "evidence": {"status": "complete", "proof_obligation_id": ("legacy", "shared")},
    },), reasons=(reason,)) == ()


def test_running_producer_can_supersede_its_parent_view():
    left = SimpleNamespace(binary_id="B1", function_name="f", entry_point="0x1000")
    right = SimpleNamespace(binary_id="B2", function_name="f", entry_point="0x1000")
    runtime = ObligationRuntimeSession.create(left, right)
    branch = _requirement("function_branch")
    coverage = _requirement("return_coverage")
    runtime.proof_outcomes[coverage.to_key()] = FunctionProofOutcome.EQUIVALENT

    def produce_derived_view():
        _apply_in_comparison(runtime, ({"evidence": {
            "proof_requirement_id": coverage.to_dict(),
            "status": "complete",
            "proof_source": "test_coverage_producer",
            "proof_content": {"coverage": "proven"},
        }},))
        return "branch_result"

    item = runtime.schedule(branch, "function_branch", produce_derived_view)
    popped, result = runtime.run_next()
    assert popped is item
    assert result == "branch_result"
    assert item.state.value == "superseded"
    assert runtime.events[-1].event == "completed_superseded"


def test_decision_aggregator_turns_proof_closed_global_blocker_into_eq():
    runtime = ObligationRuntimeSession.create(
        SimpleNamespace(binary_id="B1", function_name="f", entry_point="0x1000"),
        SimpleNamespace(binary_id="B2", function_name="f", entry_point="0x1000"),
    )
    requirement = _requirement("return_coverage")
    reason = SimpleNamespace(reason_id="return_coverage_gap", pair_or_case=None)
    runtime.proof_outcomes[requirement.to_key()] = FunctionProofOutcome.EQUIVALENT
    _apply_in_comparison(runtime, ({"evidence": {
        "proof_requirement_id": requirement.to_dict(),
        "status": "complete",
        "proof_source": "coverage_test",
    }},))
    runtime.reason_requirements[id(reason)] = (requirement,)
    runtime.planned_reasons[id(reason)] = reason
    runtime.proof_outcomes[requirement.to_key()] = FunctionProofOutcome.EQUIVALENT
    result = SimpleNamespace(
        is_equivalent=None,
        unknown_reasons=[reason],
        unknown_recovery_actions=[],
        decision_gated_by_pending_proof=True,
        pairwise_stats={
            "total_pairs": 4,
            "unsat_pairs": 4,
            "sat_pairs": 0,
            "unknown_pairs": 0,
            "error_pairs": 0,
        },
    )
    decision = DecisionAggregator.apply(result, runtime)
    assert decision.outcome == FunctionProofOutcome.EQUIVALENT
    assert result.is_equivalent is True
    assert result.unknown_reasons == []


def test_decision_aggregator_does_not_reclassify_proof_closed_reason_as_pair_unsat():
    runtime = ObligationRuntimeSession.create(
        SimpleNamespace(binary_id="B1", function_name="f", entry_point="0x1000"),
        SimpleNamespace(binary_id="B2", function_name="f", entry_point="0x1000"),
    )
    requirement = _requirement("value_relation")
    reason = SimpleNamespace(reason_id="return_width_bridge_missing", pair_or_case="(0,1)")
    runtime.proof_outcomes[requirement.to_key()] = FunctionProofOutcome.EQUIVALENT
    _apply_in_comparison(runtime, ({"evidence": {
        "proof_requirement_id": requirement.to_dict(),
        "status": "complete",
        "proof_source": "value_test",
    }},))
    runtime.reason_requirements[id(reason)] = (requirement,)
    runtime.planned_reasons[id(reason)] = reason
    runtime.proof_outcomes[requirement.to_key()] = FunctionProofOutcome.EQUIVALENT
    result = SimpleNamespace(
        is_equivalent=None,
        unknown_reasons=[reason],
        unknown_recovery_actions=[],
        decision_gated_by_pending_proof=True,
        pairwise_stats={
            "total_pairs": 2,
            "unsat_pairs": 1,
            "sat_pairs": 0,
            "unknown_pairs": 1,
            "error_pairs": 0,
        },
    )
    DecisionAggregator.apply(result, runtime)
    assert result.is_equivalent is None
    assert result.unknown_reasons == []
    assert result.pairwise_stats["unknown_pairs"] == 1
    assert result.pairwise_stats["unsat_pairs"] == 1


def test_typed_query_reuse_reexecutes_only_changed_semantic_pair():
    from unittest.mock import Mock

    from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.core import Expression, ReturnInfo
    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
    from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis

    solver = Mock()
    solver.run_sequential.side_effect = [
        ParallelResult(results=[SolverResult("z3", SolverStatus.SAT, elapsed_time=0.001)]),
        ParallelResult(results=[SolverResult("z3", SolverStatus.UNSAT, elapsed_time=0.001)]),
        ParallelResult(results=[SolverResult("z3", SolverStatus.UNSAT, elapsed_time=0.001)]),
    ]
    strategy = PairwiseStrategy(
        FormulaBuilder(),
        solver,
        enable_completed_recovery_proofs=False,
    )
    left = create_mock_analysis(
        "left", returns=[ReturnInfo("0x1000", Expression.constant(1, 4), [])]
    )
    right = create_mock_analysis(
        "right", returns=[ReturnInfo("0x2000", Expression.constant(1, 4), [])]
    )
    runtime = ObligationRuntimeSession.create(left, right)
    strategy._obligation_runtime_session = runtime

    first = strategy.check(left, right)
    calls_after_first = solver.run_sequential.call_count
    second = strategy.check(left, right)
    assert first.is_equivalent is True
    assert second.is_equivalent is True
    assert solver.run_sequential.call_count == calls_after_first
    assert second.pairwise_debug_stats["guard_overlap_logical_edges"] == 1
    assert second.pairwise_debug_stats["guard_overlap_value_candidates"] == 1
    assert any(event.event == "result_reused" for event in runtime.events)
    assert any(event.kind == "guard_overlap" for event in runtime.events)
    query_completions = len([
        event for event in runtime.events
        if event.kind in {"guard_overlap", "value_relation"}
        and event.event == "completed"
    ])
    assert query_completions == 2

    changed = create_mock_analysis(
        "right", returns=[ReturnInfo("0x2000", Expression.constant(2, 4), [])]
    )
    # (left, changed) は別の raw pair の比較なので、(left, right) の runtime は使えない
    # （Issue #167: runtime は 1 つの比較に仕える）。別の比較は自分の runtime を使う。
    from scripts.function_tracer_pcode.proof.obligations.runtime import ComparisonRuntimeMismatch

    with pytest.raises(ComparisonRuntimeMismatch):
        strategy.check(left, changed)
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, changed)
    changed_result = strategy.check(left, changed)
    assert changed_result.pairwise_debug_stats["guard_overlap_logical_edges"] == 1
    assert solver.run_sequential.call_count > calls_after_first


def test_gate_completion_requires_real_replanned_query_outcome():
    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult

    runtime = ObligationRuntimeSession.create(
        SimpleNamespace(binary_id="B1", function_name="f", entry_point="0x1000"),
        SimpleNamespace(binary_id="B2", function_name="f", entry_point="0x1000"),
    )
    gate = _requirement("abi_relation_high_bit_proof")
    target = ("return_width_bridge", "pair-0")
    reason = SimpleNamespace(
        reason_id="return_width_bridge_missing",
        recovery_proof_kind="abi_relation_high_bit_proof",
        proof_requirement_ids=(gate.to_dict(),),
        object_target_key=target,
        pair_or_case="(0,0)",
        stage="S_PAIRWISE",
    )
    query_runs = []

    def replan_value_query():
        requirement = _requirement("value_relation_replanned")

        def run_query():
            query_runs.append(runtime.current_view.view_id)
            return QueryResult(None)

        return requirement, "value_relation", run_query

    runtime.register_target_query_replanner(target, replan_value_query)
    result = SimpleNamespace(unknown_reasons=[reason])
    runtime.plan_proof_gates(
        result,
        {"abi_relation_high_bit_proof": "return_width"},
        lambda *_args: lambda: FunctionProofOutcome.EQUIVALENT,
    )
    while runtime.run_next()[0] is not None:
        pass
    evidence = {
        "proof_requirement_id": gate.to_dict(),
        "status": "complete",
        "proof_source": "width_gate_test",
    }
    assert _apply_in_comparison(runtime, ({"evidence": evidence},), reasons=(reason,))
    while runtime.run_next()[0] is not None:
        pass

    assert len(query_runs) == 1
    assert query_runs[0] == runtime.current_view.view_id
    assert runtime.outcome_for_reason(reason) == FunctionProofOutcome.INCONCLUSIVE


def test_replanned_sat_value_query_stays_unknown_until_counterexample_is_safe():
    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult

    runtime = ObligationRuntimeSession.create(
        SimpleNamespace(binary_id="B1", function_name="f", entry_point="0x1000"),
        SimpleNamespace(binary_id="B2", function_name="f", entry_point="0x1000"),
    )
    gate = _requirement("abi_relation_high_bit_proof")
    target = ("return_width_bridge", "pair-sat")
    reason = SimpleNamespace(
        reason_id="return_width_bridge_missing",
        recovery_proof_kind="abi_relation_high_bit_proof",
        proof_requirement_ids=(gate.to_dict(),),
        object_target_key=target,
        pair_or_case="(0,0)",
        stage="S_PAIRWISE",
    )
    model = {"x": 1}
    safety_runs = []

    def replan_value_query():
        requirement = ProofRequirementId.create(
            "value_relation",
            ("pair_query", "(0,0)", "with-ineq", "sat-query"),
            ProofRequirementContract(proposition="replanned value relation"),
        )
        return requirement, "value_relation", lambda: QueryResult(
            False,
            counterexample_raw=model,
        )

    def replan_safety(pending):
        requirement = _requirement("counterexample_safety_pending")

        def run_safety():
            safety_runs.append(pending.counterexample_raw)
            return FunctionProofOutcome.INCONCLUSIVE

        return requirement, "counterexample_safety", run_safety

    runtime.register_target_query_replanner(target, replan_value_query)
    runtime.register_counterexample_safety_replanner("(0,0)", replan_safety)
    runtime.plan_proof_gates(
        SimpleNamespace(unknown_reasons=[reason]),
        {"abi_relation_high_bit_proof": "return_width"},
        lambda *_args: lambda: FunctionProofOutcome.EQUIVALENT,
    )
    while runtime.run_next()[0] is not None:
        pass
    assert _apply_in_comparison(runtime, 
        ({"evidence": {
            "proof_requirement_id": gate.to_dict(),
            "status": "complete",
            "proof_source": "width_gate_test",
        }},),
        reasons=(reason,),
    )
    while runtime.run_next()[0] is not None:
        pass

    value_key = next(iter(runtime.pending_counterexamples))
    dependent_keys = runtime.requirement_dependents[gate.to_key()]
    assert value_key in dependent_keys
    assert runtime.proof_outcomes[value_key] == FunctionProofOutcome.INCONCLUSIVE
    assert runtime.pending_counterexamples[value_key].counterexample_raw == model
    assert safety_runs == [model]
    assert any(
        event.event == "counterexample_safety_scheduled"
        for event in runtime.events
    )
    assert runtime.outcome_for_reason(reason) == FunctionProofOutcome.INCONCLUSIVE
    aggregate_target = SimpleNamespace(
        is_equivalent=None,
        unknown_reasons=[reason],
        unknown_recovery_actions=[],
        decision_gated_by_pending_proof=True,
        pairwise_stats={
            "total_pairs": 1, "unsat_pairs": 0, "sat_pairs": 0,
            "unknown_pairs": 1, "error_pairs": 0,
        },
    )
    assert DecisionAggregator.apply(aggregate_target, runtime).outcome == FunctionProofOutcome.INCONCLUSIVE
    assert aggregate_target.unknown_reasons == [reason]


def test_replanned_sat_becomes_not_eq_after_counterexample_safety_completes():
    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult

    runtime = ObligationRuntimeSession.create(
        SimpleNamespace(binary_id="B1", function_name="f", entry_point="0x1000"),
        SimpleNamespace(binary_id="B2", function_name="f", entry_point="0x1000"),
    )
    gate = _requirement("coverage_proof_for_sat")
    target = ("coverage", "pair-sat-safe")
    reason = SimpleNamespace(
        reason_id="return_coverage_gap",
        recovery_proof_kind="return_coverage_completion",
        proof_requirement_ids=(gate.to_dict(),),
        object_target_key=target,
        pair_or_case="(0,0)",
        stage="S_PAIRWISE",
    )
    model = {"x": 7}

    def replan_value_query():
        requirement = ProofRequirementId.create(
            "value_relation",
            ("pair_query", "(0,0)", "with-ineq", "safe-sat-query"),
            ProofRequirementContract(proposition="replanned value relation"),
        )
        return requirement, "value_relation", lambda: QueryResult(
            False,
            counterexample_raw=model,
        )

    runtime.register_target_query_replanner(target, replan_value_query)
    runtime.register_counterexample_safety_replanner(
        "(0,0)",
        lambda pending: (
            _requirement("counterexample_safety_complete"),
            "counterexample_safety",
            lambda: (
                FunctionProofOutcome.NOT_EQUIVALENT
                if pending.counterexample_raw == model
                else FunctionProofOutcome.INCONCLUSIVE
            ),
        ),
    )
    runtime.plan_proof_gates(
        SimpleNamespace(unknown_reasons=[reason]),
        {"return_coverage_completion": "return_coverage"},
        lambda *_args: lambda: FunctionProofOutcome.EQUIVALENT,
    )
    while runtime.run_next()[0] is not None:
        pass
    assert _apply_in_comparison(runtime, 
        ({"evidence": {
            "proof_requirement_id": gate.to_dict(),
            "status": "complete",
            "proof_source": "coverage_gate_test",
        }},),
        reasons=(reason,),
    )
    while runtime.run_next()[0] is not None:
        pass

    assert runtime.outcome_for_reason(reason) == FunctionProofOutcome.NOT_EQUIVALENT
    aggregate_target = SimpleNamespace(
        is_equivalent=None,
        unknown_reasons=[reason],
        unknown_recovery_actions=[],
        decision_gated_by_pending_proof=True,
        pairwise_stats={
            "total_pairs": 1, "unsat_pairs": 0, "sat_pairs": 0,
            "unknown_pairs": 1, "error_pairs": 0,
        },
    )
    assert DecisionAggregator.apply(aggregate_target, runtime).outcome == FunctionProofOutcome.NOT_EQUIVALENT
    assert aggregate_target.is_equivalent is False


def test_pairwise_solver_attempt_cache_reuses_identical_query(monkeypatch):
    from scripts.function_tracer_pcode.proof.strategies import pairwise_query_executor as executor

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
    assert type(first.solver_query_execution_receipt) is SolverQueryExecutionReceipt
    assert first.solver_query_execution_receipt.validates_execution(
        query="(check-sat)",
        expected_disposition="unsat",
        expected_query_label="(0,0)",
    )
    assert second.solver_query_execution_receipt.validates_execution(
        query="(check-sat)",
        expected_disposition="unsat",
        expected_query_label="(4,7)",
    )
    assert second.solver_query_execution_receipt.execution_policy == "cache_reuse"
    assert calls == [5]
    assert strategy._active_normalization_stats["exact_query_attempt_cache_hits"] == 1
