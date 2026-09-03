from types import SimpleNamespace
import hashlib
import json

import pytest

from scripts.function_tracer_pcode.equivalence.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
)
from scripts.function_tracer_pcode.equivalence.call_effect_preflight import (
    TypedProjectionAssertionBundle,
    projection_binding_evidence_from_query,
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_builder import (
    _build_pairwise_extra_assertions,
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import (
    PairwiseStrategy,
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_executor import (
    execute_canonical_guard_query,
    solve_query_after_guard,
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.smt import (
    ParallelResult,
    SolverResult,
    SolverStatus,
)
from scripts.function_tracer_pcode.smt.parallel import ParallelSolverRunner
from scripts.function_tracer_pcode.equivalence.obligations import (
    GuardDisjointArtifact,
    GuardOverlapAttempt,
    GuardOverlapExecutionResult,
    GuardOverlapGraph,
    GuardQueryExecutionArtifact,
    GuardOverlapStatus,
    GuardRegionSeed,
    ObligationRuntimeSession,
    LedgerLifecycle,
    PairClosureEvidence,
    PairClosureKind,
    PairDisposition,
    PairDispositionLedger,
    PairLedgerBinding,
    CounterexampleSafetyReceipt,
    GuardUnsatClosureArtifact,
    SolverQueryExecutionReceipt,
    SolverUnsatClosureArtifact,
    StructuralEqualityClosureArtifact,
    StructuralEqualityReceipt,
    issue_structural_equality_receipt,
)
from scripts.function_tracer_pcode.model import Expression, ExpressionType, ReturnInfo


_UNSAT_QUERY = "(set-logic QF_BV)\n(assert false)\n(check-sat)"
_SAT_QUERY = "(set-logic QF_BV)\n(assert true)\n(check-sat)"
_UNKNOWN_QUERY = "(set-logic QF_BV)\n(assert invalid)\n(check-sat)"


def _solver_execution_result(
    query: str,
    status: SolverStatus,
    *,
    model=None,
    query_label="(0,0)",
):
    parallel_result = ParallelResult(
        results=[SolverResult("fake", status, model=model)]
    )
    result = SimpleNamespace(
        is_equivalent=(status == SolverStatus.UNSAT),
        counterexample_raw=model,
    )
    result.solver_query_execution_receipt = (
        SolverQueryExecutionReceipt.from_execution(
            query=query,
            query_label=query_label,
            proof_stage="value_query",
            parallel_result=parallel_result,
            solver_identity=("unit", "fake", ("fake",)),
            timeout_budget=5.0,
            use_hard_timeout=False,
        )
    )
    return result


def _seed(side, index=0):
    return GuardRegionSeed(side, index, (("eq", "x", 0),), "rendered")


def _canonical_guard_strategy():
    strategy = getattr(_canonical_guard_strategy, "strategy", None)
    if strategy is None:
        strategy = PairwiseStrategy(
            SimpleNamespace(), ParallelSolverRunner(timeout=2)
        )
        _canonical_guard_strategy.strategy = strategy
    return strategy


def _result(requirement, query):
    return execute_canonical_guard_query(
        _canonical_guard_strategy(), requirement, query, "guard-test"
    )


def test_graph_deduplicates_same_semantic_regions_and_ignores_comments():
    graph = GuardOverlapGraph(("view", 1), "premise")
    first_query = "; pair 1\n" + _UNSAT_QUERY
    second_query = "; pair 2\n(set-logic QF_BV)\n(assert  false)\n(check-sat)"
    first = graph.requirement(_seed("left", 1), _seed("right", 2), first_query)
    second = graph.requirement(_seed("left", 9), _seed("right", 8), second_query)
    assert first.stable_key() == second.stable_key()
    node = graph.record(_result(first, first_query))
    assert node.result.query_artifact is not None
    assert node.result.query_artifact.validates(
        first, node.result.attempt, node.result.raw_result
    )
    assert graph.lookup(second).disjoint_artifact is not None


@pytest.mark.parametrize("status", [GuardOverlapStatus.SAT, GuardOverlapStatus.UNKNOWN])
def test_only_unsat_creates_disjoint_artifact(status):
    graph = GuardOverlapGraph(("view",), "premise")
    query = {
        GuardOverlapStatus.SAT: _SAT_QUERY,
        GuardOverlapStatus.UNKNOWN: _UNKNOWN_QUERY,
    }[status]
    requirement = graph.requirement(_seed("left"), _seed("right"), query)
    result = _result(requirement, query)
    assert result.status == status
    assert graph.record(result).disjoint_artifact is None


def test_guard_graph_rejects_fabricated_unsat_execution_result():
    graph = GuardOverlapGraph(("view",), "premise")
    requirement = graph.requirement(_seed("left"), _seed("right"), "(check-sat)")
    attempt = GuardOverlapAttempt(
        requirement.stable_key(), GuardOverlapStatus.UNSAT,
        ("fake",), 1.0, requirement.canonical_query_digest,
    )
    with pytest.raises(ValueError, match="typed canonical query artifact"):
        graph.record(GuardOverlapExecutionResult(
            attempt, SimpleNamespace(is_equivalent=True)
        ))


def test_guard_graph_rejects_directly_constructed_query_artifact():
    graph = GuardOverlapGraph(("view",), "premise")
    requirement = graph.requirement(_seed("left"), _seed("right"), _UNSAT_QUERY)
    attempt = GuardOverlapAttempt(
        requirement.stable_key(), GuardOverlapStatus.UNSAT,
        ("fake",), 1.0, requirement.canonical_query_digest,
    )
    raw = SimpleNamespace(is_equivalent=True)
    fabricated = GuardQueryExecutionArtifact(
        requirement.stable_key(), requirement.canonical_query_digest,
        "0" * 64, GuardOverlapStatus.UNSAT, ("fake",),
        requirement.derived_view_id, requirement.premise_digest,
        requirement.graph_generation,
        ("pairwise.canonical_guard_query_executor", "v1"),
    )

    with pytest.raises(ValueError, match="typed canonical query artifact"):
        graph.record(GuardOverlapExecutionResult(attempt, raw, fabricated))


def test_guard_disjoint_direct_issue_has_no_authority():
    graph = GuardOverlapGraph(("view",), "premise")
    requirement = graph.requirement(_seed("left"), _seed("right"), _UNSAT_QUERY)

    with pytest.raises(RuntimeError, match="issuer is not trusted"):
        GuardDisjointArtifact.issue(requirement)


def test_guard_query_artifact_direct_issue_is_rejected():
    from scripts.function_tracer_pcode.equivalence.obligations.guard_overlap import (
        issue_guard_query_execution_artifact,
    )

    graph = GuardOverlapGraph(("view",), "premise")
    requirement = graph.requirement(_seed("left"), _seed("right"), _UNSAT_QUERY)
    attempt = GuardOverlapAttempt(
        requirement.stable_key(), GuardOverlapStatus.UNSAT,
        ("fake",), 1.0, requirement.canonical_query_digest,
    )
    with pytest.raises(RuntimeError, match="issuer is not trusted"):
        issue_guard_query_execution_artifact(
            requirement, attempt, SimpleNamespace(is_equivalent=True)
        )


def test_canonical_guard_executor_rejects_strategy_stub():
    graph = GuardOverlapGraph(("view",), "premise")
    requirement = graph.requirement(_seed("left"), _seed("right"), _UNSAT_QUERY)
    strategy_stub = SimpleNamespace(
        solver_runner=SimpleNamespace(), per_query_timeout=1
    )

    with pytest.raises(RuntimeError, match="strategy is not trusted"):
        execute_canonical_guard_query(
            strategy_stub, requirement, _UNSAT_QUERY, "stub"
        )


def test_canonical_guard_executor_rejects_spoofed_strategy_identity():
    graph = GuardOverlapGraph(("view",), "premise")
    requirement = graph.requirement(_seed("left"), _seed("right"), _UNSAT_QUERY)
    spoofed_type = type(
        "PairwiseStrategy",
        (),
        {
            "__module__": (
                "scripts.function_tracer_pcode.equivalence.strategies.pairwise"
            )
        },
    )
    strategy_stub = spoofed_type()
    strategy_stub.solver_runner = SimpleNamespace()
    strategy_stub.per_query_timeout = 1

    with pytest.raises(RuntimeError, match="strategy is not trusted"):
        execute_canonical_guard_query(
            strategy_stub, requirement, _UNSAT_QUERY, "spoofed"
        )


def test_superseded_generation_never_reuses_old_closure():
    graph = GuardOverlapGraph(("view",), "premise")
    requirement = graph.requirement(_seed("left"), _seed("right"), _UNSAT_QUERY)
    graph.record(_result(requirement, _UNSAT_QUERY))
    replacement = graph.supersede()
    assert replacement.lookup(requirement) is None


def test_guard_execution_does_not_publish_function_proof_outcome():
    analysis = SimpleNamespace(binary_id="b", function_name="f", entry_point=1)
    runtime = ObligationRuntimeSession.create(analysis, analysis)
    graph = GuardOverlapGraph(runtime.current_view.view_id, runtime.premise_digest)
    graph_requirement = graph.requirement(_seed("left"), _seed("right"), _UNSAT_QUERY)
    requirement = ProofRequirementId.create(
        "guard_overlap",
        ("pair", 0),
        ProofRequirementContract(
            proposition="guard_overlap",
            observation_surface=("guard",),
            active_precondition=("query",),
        ),
    )
    runtime.execute(
        requirement,
        "guard_overlap",
        lambda: _result(graph_requirement, _UNSAT_QUERY),
    )
    assert requirement.to_key() not in runtime.proof_outcomes


def _binding(generation=1):
    return PairLedgerBinding(
        "session", "pairwise", "surface", "projection", generation,
        ("view", generation), "premise", generation,
    )


def test_ledger_seals_only_with_exact_generation_bound_closure():
    binding = _binding()
    runtime = ObligationRuntimeSession.create(
        SimpleNamespace(binary_id="b", function_name="f", entry_point=1),
        SimpleNamespace(binary_id="b", function_name="f", entry_point=1),
    )
    binding = PairLedgerBinding(
        "session", "pairwise", "surface", "projection", 1,
        runtime.current_view.view_id, runtime.premise_digest, 1,
    )
    ledger = runtime.open_pair_ledger(binding, 1)
    graph = GuardOverlapGraph(binding.derived_view_id, binding.premise_digest, 1)
    requirement = graph.requirement(_seed("left"), _seed("right"), _UNSAT_QUERY)
    node = graph.record(_result(requirement, _UNSAT_QUERY))
    ledger.close(PairClosureEvidence.validated(
        (0, 0), PairClosureKind.GUARD_QUERY, binding,
        GuardUnsatClosureArtifact(node.disjoint_artifact),
    ))
    certificate = runtime.pair_quiescence_certificate(ledger)
    ledger.seal(certificate)
    assert ledger.lifecycle == LedgerLifecycle.SEALED
    assert ledger.counts()["unsat"] == 1
    json.dumps(ledger.closure_snapshot())


def test_ledger_rejects_closure_from_prior_generation():
    ledger = PairDispositionLedger(_binding(2), 1)
    graph = GuardOverlapGraph(_binding(1).derived_view_id, _binding(1).premise_digest, 1)
    requirement = graph.requirement(_seed("left"), _seed("right"), _UNSAT_QUERY)
    node = graph.record(_result(requirement, _UNSAT_QUERY))
    stale = PairClosureEvidence.validated(
        (0, 0), PairClosureKind.GUARD_QUERY, _binding(1),
        GuardUnsatClosureArtifact(node.disjoint_artifact),
    )
    with pytest.raises(ValueError, match="invalid closure"):
        ledger.close(stale)


def test_arbitrary_tuple_cannot_be_promoted_to_pair_closure():
    assert not hasattr(PairClosureEvidence, "create")


def test_sat_terminal_requires_typed_counterexample_safety_receipt():
    binding = _binding()
    ledger = PairDispositionLedger(binding, 1)
    query = "(assert true)\n(check-sat)"
    with pytest.raises(ValueError, match="execution receipt"):
        ledger.record_terminal_query(
            (0, 0), PairDisposition.SAT, query, "value_query"
        )

    sat_execution = _solver_execution_result(
        query, SolverStatus.SAT, model={"x": 1}
    ).solver_query_execution_receipt
    with pytest.raises(ValueError, match="terminal pair artifact"):
        ledger.record_terminal_query(
            (0, 0), PairDisposition.SAT, query, "value_query",
            query_execution_receipt=sat_execution,
        )

    receipt = CounterexampleSafetyReceipt.from_pairwise_validation(
        query=query,
        model={"x": 1},
        premise_digest=binding.premise_digest,
        pair_key=(0, 0),
        analysis_safe=True,
        global_case_replay_safe=True,
        same_function_replay_safe=True,
    )
    ledger.record_terminal_query(
        (0, 0), PairDisposition.SAT, query, "value_query",
        safety_receipt=receipt,
        query_execution_receipt=sat_execution,
    )
    assert ledger.validates_complete_snapshot()
    snapshot = ledger.closure_snapshot()[0]
    assert snapshot[0] == "pair_closure_snapshot_v2"
    assert "TerminalPairArtifact" in snapshot


def test_closure_snapshot_audits_binding_use_partition():
    binding = _binding()
    query = "(assert false)\n(check-sat)"
    artifact = SolverUnsatClosureArtifact.from_validated_result(
        query, binding.premise_digest, "(0,0)",
        "value_query", _solver_execution_result(query, SolverStatus.UNSAT),
    )
    evidence = PairClosureEvidence.validated(
        (0, 0), PairClosureKind.VALUE_QUERY, binding, artifact,
        required_binding_uses=("guard-use", "value-use"),
        consumed_binding_uses=("value-use",),
    )
    snapshot = evidence.snapshot_key()
    import json

    json.dumps(snapshot)
    assert "SolverQueryExecutionReceipt" not in repr(snapshot)
    assert ("guard-use", "value-use") in snapshot
    assert ("value-use",) in snapshot
    assert ("guard-use",) in snapshot
    ledger = PairDispositionLedger(binding, 1)
    ledger.close(evidence)
    assert ledger.binding_use_partitions() == (
        ("guard-use", "value-use"),
        ("value-use",),
        ("guard-use",),
    )


def test_duplicate_closure_is_rejected_even_when_evidence_is_identical():
    binding = _binding()
    query = "(assert false)\n(check-sat)"
    artifact = SolverUnsatClosureArtifact.from_validated_result(
        query, binding.premise_digest, "(0,0)",
        "value_query", _solver_execution_result(query, SolverStatus.UNSAT),
    )
    evidence = PairClosureEvidence.validated(
        (0, 0), PairClosureKind.VALUE_QUERY, binding, artifact
    )
    ledger = PairDispositionLedger(binding, 1)
    ledger.close(evidence)
    with pytest.raises(RuntimeError, match="duplicate pair closure"):
        ledger.close(evidence)


def test_structural_equality_uses_distinct_typed_closure_authority():
    binding = _binding()
    void_expr1 = Expression(ExpressionType.UNKNOWN, name="void", size=0)
    void_expr2 = Expression(ExpressionType.UNKNOWN, name="void", size=0)
    case1 = ReturnCase(
        0, [], void_expr1,
        return_info=ReturnInfo(address="0x100", value=void_expr1),
    )
    case2 = ReturnCase(
        0, [], void_expr2,
        return_info=ReturnInfo(address="0x200", value=void_expr2),
    )

    class Strategy:
        _case_value_contains_unresolved = staticmethod(lambda *args, **kwargs: False)

        @staticmethod
        def _build_condition_only_query(*args, **kwargs):
            return _SAT_QUERY

        @staticmethod
        def _debug_print(*args, **kwargs):
            return None

        @staticmethod
        def _solve_query_internal(query, pair_id, **kwargs):
            return _solver_execution_result(
                query, SolverStatus.UNSAT, query_label=pair_id
            )

    assertion = "(assert true)"
    assertion_digest = hashlib.sha256(assertion.encode("utf-8")).hexdigest()
    binding_id = "a" * 64
    base_ctx = {
        "header_lines": [],
        "return_size1": 0,
        "return_size2": 0,
        "call_projection_binding_ids_by_pair": {
            "(0,0)": (binding_id,),
        },
        "call_projection_binding_digests_by_pair": {
            "(0,0)": {binding_id: assertion_digest},
        },
        "call_projection_assertions_by_pair": {
            "(0,0)": (
                f"; call_projection_binding {binding_id} "
                f"assertion_sha256={assertion_digest}",
                assertion,
                f"; call_projection_binding_end {binding_id}",
            ),
        },
    }

    result = solve_query_after_guard(
        Strategy(),
        base_ctx,
        case1,
        case2,
        lambda expr: expr.to_smt(),
        lambda expr: expr.to_smt(),
        "(0,0)",
    )
    consumed_bindings = tuple(sorted(
        binding_id
        for binding_id, digest in projection_binding_evidence_from_query(
            result.last_query
        ).items()
        if base_ctx["call_projection_binding_digests_by_pair"]["(0,0)"].get(
            binding_id
        ) == digest
    ))
    artifact = StructuralEqualityClosureArtifact.from_validated_result(
        premise_digest=binding.premise_digest,
        query_label="(0,0)",
        result=result,
    )
    evidence = PairClosureEvidence.validated(
        (0, 0), PairClosureKind.STRUCTURAL_EQUALITY, binding, artifact,
        required_binding_uses=(binding_id,),
        consumed_binding_uses=consumed_bindings,
    )

    assert evidence.validates(binding)
    assert evidence.closure_kind is PairClosureKind.STRUCTURAL_EQUALITY
    assert evidence.excluded_binding_uses == ()
    assert type(evidence.artifact) is StructuralEqualityClosureArtifact
    with pytest.raises(ValueError, match="exact UNSAT execution receipt"):
        SolverUnsatClosureArtifact.from_validated_result(
            "", binding.premise_digest, "(0,0)", "value_query", result
        )


def test_duplicate_terminal_query_is_rejected():
    binding = _binding()
    ledger = PairDispositionLedger(binding, 1)
    ledger.record_terminal_query(
        (0, 0), PairDisposition.UNKNOWN, "", "aggregate"
    )
    with pytest.raises(RuntimeError, match="duplicate pair closure"):
        ledger.record_terminal_query(
            (0, 0), PairDisposition.UNKNOWN, "", "aggregate"
        )


def test_fabricated_aggregate_partition_candidate_has_no_authority():
    from scripts.function_tracer_pcode.equivalence.obligations.pair_closure_producers import (
        AggregatePartitionCandidate,
        validate_aggregate_partition_candidate,
    )

    binding = _binding()
    fabricated = AggregatePartitionCandidate.create(
        binding, "(0,0)", ((0, 0), "fabricated"), ((0, 0),)
    )
    strategy = SimpleNamespace(
        _resolve_pending_loop_summary_pairs_with_partition_proof=(
            lambda *_args: set()
        )
    )
    assert validate_aggregate_partition_candidate(
        strategy,
        binding,
        fabricated,
        (0, 0),
        ((0, 0),),
        (),
        (),
        (),
        set(),
    ) is None


def test_pinned_proof_registry_is_immutable():
    from scripts.function_tracer_pcode.equivalence.obligations import (
        pair_closure_producers as producer_module,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_services import (
        orchestration_1 as _sealed_orchestration,
    )

    assert _sealed_orchestration is not None
    pinned = getattr(producer_module, "_PINNED_PROOF_IMPLEMENTATIONS")
    assert pinned is not None
    with pytest.raises(TypeError):
        pinned["_cases_have_equivalent_runtime_reductions"] = lambda *_args: True


def test_other_producer_execution_namespace_mutation_fails_closed(
    monkeypatch,
):
    from scripts.function_tracer_pcode.equivalence.obligations.pair_closure_producers import (
        RuntimeReductionCandidate,
        validate_runtime_reduction_candidate,
    )
    from scripts.function_tracer_pcode.equivalence.obligations import (
        pair_closure_producers as producer_module,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise import (
        PairwiseStrategy,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_services import (
        orchestration_1 as _sealed_orchestration,
    )
    from scripts.function_tracer_pcode.model import Expression

    fake_oracle = SimpleNamespace(
        conjunction_is_unsat=lambda *_args, **_kwargs: True
    )
    assert _sealed_orchestration is not None
    pinned = getattr(producer_module, "_PINNED_PROOF_IMPLEMENTATIONS")
    assert pinned is not None
    frozen_reduction = pinned[
        "_cases_have_equivalent_runtime_reductions"
    ]
    monkeypatch.setitem(
        frozen_reduction.__globals__, "ConditionSMTOracle", fake_oracle
    )
    binding = _binding()
    candidate = RuntimeReductionCandidate.create(
        binding, "(0,0)", ("runtime-reduction",), ("patched-global",)
    )
    strategy = PairwiseStrategy(SimpleNamespace(), SimpleNamespace())

    assert validate_runtime_reduction_candidate(
        strategy,
        binding,
        candidate,
        SimpleNamespace(value_expr=Expression.constant(1, size=4)),
        SimpleNamespace(value_expr=Expression.constant(2, size=4)),
        (),
    ) is None


def test_solver_unsat_closure_rejects_wrong_premise():
    binding = _binding()
    query = "(assert false)\n(check-sat)"
    artifact = SolverUnsatClosureArtifact.from_validated_result(
        query, "different-premise", "(0,0)",
        "value_query", _solver_execution_result(query, SolverStatus.UNSAT),
    )
    with pytest.raises(ValueError, match="failed validation"):
        PairClosureEvidence.validated(
            (0, 0), PairClosureKind.VALUE_QUERY, binding, artifact
        )


def test_directly_constructed_artifacts_have_no_closure_authority():
    forged_solver = SolverUnsatClosureArtifact(
        "3" * 64, _binding().premise_digest, "(0,0)", "value_query"
    )
    graph = GuardOverlapGraph(
        _binding().derived_view_id, _binding().premise_digest,
        _binding().graph_generation,
    )
    requirement = graph.requirement(_seed("left"), _seed("right"), "(check-sat)")
    from scripts.function_tracer_pcode.equivalence.obligations import GuardDisjointArtifact
    forged_guard = GuardUnsatClosureArtifact(GuardDisjointArtifact(
        requirement.stable_key(), requirement.canonical_query_digest,
        _binding().derived_view_id, _binding().premise_digest,
        _binding().graph_generation,
    ))
    for artifact in (forged_solver, forged_guard):
        with pytest.raises(ValueError, match="failed validation"):
            PairClosureEvidence.validated(
                (0, 0), PairClosureKind.RECOVERY, _binding(), artifact
            )


def test_producer_closure_cannot_be_issued_outside_registered_validator():
    from scripts.function_tracer_pcode.equivalence.obligations.pair_disposition import (
        RuntimeReductionClosureArtifact,
        issue_producer_validated_closure,
    )

    with pytest.raises(RuntimeError, match="issuer is not trusted"):
        issue_producer_validated_closure(
            RuntimeReductionClosureArtifact,
            _binding(),
            ("candidate",),
            ("evidence",),
        )


def test_ledger_has_no_self_issued_quiescence_certificate():
    ledger = PairDispositionLedger(_binding(), 0)
    assert not hasattr(ledger, "quiescence_certificate")
    assert not hasattr(ledger, "issue_certificate")


def test_runtime_view_transition_retains_old_ledger_until_exact_successor_composes():
    runtime = ObligationRuntimeSession.create(
        SimpleNamespace(binary_id="b1", function_name="f", entry_point=1),
        SimpleNamespace(binary_id="b2", function_name="f", entry_point=2),
    )
    binding = PairLedgerBinding(
        "session", "pairwise", "surface", "projection", 1,
        runtime.current_view.view_id, runtime.premise_digest, 1,
    )
    ledger = runtime.open_pair_ledger(binding, 0)
    stale_certificate = runtime.pair_quiescence_certificate(ledger)
    requirement = ProofRequirementId.create(
        "return_coverage",
        ("function", "left"),
        ProofRequirementContract(
            proposition="coverage",
            observation_surface=("return",),
            active_precondition=("all-inputs",),
        ),
    )
    runtime._apply_artifact(requirement, {"proof_source": "unit-test"})
    assert ledger.lifecycle == LedgerLifecycle.OPEN
    successor_plan = runtime.pair_ledger_manager.pending_successor
    assert runtime.pair_ledger_manager.current is ledger
    assert successor_plan is not None
    assert successor_plan.comparison_session_id == "session"
    assert successor_plan.branch_id == "pairwise"
    assert successor_plan.derived_view_id == runtime.current_view.view_id
    assert successor_plan.premise_digest == runtime.premise_digest
    assert successor_plan.frame_generation == 2
    assert successor_plan.graph_generation == 2
    call_requirement = ProofRequirementId.create(
        "call_effect_summary_proof",
        ("call", "left", "right"),
        ProofRequirementContract("call effect relation"),
    )
    runtime._apply_artifact(call_requirement, {"proof_source": "unit-test-2"})
    successor_plan = runtime.pair_ledger_manager.pending_successor
    assert successor_plan is not None
    assert successor_plan.derived_view_id == runtime.current_view.view_id
    assert successor_plan.premise_digest == runtime.premise_digest
    assert successor_plan.frame_generation == 2
    assert successor_plan.graph_generation == 2
    assert successor_plan.projection_refresh_required
    replacement_binding = PairLedgerBinding(
        successor_plan.comparison_session_id,
        successor_plan.branch_id,
        "replacement-surface",
        "replacement-projection",
        binding.frame_generation + 1,
        successor_plan.derived_view_id,
        successor_plan.premise_digest,
        binding.graph_generation + 1,
    )
    successor = runtime.open_pair_ledger(replacement_binding, 0)
    assert ledger.lifecycle == LedgerLifecycle.SUPERSEDED
    assert successor.binding.prepared_surface_digest == "replacement-surface"
    assert successor.binding.projection_id == "replacement-projection"
    assert runtime.pair_ledger_manager.pending_successor is None
    assert runtime.pair_ledger_manager.last_composed_successor.accepts(
        successor.binding, successor.expected_pairs
    )
    with pytest.raises(RuntimeError, match="not open"):
        ledger.seal(stale_certificate)


def test_guard_query_consumes_only_valid_typed_guard_bundles():
    import hashlib

    guard_assertion = "(assert (= guard_call (_ bv1 32)))"
    value_assertion = "(assert (= value_call (_ bv2 32)))"
    guard_bundle = TypedProjectionAssertionBundle(
        "guard-binding", ("guard",), (guard_assertion,),
        hashlib.sha256(guard_assertion.encode()).hexdigest(),
    )
    value_bundle = TypedProjectionAssertionBundle(
        "value-binding", ("value",), (value_assertion,),
        hashlib.sha256(value_assertion.encode()).hexdigest(),
    )
    tampered_bundle = TypedProjectionAssertionBundle(
        "tampered", ("guard",), ("(assert false)",), "0" * 64,
    )
    lines = _build_pairwise_extra_assertions(
        {"call_projection_assertion_bundles_by_pair": {
            "(0,0)": (guard_bundle, value_bundle, tampered_bundle),
        }},
        "(0,0)",
        guard_only=True,
    )
    query_fragment = "\n".join(lines)
    assert guard_assertion in query_fragment
    assert value_assertion not in query_fragment
    assert "(assert false)" not in query_fragment
