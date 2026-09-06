from __future__ import annotations

from copy import deepcopy
from dataclasses import replace
import hashlib

import pytest

import scripts.function_tracer_pcode.proof.call_effect.preflight as preflight_module

from scripts.function_tracer_pcode.proof.call_effect.preflight import (
    CallSemanticProjectionBinding,
    CallProofDecisionMode,
    PreparedDispatchFrame,
    QueryExecutionRecord,
    StrategySourceAnalysisPair,
    close_prepared_dispatch_frame,
    consume_prepared_dispatch_frame,
    current_dispatch_depth,
    issue_builtin_comparison_receipt,
    prepare_solver_surface,
    projection_binding_evidence_from_query,
    push_prepared_dispatch_frame,
    validate_call_resolution_projection,
    finalize_pairwise_comparison_receipt,
)
from scripts.function_tracer_pcode.proof.query_receipt_authority import (
    canonical_region_query_receipt_digest,
)
from scripts.function_tracer_pcode.proof.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
)
from scripts.function_tracer_pcode.proof.obligations import (
    GuardOverlapGraph,
    GuardRegionSeed,
    GuardUnsatClosureArtifact,
    ObligationRuntimeSession,
    PairClosureEvidence,
    PairClosureKind,
    PairLedgerBinding,
)
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import StrategyResult
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    execute_canonical_guard_query,
)
from scripts.function_tracer_pcode.core import Expression, ReturnInfo
from scripts.function_tracer_pcode.smt import ParallelResult, ParallelSolverRunner


_GUARD_UNSAT_QUERY = "(set-logic QF_BV)\n(assert false)\n(check-sat)"


def _canonical_guard_disjoint_artifact(binding: PairLedgerBinding):
    strategy = getattr(_canonical_guard_disjoint_artifact, "strategy", None)
    if strategy is None:
        strategy = PairwiseStrategy(
            object(), ParallelSolverRunner(timeout=2)
        )
        _canonical_guard_disjoint_artifact.strategy = strategy
    graph = GuardOverlapGraph(
        binding.derived_view_id,
        binding.premise_digest,
        binding.graph_generation,
    )
    requirement = graph.requirement(
        GuardRegionSeed("left", 0, (("guard", "left"),), "left"),
        GuardRegionSeed("right", 0, (("guard", "right"),), "right"),
        _GUARD_UNSAT_QUERY,
    )
    result = execute_canonical_guard_query(
        strategy, requirement, _GUARD_UNSAT_QUERY, "receipt-test"
    )
    artifact = graph.record(result).disjoint_artifact
    assert artifact is not None
    return artifact


def _prepared(source, *, session="session", branch="S_PAIRWISE", generation=1):
    return prepare_solver_surface(
        source,
        observation_contract_digest="observation-contract",
        comparison_session_id=session,
        branch_id=branch,
        generation=generation,
        decision_mode=CallProofDecisionMode.PREFLIGHT_PROJECTION,
    )


def test_normalization_certificate_has_stable_semantic_and_fresh_instance_identity():
    source = StrategySourceAnalysisPair.create(
        create_mock_analysis("left"),
        create_mock_analysis("right"),
    )

    first = _prepared(source, session="one")
    second = _prepared(source, session="two")

    assert first.certificate.semantic_id == second.certificate.semantic_id
    assert first.certificate.instance_id != second.certificate.instance_id
    assert first.surface_digest == second.surface_digest
    assert first.is_valid_for(source)
    assert source.is_unchanged()


def test_prepared_surface_is_independently_rebuilt_normalized_child():
    parameter = Expression.parameter("x", 0, data_type="long", size=8)
    left = create_mock_analysis(
        "left",
        returns=[ReturnInfo(address="0x1", conditions=[], value=parameter)],
        parameters=[{"name": "x", "index": 0, "size": 4, "data_type": "int"}],
    )
    right = create_mock_analysis("right")
    source = StrategySourceAnalysisPair.create(left, right)

    prepared = _prepared(source)

    assert prepared.analysis1 is not left
    assert prepared.analysis1.returns[0].value.size == 4
    assert prepared.certificate.transformation_kind == (
        "trusted_semantic_width_normalization"
    )
    assert prepared.certificate.semantic_delta
    assert prepared.is_valid_for(source)


def test_normalization_certificate_rejects_tampered_rule_delta_audit():
    source = StrategySourceAnalysisPair.create(
        create_mock_analysis("left"),
        create_mock_analysis("right"),
    )
    prepared = _prepared(source)
    audit = prepared.certificate.surface_delta_audit
    tampered = replace(
        prepared.certificate,
        surface_delta_audit=replace(
            audit,
            rule_steps=(("untrusted_rewrite", audit.rule_steps[0][1], audit.rule_steps[0][2]),)
            + audit.rule_steps[1:],
        ),
    )

    assert not tampered.validate(source, (prepared.analysis1, prepared.analysis2))


def test_normalization_certificate_rejects_tampered_observation_contract():
    source = StrategySourceAnalysisPair.create(
        create_mock_analysis("left"),
        create_mock_analysis("right"),
    )
    prepared = _prepared(source)
    semantic = prepared.certificate.semantic_transformation
    tampered = replace(
        prepared.certificate,
        semantic_transformation=replace(
            semantic,
            observation_roots=("returns",),
        ),
    )

    assert not tampered.validate(source, (prepared.analysis1, prepared.analysis2))


def test_query_record_recomputes_projection_consumption_from_formula():
    binding_id = "a" * 64
    assertion = "(assert (= (_ bv1 32) (_ bv1 32)))"
    assertion_digest = hashlib.sha256(assertion.encode("utf-8")).hexdigest()
    query = "\n".join(
        (
            f"; call_projection_binding {binding_id} assertion_sha256={assertion_digest}",
            assertion,
            f"; call_projection_binding_end {binding_id}",
            "(check-sat)",
        )
    )
    query_digest = hashlib.sha256(query.encode("utf-8")).hexdigest()

    assert projection_binding_evidence_from_query(query) == {
        binding_id: assertion_digest
    }
    assert QueryExecutionRecord(
        "pair",
        query_digest,
        query_digest,
        "unsat",
        "pairwise_solver_query",
        (binding_id,),
        query,
    ).validate()
    assert not QueryExecutionRecord(
        "guard-only",
        query_digest,
        query_digest,
        "unsat",
        "guard_overlap",
        (binding_id,),
        "(check-sat)",
    ).validate()

    tampered = query.replace("(_ bv1 32)", "(_ bv2 32)", 1)
    assert projection_binding_evidence_from_query(tampered) == {}


def test_query_record_rejects_string_coercion_identity_collision():
    formula = "(set-logic QF_BV)\n(check-sat)"
    digest = hashlib.sha256(formula.encode("utf-8")).hexdigest()
    record = QueryExecutionRecord(
        query_label="1",
        premise_digest=digest,
        formula_digest=digest,
        disposition="unsat",
        proof_kind="monolithic_region_guard",
        formula_text=formula,
    )
    wrong_type = replace(record, query_label=1)

    assert record.validate()
    assert not wrong_type.validate()
    assert canonical_region_query_receipt_digest(record)
    with pytest.raises(
        ValueError, match="canonical region query receipt is invalid"
    ):
        canonical_region_query_receipt_digest(wrong_type)


def test_dispatch_frame_is_single_use_and_cleanup_revokes_copied_capability(monkeypatch):
    source = StrategySourceAnalysisPair.create(
        create_mock_analysis("left"),
        create_mock_analysis("right"),
    )
    prepared = _prepared(source)
    manifest = {}
    projection = validate_call_resolution_projection(manifest, prepared, generation=1)
    frame = PreparedDispatchFrame(
        comparison_session_id="session",
        branch_id="S_PAIRWISE",
        generation=1,
        source=source,
        prepared=prepared,
        projection=projection,
        preflight_manifest=manifest,
        trusted_proof_artifacts=(),
        decision_mode=CallProofDecisionMode.PREFLIGHT_PROJECTION,
    )

    token = push_prepared_dispatch_frame(frame)
    assert current_dispatch_depth() == 1
    assert consume_prepared_dispatch_frame(source.analysis1, source.analysis2) is frame
    with pytest.raises(RuntimeError, match="double_consumed"):
        consume_prepared_dispatch_frame(source.analysis1, source.analysis2)
    assert not hasattr(frame, "complete")
    with pytest.raises(RuntimeError, match="untrusted_issuer"):
        issue_builtin_comparison_receipt(
            frame,
            query_records=(
                QueryExecutionRecord(
                    "(0,0)",
                    "0" * 64,
                    "1" * 64,
                    "unsat",
                    "test",
                ),
            ),
            consumed_projection_binding_ids=(),
            disposition_counts={
                "total": 1,
                "unsat": 1,
                "sat": 0,
                "unknown": 0,
                "error": 0,
            },
        )
    from scripts.function_tracer_pcode.proof.strategies.pairwise_services import orchestration as orchestration_1

    def replacement_executor():
        return issue_builtin_comparison_receipt(
            frame,
            query_records=(
                QueryExecutionRecord(
                    "forged",
                    "0" * 64,
                    "1" * 64,
                    "unsat",
                    "forged",
                ),
            ),
            consumed_projection_binding_ids=(),
            disposition_counts={"total": 1, "unsat": 1, "sat": 0, "unknown": 0, "error": 0},
        )

    replacement_executor.__module__ = orchestration_1.__name__
    replacement_executor.__qualname__ = "_impl_check"
    monkeypatch.setattr(orchestration_1, "_impl_check", replacement_executor)
    with pytest.raises(RuntimeError, match="untrusted_issuer"):
        replacement_executor()
    assert close_prepared_dispatch_frame(frame, token) is True
    assert frame.lifecycle_state == "closed"
    assert frame.cleanup_complete is True
    assert current_dispatch_depth() == 0
    with pytest.raises(RuntimeError, match="missing"):
        consume_prepared_dispatch_frame(source.analysis1, source.analysis2)


def test_receipt_merges_guard_closure_binding_consumption_and_exclusion():
    source = StrategySourceAnalysisPair.create(
        create_mock_analysis("left"),
        create_mock_analysis("right"),
    )
    prepared = _prepared(source)
    projection = validate_call_resolution_projection({}, prepared, generation=1)
    requirement_id = ProofRequirementId.create(
        "call_effect",
        ("call", 1),
        ProofRequirementContract("call relation"),
    )
    semantic_bindings = tuple(
        CallSemanticProjectionBinding(
            binding_id=binding_id,
            obligation_id=f"obligation-{index}",
            requirement_id=requirement_id,
            observation_contract_id="observation-contract",
            left_fact_id=None,
            right_fact_id=None,
            left_pcode_op_key=None,
            right_pcode_op_key=None,
            left_use_bindings=(),
            right_use_bindings=(),
            proof_stage_records=(),
            relation_kind="test",
            call_on_left=None,
            region_return_members=(),
            consumer_domains=(domain,),
            status="proven",
        )
        for index, (binding_id, domain) in enumerate((
            ("guard-binding", "guard"),
            ("value-binding", "value"),
        ))
    )
    projection = replace(
        projection,
        status="proven",
        required=True,
        semantic_bindings=semantic_bindings,
    )
    frame = PreparedDispatchFrame(
        "session", "S_PAIRWISE", 1, source, prepared, projection, {}, (),
        CallProofDecisionMode.PREFLIGHT_PROJECTION,
    )
    runtime = ObligationRuntimeSession.create(source.analysis1, source.analysis2)
    frame.obligation_runtime = runtime
    ledger_binding = PairLedgerBinding(
        frame.comparison_session_id,
        frame.branch_id,
        prepared.surface_digest,
        projection.projection_id,
        frame.generation,
        runtime.current_view.view_id,
        runtime.premise_digest,
        1,
    )
    ledger = runtime.open_pair_ledger(ledger_binding, 1)
    ledger.close(PairClosureEvidence.validated(
        (0, 0), PairClosureKind.GUARD_QUERY, ledger_binding,
        GuardUnsatClosureArtifact(
            _canonical_guard_disjoint_artifact(ledger_binding)
        ),
        required_binding_uses=("guard-binding", "value-binding"),
        consumed_binding_uses=("guard-binding",),
    ))
    frame.pair_disposition_ledger = ledger
    frame.pending_query_records = ()
    frame.pending_consumed_projection_binding_ids = ()
    frame.pending_disposition_counts = {
        "total": 1, "unsat": 1, "sat": 0, "unknown": 0, "error": 0,
    }
    token = push_prepared_dispatch_frame(frame)
    consume_prepared_dispatch_frame(source.analysis1, source.analysis2)
    receipt = finalize_pairwise_comparison_receipt(frame)
    close_prepared_dispatch_frame(frame, token)

    assert receipt.required_projection_binding_ids == (
        "guard-binding", "value-binding"
    )
    assert receipt.consumed_projection_binding_ids == ("guard-binding",)
    assert receipt.excluded_projection_binding_ids == ("value-binding",)
    assert receipt.is_trusted_for(frame)


def test_call_effect_replan_binds_successor_after_new_projection_is_extracted():
    source = StrategySourceAnalysisPair.create(
        create_mock_analysis("left"), create_mock_analysis("right")
    )
    old_prepared = _prepared(source, session="successor-session")
    old_manifest = {"legacy_blocker_mapping": [{"blocker": "call-effect"}]}
    old_projection = validate_call_resolution_projection(
        old_manifest, old_prepared, generation=1
    )
    runtime = ObligationRuntimeSession.create(source.analysis1, source.analysis2)
    old_binding = PairLedgerBinding(
        "successor-session", "S_PAIRWISE", old_prepared.surface_digest,
        old_projection.projection_id, 1,
        runtime.current_view.view_id, runtime.premise_digest, 1,
    )
    old_ledger = runtime.open_pair_ledger(old_binding, 1)
    proof_requirement = ProofRequirementId.create(
        "call_effect",
        ("call", "left", "right"),
        ProofRequirementContract("call effect relation"),
    )
    runtime._apply_artifact(proof_requirement, {"proof_source": "unit-test"})
    successor_plan = runtime.pair_ledger_manager.pending_successor
    assert successor_plan is not None
    assert runtime.pair_ledger_manager.current is old_ledger

    new_prepared = _prepared(source, session="successor-session")
    new_projection = validate_call_resolution_projection(
        {}, new_prepared, generation=2
    )
    assert new_projection.projection_id != old_projection.projection_id
    frame = PreparedDispatchFrame(
        "successor-session", "S_PAIRWISE", 2, source, new_prepared,
        new_projection, {}, (), CallProofDecisionMode.PREFLIGHT_PROJECTION,
    )
    frame.obligation_runtime = runtime
    frame.replan_successor_plan = successor_plan
    stale_projection_binding = PairLedgerBinding(
        frame.comparison_session_id,
        frame.branch_id,
        new_prepared.surface_digest,
        old_projection.projection_id,
        frame.generation,
        successor_plan.derived_view_id,
        successor_plan.premise_digest,
        2,
    )
    with pytest.raises(RuntimeError, match="does not match successor intent"):
        runtime.open_pair_ledger(stale_projection_binding, 1)
    assert runtime.pair_ledger_manager.current is old_ledger
    assert runtime.pair_ledger_manager.promotion_state.value == "aborted"
    successor_plan = runtime.pair_ledger_manager.plan_successor(
        runtime.current_view.view_id,
        runtime.premise_digest,
        projection_refresh_required=True,
    )
    replacement_binding = PairLedgerBinding(
        frame.comparison_session_id,
        frame.branch_id,
        new_prepared.surface_digest,
        new_projection.projection_id,
        frame.generation,
        successor_plan.derived_view_id,
        successor_plan.premise_digest,
        2,
    )
    successor = runtime.open_pair_ledger(replacement_binding, 1)
    assert successor is not old_ledger
    assert successor.binding.graph_generation == 2
    assert successor.binding.projection_id == new_projection.projection_id
    successor.close(PairClosureEvidence.validated(
        (0, 0), PairClosureKind.GUARD_QUERY, successor.binding,
        GuardUnsatClosureArtifact(
            _canonical_guard_disjoint_artifact(successor.binding)
        ),
    ))
    frame.pair_disposition_ledger = successor
    frame.replan_successor_plan = runtime.pair_ledger_manager.last_composed_successor
    frame.replan_successor_ledger = successor
    frame.successor_ledger_reused = True
    frame.pending_disposition_counts = {
        "total": 1, "unsat": 1, "sat": 0, "unknown": 0, "error": 0,
    }
    token = push_prepared_dispatch_frame(frame)
    consume_prepared_dispatch_frame(source.analysis1, source.analysis2)
    receipt = finalize_pairwise_comparison_receipt(frame)
    close_prepared_dispatch_frame(frame, token)

    assert frame.pair_disposition_ledger is successor
    assert runtime.pair_ledger_manager.current is successor
    assert frame.projection.projection_id != old_projection.projection_id
    assert receipt.is_trusted_for(frame)
    assert receipt.ledger_binding_digest


def test_dispatch_rejects_equal_content_from_different_source_objects():
    source = StrategySourceAnalysisPair.create(
        create_mock_analysis("left"),
        create_mock_analysis("right"),
    )
    prepared = _prepared(source)
    manifest = {}
    projection = validate_call_resolution_projection(manifest, prepared, generation=1)
    frame = PreparedDispatchFrame(
        comparison_session_id="session",
        branch_id="S_PAIRWISE",
        generation=1,
        source=source,
        prepared=prepared,
        projection=projection,
        preflight_manifest=manifest,
        trusted_proof_artifacts=(),
        decision_mode=CallProofDecisionMode.PREFLIGHT_PROJECTION,
    )
    token = push_prepared_dispatch_frame(frame)
    try:
        with pytest.raises(RuntimeError, match="untrusted"):
            consume_prepared_dispatch_frame(
                create_mock_analysis("left"),
                create_mock_analysis("right"),
            )
    finally:
        close_prepared_dispatch_frame(frame, token)


def test_preflight_does_not_self_certify_monkeypatched_normalizer(monkeypatch):
    pytest.importorskip("z3")
    left = create_mock_analysis(
        "left",
        returns=[ReturnInfo("0x1", [], Expression.constant(0, size=4))],
    )
    right = create_mock_analysis(
        "right",
        returns=[ReturnInfo("0x2", [], Expression.constant(1, size=4))],
    )
    invoked = []

    def malicious_normalizer(analysis, *_args, **_kwargs):
        invoked.append(analysis)
        rewritten = deepcopy(analysis)
        rewritten.returns = [
            ReturnInfo("0xbad", [], Expression.constant(0, size=4))
        ]
        return rewritten

    monkeypatch.setattr(
        preflight_module,
        "normalize_analysis_semantic_width",
        malicious_normalizer,
        raising=False,
    )

    result = EquivalenceChecker(timeout=5).check(
        left,
        right,
        "left",
        "right",
    )

    assert invoked == []
    assert result.is_equivalent is not True


def test_receipt_v3_rejects_nonempty_pairwise_result_without_ledger():
    source = StrategySourceAnalysisPair.create(
        create_mock_analysis("left"), create_mock_analysis("right")
    )
    prepared = _prepared(source)
    projection = validate_call_resolution_projection({}, prepared, generation=1)
    frame = PreparedDispatchFrame(
        "session", "S_PAIRWISE", 1, source, prepared, projection, {}, (),
        CallProofDecisionMode.PREFLIGHT_PROJECTION,
    )
    frame.consume(source.analysis1, source.analysis2)
    formula = "(check-sat)"
    record = QueryExecutionRecord(
        "(0,0)", "0" * 64, hashlib.sha256(formula.encode()).hexdigest(),
        "unsat", "value_query", formula_text=formula,
    )
    try:
        with pytest.raises(RuntimeError, match="pair_ledger_missing"):
            frame._complete_from_builtin_executor(
                (record,), (),
                {"total": 1, "unsat": 1, "sat": 0, "unknown": 0, "error": 0},
                authority_token=preflight_module._BUILTIN_RECEIPT_AUTHORITY_TOKEN,
            )
    finally:
        frame.close()


def test_override_cannot_forge_receipt_after_consuming_dispatch(monkeypatch):
    from scripts.function_tracer_pcode.tests.unit.test_call_effect_obligations import (
        _phase2_caller_analysis,
    )

    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    checker = EquivalenceChecker(timeout=5)
    issuer_failures = []

    def forged_override(a1, a2, _save_formula=False):
        frame = consume_prepared_dispatch_frame(a1, a2)
        try:
            issue_builtin_comparison_receipt(
                frame,
                query_records=(
                    QueryExecutionRecord(
                        "forged",
                        "0" * 64,
                        "1" * 64,
                        "unsat",
                        "forged_query",
                    ),
                ),
                consumed_projection_binding_ids=(),
                disposition_counts={
                    "total": 1,
                    "unsat": 1,
                    "sat": 0,
                    "unknown": 0,
                    "error": 0,
                },
            )
        except RuntimeError as exc:
            issuer_failures.append(str(exc))
        return StrategyResult(
            is_equivalent=True,
            solver_results=ParallelResult(results=[]),
            total_pairs=1,
            unsat_pairs=1,
        )

    monkeypatch.setattr(checker.pairwise_strategy, "check", forged_override)
    result = checker.check(left, right, "left", "right")

    assert issuer_failures == ["comparison_receipt_untrusted_issuer"]
    assert result.is_equivalent is None
    assert any(
        "comparison_receipt_missing" in tuple(reason.evidence_refs or ())
        for reason in result.unknown_reasons
    )
