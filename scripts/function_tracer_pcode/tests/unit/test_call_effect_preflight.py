from __future__ import annotations

from copy import deepcopy
from dataclasses import replace
import hashlib

import pytest

import scripts.function_tracer_pcode.equivalence.call_effect_preflight as preflight_module

from scripts.function_tracer_pcode.equivalence.call_effect_preflight import (
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
)
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
from scripts.function_tracer_pcode.equivalence.strategies.proof_gates._shared import StrategyResult
from scripts.function_tracer_pcode.model import Expression, ReturnInfo
from scripts.function_tracer_pcode.smt import ParallelResult


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
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_services import (
        orchestration_1,
    )

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

    result = EquivalenceChecker(timeout=5, enable_rewrite=False).check(
        left,
        right,
        "left",
        "right",
    )

    assert invoked == []
    assert result.is_equivalent is not True


def test_override_cannot_forge_receipt_after_consuming_dispatch(monkeypatch):
    from scripts.function_tracer_pcode.tests.unit.test_call_effect_obligations import (
        _phase2_caller_analysis,
    )

    left = _phase2_caller_analysis("B1", 1, 0x1000)
    right = _phase2_caller_analysis("B2", 2, 0x3000)
    checker = EquivalenceChecker(timeout=5, enable_rewrite=False)
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
