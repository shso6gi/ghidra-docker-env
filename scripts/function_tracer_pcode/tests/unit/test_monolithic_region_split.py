from dataclasses import replace
import pytest

from scripts.function_tracer_pcode.equivalence.formula import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
from scripts.function_tracer_pcode.equivalence.strategies.monolithic import MonolithicStrategy
from scripts.function_tracer_pcode.model import Condition, Expression, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.smt import ParallelSolverRunner


def _analysis(name: str, value: int) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x1000",
        parameters=[],
        returns=[ReturnInfo("0x1010", Expression.constant(value, size=4), [])],
        return_type="int",
    )


def test_monolithic_ordered_ite_surface_is_split_into_closed_regions() -> None:
    strategy = MonolithicStrategy(FormulaBuilder(), ParallelSolverRunner(timeout=5))

    result = strategy.check(_analysis("left", 7), _analysis("right", 7))

    assert result.is_equivalent is True
    assert result.pairwise_debug_stats["monolithic_split_planned_regions"] == 1
    assert result.pairwise_debug_stats["monolithic_split_closed_regions"] == 1
    assert result.pairwise_debug_stats["monolithic_split_guard_queries"] == 1
    assert result.pairwise_debug_stats["monolithic_split_value_queries"] == 1
    assert result.pairwise_debug_stats["monolithic_split_max_query_bytes"] > 0


def test_monolithic_local_sat_requires_global_violation_replay() -> None:
    strategy = MonolithicStrategy(FormulaBuilder(), ParallelSolverRunner(timeout=5))

    result = strategy.check(_analysis("left", 7), _analysis("right", 8))

    assert result.is_equivalent is False
    assert result.pairwise_debug_stats["monolithic_split_planned_regions"] == 1
    assert result.sat_pairs == 1


def test_relation_surface_is_not_split() -> None:
    parameter = Expression.parameter("x", 0, data_type="int", size=4)
    positive = Condition(
        Expression.binary_op(
            "INT_SLESS", Expression.constant(0, size=4), parameter
        )
    )
    below_ten = Condition(
        Expression.binary_op(
            "INT_SLESS", parameter, Expression.constant(10, size=4)
        )
    )
    analysis = FunctionReturnAnalysis(
        function_name="ambiguous",
        entry_point="0x1000",
        parameters=[
            {"name": "x", "index": 0, "size": 4, "data_type": "int"}
        ],
        returns=[
            ReturnInfo("0x1010", Expression.constant(1, size=4), [positive]),
            ReturnInfo("0x1020", Expression.constant(2, size=4), [below_ten]),
        ],
        return_type="int",
    )
    strategy = MonolithicStrategy(FormulaBuilder(), ParallelSolverRunner(timeout=5))

    assert strategy._build_region_plan(analysis, analysis) is None


def test_split_receipt_is_sealed_before_cleanup_and_rechecked_by_final_gate() -> None:
    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))

    assert result.is_equivalent is True
    provenance = result.call_proof_terminal_provenance
    assert provenance["comparison_receipt_id"]
    assert provenance["dispatch_cleanup_complete"] is True
    labels = {
        record["query_label"]
        for record in provenance["query_execution_receipts"]
    }
    assert labels == {
        "monolithic.region:0:0:guard",
        "monolithic.region:0:0:value",
    }
    terminal = provenance["monolithic_terminal_receipt"]
    assert terminal["outcome_kind"] == "eq_closure"
    assert terminal["validated"] is True


def test_decisive_not_eq_terminal_receipt_binds_replay_and_safety() -> None:
    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 8))

    assert result.is_equivalent is False
    terminal = result.call_proof_terminal_provenance["monolithic_terminal_receipt"]
    assert terminal["outcome_kind"] == "decisive_counterexample"
    assert terminal["sat_region_id"] == "0:0"
    assert terminal["model_digest"]
    assert terminal["fixed_model_assertion_digest"]
    assert terminal["legacy_replay_receipt_digest"]
    assert terminal["counterexample_safety_receipt_digest"]
    assert terminal["gate_reference_digests"]
    assert terminal["validated"] is True


def test_same_name_not_eq_is_authorized_by_typed_whole_surface_replay() -> None:
    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("same_name", 7), _analysis("same_name", 8))

    assert result.is_equivalent is False
    terminal = result.call_proof_terminal_provenance["monolithic_terminal_receipt"]
    assert terminal["outcome_kind"] == "decisive_counterexample"
    assert terminal["counterexample_safety_receipt_digest"]
    assert terminal["validated"] is True


def test_production_split_does_not_trust_monkeypatched_strategy_planner(monkeypatch) -> None:
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    )
    monkeypatch.setattr(
        checker.monolithic_strategy,
        "_build_region_plan",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(AssertionError("untrusted planner")),
    )

    result = checker.check(_analysis("left", 7), _analysis("right", 7))

    assert result.is_equivalent is True


def test_final_verifier_rejects_forged_unexecuted_unsat_region(monkeypatch) -> None:
    from scripts.function_tracer_pcode.equivalence.call_effect_preflight import (
        QueryExecutionRecord,
    )
    from scripts.function_tracer_pcode.equivalence.strategies import (
        monolithic as monolithic_module,
    )
    from scripts.function_tracer_pcode.smt import ParallelResult

    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    )

    def forged_execute(*_args, **kwargs):
        plan = kwargs["plan"]
        formula = "(set-logic QF_BV)\n(assert false)\n(check-sat)"
        import hashlib
        digest = hashlib.sha256(formula.encode("utf-8")).hexdigest()
        record = QueryExecutionRecord(
            query_label="monolithic.region:0:0:guard",
            premise_digest=plan.plan_digest,
            formula_digest=digest,
            disposition="unsat",
            proof_kind="monolithic_region_guard",
            projection_binding_ids=(),
            formula_text=formula,
        )
        return monolithic_module._MonolithicRegionExecution(
            True,
            ParallelResult(results=[], is_equivalent=True),
            None,
            formula,
            (record,),
            {
                "total": 1, "unsat": 1, "sat": 0, "unknown": 0, "error": 0,
                "planned_regions": 1, "closed_regions": 1,
            },
            {
                "monolithic_split_planned_regions": 1,
                "monolithic_split_closed_regions": 1,
            },
            plan,
        )

    monkeypatch.setattr(checker.monolithic_strategy, "_execute_region_plan", forged_execute)

    result = checker.check(_analysis("left", 7), _analysis("right", 7))

    assert result.is_equivalent is None
    assert any(
        "monolithic_proof_bundle_invalid" in tuple(reason.evidence_refs or ())
        for reason in result.unknown_reasons
    )
    terminal = result.call_proof_terminal_provenance["monolithic_terminal_receipt"]
    assert terminal["outcome_kind"] == "inconclusive_diagnostic"


def test_production_split_uses_import_pinned_query_builder(monkeypatch) -> None:
    from scripts.function_tracer_pcode.equivalence.strategies import pairwise_query_builder

    monkeypatch.setattr(
        pairwise_query_builder,
        "build_pair_query",
        lambda *_args, **_kwargs: "(set-logic QF_BV)\n(assert false)\n(check-sat)",
    )
    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))

    assert result.is_equivalent is True


def test_untrusted_assert_false_in_base_context_fails_closed() -> None:
    class InjectedFalseFormulaBuilder(FormulaBuilder):
        def build_base_context(self, *args, **kwargs):
            context = super().build_base_context(*args, **kwargs)
            context["header_lines"] = [*context["header_lines"], "(assert false)"]
            return context

    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    )
    injected = InjectedFalseFormulaBuilder()
    checker.formula_builder = injected
    checker.monolithic_strategy.formula_builder = injected

    result = checker.check(_analysis("left", 7), _analysis("right", 7))

    assert result.is_equivalent is None
    terminal = result.call_proof_terminal_provenance["monolithic_terminal_receipt"]
    assert terminal["outcome_kind"] == "inconclusive_diagnostic"
    assert terminal["validated"] is True
    frame = result._prepared_dispatch_frame
    assert not frame.production_branch_authority_lease.validates()
    assert not frame.monolithic_execution_authority_lease.validates(
        frame.production_branch_authority_lease
    )


def test_region_query_slices_unrelated_assertions_and_deduplicates_prelude() -> None:
    class NoisyFormulaBuilder(FormulaBuilder):
        def build_base_context(self, *args, **kwargs):
            context = super().build_base_context(*args, **kwargs)
            noise = "(assert (= irrelevant_monolithic (_ bv9 32)))"
            context["header_lines"] = [
                *context["header_lines"],
                "(declare-const irrelevant_monolithic (_ BitVec 32))",
                noise,
                noise,
            ]
            return context

    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    )
    noisy = NoisyFormulaBuilder()
    checker.formula_builder = noisy
    checker.monolithic_strategy.formula_builder = noisy

    result = checker.check(_analysis("left", 7), _analysis("right", 7))

    assert result.is_equivalent is True
    assert result.pairwise_debug_stats["monolithic_split_sliced_assertion_bytes"] > 0
    assert result.pairwise_debug_stats["monolithic_split_shared_preludes"] == 1


def test_production_region_queries_share_one_incremental_z3_context() -> None:
    parameter = Expression.parameter("x", 0, data_type="int", size=4)
    zero = Expression.constant(0, size=4)
    analysis = FunctionReturnAnalysis(
        function_name="identity",
        entry_point="0x1000",
        parameters=[{"name": "x", "index": 0, "size": 4, "data_type": "int"}],
        returns=[
            ReturnInfo(
                "0x1010", Expression.constant(1, size=4),
                [Condition(Expression.binary_op("INT_EQUAL", parameter, zero))],
            ),
            ReturnInfo(
                "0x1020", Expression.constant(2, size=4),
                [Condition(Expression.binary_op("INT_NOTEQUAL", parameter, zero))],
            ),
        ],
        return_type="int",
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(analysis, analysis)

    assert result.is_equivalent is True
    assert result.pairwise_debug_stats["monolithic_split_shared_z3_contexts"] == 1
    assert result.pairwise_debug_stats["monolithic_split_shared_z3_checks"] == 6
    assert result.pairwise_debug_stats["monolithic_split_shared_z3_asts"] >= 1


def test_split_ignores_late_shared_z3_factory_monkeypatch(monkeypatch) -> None:
    from scripts.function_tracer_pcode.equivalence import monolithic_authority
    from scripts.function_tracer_pcode.smt import ParallelResult

    class FakeSession:
        shared_ast_count = 0
        check_count = 0

        def execute(self, _query, _timeout):
            return ParallelResult(results=[], is_equivalent=True)

    monkeypatch.setattr(
        monolithic_authority,
        "create_shared_z3_region_session",
        lambda *_args, **_kwargs: FakeSession(),
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 8))

    assert result.is_equivalent is False


def test_split_ignores_late_strategy_module_factory_symbol(monkeypatch) -> None:
    from scripts.function_tracer_pcode.equivalence.strategies import monolithic
    from scripts.function_tracer_pcode.smt import ParallelResult

    class FakeSession:
        def execute(self, _query, _timeout):
            return ParallelResult(results=[], is_equivalent=True)

    monkeypatch.setattr(
        monolithic,
        "_PINNED_CREATE_SHARED_Z3_REGION_SESSION",
        lambda *_args, **_kwargs: FakeSession(),
    )
    monkeypatch.setattr(
        monolithic,
        "_PINNED_EXECUTE_EXPECTED_VALUE_QUERY",
        lambda *_args, **_kwargs: ParallelResult(results=[], is_equivalent=True),
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 8))

    assert result.is_equivalent is False


def test_split_ignores_late_shared_z3_execute_monkeypatch(monkeypatch) -> None:
    from scripts.function_tracer_pcode.equivalence import monolithic_authority
    from scripts.function_tracer_pcode.smt import ParallelResult

    monkeypatch.setattr(
        monolithic_authority.SharedZ3RegionSession,
        "execute",
        lambda *_args, **_kwargs: ParallelResult(results=[], is_equivalent=True),
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 8))

    assert result.is_equivalent is False


def test_split_ignores_late_pinned_executor_symbol_monkeypatch(monkeypatch) -> None:
    from scripts.function_tracer_pcode.equivalence import monolithic_authority
    from scripts.function_tracer_pcode.smt import ParallelResult

    monkeypatch.setattr(
        monolithic_authority,
        "_PINNED_SHARED_Z3_EXECUTE",
        lambda *_args, **_kwargs: ParallelResult(results=[], is_equivalent=True),
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 8))

    assert result.is_equivalent is False


def test_split_ignores_strategy_executor_attribute(monkeypatch) -> None:
    from scripts.function_tracer_pcode.smt import ParallelResult

    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    )
    monkeypatch.setattr(
        checker.monolithic_strategy,
        "_monolithic_shared_region_executor",
        lambda *_args, **_kwargs: ParallelResult(results=[], is_equivalent=True),
        raising=False,
    )

    result = checker.check(_analysis("left", 7), _analysis("right", 8))

    assert result.is_equivalent is False


def test_counterexample_gate_cannot_self_report_proven(monkeypatch) -> None:
    from scripts.function_tracer_pcode.equivalence import monolithic_authority

    original = monolithic_authority.issue_gate_artifact_reference
    attempted = []

    def reject_self_report(frozen, kind, source, **kwargs):
        if kind in {"coverage", "effect", "width"}:
            kwargs["status"] = "proven"
            attempted.append(kind)
        return original(frozen, kind, source, **kwargs)

    monkeypatch.setattr(
        monolithic_authority, "issue_gate_artifact_reference", reject_self_report
    )
    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 8))

    assert attempted
    assert result.is_equivalent is None
    assert any(
        "gate_artifact_reference_proof_invalid" in tuple(reason.evidence_refs or ())
        for reason in result.unknown_reasons
    )


def test_final_gate_verifier_is_pinned_and_rechecks_source(monkeypatch) -> None:
    from scripts.function_tracer_pcode.equivalence import monolithic_authority
    from scripts.function_tracer_pcode.equivalence.call_effect_preflight import (
        finalize_monolithic_comparison_receipt,
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 8))
    frame = result._prepared_dispatch_frame
    terminal = frame.monolithic_terminal_receipt
    safety = terminal.counterexample_safety_receipt
    width_ref = next(
        item for item in safety.gate_references if item.gate_kind == "width"
    )
    forged_width_ref = replace(
        width_ref, source_artifact=(object(), object())
    )
    forged_refs = tuple(
        forged_width_ref if item.gate_kind == "width" else item
        for item in safety.gate_references
    )
    frame.monolithic_terminal_receipt = replace(
        terminal,
        counterexample_safety_receipt=replace(
            safety, gate_references=forged_refs
        ),
    )
    monkeypatch.setattr(
        monolithic_authority.GateArtifactReference,
        "validates",
        lambda *_args, **_kwargs: True,
    )
    monkeypatch.setattr(
        monolithic_authority,
        "_verify_gate_source",
        lambda *_args, **_kwargs: ("not_required", "equal_observed_return_width"),
    )

    with pytest.raises(RuntimeError, match="terminal_receipt_invalid"):
        finalize_monolithic_comparison_receipt(frame)


def test_final_verifier_rejects_forged_record_formula_despite_method_patch(
    monkeypatch,
) -> None:
    from scripts.function_tracer_pcode.equivalence.call_effect_preflight import (
        QueryExecutionRecord,
        finalize_monolithic_comparison_receipt,
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))
    frame = result._prepared_dispatch_frame
    terminal = frame.monolithic_terminal_receipt
    bundle = terminal.proof_bundle
    forged_records = (
        replace(bundle.query_records[0], formula_text="(assert false)"),
        *bundle.query_records[1:],
    )
    frame.monolithic_terminal_receipt = replace(
        terminal,
        proof_bundle=replace(bundle, query_records=forged_records),
    )
    monkeypatch.setattr(QueryExecutionRecord, "validate", lambda _self: True)

    with pytest.raises(RuntimeError, match="terminal_receipt_invalid"):
        finalize_monolithic_comparison_receipt(frame)


def test_final_verifier_does_not_dispatch_artifact_validation_methods(
    monkeypatch,
) -> None:
    from scripts.function_tracer_pcode.equivalence import monolithic_authority
    from scripts.function_tracer_pcode.equivalence.call_effect_preflight import (
        finalize_monolithic_comparison_receipt,
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))
    frame = result._prepared_dispatch_frame
    terminal = frame.monolithic_terminal_receipt
    bundle = terminal.proof_bundle
    forged_queries = (
        replace(bundle.query_set.queries[0], formula="(assert false)"),
        *bundle.query_set.queries[1:],
    )
    forged_query_set = replace(bundle.query_set, queries=forged_queries)
    frame.monolithic_terminal_receipt = replace(
        terminal,
        proof_bundle=replace(bundle, query_set=forged_query_set),
    )
    for artifact_type in (
        monolithic_authority.FrozenSurface,
        monolithic_authority.CanonicalRegionCensus,
        monolithic_authority.ExpectedRegionQueryContract,
        monolithic_authority.RenderedRegionQuery,
        monolithic_authority.ExpectedRegionQuerySet,
        monolithic_authority.SharedZ3SessionCertificate,
        monolithic_authority.RegionSolverExecutionReceipt,
    ):
        monkeypatch.setattr(
            artifact_type, "validates", lambda *_args, **_kwargs: True
        )
    # The terminal verifier captures the complete pure-verifier graph at
    # definition time.  Replacing the public/module symbols later must not
    # redirect verification of an already-issued authority artifact.
    for helper_name in (
        "verify_monolithic_proof_bundle",
        "_verify_frozen_surface",
        "_verify_canonical_census",
        "_verify_expected_query_set",
        "_verify_session_certificate",
        "_verify_region_execution_receipt",
        "_verify_query_execution_record",
        "_record_digest",
    ):
        monkeypatch.setattr(
            monolithic_authority, helper_name, lambda *_args, **_kwargs: True
        )
    monkeypatch.setattr(
        monolithic_authority,
        "reconstruct_canonical_census",
        lambda *_args, **_kwargs: bundle.census,
    )
    monkeypatch.setattr(
        monolithic_authority,
        "build_expected_region_query_set",
        lambda *_args, **_kwargs: forged_query_set,
    )
    monkeypatch.setattr(
        monolithic_authority,
        "_query_from_set",
        lambda *_args, **_kwargs: forged_queries[0],
    )
    monkeypatch.setattr(
        monolithic_authority,
        "_seal",
        lambda *_args, **_kwargs: terminal.seal,
    )

    with pytest.raises(RuntimeError, match="terminal_receipt_invalid"):
        finalize_monolithic_comparison_receipt(frame)


def test_final_verifier_rejects_authority_artifact_subclasses() -> None:
    from scripts.function_tracer_pcode.equivalence import monolithic_authority
    from scripts.function_tracer_pcode.equivalence.call_effect_preflight import (
        finalize_monolithic_comparison_receipt,
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))
    frame = result._prepared_dispatch_frame
    terminal = frame.monolithic_terminal_receipt
    bundle = terminal.proof_bundle

    class ForgedRenderedRegionQuery(monolithic_authority.RenderedRegionQuery):
        pass

    original = bundle.query_set.queries[0]
    forged = ForgedRenderedRegionQuery(
        original.contract, original.formula, original.render_context
    )
    forged_query_set = replace(
        bundle.query_set,
        queries=(forged, *bundle.query_set.queries[1:]),
    )
    frame.monolithic_terminal_receipt = replace(
        terminal,
        proof_bundle=replace(bundle, query_set=forged_query_set),
    )

    with pytest.raises(RuntimeError, match="terminal_receipt_invalid"):
        finalize_monolithic_comparison_receipt(frame)


def test_proof_bundle_binds_session_to_backend_query_set_and_lease() -> None:
    from scripts.function_tracer_pcode.equivalence import monolithic_authority

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))
    bundle = result._prepared_dispatch_frame.monolithic_terminal_receipt.proof_bundle
    certificate = replace(
        bundle.session_certificate,
        backend_identity=("fake-z3", "0", "fake-execute"),
    )

    assert not monolithic_authority.verify_monolithic_proof_bundle(
        replace(bundle, session_certificate=certificate)
    )


def test_frame_close_revokes_leases_and_rejects_post_close_issuance() -> None:
    from scripts.function_tracer_pcode.equivalence.call_effect_preflight import (
        issue_inconclusive_monolithic_receipts,
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))
    frame = result._prepared_dispatch_frame

    assert frame.lifecycle_state == "closed"
    assert not frame.production_branch_authority_lease.validates()
    assert not frame.monolithic_execution_authority_lease.validates(
        frame.production_branch_authority_lease
    )
    with pytest.raises(RuntimeError, match="scope_closed"):
        issue_inconclusive_monolithic_receipts(frame, None, None, "late")


def test_pinned_terminal_verifier_rejects_method_monkeypatch(monkeypatch) -> None:
    from scripts.function_tracer_pcode.equivalence.call_effect_preflight import (
        finalize_monolithic_comparison_receipt,
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))
    frame = result._prepared_dispatch_frame
    receipt_type = type(frame.monolithic_terminal_receipt)
    frame.monolithic_terminal_receipt = replace(
        frame.monolithic_terminal_receipt, seal="0" * 64
    )
    monkeypatch.setattr(receipt_type, "validates", lambda _self: True)

    with pytest.raises(RuntimeError, match="terminal_receipt_invalid"):
        finalize_monolithic_comparison_receipt(frame)


def test_import_pinned_verifiers_ignore_late_module_monkeypatch(monkeypatch) -> None:
    from scripts.function_tracer_pcode.equivalence import monolithic_authority
    from scripts.function_tracer_pcode.equivalence.call_effect_preflight import (
        finalize_monolithic_comparison_receipt,
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))
    frame = result._prepared_dispatch_frame
    monkeypatch.setattr(
        monolithic_authority, "verify_terminal_decision_receipt", lambda _item: False
    )
    monkeypatch.setattr(
        monolithic_authority, "verify_monolithic_proof_bundle", lambda _item: False
    )

    assert finalize_monolithic_comparison_receipt(frame) is frame.receipt


def test_tampered_typed_counterexample_safety_receipt_is_rejected() -> None:
    from scripts.function_tracer_pcode.equivalence.call_effect_preflight import (
        finalize_monolithic_comparison_receipt,
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 8))
    frame = result._prepared_dispatch_frame
    safety = replace(
        frame.monolithic_terminal_receipt.counterexample_safety_receipt,
        seal="0" * 64,
    )
    frame.monolithic_terminal_receipt = replace(
        frame.monolithic_terminal_receipt,
        counterexample_safety_receipt=safety,
    )

    with pytest.raises(RuntimeError, match="terminal_receipt_invalid"):
        finalize_monolithic_comparison_receipt(frame)


def test_direct_checker_revokes_parent_lease_when_child_derivation_fails(
    monkeypatch,
) -> None:
    from scripts.function_tracer_pcode.equivalence import monolithic_authority

    active_before = set(monolithic_authority._ACTIVE_BRANCHES)
    monkeypatch.setattr(
        monolithic_authority,
        "derive_monolithic_execution_authority",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            RuntimeError("forced_child_derivation_failure")
        ),
    )

    result = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))

    assert result.is_equivalent is None
    assert set(monolithic_authority._ACTIVE_BRANCHES) == active_before


def test_replan_generation_cannot_reuse_stale_child_lease() -> None:
    first = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))._prepared_dispatch_frame
    second = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    ).check(_analysis("left", 7), _analysis("right", 7))._prepared_dispatch_frame

    assert first.monolithic_execution_authority_lease.validates(
        first.production_branch_authority_lease, require_active=False
    )
    assert not first.monolithic_execution_authority_lease.validates(
        second.production_branch_authority_lease, require_active=False
    )


def test_region_timeout_budget_does_not_mutate_strategy_configuration() -> None:
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5, enable_rewrite=False
    )
    configured = checker.monolithic_strategy.per_query_timeout

    checker.check(_analysis("left", 7), _analysis("right", 7))

    assert checker.monolithic_strategy.per_query_timeout == configured


def test_legacy_mode_is_an_explicit_validation_control() -> None:
    result = EquivalenceChecker(
        strategy="monolithic",
        timeout=5,
        monolithic_timeout=5,
        monolithic_query_mode="legacy",
        enable_rewrite=False,
    ).check(_analysis("left", 7), _analysis("right", 7))

    assert result.is_equivalent is True
    assert result.pairwise_debug_stats["monolithic_legacy_fallback"] == 1
    assert result.pairwise_debug_stats["monolithic_legacy_query_bytes"] > 0
    assert result.pairwise_debug_stats["monolithic_legacy_solver_checks"] == 1
    terminal = result.call_proof_terminal_provenance["monolithic_terminal_receipt"]
    assert terminal["outcome_kind"] == "eq_closure"
