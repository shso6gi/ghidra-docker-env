# -*- coding: utf-8 -*-
"""Issue #325 (E1): the obligation-scope mechanism.

* the blocking rule (`authority.decision.obligation_scope`): guards x relies_on,
  every undecidable case on the blocking side (AC 4);
* both finalizers use that one rule, and with no declaration and no narrowed
  reliance they decide exactly what the old ``decision_effect`` rule decided,
  with the same receipt digests (AC 1-3 at the unit level, AC 5);
* the reliance closure (`core.fact_reliance`): upstream traversal, mandatory
  provenance, deterministic digest (AC 6).
"""

from __future__ import annotations

import ast
import itertools
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.contracts import (
    BlockerEligibilityBaseRow,
    CActiveBaseRow,
    Outcome,
    QOpenBaseRow,
    VerifiedLifecycleProjection,
    authority_digest,
)
from scripts.function_tracer_pcode.authority.decision import obligation_scope as scope_module
from scripts.function_tracer_pcode.authority.decision.conditional import (
    ConditionalDecisiveProofKind,
    ConditionalDecisiveProofReceipt,
    ConditionalFinalizationAuthority,
    finalize_conditional_decision,
    finalize_conditional_decision_with_scope,
)
from scripts.function_tracer_pcode.authority.decision.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    FinalizationAuthority,
    finalize_decision,
    finalize_decision_with_scope,
)
from scripts.function_tracer_pcode.authority.decision.obligation_scope import (
    FAMILY_BY_PROOF_KIND,
    PRODUCTION_GUARD_DECLARATIONS,
    PRODUCTION_REASON_REGISTRIES,
    DecisionSide,
    GuardDeclaration,
    Lane,
    ProofFamily,
    ScopeBasis,
    ScopedEvidence,
    SealedGuardRegistry,
    evaluate_obligation_scope,
    production_guard_registry,
    production_reason_ids,
    rows_digest,
    scoped_evidence,
)
from scripts.function_tracer_pcode.core.fact_reliance import (
    FactHandle,
    FactKind,
    FactProvenance,
    FactSide,
    FactSlot,
    FactTarget,
    RelianceBasis,
    ReliesOn,
)
from scripts.function_tracer_pcode.proof.assumptions import AssumptionKind, AssumptionPremise

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
RESULT_ID = "result-325"
EFFECTS = ("blocks_equivalence", "blocks_disequivalence", "blocks_decision", "diagnostic_only")
LEFT_RETURN = FactTarget(FactSide.LEFT, FactSlot.RETURN)
RIGHT_RETURN = FactTarget(FactSide.RIGHT, FactSlot.RETURN)


def _row(index, effect="blocks_disequivalence", reason="reason_a"):
    return CActiveBaseRow(RESULT_ID, f"occ-{index}", f"cause-{index}", reason, "domain", effect, "target")


def _projection(rows=()):
    rows = tuple(rows)
    return VerifiedLifecycleProjection.seal(
        result_occurrence_id=RESULT_ID,
        snapshot_digest="snapshot",
        c_active_base=rows,
        q_open_base=tuple(
            QOpenBaseRow(RESULT_ID, row.occurrence_id, row.cause_id, f"req-{i}", "kind", "target")
            for i, row in enumerate(rows)
        ),
        blocker_eligibility_base=tuple(
            BlockerEligibilityBaseRow(RESULT_ID, row.occurrence_id, row.cause_id) for row in rows
        ),
        satisfaction_projection={
            "occurrences": tuple(
                {"occurrence_id": row.occurrence_id, "cause_id": row.cause_id,
                 "live_requirement_ids": (f"req-{i}",), "active": True}
                for i, row in enumerate(rows)
            ),
            "execution_event_digests": (),
        },
    )


def _leaf(kind, target, origin="program-bytes"):
    return FactHandle(kind, target, provenance=FactProvenance.leaf(producer_site="test", origin=origin))


def _narrow(*handles):
    reliance = ReliesOn.closure_of(handles)
    assert reliance.basis is RelianceBasis.CLOSURE
    return reliance


def _concrete(reliance, evidence_id="concrete"):
    return scoped_evidence("CONDITIONAL_CONCRETE_COUNTEREXAMPLE", evidence_id, relies_on=reliance)


def _registry(**guards):
    return SealedGuardRegistry.build(
        GuardDeclaration(reason, frozenset(kinds), basis="test") for reason, kinds in guards.items()
    )


def _evaluate(rows, evidence, registry):
    return evaluate_obligation_scope(
        lane=Lane.CONDITIONAL, result_occurrence_id=RESULT_ID,
        lifecycle_projection_digest="p", rows=rows, evidence=evidence, registry=registry,
    )


@pytest.fixture
def mapped_targets(monkeypatch):
    """Map every row onto both sides' return slot (E1 maps none; E4 adds the mapping)."""
    monkeypatch.setattr(
        scope_module, "row_fact_targets", lambda row: frozenset({LEFT_RETURN, RIGHT_RETURN}),
    )


# ------------------------------------------------------------- AC 4: the rule


def test_guards_that_intersect_the_reliance_block(mapped_targets):
    record = _evaluate(
        [_row(0)], [_concrete(_narrow(_leaf(FactKind.RETURN_LOCATION, LEFT_RETURN)))],
        _registry(reason_a={FactKind.RETURN_LOCATION}),
    )
    assert record.causes[0].bases == (ScopeBasis.INTERSECTS,)
    assert not record.side_decisive(DecisionSide.DISEQUIVALENCE)


def test_guards_disjoint_from_the_reliance_spare(mapped_targets):
    record = _evaluate(
        [_row(0)], [_concrete(_narrow(_leaf(FactKind.RETURN_LOCATION, LEFT_RETURN)))],
        _registry(reason_a={FactKind.LOOP_SUMMARY_VALIDITY}),
    )
    assert record.causes[0].bases == (ScopeBasis.DISJOINT,)
    assert record.side_decisive(DecisionSide.DISEQUIVALENCE)
    payload = record.to_json()
    assert payload["causes"][0]["bases"] == ["DISJOINT"]
    assert payload["evidence"][0]["unblocked"] is True


def test_the_same_kind_on_a_target_outside_the_row_does_not_intersect(monkeypatch):
    monkeypatch.setattr(scope_module, "row_fact_targets", lambda row: frozenset({RIGHT_RETURN}))
    record = _evaluate(
        [_row(0)], [_concrete(_narrow(_leaf(FactKind.RETURN_LOCATION, LEFT_RETURN)))],
        _registry(reason_a={FactKind.RETURN_LOCATION}),
    )
    assert record.causes[0].bases == (ScopeBasis.DISJOINT,)


def test_a_row_whose_target_cannot_be_mapped_blocks():
    # the production mapping (E1) maps no row
    assert scope_module.row_fact_targets(_row(0)) is None
    record = _evaluate(
        [_row(0)], [_concrete(_narrow(_leaf(FactKind.RETURN_LOCATION, LEFT_RETURN)))],
        _registry(reason_a={FactKind.LOOP_SUMMARY_VALIDITY}),
    )
    assert record.causes[0].bases == (ScopeBasis.TARGET_UNMAPPED,)
    assert not record.side_decisive(DecisionSide.DISEQUIVALENCE)


def test_an_unknown_provenance_blocks(mapped_targets):
    unrecorded = FactHandle(
        FactKind.RETURN_LOCATION, LEFT_RETURN,
        provenance=FactProvenance.unrecorded(producer_site="test", reason="phase not recorded"),
    )
    reliance = ReliesOn.closure_of([unrecorded])
    assert reliance.basis is RelianceBasis.UNKNOWN_PROVENANCE and reliance.universal
    record = _evaluate([_row(0)], [_concrete(reliance)], _registry(reason_a={FactKind.LOOP_SUMMARY_VALIDITY}))
    assert record.causes[0].bases == (ScopeBasis.RELIES_ON_UNKNOWN_PROVENANCE,)
    # no reliance supplied at all is the same
    record = _evaluate([_row(0)], [_concrete(None)], _registry(reason_a={FactKind.LOOP_SUMMARY_VALIDITY}))
    assert record.causes[0].bases == (ScopeBasis.RELIES_ON_UNKNOWN_PROVENANCE,)


def test_a_reason_without_a_declaration_guards_every_fact(mapped_targets):
    record = _evaluate(
        [_row(0, reason="undeclared")], [_concrete(_narrow(_leaf(FactKind.RETURN_LOCATION, LEFT_RETURN)))],
        _registry(reason_a={FactKind.LOOP_SUMMARY_VALIDITY}),
    )
    assert record.causes[0].bases == (ScopeBasis.GUARDS_UNDECLARED,)
    assert record.causes[0].guards_declared is False


def test_smt_evidence_relies_on_every_fact_and_cannot_be_narrowed(mapped_targets):
    smt = scoped_evidence("SAFE_COUNTEREXAMPLE", "smt")
    assert smt.relies_on.basis is RelianceBasis.ALL_FACTS
    record = _evaluate([_row(0)], [smt], _registry(reason_a={FactKind.LOOP_SUMMARY_VALIDITY}))
    assert record.causes[0].bases == (ScopeBasis.RELIES_ON_ALL_FACTS,)
    narrow = _narrow(_leaf(FactKind.RETURN_LOCATION, LEFT_RETURN))
    for kind in ("EQ_CLOSURE", "SAFE_COUNTEREXAMPLE", "CONDITIONAL_EQ_CLOSURE", "CONDITIONAL_SAFE_COUNTEREXAMPLE"):
        with pytest.raises(ValueError):
            scoped_evidence(kind, "smt", relies_on=narrow)
    with pytest.raises(ValueError):
        ScopedEvidence("smt", "SAFE_COUNTEREXAMPLE", ProofFamily.SMT_COUNTEREXAMPLE, narrow)


def test_a_row_whose_effect_does_not_apply_to_the_side_spares():
    record = _evaluate(
        [_row(0, effect="blocks_equivalence"), _row(1, effect="diagnostic_only")],
        [scoped_evidence("SAFE_COUNTEREXAMPLE", "smt")], SealedGuardRegistry.build(()),
    )
    assert [cause.bases for cause in record.causes] == [
        (ScopeBasis.EFFECT_NOT_APPLICABLE,), (ScopeBasis.EFFECT_NOT_APPLICABLE,),
    ]
    assert record.side_decisive(DecisionSide.DISEQUIVALENCE)
    assert not record.side_decisive(DecisionSide.EQUIVALENCE)  # no EQ evidence at all


def test_a_side_is_decisive_when_one_of_its_evidences_is_left_unblocked(mapped_targets):
    spared = _concrete(_narrow(_leaf(FactKind.RETURN_LOCATION, LEFT_RETURN)))
    record = _evaluate(
        [_row(0)], [scoped_evidence("CONDITIONAL_SAFE_COUNTEREXAMPLE", "smt"), spared],
        _registry(reason_a={FactKind.SMT_MODEL_REALIZABILITY}),
    )
    assert record.causes[0].bases == (ScopeBasis.RELIES_ON_ALL_FACTS, ScopeBasis.DISJOINT)
    assert record.side_decisive(DecisionSide.DISEQUIVALENCE)


def test_one_evidence_per_proof_kind_is_recorded():
    record = _evaluate(
        [], [scoped_evidence("SAFE_COUNTEREXAMPLE", "a"), scoped_evidence("SAFE_COUNTEREXAMPLE", "b")],
        SealedGuardRegistry.build(()),
    )
    assert [item.evidence_id for item in record.evidence] == ["a"]


# ------------------------------------------------------------- the registry


def test_the_production_registry_declares_nothing_in_e1():
    assert PRODUCTION_GUARD_DECLARATIONS == ()
    registry = production_guard_registry()
    assert registry.declared_reason_ids() == ()
    assert registry.guards_for("counterexample_analysis_safety_unproven") is None


def test_a_declaration_is_validated():
    with pytest.raises(ValueError):
        GuardDeclaration("r", frozenset({FactKind.UNKNOWN_PROVENANCE}), basis="t")
    with pytest.raises(TypeError):
        GuardDeclaration("r", frozenset(), basis="t")
    with pytest.raises(TypeError):
        GuardDeclaration("r", frozenset({"RETURN_LOCATION"}), basis="t")
    with pytest.raises(TypeError):
        GuardDeclaration("r", frozenset({FactKind.RETURN_LOCATION}), basis="")
    declaration = GuardDeclaration("r", frozenset({FactKind.RETURN_LOCATION}), basis="t")
    with pytest.raises(ValueError):
        SealedGuardRegistry.build([declaration, declaration])
    with pytest.raises(ValueError):
        SealedGuardRegistry.build([declaration], known_reason_ids=frozenset({"other"}))
    with pytest.raises(ValueError):
        SealedGuardRegistry({}, "digest")


def test_the_registry_digest_does_not_depend_on_the_declaration_order():
    a = GuardDeclaration("a", frozenset({FactKind.RETURN_LOCATION}), basis="t")
    b = GuardDeclaration("b", frozenset({FactKind.LOOP_SUMMARY_VALIDITY, FactKind.TYPE_HYPOTHESIS}), basis="t")
    assert SealedGuardRegistry.build([a, b]).digest == SealedGuardRegistry.build([b, a]).digest
    assert SealedGuardRegistry.build([a]).digest != SealedGuardRegistry.build([b]).digest


def _module_level_reason_registries():
    found = set()
    for path in sorted((PACKAGE_ROOT / "authority").rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in tree.body:
            if not isinstance(node, ast.Assign) or not isinstance(node.value, ast.Call):
                continue
            func = node.value.func
            if (
                isinstance(func, ast.Attribute) and func.attr == "build"
                and isinstance(func.value, ast.Name) and func.value.id == "SealedReasonRegistry"
            ):
                module = ".".join(("scripts", "function_tracer_pcode", *path.relative_to(PACKAGE_ROOT).with_suffix("").parts))
                for target in node.targets:
                    found.add(f"{module}:{target.id}")
    return found


def test_the_declarable_reason_registries_are_every_sealed_authority_registry():
    assert set(PRODUCTION_REASON_REGISTRIES) == _module_level_reason_registries()
    ids = production_reason_ids()
    assert "counterexample_analysis_safety_unproven" in ids
    assert "recurrence_proposal_validation_unproven" in ids


def test_every_decisive_proof_kind_has_a_family():
    kinds = {kind.value for kind in DecisiveProofKind} | {kind.value for kind in ConditionalDecisiveProofKind}
    assert set(FAMILY_BY_PROOF_KIND) == kinds


# ------------------------------------------------- AC 1-3, 5: the finalizers


def _legacy_outcome(rows, has_eq, has_not_eq, *, conditional=False):
    """The pre-#325 rule, spelled out independently of the production code."""
    blocks_eq = any(row.decision_effect in {"blocks_equivalence", "blocks_decision"} for row in rows)
    blocks_not_eq = any(row.decision_effect in {"blocks_disequivalence", "blocks_decision"} for row in rows)
    if has_eq and has_not_eq:
        return Outcome.ERROR
    if has_eq:
        return Outcome.EQUIVALENT if not blocks_eq else Outcome.UNKNOWN
    if has_not_eq:
        return Outcome.NOT_EQ if not blocks_not_eq else Outcome.UNKNOWN
    if conditional:
        return Outcome.UNKNOWN
    return Outcome.UNKNOWN if rows else Outcome.ERROR


def _row_sets():
    for count in range(3):
        for effects in itertools.product(EFFECTS, repeat=count):
            yield tuple(_row(i, effect) for i, effect in enumerate(effects))


def _decisive(projection, kind):
    return DecisiveProofReceipt.create(
        result_occurrence_id=RESULT_ID,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        proof_kind=kind, proof_artifact_digest=f"artifact-{kind.value}",
    )


@pytest.mark.parametrize("kinds", [(), (DecisiveProofKind.EQ_CLOSURE,), (DecisiveProofKind.SAFE_COUNTEREXAMPLE,),
                                   (DecisiveProofKind.EQ_CLOSURE, DecisiveProofKind.SAFE_COUNTEREXAMPLE)])
def test_the_unconditional_finalizer_decides_what_the_decision_effect_rule_decided(kinds):
    for rows in _row_sets():
        projection = _projection(rows)
        receipts = tuple(_decisive(projection, kind) for kind in kinds)
        finalization = finalize_decision_with_scope(
            FinalizationAuthority(RESULT_ID, projection, decisive_proof_receipts=receipts)
        )
        expected = _legacy_outcome(
            projection.c_active_base,
            DecisiveProofKind.EQ_CLOSURE in kinds, DecisiveProofKind.SAFE_COUNTEREXAMPLE in kinds,
        )
        assert finalization.receipt.outcome is expected, (rows, kinds)
        # the receipt digest is the pre-#325 one: the scope is not bound when nothing is narrowed
        legacy_input = authority_digest({
            "result_occurrence_id": RESULT_ID,
            "lifecycle_projection_digest": projection.lifecycle_projection_digest,
            "decisive_receipt_digests": tuple(receipt.receipt_digest for receipt in receipts),
            "terminal_timeout_receipt_digests": (),
            "error_receipt_digests": (),
            "malformed_authority": False,
        })
        assert finalization.receipt.authority_input_digest == legacy_input
        assert not finalization.obligation_scope.bound_to_receipt
        assert finalize_decision(
            FinalizationAuthority(RESULT_ID, projection, decisive_proof_receipts=receipts)
        ) == finalization.receipt
        scope = finalization.obligation_scope
        assert scope.lane is Lane.UNCONDITIONAL and scope.row_count == len(rows)
        assert scope.rows_digest == rows_digest(projection.c_active_base)
        assert all(
            basis in (ScopeBasis.EFFECT_NOT_APPLICABLE, ScopeBasis.RELIES_ON_ALL_FACTS)
            for cause in scope.causes for basis in cause.bases
        )


def _premises():
    return (AssumptionPremise(
        kind=AssumptionKind.CONCRETE_PCODE_SEMANTICS, subject="executor",
        payload={"executor": "e", "ghidra": "g", "languages": ("x",)},
    ),)


def _unconditional_unknown(projection):
    return finalize_decision(FinalizationAuthority(RESULT_ID, projection))


def _conditional_receipt(projection, kind, premises):
    return ConditionalDecisiveProofReceipt.create(
        result_occurrence_id=RESULT_ID,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        proof_kind=kind, proof_artifact_digest=f"artifact-{kind.value}",
        assumption_dependencies=premises,
    )


CONDITIONAL_KIND_SETS = [
    (), (ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE,),
    (ConditionalDecisiveProofKind.CONDITIONAL_SAFE_COUNTEREXAMPLE,),
    (ConditionalDecisiveProofKind.CONDITIONAL_CONCRETE_COUNTEREXAMPLE,),
    (ConditionalDecisiveProofKind.CONDITIONAL_SAFE_COUNTEREXAMPLE,
     ConditionalDecisiveProofKind.CONDITIONAL_CONCRETE_COUNTEREXAMPLE),
    (ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE,
     ConditionalDecisiveProofKind.CONDITIONAL_CONCRETE_COUNTEREXAMPLE),
]


@pytest.mark.parametrize("kinds", CONDITIONAL_KIND_SETS)
def test_the_conditional_finalizer_decides_what_the_decision_effect_rule_decided(kinds):
    premises = _premises()
    for rows in _row_sets():
        if not any(row.decision_effect != "diagnostic_only" for row in rows):
            continue  # the lane runs only after an unconditional UNKNOWN
        projection = _projection(rows)
        unconditional = _unconditional_unknown(projection)
        assert unconditional.outcome is Outcome.UNKNOWN
        receipts = tuple(_conditional_receipt(projection, kind, premises) for kind in kinds)
        authority = ConditionalFinalizationAuthority(
            RESULT_ID, unconditional, projection, premises, conditional_decisive_proof_receipts=receipts,
        )
        finalization = finalize_conditional_decision_with_scope(authority)
        expected = _legacy_outcome(
            projection.c_active_base,
            ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE in kinds,
            any(kind is not ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE for kind in kinds),
            conditional=True,
        )
        assert finalization.receipt.conditional_outcome is expected, (rows, kinds)
        legacy_input = authority_digest({
            "result_occurrence_id": RESULT_ID,
            "lifecycle_projection_digest": projection.lifecycle_projection_digest,
            "unconditional_receipt_digest": unconditional.receipt_digest,
            "assumption_set_digest": authority_digest(premises),
            "conditional_receipt_digests": tuple(receipt.receipt_digest for receipt in receipts),
            "malformed_authority": False,
        })
        assert finalization.receipt.authority_input_digest == legacy_input
        assert finalize_conditional_decision(authority) == finalization.receipt
        assert finalization.obligation_scope.lane is Lane.CONDITIONAL


def test_a_narrowed_concrete_reliance_is_bound_into_the_conditional_receipt(mapped_targets):
    # Not reachable in production in E1 (no declaration, no recorded provenance):
    # the binding exists so that a scope that can differ from the old rule is
    # always committed to by the receipt.
    rows = (_row(0),)
    projection = _projection(rows)
    premises = _premises()
    unconditional = _unconditional_unknown(projection)
    receipts = (_conditional_receipt(
        projection, ConditionalDecisiveProofKind.CONDITIONAL_CONCRETE_COUNTEREXAMPLE, premises,
    ),)
    narrow = _narrow(_leaf(FactKind.RETURN_LOCATION, LEFT_RETURN))
    universal = finalize_conditional_decision_with_scope(ConditionalFinalizationAuthority(
        RESULT_ID, unconditional, projection, premises, conditional_decisive_proof_receipts=receipts,
    ))
    bound = finalize_conditional_decision_with_scope(ConditionalFinalizationAuthority(
        RESULT_ID, unconditional, projection, premises, conditional_decisive_proof_receipts=receipts,
        concrete_reliance=narrow,
    ))
    assert not universal.obligation_scope.bound_to_receipt
    assert bound.obligation_scope.bound_to_receipt
    # undeclared guards still block, so the outcome is the same, but the receipt commits to the scope
    assert bound.receipt.conditional_outcome is universal.receipt.conditional_outcome is Outcome.UNKNOWN
    assert bound.receipt.authority_input_digest != universal.receipt.authority_input_digest
    with pytest.raises(TypeError):
        ConditionalFinalizationAuthority(
            RESULT_ID, unconditional, projection, premises, concrete_reliance="narrow",
        )


def test_a_forged_receipt_still_decides_error():
    projection = _projection((_row(0),))
    receipt = _decisive(projection, DecisiveProofKind.SAFE_COUNTEREXAMPLE)
    object.__setattr__(receipt, "receipt_digest", None)
    finalization = finalize_decision_with_scope(
        FinalizationAuthority(RESULT_ID, projection, decisive_proof_receipts=(receipt,))
    )
    assert finalization.receipt.outcome is Outcome.ERROR
    assert finalization.obligation_scope.evidence == ()


def test_rows_of_one_cause_judged_differently_make_the_decision_error():
    # impossible in a real lifecycle (a cause's reason fixes its decision_effect);
    # a projection that has it is not one lifecycle's, so the decision is ERROR
    rows = (
        CActiveBaseRow(RESULT_ID, "occ-0", "cause-x", "reason_a", "domain", "blocks_equivalence", "t"),
        CActiveBaseRow(RESULT_ID, "occ-1", "cause-x", "reason_a", "domain", "blocks_disequivalence", "t"),
    )
    projection = _projection(rows)
    receipt = _decisive(projection, DecisiveProofKind.SAFE_COUNTEREXAMPLE)
    finalization = finalize_decision_with_scope(
        FinalizationAuthority(RESULT_ID, projection, decisive_proof_receipts=(receipt,))
    )
    assert finalization.receipt.outcome is Outcome.ERROR
    assert finalization.obligation_scope.evidence == ()
    assert finalization.obligation_scope.row_count == 2


def test_the_blocking_rule_is_written_once():
    """AC 5: neither finalizer spells the decision_effect rule; both call the shared evaluation."""
    for relative in ("authority/decision/decision.py", "authority/decision/conditional.py"):
        tree = ast.parse((PACKAGE_ROOT / relative).read_text(encoding="utf-8"))
        literals = {
            node.value for node in ast.walk(tree)
            if isinstance(node, ast.Constant) and isinstance(node.value, str)
        }
        assert not literals & {"blocks_equivalence", "blocks_disequivalence", "blocks_decision"}, relative
        calls = {
            node.func.id for node in ast.walk(tree)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        }
        assert "evaluate_obligation_scope" in calls, relative
    owner = ast.parse((PACKAGE_ROOT / "authority/decision/obligation_scope.py").read_text(encoding="utf-8"))
    assert any(
        isinstance(node, ast.Constant) and node.value == "blocks_decision" for node in ast.walk(owner)
    )


# ------------------------------------------------------------- AC 6: closure


def test_the_closure_follows_the_upstream_provenance():
    raw = _leaf(FactKind.PROGRAM_IMAGE, FactTarget(FactSide.LEFT, FactSlot.PROGRAM))
    abi = _leaf(FactKind.ABI_MODEL, FactTarget(FactSide.PAIR, FactSlot.FUNCTION), origin="cspec")
    derived = FactHandle(
        FactKind.RETURN_LOCATION, LEFT_RETURN,
        provenance=FactProvenance.derived(producer_site="test", rule="abi-return", upstream=(raw, abi)),
    )
    reliance = ReliesOn.closure_of([derived])
    assert reliance.basis is RelianceBasis.CLOSURE
    assert {ref.kind for ref in reliance.refs} == {
        FactKind.RETURN_LOCATION, FactKind.PROGRAM_IMAGE, FactKind.ABI_MODEL,
    }


def test_an_unrecorded_origin_anywhere_upstream_makes_the_closure_universal():
    unrecorded = FactHandle(
        FactKind.TYPE_HYPOTHESIS, FactTarget(FactSide.LEFT, FactSlot.FUNCTION),
        provenance=FactProvenance.unrecorded(producer_site="test", reason="phase"),
    )
    derived = FactHandle(
        FactKind.PARAMETER_STORAGE, FactTarget(FactSide.LEFT, FactSlot.PARAMETERS),
        provenance=FactProvenance.derived(producer_site="test", rule="retype", upstream=(unrecorded,)),
    )
    reliance = ReliesOn.closure_of([derived])
    assert reliance.basis is RelianceBasis.UNKNOWN_PROVENANCE and reliance.universal
    assert reliance.unrecorded_sites == ("test:phase",)
    assert ReliesOn.closure_of([]).basis is RelianceBasis.UNKNOWN_PROVENANCE


def test_a_handle_cannot_be_made_without_its_provenance():
    with pytest.raises(TypeError):
        FactHandle(FactKind.RETURN_LOCATION, LEFT_RETURN, provenance=None)
    with pytest.raises(TypeError):
        FactHandle(FactKind.RETURN_LOCATION, LEFT_RETURN)  # noqa - provenance is keyword-required
    with pytest.raises(ValueError):
        FactProvenance("LEAF", "site", "origin", ())
    with pytest.raises(TypeError):
        FactProvenance.leaf(producer_site="", origin="x")
    with pytest.raises(TypeError):
        FactProvenance.derived(producer_site="s", rule="r", upstream=())
    with pytest.raises(ValueError):
        FactHandle(FactKind.UNKNOWN_PROVENANCE, LEFT_RETURN,
                   provenance=FactProvenance.leaf(producer_site="s", origin="o"))


def test_a_narrow_reliance_comes_only_from_a_closure():
    with pytest.raises(ValueError):
        ReliesOn(RelianceBasis.CLOSURE, (), ())
    with pytest.raises(TypeError):
        ReliesOn.closure_of(["RETURN_LOCATION"])


def test_the_closure_digest_is_deterministic():
    def handles():
        return [
            _leaf(FactKind.RETURN_LOCATION, LEFT_RETURN),
            _leaf(FactKind.PARAMETER_STORAGE, FactTarget(FactSide.RIGHT, FactSlot.PARAMETERS)),
        ]

    first = ReliesOn.closure_of(handles())
    again = ReliesOn.closure_of(list(reversed(handles())))
    assert first == again and first.digest == again.digest
    other = ReliesOn.closure_of(handles()[:1])
    assert other.digest != first.digest
    assert ReliesOn.all_facts().digest != ReliesOn.unknown_provenance(reason="x").digest


def test_a_handle_value_is_a_read_only_copy():
    source = {"storage": {"is_register": True}, "names": ["a"]}
    handle = FactHandle(
        FactKind.PARAMETER_STORAGE, LEFT_RETURN,
        provenance=FactProvenance.leaf(producer_site="s", origin="o"), value=source,
    )
    source["storage"]["is_register"] = False
    assert handle.value["storage"]["is_register"] is True
    assert handle.value["names"] == ("a",)
    with pytest.raises(TypeError):
        handle.value["storage"]["is_register"] = False
