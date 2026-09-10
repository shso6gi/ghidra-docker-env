# -*- coding: utf-8 -*-
"""Issue #20 PR-A: proof-owned assumption premises and the conditional column.

The conditional lane is not activated yet, so these tests pin the contract
itself: premises are canonical and deeply immutable, conditional receipts carry
their whole assumption set, and nothing conditional can reach the unconditional
outcome, the CLI exit code, or the unconditional summary columns.
"""
from __future__ import annotations

import json

import pytest

from scripts.function_tracer_pcode.authority.codecs import StrictV2JsonCodec
from scripts.function_tracer_pcode.authority.contracts import (
    BlockerEligibilityBaseRow,
    CActiveBaseRow,
    CLI_EXIT_CODE_BY_OUTCOME,
    Outcome,
    QOpenBaseRow,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    all_of,
    requirement_slot,
    VerifiedLifecycleProjection,
    assert_deep_immutable,
    authority_digest,
)
from scripts.function_tracer_pcode.authority.decision.conditional import (
    ConditionalDecisionReceipt,
    ConditionalDecisiveProofKind,
    ConditionalDecisiveProofReceipt,
    ConditionalFinalizationAuthority,
    assumption_dependencies_digest,
    canonical_assumption_dependencies,
    finalize_conditional_decision,
)
from scripts.function_tracer_pcode.authority.decision.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    DecisionReceipt,
    FinalizationAuthority,
    finalize_decision,
)
from scripts.function_tracer_pcode.authority.decision.production_cutover import (
    attach_canonical_decision,
    attach_conditional_decision,
    conditional_decision_receipt_payload,
    conditional_outcome_from_payload,
    outcome_from_payload,
    outcome_from_result,
)
from scripts.function_tracer_pcode.authority.registry import (
    SealedReasonRegistry,
    SealedRecoveryRegistry,
)
from scripts.function_tracer_pcode.proof.assumptions import (
    CONDITIONAL_ASSUMPTION_SCHEMA_VERSION,
    AssumptionKind,
    AssumptionPremise,
    normalize_assumption_premises,
)


REASON_ID = "pure_call_semantics_unproven"


def _premise(subject: str = "log", **payload) -> AssumptionPremise:
    return AssumptionPremise(
        kind=AssumptionKind.EXTERNAL_CALLEE_SPEC,
        subject=subject,
        payload=payload or {
            "canonical_symbol": subject,
            "signature": ("double", "double"),
            "no_observable_memory_write": True,
            "returns_normally": True,
        },
    )


def _reason_registry() -> SealedReasonRegistry:
    return SealedReasonRegistry.build((
        ReasonDefinition(
            REASON_ID, "call_effect", "semantic", "blocks_decision",
            frozenset({"relational_call"}), ("evidence",), frozenset({"call"}),
            False, "policy-1", RecoveryAddressability.REQUIREMENT_REQUIRED,
        ),
    ))


def _projection(result_id: str = "result-1", *, decision_effect: str = "blocks_decision"):
    active = (
        CActiveBaseRow(
            result_id, "occ-1", "cause-1", REASON_ID,
            "call_effect", decision_effect, "relational_call",
        ),
    )
    return VerifiedLifecycleProjection.seal(
        result_occurrence_id=result_id,
        snapshot_digest="snapshot",
        c_active_base=active,
        q_open_base=(QOpenBaseRow(result_id, "occ-1", "cause-1", "req-A", "call", "target"),),
        blocker_eligibility_base=(
            BlockerEligibilityBaseRow(result_id, "occ-1", "cause-1"),
        ),
        satisfaction_projection={"live": ("req-A",)},
    )


def _unconditional(result_id: str = "result-1", *, outcome: Outcome = Outcome.UNKNOWN):
    """Build a real unconditional DecisionReceipt with the requested outcome."""
    if outcome is Outcome.UNKNOWN:
        projection = _projection(result_id)
        return projection, finalize_decision(
            FinalizationAuthority(result_id, projection)
        )
    projection = VerifiedLifecycleProjection.seal(
        result_occurrence_id=result_id,
        snapshot_digest="snapshot",
        c_active_base=(),
        q_open_base=(),
        blocker_eligibility_base=(),
        satisfaction_projection={"live": ()},
    )
    proof = DecisiveProofReceipt.create(
        result_occurrence_id=result_id,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        proof_kind=DecisiveProofKind.EQ_CLOSURE,
        proof_artifact_digest="eq-proof",
    )
    return projection, finalize_decision(FinalizationAuthority(
        result_id, projection, decisive_proof_receipts=(proof,),
    ))


def _conditional_proof(projection, premises, *, kind=None, artifact="conditional-proof"):
    return ConditionalDecisiveProofReceipt.create(
        result_occurrence_id=projection.result_occurrence_id,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        proof_kind=kind or ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE,
        proof_artifact_digest=artifact,
        assumption_dependencies=premises,
    )


def _conditional_lane(*, decision_effect: str = "blocks_decision", premises=None, kind=None):
    """Run one conditional lane over an unconditional UNKNOWN pair."""
    _unconditional_projection, decision = _unconditional()
    conditional_projection = _projection("result-1", decision_effect=decision_effect)
    assumption_set = premises if premises is not None else (_premise(),)
    proof = _conditional_proof(conditional_projection, assumption_set, kind=kind)
    receipt = finalize_conditional_decision(ConditionalFinalizationAuthority(
        "result-1", decision, conditional_projection, assumption_set,
        conditional_decisive_proof_receipts=(proof,),
    ))
    return decision, conditional_projection, assumption_set, proof, receipt


def _codec() -> StrictV2JsonCodec:
    contract = SatisfactionContractDefinition(
        "conditional-call-recovery", 1,
        (RequirementSlotDefinition("A", frozenset(("call",))),),
        all_of(requirement_slot("A")),
    )
    return StrictV2JsonCodec(
        reason_registry=_reason_registry(),
        recovery_registry=SealedRecoveryRegistry.build((contract,)),
    )


# --- proof-owned premise contract ------------------------------------------


def test_premise_payload_is_canonical_regardless_of_input_container_and_order():
    from_mapping = AssumptionPremise(
        kind=AssumptionKind.EXTERNAL_CALLEE_SPEC,
        subject="log",
        payload={"returns_normally": True, "canonical_symbol": "log"},
    )
    from_pairs = AssumptionPremise(
        kind="EXTERNAL_CALLEE_SPEC",
        subject="log",
        payload=[["canonical_symbol", "log"], ["returns_normally", True]],
    )
    assert from_mapping == from_pairs
    assert from_mapping.payload == (
        ("canonical_symbol", "log"), ("returns_normally", True),
    )
    assert from_mapping.premise_key() == from_pairs.premise_key()
    assert from_mapping.payload_value("canonical_symbol") == "log"
    assert from_mapping.payload_value("absent", "fallback") == "fallback"
    assert from_mapping.schema_version == CONDITIONAL_ASSUMPTION_SCHEMA_VERSION


def test_premise_payload_is_deeply_immutable_by_construction():
    premise = _premise()
    assert_deep_immutable(premise)
    with pytest.raises(Exception):
        premise.subject = "exp"  # frozen dataclass
    nested = AssumptionPremise(
        kind=AssumptionKind.EXTERNAL_CALLEE_SPEC,
        subject="log",
        payload={"signature": [["ret", "double"], ["arg0", "double"]]},
    )
    assert nested.payload_value("signature") == (("ret", "double"), ("arg0", "double"))
    assert_deep_immutable(nested)


@pytest.mark.parametrize("payload", [
    {"live_object": object()},
    {"handle": {1: "not-a-str-key"}},
    {"mutable": bytearray(b"x")},
    {"non_finite": float("nan")},
])
def test_premise_rejects_payloads_that_are_not_reproducible(payload):
    with pytest.raises((TypeError, ValueError)):
        AssumptionPremise(
            kind=AssumptionKind.EXTERNAL_CALLEE_SPEC, subject="log", payload=payload,
        )


def test_premise_rejects_primitive_subclasses_instead_of_normalizing_them():
    class WideInt(int):
        pass

    with pytest.raises(TypeError, match="exact primitive"):
        AssumptionPremise(
            kind=AssumptionKind.EXTERNAL_CALLEE_SPEC,
            subject="log",
            payload={"width": WideInt(64)},
        )


def test_premise_rejects_unknown_kind_empty_subject_and_repeated_payload_name():
    with pytest.raises(ValueError):
        AssumptionPremise(kind="NO_SUCH_KIND", subject="log", payload={})
    with pytest.raises(TypeError):
        AssumptionPremise(kind=AssumptionKind.EXTERNAL_CALLEE_SPEC, subject="", payload={})
    with pytest.raises(ValueError, match="repeats a name"):
        AssumptionPremise(
            kind=AssumptionKind.EXTERNAL_CALLEE_SPEC,
            subject="log",
            payload=[["a", 1], ["a", 2]],
        )
    with pytest.raises(ValueError, match="schema version"):
        AssumptionPremise(
            kind=AssumptionKind.EXTERNAL_CALLEE_SPEC, subject="log",
            payload={}, schema_version=CONDITIONAL_ASSUMPTION_SCHEMA_VERSION + 1,
        )


def test_normalize_assumption_premises_drops_repeats_only():
    log, exp = _premise("log"), _premise("exp")
    assert normalize_assumption_premises((log, exp, log)) == (log, exp)
    with pytest.raises(TypeError):
        normalize_assumption_premises(("log",))


def test_the_premise_contract_does_not_import_the_authority_layer():
    """The dependency runs authority -> proof; test_import_layers pins the rest."""
    import ast

    from scripts.function_tracer_pcode.proof import assumptions

    tree = ast.parse(open(assumptions.__file__, encoding="utf-8").read())
    imported = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imported.add(node.module)
    assert not [name for name in imported if "authority" in name]


# --- conditional receipts ---------------------------------------------------


def test_conditional_proof_receipt_requires_non_empty_assumption_dependencies():
    _projection_unconditional, _decision = _unconditional()
    conditional_projection = _projection()
    with pytest.raises(ValueError, match="requires assumption dependencies"):
        _conditional_proof(conditional_projection, ())
    with pytest.raises(TypeError, match="AssumptionPremise only"):
        _conditional_proof(conditional_projection, ("log",))


def test_conditional_dependency_digest_is_order_independent_and_deduplicated():
    log, exp = _premise("log"), _premise("exp")
    assert canonical_assumption_dependencies((log, exp)) == canonical_assumption_dependencies(
        (exp, log, log)
    )
    assert assumption_dependencies_digest((log, exp)) == assumption_dependencies_digest(
        (exp, log)
    )
    assert assumption_dependencies_digest((log,)) != assumption_dependencies_digest((exp,))
    conditional_projection = _projection()
    forward = _conditional_proof(conditional_projection, (log, exp))
    backward = _conditional_proof(conditional_projection, (exp, log))
    assert forward == backward
    assert forward.receipt_digest == backward.receipt_digest
    forward.validate()


def test_conditional_decision_is_decisive_only_with_its_whole_assumption_set():
    _decision, _projection_c, assumption_set, _proof, receipt = _conditional_lane(
        decision_effect="blocks_disequivalence",
    )
    assert receipt.conditional_outcome is Outcome.EQUIVALENT
    assert receipt.unconditional_outcome is Outcome.UNKNOWN
    assert receipt.assumption_set_digest == authority_digest(assumption_set)
    assert receipt.is_decisive()
    receipt.validate()


def test_conditional_receipt_that_drops_a_premise_is_malformed():
    """#20 does not minimize dependencies: a smaller set is not a valid proof."""
    _unconditional_projection, decision = _unconditional()
    conditional_projection = _projection(decision_effect="blocks_disequivalence")
    assumption_set = (_premise("log"), _premise("exp"))
    minimized = _conditional_proof(conditional_projection, (assumption_set[0],))
    receipt = finalize_conditional_decision(ConditionalFinalizationAuthority(
        "result-1", decision, conditional_projection, assumption_set,
        conditional_decisive_proof_receipts=(minimized,),
    ))
    assert receipt.conditional_outcome is Outcome.ERROR


def test_conditional_lane_requires_a_non_empty_assumption_set():
    _unconditional_projection, decision = _unconditional()
    with pytest.raises(ValueError, match="non-empty assumption set"):
        ConditionalFinalizationAuthority(
            "result-1", decision, _projection(), (),
        )


def test_conditional_lane_after_a_decided_pair_claims_nothing():
    _decided_projection, decided = _unconditional(outcome=Outcome.EQUIVALENT)
    conditional_projection = _projection(decision_effect="blocks_disequivalence")
    assumption_set = (_premise(),)
    proof = _conditional_proof(conditional_projection, assumption_set)
    receipt = finalize_conditional_decision(ConditionalFinalizationAuthority(
        "result-1", decided, conditional_projection, assumption_set,
        conditional_decisive_proof_receipts=(proof,),
    ))
    assert decided.outcome is Outcome.EQUIVALENT
    assert receipt.conditional_outcome is Outcome.ERROR
    assert receipt.unconditional_outcome is Outcome.EQUIVALENT
    assert not receipt.is_decisive()


def test_conditional_blockers_and_conflicting_proofs_stay_undecided():
    _d, _p, _a, _r, blocked = _conditional_lane(decision_effect="blocks_equivalence")
    assert blocked.conditional_outcome is Outcome.UNKNOWN

    _unconditional_projection, decision = _unconditional()
    conditional_projection = _projection(decision_effect="blocks_disequivalence")
    assumption_set = (_premise(),)
    both = (
        _conditional_proof(conditional_projection, assumption_set),
        _conditional_proof(
            conditional_projection, assumption_set,
            kind=ConditionalDecisiveProofKind.CONDITIONAL_SAFE_COUNTEREXAMPLE,
            artifact="counterexample",
        ),
    )
    conflict = finalize_conditional_decision(ConditionalFinalizationAuthority(
        "result-1", decision, conditional_projection, assumption_set,
        conditional_decisive_proof_receipts=both,
    ))
    assert conflict.conditional_outcome is Outcome.ERROR


def test_conditional_lane_without_a_decisive_proof_is_unknown():
    _unconditional_projection, decision = _unconditional()
    conditional_projection = _projection()
    receipt = finalize_conditional_decision(ConditionalFinalizationAuthority(
        "result-1", decision, conditional_projection, (_premise(),),
    ))
    assert receipt.conditional_outcome is Outcome.UNKNOWN
    assert not receipt.is_decisive()


def test_conditional_decision_receipts_are_issued_only_by_the_finalizer():
    _d, _p, _a, _proof, receipt = _conditional_lane()
    with pytest.raises(ValueError, match="issued only by"):
        ConditionalDecisionReceipt(*[getattr(receipt, name) for name in (
            "result_occurrence_id", "conditional_outcome", "unconditional_outcome",
            "unconditional_receipt_digest", "lifecycle_projection_digest",
            "assumption_set_digest", "authority_input_digest", "receipt_digest",
        )])


# --- conditional must not become unconditional ------------------------------


def test_unconditional_finalizer_rejects_conditional_receipts_by_type():
    _unconditional_projection, _decision = _unconditional()
    conditional_projection = _projection()
    proof = _conditional_proof(conditional_projection, (_premise(),))
    with pytest.raises(TypeError, match="DecisiveProofReceipt only"):
        FinalizationAuthority(
            "result-1", conditional_projection, decisive_proof_receipts=(proof,),
        )
    with pytest.raises(TypeError, match="TerminalTimeoutReceipt only"):
        FinalizationAuthority(
            "result-1", conditional_projection, terminal_timeout_receipts=(proof,),
        )
    with pytest.raises(TypeError, match="ErrorReceipt only"):
        FinalizationAuthority(
            "result-1", conditional_projection, error_receipts=(proof,),
        )


def test_conditional_receipt_cannot_stand_in_for_the_unconditional_decision():
    _d, _p, _a, _proof, receipt = _conditional_lane()
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        decision_receipt_payload,
    )

    with pytest.raises(TypeError, match="exact DecisionReceipt"):
        decision_receipt_payload(receipt)
    assert type(receipt) is not DecisionReceipt


def test_conditional_column_never_moves_the_outcome_or_the_exit_code():
    class _Result:
        decision_receipt = None
        final_outcome = None
        is_equivalent = None
        conditional_decision_receipt = None
        conditional_outcome = None

    result = _Result()
    _unconditional_projection, decision = _unconditional()
    attach_canonical_decision(result, decision)
    before = (result.final_outcome, result.is_equivalent, outcome_from_result(result))

    _d, _p, _a, _proof, conditional = _conditional_lane(
        decision_effect="blocks_disequivalence",
    )
    attach_conditional_decision(result, conditional)

    assert conditional.conditional_outcome is Outcome.EQUIVALENT
    assert (result.final_outcome, result.is_equivalent, outcome_from_result(result)) == before
    assert outcome_from_result(result) is Outcome.UNKNOWN
    assert CLI_EXIT_CODE_BY_OUTCOME[outcome_from_result(result)] == 2
    assert result.conditional_outcome == "EQUIVALENT"


def test_conditional_column_refuses_a_pair_that_is_already_decided():
    class _Result:
        decision_receipt = None
        final_outcome = None
        is_equivalent = None
        conditional_decision_receipt = None
        conditional_outcome = None

    result = _Result()
    _decided_projection, decided = _unconditional(outcome=Outcome.EQUIVALENT)
    attach_canonical_decision(result, decided)
    _d, _p, _a, _proof, conditional = _conditional_lane()
    with pytest.raises(ValueError, match="only after an unconditional UNKNOWN"):
        attach_conditional_decision(result, conditional)
    assert result.conditional_outcome is None


def test_conditional_column_refuses_a_receipt_from_another_decision():
    class _Result:
        decision_receipt = None
        final_outcome = None
        is_equivalent = None
        conditional_decision_receipt = None
        conditional_outcome = None

    result = _Result()
    _projection_a, decision = _unconditional("result-1")
    attach_canonical_decision(result, decision)
    other_projection = _projection("result-2")
    _other_unconditional_projection, other_decision = _unconditional("result-2")
    other = finalize_conditional_decision(ConditionalFinalizationAuthority(
        "result-2", other_decision, other_projection, (_premise(),),
    ))
    with pytest.raises(ValueError, match="different DecisionReceipt"):
        attach_conditional_decision(result, other)


# --- serialization ----------------------------------------------------------


def test_strict_codec_round_trips_premises_and_both_conditional_receipts():
    codec = _codec()
    premise = _premise()
    _d, _p, _assumption_set, proof, receipt = _conditional_lane()
    for value in (premise, proof, receipt):
        encoded = codec.dumps(value)
        assert json.loads(encoded)["object_type"] == type(value).__name__
        decoded = codec.loads(encoded)
        assert decoded == value
        assert codec.dumps(decoded) == encoded


def test_serialized_premise_payload_keeps_its_canonical_leaves():
    codec = _codec()
    premise = _premise()
    payload = json.loads(codec.dumps(premise))["payload"]
    assert payload["kind"] == "EXTERNAL_CALLEE_SPEC"
    assert payload["payload"] == [
        ["canonical_symbol", "log"],
        ["no_observable_memory_write", True],
        ["returns_normally", True],
        ["signature", ["double", "double"]],
    ]
    assert codec.loads(codec.dumps(premise)).payload_value("signature") == ("double", "double")


def test_strict_codec_rejects_a_tampered_conditional_receipt():
    codec = _codec()
    _d, _p, _a, proof, receipt = _conditional_lane()
    for value, mutation in (
        (proof, lambda body: body["assumption_dependencies"].pop()),
        (proof, lambda body: body.__setitem__("proof_artifact_digest", "other")),
        (receipt, lambda body: body.__setitem__("conditional_outcome", "EQUIVALENT")),
        (receipt, lambda body: body.__setitem__("unconditional_outcome", "EQUIVALENT")),
    ):
        envelope = json.loads(codec.dumps(value))
        mutation(envelope["payload"])
        envelope["payload_digest"] = authority_digest(envelope["payload"])
        with pytest.raises((ValueError, TypeError)):
            codec.loads(json.dumps(envelope))


def test_result_payload_reports_the_conditional_column_separately():
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult

    result = EquivalenceResult(
        is_equivalent=None, function1_name="f", function2_name="f",
        binary1_name="a", binary2_name="b", solver_results=None,
    )
    _unconditional_projection, decision = _unconditional()
    attach_canonical_decision(result, decision)
    payload = result.to_dict()
    assert payload["final_outcome"] == "UNKNOWN"
    assert payload["conditional_outcome"] is None
    assert payload["conditional_decision_receipt"] is None
    assert conditional_outcome_from_payload(payload) is None
    assert outcome_from_payload(payload) is Outcome.UNKNOWN

    _d, _p, _a, _proof, conditional = _conditional_lane(
        decision_effect="blocks_disequivalence",
    )
    attach_conditional_decision(result, conditional)
    payload = result.to_dict()
    assert payload["final_outcome"] == "UNKNOWN"
    assert payload["is_equivalent"] is None
    assert payload["conditional_outcome"] == "EQUIVALENT"
    assert payload["conditional_decision_receipt"] == conditional_decision_receipt_payload(
        conditional
    )
    assert conditional_outcome_from_payload(payload) is Outcome.EQUIVALENT
    # The unconditional reader is untouched by the conditional column.
    assert outcome_from_payload(payload) is Outcome.UNKNOWN


def test_serialized_conditional_column_is_validated_against_its_receipt():
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult

    result = EquivalenceResult(
        is_equivalent=None, function1_name="f", function2_name="f",
        binary1_name="a", binary2_name="b", solver_results=None,
    )
    _unconditional_projection, decision = _unconditional()
    attach_canonical_decision(result, decision)
    _d, _p, _a, _proof, conditional = _conditional_lane(
        decision_effect="blocks_disequivalence",
    )
    attach_conditional_decision(result, conditional)
    payload = dict(result.to_dict())

    payload["conditional_outcome"] = "NOT_EQ"
    with pytest.raises(ValueError, match="contradicts its receipt"):
        conditional_outcome_from_payload(payload)

    payload = dict(result.to_dict())
    payload["conditional_decision_receipt"] = None
    with pytest.raises(ValueError, match="without its conditional receipt"):
        conditional_outcome_from_payload(payload)

    payload = dict(result.to_dict())
    receipt_payload = dict(payload["conditional_decision_receipt"])
    receipt_payload["conditional_outcome"] = "NOT_EQ"
    payload["conditional_decision_receipt"] = receipt_payload
    payload["conditional_outcome"] = "NOT_EQ"
    with pytest.raises(ValueError, match="digest is invalid"):
        conditional_outcome_from_payload(payload)


def test_result_refuses_a_conditional_outcome_without_its_receipt():
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult

    result = EquivalenceResult(
        is_equivalent=None, function1_name="f", function2_name="f",
        binary1_name="a", binary2_name="b", solver_results=None,
    )
    _unconditional_projection, decision = _unconditional()
    attach_canonical_decision(result, decision)
    result.conditional_outcome = "EQUIVALENT"
    with pytest.raises(ValueError, match="without its ConditionalDecisionReceipt"):
        result.to_dict()


def test_conditional_and_unconditional_receipts_stay_distinct_documents():
    codec = _codec()
    _unconditional_projection, decision = _unconditional()
    _d, _p, _a, _proof, conditional = _conditional_lane()
    assert decision.receipt_digest != conditional.receipt_digest
    assert conditional.unconditional_receipt_digest == decision.receipt_digest
    assert codec.dumps(decision) != codec.dumps(conditional)
