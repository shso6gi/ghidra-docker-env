# -*- coding: utf-8 -*-
"""Conditional lane activation + receipt issuance + sqrt cutover (Issue #20 PR-20-B3).

ここで固定するのは

* lane は **無条件 UNKNOWN のあとだけ**起動すること
* proof artifact → ``ConditionalDecisiveProofReceipt`` →
  ``ConditionalDecisionReceipt`` の authority flow と、その bind 先
* assumption dependency を **最小化しない**こと
* UF を含む SAT を根拠に NOT_EQ を出さないこと
* 旧 sqrt/sqrtf 無条件 pure-return path が消え、catalog + 明示仮定の経路だけが
  残ること

である。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.analysis.effects.external_call_models import (
    ExternalCallEffectPolicy,
)
from scripts.function_tracer_pcode.authority.contracts import (
    BlockerEligibilityBaseRow,
    CActiveBaseRow,
    Outcome,
    QOpenBaseRow,
    VerifiedLifecycleProjection,
)
from scripts.function_tracer_pcode.authority.decision.conditional import (
    ConditionalDecisionReceipt,
    ConditionalDecisiveProofKind,
    ConditionalDecisiveProofReceipt,
    ConditionalFinalizationAuthority,
    finalize_conditional_decision,
)
from scripts.function_tracer_pcode.authority.decision.conditional_lane import (
    ASSUMPTION_DISCHARGED_REASON_IDS,
    conditional_lane_is_eligible,
    conditional_lane_projection,
    issue_conditional_decision,
    run_production_conditional_lane,
)
from scripts.function_tracer_pcode.authority.decision.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    FinalizationAuthority,
    finalize_decision,
)
from scripts.function_tracer_pcode.core.analysis import (
    DeferredCallInfo,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.runtime_refs import (
    CallModelCandidateRef,
    DeferredCallRef,
)
from scripts.function_tracer_pcode.proof import conditional_lane as lane_module
from scripts.function_tracer_pcode.proof.conditional_lane import (
    CONDITIONAL_EQ_CLOSURE,
    CONDITIONAL_SAFE_COUNTEREXAMPLE,
    COUNTEREXAMPLE_REPLAY_MISSING,
    COUNTEREXAMPLE_UF_INTERPRETATION_DEPENDENT,
    ConditionalProofArtifact,
    conditional_counterexample_safety_reasons,
    run_conditional_proof,
)


NO_OBSERVATION = ExternalCallEffectPolicy()
CALL_REASON_ID = "pure_call_semantics_unproven"
OTHER_REASON_ID = "outcome_path_region_completeness_unproven"
RESULT_ID = "result-b3"


# --- analysis fixtures (B2 と同じ形。catalog candidate 付き deferred call) ----


def _candidate(symbol="log", *, argument_widths=(64,), return_width=64):
    return CallModelCandidateRef(
        provider="c99_math_catalog_v1",
        canonical_symbol=symbol,
        signature_key=(
            "c99_math_signature_v1",
            symbol,
            tuple(("float", width) for width in argument_widths),
            ("float", return_width),
        ),
        provenance_key=(
            "external_import_provenance_v1",
            "thunk_to_external",
            "<EXTERNAL>",
            (symbol,),
        ),
    )


def _param(name="x", index=0, size=8):
    return Expression.parameter(name, index=index, data_type="double", size=size)


def _analysis(*, symbol="log", binary_id="binary1", entry=0x1000, recovery_status="complete"):
    candidate = _candidate(symbol)
    target_ref = CallTargetRef.from_name(symbol, program_id=entry, entry_offset=entry + 1)
    info = DeferredCallInfo(
        placeholder_name="call#1",
        target_ref=target_ref,
        arguments=[_param()],
        deferred_call_ref=DeferredCallRef(
            caller_program_id=entry,
            caller_entry_offset=entry,
            target_ref=target_ref,
            sequence=1,
        ),
        call_argument_recovery_status=recovery_status,
        call_model_candidate=candidate,
    )
    value = Expression.unknown(info.placeholder_name, runtime_ref=info.unknown_ref).clone_with(size=8)
    return FunctionReturnAnalysis(
        function_name="snippet",
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name("snippet", program_id=entry, entry_offset=entry),
        binary_id=binary_id,
        parameters=[{"name": "x", "index": 0, "size": 8, "data_type": "double", "is_signed": True}],
        returns=[ReturnInfo(address=hex(entry), value=value, conditions=[])],
        return_type="double",
        deferred_calls={info.deferred_call_ref.stable_key(): info},
    )


class _Solver:
    """`ParallelSolverRunner` と同じ形の最小 stub。"""

    def __init__(self, disposition):
        self.disposition = disposition
        self.formulas = []

    def run_parallel(self, formula, timeout=None):
        self.formulas.append(formula)
        return type("_R", (), {"is_equivalent": self.disposition})()


# --- authority fixtures -----------------------------------------------------


def _projection(*, reason_ids=(CALL_REASON_ID,), result_id=RESULT_ID, decision_effect="blocks_decision"):
    causes = tuple(
        CActiveBaseRow(
            result_id, f"occ-{index}", f"cause-{index}", reason_id,
            "expression_call_effect_memory", decision_effect, "call_semantic_obligation",
        )
        for index, reason_id in enumerate(reason_ids)
    )
    return VerifiedLifecycleProjection.seal(
        result_occurrence_id=result_id,
        snapshot_digest="snapshot",
        c_active_base=causes,
        q_open_base=tuple(
            QOpenBaseRow(result_id, row.occurrence_id, row.cause_id, f"req-{index}", "call", "target")
            for index, row in enumerate(causes)
        ),
        blocker_eligibility_base=tuple(
            BlockerEligibilityBaseRow(result_id, row.occurrence_id, row.cause_id)
            for row in causes
        ),
        satisfaction_projection={"live": tuple(f"req-{index}" for index in range(len(causes)))},
    )


def _decision(outcome=Outcome.UNKNOWN, *, projection=None):
    projection = projection if projection is not None else _projection()
    if outcome is Outcome.UNKNOWN:
        return finalize_decision(FinalizationAuthority(RESULT_ID, projection))
    clear = VerifiedLifecycleProjection.seal(
        result_occurrence_id=RESULT_ID,
        snapshot_digest="snapshot",
        c_active_base=(),
        q_open_base=(),
        blocker_eligibility_base=(),
        satisfaction_projection={"live": ()},
    )
    if outcome is Outcome.EQUIVALENT:
        proof = DecisiveProofReceipt.create(
            result_occurrence_id=RESULT_ID,
            lifecycle_projection_digest=clear.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.EQ_CLOSURE,
            proof_artifact_digest="eq-proof",
        )
        return finalize_decision(FinalizationAuthority(
            RESULT_ID, clear, decisive_proof_receipts=(proof,)
        ))
    if outcome is Outcome.NOT_EQ:
        proof = DecisiveProofReceipt.create(
            result_occurrence_id=RESULT_ID,
            lifecycle_projection_digest=clear.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.SAFE_COUNTEREXAMPLE,
            proof_artifact_digest="neq-proof",
        )
        return finalize_decision(FinalizationAuthority(
            RESULT_ID, clear, decisive_proof_receipts=(proof,)
        ))
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        issue_infrastructure_error_decision,
    )
    if outcome is Outcome.ERROR:
        return issue_infrastructure_error_decision(
            result_occurrence_id=RESULT_ID,
            error_kind="test_error",
            error_artifact_digest="error-artifact",
        )
    raise AssertionError(f"unsupported fixture outcome: {outcome}")


class _Result:
    """production_cutover が読む最小の result 面。"""

    def __init__(self, decision):
        self.decision_receipt = decision
        self.final_outcome = decision.outcome.value
        self.is_equivalent = {
            Outcome.EQUIVALENT: True, Outcome.NOT_EQ: False,
        }.get(decision.outcome, None)
        self.conditional_decision_receipt = None
        self.conditional_outcome = None


def _run_lane(result, projection, analyses, *, disposition=True, policy=NO_OBSERVATION):
    return run_production_conditional_lane(
        result,
        projection=projection,
        analyses=analyses,
        observation_policy=policy,
        solver_runner=_Solver(disposition),
    )


def _both_analyses():
    return _analysis(binary_id="binary1"), _analysis(binary_id="binary2", entry=0x2000)


# --- lane activation --------------------------------------------------------


def test_lane_runs_after_an_unconditional_unknown_with_eligible_views():
    projection = _projection()
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection))
    diagnostics = _run_lane(result, projection, _both_analyses())

    assert diagnostics is not None and diagnostics["conditional_lane"] == "issued"
    assert type(result.conditional_decision_receipt) is ConditionalDecisionReceipt
    assert result.conditional_outcome is not None


@pytest.mark.parametrize(
    "outcome", [Outcome.EQUIVALENT, Outcome.NOT_EQ, Outcome.ERROR]
)
def test_lane_never_runs_after_a_decided_pair(outcome):
    projection = _projection()
    result = _Result(_decision(outcome))
    assert conditional_lane_is_eligible(result.decision_receipt) is False
    assert _run_lane(result, projection, _both_analyses()) is None
    assert result.conditional_decision_receipt is None
    assert result.conditional_outcome is None


def test_lane_never_runs_after_a_timeout():
    """TIMEOUT は supervisor 由来 receipt なので eligibility 面だけを固定する。

    ``conditional_lane_is_eligible`` は exact ``DecisionReceipt`` 以外を受け付け
    ないので、outcome を騙った偽物でも起動しない。
    """
    fake = type("_D", (), {"outcome": Outcome.TIMEOUT})()
    assert conditional_lane_is_eligible(fake) is False
    projection = _projection()
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection))
    result.decision_receipt = fake
    assert _run_lane(result, projection, _both_analyses()) is None
    assert result.conditional_decision_receipt is None


def test_unknown_without_a_constructible_view_issues_no_conditional_receipt():
    projection = _projection()
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection))
    # 引数証拠が未証明なら view は立たない。
    analyses = (
        _analysis(binary_id="binary1", recovery_status="partial"),
        _analysis(binary_id="binary2", entry=0x2000, recovery_status="partial"),
    )
    diagnostics = _run_lane(result, projection, analyses)

    assert diagnostics["conditional_lane"] == "not_constructed"
    assert result.conditional_decision_receipt is None
    assert result.conditional_outcome is None


def test_lane_does_not_run_without_bound_analyses():
    projection = _projection()
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection))
    assert _run_lane(result, projection, None) is None
    assert result.conditional_decision_receipt is None


# --- authority flow ---------------------------------------------------------


def test_proof_artifact_becomes_a_conditional_decisive_receipt_and_decision():
    projection = _projection()
    decision = _decision(Outcome.UNKNOWN, projection=projection)
    artifact = run_conditional_proof(
        *_both_analyses(),
        observation_policy=NO_OBSERVATION,
        solver_runner=_Solver(True),
    )
    assert artifact.proof_kind == CONDITIONAL_EQ_CLOSURE

    receipt = issue_conditional_decision(
        unconditional_decision=decision, projection=projection, artifact=artifact
    )
    assert type(receipt) is ConditionalDecisionReceipt
    receipt.validate()
    assert receipt.result_occurrence_id == RESULT_ID
    assert receipt.unconditional_outcome is Outcome.UNKNOWN
    assert receipt.unconditional_receipt_digest == decision.receipt_digest
    assert receipt.conditional_outcome is Outcome.EQUIVALENT


def test_conditional_decision_binds_to_its_own_pair_and_receipt():
    from scripts.function_tracer_pcode.authority.decision.conditional import (
        validate_conditional_decision_join,
    )

    projection = _projection()
    decision = _decision(Outcome.UNKNOWN, projection=projection)
    artifact = run_conditional_proof(
        *_both_analyses(), observation_policy=NO_OBSERVATION, solver_runner=_Solver(True)
    )
    receipt = issue_conditional_decision(
        unconditional_decision=decision, projection=projection, artifact=artifact
    )
    validate_conditional_decision_join(
        receipt,
        result_occurrence_id=RESULT_ID,
        unconditional_outcome=Outcome.UNKNOWN,
        unconditional_receipt_digest=decision.receipt_digest,
    )
    with pytest.raises(ValueError):
        validate_conditional_decision_join(
            receipt,
            result_occurrence_id="another-pair",
            unconditional_outcome=Outcome.UNKNOWN,
            unconditional_receipt_digest=decision.receipt_digest,
        )
    with pytest.raises(ValueError):
        validate_conditional_decision_join(
            receipt,
            result_occurrence_id=RESULT_ID,
            unconditional_outcome=Outcome.UNKNOWN,
            unconditional_receipt_digest="another-decision",
        )


def test_a_conditional_receipt_is_rejected_by_the_unconditional_finalizer():
    projection = _projection()
    conditional = ConditionalDecisiveProofReceipt.create(
        result_occurrence_id=RESULT_ID,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        proof_kind=ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE,
        proof_artifact_digest="conditional-proof",
        assumption_dependencies=(_premise(),),
    )
    with pytest.raises(TypeError):
        FinalizationAuthority(
            RESULT_ID, projection, decisive_proof_receipts=(conditional,)
        )


def test_conditional_result_never_moves_the_unconditional_outcome_or_exit_code():
    from scripts.function_tracer_pcode.authority.contracts import CLI_EXIT_CODE_BY_OUTCOME
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        outcome_from_result,
    )

    projection = _projection()
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection))
    before = (result.is_equivalent, result.final_outcome, result.decision_receipt)
    _run_lane(result, projection, _both_analyses())

    assert (result.is_equivalent, result.final_outcome, result.decision_receipt) == before
    assert outcome_from_result(result) is Outcome.UNKNOWN
    assert CLI_EXIT_CODE_BY_OUTCOME[outcome_from_result(result)] == (
        CLI_EXIT_CODE_BY_OUTCOME[Outcome.UNKNOWN]
    )


def _premise(symbol="log"):
    from scripts.function_tracer_pcode.proof.conditional_view import (
        external_callee_spec_premise,
    )

    return external_callee_spec_premise(
        _candidate(symbol), argument_widths=(64,), return_width_bits=64
    )


# --- assumption dependencies ------------------------------------------------


def test_receipt_dependencies_are_the_whole_assumption_set():
    projection = _projection()
    decision = _decision(Outcome.UNKNOWN, projection=projection)
    left = _analysis(symbol="log", binary_id="binary1")
    right = _analysis(symbol="exp", binary_id="binary2", entry=0x2000)
    artifact = run_conditional_proof(
        left, right, observation_policy=NO_OBSERVATION, solver_runner=_Solver(True)
    )
    assert len(artifact.assumption_set) == 2

    lane_projection = conditional_lane_projection(
        projection, discharged_reason_ids=ASSUMPTION_DISCHARGED_REASON_IDS
    )
    proof_receipt = ConditionalDecisiveProofReceipt.create(
        result_occurrence_id=RESULT_ID,
        lifecycle_projection_digest=lane_projection.lifecycle_projection_digest,
        proof_kind=ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE,
        proof_artifact_digest=artifact.artifact_digest,
        assumption_dependencies=artifact.assumption_set,
    )
    assert len(proof_receipt.assumption_dependencies) == 2
    receipt = issue_conditional_decision(
        unconditional_decision=decision, projection=projection, artifact=artifact
    )
    assert len(receipt.assumption_set) == 2
    assert {premise.subject for premise in receipt.assumption_set} == {
        premise.subject for premise in artifact.assumption_set
    }


def test_identical_premises_are_deduplicated_but_nothing_else_is_dropped():
    left = _analysis(symbol="log", binary_id="binary1")
    right = _analysis(symbol="log", binary_id="binary2", entry=0x2000)
    artifact = run_conditional_proof(
        left, right, observation_policy=NO_OBSERVATION, solver_runner=_Solver(True)
    )
    # 左右が同じ callee を仮定しているので premise は 1 つに畳まれる。
    assert len(artifact.assumption_set) == 1


def test_dependencies_survive_when_the_uf_does_not_appear_in_the_final_formula():
    """simplification で UF が消えても premise は落とさない。"""
    projection = _projection()
    decision = _decision(Outcome.UNKNOWN, projection=projection)
    artifact = run_conditional_proof(
        *_both_analyses(), observation_policy=NO_OBSERVATION, solver_runner=_Solver(True)
    )
    stripped = ConditionalProofArtifact(
        proof_kind=artifact.proof_kind,
        assumption_set=artifact.assumption_set,
        artifact_digest=artifact.artifact_digest,
        modelled_call_count=artifact.modelled_call_count,
        all_calls_modelled=True,
        unsupported_calls_all_modelled=artifact.unsupported_calls_all_modelled,
    )
    receipt = issue_conditional_decision(
        unconditional_decision=decision, projection=projection, artifact=stripped
    )
    assert len(receipt.assumption_set) == len(artifact.assumption_set)


def test_a_receipt_that_depends_on_less_than_the_lane_assumption_set_is_malformed():
    projection = _projection()
    decision = _decision(Outcome.UNKNOWN, projection=projection)
    full = (_premise("log"), _premise("exp"))
    partial_receipt = ConditionalDecisiveProofReceipt.create(
        result_occurrence_id=RESULT_ID,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        proof_kind=ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE,
        proof_artifact_digest="conditional-proof",
        assumption_dependencies=(full[0],),
    )
    authority = ConditionalFinalizationAuthority(
        RESULT_ID, decision, projection, full,
        conditional_decisive_proof_receipts=(partial_receipt,),
    )
    assert finalize_conditional_decision(authority).conditional_outcome is Outcome.ERROR


def test_a_lane_without_an_assumption_set_is_refused():
    projection = _projection()
    decision = _decision(Outcome.UNKNOWN, projection=projection)
    empty = ConditionalProofArtifact(
        proof_kind=None, assumption_set=(), artifact_digest="x"
    )
    with pytest.raises(ValueError):
        issue_conditional_decision(
            unconditional_decision=decision, projection=projection, artifact=empty
        )


# --- discharge rule ---------------------------------------------------------


def test_only_assumption_owned_reasons_leave_the_conditional_projection():
    projection = _projection(reason_ids=(CALL_REASON_ID, OTHER_REASON_ID))
    lane = conditional_lane_projection(
        projection, discharged_reason_ids=ASSUMPTION_DISCHARGED_REASON_IDS
    )
    assert {row.reason_id for row in lane.c_active_base} == {OTHER_REASON_ID}
    # 落とした cause にぶら下がる open requirement も一緒に落ちる。
    assert len(lane.q_open_base) == 1
    lane.validate()
    assert OTHER_REASON_ID not in ASSUMPTION_DISCHARGED_REASON_IDS


def test_a_call_only_blocker_set_lets_the_conditional_column_reach_equivalent():
    """discharge 対象だけが残っていれば conditional 列は EQUIVALENT になる。

    次の test の対照。これが無いと「常に UNKNOWN」でも通ってしまう。
    """
    projection = _projection(
        reason_ids=(CALL_REASON_ID,), decision_effect="blocks_equivalence"
    )
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection))
    diagnostics = _run_lane(result, projection, _both_analyses())

    assert diagnostics["proof_kind"] == CONDITIONAL_EQ_CLOSURE
    assert result.conditional_outcome == Outcome.EQUIVALENT.value


def test_a_residual_non_call_blocker_keeps_the_conditional_column_unknown():
    projection = _projection(
        reason_ids=(CALL_REASON_ID, OTHER_REASON_ID), decision_effect="blocks_equivalence"
    )
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection))
    diagnostics = _run_lane(result, projection, _both_analyses())

    # EQ closure 自体は立つが、仮定が引き受けない blocker が残るので列は UNKNOWN。
    assert diagnostics["proof_kind"] == CONDITIONAL_EQ_CLOSURE
    assert result.conditional_outcome == Outcome.UNKNOWN.value


def test_argument_and_abi_reasons_are_not_discharged_by_the_assumption():
    for reason_id in (
        "call_argument_extraction_incomplete",
        "abi_argument_relation_unproven",
        "return_width_provenance_unavailable",
        "outcome_path_region_completeness_unproven",
    ):
        assert reason_id not in ASSUMPTION_DISCHARGED_REASON_IDS


# --- SAT safety -------------------------------------------------------------


def test_a_uf_sat_is_never_a_decisive_conditional_counterexample():
    artifact = run_conditional_proof(
        *_both_analyses(), observation_policy=NO_OBSERVATION, solver_runner=_Solver(False)
    )
    assert artifact.proof_kind is None
    assert COUNTEREXAMPLE_UF_INTERPRETATION_DEPENDENT in artifact.non_decisive_reasons


def test_a_uf_sat_does_not_move_the_unconditional_outcome():
    projection = _projection()
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection))
    diagnostics = _run_lane(result, projection, _both_analyses(), disposition=False)

    assert result.final_outcome == Outcome.UNKNOWN.value
    assert result.is_equivalent is None
    # 何も証明できていないので conditional 列そのものを出さない。
    assert diagnostics["conditional_lane"] == "non_decisive"
    assert result.conditional_outcome is None
    assert result.conditional_decision_receipt is None


def test_counterexample_safety_keeps_the_existing_analysis_side_contract():
    left, right = _both_analyses()
    # 解析側の既存 safety reason（未解決の戻り値など）はそのまま前置きで現れる。
    left.analysis_notes.append("unresolved_return_value")
    reasons = conditional_counterexample_safety_reasons(
        left, right, formula_has_uninterpreted_call=False
    )
    # UF が無い formula でも既存 production の replay 要求は残る。
    assert COUNTEREXAMPLE_REPLAY_MISSING in reasons
    assert COUNTEREXAMPLE_UF_INTERPRETATION_DEPENDENT not in reasons

    # 解析側 contract が消えていないこと: 側を特定できない reason は返さない。
    for reason in reasons:
        assert reason.startswith(("function1:", "function2:")) or reason in (
            COUNTEREXAMPLE_REPLAY_MISSING,
            COUNTEREXAMPLE_UF_INTERPRETATION_DEPENDENT,
        )

    # side-specific fresh / unresolved を持つ側は、その理由が側つきで現れる。
    left.returns[0].value = Expression.unknown("fresh_value").clone_with(size=8)
    with_unresolved = conditional_counterexample_safety_reasons(
        left, right, formula_has_uninterpreted_call=False
    )
    assert [
        reason for reason in with_unresolved if reason.startswith("function1:")
    ] != []


def test_a_conditional_counterexample_is_issued_only_when_no_safety_reason_remains():
    """safety reason が空のときだけ decisive になる、という合成規則。"""
    left, right = _both_analyses()
    artifact = run_conditional_proof(
        left, right, observation_policy=NO_OBSERVATION, solver_runner=_Solver(False)
    )
    assert artifact.proof_kind is None

    calls = {}

    def _no_reasons(*args, **kwargs):
        calls["called"] = True
        return ()

    original = lane_module.conditional_counterexample_safety_reasons
    lane_module.conditional_counterexample_safety_reasons = _no_reasons
    try:
        cleared = run_conditional_proof(
            left, right, observation_policy=NO_OBSERVATION, solver_runner=_Solver(False)
        )
    finally:
        lane_module.conditional_counterexample_safety_reasons = original
    assert calls.get("called") is True
    assert cleared.proof_kind == CONDITIONAL_SAFE_COUNTEREXAMPLE


def test_the_solver_being_inconclusive_is_not_decisive():
    artifact = run_conditional_proof(
        *_both_analyses(), observation_policy=NO_OBSERVATION, solver_runner=_Solver(None)
    )
    assert artifact.proof_kind is None
    projection = _projection()
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection))
    diagnostics = _run_lane(result, projection, _both_analyses(), disposition=None)
    assert diagnostics["conditional_lane"] == "non_decisive"
    assert result.conditional_decision_receipt is None


# --- sqrt/sqrtf cutover -----------------------------------------------------


def test_the_old_unconditional_sqrt_pure_return_path_is_gone():
    from scripts.function_tracer_pcode.proof import deferred_call_abstraction
    from scripts.function_tracer_pcode.core import analysis as core_analysis

    assert not hasattr(deferred_call_abstraction, "_PURE_RETURN_CALLS")
    source = open(core_analysis.__file__, encoding="utf-8").read()
    assert "_target_ref_has_external_library_provenance" not in source


def test_sqrt_is_no_longer_classified_as_a_pure_return_effect():
    for symbol in ("sqrt", "sqrtf"):
        target_ref = CallTargetRef.from_name(
            symbol, is_external=True, library_name="libm"
        )
        info = DeferredCallInfo(placeholder_name=f"{symbol}#1", target_ref=target_ref, sequence=1)
        assert info.effect_class == "unknown_effect"


def test_sqrt_enters_the_catalog_and_assumption_path_instead():
    left = _analysis(symbol="sqrt", binary_id="binary1")
    right = _analysis(symbol="sqrt", binary_id="binary2", entry=0x2000)
    artifact = run_conditional_proof(
        left, right, observation_policy=NO_OBSERVATION, solver_runner=_Solver(True)
    )
    assert artifact.proof_kind == CONDITIONAL_EQ_CLOSURE
    assert [premise.subject for premise in artifact.assumption_set] == ["sqrt"]


@pytest.mark.parametrize(
    "policy",
    [
        ExternalCallEffectPolicy(observe_errno=True),
        ExternalCallEffectPolicy(observe_fenv=True),
    ],
)
def test_sqrt_fails_closed_instead_of_falling_back_to_the_old_path(policy):
    left = _analysis(symbol="sqrt", binary_id="binary1")
    right = _analysis(symbol="sqrt", binary_id="binary2", entry=0x2000)
    artifact = run_conditional_proof(
        left, right, observation_policy=policy, solver_runner=_Solver(True)
    )
    assert artifact.proof_kind is None
    assert artifact.assumption_set == ()


def test_an_unproven_sqrt_argument_recovery_fails_closed():
    left = _analysis(symbol="sqrt", binary_id="binary1", recovery_status="inconclusive")
    right = _analysis(symbol="sqrt", binary_id="binary2", entry=0x2000)
    artifact = run_conditional_proof(
        left, right, observation_policy=NO_OBSERVATION, solver_runner=_Solver(True)
    )
    assert artifact.proof_kind is None


# --- regression -------------------------------------------------------------


def test_the_lane_never_raises_out_of_production():
    projection = _projection()
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection))

    class _Exploding:
        def run_parallel(self, formula, timeout=None):
            raise RuntimeError("solver exploded")

    diagnostics = run_production_conditional_lane(
        result,
        projection=projection,
        analyses=_both_analyses(),
        observation_policy=NO_OBSERVATION,
        solver_runner=_Exploding(),
    )
    assert diagnostics["conditional_lane"] == "non_decisive"
    assert result.conditional_outcome is None
    assert result.final_outcome == Outcome.UNKNOWN.value


def test_lane_diagnostics_reach_the_serialized_result():
    """lane が回ったことを結果 JSON から観測できる（判定には効かない）。"""
    from scripts.function_tracer_pcode.checker.diagnostics import (
        result_diagnostics_payload,
    )

    result = type("_R", (), {})()
    result.diagnostics = {"conditional_lane": {"conditional_lane": "issued"}}
    payload = result_diagnostics_payload(result)
    assert payload["conditional_lane"] == {"conditional_lane": "issued"}
    # lane が回っていない結果では None のまま。
    empty = type("_R", (), {})()
    empty.diagnostics = {}
    assert result_diagnostics_payload(empty)["conditional_lane"] is None


def test_the_proof_layer_does_not_import_the_authority_layer():
    import ast

    tree = ast.parse(open(lane_module.__file__, encoding="utf-8").read())
    imported = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            imported.append(node.module)
        elif isinstance(node, ast.Import):
            imported.extend(alias.name for alias in node.names)
    assert not [name for name in imported if ".authority" in name], imported


def test_a_decisive_artifact_requires_every_call_to_be_modelled():
    with pytest.raises(ValueError):
        ConditionalProofArtifact(
            proof_kind=CONDITIONAL_EQ_CLOSURE,
            assumption_set=(_premise(),),
            artifact_digest="x",
            all_calls_modelled=False,
        )
