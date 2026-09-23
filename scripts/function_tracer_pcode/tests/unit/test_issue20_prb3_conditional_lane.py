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
    CALL_EFFECT_PREREQUISITE_TARGET_TAG,
    conditional_discharged_causes,
    conditional_lane_is_eligible,
    conditional_lane_projection,
    issue_conditional_decision,
    run_production_conditional_lane as _run_production_lane_with_factory,
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
    PcodeOpRef,
)
from scripts.function_tracer_pcode.proof import conditional_lane as lane_module
from scripts.function_tracer_pcode.proof.formula.input_correspondence import build_input_correspondence_set
from scripts.function_tracer_pcode.proof.conditional_lane import (
    CONDITIONAL_EQ_CLOSURE,
    CONDITIONAL_SAFE_COUNTEREXAMPLE,
    COUNTEREXAMPLE_REPLAY_MISSING,
    COUNTEREXAMPLE_UF_INTERPRETATION_DEPENDENT,
    ConditionalProofArtifact,
    conditional_counterexample_safety_reasons,
    run_conditional_proof as _run_conditional_proof_with_relation,
)


# Issue #167: lane の formula の parameter premise は base（raw）pair の最終
# relation だけから作る。test は raw の analysis から relation を明示的に作って渡す。
def run_conditional_proof(analysis1, analysis2, **kwargs):
    if "input_correspondence" not in kwargs and analysis1 is not None and analysis2 is not None:
        kwargs["input_correspondence"] = build_input_correspondence_set(analysis1, analysis2)
    kwargs.setdefault("input_correspondence", None)
    return _run_conditional_proof_with_relation(analysis1, analysis2, **kwargs)


def run_production_conditional_lane(result, *, analyses, **kwargs):
    if "input_correspondence_factory" not in kwargs and analyses is not None:
        kwargs["input_correspondence_factory"] = lambda: build_input_correspondence_set(*analyses)
    return _run_production_lane_with_factory(result, analyses=analyses, **kwargs)


NO_OBSERVATION = ExternalCallEffectPolicy()
CALL_REASON_ID = "pure_call_semantics_unproven"
CORRESPONDENCE_REASON_ID = "callsite_correspondence_unproven"
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


def _op_ref(binary_id, offset, entry=0x1000):
    return PcodeOpRef(
        address_offset=offset,
        seq_time=offset,
        seq_order=1,
        block_index=0,
        mnemonic="CALL",
        binary_id=binary_id,
        function_entry_space="ram",
        function_entry_offset=entry,
        target_space="ram",
        target_offset=offset,
        local_op_ordinal=1,
        program_uid=entry,
    )


def _analysis(
    *, symbol="log", binary_id="binary1", entry=0x1000, recovery_status="complete",
    op_offset=0x1100,
):
    candidate = _candidate(symbol)
    target_ref = CallTargetRef.from_name(symbol, program_id=entry, entry_offset=entry + 1)
    info = DeferredCallInfo(
        placeholder_name="call#1",
        target_ref=target_ref,
        arguments=[_param()],
        deferred_call_ref=DeferredCallRef(
            caller_program_id=entry,
            caller_entry_offset=entry,
            pcode_op_ref=_op_ref(binary_id, op_offset, entry=entry),
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


#: 1 本の cause occurrence を表すテスト用の記述。``left`` / ``right`` は
#: ``(fact_id, pcode_op_key)`` で、None 側は「その側に callsite が無い」。
def _cause(reason_id, *, index, left=None, right=None,
           target_kind="call_semantic_obligation", prerequisite=True):
    return {
        "reason_id": reason_id,
        "occurrence_id": f"occ-{index}",
        "cause_id": f"cause-{index}",
        "left": left,
        "right": right,
        "target_kind": target_kind,
        "prerequisite": prerequisite,
    }


def _projection(*, causes=None, reason_ids=(CALL_REASON_ID,), result_id=RESULT_ID,
                decision_effect="blocks_decision"):
    causes = causes if causes is not None else _default_causes(reason_ids)
    rows = tuple(
        CActiveBaseRow(
            result_id, spec["occurrence_id"], spec["cause_id"], spec["reason_id"],
            "expression_call_effect_memory", decision_effect, spec["target_kind"],
        )
        for spec in causes
    )
    return VerifiedLifecycleProjection.seal(
        result_occurrence_id=result_id,
        snapshot_digest="snapshot",
        c_active_base=rows,
        q_open_base=tuple(
            QOpenBaseRow(result_id, row.occurrence_id, row.cause_id, f"req-{index}", "call", "target")
            for index, row in enumerate(rows)
        ),
        blocker_eligibility_base=tuple(
            BlockerEligibilityBaseRow(result_id, row.occurrence_id, row.cause_id)
            for row in rows
        ),
        satisfaction_projection={
            "occurrences": tuple(
                {
                    "occurrence_id": row.occurrence_id,
                    "cause_id": row.cause_id,
                    "live_requirement_ids": (f"req-{index}",),
                    "active": True,
                }
                for index, row in enumerate(rows)
            ),
            "execution_event_digests": (),
        },
    )


def _prerequisite_target_key(spec):
    """`_prerequisite_authority` が作るのと同じ形の canonical target key。"""
    left = spec["left"][0] if spec["left"] else None
    right = spec["right"][0] if spec["right"] else None
    return (
        spec["target_kind"],
        CALL_EFFECT_PREREQUISITE_TARGET_TAG,
        "obligation-" + spec["cause_id"],
        "observation-contract",
        left,
        right,
        "structural-certificate",
    )


class _ReasonRecord:
    """production の `UnknownReasonRecord` のうち binding が読む面だけ。"""

    def __init__(self, spec):
        self.reason_id = spec["reason_id"]
        self.object_target_key = (
            _prerequisite_target_key(spec) if spec["prerequisite"] else
            ("function_outcome_seed_stage", "unary-target", spec["cause_id"])
        )
        self.typed_cause_key = {
            "occurrence_id": spec["occurrence_id"],
            "cause_id": spec["cause_id"],
            "reason_id": spec["reason_id"],
        }


def _manifest_for(causes):
    """cause 記述から call-effect shadow manifest の fact 面を作る。"""
    left_rows, right_rows = [], []
    for spec in causes:
        for endpoint, rows in ((spec["left"], left_rows), (spec["right"], right_rows)):
            if not endpoint:
                continue
            fact_id, pcode_op_key = endpoint
            if pcode_op_key is None:
                continue
            rows.append(
                {"fact_id": fact_id, "identity": {"pcode_op_key": list(pcode_op_key)}}
            )
    return {"left_facts": left_rows, "right_facts": right_rows}


def _satisfaction_occurrences(projection):
    """封じた projection の satisfaction 行（canonical な pair tuple）を読む。"""
    fields = dict(projection.satisfaction_projection)
    return {dict(row)["occurrence_id"] for row in fields["occurrences"]}


def _call_site_key(analysis):
    info = next(iter(analysis.deferred_calls.values()))
    return info.deferred_call_ref.pcode_op_ref.stable_key()


#: 既定 fixture が写像する callsite の object identity。
LEFT_SITE = _op_ref("binary1", 0x1100).stable_key()
RIGHT_SITE = _op_ref("binary2", 0x2100, entry=0x2000).stable_key()
#: 写像していない別 callsite の object identity（internal call を模す）。
UNRELATED_LEFT_SITE = _op_ref("binary1", 0x1900).stable_key()
UNRELATED_RIGHT_SITE = _op_ref("binary2", 0x2900, entry=0x2000).stable_key()


def _default_causes(reason_ids=(CALL_REASON_ID,)):
    """写像した callsite に bind された既定の cause 記述。"""
    return [
        _cause(
            reason_id,
            index=index,
            left=(f"fact-left-{index}", LEFT_SITE),
            right=(f"fact-right-{index}", RIGHT_SITE),
        )
        for index, reason_id in enumerate(reason_ids)
    ]


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
    """production_cutover / discharge binding が読む最小の result 面。"""

    def __init__(self, decision, *, causes=None):
        causes = causes if causes is not None else _default_causes()
        self.decision_receipt = decision
        self.final_outcome = decision.outcome.value
        self.is_equivalent = {
            Outcome.EQUIVALENT: True, Outcome.NOT_EQ: False,
        }.get(decision.outcome, None)
        self.conditional_decision_receipt = None
        self.conditional_outcome = None
        self.unknown_reasons = [_ReasonRecord(spec) for spec in causes]
        self.call_effect_shadow_manifest = _manifest_for(causes)


def _run_lane(result, projection, analyses, *, disposition=True, policy=NO_OBSERVATION):
    return run_production_conditional_lane(
        result,
        projection=projection,
        analyses=analyses,
        observation_policy=policy,
        solver_runner=_Solver(disposition),
    )


def _both_analyses():
    return (
        _analysis(binary_id="binary1", op_offset=0x1100),
        _analysis(binary_id="binary2", entry=0x2000, op_offset=0x2100),
    )


def _pair(reason_ids=(CALL_REASON_ID,), *, causes=None,
          decision_effect="blocks_decision", outcome=Outcome.UNKNOWN):
    """同じ cause 記述から projection と result を作る。"""
    causes = causes if causes is not None else _default_causes(reason_ids)
    projection = _projection(causes=causes, decision_effect=decision_effect)
    decision = (
        _decision(outcome, projection=projection) if outcome is Outcome.UNKNOWN
        else _decision(outcome)
    )
    return projection, _Result(decision, causes=causes)


# --- lane activation --------------------------------------------------------


def test_lane_runs_after_an_unconditional_unknown_with_eligible_views():
    projection, result = _pair()
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
    projection, result = _pair()
    result.decision_receipt = fake
    assert _run_lane(result, projection, _both_analyses()) is None
    assert result.conditional_decision_receipt is None


def test_unknown_without_a_constructible_view_issues_no_conditional_receipt():
    projection, result = _pair()
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
    projection, result = _pair()
    assert _run_lane(result, projection, None) is None
    assert result.conditional_decision_receipt is None


# --- authority flow ---------------------------------------------------------


def test_proof_artifact_becomes_a_conditional_decisive_receipt_and_decision():
    projection, result = _pair()
    decision = result.decision_receipt
    artifact = run_conditional_proof(
        *_both_analyses(),
        observation_policy=NO_OBSERVATION,
        solver_runner=_Solver(True),
    )
    assert artifact.proof_kind == CONDITIONAL_EQ_CLOSURE

    receipt = issue_conditional_decision(
        unconditional_decision=decision, projection=projection, artifact=artifact,
        result=result,
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

    projection, result = _pair()
    decision = result.decision_receipt
    artifact = run_conditional_proof(
        *_both_analyses(), observation_policy=NO_OBSERVATION, solver_runner=_Solver(True)
    )
    receipt = issue_conditional_decision(
        unconditional_decision=decision, projection=projection, artifact=artifact,
        result=result,
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

    projection, result = _pair()
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
    projection, result = _pair()
    decision = result.decision_receipt
    left = _analysis(symbol="log", binary_id="binary1", op_offset=0x1100)
    right = _analysis(symbol="exp", binary_id="binary2", entry=0x2000, op_offset=0x2100)
    artifact = run_conditional_proof(
        left, right, observation_policy=NO_OBSERVATION, solver_runner=_Solver(True)
    )
    assert len(artifact.assumption_set) == 2

    lane_projection = conditional_lane_projection(
        projection,
        discharged_causes=conditional_discharged_causes(
            projection, result=result, artifact=artifact
        ),
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
        unconditional_decision=decision, projection=projection, artifact=artifact,
        result=result,
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
    projection, result = _pair()
    decision = result.decision_receipt
    artifact = run_conditional_proof(
        *_both_analyses(), observation_policy=NO_OBSERVATION, solver_runner=_Solver(True)
    )
    # UF が formula から消えた別 artifact（formula digest が違う）でも、
    # assumption_set は view が運んだものをそのまま持つ。
    stripped = ConditionalProofArtifact._create(
        proof_kind=artifact.proof_kind,
        assumption_set=artifact.assumption_set,
        formula_digest="formula-without-any-uf",
        solver_disposition=artifact.solver_disposition,
        modelled_call_count=artifact.modelled_call_count,
        modelled_call_sites=artifact.modelled_call_sites,
        modelled_call_sites_complete=artifact.modelled_call_sites_complete,
        all_calls_modelled=True,
        unsupported_calls_all_modelled=artifact.unsupported_calls_all_modelled,
    )
    assert stripped.validates()
    receipt = issue_conditional_decision(
        unconditional_decision=decision, projection=projection, artifact=stripped,
        result=result,
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
    empty = ConditionalProofArtifact._create(proof_kind=None, assumption_set=())
    with pytest.raises(ValueError):
        issue_conditional_decision(
            unconditional_decision=decision, projection=projection, artifact=empty
        )


# --- artifact sealing -------------------------------------------------------


def _tampered(artifact, **changes):
    """digest はそのままに field だけ差し替える（改竄を模す）。"""
    import copy

    forged = copy.copy(artifact)
    for name, value in changes.items():
        object.__setattr__(forged, name, value)
    return forged


def test_a_freshly_issued_artifact_validates():
    artifact = _artifact_for()
    artifact.validate()
    assert artifact.validates() is True
    assert artifact.artifact_digest
    assert artifact.assumption_set_digest
    assert artifact.formula_digest and artifact.solver_disposition == "unsat"


def test_an_artifact_cannot_be_constructed_outside_its_factory():
    artifact = _artifact_for()
    with pytest.raises(ValueError):
        ConditionalProofArtifact(
            proof_kind=artifact.proof_kind,
            assumption_set=artifact.assumption_set,
            assumption_set_digest=artifact.assumption_set_digest,
            formula_digest=artifact.formula_digest,
            solver_disposition=artifact.solver_disposition,
            modelled_call_count=artifact.modelled_call_count,
            modelled_call_sites=artifact.modelled_call_sites,
            modelled_call_sites_complete=artifact.modelled_call_sites_complete,
            all_calls_modelled=artifact.all_calls_modelled,
            unsupported_calls_all_modelled=artifact.unsupported_calls_all_modelled,
            non_decisive_reasons=artifact.non_decisive_reasons,
            artifact_digest=artifact.artifact_digest,
        )
    # dataclasses.replace も init=False なので通らない。
    import dataclasses

    with pytest.raises(Exception):
        dataclasses.replace(artifact, proof_kind=None)


@pytest.mark.parametrize(
    "field_name, replacement",
    [
        pytest.param("modelled_call_sites", lambda value: (), id="modelled_call_sites"),
        pytest.param(
            "modelled_call_sites",
            lambda value: (("function1", UNRELATED_LEFT_SITE),),
            id="modelled_call_sites_swapped",
        ),
        pytest.param(
            "modelled_call_sites_complete", lambda value: not value,
            id="modelled_call_sites_complete",
        ),
        pytest.param(
            "proof_kind", lambda value: CONDITIONAL_SAFE_COUNTEREXAMPLE, id="proof_kind"
        ),
        pytest.param("all_calls_modelled", lambda value: not value, id="all_calls_modelled"),
        pytest.param(
            "unsupported_calls_all_modelled", lambda value: not value,
            id="unsupported_calls_all_modelled",
        ),
        pytest.param("solver_disposition", lambda value: "sat", id="solver_disposition"),
        pytest.param("formula_digest", lambda value: "other-formula", id="formula_digest"),
        pytest.param("modelled_call_count", lambda value: value + 1, id="modelled_call_count"),
        pytest.param("non_decisive_reasons", lambda value: ("x",), id="non_decisive_reasons"),
    ],
)
def test_a_tampered_field_with_the_old_digest_is_rejected(field_name, replacement):
    artifact = _artifact_for()
    current = getattr(artifact, field_name)
    new_value = replacement(current)
    # 差し替えが本当に値を変えていること（no-op で通る test にしない）。
    assert new_value != current, field_name

    forged = _tampered(artifact, **{field_name: new_value})
    assert forged.artifact_digest == artifact.artifact_digest
    assert forged.validates() is False
    with pytest.raises(ValueError):
        forged.validate()


def test_a_tampered_assumption_set_with_the_old_digest_is_rejected():
    artifact = _artifact_for()
    forged = _tampered(artifact, assumption_set=(_premise("exp"),))
    assert forged.validates() is False
    with pytest.raises(ValueError):
        forged.validate()
    # digest だけ辻褄を合わせても artifact digest 側で落ちる。
    forged = _tampered(
        artifact,
        assumption_set=(_premise("exp"),),
        assumption_set_digest=ConditionalProofArtifact.assumption_digest(
            (_premise("exp"),)
        ),
    )
    with pytest.raises(ValueError):
        forged.validate()


def test_the_authority_entry_points_reject_a_tampered_artifact():
    projection, result = _pair()
    artifact = _artifact_for()
    forged = _tampered(artifact, modelled_call_sites_complete=False)

    with pytest.raises(ValueError):
        conditional_discharged_causes(projection, result=result, artifact=forged)
    with pytest.raises(ValueError):
        issue_conditional_decision(
            unconditional_decision=result.decision_receipt,
            projection=projection,
            artifact=forged,
            result=result,
        )


def test_the_authority_entry_points_reject_a_duck_typed_artifact():
    projection, result = _pair()
    artifact = _artifact_for()

    class _LookAlike:
        pass

    forged = _LookAlike()
    for name in (
        "proof_kind", "assumption_set", "assumption_set_digest", "formula_digest",
        "solver_disposition", "modelled_call_count", "modelled_call_sites",
        "modelled_call_sites_complete", "all_calls_modelled",
        "unsupported_calls_all_modelled", "non_decisive_reasons", "artifact_digest",
    ):
        setattr(forged, name, getattr(artifact, name))
    forged.validate = lambda: None

    with pytest.raises(TypeError):
        conditional_discharged_causes(projection, result=result, artifact=forged)
    with pytest.raises(TypeError):
        issue_conditional_decision(
            unconditional_decision=result.decision_receipt,
            projection=projection,
            artifact=forged,
            result=result,
        )


def test_a_tampered_artifact_leaves_the_unconditional_result_untouched():
    projection, result = _pair(decision_effect="blocks_equivalence")
    before = (result.is_equivalent, result.final_outcome, result.decision_receipt)

    class _ForgingSolver:
        def run_parallel(self, formula, timeout=None):
            return type("_R", (), {"is_equivalent": True})()

    # production 経路は lane 内で artifact を発行するので、改竄は
    # authority 入口で落ちる = conditional 列が付かないだけ。
    forged = _tampered(_artifact_for(), modelled_call_sites=())
    with pytest.raises(ValueError):
        issue_conditional_decision(
            unconditional_decision=result.decision_receipt,
            projection=projection,
            artifact=forged,
            result=result,
        )
    assert (result.is_equivalent, result.final_outcome, result.decision_receipt) == before
    assert result.conditional_decision_receipt is None
    assert result.conditional_outcome is None


def test_a_valid_artifact_still_discharges_the_bound_occurrence():
    """sealing を入れても occurrence-scoped discharge はそのまま成功する。"""
    causes = [
        _cause(CORRESPONDENCE_REASON_ID, index=0,
               left=("fact-left-modelled", LEFT_SITE),
               right=("fact-right-modelled", RIGHT_SITE)),
        _cause(CORRESPONDENCE_REASON_ID, index=1,
               left=("fact-left-internal", UNRELATED_LEFT_SITE),
               right=("fact-right-internal", UNRELATED_RIGHT_SITE)),
    ]
    projection, result = _pair(causes=causes, decision_effect="blocks_equivalence")
    artifact = _artifact_for()
    artifact.validate()
    assert conditional_discharged_causes(
        projection, result=result, artifact=artifact
    ) == frozenset({("occ-0", "cause-0")})
    diagnostics = _run_lane(result, projection, _both_analyses())
    assert diagnostics["discharged_cause_count"] == 1
    assert result.conditional_outcome == Outcome.UNKNOWN.value


# --- discharge rule ---------------------------------------------------------


def _artifact_for(analyses=None, *, disposition=True):
    return run_conditional_proof(
        *(analyses or _both_analyses()),
        observation_policy=NO_OBSERVATION,
        solver_runner=_Solver(disposition),
    )


def test_the_fixture_call_site_identities_are_the_ones_the_lane_derives():
    """LEFT_SITE / RIGHT_SITE が作り話でないこと（binding の前提）。"""
    left, right = _both_analyses()
    assert _call_site_key(left) == LEFT_SITE
    assert _call_site_key(right) == RIGHT_SITE
    artifact = _artifact_for((left, right))
    assert artifact.modelled_call_sites_complete is True
    assert set(artifact.modelled_call_sites) == {
        ("function1", LEFT_SITE), ("function2", RIGHT_SITE)
    }


def test_only_causes_bound_to_a_modelled_call_leave_the_conditional_projection():
    causes = [
        # A: 写像した external log の callsite に bind された occurrence。
        _cause(CALL_REASON_ID, index=0,
               left=("fact-left-0", LEFT_SITE), right=("fact-right-0", RIGHT_SITE)),
        # B: 仮定と無関係な別 blocker。
        _cause(OTHER_REASON_ID, index=1,
               left=("fact-left-1", LEFT_SITE), right=("fact-right-1", RIGHT_SITE)),
    ]
    projection, result = _pair(causes=causes)
    lane = conditional_lane_projection(
        projection,
        discharged_causes=conditional_discharged_causes(
            projection, result=result, artifact=_artifact_for()
        ),
    )
    assert {row.reason_id for row in lane.c_active_base} == {OTHER_REASON_ID}
    # 落とした cause にぶら下がる open requirement も satisfaction 行も落ちる。
    assert len(lane.q_open_base) == 1
    assert _satisfaction_occurrences(lane) == {"occ-1"}
    lane.validate()


def test_the_same_reason_id_is_discharged_only_where_it_binds_to_a_modelled_call():
    """同じ reason でも、写像した call 由来の occurrence だけを落とす。

    A: modelled external ``log`` に対応する ``callsite_correspondence_unproven``
    B: 写像していない internal call に対応する同じ reason
    → A だけ discharge、B は残り、conditional outcome は UNKNOWN。
    """
    causes = [
        _cause(CORRESPONDENCE_REASON_ID, index=0,
               left=("fact-left-modelled", LEFT_SITE),
               right=("fact-right-modelled", RIGHT_SITE)),
        _cause(CORRESPONDENCE_REASON_ID, index=1,
               left=("fact-left-internal", UNRELATED_LEFT_SITE),
               right=("fact-right-internal", UNRELATED_RIGHT_SITE)),
    ]
    projection, result = _pair(causes=causes, decision_effect="blocks_equivalence")
    artifact = _artifact_for()
    discharged = conditional_discharged_causes(
        projection, result=result, artifact=artifact
    )
    assert discharged == frozenset({("occ-0", "cause-0")})

    diagnostics = _run_lane(result, projection, _both_analyses())
    assert diagnostics["proof_kind"] == CONDITIONAL_EQ_CLOSURE
    assert diagnostics["discharged_cause_count"] == 1
    # B が残るので conditional 列は EQUIVALENT にならない。
    assert result.conditional_outcome == Outcome.UNKNOWN.value


def test_one_endpoint_outside_the_modelled_set_keeps_the_whole_cause():
    """左右どちらかでも写像外の callsite なら、その cause は落とさない。"""
    causes = [
        _cause(CORRESPONDENCE_REASON_ID, index=0,
               left=("fact-left-modelled", LEFT_SITE),
               right=("fact-right-internal", UNRELATED_RIGHT_SITE)),
    ]
    projection, result = _pair(causes=causes)
    assert conditional_discharged_causes(
        projection, result=result, artifact=_artifact_for()
    ) == frozenset()


def test_a_single_sided_cause_binds_to_that_side_only():
    """片側だけの obligation は、その側が写像済みなら discharge できる。"""
    causes = [
        _cause(CORRESPONDENCE_REASON_ID, index=0,
               left=("fact-left-modelled", LEFT_SITE), right=None),
        _cause(CORRESPONDENCE_REASON_ID, index=1,
               left=("fact-left-internal", UNRELATED_LEFT_SITE), right=None),
    ]
    projection, result = _pair(causes=causes)
    assert conditional_discharged_causes(
        projection, result=result, artifact=_artifact_for()
    ) == frozenset({("occ-0", "cause-0")})


@pytest.mark.parametrize(
    "mutate",
    [
        pytest.param(lambda result: setattr(result, "call_effect_shadow_manifest", None),
                     id="manifest_missing"),
        pytest.param(lambda result: setattr(result, "unknown_reasons", []),
                     id="cause_target_key_missing"),
        pytest.param(
            lambda result: setattr(
                result, "call_effect_shadow_manifest",
                {"left_facts": [{"fact_id": "fact-left-0", "identity": {}}],
                 "right_facts": []},
            ),
            id="fact_identity_missing",
        ),
    ],
)
def test_discharge_fails_closed_when_the_binding_cannot_be_resolved(mutate):
    projection, result = _pair()
    mutate(result)
    assert conditional_discharged_causes(
        projection, result=result, artifact=_artifact_for()
    ) == frozenset()


def test_a_non_prerequisite_target_key_is_never_discharged():
    """call-effect prerequisite 以外の鍵形の cause は対応付けない。"""
    causes = [
        _cause(CALL_REASON_ID, index=0,
               left=("fact-left-0", LEFT_SITE), right=("fact-right-0", RIGHT_SITE),
               prerequisite=False),
    ]
    projection, result = _pair(causes=causes)
    assert conditional_discharged_causes(
        projection, result=result, artifact=_artifact_for()
    ) == frozenset()


def test_incomplete_modelled_call_site_identity_discharges_nothing():
    """写像した callsite の identity が 1 つでも取れなければ何も落とさない。"""
    projection, result = _pair()
    artifact = _artifact_for()
    blinded = ConditionalProofArtifact._create(
        proof_kind=artifact.proof_kind,
        assumption_set=artifact.assumption_set,
        formula_digest=artifact.formula_digest,
        solver_disposition=artifact.solver_disposition,
        modelled_call_count=artifact.modelled_call_count,
        modelled_call_sites=artifact.modelled_call_sites,
        modelled_call_sites_complete=False,
        all_calls_modelled=True,
        unsupported_calls_all_modelled=artifact.unsupported_calls_all_modelled,
    )
    assert conditional_discharged_causes(
        projection, result=result, artifact=blinded
    ) == frozenset()


def test_a_deferred_call_without_a_pcode_identity_is_not_bindable():
    left = _analysis(binary_id="binary1", op_offset=0x1100)
    right = _analysis(binary_id="binary2", entry=0x2000, op_offset=0x2100)
    info = next(iter(left.deferred_calls.values()))
    info.deferred_call_ref = DeferredCallRef(
        caller_program_id=0x1000,
        caller_entry_offset=0x1000,
        target_ref=info.target_ref,
        sequence=1,
    )
    left.deferred_calls = {info.deferred_call_ref.stable_key(): info}
    artifact = _artifact_for((left, right))
    assert artifact.modelled_call_sites_complete is False
    projection, result = _pair()
    assert conditional_discharged_causes(
        projection, result=result, artifact=artifact
    ) == frozenset()


def test_the_conditional_projection_rebuilds_its_derived_digests():
    """seal が通ることではなく、派生 digest が作り直されていることを見る。"""
    causes = [
        _cause(CALL_REASON_ID, index=0,
               left=("fact-left-0", LEFT_SITE), right=("fact-right-0", RIGHT_SITE)),
        _cause(OTHER_REASON_ID, index=1,
               left=("fact-left-1", LEFT_SITE), right=("fact-right-1", RIGHT_SITE)),
    ]
    projection, result = _pair(causes=causes)
    lane = conditional_lane_projection(
        projection,
        discharged_causes=conditional_discharged_causes(
            projection, result=result, artifact=_artifact_for()
        ),
    )
    lane.validate()
    for name in (
        "c_active_base_digest",
        "q_open_base_digest",
        "semantic_cause_projection_digest",
        "satisfaction_projection_digest",
        "lifecycle_projection_digest",
    ):
        assert getattr(lane, name) != getattr(projection, name), name
    # 観測事実（blocker eligibility）は仮定では消えない。
    assert lane.blocker_eligibility_base == projection.blocker_eligibility_base


def test_an_unreadable_satisfaction_projection_fails_the_lane_closed():
    causes = [
        _cause(CALL_REASON_ID, index=0,
               left=("fact-left-0", LEFT_SITE), right=("fact-right-0", RIGHT_SITE)),
        _cause(OTHER_REASON_ID, index=1,
               left=("fact-left-1", LEFT_SITE), right=("fact-right-1", RIGHT_SITE)),
    ]
    rows = tuple(
        CActiveBaseRow(
            RESULT_ID, spec["occurrence_id"], spec["cause_id"], spec["reason_id"],
            "expression_call_effect_memory", "blocks_equivalence", spec["target_kind"],
        )
        for spec in causes
    )
    projection = VerifiedLifecycleProjection.seal(
        result_occurrence_id=RESULT_ID,
        snapshot_digest="snapshot",
        c_active_base=rows,
        q_open_base=(),
        blocker_eligibility_base=tuple(
            BlockerEligibilityBaseRow(RESULT_ID, row.occurrence_id, row.cause_id)
            for row in rows
        ),
        # 行の形が読めない satisfaction。整合検査で弾かれる。
        satisfaction_projection={"occurrences": ("unreadable-row",)},
    )
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection), causes=causes)
    with pytest.raises(ValueError):
        conditional_lane_projection(
            projection,
            discharged_causes=conditional_discharged_causes(
                projection, result=result, artifact=_artifact_for()
            ),
        )
    # production 経路では conditional 列を作らずに落ちる。
    diagnostics = _run_lane(result, projection, _both_analyses())
    assert diagnostics["conditional_lane"] == "failed"
    assert result.conditional_decision_receipt is None
    assert result.final_outcome == Outcome.UNKNOWN.value


def test_a_call_only_blocker_set_lets_the_conditional_column_reach_equivalent():
    """写像した call 由来の blocker だけなら conditional 列は EQUIVALENT になる。

    次の test の対照。これが無いと「常に UNKNOWN」でも通ってしまう。
    """
    projection, result = _pair(decision_effect="blocks_equivalence")
    diagnostics = _run_lane(result, projection, _both_analyses())

    assert diagnostics["proof_kind"] == CONDITIONAL_EQ_CLOSURE
    assert diagnostics["discharged_cause_count"] == 1
    assert result.conditional_outcome == Outcome.EQUIVALENT.value


def test_a_residual_non_call_blocker_keeps_the_conditional_column_unknown():
    causes = [
        _cause(CALL_REASON_ID, index=0,
               left=("fact-left-0", LEFT_SITE), right=("fact-right-0", RIGHT_SITE)),
        _cause(OTHER_REASON_ID, index=1,
               left=("fact-left-1", LEFT_SITE), right=("fact-right-1", RIGHT_SITE)),
    ]
    projection, result = _pair(causes=causes, decision_effect="blocks_equivalence")
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
    projection, result = _pair()
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
    projection, result = _pair()
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
    projection, result = _pair()

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
        ConditionalProofArtifact._create(
            proof_kind=CONDITIONAL_EQ_CLOSURE,
            assumption_set=(_premise(),),
            formula_digest="formula",
            solver_disposition="unsat",
            all_calls_modelled=False,
        )


# --- Issue #167: 最終 InputCorrespondence ---------------------------------------


def test_the_lane_is_not_decisive_without_the_final_relation():
    artifact = run_conditional_proof(
        *_both_analyses(),
        input_correspondence=None,
        observation_policy=NO_OBSERVATION,
        solver_runner=_Solver(True),
    )
    assert not artifact.decisive
    assert artifact.non_decisive_reasons == (lane_module.LANE_INPUT_CORRESPONDENCE_UNAVAILABLE,)


@pytest.mark.parametrize("disposition", [True, False])
def test_an_insufficient_final_relation_blocks_both_conditional_directions(disposition):
    from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
        InputCorrespondenceSet,
    )

    left, right = _both_analyses()
    relation = build_input_correspondence_set(left, right)
    assert relation.decisive_sufficient
    insufficient = InputCorrespondenceSet(
        correspondences=relation.correspondences,
        left_parameter_count=relation.left_parameter_count,
        right_parameter_count=relation.right_parameter_count,
        structural_defects=("synthetic_defect",),
        left_parameters=relation.left_parameters,
        right_parameters=relation.right_parameters,
    )
    artifact = run_conditional_proof(
        left,
        right,
        input_correspondence=insufficient,
        observation_policy=NO_OBSERVATION,
        solver_runner=_Solver(disposition),
    )
    assert not artifact.decisive
    assert lane_module.LANE_INPUT_CORRESPONDENCE_INSUFFICIENT in artifact.non_decisive_reasons
    assert "pair:input_correspondence:synthetic_defect" in artifact.non_decisive_reasons
