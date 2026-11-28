# -*- coding: utf-8 -*-
"""The concrete replay of the solver's witnesses in the conditional lane (#18, C2).

The executors are stand-ins answering with given ``ExecutionResult`` s (the
real executor's facts are pinned by ``test_concrete_*`` and the recorded
traces); the proof, the discharge rule, the receipts and the conditional
decision are the production ones.
"""
import json
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.authority.contracts import Outcome
from scripts.function_tracer_pcode.authority.decision.conditional import ConditionalDecisiveProofKind
from scripts.function_tracer_pcode.authority.decision.conditional_lane import (
    CONCRETE_DISCHARGED_REASON_IDS,
    concrete_discharged_causes,
    issue_conditional_decision,
)
from scripts.function_tracer_pcode.concrete.abi import AbiId, abi_model
from scripts.function_tracer_pcode.concrete.executor import ExecutionResult, Hazard, HazardKind, Termination
from scripts.function_tracer_pcode.concrete.observation import ObservedRegister
from scripts.function_tracer_pcode.concrete.storage import StorageLocation
from scripts.function_tracer_pcode.core.analysis import ReturnInfo
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.proof.assumptions import AssumptionKind
from scripts.function_tracer_pcode.smt.interface import SolverStatus
from scripts.function_tracer_pcode.proof.concrete_counterexample import (
    CONCRETE_BUDGET_EXHAUSTED,
    CONCRETE_NO_WITNESS,
    CONCRETE_NOT_CONFIRMED,
    CONCRETE_PLAN_REFUSED,
    CONCRETE_SIDE_UNAVAILABLE,
    CONDITIONAL_CONCRETE_COUNTEREXAMPLE,
    ConcreteCounterexampleArtifact,
    ConcreteSubject,
    formula_inputs,
    return_storage,
    run_concrete_counterexample_proof,
    solver_witnesses,
    verify_concrete_record,
)
from scripts.function_tracer_pcode.checker.concrete_replay import concrete_side_facts
from scripts.function_tracer_pcode.core.fact_reliance import FactSide
from scripts.function_tracer_pcode.tests.unit._publication import raw_function_analysis
from scripts.function_tracer_pcode.tests.unit.test_issue20_prb3_conditional_lane import (
    NO_OBSERVATION,
    RESULT_ID,
    _artifact_for,
    _both_analyses,
    _cause,
    _decision,
    _projection,
    _Result,
    _Solver,
    run_production_conditional_lane,
)

ARM = abi_model(AbiId.AARCH64_AAPCS64)
SAT_REASON = "counterexample_analysis_safety_unproven"
OTHER_REASON = "outcome_path_region_completeness_unproven"
W0 = StorageLocation(True, "w0", "x0", 8, 0, 4)


def _storage(register="w0", base="x0", offset=0x4000):
    # the shape ``analysis.returns.parameters.get_storage_info`` records
    return {"is_register": True, "offset": offset, "size": 4, "size_bits": 32, "space_name": "register",
            "register_name": register, "base_register_name": base, "base_register_size": 8,
            "base_register_size_bits": 64, "bit_offset_in_base": 0}


def _analysis(entry=0x1000, *, return_type="int"):
    return raw_function_analysis(
        function_name="snippet",
        entry_point=hex(entry),
        parameters=[{"name": "param_1", "index": 0, "size": 4, "data_type": "int",
                     "is_signed": True, "storage": _storage()}],
        returns=[ReturnInfo(address=hex(entry),
                            value=Expression.parameter("param_1", index=0, data_type="int", size=4),
                            conditions=[])],
        return_type=return_type,
        return_abi_facts={"return_storage_descriptor": {
            "status": "PRESENT", "source": "test",
            "value": ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "register", 0x4000, 4),)),
        }},
    )


def _locate(space, offset, size):
    return W0 if (space, offset, size) == ("register", 0x4000, 4) else None


def _clean(value, **kw):
    kw.setdefault("fp_operations_tracked", True)
    kw.setdefault("integer_ub_operations_tracked", True)
    kw.setdefault("address_provenance_tracked", True)
    return ExecutionResult(Termination.RETURNED, 4, (("x0", ObservedRegister(value, 8, None, 8)),), **kw)


class Fixed:
    def __init__(self, *results):
        self.results = list(results)
        self.requests = []

    def execute(self, request):
        self.requests.append(request)
        return self.results.pop(0)


FACTS = {"sha256": "ab" * 32, "language_id": "AARCH64:LE:64:v8A", "compiler_spec_id": "default",
         "executor": "pcode-emulator-executor-v3", "ghidra": "12.0"}


def _subjects(left, right, analyses=None):
    # Issue #325: the proof reads each side's analysis only through the adapter's fact handles
    analysis1, analysis2 = analyses or (_analysis(), _analysis(0x2000))
    return (ConcreteSubject(left, ARM, 0x1000, _locate, FACTS,
                            concrete_side_facts(analysis1, FactSide.LEFT)),
            ConcreteSubject(right, ARM, 0x2000, _locate, dict(FACTS, sha256="cd" * 32),
                            concrete_side_facts(analysis2, FactSide.RIGHT)))


def _params(analysis):
    return concrete_side_facts(analysis, FactSide.LEFT).parameters


def _return(analysis, locate=None):
    facts = concrete_side_facts(analysis, FactSide.LEFT)
    return return_storage(facts.return_location, facts.return_value_class, locate or _locate)


WITNESS = {"param_1_1": 3, "param_1_2": 3, "rtunk_x_32": 9}


def _proof(left, right, witnesses=(WITNESS,), **kw):
    kw.setdefault("budget_seconds", 30.0)
    kw.setdefault("step_limit", 1000)
    return run_concrete_counterexample_proof(witnesses, _subjects(left, right), **kw)


# ------------------------------------------------------------------ the proof

def test_witnesses_come_from_the_sat_rows_distinct_and_in_order():
    rows = [SimpleNamespace(status=SolverStatus.UNSAT, model=None), SimpleNamespace(status=SolverStatus.SAT, model={"a": 1}),
            SimpleNamespace(status=SolverStatus.SAT, model={"a": 1}), SimpleNamespace(status=SolverStatus.SAT, model={"a": 2}),
            SimpleNamespace(status=SolverStatus.SAT, model=None)]
    assert solver_witnesses(SimpleNamespace(solver_results=SimpleNamespace(results=rows))) == ({"a": 1}, {"a": 2})
    assert solver_witnesses(SimpleNamespace()) == ()


def test_the_formula_inputs_and_the_return_location_are_read_from_the_analysis():
    analysis = _analysis()
    (only,) = formula_inputs(_params(analysis), "_2", _locate)
    assert only.variable == "param_1_2" and only.bit_width == 32 and only.location == W0
    storage = _return(analysis)
    assert storage.locations == (W0,) and not storage.is_pointer
    # pointer-ness is the recovered type object's (never the type's spelling)
    assert _return(_analysis_pointer()).is_pointer
    assert not _return(_analysis(return_type="int *")).is_pointer


def test_a_witness_whose_runs_differ_is_a_decisive_conditional_proof():
    left, right = Fixed(_clean(13)), Fixed(_clean(14))
    artifact = _proof(left, right)
    assert artifact.decisive and artifact.proof_kind == CONDITIONAL_CONCRETE_COUNTEREXAMPLE
    assert artifact.validates() and artifact.confirmed == 0
    # the same corresponding input on both sides; the formula's other variables are not inputs
    assert dict(left.requests[0].entry_state.registers)["x0"] == 3
    assert dict(right.requests[0].entry_state.registers)["x0"] == 3
    kinds = sorted((p.kind, p.subject) for p in artifact.assumption_set)
    # Issue #327: the return observation is its own premise per side (no evidence here: all assumed)
    assert kinds == [
        (AssumptionKind.CONCRETE_CALLING_CONVENTION, "function1"),
        (AssumptionKind.CONCRETE_CALLING_CONVENTION, "function2"),
        (AssumptionKind.CONCRETE_PCODE_SEMANTICS, "executor"),
        (AssumptionKind.CONCRETE_RETURN_OBSERVATION, "function1"),
        (AssumptionKind.CONCRETE_RETURN_OBSERVATION, "function2"),
    ]
    convention = [p for p in artifact.assumption_set
                  if p.subject == "function2" and p.kind is AssumptionKind.CONCRETE_CALLING_CONVENTION][0]
    assert convention.payload_value("return_width_bytes") is None   # moved to the observation premise
    observation = [p for p in artifact.assumption_set
                   if p.subject == "function2" and p.kind is AssumptionKind.CONCRETE_RETURN_OBSERVATION][0]
    assert observation.payload_value("verified_bits") == 0
    assert artifact.observation["difference_range"] == "ASSUMED_RANGE_ONLY"
    assert convention.payload_value("program_sha256") == "cd" * 32
    assert convention.payload_value("argument_registers") == ("x0",)
    record = json.loads(json.dumps(artifact.to_json()))
    assert verify_concrete_record(record)
    replay = record["artifact_payload"]["replays"][0]
    assert replay["status"] == "CONFIRMED" and replay["observed_values"] == [13, 14]
    assert replay["values"] == [3]
    record["artifact_payload"]["replays"][0]["observed_values"] = [13, 13]
    assert not verify_concrete_record(record)


@pytest.mark.parametrize("left_result, reason", [
    (_clean(14, writable_image_reads=((0x412000, 4),)), "WRITABLE_IMAGE_READ:side0"),
    (_clean(14, hazards=(Hazard(HazardKind.SIGNED_OVERFLOW, "x"),)), "RUN_HAS_HAZARD:side0:SIGNED_OVERFLOW"),
    (_clean(13), "NO_DIFFERENCE_OBSERVED"),
])
def test_runs_that_establish_nothing_leave_the_proof_non_decisive(left_result, reason):
    artifact = _proof(Fixed(left_result), Fixed(_clean(13)))
    assert not artifact.decisive and artifact.non_decisive_reasons == (CONCRETE_NOT_CONFIRMED,)
    assert artifact.assumption_set == () and artifact.replays[0]["reason"] == reason


def test_no_witness_no_side_a_refused_plan_and_a_spent_budget_are_non_decisive():
    assert _proof(Fixed(), Fixed(), witnesses=()).non_decisive_reasons == (CONCRETE_NO_WITNESS,)
    artifact = run_concrete_counterexample_proof(
        (WITNESS,), ("PROGRAM_NOT_MODELLED:x", None), budget_seconds=1, step_limit=1
    )
    assert artifact.non_decisive_reasons == (CONCRETE_SIDE_UNAVAILABLE,)
    assert artifact.plan == "SIDE_REFUSED:side0:PROGRAM_NOT_MODELLED:x;side1:UNAVAILABLE"
    pointer = run_concrete_counterexample_proof(
        (WITNESS,), _subjects(Fixed(), Fixed(), (_analysis(), _analysis_pointer())),
        budget_seconds=1, step_limit=1,
    )
    assert pointer.non_decisive_reasons == (CONCRETE_PLAN_REFUSED,)
    assert pointer.plan == "RETURN_LOCATION:side1:RETURN_TYPE_POINTER"
    ticks = iter([0.0, 5.0, 5.0, 5.0])
    spent = _proof(Fixed(), Fixed(), budget_seconds=1.0, clock=lambda: next(ticks))
    assert spent.non_decisive_reasons == (CONCRETE_NOT_CONFIRMED, CONCRETE_BUDGET_EXHAUSTED)
    assert spent.replays == ()


def _analysis_pointer():
    analysis = _analysis(0x2000, return_type="int *")
    analysis.return_type_obj = SimpleNamespace(isPointer=lambda: True, getName=lambda: "int *")
    return analysis


def test_an_artifact_is_made_only_by_its_factory_and_a_tampered_one_is_refused():
    artifact = _proof(Fixed(_clean(13)), Fixed(_clean(14)))
    with pytest.raises(ValueError):
        ConcreteCounterexampleArtifact(proof_kind=None)
    object.__setattr__(artifact, "confirmed", None)
    assert not artifact.validates()


# ------------------------------------------------------------- the authority

def _sat_pair(*reasons, effect="blocks_disequivalence"):
    causes = [_cause(reason, index=i) for i, reason in enumerate(reasons)]
    projection = _projection(causes=causes, decision_effect=effect)
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection), causes=causes)
    result.solver_results = SimpleNamespace(results=[SimpleNamespace(status=SolverStatus.SAT, model=dict(WITNESS))])
    return projection, result


def _concrete_lane(result, projection, left, right, analyses=None, *, deadline=600.0):
    """The production lane inside an analysis deadline of ``deadline`` seconds (``None``: none)."""
    from scripts.function_tracer_pcode.core.deadline import DeadlinePolicy, deadline_scope

    analyses = analyses or (_analysis(), _analysis(0x2000))
    with deadline_scope(None if deadline is None else DeadlinePolicy(deadline)):
        return run_production_conditional_lane(
            result, projection=projection, analyses=analyses, observation_policy=NO_OBSERVATION,
            solver_runner=_Solver(True),
            concrete_subjects=lambda a1, a2, observation_inputs=None: _subjects(left, right, (a1, a2)),
            concrete_options=SimpleNamespace(budget_seconds=30.0, step_limit=1000),
        )
@pytest.mark.wall_clock   # the lane reads the analysis deadline (Issue #239)

def test_a_confirmed_replay_discharges_only_the_sat_safety_causes_and_gives_conditional_not_eq():
    projection, result = _sat_pair(SAT_REASON, "counterexample_replay_unproven")
    diagnostics = _concrete_lane(result, projection, Fixed(_clean(13)), Fixed(_clean(14)))
    assert diagnostics["conditional_lane"] == "issued" and diagnostics["conditional_outcome"] == "NOT_EQ"
    assert diagnostics["concrete_proof_kind"] == CONDITIONAL_CONCRETE_COUNTEREXAMPLE
    assert diagnostics["discharged_cause_count"] == 2
    assert verify_concrete_record(diagnostics["concrete_replay"])
    # the unconditional decision is untouched
    assert result.final_outcome == "UNKNOWN" and result.decision_receipt.outcome is Outcome.UNKNOWN
    assert result.conditional_outcome == "NOT_EQ"
    receipt = result.conditional_decision_receipt
    assert receipt.unconditional_outcome is Outcome.UNKNOWN
    assert {p.kind for p in receipt.assumption_set} == {
        AssumptionKind.CONCRETE_CALLING_CONVENTION, AssumptionKind.CONCRETE_PCODE_SEMANTICS,
        AssumptionKind.CONCRETE_RETURN_OBSERVATION,   # Issue #327: the assumed observation elements
    }


@pytest.mark.wall_clock   # the lane reads the analysis deadline (Issue #239)
@pytest.mark.parametrize("effect", ["blocks_decision", "blocks_disequivalence"])
def test_a_confirmed_replay_does_not_discharge_other_blockers(effect):
    causes = [_cause(SAT_REASON, index=0), _cause(OTHER_REASON, index=1)]
    projection = _projection(causes=causes, decision_effect=effect)
    result = _Result(_decision(Outcome.UNKNOWN, projection=projection), causes=causes)
    result.solver_results = SimpleNamespace(results=[SimpleNamespace(status=SolverStatus.SAT, model=dict(WITNESS))])
    diagnostics = _concrete_lane(result, projection, Fixed(_clean(13)), Fixed(_clean(14)))
    assert diagnostics["conditional_outcome"] == "UNKNOWN"
    assert diagnostics["discharged_cause_count"] == 1
    artifact = _proof(Fixed(_clean(13)), Fixed(_clean(14)))
    assert concrete_discharged_causes(projection, artifact=artifact) == frozenset({("occ-0", "cause-0")})
    assert CONCRETE_DISCHARGED_REASON_IDS == {
        "counterexample_analysis_safety_unproven", "counterexample_replay_unproven",
        "counterexample_partition_replay_ambiguous",
    }
@pytest.mark.wall_clock   # the lane reads the analysis deadline (Issue #239)

def test_an_unconfirmed_replay_issues_no_column_and_keeps_its_record():
    projection, result = _sat_pair(SAT_REASON)
    diagnostics = _concrete_lane(result, projection, Fixed(_clean(13)), Fixed(_clean(13)))
    assert diagnostics["conditional_lane"] == "not_constructed"
    assert result.conditional_decision_receipt is None and result.conditional_outcome is None
    record = diagnostics["concrete_replay"]
    assert record["artifact_payload"]["non_decisive_reasons"] == [CONCRETE_NOT_CONFIRMED]
    assert record["artifact_payload"]["replays"][0]["reason"] == "NO_DIFFERENCE_OBSERVED"


@pytest.mark.wall_clock   # the lane reads the analysis deadline (Issue #239)
@pytest.mark.parametrize("outcome", [Outcome.EQUIVALENT, Outcome.NOT_EQ, Outcome.ERROR])
def test_no_replay_runs_after_a_decided_pair(outcome):
    projection, _ = _sat_pair(SAT_REASON)
    result = _Result(_decision(outcome))
    result.solver_results = SimpleNamespace(results=[SimpleNamespace(status=SolverStatus.SAT, model=dict(WITNESS))])
    left = Fixed()
    assert _concrete_lane(result, projection, left, Fixed()) is None
    assert left.requests == [] and result.conditional_outcome is None


def test_without_concrete_options_the_lane_is_unchanged():
    projection, result = _sat_pair(SAT_REASON)
    diagnostics = run_production_conditional_lane(
        result, projection=projection, analyses=(_analysis(), _analysis(0x2000)),
        observation_policy=NO_OBSERVATION, solver_runner=_Solver(True),
    )
    assert "concrete_replay" not in diagnostics and diagnostics["conditional_lane"] == "not_constructed"


def test_an_external_call_eq_and_a_concrete_difference_contradict():
    analyses = _both_analyses()
    eq_artifact = _artifact_for(analyses)
    assert eq_artifact.proof_kind == "CONDITIONAL_EQ_CLOSURE"
    projection, result = _sat_pair(SAT_REASON)
    concrete = _proof(Fixed(_clean(13)), Fixed(_clean(14)))
    receipt = issue_conditional_decision(
        unconditional_decision=result.decision_receipt, projection=projection,
        artifact=eq_artifact, result=result, concrete_artifact=concrete,
    )
    assert receipt.conditional_outcome is Outcome.ERROR
    kinds = {p.kind for p in receipt.assumption_set}
    assert AssumptionKind.EXTERNAL_CALLEE_SPEC in kinds and AssumptionKind.CONCRETE_PCODE_SEMANTICS in kinds


def test_the_authority_refuses_a_tampered_or_foreign_concrete_artifact():
    projection, result = _sat_pair(SAT_REASON)
    concrete = _proof(Fixed(_clean(13)), Fixed(_clean(14)))
    object.__setattr__(concrete, "plan", "forged")
    with pytest.raises(ValueError):
        issue_conditional_decision(unconditional_decision=result.decision_receipt, projection=projection,
                                   artifact=None, concrete_artifact=concrete)
    with pytest.raises(TypeError):
        issue_conditional_decision(unconditional_decision=result.decision_receipt, projection=projection,
                                   artifact=None, concrete_artifact=SimpleNamespace(decisive=True))
    assert ConditionalDecisiveProofKind.CONDITIONAL_CONCRETE_COUNTEREXAMPLE.value == CONDITIONAL_CONCRETE_COUNTEREXAMPLE


def test_the_checker_takes_the_entry_from_the_typed_function_reference():
    from scripts.function_tracer_pcode.checker.concrete_replay import _entry
    from scripts.function_tracer_pcode.core.call_target import CallTargetRef

    analysis = _analysis()
    analysis.function_ref = None
    assert _entry(analysis) is None            # no reference: refused, not parsed from text
    analysis.function_ref = CallTargetRef.from_name("snippet", program_id=1, entry_offset=0x100714)
    analysis.entry_point = "00100714"           # Ghidra's address text is not read
    assert _entry(analysis) == 0x100714


def test_a_parameter_is_located_by_its_varnode_and_read_at_its_type_width():
    # a type hypothesis narrowed an ``int`` whose storage is the whole ``x0``
    analysis = _analysis()
    analysis.parameters[0]["storage"] = dict(_storage(), size=8, register_name="x0")
    seen = []

    def locate(space, offset, size):
        seen.append((space, offset, size))
        return StorageLocation(True, "x0", "x0", 8, 0, size)

    (only,) = formula_inputs(_params(analysis), "_1", locate)
    assert seen == [("register", 0x4000, 8)]
    # the same when the record keeps the type's width at the base register's
    # start (MIPS: 4 bytes at ``a0``'s offset would be its high half)
    analysis.parameters[0]["storage"] = dict(_storage(), size=4, register_name="x0")
    seen.clear()
    (only,) = formula_inputs(_params(analysis), "_1", locate)
    assert seen == [("register", 0x4000, 8)] and only.location.names_whole_base_register()
    assert only.location.size_bytes == 4 and only.location.names_whole_base_register()
    # a stack or unlocatable parameter is not a register parameter
    analysis.parameters[0]["storage"] = {"is_register": False, "offset": 8, "size": 4, "space_name": "stack"}
    assert not formula_inputs(_params(analysis), "_1", locate)[0].location.is_register


def test_the_replay_never_outlasts_its_budget():
    # (review of PR #321/#322) a witness started 1 s before the end of the budget
    # gets 1 s, not the executor's own 20 s per run
    now = [0.0]
    left, right = Fixed(_clean(13), _clean(13)), Fixed(_clean(13), _clean(14))

    def tick():
        now[0] += 4.5
        return now[0]

    artifact = _proof(left, right, witnesses=(WITNESS, dict(WITNESS, param_1_1=4, param_1_2=4)),
                      budget_seconds=10.0, clock=tick)
    limits = [r.time_limit_seconds for r in left.requests + right.requests]
    assert all(limit is not None and limit <= 10.0 for limit in limits)
    assert artifact.diagnostics["replayed"] <= 2
@pytest.mark.wall_clock   # the lane reads the analysis deadline (Issue #239)

def test_the_replay_runs_only_inside_an_analysis_deadline():
    # without a cooperative deadline the time added after the decision would only
    # bring the pair process closer to the supervisor's timeout
    projection, result = _sat_pair(SAT_REASON)
    left = Fixed(_clean(13))
    diagnostics = _concrete_lane(result, projection, left, Fixed(_clean(14)), deadline=None)
    assert left.requests == [] and result.conditional_outcome is None
    payload = diagnostics["concrete_replay"]["artifact_payload"]
    assert payload["non_decisive_reasons"] == ["concrete_replay_no_analysis_deadline"]
@pytest.mark.wall_clock   # the lane reads the analysis deadline (Issue #239)

def test_the_replay_budget_is_what_is_left_of_the_deadline():
    projection, result = _sat_pair(SAT_REASON)
    left, right = Fixed(_clean(13)), Fixed(_clean(14))
    _concrete_lane(result, projection, left, right, deadline=5.0)
    assert 0 < left.requests[0].time_limit_seconds <= 5.0
    assert 0 < right.requests[0].time_limit_seconds <= left.requests[0].time_limit_seconds
