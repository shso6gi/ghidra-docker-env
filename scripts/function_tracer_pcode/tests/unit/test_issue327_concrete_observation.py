# -*- coding: utf-8 -*-
"""Issue #327 (E2): the return-observation classification inside the concrete proof.

Production proof, stand-in executors (``test_concrete_counterexample_lane``).
Pins what the classification may and may not change:

* the evidence is read only after a witness confirmed a difference, so the
  witnesses replayed, the one confirmed and the compared range R_C are the same
  with or without it (the conditional set can only shrink);
* a producer that fails, or a deadline that has passed, leaves every element
  assumed and the difference adopted as before;
* only a positive contradiction (``CONFLICT``) refuses the difference;
* the premises and the serialized record carry the classification, within the
  receipt's premise bounds; the reliance closure gains exactly the consulted
  handles and stays ``UNKNOWN_PROVENANCE``.
"""

import json
from types import SimpleNamespace

from scripts.function_tracer_pcode.authority.decision.conditional import (
    ASSUMPTION_PREMISE_MAX_BYTES,
    assumption_set_receipt_bound_violation,
)
from scripts.function_tracer_pcode.authority.decision.conditional_lane import return_width_parity_inputs
from scripts.function_tracer_pcode.checker import concrete_replay as adapter
from scripts.function_tracer_pcode.concrete.observation import (
    ObservationRelation,
    ObservedRegister,
    ReturnLocation,
    ReturnObservationPlan,
    compare_return_values,
    compared_extent,
)
from scripts.function_tracer_pcode.concrete.abi import ArgClass
from scripts.function_tracer_pcode.concrete.observation_claim import EvidenceStatus
from scripts.function_tracer_pcode.core.fact_reliance import (
    FactHandle,
    FactKind,
    FactProvenance,
    FactSide,
    FactSlot,
    FactTarget,
    RelianceBasis,
)
from scripts.function_tracer_pcode.proof.assumptions import AssumptionKind
from scripts.function_tracer_pcode.proof.concrete_counterexample import (
    CONCRETE_OBSERVATION_CONFLICT,
    ConcreteSubject,
    LazyObservationFacts,
    ReturnObservationFacts,
    run_concrete_counterexample_proof,
    subject_reliance,
    verify_concrete_record,
)
from scripts.function_tracer_pcode.tests.unit.test_concrete_counterexample_lane import (
    ARM,
    FACTS,
    Fixed,
    _analysis,
    _clean,
    _locate,
    _subjects,
)
from scripts.function_tracer_pcode.checker.concrete_replay import concrete_side_facts

WITNESSES = ({"param_1_1": 3, "param_1_2": 3},)


def _demand_facts(side, *, int_mask=0, fp_mask=0, own_int=True, own_fp=False, status="SCANNED"):
    target = FactTarget(side, FactSlot.RETURN)
    record = {"status": status, "own_writes": {"INT": own_int, "FP": own_fp},
              "callsites": [{"call": 0x500, "caller": 0x400, "end": "CBRANCH",
                             "demand": {"INT": int_mask, "FP": fp_mask}}]}
    handle = FactHandle(FactKind.RETURN_CALLER_DEMAND, target,
                        provenance=FactProvenance.leaf(producer_site="test", origin="synthetic"), value=record)
    return ReturnObservationFacts(handle, EvidenceStatus.CONSULTED, None, EvidenceStatus.NOT_CONSULTED)


class Counting:
    def __init__(self, build):
        self.calls = 0
        self._build = build

    def __call__(self):
        self.calls += 1
        return self._build()


def _with_observation(left, right, builders):
    base = _subjects(left, right)
    return tuple(
        ConcreteSubject(s.executor, s.abi, s.entry_address, s.locate, s.facts, s.side_facts, LazyObservationFacts(b))
        for s, b in zip(base, builders)
    )


def _run(subjects):
    return run_concrete_counterexample_proof(WITNESSES, subjects, budget_seconds=30.0, step_limit=1000)


def test_the_evidence_is_read_only_after_a_confirmation():
    builders = (Counting(lambda: _demand_facts(FactSide.LEFT)), Counting(lambda: _demand_facts(FactSide.RIGHT)))
    artifact = _run(_with_observation(Fixed(_clean(13)), Fixed(_clean(13)), builders))
    assert not artifact.decisive and artifact.observation is None
    assert [b.calls for b in builders] == [0, 0]
    artifact = _run(_with_observation(Fixed(_clean(13)), Fixed(_clean(14)), builders))
    assert artifact.decisive and [b.calls for b in builders] == [1, 1]


def test_the_replays_and_the_confirmed_witness_do_not_depend_on_the_evidence():
    plain = _run(_subjects(Fixed(_clean(13)), Fixed(_clean(14))))
    observed = _run(_with_observation(
        Fixed(_clean(13)), Fixed(_clean(14)),
        (lambda: _demand_facts(FactSide.LEFT, int_mask=0xFFFFFFFF),
         lambda: _demand_facts(FactSide.RIGHT, int_mask=0xFFFFFFFF)),
    ))
    assert plain.decisive and observed.decisive
    assert plain.replays == observed.replays and plain.confirmed == observed.confirmed
    assert plain.observation["compared_bits"] == observed.observation["compared_bits"] == 32
    # E-b verified O1/O2 on both sides, but O3 stays assumed: R_V is empty
    sides = observed.observation["sides"]
    assert [e["state"] for e in sides[0]["elements"]][:3] == ["VERIFIED", "VERIFIED", "ASSUMED"]
    assert observed.observation["verified_bits"] == 0


def test_a_failing_or_late_producer_leaves_every_element_assumed_and_the_difference_adopted(monkeypatch):
    def boom():
        raise ValueError("cannot read the program")
    artifact = _run(_with_observation(Fixed(_clean(13)), Fixed(_clean(14)), (boom, boom)))
    assert artifact.decisive
    assert all(e["state"] != "VERIFIED" for s in artifact.observation["sides"] for e in s["elements"])
    assert artifact.diagnostics["observation_evidence"]["side0"]["failure"].startswith("ValueError")

    # the adapter reads nothing once the analysis deadline has passed
    import scripts.function_tracer_pcode.core.deadline as deadline
    monkeypatch.setattr(deadline, "active_deadline", lambda: SimpleNamespace(remaining_seconds=lambda: 0.0))
    facts = adapter.return_observation_facts(None, 0x1000, ARM, FACTS, FactSide.LEFT, {"complete": True})
    assert facts.caller_demand_status is EvidenceStatus.DEADLINE and facts.handles() == ()


def test_a_positive_contradiction_refuses_the_difference():
    artifact = _run(_with_observation(
        Fixed(_clean(13)), Fixed(_clean(14)),
        (lambda: _demand_facts(FactSide.LEFT, fp_mask=0xFF, own_int=True, own_fp=True),
         lambda: _demand_facts(FactSide.RIGHT, int_mask=0xFF)),
    ))
    assert not artifact.decisive and artifact.non_decisive_reasons == (CONCRETE_OBSERVATION_CONFLICT,)
    assert artifact.confirmed is None and artifact.observation["conflict"] is True
    assert artifact.replays[0]["status"] == "CONFIRMED"   # the run is kept as a record


def test_the_premises_and_record_carry_the_classification_within_the_receipt_bounds():
    artifact = _run(_with_observation(
        Fixed(_clean(13)), Fixed(_clean(14)),
        (lambda: _demand_facts(FactSide.LEFT, int_mask=0xFFFFFFFF),
         lambda: _demand_facts(FactSide.RIGHT, int_mask=0xFF)),
    ))
    observation = [p for p in artifact.assumption_set if p.kind is AssumptionKind.CONCRETE_RETURN_OBSERVATION]
    assert [p.subject for p in observation] == ["function1", "function2"]
    for premise in artifact.assumption_set:
        assert len(json.dumps(premise.premise_key(), default=repr)) <= ASSUMPTION_PREMISE_MAX_BYTES
    assert assumption_set_receipt_bound_violation(tuple(artifact.assumption_set)) is None
    elements = dict(observation[0].payload)["elements"]
    o3 = dict(elements[2])
    assert o3["state"] == "ASSUMED" and o3["assumed"] == 32
    assert set(o3["unconfirmed"]) == {"C-b5_standard_calling_convention", "H3_no_interprocedural_reliance"}
    record = json.loads(json.dumps(artifact.to_json()))
    assert verify_concrete_record(record)
    assert record["artifact_payload"]["observation"]["difference_range"] == "ASSUMED_RANGE_ONLY"


def test_the_reliance_closure_gains_only_the_consulted_handles_and_stays_unknown():
    subjects = _with_observation(
        Fixed(_clean(13)), Fixed(_clean(14)),
        (lambda: _demand_facts(FactSide.LEFT, int_mask=0xFF), lambda: _demand_facts(FactSide.RIGHT, int_mask=0xFF)),
    )
    before = subject_reliance(subjects)
    assert FactKind.RETURN_CALLER_DEMAND not in {r.kind for r in before.refs}
    _run(subjects)
    after = subject_reliance(subjects)
    assert after.basis is before.basis is RelianceBasis.UNKNOWN_PROVENANCE
    # the synthetic handle is a leaf; the adapter's handle also brings PROGRAM_IMAGE / ABI_MODEL upstream
    assert {r.kind for r in after.refs} - {r.kind for r in before.refs} == {FactKind.RETURN_CALLER_DEMAND}


def test_the_compared_range_is_the_comparisons_own_value():
    location = ReturnLocation(ArgClass.INT, "x0", 8, 4)
    plan = ReturnObservationPlan(ArgClass.INT, (location, ReturnLocation(ArgClass.INT, "x0", 8, 8)), True)
    for defined, value in ((8, 0x1_0000_0001), (2, 0x10001), (4, 0x80000000)):
        left, right = ObservedRegister(0, 8, None, 8), ObservedRegister(value, defined, None, 8)
        relation = compare_return_values(plan, left, right)
        extent = compared_extent(plan, left, right)
        if relation is ObservationRelation.DIFFERENT:
            assert extent.compared_bits == 8 * min(4, defined)
            assert extent.first_difference_bit < extent.compared_bits
        else:
            assert extent is None


def test_the_lane_gives_the_smt_parity_inputs_and_the_adapter_reads_them_per_side():
    evidence = [
        {"side": "function1", "evidence": {"proof_requirement_id": {"proof_kind": "unary_return_width_relation"},
                                            "width_facts": {"semantic_payload_width": 32}}},
        {"binary_id": "B2", "evidence": {"proof_requirement_id": {"proof_kind": "unary_return_width_relation"},
                                          "width_facts": {"semantic_payload_width": 64}}},
        {"side": "function1", "evidence": {"proof_requirement_id": {"proof_kind": "other"}}},
    ]
    result = SimpleNamespace(completed_recovery_proof_evidence=evidence)
    quiet = SimpleNamespace(c_active_base=(SimpleNamespace(reason_id="counterexample_analysis_safety_unproven"),))
    inputs = return_width_parity_inputs(quiet, result)
    assert inputs["return_width_domain_active"] is False and len(inputs["completed"]) == 2
    left = adapter.smt_parity_of_side(inputs, FactSide.LEFT, SimpleNamespace(binary_id="B1"))
    right = adapter.smt_parity_of_side(inputs, FactSide.RIGHT, SimpleNamespace(binary_id="B2"))
    assert left == {"complete": True, "payload_bits": 32} and right == {"complete": True, "payload_bits": 64}
    active = SimpleNamespace(c_active_base=(SimpleNamespace(reason_id="return_width_provenance_unavailable"),))
    blocked = return_width_parity_inputs(active, result)
    assert adapter.smt_parity_of_side(blocked, FactSide.LEFT, SimpleNamespace(binary_id="B1"))["complete"] is False
    assert adapter.smt_parity_of_side(None, FactSide.LEFT, SimpleNamespace(binary_id="B1")) is None


def test_only_the_adapter_builds_return_observation_facts():
    import ast
    from pathlib import Path
    root = Path(__file__).resolve().parents[2]
    builders = []
    for path in root.rglob("*.py"):
        if "tests" in path.relative_to(root).parts:
            continue
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
            if isinstance(node, ast.Call) and getattr(node.func, "id", None) == "ReturnObservationFacts":
                builders.append(str(path.relative_to(root)))
    assert sorted(set(builders)) == ["checker/concrete_replay.py"]


def test_the_caller_demand_producer_reads_no_analysis_and_no_decompiler():
    import ast
    from pathlib import Path
    path = Path(__file__).resolve().parents[2] / "ghidra" / "return_use_evidence.py"
    tree = ast.parse(path.read_text(encoding="utf-8"))
    imported = {getattr(n, "module", None) or "" for n in ast.walk(tree) if isinstance(n, ast.ImportFrom)}
    imported |= {a.name for n in ast.walk(tree) if isinstance(n, ast.Import) for a in n.names}
    assert not any(m.startswith("scripts.function_tracer_pcode.") for m in imported)
    assert "DecompInterface" not in path.read_text(encoding="utf-8")


def test_the_evaluation_report_counts_the_classification_and_flags_unclassified_pairs():
    from scripts.function_tracer_pcode.reporting import concrete_evaluation as ce
    artifact = _run(_with_observation(
        Fixed(_clean(13)), Fixed(_clean(14)),
        (lambda: _demand_facts(FactSide.LEFT, int_mask=0xFF), lambda: _demand_facts(FactSide.RIGHT, int_mask=0xFF)),
    ))
    record = json.loads(json.dumps(artifact.to_json()))
    old = json.loads(json.dumps(record))
    old["artifact_payload"].pop("observation")
    facts = {
        ("f", "a", "b"): ce.PairFacts(key=("f", "a", "b"), label=ce.LABEL_NEQ, neq_core=True, outcome="UNKNOWN",
                                      conditional="NOT_EQ", left_sha256=None, right_sha256=None, concrete=record),
        ("f", "c", "d"): ce.PairFacts(key=("f", "c", "d"), label=ce.LABEL_NEQ, neq_core=True, outcome="UNKNOWN",
                                      conditional="NOT_EQ", left_sha256=None, right_sha256=None, concrete=old),
    }
    section = ce.observation(SimpleNamespace(facts=facts))
    assert section["pairs"] == 2 and section["unclassified_count"] == 1
    assert section["difference_range"] == {"ASSUMED_RANGE_ONLY": 1}
    assert section["elements"]["INT/O1_EXISTS/VERIFIED/None/E-b"] == 2
    assert section["elements"]["INT/O3_VALID_BITS/ASSUMED/PROTOTYPE/E-b"] == 2
