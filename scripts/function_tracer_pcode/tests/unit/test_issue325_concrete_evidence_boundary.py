# -*- coding: utf-8 -*-
"""Issue #325 (E1): the boundary of the concrete evidence and the serialized scope record.

* (i) the modules that build concrete evidence import only an allow-listed set
  directly, and reach none of the symbolic-proof builders (recurrence,
  call effect, formula, return width) transitively;
* (ii) the fact types are closed;
* (iii) no analysis object reaches the evidence: the proof reads the facts
  through ``ConcreteSideFacts`` handles built by one adapter, whose provenance
  is recorded as unknown (so the evidence relies on every fact);
* AC 8: the obligation-scope record reaches the serialized result payload,
  joined to its receipt and to the relation rows it explains.
"""

from __future__ import annotations

import ast
import json
import os
from enum import Enum
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.checker.concrete_replay import (
    SIDE_FACTS_PRODUCER_SITE,
    concrete_side_facts,
)
from scripts.function_tracer_pcode.core.fact_reliance import (
    FactHandle,
    FactKind,
    FactProvenance,
    FactSide,
    FactSlot,
    FactTarget,
    ProvenanceKind,
    RelianceBasis,
)
from scripts.function_tracer_pcode.proof.concrete_counterexample import (
    ConcreteSideFacts,
    subject_reliance,
)

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
PREFIX = "scripts.function_tracer_pcode."

#: the modules that build concrete evidence (the producer side of the boundary)
EVIDENCE_MODULES = tuple(sorted(
    [f"concrete.{path.stem}" for path in (PACKAGE_ROOT / "concrete").glob("*.py")]
    + ["proof.concrete_counterexample"]
))
#: what they may import directly (module prefixes, package-relative)
DIRECT_ALLOW = (
    "concrete",
    "core.fact_reliance",
    "core.parameter_domain",
    "core.structural",
    "smt.interface",
    "proof.assumptions",
    "proof.concrete_counterexample",
)
#: what they must not reach even transitively: the builders of the symbolic proof
TRANSITIVE_FORBIDDEN = (
    "proof.formula",
    "proof.recurrence_pcode_semantics",
    "proof.recurrence_promotion",
    "proof.recurrence_return_binding",
    "proof.call_effect",
    "proof.return_width",
    "proof.strategies",
    "analysis.recurrence",
    "analysis.returns",
    "authority",
    "checker",
)


def _path(module: str) -> Path:
    base = PACKAGE_ROOT.joinpath(*module.split("."))
    return base / "__init__.py" if base.is_dir() else base.with_suffix(".py")


def _imports(module: str):
    """Every project module ``module`` imports (top-level and lazy), package-relative."""
    path = _path(module)
    if not path.exists():
        return set()
    found = set()
    for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
        if isinstance(node, ast.ImportFrom) and node.module and node.module.startswith(PREFIX):
            name = node.module[len(PREFIX):]
            found.add(name)
            for alias in node.names:
                if _path(f"{name}.{alias.name}").exists():
                    found.add(f"{name}.{alias.name}")
        elif isinstance(node, ast.Import):
            found.update(alias.name[len(PREFIX):] for alias in node.names if alias.name.startswith(PREFIX))
    return found


def _within(name: str, prefixes) -> bool:
    return any(name == prefix or name.startswith(prefix + ".") for prefix in prefixes)


def test_i_the_evidence_modules_import_only_the_allow_list():
    offenders = {
        module: sorted(name for name in _imports(module) if not _within(name, DIRECT_ALLOW))
        for module in EVIDENCE_MODULES
    }
    assert {module: names for module, names in offenders.items() if names} == {}


def test_i_the_evidence_modules_reach_no_symbolic_proof_builder():
    seen, stack = set(), list(EVIDENCE_MODULES)
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        stack.extend(_imports(module))
    assert sorted(name for name in seen if _within(name, TRANSITIVE_FORBIDDEN)) == []


def test_ii_the_fact_types_are_closed():
    with pytest.raises(TypeError):
        type("Forged", (FactHandle,), {})
    with pytest.raises(TypeError):
        type("MoreKinds", (FactKind,), {"EXTRA": "EXTRA"})
    assert issubclass(FactKind, Enum)
    provenance = FactProvenance.leaf(producer_site="s", origin="o")
    wrong = FactHandle(FactKind.ABI_MODEL, FactTarget(FactSide.LEFT, FactSlot.RETURN), provenance=provenance)
    right = FactHandle(FactKind.RETURN_LOCATION, FactTarget(FactSide.LEFT, FactSlot.RETURN), provenance=provenance)
    cls = FactHandle(FactKind.RETURN_VALUE_CLASS, FactTarget(FactSide.LEFT, FactSlot.RETURN), provenance=provenance)
    with pytest.raises(TypeError):
        ConcreteSideFacts(parameters=wrong, return_location=right, return_value_class=cls)
    with pytest.raises(TypeError):
        ConcreteSideFacts(parameters={"name": "x"}, return_location=right, return_value_class=cls)


_ANALYSIS_ATTRIBUTES = {"parameters", "return_abi_facts", "return_type_obj", "return_type", "function_ref"}


def test_iii_no_analysis_object_reaches_the_evidence_modules():
    offenders = []
    for module in EVIDENCE_MODULES:
        tree = ast.parse(_path(module).read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
                for arg in (*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs):
                    if "analys" in arg.arg:
                        offenders.append(f"{module}: parameter {arg.arg}")
            if (
                isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "getattr"
                and len(node.args) >= 2 and isinstance(node.args[1], ast.Constant)
                and node.args[1].value in _ANALYSIS_ATTRIBUTES
            ):
                offenders.append(f"{module}: getattr(..., {node.args[1].value!r})")
            if isinstance(node, ast.Attribute) and node.attr in _ANALYSIS_ATTRIBUTES - {"parameters"}:
                offenders.append(f"{module}: .{node.attr}")
    assert offenders == []


def test_iii_one_adapter_builds_the_side_facts():
    builders = []
    for path in PACKAGE_ROOT.rglob("*.py"):
        relative = path.relative_to(PACKAGE_ROOT)
        if relative.parts[0] == "tests":
            continue
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "ConcreteSideFacts":
                builders.append(str(relative))
    assert builders == [os.path.join("checker", "concrete_replay.py")]


def _analysis():
    from scripts.function_tracer_pcode.tests.unit.test_concrete_counterexample_lane import _analysis as make

    return make()


def test_iii_the_adapter_records_an_unknown_provenance():
    facts = concrete_side_facts(_analysis(), FactSide.RIGHT)
    for handle in facts.handles():
        assert handle.provenance.kind is ProvenanceKind.UNRECORDED
        assert handle.provenance.producer_site == SIDE_FACTS_PRODUCER_SITE
        assert handle.ref.target.side is FactSide.RIGHT
    assert facts.parameters.value[0]["name"] == "param_1"
    assert facts.return_value_class.value == {"is_pointer": False}


def test_iii_a_concrete_evidence_relies_on_every_fact_until_its_provenance_is_recorded():
    from scripts.function_tracer_pcode.tests.unit.test_concrete_counterexample_lane import Fixed, _subjects

    reliance = subject_reliance(_subjects(Fixed(), Fixed()))
    assert reliance.basis is RelianceBasis.UNKNOWN_PROVENANCE
    assert {ref.kind for ref in reliance.refs} == {
        FactKind.PARAMETER_STORAGE, FactKind.RETURN_LOCATION, FactKind.RETURN_VALUE_CLASS,
    }
    assert subject_reliance(("PROGRAM_NOT_MODELLED:x", None)).basis is RelianceBasis.UNKNOWN_PROVENANCE
    assert subject_reliance(None).basis is RelianceBasis.UNKNOWN_PROVENANCE


# ------------------------------------------------------------- AC 8: serialized


def _check_record(record, receipt, relation_rows, lane):
    assert record["schema"] == "obligation-scope-v1" and record["lane"] == lane
    assert record["result_occurrence_id"] == receipt["result_occurrence_id"]
    assert record["lifecycle_projection_digest"] == receipt["lifecycle_projection_digest"]
    body = {key: value for key, value in record.items() if key != "record_digest"}
    assert record["record_digest"] == authority_digest(body)
    assert record["bound_to_receipt"] is False
    if relation_rows is not None:
        assert record["row_count"] == len(relation_rows)
        assert record["rows_digest"] == authority_digest(
            [[row["occurrence_id"], row["cause_id"]] for row in relation_rows]
        )
        assert {cause["cause_id"] for cause in record["causes"]} == {row["cause_id"] for row in relation_rows}
    for cause in record["causes"]:
        assert cause["guards_declared"] is False
        assert len(cause["bases"]) == len(record["evidence"])


@pytest.mark.wall_clock   # the production pair flow (Issue #239)
def test_the_unconditional_scope_reaches_the_canonical_payload():
    from scripts.function_tracer_pcode.checker.output_preparation import (
        build_final_result_envelope,
        envelope_seal_work,
    )
    from scripts.function_tracer_pcode.tests.unit.test_issue22d_o4_seal_contract import (
        _real_seal,
        _result_with_blockers,
    )

    result = _result_with_blockers(3)
    envelope = build_final_result_envelope(result, seal=_real_seal(result), work=envelope_seal_work())
    payload = json.loads(json.dumps(envelope.payload))
    record = payload["obligation_scope"]
    _check_record(record, payload["decision_receipt"], payload["c_active_base"], "UNCONDITIONAL")
    assert record["row_count"] == 3
    assert "obligation_scope" not in envelope.truncated_metadata


@pytest.mark.wall_clock   # the lane reads the analysis deadline (Issue #239)
def test_the_conditional_scope_reaches_the_payload_and_shows_the_concrete_reliance():
    from scripts.function_tracer_pcode.tests.unit.test_concrete_counterexample_lane import (
        SAT_REASON,
        Fixed,
        _clean,
        _concrete_lane,
        _sat_pair,
    )

    projection, result = _sat_pair(SAT_REASON, "counterexample_replay_unproven")
    diagnostics = _concrete_lane(result, projection, Fixed(_clean(13)), Fixed(_clean(14)))
    assert diagnostics["conditional_outcome"] == "NOT_EQ"
    # serialize through the production field table (the lane ran on the test's stub result)
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        attach_canonical_decision,
        attach_conditional_decision,
    )
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult

    real = EquivalenceResult(
        is_equivalent=None, function1_name="f", function2_name="f",
        binary1_name="a", binary2_name="b", solver_results=None,
    )
    attach_canonical_decision(real, result.decision_receipt)
    attach_conditional_decision(real, result.conditional_decision_receipt, result.conditional_obligation_scope)
    payload = json.loads(json.dumps(real.to_dict()))
    record = payload["conditional_obligation_scope"]
    _check_record(record, payload["conditional_decision_receipt"], None, "CONDITIONAL")
    # the SAT-safety rows were discharged by the lane before the scope was evaluated
    assert record["row_count"] == 0 and record["causes"] == []
    (evidence,) = record["evidence"]
    assert evidence["proof_kind"] == "CONDITIONAL_CONCRETE_COUNTEREXAMPLE"
    assert evidence["relies_on_basis"] == "UNKNOWN_PROVENANCE" and evidence["unblocked"] is True
    unconditional = payload["obligation_scope"] if "obligation_scope" in payload else None
    assert unconditional is None  # the test result was not finalized through the lifecycle
