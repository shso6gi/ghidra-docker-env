"""Build the source-bound Phase 7 production cutover authority artifact."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from typing import Any, Mapping, Optional, Sequence
from xml.etree import ElementTree
from enum import Enum

from ..equivalence.v2.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    IdentityScope,
    ProofRequirement,
    RecoveryAddressability,
    authority_digest,
)
from ..equivalence.v2.decision import (
    FinalizationAuthority,
    TerminalTimeoutReceipt,
    finalize_decision,
)
from ..equivalence.v2.phase7_cutover import (
    ActivationDisposition,
    ExpectedActivationContract,
    ExpectedActivationLedgerFactory,
    ExpectedCauseSlotContract,
    ProducerSiteContract,
    SealedProducerSiteRegistry,
    VerifiedFinalizationBundleFactory,
    typed_cause_coverage,
)
from ..equivalence.v2.reducer import ShadowLifecycleReducer
from ..equivalence.v2.codecs import StrictV2JsonCodec
from ..equivalence.v2.process_supervisor import (
    DurableCheckpointStore,
    PROCESS_DURABLE_REASON_REGISTRY,
    PROCESS_DURABLE_RECOVERY_REGISTRY,
    ProcessSupervisorAuthorityFactory,
)
from ..equivalence.v2.registry import (
    SatisfactionBindingFactory,
    SemanticCauseIdentityFactory,
)


VALIDATION_KIND = "unknown-taxonomy-v2-phase7-cutover-contract-fixture-v2"

_DOMAIN_ROWS = (
    (
        "operational_extraction", "function_decompilation_artifact_unavailable",
        IdentityScope.UNARY,
        "scripts/function_tracer_pcode/equivalence/v2/operational_extraction.py",
    ),
    (
        "expression_call_effect_memory", "expression_semantics_unsupported",
        IdentityScope.UNARY,
        "scripts/function_tracer_pcode/equivalence/strategies/monolithic.py",
    ),
    (
        "loop_recurrence_summary", "loop_summary_semantic_equality_unproven",
        IdentityScope.RELATIONAL,
        "scripts/function_tracer_pcode/equivalence/strategies/pairwise_services/orchestration_1.py",
    ),
    (
        "return_outcome", "outcome_partition_completion_unproven",
        IdentityScope.UNARY,
        "scripts/function_tracer_pcode/equivalence/strategies/proof_gates/return_coverage.py",
    ),
    (
        "sat_safety", "counterexample_analysis_safety_unproven",
        IdentityScope.RELATIONAL,
        "scripts/function_tracer_pcode/equivalence/strategies/proof_gates/sat_safety.py",
    ),
    (
        "return_width", "return_width_provenance_unavailable",
        IdentityScope.UNARY,
        "scripts/function_tracer_pcode/equivalence/checker.py",
    ),
)

_CROSS_SLICE_TEST_PATHS = (
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_contracts.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase2.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase3.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase4.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase5.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_abi_width_readonly.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_call_effect.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_loop_recurrence.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_operational_extraction.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_process_census.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_process_supervisor.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_process_supervisor_command.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_process_worker_runtime.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_return_outcome.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_sat_safety.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_subordinate_decompilation.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase7_cutover.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase7_inventory.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase7_legacy_baseline.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase7_producer_manifest.py",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _require_passing_junit(path: Path, test_name: str) -> None:
    root = ElementTree.parse(path).getroot()
    suites = tuple(root.iter("testsuite"))
    cases = tuple(root.iter("testcase"))
    if (
        sum(int(suite.attrib.get("tests", "0")) for suite in suites) != 1
        or any(int(suite.attrib.get("errors", "0")) for suite in suites)
        or any(int(suite.attrib.get("failures", "0")) for suite in suites)
        or len(cases) != 1
        or cases[0].attrib.get("name") != test_name
    ):
        raise ValueError(f"Phase 7 JUnit authority is not passing: {test_name}")


def write_cross_slice_validation_source_map(
    repo_root: Path, junit_path: Path, output_path: Path,
) -> Mapping[str, Any]:
    root = Path(repo_root).resolve()
    junit = Path(junit_path).resolve()
    xml = ElementTree.parse(junit).getroot()
    suites = tuple(xml.iter("testsuite"))
    cases = tuple(xml.iter("testcase"))
    test_count = sum(int(item.attrib.get("tests", "0")) for item in suites)
    if (
        test_count != len(cases)
        or test_count < 403
        or any(int(item.attrib.get("errors", "0")) for item in suites)
        or any(int(item.attrib.get("failures", "0")) for item in suites)
        or any(int(item.attrib.get("skipped", "0")) for item in suites)
    ):
        raise ValueError("cross-slice JUnit is not a complete passing run")
    body = {
        "manifest_kind": "unknown-taxonomy-v2-phase7-cross-slice-junit-v1",
        "pytest_selection": _CROSS_SLICE_TEST_PATHS,
        "junit_path": junit.relative_to(root).as_posix(),
        "junit_sha256": _sha256(junit),
        "test_count": test_count,
        "source_files": tuple({
            "path": path,
            "sha256": _sha256(root / path),
        } for path in _CROSS_SLICE_TEST_PATHS),
    }
    payload = {**body, "artifact_digest": authority_digest(body)}
    output = Path(output_path)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return payload


def _verify_cross_slice_validation_source_map(
    repo_root: Path, payload: Mapping[str, Any],
) -> None:
    root = Path(repo_root).resolve()
    body = {key: value for key, value in payload.items() if key != "artifact_digest"}
    junit = root / payload.get("junit_path", "")
    source_rows = tuple(payload.get("source_files", ()))
    if (
        payload.get("artifact_digest") != authority_digest(body)
        or tuple(payload.get("pytest_selection", ())) != _CROSS_SLICE_TEST_PATHS
        or tuple(row.get("path") for row in source_rows) != _CROSS_SLICE_TEST_PATHS
        or any(_sha256(root / row["path"]) != row.get("sha256") for row in source_rows)
        or not junit.is_file()
        or _sha256(junit) != payload.get("junit_sha256")
    ):
        raise ValueError("cross-slice validation source map drifted")
    xml = ElementTree.parse(junit).getroot()
    suites = tuple(xml.iter("testsuite"))
    cases = tuple(xml.iter("testcase"))
    if (
        payload.get("test_count") != len(cases)
        or payload.get("test_count", 0) < 403
        or any(int(item.attrib.get("errors", "0")) for item in suites)
        or any(int(item.attrib.get("failures", "0")) for item in suites)
        or any(int(item.attrib.get("skipped", "0")) for item in suites)
    ):
        raise ValueError("cross-slice validation JUnit is incomplete")


def _json_authority_value(value: Any) -> Any:
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, Mapping):
        return {str(key): _json_authority_value(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [_json_authority_value(item) for item in value]
    return value


def _persistable_authority(value: Any) -> Any:
    return _json_authority_value({
        name: getattr(value, name)
        for name in value.__dataclass_fields__
        if not name.startswith("_")
    })


def _verify_real_timeout_authority(payload: Mapping[str, Any]) -> None:
    durable = payload.get("durable_store")
    if not isinstance(durable, Mapping) or not isinstance(
        durable.get("files"), Mapping
    ):
        raise ValueError("Phase 7 TIMEOUT lacks durable rematerialization files")
    factory = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id=durable["supervisor_signing_key_id"],
        supervisor_signing_key=bytes.fromhex(durable["supervisor_signing_key_hex"]),
        worker_signing_key_id=durable["worker_signing_key_id"],
        worker_signing_key=bytes.fromhex(durable["worker_signing_key_hex"]),
    )
    with tempfile.TemporaryDirectory() as temporary:
        store = DurableCheckpointStore(
            Path(temporary), factory, durable["execution_nonce"]
        )
        for name, content in durable["files"].items():
            if (
                type(name) is not str
                or Path(name).name != name
                or type(content) is not str
            ):
                raise ValueError("Phase 7 TIMEOUT durable file is not canonical")
            (store.directory / name).write_text(content, encoding="utf-8")
        prefix = store.rematerialize_active_prefix()
        bundle = store.rematerialize_timeout_bundle(prefix=prefix)
    reduction = ShadowLifecycleReducer(
        reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
        recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
    ).replay(bundle.terminal_segment.composite_stream)
    terminal_event = bundle.terminal_segment.composite_stream.events[-1]
    timeout_receipt = TerminalTimeoutReceipt.create(
        result_occurrence_id=bundle.result_occurrence_id,
        lifecycle_projection_digest=reduction.projection.lifecycle_projection_digest,
        proof_requirement_id=bundle.proof_requirement_id,
        execution_event_digest=terminal_event.authority_digest,
    )
    decision = finalize_decision(FinalizationAuthority(
        result_occurrence_id=bundle.result_occurrence_id,
        lifecycle_projection=reduction.projection,
        terminal_timeout_receipts=(timeout_receipt,),
    ))
    typed = payload.get("typed_projection_receipt")
    if not isinstance(typed, Mapping):
        raise ValueError("Phase 7 TIMEOUT lacks a typed projection authority")
    typed_body = {key: value for key, value in typed.items() if key != "receipt_digest"}
    active_join = tuple(
        row for row in reduction.projection.c_active_base
        if (
            row.result_occurrence_id == typed.get("result_occurrence_id")
            and row.occurrence_id == typed.get("occurrence_id")
            and row.cause_id == typed.get("cause_id")
            and row.reason_id == typed.get("reason_id")
        )
    )
    checkpoint = factory.decode(json.loads(durable["files"]["checkpoint.json"]))
    live_assignment = payload.get("durable_live_assignment")
    decoded_assignment = (
        factory.decode(live_assignment) if isinstance(live_assignment, Mapping)
        else None
    )
    if (
        bundle.bundle_digest != payload.get("durable_timeout_bundle_digest")
        or bundle.composite_stream_authority_digest != payload.get("event_stream_digest")
        or reduction.projection.lifecycle_projection_digest
        != payload.get("lifecycle_projection_digest")
        or _persistable_authority(timeout_receipt)
        != payload.get("terminal_timeout_receipt")
        or _persistable_authority(decision) != payload.get("decision_receipt")
        or tuple(_persistable_authority(row) for row in reduction.projection.c_active_base)
        != tuple(payload.get("c_active_rows", ()))
        or tuple(_persistable_authority(row) for row in reduction.projection.q_open_base)
        != tuple(payload.get("q_open_rows", ()))
        or typed.get("receipt_digest") != authority_digest(typed_body)
        or typed.get("event_stream_digest") != bundle.composite_stream_authority_digest
        or typed.get("lifecycle_projection_digest")
        != reduction.projection.lifecycle_projection_digest
        or len(active_join) != 1
        or not isinstance(live_assignment, Mapping)
        or decoded_assignment.receipt_digest
        != checkpoint.payload.get("assignment_receipt_digest")
        or any(
            "timeout" in row.reason_id.lower()
            for row in reduction.projection.c_active_base
        )
    ):
        raise ValueError("Phase 7 TIMEOUT rematerialized authority join failed")


def _verify_real_sat_authority(
    payload: Mapping[str, Any], producer_manifest: Mapping[str, Any],
    repo_root: Path,
) -> None:
    body = {key: value for key, value in payload.items() if key != "artifact_digest"}
    codec = StrictV2JsonCodec(
        reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
        recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    stream = codec.loads(json.dumps(payload.get("sealed_event_stream")))
    reduction = ShadowLifecycleReducer(
        reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
        recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
    ).replay(stream)
    decision = finalize_decision(FinalizationAuthority(
        result_occurrence_id=stream.envelope.result_occurrence_id,
        lifecycle_projection=reduction.projection,
    ))
    typed = payload.get("typed_projection_receipt")
    typed_body = (
        {key: value for key, value in typed.items() if key != "receipt_digest"}
        if isinstance(typed, Mapping) else {}
    )
    active_join = tuple(
        row for row in reduction.projection.c_active_base
        if (
            row.result_occurrence_id == typed.get("result_occurrence_id")
            and row.occurrence_id == typed.get("occurrence_id")
            and row.cause_id == typed.get("cause_id")
            and row.reason_id == typed.get("reason_id")
        )
    ) if isinstance(typed, Mapping) else ()
    receipts = tuple(payload.get("query_execution_receipts", ()))
    identities = tuple(payload.get("binary_content_identities", ()))
    source_paths = tuple(payload.get("source_paths", ()))
    compiler_argv = tuple(payload.get("compiler_argv", ()))
    current_sources = tuple(
        (repo_root / path).resolve() for path in source_paths
    )
    current_source_hashes = tuple(
        hashlib.sha256(path.read_bytes()).hexdigest()
        for path in current_sources
        if path.is_file() and repo_root.resolve() in path.parents
    )
    rebuilt_hashes = []
    if (
        len(current_sources) == 2
        and len(current_source_hashes) == 2
        and compiler_argv == ("gcc", "-O0", "-c")
    ):
        with tempfile.TemporaryDirectory(prefix="phase7-sat-rebuild-") as tmp:
            for index, source in enumerate(current_sources):
                output = Path(tmp) / f"fixture-{index}.o"
                subprocess.run(
                    (*compiler_argv, "-o", str(output), str(source)),
                    check=True, capture_output=True, text=True,
                )
                rebuilt_hashes.append(
                    hashlib.sha256(output.read_bytes()).hexdigest()
                )
    if (
        payload.get("artifact_digest") != authority_digest(body)
        or payload.get("producer_manifest_digest")
        != producer_manifest.get("manifest_digest")
        or payload.get("producer_site_count") != producer_manifest.get("site_count")
        or payload.get("static_producer_site_count") != producer_manifest.get("site_count")
        or payload.get("expected_activation_count") != 1
        or payload.get("runtime_activation_count") != 1
        or payload.get("discovered_activation_count") != 1
        or payload.get("not_reached_activation_count") != 0
        or payload.get("selected_activation_count") != 1
        or payload.get("selected_site_id") != "sat-safety-blocker-observed"
        or payload.get("final_outcome") != "UNKNOWN"
        or payload.get("terminal_timeout_receipt_count") != 0
        or _persistable_authority(decision) != payload.get("decision_receipt")
        or tuple(_persistable_authority(row) for row in reduction.projection.c_active_base)
        != tuple(payload.get("c_active_rows", ()))
        or tuple(_persistable_authority(row) for row in reduction.projection.q_open_base)
        != tuple(payload.get("q_open_rows", ()))
        or not isinstance(typed, Mapping)
        or typed.get("receipt_digest") != authority_digest(typed_body)
        or typed.get("event_stream_digest") != stream.envelope.authority_chain_digest
        or typed.get("lifecycle_projection_digest")
        != reduction.projection.lifecycle_projection_digest
        or len(active_join) != 1
        or typed.get("reason_id") != "counterexample_analysis_safety_unproven"
        or not receipts
        or not all(receipt.get("validated") is True for receipt in receipts)
        or not any(
            receipt.get("disposition") == "sat"
            and "(check-sat)" in receipt.get("formula_text", "")
            for receipt in receipts
        )
        or len(identities) != 2
        or any(
            type(identity) is not str or len(identity) != 64
            for identity in identities
        )
        or tuple(payload.get("binary_sha256", ())) != identities
        or tuple(payload.get("source_sha256", ())) != current_source_hashes
        or tuple(rebuilt_hashes) != identities
        or payload.get("function_pair") != [
            "phase7_sat_witness", "phase7_sat_witness"
        ]
        or not any("(_ bv7 32)" in receipt.get("formula_text", "") for receipt in receipts)
        or not any("(_ bv8 32)" in receipt.get("formula_text", "") for receipt in receipts)
        or payload.get("result_projection") != {
            "is_equivalent": None,
            "error_message": None,
            "reason_ids": ["counterexample_analysis_safety_unproven"],
            "projection_mode": "V2_CANONICAL",
        }
    ):
        raise ValueError("Phase 7 real SAT UNKNOWN authority is incomplete")


def _bound_contract(reason_id: str):
    definition = PROCESS_DURABLE_REASON_REGISTRY.get(reason_id)
    if definition.recovery_addressability is RecoveryAddressability.NO_PROOF_RECOVERY:
        return None
    allowed = definition.allowed_proof_kinds
    candidates = []
    for contract in PROCESS_DURABLE_RECOVERY_REGISTRY.snapshot():
        slot_union = frozenset().union(*(
            slot.allowed_proof_kinds for slot in contract.requirement_slots
        ))
        if slot_union == allowed and all(
            slot.allowed_proof_kinds & allowed for slot in contract.requirement_slots
        ):
            candidates.append(contract)
    if len(candidates) != 1:
        raise ValueError(f"reason does not select one exact recovery contract: {reason_id}")
    contract = candidates[0]
    bindings = {
        slot.name: ProofRequirement(
            "phase7-q-" + authority_digest({
                "reason_id": reason_id,
                "contract": contract.contract_definition_id,
                "slot": slot.name,
            })[:32],
            min(slot.allowed_proof_kinds & allowed),
            ("phase7-semantic-target", reason_id, slot.name),
        )
        for slot in contract.requirement_slots
    }
    return SatisfactionBindingFactory(PROCESS_DURABLE_RECOVERY_REGISTRY).bind(
        contract_definition_id=contract.contract_definition_id,
        contract_version=contract.contract_version,
        bindings=bindings,
    )


def _occurrence(
    reason_id: str, scope: IdentityScope, source_snapshot: str, attempt_id: str,
):
    definition = PROCESS_DURABLE_REASON_REGISTRY.get(reason_id)
    target_kind = min(definition.allowed_target_kinds)
    cause = SemanticCauseIdentityFactory(PROCESS_DURABLE_REASON_REGISTRY).create(
        reason_id=reason_id,
        identity_scope=scope,
        target_kind=target_kind,
        canonical_target_key=("phase7-target", reason_id),
        missing_semantic_fact=("phase7-missing-fact", reason_id),
        semantic_proposition=("phase7-proposition", reason_id),
        observation_surface=("phase7-production-cutover",),
        active_semantic_precondition=("representative_activation", True),
        correspondence_contract=("phase7-ordered-domain-contract",),
    )
    bound = _bound_contract(reason_id)
    occurrence_id = "phase7-occ-" + authority_digest({
        "reason_id": reason_id, "cause_id": cause.value,
    })[:32]
    occurrence = CauseOccurrence(
        occurrence_id, cause, reason_id,
        authority_digest(("phase7-target", reason_id)), target_kind, scope,
        bound.contract_definition_id if bound else None,
        bound.contract_version if bound else None,
        bound.normalized_expression_digest if bound else None,
        bound.bound_expression_digest if bound else None,
        tuple(item.requirement_id for _, item in bound.slot_bindings) if bound else (),
        ("phase7-production-representative",), "typed_phase7_cutover",
        source_snapshot, "phase7-cutover-validator", attempt_id,
    )
    return CauseOccurrenceAuthority(occurrence, bound)


def build_phase7_cutover_validation(repo_root: Path) -> Mapping[str, Any]:
    root = Path(repo_root).resolve()
    inventory = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/retired-reference-inventory.json"
    )).read_text(encoding="utf-8"))
    legacy = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/legacy-baseline-manifest.json"
    )).read_text(encoding="utf-8"))
    producer_manifest = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    timeout_path = root / (
        "artifacts/unknown_taxonomy_v2/phase7/real-process-timeout.json"
    )
    timeout_xml_path = root / (
        "artifacts/unknown_taxonomy_v2/phase7/real-process-timeout.xml"
    )
    no_live_requirement_xml_path = root / (
        "artifacts/unknown_taxonomy_v2/phase7/"
        "real-process-timeout-no-live-requirement.xml"
    )
    sat_path = root / (
        "artifacts/unknown_taxonomy_v2/phase7/real-sat-unknown.json"
    )
    sat_xml_path = root / (
        "artifacts/unknown_taxonomy_v2/phase7/real-sat-unknown.xml"
    )
    cross_slice_path = root / (
        "artifacts/unknown_taxonomy_v2/phase7/phase7-cross-slice-validation-sources.json"
    )
    cross_slice = json.loads(cross_slice_path.read_text(encoding="utf-8"))
    _verify_cross_slice_validation_source_map(root, cross_slice)
    _require_passing_junit(
        timeout_xml_path,
        "test_deadline_with_exact_durable_active_checkpoint_is_timeout",
    )
    _require_passing_junit(
        sat_xml_path,
        "test_real_solver_checker_unknown_uses_all_site_activation_census",
    )
    _require_passing_junit(
        no_live_requirement_xml_path,
        "test_deadline_without_active_checkpoint_is_error_not_timeout",
    )
    real_timeout = json.loads(timeout_path.read_text(encoding="utf-8"))
    real_sat = json.loads(sat_path.read_text(encoding="utf-8"))
    _verify_real_sat_authority(real_sat, producer_manifest, root)
    timeout_body = {
        key: value for key, value in real_timeout.items() if key != "artifact_digest"
    }
    if (
        real_timeout.get("artifact_digest") != authority_digest(timeout_body)
        or real_timeout.get("final_outcome") != "TIMEOUT"
        or real_timeout.get("active_cause_count", 0) < 1
        or real_timeout.get("open_requirement_count", 0) < 1
        or real_timeout.get("terminal_timeout_event_count") != 1
        or real_timeout.get("timeout_derived_reason_count") != 0
        or real_timeout.get("v2_native_typed_cause_coverage") != 1.0
        or not real_timeout.get("typed_projection_receipt_digest")
        or not real_timeout.get("runtime_activation_ledger_digest")
        or real_timeout.get("typed_projection_lifecycle_projection_digest")
        != real_timeout.get("lifecycle_projection_digest")
        or real_timeout.get("typed_projection_active_cause_join_count") != 1
        or real_timeout.get("typed_projection_reason_id")
        != "function_decompilation_artifact_unavailable"
        or real_timeout.get("static_producer_site_count")
        != producer_manifest.get("site_count")
        or real_timeout.get("expected_activation_count") != 1
        or real_timeout.get("runtime_activation_count") != 1
        or real_timeout.get("discovered_activation_count") != 1
        or real_timeout.get("not_reached_activation_count") != 0
    ):
        raise ValueError("Phase 7 real process TIMEOUT authority is incomplete")
    _verify_real_timeout_authority(real_timeout)
    if inventory["production_umbrella_generation"] != 0:
        raise ValueError("Phase 7 production umbrella generation is not zero")
    if inventory["production_umbrella_routing"] != 0:
        raise ValueError("Phase 7 production umbrella routing is not zero")
    if legacy["entry_count"] != 411:
        raise ValueError("Phase 7 legacy baseline is not the ordered 411 census")
    runtime_coverage = {
        "eligible_cause_slot_count": 2,
        "covered_cause_slot_count": 2,
        "v2_native_typed_cause_coverage": 1.0,
        "audited_site_count": producer_manifest["site_count"],
        "run_count": 2,
        "expected_activation_count": (
            real_sat["expected_activation_count"]
            + real_timeout["expected_activation_count"]
        ),
        "runtime_activation_count": (
            real_sat["runtime_activation_count"]
            + real_timeout["runtime_activation_count"]
        ),
        "not_reached_activation_count": (
            real_sat["not_reached_activation_count"]
            + real_timeout["not_reached_activation_count"]
        ),
        "selected_activation_count": 2,
        "manifest_runtime_conservation": (
            real_sat["expected_activation_count"]
            == real_sat["runtime_activation_count"] == 1
            and real_timeout["expected_activation_count"]
            == real_timeout["runtime_activation_count"] == 1
            and real_sat["static_producer_site_count"]
            == real_timeout["static_producer_site_count"]
            == producer_manifest["site_count"]
        ),
        "activated_domains": {
            "operational_extraction": {
                "eligible_cause_slot_count": 1,
                "covered_cause_slot_count": 1,
                "coverage": real_timeout["v2_native_typed_cause_coverage"],
            },
            "sat_safety": {
                "eligible_cause_slot_count": 1,
                "covered_cause_slot_count": 1,
                "coverage": 1.0,
            },
        },
    }

    source_rows = tuple((path, _sha256(root / path)) for *_prefix, path in _DOMAIN_ROWS)
    source_snapshot = authority_digest({"phase7_production_sources": source_rows})
    sites = []
    expected = []
    for index, (domain, reason_id, scope, path) in enumerate(_DOMAIN_ROWS, 1):
        definition = PROCESS_DURABLE_REASON_REGISTRY.get(reason_id)
        site_id = f"phase7-site-{index}"
        slot_id = f"phase7-slot-{index}"
        sites.append(ProducerSiteContract(
            site_id, _sha256(root / path), domain,
            frozenset((ActivationDisposition.ELIGIBLE,)),
            (ExpectedCauseSlotContract(
                slot_id, frozenset((reason_id,)), domain,
                min(definition.allowed_target_kinds), scope.value,
            ),),
        ))
        expected.append(ExpectedActivationContract(
            f"phase7-activation-{index}", site_id, f"phase7-branch-{index}",
            "phase7-cutover-validator", ActivationDisposition.ELIGIBLE,
        ))

    site_registry = SealedProducerSiteRegistry(tuple(sites))
    expected_factory = ExpectedActivationLedgerFactory(
        site_registry, ledger_id="phase7-expected-ledger",
        result_occurrence_id="phase7-result-1", expected=tuple(expected),
    )
    activation_factory = expected_factory.open_runtime_ledger()
    for authority in expected_factory.ledger.authorities:
        activation_factory.record(authority)
    activation_ledger = activation_factory.seal()

    finalization_factory = VerifiedFinalizationBundleFactory(
        PROCESS_DURABLE_REASON_REGISTRY, PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    recorder = finalization_factory.open_recorder(
        stream_id="phase7-production-stream",
        result_occurrence_id="phase7-result-1",
        source_snapshot_fingerprint=source_snapshot,
    )
    bindings = []
    for index, ((_, reason_id, scope, _), activation) in enumerate(
        zip(_DOMAIN_ROWS, activation_ledger.receipts), 1
    ):
        occurrence = _occurrence(
            reason_id, scope, source_snapshot, f"phase7-branch-{index}"
        )
        binding = activation_factory.bind_emission(
            activation=activation, expected_cause_slot_id=f"phase7-slot-{index}",
            occurrence_authority=occurrence,
        )
        finalization_factory.append_cause_observed(
            recorder=recorder, emission_binding=binding,
            activation_factory=activation_factory,
        )
        bindings.append((activation, binding))
    bundle = finalization_factory.issue(recorder)
    projection_factory = activation_factory.open_projection_factory(
        finalization_factory
    )
    projections = []
    for index, (activation, binding) in enumerate(bindings, 1):
        projections.append(projection_factory.issue(
            activation=activation,
            expected_cause_slot_id=f"phase7-slot-{index}", bundle=bundle,
            emission_binding=binding,
            emitted_cause=finalization_factory.emitted_for(binding),
        ))
    coverage = typed_cause_coverage(
        activation_ledger, activation_factory, projection_factory, projections,
    )
    if coverage["eligible_cause_slot_count"] == 0 or (
        coverage["v2_native_typed_cause_coverage"] != 1.0
    ):
        raise ValueError("Phase 7 typed production coverage is incomplete")

    body = {
        "manifest_kind": VALIDATION_KIND,
        "status": "phase7_integration_validation_pending_fixed_review",
        "validator_source_sha256": _sha256(Path(__file__)),
        "source_rows": source_rows,
        "source_snapshot_fingerprint": source_snapshot,
        "site_registry_digest": site_registry.registry_digest,
        "expected_activation_ledger_digest": expected_factory.ledger.ledger_digest,
        "runtime_activation_ledger_digest": activation_ledger.ledger_digest,
        "inventory_manifest_digest": inventory["manifest_digest"],
        "legacy_manifest_digest": legacy["manifest_digest"],
        "producer_site_manifest_digest": producer_manifest["manifest_digest"],
        "production_umbrella_generation": 0,
        "production_umbrella_routing": 0,
        "legacy_entry_count": 411,
        "fixture_domains": tuple(row[0] for row in _DOMAIN_ROWS),
        "contract_fixture_coverage": coverage,
        "production_runtime_coverage": runtime_coverage,
        "active_cause_count": len(bundle.lifecycle_projection.c_active_base),
        "open_requirement_count": len(bundle.lifecycle_projection.q_open_base),
        "event_stream_digest": bundle.sealed_event_stream.envelope.authority_chain_digest,
        "semantic_projection_digest": bundle.lifecycle_projection.semantic_cause_projection_digest,
        "lifecycle_projection_digest": bundle.lifecycle_projection.lifecycle_projection_digest,
        "projection_receipt_digests": tuple(item.receipt_digest for item in projections),
        "production_runtime_unknown": {
            **real_sat,
            "junit_sha256": _sha256(sat_xml_path),
            "test_source_sha256": _sha256(root / (
                "scripts/function_tracer_pcode/tests/unit/"
                "test_unknown_taxonomy_v2_phase7_cutover.py"
            )),
        },
        "production_runtime_timeout": {
            **real_timeout,
            "junit_sha256": _sha256(timeout_xml_path),
            "process_supervisor_source_sha256": _sha256(root / (
                "scripts/function_tracer_pcode/equivalence/v2/"
                "process_supervisor_command.py"
            )),
            "process_supervisor_test_source_sha256": _sha256(root / (
                "scripts/function_tracer_pcode/tests/unit/"
                "test_unknown_taxonomy_v2_phase6_process_supervisor_command.py"
            )),
        },
        "production_runtime_timeout_negative": {
            "expected_outcome": "ERROR",
            "forbidden_outcome": "TIMEOUT",
            "precondition": "no durable ACTIVE checkpoint and no live requirement",
            "test_name": (
                "test_deadline_without_active_checkpoint_is_error_not_timeout"
            ),
            "junit_sha256": _sha256(no_live_requirement_xml_path),
        },
        "cross_slice_validation": cross_slice,
    }
    return {**body, "artifact_digest": authority_digest(body)}


def validate_phase7_cutover_validation(
    repo_root: Path, payload: Mapping[str, Any],
) -> None:
    expected = build_phase7_cutover_validation(repo_root)
    json_expected = json.loads(json.dumps(expected, sort_keys=True))
    if payload != json_expected:
        raise ValueError("Phase 7 cutover validation artifact drifted")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--output", required=True)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args(argv)
    if args.validate:
        payload = json.loads(Path(args.output).read_text(encoding="utf-8"))
        validate_phase7_cutover_validation(Path(args.repo_root), payload)
        print(args.output)
        return 0
    payload = build_phase7_cutover_validation(Path(args.repo_root))
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
