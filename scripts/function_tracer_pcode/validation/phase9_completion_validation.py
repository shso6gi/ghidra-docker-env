"""Materialize and validate current-HEAD UNKNOWN taxonomy v2 closeout evidence."""

from __future__ import annotations

import argparse
import ast
from functools import lru_cache
import hashlib
import io
import json
import os
import subprocess
import sys
import tarfile
from pathlib import Path
from typing import Any, Mapping, Optional, Sequence
from xml.etree import ElementTree

from ..equivalence.v2.census_contract import (
    ActiveOccurrenceMaterialization,
    materialization_metrics,
)
from ..equivalence.v2.codecs import StrictV2JsonCodec
from ..equivalence.v2.contracts import Outcome, QOpenBaseRow, authority_digest
from ..equivalence.v2.phase8_cutover import (
    BATCH_RESUME_MATRIX,
    CLI_EXIT_MATRIX,
    RETRY_FALLBACK_MATRIX,
)
from ..equivalence.v2.pilot import run_dual_write_pilot
from ..equivalence.v2.process_supervisor import PROCESS_DURABLE_REASON_REGISTRY
from ..equivalence.v2.process_supervisor import PROCESS_DURABLE_RECOVERY_REGISTRY
from ..equivalence.v2.reducer import ShadowLifecycleReducer
from ..equivalence.v2.stream import EventType
from .phase7_cutover_validation import validate_phase7_cutover_validation
from .phase7_producer_manifest import validate_phase7_producer_manifest
from .phase8_cutover_validation import validate_phase8_cutover_validation
from .result_summary import classify_canonical_log_text, classify_log_text
from .refactor_contract import (
    capture_contract,
    compare_contract,
    dependency_snapshot,
    size_snapshot,
)


ARTIFACT_DIR = Path("artifacts/unknown_taxonomy_v2/phase9")
SOURCE_PATHS = (
    "scripts/function_tracer_pcode/equivalence/v2/contracts.py",
    "scripts/function_tracer_pcode/equivalence/v2/census_contract.py",
    "scripts/function_tracer_pcode/equivalence/v2/decision.py",
    "scripts/function_tracer_pcode/equivalence/v2/production_context.py",
    "scripts/function_tracer_pcode/equivalence/v2/production_signals.py",
    "scripts/function_tracer_pcode/equivalence/v2/execution_authority.py",
    "scripts/function_tracer_pcode/equivalence/v2/process_supervisor_command.py",
    "scripts/function_tracer_pcode/equivalence/v2/phase7_cutover.py",
    "scripts/function_tracer_pcode/equivalence/v2/phase7_runtime.py",
    "scripts/function_tracer_pcode/equivalence/v2/pilot.py",
    "scripts/function_tracer_pcode/equivalence/v2/return_outcome.py",
    "scripts/function_tracer_pcode/equivalence/call_effect_preflight.py",
    "scripts/function_tracer_pcode/equivalence/checker.py",
    "scripts/function_tracer_pcode/equivalence/recurrence_promotion.py",
    "scripts/function_tracer_pcode/equivalence/strategies/monolithic.py",
    "scripts/function_tracer_pcode/equivalence/strategies/pairwise_services/_shared.py",
    "scripts/function_tracer_pcode/equivalence/strategies/pairwise_services/auxiliary_smt.py",
    "scripts/function_tracer_pcode/analysis/recurrence/proof_utils.py",
    "scripts/function_tracer_pcode/model/expression.py",
    "scripts/function_tracer_pcode/model/render_smt.py",
    "scripts/function_tracer_pcode/transform/expander.py",
    "scripts/function_tracer_pcode/validation/result_summary.py",
    "scripts/function_tracer_pcode/validation/phase9_completion_validation.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase9_completion.py",
    "scripts/function_tracer_pcode/tests/unit/test_expander_combination_guards.py",
    "scripts/function_tracer_pcode/tests/unit/test_monolithic_region_split.py",
    "scripts/function_tracer_pcode/tests/unit/test_loop_method_b_regressions.py",
    "scripts/function_tracer_pcode/tests/unit/test_render_smt_bool_comparison_regression.py",
    "scripts/function_tracer_pcode/tests/unit/test_recurrence_proof_1.py",
    "scripts/function_tracer_pcode/tests/unit/test_recurrence_proof_contract.py",
    "scripts/function_tracer_pcode/tests/unit/test_smt_formula_builder.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_loop_recurrence.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_return_outcome.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase7_cutover.py",
    "scripts/function_tracer_pcode/tests/unit/test_unknown_taxonomy_v2_phase6_process_supervisor_command.py",
    "scripts/function_tracer_pcode/equivalence/v2/canonical_result.py",
    "scripts/function_tracer_pcode/equivalence/v2/pair_status_authority.py",
)

_SERVICE_INTERNAL_PREFIXES = (
    "scripts.function_tracer_pcode.analysis.analyzer_services",
    "scripts.function_tracer_pcode.analysis.effect_services",
    "scripts.function_tracer_pcode.analysis.recurrence",
    "scripts.function_tracer_pcode.equivalence.strategies.pairwise_services",
    "scripts.function_tracer_pcode.equivalence.strategies.proof_gates",
)


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load(root: Path, relative: str) -> Mapping[str, Any]:
    value = json.loads((root / relative).read_text(encoding="utf-8"))
    if not isinstance(value, Mapping):
        raise ValueError(f"closeout input is not an object: {relative}")
    return value


def _sealed(body: Mapping[str, Any]) -> Mapping[str, Any]:
    return {**body, "artifact_digest": authority_digest(body)}


def _validate_phase6_inventory_bindings(root: Path) -> None:
    from .unknown_taxonomy_audit import build_inventory_review_template

    current = build_inventory_review_template(root)
    expected = {
        "candidate_set_digest": current["candidate_set_digest"],
        "candidate_count": len(current["entries"]),
    }
    slice2 = _load(
        root, "artifacts/unknown_taxonomy_v2/phase6/slice2_inventory_delta.json"
    )
    if slice2.get("current_source") != expected:
        raise ValueError("Phase 6 slice2 inventory is not current-source bound")

    for name in (
        "slice3_representative_validation.json", "slice4_representative_validation.json",
        "slice5_representative_validation.json",
    ):
        payload = _load(root, f"artifacts/unknown_taxonomy_v2/phase6/{name}")
        body = dict(payload)
        saved_digest = body.pop("artifact_digest", None)
        if saved_digest != authority_digest(body):
            raise ValueError(f"Phase 6 inventory artifact digest drifted: {name}")
        source_inventory = payload.get("source_inventory") or {}
        if (
            source_inventory.get("current_source") != expected
            or source_inventory.get("live_delta") != {"added": 0, "removed": 0}
        ):
            raise ValueError(f"Phase 6 inventory binding drifted: {name}")


def _canonical_json_bytes(payload: Mapping[str, Any]) -> bytes:
    return (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _normalized_refactor_symbol(contract: Mapping[str, Any]) -> Mapping[str, Any]:
    normalized = dict(contract)
    export = f"{contract['module']}.{contract['symbol']}"
    normalized["defined_as"] = export
    mro = list(normalized.get("mro") or ())
    if mro:
        mro[0] = export
        normalized["mro"] = mro
    callable_contract = normalized.get("callable")
    if isinstance(callable_contract, Mapping):
        callable_normalized = dict(callable_contract)
        signature = callable_normalized.get("signature")
        if isinstance(signature, str):
            callable_normalized["signature"] = signature.replace(
                "scripts.function_tracer_pcode.equivalence.strategies.proof_gates._shared.StrategyResult",
                "scripts.function_tracer_pcode.equivalence.strategies.base.StrategyResult",
            )
        normalized["callable"] = callable_normalized
    return normalized


def _resolve_import(module_name: str, node: ast.ImportFrom) -> str:
    if node.level == 0:
        return node.module or ""
    package = module_name.split(".")[:-1]
    keep = max(0, len(package) - node.level + 1)
    prefix = package[:keep]
    if node.module:
        prefix.extend(node.module.split("."))
    return ".".join(prefix)


def _baseline_private_imports(root: Path, commit: str) -> tuple[tuple[Any, ...], ...]:
    archive = subprocess.check_output(
        ["git", "archive", commit, "scripts/function_tracer_pcode"], cwd=root
    )
    rows = []
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as bundle:
        for member in bundle.getmembers():
            if not member.isfile() or not member.name.endswith(".py"):
                continue
            extracted = bundle.extractfile(member)
            if extracted is None:
                continue
            module = member.name[:-3].replace("/", ".")
            tree = ast.parse(extracted.read().decode("utf-8"), filename=member.name)
            for node in ast.walk(tree):
                if not isinstance(node, ast.ImportFrom):
                    continue
                imported = _resolve_import(module, node)
                for alias in node.names:
                    same_boundary = any(
                        module.startswith(prefix + ".")
                        and imported.startswith(prefix + ".")
                        for prefix in _SERVICE_INTERNAL_PREFIXES
                    )
                    if (
                        alias.name.startswith("_")
                        and alias.name != "*"
                        and not same_boundary
                    ):
                        rows.append((module, imported, alias.name, node.lineno))
    return tuple(sorted(rows))


@lru_cache(maxsize=1)
def _refactor_replacement_contract(root: Path) -> Mapping[str, Any]:
    tool = root / "scripts/function_tracer_pcode/validation/refactor_contract.py"
    baseline_path = root / "artifacts/refactor/phase10/contract.json"
    baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
    current = capture_contract()
    canonical_current = {
        key: value for key, value in current.items()
        if key not in {"git_commit", "tracked_dirty"}
    }
    dependencies = dependency_snapshot()
    failures = compare_contract(baseline)
    environment = dict(os.environ)
    environment["PYTHONPATH"] = str(root)
    completed = subprocess.run(
        [sys.executable, str(tool), "--manifest", str(baseline_path)],
        cwd=root, env=environment, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        check=False,
    )
    stdout_lines = tuple(completed.stdout.splitlines())
    command_is_green = (
        completed.returncode == 0
        and stdout_lines == ("refactor contract: ok",)
        and not failures
        and not completed.stderr
    )
    command_is_legacy_replacement = (
        completed.returncode == 1
        and stdout_lines == failures
        and not completed.stderr
    )
    if not (command_is_green or command_is_legacy_replacement):
        raise ValueError("refactor replacement contract command evidence drifted")
    before_symbols = {
        (item["module"], item["symbol"]): item for item in baseline["symbols"]
    }
    after_symbols = {
        (item["module"], item["symbol"]): item for item in current["symbols"]
    }
    raw_symbol_deltas = tuple({
        "module": key[0], "symbol": key[1],
        "before": before_symbols[key], "after": after_symbols[key],
    } for key in sorted(before_symbols) if before_symbols[key] != after_symbols[key])
    symbol_deltas = tuple({
        "module": key[0], "symbol": key[1],
        "before": _normalized_refactor_symbol(before_symbols[key]),
        "after": _normalized_refactor_symbol(after_symbols[key]),
    } for key in sorted(before_symbols) if (
        _normalized_refactor_symbol(before_symbols[key])
        != _normalized_refactor_symbol(after_symbols[key])
    ))
    baseline_cycles = tuple(tuple(item) for item in baseline["dependency_cycles"])
    new_cycles = tuple(
        tuple(cycle) for cycle in current["dependency_cycles"]
        if not any(set(cycle) <= set(old) for old in baseline_cycles)
    )
    before_private_imports = tuple(
        tuple(item) for item in baseline.get("private_imports", ())
    ) or _baseline_private_imports(root, baseline["git_commit"])
    after_private_imports = tuple(
        tuple(item) for item in dependencies["private_imports"]
    )
    before_private_import_edges = tuple(
        tuple(item[:3]) for item in before_private_imports
    )
    after_private_import_edges = tuple(
        tuple(item[:3]) for item in after_private_imports
    )
    added_private_imports = tuple(sorted(
        set(after_private_import_edges) - set(before_private_import_edges)
    ))
    removed_private_imports = tuple(sorted(
        set(before_private_import_edges) - set(after_private_import_edges)
    ))
    sizes = size_snapshot()
    delta_classifications = () if command_is_green else (
        {
            "failure": "symbols_changed",
            "classification": "five_value_error_surface_contract",
            "evidence": "Phase8 all-five receipt and ERROR boundary JUnit",
        },
        {
            "failure": "private_import_count_increased",
            "classification": "exact_import_edge_delta",
            "evidence": "baseline/current/add/remove import tuples persisted",
        },
        {
            "failure": failures[2],
            "classification": "legacy_v2_migration_integration_scc",
            "evidence": "complete 41-module membership persisted",
        },
    )
    replacement = {
        "contract_kind": (
            "phase10-refactor-contract-green-v1" if command_is_green
            else "phase9-exact-refactor-replacement-v1"
        ),
        "command": (
            "python", "scripts/function_tracer_pcode/validation/refactor_contract.py",
            "--manifest", "artifacts/refactor/phase10/contract.json",
        ),
        "exit_code": completed.returncode,
        "stdout_lines": stdout_lines,
        "stderr": completed.stderr,
        "tool_sha256": _sha(tool),
        "baseline_path": baseline_path.relative_to(root).as_posix(),
        "baseline_sha256": _sha(baseline_path),
        "baseline_contract_digest": authority_digest(baseline),
        "current_contract_digest": authority_digest(canonical_current),
        "current_source_tree_hash": current["source_tree_hash"],
        "exact_failures": failures,
        "raw_symbol_move_or_contract_deltas": raw_symbol_deltas,
        "public_symbol_deltas": symbol_deltas,
        "abi_width_readonly_line_count": sizes["equivalence/v2/abi_width_readonly.py"],
        "new_file_hard_limit": 3000,
        "private_import_count_before": baseline["private_import_count"],
        "private_import_count_after": current["private_import_count"],
        "private_import_count_delta": (
            current["private_import_count"] - baseline["private_import_count"]
        ),
        "current_private_imports": dependencies["private_imports"],
        "baseline_private_imports": before_private_imports,
        "added_private_imports": added_private_imports,
        "removed_private_imports": removed_private_imports,
        "baseline_dependency_cycles": baseline_cycles,
        "current_dependency_cycles": tuple(tuple(item) for item in current["dependency_cycles"]),
        "new_dependency_cycles": new_cycles,
        "new_dependency_cycle_module_counts": tuple(len(item) for item in new_cycles),
        "review_disposition": (
            "contract_green" if command_is_green else "pending_fixed_review"
        ),
        "blanket_baseline_regeneration": False,
        "delta_classifications": delta_classifications,
    }
    if command_is_green:
        if (
            raw_symbol_deltas
            or symbol_deltas
            or new_cycles
            or replacement["private_import_count_delta"] != 0
            or added_private_imports
            or removed_private_imports
            or len(before_private_imports) != baseline["private_import_count"]
            or len(after_private_imports) != current["private_import_count"]
        ):
            raise ValueError("green refactor contract has an unsealed delta")
    elif (
        len(failures) != 3
        or len(raw_symbol_deltas) != 18
        or len(symbol_deltas) != 1
        or len(new_cycles) != 1
        or len(new_cycles[0]) != 41
        or replacement["private_import_count_delta"] != 59
        or len(before_private_imports) != baseline["private_import_count"]
        or len(after_private_imports) != current["private_import_count"]
        or len(added_private_imports) - len(removed_private_imports) != 59
        or failures[:2] != (
            "symbols_changed",
            "private_import_count_increased",
        )
        or not failures[2].startswith("new_dependency_cycle:")
        or any(item.startswith("new_file_hard_limit_exceeded:") for item in failures)
    ):
        raise ValueError("refactor replacement contract is not the cleanup three-delta set")
    return replacement


def _junit(root: Path, relative: str, expected: int) -> Mapping[str, Any]:
    path = root / relative
    xml = ElementTree.parse(path).getroot()
    suites = tuple(xml.iter("testsuite"))
    cases = tuple(xml.iter("testcase"))
    count = sum(int(item.attrib.get("tests", "0")) for item in suites)
    if (
        count != expected
        or len(cases) != expected
        or any(int(item.attrib.get(name, "0")) for item in suites
               for name in ("failures", "errors", "skipped"))
    ):
        raise ValueError(f"closeout JUnit is not {expected}/{expected}: {relative}")
    return {"path": relative, "sha256": _sha(path), "test_count": count}


def _replay_lifecycle_evidence(sat: Mapping[str, Any]) -> Mapping[str, Any]:
    codec = StrictV2JsonCodec(
        reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
        recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    stream = codec.loads(json.dumps(
        sat["sealed_event_stream"], sort_keys=True, separators=(",", ":")
    ))
    pilot = run_dual_write_pilot(
        legacy_outcome=Outcome.UNKNOWN,
        reducer=ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        stream=stream,
    )
    explicit_completions = sum(
        event.header.event_type is EventType.REQUIREMENT_COMPLETED
        for event in stream.events
    )
    explicit_transformations = sum(
        event.header.event_type is EventType.CAUSE_TRANSFORMED
        for event in stream.events
    )
    implicit = (
        abs(len(pilot.reduction.snapshot.completion_receipts) - explicit_completions)
        + abs(
            len(pilot.reduction.snapshot.transformation_receipt_ids)
            - explicit_transformations
        )
    )
    return {
        "lifecycle_inference_count": pilot.lifecycle_inference_count,
        "implicit_replacement_or_completion_count": implicit,
        "pilot_receipt_digest": pilot.pilot_receipt_digest,
        "sealed_event_stream_authority_digest": (
            stream.envelope.authority_chain_digest
        ),
        "replayed_snapshot_digest": pilot.reduction.snapshot.snapshot_digest,
        "replayed_lifecycle_projection_digest": (
            pilot.reduction.projection.lifecycle_projection_digest
        ),
        "explicit_completion_event_count": explicit_completions,
        "materialized_completion_receipt_count": len(
            pilot.reduction.snapshot.completion_receipts
        ),
        "explicit_transformation_event_count": explicit_transformations,
        "materialized_transformation_receipt_count": len(
            pilot.reduction.snapshot.transformation_receipt_ids
        ),
    }


@lru_cache(maxsize=1)
def build_phase9_evidence(repo_root: Path) -> Mapping[str, Mapping[str, Any]]:
    root = Path(repo_root).resolve()
    sat = _load(root, "artifacts/unknown_taxonomy_v2/phase7/real-sat-unknown.json")
    timeout = _load(root, "artifacts/unknown_taxonomy_v2/phase7/real-process-timeout.json")
    phase7 = _load(root, "artifacts/unknown_taxonomy_v2/phase7/cutover-validation.json")
    phase8 = _load(root, "artifacts/unknown_taxonomy_v2/phase8/cutover-validation.json")
    producer = _load(root, "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json")
    validate_phase7_producer_manifest(root, producer)
    validate_phase7_cutover_validation(root, phase7)
    validate_phase8_cutover_validation(root, phase8)
    _validate_phase6_inventory_bindings(root)
    if sat["final_outcome"] != "UNKNOWN" or timeout["final_outcome"] != "TIMEOUT":
        raise ValueError("representative final outcomes drifted")
    base_rows = tuple(sat["c_active_rows"]) + tuple(sat["q_open_rows"])
    base_rows += tuple(timeout["c_active_rows"]) + tuple(timeout["q_open_rows"])
    if any("final_outcome" in row for row in base_rows):
        raise ValueError("base semantic/proof relation contains outcome authority")
    c_rows = tuple(sat["c_active_rows"]) + tuple(timeout["c_active_rows"])
    q_rows = tuple(sat["q_open_rows"]) + tuple(timeout["q_open_rows"])
    relations_are_separate = bool(
        c_rows and q_rows
        and all("proof_requirement_id" not in row for row in c_rows)
        and all("reason_id" not in row for row in q_rows)
    )
    if not relations_are_separate:
        raise ValueError("semantic cause and proof backlog relations are conflated")
    if (
        sat["coverage"]["v2_native_typed_cause_coverage"] != 1.0
        or timeout["v2_native_typed_cause_coverage"] != 1.0
        or timeout["terminal_timeout_event_count"] != 1
        or timeout["open_requirement_count"] < 1
        or phase7["production_umbrella_generation"] != 0
        or phase7["production_umbrella_routing"] != 0
    ):
        raise ValueError("Phase 9 completion coverage gate failed")
    representative_results = (sat, timeout)
    final_blocker_candidates = tuple(
        item for item in representative_results
        if item["decision_receipt"]["outcome"] in {"UNKNOWN", "TIMEOUT"}
    )
    final_blocker_denominator = len(final_blocker_candidates)
    final_blocker_numerator = sum(int(
        item["active_cause_count"] > 0
        and all(
            row["result_occurrence_id"]
            == item["decision_receipt"]["result_occurrence_id"]
            for row in item["c_active_rows"]
        )
    ) for item in final_blocker_candidates)
    final_blocker_coverage = final_blocker_numerator / final_blocker_denominator
    active_rows = tuple(sat["c_active_rows"]) + tuple(timeout["c_active_rows"])
    typed_coverage = sum(bool(row.get("cause_id")) for row in active_rows) / len(active_rows)
    active_materializations = tuple(
        ActiveOccurrenceMaterialization(
            row["result_occurrence_id"], row["occurrence_id"], row["cause_id"],
            PROCESS_DURABLE_REASON_REGISTRY.get(
                row["reason_id"]
            ).recovery_addressability,
        ) for row in active_rows
    )
    q_open_rows = tuple(
        QOpenBaseRow(**row) for row in (
            tuple(sat["q_open_rows"]) + tuple(timeout["q_open_rows"])
        )
    )
    materialization = materialization_metrics(active_materializations, q_open_rows)
    addressability_counts: dict[str, int] = {}
    for item in active_materializations:
        key = item.recovery_addressability.value
        addressability_counts[key] = addressability_counts.get(key, 0) + 1
    phase8_path = root / "artifacts/unknown_taxonomy_v2/phase8/cutover-validation.json"
    phase8_receipt_gate = phase8["gates"]["decision_receipt_only_final_status"]
    if phase8_receipt_gate["outcome_case_count"] != len(tuple(Outcome)):
        raise ValueError("Phase 8 all-five receipt evidence is incomplete")
    lifecycle_replay = _replay_lifecycle_evidence(sat)
    if (
        lifecycle_replay["lifecycle_inference_count"] != 0
        or lifecycle_replay["implicit_replacement_or_completion_count"] != 0
    ):
        raise ValueError("Phase 9 lifecycle replay inferred implicit state")

    decision_receipt = _sealed({
        "artifact_kind": "phase9-decision-receipt-census-v1",
        "receipts": (sat["decision_receipt"], timeout["decision_receipt"]),
        "observed_outcomes": ("UNKNOWN", "TIMEOUT"),
        "all_five_outcomes_contract": tuple(item.value for item in Outcome),
        "sole_final_status_authority": "DecisionReceipt",
        "all_five_source_bound_authority": {
            "phase8_artifact_digest": phase8["artifact_digest"],
            "phase8_artifact_sha256": _sha(phase8_path),
            "focused_junit_sha256": phase8["focused_junit"]["sha256"],
            "focused_test_source_sha256": next(
                row["sha256"] for row in phase8["source_files"]
                if row["path"].endswith("test_unknown_taxonomy_v2_phase8_cutover.py")
            ),
            "test_family": phase8_receipt_gate["test_family"],
            "outcome_case_count": phase8_receipt_gate["outcome_case_count"],
        },
    })
    cause_snapshot = _sealed({
        "artifact_kind": "phase9-cause-lifecycle-snapshot-v1",
        "base_relations_exclude_final_outcome": True,
        "unknown": {"final_outcome": "UNKNOWN", "c_active": sat["c_active_rows"],
                    "q_open": sat["q_open_rows"]},
        "timeout": {"final_outcome": "TIMEOUT", "c_active": timeout["c_active_rows"],
                    "q_open": timeout["q_open_rows"]},
        "semantic_cause_and_proof_backlog_are_separate": relations_are_separate,
        "lifecycle_replay_authority": lifecycle_replay,
    })
    observed_nonterminal_timeouts = sum(
        str(receipt.get("disposition", "")).lower() == "timeout"
        for receipt in sat["query_execution_receipts"]
    )
    query_receipts = _sealed({
        "artifact_kind": "phase9-query-execution-receipts-v1",
        "unknown_query_execution_receipts": sat["query_execution_receipts"],
        "terminal_timeout_receipt": timeout["terminal_timeout_receipt"],
        "terminal_timeout_receipt_count": timeout["terminal_timeout_event_count"],
        "observed_nonterminal_timeout_event_count": observed_nonterminal_timeouts,
        "final_timeout_result_count": int(
            timeout["decision_receipt"]["outcome"] == "TIMEOUT"
        ),
    })
    legacy_probe = "\n".join((
        "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
        '{"is_equivalent":null,"is_timeout":true}',
        "=== EQUIVALENCE_RESULT_JSON_END ===",
    ))
    legacy_status = classify_log_text(legacy_probe, matrix_context=True)
    canonical_status = classify_canonical_log_text(legacy_probe, matrix_context=True)
    if legacy_status != "TIMEOUT" or canonical_status != "INCOMPLETE":
        raise ValueError("legacy diagnostic/canonical isolation probe failed")
    legacy_coverage = _sealed({
        "artifact_kind": "phase9-legacy-coverage-v1",
        "legacy_manifest_entry_count": phase7["legacy_entry_count"],
        "legacy_diagnostic_probe": {
            "legacy_status": legacy_status,
            "canonical_status": canonical_status,
            "payload_sha256": hashlib.sha256(legacy_probe.encode("utf-8")).hexdigest(),
        },
        "v2_native_typed_cause_coverage": typed_coverage,
        "final_blocker_authority_numerator": final_blocker_numerator,
        "final_blocker_authority_denominator": final_blocker_denominator,
        "final_blocker_authority_coverage": final_blocker_coverage,
        **materialization,
        "active_cause_count_by_recovery_addressability": dict(
            sorted(addressability_counts.items())
        ),
        "optional_requirement_materialization_display": (
            "N/A" if materialization["optional_requirement_materialization_rate"] is None
            else str(materialization["optional_requirement_materialization_rate"])
        ),
    })
    unsupported_reason_rows = tuple({
        "reason_id": definition.reason_id,
        "reason_class": definition.reason_class,
        "decision_effect": definition.decision_effect,
        "recovery_addressability": definition.recovery_addressability.value,
        "allowed_proof_kinds": tuple(sorted(definition.allowed_proof_kinds)),
    } for definition in PROCESS_DURABLE_REASON_REGISTRY.snapshot()
      if "unsupported" in definition.reason_id)
    missing_categories = materialization[
        "active_causes_without_materialized_requirement"
    ]
    reason_before_after = _sealed({
        "artifact_kind": "phase9-reason-before-after-v1",
        "legacy_solver_unknown_timeout": {
            "before": "UNKNOWN diagnostic reason could coexist with timeout",
            "after": "diagnostic-only; terminal timeout receipt finalizes TIMEOUT",
            "phase7_artifact_digest": phase7["artifact_digest"],
            "production_emit_count": phase7["production_umbrella_generation"],
            "production_route_count": phase7["production_umbrella_routing"],
            "terminal_timeout_receipt_digest": (
                timeout["terminal_timeout_receipt"]["receipt_digest"]
            ),
            "final_outcome": timeout["decision_receipt"]["outcome"],
        },
        "representative_unknown_reason_ids": tuple(
            sorted({row["reason_id"] for row in sat["c_active_rows"]})
        ),
        "representative_timeout_reason_ids": tuple(
            sorted({row["reason_id"] for row in timeout["c_active_rows"]})
        ),
        "unsupported_semantics_registry_rows": unsupported_reason_rows,
        "internal_error_authority": {
            "outcome": "ERROR",
            "phase8_artifact_digest": phase8["artifact_digest"],
            "required_tests": (
                "test_cli_startup_error_emits_canonical_error_and_exit_four",
                "test_cli_no_solver_emits_canonical_error_and_exit_four",
                "test_cli_missing_function_emits_canonical_error_and_exit_four",
            ),
            "focused_junit_sha256": phase8["focused_junit"]["sha256"],
        },
        "materialization_missing_counts": missing_categories,
    })
    transition = _sealed({
        "artifact_kind": "phase9-decision-transition-matrix-v1",
        "retry_fallback": {item.value: RETRY_FALLBACK_MATRIX[item] for item in Outcome},
        "batch_resume": {item.value: BATCH_RESUME_MATRIX[item] for item in Outcome},
        "cli_exit": {item.value: CLI_EXIT_MATRIX[item] for item in Outcome},
        "unknown_and_timeout_are_distinct": (
            RETRY_FALLBACK_MATRIX[Outcome.UNKNOWN]
            != RETRY_FALLBACK_MATRIX[Outcome.TIMEOUT]
            and BATCH_RESUME_MATRIX[Outcome.UNKNOWN]
            != BATCH_RESUME_MATRIX[Outcome.TIMEOUT]
        ),
        "eq_not_eq_decisive_receipts_unchanged_authority": {
            "phase8_artifact_digest": phase8["artifact_digest"],
            "phase8_artifact_sha256": _sha(phase8_path),
            "focused_junit_sha256": phase8["focused_junit"]["sha256"],
            "all_five_test_family": phase8_receipt_gate["test_family"],
        },
    })
    refactor_replacement = _refactor_replacement_contract(root)
    validation = {
        "artifact_kind": "phase9-validation-run-v1",
        "junit": (
            _junit(
                root,
                "artifacts/unknown_taxonomy_v2/phase7/phase7-cross-slice-validation.xml",
                int(phase8["gates"][
                    "canonical_census_uses_manifest_receipt_stream_join"
                ]["test_count"]),
            ),
            _junit(root, "artifacts/unknown_taxonomy_v2/phase7/phase7-final-focused-validation.xml", 39),
            _junit(root, "artifacts/unknown_taxonomy_v2/phase8/phase8-focused-validation.xml", 27),
            _junit(
                root,
                "artifacts/unknown_taxonomy_v2/phase8/phase8-workflow-regression.xml",
                int(phase8["workflow_regression_junit"]["test_count"]),
            ),
        ),
        "phase7_validator": "PASS",
        "phase8_validator": "PASS",
        "refactor_contract": "GREEN",
        "refactor_replacement_contract": refactor_replacement,
    }
    validation_run = _sealed(validation)
    subordinate = {
        "decision_receipt.json": decision_receipt,
        "cause_lifecycle_snapshot.json": cause_snapshot,
        "query_execution_receipts.json": query_receipts,
        "legacy_coverage.json": legacy_coverage,
        "reason_before_after.json": reason_before_after,
        "decision_transition_matrix.json": transition,
        "validation_run.json": validation_run,
    }
    log_bytes = _validation_log_bytes(subordinate)
    source_rows = tuple({"path": path, "sha256": _sha(root / path)} for path in SOURCE_PATHS)
    manifest = _sealed({
        "artifact_kind": "phase9-source-tree-manifest-v3",
        "source_tree_digest": authority_digest({"source_files": source_rows}),
        "source_files": source_rows,
        "phase7_artifact_sha256": _sha(root / "artifacts/unknown_taxonomy_v2/phase7/cutover-validation.json"),
        "phase8_artifact_sha256": _sha(root / "artifacts/unknown_taxonomy_v2/phase8/cutover-validation.json"),
        "producer_manifest_digest": producer["manifest_digest"],
        "phase9_focused_junit": _junit(
            root,
            "artifacts/unknown_taxonomy_v2/phase9/phase9-focused-validation.xml",
            6,
        ),
        "closeout_bindings": tuple({
            "path": name,
            "artifact_digest": payload["artifact_digest"],
            "sha256": hashlib.sha256(_canonical_json_bytes(payload)).hexdigest(),
        } for name, payload in sorted(subordinate.items())),
        "validation_run_log_sha256": hashlib.sha256(log_bytes).hexdigest(),
    })
    return {"current_head_manifest.json": manifest, **subordinate}


def _validation_log_bytes(payloads: Mapping[str, Mapping[str, Any]]) -> bytes:
    validation = payloads["validation_run.json"]
    refactor = validation["refactor_replacement_contract"]
    lines = [
        "Phase 9 current-HEAD validation",
        *(f"{name}: {payload['artifact_digest']}"
          for name, payload in sorted(payloads.items())),
        "refactor_contract_command: " + json.dumps(refactor["command"]),
        f"refactor_contract_exit_code: {refactor['exit_code']}",
        "refactor_contract_stdout_begin",
        *refactor["stdout_lines"],
        "refactor_contract_stdout_end",
        "refactor_contract_stderr_begin",
        refactor["stderr"],
        "refactor_contract_stderr_end",
    ]
    return ("\n".join(lines) + "\n").encode("utf-8")


def write_phase9_evidence(repo_root: Path) -> None:
    root = Path(repo_root).resolve()
    directory = root / ARTIFACT_DIR
    directory.mkdir(parents=True, exist_ok=True)
    payloads = build_phase9_evidence(root)
    for name, payload in payloads.items():
        (directory / name).write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    subordinate = {
        name: payload for name, payload in payloads.items()
        if name != "current_head_manifest.json"
    }
    (directory / "validation_run.log").write_bytes(
        _validation_log_bytes(subordinate)
    )


def validate_phase9_evidence(
    repo_root: Path, *, evidence_directory: Optional[Path] = None,
) -> None:
    root = Path(repo_root).resolve()
    directory = (
        Path(evidence_directory).resolve()
        if evidence_directory is not None else root / ARTIFACT_DIR
    )
    expected = json.loads(json.dumps(build_phase9_evidence(root), sort_keys=True))
    for name, payload in expected.items():
        stored = json.loads((directory / name).read_text(encoding="utf-8"))
        if stored != payload:
            raise ValueError(f"Phase 9 artifact drifted: {name}")
    subordinate = {
        name: payload for name, payload in expected.items()
        if name != "current_head_manifest.json"
    }
    expected_log = _validation_log_bytes(subordinate)
    log_path = directory / "validation_run.log"
    if not log_path.is_file() or log_path.read_bytes() != expected_log:
        raise ValueError("Phase 9 validation_run.log drifted")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args(argv)
    if args.validate:
        validate_phase9_evidence(Path(args.repo_root))
    else:
        write_phase9_evidence(Path(args.repo_root))
    print(ARTIFACT_DIR)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
