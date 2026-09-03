"""Discover and seal every production v2 signal activation call site."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Optional, Sequence

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
    ABI_WIDTH_READONLY_REASON_SPECS,
)
from scripts.function_tracer_pcode.authority.domains.call_effect import CALL_EFFECT_REASON_SPECS
from scripts.function_tracer_pcode.authority.domains.call_effect_sites import (
    CALL_EFFECT_PROOF_BATCH_SITE,
    CALL_EFFECT_PRODUCER_SITE_SPECS,
)
from scripts.function_tracer_pcode.authority.domains.loop_recurrence import LOOP_REASON_SPECS
from scripts.function_tracer_pcode.authority.process.operational_extraction import (
    OPERATIONAL_REASON_SPECS,
)
from scripts.function_tracer_pcode.authority.process.supervisor import (
    PROCESS_DURABLE_REASON_REGISTRY,
)
from scripts.function_tracer_pcode.authority.domains.return_outcome import (
    OUTCOME_STAGE_REASON_MATRIX,
)
from scripts.function_tracer_pcode.authority.domains.sat_safety_sites import (
    SAT_SAFETY_PRODUCER_SITE_SPECS,
)


EMITTERS = frozenset({
    "emit_outcome_partition_signal",
    "emit_sat_safety_signal",
    "emit_sat_safety_completion_if_observed",
    "emit_call_effect_signal",
    "emit_loop_recurrence_signal",
    "emit_abi_width_readonly_signal",
    "_emit_return_width_signal_once",
    "emit_operational_extraction_signal",
    "emit_comparison_closure_signal",
})

_DOMAIN_BY_EMITTER = {
    "emit_outcome_partition_signal": "return_outcome",
    "emit_sat_safety_signal": "sat_safety",
    "emit_sat_safety_completion_if_observed": "sat_safety",
    "emit_call_effect_signal": "expression_call_effect_memory",
    "emit_loop_recurrence_signal": "loop_recurrence_summary",
    "emit_abi_width_readonly_signal": "return_width",
    "_emit_return_width_signal_once": "return_width",
    "emit_operational_extraction_signal": "operational_extraction",
    "emit_comparison_closure_signal": "comparison_closure",
}

_DOMAIN_BY_SITE_OVERRIDE = {
    "pairwise-readonly-correspondence-member": "readonly_identity",
    "pairwise-readonly-identity-blocker": "readonly_identity",
    "return-width-pair-assessment": "abi",
}

_SEALED_SITE_SPEC_IDS = {
    "CALL_EFFECT_PROOF_BATCH_SITE": CALL_EFFECT_PROOF_BATCH_SITE.site_id,
}

_PRODUCER_IDS_BY_SITE = {
    "call-effect-producer-blocker": (
        "internal_typed_pure_direct_call_stage_producer",
    ),
    "call-effect-producer-prerequisite": (
        "internal_typed_pure_direct_call_stage_producer",
    ),
    **{
        spec.site_id: (spec.producer_id,)
        for spec in CALL_EFFECT_PRODUCER_SITE_SPECS
    },
    "checker-recurrence-proposal-blocker": (
        "typed-recurrence-proposal-signal-v2",
    ),
    "checker-recurrence-validation-completed": (
        "equivalence_recurrence_validator",
    ),
    "pairwise-loop-sat-safety-observed": (
        "loop-model-bound-refutation-handoff-v1",
    ),
    **{
        spec.site_id: (spec.producer_id,)
        for spec in SAT_SAFETY_PRODUCER_SITE_SPECS
    },
    "safe-counterexample-pairwise-production": (
        "safe-counterexample-production-v2",
    ),
    "safe-counterexample-monolithic-production": (
        "safe-counterexample-production-v2",
    ),
    "outcome-partition-stage-result": ("reachable_outcome_producer_v1",),
    "pairwise-loop-fallback-blocker": ("typed-loop-pair-fallback-signal-v2",),
    "pairwise-pending-loop-blocker": ("typed-loop-pair-fallback-signal-v2",),
    "pairwise-loop-term-completed": (
        "loop-exact-term-relation-validator-v2",
    ),
    "pairwise-loop-guard-completed": (
        "loop-exact-guard-partition-validator-v2",
    ),
    "recurrence-summary-loop": (
        "typed-summary-acceptance-signal-v2",
        "typed-summary-candidate-signal-v2",
    ),
    "recurrence-summary-call-effect": (
        "internal_typed_pure_direct_call_stage_producer",
    ),
    "recurrence-summary-abi-width": (
        "typed-summary-width-occurrence-v2",
    ),
    "return-width-unary-provenance-blocker": (
        "typed-return-width-seed-signal-v2",
    ),
    "return-width-pair-unary-provenance-blocker": (
        "typed-return-width-seed-signal-v2",
    ),
    "return-width-observation-contract-blocker": (
        "typed-return-observation-need-signal-v2",
    ),
    "return-width-projection-relation-blocker": (
        "typed-return-observation-signal-v2",
    ),
    "return-width-pair-assessment": (
        "typed-return-abi-fact-seed-v2",
        "typed-return-observation-signal-v2",
        "typed-same-function-width-signal-v2",
    ),
    "pairwise-readonly-identity-blocker": ("typed-readonly-member-signal-v2",),
    "pairwise-readonly-correspondence-member": (
        "typed-readonly-member-signal-v2",
    ),
    "decompilation-broker-operational-signal": (
        "function-decompilation-artifact-producer-v2",
        "function-decompilation-operational-error-producer-v2",
        "high-function-ir-validator-v2",
        "subordinate-parent-authority-producer-v2",
    ),
    "comparison-inconclusive-terminal": ("comparison-closure-producer-v1",),
}

_DISPOSITIONS_BY_SITE = {
    "call-effect-producer-blocker": ("ELIGIBLE",),
    "call-effect-producer-prerequisite": ("ELIGIBLE",),
    **{
        spec.site_id: (spec.disposition,)
        for spec in CALL_EFFECT_PRODUCER_SITE_SPECS
    },
    "checker-recurrence-proposal-blocker": ("ELIGIBLE",),
    "checker-recurrence-validation-completed": ("DECISIVE",),
    "pairwise-loop-sat-safety-observed": ("ELIGIBLE",),
    "decompilation-broker-operational-signal": (
        "DECISIVE", "ELIGIBLE",
    ),
    "outcome-partition-stage-result": ("DECISIVE", "ELIGIBLE"),
    "safe-counterexample-pairwise-production": ("DECISIVE",),
    "safe-counterexample-monolithic-production": ("DECISIVE",),
    "pairwise-loop-fallback-blocker": ("ELIGIBLE",),
    "pairwise-loop-guard-completed": ("DECISIVE",),
    "pairwise-loop-term-completed": ("DECISIVE",),
    "pairwise-pending-loop-blocker": ("ELIGIBLE",),
    "pairwise-readonly-correspondence-member": ("ELIGIBLE",),
    "pairwise-readonly-identity-blocker": ("ELIGIBLE",),
    "recurrence-summary-abi-width": ("ELIGIBLE",),
    "recurrence-summary-call-effect": ("ELIGIBLE",),
    "recurrence-summary-loop": ("ELIGIBLE",),
    "return-width-observation-contract-blocker": ("ELIGIBLE",),
    "return-width-pair-assessment": ("ELIGIBLE",),
    "return-width-projection-relation-blocker": ("ELIGIBLE",),
    "return-width-unary-provenance-blocker": ("ELIGIBLE",),
    "return-width-pair-unary-provenance-blocker": ("ELIGIBLE",),
    **{
        spec.site_id: (spec.disposition,)
        for spec in SAT_SAFETY_PRODUCER_SITE_SPECS
    },
    "comparison-inconclusive-terminal": ("ELIGIBLE",),
}


# Reviewed producer-site ownership.  Each tuple is an alternative reason choice
# for one wrapper activation, never a set of mandatory causes.  A new reason or
# site must update this table explicitly; domain-wide registry expansion is
# forbidden.
_CAUSE_REASON_IDS_BY_SITE = {
    "comparison-inconclusive-terminal": (
        "comparison_equivalence_closure_unproven",
    ),
    "call-effect-producer-blocker": ("pure_call_semantics_unproven",),
    "call-effect-producer-prerequisite": (
        "abi_argument_relation_unproven",
        "callsite_correspondence_unproven",
        "memory_final_state_correspondence_unproven",
        "pure_call_semantics_unproven",
    ),
    "checker-recurrence-proposal-blocker": (
        "recurrence_proposal_validation_unproven",
    ),
    "decompilation-broker-operational-signal": (
        "function_decompilation_artifact_unavailable",
        "high_function_ir_unavailable",
        "subordinate_parent_authority_unproven",
    ),
    "outcome-partition-stage-result": tuple(sorted({
        reason_id for reason_id in OUTCOME_STAGE_REASON_MATRIX.values()
        if reason_id is not None
    })),
    "pairwise-loop-fallback-blocker": (
        "loop_exact_summary_relation_unproven",
        "loop_summary_guard_correspondence_unproven",
        "loop_summary_semantic_equality_unproven",
        "loop_summary_structure_correspondence_unproven",
    ),
    "pairwise-pending-loop-blocker": (
        "loop_exact_summary_relation_unproven",
        "loop_summary_guard_correspondence_unproven",
        "loop_summary_semantic_equality_unproven",
        "loop_summary_structure_correspondence_unproven",
    ),
    "pairwise-readonly-correspondence-member": (
        "readonly_object_correspondence_unproven",
    ),
    "pairwise-readonly-identity-blocker": (
        "readonly_storage_identity_unproven",
    ),
    "recurrence-summary-abi-width": (
        "return_width_provenance_unavailable",
        "return_width_relation_unproven",
    ),
    "recurrence-summary-call-effect": (
        "callee_effect_summary_incomplete",
        "effect_observation_coverage_incomplete",
        "memory_effect_order_extraction_incomplete",
        "unsupported_call_effect_semantics",
    ),
    "recurrence-summary-loop": (
        "phi_cycle_lowering_unproven",
        "summary_effect_model_incomplete",
        "summary_recurrence_transition_validation_incomplete",
        "summary_return_extraction_incomplete",
        "summary_return_memory_observation_mismatch",
        "summary_return_overlap_feasibility_unproven",
        "summary_return_overlap_input_incomplete",
        "summary_return_overlap_value_equality_unproven",
        "summary_return_partition_totality_unproven",
        "summary_return_precondition_incomplete",
        "summary_return_value_extraction_incomplete",
    ),
    "return-width-observation-contract-blocker": (
        "return_observation_contract_unproven",
    ),
    "return-width-pair-assessment": (
        "return_abi_provenance_unavailable",
        "return_abi_relation_unproven",
    ),
    "return-width-projection-relation-blocker": (
        "return_high_bit_relation_unproven",
        "return_observation_contract_unproven",
    ),
    "return-width-unary-provenance-blocker": (
        "return_width_provenance_unavailable",
    ),
    "return-width-pair-unary-provenance-blocker": (
        "return_width_provenance_unavailable",
    ),
    **{
        spec.site_id: spec.reason_ids
        for spec in SAT_SAFETY_PRODUCER_SITE_SPECS
        if spec.reason_ids
    },
    "pairwise-loop-sat-safety-observed": (
        "counterexample_analysis_safety_unproven",
        "counterexample_same_function_replay_unproven",
    ),
}

_REASON_IDENTITY_SCOPES = {
    **{key: value.identity_scope.value for key, value in CALL_EFFECT_REASON_SPECS.items()},
    **{key: value.identity_scope.value for key, value in LOOP_REASON_SPECS.items()},
    **{key: value.identity_scope.value for key, value in ABI_WIDTH_READONLY_REASON_SPECS.items()},
    **{key: "UNARY" for key in OPERATIONAL_REASON_SPECS},
    **{
        reason_id: "UNARY"
        for reason_id in OUTCOME_STAGE_REASON_MATRIX.values()
        if reason_id is not None
    },
    "counterexample_analysis_safety_unproven": "RELATIONAL",
    "counterexample_partition_replay_ambiguous": "RELATIONAL",
    "counterexample_same_function_replay_unproven": "RELATIONAL",
    "comparison_equivalence_closure_unproven": "RELATIONAL",
}


def _call_name(node: ast.Call) -> Optional[str]:
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        return node.func.attr
    return None


def _sealed_site_id(node: ast.AST) -> Optional[str]:
    if (
        isinstance(node, ast.Constant)
        and type(node.value) is str
        and node.value
    ):
        return node.value
    if (
        isinstance(node, ast.Attribute)
        and node.attr == "site_id"
        and isinstance(node.value, ast.Name)
    ):
        return _SEALED_SITE_SPEC_IDS.get(node.value.id)
    return None


def _enclosing_function(node: ast.AST, parents: Mapping[ast.AST, ast.AST]) -> str:
    current = node
    while current in parents:
        current = parents[current]
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return current.name
    return "<module>"


def _allowed_dispositions(site_id: str, emitter: str) -> tuple[str, ...]:
    del emitter
    try:
        return _DISPOSITIONS_BY_SITE[site_id]
    except KeyError as exc:
        raise ValueError("production site lacks a reviewed disposition contract") from exc


def _cause_slots(site_id: str, domain: str) -> tuple[Mapping[str, Any], ...]:
    definitions = {
        item.reason_id: item for item in PROCESS_DURABLE_REASON_REGISTRY.snapshot()
    }
    reason_ids = _CAUSE_REASON_IDS_BY_SITE.get(site_id, ())
    rows = []
    for reason_id in reason_ids:
        definition = definitions.get(reason_id)
        if definition is None or definition.domain != domain:
            raise ValueError("reviewed site reason differs from sealed domain registry")
        target_kinds = tuple(sorted(definition.allowed_target_kinds))
        if len(target_kinds) != 1 or reason_id not in _REASON_IDENTITY_SCOPES:
            raise ValueError("reviewed site reason lacks one exact target/scope")
        rows.append({
        "slot_id": f"{site_id}:{reason_id}",
        "allowed_reason_ids": (reason_id,),
        "expected_domain": domain,
        "expected_target_kind": target_kinds[0],
        "expected_identity_scope": _REASON_IDENTITY_SCOPES[reason_id],
        "slot_semantics": "ALTERNATIVE_REASON_CHOICE",
        })
    return tuple(rows)


def build_phase7_producer_manifest(repo_root: Path) -> Mapping[str, Any]:
    root = Path(repo_root).resolve()
    source_root = root / "scripts/function_tracer_pcode"
    rows = []
    missing = []
    for path in sorted(source_root.rglob("*.py")):
        rel = path.relative_to(root).as_posix()
        if "/tests/" in f"/{rel}/":
            continue
        source = path.read_text(encoding="utf-8")
        tree = ast.parse(source, filename=rel)
        parents = {
            child: parent for parent in ast.walk(tree)
            for child in ast.iter_child_nodes(parent)
        }
        source_hash = hashlib.sha256(path.read_bytes()).hexdigest()
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call) or _call_name(node) not in EMITTERS:
                continue
            emitter = _call_name(node)
            keyword = next((
                item for item in node.keywords
                if item.arg == "producer_site_manifest_id"
            ), None)
            site_id = (
                _sealed_site_id(keyword.value)
                if keyword is not None
                else None
            )
            if site_id is None:
                missing.append((rel, node.lineno, emitter))
                continue
            domain = _DOMAIN_BY_SITE_OVERRIDE.get(
                site_id, _DOMAIN_BY_EMITTER[emitter]
            )
            allowed_dispositions = _allowed_dispositions(site_id, emitter)
            rows.append({
                "producer_site_manifest_id": site_id,
                "path": rel,
                "line": node.lineno,
                "column": node.col_offset,
                "enclosing_function": _enclosing_function(node, parents),
                "emitter": emitter,
                "source_sha256": source_hash,
                "domain": domain,
                "allowed_dispositions": allowed_dispositions,
                "branch_or_attempt_contract_id": f"{site_id}:invocation",
                "allowed_producer_ids": _PRODUCER_IDS_BY_SITE[site_id],
                "expected_cause_slots": (
                    _cause_slots(site_id, domain)
                    if "ELIGIBLE" in allowed_dispositions else ()
                ),
            })
    if missing:
        raise ValueError(f"production signal calls lack audited site IDs: {missing}")
    ids = tuple(row["producer_site_manifest_id"] for row in rows)
    if not rows or len(ids) != len(set(ids)):
        raise ValueError("production activation site IDs are empty or duplicated")
    if set(ids) != set(_DISPOSITIONS_BY_SITE):
        raise ValueError("reviewed production-site contract differs from AST discovery")
    if set(ids) != set(_PRODUCER_IDS_BY_SITE):
        raise ValueError("production-site producer contracts are incomplete")
    eligible_ids = {
        site_id for site_id, dispositions in _DISPOSITIONS_BY_SITE.items()
        if "ELIGIBLE" in dispositions
    }
    if set(_CAUSE_REASON_IDS_BY_SITE) != eligible_ids:
        raise ValueError("reviewed cause-slot table differs from eligible site set")
    ordered = tuple(sorted(rows, key=lambda row: row["producer_site_manifest_id"]))
    body = {
        "manifest_kind": "unknown-taxonomy-v2-phase7-producer-sites-v2",
        "site_count": len(ordered),
        "sites": ordered,
    }
    return {**body, "manifest_digest": authority_digest(body)}


def validate_phase7_producer_manifest(
    repo_root: Path, payload: Mapping[str, Any],
) -> None:
    expected = json.loads(json.dumps(
        build_phase7_producer_manifest(repo_root), sort_keys=True
    ))
    if payload != expected:
        raise ValueError("Phase 7 producer activation manifest drifted")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--output", required=True)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args(argv)
    output = Path(args.output)
    if args.validate:
        validate_phase7_producer_manifest(
            Path(args.repo_root), json.loads(output.read_text(encoding="utf-8"))
        )
    else:
        payload = build_phase7_producer_manifest(Path(args.repo_root))
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
