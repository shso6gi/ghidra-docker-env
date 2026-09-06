"""Final call/effect preflight gate, shadow manifests and phase-2 relational call discharge."""

from __future__ import annotations

from typing import Optional, Dict, Any, List, Mapping, Tuple
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
    run_check_from_binaries_with_v2_pilot as run_check_from_binaries,
)
from scripts.function_tracer_pcode.checker.unknown_reason import make_internal_v2_reason_diagnostic
from scripts.function_tracer_pcode.proof.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
    RelationalCauseKey,
    canonical_cause_tuple,
)
from scripts.function_tracer_pcode.proof.call_effect.obligations import (
    apply_solver_proof_artifacts_to_manifest,
    build_call_effect_shadow_manifest,
    build_structural_coverage_certificate,
)
from scripts.function_tracer_pcode.proof.call_effect.producer import (
    produce_pure_direct_call_proofs,
    produce_v2_pure_direct_call_proofs,
)
from scripts.function_tracer_pcode.authority.domains.call_effect import (
    CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
)
from scripts.function_tracer_pcode.authority.domains.call_effect_sites import (
    CALL_EFFECT_PROOF_BATCH_SITE,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    CallEffectProofBatchProductionSignal,
    build_active_call_effect_execution_context,
    emit_call_effect_signal,
    record_production_pilot_shadow_error,
)
from scripts.function_tracer_pcode.proof.call_effect.preflight import (
    PreparedDispatchFrame,
    validate_call_resolution_projection,
    verify_monolithic_terminal_receipt,
    verify_monolithic_proof_receipt,
)


class PreflightGateMixin:
    """Final call/effect preflight gate, shadow manifests and phase-2 relational call discharge."""

    def _apply_preflight_final_gate(
        self,
        strategy_result: Any,
        frame: PreparedDispatchFrame,
        *,
        cleanup_complete: bool,
    ) -> None:
        """Apply veto-only preflight checks without rewriting pair outcomes."""

        receipt = getattr(strategy_result, "comparison_execution_receipt", None)
        receipt_valid = bool(
            receipt is not None
            and frame.receipt is receipt
            and receipt.is_trusted_for(frame)
        )
        source_valid = frame.source.is_unchanged()
        prepared_valid = frame.prepared.is_valid_for(frame.source) and frame.prepared.is_unchanged()
        projection_valid = frame.projection.proven
        recomputed_projection = validate_call_resolution_projection(
            frame.preflight_manifest,
            frame.prepared,
            generation=frame.generation,
            trusted_proof_artifacts=frame.trusted_proof_artifacts,
        )
        mapping_valid = (
            recomputed_projection.projection_id == frame.projection.projection_id
            and recomputed_projection.use_census_digest == frame.projection.use_census_digest
            and recomputed_projection.coverage_mapping_digest
            == frame.projection.coverage_mapping_digest
        )
        total = int(getattr(strategy_result, "total_pairs", 0) or 0)
        pairwise_complete = (
            total > 0
            and int(getattr(strategy_result, "unsat_pairs", 0) or 0) == total
            and int(getattr(strategy_result, "sat_pairs", 0) or 0) == 0
            and int(getattr(strategy_result, "unknown_pairs", 0) or 0) == 0
            and int(getattr(strategy_result, "error_pairs", 0) or 0) == 0
        )
        receipt_queries = tuple(getattr(receipt, "query_records", ()) or ())
        receipt_counts = dict(getattr(receipt, "disposition_counts", ()) or ())
        receipt_matches_pair_dispositions = bool(
            receipt is not None
            and receipt_counts.get("total") == total
            and receipt_counts.get("unsat")
            == int(getattr(strategy_result, "unsat_pairs", 0) or 0)
            and receipt_counts.get("sat")
            == int(getattr(strategy_result, "sat_pairs", 0) or 0)
            and receipt_counts.get("unknown")
            == int(getattr(strategy_result, "unknown_pairs", 0) or 0)
            and receipt_counts.get("error")
            == int(getattr(strategy_result, "error_pairs", 0) or 0)
        )
        legacy_monolithic_complete = (
            len(receipt_queries) == 1
            and receipt_queries[0].query_label == "monolithic"
            and receipt_queries[0].disposition == "unsat"
            and all(
                receipt_counts.get(name) == count
                for name, count in {
                    "total": 1,
                    "unsat": 1,
                    "sat": 0,
                    "unknown": 0,
                    "error": 0,
                }.items()
            )
            and getattr(getattr(strategy_result, "solver_results", None), "is_equivalent", None)
            is True
        )
        terminal_receipt = frame.monolithic_terminal_receipt
        from scripts.function_tracer_pcode.proof.query_receipt_authority import (
            canonical_region_query_receipt_digests,
        )
        terminal_region_digests = (
            canonical_region_query_receipt_digests(receipt_queries)
        )
        terminal_receipt_valid = bool(
            terminal_receipt is not None
            and verify_monolithic_terminal_receipt(frame)
            and receipt is not None
            and terminal_receipt.comparison_receipt_id == receipt.receipt_id
            and terminal_receipt.region_receipt_digests == terminal_region_digests
        )
        split_region_complete = bool(
            terminal_receipt_valid
            and verify_monolithic_proof_receipt(frame)
            and frame.monolithic_proof_bundle.outcome_kind == "eq_closure"
            and terminal_receipt.outcome_kind == "eq_closure"
            and receipt_counts.get("total", 0) > 0
            and receipt_counts.get("unsat") == receipt_counts.get("total")
            and receipt_counts.get("sat") == 0
            and receipt_counts.get("unknown") == 0
            and receipt_counts.get("error") == 0
            and getattr(getattr(strategy_result, "solver_results", None), "is_equivalent", None)
            is True
        )
        monolithic_complete = (
            terminal_receipt_valid
            and terminal_receipt.outcome_kind == "eq_closure"
            and (legacy_monolithic_complete or split_region_complete)
        )
        decisive_not_eq_receipt = bool(
            getattr(strategy_result, "is_equivalent", None) is False
            and (
                (
                    getattr(receipt, "branch_payload_kind", None) == "pairwise_ledger"
                    and int(receipt_counts.get("sat", 0) or 0) > 0
                )
                or (
                    terminal_receipt_valid
                    and verify_monolithic_proof_receipt(frame)
                    and frame.monolithic_proof_bundle.outcome_kind
                    == "decisive_counterexample"
                    and terminal_receipt.outcome_kind == "decisive_counterexample"
                    and (
                        (
                            len(receipt_queries) == 1
                            and receipt_queries[0].query_label == "monolithic"
                            and receipt_queries[0].disposition == "sat"
                        )
                        or any(
                            record.proof_kind == "monolithic_global_counterexample_replay"
                            and record.disposition == "sat"
                            for record in receipt_queries
                        )
                    )
                )
            )
        )
        ordinary_complete = (
            pairwise_complete
            and receipt_matches_pair_dispositions
            and getattr(receipt, "branch_payload_kind", None) == "pairwise_ledger"
            and len(tuple(getattr(receipt, "closure_snapshot", ()) or ())) == total
        ) or monolithic_complete
        required_projection_binding_ids = tuple(sorted(
            binding.binding_id for binding in frame.projection.semantic_bindings
        ))
        consumed_projection_binding_ids = tuple(
            getattr(receipt, "consumed_projection_binding_ids", ()) or ()
        )
        excluded_projection_binding_ids = tuple(
            getattr(receipt, "excluded_projection_binding_ids", ()) or ()
        )
        receipt_required_projection_binding_ids = tuple(
            getattr(receipt, "required_projection_binding_ids", ()) or ()
        )
        projection_bindings_consumed = (
            not frame.projection.required
            or (
                bool(required_projection_binding_ids)
                and receipt_required_projection_binding_ids
                == required_projection_binding_ids
                and not (
                    set(consumed_projection_binding_ids)
                    & set(excluded_projection_binding_ids)
                )
                and tuple(sorted(
                    set(consumed_projection_binding_ids)
                    | set(excluded_projection_binding_ids)
                )) == required_projection_binding_ids
            )
        )
        projection_active_total = int(
            receipt_counts.get("projection_active_total", -1)
        )
        projection_receipt_partition_valid = bool(
            receipt is not None
            and projection_active_total
            == sum(1 for record in receipt_queries if record.projection_binding_ids)
            and int(receipt_counts.get("projection_inactive_total", -1))
            == sum(1 for record in receipt_queries if not record.projection_binding_ids)
        )
        no_active_pair_proven = bool(
            int(receipt_counts.get("projection_no_active_pair_proven", 0)) == 1
        )

        blockers = []
        expected_terminal_kind = (
            "eq_closure" if getattr(strategy_result, "is_equivalent", None) is True
            else "decisive_counterexample"
            if getattr(strategy_result, "is_equivalent", None) is False
            else "inconclusive_diagnostic"
        )
        if (
            terminal_receipt is not None
            and (
                not terminal_receipt_valid
                or terminal_receipt.outcome_kind != expected_terminal_kind
            )
        ):
            blockers.append("monolithic_terminal_outcome_mismatch")
        if not cleanup_complete or not frame.cleanup_complete:
            blockers.append("dispatch_cleanup_incomplete")
        if not source_valid:
            blockers.append("source_analysis_mutated")
        if not prepared_valid:
            blockers.append("prepared_surface_invalid")
        if frame.projection.required and not projection_valid:
            blockers.extend(frame.projection.root_blockers or ("call_effect_preflight_incomplete",))
        if not mapping_valid:
            blockers.append("deferred_call_use_coverage_mapping_invalid")
        split_stats = dict(
            getattr(strategy_result, "pairwise_debug_stats", None) or {}
        )
        split_receipt_required = int(
            split_stats.get("monolithic_split_planned_regions", 0) or 0
        ) > 0
        if (
            getattr(strategy_result, "is_equivalent", None) in {True, False}
            and not receipt_valid
            and (frame.projection.required or split_receipt_required)
        ):
            blockers.append("comparison_receipt_missing")
        if receipt_valid and not projection_receipt_partition_valid:
            blockers.append("call_projection_active_pair_receipt_invalid")
        if (
            receipt_valid
            and frame.projection.required
            and projection_valid
            and projection_active_total == 0
            and not no_active_pair_proven
        ):
            blockers.append("call_projection_no_active_pair_proof_missing")
        if (
            receipt_valid
            and getattr(strategy_result, "is_equivalent", None) is True
            and not projection_bindings_consumed
        ):
            blockers.append("call_projection_binding_consumption_incomplete")
        if receipt_valid and getattr(strategy_result, "is_equivalent", None) is True and not ordinary_complete:
            blockers.append("ordinary_comparison_proof_incomplete")
        if receipt_valid and getattr(strategy_result, "is_equivalent", None) is False and not decisive_not_eq_receipt:
            blockers.append("decisive_counterexample_receipt_incomplete")

        if blockers:
            if getattr(strategy_result, "is_equivalent", None) in {True, False}:
                strategy_result.is_equivalent = None
            existing = {
                str(ref)
                for reason in tuple(getattr(strategy_result, "unknown_reasons", ()) or ())
                for ref in tuple(getattr(reason, "evidence_refs", ()) or ())
            }
            for blocker in dict.fromkeys(str(item) for item in blockers):
                if blocker in existing:
                    continue
                strategy_result.unknown_reasons.append(
                    make_internal_v2_reason_diagnostic(
                        "pure_call_semantics_unproven",
                        stage="CALL_EFFECT_PREFLIGHT",
                        evidence_refs=(blocker,),
                        detail=f"Call/effect preflight veto: {blocker}",
                    )
                )

    def _call_effect_shadow_manifest(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        binary1_name: str,
        binary2_name: str,
    ) -> Dict[str, Any]:
        """Build decision-neutral evidence; shadow failures must not change a result."""

        try:
            manifest = build_call_effect_shadow_manifest(
                analysis1,
                analysis2,
                binary1_name=binary1_name,
                binary2_name=binary2_name,
                observation_contract=self.observation_contract,
            )
            self._attach_structural_coverage_certificate(manifest)
            production = produce_pure_direct_call_proofs(
                manifest,
                analysis1,
                analysis2,
                solver_runner=self.solver_runner,
                timeout_seconds=self.timeout,
            )
            if not any(
                signal.effect_stage_required
                for signal in production.v2_blocker_signals
            ):
                try:
                    v2_context = build_active_call_effect_execution_context(
                        production.v2_blocker_signals,
                        CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
                    )
                    if v2_context is not None:
                        v2_production = produce_v2_pure_direct_call_proofs(
                            manifest,
                            analysis1,
                            analysis2,
                            execution_context=v2_context,
                            timeout_seconds=self.timeout,
                        )
                        apply_solver_proof_artifacts_to_manifest(
                            manifest,
                            v2_production.artifacts,
                        )
                        completed_obligation_ids = {
                            str(item.get("obligation_id") or "")
                            for item in manifest.get("proof_readiness", ()) or ()
                            if isinstance(item, Mapping)
                            and item.get("decision_eligible") is True
                        }
                        required_obligation_ids = {
                            signal.obligation_id
                            for signal in production.v2_blocker_signals
                        }
                        if (
                            v2_production.failure_causes
                            and required_obligation_ids
                            and required_obligation_ids.issubset(
                                completed_obligation_ids
                            )
                        ):
                            raise ValueError(
                                "V2 call/effect proof has unmaterialized post-stage blockers"
                            )
                        artifacts_by_obligation: Dict[str, List[Any]] = {}
                        for artifact in v2_production.artifacts:
                            artifacts_by_obligation.setdefault(
                                artifact.record.obligation_id, []
                            ).append(artifact)
                        for signal in production.v2_blocker_signals:
                            artifacts = tuple(
                                artifacts_by_obligation.get(signal.obligation_id, ())
                            )
                            if artifacts:
                                emit_call_effect_signal(
                                    CallEffectProofBatchProductionSignal(
                                        signal, artifacts
                                    ),
                                    producer_site_manifest_id=(
                                        CALL_EFFECT_PROOF_BATCH_SITE.site_id
                                    ),
                                )
                        manifest["v2_call_effect_shadow_producer"] = {
                            "mode": "pinned_execution_dual_write",
                            "artifact_count": len(v2_production.artifacts),
                            "failure_causes": list(v2_production.failure_causes),
                            "completed_obligation_ids": sorted(
                                completed_obligation_ids
                            ),
                        }
                except Exception as exc:
                    record_production_pilot_shadow_error(exc)
                    manifest["v2_call_effect_shadow_producer"] = {
                        "mode": "shadow_evidence_incomplete",
                        "error_kind": type(exc).__name__,
                    }
            self._last_internal_call_effect_artifacts = production.artifacts
            if production.artifacts:
                manifest["mode"] = "typed_relational_call_effect_proof"
            apply_solver_proof_artifacts_to_manifest(
                manifest,
                production.artifacts,
            )
            manifest["stage_specific_producer"] = {
                "producer_kind": "typed_pure_direct_call_v1",
                "artifact_count": len(production.artifacts),
                "failure_causes": list(production.failure_causes),
            }
            return manifest
        except Exception as exc:
            self._last_internal_call_effect_artifacts = ()
            self._debug_print(f"Call/effect shadow manifest unavailable: {exc}")
            return {
                "schema_version": 1,
                "mode": "shadow_no_decision_effect",
                "observation_contract": self.observation_contract.to_dict(),
                "shadow_status": "inconclusive",
                "failure_cause": "shadow_manifest_construction_failed",
                "error_type": type(exc).__name__,
                "error_detail": str(exc),
            }

    @staticmethod
    def _attach_structural_coverage_certificate(
        manifest: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Attach an exact deterministic certificate, not a semantic SMT proof."""

        certificate = build_structural_coverage_certificate(manifest)
        manifest["structural_coverage_certificate"] = certificate.to_dict()
        summary = manifest.get("summary")
        if isinstance(summary, dict):
            summary["structural_certificate_status"] = certificate.status
            summary["solver_proof_record_count"] = 0
            summary["solver_proven_stage_count"] = 0
            summary["decision_eligible_obligation_count"] = 0
        return manifest

    def _apply_phase2_relational_call_discharge(
        self,
        strategy_result,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        manifest: Dict[str, Any],
    ) -> None:
        """Promote only an all-UNSAT caller result with complete typed call proofs."""

        gate = {
            "status": "blocked",
            "decision_effect": "blocks_equivalence",
            "failure_cause": "call_effect_stage_proofs_incomplete",
        }
        manifest["phase2_discharge_gate"] = gate
        if not self.enable_completed_recovery_proofs:
            gate["status"] = "disabled"
            gate["decision_effect"] = "diagnostic_only"
            gate["failure_cause"] = "completed_recovery_proofs_disabled"
            return
        apply_solver_proof_artifacts_to_manifest(
            manifest,
            self._last_internal_call_effect_artifacts,
        )
        certificate = manifest.get("structural_coverage_certificate")
        rebuilt_certificate = build_structural_coverage_certificate(manifest)
        if not isinstance(certificate, Mapping) or (
            certificate.get("status") != "complete"
            or certificate.get("verification_status") != "verified"
            or certificate.get("certificate_id") != rebuilt_certificate.certificate_id
            or rebuilt_certificate.verification_failure() is not None
        ):
            gate["failure_cause"] = "structural_coverage_certificate_incomplete"
            return
        obligations = tuple(
            item
            for item in manifest.get("relational_obligations", ()) or ()
            if isinstance(item, Mapping)
        )
        readiness = tuple(
            item
            for item in manifest.get("proof_readiness", ()) or ()
            if isinstance(item, Mapping)
        )
        if not obligations or len(readiness) != len(obligations):
            gate["failure_cause"] = "call_effect_obligation_coverage_incomplete"
            return
        supported_relation_kinds = {
            "call_to_call",
            "call_to_region",
            "region_to_call",
        }
        if any(
            item.get("relation_kind") not in supported_relation_kinds
            for item in obligations
        ):
            gate["failure_cause"] = "unsupported_relational_call_effect_lane"
            return
        caller_memory_effect_counts = []
        for side, analysis in (("function1", analysis1), ("function2", analysis2)):
            effect_summary = getattr(analysis, "effect_summary", None)
            effect_count = len(tuple(getattr(effect_summary, "effects", ()) or ()))
            profile = getattr(
                effect_summary,
                "function_control_effect_profile",
                None,
            )
            explicit_store_count = int(getattr(profile, "store_count", 0) or 0)
            call_derived_store_count = sum(
                int(getattr(evidence, "memory_effect_count", 0) or 0)
                for evidence in tuple(
                    getattr(
                        effect_summary,
                        "call_site_effect_summary_evidence",
                        (),
                    )
                    or ()
                )
            )
            if effect_count or explicit_store_count or call_derived_store_count:
                caller_memory_effect_counts.append(
                    {
                        "side": side,
                        "effect_count": effect_count,
                        "explicit_store_count": explicit_store_count,
                        "call_derived_store_count": call_derived_store_count,
                    }
                )
        caller_memory_proven = bool(readiness) and all(
            "caller_memory_relation"
            in tuple(item.get("completed_stages", ()) or ())
            for item in readiness
        )
        if caller_memory_effect_counts and not caller_memory_proven:
            gate["failure_cause"] = "caller_memory_relation_not_proven"
            gate["caller_memory_effects"] = caller_memory_effect_counts
            return
        if not all(item.get("decision_eligible") is True for item in readiness):
            gate["failure_cause"] = "call_effect_stage_proofs_incomplete"
            return
        for analysis in (analysis1, analysis2):
            effect_summary = getattr(analysis, "effect_summary", None)
            incomplete_reasons = tuple(
                getattr(effect_summary, "incomplete_reasons", ()) or ()
            )
            if incomplete_reasons:
                gate["failure_cause"] = "non_call_effect_unsafety_present"
                gate["non_call_effect_unsafety"] = list(incomplete_reasons)
                return
            if bool(getattr(effect_summary, "has_unsupported_call", False)):
                gate["failure_cause"] = "unsupported_call_effect_present"
                return
            if "effect_summary_path_coverage_incomplete" in tuple(
                getattr(analysis, "analysis_notes", ()) or ()
            ):
                gate["failure_cause"] = "non_call_effect_unsafety_present"
                gate["non_call_effect_unsafety"] = [
                    "effect_summary_path_coverage_incomplete"
                ]
                return
        replacement_readiness = manifest.get("legacy_replacement_readiness")
        if not isinstance(replacement_readiness, Mapping) or (
            replacement_readiness.get("status") != "ready"
        ):
            gate["failure_cause"] = "legacy_blocker_replacement_not_ready"
            return
        raw_reasons = list(getattr(strategy_result, "unknown_reasons", ()) or ())
        from scripts.function_tracer_pcode.authority.domains.call_effect import (
            CALL_EFFECT_REASON_SPECS,
        )

        if not raw_reasons or any(
            str(getattr(reason, "reason_id", "")) not in CALL_EFFECT_REASON_SPECS
            for reason in raw_reasons
        ):
            gate["failure_cause"] = "non_call_unknown_reason_present"
            return
        completed_obligation_ids = {
            str(item.get("obligation_id"))
            for item in readiness
            if item.get("decision_eligible") is True and item.get("obligation_id")
        }
        blocker_mappings = tuple(
            item
            for item in manifest.get("legacy_blocker_mapping", ()) or ()
            if isinstance(item, Mapping)
        )
        for reason in raw_reasons:
            evidence_refs = tuple(getattr(reason, "evidence_refs", ()) or ())
            if len(evidence_refs) != 1:
                gate["failure_cause"] = "call_blocker_obligation_mapping_incomplete"
                return
            matching = tuple(
                item
                for item in blocker_mappings
                if str(item.get("legacy_blocker") or "") == str(evidence_refs[0])
            )
            if len(matching) != 1:
                gate["failure_cause"] = "call_blocker_obligation_mapping_incomplete"
                return
            mapping = matching[0]
            obligation_ids = tuple(mapping.get("obligation_ids", ()) or ())
            if (
                mapping.get("mapping_basis") != "callsite_pcode_ref"
                or mapping.get("mapping_status") != "mapped"
                or len(obligation_ids) != 1
                or str(obligation_ids[0]) not in completed_obligation_ids
            ):
                gate["failure_cause"] = "call_blocker_not_exactly_mapped"
                gate["unmapped_blocker"] = str(evidence_refs[0])
                return
        total_pairs = int(getattr(strategy_result, "total_pairs", 0) or 0)
        if (
            total_pairs <= 0
            or int(getattr(strategy_result, "unsat_pairs", 0) or 0) != total_pairs
            or int(getattr(strategy_result, "sat_pairs", 0) or 0) != 0
            or int(getattr(strategy_result, "unknown_pairs", 0) or 0) != 0
            or int(getattr(strategy_result, "error_pairs", 0) or 0) != 0
            or getattr(strategy_result, "is_equivalent", None) is False
        ):
            gate["failure_cause"] = "caller_relational_return_proof_incomplete"
            return
        strategy_result.is_equivalent = True
        strategy_result.unknown_reasons = []
        coupling = manifest.get("coupling")
        if isinstance(coupling, dict):
            coupling["semantic_proof_status"] = "proven"
        summary = manifest.get("summary")
        if isinstance(summary, dict):
            summary["semantic_proof_status"] = "proven"
        gate.update(
            {
                "status": "proven",
                "decision_effect": "promotes_equivalence",
                "failure_cause": None,
                "proof_kind": "typed_pure_direct_call_relational_proof",
            }
        )

    @staticmethod
    def _specialize_call_effect_unknown_reasons(
        reasons: List[Any],
        manifest: Mapping[str, Any],
        comparison_identity: Optional[Mapping[str, Any]] = None,
    ) -> List[Any]:
        """Move broad call unsafety to the first concrete relational proof stage."""

        backlog = manifest.get("proof_stage_backlog")
        mappings = manifest.get("legacy_blocker_mapping")
        if not isinstance(backlog, list) or not isinstance(mappings, list):
            return reasons
        stage_by_obligation = {
            str(item.get("obligation_id")): str(item.get("primary_proof_stage"))
            for item in backlog
            if isinstance(item, Mapping)
            and item.get("obligation_id")
            and item.get("primary_proof_stage")
        }
        blocker_stages: Dict[str, Tuple[str, ...]] = {}
        blocker_obligations: Dict[str, Tuple[str, ...]] = {}
        for item in mappings:
            if not isinstance(item, Mapping):
                continue
            if (
                item.get("mapping_basis") != "callsite_pcode_ref"
                or item.get("mapping_status") != "mapped"
            ):
                continue
            blocker = str(item.get("legacy_blocker") or "")
            stages = tuple(
                sorted(
                    {
                        stage_by_obligation[str(obligation_id)]
                        for obligation_id in item.get("obligation_ids", ()) or ()
                        if str(obligation_id) in stage_by_obligation
                    }
                )
            )
            if blocker and stages:
                blocker_stages[blocker] = stages
                blocker_obligations[blocker] = tuple(
                    sorted(str(value) for value in (item.get("obligation_ids") or ()))
                )

        specialized: List[Any] = []
        for reason in reasons:
            from scripts.function_tracer_pcode.authority.domains.call_effect import (
                CALL_EFFECT_REASON_SPECS,
            )

            if str(getattr(reason, "reason_id", "")) not in CALL_EFFECT_REASON_SPECS:
                specialized.append(reason)
                continue
            stages = {
                stage
                for ref in getattr(reason, "evidence_refs", ()) or ()
                for stage in blocker_stages.get(str(ref), ())
            }
            if not stages:
                specialized.append(reason)
                continue
            proof_stage = (
                next(iter(stages))
                if len(stages) == 1
                else "multiple_relational_call_effect_stages_missing"
            )
            matched_blockers = tuple(
                sorted(
                    str(ref)
                    for ref in getattr(reason, "evidence_refs", ()) or ()
                    if str(ref) in blocker_stages
                )
            )
            obligation_ids = tuple(
                sorted(
                    {
                        obligation_id
                        for blocker in matched_blockers
                        for obligation_id in blocker_obligations.get(blocker, ())
                    }
                )
            )
            coupling = manifest.get("coupling") if isinstance(manifest.get("coupling"), Mapping) else {}
            observation = manifest.get("observation_contract") if isinstance(manifest.get("observation_contract"), Mapping) else {}
            typed_cause = RelationalCauseKey(
                cause_kind="deferred_call_effect_relation",
                comparison_domain=(
                    "semantic_comparison_domain",
                    tuple((comparison_identity or {}).get("left_binary_content_identity") or ()),
                    tuple((comparison_identity or {}).get("right_binary_content_identity") or ()),
                    tuple((comparison_identity or {}).get("function_identity") or ()),
                    tuple((comparison_identity or {}).get("architecture_identity") or ()),
                    tuple((comparison_identity or {}).get("abi_identity") or ()),
                    tuple((comparison_identity or {}).get("signature_storage_contract") or ()),
                    tuple((comparison_identity or {}).get("calling_convention_fingerprint") or ()),
                    tuple((comparison_identity or {}).get("comparison_policy_fingerprint") or ()),
                    "call_effect_coupling",
                    str(coupling.get("coupling_id") or "missing_coupling_id"),
                    str(observation.get("contract_id") or "missing_observation_contract"),
                ),
                left_semantic_object=(
                    "legacy_blocker_target",
                    reason.object_target_key,
                ),
                right_semantic_object=(
                    "relational_obligation_ids",
                    obligation_ids,
                ),
                correspondence_contract=(
                    "mapping_basis",
                    "callsite_pcode_ref",
                    "proof_stages",
                    tuple(sorted(stages)),
                ),
            )
            proof_requirement = ProofRequirementId.create(
                reason.recovery_proof_kind,
                canonical_cause_tuple(typed_cause),
                ProofRequirementContract(
                    "prove relational deferred call return/effect equivalence",
                    relation_direction="ordered",
                    observation_surface=(
                        str(observation.get("contract_id") or "missing_observation_contract"),
                    ),
                    active_precondition=("mapped_obligations", obligation_ids),
                ),
            )
            comparison_identity_complete = bool(
                (comparison_identity or {}).get("left_binary_content_identity")
                and (comparison_identity or {}).get("right_binary_content_identity")
            )
            specialized.append(
                make_internal_v2_reason_diagnostic(
                    reason.reason_id,
                    count_kind=reason.count_kind,
                    reason_class=reason.reason_class,
                    decision_effect=reason.decision_effect,
                    reason_scope=reason.reason_scope,
                    aggregation_unit=reason.aggregation_unit,
                    stage=reason.stage,
                    pair_or_case=reason.pair_or_case,
                    evidence_refs=reason.evidence_refs,
                    recovery_proof_kind=reason.recovery_proof_kind,
                    recovery_proof_obligations=(
                        {
                            "proof_kind": reason.recovery_proof_kind,
                            "proof_stage": proof_stage,
                            "required_evidence": (
                                "relational_call_effect_obligation",
                                "solver_proof_record",
                            ),
                            "description": "Complete the obligation-specific relational call/effect proof stage.",
                        },
                    ),
                    proof_stage=proof_stage,
                    evidence_kind=reason.evidence_kind,
                    object_target_key=reason.object_target_key,
                    object_evidence=reason.object_evidence,
                    proof_obligation_id=None,
                    typed_cause_key=(
                        typed_cause.to_dict() if comparison_identity_complete else None
                    ),
                    proof_requirement_ids=(
                        (proof_requirement.to_dict(),)
                        if comparison_identity_complete
                        else ()
                    ),
                    recovery_action="relational_call_effect_stage_proof_required",
                    action_status=reason.action_status,
                    target_regression=reason.target_regression,
                    detail=(
                        f"Relational call/effect proof is incomplete at {proof_stage}."
                    ),
                )
            )
        return specialized
