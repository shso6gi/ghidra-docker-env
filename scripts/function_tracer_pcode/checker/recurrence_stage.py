"""Recurrence promotion, recursive abstraction and loop-template stage decisions."""

from __future__ import annotations

from typing import Optional, Dict, Any, List
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis, FunctionSignature
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.proof.recursive_abstraction import abstract_recursive_calls
from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
    run_check_from_binaries_with_v2_pilot as run_check_from_binaries,
)
from scripts.function_tracer_pcode.checker.unknown_reason import make_internal_v2_reason_diagnostic
from scripts.function_tracer_pcode.proof.recurrence_promotion import (
    PairPromotionState,
    PairRecurrencePromotionAuthority,
)
from scripts.function_tracer_pcode.core.recurrence_contracts import RecurrenceDigestCodec


class RecurrenceStageMixin:
    """Recurrence promotion, recursive abstraction and loop-template stage decisions."""

    def _recurrence_promotion_result_receipt(self, strategy_result: Any) -> Optional[Dict[str, Any]]:
        attempt = getattr(self, "_last_recurrence_promotion_attempt", None)
        active_authority = getattr(self, "_active_recurrence_promotion_authority", None)
        if (
            attempt is None
            or active_authority is None
            or attempt.authority is None
            or attempt.authority.digest != active_authority.digest
            or attempt.state != PairPromotionState.COMPOSED
        ):
            return None
        receipt = dict(attempt.to_dict())
        comparison_receipt = getattr(strategy_result, "comparison_execution_receipt", None)
        receipt.update({
            "final_decision_used_promoted_successor": True,
            "promoted_successor_final_outcome": (
                "EQ" if strategy_result.is_equivalent is True
                else "NOT_EQ" if strategy_result.is_equivalent is False
                else "UNKNOWN"
            ),
            "promoted_successor_comparison_receipt_id": getattr(
                comparison_receipt, "receipt_id", None
            ),
        })
        return receipt

    @staticmethod
    def _recurrence_promotion_authority(
        strategy_result: Any,
        *,
        comparison_session_id: str,
        branch_id: str,
    ) -> Optional[PairRecurrencePromotionAuthority]:
        if getattr(strategy_result, "is_equivalent", None) is not None:
            return None
        reasons = tuple(getattr(strategy_result, "unknown_reasons", ()) or ())
        if not reasons:
            return None
        sat_reason_ids = {
            "counterexample_analysis_safety_unproven",
            "counterexample_replay_unproven",
            "counterexample_partition_replay_ambiguous",
            "sat_counterexample_ambiguous",
        }
        if (
            int(getattr(strategy_result, "sat_pairs", 0) or 0) > 0
            or getattr(strategy_result, "counterexample_raw", None) is not None
            or any(
                str(getattr(reason, "reason_id", "") or "") in sat_reason_ids
                or str(getattr(reason, "recovery_proof_kind", "") or "")
                == "sat_unsafety_resolution"
                for reason in reasons
            )
        ):
            return None
        recurrence_proof_kinds = {
            "loop_summary_completion", "loop_recurrence_proof",
            "call_effect_summary_proof", "effect_summary_completion",
            "guard_partition_completion", "return_partition_overlap_proof",
            "precondition_completion",
        }
        targeted = []
        for reason in reasons:
            reason_id = getattr(reason, "reason_id", None)
            if not isinstance(reason_id, str) or not reason_id:
                continue
            proof_kind = str(getattr(reason, "recovery_proof_kind", "") or "")
            if proof_kind not in recurrence_proof_kinds:
                continue
            payload = {
                "reason_id": reason_id,
                "recovery_proof_kind": proof_kind,
                "proof_stage": str(getattr(reason, "proof_stage", "") or ""),
                "object_target_key": getattr(reason, "object_target_key", None),
                "proof_obligation_id": getattr(reason, "proof_obligation_id", None),
                "typed_cause_key": getattr(reason, "typed_cause_key", None),
                "proof_requirement_ids": tuple(
                    getattr(reason, "proof_requirement_ids", ()) or ()
                ),
            }
            try:
                blocker_digest = RecurrenceDigestCodec.digest(
                    "recurrence_targeted_branch_blocker_v1", payload
                )
            except TypeError:
                continue
            targeted.append((
                "recurrence_targeted_branch_blocker_v1",
                payload["reason_id"],
                proof_kind,
                payload["object_target_key"],
                blocker_digest,
            ))
        if not targeted:
            return None
        return PairRecurrencePromotionAuthority(
            str(comparison_session_id),
            str(branch_id),
            tuple(dict.fromkeys(targeted)),
        )

    @staticmethod
    def _attach_recurrence_proposal_blockers(
        strategy_result: Any,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        *,
        branch_id: str,
    ) -> List[Any]:
        reasons = list(getattr(strategy_result, "unknown_reasons", ()) or ())
        if (
            getattr(strategy_result, "is_equivalent", None) is not None
            or int(getattr(strategy_result, "sat_pairs", 0) or 0) > 0
            or getattr(strategy_result, "counterexample_raw", None) is not None
        ):
            return reasons
        known_targets = {
            tuple(getattr(reason, "object_target_key", ()) or ())
            for reason in reasons
        }
        for side, analysis in (("function1", analysis1), ("function2", analysis2)):
            for proposal in tuple(
                getattr(analysis, "quarantined_recurrence_proposals", ()) or ()
            ):
                try:
                    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
                        LoopBlockerProductionSignal,
                    )
                    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                        emit_loop_recurrence_signal,
                    )

                    emit_loop_recurrence_signal(
                        LoopBlockerProductionSignal.from_recurrence_proposal(
                            analysis, proposal
                        ),
                        producer_site_manifest_id=(
                            "checker-recurrence-proposal-blocker"
                        ),
                    )
                except Exception as exc:
                    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                        record_production_pilot_shadow_error,
                    )

                    record_production_pilot_shadow_error(exc)
                target = (
                    "quarantined_recurrence_proposal_blocker_v1",
                    side,
                    analysis.outcome_function_identity(),
                    proposal.digest,
                )
                if target in known_targets:
                    continue
                reasons.append(make_internal_v2_reason_diagnostic(
                    "recurrence_proposal_validation_unproven",
                    stage=str(branch_id),
                    recovery_proof_kind="loop_recurrence_proof",
                    proof_stage="recurrence_validation_complete",
                    evidence_kind="quarantined_recurrence_proposal",
                    object_target_key=target,
                    evidence_refs=(proposal.digest,),
                    detail="proof-free recurrence proposal awaits branch-local validation",
                ))
                known_targets.add(target)
        return reasons

    def _run_recursive_abstraction_stage(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        binary1_name: str,
        binary2_name: str,
        save_formula: bool,
        type_fix_result: Optional[TypeFixResult],
        retry_count: int,
        original_signature1: Optional[FunctionSignature],
        original_signature2: Optional[FunctionSignature],
        *,
        branch_context=None,
    ) -> Optional[EquivalenceResult]:
        """``branch_context``: Internal execution context (Phase 6c #93)。stage runner は inner ``check()`` が
        現在得ている effective context（session / generation / lease は runner 由来、branch_id は strategy class 名の
        fallback）を渡す。direct 呼び出しでは省略し、``check()`` が direct semantics で組む。"""
        self._last_recursive_derived_view_identity = None
        abstraction = abstract_recursive_calls(
            analysis1,
            analysis2,
            assume_fp_non_nan=self.assume_fp_non_nan,
            observes_errno=self.observes_errno,
            observes_fenv=self.observes_fenv,
            debug=self.debug,
        )
        if not abstraction.applied:
            self._debug_print("Recursive abstraction fallback: no compatible deferred-call matches")
            return None

        self._debug_print(
            "Deferred call abstraction fallback: matched "
            f"{len(abstraction.matches)} deferred call(s)"
        )
        runtime = getattr(self, "_obligation_runtime_session", None)
        if runtime is None:
            from scripts.function_tracer_pcode.proof.obligations.runtime import (
                ObligationRuntimeSession,
            )

            runtime = ObligationRuntimeSession.create(analysis1, analysis2)
            self._obligation_runtime_session = runtime
        recursive_view = runtime.create_recursive_view(
            abstraction.analysis1,
            abstraction.analysis2,
            abstraction.matches,
        )
        self._last_recursive_derived_view = recursive_view
        self._last_recursive_derived_view_identity = recursive_view.view_id
        return self.check(
            abstraction.analysis1,
            abstraction.analysis2,
            binary1_name,
            binary2_name,
            save_formula,
            type_fix_result=type_fix_result,
            retry_count=retry_count,
            original_signature1=original_signature1,
            original_signature2=original_signature2,
            force_strategy=self.pairwise_strategy,
            branch_context=branch_context,
        )

    def _should_try_loop_template_stage(
        self,
        last_result: Optional[EquivalenceResult],
    ) -> bool:
        """Layer 2 は solver timeout に起因する UNKNOWN にだけ適用する。"""
        if last_result is None:
            return False
        if last_result.is_equivalent is not None or last_result.error_message is not None:
            return False
        if last_result.is_timeout():
            return True

        pairwise_stats = last_result.pairwise_debug_stats or {}
        timeout_fallback_attempts = int(pairwise_stats.get("timeout_fallback_attempts", 0) or 0)
        if timeout_fallback_attempts > 0:
            self._debug_print(
                "Stage S_LOOP_TEMPLATE_ABSTRACTION: enabling due to pairwise query timeouts "
                f"(timeout_fallback_attempts={timeout_fallback_attempts})"
            )
            return True

        return False

    def _should_skip_monolithic_fallback(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> bool:
        """monolithic 化で誤判定しやすい不完全要約を検出する。"""
        return (
            analysis1.should_skip_monolithic_fallback()
            or analysis2.should_skip_monolithic_fallback()
        )
