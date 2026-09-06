"""Root-blocker identities and typed UNKNOWN causes."""

from __future__ import annotations

from typing import Optional, Dict, Any, List, Mapping, Tuple
from dataclasses import replace
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis, FunctionSignature
from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
    run_check_from_binaries_with_v2_pilot as run_check_from_binaries,
)
from scripts.function_tracer_pcode.checker.unknown_reason import build_unknown_recovery_actions
from scripts.function_tracer_pcode.proof.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
    UnaryCauseKey,
    RelationalCauseKey,
    canonical_cause_tuple,
)


class RootCauseMixin:
    """Root-blocker identities and typed UNKNOWN causes."""

    @classmethod
    def _attach_root_blocker_identities(
        cls,
        reasons: List[Any],
        comparison_identity: Mapping[str, Any],
    ) -> List[Any]:
        """Attach typed root-cause/proof identities to all key-backed reasons."""

        if not (
            comparison_identity.get("left_binary_content_identity")
            and comparison_identity.get("right_binary_content_identity")
        ):
            return reasons
        enriched = []
        for reason in reasons:
            if getattr(reason, "typed_cause_key", None):
                enriched.append(reason)
                continue
            target = getattr(reason, "object_target_key", None)
            if not target:
                enriched.append(reason)
                continue
            cause = cls._typed_cause_for_reason(reason, target, comparison_identity)
            if cause is None:
                enriched.append(reason)
                continue
            requirements = []
            for action in build_unknown_recovery_actions((reason,)):
                proof_kind = str(getattr(action, "proof_kind", "none") or "none")
                if proof_kind == "none":
                    continue
                contract = ProofRequirementContract(
                    proposition=f"complete {proof_kind}",
                    relation_direction=(
                        "ordered"
                        if getattr(cause, "identity_scope", "") == "relational"
                        else "unary"
                    ),
                    observation_surface=tuple(
                        getattr(action, "required_evidence", ()) or ()
                    ),
                    active_precondition=(
                        "recovery_action",
                        str(getattr(action, "recovery_action", "") or "unspecified"),
                    ),
                )
                requirements.append(
                    ProofRequirementId.create(
                        proof_kind,
                        canonical_cause_tuple(cause),
                        contract,
                    ).to_dict()
                )
            enriched.append(
                replace(
                    reason,
                    typed_cause_key=cause.to_dict(),
                    proof_requirement_ids=tuple(requirements),
                )
            )
        return enriched

    @classmethod
    def _typed_cause_for_reason(
        cls,
        reason: Any,
        target: Tuple[Any, ...],
        comparison_identity: Mapping[str, Any],
    ) -> Any:
        raw_reason_id = getattr(reason, "reason_id", None)
        if not isinstance(raw_reason_id, str) or not raw_reason_id:
            return None
        reason_id = raw_reason_id
        side = cls._root_cause_side(target)
        relational_reasons = {
            "sat_counterexample_ambiguous",
            "return_width_bridge_missing",
        }
        unary_reasons = {
            "return_coverage_gap",
            "return_coverage_inconclusive",
            "phi_circular_replacement_unproven",
            "summary_return_candidate_invalid",
            "summary_return_overlap_unproven",
            "summary_effect_unmodeled",
            "summary_precondition_incomplete",
            "summary_partition_not_total",
        }
        if side is not None:
            local_content = (
                comparison_identity.get("left_binary_content_identity")
                if side == "function1"
                else comparison_identity.get("right_binary_content_identity")
            )
            function_identities = tuple(
                comparison_identity.get("function_identity") or ()
            )
            local_function = (
                function_identities[0]
                if side == "function1" and function_identities
                else function_identities[1]
                if side == "function2" and len(function_identities) > 1
                else ("missing_function_identity",)
            )
            return UnaryCauseKey(
                cause_kind=reason_id,
                binary_content_identity=tuple(local_content or ()),
                function_ir_identity=("function_identity", local_function),
                semantic_object_identity=(
                    "object_target",
                    cls._strip_root_cause_side(target),
                ),
            )
        if reason_id in relational_reasons or reason_id in unary_reasons or reason_id == (
            "unresolved_value_expression"
        ):
            function_identities = tuple(
                comparison_identity.get("function_identity") or ()
            )
            return RelationalCauseKey(
                cause_kind=reason_id,
                comparison_domain=cls._root_comparison_domain(comparison_identity),
                left_semantic_object=(
                    "left_function",
                    function_identities[0] if function_identities else (),
                    "target",
                    target,
                ),
                right_semantic_object=(
                    "right_function",
                    function_identities[1] if len(function_identities) > 1 else (),
                    "target",
                    target,
                ),
                correspondence_contract=("reason_scope", getattr(reason, "reason_scope", None)),
            )
        return None

    @staticmethod
    def _root_cause_side(value: Any) -> Optional[str]:
        if isinstance(value, tuple):
            for item in value[:4]:
                if isinstance(item, str) and item in {"function1", "function2"}:
                    return str(item)
        return None

    @classmethod
    def _strip_root_cause_side(cls, value: Any) -> Any:
        if isinstance(value, tuple):
            return tuple(
                "local_function"
                if isinstance(item, str) and item in {"function1", "function2"}
                else cls._strip_root_cause_side(item)
                for item in value
            )
        return value

    @staticmethod
    def _root_comparison_domain(identity: Mapping[str, Any]) -> Tuple[Any, ...]:
        return tuple(
            (name, tuple(identity.get(name) or ()))
            for name in (
                "left_binary_content_identity",
                "right_binary_content_identity",
                "function_identity",
                "architecture_identity",
                "abi_identity",
                "signature_storage_contract",
                "calling_convention_fingerprint",
                "comparison_policy_fingerprint",
            )
        )

    @staticmethod
    def _deterministic_analysis_identity(strategy: Any, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        method = getattr(strategy, "_deterministic_function_identity", None)
        if callable(method):
            return tuple(method(analysis))
        function_ref = getattr(analysis, "function_ref", None)
        return (
            "function_identity",
            ("binary_id", getattr(analysis, "binary_id", None)),
            ("function_name", getattr(analysis, "function_name", None)),
            ("entry_offset", getattr(function_ref, "entry_offset", None)),
            ("entry_point", getattr(analysis, "entry_point", None)),
            ("signature", FunctionSignature.from_analysis(analysis).to_dict()),
            ("calling_convention", getattr(analysis, "calling_convention", None)),
        )

    def _call_effect_comparison_identity(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        manifest: Mapping[str, Any],
    ) -> Dict[str, Any]:
        left_content, right_content = getattr(
            self, "_active_binary_content_identities", (None, None)
        ) or (None, None)
        left_identity = self._deterministic_analysis_identity(
            self.pairwise_strategy, analysis1
        )
        right_identity = self._deterministic_analysis_identity(
            self.pairwise_strategy, analysis2
        )
        observation = manifest.get("observation_contract")
        observation = observation if isinstance(observation, Mapping) else {}
        return {
            "left_binary_content_identity": tuple(left_content or ()),
            "right_binary_content_identity": tuple(right_content or ()),
            "function_identity": (
                ("left_function_identity", left_identity),
                ("right_function_identity", right_identity),
            ),
            "architecture_identity": (
                ("left", self._analysis_architecture_identity(analysis1)),
                ("right", self._analysis_architecture_identity(analysis2)),
            ),
            "abi_identity": (
                ("left", self._analysis_abi_identity(analysis1)),
                ("right", self._analysis_abi_identity(analysis2)),
            ),
            "signature_storage_contract": (
                ("left_signature", FunctionSignature.from_analysis(analysis1).to_dict()),
                ("right_signature", FunctionSignature.from_analysis(analysis2).to_dict()),
            ),
            "calling_convention_fingerprint": (
                getattr(analysis1, "calling_convention", None)
                or getattr(analysis1, "calling_convention_name", None)
                or "unknown_calling_convention",
                getattr(analysis2, "calling_convention", None)
                or getattr(analysis2, "calling_convention_name", None)
                or "unknown_calling_convention",
            ),
            "comparison_policy_fingerprint": (
                "observation_contract",
                observation.get("contract_id"),
                "normalize_mode",
                getattr(self.normalization_settings, "mode", None),
            ),
        }

    @staticmethod
    def _analysis_architecture_identity(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        return (
            "architecture_identity",
            ("language_id", getattr(analysis, "language_id", None) or getattr(analysis, "program_language_id", None)),
            ("processor", getattr(analysis, "processor", None) or getattr(analysis, "processor_name", None)),
            ("endianness", getattr(analysis, "endianness", None) or getattr(analysis, "endian", None)),
            ("address_size", getattr(analysis, "address_size", None) or getattr(analysis, "pointer_size", None)),
        )

    @staticmethod
    def _analysis_abi_identity(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        return (
            "abi_identity",
            ("abi_name", getattr(analysis, "abi_name", None) or getattr(analysis, "abi", None)),
            ("compiler_spec_id", getattr(analysis, "compiler_spec_id", None)),
            ("compiler_artifact_identity", getattr(analysis, "compiler_artifact_identity", None)),
        )
