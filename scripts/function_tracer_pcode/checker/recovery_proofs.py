"""Completed recovery-proof payloads and their merge into results."""

from __future__ import annotations

from typing import Dict, Any, List, Mapping
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import (
    RELATION_DIGEST_KEY,
    merge_new_evidence,
)
from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec
from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
    run_check_from_binaries_with_v2_pilot as run_check_from_binaries,
)


class RecoveryProofMixin:
    """Completed recovery-proof payloads and their merge into results."""

    def _completed_recovery_proof_payload(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        binary1_name: str,
        binary2_name: str,
        *,
        extra_records=(),
    ) -> List[Dict[str, Any]]:
        if not self.enable_completed_recovery_proofs:
            return []
        records: List[Dict[str, Any]] = []
        for side, binary_name, analysis in (
            ("function1", binary1_name, analysis1),
            ("function2", binary2_name, analysis2),
        ):
            for evidence in getattr(analysis, "completed_recovery_proof_evidence", ()) or ():
                if not isinstance(evidence, Mapping):
                    continue
                records.append(
                    {
                        "side": side,
                        "function_name": analysis.function_name,
                        "binary_name": binary_name,
                        "binary_id": getattr(analysis, "binary_id", None),
                        "evidence": dict(evidence),
                    }
                )
        records.extend(
            dict(item) for item in tuple(extra_records or ())
            if isinstance(item, Mapping)
        )
        unique = {}
        for item in records:
            evidence = item.get("evidence") or {}
            identity = (
                item.get("side"),
                SnapshotFingerprintCodec.freeze(
                    evidence.get("proof_requirement_id")
                    or evidence.get("proof_obligation_id")
                    or evidence
                ),
                evidence.get(RELATION_DIGEST_KEY),
            )
            unique.setdefault(identity, item)
        return list(unique.values())

    @staticmethod
    def _reason_completion_applicability_contexts(
        completed_proofs,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> List[Dict[str, Any]]:
        """Validate completion artifacts against the live analysis snapshots.

        This is the runtime trust boundary used by attempt recording.  Evidence
        fields are never reused as their own current applicability values.
        """

        from scripts.function_tracer_pcode.proof.obligations.runtime import (
            GLOBAL_VALIDATED_UNARY_ARTIFACT_CACHE,
            ObligationRuntimeSession,
        )

        by_side = {"function1": analysis1, "function2": analysis2}
        contexts: List[Dict[str, Any]] = []
        for wrapper in tuple(completed_proofs or ()):
            if not isinstance(wrapper, Mapping):
                continue
            analysis = by_side.get(str(wrapper.get("side") or ""))
            evidence = wrapper.get("evidence")
            if analysis is None or not isinstance(evidence, Mapping):
                continue
            artifact_id = evidence.get("proof_artifact_ref")
            requirement = evidence.get("proof_requirement_id")
            if artifact_id is None or not isinstance(requirement, Mapping):
                continue
            try:
                artifact_id = tuple(SnapshotFingerprintCodec.freeze(artifact_id))
                current_snapshot = ObligationRuntimeSession._snapshot(
                    analysis, "completion_applicability"
                ).semantic_fingerprint
            except (TypeError, ValueError):
                continue
            entry = GLOBAL_VALIDATED_UNARY_ARTIFACT_CACHE.find_applicable_artifact(
                artifact_id,
                function_snapshot_fingerprint=current_snapshot,
            )
            if entry is None:
                continue
            artifact_digest = SnapshotFingerprintCodec.digest((
                entry.artifact.artifact_id,
                entry.artifact.payload,
            ))
            contexts.append({
                "proof_requirement_id": dict(requirement),
                "proof_artifact_ref": entry.artifact.artifact_id,
                "current_snapshot_fingerprint": current_snapshot,
                "current_semantic_seed_or_premise_digest": entry.function_premise_digest,
                "current_evidence_or_artifact_digest": artifact_digest,
                "artifact_is_valid": True,
            })
        return contexts

    def _merge_completed_recovery_proofs_from_result(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        result: EquivalenceResult,
    ) -> None:
        if not self.enable_completed_recovery_proofs:
            return
        payload = getattr(result, "completed_recovery_proof_evidence", None) or ()
        if not payload:
            return
        by_side = {
            "function1": analysis1,
            "function2": analysis2,
        }
        for item in payload:
            if not isinstance(item, Mapping):
                continue
            side = str(item.get("side") or "")
            analysis = by_side.get(side)
            if analysis is None:
                continue
            evidence = item.get("evidence")
            if not isinstance(evidence, Mapping):
                continue
            # 証拠の relation 束縛（Issue #167）はそのまま持ち込む。同じ proof でも
            # 別の relation で作った record は、別の証拠として並べる。
            merged = merge_new_evidence(
                getattr(analysis, "completed_recovery_proof_evidence", ()) or (),
                (evidence,),
            )
            if merged is not None:
                analysis.completed_recovery_proof_evidence = tuple(merged)
