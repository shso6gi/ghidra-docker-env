"""Immutable analysis snapshots and derived semantic views."""

from __future__ import annotations

from dataclasses import dataclass, field, fields, is_dataclass
from enum import Enum
import hashlib
import json
from types import MappingProxyType
from typing import Any, Mapping, Tuple

from scripts.function_tracer_pcode.core.budget_policy import (
    alias_serialized_tree,
    serialization_scope,
)
from scripts.function_tracer_pcode.proof.obligations.model import SemanticFactProvenance


SEMANTIC_ANALYSIS_NOTES = frozenset({
    "indirect_control_flow_unresolved",
    "symbolic_post_state_reads",
    "return_case_coverage_gap",
    "return_case_coverage_inconclusive",
    "effect_summary_path_coverage_incomplete",
    "bounded_call_refinement_argument_alignment_failed",
    "bounded_call_refinement_deferred_target_unresolved",
    "bounded_call_refinement_return_summary_unusable",
    "effect_call_argument_evidence_incomplete",
})

# Every FunctionReturnAnalysis dataclass field must be classified here.  Fields
# represented by a normalized projection still remain listed explicitly.
FUNCTION_ANALYSIS_FIELD_CLASSIFICATION = MappingProxyType({
    "function_name": "semantic", "entry_point": "semantic", "parameters": "semantic",
    "returns": "semantic", "function_ref": "semantic", "return_type": "semantic",
    "return_type_obj": "semantic_projection", "signedness_result": "semantic",
    "unknown_event_count": "semantic", "unknown_event_reasons": "semantic",
    "analysis_notes": "typed_notes", "recovered_from_decompiler": "semantic",
    "incomplete_control_flow": "semantic", "deferred_calls": "semantic",
    "effect_summary": "semantic_projection", "signature_hypotheses": "semantic",
    "return_type_provenance": "semantic", "comparison_surface": "semantic",
    "analysis_scope_key": "semantic", "program_is_big_endian": "semantic",
    "completed_recovery_proof_ids": "derived_proof",
    "completed_recovery_proof_evidence": "derived_proof",
    "binary_id": "semantic", "summary_return_candidates": "semantic",
    "return_outcomes": "semantic", "divergence_outcomes": "semantic",
    "unknown_outcomes": "semantic", "analysis_view_identity": "semantic",
    "partition_revision": "semantic",
    "outcome_seed": "semantic",
    "termination_path_effect_evidence": "semantic",
    "quarantined_recurrence_proposals": "semantic",
    "return_abi_facts": "semantic",
    # Issue #131 PR-B: 切り捨て marker は解析前提の一部。``to_dict`` の正規化済み
    # 全記録が snapshot fingerprint に入るので、marker を知らずに作った証明は
    # 別の前提のものとして再利用されない。
    "expansion_budget_truncations": "semantic",
})


def deep_freeze(value: Any) -> Any:
    if isinstance(value, Mapping):
        return MappingProxyType({key: deep_freeze(item) for key, item in value.items()})
    if isinstance(value, (list, tuple)):
        return tuple(deep_freeze(item) for item in value)
    if isinstance(value, (set, frozenset)):
        return frozenset(deep_freeze(item) for item in value)
    return value


def _semantic_effect_summary_projection(effect_summary: Any, work: Any = None) -> Any:
    if effect_summary is None:
        return None
    # The dataclass projection is object-derived and includes stores, calls,
    # completeness reasons, and the function control/effect profile.  freeze()
    # rejects any opaque object that lacks a stable key instead of stringifying it.
    if work is None or not _is_plain_dataclass(effect_summary):
        return SnapshotFingerprintCodec.freeze(effect_summary)
    # Issue #22 PR-22-D: 同じ投影（`freeze` の dataclass 分岐と同じ値）を、field の
    # collection は 1 要素ずつ作って直列化の作業量へ足す。効果が大量でも、予算を
    # 超えた時点で残りの要素を投影しない。
    return (
        effect_summary.__class__.__qualname__,
        tuple(
            (item.name, _freeze_counted(getattr(effect_summary, item.name), work))
            for item in fields(effect_summary)
        ),
    )


def _is_plain_dataclass(value: Any) -> bool:
    """`freeze` が dataclass 分岐で投影する値か（stable key / to_dict を持たない）。"""

    return is_dataclass(value) and not isinstance(value, type) and not any(
        callable(getattr(value, name, None)) for name in ("stable_key", "to_key", "to_dict")
    )


def _freeze_counted(value: Any, work: Any) -> Any:
    """`SnapshotFingerprintCodec.freeze(value)` と同じ値を、要素ごとに数えながら作る。"""

    freeze = SnapshotFingerprintCodec.freeze
    if isinstance(value, (tuple, list)):
        return tuple(work.records(value, freeze))
    if isinstance(value, Mapping):
        items = tuple(work.records(value.items(), lambda pair: (freeze(pair[0]), freeze(pair[1]))))
        return SnapshotFingerprintCodec.sorted_mapping_items(items)
    return work.record(lambda: freeze(value))


def _classify_analysis_notes(notes: Any) -> Tuple[Tuple[str, ...], Tuple[str, ...]]:
    semantic = []
    diagnostic = []
    for raw_note in notes or ():
        note = str(raw_note)
        if note in SEMANTIC_ANALYSIS_NOTES:
            semantic.append(note)
        elif note.startswith(("debug:", "diagnostic:")):
            diagnostic.append(note)
        else:
            # Unknown notes are semantic by default.  This is conservative and
            # prevents a newly introduced blocker from silently missing identity.
            semantic.append(note)
    return tuple(semantic), tuple(diagnostic)


class SnapshotFingerprintCodec:
    """Canonicalizes semantic DTO data without stringifying opaque objects."""

    @classmethod
    def freeze(cls, value: Any) -> Any:
        if value is None or isinstance(value, (bool, int, float, str)):
            return value
        if isinstance(value, Enum):
            return (value.__class__.__qualname__, value.value)
        if isinstance(value, bytes):
            return ("bytes", value.hex())
        if isinstance(value, Mapping):
            items = tuple((cls.freeze(key), cls.freeze(item)) for key, item in value.items())
            return cls.sorted_mapping_items(items)
        if isinstance(value, (tuple, list)):
            return tuple(cls.freeze(v) for v in value)
        if isinstance(value, (set, frozenset)):
            return tuple(sorted((cls.freeze(v) for v in value), key=repr))
        stable_key = getattr(value, "stable_key", None)
        if callable(stable_key):
            return (value.__class__.__qualname__, cls.freeze(stable_key()))
        to_key = getattr(value, "to_key", None)
        if callable(to_key):
            return (value.__class__.__qualname__, cls.freeze(to_key()))
        to_dict = getattr(value, "to_dict", None)
        if callable(to_dict):
            built = to_dict()
            frozen = cls.freeze(built)
            # Issue #22 PR-22-D: 木表現を写した側は、元の木として数え済み
            alias_serialized_tree(built, frozen)
            return (value.__class__.__qualname__, frozen)
        if is_dataclass(value):
            return (
                value.__class__.__qualname__,
                tuple((f.name, cls.freeze(getattr(value, f.name))) for f in fields(value)),
            )
        raise TypeError(
            f"opaque object {value.__class__.__qualname__} has no object-derived stable identity"
        )

    @classmethod
    def sorted_mapping_items(cls, items: Tuple[Tuple[Any, Any], ...]) -> Tuple[Tuple[Any, Any], ...]:
        """凍結した (key, 値) の組を、mapping の canonical な並びにする。"""

        canonical_keys = tuple(key for key, _item in items)
        if len(set(canonical_keys)) != len(canonical_keys):
            raise ValueError("mapping contains duplicate canonical semantic keys")
        return tuple(sorted(items, key=lambda pair: cls._sort_key(pair[0])))

    @staticmethod
    def _sort_key(value: Any) -> str:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)

    @classmethod
    def digest(cls, value: Any) -> str:
        frozen = cls.freeze(value)
        payload = json.dumps(frozen, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        return hashlib.sha256(payload.encode("utf-8")).hexdigest()


#: snapshot 1 つ分の直列化の作業量を数える観測点。
SNAPSHOT_SERIALIZATION_SITE = "proof.obligations.snapshot.from_function_analysis"


@dataclass(frozen=True)
class AnalysisSnapshot:
    snapshot_id: Tuple[Any, ...]
    semantic_fields: Mapping[str, Any]
    semantic_fingerprint: str
    extraction_schema_version: int = 1
    diagnostic_refs: Mapping[str, Any] = field(default_factory=dict, compare=False, hash=False)

    @classmethod
    def create(
        cls,
        snapshot_id: Tuple[Any, ...],
        semantic_fields: Mapping[str, Any],
        *,
        diagnostic_refs: Mapping[str, Any] | None = None,
        extraction_schema_version: int = 1,
    ) -> "AnalysisSnapshot":
        payload = (extraction_schema_version, snapshot_id, semantic_fields)
        return cls(
            snapshot_id=tuple(snapshot_id),
            semantic_fields=deep_freeze(dict(semantic_fields)),
            semantic_fingerprint=SnapshotFingerprintCodec.digest(payload),
            extraction_schema_version=extraction_schema_version,
            diagnostic_refs=deep_freeze(dict(diagnostic_refs or {})),
        )

    @classmethod
    def from_function_analysis(cls, analysis: Any) -> "AnalysisSnapshot":
        """Freeze the semantic extraction result, excluding mutable proof state."""

        to_dict = getattr(analysis, "to_dict", None)
        if not callable(to_dict):
            raise TypeError("analysis must provide object-derived to_dict() data")
        # Issue #22 PR-22-D: snapshot 1 つ分の最終表現（解析の `to_dict()` と効果要約の
        # 投影）を **1 つの直列化の作業量** として数える。木も木以外の値も、作る前か
        # record 1 件を作った直後に足され、合計が予算を超えた時点で残りを作らずに
        # pair terminal な限界になる（式 1 本ごとの予算とは別の aggregate）。
        with serialization_scope(
            site=SNAPSHOT_SERIALIZATION_SITE,
            target_parts=(
                "function_analysis_snapshot",
                getattr(analysis, "binary_id", None),
                getattr(analysis, "function_name", None),
                getattr(analysis, "entry_point", None),
            ),
        ) as work:
            return cls._from_function_analysis_with(analysis, to_dict, work)

    @classmethod
    def _from_function_analysis_with(cls, analysis: Any, to_dict: Any, work: Any) -> "AnalysisSnapshot":
        semantic_fields = dict(to_dict())
        # These fields describe execution/diagnostic state rather than the
        # immutable extraction premise.  Proofs are applied through a derived
        # view and must never mutate snapshot identity.
        for key in ("completed_recovery_proof_ids", "completed_recovery_proof_evidence"):
            semantic_fields.pop(key, None)
        semantic_notes, diagnostic_notes = _classify_analysis_notes(
            semantic_fields.pop("analysis_notes", ())
        )
        semantic_fields["semantic_analysis_notes"] = semantic_notes
        semantic_fields["effect_summary"] = _semantic_effect_summary_projection(
            getattr(analysis, "effect_summary", None), work,
        )
        function_ref = getattr(analysis, "function_ref", None)
        function_key = (
            function_ref.stable_key()
            if function_ref is not None and callable(getattr(function_ref, "stable_key", None))
            else (getattr(analysis, "function_name", None), getattr(analysis, "entry_point", None))
        )
        snapshot_id = (
            "function_analysis_snapshot",
            getattr(analysis, "binary_id", None),
            function_key,
            getattr(analysis, "analysis_scope_key", None),
        )
        return cls.create(
            snapshot_id,
            semantic_fields,
            diagnostic_refs={"function_ref": function_ref, "analysis_notes": diagnostic_notes},
        )


@dataclass(frozen=True)
class DerivedAnalysisView:
    view_id: Tuple[Any, ...]
    snapshot_id: Tuple[Any, ...]
    parent_view_id: Tuple[Any, ...] | None
    validated_proof_closure_id: Tuple[Any, ...]
    normalization_policy_digest: str
    view_builder_version: str
    semantic_surface: Mapping[str, Any]
    semantic_fingerprint: str
    fact_provenance: Mapping[Tuple[Any, ...], SemanticFactProvenance] = field(
        default_factory=dict, compare=False, hash=False
    )

    @classmethod
    def create(
        cls,
        *,
        snapshot_id: Tuple[Any, ...],
        parent_view_id: Tuple[Any, ...] | None,
        validated_proof_closure_id: Tuple[Any, ...],
        normalization_policy_digest: str,
        view_builder_version: str,
        semantic_surface: Mapping[str, Any],
        fact_provenance: Mapping[Tuple[Any, ...], SemanticFactProvenance] | None = None,
    ) -> "DerivedAnalysisView":
        fingerprint = SnapshotFingerprintCodec.digest(
            (snapshot_id, validated_proof_closure_id, normalization_policy_digest,
             view_builder_version, semantic_surface)
        )
        view_id = ("derived_view", tuple(snapshot_id), fingerprint)
        return cls(
            view_id=view_id,
            snapshot_id=tuple(snapshot_id),
            parent_view_id=parent_view_id,
            validated_proof_closure_id=tuple(validated_proof_closure_id),
            normalization_policy_digest=normalization_policy_digest,
            view_builder_version=view_builder_version,
            semantic_surface=deep_freeze(dict(semantic_surface)),
            semantic_fingerprint=fingerprint,
            fact_provenance=deep_freeze(dict(fact_provenance or {})),
        )
