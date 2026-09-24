"""Immutable analysis snapshots and derived semantic views."""

from __future__ import annotations

from dataclasses import dataclass, field, fields, is_dataclass
from enum import Enum
import hashlib
import json
from types import MappingProxyType
from typing import Any, Mapping, Tuple

from scripts.function_tracer_pcode.core.budget_policy import serialization_scope
from scripts.function_tracer_pcode.core.builtin_containers import plain_field_value
from scripts.function_tracer_pcode.core.json_encoding import (
    LEGACY,
    RESULT_JSON_POLICY,
    cached_string_bytes,
    identity_key_of,
    is_json_record,
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

#: 比較（pair の comparison）が自分の観測として raw analysis に書き戻す note（Issue #167）。
#: semantic fingerprint には入る（blocker を知らずに作った証明を別の前提として扱う）が、
#: 比較の authority が束縛する raw pair の identity（``comparison_fingerprint``）には入らない:
#: 比較が自分で書いた観測で、比べている raw pair が別物になるわけではない。書くのは
#: ``record_comparison_annotation`` だけ（ここに無い note を比較が書くと identity が変わり、
#: 以後の branch は別の比較として扱われる = fail-closed）。
COMPARISON_ANNOTATION_NOTES = frozenset({
    "return_case_coverage_gap",
    "return_case_coverage_inconclusive",
})


def comparison_pair_identity(left: "AnalysisSnapshot", right: "AnalysisSnapshot") -> str:
    """比較の authority が束縛する raw pair の identity（左右の ``comparison_fingerprint`` の組）。"""

    return SnapshotFingerprintCodec.digest(
        ("comparison_raw_pair_v1", left.comparison_fingerprint, right.comparison_fingerprint)
    )


def record_comparison_annotation(analysis: Any, note: str) -> None:
    """比較の観測 ``note`` を raw analysis に書き戻す（登録済みの note だけ）。"""

    if note not in COMPARISON_ANNOTATION_NOTES:
        raise ValueError(f"unregistered comparison annotation: {note!r}")
    if note not in analysis.analysis_notes:
        analysis.analysis_notes.append(note)


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
    # Issue #22 PR-22-D: 投影は写しながら直列化の作業量へ足す（`freeze(budget=work)`）。
    # 効果が大量でも、予算を超えた時点で残りを投影しない。
    return SnapshotFingerprintCodec.freeze(effect_summary, budget=work)


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
    def freeze(cls, value: Any, *, budget: Any = None) -> Any:
        """値の canonical な写し。`budget` を渡すと、写す値の byte を写しながら足す。

        `budget`（`JsonBudget` の interface、snapshot では `SerializationWork`）は写した
        葉と容器の区切りごとに数え、超えた時点で残りを写さない。record の `to_dict()`
        は walker が同じ `budget` で数えながら作る（作ってから数えない）。
        """

        if budget is None:
            return cls._freeze_unmetered(value)
        return cls._freeze(value, _FreezeMeter(budget))

    @classmethod
    def _freeze_unmetered(cls, value: Any) -> Any:
        """数えない写し（fingerprint の digest など）。`_freeze(value, None)` と同じ値。

        digest は snapshot のたびに値全体を写すので、数える経路の分岐・helper を通さない
        （`test_the_unmetered_freeze_equals_the_metered_copy` が同じ値であることを固定）。
        """

        if value is None or isinstance(value, (bool, int, float, str)):
            return value
        if isinstance(value, Enum):
            return (value.__class__.__qualname__, value.value)
        if isinstance(value, bytes):
            return ("bytes", value.hex())
        freeze = cls._freeze_unmetered
        if isinstance(value, Mapping):
            return cls.sorted_mapping_items(
                tuple((freeze(key), freeze(item)) for key, item in value.items())
            )
        if isinstance(value, (tuple, list)):
            return tuple(freeze(v) for v in value)
        if isinstance(value, (set, frozenset)):
            return tuple(sorted((freeze(v) for v in value), key=repr))
        name = value.__class__.__qualname__
        has_key, identity_key = identity_key_of(value)
        if has_key:
            return (name, freeze(identity_key))
        if is_json_record(value):
            return (name, freeze(value.to_dict()))
        if is_dataclass(value):
            return (name, tuple((f.name, freeze(plain_field_value(value, f.name))) for f in fields(value)))
        raise TypeError(
            f"opaque object {value.__class__.__qualname__} has no object-derived stable identity"
        )

    @classmethod
    def _freeze(cls, value: Any, meter: Any) -> Any:
        if meter is None:
            return cls._freeze_unmetered(value)
        if value is None or isinstance(value, (bool, int, float, str)):
            if meter is not None:
                meter.scalar(value)
            return value
        if isinstance(value, Enum):
            if meter is not None:
                meter.frame(2)
                meter.scalar(value.__class__.__qualname__)
                meter.scalar(value.value)
            return (value.__class__.__qualname__, value.value)
        if isinstance(value, bytes):
            if meter is not None:
                meter.frame(2)
                meter.scalar("bytes")
                meter.scalar_bytes(2 * len(value) + 2)
            return ("bytes", value.hex())
        if isinstance(value, Mapping):
            if meter is not None:
                meter.frame(len(value))
            items = tuple(
                cls._pair(cls._freeze(key, meter), cls._freeze(item, meter), meter, key_counted=True)
                for key, item in value.items()
            )
            return cls.sorted_mapping_items(items)
        if isinstance(value, (tuple, list)):
            if meter is not None:
                meter.frame(len(value))
            return tuple(cls._freeze(v, meter) for v in value)
        if isinstance(value, (set, frozenset)):
            if meter is not None:
                meter.frame(len(value))
            return tuple(sorted((cls._freeze(v, meter) for v in value), key=repr))
        has_key, identity_key = identity_key_of(value)
        if has_key:
            return cls._tagged(value, cls._freeze_key(identity_key, meter), meter)
        if is_json_record(value):
            # walker が `budget` で数えながら作る。写しは数え済みの値から作る（json record でない
            # object の `to_dict()` は任意の producer なので呼ばない: object-derived な identity の
            # 無い値として拒む）
            built = RESULT_JSON_POLICY.materialize(value, budget=meter.budget)
            return cls._tagged(value, cls._freeze(built, None), meter)
        if is_dataclass(value):
            if meter is not None:
                meter.frame(len(fields(value)))
            return cls._tagged(
                value,
                tuple(
                    cls._pair(f.name, cls._freeze(plain_field_value(value, f.name), meter), meter)
                    for f in fields(value)
                ),
                meter,
            )
        raise TypeError(
            f"opaque object {value.__class__.__qualname__} has no object-derived stable identity"
        )

    @classmethod
    def _freeze_key(cls, key: Any, meter: Any) -> Any:
        """identity key（`stable_key()` / `to_key()` の値）の写し。

        key は同じ値が何度も現れる（snapshot ごとに同じ効果を投影する）ので、大きさは
        walker が数え（tuple だけの部分木は pair の間 cache）、予算に収まってから写す。
        """

        if meter is None:
            return cls._freeze(key, None)
        meter.count_value(key)
        return cls._freeze(key, None)

    @staticmethod
    def _pair(key: Any, item: Any, meter: Any, *, key_counted: bool = False) -> Tuple[Any, Any]:
        if meter is not None:
            meter.frame(2)
            if not key_counted:
                meter.scalar(key)
        return (key, item)

    @staticmethod
    def _tagged(value: Any, frozen: Any, meter: Any) -> Tuple[str, Any]:
        name = value.__class__.__qualname__
        if meter is not None:
            meter.frame(2)
            meter.scalar(name)
        return (name, frozen)

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


class _FreezeMeter:
    """`freeze(budget=...)` が写した値の byte を `budget` へ足す（写しの JSON の大きさ）。"""

    __slots__ = ("budget", "_policy")

    def __init__(self, budget: Any) -> None:
        self.budget = budget
        self._policy = RESULT_JSON_POLICY

    def frame(self, count: int) -> None:
        self.budget.charge(self._policy.container_frame_bytes(count))

    def scalar(self, value: Any) -> None:
        policy = self._policy
        if type(value) is str:
            size = cached_string_bytes(policy, value, max_bytes=self.budget.remaining())
        elif value is None or value is True:
            size = 4
        elif value is False:
            size = 5
        elif isinstance(value, str):
            size = policy.string_bytes(value, max_bytes=self.budget.remaining())
        elif isinstance(value, int):
            size = len(int.__repr__(int(value)))
        elif isinstance(value, float):
            size = len(float.__repr__(float(value)))
        else:
            size = policy.string_bytes(type(value).__qualname__)
        self.budget.charge(size)

    def scalar_bytes(self, size: int) -> None:
        self.budget.charge(size)

    def count_value(self, value: Any) -> None:
        """既に在る値（identity key）の JSON byte を、写す前に数えて足す。"""

        self._policy.count_into(value, self.budget, mode=LEGACY)


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

    @property
    def comparison_fingerprint(self) -> str:
        """比較の authority が束縛する identity（比較自身が書いた note を除く、Issue #167）。"""

        semantic_fields = dict(self.semantic_fields)
        semantic_fields["semantic_analysis_notes"] = tuple(
            note
            for note in semantic_fields.get("semantic_analysis_notes", ()) or ()
            if note not in COMPARISON_ANNOTATION_NOTES
        )
        return SnapshotFingerprintCodec.digest(
            ("comparison_identity_v1", self.extraction_schema_version, self.snapshot_id, semantic_fields)
        )

    @classmethod
    def from_function_analysis(cls, analysis: Any) -> "AnalysisSnapshot":
        """Freeze the semantic extraction result, excluding mutable proof state."""

        to_dict = getattr(analysis, "to_dict", None)
        if not callable(to_dict):
            raise TypeError("analysis must provide object-derived to_dict() data")
        # Issue #22 PR-22-D: snapshot 1 つ分の最終表現（解析の `to_dict()` と効果要約の
        # 投影）を **1 つの直列化の作業量** として数える。木は DAG のまま見積もってから、
        # 木以外の値は walker / codec が 1 要素ずつ写しながら足し（作ってから数えない）、
        # 合計が予算を超えた時点で残りを作らずに pair terminal な限界になる（式 1 本ごとの
        # 予算とは別の aggregate）。
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
        # 解析前提でない derived proof は下で捨てるので、表現できる解析は最初から
        # 作らない（`semantic_snapshot_dict`。残りは `to_dict()` と同じ値）
        semantic_view = getattr(analysis, "semantic_snapshot_dict", None)
        semantic_fields = dict(semantic_view() if callable(semantic_view) else to_dict())
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
        has_key, function_key = (False, None) if function_ref is None else identity_key_of(function_ref)
        if not has_key:
            function_key = (getattr(analysis, "function_name", None), getattr(analysis, "entry_point", None))
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
