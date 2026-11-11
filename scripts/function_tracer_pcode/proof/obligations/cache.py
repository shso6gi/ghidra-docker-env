"""Process-local caches with proof/attempt separation."""

from __future__ import annotations

from dataclasses import dataclass, field
from collections import OrderedDict
from threading import RLock
from typing import Any, Dict, Generic, Iterable, Mapping, Optional, Tuple, TypeVar

from scripts.function_tracer_pcode.proof.obligations.model import (
    AttemptKey,
    ProofArtifact,
    UnaryArtifactDomain,
)
from scripts.function_tracer_pcode.proof.obligations.proof import (
    ArtifactApplicabilityRecord,
    ViewPremiseRecord,
    validate_artifact_applicability,
    validate_proof_closure,
)
from scripts.function_tracer_pcode.proof.obligations.recurrence import (
    validate_recurrence_artifact_content,
)

T = TypeVar("T")


@dataclass(frozen=True)
class AttemptCacheEntry(Generic[T]):
    outcome: T
    query_digest: str
    query_size: int
    elapsed_time: float
    artifact_validation_status: str = "not_applicable"
    retry_eligible: bool = False
    #: 結果を出した query の文字列そのもの。key の digest が一致しても、文字列が違えば同じ query
    #: として再利用しない（#218 PR-D: digest は bucket を選ぶだけ）
    query_text: Optional[str] = field(default=None, repr=False, compare=False)

    def answers(self, query: str) -> bool:
        """この entry が `query` の結果か（文字列の厳密な一致）。"""

        return type(self.query_text) is str and self.query_text == query


class AttemptCache(Generic[T]):
    def __init__(self, max_entries: int = 4096) -> None:
        if max_entries <= 0:
            raise ValueError("AttemptCache max_entries must be positive")
        self.max_entries = int(max_entries)
        self._entries: "OrderedDict[Tuple[Any, ...], AttemptCacheEntry[T]]" = OrderedDict()
        self._lock = RLock()
        self.hits = 0
        self.misses = 0

    def get(self, key: AttemptKey) -> Optional[AttemptCacheEntry[T]]:
        with self._lock:
            value = self._entries.get(key.to_key())
            if value is None:
                self.misses += 1
            else:
                self.hits += 1
                self._entries.move_to_end(key.to_key())
            return value

    def put(self, key: AttemptKey, entry: AttemptCacheEntry[T]) -> None:
        with self._lock:
            frozen_key = key.to_key()
            self._entries[frozen_key] = entry
            self._entries.move_to_end(frozen_key)
            while len(self._entries) > self.max_entries:
                self._entries.popitem(last=False)

    def __len__(self) -> int:
        return len(self._entries)


@dataclass(frozen=True)
class ProofCacheEntry:
    artifact: ProofArtifact
    validation_record: ArtifactApplicabilityRecord


class ProofCache:
    """Stores only validated proof or counterexample artifacts."""

    def __init__(self) -> None:
        self._entries: Dict[Tuple[Any, ...], ProofCacheEntry] = {}

    @staticmethod
    def key(entry: ProofCacheEntry) -> Tuple[Any, ...]:
        artifact = entry.artifact
        record = entry.validation_record
        return (
            artifact.requirement_id.to_key(), artifact.premise_digest,
            artifact.producer_version, artifact.encoding_version,
            record.target_view_id, record.premise_digest,
        )

    def put(
        self,
        artifact: ProofArtifact,
        *,
        artifacts: Iterable[ProofArtifact],
        root_artifact_ids: Iterable[Tuple[object, ...]],
        view_records: Mapping[Tuple[object, ...], ViewPremiseRecord],
        target_view: ViewPremiseRecord,
        candidate_independent_premise_digest: str,
    ) -> ProofCacheEntry:
        """Validate provenance and applicability inside the cache trust boundary."""

        if not artifact.is_validated:
            raise ValueError("ProofCache accepts only validated artifacts")
        materialized_artifacts = tuple(artifacts)
        matching_artifacts = tuple(
            candidate
            for candidate in materialized_artifacts
            if candidate.artifact_id == artifact.artifact_id
        )
        if len(matching_artifacts) != 1:
            raise ValueError(
                "ProofCache requires exactly one validated artifact with the target id"
            )
        if matching_artifacts[0] is not artifact:
            raise ValueError(
                "ProofCache target must be the exact process-local artifact validated in the closure"
            )
        closure = validate_proof_closure(
            materialized_artifacts,
            tuple(root_artifact_ids),
            view_records,
        )
        if artifact.artifact_id not in closure.topological_order:
            raise ValueError("proof artifact is absent from validated closure")
        source_view = view_records.get(artifact.produced_from_view_id)
        if source_view is None:
            raise ValueError("proof artifact source view is unavailable")
        record = validate_artifact_applicability(
            artifact,
            source_view=source_view,
            target_view=target_view,
            candidate_independent_premise_digest=candidate_independent_premise_digest,
            validated_closure_id=closure.closure_id,
        )
        if record.status != "applicable" or not record.candidate_independent:
            raise ValueError("ProofCache requires candidate-independent applicability")
        entry = ProofCacheEntry(artifact, record)
        self._entries[self.key(entry)] = entry
        return entry

    def get(self, key: Tuple[Any, ...]) -> Optional[ProofCacheEntry]:
        return self._entries.get(key)


@dataclass(frozen=True)
class ValidatedUnaryArtifactEntry:
    artifact: ProofArtifact
    domain: str
    function_premise_digest: str
    function_snapshot_fingerprint: str
    semantic_seed_digest: str
    normalization_policy_digest: str
    attempt_candidate_independent: bool
    pair_independent: bool
    closure_artifacts: Tuple[ProofArtifact, ...] = ()
    source_view_records: Mapping[Tuple[Any, ...], ViewPremiseRecord] = field(
        default_factory=dict, compare=False, hash=False
    )
    premise_schema_id: str = "function_unary_premise_v2"
    premise_codec_id: str = "snapshot_fingerprint_codec_v1"
    proposal_digest: Optional[str] = None
    function_recurrence_binding_digest: Optional[str] = None

    @property
    def outcome_seed_digest(self) -> str:
        """Compatibility alias for the original return-outcome-only API."""

        return self.semantic_seed_digest


class ValidatedUnaryArtifactCache:
    """Process-local cache for function-scoped, pair-independent proof artifacts."""

    def __init__(self, max_entries: int = 2048) -> None:
        if max_entries <= 0:
            raise ValueError("ValidatedUnaryArtifactCache max_entries must be positive")
        self.max_entries = int(max_entries)
        self._entries: "OrderedDict[Tuple[Any, ...], ValidatedUnaryArtifactEntry]" = OrderedDict()
        self._lock = RLock()

    @staticmethod
    def key(
        domain: str,
        requirement_key: Tuple[Any, ...],
        function_premise_digest: str,
    ) -> Tuple[Any, ...]:
        return (
            "validated_unary_artifact_v2",
            UnaryArtifactDomain.normalize(domain),
            requirement_key,
            function_premise_digest,
        )

    def put(self, entry: ValidatedUnaryArtifactEntry) -> None:
        if UnaryArtifactDomain.normalize(entry.domain) == UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value:
            # Issue #297: a recurrence artifact is stored only with the proposal it
            # proves (``put_recurrence`` re-validates the return binding subproof).
            raise ValueError("recurrence artifacts must be stored with their selected proposal")
        self._store(entry)

    def _store(self, entry: ValidatedUnaryArtifactEntry) -> None:
        if not entry.artifact.is_validated:
            raise ValueError("unary cache accepts only validated artifacts")
        if not entry.attempt_candidate_independent:
            raise ValueError("unary artifact depends on an attempt/counterexample candidate")
        if not entry.pair_independent:
            raise ValueError("unary artifact depends on a pair peer or side label")
        try:
            normalized_domain = UnaryArtifactDomain.normalize(entry.domain)
            UnaryArtifactDomain(normalized_domain)
        except ValueError as exc:
            raise ValueError("unary artifact has an unsupported semantic domain") from exc
        is_recurrence = normalized_domain == UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value
        proposal_fields_present = bool(
            entry.proposal_digest and entry.function_recurrence_binding_digest
        )
        if is_recurrence != proposal_fields_present:
            raise ValueError("unary artifact proposal binding does not match its domain")
        if is_recurrence:
            from scripts.function_tracer_pcode.proof.obligations.recurrence import (
                validate_recurrence_requirement_target,
            )

            target = entry.artifact.requirement_id.proof_target_key
            try:
                fields = dict(target[1:])
                validate_recurrence_requirement_target(
                    entry.artifact.requirement_id,
                    seed_core_digest=str(fields["seed_core_digest"]),
                    proposal_digest=str(entry.proposal_digest),
                    function_recurrence_binding_digest=str(
                        entry.function_recurrence_binding_digest
                    ),
                    proof_stage=str(fields["proof_stage"]),
                    proof_target_semantic_key=tuple(fields["proof_target"]),
                )
            except (KeyError, TypeError, ValueError) as exc:
                raise ValueError("invalid recurrence requirement target") from exc
        key = self.key(
            entry.domain,
            entry.artifact.requirement_id.to_key(),
            entry.function_premise_digest,
        )
        with self._lock:
            self._entries[key] = entry
            self._entries.move_to_end(key)
            while len(self._entries) > self.max_entries:
                self._entries.popitem(last=False)

    def get(
        self,
        requirement_key: Tuple[Any, ...],
        function_premise_digest: str,
        *,
        domain: str = UnaryArtifactDomain.RETURN_OUTCOME_V1.value,
        function_snapshot_fingerprint: str,
        semantic_seed_digest: Optional[str] = None,
        outcome_seed_digest: Optional[str] = None,
        normalization_policy_digest: Optional[str] = None,
        producer_version: str,
        encoding_version: str,
        premise_schema_id: Optional[str] = None,
        premise_codec_id: Optional[str] = None,
        proposal_digest: Optional[str] = None,
        function_recurrence_binding_digest: Optional[str] = None,
    ) -> Optional[ValidatedUnaryArtifactEntry]:
        expected_seed_digest = semantic_seed_digest or outcome_seed_digest
        if not expected_seed_digest:
            raise ValueError("unary cache lookup requires a semantic seed digest")
        normalized_domain = UnaryArtifactDomain.normalize(domain)
        key = self.key(normalized_domain, requirement_key, function_premise_digest)
        with self._lock:
            entry = self._entries.get(key)
            if entry is None:
                return None
            if (
                entry.function_snapshot_fingerprint != function_snapshot_fingerprint
                or entry.semantic_seed_digest != expected_seed_digest
                or entry.domain != normalized_domain
                or (
                    normalization_policy_digest is not None
                    and entry.normalization_policy_digest != str(normalization_policy_digest)
                )
                or entry.artifact.producer_version != producer_version
                or entry.artifact.encoding_version != encoding_version
                or (
                    premise_schema_id is not None
                    and entry.premise_schema_id != premise_schema_id
                )
                or (
                    premise_codec_id is not None
                    and entry.premise_codec_id != premise_codec_id
                )
                or entry.proposal_digest != proposal_digest
                or entry.function_recurrence_binding_digest
                != function_recurrence_binding_digest
            ):
                return None
            self._entries.move_to_end(key)
            return entry

    def put_recurrence(self, entry: ValidatedUnaryArtifactEntry, *, proposal: Any) -> None:
        if entry.domain != UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value:
            raise ValueError("put_recurrence requires the recurrence domain")
        validate_recurrence_artifact_content(
            entry.artifact,
            seed_core_digest=entry.semantic_seed_digest,
            proposal_digest=str(entry.proposal_digest or ""),
            function_recurrence_binding_digest=str(
                entry.function_recurrence_binding_digest or ""
            ),
            proposal=proposal,
        )
        self._store(entry)

    def get_recurrence(
        self,
        requirement_key: Tuple[Any, ...],
        function_premise_digest: str,
        **kwargs: Any,
    ) -> Optional[ValidatedUnaryArtifactEntry]:
        proposal_digest = kwargs.get("proposal_digest")
        binding_digest = kwargs.get("function_recurrence_binding_digest")
        if not proposal_digest or not binding_digest:
            raise ValueError("recurrence lookup requires proposal and function binding digests")
        return self.get(
            requirement_key,
            function_premise_digest,
            domain=UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value,
            **kwargs,
        )

    def find_applicable_artifact(
        self,
        artifact_id: Tuple[Any, ...],
        *,
        function_snapshot_fingerprint: str,
    ) -> Optional[ValidatedUnaryArtifactEntry]:
        """Return the exact currently-applicable unary artifact, never a digest peer."""

        with self._lock:
            matches = [
                entry
                for entry in self._entries.values()
                if (
                    entry.artifact.artifact_id == tuple(artifact_id)
                    and entry.function_snapshot_fingerprint
                    == str(function_snapshot_fingerprint)
                    and entry.artifact.is_validated
                )
            ]
            return matches[0] if len(matches) == 1 else None
