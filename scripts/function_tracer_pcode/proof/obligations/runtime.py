"""Production proof-obligation runtime and dependency based rescheduling."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, List, Mapping, Optional, Set, Tuple

from scripts.function_tracer_pcode.core.stage_clock import stage_region
from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import (
    ComparisonAuthorityBinding,
    current_comparison,
    evidence_authority_holds,
    run_in_current_comparison,
)
from scripts.function_tracer_pcode.proof.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
)
from scripts.function_tracer_pcode.proof.obligations.cache import (
    ProofCache,
    ValidatedUnaryArtifactCache,
    ValidatedUnaryArtifactEntry,
)
from scripts.function_tracer_pcode.proof.obligations.model import (
    ExecutionState,
    FunctionProofOutcome,
    ObligationInstanceId,
    ProofArtifact,
    SemanticFactProvenance,
    UnaryArtifactDomain,
)
from scripts.function_tracer_pcode.proof.obligations.proof import (
    ViewPremiseRecord,
    validate_proof_closure,
)
from scripts.function_tracer_pcode.proof.obligations.snapshot import (
    AnalysisSnapshot,
    DerivedAnalysisView,
    SnapshotFingerprintCodec,
)
from scripts.function_tracer_pcode.proof.obligations.unary_premise import (
    build_function_unary_premise,
)
from scripts.function_tracer_pcode.proof.obligations.worklist import ProofWorklist, WorkItem
from scripts.function_tracer_pcode.proof.obligations.guard_overlap import WorkResultRole
from scripts.function_tracer_pcode.proof.obligations.pair_disposition import (
    PairDispositionLedger,
    PairLedgerBinding,
    PairLedgerManager,
    RuntimeQuiescenceCertificate,
)
from scripts.function_tracer_pcode.core.recurrence_contracts import (
    QuarantinedRecurrenceProposal,
    RecurrenceSeedCore,
    function_recurrence_binding_digest,
)
from scripts.function_tracer_pcode.proof.obligations.recurrence import (
    validate_recurrence_artifact_content,
    validate_recurrence_requirement_binding,
)


GLOBAL_VALIDATED_UNARY_ARTIFACT_CACHE = ValidatedUnaryArtifactCache()


_GATE_DEPENDENTS: Mapping[str, Tuple[str, ...]] = {
    "return_coverage": ("guard_overlap", "value_relation"),
    "return_width": ("value_relation",),
    "call_effect": ("value_relation", "counterexample_safety"),
    "loop_summary": ("guard_overlap", "value_relation"),
    "counterexample_safety": (),
}


@dataclass(frozen=True)
class ObligationExecutionEvent:
    event: str
    obligation_key: Tuple[Any, ...]
    view_id: Tuple[Any, ...]
    kind: str


@dataclass(frozen=True)
class PendingCounterexampleSafety:
    """A SAT value query whose model has not passed global safety replay."""

    requirement_key: Tuple[Any, ...]
    counterexample_raw: Any


class ComparisonRuntimeMismatch(RuntimeError):
    """別の比較（raw pair か最終 relation が違う）の仕事を、この runtime に持ち込もうとした。"""


def _planner_in_current_comparison(planner: Callable[..., Any]) -> Callable[..., Any]:
    """replanner とそれが返す producer を、登録した比較の範囲の下で実行する。

    replanner は後の gate 完了から呼ばれるので、呼ばれた時点の範囲ではなく、
    それを登録した比較の authority で証拠を照合する（Issue #167）。
    """

    def plan(*args: Any) -> Any:
        requirement, kind, producer = planner(*args)
        if producer is not None:
            producer = run_in_current_comparison(producer)
        return requirement, kind, producer

    return run_in_current_comparison(plan)


@dataclass
class ObligationRuntimeSession:
    """Owns immutable views, proof artifacts, and the executable worklist.

    Issue #167: 1 つの runtime は 1 つの比較（``ComparisonAuthorityBinding``: raw pair と
    最終 relation）だけに仕える。artifact・view・dependency・producer・replanner・
    outcome・cache はすべてこの比較の state で、別の比較の仕事を持ち込むと
    ``ComparisonRuntimeMismatch`` で拒否する（別の比較は自分の runtime を使う。
    ``checker/strategy_execution.prepare_strategy_runtime``）。比較の外（binding の無い
    範囲）からは、比較の証拠も state も読まない仕事（branch の実行・view の記録）だけを
    受け付け、gate の計画・完了証拠の適用・outcome の読み出しは仕える比較の中でだけ行う。
    """

    base_view: DerivedAnalysisView
    current_view: DerivedAnalysisView
    worklist: ProofWorklist = field(default_factory=ProofWorklist)
    proof_cache: ProofCache = field(default_factory=ProofCache)
    events: List[ObligationExecutionEvent] = field(default_factory=list)
    artifacts: List[ProofArtifact] = field(default_factory=list)
    view_records: Dict[Tuple[Any, ...], ViewPremiseRecord] = field(default_factory=dict)
    dependencies: Dict[Tuple[Any, ...], Set[Tuple[Any, ...]]] = field(default_factory=dict)
    requirement_dependents: Dict[Tuple[Any, ...], Set[Tuple[Any, ...]]] = field(default_factory=dict)
    pair_query_replanners: Dict[Tuple[str, str], Callable[[], Tuple[ProofRequirementId, str, Callable[[], Any]]]] = field(default_factory=dict)
    target_query_replanners: Dict[Any, List[Callable[[], Tuple[ProofRequirementId, str, Callable[[], Any]]]]] = field(default_factory=dict)
    gate_replanners: Dict[Tuple[Any, ...], List[Callable[[], Tuple[ProofRequirementId, str, Callable[[], Any]]]]] = field(default_factory=dict)
    counterexample_safety_replanners: Dict[str, Callable[[PendingCounterexampleSafety], Tuple[ProofRequirementId, str, Callable[[], Any]]]] = field(default_factory=dict)
    callbacks: Dict[Tuple[Any, ...], Callable[[], Any]] = field(default_factory=dict)
    producers: Dict[Tuple[Any, ...], Callable[[], Any]] = field(default_factory=dict)
    results: Dict[Tuple[Any, ...], Any] = field(default_factory=dict)
    proof_outcomes: Dict[Tuple[Any, ...], FunctionProofOutcome] = field(default_factory=dict)
    pending_counterexamples: Dict[Tuple[Any, ...], PendingCounterexampleSafety] = field(default_factory=dict)
    reason_requirements: Dict[int, Tuple[ProofRequirementId, ...]] = field(default_factory=dict)
    #: ``reason_requirements`` の key（``id``）の持ち主。runtime が参照を保つので id は再利用されず、
    #: 読むときも同じ object であることを確かめる（object の id を authority の代わりにしない）。
    planned_reasons: Dict[int, Any] = field(default_factory=dict)
    unary_artifact_cache: ValidatedUnaryArtifactCache = field(
        default_factory=lambda: GLOBAL_VALIDATED_UNARY_ARTIFACT_CACHE
    )
    pair_ledger_manager: PairLedgerManager = field(default_factory=PairLedgerManager)
    #: この runtime が仕える比較（最初にこの runtime を使った比較が決める）。
    comparison_binding: Optional[ComparisonAuthorityBinding] = None

    @classmethod
    def create(cls, analysis1: Any, analysis2: Any) -> "ObligationRuntimeSession":
        # Issue #124: pair obligation runtime の構築を計測する。
        with stage_region("obligation_build"):
            left = cls._snapshot(analysis1, "left")
            right = cls._snapshot(analysis2, "right")
            pair_snapshot_id = ("analysis_pair", left.snapshot_id, right.snapshot_id)
            premise = SnapshotFingerprintCodec.digest(
                (left.semantic_fingerprint, right.semantic_fingerprint)
            )
            view = DerivedAnalysisView.create(
                snapshot_id=pair_snapshot_id,
                parent_view_id=None,
                validated_proof_closure_id=("proof_closure", ()),
                normalization_policy_digest="legacy-normalization-surface-v1",
                view_builder_version="obligation-runtime-v1",
                semantic_surface={
                    "left_snapshot": left.semantic_fingerprint,
                    "right_snapshot": right.semantic_fingerprint,
                    "premise_digest": premise,
                    "applied_artifact_ids": (),
                },
            )
            session = cls(view, view)
            session.view_records[view.view_id] = ViewPremiseRecord(view.view_id, premise)
            return session

    @classmethod
    def create_unary(
        cls,
        analysis: Any,
        *,
        domain: str = UnaryArtifactDomain.RETURN_OUTCOME_V1.value,
        semantic_seed: Any = None,
        domain_contract: Any,
        normalization_policy_digest: str,
    ) -> "ObligationRuntimeSession":
        # Issue #124: unary obligation runtime の構築を計測する。
        with stage_region("obligation_build"):
            normalized_domain = UnaryArtifactDomain.normalize(domain)
            snapshot = cls._snapshot(analysis, "unary")
            seed = semantic_seed
            if seed is None and normalized_domain == UnaryArtifactDomain.RETURN_OUTCOME_V1.value:
                seed = getattr(analysis, "outcome_seed", None)
            unary_premise = build_function_unary_premise(
                normalized_domain,
                snapshot.semantic_fingerprint,
                seed,
                domain_contract,
                normalization_policy_digest,
            )
            seed_digest = unary_premise.semantic_seed_digest
            premise = unary_premise.function_premise_digest
            view = DerivedAnalysisView.create(
                snapshot_id=("function_analysis", snapshot.snapshot_id),
                parent_view_id=None,
                validated_proof_closure_id=("proof_closure", ()),
                normalization_policy_digest=str(normalization_policy_digest),
                view_builder_version="unary-obligation-runtime-v1",
                semantic_surface={
                    "function_snapshot": snapshot.semantic_fingerprint,
                    "unary_artifact_domain": normalized_domain,
                    "domain_contract": SnapshotFingerprintCodec.freeze(domain_contract),
                    "semantic_seed_digest": seed_digest,
                    "premise_digest": premise,
                    "premise_schema_id": unary_premise.premise_schema_id,
                    "premise_codec_id": unary_premise.premise_codec_id,
                    "applied_artifact_ids": (),
                },
            )
            session = cls(view, view)
            session.view_records[view.view_id] = ViewPremiseRecord(view.view_id, premise)
            return session

    def publish_unary_artifact(
        self,
        artifact: ProofArtifact,
        *,
        domain: str = UnaryArtifactDomain.RETURN_OUTCOME_V1.value,
        semantic_seed_digest: Optional[str] = None,
        function_snapshot_fingerprint: str,
        outcome_seed_digest: Optional[str] = None,
        function_premise_digest: str,
        normalization_policy_digest: Optional[str] = None,
        attempt_candidate_independent: bool,
        pair_independent: bool,
        proposal_digest: Optional[str] = None,
        function_recurrence_binding_digest: Optional[str] = None,
    ) -> ValidatedUnaryArtifactEntry:
        source_record = self.view_records.get(artifact.produced_from_view_id)
        if source_record is None:
            raise ValueError("unary artifact source view is unavailable")
        closure = validate_proof_closure(
            tuple(self.artifacts),
            (artifact.artifact_id,),
            self.view_records,
        )
        seed_digest = semantic_seed_digest or outcome_seed_digest
        if not seed_digest:
            raise ValueError("publishing a unary artifact requires a semantic seed digest")
        policy_digest = normalization_policy_digest or self.current_view.normalization_policy_digest
        surface = self.current_view.semantic_surface
        if str(function_premise_digest) != str(
            self.current_view.semantic_surface.get("premise_digest") or ""
        ):
            raise ValueError("published unary artifact premise is not the runtime premise")
        if str(seed_digest) != str(surface.get("semantic_seed_digest") or ""):
            raise ValueError("published unary artifact seed is not the runtime seed")
        normalized_domain = UnaryArtifactDomain.normalize(domain)
        if normalized_domain == UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value:
            raise ValueError(
                "recurrence artifacts must be published with a selected proposal"
            )
        entry = ValidatedUnaryArtifactEntry(
            artifact=artifact,
            domain=normalized_domain,
            function_premise_digest=str(function_premise_digest),
            function_snapshot_fingerprint=function_snapshot_fingerprint,
            semantic_seed_digest=str(seed_digest),
            normalization_policy_digest=str(policy_digest),
            attempt_candidate_independent=bool(attempt_candidate_independent),
            pair_independent=bool(pair_independent),
            closure_artifacts=tuple(
                item for artifact_id in closure.topological_order
                for item in self.artifacts if item.artifact_id == artifact_id
            ),
            source_view_records=dict(self.view_records),
            premise_schema_id=str(surface.get("premise_schema_id") or ""),
            premise_codec_id=str(surface.get("premise_codec_id") or ""),
            proposal_digest=proposal_digest,
            function_recurrence_binding_digest=function_recurrence_binding_digest,
        )
        self.unary_artifact_cache.put(entry)
        return entry

    def publish_recurrence_artifact(
        self,
        artifact: ProofArtifact,
        semantic_seed: RecurrenceSeedCore,
        selected_proposal: QuarantinedRecurrenceProposal,
    ) -> ValidatedUnaryArtifactEntry:
        """Publish only after recomputing the proposal-specific function binding."""

        if not isinstance(semantic_seed, RecurrenceSeedCore):
            raise TypeError("recurrence publication requires a RecurrenceSeedCore")
        if not isinstance(selected_proposal, QuarantinedRecurrenceProposal):
            raise TypeError("recurrence publication requires a selected proposal")
        surface = self.current_view.semantic_surface
        premise = str(surface.get("premise_digest") or "")
        snapshot = str(surface.get("function_snapshot") or "")
        if not premise or not snapshot:
            raise ValueError("recurrence publication requires a unary function runtime")
        if semantic_seed.digest != str(surface.get("semantic_seed_digest") or ""):
            raise ValueError("selected recurrence seed is not the runtime seed")
        if selected_proposal.seed_core_digest != semantic_seed.digest:
            raise ValueError("selected recurrence proposal is bound to another seed")
        proposal_digest = selected_proposal.digest
        binding_digest = function_recurrence_binding_digest(
            semantic_seed.digest, proposal_digest, premise
        )
        try:
            validate_recurrence_requirement_binding(
                artifact.requirement_id,
                seed_core_digest=semantic_seed.digest,
                proposal_digest=proposal_digest,
                function_recurrence_binding_digest=binding_digest,
            )
        except (TypeError, ValueError) as exc:
            raise ValueError(
                "recurrence artifact requirement is not bound to the selected proposal"
            ) from exc
        validate_recurrence_artifact_content(
            artifact,
            seed_core_digest=semantic_seed.digest,
            proposal_digest=proposal_digest,
            function_recurrence_binding_digest=binding_digest,
        )
        source_record = self.view_records.get(artifact.produced_from_view_id)
        if source_record is None:
            raise ValueError("unary artifact source view is unavailable")
        closure = validate_proof_closure(
            tuple(self.artifacts), (artifact.artifact_id,), self.view_records
        )
        entry = ValidatedUnaryArtifactEntry(
            artifact=artifact,
            domain=UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value,
            function_premise_digest=premise,
            function_snapshot_fingerprint=snapshot,
            semantic_seed_digest=semantic_seed.digest,
            normalization_policy_digest=self.current_view.normalization_policy_digest,
            attempt_candidate_independent=True,
            pair_independent=True,
            closure_artifacts=tuple(
                item for artifact_id in closure.topological_order
                for item in self.artifacts if item.artifact_id == artifact_id
            ),
            source_view_records=dict(self.view_records),
            premise_schema_id=str(surface.get("premise_schema_id") or ""),
            premise_codec_id=str(surface.get("premise_codec_id") or ""),
            proposal_digest=proposal_digest,
            function_recurrence_binding_digest=binding_digest,
        )
        self.unary_artifact_cache.put_recurrence(entry)
        return entry

    def import_unary_artifact_for_analysis(
        self,
        entry: ValidatedUnaryArtifactEntry,
        *,
        analysis: Any,
        domain: str = UnaryArtifactDomain.RETURN_OUTCOME_V1.value,
        semantic_seed: Any = None,
        selected_recurrence_proposal: Optional[QuarantinedRecurrenceProposal] = None,
        pair_side: str,
        domain_contract: Any,
        normalization_policy_digest: str,
    ) -> DerivedAnalysisView:
        normalized_domain = UnaryArtifactDomain.normalize(domain)
        if pair_side not in {"left", "right"}:
            raise ValueError("pair side must be left or right")
        current_snapshot = self._snapshot(analysis, pair_side)
        pair_snapshot_fingerprint = self.current_view.semantic_surface.get(
            f"{pair_side}_snapshot"
        )
        if pair_snapshot_fingerprint != current_snapshot.semantic_fingerprint:
            raise ValueError("unary artifact pair-side snapshot mismatch")
        seed = semantic_seed
        if seed is None and normalized_domain == UnaryArtifactDomain.RETURN_OUTCOME_V1.value:
            seed = getattr(analysis, "outcome_seed", None)
        unary_view = self.create_unary(
            analysis,
            domain=domain,
            semantic_seed=seed,
            domain_contract=domain_contract,
            normalization_policy_digest=normalization_policy_digest,
        )
        expected_function_premise_digest = unary_view.premise_digest
        expected_outcome_seed_digest = str(
            unary_view.current_view.semantic_surface["semantic_seed_digest"]
        )
        expected_snapshot_fingerprint = str(
            unary_view.current_view.semantic_surface["function_snapshot"]
        )
        if entry.function_premise_digest != expected_function_premise_digest:
            raise ValueError("unary artifact function premise mismatch")
        if entry.function_snapshot_fingerprint != expected_snapshot_fingerprint:
            raise ValueError("unary artifact function snapshot mismatch")
        if entry.domain != normalized_domain:
            raise ValueError("unary artifact domain mismatch")
        if entry.semantic_seed_digest != expected_outcome_seed_digest:
            raise ValueError("unary artifact semantic seed mismatch")
        if entry.normalization_policy_digest != str(normalization_policy_digest):
            raise ValueError("unary artifact normalization policy mismatch")
        if entry.premise_schema_id != str(
            unary_view.current_view.semantic_surface.get("premise_schema_id") or ""
        ):
            raise ValueError("unary artifact premise schema mismatch")
        if entry.premise_codec_id != str(
            unary_view.current_view.semantic_surface.get("premise_codec_id") or ""
        ):
            raise ValueError("unary artifact premise codec mismatch")
        if normalized_domain == UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value:
            if not isinstance(seed, RecurrenceSeedCore):
                raise TypeError("recurrence import requires a RecurrenceSeedCore")
            if not isinstance(
                selected_recurrence_proposal, QuarantinedRecurrenceProposal
            ):
                raise TypeError("recurrence import requires a selected proposal")
            if selected_recurrence_proposal.seed_core_digest != seed.digest:
                raise ValueError("recurrence import proposal seed mismatch")
            proposal_digest = selected_recurrence_proposal.digest
            binding_digest = function_recurrence_binding_digest(
                seed.digest, proposal_digest, expected_function_premise_digest
            )
            try:
                validate_recurrence_requirement_binding(
                    entry.artifact.requirement_id,
                    seed_core_digest=seed.digest,
                    proposal_digest=proposal_digest,
                    function_recurrence_binding_digest=binding_digest,
                )
            except (TypeError, ValueError) as exc:
                raise ValueError("recurrence import requirement mismatch") from exc
            validate_recurrence_artifact_content(
                entry.artifact,
                seed_core_digest=seed.digest,
                proposal_digest=proposal_digest,
                function_recurrence_binding_digest=binding_digest,
            )
            cached = self.unary_artifact_cache.get_recurrence(
                entry.artifact.requirement_id.to_key(),
                expected_function_premise_digest,
                function_snapshot_fingerprint=expected_snapshot_fingerprint,
                semantic_seed_digest=seed.digest,
                normalization_policy_digest=normalization_policy_digest,
                producer_version=entry.artifact.producer_version,
                encoding_version=entry.artifact.encoding_version,
                premise_schema_id=entry.premise_schema_id,
                premise_codec_id=entry.premise_codec_id,
                proposal_digest=proposal_digest,
                function_recurrence_binding_digest=binding_digest,
            )
            if cached is not entry:
                raise ValueError(
                    "recurrence artifact was not resolved by exact production cache lookup"
                )
        elif selected_recurrence_proposal is not None:
            raise ValueError("selected recurrence proposal used outside recurrence domain")
        validate_proof_closure(
            entry.closure_artifacts,
            (entry.artifact.artifact_id,),
            entry.source_view_records,
        )
        # Preserve the complete imported proof closure as real provenance.
        for view_id, record in entry.source_view_records.items():
            self.view_records.setdefault(view_id, record)
        for artifact in entry.closure_artifacts:
            if all(item.artifact_id != artifact.artifact_id for item in self.artifacts):
                self.artifacts.append(artifact)
        current_record = self.view_records[self.current_view.view_id]
        imported_ids = tuple(item.artifact_id for item in entry.closure_artifacts)
        missing_ids = tuple(
            artifact_id for artifact_id in imported_ids
            if artifact_id not in current_record.available_artifact_ids
        )
        if missing_ids:
            self.view_records[self.current_view.view_id] = ViewPremiseRecord(
                current_record.view_id,
                current_record.premise_digest,
                available_artifact_ids=current_record.available_artifact_ids + missing_ids,
                parent_view_id=current_record.parent_view_id,
            )
        evidence = dict(entry.artifact.payload)
        evidence["proof_source"] = "imported_unary_artifact"
        evidence["source_unary_artifact_id"] = entry.artifact.artifact_id
        if any(
            item.requirement_id == entry.artifact.requirement_id
            and item.payload.get("source_unary_artifact_id") == entry.artifact.artifact_id
            for item in self.artifacts
        ):
            return self.current_view
        return self._apply_artifact(entry.artifact.requirement_id, evidence)

    @staticmethod
    def _snapshot(analysis: Any, side: str) -> AnalysisSnapshot:
        if callable(getattr(analysis, "to_dict", None)):
            return AnalysisSnapshot.from_function_analysis(analysis)
        semantic = {
            "binary_id": getattr(analysis, "binary_id", None),
            "function_name": getattr(analysis, "function_name", None),
            "entry_point": getattr(analysis, "entry_point", None),
        }
        return AnalysisSnapshot.create(("minimal_analysis", side, tuple(semantic.items())), semantic)

    @property
    def premise_digest(self) -> str:
        return self.view_records[self.current_view.view_id].premise_digest

    def serves_comparison(self, binding: Optional[ComparisonAuthorityBinding]) -> bool:
        """``binding`` の比較の仕事をこの runtime で扱ってよいか。"""

        return binding is None or self.comparison_binding is None or self.comparison_binding == binding

    def claim_comparison(self, binding: Optional[ComparisonAuthorityBinding]) -> None:
        """この runtime を ``binding`` の比較に仕えさせる（別の比較なら拒否）。"""

        if not self.serves_comparison(binding):
            raise ComparisonRuntimeMismatch("obligation_runtime_comparison_mismatch")
        if binding is not None and self.comparison_binding is None:
            self.comparison_binding = binding

    def _enter_current_comparison(self) -> None:
        self.claim_comparison(current_comparison())

    def _require_current_comparison(self) -> None:
        """authority を読む・作る仕事は、この runtime が仕える比較の中でだけ行う。

        比較の外（binding の無い範囲）から、ある比較に仕える runtime の artifact・outcome を
        読ませない（証拠 record の照合だけでは、runtime の state が漏れる）。
        """

        current = current_comparison()
        if self.comparison_binding is not None and current != self.comparison_binding:
            raise ComparisonRuntimeMismatch("obligation_runtime_comparison_mismatch")
        self.claim_comparison(current)

    def _bound_producer(self, callback: Optional[Callable[[], Any]]) -> Optional[Callable[[], Any]]:
        """producer を、積んだ比較の範囲で実行する形にし、その比較をこの runtime に求める。"""

        if callback is None:
            self._enter_current_comparison()
            return None
        bound = run_in_current_comparison(callback)
        self.claim_comparison(bound.binding)
        return bound

    def schedule(
        self,
        requirement: ProofRequirementId,
        kind: str,
        callback: Optional[Callable[[], Any]] = None,
        *,
        depends_on: Iterable[ProofRequirementId] = (),
        payload: Any = None,
    ) -> WorkItem:
        # Issue #124: obligation の構築（scheduling）を計測する。producer の実行は run_next 側なので含まない。
        with stage_region("obligation_build"):
            callback = self._bound_producer(callback)
            instance = ObligationInstanceId(
                requirement,
                self.current_view.view_id,
                self.premise_digest,
            )
            item = WorkItem(instance, kind, payload)
            self.worklist.add(item)
            key = instance.to_key()
            if callback is not None:
                self.callbacks[key] = callback
                self.producers[requirement.to_key()] = callback
            for dependency in depends_on:
                self.dependencies.setdefault(dependency.to_key(), set()).add(requirement.to_key())
            self.events.append(ObligationExecutionEvent("scheduled", key, self.current_view.view_id, kind))
            return item

    def execute(
        self,
        requirement: ProofRequirementId,
        kind: str,
        producer: Callable[[], Any],
        *,
        depends_on: Iterable[ProofRequirementId] = (),
    ) -> Any:
        """Schedule and execute one concrete producer in the current view."""
        producer = self._bound_producer(producer)
        instance = ObligationInstanceId(
            requirement,
            self.current_view.view_id,
            self.premise_digest,
        )
        cached_key = instance.to_key()
        if cached_key in self.results:
            self.events.append(ObligationExecutionEvent(
                "result_reused",
                cached_key,
                self.current_view.view_id,
                kind,
            ))
            return self.results[cached_key]
        self.schedule(requirement, kind, producer, depends_on=depends_on)
        item, value = self.run_next()
        if item is None or item.obligation_id.requirement_id != requirement:
            raise RuntimeError("obligation producer execution order was violated")
        return value

    def open_pair_ledger(self, binding: PairLedgerBinding, expected_pairs: int) -> PairDispositionLedger:
        self._enter_current_comparison()
        if binding.derived_view_id != self.current_view.view_id or binding.premise_digest != self.premise_digest:
            raise ValueError("pair ledger binding is not current runtime generation")
        if (
            self.comparison_binding is not None
            and binding.comparison_authority_digest != self.comparison_binding.digest
        ):
            raise ComparisonRuntimeMismatch("pair ledger belongs to another comparison")
        return self.pair_ledger_manager.open(binding, expected_pairs)

    def pair_quiescence_certificate(self, ledger: PairDispositionLedger) -> RuntimeQuiescenceCertificate:
        owner_items = tuple(
            item for item in self.worklist.items()
            if item.state == ExecutionState.RUNNING
            and item.kind == "function_branch"
            and item.obligation_id.derived_view_id == self.current_view.view_id
            and tuple(item.obligation_id.requirement_id.proof_target_key)
            == ("branch", ledger.binding.branch_id)
        )
        if len(owner_items) > 1:
            raise RuntimeError("multiple active function-branch owners for pair ledger")
        pending_items = tuple(
            item for item in self.worklist.items()
            if item.state in {ExecutionState.READY, ExecutionState.RUNNING}
            and item.obligation_id.derived_view_id == self.current_view.view_id
            and item not in owner_items
        )
        return RuntimeQuiescenceCertificate(
            ledger.binding.stable_key(), ledger.expected_pairs, len(ledger.closures),
            len(pending_items), len(ledger.provisional), self.current_view.view_id,
            self.premise_digest,
            tuple((item.kind, item.state.value) for item in pending_items),
            (
                owner_items[0].obligation_id.to_key()
                if owner_items else ()
            ),
        )

    def drain_pair_terminal_work(self) -> Tuple[Any, ...]:
        """Execute terminal safety checks; refuse to hide other pending proof work."""

        pending = tuple(
            item for item in self.worklist.items()
            if item.state == ExecutionState.READY
            and item.obligation_id.derived_view_id == self.current_view.view_id
        )
        unsupported = tuple(item.kind for item in pending if item.kind != "counterexample_safety")
        if unsupported:
            raise RuntimeError(
                "pair ledger has non-terminal pending proof work: "
                + ",".join(sorted(unsupported))
            )
        outcomes = []
        while any(
            item.state == ExecutionState.READY
            and item.obligation_id.derived_view_id == self.current_view.view_id
            for item in self.worklist.items()
        ):
            item, value = self.run_next()
            if item is None or item.kind != "counterexample_safety":
                raise RuntimeError("terminal safety work execution order was violated")
            outcomes.append(value)
        return tuple(outcomes)

    def run_next(self) -> Tuple[Optional[WorkItem], Any]:
        item = self.worklist.pop()
        if item is None:
            return None, None
        key = item.obligation_id.to_key()
        callback = self.callbacks.get(key)
        value = callback() if callback is not None else item.payload
        self.results[key] = value
        outcomes = self.proof_outcomes
        pending_safety: Optional[PendingCounterexampleSafety] = None
        result_role = getattr(value, "result_role", WorkResultRole.PROOF_DECISION)
        if result_role == WorkResultRole.NON_DECISIONAL_EXECUTION:
            pass
        elif isinstance(value, FunctionProofOutcome):
            outcomes[item.obligation_id.requirement_id.to_key()] = value
        elif hasattr(value, "is_equivalent"):
            semantic = getattr(value, "is_equivalent", None)
            if semantic is True:
                outcome = FunctionProofOutcome.EQUIVALENT
            elif semantic is False and item.kind == "value_relation":
                # A replanned SAT query is only a candidate counterexample.
                # The ordinary pairwise path validates its model across every
                # case and checks analysis/replay safety before deciding NOT_EQ.
                # A local replanner does not own that complete validation
                # surface, so retain the model for a counterexample_safety
                # obligation and keep the decision inconclusive.
                outcome = FunctionProofOutcome.INCONCLUSIVE
                requirement_key = item.obligation_id.requirement_id.to_key()
                pending_safety = PendingCounterexampleSafety(
                    requirement_key=requirement_key,
                    counterexample_raw=getattr(value, "counterexample_raw", None),
                )
                self.pending_counterexamples[requirement_key] = pending_safety
            elif semantic is False:
                outcome = FunctionProofOutcome.NOT_EQUIVALENT
            else:
                outcome = FunctionProofOutcome.INCONCLUSIVE
            outcomes[item.obligation_id.requirement_id.to_key()] = outcome
        if item.state == ExecutionState.RUNNING:
            self.worklist.complete(item)
            event = "completed"
        elif item.state == ExecutionState.SUPERSEDED:
            # A producer may create a child view while it is running.  Its
            # result is returned to the branch controller but never reattached
            # to the superseded parent generation.
            event = "completed_superseded"
        else:
            raise ValueError(f"work item left running in invalid state: {item.state}")
        self.events.append(ObligationExecutionEvent(event, key, self.current_view.view_id, item.kind))
        if pending_safety is not None:
            self._schedule_counterexample_safety(item, pending_safety)
        return item, value

    def plan_proof_gates(
        self,
        result: Any,
        gate_for_kind: Mapping[str, str],
        producer_factory: Callable[[str, Any, ProofRequirementId], Callable[[], FunctionProofOutcome]],
    ) -> Tuple[ProofRequirementId, ...]:
        self._require_current_comparison()
        requirements: List[ProofRequirementId] = []
        seen: Set[Tuple[Any, ...]] = set()
        reasons = tuple(getattr(result, "unknown_reasons", ()) or ())
        for reason in reasons:
            proof_kind = str(getattr(reason, "recovery_proof_kind", "") or "")
            gate_kind = gate_for_kind.get(proof_kind)
            if getattr(reason, "reason_id", None) in {
                "loop_exact_summary_relation_unproven",
                "loop_summary_guard_correspondence_unproven",
                "loop_summary_semantic_equality_unproven",
                "loop_summary_structure_correspondence_unproven",
                "phi_circular_replacement_unproven",
                "readonly_identity_missing",
            }:
                gate_kind = "loop_summary"
            if gate_kind is None:
                continue
            typed = tuple(getattr(reason, "proof_requirement_ids", ()) or ())
            candidates: List[ProofRequirementId] = []
            for payload in typed:
                try:
                    candidates.append(ProofRequirementId.from_dict(payload))
                except (TypeError, ValueError):
                    continue
            if not candidates:
                reason_id = getattr(reason, "reason_id", None)
                if not isinstance(reason_id, str) or not reason_id:
                    continue
                target = getattr(reason, "object_target_key", None) or (
                    "semantic_reason_target", reason_id,
                    getattr(reason, "pair_or_case", None),
                )
                contract = ProofRequirementContract(
                    proposition=proof_kind,
                    observation_surface=(gate_kind,),
                    active_precondition=(getattr(reason, "stage", None),),
                )
                candidates.append(ProofRequirementId.create(proof_kind, target, contract))
            for requirement in candidates:
                if requirement.to_key() in seen:
                    continue
                seen.add(requirement.to_key())
                requirements.append(requirement)
                self.planned_reasons[id(reason)] = reason
                self.reason_requirements.setdefault(id(reason), tuple())
                self.reason_requirements[id(reason)] += (requirement,)
                self.schedule(
                    requirement,
                    gate_kind,
                    producer_factory(gate_kind, reason, requirement),
                    payload=reason,
                )
                replanners = []
                pair_id = getattr(reason, "pair_or_case", None)
                if pair_id:
                    for dependent_kind in _GATE_DEPENDENTS.get(gate_kind, ()):
                        replanner = self.pair_query_replanners.get(
                            (str(pair_id), dependent_kind)
                        )
                        if replanner is not None:
                            replanners.append(replanner)
                target = getattr(reason, "object_target_key", None)
                if target is not None:
                    replanners.extend(
                        self.target_query_replanners.get(
                            SnapshotFingerprintCodec.freeze(target),
                            (),
                        )
                    )
                if replanners:
                    self.gate_replanners[requirement.to_key()] = list(dict.fromkeys(replanners))
        return tuple(requirements)

    def register_pair_query_replanner(
        self,
        pair_id: str,
        kind: str,
        replanner: Callable[[], Tuple[ProofRequirementId, str, Callable[[], Any]]],
    ) -> None:
        self._enter_current_comparison()
        self.pair_query_replanners[(str(pair_id), str(kind))] = _planner_in_current_comparison(replanner)

    def register_target_query_replanner(
        self,
        target_key: Any,
        replanner: Callable[[], Tuple[ProofRequirementId, str, Callable[[], Any]]],
    ) -> None:
        self._enter_current_comparison()
        frozen = SnapshotFingerprintCodec.freeze(target_key)
        self.target_query_replanners.setdefault(frozen, []).append(
            _planner_in_current_comparison(replanner)
        )

    def register_counterexample_safety_replanner(
        self,
        pair_id: str,
        replanner: Callable[[PendingCounterexampleSafety], Tuple[ProofRequirementId, str, Callable[[], Any]]],
    ) -> None:
        self._enter_current_comparison()
        self.counterexample_safety_replanners[str(pair_id)] = _planner_in_current_comparison(replanner)

    def _schedule_counterexample_safety(
        self,
        value_item: WorkItem,
        pending: PendingCounterexampleSafety,
    ) -> None:
        target = value_item.obligation_id.requirement_id.proof_target_key
        if len(target) < 2 or target[0] != "pair_query":
            return
        replanner = self.counterexample_safety_replanners.get(str(target[1]))
        if replanner is None:
            return
        value_key = value_item.obligation_id.requirement_id.to_key()
        parent_dependents = tuple(
            dependents
            for dependents in self.requirement_dependents.values()
            if value_key in dependents
        )
        # Initial pairwise SAT follows the ordinary inline safety path.  Only a
        # query rescheduled by a completed proof gate is handled here.
        if not parent_dependents:
            return
        requirement, kind, producer = replanner(pending)
        self.schedule(
            requirement,
            kind,
            producer,
            depends_on=(value_item.obligation_id.requirement_id,),
        )
        safety_key = requirement.to_key()
        for dependents in parent_dependents:
            dependents.add(safety_key)
        self.events.append(ObligationExecutionEvent(
            "counterexample_safety_scheduled",
            requirement.to_key(),
            self.current_view.view_id,
            kind,
        ))

    def apply_completed_evidence(
        self,
        evidence_wrappers: Iterable[Mapping[str, Any]],
        *,
        reasons: Iterable[Any] = (),
    ) -> Tuple[DerivedAnalysisView, ...]:
        self._require_current_comparison()
        produced: List[DerivedAnalysisView] = []
        for wrapper in evidence_wrappers:
            evidence = wrapper.get("evidence", wrapper)
            if not isinstance(evidence, Mapping):
                continue
            if not evidence_authority_holds(evidence):
                # 別の比較で作った証拠・scope の無い証拠から、この比較の view を作らない（Issue #167）。
                continue
            status = str(evidence.get("proof_status") or evidence.get("status") or "").lower()
            if status not in {"complete", "completed", "discharged", "proven", "verified"}:
                continue
            requirement_payload = evidence.get("proof_requirement_id")
            if not isinstance(requirement_payload, Mapping):
                requirement_payload = self._unique_requirement_for_legacy_evidence(
                    evidence,
                    reasons,
                )
            if not isinstance(requirement_payload, Mapping):
                continue
            try:
                requirement = ProofRequirementId.from_dict(requirement_payload)
            except (TypeError, ValueError):
                continue
            if any(
                artifact.requirement_id.to_key() == requirement.to_key()
                for artifact in self.artifacts
            ):
                # One requirement denotes one proposition.  Re-emitting the
                # same completed evidence must not create an unbounded chain
                # of derived views or pair replans.
                continue
            producer_outcome = self.proof_outcomes.get(
                requirement.to_key(),
                FunctionProofOutcome.INCONCLUSIVE,
            )
            if producer_outcome == FunctionProofOutcome.INCONCLUSIVE:
                # A producer status string is not proof validation.  Only an
                # exact typed producer outcome may cross the cache/view boundary.
                continue
            produced.append(self._apply_artifact(requirement, evidence))
        return tuple(produced)

    @staticmethod
    def _unique_requirement_for_legacy_evidence(
        evidence: Mapping[str, Any],
        reasons: Iterable[Any],
    ) -> Optional[Mapping[str, Any]]:
        legacy_id = evidence.get("proof_obligation_id")
        if legacy_id is None:
            return None
        frozen_id = SnapshotFingerprintCodec.freeze(legacy_id)
        requirements: Dict[Tuple[Any, ...], Mapping[str, Any]] = {}
        for reason in reasons:
            reason_id = getattr(reason, "proof_obligation_id", None)
            if reason_id is None or SnapshotFingerprintCodec.freeze(reason_id) != frozen_id:
                continue
            for payload in getattr(reason, "proof_requirement_ids", ()) or ():
                if not isinstance(payload, Mapping):
                    continue
                try:
                    canonical = ProofRequirementId.from_dict(payload).to_dict()
                except (TypeError, ValueError):
                    continue
                requirements[ProofRequirementId.from_dict(canonical).to_key()] = canonical
        if len(requirements) != 1:
            return None
        return next(iter(requirements.values()))

    def _apply_artifact(self, requirement: ProofRequirementId, evidence: Mapping[str, Any]) -> DerivedAnalysisView:
        source = self.current_view
        source_record = self.view_records[source.view_id]
        artifact_id = (
            "proof_artifact",
            requirement.to_key(),
            SnapshotFingerprintCodec.digest(evidence),
        )
        artifact = ProofArtifact(
            artifact_id=artifact_id,
            requirement_id=requirement,
            produced_from_view_id=source.view_id,
            premise_digest=source_record.premise_digest,
            dependency_artifact_ids=tuple(source_record.available_artifact_ids),
            producer_id=str(evidence.get("proof_source") or "completed_recovery_proof"),
            artifact_validation_status="validated",
            payload=dict(evidence),
        )
        materialized = tuple(self.artifacts) + (artifact,)
        roots = tuple(item.artifact_id for item in materialized)
        closure = validate_proof_closure(materialized, roots, self.view_records)
        self.proof_cache.put(
            artifact,
            artifacts=materialized,
            root_artifact_ids=roots,
            view_records=self.view_records,
            target_view=source_record,
            candidate_independent_premise_digest=source_record.premise_digest,
        )
        applied = tuple(item.artifact_id for item in materialized)
        fact_id = ("proof_fact", requirement.to_key())
        provenance = dict(source.fact_provenance)
        provenance[fact_id] = SemanticFactProvenance(fact_id, source_artifact_ids=(artifact_id,))
        derived = DerivedAnalysisView.create(
            snapshot_id=source.snapshot_id,
            parent_view_id=source.view_id,
            validated_proof_closure_id=closure.closure_id,
            normalization_policy_digest=source.normalization_policy_digest,
            view_builder_version="obligation-runtime-v1",
            semantic_surface={**dict(source.semantic_surface), "applied_artifact_ids": applied},
            fact_provenance=provenance,
        )
        self.worklist.supersede_view(source.view_id)
        self.artifacts.append(artifact)
        self.current_view = derived
        derived_premise = SnapshotFingerprintCodec.digest((
            "derived_view_premise_v1",
            derived.semantic_fingerprint,
            closure.validation_digest,
            tuple(
                (item.artifact_id, SnapshotFingerprintCodec.digest(item.payload))
                for item in materialized
            ),
            derived.normalization_policy_digest,
            derived.view_builder_version,
        ))
        self.view_records[derived.view_id] = ViewPremiseRecord(
            derived.view_id,
            derived_premise,
            available_artifact_ids=applied,
            parent_view_id=source.view_id,
        )
        successor_ledger = self.pair_ledger_manager.plan_successor(
            derived.view_id,
            derived_premise,
            projection_refresh_required=str(requirement.proof_kind).startswith(
                "call_effect"
            ),
        )
        if successor_ledger is not None:
            self.events.append(ObligationExecutionEvent(
                "pair_ledger_replan_required",
                successor_ledger.stable_key(),
                derived.view_id,
                "guard_overlap",
            ))
        self.events.append(ObligationExecutionEvent("view_created", requirement.to_key(), derived.view_id, requirement.proof_kind))
        self._reschedule_dependents(requirement)
        return derived

    def outcome_for_reason(self, reason: Any) -> FunctionProofOutcome:
        self._require_current_comparison()
        requirements = (
            self.reason_requirements.get(id(reason), ())
            if self.planned_reasons.get(id(reason)) is reason
            else ()
        )
        validated = {artifact.requirement_id.to_key() for artifact in self.artifacts}
        outcomes = tuple(
            (
                self.proof_outcomes.get(
                    requirement.to_key(),
                    FunctionProofOutcome.INCONCLUSIVE,
                )
                if requirement.to_key() in validated
                else FunctionProofOutcome.INCONCLUSIVE
            )
            for requirement in requirements
        )
        dependent_outcomes = tuple(
            self.proof_outcomes.get(key, FunctionProofOutcome.INCONCLUSIVE)
            for requirement in requirements
            for key in self.requirement_dependents.get(requirement.to_key(), ())
        )
        if any(
            value == FunctionProofOutcome.NOT_EQUIVALENT
            for value in dependent_outcomes
        ):
            return FunctionProofOutcome.NOT_EQUIVALENT
        if dependent_outcomes and not all(
            value == FunctionProofOutcome.EQUIVALENT for value in dependent_outcomes
        ):
            return FunctionProofOutcome.INCONCLUSIVE
        if outcomes and all(value == FunctionProofOutcome.EQUIVALENT for value in outcomes):
            return FunctionProofOutcome.EQUIVALENT
        if any(value == FunctionProofOutcome.NOT_EQUIVALENT for value in outcomes):
            return FunctionProofOutcome.NOT_EQUIVALENT
        return FunctionProofOutcome.INCONCLUSIVE

    def _reschedule_dependents(self, completed: ProofRequirementId) -> None:
        for dependent_key in sorted(self.dependencies.get(completed.to_key(), ()), key=repr):
            requirement = ProofRequirementId(
                proof_kind=str(dependent_key[1]),
                proof_target_key=tuple(dependent_key[2]),
                proof_contract_key=tuple(dependent_key[3]),
                schema_version=int(dependent_key[0]),
            )
            self.schedule(
                requirement,
                requirement.proof_kind,
                self.producers.get(requirement.to_key()),
            )
            self.requirement_dependents.setdefault(completed.to_key(), set()).add(
                requirement.to_key()
            )
        for replanner in self.gate_replanners.get(completed.to_key(), ()):
            requirement, kind, producer = replanner()
            self.schedule(requirement, kind, producer)
            self.requirement_dependents.setdefault(completed.to_key(), set()).add(
                requirement.to_key()
            )

    def create_recursive_view(self, analysis1: Any, analysis2: Any, matches: Iterable[Any]) -> DerivedAnalysisView:
        self._enter_current_comparison()
        match_digest = SnapshotFingerprintCodec.digest(tuple(matches))
        requirement = ProofRequirementId.create(
            "recursive_call_abstraction",
            ("recursive_matches", match_digest),
            ProofRequirementContract(
                proposition="matched recursive calls share an abstract return",
                observation_surface=("return_and_effect",),
                active_precondition=(self.current_view.view_id,),
            ),
        )
        evidence = {
            "proof_requirement_id": requirement.to_dict(),
            "status": "complete",
            "proof_source": "recursive_abstraction_acceptance_gate",
            "match_digest": match_digest,
            "left_snapshot": self._snapshot(analysis1, "recursive_left").semantic_fingerprint,
            "right_snapshot": self._snapshot(analysis2, "recursive_right").semantic_fingerprint,
        }
        return self._apply_artifact(requirement, evidence)
