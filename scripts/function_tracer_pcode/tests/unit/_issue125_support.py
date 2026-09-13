# -*- coding: utf-8 -*-
"""Issue #125 の帰属契約 test が共有する最小の lifecycle harness。

判定 authority の本物の registry（`PROCESS_DURABLE_*`）と本物の reducer を使い、
active cause を **occurrence 単位で** 組み立てる。producer 固有の受領証を作らずに
「同じ reason・別 target」「同じ target・別 scope」などの variant を作れるのが
狙いで、reducer の検証（registry / binding / 一意性）はすべて本物が効く。
"""

from types import SimpleNamespace

from scripts.function_tracer_pcode.authority.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    IdentityScope,
    ProofRequirement,
    RequirementCompletionReceipt,
    authority_digest,
)
from scripts.function_tracer_pcode.authority.lifecycle.reducer import (
    ShadowLifecycleReducer,
)
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
    CauseObservedEventAuthority,
    EventIntent,
    EventRecorder,
    EventType,
    RequirementCompletedEventAuthority,
)
from scripts.function_tracer_pcode.authority.process.supervisor import (
    PROCESS_DURABLE_REASON_REGISTRY,
    PROCESS_DURABLE_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.authority.registry import (
    SatisfactionBindingFactory,
    SemanticCauseIdentityFactory,
)
from scripts.function_tracer_pcode.core.errors import CauseAttributionKey


SAT_SAFETY_REASON_ID = "counterexample_analysis_safety_unproven"
SAT_SAFETY_TARGET_KIND = "counterexample_safety_gate"
SAT_SAFETY_CONTRACT = ("counterexample-safety-recovery", 1, "safety")
SAT_SAFETY_PROOF_KIND = "counterexample_safety"

OUTCOME_REASON_ID = "outcome_partition_completion_unproven"
OUTCOME_TARGET_KIND = "function_outcome_stage"
OUTCOME_CONTRACT = ("return-outcome-stage-recovery", 1, "stage_proof")
OUTCOME_PROOF_KIND = "unary_outcome_partition_complete"


class LifecycleHarness:
    """1 本の event stream を持つ最小 session（`recorder` / `reducer` / `identity`）。"""

    def __init__(
        self,
        *,
        result_occurrence_id: str = "result-issue125",
        source_snapshot_fingerprint: str = "snapshot-issue125",
        reason_registry=None,
        recovery_registry=None,
    ) -> None:
        self.identity = SimpleNamespace(
            result_occurrence_id=result_occurrence_id,
            source_snapshot_fingerprint=source_snapshot_fingerprint,
            execution_identity_digest="execution-issue125",
        )
        self.recorder = EventRecorder(
            stream_id=f"stream-{result_occurrence_id}",
            result_occurrence_id=result_occurrence_id,
            source_snapshot_fingerprint=source_snapshot_fingerprint,
        )
        self.reducer = ShadowLifecycleReducer(
            reason_registry=reason_registry or PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=recovery_registry or PROCESS_DURABLE_RECOVERY_REGISTRY,
        )
        self._reason_registry = reason_registry or PROCESS_DURABLE_REASON_REGISTRY
        self._recovery_registry = (
            recovery_registry or PROCESS_DURABLE_RECOVERY_REGISTRY
        )

    # -- occurrence 組み立て ------------------------------------------------

    def build_occurrence(
        self,
        cause_inputs,
        *,
        contract,
        proof_kind,
        occurrence_target_kind=None,
        suffix="a",
    ):
        """1 件の `CauseOccurrenceAuthority` と、その唯一の requirement を返す。

        `occurrence_target_kind` を渡すと、cause identity の target_kind とは
        別の target_kind で occurrence を作る（digest に含まれない要素を
        独立に照合できているかの検証用）。
        """
        contract_id, contract_version, slot = contract
        cause = SemanticCauseIdentityFactory(self._reason_registry).create(
            **cause_inputs
        )
        requirement = ProofRequirement(
            "issue125-q-" + authority_digest(
                {"cause": cause.value, "suffix": suffix}
            )[:32],
            proof_kind,
            ("cause", cause.value, suffix),
        )
        bound = SatisfactionBindingFactory(self._recovery_registry).bind(
            contract_definition_id=contract_id,
            contract_version=contract_version,
            bindings={slot: requirement},
        )
        occurrence = CauseOccurrence(
            "issue125-occ-" + authority_digest(
                {"cause": cause.value, "suffix": suffix}
            )[:32],
            cause,
            cause_inputs["reason_id"],
            authority_digest(cause_inputs["canonical_target_key"]),
            occurrence_target_kind or cause_inputs["target_kind"],
            cause_inputs["identity_scope"],
            bound.contract_definition_id,
            bound.contract_version,
            bound.normalized_expression_digest,
            bound.bound_expression_digest,
            (requirement.requirement_id,),
            (f"issue125-evidence-{suffix}",),
            "issue125_test_producer_signal",
            self.identity.source_snapshot_fingerprint,
            "issue125-test-producer-v1",
            self.identity.execution_identity_digest,
        )
        return CauseOccurrenceAuthority(occurrence, bound), requirement

    # -- event の記録 -------------------------------------------------------

    def observe(self, authority) -> None:
        self.recorder.append(EventIntent(
            EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority),
        ))

    def complete(self, authority, requirement) -> None:
        occurrence = authority.occurrence
        bound = authority.bound_contract
        receipt = RequirementCompletionReceipt(
            occurrence.cause_id.value,
            occurrence.occurrence_id,
            requirement.requirement_id,
            bound.contract_definition_id,
            bound.contract_version,
            bound.bound_expression_digest,
            "issue125-proof-artifact-" + requirement.requirement_id[-8:],
            "issue125-applicability-" + requirement.requirement_id[-8:],
        )
        self.recorder.append(EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(receipt),
        ))

    # -- 読み出し -----------------------------------------------------------

    def active_reason_ids(self):
        projection = self.reducer.replay_prefix(self.recorder.prefix_view())
        return sorted(row.reason_id for row in projection.c_active_base)

    def final_projection(self):
        """FINAL な lifecycle projection（`finalize_decision` の入力）。"""
        return self.reducer.replay(self.recorder.seal()).projection


def sat_safety_cause_inputs(**overrides):
    """`blocks_disequivalence` の cause identity 入力（NOT_EQ を塞ぐ側）。"""
    base = dict(
        reason_id=SAT_SAFETY_REASON_ID,
        identity_scope=IdentityScope.RELATIONAL,
        target_kind=SAT_SAFETY_TARGET_KIND,
        canonical_target_key=("pair", "left", "right"),
        missing_semantic_fact=("counterexample_safety_gate_unproven", "model"),
        semantic_proposition=("counterexample_is_safe_and_decisive", "gate"),
        observation_surface=("analysis_safety",),
        active_semantic_precondition=("sat_candidate_observed", True),
        correspondence_contract=("ordered_function_pair",),
    )
    base.update(overrides)
    return base


def outcome_cause_inputs(**overrides):
    """`blocks_equivalence` の cause identity 入力（EQ を塞ぐ側）。"""
    base = dict(
        reason_id=OUTCOME_REASON_ID,
        identity_scope=IdentityScope.UNARY,
        target_kind=OUTCOME_TARGET_KIND,
        canonical_target_key=("function", "left", "stage"),
        missing_semantic_fact=("outcome_partition_incomplete", "left"),
        semantic_proposition=("outcome_partition_is_complete", "left"),
        observation_surface=("outcome_stage",),
        active_semantic_precondition=("stage_observed", True),
        correspondence_contract=None,
    )
    base.update(overrides)
    return base


def attribution_key(cause_inputs, requirement_ids, **overrides):
    """cause identity 入力と同じ値から帰属キーを作る。"""
    fields = dict(
        reason_id=cause_inputs["reason_id"],
        identity_scope=IdentityScope(cause_inputs["identity_scope"]).value,
        target_kind=cause_inputs["target_kind"],
        canonical_target_key=cause_inputs["canonical_target_key"],
        missing_semantic_fact=cause_inputs["missing_semantic_fact"],
        semantic_proposition=cause_inputs["semantic_proposition"],
        proof_requirement_ids=tuple(requirement_ids),
        observation_surface=cause_inputs["observation_surface"],
        active_semantic_precondition=cause_inputs["active_semantic_precondition"],
        correspondence_contract=cause_inputs["correspondence_contract"],
    )
    fields.update(overrides)
    return CauseAttributionKey(**fields)
