# -*- coding: utf-8 -*-
"""等価性判定のデバッグトレース（機械可読）"""

from typing import List, Dict, Any, Mapping, Optional, Tuple
from dataclasses import dataclass, field, asdict
from enum import Enum

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.json_encoding import (
    JsonBudget,
    Reducer,
    as_dict,
    as_list,
    each,
    flatten,
    hashable_key,
    inline,
    materialize,
    raw,
    scan,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownReasonRecord,
    coerce_unknown_reason_records,
    recovery_actions_reducer,
    recovery_actions_source,
    recovery_backlog_reducer,
    recovery_backlog_source,
    unknown_reason_counts_reducer,
    unknown_reason_counts_source,
)


class TransitionReason(Enum):
    """Phase/Stage遷移理由"""
    UNSAT = "UNSAT"  # 等価確定 → 終了
    SAT = "SAT"  # 非等価確定 → 終了
    SAT_PHASE4B = "SAT->Phase4B"  # SAT だが Phase 4-B 試行
    UNKNOWN = "UNKNOWN"  # 不明 → 次Phase
    TIMEOUT = "TIMEOUT"  # タイムアウト → 次Phase
    NO_CHANGES = "no_changes"  # Phase適用されず → スキップ
    CRITICAL_ERROR = "critical_error"  # 致命的エラー → 終了
    STAGE_FALLBACK = "stage_fallback"  # Pairwise UNKNOWN → Monolithic


class CausalStatus(str, Enum):
    ACTIVE_FINAL_BLOCKER = "active_final_blocker"
    CONTRIBUTING_BLOCKER = "contributing_blocker"
    DIAGNOSTIC_ONLY = "diagnostic_only"
    UNCLASSIFIED = "unclassified"


class CompletionApplicabilityStatus(str, Enum):
    APPLICABLE = "APPLICABLE"
    STALE_SNAPSHOT = "STALE_SNAPSHOT"
    PREMISE_MISMATCH = "PREMISE_MISMATCH"
    TARGET_OR_SLOT_MISMATCH = "TARGET_OR_SLOT_MISMATCH"
    ARTIFACT_INVALID = "ARTIFACT_INVALID"
    OCCURRENCE_ALREADY_COMPLETED = "OCCURRENCE_ALREADY_COMPLETED"


@dataclass(frozen=True)
class AttemptIdentity:
    strategy_identity: str
    attempt_ordinal: int
    trace_schema_version: int = 1

    def json_items(self):
        yield "strategy_identity", self.strategy_identity
        yield "attempt_ordinal", self.attempt_ordinal
        yield "trace_schema_version", self.trace_schema_version

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class ReasonOccurrenceId:
    attempt_identity: AttemptIdentity
    reason_ordinal: int
    occurrence_schema_version: int = 1

    def json_items(self):
        yield "occurrence_schema_version", self.occurrence_schema_version
        yield "attempt_identity", self.attempt_identity
        yield "reason_ordinal", self.reason_ordinal

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class ReasonOccurrence:
    occurrence_id: ReasonOccurrenceId
    reason_record: UnknownReasonRecord
    initial_causal_status: str = CausalStatus.UNCLASSIFIED.value

    def json_items(self):
        yield "occurrence_id", self.occurrence_id
        yield "reason_record", self.reason_record
        yield "attempt_identity", live_values.attribute(self.occurrence_id, "attempt_identity")
        yield "initial_causal_status", self.initial_causal_status

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class ProofCompletionEvent:
    completion_id: Tuple[Any, ...]
    proof_requirement_id: Mapping[str, Any]
    proof_artifact_ref: Tuple[Any, ...]
    proof_status: str
    completed_at_attempt: AttemptIdentity

    def json_items(self):
        yield "completion_id", self.completion_id
        yield "proof_requirement_id", as_dict(self.proof_requirement_id)
        yield "proof_artifact_ref", self.proof_artifact_ref
        yield "proof_status", self.proof_status
        yield "completed_at_attempt", self.completed_at_attempt

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class ReasonCompletionEvent:
    completion_event_id: Tuple[Any, ...]
    completed_occurrence_id: ReasonOccurrenceId
    exact_target_id: Tuple[Any, ...]
    exact_missing_fact_or_proof_slot: str
    source_snapshot_fingerprint: str
    semantic_seed_or_premise_digest: str
    evidence_or_artifact_digest: str
    recognizing_stage: str
    completed_at_attempt: AttemptIdentity
    applicability_status: str

    def json_items(self):
        yield "completion_event_id", self.completion_event_id
        yield "completed_occurrence_id", self.completed_occurrence_id
        yield "exact_target_id", self.exact_target_id
        yield "exact_missing_fact_or_proof_slot", self.exact_missing_fact_or_proof_slot
        yield "source_snapshot_fingerprint", self.source_snapshot_fingerprint
        yield "semantic_seed_or_premise_digest", self.semantic_seed_or_premise_digest
        yield "evidence_or_artifact_digest", self.evidence_or_artifact_digest
        yield "recognizing_stage", self.recognizing_stage
        yield "completed_at_attempt", self.completed_at_attempt
        yield "applicability_status", self.applicability_status

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class ReasonCausalTransition:
    transition_id: Tuple[Any, ...]
    target_occurrence_id: ReasonOccurrenceId
    transition_kind: str
    cause_kind: str
    cause_ref: Any
    emitted_at_attempt: AttemptIdentity
    transition_ordinal: int

    def json_items(self):
        cause_ref = self.cause_ref
        yield "transition_id", self.transition_id
        yield "target_occurrence_id", self.target_occurrence_id
        yield "transition_kind", self.transition_kind
        yield "cause_kind", self.cause_kind
        # 旧 `to_dict`: 表現を持つ参照は表現に、それ以外はそのまま置く
        yield "cause_ref", cause_ref if live_values.type_attribute(type(cause_ref), "to_dict") is not None else raw(cause_ref)
        yield "emitted_at_attempt", self.emitted_at_attempt
        yield "transition_ordinal", self.transition_ordinal

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass
class NormalizationRuleApplication:
    """正規化ルール適用記録"""
    rule_name: str
    reason: str
    applied_to: str  # "value1" or "value2" or "both" or "case_i_j"
    before: Optional[str] = None
    after: Optional[str] = None
    
    def json_items(self):
        yield "rule_name", self.rule_name
        yield "reason", self.reason
        yield "applied_to", self.applied_to
        yield "before", self.before
        yield "after", self.after

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


#: 列の要素が尽きたことを知る印（`PairwiseDecisiveInfo.json_items`）
_NO_ELEMENT = object()


@dataclass
class PairwiseDecisiveInfo:
    """Pairwise戦略の決定的情報（どのペアが結果を決定したか）"""
    decisive_result: str  # "SAT" or "UNSAT" or "UNKNOWN"
    total_pairs: int
    unsat_pairs: int
    sat_pairs: int
    unknown_pairs: int
    
    # SAT時の decisive ペア情報
    decisive_pair: Optional[Tuple[int, int]] = None  # (i, j)
    pair_stage: Optional[str] = None  # "conds-only", "with-ineq", "norm-ineq"
    case1_summary: Optional[str] = None
    case2_summary: Optional[str] = None
    value1_expr: Optional[str] = None
    value2_expr: Optional[str] = None
    final_query_excerpt: Optional[str] = None  # ★ 互換性のため残す（先頭200文字）
    final_query: Optional[str] = None  # ★ 新規追加: 完全なクエリ
    
    def json_items(self):
        yield "decisive_result", self.decisive_result
        yield "total_pairs", self.total_pairs
        yield "unsat_pairs", self.unsat_pairs
        yield "sat_pairs", self.sat_pairs
        yield "unknown_pairs", self.unknown_pairs
        pair = self.decisive_pair
        if pair is not None:
            # 組み込みの列は添字で、それ以外は組み込みの振る舞いの列だけを先頭から読む
            if type(pair) in (tuple, list):
                first = pair[0]
                second = pair[1]
            else:
                elements = live_values.elements_of(pair)
                first = next(elements, _NO_ELEMENT)
                second = next(elements, _NO_ELEMENT)
                if second is _NO_ELEMENT:
                    raise IndexError("a decisive pair needs two elements")
            yield "decisive_pair", inline(("i", first), ("j", second))
            yield "pair_stage", self.pair_stage
            yield "case1_summary", self.case1_summary
            yield "case2_summary", self.case2_summary
            yield "value1_expr", self.value1_expr
            yield "value2_expr", self.value2_expr
            yield "final_query_excerpt", self.final_query_excerpt
            yield "final_query", self.final_query  # ★ 追加

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass
class Attempt:
    """1回の等価性判定試行（1つのPhase/Stageセット）"""
    attempt_id: int
    retry_count: int
    phase: str
    stage_path: List[str]
    strategy: str
    result: Optional[bool]
    transition_reason: str
    
    # 詳細情報
    type_fix_result: Optional[Dict[str, Any]] = None
    original_function1_signature: Optional[Dict[str, Any]] = None
    original_function2_signature: Optional[Dict[str, Any]] = None
    effective_function1_signature: Optional[Dict[str, Any]] = None
    effective_function2_signature: Optional[Dict[str, Any]] = None
    function1_signature_hypotheses: List[Dict[str, Any]] = field(default_factory=list)
    function2_signature_hypotheses: List[Dict[str, Any]] = field(default_factory=list)
    solver_results: Optional[Dict[str, Any]] = None
    final_smt_excerpt: Optional[str] = None  # SMT式の先頭500文字（互換性のため残す）
    final_smt: Optional[str] = None  # ★ 新規: 完全なSMT式
    counterexample: Optional[Dict[str, Any]] = None
    pairwise_decisive: Optional[PairwiseDecisiveInfo] = None
    pairwise_debug_stats: Dict[str, int] = field(default_factory=dict)
    normalization_rules: List[NormalizationRuleApplication] = field(default_factory=list)
    unknown_reasons: List[UnknownReasonRecord] = field(default_factory=list)
    reason_occurrences: List[ReasonOccurrence] = field(default_factory=list)
    mips64_abi_constraints: Optional[Dict[str, Any]] = None
    elapsed_time: float = 0.0
    # Issue #107: phase 観測（診断のみ）。既存の payload に無ければ既定値のままで、
    # 判定にも reason にも関与しない。`applied` は三値: True/False は型修正 phase の
    # 適用有無、None は「その概念が無い attempt」（P0 や ABI 制約リトライ）。
    applied: Optional[bool] = None
    reanalyzed_sides: List[str] = field(default_factory=list)
    skipped_reason: Optional[str] = None
    reason_before: List[str] = field(default_factory=list)
    reason_after: List[str] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.unknown_reasons = list(coerce_unknown_reason_records(self.unknown_reasons))
        if not self.reason_occurrences:
            identity = AttemptIdentity(self.strategy, self.attempt_id)
            self.reason_occurrences = [
                ReasonOccurrence(
                    occurrence_id=ReasonOccurrenceId(identity, ordinal),
                    reason_record=reason,
                )
                for ordinal, reason in enumerate(self.unknown_reasons)
            ]
    
    def json_items(self):
        """結果 JSON での表現（**唯一の schema**）。値は source で渡し、walker が写す。"""

        yield "attempt_id", self.attempt_id
        yield "retry_count", self.retry_count
        yield "phase", self.phase
        yield "stage_path", self.stage_path
        yield "strategy", self.strategy
        yield "result", self.result
        yield "transition_reason", self.transition_reason
        yield "type_fix_result", self.type_fix_result
        yield "original_function1_signature", self.original_function1_signature
        yield "original_function2_signature", self.original_function2_signature
        yield "effective_function1_signature", self.effective_function1_signature
        yield "effective_function2_signature", self.effective_function2_signature
        yield "function1_signature_hypotheses", as_list(self.function1_signature_hypotheses)
        yield "function2_signature_hypotheses", as_list(self.function2_signature_hypotheses)
        yield "solver_results", self.solver_results
        yield "final_smt_excerpt", self.final_smt_excerpt
        yield "final_smt", self.final_smt  # ★ 追加
        yield "counterexample", self.counterexample
        pairwise_decisive = self.pairwise_decisive
        yield "pairwise_decisive", pairwise_decisive if live_values.as_bool(pairwise_decisive) else None
        yield "pairwise_debug_stats", as_dict(self.pairwise_debug_stats)
        yield "normalization_rules", each(self.normalization_rules)
        yield "unknown_reasons", each(self.unknown_reasons)
        yield "reason_occurrences", each(self.reason_occurrences)
        yield "mips64_abi_constraints", self.mips64_abi_constraints
        yield "elapsed_time", self.elapsed_time
        yield "applied", self.applied
        yield "reanalyzed_sides", as_list(self.reanalyzed_sides)
        yield "skipped_reason", self.skipped_reason
        yield "reason_before", as_list(self.reason_before)
        yield "reason_after", as_list(self.reason_after)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)



@dataclass
class DebugTrace:
    """デバッグトレース（機械可読）"""
    attempts: List[Attempt] = field(default_factory=list)
    planned_phases: List[str] = field(default_factory=list)
    known_phases: List[str] = field(default_factory=list)
    final_result: Optional[bool] = None
    total_time: float = 0.0
    error_message: Optional[str] = None
    causal_transitions: List[ReasonCausalTransition] = field(default_factory=list)
    proof_completion_events: List[ProofCompletionEvent] = field(default_factory=list)
    reason_completion_events: List[ReasonCompletionEvent] = field(default_factory=list)
    
    def add_attempt(self, attempt: Attempt):
        """試行を追加"""
        self.attempts.append(attempt)

    def add_proof_completion(self, completion: ProofCompletionEvent) -> None:
        self.proof_completion_events.append(completion)

    def add_reason_completion(
        self,
        completion: ReasonCompletionEvent,
        *,
        current_snapshot_fingerprint: str,
        current_semantic_seed_or_premise_digest: str,
        artifact_is_valid: bool,
    ) -> ReasonCompletionEvent:
        """Validate exact occurrence applicability before closing a reason."""

        occurrence = next(
            (
                item
                for attempt in self.attempts
                for item in attempt.reason_occurrences
                if item.occurrence_id == completion.completed_occurrence_id
            ),
            None,
        )
        already_completed = any(
            item.completed_occurrence_id == completion.completed_occurrence_id
            and item.applicability_status == CompletionApplicabilityStatus.APPLICABLE.value
            for item in self.reason_completion_events
        )
        status = CompletionApplicabilityStatus.APPLICABLE
        if already_completed:
            status = CompletionApplicabilityStatus.OCCURRENCE_ALREADY_COMPLETED
        elif occurrence is None:
            status = CompletionApplicabilityStatus.TARGET_OR_SLOT_MISMATCH
        elif (
            completion.completed_at_attempt.attempt_ordinal
            <= completion.completed_occurrence_id.attempt_identity.attempt_ordinal
        ):
            status = CompletionApplicabilityStatus.TARGET_OR_SLOT_MISMATCH
        elif completion.source_snapshot_fingerprint != str(current_snapshot_fingerprint):
            status = CompletionApplicabilityStatus.STALE_SNAPSHOT
        elif (
            completion.semantic_seed_or_premise_digest
            != str(current_semantic_seed_or_premise_digest)
        ):
            status = CompletionApplicabilityStatus.PREMISE_MISMATCH
        elif not artifact_is_valid or not completion.evidence_or_artifact_digest:
            status = CompletionApplicabilityStatus.ARTIFACT_INVALID
        else:
            reason = occurrence.reason_record
            expected_target = tuple(getattr(reason, "object_target_key", ()) or ())
            requirements = tuple(getattr(reason, "proof_requirement_ids", ()) or ())
            expected_slots = {
                str(item.get("proof_kind") or "")
                for item in requirements
                if isinstance(item, Mapping)
            }
            if expected_target and expected_target != tuple(completion.exact_target_id):
                status = CompletionApplicabilityStatus.TARGET_OR_SLOT_MISMATCH
            elif expected_slots and completion.exact_missing_fact_or_proof_slot not in expected_slots:
                status = CompletionApplicabilityStatus.TARGET_OR_SLOT_MISMATCH

        validated = ReasonCompletionEvent(
            completion_event_id=completion.completion_event_id,
            completed_occurrence_id=completion.completed_occurrence_id,
            exact_target_id=completion.exact_target_id,
            exact_missing_fact_or_proof_slot=completion.exact_missing_fact_or_proof_slot,
            source_snapshot_fingerprint=completion.source_snapshot_fingerprint,
            semantic_seed_or_premise_digest=completion.semantic_seed_or_premise_digest,
            evidence_or_artifact_digest=completion.evidence_or_artifact_digest,
            recognizing_stage=completion.recognizing_stage,
            completed_at_attempt=completion.completed_at_attempt,
            applicability_status=status.value,
        )
        self.reason_completion_events.append(validated)
        return validated

    def get_phase_usage(self) -> List[Dict[str, Any]]:
        """Phase 利用状況を集約して返す。"""
        return list(self._iter_phase_usage())

    def get_used_phases(self) -> List[str]:
        """実際に再解析・再判定まで進んだ Phase の一覧を返す。"""
        return list(self._iter_used_phases())

    def _iter_phase_usage(self):
        """phase ごとの利用状況の行（`known_phases` → attempt の初出の順）。attempt を 1 回だけ辿る。"""

        fold = _PhaseUsageFold(self.known_phases, self.planned_phases)
        # 人向けの一覧（出力の準備の外。出力は `phase_usage_source` が walk の作業量で畳む）
        work = JsonBudget(None)
        fold._seed(work)
        for attempt in self.attempts:
            fold.add(attempt, work=work)
        return fold.rows()

    def _iter_used_phases(self):
        for row in self._iter_phase_usage():
            if row["used"]:
                yield row["phase"]

    def phase_usage_source(self, *, used_only: bool = False):
        """出力の準備用: walker が attempt を 1 つずつ数えながら phase の行へ畳み込む（`scan`）。"""

        from scripts.function_tracer_pcode.core.json_encoding import scan

        return scan(self.attempts, _PhaseUsageFold(self.known_phases, self.planned_phases, used_only=used_only))

    def format_phase_usage_summary(self) -> str:
        """人間向けの Phase 利用状況サマリを返す。"""
        return format_phase_usage_rows(self.get_phase_usage())

    def json_items(self):
        """結果 JSON での表現（**唯一の schema**）。

        attempt / event は 1 件ずつ辿る。集計は key / 行を 1 つずつ作る source（`unknown_reason`
        の `*_source`・phase ごとの行の generator）で渡し、全体の表を先に作らない。
        """

        yield "attempts", each(self.attempts)
        yield "causal_transitions", each(self.causal_transitions)
        yield "proof_completion_events", each(self.proof_completion_events)
        yield "reason_completion_events", each(self.reason_completion_events)
        yield "planned_phases", self.planned_phases
        yield "known_phases", self.known_phases
        yield "used_phases", self.phase_usage_source(used_only=True)
        yield "phase_usage", self.phase_usage_source()
        # 最後の UNKNOWN / TIMEOUT の attempt を探す仕事・attempt ごとの reason を辿る仕事は、
        # walker が attempt / reason を 1 つずつ引き出して数える（`scan` の reducer / `flatten`）
        skip_final = self.final_result is not None
        observed = flatten(self.attempts, "unknown_reasons")
        yield "unknown_reason_counts", scan(
            self.attempts, _FinalAttemptReasons(unknown_reason_counts_reducer(True), skip=skip_final),
        )
        yield "observed_unknown_reason_counts", unknown_reason_counts_source(observed)
        yield "unknown_recovery_backlog", scan(
            self.attempts, _FinalAttemptReasons(recovery_backlog_reducer(True), skip=skip_final),
        )
        yield "unknown_recovery_actions", scan(
            self.attempts, _FinalAttemptReasons(recovery_actions_reducer(True), skip=skip_final),
        )
        yield "observed_unknown_recovery_backlog", recovery_backlog_source(flatten(self.attempts, "unknown_reasons"))
        yield "observed_unknown_recovery_actions", recovery_actions_source(flatten(self.attempts, "unknown_reasons"))
        yield "final_result", self.final_result
        yield "total_time", self.total_time
        yield "error_message", self.error_message
        yield "attempt_count", live_values.size(self.attempts)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)

    



#: 最後の attempt として reason を読む遷移（`_extract_final_unknown_reasons` と同じ）
_FINAL_TRANSITION_REASONS = frozenset({TransitionReason.UNKNOWN.value, TransitionReason.TIMEOUT.value})


class _FinalAttemptReasons(Reducer):
    """`scan` の reducer: 最後の UNKNOWN / TIMEOUT の attempt の reason を、`inner`（Reducer）で畳む。

    walker が attempt を 1 つずつ引き出して数える（探す仕事は walker の勘定）。`add` は attempt の
    field を読んで最後に当たる attempt を覚えるだけ（O(1)）。`result` は、その attempt の reason を
    `inner` で畳む `scan`（reason も walker が 1 つずつ数える）。
    """

    __slots__ = ("inner", "skip", "last")

    def __init__(self, inner: Reducer, *, skip: bool) -> None:
        self.inner = inner
        self.skip = skip
        self.last: Any = None

    def add(self, attempt: Any, *, work: Any) -> None:
        if self.skip:
            return
        if (
            live_values.attribute(attempt, "result") is None
            and hashable_key(live_values.attribute(attempt, "transition_reason"), work) in _FINAL_TRANSITION_REASONS
        ):
            self.last = attempt

    def result(self, *, work: Any) -> Any:
        reasons = None if self.last is None else live_values.attribute(self.last, "unknown_reasons")
        return scan(() if reasons is None else reasons, self.inner)


class _PhaseUsageFold(Reducer):
    """phase ごとの利用状況の行へ attempt を 1 つずつ畳み込む（`scan` の reducer を兼ねる）。

    行は `known_phases` → attempt の初出の順（行の数は phase の数）。`used_only` は実際に
    再解析・再判定まで進んだ phase の名前だけを返す。
    """

    __slots__ = ("counts", "phases", "last_reasons", "last_results", "known", "planned", "planned_keys", "used_only")

    def __init__(self, known_phases: Any, planned_phases: Any, *, used_only: bool = False) -> None:
        # 行の種は最初の `add` / `result` で作業量の中で作る（構築では辿らない）
        self.known = known_phases
        self.planned = planned_phases
        self.planned_keys: Optional[set] = None
        self.used_only = used_only
        #: phase の key → 数え上げ（package が作る plain な値だけ）。live な値（phase の名前・最後の
        #: 遷移理由 / 結果）は key ごとの別の表に置き、行は `rows` が組み立てる
        self.counts: Dict[Any, Dict[str, Any]] = {}
        self.phases: Dict[Any, Any] = {}
        self.last_reasons: Dict[Any, Any] = {}
        self.last_results: Dict[Any, Any] = {}

    #: phase の行 1 つの手間（固定の形: 11 の field と 7 の遷移の件数）
    ROW_COST = 32

    def _seed(self, work: Any) -> None:
        if self.planned_keys is not None:
            return
        self.planned_keys = {hashable_key(phase, work) for phase in _phase_names(self.planned)}
        for phase in _phase_names(self.known):
            self._counts(hashable_key(phase, work), phase, work)

    def _counts(self, key: Any, phase: Any, work: Any) -> Dict[str, Any]:
        counts = self.counts.get(key)
        if counts is None:
            # 新しい phase は行を 1 つ作る（行の数は phase の数で、attempt の数ではない）
            work.charge(self.ROW_COST)
            counts = self.counts[key] = {
                "planned": key in self.planned_keys,
                "reached": False,
                "used": False,
                "attempt_count": 0,
                "result_attempt_count": 0,
                "no_change_skip_count": 0,
                "transition_counts": {
                    TransitionReason.UNSAT.value: 0,
                    TransitionReason.SAT.value: 0,
                    TransitionReason.SAT_PHASE4B.value: 0,
                    TransitionReason.UNKNOWN.value: 0,
                    TransitionReason.TIMEOUT.value: 0,
                    TransitionReason.CRITICAL_ERROR.value: 0,
                    TransitionReason.NO_CHANGES.value: 0,
                },
            }
            self.phases[key] = phase
            self.last_reasons[key] = None
            self.last_results[key] = None
        return counts

    def add(self, attempt: Any, *, work: Any) -> None:
        self._seed(work)
        # key として hash する値は hash する前に数える（上書きした `__hash__` / `__eq__` を呼ばない）
        phase = live_values.attribute(attempt, "phase")
        reason = live_values.attribute(attempt, "transition_reason")
        reason_key = hashable_key(reason, work)
        key = hashable_key(phase, work)
        counts = self._counts(key, phase, work)
        counts["reached"] = True
        counts["attempt_count"] += 1
        transition_counts = counts["transition_counts"]
        transition_counts[reason_key] = transition_counts.get(reason_key, 0) + 1
        if reason_key == TransitionReason.NO_CHANGES.value:
            counts["no_change_skip_count"] += 1
        else:
            counts["result_attempt_count"] += 1
            counts["used"] = True
        self.last_reasons[key] = reason
        self.last_results[key] = live_values.attribute(attempt, "result")

    def rows(self):
        """phase ごとの行（`known_phases` → attempt の初出の順）。"""

        for key, counts in self.counts.items():
            yield {
                "phase": self.phases[key],
                "planned": counts["planned"],
                "reached": counts["reached"],
                "used": counts["used"],
                "attempt_count": counts["attempt_count"],
                "result_attempt_count": counts["result_attempt_count"],
                "no_change_skip_count": counts["no_change_skip_count"],
                "transition_counts": counts["transition_counts"],
                "last_transition_reason": self.last_reasons[key],
                "last_result": self.last_results[key],
            }

    def _used_phases(self):
        for key, counts in self.counts.items():
            if counts["used"]:
                yield self.phases[key]

    def result(self, *, work: Any) -> Any:
        self._seed(work)
        if self.used_only:
            return each(self._used_phases())
        return each(self.rows())


def _phase_names(phases: Any) -> Any:
    """phase の名前の列（`None` は空。組み込みの振る舞いの列だけを辿る）。"""

    return () if phases is None else live_values.elements_of(phases)


def format_phase_usage_rows(usage: Any) -> str:
    """phase 利用状況の行（`get_phase_usage()` / 出力の `phase_usage`）を人間向けに整形する。"""
    usage = list(usage or ())
    if not usage:
        return "Phase Usage Summary:\n  (none)"

    lines = ["Phase Usage Summary:"]
    for entry in usage:
        if not entry["reached"]:
            status = "NOT_REACHED"
        elif entry["used"]:
            status = "USED"
        else:
            status = "NO_CHANGES"

        scope = "planned" if entry["planned"] else "aux"
        details = [f"scope={scope}"]
        if entry["attempt_count"] > 0:
            details.append(f"attempts={entry['attempt_count']}")
        if entry["result_attempt_count"] > 0:
            details.append(f"rechecks={entry['result_attempt_count']}")
        if entry["no_change_skip_count"] > 0:
            details.append(f"no_changes={entry['no_change_skip_count']}")
        transition_counts = entry["transition_counts"]
        details.append(f"unsat={transition_counts.get(TransitionReason.UNSAT.value, 0)}")
        details.append(f"sat={transition_counts.get(TransitionReason.SAT.value, 0)}")
        details.append(
            f"sat_phase4b={transition_counts.get(TransitionReason.SAT_PHASE4B.value, 0)}"
        )
        details.append(f"unknown={transition_counts.get(TransitionReason.UNKNOWN.value, 0)}")
        details.append(f"timeout={transition_counts.get(TransitionReason.TIMEOUT.value, 0)}")
        details.append(
            f"critical={transition_counts.get(TransitionReason.CRITICAL_ERROR.value, 0)}"
        )
        if entry["last_transition_reason"] is not None:
            details.append(f"last={entry['last_transition_reason']}")

        lines.append(f"  {entry['phase']}: {status} ({', '.join(details)})")
    return "\n".join(lines)
