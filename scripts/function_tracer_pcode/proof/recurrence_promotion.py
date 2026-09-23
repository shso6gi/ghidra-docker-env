"""Pair-barrier promotion for proof-free recurrence proposals."""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Any, Iterable, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.core.evidence_authority import (
    AUTHORITY_SCOPE_KEY,
    FUNCTION_UNARY,
    record_function_unary_evidence,
)
from scripts.function_tracer_pcode.analysis.returns.summary_returns import (
    accept_summary_return_candidates,
)
from scripts.function_tracer_pcode.core.analysis import (
    FunctionReturnAnalysis,
    SummaryReturnCandidate,
)
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.runtime_refs import (
    CountedLoopSummaryRef,
    CountedStateTransitionLoopSummaryRef,
    StateTransitionLoopSummaryRef,
)
from scripts.function_tracer_pcode.core.recurrence_contracts import (
    ImmutableRecurrenceExpression,
    ImmutableRecurrenceCondition,
    QuarantinedRecurrenceProposal,
    RecurrenceSeedCore,
    RecurrenceSubproofEvidence,
    RecurrenceValidationEvidence,
    function_recurrence_binding_digest,
    semantic_recurrence_closure_digest,
    RecurrenceDigestCodec,
)
from scripts.function_tracer_pcode.proof.obligations.model import ProofArtifact, UnaryArtifactDomain
from scripts.function_tracer_pcode.proof.obligations.recurrence import recurrence_proof_requirement
from scripts.function_tracer_pcode.proof.obligations.runtime import ObligationRuntimeSession
from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot


RECURRENCE_DOMAIN_CONTRACT = (
    "recurrence_domain_contract_v1",
    "integer_bitvector",
    "pure_or_proved_effects",
)
RECURRENCE_NORMALIZATION_POLICY = "recurrence-summary-normalization-v1"


def _candidate_width_sort_key(candidate: SummaryReturnCandidate) -> Tuple[Any, ...]:
    expression = ImmutableRecurrenceExpression.from_expression(
        candidate.return_info.value
    )
    signedness = (
        "neutral" if expression.signedness == "signless" else expression.signedness
    )
    sort = "bitvec" if expression.sort == "bitvector" else expression.sort
    return ("width_sort_v1", int(expression.size), str(sort), str(signedness))


def _candidate_guard_identity(candidate: SummaryReturnCandidate) -> Tuple[Any, ...]:
    return (
        "guard_conditions_v1",
        tuple(
            ImmutableRecurrenceCondition.from_condition(condition).stable_key()
            for condition in tuple(candidate.return_info.conditions or ())
        ),
    )


def _candidate_transition_identity(candidate: SummaryReturnCandidate) -> Tuple[Any, ...]:
    evidence = tuple(candidate.transition_evidence_key or ())
    if not evidence or not isinstance(evidence[0], str):
        raise ValueError("recurrence transition evidence has no typed tag")
    return (
        "transition_evidence_digest_v1",
        evidence[0],
        RecurrenceDigestCodec.digest("recurrence_transition_evidence_v1", evidence),
    )


def _constant_integer(expression: Any) -> Optional[int]:
    if (
        isinstance(expression, Expression)
        and expression.expr_type == ExpressionType.CONSTANT
        and isinstance(expression.value, int)
    ):
        return int(expression.value)
    return None


def _same_expression(left: Any, right: Any) -> bool:
    if left is right:
        return True
    left_key = getattr(left, "structural_key", None)
    right_key = getattr(right, "structural_key", None)
    if not callable(left_key) or not callable(right_key):
        return False
    try:
        return left_key() == right_key()
    except (TypeError, ValueError):
        return False


def _runtime_refs(value: Any) -> Iterable[Any]:
    """Yield recurrence runtime refs from an expression without string parsing."""

    seen: set[int] = set()

    def visit(item: Any) -> Iterable[Any]:
        if item is None or id(item) in seen:
            return
        seen.add(id(item))
        runtime_ref = getattr(item, "runtime_ref", None)
        if isinstance(
            runtime_ref,
            (
                CountedLoopSummaryRef,
                StateTransitionLoopSummaryRef,
                CountedStateTransitionLoopSummaryRef,
            ),
        ):
            yield runtime_ref
        for operand in tuple(getattr(item, "operands", ()) or ()):
            yield from visit(operand)

    yield from visit(value)


def _effect_profile_is_scalar_pure(profile: Any) -> bool:
    return profile is not None and not any(
        bool(getattr(profile, name, False))
        for name in (
            "memory_reads", "memory_writes", "calls", "escapes",
            "context_memory_writes", "context_calls", "context_escapes",
        )
    ) and not tuple(getattr(profile, "effect_descriptors", ()) or ())


def _positive_guard_state(expression: Any) -> Optional[Expression]:
    if not isinstance(expression, Expression) or expression.expr_type != ExpressionType.BINARY_OP:
        return None
    operands = tuple(expression.operands or ())
    if len(operands) != 2 or expression.operator not in {"INT_SLESS", "INT_LESS"}:
        return None
    if _constant_integer(operands[0]) == 0 and isinstance(operands[1], Expression):
        return operands[1]
    return None


def _strict_affine_decrement(expression: Any, state: Expression) -> Optional[int]:
    if not isinstance(expression, Expression) or expression.expr_type != ExpressionType.BINARY_OP:
        return None
    operands = tuple(expression.operands or ())
    if len(operands) != 2:
        return None
    left, right = operands
    if expression.operator == "INT_SUB" and _same_expression(left, state):
        decrement = _constant_integer(right)
        return decrement if decrement is not None and decrement > 0 else None
    if expression.operator != "INT_ADD":
        return None
    constant_expr = right if _same_expression(left, state) else left if _same_expression(right, state) else None
    raw = _constant_integer(constant_expr)
    if raw is None:
        return None
    size = max(1, int(getattr(constant_expr, "size", 0) or getattr(state, "size", 0) or 1))
    modulus = 1 << (size * 8)
    signed = raw - modulus if raw >= modulus // 2 else raw
    return -signed if signed < 0 else None


def _region_proves_no_decrement_wrap(
    region: Tuple[Condition, ...], state: Expression, decrement: int
) -> bool:
    if int(decrement) == 1:
        return True
    if int(decrement) != 2:
        return False
    for condition in region:
        expression = condition.expression
        if (
            expression.expr_type != ExpressionType.BINARY_OP
            or expression.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}
            or len(expression.operands) != 2
        ):
            continue
        left, right = expression.operands
        masked = left if _constant_integer(right) == 0 else right if _constant_integer(left) == 0 else None
        if (
            not isinstance(masked, Expression)
            or masked.expr_type != ExpressionType.BINARY_OP
            or masked.operator != "INT_AND"
            or len(masked.operands) != 2
        ):
            continue
        mask_left, mask_right = masked.operands
        is_low_bit = (
            _same_expression(mask_left, state) and _constant_integer(mask_right) == 1
        ) or (
            _same_expression(mask_right, state) and _constant_integer(mask_left) == 1
        )
        proves_even = bool(expression.operator == "INT_EQUAL") != bool(condition.negated)
        if is_low_bit and proves_even:
            return True
    return False


def _validate_state_transition_termination(
    runtime_ref: StateTransitionLoopSummaryRef,
) -> Tuple[Any, ...]:
    if not _effect_profile_is_scalar_pure(runtime_ref.side_effect_profile):
        raise ValueError("state-transition recurrence has an unexplained effect")
    state = _positive_guard_state(runtime_ref.state_guard)
    if state is None:
        raise ValueError("state-transition recurrence lacks a positive-state guard")
    cases = tuple(runtime_ref.transition_cases or ())
    if not cases:
        cases = (((), runtime_ref.transition_expr),)
    decrements = []
    case_regions = []
    for case in cases:
        if not isinstance(case, (tuple, list)) or len(case) not in {2, 3}:
            raise ValueError("state-transition recurrence has malformed cases")
        if len(case) == 3:
            condition_expr, negated, transition = case
            region = (
                () if condition_expr is None
                else (Condition(condition_expr, bool(negated)),)
            )
        else:
            raw_conditions, transition = case
            if not isinstance(raw_conditions, (tuple, list)) or any(
                not isinstance(condition, Condition) for condition in raw_conditions
            ):
                raise ValueError("state-transition recurrence has malformed case guards")
            region = tuple(raw_conditions)
        decrement = _strict_affine_decrement(transition, state)
        if decrement is None:
            raise ValueError("state-transition recurrence is not a strict affine decrement")
        if not _region_proves_no_decrement_wrap(region, state, int(decrement)):
            raise ValueError("state-transition recurrence can wrap before decreasing")
        decrements.append(int(decrement))
        case_regions.append(region)
    unconditional = tuple(region for region in case_regions if not region)
    if unconditional:
        if len(case_regions) != 1:
            raise ValueError("state-transition unconditional branch overlaps another branch")
    else:
        if len(case_regions) != 2 or any(len(region) != 1 for region in case_regions):
            raise ValueError("state-transition branch coverage is not canonical")
        left_condition = case_regions[0][0]
        right_condition = case_regions[1][0]
        if (
            left_condition.expression.structural_key()
            != right_condition.expression.structural_key()
            or bool(left_condition.negated) == bool(right_condition.negated)
        ):
            raise ValueError("state-transition branch guards are not complementary")
    # The extractor owns branch partition totality.  This validator binds the
    # independent well-founded measure: unsigned/signed mathematical state > 0,
    # decreased by a positive constant in every extracted transition case.
    return (
        "guarded_affine_decreasing_state_v1",
        bool(runtime_ref.state_guard.operator == "INT_SLESS"),
        tuple(decrements),
        int(runtime_ref.state_size),
    )


def _validate_counted_summary(runtime_ref: CountedLoopSummaryRef) -> Tuple[Any, ...]:
    step = int(runtime_ref.induction_step)
    if step == 0:
        raise ValueError("counted recurrence has zero induction step")
    cases = tuple(runtime_ref.residue_cases or ())
    moduli = {int(case[0]) for case in cases}
    if not moduli or any(modulus not in {1, 2, 4} for modulus in moduli):
        raise ValueError("counted recurrence uses an unsupported residue modulus")
    for modulus in moduli:
        residues = {int(case[1]) % modulus for case in cases if int(case[0]) == modulus}
        if residues != set(range(modulus)):
            raise ValueError("counted recurrence residue partition is incomplete")
    return (
        "affine_counted_loop_v1",
        step,
        bool(runtime_ref.signed_loop),
        tuple(sorted(moduli)),
        tuple(sorted((int(a), int(b), int(c), int(d)) for a, b, c, d in cases)),
    )


def _validate_counted_state_transition(
    runtime_ref: CountedStateTransitionLoopSummaryRef,
) -> Tuple[Any, ...]:
    if not _effect_profile_is_scalar_pure(runtime_ref.side_effect_profile):
        raise ValueError("counted state transition has an unexplained effect")
    step = _constant_integer(runtime_ref.step_expr)
    if step is None or step == 0:
        raise ValueError("counted state transition has no constant progress step")
    if runtime_ref.transition_cases:
        raise ValueError("branched counted state transition lacks typed affine evidence")
    if _strict_affine_decrement(runtime_ref.transition_expr, runtime_ref.state_placeholder) is None:
        raise ValueError("counted state transition is not affine")
    return ("affine_counted_state_transition_v1", int(step), bool(runtime_ref.signed_loop))


def _validated_transition_termination(
    candidates: Tuple[SummaryReturnCandidate, ...],
    proposal: QuarantinedRecurrenceProposal,
) -> Tuple[Any, ...]:
    """Return normalized proof propositions or fail closed.

    Extraction evidence is necessary but not authority.  Only the four roadmap
    patterns below can produce the transition/termination sub-proof.
    """

    proposal_ids = {item.candidate_id for item in proposal.new_returns}
    proposal_candidates = tuple(
        candidate for candidate in candidates if candidate.candidate_id in proposal_ids
    )
    propositions = []
    validated_evidence_keys = set()
    unresolved = []
    for candidate in proposal_candidates:
        evidence = tuple(candidate.transition_evidence_key or ())
        if evidence and evidence[0] == "linear_self_recursion_transition_evidence_v1":
            fields = dict(item for item in evidence[1:] if isinstance(item, tuple) and len(item) == 2)
            if (
                fields.get("step") not in {-1, 1}
                or fields.get("effect_profile") != "single_direct_self_call_no_store"
                or fields.get("termination_measure") not in {
                    "signed_unit_decrement_to_bound", "signed_unit_increment_to_bound",
                }
            ):
                raise ValueError("unit-step recursion lacks typed termination evidence")
            propositions.append((
                "candidate_transition_v2", candidate.candidate_id,
                ("unit_step_affine_recursion_v1", tuple(evidence)),
            ))
            validated_evidence_keys.add(candidate.transition_evidence_key)
            continue
        refs = tuple(_runtime_refs(candidate.return_info.value))
        if not refs:
            unresolved.append(candidate)
            continue
        for runtime_ref in refs:
            if isinstance(runtime_ref, CountedLoopSummaryRef):
                proposition = _validate_counted_summary(runtime_ref)
            elif isinstance(runtime_ref, StateTransitionLoopSummaryRef):
                proposition = _validate_state_transition_termination(runtime_ref)
            elif isinstance(runtime_ref, CountedStateTransitionLoopSummaryRef):
                proposition = _validate_counted_state_transition(runtime_ref)
            else:  # pragma: no cover - guarded by _runtime_refs
                raise ValueError("unsupported recurrence runtime summary")
            propositions.append((
                "candidate_transition_v2", candidate.candidate_id, proposition,
            ))
        validated_evidence_keys.add(candidate.transition_evidence_key)
    # A zero-trip/base member intentionally has no runtime intrinsic.  It can
    # share authority only with a summary member carrying the exact same typed
    # transition evidence inside this proposal; arbitrary evidence reuse is
    # rejected.
    for candidate in unresolved:
        if (
            candidate.transition_evidence_key is None
            or candidate.transition_evidence_key not in validated_evidence_keys
        ):
            raise ValueError("recurrence candidate has no typed runtime summary")
        propositions.append(
            (
                "candidate_transition_v2",
                candidate.candidate_id,
                (
                    "base_member_bound_to_transition_v1",
                    candidate.candidate_id,
                    candidate.transition_evidence_key,
                ),
            )
        )
    if not propositions:
        raise ValueError("recurrence proposal has no transition/termination proposition")
    return tuple(propositions)


class PairPromotionState(str, Enum):
    OPEN = "open"
    COMPOSED = "composed"
    ABORTED = "aborted"


@dataclass(frozen=True)
class RecurrenceSidePromotion:
    side: str
    source_analysis: FunctionReturnAnalysis
    successor_analysis: FunctionReturnAnalysis
    proposal: Optional[QuarantinedRecurrenceProposal]
    seed_core: Optional[RecurrenceSeedCore]
    entry: Any = None


@dataclass(frozen=True)
class PairPromotionAttempt:
    state: PairPromotionState
    authority: Optional["PairRecurrencePromotionAuthority"] = None
    left: Optional[RecurrenceSidePromotion] = None
    right: Optional[RecurrenceSidePromotion] = None
    failure: Optional[str] = None
    schema_version: str = "pair_recurrence_promotion_v1"

    def to_dict(self) -> Mapping[str, Any]:
        def side_payload(side: Optional[RecurrenceSidePromotion]) -> Optional[Mapping[str, Any]]:
            if side is None:
                return None
            transition_tags = []
            if side.entry is not None:
                validation = side.entry.artifact.payload.get(
                    "recurrence_validation_evidence", {}
                )
                for subproof in validation.get("subproofs", ()):
                    if subproof.get("proof_kind") != "transition_termination":
                        continue
                    proposition = tuple(subproof.get("proposition_key", ()))
                    if len(proposition) >= 3:
                        transition_tags.extend(
                            item[2][0] for item in proposition[2]
                            if (
                                isinstance(item, (tuple, list)) and len(item) == 3
                                and isinstance(item[2], (tuple, list)) and item[2]
                            )
                        )
            return {
                "side": side.side,
                "proposal_generated": side.proposal is not None,
                "pattern_kind": side.proposal.pattern_kind if side.proposal is not None else None,
                "proposal_digest": side.proposal.digest if side.proposal is not None else None,
                "transition_proposition_tags": transition_tags,
                "validated_artifact_id": (
                    side.entry.artifact.artifact_id if side.entry is not None else None
                ),
                "artifact_validation_status": (
                    side.entry.artifact.artifact_validation_status
                    if side.entry is not None else None
                ),
                "validated_artifact_imported": side.entry is not None and self.state == PairPromotionState.COMPOSED,
                "promoted_successor_surface_fingerprint": (
                    AnalysisSnapshot.from_function_analysis(
                        side.successor_analysis
                    ).semantic_fingerprint
                    if side.proposal is not None else None
                ),
            }

        return {
            "schema_version": "pair_recurrence_promotion_receipt_v1",
            "state": self.state.value,
            "failure": self.failure,
            "branch_local_authority_issued": self.authority is not None,
            "authority": (
                {
                    "comparison_session_id": self.authority.comparison_session_id,
                    "branch_id": self.authority.branch_id,
                    "targeted_blocker_keys": self.authority.targeted_blocker_keys,
                    "digest": self.authority.digest,
                }
                if self.authority is not None else None
            ),
            "left": side_payload(self.left),
            "right": side_payload(self.right),
        }


@dataclass(frozen=True)
class PairRecurrencePromotionAuthority:
    comparison_session_id: str
    branch_id: str
    targeted_blocker_keys: Tuple[Tuple[Any, ...], ...]
    predecessor_outcome: str = "inconclusive"
    counterexample_safety_pending: bool = False
    schema_version: str = "pair_recurrence_promotion_authority_v1"

    def __post_init__(self) -> None:
        if not self.comparison_session_id or not self.branch_id:
            raise ValueError("recurrence promotion requires pair branch identity")
        if self.predecessor_outcome not in {"inconclusive", "unknown"}:
            raise ValueError("terminal branch cannot authorize recurrence promotion")
        if self.counterexample_safety_pending:
            raise ValueError("counterexample-safety pending branch cannot be promoted")
        if not self.targeted_blocker_keys or any(
            not isinstance(item, tuple) or not item
            for item in self.targeted_blocker_keys
        ):
            raise ValueError("recurrence promotion requires targeted blocker authority")

    @property
    def digest(self) -> str:
        return RecurrenceDigestCodec.digest(
            self.schema_version,
            (
                self.comparison_session_id, self.branch_id,
                self.targeted_blocker_keys, self.predecessor_outcome,
                self.counterexample_safety_pending,
            ),
        )


def _proposal_candidates(
    analysis: FunctionReturnAnalysis,
    proposal: QuarantinedRecurrenceProposal,
) -> Tuple[SummaryReturnCandidate, ...]:
    proposal_ids = {item.candidate_id for item in proposal.new_returns}
    retained_keys = {
        (item.identity_key, item.payload_digest)
        for item in proposal.retained_exact_return_refs
    }

    def belongs(candidate: SummaryReturnCandidate) -> bool:
        if candidate.candidate_id in proposal_ids:
            return True
        marker = getattr(candidate.return_info, "retained_exact_return_ref", None)
        return bool(
            isinstance(marker, tuple)
            and len(marker) == 3
            and marker[0] == "retained_exact_return_v1"
            and (
                tuple(marker[1]),
                RecurrenceDigestCodec.digest(
                    "retained_exact_return_payload_v1", marker[2]
                ),
            ) in retained_keys
        )

    return tuple(
        candidate
        for candidate in tuple(analysis.summary_return_candidates or ())
        if belongs(candidate)
    )


def _proposal_return_semantic_identity(value: Any) -> Tuple[Any, ...]:
    return (
        "recurrence_proposal_return_semantic_v1",
        tuple(item.stable_key() for item in value.guard),
        value.value.stable_key(),
        tuple(value.transition_evidence_key or ()),
    )


def _accepted_candidate_semantic_identity(
    candidate: SummaryReturnCandidate,
) -> Tuple[Any, ...]:
    return (
        "recurrence_proposal_return_semantic_v1",
        tuple(
            ImmutableRecurrenceCondition.from_condition(condition).stable_key()
            for condition in tuple(candidate.return_info.conditions or ())
        ),
        ImmutableRecurrenceExpression.from_expression(
            candidate.return_info.value
        ).stable_key(),
        tuple(candidate.transition_evidence_key or ()),
    )


def _bind_accepted_candidates_to_proposal(
    accepted: Any,
    proposal: QuarantinedRecurrenceProposal,
) -> Any:
    proposal_by_id = {
        tuple(item.candidate_id): item for item in proposal.new_returns
    }
    proposal_by_semantic: dict[Tuple[Any, ...], list[Any]] = {}
    for item in proposal.new_returns:
        proposal_by_semantic.setdefault(
            _proposal_return_semantic_identity(item), []
        ).append(item)

    used_ids: set[Tuple[Any, ...]] = set()
    rebound = []
    rebound_ids: dict[Tuple[Any, ...], Tuple[Any, ...]] = {}
    for candidate in tuple(accepted.candidates or ()):
        old_id = tuple(candidate.candidate_id)
        semantic_identity = _accepted_candidate_semantic_identity(candidate)
        proposal_return = proposal_by_id.get(old_id)
        if (
            proposal_return is not None
            and _proposal_return_semantic_identity(proposal_return)
            != semantic_identity
        ):
            raise ValueError(
                "accepted recurrence candidate content differs from proposal identity"
            )
        if proposal_return is None:
            matches = tuple(
                item
                for item in proposal_by_semantic.get(
                    semantic_identity, ()
                )
                if tuple(item.candidate_id) not in used_ids
            )
            if len(matches) != 1:
                raise ValueError(
                    "accepted recurrence candidate has no unique proposal identity"
                )
            proposal_return = matches[0]
        proposal_id = tuple(proposal_return.candidate_id)
        if proposal_id in used_ids:
            raise ValueError("accepted recurrence candidate identity is duplicated")
        used_ids.add(proposal_id)
        rebound_ids[old_id] = proposal_id
        rebound_return = replace(
            candidate.return_info,
            summary_candidate_id=proposal_id,
        )
        rebound.append(replace(
            candidate,
            candidate_id=proposal_id,
            return_info=rebound_return,
        ))

    if used_ids != set(proposal_by_id):
        raise ValueError("accepted recurrence candidate set is incomplete")

    accepted_returns = tuple(
        replace(
            item,
            summary_candidate_id=rebound_ids[tuple(item.summary_candidate_id)],
        )
        if (
            item.summary_candidate_id is not None
            and tuple(item.summary_candidate_id) in rebound_ids
        )
        else item
        for item in tuple(accepted.accepted_returns or ())
    )
    return replace(
        accepted,
        candidates=tuple(rebound),
        accepted_returns=accepted_returns,
    )


def _seed_core(
    analysis: FunctionReturnAnalysis,
    proposal: QuarantinedRecurrenceProposal,
    candidates: Tuple[SummaryReturnCandidate, ...],
) -> RecurrenceSeedCore:
    proposal_ids = {item.candidate_id for item in proposal.new_returns}
    proposal_candidates = tuple(
        candidate for candidate in candidates if candidate.candidate_id in proposal_ids
    )
    proposal_candidates = tuple(sorted(
        proposal_candidates,
        key=lambda candidate: RecurrenceDigestCodec.canonical_bytes(
            "recurrence_candidate_sort_v1",
            (
                candidate.guard_structural_key,
                candidate.value_structural_key,
                candidate.transition_evidence_key,
                candidate.effect_region_key,
            ),
        ),
    ))
    if not proposal_candidates:
        raise ValueError("recurrence proposal has no accepted candidate binding")
    seed = RecurrenceSeedCore(
        analysis.outcome_function_identity(),
        proposal_candidates[0].active_precondition_key,
        proposal.retained_exact_return_refs,
        tuple(
            (
                candidate.effect_region_key,
                candidate.memory_read_set_key,
                candidate.memory_write_set_key,
                candidate.call_effect_key,
                candidate.ub_assumption_key,
            )
            for candidate in proposal_candidates
        ),
    )
    if seed.digest != proposal.seed_core_digest:
        raise ValueError("recurrence proposal seed core mismatch")
    return seed


def _is_self_target(value: Any, function_key: Tuple[Any, ...]) -> bool:
    target = getattr(value, "target_ref", None)
    stable_key = getattr(target, "stable_key", None)
    return callable(stable_key) and stable_key() == function_key


def _materialize_effect_successor(
    successor: FunctionReturnAnalysis,
    source: FunctionReturnAnalysis,
) -> FunctionReturnAnalysis:
    source_effect_summary = getattr(source, "effect_summary", None)
    effect_summary = (
        replace(
            source_effect_summary,
            parameter_names=list(source_effect_summary.parameter_names or ()),
            effects=list(source_effect_summary.effects or ()),
            parameter_refs=list(source_effect_summary.parameter_refs or ()),
            call_argument_evidence=dict(
                source_effect_summary.call_argument_evidence or {}
            ),
        )
        if source_effect_summary is not None else None
    )
    promoted = replace(
        successor,
        effect_summary=effect_summary,
        deferred_calls=dict(getattr(source, "deferred_calls", {}) or {}),
    )
    if effect_summary is None:
        return promoted
    if tuple(getattr(effect_summary, "effects", ()) or ()):
        raise ValueError("recurrence promotion cannot erase STORE effects")
    function_ref = getattr(source, "function_ref", None)
    function_key = (
        function_ref.stable_key()
        if callable(getattr(function_ref, "stable_key", None))
        else None
    )
    if function_key is None:
        raise ValueError("recurrence promotion requires function identity")
    unsupported_sites = tuple(effect_summary.unsupported_call_sites or ())
    call_evidence = tuple(
        item for item in effect_summary.call_argument_evidence.values() if item is not None
    )
    deferred_calls = tuple(
        item for item in promoted.deferred_calls.values() if item is not None
    )
    if not unsupported_sites and not call_evidence and not deferred_calls:
        if effect_summary.has_unsupported_call:
            raise ValueError("recurrence promotion has an unbound unsupported CALL")
        return promoted
    if not unsupported_sites or not all(
        _is_self_target(item, function_key) for item in unsupported_sites
    ):
        raise ValueError("recurrence promotion has an unexplained non-self CALL")
    if call_evidence and not all(
        _is_self_target(item, function_key) for item in call_evidence
    ):
        raise ValueError("recurrence promotion has non-self call evidence")
    if deferred_calls and not all(
        _is_self_target(item, function_key) for item in deferred_calls
    ):
        raise ValueError("recurrence promotion has an unexplained deferred CALL")
    profile = effect_summary.function_control_effect_profile
    if profile is not None:
        effect_summary.function_control_effect_profile = replace(
            profile,
            call_count=0,
            callind_count=0,
            callother_count=0,
            call_like_pcode_op_keys=(),
            direct_call_target_keys=(),
            phase2_unsafe_mnemonics=tuple(
                item
                for item in profile.phase2_unsafe_mnemonics
                if str(item) not in {"CALL", "CALLIND", "CALLOTHER"}
            ),
        )
    effect_summary.has_unsupported_call = False
    effect_summary.unsupported_call_sites = ()
    effect_summary.call_argument_evidence = {}
    effect_summary.call_site_effect_summary_evidence = ()
    effect_summary.call_target_resolution_evidence = ()
    effect_summary.incomplete_reasons = tuple(
        reason
        for reason in tuple(effect_summary.incomplete_reasons or ())
        if str(reason)
        not in {
            "callee_effect_summary_missing",
            "unsupported_call_effect",
            "effect_call_argument_evidence_incomplete",
        }
    )
    promoted.deferred_calls = {}
    return promoted


def _prepare_side_for_proposal(
    analysis: FunctionReturnAnalysis,
    side: str,
    proposal: QuarantinedRecurrenceProposal,
) -> RecurrenceSidePromotion:
    candidates = _proposal_candidates(analysis, proposal)
    if not candidates:
        raise ValueError("recurrence proposal candidates are unavailable")
    accepted = accept_summary_return_candidates(
        analysis,
        tuple(candidate.return_info for candidate in candidates),
        summary_note=proposal.pattern_kind,
        enable_completed_recovery_proofs=True,
        require_smt_receipts=True,
    )
    try:
        from scripts.function_tracer_pcode.authority.domains.call_effect import (
            summary_effect_prerequisite_signals_from_acceptance,
        )
        from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
            summary_signals_from_acceptance,
        )
        from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
            summary_abi_width_signals_from_acceptance,
        )
        from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
            emit_abi_width_readonly_signal,
            emit_call_effect_signal,
            emit_loop_recurrence_signal,
        )

        for signal in summary_effect_prerequisite_signals_from_acceptance(
            analysis, accepted
        ):
            emit_call_effect_signal(
                signal, producer_site_manifest_id="recurrence-summary-call-effect"
            )
        for signal in summary_signals_from_acceptance(analysis, accepted):
            emit_loop_recurrence_signal(
                signal, producer_site_manifest_id="recurrence-summary-loop"
            )
        for signal in summary_abi_width_signals_from_acceptance(analysis, accepted):
            emit_abi_width_readonly_signal(
                signal, producer_site_manifest_id="recurrence-summary-abi-width"
            )
    except Exception as exc:
        from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
            record_production_pilot_shadow_error,
        )

        record_production_pilot_shadow_error(exc)
    if accepted.blockers or not accepted.accepted_returns:
        raise ValueError(
            "recurrence acceptance failed:" + ",".join(accepted.blockers)
        )
    accepted = _bind_accepted_candidates_to_proposal(accepted, proposal)
    seed = _seed_core(analysis, proposal, tuple(accepted.candidates))
    successor = analysis.with_accepted_return_partition(
        list(accepted.accepted_returns),
        summary_return_candidates=accepted.candidates,
        reason=proposal.pattern_kind,
    )
    successor = replace(successor, quarantined_recurrence_proposals=())
    # Validate the complete effect surface before minting any proved receipt.
    # This is the equivalence-layer proof that recursive CALLs are precisely
    # self-calls and that no STORE or unrelated CALL is erased.
    successor = _materialize_effect_successor(successor, analysis)
    unary = ObligationRuntimeSession.create_unary(
        analysis,
        domain=UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value,
        semantic_seed=seed,
        domain_contract=RECURRENCE_DOMAIN_CONTRACT,
        normalization_policy_digest=RECURRENCE_NORMALIZATION_POLICY,
    )
    premise = unary.premise_digest
    binding = function_recurrence_binding_digest(seed.digest, proposal.digest, premise)
    target = (
        "function_recurrence_promotion_v1",
        analysis.outcome_function_identity(),
        proposal.pattern_kind,
    )
    requirement = recurrence_proof_requirement(
        seed.digest,
        proposal.digest,
        binding,
        "recurrence_validation_complete",
        target,
    )
    proposal_candidate_ids = {item.candidate_id for item in proposal.new_returns}
    candidate_keys = tuple(
        (
            "candidate_v2",
            candidate.candidate_id,
            _candidate_guard_identity(candidate),
            ImmutableRecurrenceExpression.from_expression(
                candidate.return_info.value
            ).stable_key(),
            _candidate_transition_identity(candidate),
            _candidate_width_sort_key(candidate),
            (
                "active_precondition_digest_v1",
                RecurrenceDigestCodec.digest(
                    "recurrence_active_precondition_v1",
                    candidate.active_precondition_key,
                ),
            ),
        )
        for candidate in accepted.candidates
        if candidate.candidate_id in proposal_candidate_ids
    )
    candidate_proof = RecurrenceSubproofEvidence(
        "candidate_validation",
        (
            "candidate_validation_v2",
            proposal.pattern_kind,
            proposal.digest,
            candidate_keys,
        ),
        "summary_return_candidate_validator_v2",
    )
    termination_propositions = _validated_transition_termination(
        tuple(accepted.candidates), proposal
    )
    transition_proof = RecurrenceSubproofEvidence(
        "transition_termination",
        (
            "transition_termination_v2",
            proposal.digest,
            termination_propositions,
            tuple(
                ("candidate_surface_v1", item[1], item[5])
                for item in candidate_keys
            ),
        ),
        "typed_recurrence_transition_termination_validator_v2",
        dependencies=(candidate_proof.digest,),
    )
    overlap_proof = RecurrenceSubproofEvidence(
        "overlap",
        (
            "overlap_unsat_v2",
            proposal.digest,
            tuple(item.stable_key() for item in accepted.overlap_query_receipts),
        ),
        "condition_smt_overlap_validator_v2",
        dependencies=(candidate_proof.digest, transition_proof.digest),
    )
    coverage_proof = RecurrenceSubproofEvidence(
        "partition_coverage",
        (
            "partition_coverage_unsat_v2",
            proposal.digest,
            tuple(item.stable_key() for item in accepted.coverage_query_receipts),
        ),
        "condition_smt_partition_totality_v2",
        dependencies=(overlap_proof.digest,),
    )
    effect_proof = RecurrenceSubproofEvidence(
        "effect_surface",
        (
            "effect_surface_v2",
            proposal.digest,
            tuple(
                (
                    "candidate_effect_v1",
                    candidate.candidate_id,
                    candidate.effect_region_key,
                    candidate.memory_read_set_key,
                    candidate.memory_write_set_key,
                    candidate.call_effect_key,
                    candidate.ub_assumption_key,
                )
                for candidate in accepted.candidates
                if candidate.candidate_id in proposal_candidate_ids
            ),
        ),
        "recurrence_effect_surface_validator_v2",
        dependencies=(candidate_proof.digest,),
    )
    validation_evidence = RecurrenceValidationEvidence(
        seed.digest,
        proposal.digest,
        binding,
        (
            candidate_proof, transition_proof, overlap_proof,
            coverage_proof, effect_proof,
        ),
    )
    closure = semantic_recurrence_closure_digest(
        binding,
        (requirement.to_key(),),
        validation_evidence.proof_result_digest,
        validation_evidence.dependency_subproof_digests,
    )
    # unary（関数単体）の recurrence artifact。peer 関数も入力の対応も前提にしない。
    evidence = {
        AUTHORITY_SCOPE_KEY: FUNCTION_UNARY,
        "proof_obligation_id": (
            "proof_obligation_id",
            "loop_recurrence_proof",
            requirement.proof_target_key,
        ),
        "reason_id": "recurrence_validation_complete",
        "status": "complete",
        "proof_stage": "recurrence_validation_complete",
        "evidence_kind": "validated_unary_recurrence_artifact",
        "object_target_key": requirement.proof_target_key,
        "proof_source": "equivalence_recurrence_validator_v1",
        "proof_requirement": requirement.to_dict(),
        "seed_core_digest": seed.digest,
        "proposal_digest": proposal.digest,
        "function_unary_premise_digest": premise,
        "function_recurrence_binding_digest": binding,
        "semantic_closure_digest": closure,
        "validated_unary_artifact_id": ("validated_recurrence_artifact_v2", closure),
        "recurrence_validation_evidence": validation_evidence.to_dict(),
        "proof_content": {
            "object_derived": True,
            "status": "complete",
            "candidate_ids": tuple(item.candidate_id for item in accepted.candidates),
            "candidate_validation": "proved",
            "overlap_proof": "proved",
            "candidate_partition_coverage": "proved",
            "effect_surface": "proved_or_empty",
            "final_pairwise_coverage": "not_claimed",
            "proof_result_digest": validation_evidence.proof_result_digest,
            "dependency_subproof_digests": (
                validation_evidence.dependency_subproof_digests
            ),
        },
    }
    artifact = ProofArtifact(
        artifact_id=("validated_recurrence_artifact_v2", closure),
        requirement_id=requirement,
        produced_from_view_id=unary.current_view.view_id,
        premise_digest=premise,
        producer_id="equivalence_recurrence_validator",
        producer_version="1",
        encoding_version="recurrence_digest_codec_v1",
        artifact_validation_status="validated",
        payload=evidence,
    )
    unary.artifacts.append(artifact)
    entry = unary.publish_recurrence_artifact(artifact, seed, proposal)
    record_function_unary_evidence(successor, evidence)
    successor.completed_recovery_proof_ids = (
        tuple(successor.completed_recovery_proof_ids or ())
        + (evidence["proof_obligation_id"],)
    )
    return RecurrenceSidePromotion(side, analysis, successor, proposal, seed, entry)


def _prepare_side(
    analysis: FunctionReturnAnalysis,
    side: str,
) -> RecurrenceSidePromotion:
    proposals = tuple(analysis.quarantined_recurrence_proposals or ())
    if not proposals:
        return RecurrenceSidePromotion(side, analysis, analysis, None, None)
    prepared = []
    failures = []
    for proposal in proposals:
        try:
            prepared.append(_prepare_side_for_proposal(analysis, side, proposal))
        except (TypeError, ValueError, RuntimeError) as exc:
            failures.append(f"{proposal.digest}:{type(exc).__name__}:{exc}")
    if not prepared:
        raise ValueError("no recurrence proposal validated:" + "|".join(failures))
    if len(prepared) != 1:
        raise ValueError("multiple recurrence proposals validated for one branch")
    return prepared[0]


def promote_recurrence_pair(
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    authority: PairRecurrencePromotionAuthority,
) -> Tuple[FunctionReturnAnalysis, FunctionReturnAnalysis, ObligationRuntimeSession, PairPromotionAttempt]:
    if not isinstance(authority, PairRecurrencePromotionAuthority):
        raise TypeError("recurrence promotion requires pair-local branch authority")
    pair_runtime = ObligationRuntimeSession.create(analysis1, analysis2)
    try:
        left = _prepare_side(analysis1, "left")
        right = _prepare_side(analysis2, "right")
        for prepared in (left, right):
            if prepared.proposal is not None and not any(
                prepared.proposal.digest in tuple(_flatten_tuple(blocker_key))
                for blocker_key in authority.targeted_blocker_keys
            ):
                raise ValueError(
                    "validated recurrence proposal does not target this branch blocker"
                )
            if prepared.entry is None:
                continue
            pair_runtime.import_unary_artifact_for_analysis(
                prepared.entry,
                analysis=prepared.source_analysis,
                domain=UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value,
                semantic_seed=prepared.seed_core,
                selected_recurrence_proposal=prepared.proposal,
                pair_side=prepared.side,
                domain_contract=RECURRENCE_DOMAIN_CONTRACT,
                normalization_policy_digest=RECURRENCE_NORMALIZATION_POLICY,
            )
    except (TypeError, ValueError, RuntimeError) as exc:
        return (
            analysis1,
            analysis2,
            pair_runtime,
            PairPromotionAttempt(
                PairPromotionState.ABORTED,
                authority=authority,
                failure=f"{type(exc).__name__}:{exc}",
            ),
        )
    return (
        left.successor_analysis,
        right.successor_analysis,
        pair_runtime,
        PairPromotionAttempt(
            PairPromotionState.COMPOSED,
            authority=authority,
            left=left,
            right=right,
        ),
    )


def _flatten_tuple(value: Any) -> Iterable[Any]:
    if isinstance(value, tuple):
        for item in value:
            yield from _flatten_tuple(item)
        return
    yield value
