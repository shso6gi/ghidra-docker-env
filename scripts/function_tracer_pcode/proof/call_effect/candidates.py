"""Internal call-site correspondence candidates (Issue #20 PR-D).

`CallSiteFact.semantic_shape_key()` の思想 —— **候補対応は未証明の callee return
relation に依存してはならない** —— をそのまま維持したまま、内部 callee の
callsite 対応候補に型付きの identity を与える。

順序は次で固定する。

    candidate correspondence  →  後段の callee return / effect proof

したがって本モジュールは ``callee_return_shape_keys`` /
``callee_return_summary_statuses`` / ``callee_effect_summary_statuses`` /
``callee_memory_effect_counts`` を **一切読まない**。読まないことは
``internal_candidate_inputs`` を通した投影と unit test で固定する。

候補は semantic shape の **相互一意**でのみ成立する。同じ shape が片側に複数
あれば ambiguous として不成立（fail closed）にする。候補を増やすために一致
条件を緩めることはしない。P-code 位置は出力順を決めるためだけに保持し、
shape が同じ複数候補を「位置が近いから」で結び付けることはしない。

``InternalCallCorrespondenceCandidateId`` は **candidate matching identity** であって
callee semantic equivalence proof digest ではない。callee return relation /
callee effect relation / invocation・use・guard proof は、正本 v4 のとおり
**既存の call-effect proof stage** が担う。ここで callee の意味に踏み込む前段
gate は置かない（構造が違っても後段 solver が等価を証明できる余地を潰さない）。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence, Tuple


#: 内部 callee の callsite だけが候補になる。
INTERNAL_CALL_CANDIDATE_OPERATION_CLASS = "resolved_internal_call_candidate"

#: 候補が成立しなかった理由。
CANDIDATE_SHAPE_AMBIGUOUS = "internal_call_candidate_shape_ambiguous"
CANDIDATE_SHAPE_UNMATCHED = "internal_call_candidate_shape_unmatched"

#: 候補 identity が読んではいけない CallSiteFact のフィールド。
#: 後段 proof の入力であって、候補形成の前提ではない（循環防止）。
CALLEE_PROOF_FIELDS_EXCLUDED_FROM_CANDIDATE_IDENTITY = (
    "callee_return_shape_keys",
    "callee_return_summary_statuses",
    "callee_effect_summary_statuses",
    "callee_memory_effect_counts",
    "callee_has_unsupported_nested_call",
    "callee_recursive_scc_proven",
    "callee_recursive_scc_identities",
    "callee_recursive_scc_member_keys",
    "callee_ordered_scalar_store_candidates",
    "callee_control_profile_keys",
)


def _pcode_position(fact: Any) -> Tuple[Any, ...]:
    """Deterministic ordering position of a call site.

    Ordering only.  It never disambiguates two shape-equal candidates.
    """

    identity = getattr(fact, "identity", None)
    pcode_key = getattr(identity, "pcode_op_key", None)
    if isinstance(pcode_key, (tuple, list)):
        return tuple(pcode_key)
    return ()


def internal_candidate_inputs(fact: Any) -> Dict[str, Any]:
    """The exact projection a candidate identity is allowed to read.

    Anything not in here — in particular every callee return / effect fact — is
    an input to a *later* proof stage and must not gate candidate formation.
    """

    return {
        "fact_kind": getattr(fact, "fact_kind", None),
        "operation_class": (
            fact.correspondence_operation_class()
            if callable(getattr(fact, "correspondence_operation_class", None))
            else None
        ),
        "semantic_shape_key": (
            tuple(fact.semantic_shape_key())
            if callable(getattr(fact, "semantic_shape_key", None))
            else ()
        ),
        "argument_arity": len(getattr(fact, "argument_keys", ()) or ()),
        "callee_parameter_arity": len(getattr(fact, "callee_parameter_keys", ()) or ()),
        "abi_argument_slot_keys": tuple(getattr(fact, "abi_argument_slot_keys", ()) or ()),
        "target_categories": tuple(getattr(fact, "target_categories", ()) or ()),
        "target_resolution_status": getattr(fact, "target_resolution_status", None),
    }


@dataclass(frozen=True)
class InternalCallCorrespondenceCandidateId:
    """Identity of one internal callsite correspondence *candidate*.

    This is a matching identity, not a proof digest: it says which left call
    site is paired with which right call site for the later callee return /
    effect obligations to work on.  It deliberately carries nothing about
    whether those obligations hold.
    """

    left_fact_id: str
    right_fact_id: str
    correspondence_shape_key: Tuple[Any, ...]
    abi_argument_slot_keys: Tuple[Tuple[Any, ...], ...] = ()
    left_position: Tuple[Any, ...] = ()
    right_position: Tuple[Any, ...] = ()

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "internal_call_correspondence_candidate",
            self.left_fact_id,
            self.right_fact_id,
            self.correspondence_shape_key,
            self.abi_argument_slot_keys,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "internal_call_correspondence_candidate",
            "left_fact_id": self.left_fact_id,
            "right_fact_id": self.right_fact_id,
            "correspondence_shape_key": list(self.correspondence_shape_key),
            "abi_argument_slot_keys": [list(key) for key in self.abi_argument_slot_keys],
            "left_position": list(self.left_position),
            "right_position": list(self.right_position),
        }


@dataclass(frozen=True)
class InternalCallCandidateResult:
    """Formed candidates plus the fail-closed reasons for the rest."""

    candidates: Tuple[InternalCallCorrespondenceCandidateId, ...] = ()
    unmatched_reasons: Tuple[Tuple[str, str], ...] = ()

    def candidate_for(self, left_fact_id: str) -> Optional[InternalCallCorrespondenceCandidateId]:
        for candidate in self.candidates:
            if candidate.left_fact_id == left_fact_id:
                return candidate
        return None


def _is_internal_call_site(fact: Any) -> bool:
    if getattr(fact, "fact_kind", None) != "call_site":
        return False
    operation_class = getattr(fact, "correspondence_operation_class", None)
    if not callable(operation_class):
        return False
    return operation_class() == INTERNAL_CALL_CANDIDATE_OPERATION_CLASS


def build_internal_call_correspondence_candidates(
    left_facts: Sequence[Any],
    right_facts: Sequence[Any],
) -> InternalCallCandidateResult:
    """Form mutually unique internal callsite candidates, failing closed.

    A candidate exists only when exactly one left fact and exactly one right
    fact share a semantic shape.  Duplicated shapes stay unmatched: pairing them
    would need a tiebreak that no evidence supports.
    """

    left_internal = [fact for fact in (left_facts or ()) if _is_internal_call_site(fact)]
    right_internal = [fact for fact in (right_facts or ()) if _is_internal_call_site(fact)]

    def index_by_shape(facts: Sequence[Any]) -> Dict[Tuple[Any, ...], List[Any]]:
        index: Dict[Tuple[Any, ...], List[Any]] = {}
        for fact in facts:
            index.setdefault(tuple(fact.semantic_shape_key()), []).append(fact)
        return index

    left_index = index_by_shape(left_internal)
    right_index = index_by_shape(right_internal)

    candidates: List[InternalCallCorrespondenceCandidateId] = []
    reasons: List[Tuple[str, str]] = []
    for shape, lefts in left_index.items():
        rights = right_index.get(shape, [])
        if len(lefts) != 1 or len(rights) != 1:
            reason = (
                CANDIDATE_SHAPE_AMBIGUOUS
                if (len(lefts) > 1 or len(rights) > 1)
                else CANDIDATE_SHAPE_UNMATCHED
            )
            for fact in lefts:
                reasons.append((str(fact.fact_id), reason))
            continue
        left_fact, right_fact = lefts[0], rights[0]
        # identity correspondence は左右で一致したときだけ候補 ID に載せる。
        # 片側にしか無いスロット identity を「対応した」と書かない。
        left_slots = tuple(tuple(key) for key in (getattr(left_fact, "abi_argument_slot_keys", ()) or ()))
        right_slots = tuple(tuple(key) for key in (getattr(right_fact, "abi_argument_slot_keys", ()) or ()))
        agreed_slots = left_slots if left_slots == right_slots else ()
        candidates.append(
            InternalCallCorrespondenceCandidateId(
                left_fact_id=str(left_fact.fact_id),
                right_fact_id=str(right_fact.fact_id),
                correspondence_shape_key=shape,
                abi_argument_slot_keys=agreed_slots,
                left_position=_pcode_position(left_fact),
                right_position=_pcode_position(right_fact),
            )
        )
    for shape, rights in right_index.items():
        if shape in left_index:
            continue
        for fact in rights:
            reasons.append((str(fact.fact_id), CANDIDATE_SHAPE_UNMATCHED))

    # P-code position はここでの並べ替えにだけ使う（候補の解消には使わない）。
    candidates.sort(key=lambda item: (item.left_position, item.right_position, item.left_fact_id))
    return InternalCallCandidateResult(
        candidates=tuple(candidates),
        unmatched_reasons=tuple(sorted(set(reasons))),
    )


def candidate_identity_is_callee_proof_free(
    candidate: InternalCallCorrespondenceCandidateId,
    fact: Any,
) -> bool:
    """Assert the identity did not consume any callee return / effect fact.

    Used by tests: mutating an excluded field must leave ``stable_key()`` alone.
    """

    projection = internal_candidate_inputs(fact)
    return all(
        field not in projection
        for field in CALLEE_PROOF_FIELDS_EXCLUDED_FROM_CANDIDATE_IDENTITY
    ) and bool(candidate.stable_key())
