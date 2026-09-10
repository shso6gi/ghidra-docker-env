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


# ---------------------------------------------------------------------------
# candidate → callee correspondence proof → callsite correspondence
# ---------------------------------------------------------------------------
#
# 権限境界を型で分ける（正本 v4 §4.3.4）。
#
#   1. candidate 形成            InternalCallCorrespondenceCandidateId
#        semantic shape の相互一意のみ。callee return / effect を読まない。
#   2. callee correspondence     RelationalCalleeCorrespondenceId
#        **左右 callee が対応する**ことを、後段の callee return / effect 事実から
#        関係的に確立する。ここで初めて callee の事実を読んでよい。
#   3. callsite correspondence   InternalCallsiteCorrespondence
#        candidate + callee correspondence + relational argument key の三点が
#        揃って初めて成立する。
#
# 1 で 2/3 の入力を先取りしない（循環防止）。2 が無ければ 3 は成立しない。

#: callee correspondence が確立できない理由（fail closed）。
CALLEE_RETURN_SUMMARY_UNPROVEN = "internal_callee_return_summary_unproven"
CALLEE_RETURN_SHAPE_RELATION_MISSING = "internal_callee_return_shape_relation_missing"
CALLEE_EFFECT_SUMMARY_UNPROVEN = "internal_callee_effect_summary_unproven"
CALLEE_MEMORY_EFFECT_RELATION_MISSING = "internal_callee_memory_effect_relation_missing"
CALLEE_CONTROL_PROFILE_RELATION_MISSING = "internal_callee_control_profile_relation_missing"

#: callsite correspondence が確立できない理由（fail closed）。
CALLSITE_CANDIDATE_MISSING = "internal_callsite_candidate_missing"
CALLSITE_CALLEE_CORRESPONDENCE_MISSING = "internal_callsite_callee_correspondence_missing"
CALLSITE_ARGUMENT_RELATION_MISSING = "internal_callsite_argument_relation_missing"


def _single(values: Any) -> Optional[Any]:
    """The one element of a one-element sequence, else ``None`` (fail closed)."""

    items = tuple(values or ())
    return items[0] if len(items) == 1 else None


@dataclass(frozen=True)
class RelationalCalleeCorrespondenceId:
    """Identity of the left-callee ↔ right-callee correspondence obligation.

    **何を主張するか**: 「この 2 つの callsite の callee を突き合わせる関係が、
    後段 proof の入力として関係的に成立している」ことだけ。両 callee が
    *等価である*ことは主張しない。等価性は後段の ``return_relation`` /
    ``memory_relation`` 等が証明する。

    **何を主張しないか**: 左右の return shape / memory 効果数 / control profile が
    構造的に一致すること。一致は等価の必要条件ではない（同じ番地を 2 回上書き
    する callee と 1 回だけ書く callee は最終状態が同じなら等価であり、効果数は
    違う）。ここで構造一致を要求すると、後段 proof が証明できるはずの等価を
    先回りして潰してしまう。

    したがって成立条件は **入力の関係的な健全性**に限る。
    """

    candidate_key: Tuple[Any, ...]
    left_callee_return_shape_keys: Tuple[Tuple[Any, ...], ...]
    right_callee_return_shape_keys: Tuple[Tuple[Any, ...], ...]
    left_callee_effect_key: Tuple[Any, ...]
    right_callee_effect_key: Tuple[Any, ...]

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "relational_callee_correspondence",
            self.candidate_key,
            self.left_callee_return_shape_keys,
            self.right_callee_return_shape_keys,
            self.left_callee_effect_key,
            self.right_callee_effect_key,
        )

    def return_shapes_agree(self) -> bool:
        """Diagnostic only. Never a condition for the identity to exist."""

        return self.left_callee_return_shape_keys == self.right_callee_return_shape_keys

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "relational_callee_correspondence",
            "candidate_key": list(self.candidate_key),
            "left_callee_return_shape_keys": [list(k) for k in self.left_callee_return_shape_keys],
            "right_callee_return_shape_keys": [list(k) for k in self.right_callee_return_shape_keys],
            "left_callee_effect_key": list(self.left_callee_effect_key),
            "right_callee_effect_key": list(self.right_callee_effect_key),
            "return_shapes_agree": self.return_shapes_agree(),
        }


def build_relational_callee_correspondence(
    candidate: Optional[InternalCallCorrespondenceCandidateId],
    left_fact: Any,
    right_fact: Any,
) -> Tuple[Optional[RelationalCalleeCorrespondenceId], Tuple[str, ...]]:
    """Bind the candidate to a callee-correspondence obligation, or fail closed.

    Consumes callee return / effect facts — that is the *later* stage and is
    allowed here; the candidate itself never saw them.  Every leg must be
    present and unambiguous **on each side**; cross-side agreement is what the
    downstream solver stages prove, so it is not required here.
    """

    if candidate is None or left_fact is None or right_fact is None:
        return None, (CALLSITE_CANDIDATE_MISSING,)

    blockers: List[str] = []
    sides = (left_fact, right_fact)

    if any(
        tuple(getattr(fact, "callee_return_summary_statuses", ()) or ()) != ("complete",)
        for fact in sides
    ):
        blockers.append(CALLEE_RETURN_SUMMARY_UNPROVEN)
    if any(
        tuple(getattr(fact, "callee_effect_summary_statuses", ()) or ()) != ("complete",)
        for fact in sides
    ):
        blockers.append(CALLEE_EFFECT_SUMMARY_UNPROVEN)

    return_shapes = []
    for fact in sides:
        shapes = tuple(
            tuple(key) for key in (getattr(fact, "callee_return_shape_keys", ()) or ())
        )
        if not shapes:
            blockers.append(CALLEE_RETURN_SHAPE_RELATION_MISSING)
        return_shapes.append(shapes)

    memory_counts = []
    for fact in sides:
        count = _single(getattr(fact, "callee_memory_effect_counts", ()))
        if count is None:
            blockers.append(CALLEE_MEMORY_EFFECT_RELATION_MISSING)
        memory_counts.append(count)

    profiles = []
    for fact in sides:
        profile = _single(getattr(fact, "callee_control_profile_keys", ()))
        if profile is None:
            blockers.append(CALLEE_CONTROL_PROFILE_RELATION_MISSING)
        profiles.append(tuple(profile) if profile is not None else ())

    if blockers:
        return None, tuple(dict.fromkeys(blockers))

    return (
        RelationalCalleeCorrespondenceId(
            candidate_key=candidate.stable_key(),
            left_callee_return_shape_keys=return_shapes[0],
            right_callee_return_shape_keys=return_shapes[1],
            left_callee_effect_key=("callee_effect", memory_counts[0], profiles[0]),
            right_callee_effect_key=("callee_effect", memory_counts[1], profiles[1]),
        ),
        (),
    )


def relational_argument_key(
    left_fact: Any,
    right_fact: Any,
) -> Optional[Tuple[Any, ...]]:
    """Cross-binary argument relation shared by two corresponding call sites.

    ``None`` when the two sides do not agree on arity or on the cross-binary
    argument shapes, or when no argument shape was extracted at all.  It states
    *which slots correspond*, never that the argument values are equal.

    ABI slot identities are recorded but not required to agree: a side that went
    through ABI recovery and a side that did not are still candidate
    counterparts, and forcing agreement would gate on where the evidence came
    from rather than on what it says.
    """

    left_args = tuple(getattr(left_fact, "argument_keys", ()) or ())
    right_args = tuple(getattr(right_fact, "argument_keys", ()) or ())
    if len(left_args) != len(right_args):
        return None
    left_shapes = tuple(getattr(left_fact, "argument_shape_keys", ()) or ())
    right_shapes = tuple(getattr(right_fact, "argument_shape_keys", ()) or ())
    if left_shapes != right_shapes:
        return None
    if left_args and not left_shapes:
        return None
    return (
        "relational_argument",
        len(left_args),
        left_shapes,
        tuple(getattr(left_fact, "abi_argument_slot_keys", ()) or ()),
        tuple(getattr(right_fact, "abi_argument_slot_keys", ()) or ()),
    )


@dataclass(frozen=True)
class InternalCallsiteCorrespondence:
    """A confirmed internal callsite correspondence.

    成立には三点すべてが要る。どれか一つでも欠ければ correspondence は成立しない。
    """

    candidate: InternalCallCorrespondenceCandidateId
    callee_correspondence: RelationalCalleeCorrespondenceId
    argument_relation_key: Tuple[Any, ...]

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "internal_callsite_correspondence",
            self.candidate.stable_key(),
            self.callee_correspondence.stable_key(),
            self.argument_relation_key,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "internal_callsite_correspondence",
            "candidate": self.candidate.to_dict(),
            "callee_correspondence": self.callee_correspondence.to_dict(),
            "argument_relation_key": list(self.argument_relation_key),
        }


def confirm_internal_callsite_correspondence(
    candidate: Optional[InternalCallCorrespondenceCandidateId],
    left_fact: Any,
    right_fact: Any,
) -> Tuple[Optional[InternalCallsiteCorrespondence], Tuple[str, ...]]:
    """candidate + callee correspondence + relational argument key を突き合わせる。

    ``RelationalCalleeCorrespondenceId`` が得られなければ correspondence は
    成立しない（``None`` と blocker を返す）。
    """

    if candidate is None:
        return None, (CALLSITE_CANDIDATE_MISSING,)

    callee_correspondence, callee_blockers = build_relational_callee_correspondence(
        candidate, left_fact, right_fact
    )
    blockers: List[str] = list(callee_blockers)
    if callee_correspondence is None:
        blockers.append(CALLSITE_CALLEE_CORRESPONDENCE_MISSING)

    argument_key = relational_argument_key(left_fact, right_fact)
    if argument_key is None:
        blockers.append(CALLSITE_ARGUMENT_RELATION_MISSING)

    if callee_correspondence is None or argument_key is None:
        return None, tuple(dict.fromkeys(blockers))

    return (
        InternalCallsiteCorrespondence(
            candidate=candidate,
            callee_correspondence=callee_correspondence,
            argument_relation_key=argument_key,
        ),
        (),
    )
