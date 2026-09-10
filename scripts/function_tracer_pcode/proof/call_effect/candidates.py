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

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple


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
# candidate → callee correspondence proof → RelationalCalleeCorrespondenceId
#             → relational argument key → internal callsite correspondence
# ---------------------------------------------------------------------------
#
# 権限境界（正本 v4 §4.3.4）。所有者を分ける。
#
#   candidate 形成          InternalCallCorrespondenceCandidateId
#       semantic shape の相互一意のみ。callee return / effect を読まない。
#   callee correspondence   CalleeCorrespondenceProof（factory 発行の receipt）
#       **左右 callee が対応する**ことを関係的に証明する。
#   correspondence id       RelationalCalleeCorrespondenceId
#       proof digest に bind される。proof 無しでは発行できない。
#   callsite correspondence InternalCallsiteCorrespondence
#       candidate + correspondence id + relational argument key。
#
# **何を関係的な証明とするか**
#
# callee identity (`CallTargetRef.stable_key()`) は `program_id` を含むので左右で
# 一致しない（正本 G3）。したがって「左右の callee が同じ」ことは直接は言えない。
# 代わりに、この関数対の **候補集合全体が誘導する callee の対応**が
# 双方向に一意（bijection）であることを証明する。
#
#   左 callsite A ↔ 右 callsite A'、左 callsite B ↔ 右 callsite B' が候補で、
#   A と B が同じ左 callee を呼ぶなら、A' と B' も同じ右 callee を呼ばねばならない。
#   一つでも破れていれば callee の対応は曖昧であり、ID を発行しない。
#
# これは各 side の情報が「存在する」ことの確認ではなく、候補集合という関係の上で
# しか書けない制約であり、かつ callee の **意味的等価**は何も主張しない。等価性は
# 後段の `return_relation` / `memory_relation` が証明する（責務を先取りしない）。

CALLEE_CORRESPONDENCE_PROOF_KIND = "internal_callee_correspondence_bijection_v1"
CALLEE_CORRESPONDENCE_SCHEMA_VERSION = 1

#: candidate の binding 検証で拒否する理由。
CANDIDATE_SCHEMA_INVALID = "internal_callsite_candidate_schema_invalid"
CANDIDATE_OBLIGATION_MISMATCH = "internal_callsite_candidate_obligation_mismatch"
CANDIDATE_STALE = "internal_callsite_candidate_stale"

#: callee correspondence proof が成立しない理由（fail closed）。
CALLEE_TARGET_UNRESOLVED = "internal_callee_target_unresolved"
CALLEE_CORRESPONDENCE_AMBIGUOUS = "internal_callee_correspondence_ambiguous"
CALLEE_CORRESPONDENCE_PROOF_INVALID = "internal_callee_correspondence_proof_invalid"
CALLEE_CORRESPONDENCE_PROOF_STALE = "internal_callee_correspondence_proof_stale"
CALLEE_RETURN_SUMMARY_UNPROVEN = "internal_callee_return_summary_unproven"
CALLEE_RETURN_SHAPE_RELATION_MISSING = "internal_callee_return_shape_relation_missing"
CALLEE_EFFECT_SUMMARY_UNPROVEN = "internal_callee_effect_summary_unproven"
CALLEE_MEMORY_EFFECT_RELATION_MISSING = "internal_callee_memory_effect_relation_missing"
CALLEE_CONTROL_PROFILE_RELATION_MISSING = "internal_callee_control_profile_relation_missing"

#: callsite correspondence が成立しない理由（fail closed）。
CALLSITE_CANDIDATE_MISSING = "internal_callsite_candidate_missing"
CALLSITE_CALLEE_CORRESPONDENCE_MISSING = "internal_callsite_callee_correspondence_missing"
CALLSITE_ARGUMENT_RELATION_MISSING = "internal_callsite_argument_relation_missing"

#: 候補 identity の永続化キーの形（schema 検証に使う）。
_CANDIDATE_KEY_KIND = "internal_call_correspondence_candidate"
_CANDIDATE_KEY_LENGTH = 5


def _single(values: Any) -> Optional[Any]:
    """The one element of a one-element sequence, else ``None`` (fail closed)."""

    items = tuple(values or ())
    return items[0] if len(items) == 1 else None


def _resolved_callee_key(fact: Any) -> Optional[Tuple[Any, ...]]:
    """The single resolved callee identity of a call site, else ``None``."""

    if getattr(fact, "target_resolution_status", None) != "resolved":
        return None
    target = _single(getattr(fact, "target_candidates", ()))
    if target is None:
        return None
    return tuple(target) if isinstance(target, (tuple, list)) else (target,)


def _callee_wellformedness(fact: Any) -> Tuple[Optional[Tuple[Any, ...]], Tuple[str, ...]]:
    """Per-side inputs the later callee proof needs, or the reasons they are missing.

    存在確認そのものは *証明ではない*。ここで集めるのは、関係の証明を書くための
    入力が各 side で一意に定まっていることの確認であり、correspondence の成立は
    後段の bijection 検査が担う。
    """

    reasons: List[str] = []
    if tuple(getattr(fact, "callee_return_summary_statuses", ()) or ()) != ("complete",):
        reasons.append(CALLEE_RETURN_SUMMARY_UNPROVEN)
    if tuple(getattr(fact, "callee_effect_summary_statuses", ()) or ()) != ("complete",):
        reasons.append(CALLEE_EFFECT_SUMMARY_UNPROVEN)
    shapes = tuple(tuple(k) for k in (getattr(fact, "callee_return_shape_keys", ()) or ()))
    if not shapes:
        reasons.append(CALLEE_RETURN_SHAPE_RELATION_MISSING)
    memory = _single(getattr(fact, "callee_memory_effect_counts", ()))
    if memory is None:
        reasons.append(CALLEE_MEMORY_EFFECT_RELATION_MISSING)
    profile = _single(getattr(fact, "callee_control_profile_keys", ()))
    if profile is None:
        reasons.append(CALLEE_CONTROL_PROFILE_RELATION_MISSING)
    if reasons:
        return None, tuple(dict.fromkeys(reasons))
    return ("callee_inputs", shapes, memory, tuple(profile)), ()


@dataclass(frozen=True)
class CalleeCorrespondencePair:
    """One proven callee correspondence inside a ``CalleeCorrespondenceProof``."""

    candidate_key: Tuple[Any, ...]
    left_fact_id: str
    right_fact_id: str
    left_callee_key: Tuple[Any, ...]
    right_callee_key: Tuple[Any, ...]
    left_inputs_key: Tuple[Any, ...]
    right_inputs_key: Tuple[Any, ...]

    def payload(self) -> Tuple[Any, ...]:
        return (
            self.candidate_key,
            self.left_fact_id,
            self.right_fact_id,
            self.left_callee_key,
            self.right_callee_key,
            self.left_inputs_key,
            self.right_inputs_key,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "candidate_key": list(self.candidate_key),
            "left_fact_id": self.left_fact_id,
            "right_fact_id": self.right_fact_id,
            "left_callee_key": list(self.left_callee_key),
            "right_callee_key": list(self.right_callee_key),
            "left_inputs_key": list(self.left_inputs_key),
            "right_inputs_key": list(self.right_inputs_key),
        }


@dataclass(frozen=True)
class CalleeCorrespondenceProof:
    """Factory-issued receipt for one function pair's induced callee bijection.

    ``proof_id`` は payload 全体の digest で、``verification_failure()`` が再計算して
    突き合わせる。差し替え・改竄された receipt は拒否される。
    """

    proof_id: str
    pairs: Tuple[CalleeCorrespondencePair, ...] = ()
    rejected: Tuple[Tuple[Tuple[Any, ...], str], ...] = ()
    proof_kind: str = CALLEE_CORRESPONDENCE_PROOF_KIND
    schema_version: int = CALLEE_CORRESPONDENCE_SCHEMA_VERSION

    def payload(self) -> Tuple[Any, ...]:
        return (
            self.proof_kind,
            int(self.schema_version),
            tuple(pair.payload() for pair in self.pairs),
            tuple((tuple(key), reason) for key, reason in self.rejected),
        )

    def verification_failure(self) -> Optional[str]:
        if self.proof_kind != CALLEE_CORRESPONDENCE_PROOF_KIND:
            return "proof_kind_mismatch"
        if int(self.schema_version) != CALLEE_CORRESPONDENCE_SCHEMA_VERSION:
            return "proof_schema_version_mismatch"
        if _proof_digest(self.payload()) != self.proof_id:
            return "proof_digest_mismatch"
        return None

    def pair_for(self, candidate_key: Tuple[Any, ...]) -> Optional[CalleeCorrespondencePair]:
        key = tuple(candidate_key or ())
        for pair in self.pairs:
            if pair.candidate_key == key:
                return pair
        return None

    def rejection_for(self, candidate_key: Tuple[Any, ...]) -> Tuple[str, ...]:
        key = tuple(candidate_key or ())
        return tuple(reason for rejected_key, reason in self.rejected if tuple(rejected_key) == key)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": self.proof_kind,
            "schema_version": int(self.schema_version),
            "proof_id": self.proof_id,
            "pairs": [pair.to_dict() for pair in self.pairs],
            "rejected": [[list(key), reason] for key, reason in self.rejected],
            "verification_status": (
                "verified" if self.verification_failure() is None else "invalid"
            ),
        }


def _proof_digest(value: Any) -> str:
    def jsonable(item: Any) -> Any:
        if item is None or isinstance(item, (bool, int, float, str)):
            return item
        if isinstance(item, (tuple, list)):
            return [jsonable(entry) for entry in item]
        if isinstance(item, dict):
            return {str(k): jsonable(v) for k, v in sorted(item.items(), key=lambda kv: str(kv[0]))}
        return str(item)

    payload = json.dumps(
        jsonable(value), sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def build_callee_correspondence_proof(
    candidates: Sequence[InternalCallCorrespondenceCandidateId],
    left_by_id: Mapping[str, Any],
    right_by_id: Mapping[str, Any],
) -> CalleeCorrespondenceProof:
    """Prove the callee correspondence induced by a function pair's candidate set.

    候補集合が誘導する callee の対応が双方向に一意であることを検査する。曖昧な
    ものは ``rejected`` に落ち、``RelationalCalleeCorrespondenceId`` を得られない。
    """

    resolved: List[Tuple[InternalCallCorrespondenceCandidateId, Tuple[Any, ...], Tuple[Any, ...], Tuple[Any, ...], Tuple[Any, ...]]] = []
    rejected: List[Tuple[Tuple[Any, ...], str]] = []

    for candidate in candidates or ():
        key = candidate.stable_key()
        left_fact = left_by_id.get(candidate.left_fact_id)
        right_fact = right_by_id.get(candidate.right_fact_id)
        if left_fact is None or right_fact is None:
            rejected.append((key, CALLSITE_CANDIDATE_MISSING))
            continue
        left_callee = _resolved_callee_key(left_fact)
        right_callee = _resolved_callee_key(right_fact)
        if left_callee is None or right_callee is None:
            rejected.append((key, CALLEE_TARGET_UNRESOLVED))
            continue
        left_inputs, left_reasons = _callee_wellformedness(left_fact)
        right_inputs, right_reasons = _callee_wellformedness(right_fact)
        if left_inputs is None or right_inputs is None:
            for reason in dict.fromkeys(tuple(left_reasons) + tuple(right_reasons)):
                rejected.append((key, reason))
            continue
        resolved.append((candidate, left_callee, right_callee, left_inputs, right_inputs))

    # 誘導される callee 対応が双方向に一意か。破れていればその callee に関わる
    # 候補をすべて落とす（どれが正しいか決める根拠が無いので推測しない）。
    left_to_right: Dict[Tuple[Any, ...], set] = {}
    right_to_left: Dict[Tuple[Any, ...], set] = {}
    for _candidate, left_callee, right_callee, _li, _ri in resolved:
        left_to_right.setdefault(left_callee, set()).add(right_callee)
        right_to_left.setdefault(right_callee, set()).add(left_callee)

    pairs: List[CalleeCorrespondencePair] = []
    for candidate, left_callee, right_callee, left_inputs, right_inputs in resolved:
        if len(left_to_right.get(left_callee, ())) != 1 or len(right_to_left.get(right_callee, ())) != 1:
            rejected.append((candidate.stable_key(), CALLEE_CORRESPONDENCE_AMBIGUOUS))
            continue
        pairs.append(
            CalleeCorrespondencePair(
                candidate_key=candidate.stable_key(),
                left_fact_id=candidate.left_fact_id,
                right_fact_id=candidate.right_fact_id,
                left_callee_key=left_callee,
                right_callee_key=right_callee,
                left_inputs_key=left_inputs,
                right_inputs_key=right_inputs,
            )
        )

    pairs_tuple = tuple(sorted(pairs, key=lambda item: (item.left_fact_id, item.right_fact_id)))
    rejected_tuple = tuple(sorted(set(rejected), key=lambda item: (str(item[0]), item[1])))
    proof = CalleeCorrespondenceProof(
        proof_id="",
        pairs=pairs_tuple,
        rejected=rejected_tuple,
    )
    return CalleeCorrespondenceProof(
        proof_id=_proof_digest(proof.payload()),
        pairs=pairs_tuple,
        rejected=rejected_tuple,
    )


@dataclass(frozen=True)
class RelationalCalleeCorrespondenceId:
    """Identity of a *proven* left-callee ↔ right-callee correspondence.

    ``proof_id`` に bind されており、``CalleeCorrespondenceProof`` を通さずには
    生成できない（``issue_relational_callee_correspondence`` が唯一の入口）。
    """

    proof_id: str
    candidate_key: Tuple[Any, ...]
    left_callee_key: Tuple[Any, ...]
    right_callee_key: Tuple[Any, ...]

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "relational_callee_correspondence",
            self.proof_id,
            self.candidate_key,
            self.left_callee_key,
            self.right_callee_key,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "relational_callee_correspondence",
            "proof_id": self.proof_id,
            "candidate_key": list(self.candidate_key),
            "left_callee_key": list(self.left_callee_key),
            "right_callee_key": list(self.right_callee_key),
        }


def issue_relational_callee_correspondence(
    proof: Optional[CalleeCorrespondenceProof],
    candidate: Optional[InternalCallCorrespondenceCandidateId],
) -> Tuple[Optional[RelationalCalleeCorrespondenceId], Tuple[str, ...]]:
    """Issue the correspondence id **only** from a verified proof."""

    if candidate is None:
        return None, (CALLSITE_CANDIDATE_MISSING,)
    if proof is None:
        return None, (CALLSITE_CALLEE_CORRESPONDENCE_MISSING,)
    if proof.verification_failure() is not None:
        return None, (CALLEE_CORRESPONDENCE_PROOF_INVALID,)
    key = candidate.stable_key()
    pair = proof.pair_for(key)
    if pair is None:
        reasons = proof.rejection_for(key) or (CALLSITE_CALLEE_CORRESPONDENCE_MISSING,)
        return None, tuple(dict.fromkeys(reasons + (CALLSITE_CALLEE_CORRESPONDENCE_MISSING,)))
    if pair.left_fact_id != candidate.left_fact_id or pair.right_fact_id != candidate.right_fact_id:
        return None, (CALLEE_CORRESPONDENCE_PROOF_STALE,)
    return (
        RelationalCalleeCorrespondenceId(
            proof_id=proof.proof_id,
            candidate_key=key,
            left_callee_key=pair.left_callee_key,
            right_callee_key=pair.right_callee_key,
        ),
        (),
    )


def verify_internal_candidate_binding(
    persisted_key: Any,
    obligation_left_fact_id: Optional[str],
    obligation_right_fact_id: Optional[str],
    left_fact: Any,
    right_fact: Any,
) -> Tuple[Optional[InternalCallCorrespondenceCandidateId], Tuple[str, ...]]:
    """Validate a persisted candidate key against the obligation and current facts.

    永続化されたキーを *信用しない*。schema、obligation との所属関係、そして
    現在の fact から再導出した候補との一致をすべて確認する。obligation の値で
    キーを作り直して辻褄を合わせることはしない（foreign / stale / tampered を
    そこで見逃すため）。
    """

    if not persisted_key:
        return None, (CALLSITE_CANDIDATE_MISSING,)
    key = tuple(persisted_key)
    if (
        len(key) != _CANDIDATE_KEY_LENGTH
        or key[0] != _CANDIDATE_KEY_KIND
        or not isinstance(key[1], str)
        or not isinstance(key[2], str)
    ):
        return None, (CANDIDATE_SCHEMA_INVALID,)
    if key[1] != str(obligation_left_fact_id or "") or key[2] != str(obligation_right_fact_id or ""):
        return None, (CANDIDATE_OBLIGATION_MISMATCH,)
    if left_fact is None or right_fact is None:
        return None, (CALLSITE_CANDIDATE_MISSING,)
    if str(getattr(left_fact, "fact_id", "")) != key[1] or str(getattr(right_fact, "fact_id", "")) != key[2]:
        return None, (CANDIDATE_OBLIGATION_MISMATCH,)

    rebuilt = build_internal_call_correspondence_candidates([left_fact], [right_fact])
    candidate = rebuilt.candidate_for(key[1])
    if candidate is None or candidate.stable_key() != key:
        return None, (CANDIDATE_STALE,)
    return candidate, ()


@dataclass(frozen=True)
class InternalCallsiteCorrespondence:
    """A confirmed internal callsite correspondence.

    成立には candidate / callee correspondence id / relational argument key の
    三点すべてが要る。どれか一つでも欠ければ correspondence は成立しない。
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


def confirm_internal_callsite_correspondence(
    candidate: Optional[InternalCallCorrespondenceCandidateId],
    proof: Optional[CalleeCorrespondenceProof],
    left_fact: Any,
    right_fact: Any,
) -> Tuple[Optional[InternalCallsiteCorrespondence], Tuple[str, ...]]:
    """candidate + proof 由来の correspondence id + relational argument key。

    ``RelationalCalleeCorrespondenceId`` が得られなければ correspondence は
    成立しない。
    """

    if candidate is None:
        return None, (CALLSITE_CANDIDATE_MISSING,)

    callee_correspondence, callee_blockers = issue_relational_callee_correspondence(
        proof, candidate
    )
    blockers: List[str] = list(callee_blockers)

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
