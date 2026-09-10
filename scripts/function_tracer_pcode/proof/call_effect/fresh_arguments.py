"""Fresh call-argument correspondence, value coupling and proof irrelevance.

Issue #20 PR-D の soundness の中心。三つを型で分ける。

1. **identity correspondence** — ``FreshArgumentIdentityCorrespondence``
   「左の ABI スロット n は右の ABI スロット n の対応候補である」だけを表す。
   ordinal / storage class / 幅が一致していても、それは値の一致ではない。

2. **value coupling** — ``FreshArgumentCoupling``
   左右の fresh を同一シンボルとして扱ってよいのは、
   ``RelationalEqualityProof`` が与えられ、しかもそれが discharge 済みの
   場合だけ。証明が無ければ ``coupled_symbol_key()`` は ``None`` を返し、
   二つの fresh は独立のままでなければならない。

3. **proof irrelevance** — ``FreshArgumentIrrelevanceProof``
   「その fresh 値は当該 decisive predicate に影響しない」ことの証明。
   これは **coupling ではない**。証明があっても左右の fresh は別シンボルの
   ままで、その proof に限って blocker を discharge するだけである。

``FreshCallArgumentRef.stable_key()`` は ``binary_id`` を含むので、そもそも
左右の fresh が同一シンボルになることは構造的に起こらない。本モジュールは
「意図的に結合してよいのはどういう証拠があるときか」を明示する層である。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core import FreshCallArgumentRef


#: fresh 値が復元されていないこと自体の blocker。
FRESH_ARGUMENT_VALUE_UNOBSERVED = "call_argument_fresh_value_unobserved"


@dataclass(frozen=True)
class FreshArgumentIdentityCorrespondence:
    """A candidate pairing of one left and one right fresh argument slot.

    Validity means "these two slots are counterparts", never "these two slots
    hold the same value".
    """

    left: FreshCallArgumentRef
    right: FreshCallArgumentRef

    def is_valid(self) -> bool:
        if not isinstance(self.left, FreshCallArgumentRef):
            return False
        if not isinstance(self.right, FreshCallArgumentRef):
            return False
        if self.left.identity_correspondence_key() != self.right.identity_correspondence_key():
            return False
        # 同一シンボルを「対応」と呼ばない。左右は別の側から来ていなければならない。
        return self.left.stable_key() != self.right.stable_key()

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "fresh_argument_identity_correspondence",
            self.left.stable_key(),
            self.right.stable_key(),
            self.left.identity_correspondence_key(),
        )


@dataclass(frozen=True)
class RelationalEqualityProof:
    """Evidence that two side-specific values are equal under the compared premise.

    ``discharged`` が False の間は「主張はあるが証明されていない」状態であり、
    coupling には使えない。
    """

    proof_id: str
    left_key: Tuple[Any, ...]
    right_key: Tuple[Any, ...]
    premise_digest: Optional[str] = None
    obligation_id: Optional[str] = None
    discharged: bool = False

    def covers(self, correspondence: FreshArgumentIdentityCorrespondence) -> bool:
        if not correspondence.is_valid():
            return False
        return (
            tuple(self.left_key) == tuple(correspondence.left.stable_key())
            and tuple(self.right_key) == tuple(correspondence.right.stable_key())
        )

    def is_usable(self) -> bool:
        return bool(self.discharged) and bool(self.proof_id) and bool(self.premise_digest)


@dataclass(frozen=True)
class FreshArgumentCoupling:
    """A *proved* identification of two fresh arguments as one symbolic value."""

    correspondence: FreshArgumentIdentityCorrespondence
    proof: RelationalEqualityProof

    def coupled_symbol_key(self) -> Optional[Tuple[Any, ...]]:
        """The shared symbol key, or ``None`` when the coupling is not proved.

        Callers must treat ``None`` as "keep the two side-specific symbols".
        """

        if not self.correspondence.is_valid():
            return None
        if not self.proof.is_usable() or not self.proof.covers(self.correspondence):
            return None
        return (
            "coupled_fresh_call_argument",
            self.correspondence.left.identity_correspondence_key(),
            self.proof.proof_id,
            self.proof.premise_digest,
        )


def couple_fresh_arguments(
    left: Optional[FreshCallArgumentRef],
    right: Optional[FreshCallArgumentRef],
    proof: Optional[RelationalEqualityProof] = None,
) -> Optional[FreshArgumentCoupling]:
    """Couple two fresh arguments **only** under a discharged relational proof.

    Matching ABI ordinal / storage / width is deliberately *not* enough: that is
    identity correspondence, and ``log(x)`` against ``log(x + 1)`` satisfies it
    while the values differ.  Without a usable proof this returns ``None`` and
    the two sides keep their own symbols.
    """

    if left is None or right is None or proof is None:
        return None
    correspondence = FreshArgumentIdentityCorrespondence(left=left, right=right)
    if not correspondence.is_valid():
        return None
    coupling = FreshArgumentCoupling(correspondence=correspondence, proof=proof)
    return coupling if coupling.coupled_symbol_key() is not None else None


@dataclass(frozen=True)
class FreshArgumentIrrelevanceProof:
    """The fresh value provably does not affect one specific decisive predicate.

    This discharges a blocker for *that* proof only.  It never merges symbols:
    "irrelevant" and "equal" are different claims and are kept apart here on
    purpose.
    """

    proof_id: str
    fresh_key: Tuple[Any, ...]
    decisive_predicate_key: Tuple[Any, ...]
    obligation_id: Optional[str] = None
    discharged: bool = False

    def is_usable(self) -> bool:
        return bool(self.discharged) and bool(self.proof_id) and bool(self.decisive_predicate_key)

    def covers(
        self,
        fresh_ref: FreshCallArgumentRef,
        decisive_predicate_key: Tuple[Any, ...],
    ) -> bool:
        if not self.is_usable():
            return False
        return (
            tuple(self.fresh_key) == tuple(fresh_ref.stable_key())
            and tuple(self.decisive_predicate_key) == tuple(decisive_predicate_key or ())
        )


def fresh_arguments_are_independent(
    left: Optional[FreshCallArgumentRef],
    right: Optional[FreshCallArgumentRef],
    coupling: Optional[FreshArgumentCoupling] = None,
) -> bool:
    """True when the two fresh values must stay separate symbols.

    Independence is the default; only a coupling with a usable proof removes it.
    """

    if left is None or right is None:
        return True
    if coupling is None:
        return True
    return coupling.coupled_symbol_key() is None


def discharge_fresh_argument_blockers(
    fresh_refs: Sequence[FreshCallArgumentRef],
    decisive_predicate_key: Tuple[Any, ...],
    irrelevance_proofs: Iterable[FreshArgumentIrrelevanceProof] = (),
) -> Tuple[bool, Tuple[Tuple[Any, ...], ...]]:
    """Can the fresh-value blocker be dropped for this one decisive predicate?

    Returns ``(discharged, undischarged_fresh_keys)``.  Every fresh value of the
    call site must be covered by its own irrelevance proof; a partial cover
    leaves the blocker in place.  The symbols stay independent either way.
    """

    proofs = tuple(item for item in irrelevance_proofs or () if item is not None)
    undischarged: list = []
    for fresh_ref in fresh_refs or ():
        if not any(proof.covers(fresh_ref, decisive_predicate_key) for proof in proofs):
            undischarged.append(tuple(fresh_ref.stable_key()))
    if not fresh_refs:
        return True, ()
    return (not undischarged), tuple(undischarged)


def fresh_argument_blockers(
    fresh_refs: Sequence[FreshCallArgumentRef],
    *,
    side: str,
    decisive_predicate_key: Tuple[Any, ...] = (),
    irrelevance_proofs: Iterable[FreshArgumentIrrelevanceProof] = (),
) -> Tuple[str, ...]:
    """Blocker codes contributed by unobserved fresh arguments on one side."""

    if not fresh_refs:
        return ()
    discharged, _undischarged = discharge_fresh_argument_blockers(
        fresh_refs,
        decisive_predicate_key,
        irrelevance_proofs,
    )
    if discharged:
        return ()
    return (f"{side}_{FRESH_ARGUMENT_VALUE_UNOBSERVED}",)


def fresh_argument_registry(
    refs_by_side: Mapping[str, Sequence[FreshCallArgumentRef]],
) -> Dict[str, Tuple[Tuple[Any, ...], ...]]:
    """Diagnostic projection: the fresh symbols each side introduced."""

    return {
        str(side): tuple(tuple(ref.stable_key()) for ref in (refs or ()))
        for side, refs in (refs_by_side or {}).items()
    }


#: 左右 fresh 引数の状態。既定は independent（結合していない）。
FRESH_ARGUMENT_STATUS_NONE = "none"
FRESH_ARGUMENT_STATUS_INDEPENDENT = "independent"
FRESH_ARGUMENT_STATUS_SIDE_IDENTITY_VIOLATED = "side_identity_violated"


def fresh_argument_correspondence_status(
    left_keys: Sequence[Tuple[Any, ...]],
    right_keys: Sequence[Tuple[Any, ...]],
) -> str:
    """How a pair's fresh arguments relate.

    ``independent`` is the only healthy outcome without a relational equality
    proof.  ``side_identity_violated`` means a left and a right fresh argument
    ended up sharing a symbol identity, which would silently assert equality;
    it is reported so the invariant is observable rather than assumed.
    """

    left = tuple(tuple(key) for key in (left_keys or ()))
    right = tuple(tuple(key) for key in (right_keys or ()))
    if not left and not right:
        return FRESH_ARGUMENT_STATUS_NONE
    if set(left) & set(right):
        return FRESH_ARGUMENT_STATUS_SIDE_IDENTITY_VIOLATED
    return FRESH_ARGUMENT_STATUS_INDEPENDENT
