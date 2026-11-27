"""Obligation scope: which active cause rows block which decisive evidence (Issue #325, E1).

The decision authorities (``decision.finalize_decision`` and
``conditional.finalize_conditional_decision``) used to decide "does an active
row block this side" from ``decision_effect`` alone, each with its own copy of
the rule.  This module is now the **only** owner of that rule, and it scopes
it to what the evidence relies on:

    row r blocks evidence E  <=>  decision_effect(r) applies to E's side
                                  and guards(r) intersects relies_on(E)

* ``guards(r)`` is the static declaration of the facts r's obligation
  guarantees (`SealedGuardRegistry`).  A reason without a declaration guards
  **every** fact.
* ``relies_on(E)`` is the closure of the facts E depended on
  (``core.fact_reliance.ReliesOn``).  SMT evidence relies on every fact by
  rule; evidence whose provenance is not fully recorded relies on every fact.
* A row whose target cannot be mapped onto the evidence's fact targets
  intersects.

Every undecidable case falls on the "blocks" side (fail-closed).  With no
declaration and no narrow reliance -- the state of every production path in
E1 -- the evaluation reproduces the old ``decision_effect`` rule exactly.

What stays with each finalizer is its own adoption rule (receipt validation,
conflicts, TIMEOUT / ERROR, the conditional lane's join and assumption set).
This module only answers, per side, whether some decisive evidence is left
unblocked, and records the answer row by row (`ObligationScopeRecord`).

Discharge (``REQUIREMENT_COMPLETED``: the obligation was met) and
non-applicability (``DISJOINT``: the evidence does not rely on what the
obligation guards) stay different things: this module never completes an
obligation, it only says an evidence did not rely on it.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from functools import lru_cache
from importlib import import_module
from typing import Any, FrozenSet, Iterable, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.core.fact_reliance import (
    CONCRETE_FACT_KINDS,
    FactKind,
    FactTarget,
    RelianceBasis,
    ReliesOn,
)

OBLIGATION_SCOPE_SCHEMA = "obligation-scope-v1"


class DecisionSide(str, Enum):
    """The side of the decision an evidence supports."""

    EQUIVALENCE = "EQUIVALENCE"
    DISEQUIVALENCE = "DISEQUIVALENCE"


#: ``decision_effect`` values that make a row apply to a side (the rule the two
#: finalizers used to spell out separately).
BLOCKING_EFFECTS: Mapping[DecisionSide, FrozenSet[str]] = {
    DecisionSide.EQUIVALENCE: frozenset({"blocks_equivalence", "blocks_decision"}),
    DecisionSide.DISEQUIVALENCE: frozenset({"blocks_disequivalence", "blocks_decision"}),
}


class ProofFamily(str, Enum):
    """The proof method an evidence comes from."""

    SMT_EQ_CLOSURE = "SMT_EQ_CLOSURE"
    SMT_COUNTEREXAMPLE = "SMT_COUNTEREXAMPLE"
    CONCRETE_COUNTEREXAMPLE = "CONCRETE_COUNTEREXAMPLE"


#: The families whose evidence relies on every fact by rule (the SMT proofs
#: read the whole static analysis; narrowing them is not part of this scope).
ALL_FACT_FAMILIES: FrozenSet[ProofFamily] = frozenset({
    ProofFamily.SMT_EQ_CLOSURE,
    ProofFamily.SMT_COUNTEREXAMPLE,
})

FAMILY_SIDE: Mapping[ProofFamily, DecisionSide] = {
    ProofFamily.SMT_EQ_CLOSURE: DecisionSide.EQUIVALENCE,
    ProofFamily.SMT_COUNTEREXAMPLE: DecisionSide.DISEQUIVALENCE,
    ProofFamily.CONCRETE_COUNTEREXAMPLE: DecisionSide.DISEQUIVALENCE,
}

#: Decisive proof kind (its ``.value``) -> family.  Keyed by value so this
#: module needs neither finalizer; a unit test pins that every member of
#: ``DecisiveProofKind`` and ``ConditionalDecisiveProofKind`` is mapped.
FAMILY_BY_PROOF_KIND: Mapping[str, ProofFamily] = {
    "EQ_CLOSURE": ProofFamily.SMT_EQ_CLOSURE,
    "SAFE_COUNTEREXAMPLE": ProofFamily.SMT_COUNTEREXAMPLE,
    "CONDITIONAL_EQ_CLOSURE": ProofFamily.SMT_EQ_CLOSURE,
    "CONDITIONAL_SAFE_COUNTEREXAMPLE": ProofFamily.SMT_COUNTEREXAMPLE,
    "CONDITIONAL_CONCRETE_COUNTEREXAMPLE": ProofFamily.CONCRETE_COUNTEREXAMPLE,
}

#: At most one evidence per proof kind (a finalizer that sees a repeated kind is
#: malformed and decides ERROR; the record keeps the first of each kind).
MAX_SCOPE_EVIDENCE = len(FAMILY_BY_PROOF_KIND)


class Lane(str, Enum):
    UNCONDITIONAL = "UNCONDITIONAL"
    CONDITIONAL = "CONDITIONAL"


class ScopeBasis(str, Enum):
    """Why one row does or does not block one evidence."""

    #: the row's decision_effect does not apply to the evidence's side (spares)
    EFFECT_NOT_APPLICABLE = "EFFECT_NOT_APPLICABLE"
    #: the evidence relies on every fact by its family's rule (blocks)
    RELIES_ON_ALL_FACTS = "RELIES_ON_ALL_FACTS"
    #: the evidence's reliance has an unrecorded provenance (blocks)
    RELIES_ON_UNKNOWN_PROVENANCE = "RELIES_ON_UNKNOWN_PROVENANCE"
    #: the row's reason declares no guards, so it guards every fact (blocks)
    GUARDS_UNDECLARED = "GUARDS_UNDECLARED"
    #: the row's target cannot be mapped onto fact targets (blocks)
    TARGET_UNMAPPED = "TARGET_UNMAPPED"
    #: guards and reliance share a fact on a common target (blocks)
    INTERSECTS = "INTERSECTS"
    #: guards and reliance share nothing (spares: non-applicability)
    DISJOINT = "DISJOINT"


_SPARING_BASES = frozenset({ScopeBasis.EFFECT_NOT_APPLICABLE, ScopeBasis.DISJOINT})

#: The longest vocabulary string a serialized record carries (schema, lane,
#: proof kind, family, side, reliance basis, scope basis): the output bound
#: (``checker.output_schema.obligation_scope_max_bytes``) reads this one value.
SCOPE_VOCABULARY_MAX_CHARS = max(
    len(value)
    for value in (
        OBLIGATION_SCOPE_SCHEMA,
        *FAMILY_BY_PROOF_KIND,
        *(item.value for item in ProofFamily),
        *(item.value for item in DecisionSide),
        *(item.value for item in Lane),
        *(item.value for item in ScopeBasis),
        *(item.value for item in RelianceBasis),
    )
)


# ---------------------------------------------------------------- guards


@dataclass(frozen=True)
class GuardDeclaration:
    """One reason's declared guards and where the declaration's evidence lives.

    ``basis`` names the tests that back the declaration (Issue #325 Must: the
    producer that guarantees the fact, the boundary test, a representative
    pair, the metamorphic test).
    """

    reason_id: str
    guards: FrozenSet[FactKind]
    basis: str

    def __post_init__(self) -> None:
        if type(self.reason_id) is not str or not self.reason_id:
            raise TypeError("a guard declaration names an exact reason id")
        if type(self.basis) is not str or not self.basis:
            raise TypeError("a guard declaration names the evidence it rests on")
        guards = frozenset(self.guards)
        if not guards or any(type(kind) is not FactKind for kind in guards):
            raise TypeError("a guard declaration lists one or more exact FactKind values")
        if not guards <= CONCRETE_FACT_KINDS:
            raise ValueError("guards name concrete fact kinds (UNKNOWN_PROVENANCE is not a fact)")
        object.__setattr__(self, "guards", guards)

    def to_json(self) -> Mapping[str, Any]:
        return {
            "reason_id": self.reason_id,
            "guards": sorted(kind.value for kind in self.guards),
            "basis": self.basis,
        }


_GUARD_REGISTRY_FACTORY_TOKEN = object()


@dataclass(frozen=True, init=False)
class SealedGuardRegistry:
    """reason id -> declared guards.  Undeclared reasons guard every fact."""

    _declarations: Mapping[str, GuardDeclaration]
    digest: str

    def __init__(self, declarations, digest, *, _token=None):
        if _token is not _GUARD_REGISTRY_FACTORY_TOKEN:
            raise ValueError("guard registries are built by SealedGuardRegistry.build")
        object.__setattr__(self, "_declarations", dict(declarations))
        object.__setattr__(self, "digest", digest)

    @classmethod
    def build(
        cls,
        declarations: Iterable[GuardDeclaration],
        *,
        known_reason_ids: Optional[FrozenSet[str]] = None,
    ) -> "SealedGuardRegistry":
        """Seal ``declarations``; each reason at most once and (when given) a known reason."""

        indexed: dict = {}
        for declaration in declarations:
            if type(declaration) is not GuardDeclaration:
                raise TypeError("a guard registry accepts exact GuardDeclaration values")
            if declaration.reason_id in indexed:
                raise ValueError(f"duplicate guard declaration: {declaration.reason_id}")
            if known_reason_ids is not None and declaration.reason_id not in known_reason_ids:
                raise ValueError(f"guard declaration for an unregistered reason: {declaration.reason_id}")
            indexed[declaration.reason_id] = declaration
        ordered = dict(sorted(indexed.items()))
        digest = authority_digest({
            "schema": OBLIGATION_SCOPE_SCHEMA,
            "declarations": [item.to_json() for item in ordered.values()],
        })
        return cls(ordered, digest, _token=_GUARD_REGISTRY_FACTORY_TOKEN)

    def guards_for(self, reason_id: str) -> Optional[FrozenSet[FactKind]]:
        """The declared guards, or ``None`` when the reason declares none (= every fact)."""

        declaration = self._declarations.get(reason_id)
        return None if declaration is None else declaration.guards

    def declared_reason_ids(self) -> Tuple[str, ...]:
        return tuple(self._declarations)


#: The production declarations.  Issue #325 E1 adds **none**: every reason
#: guards every fact.  E4 adds one domain per commit, each with the evidence
#: the Issue's Must lists.
PRODUCTION_GUARD_DECLARATIONS: Tuple[GuardDeclaration, ...] = ()

#: The sealed reason registries whose ids a declaration may name
#: (``module:attribute``).  A unit test pins this list against every
#: module-level ``SealedReasonRegistry.build`` in the authority layer.
PRODUCTION_REASON_REGISTRIES: Tuple[str, ...] = (
    "scripts.function_tracer_pcode.authority.domains.abi_width_readonly:ABI_WIDTH_READONLY_REASON_REGISTRY",
    "scripts.function_tracer_pcode.authority.domains.analysis_limitation:ANALYSIS_LIMITATION_REASON_REGISTRY",
    "scripts.function_tracer_pcode.authority.domains.call_effect:CALL_EFFECT_REASON_REGISTRY",
    "scripts.function_tracer_pcode.authority.domains.cross_side_identity:CROSS_SIDE_IDENTITY_REASON_REGISTRY",
    "scripts.function_tracer_pcode.authority.domains.loop_recurrence:LOOP_REASON_REGISTRY",
    "scripts.function_tracer_pcode.authority.domains.return_coverage:RETURN_COVERAGE_REASON_REGISTRY",
    "scripts.function_tracer_pcode.authority.domains.return_outcome:RETURN_OUTCOME_REASON_REGISTRY",
    "scripts.function_tracer_pcode.authority.domains.sat_safety:SAT_SAFETY_REASON_REGISTRY",
    "scripts.function_tracer_pcode.authority.lifecycle.production_signals:COMPARISON_CLOSURE_REASON_REGISTRY",
    "scripts.function_tracer_pcode.authority.process.operational_extraction:OPERATIONAL_REASON_REGISTRY",
    "scripts.function_tracer_pcode.authority.process.supervisor:PROCESS_COMPLETION_REASON_REGISTRY",
    "scripts.function_tracer_pcode.authority.process.supervisor:PROCESS_DURABLE_REASON_REGISTRY",
)


def production_reason_ids() -> FrozenSet[str]:
    """Every reason id of the production sealed registries (imported lazily: no cycle)."""

    ids = set()
    for spec in PRODUCTION_REASON_REGISTRIES:
        module_name, attribute = spec.split(":")
        registry = getattr(import_module(module_name), attribute)
        ids.update(definition.reason_id for definition in registry.snapshot())
    return frozenset(ids)


@lru_cache(maxsize=1)
def production_guard_registry() -> SealedGuardRegistry:
    """The production guard registry (sealed once per process)."""

    known = production_reason_ids() if PRODUCTION_GUARD_DECLARATIONS else None
    return SealedGuardRegistry.build(PRODUCTION_GUARD_DECLARATIONS, known_reason_ids=known)


# ---------------------------------------------------------------- evidence


@dataclass(frozen=True)
class ScopedEvidence:
    """One decisive evidence as the scope evaluation sees it."""

    evidence_id: str
    proof_kind: str
    family: ProofFamily
    relies_on: ReliesOn

    def __post_init__(self) -> None:
        if type(self.evidence_id) is not str or not self.evidence_id:
            raise TypeError("a scoped evidence names its receipt")
        if type(self.relies_on) is not ReliesOn:
            raise TypeError("a scoped evidence carries an exact ReliesOn")
        if self.family in ALL_FACT_FAMILIES and self.relies_on.basis is not RelianceBasis.ALL_FACTS:
            raise ValueError(f"{self.family.value} evidence relies on every fact")

    @property
    def side(self) -> DecisionSide:
        return FAMILY_SIDE[self.family]

    def to_json(self) -> Mapping[str, Any]:
        return {
            "evidence_id": self.evidence_id,
            "proof_kind": self.proof_kind,
            "family": self.family.value,
            "side": self.side.value,
            "relies_on_basis": self.relies_on.basis.value,
            "relies_on_digest": self.relies_on.digest,
        }


def scoped_evidence(
    proof_kind: str, evidence_id: str, *, relies_on: Optional[ReliesOn] = None,
) -> ScopedEvidence:
    """The evidence of one decisive receipt.

    SMT families rely on every fact whatever is passed.  A family that may be
    narrowed relies on what its producer supplied, or on every fact (unknown
    provenance) when nothing was supplied.
    """

    family = FAMILY_BY_PROOF_KIND[proof_kind]
    if family in ALL_FACT_FAMILIES:
        if relies_on is not None and relies_on.basis is not RelianceBasis.ALL_FACTS:
            raise ValueError(f"{family.value} evidence cannot carry a narrowed reliance")
        reliance = ReliesOn.all_facts()
    else:
        reliance = relies_on if relies_on is not None else ReliesOn.unknown_provenance(
            reason="the producer supplied no reliance",
        )
    return ScopedEvidence(evidence_id, proof_kind, family, reliance)


# ---------------------------------------------------------------- evaluation


def row_fact_targets(row: Any) -> Optional[FrozenSet[FactTarget]]:
    """The fact targets one active row is about, or ``None`` when they cannot be mapped.

    Active rows carry a reason, a domain and a target kind, but no fact target
    yet; E1 maps none of them, so every row intersects (fail-closed).  The
    mapping is added together with the first declaration that needs it.
    """

    return None


def _judge(row: Any, evidence: ScopedEvidence, registry: SealedGuardRegistry) -> ScopeBasis:
    if row.decision_effect not in BLOCKING_EFFECTS[evidence.side]:
        return ScopeBasis.EFFECT_NOT_APPLICABLE
    reliance = evidence.relies_on
    if reliance.basis is RelianceBasis.ALL_FACTS:
        return ScopeBasis.RELIES_ON_ALL_FACTS
    if reliance.basis is RelianceBasis.UNKNOWN_PROVENANCE:
        return ScopeBasis.RELIES_ON_UNKNOWN_PROVENANCE
    guards = registry.guards_for(row.reason_id)
    if guards is None:
        return ScopeBasis.GUARDS_UNDECLARED
    targets = row_fact_targets(row)
    if targets is None:
        return ScopeBasis.TARGET_UNMAPPED
    if any(ref.kind in guards and ref.target in targets for ref in reliance.refs):
        return ScopeBasis.INTERSECTS
    return ScopeBasis.DISJOINT


@dataclass(frozen=True)
class CauseScope:
    """The verdicts of one cause against each recorded evidence (in evidence order).

    A verdict depends only on the cause (its reason, decision_effect and
    target), never on the occurrence, so the record keeps one entry per cause;
    every active row with that ``cause_id`` has these verdicts.
    """

    cause_id: str
    guards_declared: bool
    bases: Tuple[ScopeBasis, ...]

    def blocks(self, index: int) -> bool:
        return self.bases[index] not in _SPARING_BASES

    def to_json(self) -> Mapping[str, Any]:
        return {
            "cause_id": self.cause_id,
            "guards_declared": self.guards_declared,
            "bases": [basis.value for basis in self.bases],
        }


@dataclass(frozen=True)
class ObligationScopeRecord:
    """The cause-by-cause answer of one scope evaluation (what blocked what, and why).

    ``rows_digest`` is the digest of the evaluated active rows' keys
    ``(occurrence_id, cause_id)`` in projection order, so a reader can check
    the record against the relation rows it explains.  A basis is "blocks"
    unless it is ``EFFECT_NOT_APPLICABLE`` or ``DISJOINT``.

    ``bound_to_receipt`` is true when some evidence relies on a narrowed
    closure: only then can the evaluation differ from the plain
    ``decision_effect`` rule, and the finalizer then puts ``record_digest``
    into the receipt's authority input.  A record whose evidence all relies on
    every fact is fully determined by the projection and the receipts, and the
    receipt keeps its pre-#325 digest.
    """

    lane: Lane
    result_occurrence_id: str
    lifecycle_projection_digest: str
    guard_registry_digest: str
    evidence: Tuple[ScopedEvidence, ...]
    row_count: int
    rows_digest: str
    causes: Tuple[CauseScope, ...]

    @property
    def bound_to_receipt(self) -> bool:
        return any(not item.relies_on.universal for item in self.evidence)

    def evidence_unblocked(self, index: int) -> bool:
        return not any(cause.blocks(index) for cause in self.causes)

    def side_decisive(self, side: DecisionSide) -> bool:
        """Some decisive evidence of ``side`` is left unblocked by every active row."""

        return any(
            item.side is side and self.evidence_unblocked(index)
            for index, item in enumerate(self.evidence)
        )

    def _body(self) -> Mapping[str, Any]:
        return {
            "schema": OBLIGATION_SCOPE_SCHEMA,
            "lane": self.lane.value,
            "result_occurrence_id": self.result_occurrence_id,
            "lifecycle_projection_digest": self.lifecycle_projection_digest,
            "guard_registry_digest": self.guard_registry_digest,
            "bound_to_receipt": self.bound_to_receipt,
            "evidence": [
                {**item.to_json(), "unblocked": self.evidence_unblocked(index)}
                for index, item in enumerate(self.evidence)
            ],
            "row_count": self.row_count,
            "rows_digest": self.rows_digest,
            "causes": [cause.to_json() for cause in self.causes],
        }

    @property
    def record_digest(self) -> str:
        return authority_digest(self._body())

    def to_json(self) -> Mapping[str, Any]:
        return {**self._body(), "record_digest": self.record_digest}


def rows_digest(rows: Sequence[Any]) -> str:
    """The digest of active rows' keys ``(occurrence_id, cause_id)`` in the given order."""

    return authority_digest([[row.occurrence_id, row.cause_id] for row in rows])


def evaluate_obligation_scope(
    *,
    lane: Lane,
    result_occurrence_id: str,
    lifecycle_projection_digest: str,
    rows: Sequence[Any],
    evidence: Iterable[ScopedEvidence],
    registry: Optional[SealedGuardRegistry] = None,
) -> ObligationScopeRecord:
    """Evaluate every active row against every decisive evidence (the one blocking rule).

    A row that applies to a side and shares a fact with the evidence's reliance
    blocks it; ``ScopeBasis`` says why for each (cause, evidence).
    """

    registry = production_guard_registry() if registry is None else registry
    if type(registry) is not SealedGuardRegistry:
        raise TypeError("scope evaluation needs a SealedGuardRegistry")
    unique: list = []
    seen_kinds = set()
    for item in evidence:
        if type(item) is not ScopedEvidence:
            raise TypeError("scope evaluation reads ScopedEvidence only")
        if item.proof_kind in seen_kinds:
            continue
        seen_kinds.add(item.proof_kind)
        unique.append(item)
    scoped = tuple(unique)
    rows = tuple(rows)
    by_cause: dict = {}
    for row in rows:
        scope = CauseScope(
            cause_id=row.cause_id,
            guards_declared=registry.guards_for(row.reason_id) is not None,
            bases=tuple(_judge(row, item, registry) for item in scoped),
        )
        seen = by_cause.setdefault(row.cause_id, scope)
        if seen != scope:
            # a verdict must be a property of the cause; two rows of one cause
            # judged differently means a mapping read something else (fail loudly)
            raise ValueError(f"rows of cause {row.cause_id} were judged differently")
    return ObligationScopeRecord(
        lane=Lane(lane),
        result_occurrence_id=result_occurrence_id,
        lifecycle_projection_digest=lifecycle_projection_digest,
        guard_registry_digest=registry.digest,
        evidence=scoped,
        row_count=len(rows),
        rows_digest=rows_digest(rows),
        causes=tuple(by_cause[key] for key in sorted(by_cause)),
    )


__all__ = [
    "ALL_FACT_FAMILIES",
    "BLOCKING_EFFECTS",
    "DecisionSide",
    "FAMILY_BY_PROOF_KIND",
    "GuardDeclaration",
    "Lane",
    "MAX_SCOPE_EVIDENCE",
    "OBLIGATION_SCOPE_SCHEMA",
    "ObligationScopeRecord",
    "PRODUCTION_GUARD_DECLARATIONS",
    "PRODUCTION_REASON_REGISTRIES",
    "ProofFamily",
    "CauseScope",
    "SCOPE_VOCABULARY_MAX_CHARS",
    "ScopeBasis",
    "ScopedEvidence",
    "SealedGuardRegistry",
    "evaluate_obligation_scope",
    "production_guard_registry",
    "production_reason_ids",
    "row_fact_targets",
    "rows_digest",
    "scoped_evidence",
]
