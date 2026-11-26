# -*- coding: utf-8 -*-
"""Concrete replay of the symbolic analysis' witnesses as conditional evidence (#18, C2).

When the unconditional decision of a pair is UNKNOWN although the solver found
witnesses (satisfying assignments of "the two return values differ"), this
module runs both binaries on each witness's inputs (``concrete.replay``) and
returns a **proof artifact**: the facts of every replay and, when one replay
established a difference, the conditional proof kind
``CONDITIONAL_CONCRETE_COUNTEREXAMPLE`` with the premises it rests on.  Issuing
a receipt and the conditional verdict is the authority layer's job
(``authority.decision.conditional_lane``); this module imports no authority.

What the evidence is.  A difference established by two runs does not depend on
the symbolic analysis: the witness is only a choice of input, and the runs, not
the formula, show the difference.  It depends instead on:

* ``CONCRETE_CALLING_CONVENTION`` (one per side): the function is called as the
  ABI model says, its recovered parameter storage are its inputs and its
  recovered return location is its result;
* ``CONCRETE_PCODE_SEMANTICS``: the P-code of the processor specification is
  what the machine computes for the instructions the runs executed (the
  executor and the specification are named in the premise).

Everything else a run could depend on is refused by the concrete layer (an
undefined read, writable program data, an address's placement, a hazard of the
integer-UB or floating-point monitors, a pointer-typed return).  A witness
whose replay establishes nothing is evidence of nothing, and in particular not
of equivalence.

Sources.  Witnesses are the canonical SAT witnesses on the pair's solver rows
(``smt.witness``); a formula variable is named ``<parameter><suffix>`` with the
suffix of its side (``proof.formula.params``) and is found in a witness by that
name, its storage by the analysis' parameter record.  Nothing else of the
formula is read.

Facts, not analyses (Issue #325).  This module never receives an analysis
object.  What it reads of each side's analysis -- the parameter records, the
return storage descriptor and whether the return is a pointer -- arrives as
typed fact handles (``ConcreteSideFacts``, ``core.fact_reliance.FactHandle``)
built by one adapter (``checker.concrete_replay.concrete_side_facts``), so the
facts the evidence relies on are exactly the handles' closure
(`subject_reliance`).
"""

from __future__ import annotations

import hashlib
import json
import time
from dataclasses import dataclass, field, replace
from typing import Any, Callable, Iterable, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.concrete.observation import ReturnStorage
from scripts.function_tracer_pcode.concrete.replay import (
    PlanRefusal,
    ReplayPlan,
    ReplaySide,
    WitnessReplay,
    WitnessStatus,
    plan_replay,
    replay_witnesses,
)
from scripts.function_tracer_pcode.concrete.storage import StorageLocation
from scripts.function_tracer_pcode.concrete.witness import FormulaInput
from scripts.function_tracer_pcode.core.fact_reliance import (
    FactHandle,
    FactKind,
    ReliesOn,
)
from scripts.function_tracer_pcode.core.parameter_domain import parameter_descriptor_bits
from scripts.function_tracer_pcode.smt.interface import SolverStatus
from scripts.function_tracer_pcode.proof.assumptions import (
    AssumptionKind,
    AssumptionPremise,
    normalize_assumption_premises,
)

CONCRETE_PROOF_ADAPTER_VERSION = "concrete-counterexample-proof-v1"

#: authority 側 ``ConditionalDecisiveProofKind`` と同じ名前（import はしない）。
CONDITIONAL_CONCRETE_COUNTEREXAMPLE = "CONDITIONAL_CONCRETE_COUNTEREXAMPLE"

#: suffix of each side's formula variables (``proof.formula.params.collect_param_info``)
SIDE_SUFFIXES = ("_1", "_2")

# Why the replay was not decisive (diagnostics; never a verdict).
CONCRETE_NO_WITNESS = "concrete_replay_no_witness"
CONCRETE_EXECUTOR_UNAVAILABLE = "concrete_replay_executor_unavailable"
CONCRETE_SIDE_UNAVAILABLE = "concrete_replay_side_unavailable"
CONCRETE_PLAN_REFUSED = "concrete_replay_plan_refused"
CONCRETE_NOT_CONFIRMED = "concrete_replay_not_confirmed"
CONCRETE_BUDGET_EXHAUSTED = "concrete_replay_budget_exhausted"
#: the pair has no analysis deadline: the replay runs only inside one
CONCRETE_NO_DEADLINE = "concrete_replay_no_analysis_deadline"

#: Distinct witnesses replayed per pair at most.
MAX_WITNESSES = 16


def _digest(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":"), default=repr).encode("utf-8")
    ).hexdigest()


# ----------------------------------------------------------------- inputs

def solver_witnesses(result: Any) -> Tuple[Mapping[str, object], ...]:
    """The SAT witnesses on the result's solver rows, distinct, in row order."""
    rows = getattr(getattr(result, "solver_results", None), "results", None) or ()
    witnesses: List[Mapping[str, object]] = []
    for row in rows:
        model = getattr(row, "model", None)
        if getattr(row, "status", None) is not SolverStatus.SAT or not isinstance(model, Mapping) or not model:
            continue
        if any(dict(model) == dict(seen) for seen in witnesses):
            continue
        witnesses.append(dict(model))
    return tuple(witnesses)


@dataclass(frozen=True)
class ConcreteSideFacts:
    """What the concrete proof reads of one side's analysis, as fact handles (Issue #325).

    * ``parameters``: ``PARAMETER_STORAGE`` -- the parameter records (name,
      storage, size, ...) in the analysis' order;
    * ``return_location``: ``RETURN_LOCATION`` -- the return storage descriptor
      (``None`` when the analysis has none);
    * ``return_value_class``: ``RETURN_VALUE_CLASS`` -- ``{"is_pointer": bool}``.
    """

    parameters: FactHandle
    return_location: FactHandle
    return_value_class: FactHandle

    def __post_init__(self) -> None:
        for name, kind in (
            ("parameters", FactKind.PARAMETER_STORAGE),
            ("return_location", FactKind.RETURN_LOCATION),
            ("return_value_class", FactKind.RETURN_VALUE_CLASS),
        ):
            handle = getattr(self, name)
            if type(handle) is not FactHandle or handle.ref.kind is not kind:
                raise TypeError(f"concrete side facts carry a {kind.value} FactHandle as {name}")

    def handles(self) -> Tuple[FactHandle, ...]:
        return (self.parameters, self.return_location, self.return_value_class)


def formula_inputs(
    parameters: FactHandle,
    suffix: str,
    locate: Callable[[str, int, int], Optional[StorageLocation]],
) -> Tuple[FormulaInput, ...]:
    """The formula's input variables of one side, with the storage of their parameters.

    A parameter's storage is located from its exact varnode (address space,
    offset, size) by ``locate`` -- the executor's language -- never from the
    position of a named register that contains it; the width the recovered
    type gives the value is kept as the location's size (a reading).
    """
    if type(parameters) is not FactHandle or parameters.ref.kind is not FactKind.PARAMETER_STORAGE:
        raise TypeError("formula inputs are read from a PARAMETER_STORAGE FactHandle")
    inputs = []
    for parameter in parameters.value or ():
        name = parameter.get("name")
        storage = parameter.get("storage")
        size = int(parameter.get("size") or 0)
        location = None
        if name and isinstance(storage, Mapping) and storage.get("is_register"):
            piece = int(storage.get("size") or 0)
            if storage.get("register_name") and storage.get("register_name") == storage.get("base_register_name"):
                # The record names the base register itself: a type hypothesis
                # narrowed the type, not the storage, so the value is the whole
                # register (``concrete.storage.StorageLocation.names_whole_base_register``).
                piece = int(storage.get("base_register_size") or 0)
            try:
                location = locate(str(storage.get("space_name")), int(storage.get("offset")), piece)
            except (TypeError, ValueError):
                location = None
        if location is None:
            location = StorageLocation(False, None, None, 0, 0, size)
        elif size:
            location = replace(location, size_bytes=size)
        inputs.append(FormulaInput(f"{name}{suffix}", int(parameter_descriptor_bits(parameter)), location))
    return tuple(inputs)


def return_storage(
    return_location: FactHandle,
    return_value_class: FactHandle,
    locate: Callable[[str, int, int], Optional[StorageLocation]],
) -> Optional[ReturnStorage]:
    """The recovered return location of one side, or ``None`` when it is not known.

    ``locate(space, offset, size)`` names the register piece of a storage
    member (the executor's language does).
    """
    if type(return_location) is not FactHandle or return_location.ref.kind is not FactKind.RETURN_LOCATION:
        raise TypeError("the return storage is read from a RETURN_LOCATION FactHandle")
    if (
        type(return_value_class) is not FactHandle
        or return_value_class.ref.kind is not FactKind.RETURN_VALUE_CLASS
    ):
        raise TypeError("the return class is read from a RETURN_VALUE_CLASS FactHandle")
    descriptor = return_location.value or {}
    if descriptor.get("status") != "PRESENT" or not descriptor.get("value"):
        return None
    _schema, members = descriptor["value"]
    locations = []
    for member in members:
        _tag, space, offset, size = member
        location = locate(str(space), int(offset), int(size))
        if location is None:
            location = StorageLocation(False, None, None, 0, 0, int(size))
        locations.append(location)
    is_pointer = bool((return_value_class.value or {}).get("is_pointer"))
    return ReturnStorage(False, tuple(locations), is_pointer)


def subject_reliance(subjects: Optional[Sequence[Any]]) -> ReliesOn:
    """The facts a concrete artifact of ``subjects`` relied on (the handles' closure).

    A side that was refused (or no subjects at all) supplies no handle, so the
    reliance is every fact.
    """
    handles: List[FactHandle] = []
    for subject in subjects or ():
        if not isinstance(subject, ConcreteSubject):
            return ReliesOn.unknown_provenance(reason="a concrete side supplied no fact handles")
        handles.extend(subject.side_facts.handles())
    return ReliesOn.closure_of(handles)


# ---------------------------------------------------------------- premises

def concrete_premises(plan: ReplayPlan, programs: Sequence[Mapping[str, Any]]) -> Tuple[AssumptionPremise, ...]:
    premises = []
    for side, (item, location, facts) in enumerate(zip(plan.sides, plan.observation.locations, programs)):
        premises.append(AssumptionPremise(
            kind=AssumptionKind.CONCRETE_CALLING_CONVENTION,
            subject=f"function{side + 1}",
            payload={
                "abi_id": item.abi.abi_id.value,
                "entry_address": item.entry_address,
                "program_sha256": str(facts.get("sha256", "")),
                "argument_registers": [
                    item.abi.argument_register(argument.slots[side]) or ""
                    for argument in plan.correspondence.arguments
                ],
                "return_register": location.register,
                "return_class": location.arg_class.value,
                "return_width_bytes": location.width_bytes,
            },
        ))
    premises.append(AssumptionPremise(
        kind=AssumptionKind.CONCRETE_PCODE_SEMANTICS,
        subject="executor",
        payload={
            "executor": str(programs[0].get("executor", "")),
            "ghidra": str(programs[0].get("ghidra", "")),
            "languages": [str(facts.get("language_id", "")) for facts in programs],
            "compiler_specs": [str(facts.get("compiler_spec_id", "")) for facts in programs],
        },
    ))
    return normalize_assumption_premises(premises)


# ---------------------------------------------------------------- artifact

_CONCRETE_ARTIFACT_FACTORY_TOKEN = object()


@dataclass(frozen=True, init=False)
class ConcreteCounterexampleArtifact:
    """The concrete replay of one pair's witnesses (a proof artifact, not authority).

    Every field the authority layer reads is bound into ``artifact_digest``;
    ``validate`` rebuilds it.  ``replays`` are the records of the witnesses
    replayed (``concrete.replay.WitnessReplay.to_json``), ``confirmed`` the
    index of the one that established a difference.  ``proof_kind`` is
    ``None`` unless one did.
    """

    proof_kind: Optional[str]
    assumption_set: Tuple[AssumptionPremise, ...]
    plan: str
    witness_count: int
    replays: Tuple[Mapping[str, Any], ...]
    confirmed: Optional[int]
    programs: Tuple[Mapping[str, Any], ...]
    non_decisive_reasons: Tuple[str, ...]
    artifact_digest: str
    diagnostics: Mapping[str, Any] = field(default_factory=dict, compare=False, repr=False)

    def __init__(self, *, _factory_token: object = None, diagnostics: Optional[Mapping[str, Any]] = None,
                 **fields: Any) -> None:
        if _factory_token is not _CONCRETE_ARTIFACT_FACTORY_TOKEN:
            raise ValueError("concrete proof artifacts are issued only by run_concrete_counterexample_proof")
        for name in ("proof_kind", "plan", "witness_count", "confirmed", "artifact_digest"):
            object.__setattr__(self, name, fields[name])
        object.__setattr__(self, "assumption_set", tuple(fields["assumption_set"]))
        object.__setattr__(self, "replays", tuple(fields["replays"]))
        object.__setattr__(self, "programs", tuple(fields["programs"]))
        object.__setattr__(self, "non_decisive_reasons", tuple(fields["non_decisive_reasons"]))
        object.__setattr__(self, "diagnostics", dict(diagnostics or {}))

    @property
    def decisive(self) -> bool:
        return self.proof_kind is not None

    def confirmed_replay(self) -> Optional[Mapping[str, Any]]:
        return None if self.confirmed is None else self.replays[self.confirmed]

    def artifact_payload(self) -> Mapping[str, Any]:
        return {
            "adapter": CONCRETE_PROOF_ADAPTER_VERSION,
            "proof_kind": self.proof_kind,
            "assumption_set": [premise.premise_key() for premise in self.assumption_set],
            "plan": self.plan,
            "witness_count": self.witness_count,
            "replays": list(self.replays),
            "confirmed": self.confirmed,
            "programs": list(self.programs),
            "non_decisive_reasons": list(self.non_decisive_reasons),
        }

    def validate(self) -> None:
        if self.proof_kind not in (None, CONDITIONAL_CONCRETE_COUNTEREXAMPLE):
            raise ValueError(f"unknown concrete proof kind: {self.proof_kind}")
        for premise in self.assumption_set:
            if type(premise) is not AssumptionPremise:
                raise TypeError("concrete proof artifacts carry AssumptionPremise only")
        if _digest(self.artifact_payload()) != self.artifact_digest:
            raise ValueError("concrete proof artifact digest mismatch")
        if self.decisive:
            if not self.assumption_set or self.non_decisive_reasons:
                raise ValueError("a decisive concrete proof carries its premises and no refusal")
            if self.confirmed is None or not 0 <= self.confirmed < len(self.replays):
                raise ValueError("a decisive concrete proof names its confirmed replay")
            if self.replays[self.confirmed].get("status") != WitnessStatus.CONFIRMED.value:
                raise ValueError("the confirmed replay of a concrete proof is not a confirmation")
        elif self.confirmed is not None:
            raise ValueError("a non-decisive concrete proof names no confirmed replay")

    def validates(self) -> bool:
        try:
            self.validate()
        except (TypeError, ValueError):
            return False
        return True

    def to_json(self) -> Mapping[str, Any]:
        """The record written to the result: the exact digest preimage and its
        digest (``verify_concrete_record`` recomputes it; the conditional receipt
        binds the digest), plus the premises in readable form."""
        return {
            "artifact_payload": json.loads(json.dumps(self.artifact_payload(), default=repr)),
            "artifact_digest": self.artifact_digest,
            "premises": [
                {"kind": p.kind.value, "subject": p.subject, "payload": {k: v for k, v in p.payload}}
                for p in self.assumption_set
            ],
        }

    @classmethod
    def _create(cls, *, diagnostics: Optional[Mapping[str, Any]] = None, **fields: Any) -> "ConcreteCounterexampleArtifact":
        fields.setdefault("proof_kind", None)
        fields.setdefault("assumption_set", ())
        fields.setdefault("plan", "")
        fields.setdefault("witness_count", 0)
        fields.setdefault("replays", ())
        fields.setdefault("confirmed", None)
        fields.setdefault("programs", ())
        fields.setdefault("non_decisive_reasons", ())
        draft = cls(_factory_token=_CONCRETE_ARTIFACT_FACTORY_TOKEN, artifact_digest="", **fields)
        artifact = cls(
            _factory_token=_CONCRETE_ARTIFACT_FACTORY_TOKEN,
            artifact_digest=_digest(draft.artifact_payload()),
            diagnostics=diagnostics,
            **fields,
        )
        artifact.validate()
        return artifact


def verify_concrete_record(record: Mapping[str, Any]) -> bool:
    """A written record's digest is the digest of its payload (no authority needed)."""
    payload = record.get("artifact_payload")
    return isinstance(payload, Mapping) and _digest(payload) == record.get("artifact_digest")


# ----------------------------------------------------------------- running

@dataclass(frozen=True)
class ConcreteSubject:
    """What the proof needs of one side's binary, opened by the caller.

    ``executor`` runs functions of the side's program (``ConcreteExecutor``);
    ``abi`` and ``entry_address`` are the executor's ABI model for the
    function and its entry; ``locate`` names a register storage piece;
    ``facts`` identify the program and the executor (sha256, language,
    compiler specification, executor and Ghidra versions).
    """

    executor: Any
    abi: Any
    entry_address: int
    locate: Callable[[str, int, int], Optional[StorageLocation]]
    facts: Mapping[str, Any]
    #: what the proof reads of this side's analysis, as fact handles (Issue #325)
    side_facts: ConcreteSideFacts

    def __post_init__(self) -> None:
        if type(self.side_facts) is not ConcreteSideFacts:
            raise TypeError("a concrete subject carries its ConcreteSideFacts")


def run_concrete_counterexample_proof(
    witnesses: Iterable[Mapping[str, object]],
    subjects: Optional[Tuple[Any, Any]],
    *,
    budget_seconds: float,
    step_limit: int,
    clock: Callable[[], float] = time.monotonic,
) -> ConcreteCounterexampleArtifact:
    """Replay ``witnesses`` on both sides within ``budget_seconds`` (no witness
    starts after it, and every run's time limit is what is left of it).

    ``subjects`` holds, per side, a ``ConcreteSubject`` or the reason the side
    was refused (a string, recorded in the artifact's ``plan``)."""
    witnesses = tuple(witnesses)[:MAX_WITNESSES]
    if not witnesses:
        return ConcreteCounterexampleArtifact._create(non_decisive_reasons=(CONCRETE_NO_WITNESS,))
    if subjects is None:
        return ConcreteCounterexampleArtifact._create(
            witness_count=len(witnesses), non_decisive_reasons=(CONCRETE_EXECUTOR_UNAVAILABLE,)
        )
    refused = [
        f"side{side}:{subject if isinstance(subject, str) else 'UNAVAILABLE'}"
        for side, subject in enumerate(subjects) if not isinstance(subject, ConcreteSubject)
    ]
    if refused:
        return ConcreteCounterexampleArtifact._create(
            plan="SIDE_REFUSED:" + ";".join(refused),
            witness_count=len(witnesses), non_decisive_reasons=(CONCRETE_SIDE_UNAVAILABLE,)
        )
    programs = tuple(dict(subject.facts) for subject in subjects)
    sides = []
    for subject, suffix in zip(subjects, SIDE_SUFFIXES):
        facts = subject.side_facts
        storage = return_storage(facts.return_location, facts.return_value_class, subject.locate)
        if storage is None:
            storage = ReturnStorage(False, ())
        sides.append(ReplaySide(
            subject.abi, subject.entry_address,
            formula_inputs(facts.parameters, suffix, subject.locate), storage,
        ))
    plan = plan_replay(sides[0], sides[1], step_limit)
    if isinstance(plan, PlanRefusal):
        return ConcreteCounterexampleArtifact._create(
            plan=plan.describe(), witness_count=len(witnesses), programs=programs,
            non_decisive_reasons=(CONCRETE_PLAN_REFUSED,),
        )
    started = clock()
    spent = {"exhausted": False}

    def may_continue() -> bool:
        if clock() - started >= budget_seconds:
            spent["exhausted"] = True
            return False
        return True

    replays: Tuple[WitnessReplay, ...] = replay_witnesses(
        plan, witnesses, (subjects[0].executor, subjects[1].executor),
        may_continue=may_continue, clock=clock,
        # every run gets what is left: the replay never outlasts its budget
        time_left=lambda: budget_seconds - (clock() - started),
    )
    records = tuple(replay.to_json() for replay in replays)
    confirmed = next(
        (index for index, replay in enumerate(replays) if replay.status is WitnessStatus.CONFIRMED), None
    )
    diagnostics = {"seconds": round(clock() - started, 4), "replayed": len(replays)}
    if confirmed is None:
        reasons = [CONCRETE_NOT_CONFIRMED]
        if spent["exhausted"]:
            reasons.append(CONCRETE_BUDGET_EXHAUSTED)
        return ConcreteCounterexampleArtifact._create(
            plan="OK", witness_count=len(witnesses), replays=records, programs=programs,
            non_decisive_reasons=tuple(reasons), diagnostics=diagnostics,
        )
    return ConcreteCounterexampleArtifact._create(
        proof_kind=CONDITIONAL_CONCRETE_COUNTEREXAMPLE,
        assumption_set=concrete_premises(plan, programs),
        plan="OK", witness_count=len(witnesses), replays=records, confirmed=confirmed,
        programs=programs, diagnostics=diagnostics,
    )
