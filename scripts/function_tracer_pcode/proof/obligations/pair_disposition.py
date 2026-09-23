"""Validated, generation-bound authority for logical pair disposition."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
import hashlib
import hmac
import inspect
import marshal
import secrets
from threading import Lock
from typing import Any, ClassVar, Dict, Mapping, Optional, Tuple, Union

from scripts.function_tracer_pcode.proof.obligations.guard_overlap import GuardDisjointArtifact


_CLOSURE_ARTIFACT_AUTHORITY_KEY = secrets.token_bytes(32)


def _closure_artifact_seal(payload: Tuple[Any, ...]) -> str:
    return hmac.new(
        _CLOSURE_ARTIFACT_AUTHORITY_KEY,
        repr(payload).encode("utf-8"),
        hashlib.sha256,
    ).hexdigest()


class PairDisposition(str, Enum):
    UNSAT = "unsat"
    SAT = "sat"
    UNKNOWN = "unknown"
    ERROR = "error"
    SKIPPED = "skipped_after_terminal_decision"


class PairClosureKind(str, Enum):
    GUARD_QUERY = "guard_query"
    VALUE_QUERY = "value_query"
    STRUCTURAL_EQUALITY = "structural_equality"
    CACHE = "cache"
    RECOVERY = "recovery"
    RETURN_WIDTH = "return_width"
    AGGREGATE = "aggregate"


class LedgerLifecycle(str, Enum):
    OPEN = "open"
    SEALED = "sealed"
    SUPERSEDED = "superseded"


@dataclass(frozen=True)
class PairLedgerBinding:
    comparison_session_id: str
    branch_id: str
    prepared_surface_digest: str
    projection_id: str
    frame_generation: int
    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    graph_generation: int
    #: この ledger の closure の前提になった比較の authority（raw pair と最終
    #: InputCorrespondence の組の digest、Issue #167）。validator は現在の比較と値で照合する。
    comparison_authority_digest: str
    schema_version: str = "pair_disposition_ledger_v3"

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version, self.comparison_session_id, self.branch_id,
            self.prepared_surface_digest, self.projection_id, self.frame_generation,
            self.derived_view_id, self.premise_digest, self.graph_generation,
            self.comparison_authority_digest,
        )


class PairLedgerPromotionState(str, Enum):
    OPEN = "open"
    COMPOSED = "composed"
    ABORTED = "aborted"


@dataclass(frozen=True)
class SolverQueryExecutionReceipt:
    """Process-local authority for the exact query submitted to a solver."""

    formula_digest: str
    model_digest: str
    query_label: str
    proof_stage: str
    disposition: str
    solver_identity_digest: str
    timeout_budget: float
    execution_policy: str
    source_receipt: Optional["SolverQueryExecutionReceipt"]
    authority_digest: str
    schema_version: str = "solver_query_execution_receipt_v1"

    @classmethod
    def from_execution(
        cls,
        *,
        query: str,
        query_label: str,
        proof_stage: str,
        parallel_result: Any,
        solver_identity: Tuple[Any, ...],
        timeout_budget: float,
        use_hard_timeout: bool,
    ) -> "SolverQueryExecutionReceipt":
        if not isinstance(query, str) or not query.strip():
            raise ValueError("solver execution receipt requires a non-empty query")
        semantic = getattr(parallel_result, "is_equivalent", None)
        if type(semantic) is bool:
            disposition = "unsat" if semantic else "sat"
        else:
            disposition = "unknown"
        model = (
            parallel_result.get_counterexample()
            if disposition == "sat"
            else None
        )
        schema_version = "solver_query_execution_receipt_v1"
        formula_digest = hashlib.sha256(query.encode("utf-8")).hexdigest()
        model_digest = hashlib.sha256(repr(model).encode("utf-8")).hexdigest()
        solver_identity_digest = hashlib.sha256(
            repr(solver_identity).encode("utf-8")
        ).hexdigest()
        execution_policy = "hard_timeout" if use_hard_timeout else "normal_timeout"
        payload = (
            schema_version,
            formula_digest,
            model_digest,
            str(query_label),
            str(proof_stage),
            disposition,
            solver_identity_digest,
            float(timeout_budget),
            execution_policy,
            (),
        )
        return cls(
            formula_digest=formula_digest,
            model_digest=model_digest,
            query_label=str(query_label),
            proof_stage=str(proof_stage),
            disposition=disposition,
            solver_identity_digest=solver_identity_digest,
            timeout_budget=float(timeout_budget),
            execution_policy=execution_policy,
            source_receipt=None,
            authority_digest=_closure_artifact_seal(payload),
            schema_version=schema_version,
        )

    def _authority_payload(self) -> Tuple[Any, ...]:
        return (
            self.schema_version,
            self.formula_digest,
            self.model_digest,
            self.query_label,
            self.proof_stage,
            self.disposition,
            self.solver_identity_digest,
            float(self.timeout_budget),
            self.execution_policy,
            (
                self.source_receipt.stable_key()
                if self.source_receipt is not None
                else ()
            ),
        )

    def for_cache_reuse(
        self,
        *,
        query_label: str,
        proof_stage: str,
    ) -> "SolverQueryExecutionReceipt":
        if not self.validates_authority():
            raise ValueError("cache reuse requires valid source execution receipt")
        payload = (
            self.schema_version,
            self.formula_digest,
            self.model_digest,
            str(query_label),
            str(proof_stage),
            self.disposition,
            self.solver_identity_digest,
            float(self.timeout_budget),
            "cache_reuse",
            self.stable_key(),
        )
        return type(self)(
            formula_digest=self.formula_digest,
            model_digest=self.model_digest,
            query_label=str(query_label),
            proof_stage=str(proof_stage),
            disposition=self.disposition,
            solver_identity_digest=self.solver_identity_digest,
            timeout_budget=float(self.timeout_budget),
            execution_policy="cache_reuse",
            source_receipt=self,
            authority_digest=_closure_artifact_seal(payload),
            schema_version=self.schema_version,
        )

    def validates_authority(self) -> bool:
        return (
            self.schema_version == "solver_query_execution_receipt_v1"
            and len(self.formula_digest) == 64
            and len(self.model_digest) == 64
            and bool(self.query_label)
            and bool(self.proof_stage)
            and self.disposition in {"sat", "unsat", "unknown"}
            and len(self.solver_identity_digest) == 64
            and self.timeout_budget >= 0.0
            and self.execution_policy
            in {"normal_timeout", "hard_timeout", "cache_reuse"}
            and (
                self.execution_policy != "cache_reuse"
                or (
                    type(self.source_receipt)
                    is SolverQueryExecutionReceipt
                    and self.source_receipt.validates_authority()
                    and self.source_receipt.formula_digest
                    == self.formula_digest
                    and self.source_receipt.model_digest == self.model_digest
                    and self.source_receipt.disposition == self.disposition
                    and self.source_receipt.solver_identity_digest
                    == self.solver_identity_digest
                    and float(self.source_receipt.timeout_budget)
                    == float(self.timeout_budget)
                )
            )
            and (
                self.execution_policy == "cache_reuse"
                or self.source_receipt is None
            )
            and hmac.compare_digest(
                self.authority_digest,
                _closure_artifact_seal(self._authority_payload()),
            )
        )

    def validates_execution(
        self,
        *,
        query: str,
        expected_disposition: str,
        expected_query_label: str,
        expected_model: Any = None,
        verify_model: bool = True,
    ) -> bool:
        return (
            self.validates_authority()
            and isinstance(query, str)
            and bool(query.strip())
            and self.formula_digest
            == hashlib.sha256(query.encode("utf-8")).hexdigest()
            and self.disposition == expected_disposition
            and self.query_label == str(expected_query_label)
            and (
                not verify_model
                or self.model_digest
                == hashlib.sha256(
                    repr(expected_model).encode("utf-8")
                ).hexdigest()
            )
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return self._authority_payload() + (self.authority_digest,)


@dataclass(frozen=True)
class StructuralEqualityReceipt:
    """Typed authority for equality proved without an UNSAT value query."""

    query_label: str
    proof_kind: str
    evidence_digest: str
    supporting_solver_receipts: Tuple[SolverQueryExecutionReceipt, ...]
    authority_digest: str
    schema_version: str = "structural_equality_receipt_v1"

    def _authority_payload(self) -> Tuple[Any, ...]:
        return (
            self.schema_version,
            self.query_label,
            self.proof_kind,
            self.evidence_digest,
            tuple(
                receipt.stable_key()
                for receipt in self.supporting_solver_receipts
            ),
        )

    def validates_authority(self) -> bool:
        return (
            self.schema_version == "structural_equality_receipt_v1"
            and bool(self.query_label)
            and self.proof_kind
            in {"rewrite-structural", "void-return", "loop-template"}
            and len(self.evidence_digest) == 64
            and all(
                type(receipt) is SolverQueryExecutionReceipt
                and receipt.validates_authority()
                and receipt.disposition == "unsat"
                for receipt in self.supporting_solver_receipts
            )
            and hmac.compare_digest(
                self.authority_digest,
                _closure_artifact_seal(self._authority_payload()),
            )
        )

    def validates(self, *, expected_query_label: str) -> bool:
        return (
            self.validates_authority()
            and self.query_label == str(expected_query_label)
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return self._authority_payload() + (self.authority_digest,)


_STRUCTURAL_EQUALITY_PRODUCER_IDENTITIES = {
    "rewrite-structural": (
        "function_tracer_pcode.proof.strategies."
        "pairwise_solver_proven_rewrite",
        "try_solver_proven_rewrite_equivalence",
    ),
    "void-return": (
        "function_tracer_pcode.proof.strategies."
        "pairwise_query_executor",
        "solve_query_after_guard",
    ),
    "loop-template": (
        "function_tracer_pcode.proof.strategies.loop_template",
        "LoopTemplatePairwiseStrategy._try_normalization_equivalence",
    ),
}
_TRUSTED_STRUCTURAL_EQUALITY_PRODUCER_CODES: Dict[str, Any] = {}


def register_structural_equality_producer(
    proof_kind: str,
    producer: Any,
) -> None:
    """Pin the exact production code object allowed to issue one proof kind."""

    expected = _STRUCTURAL_EQUALITY_PRODUCER_IDENTITIES.get(str(proof_kind))
    if expected is None:
        raise RuntimeError("structural equality producer kind is not trusted")
    frame = inspect.currentframe()
    caller = frame.f_back if frame is not None else None
    try:
        producer_module = str(getattr(producer, "__module__", "") or "")
        producer_qualname = str(getattr(producer, "__qualname__", "") or "")
        if (
            caller is None
            or caller.f_code.co_name != "<module>"
            or not producer_module.endswith(expected[0])
            or producer_qualname != expected[1]
            or caller.f_globals.get("__name__") != producer_module
        ):
            raise RuntimeError("structural equality producer registrar is not trusted")
    finally:
        del caller
        del frame
    code = getattr(producer, "__code__", None)
    if code is None:
        raise RuntimeError("structural equality producer code is unavailable")
    existing = _TRUSTED_STRUCTURAL_EQUALITY_PRODUCER_CODES.get(str(proof_kind))
    if existing is not None and marshal.dumps(existing) != marshal.dumps(code):
        raise RuntimeError("structural equality producer replacement rejected")
    _TRUSTED_STRUCTURAL_EQUALITY_PRODUCER_CODES[str(proof_kind)] = code


def issue_structural_equality_receipt(
    *,
    query_label: str,
    proof_kind: str,
    evidence: Any,
    supporting_solver_receipts: Tuple[SolverQueryExecutionReceipt, ...] = (),
) -> StructuralEqualityReceipt:
    """Seal structural EQ only from the registered proof implementation."""

    current = inspect.currentframe()
    caller = current.f_back if current is not None else None
    try:
        if (
            caller is None
            or _TRUSTED_STRUCTURAL_EQUALITY_PRODUCER_CODES.get(str(proof_kind))
            is not caller.f_code
        ):
            raise RuntimeError("structural equality receipt issuer is not trusted")
    finally:
        del caller
        del current
    if not isinstance(evidence, tuple) or not evidence or evidence[0] != proof_kind:
        raise ValueError("structural equality evidence kind mismatch")
    receipts = tuple(supporting_solver_receipts)
    if any(
        type(receipt) is not SolverQueryExecutionReceipt
        or not receipt.validates_authority()
        or receipt.disposition != "unsat"
        for receipt in receipts
    ):
        raise ValueError("structural equality has invalid solver support")
    schema_version = "structural_equality_receipt_v1"
    evidence_digest = hashlib.sha256(repr(evidence).encode("utf-8")).hexdigest()
    payload = (
        schema_version,
        str(query_label),
        str(proof_kind),
        evidence_digest,
        tuple(receipt.stable_key() for receipt in receipts),
    )
    return StructuralEqualityReceipt(
        query_label=str(query_label),
        proof_kind=str(proof_kind),
        evidence_digest=evidence_digest,
        supporting_solver_receipts=receipts,
        authority_digest=_closure_artifact_seal(payload),
        schema_version=schema_version,
    )


@dataclass(frozen=True)
class PairLedgerSuccessorIntent:
    """Exact predecessor-derived identity, before pair surface enumeration."""

    comparison_session_id: str
    branch_id: str
    frame_generation: int
    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    graph_generation: int
    #: 後継も前任と同じ比較（同じ raw pair と最終 InputCorrespondence）の ledger（Issue #167）。
    comparison_authority_digest: str
    predecessor_projection_id: str
    projection_refresh_required: bool = False
    state: PairLedgerPromotionState = PairLedgerPromotionState.OPEN
    schema_version: str = "pair_ledger_successor_intent_v3"

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version,
            self.comparison_session_id,
            self.branch_id,
            self.frame_generation,
            self.derived_view_id,
            self.premise_digest,
            self.graph_generation,
            self.comparison_authority_digest,
            self.predecessor_projection_id,
            self.projection_refresh_required,
            self.state.value,
        )

    def accepts_binding(self, binding: PairLedgerBinding) -> bool:
        return (
            self.state == PairLedgerPromotionState.OPEN
            and binding.comparison_session_id == self.comparison_session_id
            and binding.branch_id == self.branch_id
            and binding.frame_generation == self.frame_generation
            and binding.derived_view_id == self.derived_view_id
            and binding.premise_digest == self.premise_digest
            and binding.graph_generation == self.graph_generation
            and binding.comparison_authority_digest == self.comparison_authority_digest
            and (
                not self.projection_refresh_required
                or binding.projection_id != self.predecessor_projection_id
            )
        )


@dataclass(frozen=True)
class PairLedgerSuccessorPlan:
    """Fully composed successor authority; contains no wildcard fields."""

    binding_key: Tuple[Any, ...]
    expected_pairs: int
    predecessor_projection_id: str
    state: PairLedgerPromotionState = PairLedgerPromotionState.COMPOSED
    schema_version: str = "pair_ledger_successor_plan_v2"

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version, self.binding_key, int(self.expected_pairs),
            self.predecessor_projection_id, self.state.value,
        )

    def accepts(self, binding: PairLedgerBinding, expected_pairs: int) -> bool:
        return (
            self.state == PairLedgerPromotionState.COMPOSED
            and binding.stable_key() == self.binding_key
            and int(expected_pairs) == int(self.expected_pairs)
        )


@dataclass(frozen=True)
class SolverUnsatClosureArtifact:
    formula_digest: str
    premise_digest: str
    query_label: str
    producer_kind: str
    authority_digest: str = ""
    solver_status: str = "unsat"
    execution_receipt: Optional[SolverQueryExecutionReceipt] = None
    schema_version: str = "solver_unsat_closure_v2"

    @classmethod
    def from_validated_result(
        cls, query: str, premise_digest: str, query_label: str,
        producer_kind: str, result: Any,
    ) -> "SolverUnsatClosureArtifact":
        if getattr(result, "is_equivalent", None) is not True:
            raise ValueError("solver closure requires a validated UNSAT result")
        execution_receipt = getattr(
            result, "solver_query_execution_receipt", None
        )
        if (
            type(execution_receipt) is not SolverQueryExecutionReceipt
            or not execution_receipt.validates_execution(
                query=query,
                expected_disposition="unsat",
                expected_query_label=query_label,
                expected_model=None,
            )
        ):
            raise ValueError(
                "solver closure requires the exact UNSAT execution receipt"
            )
        formula_digest = hashlib.sha256(query.encode()).hexdigest()
        payload = (
            "solver_unsat_closure_v2",
            formula_digest,
            premise_digest,
            query_label,
            producer_kind,
            "unsat",
            execution_receipt.stable_key(),
        )
        return cls(
            formula_digest=formula_digest,
            premise_digest=premise_digest,
            query_label=query_label,
            producer_kind=producer_kind,
            authority_digest=_closure_artifact_seal(payload),
            execution_receipt=execution_receipt,
        )

    @classmethod
    def from_terminal_record(
        cls, query: str, premise_digest: str, query_label: str,
        producer_kind: str, disposition: PairDisposition,
        execution_receipt: Optional[SolverQueryExecutionReceipt] = None,
    ) -> "SolverUnsatClosureArtifact":
        if disposition == PairDisposition.UNSAT:
            raise ValueError("UNSAT requires validated solver authority")
        status = disposition.value
        if status == "sat" and (
            type(execution_receipt) is not SolverQueryExecutionReceipt
            or not execution_receipt.validates_execution(
                query=query,
                expected_disposition="sat",
                expected_query_label=query_label,
                verify_model=False,
            )
        ):
            raise ValueError("SAT terminal record requires exact execution receipt")
        formula_digest = hashlib.sha256(query.encode()).hexdigest()
        payload = (
            "solver_unsat_closure_v2",
            formula_digest,
            premise_digest,
            query_label,
            producer_kind,
            status,
            execution_receipt.stable_key() if execution_receipt else (),
        )
        return cls(
            formula_digest=formula_digest,
            premise_digest=premise_digest,
            query_label=query_label,
            producer_kind=producer_kind,
            authority_digest=_closure_artifact_seal(payload),
            solver_status=status,
            execution_receipt=execution_receipt,
        )

    def validates(
        self,
        expected_status: str = "unsat",
        expected_premise_digest: Optional[str] = None,
    ) -> bool:
        receipt_key = (
            self.execution_receipt.stable_key()
            if self.execution_receipt is not None
            else ()
        )
        return (
            self.schema_version == "solver_unsat_closure_v2"
            and self.solver_status == expected_status
            and len(self.formula_digest) == 64
            and bool(self.premise_digest)
            and (
                expected_premise_digest is None
                or self.premise_digest == expected_premise_digest
            )
            and bool(self.query_label)
            and self.producer_kind in {"value_query", "return_width", "recovery", "aggregate"}
            and (
                self.solver_status not in {"sat", "unsat"}
                or (
                    type(self.execution_receipt)
                    is SolverQueryExecutionReceipt
                    and self.execution_receipt.validates_authority()
                    and self.execution_receipt.disposition
                    == self.solver_status
                    and self.execution_receipt.formula_digest
                    == self.formula_digest
                    and self.execution_receipt.query_label
                    == self.query_label
                )
            )
            and hmac.compare_digest(
                self.authority_digest,
                _closure_artifact_seal((
                    self.schema_version,
                    self.formula_digest,
                    self.premise_digest,
                    self.query_label,
                    self.producer_kind,
                    self.solver_status,
                    receipt_key,
                )),
            )
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version,
            self.formula_digest,
            self.premise_digest,
            self.query_label,
            self.producer_kind,
            self.authority_digest,
            self.solver_status,
            (
                self.execution_receipt.stable_key()
                if self.execution_receipt is not None
                else ()
            ),
        )


@dataclass(frozen=True)
class StructuralEqualityClosureArtifact:
    receipt: StructuralEqualityReceipt
    premise_digest: str
    query_label: str
    producer_kind: str
    authority_digest: str
    schema_version: str = "structural_equality_closure_v1"

    @classmethod
    def from_validated_result(
        cls,
        *,
        premise_digest: str,
        query_label: str,
        result: Any,
    ) -> "StructuralEqualityClosureArtifact":
        if getattr(result, "is_equivalent", None) is not True:
            raise ValueError("structural closure requires an equivalent result")
        receipt = getattr(result, "structural_equality_receipt", None)
        if (
            type(receipt) is not StructuralEqualityReceipt
            or not receipt.validates(expected_query_label=query_label)
        ):
            raise ValueError("structural closure requires exact typed receipt")
        schema_version = "structural_equality_closure_v1"
        payload = (
            schema_version,
            receipt.stable_key(),
            premise_digest,
            query_label,
            receipt.proof_kind,
        )
        return cls(
            receipt=receipt,
            premise_digest=premise_digest,
            query_label=query_label,
            producer_kind=receipt.proof_kind,
            authority_digest=_closure_artifact_seal(payload),
            schema_version=schema_version,
        )

    def validates(self, binding: PairLedgerBinding) -> bool:
        payload = (
            self.schema_version,
            self.receipt.stable_key(),
            self.premise_digest,
            self.query_label,
            self.producer_kind,
        )
        return (
            self.schema_version == "structural_equality_closure_v1"
            and type(self.receipt) is StructuralEqualityReceipt
            and self.receipt.validates(
                expected_query_label=self.query_label
            )
            and self.producer_kind == self.receipt.proof_kind
            and self.premise_digest == binding.premise_digest
            and hmac.compare_digest(
                self.authority_digest,
                _closure_artifact_seal(payload),
            )
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version,
            self.receipt.stable_key(),
            self.premise_digest,
            self.query_label,
            self.producer_kind,
            self.authority_digest,
        )


@dataclass(frozen=True)
class GuardUnsatClosureArtifact:
    artifact: GuardDisjointArtifact

    def validates(self, binding: PairLedgerBinding) -> bool:
        return (
            self.artifact.validates()
            and
            self.artifact.derived_view_id == binding.derived_view_id
            and self.artifact.premise_digest == binding.premise_digest
            and self.artifact.graph_generation == binding.graph_generation
            and len(self.artifact.query_digest) == 64
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "guard_unsat_closure_v1",
            self.artifact.requirement_key,
            self.artifact.query_digest,
            self.artifact.derived_view_id,
            self.artifact.premise_digest,
            self.artifact.graph_generation,
            self.artifact.query_execution_digest,
            self.artifact.query_issuer_identity,
            self.artifact.authority_digest,
            "validated" if self.artifact.validates() else "invalid",
        )


def emit_safe_counterexample_production_signal(
    *,
    safety_receipt: "CounterexampleSafetyReceipt",
) -> int:
    """Publish one validated SAT witness through the shared V2 bridge.

    Pairwise and Monolithic produce different native safety receipts, but the
    V2 decision authority must consume the same typed decisive event. Keep
    the audited emitter in this shared producer so either strategy cannot
    accidentally stop at a strategy-local receipt.
    """

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        SafeCounterexampleProductionSignal,
        active_production_pilot_session,
        emit_sat_safety_signal,
    )

    session = active_production_pilot_session()
    if session is not None and session.domain_signal_state.get(
        "sat_safety_safe_counterexample_committed"
    ):
        return 0
    signal = SafeCounterexampleProductionSignal.from_pairwise_receipt(
        safety_receipt
    )
    return emit_sat_safety_signal(
        signal,
        producer_site_manifest_id="safe-counterexample-pairwise-production",
    )


@dataclass(frozen=True)
class CounterexampleSafetyReceipt:
    formula_digest: str
    model_digest: str
    premise_digest: str
    pair_key: Tuple[int, int]
    validation_steps: Tuple[str, ...]
    authority_digest: str
    schema_version: str = "counterexample_safety_receipt_v1"

    @classmethod
    def from_pairwise_validation(
        cls, *, query: str, model: Any, premise_digest: str,
        pair_key: Tuple[int, int], analysis_safe: bool,
        global_case_replay_safe: bool, same_function_replay_safe: bool,
    ) -> "CounterexampleSafetyReceipt":
        if not (analysis_safe and global_case_replay_safe and same_function_replay_safe):
            raise ValueError("counterexample safety validation is incomplete")
        formula_digest = hashlib.sha256(query.encode()).hexdigest()
        model_digest = hashlib.sha256(repr(model).encode()).hexdigest()
        steps = (
            "analysis_summary_safe", "global_case_replay_safe",
            "same_function_replay_safe",
        )
        schema_version = "counterexample_safety_receipt_v1"
        payload = (
            schema_version, formula_digest, model_digest, premise_digest,
            pair_key, steps,
        )
        receipt = cls(
            formula_digest, model_digest, premise_digest, pair_key, steps,
            _closure_artifact_seal(payload), schema_version,
        )
        emit_safe_counterexample_production_signal(safety_receipt=receipt)
        return receipt

    def validates_authority(self) -> bool:
        payload = (
            self.schema_version, self.formula_digest, self.model_digest,
            self.premise_digest, self.pair_key, self.validation_steps,
        )
        return (
            self.schema_version == "counterexample_safety_receipt_v1"
            and len(self.formula_digest) == 64
            and len(self.model_digest) == 64
            and bool(self.premise_digest)
            and type(self.pair_key) is tuple
            and len(self.pair_key) == 2
            and self.validation_steps == (
                "analysis_summary_safe", "global_case_replay_safe",
                "same_function_replay_safe",
            )
            and hmac.compare_digest(
                self.authority_digest, _closure_artifact_seal(payload)
            )
        )

    def validates(self, binding: PairLedgerBinding, pair_key: Tuple[int, int]) -> bool:
        return (
            self.validates_authority()
            and self.premise_digest == binding.premise_digest
            and self.pair_key == pair_key
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return tuple(self.__dict__.values())


@dataclass(frozen=True)
class TerminalPairArtifact:
    terminal_record: SolverUnsatClosureArtifact
    safety_receipt: Optional[CounterexampleSafetyReceipt] = None

    def validates(
        self, binding: PairLedgerBinding, pair_key: Tuple[int, int],
        disposition: PairDisposition,
    ) -> bool:
        return (
            self.terminal_record.validates(disposition.value, binding.premise_digest)
            and (
                disposition != PairDisposition.SAT
                or (
                    self.safety_receipt is not None
                    and self.safety_receipt.validates(binding, pair_key)
                    and self.safety_receipt.formula_digest
                    == self.terminal_record.formula_digest
                    and self.terminal_record.execution_receipt is not None
                    and self.safety_receipt.model_digest
                    == self.terminal_record.execution_receipt.model_digest
                )
            )
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "terminal_pair_artifact_v1",
            self.terminal_record.stable_key(),
            self.safety_receipt.stable_key() if self.safety_receipt else (),
        )


@dataclass(frozen=True)
class ProducerValidatedClosureArtifact:
    """Sealed output issued only after a producer-specific candidate check."""

    proposition_digest: str
    evidence_digest: str
    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    graph_generation: int
    #: closure を発行した比較の authority（Issue #167）。封印に入れ、別の比較の ledger では
    #: 検証を通らない。
    comparison_authority_digest: str
    authority_digest: str
    validation_status: str = "validated"
    schema_version: str = "producer_validated_closure_v3"

    PRODUCER_KIND: ClassVar[str] = "abstract"

    def validates(self, binding: PairLedgerBinding) -> bool:
        payload = (
            self.PRODUCER_KIND, self.proposition_digest, self.evidence_digest,
            self.derived_view_id, self.premise_digest,
            self.graph_generation, self.comparison_authority_digest,
            self.validation_status, self.schema_version,
        )
        return (
            self.PRODUCER_KIND != "abstract"
            and self.validation_status == "validated"
            and len(self.proposition_digest) == 64
            and len(self.evidence_digest) == 64
            and self.derived_view_id == binding.derived_view_id
            and self.premise_digest == binding.premise_digest
            and self.graph_generation == binding.graph_generation
            and self.comparison_authority_digest == binding.comparison_authority_digest
            and hmac.compare_digest(
                self.authority_digest, _closure_artifact_seal(payload)
            )
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return (self.PRODUCER_KIND,) + tuple(self.__dict__.values())


class RuntimeReductionClosureArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "runtime_reduction_v2"


class CountedLoopClosedExpressionArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "counted_loop_closed_expression_v2"


class MethodBClosureArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "method_b_closure_v2"


class ReadonlyIdentityClosureArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "readonly_identity_closure_v2"


class CountedLoopValueRelationArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "counted_loop_value_relation_v2"


class AggregatePartitionClosureArtifact(ProducerValidatedClosureArtifact):
    PRODUCER_KIND = "aggregate_partition_closure_v2"


_TRUSTED_PRODUCER_VALIDATOR_CODES: Dict[str, Any] = {}


def issue_producer_validated_closure(
    artifact_type: type[ProducerValidatedClosureArtifact],
    binding: PairLedgerBinding,
    proposition: Any,
    evidence: Any,
) -> ProducerValidatedClosureArtifact:
    """Issue authority only from an import-time registered validator."""

    current = inspect.currentframe()
    caller = current.f_back if current is not None else None
    try:
        if (
            caller is None
            or _TRUSTED_PRODUCER_VALIDATOR_CODES.get(
                artifact_type.PRODUCER_KIND
            ) is not caller.f_code
        ):
            raise RuntimeError("producer closure issuer is not trusted")
    finally:
        del caller
        del current
    proposition_digest = hashlib.sha256(repr(proposition).encode()).hexdigest()
    evidence_digest = hashlib.sha256(repr(evidence).encode()).hexdigest()
    payload = (
        artifact_type.PRODUCER_KIND, proposition_digest, evidence_digest,
        binding.derived_view_id, binding.premise_digest,
        binding.graph_generation, binding.comparison_authority_digest, "validated",
        artifact_type.schema_version,
    )
    return artifact_type(
        proposition_digest, evidence_digest, binding.derived_view_id,
        binding.premise_digest, binding.graph_generation,
        binding.comparison_authority_digest,
        _closure_artifact_seal(payload),
    )


def register_producer_closure_validator(
    artifact_type: type[ProducerValidatedClosureArtifact],
    validator: Any,
) -> None:
    """Pin one import-time validator code object per artifact variant."""

    existing = _TRUSTED_PRODUCER_VALIDATOR_CODES.get(
        artifact_type.PRODUCER_KIND
    )
    if existing is not None:
        # Some CLI import-fallback tests deliberately reload the producer
        # module while this authority module remains live.  Accept only an
        # exact bytecode-identical reload and rotate membership to the new code
        # object; a changed validator remains a hard duplicate-registration
        # error.
        if marshal.dumps(existing) != marshal.dumps(validator.__code__):
            raise RuntimeError("producer closure validator already registered")
    _TRUSTED_PRODUCER_VALIDATOR_CODES[
        artifact_type.PRODUCER_KIND
    ] = validator.__code__


ValidatedClosureArtifact = Union[
    GuardUnsatClosureArtifact,
    SolverUnsatClosureArtifact,
    StructuralEqualityClosureArtifact,
    TerminalPairArtifact,
    ProducerValidatedClosureArtifact,
]


@dataclass(frozen=True)
class PairClosureEvidence:
    pair_key: Tuple[int, int]
    disposition: PairDisposition
    closure_kind: PairClosureKind
    binding_key: Tuple[Any, ...]
    artifact: ValidatedClosureArtifact
    evidence_digest: str
    required_binding_uses: Tuple[str, ...] = ()
    consumed_binding_uses: Tuple[str, ...] = ()
    excluded_binding_uses: Tuple[str, ...] = ()

    @classmethod
    def validated(
        cls, pair_key: Tuple[int, int], closure_kind: PairClosureKind,
        binding: PairLedgerBinding, artifact: ValidatedClosureArtifact, *,
        required_binding_uses: Tuple[str, ...] = (),
        consumed_binding_uses: Tuple[str, ...] = (),
    ) -> "PairClosureEvidence":
        valid = (
            artifact.validates(binding)
            if isinstance(
                artifact,
                (
                    GuardUnsatClosureArtifact,
                    StructuralEqualityClosureArtifact,
                    ProducerValidatedClosureArtifact,
                ),
            )
            else artifact.validates("unsat", binding.premise_digest)
        )
        if not valid:
            raise ValueError("pair closure artifact failed validation")
        required = tuple(sorted(set(required_binding_uses)))
        consumed = tuple(sorted(set(consumed_binding_uses)))
        if not set(consumed).issubset(required):
            raise ValueError("consumed binding use is not required by pair")
        excluded = tuple(sorted(set(required) - set(consumed)))
        digest = hashlib.sha256(repr((
            binding.stable_key(), artifact.stable_key(), required, consumed, excluded,
        )).encode()).hexdigest()
        return cls(
            pair_key, PairDisposition.UNSAT, closure_kind, binding.stable_key(),
            artifact, digest, required, consumed, excluded,
        )

    def validates(self, binding: PairLedgerBinding) -> bool:
        if self.binding_key != binding.stable_key() or self.disposition != PairDisposition.UNSAT:
            return False
        valid = (
            self.artifact.validates(binding)
            if isinstance(
                self.artifact,
                (
                    GuardUnsatClosureArtifact,
                    StructuralEqualityClosureArtifact,
                    ProducerValidatedClosureArtifact,
                ),
            )
            else self.artifact.validates("unsat", binding.premise_digest)
        )
        if (
            tuple(sorted(set(self.required_binding_uses))) != self.required_binding_uses
            or tuple(sorted(set(self.consumed_binding_uses))) != self.consumed_binding_uses
            or self.excluded_binding_uses != tuple(sorted(
                set(self.required_binding_uses) - set(self.consumed_binding_uses)
            ))
        ):
            return False
        expected = hashlib.sha256(repr((
            binding.stable_key(), self.artifact.stable_key(),
            self.required_binding_uses, self.consumed_binding_uses,
            self.excluded_binding_uses,
        )).encode()).hexdigest()
        return valid and self.evidence_digest == expected

    def snapshot_key(self) -> Tuple[Any, ...]:
        artifact = self.artifact
        return (
            "pair_closure_snapshot_v2",
            self.pair_key,
            self.disposition.value,
            self.closure_kind.value,
            self.binding_key,
            type(artifact).__name__,
            artifact.stable_key(),
            "validated" if self.disposition == PairDisposition.UNSAT else "terminal",
            self.required_binding_uses,
            self.consumed_binding_uses,
            self.excluded_binding_uses,
            self.evidence_digest,
        )


@dataclass(frozen=True)
class InconclusivePairRecord:
    pair_key: Tuple[int, int]
    reason_id: str
    binding_key: Tuple[Any, ...]
    evidence_digest: str


@dataclass(frozen=True)
class RuntimeQuiescenceCertificate:
    binding_key: Tuple[Any, ...]
    expected_pairs: int
    closed_pairs: int
    pending_work_items: int
    provisional_pairs: int
    runtime_view_id: Tuple[Any, ...]
    runtime_premise_digest: str
    pending_work: Tuple[Tuple[str, str], ...] = ()
    active_owner_work: Tuple[Any, ...] = ()

    @property
    def is_quiescent(self) -> bool:
        return self.closed_pairs == self.expected_pairs and self.pending_work_items == 0 and self.provisional_pairs == 0


@dataclass
class PairDispositionLedger:
    binding: PairLedgerBinding
    expected_pairs: int
    lifecycle: LedgerLifecycle = LedgerLifecycle.OPEN
    closures: Dict[Tuple[int, int], PairClosureEvidence] = field(default_factory=dict)
    provisional: Dict[Tuple[int, int], InconclusivePairRecord] = field(default_factory=dict)
    _lock: Lock = field(default_factory=Lock, repr=False, compare=False)

    def close(self, evidence: PairClosureEvidence) -> None:
        with self._lock:
            if self.lifecycle != LedgerLifecycle.OPEN or not evidence.validates(self.binding):
                raise ValueError("invalid closure for current open ledger")
            if evidence.pair_key in self.provisional:
                raise RuntimeError("pair already has provisional disposition")
            previous = self.closures.get(evidence.pair_key)
            if previous is not None:
                raise RuntimeError("duplicate pair closure")
            self.closures[evidence.pair_key] = evidence

    def record_inconclusive(self, pair_key: Tuple[int, int], reason_id: str, evidence: Any) -> None:
        with self._lock:
            if self.lifecycle != LedgerLifecycle.OPEN or pair_key in self.closures:
                raise RuntimeError("cannot record provisional pair")
            self.provisional[pair_key] = InconclusivePairRecord(
                pair_key, str(reason_id), self.binding.stable_key(),
                hashlib.sha256(repr(evidence).encode()).hexdigest(),
            )

    def record_terminal_query(
        self, pair_key: Tuple[int, int], disposition: PairDisposition,
        query: str, producer_kind: str, *,
        safety_receipt: Optional[CounterexampleSafetyReceipt] = None,
        query_execution_receipt: Optional[SolverQueryExecutionReceipt] = None,
    ) -> None:
        if disposition == PairDisposition.UNSAT:
            raise ValueError("UNSAT requires validated closure path")
        with self._lock:
            if self.lifecycle != LedgerLifecycle.OPEN or pair_key in self.provisional:
                raise RuntimeError("cannot record terminal pair")
            query_label = (
                query_execution_receipt.query_label
                if query_execution_receipt is not None
                else repr(pair_key)
            )
            terminal_record = SolverUnsatClosureArtifact.from_terminal_record(
                query or repr((pair_key, disposition.value)),
                self.binding.premise_digest,
                query_label, producer_kind, disposition,
                query_execution_receipt,
            )
            artifact = TerminalPairArtifact(terminal_record, safety_receipt)
            if not artifact.validates(self.binding, pair_key, disposition):
                raise ValueError("terminal pair artifact failed validation")
            digest = hashlib.sha256(repr((
                self.binding.stable_key(), artifact.stable_key(), (), (), (),
            )).encode()).hexdigest()
            evidence = PairClosureEvidence(
                pair_key, disposition, PairClosureKind.VALUE_QUERY,
                self.binding.stable_key(), artifact, digest,
            )
            previous = self.closures.get(pair_key)
            if previous is not None:
                raise RuntimeError("duplicate pair closure")
            self.closures[pair_key] = evidence

    def finalize_inconclusive(self) -> None:
        with self._lock:
            for pair_key, record in tuple(self.provisional.items()):
                artifact = TerminalPairArtifact(
                    SolverUnsatClosureArtifact.from_terminal_record(
                        record.evidence_digest, self.binding.premise_digest,
                        repr(pair_key), "aggregate", PairDisposition.UNKNOWN,
                    )
                )
                # UNKNOWN is a terminal record, not a proof closure.
                digest = hashlib.sha256(repr((
                    self.binding.stable_key(), artifact.stable_key(), (), (), (),
                )).encode()).hexdigest()
                self.closures[pair_key] = PairClosureEvidence(
                    pair_key, PairDisposition.UNKNOWN, PairClosureKind.AGGREGATE,
                    self.binding.stable_key(), artifact, digest,
                )
            self.provisional.clear()

    def counts(self) -> Mapping[str, int]:
        counts = {item.value: 0 for item in PairDisposition}
        for closure in self.closures.values():
            counts[closure.disposition.value] += 1
        counts["total"] = self.expected_pairs
        return counts

    def closure_snapshot(self) -> Tuple[Tuple[Any, ...], ...]:
        return tuple(self.closures[key].snapshot_key() for key in sorted(self.closures))

    def binding_use_partitions(
        self,
    ) -> Tuple[Tuple[str, ...], Tuple[str, ...], Tuple[str, ...]]:
        """Aggregate binding use from the validated closure snapshot."""

        required = {
            use
            for closure in self.closures.values()
            for use in closure.required_binding_uses
        }
        consumed = {
            use
            for closure in self.closures.values()
            for use in closure.consumed_binding_uses
        }
        excluded = {
            use
            for closure in self.closures.values()
            for use in closure.excluded_binding_uses
        } - consumed
        return (
            tuple(sorted(required)),
            tuple(sorted(consumed)),
            tuple(sorted(excluded)),
        )

    def validates_complete_snapshot(self) -> bool:
        if len(self.closures) != self.expected_pairs or self.provisional:
            return False
        for evidence in self.closures.values():
            if evidence.disposition == PairDisposition.UNSAT:
                if not evidence.validates(self.binding):
                    return False
            else:
                if (
                    evidence.binding_key != self.binding.stable_key()
                    or not isinstance(evidence.artifact, TerminalPairArtifact)
                    or not evidence.artifact.validates(
                        self.binding, evidence.pair_key, evidence.disposition
                    )
                ):
                    return False
                expected = hashlib.sha256(repr((
                    self.binding.stable_key(), evidence.artifact.stable_key(),
                    evidence.required_binding_uses, evidence.consumed_binding_uses,
                    evidence.excluded_binding_uses,
                )).encode()).hexdigest()
                if evidence.evidence_digest != expected:
                    return False
        return True

    def seal(self, certificate: RuntimeQuiescenceCertificate) -> None:
        with self._lock:
            if self.lifecycle != LedgerLifecycle.OPEN:
                raise RuntimeError("pair ledger is not open")
            if certificate.binding_key != self.binding.stable_key():
                raise ValueError("quiescence certificate binding mismatch")
            if not certificate.is_quiescent:
                raise RuntimeError(
                    "pair ledger cannot seal before runtime quiescence: "
                    f"closed={certificate.closed_pairs}/{certificate.expected_pairs}, "
                    f"pending={certificate.pending_work_items}, "
                    f"provisional={certificate.provisional_pairs}, "
                    f"work={certificate.pending_work!r}"
                )
            if not self.validates_complete_snapshot():
                raise RuntimeError("pair ledger closure snapshot is incomplete or invalid")
            if certificate.runtime_view_id != self.binding.derived_view_id or certificate.runtime_premise_digest != self.binding.premise_digest:
                raise RuntimeError("runtime generation changed before seal")
            self.lifecycle = LedgerLifecycle.SEALED

    def supersede(self) -> None:
        with self._lock:
            if self.lifecycle != LedgerLifecycle.SUPERSEDED:
                self.lifecycle = LedgerLifecycle.SUPERSEDED


@dataclass
class PairLedgerManager:
    current: Optional[PairDispositionLedger] = None
    history: list[PairDispositionLedger] = field(default_factory=list)
    pending_successor: Optional[PairLedgerSuccessorIntent] = None
    last_composed_successor: Optional[PairLedgerSuccessorPlan] = None
    promotion_state: Optional[PairLedgerPromotionState] = None

    def open(self, binding: PairLedgerBinding, expected_pairs: int) -> PairDispositionLedger:
        if self.pending_successor is not None:
            intent = self.pending_successor
            predecessor = self.current
            if predecessor is None:
                self.pending_successor = None
                self.promotion_state = PairLedgerPromotionState.ABORTED
                raise RuntimeError("successor promotion lost its predecessor ledger")
            if not intent.accepts_binding(binding):
                self.pending_successor = None
                self.promotion_state = PairLedgerPromotionState.ABORTED
                raise RuntimeError(
                    "replacement ledger does not match successor intent: "
                    f"intent={intent.stable_key()!r}, "
                    f"binding={binding.stable_key()!r}, "
                    f"expected_pairs={int(expected_pairs)}"
                )
            replacement = PairDispositionLedger(binding, expected_pairs)
            plan = PairLedgerSuccessorPlan(
                binding.stable_key(), int(expected_pairs),
                intent.predecessor_projection_id,
            )
            predecessor.supersede()
            self.history.append(predecessor)
            self.current = replacement
            self.pending_successor = None
            self.last_composed_successor = plan
            self.promotion_state = PairLedgerPromotionState.COMPOSED
            return self.current
        if self.current is not None and (
            self.current.binding.stable_key() != binding.stable_key()
            or self.current.lifecycle != LedgerLifecycle.OPEN
        ):
            self.current.supersede()
            self.history.append(self.current)
            self.current = None
        if self.current is None:
            self.current = PairDispositionLedger(binding, expected_pairs)
        elif self.current.expected_pairs != expected_pairs:
            raise RuntimeError("successor ledger pair plan changed during replan")
        return self.current

    def supersede_current(self) -> None:
        if self.current is not None:
            self.current.supersede()
            self.history.append(self.current)
            self.current = None

    def plan_successor(
        self,
        derived_view_id: Tuple[Any, ...],
        premise_digest: str,
        *,
        projection_refresh_required: bool = False,
    ) -> Optional[PairLedgerSuccessorIntent]:
        """Open a successor attempt while retaining predecessor authority."""

        previous = self.current
        if previous is None:
            return self.pending_successor
        if previous.lifecycle not in {LedgerLifecycle.OPEN, LedgerLifecycle.SEALED}:
            raise RuntimeError("only a live terminal branch may plan a successor")
        old = previous.binding
        successor = PairLedgerSuccessorIntent(
            old.comparison_session_id,
            old.branch_id,
            int(old.frame_generation) + 1,
            tuple(derived_view_id),
            str(premise_digest),
            int(old.graph_generation) + 1,
            old.comparison_authority_digest,
            old.projection_id,
            bool(projection_refresh_required),
        )
        self.pending_successor = successor
        self.last_composed_successor = None
        self.promotion_state = PairLedgerPromotionState.OPEN
        return successor
