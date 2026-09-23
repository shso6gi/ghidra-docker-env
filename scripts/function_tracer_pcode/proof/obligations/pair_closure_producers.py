"""Producer-specific validation for typed non-solver pair closures.

Candidates carry no authority.  Validators execute a registry-owned proof
bundle whose function globals are detached from the live service modules, then
bind the result to the exact ledger generation.  A failed validator returns
``None`` so orchestration uses the canonical solver or a typed UNKNOWN.
"""

from __future__ import annotations

from dataclasses import dataclass
import dis
import importlib
import inspect
from pathlib import Path
from threading import RLock
from types import FunctionType, MappingProxyType
from typing import Any, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import (
    relation_digest_is_current,
)

from scripts.function_tracer_pcode.proof.obligations.pair_disposition import (
    AggregatePartitionClosureArtifact,
    CountedLoopClosedExpressionArtifact,
    CountedLoopValueRelationArtifact,
    MethodBClosureArtifact,
    PairLedgerBinding,
    ReadonlyIdentityClosureArtifact,
    RuntimeReductionClosureArtifact,
    issue_producer_validated_closure,
    register_producer_closure_validator,
)


@dataclass(frozen=True)
class PairClosureCandidate:
    pair_id: str
    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    graph_generation: int
    input_correspondence_digest: str
    proposition: Any
    evidence: Any

    @classmethod
    def create(
        cls,
        binding: PairLedgerBinding,
        pair_id: str,
        proposition: Any,
        evidence: Any,
    ) -> "PairClosureCandidate":
        return cls(
            str(pair_id),
            binding.derived_view_id,
            binding.premise_digest,
            binding.graph_generation,
            binding.input_correspondence_digest,
            proposition,
            evidence,
        )

    def is_current_for(self, binding: PairLedgerBinding) -> bool:
        # Issue #167: closure は ledger の relation の下でだけ成り立つ。ledger と
        # candidate が同じ relation を名乗り、それがいま比較している relation である
        # こと（pinned proof が照合する証拠の relation と同じ値）。
        return (
            self.derived_view_id == binding.derived_view_id
            and self.premise_digest == binding.premise_digest
            and self.graph_generation == binding.graph_generation
            and self.input_correspondence_digest == binding.input_correspondence_digest
            and relation_digest_is_current(binding.input_correspondence_digest)
        )


class RuntimeReductionCandidate(PairClosureCandidate):
    pass


class CountedLoopClosedExpressionCandidate(PairClosureCandidate):
    pass


class MethodBClosureCandidate(PairClosureCandidate):
    pass


class ReadonlyIdentityCandidate(PairClosureCandidate):
    pass


class CountedLoopValueRelationCandidate(PairClosureCandidate):
    pass


class AggregatePartitionCandidate(PairClosureCandidate):
    pass


_ORIGINAL_CONJUNCTION_IS_UNSAT = inspect.getattr_static(
    ConditionSMTOracle, "conjunction_is_unsat"
).__func__


class _AuthorityConditionSMTOracle:
    """Cache-free facade used only inside authority-bearing proof namespaces."""

    @classmethod
    def conjunction_is_unsat(
        cls,
        conditions: Any,
        *,
        cache_key: Optional[Tuple[object, ...]] = None,
    ) -> Optional[bool]:
        return _ORIGINAL_CONJUNCTION_IS_UNSAT(
            ConditionSMTOracle,
            conditions,
            cache_key=cache_key,
            use_cache=False,
        )


_PINNED_PROOF_IMPLEMENTATIONS: Optional[Mapping[str, Any]] = None
_PINNED_DEPENDENCY_CONTRACTS: Tuple[Any, ...] = ()
_PINNED_IMPLEMENTATION_CONTRACT: Tuple[Any, ...] = ()
_PINNED_STRATEGY_TYPES: dict[type, type] = {}
_PROOF_EXECUTION_LOCK = RLock()


def _stable_value_token(value: Any, depth: int = 0) -> Tuple[Any, ...]:
    """Capture mutation-sensitive state without trusting object ``repr``."""

    if depth >= 4:
        return ("identity", id(value), type(value))
    if value is None or isinstance(value, (bool, int, float, str, bytes)):
        return ("scalar", type(value), value)
    if isinstance(value, tuple):
        return (
            "tuple",
            tuple(_stable_value_token(item, depth + 1) for item in value),
        )
    if isinstance(value, list):
        return (
            "list",
            tuple(_stable_value_token(item, depth + 1) for item in value),
        )
    if isinstance(value, dict):
        return (
            "dict",
            tuple(sorted((
                (
                    _stable_value_token(key, depth + 1),
                    _stable_value_token(item, depth + 1),
                )
                for key, item in value.items()
            ), key=repr)),
        )
    if isinstance(value, (set, frozenset)):
        return (
            type(value).__name__,
            tuple(sorted(
                (_stable_value_token(item, depth + 1) for item in value),
                key=repr,
            )),
        )
    return ("identity", id(value), type(value))


def _function_dependency_token(function: Any) -> Tuple[Any, ...]:
    closure = tuple(
        _stable_value_token(cell.cell_contents)
        for cell in tuple(getattr(function, "__closure__", ()) or ())
    )
    return (
        "function",
        id(function),
        id(function.__code__),
        _stable_value_token(function.__defaults__),
        _stable_value_token(function.__kwdefaults__),
        closure,
    )


def _global_dependency_token(value: Any) -> Tuple[Any, ...]:
    if inspect.isfunction(value):
        return _function_dependency_token(value)
    if inspect.isclass(value):
        callable_descriptors = []
        for name, descriptor in value.__dict__.items():
            function = None
            descriptor_kind = None
            if isinstance(descriptor, staticmethod):
                descriptor_kind = "staticmethod"
                function = descriptor.__func__
            elif isinstance(descriptor, classmethod):
                descriptor_kind = "classmethod"
                function = descriptor.__func__
            elif inspect.isfunction(descriptor):
                descriptor_kind = "method"
                function = descriptor
            if function is not None:
                callable_descriptors.append(
                    (name, descriptor_kind, _function_dependency_token(function))
                )
            elif callable(descriptor):
                callable_descriptors.append(
                    (name, "callable", id(descriptor), type(descriptor))
                )
        return (
            "class",
            id(value),
            tuple(sorted(callable_descriptors)),
        )
    if callable(value):
        return (
            "callable",
            id(value),
            type(value),
            _global_dependency_token(type(value)),
        )
    return ("binding", id(value), type(value))


def _referenced_global_names(functions: Any) -> Tuple[str, ...]:
    names = set()
    for function in functions:
        for instruction in dis.get_instructions(function):
            if instruction.opname in {"LOAD_GLOBAL", "LOAD_NAME"}:
                names.add(str(instruction.argval))
    return tuple(sorted(names))


def _dependency_contract(
    execution_globals: dict[str, Any],
    functions: Any,
) -> Tuple[Any, ...]:
    return tuple(
        (name, _global_dependency_token(execution_globals[name]))
        for name in _referenced_global_names(functions)
        if name in execution_globals and name != "__builtins__"
    )


def _implementation_contract(implementations: Mapping[str, Any]) -> Tuple[Any, ...]:
    return tuple(
        (
            name,
            _function_dependency_token(implementation),
            id(implementation.__globals__),
        )
        for name, implementation in sorted(implementations.items())
    )


def _proof_dependencies_are_current() -> bool:
    implementations = _PINNED_PROOF_IMPLEMENTATIONS
    return (
        implementations is not None
        and _implementation_contract(implementations)
        == _PINNED_IMPLEMENTATION_CONTRACT
        and bool(_PINNED_DEPENDENCY_CONTRACTS)
        and all(
            tuple(
                (name, _global_dependency_token(execution_globals.get(name)))
                for name, _token in expected
            ) == expected
            for execution_globals, expected in _PINNED_DEPENDENCY_CONTRACTS
        )
    )


def _execute_pinned_proof(
    implementation: Any,
    *args: Any,
    **kwargs: Any,
) -> Tuple[bool, Any]:
    """Run only while the sealed dependency receipts remain unchanged."""

    if implementation is None:
        return False, None
    with _PROOF_EXECUTION_LOCK:
        if not _proof_dependencies_are_current():
            return False, None
        result = implementation(*args, **kwargs)
        if not _proof_dependencies_are_current():
            return False, None
        return True, result


def _clone_module_function_bundle(
    implementations: dict[str, Any],
) -> Tuple[dict[str, Any], Tuple[Any, ...]]:
    """Detach proof functions from mutable service-module global dictionaries."""

    module_namespaces: dict[int, tuple[dict[str, Any], dict[str, Any]]] = {}
    cloned_functions: dict[int, FunctionType] = {}
    for implementation in implementations.values():
        if not inspect.isfunction(implementation):
            raise RuntimeError("producer proof implementation must be a function")
        globals_id = id(implementation.__globals__)
        if globals_id in module_namespaces:
            continue
        live_globals = implementation.__globals__
        frozen_globals = dict(live_globals)
        if "ConditionSMTOracle" in frozen_globals:
            frozen_globals["ConditionSMTOracle"] = _AuthorityConditionSMTOracle
        module_namespaces[globals_id] = (live_globals, frozen_globals)
        for global_name, value in tuple(live_globals.items()):
            if not inspect.isfunction(value) or value.__globals__ is not live_globals:
                continue
            if value.__closure__:
                # A closure can retain mutable state outside the detached
                # namespace and therefore cannot become proof authority.
                continue
            clone = FunctionType(
                value.__code__, frozen_globals, value.__name__,
                value.__defaults__, None,
            )
            clone.__kwdefaults__ = value.__kwdefaults__
            clone.__annotations__ = dict(getattr(value, "__annotations__", {}))
            clone.__dict__.update(getattr(value, "__dict__", {}))
            clone.__module__ = value.__module__
            clone.__qualname__ = value.__qualname__
            frozen_globals[global_name] = clone
            cloned_functions[id(value)] = clone
    frozen: dict[str, Any] = {}
    for name, implementation in implementations.items():
        clone = cloned_functions.get(id(implementation))
        if clone is None:
            raise RuntimeError(
                f"producer proof implementation has an open closure: {name}"
            )
        frozen[str(name)] = clone
    dependency_contracts = tuple(
        (
            frozen_globals,
            _dependency_contract(
                frozen_globals,
                tuple(
                    value
                    for value in frozen_globals.values()
                    if inspect.isfunction(value)
                    and value.__globals__ is frozen_globals
                ),
            ),
        )
        for _live_globals, frozen_globals in module_namespaces.values()
    )
    return frozen, dependency_contracts


def seal_producer_proof_implementations(
    implementations: dict[str, Any],
) -> None:
    """Seal a closed proof bundle once from production orchestration import."""

    global _PINNED_DEPENDENCY_CONTRACTS
    global _PINNED_IMPLEMENTATION_CONTRACT
    global _PINNED_PROOF_IMPLEMENTATIONS
    frame = inspect.currentframe()
    caller = frame.f_back if frame is not None else None
    try:
        caller_path = Path(caller.f_code.co_filename) if caller is not None else None
        if (
            caller is None
            or caller.f_code.co_name != "<module>"
            or caller_path is None
            or caller_path.name != "orchestration.py"
            or caller_path.parent.name != "pairwise_services"
        ):
            raise RuntimeError("producer proof implementation sealer is not trusted")
    finally:
        del caller
        del frame
    frozen, dependency_contracts = _clone_module_function_bundle(implementations)
    if not frozen:
        raise RuntimeError("producer proof implementation snapshot is empty")
    if _PINNED_PROOF_IMPLEMENTATIONS is not None:
        raise RuntimeError("producer proof implementation reseal rejected")
    immutable_frozen = MappingProxyType(dict(frozen))
    _PINNED_PROOF_IMPLEMENTATIONS = immutable_frozen
    _PINNED_DEPENDENCY_CONTRACTS = dependency_contracts
    _PINNED_IMPLEMENTATION_CONTRACT = _implementation_contract(immutable_frozen)


def _pinned_strategy_type(strategy_type: type) -> Optional[type]:
    cached = _PINNED_STRATEGY_TYPES.get(strategy_type)
    if cached is not None:
        return cached
    implementations = _PINNED_PROOF_IMPLEMENTATIONS
    if implementations is None:
        return None
    namespace: dict[str, Any] = {}
    for name, implementation in implementations.items():
        descriptor = inspect.getattr_static(strategy_type, name, None)
        if isinstance(descriptor, staticmethod):
            namespace[name] = staticmethod(implementation)
        elif isinstance(descriptor, classmethod):
            namespace[name] = classmethod(implementation)
        elif inspect.isfunction(descriptor):
            namespace[name] = implementation
        else:
            parameters = tuple(inspect.signature(implementation).parameters)
            first = parameters[0] if parameters else None
            if first == "cls":
                namespace[name] = classmethod(implementation)
            elif first == "self":
                namespace[name] = implementation
            else:
                namespace[name] = staticmethod(implementation)
    pinned = type(
        f"_Pinned{strategy_type.__name__}ProofStrategy",
        (strategy_type,),
        namespace,
    )
    _PINNED_STRATEGY_TYPES[strategy_type] = pinned
    return pinned


def _fixed_proof_implementation(strategy: Any, method_name: str) -> Any:
    pairwise_module = importlib.import_module(
        "scripts.function_tracer_pcode.proof.strategies.pairwise"
    )
    loop_template_module = importlib.import_module(
        "scripts.function_tracer_pcode.proof.strategies.loop_template"
    )
    if type(strategy) not in (
        pairwise_module.PairwiseStrategy,
        loop_template_module.LoopTemplatePairwiseStrategy,
    ):
        return None
    pinned_type = _pinned_strategy_type(type(strategy))
    if pinned_type is None:
        return None
    sanitized_strategy = object.__new__(pinned_type)
    for name, value in getattr(strategy, "__dict__", {}).items():
        if name.startswith("_") and callable(value):
            continue
        setattr(sanitized_strategy, name, value)
    implementation = getattr(sanitized_strategy, method_name, None)
    return implementation if callable(implementation) else None


def validate_runtime_reduction_candidate(
    strategy: Any,
    binding: PairLedgerBinding,
    candidate: RuntimeReductionCandidate,
    case1: Any,
    case2: Any,
    semantic_parameter_sources: Any,
) -> Optional[RuntimeReductionClosureArtifact]:
    if not candidate.is_current_for(binding):
        return None
    implementation = _fixed_proof_implementation(
        strategy, "_cases_have_equivalent_runtime_reductions"
    )
    executed, valid = _execute_pinned_proof(
        implementation,
        case1, case2,
        semantic_parameter_sources=semantic_parameter_sources,
    )
    if not executed or not valid:
        return None
    return issue_producer_validated_closure(
        RuntimeReductionClosureArtifact, binding,
        (candidate.pair_id, candidate.proposition), candidate.evidence,
    )


def validate_counted_loop_closed_expression_candidate(
    strategy: Any,
    binding: PairLedgerBinding,
    candidate: CountedLoopClosedExpressionCandidate,
    case1: Any,
    case2: Any,
    base_ctx: Any,
) -> Optional[CountedLoopClosedExpressionArtifact]:
    if not candidate.is_current_for(binding):
        return None
    implementation = _fixed_proof_implementation(
        strategy, "_case_pair_counted_loop_summary_matches_closed_expression"
    )
    executed, valid = _execute_pinned_proof(
        implementation, case1, case2, base_ctx=base_ctx
    )
    if not executed or not valid:
        return None
    return issue_producer_validated_closure(
        CountedLoopClosedExpressionArtifact, binding,
        (candidate.pair_id, candidate.proposition), candidate.evidence,
    )


def validate_method_b_candidate(
    strategy: Any,
    binding: PairLedgerBinding,
    candidate: MethodBClosureCandidate,
    reason: Any,
    analysis1: Any,
    analysis2: Any,
) -> Optional[MethodBClosureArtifact]:
    if not candidate.is_current_for(binding):
        return None
    implementation = _fixed_proof_implementation(strategy, "_method_b_closure_proof_is_complete")
    executed, valid = _execute_pinned_proof(
        implementation, reason, analysis1, analysis2
    )
    if not executed or not valid:
        return None
    return issue_producer_validated_closure(
        MethodBClosureArtifact, binding,
        (candidate.pair_id, candidate.proposition), candidate.evidence,
    )


def validate_readonly_identity_candidate(
    strategy: Any,
    binding: PairLedgerBinding,
    candidate: ReadonlyIdentityCandidate,
    reason: Any,
    analysis1: Any,
    analysis2: Any,
) -> Optional[ReadonlyIdentityClosureArtifact]:
    if not candidate.is_current_for(binding):
        return None
    implementation = _fixed_proof_implementation(strategy, "_readonly_identity_proof_is_complete")
    executed, valid = _execute_pinned_proof(
        implementation, reason, analysis1, analysis2
    )
    if not executed or not valid:
        return None
    return issue_producer_validated_closure(
        ReadonlyIdentityClosureArtifact, binding,
        (candidate.pair_id, candidate.proposition), candidate.evidence,
    )


def validate_counted_loop_value_candidate(
    strategy: Any,
    binding: PairLedgerBinding,
    candidate: CountedLoopValueRelationCandidate,
    case1: Any,
    case2: Any,
    base_ctx: Any,
    semantic_parameter_sources: Any,
) -> Optional[CountedLoopValueRelationArtifact]:
    if not candidate.is_current_for(binding):
        return None
    closed_values = _fixed_proof_implementation(
        strategy, "_case_pair_counted_loop_summaries_match_by_closed_values"
    )
    value_relation = _fixed_proof_implementation(
        strategy, "_counted_loop_values_are_provably_equivalent"
    )
    closed_executed, closed_valid = _execute_pinned_proof(
        closed_values, case1, case2, base_ctx=base_ctx
    )
    relation_executed, relation_valid = _execute_pinned_proof(
        value_relation,
            case1.value_expr, case2.value_expr,
            left_case=case1, right_case=case2,
            semantic_parameter_sources=semantic_parameter_sources,
    )
    valid = bool(closed_executed and closed_valid) or bool(
        relation_executed and relation_valid
    )
    if not valid:
        return None
    return issue_producer_validated_closure(
        CountedLoopValueRelationArtifact, binding,
        (candidate.pair_id, candidate.proposition), candidate.evidence,
    )


def validate_aggregate_partition_candidate(
    strategy: Any,
    binding: PairLedgerBinding,
    candidate: AggregatePartitionCandidate,
    pending_pair: Tuple[int, int],
    partition_witness: Tuple[Tuple[int, int], ...],
    pending_pairs: Any,
    cases1: Any,
    cases2: Any,
    resolved_pairs: Any,
) -> Optional[AggregatePartitionClosureArtifact]:
    if not candidate.is_current_for(binding):
        return None
    normalized = tuple(sorted(set(tuple(pair) for pair in partition_witness)))
    implementation = _fixed_proof_implementation(
        strategy, "_resolve_pending_loop_summary_pairs_with_partition_proof"
    )
    executed, recomputed_value = _execute_pinned_proof(
        implementation,
        pending_pairs, cases1, cases2, set(resolved_pairs),
    )
    if not executed:
        return None
    recomputed = tuple(sorted(set(
        tuple(pair) for pair in recomputed_value
    )))
    if (
        normalized != recomputed
        or tuple(pending_pair) not in normalized
        or candidate.evidence != normalized
    ):
        return None
    return issue_producer_validated_closure(
        AggregatePartitionClosureArtifact, binding,
        (candidate.pair_id, candidate.proposition), candidate.evidence,
    )


for _artifact_type, _validator in (
    (RuntimeReductionClosureArtifact, validate_runtime_reduction_candidate),
    (CountedLoopClosedExpressionArtifact, validate_counted_loop_closed_expression_candidate),
    (MethodBClosureArtifact, validate_method_b_candidate),
    (ReadonlyIdentityClosureArtifact, validate_readonly_identity_candidate),
    (CountedLoopValueRelationArtifact, validate_counted_loop_value_candidate),
    (AggregatePartitionClosureArtifact, validate_aggregate_partition_candidate),
):
    register_producer_closure_validator(_artifact_type, _validator)


__all__ = (
    "AggregatePartitionCandidate",
    "CountedLoopClosedExpressionCandidate",
    "CountedLoopValueRelationCandidate",
    "MethodBClosureCandidate",
    "PairClosureCandidate",
    "ReadonlyIdentityCandidate",
    "RuntimeReductionCandidate",
    "validate_aggregate_partition_candidate",
    "validate_counted_loop_closed_expression_candidate",
    "validate_counted_loop_value_candidate",
    "validate_method_b_candidate",
    "validate_readonly_identity_candidate",
    "validate_runtime_reduction_candidate",
)
