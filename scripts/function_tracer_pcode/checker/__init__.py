"""等価性判定層.

Public imports stay concentrated here while internal responsibilities are
split across checker/workflow/reanalysis/attempts/result helpers.

Names are resolved lazily on first access so importing a submodule never
pulls in the whole layer (and cannot create import cycles)."""

from importlib import import_module

_LAZY = {
    "ArchitectureDetector": ("scripts.function_tracer_pcode.checker.arch.detector", "ArchitectureDetector"),
    "CheckStrategy": ("scripts.function_tracer_pcode.proof.strategies", "CheckStrategy"),
    "CounterexampleFormatter": ("scripts.function_tracer_pcode.checker.counterexample", "CounterexampleFormatter"),
    "EquivalenceChecker": ("scripts.function_tracer_pcode.checker.checker", "EquivalenceChecker"),
    "EquivalenceResult": ("scripts.function_tracer_pcode.checker.result", "EquivalenceResult"),
    "FormattedCounterexample": ("scripts.function_tracer_pcode.checker.counterexample", "FormattedCounterexample"),
    "FormulaBuilder": ("scripts.function_tracer_pcode.proof.formula", "FormulaBuilder"),
    "MIPS64Handler": ("scripts.function_tracer_pcode.checker.arch.mips64", "MIPS64Handler"),
    "MonolithicStrategy": ("scripts.function_tracer_pcode.proof.strategies", "MonolithicStrategy"),
    "PairwiseStrategy": ("scripts.function_tracer_pcode.proof.strategies", "PairwiseStrategy"),
    "ParameterFragmentInfo": ("scripts.function_tracer_pcode.proof.formula", "ParameterFragmentInfo"),
    "PhaseContext": ("scripts.function_tracer_pcode.checker.phases.handler", "PhaseContext"),
    "PhaseHandler": ("scripts.function_tracer_pcode.checker.phases.handler", "PhaseHandler"),
    "RewriteInfo": ("scripts.function_tracer_pcode.checker.result", "RewriteInfo"),
    "TypeFixResult": ("scripts.function_tracer_pcode.semantics.typing.fixer", "TypeFixResult"),
    "TypeFixer": ("scripts.function_tracer_pcode.semantics.typing.fixer", "TypeFixer"),
    "TypeFixerConfig": ("scripts.function_tracer_pcode.semantics.typing.fixer", "TypeFixerConfig"),
    "UNKNOWN_TUPLE_MISSING": ("scripts.function_tracer_pcode.proof.unknown_reason", "UNKNOWN_TUPLE_MISSING"),
    "UnknownAggregationUnit": ("scripts.function_tracer_pcode.proof.unknown_reason", "UnknownAggregationUnit"),
    "UnknownCountKind": ("scripts.function_tracer_pcode.proof.unknown_reason", "UnknownCountKind"),
    "UnknownDecisionEffect": ("scripts.function_tracer_pcode.proof.unknown_reason", "UnknownDecisionEffect"),
    "UnknownReasonClass": ("scripts.function_tracer_pcode.proof.unknown_reason", "UnknownReasonClass"),
    "UnknownReasonId": ("scripts.function_tracer_pcode.proof.unknown_reason", "UnknownReasonId"),
    "UnknownReasonRecord": ("scripts.function_tracer_pcode.checker.unknown_reason", "UnknownReasonRecord"),
    "UnknownReasonScope": ("scripts.function_tracer_pcode.proof.unknown_reason", "UnknownReasonScope"),
    "UnknownRecoveryAction": ("scripts.function_tracer_pcode.checker.unknown_reason", "UnknownRecoveryAction"),
    "UnknownRecoveryActionStatus": ("scripts.function_tracer_pcode.proof.unknown_reason", "UnknownRecoveryActionStatus"),
    "UnknownRecoveryPlan": ("scripts.function_tracer_pcode.proof.unknown_reason", "UnknownRecoveryPlan"),
    "UnknownRecoveryProofKind": ("scripts.function_tracer_pcode.proof.unknown_reason", "UnknownRecoveryProofKind"),
    "UnknownRecoveryProofObligation": ("scripts.function_tracer_pcode.proof.unknown_reason", "UnknownRecoveryProofObligation"),
    "build_proof_obligation_id": ("scripts.function_tracer_pcode.proof.unknown_reason", "build_proof_obligation_id"),
    "build_unknown_recovery_actions": ("scripts.function_tracer_pcode.checker.unknown_reason", "build_unknown_recovery_actions"),
    "get_type_name_from_param": ("scripts.function_tracer_pcode.semantics.typing.helpers", "get_type_name_from_param"),
    "get_unknown_recovery_plan": ("scripts.function_tracer_pcode.proof.unknown_reason", "get_unknown_recovery_plan"),
    "is_int_type": ("scripts.function_tracer_pcode.semantics.typing.helpers", "is_int_type"),
    "is_long_type": ("scripts.function_tracer_pcode.semantics.typing.helpers", "is_long_type"),
    "is_unsigned_type": ("scripts.function_tracer_pcode.semantics.typing.helpers", "is_unsigned_type"),
    "summarize_unknown_recovery_backlog": ("scripts.function_tracer_pcode.checker.unknown_reason", "summarize_unknown_recovery_backlog"),
}

__all__ = sorted(_LAZY)


def __getattr__(name):
    try:
        module_name, attribute = _LAZY[name]
    except KeyError:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}") from None
    value = getattr(import_module(module_name), attribute)
    globals()[name] = value
    return value


def __dir__():
    return sorted(set(globals()) | set(_LAZY))
