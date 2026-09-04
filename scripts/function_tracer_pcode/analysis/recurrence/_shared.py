"""Shared dependencies for StructuralRecurrenceSummarizer services."""

from typing import Optional, Sequence
from scripts.function_tracer_pcode.core import Condition, Expression
from scripts.function_tracer_pcode.proof.formula.returns import coerce_value_to_bitvec_width
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.semantics.param_semantics import (
    parameter_identity_key_from_descriptor,
    parameter_identity_key_from_expression,
)
from scripts.function_tracer_pcode.analysis.condition import (
    ConditionConstraintSet,
    ConditionSimplifier,
    ConditionNormalizer,
)
from scripts.function_tracer_pcode.analysis.condition.bitvector import eval_constant_raw
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.analysis.effects.summary import (
    CanonicalLocation,
    _expressions_equivalent_under_conditions,
    _reduce_expression_under_conditions,
    canonicalize_location,
)

def _runtime_expression_signature(expr: Optional[Expression]):
    if expr is None:
        return ('none',)
    return ConditionNormalizer.expression_signature(expr)

def _runtime_conditions_signature(conditions: Sequence[Condition]):
    return ConditionNormalizer.conditions_signature(conditions)
_UNSUPPORTED_STATE_TRANSITION_CONDITION = object()
from scripts.function_tracer_pcode.analysis.recurrence.models import (
    CountedLoopInduction,
    CountedLoopAccumulator,
    CountedLoopGuard,
    CountedLoopUpdateCase,
    CountedStateTransitionLoopModel,
    StateTransitionLoopModel,
    ResidueLoopCase,
    ReadonlyRoundedCountCandidate,
    ReadonlyAccumulatorPhiCandidate,
    ReadonlyAffineProgressionLiteral,
)

__all__ = ('CanonicalLocation', 'ConditionConstraintSet', 'ConditionNormalizer', 'ConditionSMTOracle', 'ConditionSimplifier', 'CountedLoopAccumulator', 'CountedLoopGuard', 'CountedLoopInduction', 'CountedLoopUpdateCase', 'CountedStateTransitionLoopModel', 'ParameterInfo', 'ReadonlyAccumulatorPhiCandidate', 'ReadonlyAffineProgressionLiteral', 'ReadonlyRoundedCountCandidate', 'ResidueLoopCase', 'StateTransitionLoopModel', '_UNSUPPORTED_STATE_TRANSITION_CONDITION', '_expressions_equivalent_under_conditions', '_reduce_expression_under_conditions', '_runtime_conditions_signature', '_runtime_expression_signature', 'canonicalize_location', 'coerce_value_to_bitvec_width', 'eval_constant_raw', 'parameter_identity_key_from_descriptor', 'parameter_identity_key_from_expression')
