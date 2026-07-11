"""Shared dependencies for StructuralRecurrenceSummarizer services."""

from collections import Counter
from dataclasses import dataclass, replace
import re
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple
from ...model import COUNTED_LOOP_SUM_OPCODE, COUNTED_STATE_TRANSITION_VALUE_OPCODE, READONLY_SUM_OPCODE, STATE_TRANSITION_LOOP_COUNT_OPCODE, ComposedLoopSummaryRef, Condition, CountedStateTransitionLoopSummaryRef, CountedLoopSummaryRef, Expression, ExpressionType, LoopBodyEffectRef, LoopCaseRef, LoopSideEffectProfileRef, LoopSummaryRef, LoopTermDescriptorRef, LoopVariableIdentityRef, LocationBaseRef, PcodeBlockRef, PcodeOpRef, ReductionAccumulatorProof, ReadonlyReductionRef, ReadonlyReductionTermRef, ReadonlyReductionWitness, ReturnInfo, StorageInfo, StateTransitionLoopSummaryRef
from ...model.render_smt import collect_intrinsic_smt_declarations, collect_unknown_smt_declarations, expression_smt_bit_width
from ...model.signature import get_declared_type_signedness, is_integral_data_type, is_pointer_data_type
from ...model.runtime_refs import UnknownValueRef
from ...smt.interface import SolverStatus
from ...smt.solvers.z3 import Z3Solver
from ...equivalence.formula.returns import coerce_value_to_bitvec_width
from ...equivalence.formula.types import ParameterInfo
from ...equivalence.param_semantics import parameter_identity_key_from_descriptor, parameter_identity_key_from_expression
from ..condition import ConditionConstraintSet, ConditionSimplifier, ConditionNormalizer
from ..condition.bitvector import eval_constant_raw
from ..condition.smt_oracle import ConditionSMTOracle
from ..effect_summary import CanonicalLocation, _expressions_equivalent_under_conditions, _reduce_expression_under_conditions, canonicalize_location

def _runtime_expression_signature(expr: Optional[Expression]):
    if expr is None:
        return ('none',)
    return ConditionNormalizer.expression_signature(expr)

def _runtime_conditions_signature(conditions: Sequence[Condition]):
    return ConditionNormalizer.conditions_signature(conditions)
_UNSUPPORTED_STATE_TRANSITION_CONDITION = object()
from ..recurrence.models import CountedLoopInduction, CountedLoopAccumulator, CountedLoopGuard, CountedLoopUpdateCase, CountedStateTransitionLoopModel, StateTransitionLoopModel, ResidueLoopCase, ReadonlyRoundedCountCandidate, ReadonlyAccumulatorPhiCandidate, ReadonlyAffineProgressionLiteral

__all__ = ('Any', 'COUNTED_LOOP_SUM_OPCODE', 'COUNTED_STATE_TRANSITION_VALUE_OPCODE', 'CanonicalLocation', 'ComposedLoopSummaryRef', 'Condition', 'ConditionConstraintSet', 'ConditionNormalizer', 'ConditionSMTOracle', 'ConditionSimplifier', 'CountedLoopAccumulator', 'CountedLoopGuard', 'CountedLoopInduction', 'CountedLoopSummaryRef', 'CountedLoopUpdateCase', 'CountedStateTransitionLoopModel', 'CountedStateTransitionLoopSummaryRef', 'Counter', 'Dict', 'Expression', 'ExpressionType', 'Iterable', 'List', 'LocationBaseRef', 'LoopBodyEffectRef', 'LoopCaseRef', 'LoopSideEffectProfileRef', 'LoopSummaryRef', 'LoopTermDescriptorRef', 'LoopVariableIdentityRef', 'Optional', 'ParameterInfo', 'PcodeBlockRef', 'PcodeOpRef', 'READONLY_SUM_OPCODE', 'ReadonlyAccumulatorPhiCandidate', 'ReadonlyAffineProgressionLiteral', 'ReadonlyReductionRef', 'ReadonlyReductionTermRef', 'ReadonlyReductionWitness', 'ReadonlyRoundedCountCandidate', 'ReductionAccumulatorProof', 'ResidueLoopCase', 'ReturnInfo', 'STATE_TRANSITION_LOOP_COUNT_OPCODE', 'Sequence', 'SolverStatus', 'StateTransitionLoopModel', 'StateTransitionLoopSummaryRef', 'StorageInfo', 'Tuple', 'UnknownValueRef', 'Z3Solver', '_UNSUPPORTED_STATE_TRANSITION_CONDITION', '_expressions_equivalent_under_conditions', '_reduce_expression_under_conditions', '_runtime_conditions_signature', '_runtime_expression_signature', 'canonicalize_location', 'coerce_value_to_bitvec_width', 'collect_intrinsic_smt_declarations', 'collect_unknown_smt_declarations', 'dataclass', 'eval_constant_raw', 'expression_smt_bit_width', 'get_declared_type_signedness', 'is_integral_data_type', 'is_pointer_data_type', 'parameter_identity_key_from_descriptor', 'parameter_identity_key_from_expression', 're', 'replace')
