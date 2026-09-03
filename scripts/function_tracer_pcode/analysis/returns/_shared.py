"""Shared dependencies for ReturnAnalyzer services."""

import re
import hashlib
from dataclasses import dataclass, replace
from contextlib import contextmanager
from functools import cmp_to_key
from typing import Iterable, List, Dict, Optional, Any, Set, Tuple, Sequence, Mapping, cast
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType, Condition
from scripts.function_tracer_pcode.core.call_target import CallTargetRef, coerce_call_target_ref
from scripts.function_tracer_pcode.core.structural import StructuralKey, expression_key_safe
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.core.analysis import (
    ComparisonSurface,
    DeferredCallInfo,
    DivergenceOutcome,
    ReturnInfo,
    ReturnOutcome,
    UnknownOutcome,
    FunctionReturnAnalysis,
    SignednessResult,
    ReturnValueFlowCertificate,
    ReturnValueFlowStep,
    VarnodeFlowRef,
)
from scripts.function_tracer_pcode.core.runtime_refs import (
    AddressValueRef,
    DeferredCallRef,
    PcodeBlockRef,
    PcodeOpRef,
    PostStateValueRef,
    ReadonlyReductionRef,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.core.signature import (
    get_declared_type_signedness,
    is_void_data_type,
)
from scripts.function_tracer_pcode.core.render_smt import expression_contains_unsupported_smt_ops
from scripts.function_tracer_pcode.core.intrinsics import resolve_pcode_intrinsic
from scripts.function_tracer_pcode.config.settings import (
    BOUNDED_CALL_MAX_CASES,
    BOUNDED_CALL_REFINEMENT_ENABLED,
    BOUNDED_CALL_UNROLL_LIMIT,
)
from scripts.function_tracer_pcode.analysis import PcodeTracer
from scripts.function_tracer_pcode.analysis.bounded_refinement import BoundedCallRefiner
from scripts.function_tracer_pcode.analysis.condition import (
    ConditionTracker,
    ConditionSimplifier,
    ConditionNormalizer,
)
from scripts.function_tracer_pcode.analysis.condition.bitvector import eval_constant_raw
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.analysis.debug import summarize_expression
from scripts.function_tracer_pcode.analysis.failure import (
    ANALYSIS_STATUS_ANALYSIS_EXCEPTION,
    ANALYSIS_STATUS_DECOMPILATION_FAILED,
    ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
    ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
    AnalysisFailure,
)
from scripts.function_tracer_pcode.analysis.signedness import SignednessDetector
from scripts.function_tracer_pcode.analysis.returns.summary_returns import (
    accept_summary_return_candidates,
    attach_quarantined_recurrence_proposal,
)
from scripts.function_tracer_pcode.analysis.effects.api import EFFECT_API
CanonicalLocation = EFFECT_API.models.CanonicalLocation
EffectSummary = EFFECT_API.models.EffectSummary
CallArgumentEvidence = EFFECT_API.models.CallArgumentEvidence
FunctionControlEffectProfile = EFFECT_API.models.FunctionControlEffectProfile
_build_parameter_replacements = EFFECT_API.calls.build_parameter_replacements
_call_argument_evidence_storage_key = EFFECT_API.calls.call_argument_evidence_storage_key
_expression_location_ref = EFFECT_API.locations.expression_location_ref
_expression_reads_location = EFFECT_API.locations.expression_reads_location
_enumerate_constant_expression_branches = EFFECT_API.calls.enumerate_constant_expression_branches
_expression_contains_observed_loads = EFFECT_API.post_state.expression_contains_observed_loads
_iter_expression_nodes = EFFECT_API.post_state.iter_expression_nodes
_materialize_existing_effect_value_carrier = EFFECT_API.post_state.materialize_existing_effect_value_carrier
_strip_materialized_post_state_value_refs = EFFECT_API.post_state.strip_materialized_post_state_value_refs
_expressions_equivalent = EFFECT_API.proofs.expressions_equivalent
_expressions_equivalent_under_conditions = EFFECT_API.proofs.expressions_equivalent_under_conditions
_find_matching_effect_value = EFFECT_API.proofs.find_matching_effect_value
_find_unique_effect_location_for_value = EFFECT_API.locations.find_unique_effect_location_for_value
_resolve_call_argument_expression = EFFECT_API.calls.resolve_call_argument_expression
_resolve_call_target_ref = EFFECT_API.calls.resolve_call_target_ref
_reduce_expression_under_conditions = EFFECT_API.proofs.reduce_expression_under_conditions
_replay_definite_active_effects_for_location = EFFECT_API.proofs.replay_definite_active_effects_for_location
canonicalize_expr_read_location = EFFECT_API.locations.canonicalize_expr_read_location
expression_contains_post_state_reads = EFFECT_API.post_state.expression_contains_post_state_reads
expression_matches_stale_post_state_replay = EFFECT_API.post_state.expression_matches_stale_post_state_replay
lower_post_state_expression_for_smt = EFFECT_API.post_state.lower_post_state_expression_for_smt
materialize_definite_post_state_expression = EFFECT_API.post_state.materialize_definite_post_state_expression
normalize_post_state_expression = EFFECT_API.post_state.normalize_post_state_expression
locations_match = EFFECT_API.locations.locations_match
promote_effect_value_carrier_to_post_state_read = EFFECT_API.post_state.promote_effect_value_carrier_to_post_state_read
promote_effect_value_match_to_post_state_read = EFFECT_API.post_state.promote_effect_value_match_to_post_state_read
promote_observed_loads_to_post_state_reads = EFFECT_API.post_state.promote_observed_loads_to_post_state_reads
resolve_definite_post_state_read_for_location = EFFECT_API.post_state.resolve_definite_post_state_read_for_location
resolve_call_targets = EFFECT_API.calls.resolve_call_targets
rewrite_loads_from_effects = EFFECT_API.post_state.rewrite_loads_from_effects
rewrite_observed_loads_from_effects = EFFECT_API.post_state.rewrite_observed_loads_from_effects
_select_explicit_call_arguments_by_semantic_window = EFFECT_API.calls.select_explicit_call_arguments_by_semantic_window
summarize_store_effects = EFFECT_API.proofs.summarize_store_effects
substitute_condition = EFFECT_API.locations.substitute_condition
substitute_expression = EFFECT_API.locations.substitute_expression
from scripts.function_tracer_pcode.analysis.memory_resolver import concretize_readonly_loads
from scripts.function_tracer_pcode.analysis.recurrence.summarizer import (
    StructuralRecurrenceSummarizer,
)
from scripts.function_tracer_pcode.analysis.switch import build_switch_dispatch_summaries
from scripts.function_tracer_pcode.analysis.session import AnalysisSession
_PCODE_OPCODE_BY_MNEMONIC = {'COPY': 1, 'LOAD': 2, 'STORE': 3, 'BRANCH': 4, 'CBRANCH': 5, 'BRANCHIND': 6, 'CALL': 7, 'CALLIND': 8, 'RETURN': 10, 'INT_ZEXT': 17, 'INT_SEXT': 18, 'MULTIEQUAL': 60, 'INDIRECT': 61, 'PIECE': 62, 'SUBPIECE': 63, 'CAST': 64}
_PCODE_CALL_OPCODES = {_PCODE_OPCODE_BY_MNEMONIC['CALL'], _PCODE_OPCODE_BY_MNEMONIC['CALLIND']}
_PCODE_BRANCHLIKE_OPCODES = {_PCODE_OPCODE_BY_MNEMONIC['BRANCH'], _PCODE_OPCODE_BY_MNEMONIC['CBRANCH'], _PCODE_OPCODE_BY_MNEMONIC['BRANCHIND']}
_PCODE_VALUE_PASSTHROUGH_OPCODES = {_PCODE_OPCODE_BY_MNEMONIC['COPY'], _PCODE_OPCODE_BY_MNEMONIC['CAST'], _PCODE_OPCODE_BY_MNEMONIC['INT_ZEXT'], _PCODE_OPCODE_BY_MNEMONIC['INT_SEXT'], _PCODE_OPCODE_BY_MNEMONIC['SUBPIECE']}
_FUNCTION_PROFILE_RECOGNIZED_PCODE_MNEMONICS = frozenset({'COPY', 'LOAD', 'STORE', 'BRANCH', 'CBRANCH', 'BRANCHIND', 'CALL', 'CALLIND', 'CALLOTHER', 'RETURN', 'INT_EQUAL', 'INT_NOTEQUAL', 'INT_SLESS', 'INT_SLESSEQUAL', 'INT_LESS', 'INT_LESSEQUAL', 'INT_ZEXT', 'INT_SEXT', 'INT_ADD', 'INT_SUB', 'INT_CARRY', 'INT_SCARRY', 'INT_SBORROW', 'INT_2COMP', 'INT_NEGATE', 'INT_XOR', 'INT_AND', 'INT_OR', 'INT_LEFT', 'INT_RIGHT', 'INT_SRIGHT', 'INT_MULT', 'INT_DIV', 'INT_SDIV', 'INT_REM', 'INT_SREM', 'BOOL_NEGATE', 'BOOL_XOR', 'BOOL_AND', 'BOOL_OR', 'FLOAT_EQUAL', 'FLOAT_NOTEQUAL', 'FLOAT_LESS', 'FLOAT_LESSEQUAL', 'FLOAT_NAN', 'FLOAT_ADD', 'FLOAT_DIV', 'FLOAT_MULT', 'FLOAT_SUB', 'FLOAT_NEG', 'FLOAT_ABS', 'FLOAT_SQRT', 'INT2FLOAT', 'FLOAT2FLOAT', 'FLOAT_INT2FLOAT', 'FLOAT_FLOAT2FLOAT', 'FLOAT_TRUNC', 'FLOAT_CEIL', 'FLOAT_FLOOR', 'FLOAT_ROUND', 'TRUNC', 'CEIL', 'FLOOR', 'ROUND', 'MULTIEQUAL', 'INDIRECT', 'PIECE', 'SUBPIECE', 'CAST', 'PTRADD', 'PTRSUB', 'SEGMENTOP', 'CPOOLREF', 'NEW', 'INSERT', 'EXTRACT', 'POPCOUNT', 'LZCOUNT'})
_PHASE2_MEMORY_FREE_SCALAR_PCODE_MNEMONICS = frozenset({'COPY', 'BRANCH', 'CBRANCH', 'RETURN', 'INT_EQUAL', 'INT_NOTEQUAL', 'INT_SLESS', 'INT_SLESSEQUAL', 'INT_LESS', 'INT_LESSEQUAL', 'INT_ZEXT', 'INT_SEXT', 'INT_ADD', 'INT_SUB', 'INT_CARRY', 'INT_SCARRY', 'INT_SBORROW', 'INT_2COMP', 'INT_NEGATE', 'INT_XOR', 'INT_AND', 'INT_OR', 'INT_LEFT', 'INT_RIGHT', 'INT_SRIGHT', 'INT_MULT', 'BOOL_NEGATE', 'BOOL_XOR', 'BOOL_AND', 'BOOL_OR', 'MULTIEQUAL', 'PIECE', 'SUBPIECE', 'CAST', 'POPCOUNT', 'LZCOUNT', 'INSERT', 'EXTRACT'})
_UNSIGNED_COMPARE_TO_SIGNED = {'INT_LESS': 'INT_SLESS', 'INT_LESSEQUAL': 'INT_SLESSEQUAL'}
_SIGNED_COMPARE_TO_UNSIGNED = {'INT_SLESS': 'INT_LESS', 'INT_SLESSEQUAL': 'INT_LESSEQUAL'}

@dataclass
class _TrackedReturnValue:
    """RETURN provenance の逆追跡対象。"""
    varnode: Optional[Any] = None
    storage: Optional[StorageInfo] = None
    producer_op: Optional[Any] = None

@dataclass(frozen=True)
class _EffectRewritePrecision:
    matched_effect_locations: int
    post_state_reads: int
    object_centric_unknowns: int
    opaque_unknowns: int
    downstream_unresolved_values: int
    observed_loads: int
    phi_nodes: int

__all__ = ('ANALYSIS_STATUS_ANALYSIS_EXCEPTION', 'ANALYSIS_STATUS_DECOMPILATION_FAILED', 'ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS', 'ANALYSIS_STATUS_HIGH_FUNCTION_MISSING', 'AddressValueRef', 'AnalysisFailure', 'AnalysisSession', 'Any', 'BOUNDED_CALL_MAX_CASES', 'BOUNDED_CALL_REFINEMENT_ENABLED', 'BOUNDED_CALL_UNROLL_LIMIT', 'BoundedCallRefiner', 'CallArgumentEvidence', 'CallTargetRef', 'CanonicalLocation', 'ComparisonSurface', 'Condition', 'ConditionNormalizer', 'ConditionSMTOracle', 'ConditionSimplifier', 'ConditionTracker', 'DeferredCallInfo', 'DeferredCallRef', 'Dict', 'DivergenceOutcome', 'EFFECT_API', 'EffectSummary', 'Expression', 'ExpressionType', 'FunctionControlEffectProfile', 'FunctionReturnAnalysis', 'Iterable', 'List', 'Mapping', 'Optional', 'PcodeBlockRef', 'PcodeOpRef', 'PcodeTracer', 'PostStateValueRef', 'ReadonlyReductionRef', 'ReturnInfo', 'ReturnOutcome', 'Sequence', 'Set', 'SignednessDetector', 'SignednessResult', 'StorageInfo', 'StructuralKey', 'StructuralRecurrenceSummarizer', 'Tuple', 'UnknownOutcome', 'UnknownValueRef', '_EffectRewritePrecision', '_FUNCTION_PROFILE_RECOGNIZED_PCODE_MNEMONICS', '_PCODE_BRANCHLIKE_OPCODES', '_PCODE_CALL_OPCODES', '_PCODE_OPCODE_BY_MNEMONIC', '_PCODE_VALUE_PASSTHROUGH_OPCODES', '_PHASE2_MEMORY_FREE_SCALAR_PCODE_MNEMONICS', '_SIGNED_COMPARE_TO_UNSIGNED', '_TrackedReturnValue', '_UNSIGNED_COMPARE_TO_SIGNED', '_build_parameter_replacements', '_call_argument_evidence_storage_key', '_enumerate_constant_expression_branches', '_expression_contains_observed_loads', '_expression_location_ref', '_expression_reads_location', '_expressions_equivalent', '_expressions_equivalent_under_conditions', '_find_matching_effect_value', '_find_unique_effect_location_for_value', '_iter_expression_nodes', '_materialize_existing_effect_value_carrier', '_reduce_expression_under_conditions', '_replay_definite_active_effects_for_location', '_resolve_call_argument_expression', '_resolve_call_target_ref', '_select_explicit_call_arguments_by_semantic_window', '_strip_materialized_post_state_value_refs', 'accept_summary_return_candidates', 'attach_quarantined_recurrence_proposal', 'build_switch_dispatch_summaries', 'canonicalize_expr_read_location', 'cast', 'cmp_to_key', 'coerce_call_target_ref', 'concretize_readonly_loads', 'contextmanager', 'dataclass', 'eval_constant_raw', 'expression_contains_post_state_reads', 'expression_contains_unsupported_smt_ops', 'expression_key_safe', 'expression_matches_stale_post_state_replay', 'get_declared_type_signedness', 'hashlib', 'is_void_data_type', 'locations_match', 'lower_post_state_expression_for_smt', 'materialize_definite_post_state_expression', 'normalize_post_state_expression', 'promote_effect_value_carrier_to_post_state_read', 'promote_effect_value_match_to_post_state_read', 'promote_observed_loads_to_post_state_reads', 're', 'replace', 'resolve_call_targets', 'resolve_definite_post_state_read_for_location', 'resolve_pcode_intrinsic', 'rewrite_loads_from_effects', 'rewrite_observed_loads_from_effects', 'substitute_condition', 'substitute_expression', 'summarize_expression', 'summarize_store_effects')
