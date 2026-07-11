"""Shared dependencies for effect services."""

from dataclasses import dataclass, field
from itertools import product
import re
from typing import Callable, ClassVar, Dict, FrozenSet, Iterable, Iterator, List, Mapping, Optional, Sequence, Set, Tuple, overload
from ...model import AddressValueRef, CallTargetRef, CanonicalLocation, Condition, Expression, ExpressionType, LocationBaseRef, LocationStep, ObservedMemoryReadRef, PostStateReadRef, PostStateSnapshotRef, PostStateValueRef, PTRADD_OPCODE, PTRSUB_OPCODE, PcodeBlockRef, PcodeOpRef, StorageInfo, coerce_call_target_ref, expression_key_or_identity, expression_provenance_key, expression_key_safe
from ...model.signature import get_declared_type_size_bytes, is_integral_data_type, is_pointer_data_type, is_undefined_data_type
from ..condition import ConditionSimplifier
from ..condition.normalizer import ConditionNormalizer
from ..memory_resolver import concretize_readonly_loads
_EFFECT_ORDER_UNAVAILABLE_REASON = 'effect_order_unavailable'
_UNKNOWN_EFFECT_ORDER_KEY = -1
from ..effect_models import EffectOrderUnavailable, StoreEffectProvenance, StoreEffect, UnsupportedCallEffectRef, CallTargetResolutionEvidence, CallSiteEffectSummaryEvidence, FunctionControlEffectProfile, EffectSummary, CallArgumentEvidence, CallArgumentWidthEvidence
_MAX_CALL_ARGUMENT_VARIANTS = 16
_FIXED_PREFIX_FORMAT_CALL_TARGETS: Dict[str, Tuple[int, int]] = {'printf': (1, 0), 'isoc99_printf': (1, 0), 'printf_chk': (2, 1), 'fprintf': (2, 1), 'isoc99_fprintf': (2, 1), 'sprintf': (2, 1), 'isoc99_sprintf': (2, 1), 'snprintf': (3, 2), 'isoc99_snprintf': (3, 2), 'fprintf_chk': (3, 2), 'sprintf_chk': (4, 3), 'snprintf_chk': (5, 4)}

__all__ = ('AddressValueRef', 'CallArgumentEvidence', 'CallArgumentWidthEvidence', 'CallSiteEffectSummaryEvidence', 'CallTargetRef', 'CallTargetResolutionEvidence', 'Callable', 'CanonicalLocation', 'ClassVar', 'Condition', 'ConditionNormalizer', 'ConditionSimplifier', 'Dict', 'EffectOrderUnavailable', 'EffectSummary', 'Expression', 'ExpressionType', 'FrozenSet', 'FunctionControlEffectProfile', 'Iterable', 'Iterator', 'List', 'LocationBaseRef', 'LocationStep', 'Mapping', 'ObservedMemoryReadRef', 'Optional', 'PTRADD_OPCODE', 'PTRSUB_OPCODE', 'PcodeBlockRef', 'PcodeOpRef', 'PostStateReadRef', 'PostStateSnapshotRef', 'PostStateValueRef', 'Sequence', 'Set', 'StorageInfo', 'StoreEffect', 'StoreEffectProvenance', 'Tuple', 'UnsupportedCallEffectRef', '_EFFECT_ORDER_UNAVAILABLE_REASON', '_FIXED_PREFIX_FORMAT_CALL_TARGETS', '_MAX_CALL_ARGUMENT_VARIANTS', '_UNKNOWN_EFFECT_ORDER_KEY', 'coerce_call_target_ref', 'concretize_readonly_loads', 'dataclass', 'expression_key_or_identity', 'expression_key_safe', 'expression_provenance_key', 'field', 'get_declared_type_size_bytes', 'is_integral_data_type', 'is_pointer_data_type', 'is_undefined_data_type', 'overload', 'product', 're')
