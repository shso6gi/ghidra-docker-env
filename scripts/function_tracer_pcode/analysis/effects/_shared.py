"""Shared dependencies for effect services."""

from typing import Dict, Tuple
from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.condition.normalizer import ConditionNormalizer
from scripts.function_tracer_pcode.analysis.memory_resolver import concretize_readonly_loads
_EFFECT_ORDER_UNAVAILABLE_REASON = 'effect_order_unavailable'
# Issue #104: a memory write whose target is (possibly) observable but could not
# be canonicalised (stripped global, unresolved pointer, missing exit state).
_EFFECT_STORE_LOCATION_UNMODELED_REASON = 'effect_store_location_unmodeled'
# Issue #104: a modelled global effect value / observed return reads another
# global; reads of writable globals carry no cross-binary identity yet.
_EFFECT_GLOBAL_READ_IDENTITY_REASON = 'effect_global_read_identity_unavailable'
# Issue #104 (Gap 5): observable store effects exist but the return + effect
# comparison surface could not be composed; the return value alone is not a
# complete observation.
_EFFECT_SURFACE_COMPOSITION_REASON = 'effect_surface_composition_incomplete'
_UNKNOWN_EFFECT_ORDER_KEY = -1
from scripts.function_tracer_pcode.analysis.effects.models import (
    EffectOrderUnavailable,
    StoreEffectProvenance,
    StoreEffect,
    UnsupportedCallEffectRef,
    CallTargetResolutionEvidence,
    CallSiteEffectSummaryEvidence,
    FunctionControlEffectProfile,
    EffectSummary,
    CallArgumentEvidence,
    CallArgumentWidthEvidence,
)
_MAX_CALL_ARGUMENT_VARIANTS = 16
_FIXED_PREFIX_FORMAT_CALL_TARGETS: Dict[str, Tuple[int, int]] = {'printf': (1, 0), 'isoc99_printf': (1, 0), 'printf_chk': (2, 1), 'fprintf': (2, 1), 'isoc99_fprintf': (2, 1), 'sprintf': (2, 1), 'isoc99_sprintf': (2, 1), 'snprintf': (3, 2), 'isoc99_snprintf': (3, 2), 'fprintf_chk': (3, 2), 'sprintf_chk': (4, 3), 'snprintf_chk': (5, 4)}

__all__ = ('CallArgumentEvidence', 'CallArgumentWidthEvidence', 'CallSiteEffectSummaryEvidence', 'CallTargetResolutionEvidence', 'ConditionNormalizer', 'ConditionSimplifier', 'EffectOrderUnavailable', 'EffectSummary', 'FunctionControlEffectProfile', 'StoreEffect', 'StoreEffectProvenance', 'UnsupportedCallEffectRef', '_EFFECT_ORDER_UNAVAILABLE_REASON', '_EFFECT_STORE_LOCATION_UNMODELED_REASON', '_EFFECT_GLOBAL_READ_IDENTITY_REASON', '_EFFECT_SURFACE_COMPOSITION_REASON', '_FIXED_PREFIX_FORMAT_CALL_TARGETS', '_MAX_CALL_ARGUMENT_VARIANTS', '_UNKNOWN_EFFECT_ORDER_KEY', 'concretize_readonly_loads')
