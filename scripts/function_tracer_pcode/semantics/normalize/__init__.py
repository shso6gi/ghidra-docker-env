# -*- coding: utf-8 -*-
"""式正規化モジュール（意味論保存変形）"""

from scripts.function_tracer_pcode.semantics.normalize.core import normalize_expression
from scripts.function_tracer_pcode.semantics.normalize.context import (
    NormalizationContext,
    NormalizationSettings,
    RuleApplication,
)
from scripts.function_tracer_pcode.semantics.normalize.policy import (
    extract_min_excluded_params,
    extract_upper_bound_facts,
)
from scripts.function_tracer_pcode.semantics.normalize.facts import extract_sign_facts
from scripts.function_tracer_pcode.semantics.normalize.fact_types import SignFacts
from scripts.function_tracer_pcode.semantics.normalize.division_signedness_guarded import (
    normalize_udiv_with_guard,
    contains_udiv,
)
from scripts.function_tracer_pcode.semantics.normalize.structural import (
    are_structurally_equivalent,
    get_structural_summary,
)

__all__ = [
    'normalize_expression',
    'NormalizationContext',
    'NormalizationSettings',
    'RuleApplication',
    'extract_min_excluded_params',
    'extract_upper_bound_facts',
    'extract_sign_facts',
    'SignFacts',
    'normalize_udiv_with_guard',
    'contains_udiv',
    'are_structurally_equivalent',
    'get_structural_summary',
]
