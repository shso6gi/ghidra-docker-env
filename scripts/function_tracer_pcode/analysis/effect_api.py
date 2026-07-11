"""Small public service surface consumed by ``ReturnAnalyzer``.

Legacy names remain exported by :mod:`effect_summary`; new analysis code uses
these grouped services instead of importing dozens of implementation symbols.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from . import effect_summary as _effect


@dataclass(frozen=True)
class EffectModelAPI:
    CanonicalLocation: Any = _effect.CanonicalLocation
    EffectSummary: Any = _effect.EffectSummary
    CallArgumentEvidence: Any = _effect.CallArgumentEvidence
    FunctionControlEffectProfile: Any = _effect.FunctionControlEffectProfile


@dataclass(frozen=True)
class EffectLocationAPI:
    expression_location_ref: Any = _effect._expression_location_ref
    expression_reads_location: Any = _effect._expression_reads_location
    find_unique_effect_location_for_value: Any = _effect._find_unique_effect_location_for_value
    canonicalize_expr_read_location: Any = _effect.canonicalize_expr_read_location
    locations_match: Any = _effect.locations_match
    substitute_condition: Any = _effect.substitute_condition
    substitute_expression: Any = _effect.substitute_expression


@dataclass(frozen=True)
class EffectCallAPI:
    build_parameter_replacements: Any = _effect._build_parameter_replacements
    call_argument_evidence_storage_key: Any = _effect._call_argument_evidence_storage_key
    enumerate_constant_expression_branches: Any = _effect._enumerate_constant_expression_branches
    resolve_call_argument_expression: Any = _effect._resolve_call_argument_expression
    resolve_call_target_ref: Any = _effect._resolve_call_target_ref
    select_explicit_call_arguments_by_semantic_window: Any = (
        _effect._select_explicit_call_arguments_by_semantic_window
    )
    resolve_call_targets: Any = _effect.resolve_call_targets


@dataclass(frozen=True)
class EffectPostStateAPI:
    expression_contains_observed_loads: Any = _effect._expression_contains_observed_loads
    iter_expression_nodes: Any = _effect._iter_expression_nodes
    materialize_existing_effect_value_carrier: Any = (
        _effect._materialize_existing_effect_value_carrier
    )
    strip_materialized_post_state_value_refs: Any = (
        _effect._strip_materialized_post_state_value_refs
    )
    expression_contains_post_state_reads: Any = _effect.expression_contains_post_state_reads
    expression_matches_stale_post_state_replay: Any = (
        _effect.expression_matches_stale_post_state_replay
    )
    lower_post_state_expression_for_smt: Any = _effect.lower_post_state_expression_for_smt
    materialize_definite_post_state_expression: Any = (
        _effect.materialize_definite_post_state_expression
    )
    normalize_post_state_expression: Any = _effect.normalize_post_state_expression
    promote_effect_value_carrier_to_post_state_read: Any = (
        _effect.promote_effect_value_carrier_to_post_state_read
    )
    promote_effect_value_match_to_post_state_read: Any = (
        _effect.promote_effect_value_match_to_post_state_read
    )
    promote_observed_loads_to_post_state_reads: Any = (
        _effect.promote_observed_loads_to_post_state_reads
    )
    resolve_definite_post_state_read_for_location: Any = (
        _effect.resolve_definite_post_state_read_for_location
    )
    rewrite_loads_from_effects: Any = _effect.rewrite_loads_from_effects
    rewrite_observed_loads_from_effects: Any = _effect.rewrite_observed_loads_from_effects


@dataclass(frozen=True)
class EffectProofAPI:
    expressions_equivalent: Any = _effect._expressions_equivalent
    expressions_equivalent_under_conditions: Any = (
        _effect._expressions_equivalent_under_conditions
    )
    find_matching_effect_value: Any = _effect._find_matching_effect_value
    reduce_expression_under_conditions: Any = _effect._reduce_expression_under_conditions
    replay_definite_active_effects_for_location: Any = (
        _effect._replay_definite_active_effects_for_location
    )
    summarize_store_effects: Any = _effect.summarize_store_effects


@dataclass(frozen=True)
class EffectAnalysisAPI:
    models: EffectModelAPI = EffectModelAPI()
    locations: EffectLocationAPI = EffectLocationAPI()
    calls: EffectCallAPI = EffectCallAPI()
    post_state: EffectPostStateAPI = EffectPostStateAPI()
    proofs: EffectProofAPI = EffectProofAPI()


EFFECT_API = EffectAnalysisAPI()
