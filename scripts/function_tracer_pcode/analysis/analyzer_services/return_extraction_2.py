"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.analyzer``."""

from __future__ import annotations

from typing import Any, List, Optional, Set, Tuple
from ._shared import (
    Condition,
    ConditionSimplifier,
    ReturnInfo,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
    expression_contains_post_state_reads,
    lower_post_state_expression_for_smt,
    replace,
)

def _impl__merge_return_info_pair(
    self,
    left: ReturnInfo,
    right: ReturnInfo,
    all_infos: Optional[List[ReturnInfo]] = None,
    left_index: Optional[int] = None,
    right_index: Optional[int] = None,
) -> Optional[ReturnInfo]:
    if self._return_site_key(left) != self._return_site_key(right):
        return None
    if not _expressions_equivalent(left.value, right.value):
        return None

    shared_conditions, left_residual, right_residual = self._partition_return_conditions(
        left.conditions,
        right.conditions,
    )

    if not left_residual and not right_residual:
        return self._make_merged_return_info(left, right, shared_conditions, "deduplicated identical return case")

    if (
        self._condition_sets_are_complementary(left_residual, right_residual)
        and self._can_safely_collapse_complementary_return_pair(
            left,
            right,
            shared_conditions,
            all_infos or [],
            left_index,
            right_index,
        )
    ):
        return self._make_merged_return_info(
            left,
            right,
            shared_conditions,
            "collapsed complementary return cases",
        )

    return None

def _impl__can_safely_collapse_complementary_return_pair(
    self,
    left: ReturnInfo,
    right: ReturnInfo,
    merged_conditions: List[Condition],
    all_infos: List[ReturnInfo],
    left_index: Optional[int],
    right_index: Optional[int],
) -> bool:
    current_effect_summary = self._current_effect_summary
    if (
        current_effect_summary is not None
        and (
            expression_contains_post_state_reads(left.value)
            or expression_contains_post_state_reads(right.value)
        )
    ):
        lowered_left = lower_post_state_expression_for_smt(
            left.value,
            left.conditions,
            current_effect_summary.effects,
            self._current_parameters,
        )
        lowered_right = lower_post_state_expression_for_smt(
            right.value,
            right.conditions,
            current_effect_summary.effects,
            self._current_parameters,
        )
        if (
            lowered_left is None
            or lowered_right is None
            or expression_contains_post_state_reads(lowered_left)
            or expression_contains_post_state_reads(lowered_right)
        ):
            return False
        if not _expressions_equivalent_under_conditions(
            lowered_left,
            lowered_right,
            merged_conditions,
            self._current_parameters,
        ):
            if self.debug:
                self._debug_print(
                    "skipping complementary return-case collapse because symbolic post-state "
                    "lowers differently across branches: "
                    f"left={self._debug_expr_summary(lowered_left)} "
                    f"right={self._debug_expr_summary(lowered_right)}"
                )
            return False

    if not all_infos:
        return True

    merged_scope = ConditionSimplifier.simplify_conditions_object_centric(list(merged_conditions))
    for index, other in enumerate(all_infos):
        if index == left_index or index == right_index:
            continue
        if self._return_site_key(other) != self._return_site_key(left):
            continue
        if _expressions_equivalent(other.value, left.value):
            continue

        overlap_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(merged_scope) + list(other.conditions)
        )
        if ConditionSimplifier.object_centric_is_contradiction(overlap_conditions):
            continue

        if self.debug:
            cond_dump = [
                ConditionSimplifier.get_simplified_condition_string(cond)
                for cond in overlap_conditions
            ]
            self._debug_print(
                "skipping complementary return-case collapse due to overlapping "
                f"different-valued case: value={self._debug_expr_summary(other.value)} "
                f"conditions={cond_dump}"
            )
        return False

    return True

def _impl__partition_return_conditions(
    self,
    left_conditions: List[Condition],
    right_conditions: List[Condition],
) -> Tuple[List[Condition], List[Condition], List[Condition]]:
    shared: List[Condition] = []
    right_used: Set[int] = set()
    left_residual: List[Condition] = []

    for left_cond in left_conditions:
        match_index = None
        for index, right_cond in enumerate(right_conditions):
            if index in right_used:
                continue
            if left_cond.equals(right_cond):
                match_index = index
                break
        if match_index is None:
            left_residual.append(left_cond)
            continue
        right_used.add(match_index)
        shared.append(left_cond)

    right_residual = [
        cond for index, cond in enumerate(right_conditions) if index not in right_used
    ]
    return (
        ConditionSimplifier.simplify_conditions_object_centric(shared),
        ConditionSimplifier.simplify_conditions_object_centric(left_residual),
        ConditionSimplifier.simplify_conditions_object_centric(right_residual),
    )

def _impl__make_merged_return_info(
    self,
    primary: ReturnInfo,
    secondary: ReturnInfo,
    merged_conditions: List[Condition],
    reason: str,
) -> ReturnInfo:
    normalized_conditions = ConditionSimplifier.simplify_conditions_object_centric(
        list(merged_conditions)
    )
    if self.debug:
        cond_dump = [
            ConditionSimplifier.get_simplified_condition_string(cond)
            for cond in normalized_conditions
        ]
        self._debug_print(
            f"{reason}: value={self._debug_expr_summary(primary.value)} conditions={cond_dump}"
        )
    return replace(
        primary,
        value=primary.value,
        conditions=normalized_conditions,
        branch_index=self._min_branch_index(primary.branch_index, secondary.branch_index),
        summary_candidate_source_key=self._merge_return_info_summary_candidate_source_keys(
            primary,
            secondary,
        ),
    )

def _impl__merge_return_info_summary_candidate_source_keys(
    self,
    primary: ReturnInfo,
    secondary: ReturnInfo,
) -> Optional[Tuple[Any, ...]]:
    primary_key = getattr(primary, "summary_candidate_source_key", None)
    secondary_key = getattr(secondary, "summary_candidate_source_key", None)
    if primary_key is None:
        return secondary_key
    if secondary_key is None or secondary_key == primary_key:
        return primary_key
    candidate_keys = tuple(
        sorted(
            self._candidate_phi_origin_keys_from_summary_source_key(primary_key)
            | self._candidate_phi_origin_keys_from_summary_source_key(secondary_key),
            key=repr,
        )
    )
    return_keys = tuple(
        sorted(
            self._return_phi_origin_keys_from_summary_source_key(primary_key)
            | self._return_phi_origin_keys_from_summary_source_key(secondary_key),
            key=repr,
        )
    )
    proof_sources = tuple(
        key for key in (primary_key, secondary_key)
        if self._candidate_phi_origin_keys_from_summary_source_key(key)
        or self._return_phi_origin_keys_from_summary_source_key(key)
    )
    discovery_only_sources = tuple(
        key for key in (primary_key, secondary_key)
        if key not in proof_sources
    )
    items: List[Tuple[Any, ...]] = []
    if candidate_keys:
        items.append(("candidate_phi_origin_keys", candidate_keys))
    if return_keys:
        items.append(("return_phi_origin_keys", return_keys))
    if proof_sources:
        items.append(("proof_candidate_sources", proof_sources))
    if discovery_only_sources:
        items.append(("discovery_only_sources", discovery_only_sources))
    return ("merged_return_info_sources", *items)
