"""Standalone recurrence-summary data models."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Optional, Tuple

from scripts.function_tracer_pcode.core import Condition, Expression, LoopSideEffectProfileRef

@dataclass(frozen=True)
class CountedLoopInduction:
    phi_op: object
    phi_output: object
    init_expr: Expression
    backedge_index: int
    step: int
    placeholder: Expression
    signed_guard: bool
    init_index: Optional[int] = None
    backedge_indices: Tuple[int, ...] = ()

@dataclass(frozen=True)
class CountedLoopAccumulator:
    phi_op: Optional[object]
    phi_output: Optional[object]
    init_expr: Expression
    backedge_index: int
    placeholder: Expression
    member_outputs: Tuple[object, ...] = ()
    member_placeholders: Tuple[Expression, ...] = ()
    update_varnode: Optional[object] = None
    update_block: Optional[object] = None
    init_index: Optional[int] = None
    backedge_indices: Tuple[int, ...] = ()

@dataclass(frozen=True)
class CountedLoopGuard:
    condition_expr: Expression
    bound_expr: Expression
    continue_on_true: bool
    body_block: object
    exit_block: object
    signed_comparison: bool
    guard_op: Optional[object] = None
    entry_condition_expr: Optional[Expression] = None
    latch_block: Optional[object] = None

@dataclass(frozen=True)
class CountedLoopUpdateCase:
    conditions: Tuple[Condition, ...]
    update_expr: Expression
    delta_expr: Expression

@dataclass(frozen=True)
class CountedStateTransitionLoopModel:
    induction: CountedLoopInduction
    accumulator: CountedLoopAccumulator
    guard: CountedLoopGuard
    transition_cases: Tuple[Tuple[Tuple[Condition, ...], Expression], ...]
    side_effect_profile: LoopSideEffectProfileRef

@dataclass(frozen=True)
class StateTransitionLoopModel:
    header_block: object
    body_block: object
    exit_block: object
    state_phi_op: object
    state_phi_output: object
    state_init_expr: Expression
    state_placeholder: Expression
    state_guard_expr: Expression
    state_transition_expr: Expression
    accumulator_phi_op: object
    accumulator_phi_output: object
    accumulator_init_expr: Expression
    accumulator_delta_expr: Expression
    accumulator_placeholder: Expression
    continue_on_true: bool
    loop_blocks: Tuple[object, ...]
    state_phi_init_index: int = 0
    accumulator_phi_init_index: int = 0
    state_phi_backedge_indices: Tuple[int, ...] = ()
    accumulator_phi_backedge_indices: Tuple[int, ...] = ()

@dataclass(frozen=True)
class ResidueLoopCase:
    modulus: int
    residue: int
    affine: Tuple[int, int]
    bias_expr: Optional[Expression] = None
    affine_from_readonly_literal: bool = False
    affine_from_address_literal: bool = False

@dataclass(frozen=True)
class ReadonlyRoundedCountCandidate:
    rounded_varnode: object
    lane_count: int
    start_index: int = 0
    tail_start_index_delta: int = 0
    tail_index_source_varnode: Optional[object] = None

@dataclass(frozen=True)
class ReadonlyAccumulatorPhiCandidate:
    phi_op: object
    init_varnode: object
    back_varnode: object
    back_def: object
    load_progressions: Tuple[Dict[str, object], ...]
    reduction_kind: str = "memory_sum"
    return_projection_kind: str = "identity"

@dataclass(frozen=True)
class ReadonlyAffineProgressionLiteral:
    step: int
    lane_base: int
