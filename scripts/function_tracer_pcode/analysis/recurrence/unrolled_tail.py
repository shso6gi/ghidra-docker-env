"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence.summarizer``."""

from __future__ import annotations

from typing import Any, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core import Condition, ExpressionType
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    CountedLoopUpdateCase,
    ResidueLoopCase,
)

def _impl__extract_residue_loop_cases(
    self,
    cases: Sequence[CountedLoopUpdateCase],
    counter_name: str,
    *,
    function_body_ranges: Sequence[Tuple[int, int]] = (),
) -> Optional[Tuple[ResidueLoopCase, ...]]:
    if not cases:
        return None
    if len(cases) == 1 and not cases[0].conditions:
        affine_case = self._extract_affine_loop_case(cases[0].delta_expr, counter_name)
        if affine_case is None:
            return None
        affine, bias_expr = affine_case
        return (
            ResidueLoopCase(
                modulus=1,
                residue=0,
                affine=affine,
                bias_expr=bias_expr,
                affine_from_readonly_literal=self._expression_contains_readonly_literal_access(
                    cases[0].delta_expr
                ),
                affine_from_address_literal=self._expression_contains_address_literal_access(
                    cases[0].delta_expr,
                    function_body_ranges=function_body_ranges,
                ),
            ),
        )

    residue_cases: List[ResidueLoopCase] = []
    modulus = None
    seen_residues = set()
    for case in cases:
        affine_case = self._extract_affine_loop_case(case.delta_expr, counter_name)
        if affine_case is None:
            return None
        affine, bias_expr = affine_case
        residue_info = self._extract_exact_residue_case(case.conditions, counter_name)
        if residue_info is None:
            return None
        case_modulus, residue = residue_info
        if modulus is None:
            modulus = case_modulus
        if modulus != case_modulus:
            return None
        if residue in seen_residues:
            return None
        seen_residues.add(residue)
        residue_cases.append(
            ResidueLoopCase(
                modulus=case_modulus,
                residue=residue,
                affine=affine,
                bias_expr=bias_expr,
                affine_from_readonly_literal=self._expression_contains_readonly_literal_access(
                    case.delta_expr
                ),
                affine_from_address_literal=self._expression_contains_address_literal_access(
                    case.delta_expr,
                    function_body_ranges=function_body_ranges,
                ),
            )
        )
    if modulus is None or seen_residues != set(range(modulus)):
        return None
    return tuple(sorted(residue_cases, key=lambda item: item.residue))

def _impl__extract_exact_residue_case(
    self,
    conditions: Sequence[Condition],
    counter_name: str,
) -> Optional[Tuple[int, int]]:
    residue_cases = []
    for condition in conditions or []:
        residue = self._condition_to_exact_residue(condition, counter_name)
        if residue is not None:
            residue_cases.append(residue)
            continue
        if self._condition_mentions_counter(condition, counter_name):
            return None
    if not residue_cases:
        return None
    first = residue_cases[0]
    if any(item != first for item in residue_cases[1:]):
        return None
    return first

def _impl__condition_to_exact_residue(
    self,
    condition: Condition,
    counter_name: str,
) -> Optional[Tuple[int, int]]:
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None
    if expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
        return None

    is_equal = expr.operator == "INT_EQUAL"
    if condition.negated:
        is_equal = not is_equal

    bitand = None
    residue_value = None
    if self._raw_constant_value(expr.operands[0]) is not None:
        bitand = expr.operands[1]
        residue_value = self._raw_constant_value(expr.operands[0])
    elif self._raw_constant_value(expr.operands[1]) is not None:
        bitand = expr.operands[0]
        residue_value = self._raw_constant_value(expr.operands[1])
    if bitand is None or residue_value is None:
        return None
    if bitand.expr_type != ExpressionType.BINARY_OP or bitand.operator != "INT_AND" or len(bitand.operands) != 2:
        return None

    counter_expr = None
    mask_value = None
    if self._raw_constant_value(bitand.operands[0]) is not None and self._expr_matches_counter_placeholder(bitand.operands[1], counter_name):
        mask_value = self._raw_constant_value(bitand.operands[0])
        counter_expr = bitand.operands[1]
    elif self._raw_constant_value(bitand.operands[1]) is not None and self._expr_matches_counter_placeholder(bitand.operands[0], counter_name):
        mask_value = self._raw_constant_value(bitand.operands[1])
        counter_expr = bitand.operands[0]
    if counter_expr is None or mask_value is None:
        return None
    if mask_value <= 0 or (mask_value & (mask_value + 1)) != 0:
        return None

    modulus = int(mask_value) + 1
    residue = int(residue_value) & int(mask_value)
    if is_equal:
        return modulus, residue
    if modulus == 2:
        return modulus, residue ^ 1
    return None

def _impl__has_scalar_tail_from_rounded_count(
    self,
    all_ops: Sequence[object],
    pointer_param: dict,
    count_param: dict,
    rounded_vn,
    *,
    element_size: int,
    start_offset: int = 0,
    start_index: int = 0,
    max_unrolled_terms: int = 0,
    tail_index_source_varnode=None,
    lane_count: Optional[int] = None,
) -> bool:
    tail_starts = self._tail_start_varnodes_from_rounded_count(
        all_ops,
        pointer_param,
        rounded_vn,
        element_size=element_size,
        start_offset=start_offset,
        tail_index_source_varnode=tail_index_source_varnode,
        lane_count=lane_count,
    )
    if not tail_starts:
        self._debug(
            "Declined vectorized readonly prefix-sum tail: "
            f"no tail-start varnode for start_offset={start_offset}"
        )
        return False

    for op in all_ops:
        if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
            continue
        phi_output = getattr(op, "getOutput", lambda: None)()
        if phi_output is None:
            continue
        input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
        if not any(
            any(
                self._same_varnode_value(self._follow_passthrough_varnode(op.getInput(index)), tail_start)
                for tail_start in tail_starts
            )
            for index in range(input_count)
        ):
            continue
        if not self._phi_has_pointer_step(all_ops, phi_output, step_bytes=int(element_size)):
            self._debug(
                "Declined vectorized readonly prefix-sum tail PHI: "
                f"no +{element_size} pointer step for phi={self._varnode_cache_key(phi_output)}"
            )
            continue
        if not self._tail_load_contributes_additively_to_return(
            all_ops,
            phi_output,
            element_size=element_size,
        ):
            self._debug(
                "Declined vectorized readonly prefix-sum tail PHI: "
                f"tail load does not flow additively for phi={self._varnode_cache_key(phi_output)}"
            )
            continue
        if not (
            self._has_scalar_tail_bound_to_count(
                all_ops,
                phi_output,
                pointer_param,
                count_param,
                element_size=element_size,
            )
            or self._has_scalar_tail_countdown_from_count_minus_rounded(
                all_ops,
                rounded_vn,
                count_param,
                start_index=start_index,
            )
        ):
            self._debug(
                "Declined vectorized readonly prefix-sum tail PHI: "
                f"tail bound not tied to count for phi={self._varnode_cache_key(phi_output)}"
            )
            continue
        return True
    if self._has_unrolled_scalar_tail_from_rounded_count(
        all_ops,
        tail_starts,
        count_param,
        element_size=element_size,
        max_terms=max_unrolled_terms,
        tail_index_source_varnode=tail_index_source_varnode,
        lane_count=lane_count,
    ):
        return True
    return False

def _impl__tail_load_contributes_additively_to_return(
    self,
    all_ops: Sequence[object],
    tail_phi,
    *,
    element_size: int,
) -> bool:
    for load_op in all_ops:
        if getattr(load_op, "getMnemonic", lambda: None)() != "LOAD":
            continue
        if int(getattr(load_op, "getNumInputs", lambda: 0)() or 0) < 2:
            continue
        address = self._follow_passthrough_varnode(load_op.getInput(1))
        if not self._same_varnode_value(address, tail_phi):
            continue
        output = getattr(load_op, "getOutput", lambda: None)()
        if output is None:
            continue
        load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
        if load_size != int(element_size):
            continue
        if self._load_lanes_flow_additively_to_return(
            output,
            load_size=load_size,
            element_size=element_size,
        ):
            return True
    return False

def _impl__has_unrolled_scalar_tail_from_rounded_count(
    self,
    all_ops: Sequence[object],
    tail_starts: Sequence[object],
    count_param: dict,
    *,
    element_size: int,
    max_terms: int,
    tail_index_source_varnode=None,
    lane_count: Optional[int] = None,
) -> bool:
    """Recognize a finite scalar tail emitted as guarded straight-line loads."""

    if int(max_terms) <= 0 or not tail_starts:
        return False
    if not self._unrolled_tail_count_guards_are_object_linked(
        all_ops,
        tail_starts,
        count_param,
        max_terms=int(max_terms),
        tail_index_source_varnode=tail_index_source_varnode,
        lane_count=lane_count,
    ):
        self._debug("Declined vectorized readonly prefix-sum tail: unrolled tail guards are incomplete")
        return False

    covered_offsets = set()
    for load_op in all_ops:
        if getattr(load_op, "getMnemonic", lambda: None)() != "LOAD":
            continue
        if int(getattr(load_op, "getNumInputs", lambda: 0)() or 0) < 2:
            continue
        output = getattr(load_op, "getOutput", lambda: None)()
        if output is None:
            continue
        load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
        if load_size != int(element_size):
            continue
        address = self._follow_passthrough_varnode(load_op.getInput(1))
        term_index = None
        for tail_start in tail_starts:
            byte_offset = self._byte_offset_from_pointer_like(address, tail_start)
            if byte_offset is None:
                continue
            if int(byte_offset) % int(element_size) != 0:
                continue
            candidate_index = int(byte_offset) // int(element_size)
            if 0 <= candidate_index < int(max_terms):
                term_index = candidate_index
                break
        if term_index is None:
            continue
        if not self._load_lanes_flow_additively_to_any_return(
            output,
            load_size=load_size,
            element_size=element_size,
        ):
            continue
        covered_offsets.add(int(term_index))
    expected_offsets = set(range(int(max_terms)))
    if covered_offsets != expected_offsets:
        self._debug(
            "Declined vectorized readonly prefix-sum tail: "
            f"unrolled tail load coverage={tuple(sorted(covered_offsets))} "
            f"expected={tuple(sorted(expected_offsets))}"
        )
        return False
    return True

def _impl__unrolled_tail_count_guards_are_object_linked(
    self,
    all_ops: Sequence[object],
    tail_starts: Sequence[object],
    count_param: dict,
    *,
    max_terms: int,
    tail_index_source_varnode=None,
    lane_count: Optional[int] = None,
) -> bool:
    if int(max_terms) <= 0:
        return False
    if tail_index_source_varnode is not None and lane_count is not None:
        if not self._has_zero_tail_residue_guard(all_ops, tail_index_source_varnode, lane_count):
            return False
    tail_index_vns = self._tail_index_varnodes_from_tail_starts(tail_starts)
    if not tail_index_vns:
        return False
    required_cutoffs = set(range(1, int(max_terms)))
    if not required_cutoffs:
        return True
    proven_cutoffs = set()
    compare_ops = {
        "INT_EQUAL",
        "INT_NOTEQUAL",
        "INT_LESS",
        "INT_LESSEQUAL",
        "INT_SLESS",
        "INT_SLESSEQUAL",
    }
    for op in all_ops:
        if getattr(op, "getMnemonic", lambda: None)() not in compare_ops:
            continue
        if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
            continue
        left = self._follow_passthrough_varnode(op.getInput(0))
        right = self._follow_passthrough_varnode(op.getInput(1))
        if self._varnode_matches_parameter(left, count_param):
            cutoff = self._tail_index_plus_constant_delta(right, tail_index_vns)
            if cutoff in required_cutoffs:
                proven_cutoffs.add(int(cutoff))
        if self._varnode_matches_parameter(right, count_param):
            cutoff = self._tail_index_plus_constant_delta(left, tail_index_vns)
            if cutoff in required_cutoffs:
                proven_cutoffs.add(int(cutoff))
    return proven_cutoffs == required_cutoffs

def _impl__tail_index_varnodes_from_tail_starts(self, tail_starts: Sequence[object]) -> Tuple[object, ...]:
    indices: List[object] = []
    for tail_start in tail_starts or ():
        candidate = self._follow_passthrough_varnode(tail_start)
        def_op = getattr(candidate, "getDef", lambda: None)()
        if def_op is None:
            continue
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
            indices.append(self._follow_passthrough_varnode(def_op.getInput(1)))
    unique: List[object] = []
    seen = set()
    for index_vn in indices:
        key = self._varnode_cache_key(index_vn)
        if key in seen:
            continue
        seen.add(key)
        unique.append(index_vn)
    return tuple(unique)

def _impl__tail_index_plus_constant_delta(
    self,
    candidate_vn,
    tail_index_vns: Sequence[object],
) -> Optional[int]:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    for tail_index in tail_index_vns or ():
        if self._same_varnode_value(candidate_vn, tail_index):
            return 0
        delta = self._counter_plus_constant_delta(candidate_vn, tail_index)
        if delta is not None:
            return int(delta)
    return None

def _impl__has_zero_tail_residue_guard(
    self,
    all_ops: Sequence[object],
    tail_index_source_varnode,
    lane_count: int,
) -> bool:
    mask = int(lane_count) - 1
    if mask <= 0:
        return False
    for op in all_ops:
        if getattr(op, "getMnemonic", lambda: None)() not in {"INT_EQUAL", "INT_NOTEQUAL"}:
            continue
        if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
            continue
        left = self._follow_passthrough_varnode(op.getInput(0))
        right = self._follow_passthrough_varnode(op.getInput(1))
        if self._signed_varnode_constant_value(left) == 0 and self._varnode_is_tail_source_mask(
            right,
            tail_index_source_varnode,
            mask,
        ):
            return True
        if self._signed_varnode_constant_value(right) == 0 and self._varnode_is_tail_source_mask(
            left,
            tail_index_source_varnode,
            mask,
        ):
            return True
    return False

def _impl__varnode_is_tail_source_mask(self, candidate_vn, source_vn, mask: int) -> bool:
    if source_vn is None:
        return False
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_AND":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    if self._same_varnode_value(left, source_vn) and self._varnode_unsigned_constant_value(right) == int(mask):
        return True
    return self._same_varnode_value(right, source_vn) and self._varnode_unsigned_constant_value(left) == int(mask)

def _impl__tail_start_varnodes_from_rounded_count(
    self,
    all_ops: Sequence[object],
    pointer_param: dict,
    rounded_vn,
    *,
    element_size: int,
    start_offset: int = 0,
    tail_index_source_varnode=None,
    lane_count: Optional[int] = None,
) -> Tuple[object, ...]:
    starts: List[object] = []
    for op in all_ops:
        output = getattr(op, "getOutput", lambda: None)()
        if output is None:
            continue
        if self._varnode_is_base_plus_scaled_counter(
            output,
            pointer_param,
            rounded_vn,
            element_size=element_size,
            byte_offset=int(start_offset),
        ) or self._varnode_is_base_plus_scaled_tail_source_index(
            output,
            pointer_param,
            tail_index_source_varnode,
            lane_count=lane_count,
            element_size=element_size,
        ):
            starts.append(output)
    changed = True
    while changed:
        changed = False
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is None or any(self._same_varnode_identity(output, start) for start in starts):
                continue
            input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
            if any(
                any(
                    self._same_varnode_value(self._follow_passthrough_varnode(op.getInput(index)), start)
                    for start in starts
                )
                for index in range(input_count)
            ):
                starts.append(output)
                changed = True
    unique: List[object] = []
    seen = set()
    for start in starts:
        key = self._varnode_cache_key(start)
        if key in seen:
            continue
        seen.add(key)
        unique.append(start)
    return tuple(unique)

def _impl__has_scalar_tail_bound_to_count(
    self,
    all_ops: Sequence[object],
    tail_phi,
    pointer_param: dict,
    count_param: dict,
    *,
    element_size: int,
) -> bool:
    compare_ops = {
        "INT_EQUAL",
        "INT_NOTEQUAL",
        "INT_LESS",
        "INT_LESSEQUAL",
        "INT_SLESS",
        "INT_SLESSEQUAL",
    }
    for op in all_ops:
        if getattr(op, "getMnemonic", lambda: None)() not in compare_ops:
            continue
        if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
            continue
        left = self._follow_passthrough_varnode(op.getInput(0))
        right = self._follow_passthrough_varnode(op.getInput(1))
        if self._scalar_tail_cursor_matches_count_bound(
            left,
            right,
            tail_phi,
            pointer_param,
            count_param,
            element_size=element_size,
        ):
            return True
        if self._scalar_tail_cursor_matches_count_bound(
            right,
            left,
            tail_phi,
            pointer_param,
            count_param,
            element_size=element_size,
        ):
            return True
    return False

def _impl__has_scalar_tail_countdown_from_count_minus_rounded(
    self,
    all_ops: Sequence[object],
    rounded_vn,
    count_param: dict,
    *,
    start_index: int = 0,
) -> bool:
    """Recognize tail loops controlled by ``remaining = count - rounded - start``."""

    for op in all_ops:
        if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
            continue
        phi_output = getattr(op, "getOutput", lambda: None)()
        if phi_output is None:
            continue
        input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
        has_count_minus_rounded_init = any(
            self._varnode_is_count_minus_rounded(
                self._follow_passthrough_varnode(op.getInput(index)),
                count_param,
                rounded_vn,
                start_index=start_index,
            )
            for index in range(input_count)
        )
        if not has_count_minus_rounded_init:
            continue
        if self._index_phi_has_step(all_ops, phi_output, -1):
            return True
    return False

def _impl__scalar_tail_cursor_matches_count_bound(
    self,
    cursor_vn,
    end_vn,
    tail_phi,
    pointer_param: dict,
    count_param: dict,
    *,
    element_size: int,
) -> bool:
    cursor_offset = self._byte_offset_from_pointer_like(cursor_vn, tail_phi)
    if cursor_offset is None:
        return False
    if int(cursor_offset) not in {0, int(element_size)}:
        return False
    return self._varnode_is_base_plus_scaled_parameter(
        end_vn,
        pointer_param,
        count_param,
        element_size=element_size,
        byte_offset=int(cursor_offset),
    )

def _impl__varnode_is_base_plus_scaled_tail_source_index(
    self,
    candidate_vn,
    pointer_param: dict,
    tail_index_source_varnode,
    *,
    lane_count: Optional[int],
    element_size: int,
) -> bool:
    if tail_index_source_varnode is None or lane_count is None:
        return False
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None:
        return False
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
        base = self._follow_passthrough_varnode(def_op.getInput(0))
        index = self._follow_passthrough_varnode(def_op.getInput(1))
        elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
        return (
            elem == int(element_size)
            and self._varnode_matches_parameter(base, pointer_param)
            and self._varnode_matches_tail_index_source_or(index, tail_index_source_varnode, lane_count)
        )
    if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        if self._varnode_matches_parameter(left, pointer_param):
            return self._varnode_is_scaled_tail_source_index(
                right,
                tail_index_source_varnode,
                lane_count=lane_count,
                element_size=element_size,
            )
        if mnemonic == "INT_ADD" and self._varnode_matches_parameter(right, pointer_param):
            return self._varnode_is_scaled_tail_source_index(
                left,
                tail_index_source_varnode,
                lane_count=lane_count,
                element_size=element_size,
            )
    return False

def _impl__varnode_is_scaled_tail_source_index(
    self,
    candidate_vn,
    tail_index_source_varnode,
    *,
    lane_count: int,
    element_size: int,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None:
        return False
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic == "INT_MULT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        if self._varnode_unsigned_constant_value(right) == int(element_size):
            return self._varnode_matches_tail_index_source_or(left, tail_index_source_varnode, lane_count)
        if self._varnode_unsigned_constant_value(left) == int(element_size):
            return self._varnode_matches_tail_index_source_or(right, tail_index_source_varnode, lane_count)
        return False
    if mnemonic == "INT_LEFT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        shifted = self._follow_passthrough_varnode(def_op.getInput(0))
        shift_bits = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
        return (
            shift_bits is not None
            and (1 << int(shift_bits)) == int(element_size)
            and self._varnode_matches_tail_index_source_or(shifted, tail_index_source_varnode, lane_count)
        )
    if mnemonic == "INT_OR" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        low_bits = max(0, (int(element_size) - 1).bit_length())
        return (
            self._varnode_is_scaled_tail_source_index(
                left,
                tail_index_source_varnode,
                lane_count=lane_count,
                element_size=element_size,
            )
            and self._varnode_low_bits_clear(right, low_bits)
        ) or (
            self._varnode_is_scaled_tail_source_index(
                right,
                tail_index_source_varnode,
                lane_count=lane_count,
                element_size=element_size,
            )
            and self._varnode_low_bits_clear(left, low_bits)
        )
    return False

def _impl__varnode_matches_tail_index_source_or(
    self,
    candidate_vn,
    tail_index_source_varnode,
    lane_count: int,
) -> bool:
    if tail_index_source_varnode is None:
        return False
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    if self._same_varnode_value(candidate_vn, tail_index_source_varnode):
        return int(lane_count) == 1
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is not None and getattr(def_op, "getMnemonic", lambda: None)() == "INT_OR":
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            mask = int(lane_count) - 1
            if self._same_varnode_value(left, tail_index_source_varnode) and self._signed_varnode_constant_value(right) == mask:
                return True
            if self._same_varnode_value(right, tail_index_source_varnode) and self._signed_varnode_constant_value(left) == mask:
                return True
    if def_op is not None and getattr(def_op, "getMnemonic", lambda: None)() == "MULTIEQUAL":
        input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
        for index in range(input_count):
            try:
                input_vn = self._phi_input_value_varnode(def_op, index)
            except Exception:
                input_vn = None
            if input_vn is None:
                try:
                    input_vn = def_op.getInput(index)
                except Exception:
                    continue
            if self._varnode_matches_tail_index_source_or(input_vn, tail_index_source_varnode, lane_count):
                return True
    return False

def _impl__rounded_tail_index_varnode_matches(
    self,
    candidate_vn,
    counter_vn,
    *,
    start_index: int,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    direct_delta = self._counter_plus_constant_delta(candidate_vn, counter_vn)
    if direct_delta == int(start_index):
        return True
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
        return False
    input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
    if input_count <= 0:
        return False
    saw_seed = False
    saw_rounded = False
    for index in range(input_count):
        input_vn = self._follow_passthrough_varnode(def_op.getInput(index))
        if self._signed_varnode_constant_value(input_vn) == int(start_index):
            saw_seed = True
            continue
        if self._counter_plus_constant_delta(input_vn, counter_vn) == int(start_index):
            saw_rounded = True
            continue
    return saw_seed and saw_rounded
