"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence.summarizer``."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from collections import Counter
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    PcodeOpRef,
    ReadonlyReductionTermRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.signature import is_integral_data_type
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    ResidueLoopCase,
    _reduce_expression_under_conditions,
)
from scripts.function_tracer_pcode.analysis.debug import summarize_conditions, summarize_expression

def _impl__try_summarize_vectorized_affine_progression_sum(
    self,
    function,
    high_function,
    analysis,
) -> Optional[Tuple[List[ReturnInfo], str]]:
    if function is None or high_function is None or analysis is None:
        return None
    if not self._analysis_is_safe_for_counted_scalar_summary(analysis):
        self._debug("Declined vectorized affine progression summary: unsafe counted scalar profile")
        return None
    if getattr(getattr(analysis, "effect_summary", None), "effects", None):
        self._debug("Declined vectorized affine progression summary: function has memory side effects")
        return None
    side_effect_profile = self._build_loop_side_effect_profile(
        analysis=analysis,
        high_function=high_function,
    )
    requires_effect_proof = getattr(side_effect_profile, "requires_effect_proof", None)
    if callable(requires_effect_proof) and requires_effect_proof():
        self._debug("Declined vectorized affine progression summary: high-function effects require proof")
        return None
    parameters = list(getattr(analysis, "parameters", None) or [])
    if len(parameters) not in {1, 2}:
        self._debug(
            "Declined vectorized affine progression summary: expected one or two parameters "
            f"(found {len(parameters)})"
        )
        return None
    if not all(is_integral_data_type(param.get("data_type_obj"), param.get("data_type")) for param in parameters):
        self._debug("Declined vectorized affine progression summary: non-integral parameter")
        return None
    if any(int(param.get("size", 0) or 0) > 4 for param in parameters):
        self._debug("Declined vectorized affine progression summary: parameter wider than 32 bits")
        return None

    literal = self._readonly_affine_progression_literal(analysis)
    if literal is None or literal.step <= 0:
        self._debug("Declined vectorized affine progression summary: no readonly affine literal")
        return None
    step = int(literal.step)

    count_expr = self._vectorized_affine_counter_expression(parameters[0], analysis)
    if count_expr is None:
        self._debug("Declined vectorized affine progression summary: counter expression not identified")
        return None
    signed_counter_guard = self._vectorized_affine_counter_guard_signedness(analysis, parameters[0])
    if signed_counter_guard is None:
        self._debug("Declined vectorized affine progression summary: counter guard signedness is ambiguous")
        return None
    result_size = max(
        1,
        *(int(param.get("size", 0) or 0) for param in parameters),
        4,
    )
    bias_candidates = self._vectorized_affine_bias_candidates(
        parameters,
        result_size,
        lane_base=int(literal.lane_base),
    )
    if not bias_candidates:
        self._debug("Declined vectorized affine progression summary: no bias candidates")
        return None
    zero = Expression.constant(0, size=result_size)
    positive_operator = "INT_SLESS" if signed_counter_guard else "INT_LESS"
    positive_guard = Condition(
        Expression.binary_op(
            positive_operator,
            zero,
            self._coerce_summary_expression_to_size(count_expr, result_size, signed=signed_counter_guard),
        ),
        False,
    )
    base_guard = self._zero_base_guard_cover_for_positive_counter_guard(
        analysis,
        parameters[0],
        count_expr,
        positive_guard,
    )
    if base_guard is None:
        self._debug("Declined vectorized affine progression summary: missing proven zero base coverage")
        return None
    if not self._nonzero_returns_are_disjoint_from_base_guard(
        analysis,
        base_guard,
        parameters[0],
        count_expr,
    ):
        self._debug("Declined vectorized affine progression summary: nonzero return overlaps zero base guard")
        return None
    selected_loop_value: Optional[Expression] = None
    selected_bias_expr: Optional[Expression] = None
    for bias_expr in bias_candidates:
        summary_bias_expr = self._coerce_summary_expression_to_size(
            bias_expr,
            result_size,
            signed=self._expression_prefers_signed_extension(bias_expr),
        )
        loop_value = self._build_counted_loop_summary_value(
            base_expr=zero,
            start_expr=zero,
            limit_expr=self._coerce_summary_expression_to_size(count_expr, result_size, signed=signed_counter_guard),
            induction_step=1,
            residue_cases=(
                ResidueLoopCase(
                    modulus=1,
                    residue=0,
                    affine=(int(step), 0),
                    bias_expr=summary_bias_expr,
                ),
            ),
            result_size=result_size,
            signed_loop=signed_counter_guard,
            side_effect_profile=side_effect_profile,
            guard_constraints=(positive_guard,),
        )
        if loop_value is None:
            continue
        if self._positive_returns_match_vectorized_affine_summary(
            analysis,
            parameters[0],
            count_expr,
            step=int(step),
            bias_expr=summary_bias_expr,
            result_size=result_size,
            signed_counter_guard=signed_counter_guard,
        ):
            selected_loop_value = loop_value
            selected_bias_expr = summary_bias_expr
            break
    if selected_loop_value is None or selected_bias_expr is None:
        self._debug("Declined vectorized affine progression summary: positive return proof failed")
        return None

    anchor = next(iter((getattr(analysis, "returns", None) or [])), None)
    address = getattr(anchor, "address", getattr(function, "getEntryPoint", lambda: "0x0")())
    pcode_identity = getattr(anchor, "pcode_identity", None)
    pcode_order = getattr(anchor, "pcode_order", None)
    pcode_time = getattr(anchor, "pcode_time", None)
    pcode_op_ref = getattr(anchor, "pcode_op_ref", None)
    return [
        ReturnInfo(
            address=address,
            value=zero,
            conditions=[base_guard],
            branch_index=0,
            pcode_identity=pcode_identity,
            pcode_order=pcode_order,
            pcode_time=pcode_time,
            pcode_op_ref=pcode_op_ref,
        ),
        ReturnInfo(
            address=address,
            value=selected_loop_value,
            conditions=[positive_guard],
            branch_index=1,
            pcode_identity=pcode_identity,
            pcode_order=pcode_order,
            pcode_time=pcode_time,
            pcode_op_ref=pcode_op_ref,
        ),
    ], "vectorized_affine_progression_sum_summary"

def _impl__vectorized_affine_bias_candidates(
    self,
    parameters: Sequence[dict],
    result_size: int,
    *,
    lane_base: int = 0,
) -> Tuple[Expression, ...]:
    size = max(1, int(result_size or 0))
    lane_base_expr = Expression.constant(int(lane_base), size=size)
    if len(parameters) == 2:
        param_bias = self._parameter_expression(parameters[1])
        if int(lane_base) == 0:
            return (param_bias,)
        coerced_param_bias = self._coerce_summary_expression_to_size(
            param_bias,
            size,
            signed=self._expression_prefers_signed_extension(param_bias),
        )
        combined_bias = Expression.binary_op("INT_ADD", coerced_param_bias, lane_base_expr)
        combined_bias.size = size
        return (combined_bias,)
    if len(parameters) != 1:
        return ()
    return (lane_base_expr,)

def _impl__vectorized_affine_counter_expression(
    self,
    counter_param: dict,
    analysis,
) -> Optional[Expression]:
    primary = self._parameter_expression(counter_param)
    expressions: List[Optional[Expression]] = [primary]
    for ret in getattr(analysis, "returns", None) or ():
        expressions.append(getattr(ret, "value", None))
        for condition in getattr(ret, "conditions", None) or ():
            expressions.append(getattr(condition, "expression", None))
    candidates = self._parameter_expression_candidates(
        counter_param,
        expressions,
        include_primary=True,
        primary=primary,
    )
    selected: Optional[Expression] = None
    selected_score = -1
    for candidate in candidates:
        if getattr(candidate, "expr_type", None) != ExpressionType.PARAMETER:
            continue
        if not self._counter_parameter_candidate_matches_descriptor(candidate, counter_param):
            continue
        score = 0
        if getattr(candidate, "storage_info", None) is not None:
            score += 4
        if self._parameter_expression_semantic_identity(candidate) is not None:
            score += 2
        try:
            if int(getattr(candidate, "value", -1)) >= 0:
                score += 1
        except (TypeError, ValueError):
            pass
        if selected is None or score > selected_score:
            selected = candidate
            selected_score = score
    if selected is not None:
        return selected
    if self._counter_parameter_candidate_matches_descriptor(primary, counter_param):
        return primary
    return None

def _impl__positive_returns_match_vectorized_affine_summary(
    self,
    analysis,
    counter_param: dict,
    counter_expr: Expression,
    *,
    step: int,
    bias_expr: Expression,
    result_size: int,
    signed_counter_guard: bool,
) -> bool:
    count_expr = counter_expr
    default_summary_closed = self._build_affine_progression_sum_closed_expression(
        count_expr=count_expr,
        step=int(step),
        bias_expr=bias_expr,
        result_size=result_size,
        signed_count=signed_counter_guard,
    )
    if default_summary_closed is None:
        return False
    positive_case_count = 0
    for ret in getattr(analysis, "returns", None) or ():
        value = getattr(ret, "value", None)
        if value is None:
            return False
        conditions = self._normalize_counter_parameter_conditions(
            list(getattr(ret, "conditions", None) or []),
            counter_param,
            count_expr,
        )
        value = self._normalize_counter_parameter_expression(
            value,
            counter_param,
            count_expr,
        )
        if value is None:
            return False
        positive_counter_cases = self._positive_counter_conditions_for_return(
            conditions,
            counter_param,
            signed_counter_guard=signed_counter_guard,
        )
        if positive_counter_cases is None:
            if self._debug_available():
                self._debug(
                    "Declined vectorized affine progression summary: positive return overlap proof unknown "
                    f"(branch_index={getattr(ret, 'branch_index', None)}, "
                    f"conditions={summarize_conditions(conditions)})"
                )
            return False
        if len(positive_counter_cases) == 0:
            continue
        positive_case_count += 1
        if not any(
            self._return_value_matches_affine_progression_summary(
                value=value,
                conditions=list(conditions),
                positive_condition=positive_condition,
                counter_expr=counter_expr,
                bias_expr=bias_expr,
                step=int(step),
                result_size=result_size,
                signed_counter_guard=signed_counter_guard,
            )
            for positive_condition, counter_expr in positive_counter_cases
        ):
            if self._debug_available():
                self._debug(
                    "Declined vectorized affine progression summary: positive return fragment mismatch "
                    f"(branch_index={getattr(ret, 'branch_index', None)}, "
                    f"conditions={summarize_conditions(conditions)}, "
                    f"value={summarize_expression(value)})"
                )
            return False
    return positive_case_count > 0

def _impl__vectorized_affine_counter_guard_signedness(self, analysis, counter_param: dict) -> Optional[bool]:
    signedness_values: set[bool] = set()
    for ret in getattr(analysis, "returns", None) or ():
        conditions = list(getattr(ret, "conditions", None) or [])
        candidates = self._counter_guard_parameter_candidates(counter_param, conditions)
        for condition in conditions:
            value = self._counter_guard_signedness_from_condition(condition, candidates)
            if value is not None:
                signedness_values.add(value)
    if len(signedness_values) == 1:
        return next(iter(signedness_values))
    return None

def _impl__vector_prefix_seed_terms_from_exact_returns(
    self,
    analysis,
    pointer_param: dict,
    count_param: dict,
    seed_region_conditions: Sequence[Condition],
    *,
    start_index: int,
    element_size: int,
) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
    """Recover pre-loop seed terms for vectorized reductions.

    A vectorized reduction can start at a peeled logical index without
    being a true prefix.  For example, wrong-tail uses seed terms at
    offsets 0 and 8, then starts the loop at index 3.  Treating every
    skipped index as an implicit prefix seed would be unsound, so this
    derives the seed set only from exact object-level return witnesses.
    """

    if analysis is None or int(start_index) <= 0 or int(element_size) <= 0:
        return None
    start_offset = int(start_index) * int(element_size)
    count_name = str(count_param.get("name") or "")
    candidates: Dict[Tuple[Tuple[Any, ...], ...], Tuple[ReadonlyReductionTermRef, ...]] = {}
    for ret in getattr(analysis, "returns", None) or ():
        if not self._return_overlaps_conditions(ret, seed_region_conditions):
            continue
        exact_count = self._exact_counter_value_from_conditions(ret.conditions or [], count_name)
        if exact_count is None or int(exact_count) <= int(start_index):
            continue
        extracted = self._extract_readonly_return_terms_and_bias(
            analysis,
            pointer_param,
            ret,
            None,
        )
        if extracted is None:
            self._debug(
                "Skipped vectorized readonly seed witness: "
                f"no readonly term extraction for count={exact_count}"
            )
            continue
        terms, constant_bias = extracted
        result_size = max(1, int(getattr(ret.value, "size", 0) or element_size))
        if self._normalize_readonly_constant_bias(int(constant_bias), result_size) != 0:
            self._debug(
                "Skipped vectorized readonly seed witness: "
                f"non-zero constant bias for count={exact_count}"
            )
            continue
        term_counts = Counter((int(term.byte_offset), int(term.access_size)) for term in terms or ())
        expected_loop_offsets = tuple(
            range(start_offset, int(exact_count) * int(element_size), int(element_size))
        )
        if not expected_loop_offsets:
            continue
        missing_loop_term = False
        for offset in expected_loop_offsets:
            key = (int(offset), int(element_size))
            if term_counts.get(key, 0) <= 0:
                missing_loop_term = True
                break
            term_counts[key] -= 1
            if term_counts[key] <= 0:
                term_counts.pop(key, None)
        if missing_loop_term:
            self._debug(
                "Skipped vectorized readonly seed witness: "
                f"missing suffix term for count={exact_count}, expected_offsets={list(expected_loop_offsets)}"
            )
            continue
        seed_terms: List[ReadonlyReductionTermRef] = []
        valid_seed = True
        for (byte_offset, access_size), count in sorted(term_counts.items()):
            if count != 1:
                valid_seed = False
                break
            if int(access_size) != int(element_size):
                valid_seed = False
                break
            if int(byte_offset) < 0 or int(byte_offset) >= start_offset:
                valid_seed = False
                break
            if int(byte_offset) % int(element_size) != 0:
                valid_seed = False
                break
            seed_terms.append(
                ReadonlyReductionTermRef(
                    byte_offset=int(byte_offset),
                    access_size=int(access_size),
                )
            )
        if not valid_seed:
            self._debug(
                "Skipped vectorized readonly seed witness: "
                f"remaining terms are not valid seed terms for count={exact_count}"
            )
            continue
        seed_key = tuple(term.stable_key() for term in seed_terms)
        candidates.setdefault(seed_key, tuple(seed_terms))
    if not candidates:
        candidates.update(
            self._vector_prefix_seed_terms_from_materialized_region_returns(
                analysis,
                pointer_param,
                seed_region_conditions,
                start_offset=start_offset,
                element_size=element_size,
            )
        )
    if len(candidates) != 1:
        if len(candidates) > 1:
            self._debug("Declined vectorized readonly prefix-sum seed recovery: ambiguous seed witnesses")
        return None
    recovered = next(iter(candidates.values()))
    self._debug(
        "Recovered vectorized readonly prefix-sum seed terms from object-level returns: "
        f"offsets={[term.byte_offset for term in recovered]}"
    )
    return recovered

def _impl__vector_prefix_seed_terms_from_materialized_region_returns(
    self,
    analysis,
    pointer_param: dict,
    seed_region_conditions: Sequence[Condition],
    *,
    start_offset: int,
    element_size: int,
) -> Dict[Tuple[Tuple[Any, ...], ...], Tuple[ReadonlyReductionTermRef, ...]]:
    candidates: Dict[Tuple[Tuple[Any, ...], ...], Tuple[ReadonlyReductionTermRef, ...]] = {}
    if analysis is None or int(start_offset) <= 0 or int(element_size) <= 0:
        return candidates
    for ret in getattr(analysis, "returns", None) or ():
        if not self._return_overlaps_conditions(ret, seed_region_conditions):
            continue
        extracted = self._extract_readonly_return_terms_and_bias(
            analysis,
            pointer_param,
            ret,
            None,
        )
        if extracted is None:
            continue
        terms, constant_bias = extracted
        result_size = max(1, int(getattr(ret.value, "size", 0) or element_size))
        if self._normalize_readonly_constant_bias(int(constant_bias), result_size) != 0:
            continue
        term_counts = Counter((int(term.byte_offset), int(term.access_size)) for term in terms or ())
        loop_offsets = sorted(
            byte_offset
            for byte_offset, access_size in term_counts
            if int(access_size) == int(element_size) and int(byte_offset) >= int(start_offset)
        )
        if not loop_offsets:
            continue
        expected_loop_offsets = list(range(int(start_offset), max(loop_offsets) + int(element_size), int(element_size)))
        if loop_offsets != expected_loop_offsets:
            continue
        for offset in expected_loop_offsets:
            key = (int(offset), int(element_size))
            if term_counts.get(key, 0) != 1:
                term_counts.clear()
                break
            term_counts.pop(key, None)
        if not term_counts:
            continue
        seed_terms: List[ReadonlyReductionTermRef] = []
        valid_seed = True
        for (byte_offset, access_size), count in sorted(term_counts.items()):
            if (
                count != 1
                or int(access_size) != int(element_size)
                or int(byte_offset) < 0
                or int(byte_offset) >= int(start_offset)
                or int(byte_offset) % int(element_size) != 0
            ):
                valid_seed = False
                break
            seed_terms.append(
                ReadonlyReductionTermRef(
                    byte_offset=int(byte_offset),
                    access_size=int(access_size),
                )
            )
        if not valid_seed:
            continue
        seed_key = tuple(term.stable_key() for term in seed_terms)
        candidates.setdefault(seed_key, tuple(seed_terms))
    return candidates

def _impl__valid_power_of_two_lane_count(self, value: Optional[int]) -> Optional[int]:
    if value is None:
        return None
    lane_count = int(value)
    if lane_count <= 1:
        return None
    if lane_count & (lane_count - 1):
        return None
    return lane_count

def _impl__match_vector_prefix_pointer(
    self,
    all_ops: Sequence[object],
    pointer_param: dict,
    *,
    vector_stride: int,
    element_size: int,
    expected_start_offset: int = 0,
) -> Optional[Tuple[object, int, int]]:
    for op in all_ops:
        if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
            continue
        phi_output = getattr(op, "getOutput", lambda: None)()
        if phi_output is None:
            continue
        if not self._phi_has_pointer_step(
            all_ops,
            phi_output,
            step_bytes=vector_stride,
        ):
            continue
        lane_offsets = self._load_byte_offsets_from_pointer(all_ops, phi_output, element_size=element_size)
        if not lane_offsets:
            continue
        min_offset = min(lane_offsets)
        lane_base_offset = -int(min_offset)
        if lane_base_offset < 0:
            continue
        seed_offsets = self._pointer_phi_seed_offsets(op, pointer_param)
        for seed_offset in seed_offsets:
            global_lane_start = int(seed_offset) + int(min_offset)
            if global_lane_start == int(expected_start_offset):
                return phi_output, lane_base_offset, int(seed_offset)
        if int(expected_start_offset) == 0 and not seed_offsets and self._has_pointer_base_plus_constant(
            all_ops,
            pointer_param,
            0,
        ):
            return phi_output, lane_base_offset, 0
        if int(expected_start_offset) == 0 and 0 in seed_offsets:
            return phi_output, lane_base_offset, 0
    return None

def _impl__vector_prefix_lanes_cover_block(
    self,
    all_ops: Sequence[object],
    pointer_phi,
    *,
    base_offset: int,
    vector_stride: int,
    element_size: int,
) -> bool:
    raw_offsets = self._load_byte_offsets_from_pointer(all_ops, pointer_phi, element_size=element_size)
    normalized = sorted({int(offset) + int(base_offset) for offset in raw_offsets})
    expected = list(range(0, int(vector_stride), int(element_size)))
    return normalized == expected

def _impl__vector_prefix_lanes_have_unit_terms_in_positive_return(
    self,
    analysis,
    pointer_param: dict,
    vector_region_conditions: Sequence[Condition],
    *,
    global_start_offset: int = 0,
    vector_stride: int,
    element_size: int,
) -> Optional[bool]:
    status, _refs = self._vector_prefix_positive_return_term_proof(
        analysis,
        pointer_param,
        vector_region_conditions,
        global_start_offset=global_start_offset,
        vector_stride=vector_stride,
        element_size=element_size,
        require_site_refs=False,
    )
    return status

def _impl__vector_prefix_unit_term_positive_return_refs(
    self,
    analysis,
    pointer_param: dict,
    vector_region_conditions: Sequence[Condition],
    *,
    global_start_offset: int = 0,
    vector_stride: int,
    element_size: int,
) -> Tuple[PcodeOpRef, ...]:
    status, refs = self._vector_prefix_positive_return_term_proof(
        analysis,
        pointer_param,
        vector_region_conditions,
        global_start_offset=global_start_offset,
        vector_stride=vector_stride,
        element_size=element_size,
        require_site_refs=True,
    )
    if status is not True:
        return ()
    return refs

def _impl__vector_prefix_positive_return_term_proof(
    self,
    analysis,
    pointer_param: dict,
    vector_region_conditions: Sequence[Condition],
    *,
    global_start_offset: int = 0,
    vector_stride: int,
    element_size: int,
    require_site_refs: bool,
) -> Tuple[Optional[bool], Tuple[PcodeOpRef, ...]]:
    expected = {
        (int(byte_offset), int(element_size))
        for byte_offset in range(
            0,
            int(global_start_offset) + int(vector_stride),
            int(element_size),
        )
    }
    expected_counts = Counter({term_key: 1 for term_key in expected})
    refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    saw_overlapping_return = False
    for ret in getattr(analysis, "returns", None) or ():
        if not self._return_overlaps_conditions(ret, vector_region_conditions):
            continue
        saw_overlapping_return = True
        value = _reduce_expression_under_conditions(ret.value, ret.conditions or ())
        terms = self._extract_readonly_reduction_terms(
            value,
            getattr(analysis, "parameters", None) or (),
            pointer_param,
        )
        if terms is None and value is not ret.value:
            terms = self._extract_readonly_reduction_terms(
                ret.value,
                getattr(analysis, "parameters", None) or (),
                pointer_param,
            )
        if terms is None:
            return False, ()
        counts = Counter((int(term.byte_offset), int(term.access_size)) for term in terms)
        if counts != expected_counts:
            return False, ()
        ref = self._pcode_op_ref_from_return_info(ret)
        if ref is None:
            if require_site_refs:
                return False, ()
            continue
        refs.setdefault(ref.stable_key(), ref)
    if not saw_overlapping_return:
        return None, ()
    return True, tuple(sorted(refs.values(), key=lambda ref: repr(ref.stable_key())))

def _impl__vector_prefix_lanes_contribute_additively_to_return(
    self,
    all_ops: Sequence[object],
    pointer_phi,
    *,
    base_offset: int,
    vector_stride: int,
    element_size: int,
) -> bool:
    expected_offsets = set(range(0, int(vector_stride), int(element_size)))
    expected_counts = Counter({offset: 1 for offset in expected_offsets})
    contributing_counts: Counter[int] = Counter()
    for op in all_ops:
        if getattr(op, "getMnemonic", lambda: None)() != "LOAD":
            continue
        if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
            continue
        output = getattr(op, "getOutput", lambda: None)()
        if output is None:
            continue
        load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
        address = self._follow_passthrough_varnode(op.getInput(1))
        byte_offset = self._byte_offset_from_pointer(address, pointer_phi)
        if byte_offset is None:
            continue
        normalized_offsets = [
            int(byte_offset) + int(base_offset) + lane_delta
            for lane_delta in range(0, load_size, element_size)
        ]
        if any(offset not in expected_offsets for offset in normalized_offsets):
            if self._load_lanes_flow_additively_to_return(
                output,
                load_size=load_size,
                element_size=element_size,
                pointer_phi=pointer_phi,
                expected_offsets=expected_offsets,
                base_offset=base_offset,
            ):
                self._debug(
                    "Declined vectorized readonly prefix-sum load contribution: "
                    f"unexpected_offsets={tuple(normalized_offsets)}"
                )
                return False
            continue
        if self._load_lanes_flow_additively_to_return(
            output,
            load_size=load_size,
            element_size=element_size,
            pointer_phi=pointer_phi,
            expected_offsets=expected_offsets,
            base_offset=base_offset,
        ):
            contributing_counts.update(normalized_offsets)
    return contributing_counts == expected_counts

def _impl__vector_prefix_lane_return_refs(
    self,
    all_ops: Sequence[object],
    pointer_phi,
    *,
    base_offset: int,
    vector_stride: int,
    element_size: int,
) -> Tuple[Tuple[PcodeOpRef, ...], Tuple[PcodeOpRef, ...]]:
    expected_offsets = set(range(0, int(vector_stride), int(element_size)))
    expected_counts = Counter({offset: 1 for offset in expected_offsets})
    contributing_counts: Counter[int] = Counter()
    return_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    return_value_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    for op in all_ops:
        if getattr(op, "getMnemonic", lambda: None)() != "LOAD":
            continue
        if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
            continue
        output = getattr(op, "getOutput", lambda: None)()
        if output is None:
            continue
        load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
        address = self._follow_passthrough_varnode(op.getInput(1))
        byte_offset = self._byte_offset_from_pointer(address, pointer_phi)
        if byte_offset is None:
            continue
        normalized_offsets = [
            int(byte_offset) + int(base_offset) + lane_delta
            for lane_delta in range(0, load_size, element_size)
        ]
        if any(offset not in expected_offsets for offset in normalized_offsets):
            continue
        if not self._load_lanes_flow_additively_to_return(
            output,
            load_size=load_size,
            element_size=element_size,
            pointer_phi=pointer_phi,
            expected_offsets=expected_offsets,
            base_offset=base_offset,
        ):
            continue
        contributing_counts.update(normalized_offsets)
        for ref in self._reachable_return_op_refs_from_varnodes((output,)):
            return_refs.setdefault(ref.stable_key(), ref)
        for ref in self._reachable_return_value_op_refs_from_varnodes((output,)):
            return_value_refs.setdefault(ref.stable_key(), ref)
    if contributing_counts != expected_counts:
        return (), ()
    return (
        tuple(sorted(return_refs.values(), key=lambda ref: repr(ref.stable_key()))),
        tuple(sorted(return_value_refs.values(), key=lambda ref: repr(ref.stable_key()))),
    )

def _impl__vector_prefix_lane_return_value_refs(
    self,
    all_ops: Sequence[object],
    pointer_phi,
    *,
    base_offset: int,
    vector_stride: int,
    element_size: int,
) -> Tuple[PcodeOpRef, ...]:
    _return_refs, return_value_refs = self._vector_prefix_lane_return_refs(
        all_ops,
        pointer_phi,
        base_offset=base_offset,
        vector_stride=vector_stride,
        element_size=element_size,
    )
    return return_value_refs

def _impl__load_lanes_flow_additively_to_return(
    self,
    load_output,
    *,
    load_size: int,
    element_size: int,
    pointer_phi=None,
    expected_offsets: Sequence[int] = (),
    base_offset: int = 0,
) -> bool:
    required_lanes = max(1, int(load_size) // max(1, int(element_size)))
    if required_lanes <= 1:
        count = self._varnode_additive_return_contribution_count(load_output)
        if count != 1:
            self._debug(
                "Declined vectorized readonly prefix-sum load contribution: "
                f"load={self._varnode_cache_key(load_output)} contribution_count={count}"
            )
        return count == 1
    lane_roots = self._collect_scalar_lane_roots(load_output, element_size=element_size)
    if len(lane_roots) != required_lanes:
        self._debug(
            "Declined vectorized readonly prefix-sum load contribution: "
            f"load={self._varnode_cache_key(load_output)} "
            f"lane_roots={len(lane_roots)} required_lanes={required_lanes}"
        )
        return False
    counts = tuple(
        self._varnode_additive_return_contribution_count(lane)
        for lane in lane_roots
    )
    if any(count != 1 for count in counts):
        self._debug(
            "Declined vectorized readonly prefix-sum load contribution: "
            f"load={self._varnode_cache_key(load_output)} lane_counts={counts}"
        )
        return False
    return True

def _impl__load_lanes_flow_additively_to_any_return(
    self,
    load_output,
    *,
    load_size: int,
    element_size: int,
) -> bool:
    required_lanes = max(1, int(load_size) // max(1, int(element_size)))
    if required_lanes <= 1:
        return self._varnode_has_additive_return_contribution(load_output)
    lane_roots = self._collect_scalar_lane_roots(load_output, element_size=element_size)
    if len(lane_roots) != required_lanes:
        return False
    return all(self._varnode_has_additive_return_contribution(lane) for lane in lane_roots)

def _impl__collect_scalar_lane_roots(
    self,
    start_varnode,
    *,
    element_size: int,
    budget: int = 64,
) -> Tuple[object, ...]:
    lanes: List[object] = []
    stack = [start_varnode]
    seen = set()
    while stack and len(seen) < budget:
        current = stack.pop()
        key = self._varnode_cache_key(current)
        if key in seen:
            continue
        seen.add(key)
        for op in self._iter_varnode_descendant_ops(current):
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            output = getattr(op, "getOutput", lambda: None)()
            if output is None:
                continue
            output_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
            if mnemonic == "SUBPIECE" and output_size == int(element_size):
                lanes.append(output)
                continue
            if mnemonic in {"INT_RIGHT", "COPY", "CAST", "INT_ZEXT", "INT_SEXT"}:
                stack.append(output)
    unique: Dict[Tuple[Any, ...], object] = {}
    for lane in lanes:
        key = self._varnode_cache_key(lane)
        if key is not None:
            unique[key] = lane
    return tuple(unique.values())

def _impl__has_vector_countdown_loop(
    self,
    all_ops: Sequence[object],
    rounded_vn,
    *,
    lane_count: int,
) -> bool:
    for op in all_ops:
        if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
            continue
        phi_output = getattr(op, "getOutput", lambda: None)()
        if phi_output is None:
            continue
        has_init = False
        input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
        for index in range(input_count):
            if self._same_varnode_value(self._follow_passthrough_varnode(op.getInput(index)), rounded_vn):
                has_init = True
                break
        if not has_init:
            continue
        if self._index_phi_has_step(all_ops, phi_output, -int(lane_count)):
            return True
    return False

def _impl__has_vector_loop_bound_to_rounded_count(
    self,
    all_ops: Sequence[object],
    pointer_phi,
    pointer_param: dict,
    rounded_vn,
    *,
    element_size: int,
    base_offset: int,
    vector_stride: int,
) -> bool:
    """Prove a vector cursor stops at ``base + rounded_count * elem``.

    Clang/LLVM often emits a pointer-induction vector loop instead of a
    separate countdown induction.  This keeps the recognition object-centric:
    the proof is over Ghidra varnodes and P-code def-use links, not textual
    decompiler output.
    """

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
        if self._vector_cursor_matches_end_bound(
            left,
            right,
            pointer_phi,
            pointer_param,
            rounded_vn,
            element_size=element_size,
            base_offset=base_offset,
            vector_stride=vector_stride,
        ):
            return True
        if self._vector_cursor_matches_end_bound(
            right,
            left,
            pointer_phi,
            pointer_param,
            rounded_vn,
            element_size=element_size,
            base_offset=base_offset,
            vector_stride=vector_stride,
        ):
            return True
    return False

def _impl__vector_cursor_matches_end_bound(
    self,
    cursor_vn,
    end_vn,
    pointer_phi,
    pointer_param: dict,
    rounded_vn,
    *,
    element_size: int,
    base_offset: int,
    vector_stride: int,
) -> bool:
    cursor_offset = self._byte_offset_from_pointer_like(cursor_vn, pointer_phi)
    if cursor_offset is None:
        return False
    if int(cursor_offset) not in {0, int(vector_stride)}:
        return False
    return self._varnode_is_base_plus_scaled_counter(
        end_vn,
        pointer_param,
        rounded_vn,
        element_size=element_size,
        byte_offset=int(base_offset) + int(cursor_offset),
    )
