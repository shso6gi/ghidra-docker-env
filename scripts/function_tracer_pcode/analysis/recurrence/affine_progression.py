"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence.summarizer``."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    Condition,
    CountedLoopAccumulator,
    CountedLoopInduction,
    Expression,
    ExpressionType,
    PcodeOpRef,
    ReadonlyAccumulatorPhiCandidate,
)

def _impl__return_value_matches_affine_progression_summary(
    self,
    *,
    value: Expression,
    conditions: Sequence[Condition],
    positive_condition: Condition,
    counter_expr: Expression,
    bias_expr: Expression,
    step: int,
    result_size: int,
    signed_counter_guard: bool,
) -> bool:
    proof_conditions = list(conditions) + [positive_condition]
    direct_count = (
        self._implied_counter_constant_expression(conditions, counter_expr)
        or counter_expr
    )
    direct_summary = self._build_affine_progression_sum_closed_expression(
        count_expr=direct_count,
        step=int(step),
        bias_expr=bias_expr,
        result_size=result_size,
        signed_count=signed_counter_guard,
    )
    if direct_summary is not None and self._prove_return_value_equals_summary_closed_form(
        value,
        direct_summary,
        proof_conditions,
        result_size=result_size,
    ):
        return True

    finite_counts = self._complete_counter_constant_cover(
        proof_conditions,
        counter_expr,
    )
    if finite_counts is None:
        return False
    for count_value in finite_counts:
        count_const = Expression.constant(count_value, size=max(1, int(getattr(counter_expr, "size", 0) or 4)))
        exact_count = Condition(
            Expression.binary_op("INT_EQUAL", counter_expr, count_const),
            False,
        )
        summary = self._build_affine_progression_sum_closed_expression(
            count_expr=count_const,
            step=int(step),
            bias_expr=bias_expr,
            result_size=result_size,
            signed_count=signed_counter_guard,
        )
        if summary is None:
            return False
        if not self._prove_return_value_equals_summary_closed_form(
            value,
            summary,
            proof_conditions + [exact_count],
            result_size=result_size,
        ):
            return False
    return True

def _impl__build_affine_progression_sum_closed_expression(
    self,
    *,
    count_expr: Expression,
    step: int,
    bias_expr: Expression,
    result_size: int,
    signed_count: bool = True,
) -> Optional[Expression]:
    target_size = max(1, int(result_size or 0))
    count = self._coerce_summary_expression_to_size(count_expr, target_size, signed=bool(signed_count))
    bias = self._coerce_summary_expression_to_size(bias_expr, target_size, signed=True)
    wide_size = max(8, target_size * 2)
    wide_count = Expression.unary_op("INT_ZEXT", count)
    wide_count.size = wide_size
    count_minus_one = Expression.binary_op(
        "INT_SUB",
        count,
        Expression.constant(1, size=target_size),
    )
    count_minus_one.size = target_size
    wide_count_minus_one = Expression.unary_op("INT_ZEXT", count_minus_one)
    wide_count_minus_one.size = wide_size
    product = Expression.binary_op("INT_MULT", wide_count, wide_count_minus_one)
    product.size = wide_size
    half = Expression.binary_op("INT_RIGHT", product, Expression.constant(1, size=wide_size))
    half.size = wide_size
    triangular = Expression.binary_op("SUBPIECE", half, Expression.constant(0, size=4))
    triangular.size = target_size
    step_term = triangular
    if int(step) != 1:
        step_term = Expression.binary_op(
            "INT_MULT",
            triangular,
            Expression.constant(int(step), size=target_size),
        )
        step_term.size = target_size
    bias_term = Expression.binary_op("INT_MULT", count, bias)
    bias_term.size = target_size
    total = Expression.binary_op("INT_ADD", step_term, bias_term)
    total.size = target_size
    return total

def _impl__collect_affine_loop_state_placeholders(
    self,
    *,
    header_block,
    induction: CountedLoopInduction,
    accumulator: CountedLoopAccumulator,
) -> Dict[object, Expression]:
    placeholders: Dict[object, Expression] = {}
    if header_block is None:
        return placeholders
    member_output_keys = {
        self._varnode_cache_key(output)
        for output in accumulator.member_outputs
        if output is not None
    }
    for op in self._iter_block_ops(header_block):
        if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
            continue
        if op is induction.phi_op or op is accumulator.phi_op:
            continue
        output = getattr(op, "getOutput", lambda: None)()
        if output is not None and self._varnode_cache_key(output) in member_output_keys:
            continue
        expr = self._summarize_affine_loop_state_phi(op, induction)
        if expr is None:
            continue
        if output is None:
            continue
        placeholders[output] = expr
    return placeholders

def _impl__summarize_affine_loop_state_phi(
    self,
    phi_op,
    induction: CountedLoopInduction,
) -> Optional[Expression]:
    if phi_op is None or induction is None:
        return None
    if int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0) != 2:
        return None
    phi_output = getattr(phi_op, "getOutput", lambda: None)()
    if phi_output is None:
        return None

    backedge_index = None
    delta = None
    for candidate_index in range(2):
        candidate_delta = self._extract_index_step(phi_op.getInput(candidate_index), phi_output)
        if candidate_delta is None:
            continue
        backedge_index = candidate_index
        delta = candidate_delta
        break
    if backedge_index is None or delta is None:
        return None

    init_expr = self._build_pcode_expression(
        phi_op.getInput(1 - backedge_index),
        placeholders={
            induction.phi_output: induction.placeholder,
            induction.phi_op.getInput(self._induction_init_index(induction)): induction.placeholder,
        },
    )
    if init_expr is None or self._expression_is_unresolved(init_expr):
        return None

    size = getattr(phi_output, "getSize", lambda: 0)() or induction.placeholder.size or init_expr.size or 4
    counter_name = induction.placeholder.name or "__loop_iv"
    init_affine = self._extract_affine_term(init_expr, counter_name)
    induction_step = int(induction.step or 0)
    if induction_step == 0 or delta % induction_step != 0:
        return None
    ratio = delta // induction_step
    if init_affine is not None and init_affine[0] == ratio:
        linear_term = self._scale_term(induction.placeholder, ratio, size)
        if linear_term is None:
            return None
        if init_affine[1] == 0:
            linear_term.size = size
            return linear_term
        bias_expr = Expression.constant(init_affine[1], size)
        expr = Expression.binary_op("INT_ADD", linear_term, bias_expr)
        expr.size = size
        return expr

    current_offset = Expression.binary_op("INT_SUB", induction.placeholder, induction.init_expr)
    current_offset.size = size
    if ratio == 0:
        expr = init_expr
    elif ratio == 1:
        expr = Expression.binary_op("INT_ADD", init_expr, current_offset)
        expr.size = size
    elif ratio == -1:
        expr = Expression.binary_op("INT_SUB", init_expr, current_offset)
        expr.size = size
    else:
        scale = Expression.constant(abs(ratio), size)
        scaled_offset = Expression.binary_op("INT_MULT", current_offset, scale)
        scaled_offset.size = size
        operator = "INT_ADD" if ratio > 0 else "INT_SUB"
        expr = Expression.binary_op(operator, init_expr, scaled_offset)
        expr.size = size
    expr.size = size
    return expr

def _impl__extract_affine_loop_case(
    self,
    expr: Expression,
    counter_name: str,
) -> Optional[Tuple[Tuple[int, int], Optional[Expression]]]:
    affine = self._extract_affine_term(expr, counter_name)
    if affine is not None:
        return affine, None

    coeff = 0
    constant_bias = 0
    bias_terms: List[Expression] = []
    for sign, term in self._flatten_add_terms(expr):
        term_affine = self._extract_affine_term(term, counter_name)
        if term_affine is not None:
            coeff += int(sign) * int(term_affine[0])
            constant_bias += int(sign) * int(term_affine[1])
            continue
        if any(
            self._expr_matches_counter_placeholder(node, counter_name)
            for node in self._iter_expression_nodes(term)
        ):
            return None
        scaled = self._scale_expression(term, int(sign))
        if scaled is None:
            continue
        bias_terms.append(scaled)

    if not bias_terms:
        return None
    bias_expr = self._sum_expression_terms(bias_terms)
    if bias_expr is None or self._expression_is_unresolved(bias_expr):
        return None
    if not self._expression_is_loop_invariant_bias(bias_expr):
        return None
    return (coeff, constant_bias), bias_expr

def _impl__build_affine_delta_expression(
    self,
    counter_expr: Expression,
    affine: Tuple[int, int],
    size: int,
    *,
    bias_expr: Optional[Expression] = None,
) -> Optional[Expression]:
    coeff, bias = int(affine[0]), int(affine[1])
    terms: List[Expression] = []
    counter = self._copy_symbol_expression(counter_expr, max(1, size))
    coeff_term = self._scale_expression(counter, coeff)
    if coeff_term is not None:
        coeff_term.size = max(1, size)
        terms.append(coeff_term)
    if bias != 0:
        terms.append(Expression.constant(bias, max(1, size)))
    if bias_expr is not None:
        terms.append(bias_expr)
    if not terms:
        return Expression.constant(0, max(1, size))
    result = self._sum_expression_terms(terms)
    if result is not None:
        result.size = max(1, size)
    return result

def _impl__binary_comparison_matches_affine_constant(
    self,
    expr: Expression,
    base_expr: Expression,
    *,
    coeff: int,
    bias: int,
    constant: int,
) -> bool:
    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return False
    left, right = expr.operands
    left_affine = self._extract_affine_placeholder_term(left, base_expr)
    right_affine = self._extract_affine_placeholder_term(right, base_expr)
    left_const = self._raw_constant_value(left)
    right_const = self._raw_constant_value(right)
    return (
        left_affine == (coeff, bias)
        and right_const == constant
    ) or (
        right_affine == (coeff, bias)
        and left_const == constant
    )

def _impl__grouped_accumulator_load_progressions(
    self,
    candidate: ReadonlyAccumulatorPhiCandidate,
    count_param: Optional[dict],
    pointer_param: dict,
    pointer_phis: Sequence[Dict[str, object]],
    index_phis: Sequence[Dict[str, object]],
    *,
    result_size: Optional[int] = None,
) -> List[Dict[str, object]]:
    grouped = list(candidate.load_progressions)
    parent_block = getattr(candidate.phi_op, "getParent", lambda: None)()
    if parent_block is None:
        return grouped
    for sibling_op in self._iter_block_ops(parent_block):
        if sibling_op is candidate.phi_op:
            continue
        if getattr(sibling_op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
            continue
        sibling = self._match_accumulator_phi_candidate(
            sibling_op,
            count_param,
            pointer_param,
            pointer_phis,
            index_phis,
            result_size=result_size,
        )
        if sibling is None:
            continue
        if not self._accumulator_phi_candidates_can_group(candidate, sibling):
            continue
        grouped.extend(list(sibling.load_progressions))
    unique_grouped: List[Dict[str, object]] = []
    seen_keys = set()
    for signature in grouped:
        load_op_ref = signature.get("load_op_ref")
        if isinstance(load_op_ref, PcodeOpRef):
            load_key = load_op_ref.stable_key()
        else:
            load_key = None
        signature_key = (
            load_key,
            int(signature.get("start_offset", 0) or 0),
            max(1, int(signature.get("element_size", 0) or 0)),
        )
        if signature_key in seen_keys:
            continue
        seen_keys.add(signature_key)
        unique_grouped.append(signature)
    return unique_grouped

def _impl__collect_load_progressions_from_varnode(
    self,
    varnode,
    pointer_param: dict,
    pointer_phis: Sequence[Dict[str, object]],
    index_phis: Sequence[Dict[str, object]],
    depth: int = 0,
    *,
    count_param: Optional[dict] = None,
    lsb_byte_offset: int = 0,
    narrowed_size: Optional[int] = None,
    result_size: Optional[int] = None,
    allow_signed_extension: bool = False,
) -> Optional[List[Dict[str, object]]]:
    if varnode is None or depth > 8:
        return None
    varnode = self._follow_readonly_load_addend_passthrough(varnode)
    if self._varnode_constant_value(varnode) == 0:
        return []
    if self._varnode_constant_value(varnode) is not None:
        return None

    def_op = getattr(varnode, "getDef", lambda: None)()
    if def_op is None:
        return None
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic == "LOAD":
        signature = self._match_load_progression(
            def_op,
            pointer_param,
            pointer_phis,
            index_phis,
        )
        if signature is None:
            return None
        adjusted = self._adjust_readonly_load_signature_access(
            signature,
            lsb_byte_offset=int(lsb_byte_offset),
            narrowed_size=narrowed_size,
        )
        return [adjusted] if adjusted is not None else None
    if mnemonic == "INT_ADD":
        left = self._collect_load_progressions_from_varnode(
            def_op.getInput(0),
            pointer_param,
            pointer_phis,
            index_phis,
            depth + 1,
            count_param=count_param,
            lsb_byte_offset=lsb_byte_offset,
            narrowed_size=narrowed_size,
            result_size=result_size,
            allow_signed_extension=allow_signed_extension,
        )
        right = self._collect_load_progressions_from_varnode(
            def_op.getInput(1),
            pointer_param,
            pointer_phis,
            index_phis,
            depth + 1,
            count_param=count_param,
            lsb_byte_offset=lsb_byte_offset,
            narrowed_size=narrowed_size,
            result_size=result_size,
            allow_signed_extension=allow_signed_extension,
        )
        if left is None or right is None:
            return None
        return left + right
    if mnemonic == "INT_SEXT":
        input_varnode = self._follow_readonly_load_addend_passthrough(def_op.getInput(0))
        input_size = max(1, int(getattr(input_varnode, "getSize", lambda: 0)() or 0))
        result_bytes = int(result_size or 0)
        if result_bytes <= 0:
            if not allow_signed_extension:
                return None
            return self._collect_load_progressions_from_varnode(
                input_varnode,
                pointer_param,
                pointer_phis,
                index_phis,
                depth + 1,
                count_param=count_param,
                lsb_byte_offset=lsb_byte_offset,
                narrowed_size=narrowed_size,
                result_size=None,
                allow_signed_extension=allow_signed_extension,
            )
        if result_bytes > input_size:
            self._debug(
                "Declined readonly load progression: INT_SEXT result size is incompatible "
                f"(result_size={result_size}, input_size={input_size})"
            )
            return None
        next_narrowed_size = (
            result_bytes
            if narrowed_size is None
            else min(int(narrowed_size), result_bytes)
        )
        return self._collect_load_progressions_from_varnode(
            input_varnode,
            pointer_param,
            pointer_phis,
            index_phis,
            depth + 1,
            count_param=count_param,
            lsb_byte_offset=lsb_byte_offset,
            narrowed_size=next_narrowed_size,
            result_size=result_size,
            allow_signed_extension=allow_signed_extension,
        )
    if mnemonic == "INT2FLOAT":
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 1:
            return None
        return self._collect_load_progressions_from_varnode(
            def_op.getInput(0),
            pointer_param,
            pointer_phis,
            index_phis,
            depth + 1,
            count_param=count_param,
            lsb_byte_offset=lsb_byte_offset,
            narrowed_size=narrowed_size,
            result_size=None,
            allow_signed_extension=True,
        )
    if mnemonic == "FLOAT_DIV":
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
            return None
        if not self._varnode_is_int_to_float_parameter(def_op.getInput(1), count_param):
            self._debug("Declined readonly FP accumulator candidate: FLOAT_DIV denominator is not count parameter")
            return None
        return self._collect_load_progressions_from_varnode(
            def_op.getInput(0),
            pointer_param,
            pointer_phis,
            index_phis,
            depth + 1,
            count_param=count_param,
            lsb_byte_offset=lsb_byte_offset,
            narrowed_size=narrowed_size,
            result_size=result_size,
            allow_signed_extension=allow_signed_extension,
        )
    if mnemonic in {"SUBPIECE", "INT_RIGHT", "INT_ZEXT", "CAST", "COPY"}:
        next_lsb_byte_offset = int(lsb_byte_offset)
        next_narrowed_size = narrowed_size
        if mnemonic == "SUBPIECE":
            byte_offset = self._varnode_constant_value(
                self._follow_readonly_load_addend_passthrough(def_op.getInput(1))
            )
            if byte_offset is None or int(byte_offset) < 0:
                return None
            output = getattr(def_op, "getOutput", lambda: None)()
            next_lsb_byte_offset += int(byte_offset)
            output_size = max(1, int(getattr(output, "getSize", lambda: 0)() or 0))
            next_narrowed_size = (
                output_size
                if next_narrowed_size is None
                else min(int(next_narrowed_size), output_size)
            )
        elif mnemonic == "INT_RIGHT":
            shift_bits = self._varnode_constant_value(
                self._follow_readonly_load_addend_passthrough(def_op.getInput(1))
            )
            if shift_bits is None or int(shift_bits) < 0 or (int(shift_bits) % 8) != 0:
                return None
            next_lsb_byte_offset += int(shift_bits) // 8
        elif mnemonic != "SUBPIECE" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 1:
            return None
        return self._collect_load_progressions_from_varnode(
            def_op.getInput(0),
            pointer_param,
            pointer_phis,
            index_phis,
            depth + 1,
            count_param=count_param,
            lsb_byte_offset=next_lsb_byte_offset,
            narrowed_size=next_narrowed_size,
            result_size=result_size,
            allow_signed_extension=allow_signed_extension,
        )
    if mnemonic == "INT_AND" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._follow_readonly_load_addend_passthrough(def_op.getInput(0))
        right = self._follow_readonly_load_addend_passthrough(def_op.getInput(1))
        left_const = self._varnode_constant_value(left)
        right_const = self._varnode_constant_value(right)
        if left_const is not None:
            mask_width = self._low_mask_width_bytes_from_value(int(left_const))
            if mask_width is None:
                return None
            return self._collect_load_progressions_from_varnode(
                right,
                pointer_param,
                pointer_phis,
                index_phis,
                depth + 1,
                count_param=count_param,
                lsb_byte_offset=lsb_byte_offset,
                narrowed_size=narrowed_size or mask_width,
                result_size=result_size,
                allow_signed_extension=allow_signed_extension,
            )
        if right_const is not None:
            mask_width = self._low_mask_width_bytes_from_value(int(right_const))
            if mask_width is None:
                return None
            return self._collect_load_progressions_from_varnode(
                left,
                pointer_param,
                pointer_phis,
                index_phis,
                depth + 1,
                count_param=count_param,
                lsb_byte_offset=lsb_byte_offset,
                narrowed_size=narrowed_size or mask_width,
                result_size=result_size,
                allow_signed_extension=allow_signed_extension,
            )
    return None

def _impl__match_load_progression(
    self,
    load_op,
    pointer_param: dict,
    pointer_phis: Sequence[Dict[str, object]],
    index_phis: Sequence[Dict[str, object]],
) -> Optional[Dict[str, int]]:
    output = getattr(load_op, "getOutput", lambda: None)()
    load_size = max(1, int(getattr(output, "getSize", lambda: 4)() or 4))
    address_varnode = self._follow_passthrough_varnode(load_op.getInput(1))
    address_def = getattr(address_varnode, "getDef", lambda: None)()
    mnemonic = getattr(address_def, "getMnemonic", lambda: None)() if address_def is not None else None
    contextual_pointer_phis = self._pointer_phis_for_load_context(
        pointer_phis,
        load_op,
        address_def,
    )
    contextual_index_phis = self._index_phis_for_load_context(
        index_phis,
        load_op,
        address_def,
    )
    if address_def is not None and mnemonic == "PTRADD" and int(getattr(address_def, "getNumInputs", lambda: 0)() or 0) >= 3:
        base_input = self._follow_passthrough_varnode(address_def.getInput(0))
        index_input = self._follow_passthrough_varnode(address_def.getInput(1))
        elem_size = self._varnode_constant_value(self._follow_passthrough_varnode(address_def.getInput(2)))
        constant_index = self._varnode_constant_value(index_input)
        if elem_size is not None and elem_size > 0 and constant_index is not None:
            for pointer_info in contextual_pointer_phis:
                if self._same_varnode_value(base_input, pointer_info["phi_output"]):
                    signature = self._load_progression_from_pointer_phi(
                        load_op,
                        pointer_info,
                        load_size=load_size,
                        extra_byte_offset=int(elem_size) * int(constant_index),
                    )
                    if signature is None:
                        return None
                    return {
                        **signature,
                    }
        index_info = self._matched_index_progression(index_input, contextual_index_phis)
        if (
            elem_size is not None
            and elem_size > 0
            and self._varnode_matches_parameter(base_input, pointer_param)
            and index_info is not None
        ):
            return {
                "load_op_ref": self._make_pcode_op_ref(load_op),
                "induction_phi_ref": self._make_pcode_op_ref(index_info.get("phi_op")),
                "stride": int(elem_size) * int(index_info.get("step", 1) or 1),
                "element_size": load_size,
                "start_offset": int(elem_size) * int(index_info.get("start", 0) or 0),
                "start_index": int(index_info.get("start", 0) or 0),
                "index_step": int(index_info.get("step", 1) or 1),
                "index_scale": int(elem_size),
            }
    if address_def is not None and mnemonic == "INT_ADD" and int(getattr(address_def, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._follow_passthrough_varnode(address_def.getInput(0))
        right = self._follow_passthrough_varnode(address_def.getInput(1))
        for pointer_info in contextual_pointer_phis:
            if self._same_varnode_value(left, pointer_info["phi_output"]) and self._varnode_constant_value(right) == 0:
                return self._load_progression_from_pointer_phi(
                    load_op,
                    pointer_info,
                    load_size=load_size,
                )
            if self._same_varnode_value(right, pointer_info["phi_output"]) and self._varnode_constant_value(left) == 0:
                return self._load_progression_from_pointer_phi(
                    load_op,
                    pointer_info,
                    load_size=load_size,
                )
        if self._varnode_matches_parameter(left, pointer_param):
            scaled = self._scaled_index_stride_and_start(right, contextual_index_phis)
            if scaled is not None and scaled[0] > 0:
                induction_info = self._induction_info_from_scaled_index(right, contextual_index_phis)
                return {
                    "load_op_ref": self._make_pcode_op_ref(load_op),
                    "induction_phi_ref": self._make_pcode_op_ref(induction_info.get("phi_op") if induction_info else None),
                    "stride": int(scaled[0]),
                    "element_size": load_size,
                    "start_offset": int(scaled[1]),
                    "start_index": int(scaled[2]),
                    "index_step": int(scaled[3]),
                    "index_scale": int(scaled[4]),
                }
        if self._varnode_matches_parameter(right, pointer_param):
            scaled = self._scaled_index_stride_and_start(left, contextual_index_phis)
            if scaled is not None and scaled[0] > 0:
                induction_info = self._induction_info_from_scaled_index(left, contextual_index_phis)
                return {
                    "load_op_ref": self._make_pcode_op_ref(load_op),
                    "induction_phi_ref": self._make_pcode_op_ref(induction_info.get("phi_op") if induction_info else None),
                    "stride": int(scaled[0]),
                    "element_size": load_size,
                    "start_offset": int(scaled[1]),
                    "start_index": int(scaled[2]),
                    "index_step": int(scaled[3]),
                    "index_scale": int(scaled[4]),
                }
    if address_def is not None and mnemonic == "MULTIEQUAL":
        pointer_info = self._match_pointer_progression_phi_by_storage(
            address_def,
            pointer_param,
        )
        if pointer_info is not None:
            return self._load_progression_from_pointer_phi(
                load_op,
                pointer_info,
                load_size=load_size,
            )
    for pointer_info in contextual_pointer_phis:
        if self._same_varnode_value(address_varnode, pointer_info["phi_output"]):
            return self._load_progression_from_pointer_phi(
                load_op,
                pointer_info,
                load_size=load_size,
            )
    self._debug(
        "Declined readonly load progression: address shape unsupported "
        f"(mnemonic={mnemonic}, pointer_phis={len(contextual_pointer_phis)}, index_phis={len(contextual_index_phis)})"
    )
    return None

def _impl__build_arithmetic_progression_sum(
    self,
    first_term: Expression,
    count: Expression,
    size: int,
) -> Expression:
    one = Expression.constant(1, size)
    count_minus_one = Expression.binary_op("INT_SUB", count, one)
    count_minus_one.size = size
    tail = Expression.binary_op("INT_ADD", first_term, count_minus_one)
    tail.size = size
    pair_sum = Expression.binary_op("INT_ADD", first_term, tail)
    pair_sum.size = size
    product = Expression.binary_op("INT_MULT", count, pair_sum)
    product.size = size
    half = Expression.binary_op("INT_SDIV", product, Expression.constant(2, size))
    half.size = size
    return half

def _impl__extract_affine_term(
    self,
    expr: Expression,
    param_name: str,
    bit_width_hint: Optional[int] = None,
) -> Optional[Tuple[int, int]]:
    normalized_counter = self._normalize_counter_view(expr, param_name)
    if normalized_counter is not None:
        return 1, 0
    if expr.expr_type == ExpressionType.CONSTANT:
        signed_value = self._signed_constant_value(expr, bit_width_hint=bit_width_hint)
        if signed_value is None:
            return None
        return 0, signed_value
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"} and len(expr.operands) == 1:
        operand = self._extract_affine_term(
            expr.operands[0],
            param_name,
            bit_width_hint=bit_width_hint,
        )
        if operand is None:
            return None
        coeff, bias = operand
        return -coeff, -bias
    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None

    node_bit_width = bit_width_hint or self._infer_counter_bit_width(expr, param_name)
    left = self._extract_affine_term(expr.operands[0], param_name, bit_width_hint=node_bit_width)
    right = self._extract_affine_term(expr.operands[1], param_name, bit_width_hint=node_bit_width)

    if expr.operator == "INT_ADD" and left is not None and right is not None:
        return left[0] + right[0], left[1] + right[1]
    if expr.operator == "INT_SUB" and left is not None and right is not None:
        return left[0] - right[0], left[1] - right[1]
    if expr.operator == "INT_MULT":
        left_const = self._signed_constant_value(expr.operands[0], bit_width_hint=node_bit_width)
        right_const = self._signed_constant_value(expr.operands[1], bit_width_hint=node_bit_width)
        if left_const is not None and right is not None:
            return left_const * right[0], left_const * right[1]
        if right_const is not None and left is not None:
            return right_const * left[0], right_const * left[1]
    return None

def _impl__extract_affine_placeholder_term(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    bit_width_hint: Optional[int] = None,
) -> Optional[Tuple[int, int]]:
    expr = self._canonicalize_expression(expr)
    if expr is None:
        return None
    if bit_width_hint is None:
        bit_width_hint = max(1, int(getattr(placeholder, "size", 0) or 4)) * 8
    try:
        if expr.structural_key() == placeholder.structural_key():
            return 1, 0
    except (AttributeError, TypeError, ValueError, RecursionError):
        return None
    if expr.expr_type == ExpressionType.CONSTANT:
        signed_value = self._signed_constant_value(expr, bit_width_hint=bit_width_hint)
        if signed_value is None:
            return None
        return 0, signed_value
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"} and len(expr.operands) == 1:
        operand = self._extract_affine_placeholder_term(
            expr.operands[0],
            placeholder,
            bit_width_hint=bit_width_hint,
        )
        if operand is None:
            return None
        coeff, bias = operand
        return -coeff, -bias
    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None

    node_bit_width = bit_width_hint or (expr.size * 8 if expr.size else None)
    left = self._extract_affine_placeholder_term(
        expr.operands[0],
        placeholder,
        bit_width_hint=node_bit_width,
    )
    right = self._extract_affine_placeholder_term(
        expr.operands[1],
        placeholder,
        bit_width_hint=node_bit_width,
    )

    if expr.operator == "INT_ADD" and left is not None and right is not None:
        return left[0] + right[0], left[1] + right[1]
    if expr.operator == "INT_SUB" and left is not None and right is not None:
        return left[0] - right[0], left[1] - right[1]
    if expr.operator == "INT_MULT":
        left_const = self._signed_constant_value(expr.operands[0], bit_width_hint=node_bit_width)
        right_const = self._signed_constant_value(expr.operands[1], bit_width_hint=node_bit_width)
        if left_const is not None and right is not None:
            return left_const * right[0], left_const * right[1]
        if right_const is not None and left is not None:
            return right_const * left[0], right_const * left[1]
    return None

def _impl__solve_counter_affine_equality(
    self,
    expr: Optional[Expression],
    other_const: Optional[int],
    operator: Optional[str],
    negated: bool,
    param_name: str,
) -> Optional[int]:
    if (
        expr is None
        or other_const is None
        or operator not in {"INT_EQUAL", "INT_NOTEQUAL"}
    ):
        return None
    if operator == "INT_EQUAL" and negated:
        return None
    if operator == "INT_NOTEQUAL" and not negated:
        return None

    bit_width_hint = self._infer_counter_bit_width(expr, param_name)
    affine = self._extract_affine_term(expr, param_name, bit_width_hint=bit_width_hint)
    if affine is None:
        return None
    coeff, bias = affine
    if coeff != 1:
        return None
    return other_const - bias
