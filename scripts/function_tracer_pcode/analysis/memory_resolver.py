# -*- coding: utf-8 -*-
"""Helpers for concretizing simple read-only memory loads."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.analysis.condition.normalizer import ConditionNormalizer
from scripts.function_tracer_pcode.core import (
    AddressValueRef,
    Condition,
    Expression,
    ExpressionType,
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
    ReadonlyReductionRef,
)


MAX_ENUMERATED_INDEX_VALUES = 16


@dataclass
class IndexedAddressPattern:
    """A small subset of address expressions: base + offset + index * scale."""

    base_ref: Optional[AddressValueRef]
    base_address: int
    scale: int
    index_expr: Expression
    index_param_name: str
    index_bits: int
    const_offset: int = 0


def collect_memory_bit_widths_from_analysis(analysis) -> List[int]:
    """Return sorted memory load widths (in bits) used by an analysis result."""
    widths = set()
    for ret_info in getattr(analysis, "returns", []) or []:
        _collect_memory_bit_widths_from_expr(ret_info.value, widths)
        for cond in ret_info.conditions or []:
            _collect_memory_bit_widths_from_expr(cond.expression, widths)
    return sorted(widths)


def _collect_memory_bit_widths_from_expr(expr: Optional[Expression], widths: set) -> None:
    """Recursively collect bit widths of MEMORY expressions."""
    if expr is None:
        return

    if expr.expr_type == ExpressionType.MEMORY:
        widths.add(expr.get_bit_width())
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, ReadonlyReductionRef):
        _collect_readonly_reduction_memory_widths(runtime_ref, widths)

    for operand in getattr(expr, "operands", ()) or ():
        _collect_memory_bit_widths_from_expr(operand, widths)

    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and hasattr(cond, "expression"):
                _collect_memory_bit_widths_from_expr(cond.expression, widths)
            _collect_memory_bit_widths_from_expr(value, widths)


def _collect_readonly_reduction_memory_widths(
    reduction_ref: ReadonlyReductionRef,
    widths: set,
) -> None:
    for source in (
        reduction_ref,
        getattr(reduction_ref, "loop_summary", None),
        getattr(reduction_ref, "accumulator_proof", None),
        getattr(getattr(reduction_ref, "loop_summary", None), "term_descriptor", None),
    ):
        if source is None:
            continue
        for attr in ("element_size", "result_size"):
            try:
                size = int(getattr(source, attr, 0) or 0)
            except (TypeError, ValueError):
                size = 0
            if size > 0:
                widths.add(size * 8)

    for terms in (
        getattr(reduction_ref, "semantic_witnesses", ()) or (),
        getattr(getattr(reduction_ref, "accumulator_proof", None), "seed_terms", ()) or (),
        getattr(getattr(reduction_ref, "accumulator_proof", None), "loop_body_witnesses", ()) or (),
        getattr(getattr(reduction_ref, "accumulator_proof", None), "exact_return_witnesses", ()) or (),
    ):
        for item in terms:
            nested_terms = getattr(item, "terms", None)
            if nested_terms is None:
                nested_terms = (item,)
            for term in nested_terms or ():
                try:
                    access_size = int(getattr(term, "access_size", 0) or 0)
                except (TypeError, ValueError):
                    access_size = 0
                if access_size > 0:
                    widths.add(access_size * 8)


def concretize_readonly_loads(
    expr: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
    read_memory_value: Callable[[int, int], Optional[int]],
    image_base: Optional[int] = None,
    debug: bool = False,
) -> Expression:
    """Replace simple read-only indexed loads with a finite PHI/ITE over constants."""
    return _rewrite_expr(
        expr,
        list(conditions or []),
        list(parameters or []),
        read_memory_value,
        image_base,
        debug,
        False,
    )


def _rewrite_expr(
    expr: Expression,
    conditions: List[Condition],
    parameters: List[Dict],
    read_memory_value: Callable[[int, int], Optional[int]],
    image_base: Optional[int],
    debug: bool,
    address_context: bool,
) -> Expression:
    if expr is None:
        return expr

    direct_scalar = _try_resolve_direct_readonly_scalar(
        expr,
        read_memory_value,
        image_base,
        address_context,
        debug,
    )
    if direct_scalar is not None:
        return direct_scalar

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = _rewrite_expr(
            expr.operands[0],
            conditions,
            parameters,
            read_memory_value,
            image_base,
            debug,
            True,
        )
        candidate = expr.clone_with(operands=[rewritten_addr])
        split_phi = _split_memory_address_phi(candidate)
        if split_phi is not None:
            return _rewrite_expr(
                split_phi,
                conditions,
                parameters,
                read_memory_value,
                image_base,
                debug,
                address_context,
            )
        split_conditional = _split_conditional_offset_load(candidate)
        if split_conditional is not None:
            return _rewrite_expr(
                split_conditional,
                conditions,
                parameters,
                read_memory_value,
                image_base,
                debug,
                address_context,
            )
        resolved = _try_resolve_readonly_load(
            candidate,
            conditions,
            parameters,
            read_memory_value,
            image_base,
            debug,
        )
        return resolved or candidate

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.INTRINSIC):
        rewritten_operands = [
            _rewrite_expr(
                op,
                conditions,
                parameters,
                read_memory_value,
                image_base,
                debug,
                address_context,
            )
            for op in expr.operands
        ]
        if all(new is old for new, old in zip(rewritten_operands, expr.operands)):
            return expr
        rebuilt = expr.clone_with(operands=rewritten_operands)
        return rebuilt

    if expr.expr_type == ExpressionType.PHI and expr.value:
        rewritten_branches = []
        changed = False
        for cond, value in expr.value:
            new_value = _rewrite_expr(
                value,
                conditions,
                parameters,
                read_memory_value,
                image_base,
                debug,
                address_context,
            )
            rewritten_branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(rewritten_branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr


def _try_resolve_direct_readonly_scalar(
    expr: Expression,
    read_memory_value: Callable[[int, int], Optional[int]],
    image_base: Optional[int],
    address_context: bool,
    debug: bool,
) -> Optional[Expression]:
    if address_context:
        return None

    runtime_ref = _coerce_address_runtime_ref(expr)
    if (
        expr.expr_type == ExpressionType.CONSTANT
        and runtime_ref is not None
        and runtime_ref.has_concrete_address()
        and runtime_ref.is_readonly_memory()
        and runtime_ref.source != "constant_offset"
    ):
        load_size = expr.size if expr.size else 8
        mem_value = read_memory_value(runtime_ref.address_offset, load_size)
        if mem_value is None:
            return None
        if debug:
            print(
                "[MemoryResolver] concretized direct readonly constant address "
                f"addr=0x{runtime_ref.address_offset:x} size={load_size} -> 0x{mem_value:x}"
            )
        return Expression.constant(mem_value, load_size)

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INDIRECT"
        and getattr(expr, "operands", None)
    ):
        load_size = expr.size if expr.size else (expr.operands[0].size if expr.operands else 8)
        direct_addr = _resolve_direct_readonly_address(
            expr.operands[0],
            load_size,
            read_memory_value,
            image_base,
        )
        if direct_addr is None:
            return None
        mem_value = read_memory_value(direct_addr, load_size)
        if mem_value is None:
            return None
        if debug:
            print(
                "[MemoryResolver] concretized direct readonly binary INDIRECT "
                f"addr=0x{direct_addr:x} size={load_size} -> 0x{mem_value:x}"
            )
        return Expression.constant(mem_value, load_size)

    if expr.expr_type != ExpressionType.VARIABLE or not expr.name:
        if address_context:
            return None
        if (
            expr.expr_type == ExpressionType.INTRINSIC
            and (getattr(expr, "name", None) or "") == "INDIRECT"
            and getattr(expr, "operands", None)
        ):
            load_size = expr.size if expr.size else (expr.operands[0].size if expr.operands else 8)
            direct_addr = _resolve_direct_readonly_address(
                expr.operands[0],
                load_size,
                read_memory_value,
                image_base,
            )
            if direct_addr is None:
                return None
            mem_value = read_memory_value(direct_addr, load_size)
            if mem_value is None:
                return None
            if debug:
                print(
                    "[MemoryResolver] concretized direct readonly INDIRECT "
                    f"addr=0x{direct_addr:x} size={load_size} -> 0x{mem_value:x}"
                )
            return Expression.constant(mem_value, load_size)
        return None

    direct_addr = _resolve_direct_readonly_address(
        expr,
        expr.size if expr.size else 8,
        read_memory_value,
        image_base,
    )
    if direct_addr is None:
        return None

    load_size = expr.size if expr.size else 8
    mem_value = read_memory_value(direct_addr, load_size)
    if mem_value is None:
        return None
    if debug:
        print(
            "[MemoryResolver] concretized direct readonly scalar "
            f"addr=0x{direct_addr:x} size={load_size} -> 0x{mem_value:x}"
        )
    return Expression.constant(mem_value, load_size)


def _split_memory_address_phi(expr: Expression) -> Optional[Expression]:
    if expr.expr_type != ExpressionType.MEMORY or not expr.operands:
        return None

    addr = expr.operands[0]
    if addr.expr_type != ExpressionType.PHI or not addr.value:
        return None

    branches = []
    for cond, branch_addr in addr.value:
        branches.append((cond, expr.clone_with(operands=[branch_addr])))

    split = Expression.phi(branches)
    split.size = expr.size
    return split


def _split_conditional_offset_load(expr: Expression) -> Optional[Expression]:
    if expr.expr_type != ExpressionType.MEMORY or not expr.operands:
        return None

    pattern = _extract_conditional_offset_pattern(expr.operands[0])
    if pattern is None:
        return None

    cond_expr, base_addr, offset_value = pattern
    branches = [
        (
            Condition(cond_expr, False),
            expr.clone_with(
                operands=[
                    Expression.binary_op(
                        "INT_ADD",
                        base_addr,
                        Expression.constant(offset_value, max(1, base_addr.size or 8)),
                    )
                ],
            ),
        ),
        (None, expr.clone_with(operands=[base_addr])),
    ]
    split = Expression.phi(branches)
    split.size = expr.size
    return split


def _extract_conditional_offset_pattern(
    addr_expr: Expression,
) -> Optional[Tuple[Expression, Expression, int]]:
    if (
        addr_expr.expr_type != ExpressionType.BINARY_OP
        or addr_expr.operator != "INT_ADD"
        or len(addr_expr.operands) != 2
    ):
        return None

    left, right = addr_expr.operands
    scaled = _extract_bool_scaled_constant(right)
    if scaled is not None:
        cond_expr, offset_value = scaled
        return cond_expr, left, offset_value

    scaled = _extract_bool_scaled_constant(left)
    if scaled is not None:
        cond_expr, offset_value = scaled
        return cond_expr, right, offset_value

    return None


def _extract_bool_scaled_constant(expr: Expression) -> Optional[Tuple[Expression, int]]:
    if (
        expr.expr_type != ExpressionType.BINARY_OP
        or expr.operator != "INT_MULT"
        or len(expr.operands) != 2
    ):
        return None

    left, right = expr.operands

    if right.expr_type == ExpressionType.CONSTANT and isinstance(right.value, int):
        bool_expr = _unwrap_bool_to_bitvec(left)
        if bool_expr is not None:
            return bool_expr, right.value

    if left.expr_type == ExpressionType.CONSTANT and isinstance(left.value, int):
        bool_expr = _unwrap_bool_to_bitvec(right)
        if bool_expr is not None:
            return bool_expr, left.value

    return None


def _unwrap_bool_to_bitvec(expr: Expression) -> Optional[Expression]:
    if _is_boolean_expr(expr):
        return expr

    if (
        expr.expr_type == ExpressionType.UNARY_OP
        and expr.operator in {"INT_ZEXT", "INT_SEXT"}
        and expr.operands
        and _is_boolean_expr(expr.operands[0])
    ):
        return expr.operands[0]

    return None


def _is_boolean_expr(expr: Expression) -> bool:
    return (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator in {
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_SLESS",
            "INT_LESSEQUAL",
            "INT_SLESSEQUAL",
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
        }
    )


def _try_resolve_readonly_load(
    expr: Expression,
    conditions: List[Condition],
    parameters: List[Dict],
    read_memory_value: Callable[[int, int], Optional[int]],
    image_base: Optional[int],
    debug: bool,
) -> Optional[Expression]:
    if expr.expr_type != ExpressionType.MEMORY or not expr.operands:
        return None

    load_size = expr.size if expr.size else 4
    direct_addr = _resolve_direct_readonly_address(
        expr.operands[0],
        load_size,
        read_memory_value,
        image_base,
    )
    if direct_addr is not None:
        mem_value = read_memory_value(direct_addr, load_size)
        if mem_value is not None:
            if debug:
                print(
                    "[MemoryResolver] concretized direct readonly load "
                    f"addr=0x{direct_addr:x} size={load_size} -> 0x{mem_value:x}"
                )
            return Expression.constant(mem_value, load_size)

    pattern = _extract_indexed_pattern(expr.operands[0])
    if pattern is None:
        return None

    param_info = _get_parameter_info(parameters, pattern.index_param_name)
    if param_info is None:
        return None

    candidate_indices = _enumerate_candidate_indices(pattern, conditions, param_info, debug)
    if not candidate_indices:
        if debug:
            cond_strs = [cond.to_string() for cond in conditions]
            print(
                "[MemoryResolver] no candidate indices for "
                f"{pattern.index_param_name} with conditions {cond_strs}"
            )
        return None

    branches = []
    index_size_bytes = max(1, pattern.index_bits // 8)
    fallback = expr
    resolved_base = _resolve_readonly_base_address(
        pattern,
        candidate_indices,
        load_size,
        read_memory_value,
        image_base,
    )
    if resolved_base is None:
        if debug:
            print(
                "[MemoryResolver] unable to resolve readonly base "
                f"symbol=0x{pattern.base_address:x} const_offset=0x{pattern.const_offset:x}"
            )
        return None
    if debug:
        print(
            "[MemoryResolver] readonly base resolved to "
            f"0x{resolved_base:x} (symbol=0x{pattern.base_address:x}, const_offset=0x{pattern.const_offset:x})"
        )

    for index_value in candidate_indices:
        addr = resolved_base + pattern.const_offset + pattern.scale * index_value
        mem_value = read_memory_value(addr, load_size)
        if mem_value is None:
            return None
        cond_expr = Expression.binary_op(
            "INT_EQUAL",
            pattern.index_expr,
            Expression.constant(index_value, index_size_bytes),
        )
        branches.append((Condition(cond_expr, False), Expression.constant(mem_value, load_size)))
        if debug:
            print(
                "[MemoryResolver] concretized load "
                f"addr=0x{addr:x} size={load_size} index={index_value} -> 0x{mem_value:x}"
            )

    branches.append((None, fallback))
    resolved = Expression.phi(branches)
    resolved.size = expr.size
    return resolved


def _resolve_direct_readonly_address(
    addr_expr: Expression,
    load_size: int,
    read_memory_value: Callable[[int, int], Optional[int]],
    image_base: Optional[int],
) -> Optional[int]:
    flattened = _flatten_additive_terms(addr_expr)
    if flattened is None:
        return None

    const_total, symbolic_bases, scaled_terms = flattened
    if scaled_terms or len(symbolic_bases) > 1:
        return None

    candidates: List[int] = []

    def _append(value: Optional[int]) -> None:
        if value is None:
            return
        if value < 0:
            return
        if value not in candidates:
            candidates.append(value)

    if symbolic_bases:
        _append(symbolic_bases[0].address_offset + const_total)
        if image_base is not None:
            _append(image_base + const_total)
    else:
        _append(const_total)

    for candidate in candidates:
        if read_memory_value(candidate, load_size) is not None:
            return candidate
    return None


def _extract_indexed_pattern(addr_expr: Expression) -> Optional[IndexedAddressPattern]:
    flattened = _flatten_additive_terms(addr_expr)
    if flattened is None:
        return None

    const_total, symbolic_bases, scaled_terms = flattened
    if len(scaled_terms) != 1:
        return None
    if len(symbolic_bases) > 1:
        return None

    index_expr, scale = scaled_terms[0]
    param_name, index_bits = _extract_index_param(index_expr)
    if not param_name or index_bits <= 0:
        return None

    return IndexedAddressPattern(
        base_ref=symbolic_bases[0] if symbolic_bases else None,
        base_address=symbolic_bases[0].address_offset if symbolic_bases else 0,
        const_offset=const_total,
        scale=scale,
        index_expr=index_expr,
        index_param_name=param_name,
        index_bits=index_bits,
    )


def _flatten_additive_terms(
    expr: Expression,
) -> Optional[Tuple[int, List[AddressValueRef], List[Tuple[Expression, int]]]]:
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD" and len(expr.operands) == 2:
        left_flat = _flatten_additive_terms(expr.operands[0])
        right_flat = _flatten_additive_terms(expr.operands[1])
        if left_flat is None or right_flat is None:
            return None
        left_const, left_bases, left_terms = left_flat
        right_const, right_bases, right_terms = right_flat
        return left_const + right_const, left_bases + right_bases, left_terms + right_terms

    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_MULT" and len(expr.operands) == 2:
        left, right = expr.operands
        if left.expr_type == ExpressionType.CONSTANT and left.value == 1:
            return _flatten_additive_terms(right)
        if right.expr_type == ExpressionType.CONSTANT and right.value == 1:
            return _flatten_additive_terms(left)

    if expr.expr_type == ExpressionType.INTRINSIC:
        opcode = getattr(expr, "opcode", None)
        mnemonic = getattr(expr, "name", None) or ""
        operands = getattr(expr, "operands", None) or []

        if (opcode == PTRSUB_OPCODE or mnemonic == "PTRSUB") and len(operands) == 2:
            left_flat = _flatten_additive_terms(operands[0])
            right_flat = _flatten_additive_terms(operands[1])
            if left_flat is None or right_flat is None:
                return None
            left_const, left_bases, left_terms = left_flat
            right_const, right_bases, right_terms = right_flat
            return left_const + right_const, left_bases + right_bases, left_terms + right_terms

        if (opcode == PTRADD_OPCODE or mnemonic == "PTRADD") and len(operands) == 3:
            base_flat = _flatten_additive_terms(operands[0])
            if base_flat is None:
                return None
            multiplied_index = Expression.binary_op("INT_MULT", operands[1], operands[2])
            index_flat = _flatten_additive_terms(multiplied_index)
            if index_flat is None:
                return None
            base_const, base_refs, base_terms = base_flat
            index_const, index_refs, index_terms = index_flat
            return (
                base_const + index_const,
                base_refs + index_refs,
                base_terms + index_terms,
            )

    symbolic_base = _extract_symbolic_base_address(expr)
    if symbolic_base is not None:
        return 0, [symbolic_base], []

    const_value = _extract_constant_address(expr)
    if const_value is not None:
        return const_value, [], []

    scaled = _extract_scaled_index(expr)
    if scaled is not None:
        return 0, [], [scaled]

    return None


def _extract_symbolic_base_address(expr: Expression) -> Optional[AddressValueRef]:
    runtime_ref = _coerce_address_runtime_ref(expr)
    if runtime_ref is None or not runtime_ref.has_concrete_address():
        return None
    return runtime_ref


def _extract_constant_address(expr: Expression) -> Optional[int]:
    if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
        return expr.value

    return None


def _coerce_address_runtime_ref(expr: Optional[Expression]) -> Optional[AddressValueRef]:
    if expr is None:
        return None

    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, AddressValueRef):
        return runtime_ref
    return None


def _resolve_readonly_base_address(
    pattern: IndexedAddressPattern,
    candidate_indices: Sequence[int],
    load_size: int,
    read_memory_value: Callable[[int, int], Optional[int]],
    image_base: Optional[int],
) -> Optional[int]:
    """Pick a base interpretation that makes the readonly table readable.

    MIPS PIC often materializes jump tables as PTR_<got-slot> + constant_offset.
    The PTR symbol address is only a relocation anchor, so the useful base can be
    the image base rather than the symbol address itself.
    """
    candidates: List[int] = []

    def _append(value: Optional[int]) -> None:
        if value is None:
            return
        if value not in candidates:
            candidates.append(value)

    _append(pattern.base_address)
    pointer_size = max(8, load_size)
    if pattern.base_address:
        pointee = read_memory_value(pattern.base_address, pointer_size)
        _append(pointee)
        if image_base is not None and pointee is not None:
            _append(image_base + pointee)

    _append(0)
    _append(image_base)

    for base in candidates:
        if base is None:
            continue
        all_readable = True
        for index_value in candidate_indices:
            addr = base + pattern.const_offset + pattern.scale * index_value
            if read_memory_value(addr, load_size) is None:
                all_readable = False
                break
        if all_readable:
            return base

    return None


def _extract_scaled_index(expr: Expression) -> Optional[Tuple[Expression, int]]:
    param_name, _ = _extract_index_param(expr)
    if param_name:
        return expr, 1

    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_MULT" or len(expr.operands) != 2:
        return None

    left, right = expr.operands

    if right.expr_type == ExpressionType.CONSTANT and isinstance(right.value, int):
        inner = _extract_scaled_index(left)
        if inner is not None:
            inner_expr, inner_scale = inner
            return inner_expr, inner_scale * right.value

    if left.expr_type == ExpressionType.CONSTANT and isinstance(left.value, int):
        inner = _extract_scaled_index(right)
        if inner is not None:
            inner_expr, inner_scale = inner
            return inner_expr, inner_scale * left.value

    return None


def _extract_index_param(expr: Expression) -> Tuple[Optional[str], int]:
    if expr.expr_type == ExpressionType.PARAMETER and expr.name:
        return expr.name, expr.get_bit_width()

    if (
        expr.expr_type == ExpressionType.UNARY_OP
        and expr.operator in {"INT_SEXT", "INT_ZEXT", "CAST", "COPY", "TRUNC"}
        and expr.operands
    ):
        return _extract_index_param(expr.operands[0])

    if expr.expr_type == ExpressionType.BINARY_OP:
        if expr.operator == "SUBPIECE" and len(expr.operands) == 2:
            source, offset = expr.operands
            if offset.expr_type == ExpressionType.CONSTANT and offset.value == 0:
                name, _ = _extract_index_param(source)
                return name, expr.get_bit_width()

        if expr.operator == "INT_AND" and len(expr.operands) == 2:
            left, right = expr.operands
            if right.expr_type == ExpressionType.CONSTANT and right.value == 0xFFFFFFFF:
                name, _ = _extract_index_param(left)
                return name, 32
            if left.expr_type == ExpressionType.CONSTANT and left.value == 0xFFFFFFFF:
                name, _ = _extract_index_param(right)
                return name, 32

    return None, 0


def _get_parameter_info(parameters: Sequence[Dict], name: str) -> Optional[Dict]:
    for param in parameters:
        if param.get("name") == name:
            return param
    return None


def _enumerate_candidate_indices(
    pattern: IndexedAddressPattern,
    conditions: List[Condition],
    param_info: Dict,
    debug: bool,
) -> List[int]:
    nonneg, upper_bound = _extract_index_range(conditions, pattern.index_param_name)
    if upper_bound is None or upper_bound <= 0:
        if debug:
            print(
                "[MemoryResolver] upper bound unavailable for "
                f"{pattern.index_param_name} (nonneg={nonneg}, upper_bound={upper_bound})"
            )
        return []

    is_unsigned = (
        not param_info.get("is_signed", True)
        or _index_expr_guarantees_nonnegative(pattern.index_expr, pattern.index_param_name)
    )
    if not is_unsigned and not nonneg:
        if debug:
            print(
                "[MemoryResolver] signed index lacks non-negative proof for "
                f"{pattern.index_param_name}"
            )
        return []

    if upper_bound > MAX_ENUMERATED_INDEX_VALUES:
        return []

    indices = list(range(0, upper_bound))
    if debug:
        print(
            f"[MemoryResolver] candidate indices for {pattern.index_param_name}: {indices}"
        )
    return indices


def _index_expr_guarantees_nonnegative(expr: Optional[Expression], param_name: str) -> bool:
    if expr is None:
        return False

    if expr.expr_type == ExpressionType.PARAMETER and expr.name == param_name:
        return False

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        if expr.operator == "INT_ZEXT":
            inner_name, _ = _extract_index_param(expr.operands[0])
            return inner_name == param_name
        if expr.operator in {"CAST", "COPY", "TRUNC"}:
            return _index_expr_guarantees_nonnegative(expr.operands[0], param_name)
        return False

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left, right = expr.operands
        if expr.operator == "INT_AND":
            left_name, _ = _extract_index_param(left)
            right_name, _ = _extract_index_param(right)
            if left_name == param_name and _extract_integer_constant(right) is not None:
                return True
            if right_name == param_name and _extract_integer_constant(left) is not None:
                return True
        if expr.operator == "SUBPIECE":
            offset = _extract_integer_constant(right)
            left_name, _ = _extract_index_param(left)
            if left_name == param_name and offset == 0:
                return True

    return False


def _extract_index_range(
    conditions: List[Condition],
    param_name: str,
) -> Tuple[bool, Optional[int]]:
    """Extract a conservative [0, upper_bound) range for a parameter."""
    nonneg = False
    upper_bound: Optional[int] = None

    for cond in conditions:
        comparison = _extract_positive_comparison(cond)
        if comparison is None:
            continue
        left_expr, op, right_expr = comparison

        if op == "INT_SLESS":
            if (_is_zero_constant(left_expr) or _is_minus_one_constant(left_expr)) and _matches_index_param(
                right_expr, param_name
            ):
                nonneg = True
            elif _matches_index_param(left_expr, param_name):
                bound = _extract_nonnegative_constant_value(right_expr)
                if bound is not None:
                    upper_bound = bound if upper_bound is None else min(upper_bound, bound)
        elif op == "INT_LESS":
            if _matches_index_param(left_expr, param_name):
                bound = _extract_nonnegative_constant_value(right_expr)
                if bound is not None:
                    upper_bound = bound if upper_bound is None else min(upper_bound, bound)
        elif op == "INT_LESSEQUAL":
            if _matches_index_param(left_expr, param_name):
                bound = _extract_nonnegative_constant_value(right_expr)
                if bound is not None:
                    upper_bound_value = bound + 1
                    upper_bound = (
                        upper_bound_value if upper_bound is None else min(upper_bound, upper_bound_value)
                    )
        elif op == "INT_SLESSEQUAL":
            if _is_zero_constant(left_expr) and _matches_index_param(right_expr, param_name):
                nonneg = True
            elif _matches_index_param(left_expr, param_name):
                bound = _extract_nonnegative_constant_value(right_expr)
                if bound is not None:
                    upper_bound_value = bound + 1
                    upper_bound = (
                        upper_bound_value if upper_bound is None else min(upper_bound, upper_bound_value)
                    )

    return nonneg, upper_bound


def _extract_positive_comparison(
    condition: Condition,
) -> Optional[Tuple[Expression, str, Expression]]:
    expr = condition.expression
    negated = condition.negated

    while (
        expr is not None
        and expr.expr_type == ExpressionType.UNARY_OP
        and expr.operator == "BOOL_NEGATE"
        and expr.operands
    ):
        negated = not negated
        expr = expr.operands[0]

    if (
        expr is None
        or expr.expr_type != ExpressionType.BINARY_OP
        or len(expr.operands) != 2
        or expr.operator not in {"INT_SLESS", "INT_SLESSEQUAL", "INT_LESS", "INT_LESSEQUAL"}
    ):
        return None

    left_expr, right_expr = expr.operands
    op = expr.operator
    if negated:
        return right_expr, ConditionNormalizer._negate_comparison_op(op), left_expr
    return left_expr, op, right_expr


def _extract_nonnegative_constant_value(expr: Expression) -> Optional[int]:
    value = _extract_integer_constant(expr)
    if value is None or value < 0:
        return None
    return value


def _extract_integer_constant(expr: Optional[Expression]) -> Optional[int]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
        return int(expr.value)

    if (
        expr.expr_type == ExpressionType.UNARY_OP
        and expr.operator in {"CAST", "COPY", "INT_ZEXT", "INT_SEXT"}
        and expr.operands
    ):
        return _extract_integer_constant(expr.operands[0])

    return None


def _matches_index_param(expr: Expression, param_name: str) -> bool:
    name, _ = _extract_index_param(expr)
    return name == param_name


def _is_zero_constant(expr: Expression) -> bool:
    value = _extract_integer_constant(expr)
    return value == 0


def _is_minus_one_constant(expr: Expression) -> bool:
    value = _extract_integer_constant(expr)
    if value == -1:
        return True
    if value is None:
        return False
    bit_width = max(1, expr.get_bit_width())
    mask = (1 << bit_width) - 1
    return value == mask

