"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.base``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    expression_smt_bit_width,
    re,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__return_width_bridge_extension_op_profile_matches(
    cls,
    profile: Any,
    *,
    mnemonic: str,
    producer_bits: Any,
    return_bits: Any,
) -> bool:
    normalized = cls._normalize_nested_tuple(profile)
    if not isinstance(normalized, tuple) or len(normalized) < 6:
        return False
    if normalized[0] != "extension_op" or normalized[1] != mnemonic:
        return False
    op_ref = cls._return_width_bridge_find_tagged_entry(normalized, "op_ref")
    input_bits = cls._return_width_bridge_find_tagged_entry(normalized, "input_bits")
    output_bits = cls._return_width_bridge_find_tagged_entry(normalized, "output_bits")
    policy = cls._return_width_bridge_find_tagged_entry(normalized, "policy")
    expected_policy = "sign_extend" if mnemonic == "INT_SEXT" else "zero_extend"
    try:
        input_bits_int = int(input_bits[1] if isinstance(input_bits, tuple) and len(input_bits) == 2 else input_bits)
        output_bits_int = int(output_bits[1] if isinstance(output_bits, tuple) and len(output_bits) == 2 else output_bits)
        producer_bits_int = int(producer_bits)
        return_bits_int = int(return_bits)
    except (TypeError, ValueError):
        return False
    return (
        isinstance(op_ref, tuple)
        and len(op_ref) == 2
        and op_ref[1] is not None
        and input_bits_int == producer_bits_int
        and output_bits_int >= return_bits_int
        and isinstance(policy, tuple)
        and len(policy) == 2
        and policy[1] == expected_policy
    )

def _impl__return_width_bridge_target_widths(cls, object_target_key: Any) -> Optional[Tuple[int, int]]:
    target = cls._normalize_nested_tuple(object_target_key)
    widths = cls._return_width_bridge_find_tagged_entry(target, "return_widths")
    if not isinstance(widths, tuple) or len(widths) != 3:
        return None
    try:
        left_width = int(widths[1])
        right_width = int(widths[2])
    except (TypeError, ValueError):
        return None
    if left_width <= 0 or right_width <= 0:
        return None
    return left_width, right_width

def _impl__return_width_bridge_target_narrow_width(cls, object_target_key: Any) -> Optional[int]:
    widths = cls._return_width_bridge_target_widths(object_target_key)
    if widths is None:
        return None
    return min(widths)

def _impl__return_width_bridge_find_side(
    cls,
    object_target_key: Any,
    side_label: str,
) -> Optional[Tuple[Any, ...]]:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple):
        return None
    for item in target:
        if (
            isinstance(item, tuple)
            and len(item) >= 2
            and item[0] == "return_width_side"
            and item[1] == side_label
        ):
            return item
    return None

def _impl__return_width_bridge_find_tagged_entry(cls, value: Any, tag: str) -> Any:
    normalized = cls._normalize_nested_tuple(value)
    if not isinstance(normalized, tuple):
        return None
    for item in normalized:
        if isinstance(item, tuple) and item and item[0] == tag:
            return item
    return None

def _impl__return_width_bridge_object_target_key(
    self,
    *,
    analysis1: Optional[FunctionReturnAnalysis] = None,
    analysis2: Optional[FunctionReturnAnalysis] = None,
    base_ctx: Optional[Dict[str, Any]] = None,
    case1: Any = None,
    case2: Any = None,
    pair_id: Optional[str] = None,
    mismatch: Any = None,
) -> Tuple[Any, ...]:
    """Object-derived target key for return-width bridge proof backlog."""

    if base_ctx is not None:
        analysis1 = analysis1 or base_ctx.get("analysis1")
        analysis2 = analysis2 or base_ctx.get("analysis2")
    return_size1 = self._coerce_return_width(
        getattr(mismatch, "return_size1", None)
        if mismatch is not None
        else None,
        (base_ctx or {}).get("return_size1") if base_ctx is not None else None,
    )
    return_size2 = self._coerce_return_width(
        getattr(mismatch, "return_size2", None)
        if mismatch is not None
        else None,
        (base_ctx or {}).get("return_size2") if base_ctx is not None else None,
    )
    return (
        "return_width_bridge",
        ("pair", pair_id),
        ("return_widths", return_size1, return_size2),
        self._return_width_bridge_side_object_key(
            "left",
            analysis1,
            case1,
            return_size1,
        ),
        self._return_width_bridge_side_object_key(
            "right",
            analysis2,
            case2,
            return_size2,
        ),
    )

def _impl__coerce_return_width(*values: Any) -> Optional[int]:
    for value in values:
        if value is None:
            continue
        try:
            bits = int(value)
        except (TypeError, ValueError):
            continue
        if bits > 0:
            return bits
    return None

def _impl__return_width_bridge_side_object_key(
    self,
    side_label: str,
    analysis: Optional[FunctionReturnAnalysis],
    case: Any,
    return_size: Optional[int],
) -> Tuple[Any, ...]:
    return_info = getattr(case, "return_info", None)
    return (
        "return_width_side",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        ("return_size", return_size),
        self._return_storage_object_key(analysis) if analysis is not None else None,
        self._return_case_partition_member_object_key(case, return_info),
        self._return_width_bridge_return_value_width_object_key(
            case,
            return_info,
            return_size,
        ),
    )

def _impl__return_width_bridge_return_value_width_object_key(
    self,
    case: Any,
    return_info: Any,
    return_size: Optional[int],
) -> Tuple[Any, ...]:
    value_expr = getattr(case, "value_expr", None)
    expression_bits = self._expression_smt_bit_width_for_object_key(value_expr)
    pcode_op_ref = getattr(return_info, "pcode_op_ref", None)
    pcode_input_bits = self._return_pcode_value_input_width_bits(pcode_op_ref)
    producer_bits = self._coerce_return_width(expression_bits, pcode_input_bits)
    return_bits = self._coerce_return_width(return_size)
    use_sign_extension = bool(
        getattr(case, "should_sign_extend_value", lambda: False)()
    )
    relation = "producer_matches_return_width"
    policy = "none"
    if producer_bits is not None and return_bits is not None:
        if producer_bits < return_bits:
            relation = "producer_narrower_than_return_width"
            policy = "sign_extend" if use_sign_extension else "zero_extend"
        elif producer_bits > return_bits:
            relation = "producer_wider_than_return_width"
            policy = "truncate"
    return (
        "return_value_width",
        producer_bits,
        return_bits,
        use_sign_extension,
        ("value", self._expression_runtime_object_key(value_expr)),
        relation,
        policy,
        ("expression_bits", expression_bits),
        ("return_pcode_value_input_bits", pcode_input_bits),
        self._return_value_extension_ops_object_key(return_info),
    )

def _impl__expression_smt_bit_width_for_object_key(expr: Any) -> Optional[int]:
    if expr is None:
        return None
    try:
        bits = int(expression_smt_bit_width(expr) or 0)
    except (AttributeError, TypeError, ValueError, RecursionError):
        bits = 0
    if bits <= 0:
        try:
            bits = int(getattr(expr, "get_bit_width", lambda: 0)() or 0)
        except (AttributeError, TypeError, ValueError, RecursionError):
            bits = 0
    return bits if bits > 0 else None

def _impl__return_pcode_value_input_width_bits(pcode_op_ref: Any) -> Optional[int]:
    input_sizes = getattr(pcode_op_ref, "input_sizes", None) or ()
    if not input_sizes:
        return None
    candidates = []
    for size in input_sizes:
        try:
            int_size = int(size)
        except (TypeError, ValueError):
            continue
        if int_size > 0:
            candidates.append(int_size)
    if not candidates:
        return None
    return max(1, candidates[-1]) * 8

def _impl__normalize_zero_constant_widths_for_declared_symbols(
    cls,
    assertions: Sequence[str],
    header_lines: Sequence[str],
) -> List[str]:
    widths: Dict[str, int] = {}
    for line in header_lines or ():
        match = re.search(
            r"\(declare-(?:fun|const)\s+([^\s()]+)\s+(?:\(\)\s+)?\(_\s+BitVec\s+(\d+)\)\)",
            str(line),
        )
        if match is None:
            continue
        try:
            widths[match.group(1)] = int(match.group(2))
        except ValueError:
            continue
    if not widths:
        return list(assertions or ())

    normalized = []
    for assertion in assertions or ():
        text = str(assertion)
        for symbol, width in widths.items():
            escaped = re.escape(symbol)
            text = re.sub(
                rf"(\((?:bvslt|bvult|bvsle|bvule|=|distinct)\s+)\(_ bv0 \d+\)(\s+{escaped}(?=[\s)]))",
                rf"\1(_ bv0 {width})\2",
                text,
            )
            text = re.sub(
                rf"(\((?:bvslt|bvult|bvsle|bvule|=|distinct)\s+{escaped}\s+)\(_ bv0 \d+\)(?=\))",
                rf"\1(_ bv0 {width})",
                text,
            )
        normalized.append(text)
    return normalized
