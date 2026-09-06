"""MIPS unaligned store idiom (``sdl``/``sdr``, ``swl``/``swr``) as one store.

MIPS has no unaligned ``sd``/``sw``; the compiler emits a *left* / *right*
pair that together write the whole value ``v`` to ``[X, X + width)``.  The
decompiler renders each half as a full-width STORE to the aligned-down
address with a partially masked value (Issue #104, PR 1 follow-up):

    left  (address ``Y = X``):
        STORE (Y - (Y & m)) <- (MEM[Y - (Y & m)] & (-1 << (w - (Y & m)) * 8))
                               | (v >> ((Y & m) * 8))
    right (address ``Y = X + w - 1``):
        STORE (Y - (Y & m)) <- (v << ((w - 1 - (Y & m)) * 8))
                               | (MEM[Y - (Y & m)] & (-1 >> (((Y & m) + 1) * 8)))

with ``w`` the width in bytes and ``m = w - 1`` (big-endian encoding; this is
what Ghidra's MIPS64 sleigh produces).  The composition of the two halves is
exactly ``STORE_w(X, v)`` for **every** alignment of ``X``: the left half
writes the high bytes of ``v`` from ``X`` to the end of its aligned word and
the right half writes the low bytes from the start of its aligned word to
``X + w - 1``.  So a matched pair is modelled as a single ordinary store and
no alignment assumption is needed.  An unmatched half is *not* modelled (the
caller fails closed), because half of an unaligned store on its own has no
alignment-independent meaning.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core import (
    Expression,
    ExpressionType,
    StructuralKey,
    expression_key,
)


_SUPPORTED_WIDTHS = (8, 4)


@dataclass(frozen=True)
class UnalignedStoreHalf:
    """One ``sdl``/``sdr`` (or ``swl``/``swr``) half of an unaligned store."""

    side: str  # "left" | "right"
    width: int
    base_expr: Expression  # X: the unaligned start address of the whole store
    value_expr: Expression  # v: the full value being stored
    base_key: StructuralKey
    value_key: StructuralKey

    @property
    def pair_key(self) -> Tuple[int, StructuralKey, StructuralKey]:
        return (int(self.width), self.base_key, self.value_key)


def _key(expr: Expression) -> StructuralKey:
    return expression_key(
        expr,
        normalize_commutative=True,
        strip_width_adapters=True,
        collapse_full_masks=True,
        include_memory_read_order=False,
    )


def _is_const(expr: Optional[Expression], value: Optional[int] = None) -> bool:
    if expr is None or expr.expr_type != ExpressionType.CONSTANT:
        return False
    if value is None:
        return True
    try:
        raw = int(expr.value)
    except Exception:
        return False
    size_bits = 8 * max(1, int(expr.size or 0))
    mask = (1 << size_bits) - 1
    return (raw & mask) == (value & mask)


def _is_all_ones(expr: Optional[Expression]) -> bool:
    return _is_const(expr, -1)


def _binop(expr: Optional[Expression], operator: str) -> Optional[Tuple[Expression, Expression]]:
    if (
        expr is None
        or expr.expr_type != ExpressionType.BINARY_OP
        or expr.operator != operator
        or len(expr.operands) != 2
    ):
        return None
    return expr.operands[0], expr.operands[1]


def _split_commutative(expr: Optional[Expression], operator: str) -> List[Tuple[Expression, Expression]]:
    parts = _binop(expr, operator)
    if parts is None:
        return []
    left, right = parts
    return [(left, right), (right, left)]


def _match_align_down(addr_expr: Optional[Expression]) -> Optional[Tuple[Expression, int]]:
    """``Y - (Y & m)`` with ``m in {7, 3}``: returns ``(Y, width)``."""

    parts = _binop(addr_expr, "INT_SUB")
    if parts is None:
        return None
    y_expr, masked = parts
    for a, b in _split_commutative(masked, "INT_AND"):
        for width in _SUPPORTED_WIDTHS:
            if _is_const(b, width - 1) and _key(a) == _key(y_expr):
                return y_expr, width
    return None


def _match_low_bits(expr: Optional[Expression], y_key: StructuralKey, width: int) -> bool:
    """``Y & (width - 1)``"""
    for a, b in _split_commutative(expr, "INT_AND"):
        if _is_const(b, width - 1) and _key(a) == y_key:
            return True
    return False


def _match_times_eight(expr: Optional[Expression]) -> Optional[Expression]:
    """``e * 8`` -> ``e``"""
    for a, b in _split_commutative(expr, "INT_MULT"):
        if _is_const(b, 8):
            return a
    return None


def _match_memory_at(expr: Optional[Expression], addr_key: StructuralKey, width: int) -> bool:
    return (
        expr is not None
        and expr.expr_type == ExpressionType.MEMORY
        and bool(expr.operands)
        and int(expr.size or 0) == width
        and _key(expr.operands[0]) == addr_key
    )


def _match_left_value(
    value_expr: Optional[Expression], addr_key: StructuralKey, y_key: StructuralKey, width: int
) -> Optional[Expression]:
    """``(MEM[A] & (-1 << ((w - low) * 8))) | (v >> (low * 8))`` -> ``v``"""

    for masked_mem, shifted_value in _split_commutative(value_expr, "INT_OR"):
        mem_parts = _binop(masked_mem, "INT_AND")
        shift_parts = _binop(shifted_value, "INT_RIGHT")
        if mem_parts is None or shift_parts is None:
            continue
        mem_ok = False
        for mem_expr, mask_expr in (mem_parts, mem_parts[::-1]):
            if not _match_memory_at(mem_expr, addr_key, width):
                continue
            mask_parts = _binop(mask_expr, "INT_LEFT")
            if mask_parts is None or not _is_all_ones(mask_parts[0]):
                continue
            bytes_expr = _match_times_eight(mask_parts[1])
            sub = _binop(bytes_expr, "INT_SUB")
            if sub is None or not _is_const(sub[0], width) or not _match_low_bits(sub[1], y_key, width):
                continue
            mem_ok = True
            break
        if not mem_ok:
            continue
        value, amount = shift_parts
        low = _match_times_eight(amount)
        if low is None or not _match_low_bits(low, y_key, width):
            continue
        if int(value.size or 0) not in (0, width):
            continue
        return value
    return None


def _match_right_value(
    value_expr: Optional[Expression], addr_key: StructuralKey, y_key: StructuralKey, width: int
) -> Optional[Expression]:
    """``(v << ((w - 1 - low) * 8)) | (MEM[A] & (-1 >> ((low + 1) * 8)))`` -> ``v``"""

    for shifted_value, masked_mem in _split_commutative(value_expr, "INT_OR"):
        shift_parts = _binop(shifted_value, "INT_LEFT")
        mem_parts = _binop(masked_mem, "INT_AND")
        if shift_parts is None or mem_parts is None:
            continue
        mem_ok = False
        for mem_expr, mask_expr in (mem_parts, mem_parts[::-1]):
            if not _match_memory_at(mem_expr, addr_key, width):
                continue
            mask_parts = _binop(mask_expr, "INT_RIGHT")
            if mask_parts is None or not _is_all_ones(mask_parts[0]):
                continue
            bytes_expr = _match_times_eight(mask_parts[1])
            plus = None
            for a, b in _split_commutative(bytes_expr, "INT_ADD"):
                if _is_const(b, 1) and _match_low_bits(a, y_key, width):
                    plus = a
                    break
            if plus is None:
                continue
            mem_ok = True
            break
        if not mem_ok:
            continue
        value, amount = shift_parts
        bytes_expr = _match_times_eight(amount)
        sub = _binop(bytes_expr, "INT_SUB")
        if sub is None or not _is_const(sub[0], width - 1) or not _match_low_bits(sub[1], y_key, width):
            continue
        if int(value.size or 0) not in (0, width):
            continue
        return value
    return None


def _minus_const(expr: Expression, amount: int) -> Expression:
    """``expr - amount`` folded into an existing constant offset when possible."""

    for operator in ("INT_ADD",):
        parts = _binop(expr, operator)
        if parts is not None and _is_const(parts[1]):
            base, const = parts
            folded = Expression.constant(int(const.value) - amount, const.size or 8)
            if int(folded.value) == 0:
                return base
            result = Expression.binary_op("INT_ADD", base, folded)
            result.size = expr.size
            return result
    const = Expression.constant(amount, expr.size or 8)
    result = Expression.binary_op("INT_SUB", expr, const)
    result.size = expr.size
    return result


def _impl_match_unaligned_store_half(
    addr_expr: Optional[Expression],
    value_expr: Optional[Expression],
    store_size: int,
) -> Optional[UnalignedStoreHalf]:
    """Recognise one half of a MIPS unaligned store; ``None`` for anything else."""

    matched = _match_align_down(addr_expr)
    if matched is None:
        return None
    y_expr, width = matched
    if int(store_size or 0) != width:
        return None
    addr_key = _key(addr_expr)
    y_key = _key(y_expr)
    value = _match_left_value(value_expr, addr_key, y_key, width)
    if value is not None:
        return UnalignedStoreHalf(
            side="left",
            width=width,
            base_expr=y_expr,
            value_expr=value,
            base_key=y_key,
            value_key=_key(value),
        )
    value = _match_right_value(value_expr, addr_key, y_key, width)
    if value is not None:
        base_expr = _minus_const(y_expr, width - 1)
        return UnalignedStoreHalf(
            side="right",
            width=width,
            base_expr=base_expr,
            value_expr=value,
            base_key=_key(base_expr),
            value_key=_key(value),
        )
    return None


def _impl_pair_unaligned_store_halves(
    halves: Sequence[Tuple[Any, UnalignedStoreHalf]],
    base_key_fn: Optional[Any] = None,
) -> Tuple[List[Tuple[Any, Any, UnalignedStoreHalf]], List[Tuple[Any, UnalignedStoreHalf]]]:
    """Group halves into ``(left_tag, right_tag, half)`` pairs.

    ``halves`` are ``(tag, half)`` in program order; a left half pairs with the
    next right half that stores the same value to the same start address.
    ``base_key_fn(base_expr, width)`` may supply a canonical address key (the
    two halves are often spelled differently, ``PTRADD(p, 4, 8)`` vs
    ``p + 39 - 7``); it falls back to the structural key when it returns
    ``None``.  Returns ``(pairs, unmatched)``; every unmatched half must be
    treated as an unmodelled store by the caller.
    """

    def _pair_key(half: UnalignedStoreHalf):
        base_key = None
        if base_key_fn is not None:
            try:
                base_key = base_key_fn(half.base_expr, half.width)
            except Exception:
                base_key = None
        if base_key is None:
            base_key = ("structural", half.base_key)
        else:
            base_key = ("canonical", base_key)
        return (int(half.width), base_key, half.value_key)

    pending: Dict[Any, List[Tuple[Any, UnalignedStoreHalf]]] = {}
    pairs: List[Tuple[Any, Any, UnalignedStoreHalf]] = []
    unmatched: List[Tuple[Any, UnalignedStoreHalf]] = []
    for tag, half in halves:
        key = _pair_key(half)
        queue = pending.setdefault(key, [])
        if half.side == "left":
            queue.append((tag, half))
            continue
        if queue:
            left_tag, left_half = queue.pop(0)
            pairs.append((left_tag, tag, left_half))
        else:
            unmatched.append((tag, half))
    for queue in pending.values():
        unmatched.extend(queue)
    return pairs, unmatched
