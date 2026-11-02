"""Unknown-value runtime identities and their SMT symbol declarations."""

from __future__ import annotations

import hashlib
import re
from typing import Any, List, Optional, Tuple
from scripts.function_tracer_pcode.core.render_smt.attributes import iter_expression_nodes
from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection


GLOBAL_ADDRESS_BITS = 64


def global_address_symbol_name(identity: Tuple[str, int, int]) -> str:
    """SMT symbol for the base address of a named writable global object.

    The symbol is keyed by the object's symbol name and size only (Issue #104):
    two binaries built from the same source place the object at different
    absolute addresses, so the address is a *shared* unconstrained constant
    and every side's reads / writes of that object select the same cells of
    the shared memory arrays.  Names are sanitised and disambiguated by a
    digest so distinct C identifiers never collide.
    """

    name, size, _offset = identity
    safe = re.sub(r"[^0-9A-Za-z_]", "_", str(name))
    digest = hashlib.sha1(f"{name}\x00{int(size)}".encode("utf-8")).hexdigest()[:8]
    return f"gaddr_{safe}_{int(size)}_{digest}"


def global_address_identity(expr) -> Optional[Tuple[str, int, int]]:
    """``(symbol, size, offset)`` when ``expr`` is a constant address inside a
    named writable global object, else ``None``.

    凍結時に確定した投影から読む。生の ``AddressValueRef`` を読み直すと、同じ
    式に対する global object の共有 symbol が後から動き得る。
    """

    return semantic_projection(expr).address_object_identity


def global_address_smt(expr, bits: int) -> Optional[str]:
    """Render a global-object address constant as ``base (+ offset)`` at ``bits``."""
    identity = global_address_identity(expr)
    if identity is None:
        return None
    _name, _size, offset = identity
    base = global_address_symbol_name(identity)
    rendered = base if int(offset) == 0 else f"(bvadd {base} (_ bv{int(offset)} {GLOBAL_ADDRESS_BITS}))"
    bits = max(1, int(bits or GLOBAL_ADDRESS_BITS))
    if bits == GLOBAL_ADDRESS_BITS:
        return rendered
    if bits < GLOBAL_ADDRESS_BITS:
        return f"((_ extract {bits - 1} 0) {rendered})"
    return f"((_ zero_extend {bits - GLOBAL_ADDRESS_BITS}) {rendered})"


def side_address_smt(expr, bits: int, tag: Optional[str]) -> Optional[str]:
    """image の object を指す番地（global の identity または image の block）を、側 `tag` の記号で描く
    （Issue #282, I1）。それ以外の定数・変数は None（数値として描く）。

    * named global: その側の `gaddr_*_{tag}`（+ object の中の offset）
    * それ以外の image の番地 `C`: `(bvadd imgbase_{tag} C)`（同じ側の中の番地の差は保ち、左右では別の値）
    """

    from scripts.function_tracer_pcode.core.render_smt.sides import (
        image_base_symbol_name,
        side_qualified_name,
    )

    projection = semantic_projection(expr)
    identity = projection.address_object_identity
    if identity is not None:
        _name, _size, offset = identity
        base = side_qualified_name(global_address_symbol_name(identity), tag)
    elif projection.address_in_image and projection.address_offset is not None:
        offset = int(projection.address_offset)
        base = image_base_symbol_name(tag)
    else:
        return None
    rendered = base if int(offset) == 0 else f"(bvadd {base} (_ bv{int(offset)} {GLOBAL_ADDRESS_BITS}))"
    bits = max(1, int(bits or GLOBAL_ADDRESS_BITS))
    if bits == GLOBAL_ADDRESS_BITS:
        return rendered
    if bits < GLOBAL_ADDRESS_BITS:
        return f"((_ extract {bits - 1} 0) {rendered})"
    return f"((_ zero_extend {bits - GLOBAL_ADDRESS_BITS}) {rendered})"


def expression_addresses_image(expr) -> bool:
    """node が image の object の番地（側ごとの記号で描く値）か。"""

    projection = semantic_projection(expr)
    return projection.address_object_identity is not None or bool(projection.address_in_image)


def collect_global_address_identities(expr) -> List[Tuple[str, int]]:
    """Distinct ``(symbol, size)`` global objects addressed anywhere in ``expr``."""
    seen: List[Tuple[str, int]] = []
    for node in _iter_expression_nodes(expr):
        identity = global_address_identity(node)
        if identity is None:
            continue
        key = (str(identity[0]), int(identity[1]))
        if key not in seen:
            seen.append(key)
    return seen


def collect_unknown_smt_declarations(expr, side_tag: Optional[str] = None) -> List[Tuple[str, int]]:
    """Collect deterministic SMT declarations needed for UNKNOWN runtime objects
    and for the base addresses of image objects.

    `side_tag`（`core.render_smt.sides`）を渡すと、その側の記号（global の番地・image の基準・出口の状態の
    値）の名前で宣言する（Issue #282）。renderer が側の写像で描く名前と同じ規則。"""
    from scripts.function_tracer_pcode.core.observation_index import (
        OBSERVATION_INDEX_BYTES,
        OBSERVATION_INDEX_SMT_NAME,
        is_observation_index,
    )
    from scripts.function_tracer_pcode.core.render_smt.sides import (
        image_base_symbol_name,
        side_qualified_name,
    )

    declarations: List[Tuple[str, int]] = []
    seen = set()
    for node in _iter_expression_nodes(expr):
        if node is None or getattr(node, "expr_type", None) is None:
            continue
        expr_kind = node.expr_type.__class__
        projection = semantic_projection(node)
        decl = None
        identity = global_address_identity(node)
        if identity is not None:
            decl = (side_qualified_name(global_address_symbol_name(identity), side_tag), GLOBAL_ADDRESS_BITS)
        elif (
            side_tag is not None
            and projection.address_in_image
            and node.expr_type in (expr_kind.CONSTANT, expr_kind.VARIABLE)
        ):
            decl = (image_base_symbol_name(side_tag), GLOBAL_ADDRESS_BITS)
        elif node.expr_type == expr_kind.UNKNOWN:
            decl = _unknown_smt_declaration(node)
        elif is_observation_index(node):
            # 左右で同じ記号（store の観測の番地の量化変数）。replay の対象にする
            decl = (OBSERVATION_INDEX_SMT_NAME, OBSERVATION_INDEX_BYTES * 8)
        elif node.expr_type == expr_kind.VARIABLE and projection.declares_variable_symbol:
            # 宣言名を作るための内部描画。公開入口（`expression_to_smt`）へ
            # 戻らない — 外から来た式の検査は入口が 1 回だけ行う。
            decl = (
                side_qualified_name(_to_smt_internal(node), side_tag),
                max(1, int(expression_smt_bit_width(node) or 1)),
            )
        if decl is None:
            continue
        if decl in seen:
            continue
        seen.add(decl)
        declarations.append(decl)
    return declarations


#: 走査は `attributes` が唯一の実装。宣言収集（unknown / CALL / float 述語 /
#: global address）が同じ順序・同じ共有の扱いで回るように、ここでは名前だけ
#: 引き継ぐ（旧実装は `seen` を持たず、共有部分式を親ごとに数え直していた）。
_iter_expression_nodes = iter_expression_nodes


def _unknown_runtime_identity_key(expr) -> Tuple[Any, ...]:
    """unknown symbol の宣言 identity。

    凍結済みの式では runtime_ref の意味 key は凍結時に確定した投影から読む。
    宣言 identity が生 object の後からの変化で動くと、同じ式に対して別の
    unknown symbol が宣言されてしまう。
    """

    projection = semantic_projection(expr)
    # projection の identity の field は値として固定できる key だけ（Issue #215: 固定できない ref は
    # None になり、その式は自分だけの記号になる）
    semantic_key = projection.runtime_semantic_key
    stable_key = projection.runtime_stable_key
    if semantic_key is not None:
        return ("runtime_ref_semantic", semantic_key)
    if stable_key is not None:
        if projection.runtime_stable_origin is not None:
            return (
                "runtime_ref_with_origin",
                stable_key,
                projection.runtime_stable_origin,
            )
        return ("runtime_ref", stable_key)
    return (
        "expression_unknown_instance",
        id(expr),
        int(expression_smt_bit_width(expr) or 1),
    )


def side_state_symbol_name(expr) -> str:
    """自前で宣言する状態の記号（出口の状態の読み出し・location の値）の名前。ref の identity から作る（Issue #282）。

    identity は unknown の記号と同じ規則（`_unknown_runtime_identity_key`: 凍結した projection の key、固定できなければ
    その node だけの記号）。ref の種類（`PostStateReadRef` / `PostStateValueRef` / `CanonicalLocation`）と場所・時点を
    含むので、別の場所・別の時点の値が同じ記号にならない。
    """

    identity = _unknown_runtime_identity_key(expr)
    bits = max(1, int(expression_smt_bit_width(expr) or 1))
    digest = hashlib.sha1(repr(("side_state", identity)).encode("utf-8")).hexdigest()[:16]
    return f"state_{digest}_{bits}"


def _unknown_smt_symbol_name(expr) -> str:
    identity = _unknown_runtime_identity_key(expr)
    bits = max(1, int(expression_smt_bit_width(expr) or 1))
    digest = hashlib.sha1(repr(identity).encode("utf-8")).hexdigest()[:16]
    return f"rtunk_{digest}_{bits}"


def _unknown_smt_declaration(expr) -> Tuple[str, int]:
    bits = max(1, int(expression_smt_bit_width(expr) or 1))
    return (_unknown_smt_symbol_name(expr), bits)


# Sibling modules reference each other at call time; import them last to avoid cycles.
from scripts.function_tracer_pcode.core.render_smt.render import _to_smt_internal
from scripts.function_tracer_pcode.core.render_smt.widths import (
    expression_smt_bit_width,
)
