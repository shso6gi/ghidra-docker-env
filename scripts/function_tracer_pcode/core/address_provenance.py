# -*- coding: utf-8 -*-
"""定数の番地の出自（Issue #282, 不変条件 3）。

image の object を指す定数（Ghidra の block の中の番地・named global の番地）は、その側の program の配置の値
なので、左右の query では側ごとの記号で描く（`core.render_smt.unknowns.side_address_smt`）。その判断は定数の
node が持つ出自（`AddressValueRef` の projection: `address_object_identity` / `address_in_image`）で決める。

畳み込み（定数どうしの演算・拡張・切り詰めを 1 つの定数にする）は、新しい定数に出自を移せないと、image の
番地を素の数値にしてしまう（左右で同じ数値なら同じ値と描かれ、別の object の番地が等しくなる）。畳み込む
側（`semantics.normalize`・`analysis.condition`・`analysis.returns` の各 site）は、入力がこの判定に当たるなら
畳み込まず元の式を残す（意味は同じで、renderer が側ごとの記号で描く）。
"""

from __future__ import annotations


def carries_image_address(expr) -> bool:
    """式（の部分木）に、image の object の番地の出自を持つ定数・変数があるか。"""

    if expr is None:
        return False
    from scripts.function_tracer_pcode.core.render_smt.attributes import iter_expression_nodes
    from scripts.function_tracer_pcode.core.render_smt.unknowns import expression_addresses_image

    for node in iter_expression_nodes(expr):
        expr_type = getattr(getattr(node, "expr_type", None), "name", None)
        if expr_type in ("CONSTANT", "VARIABLE") and expression_addresses_image(node):
            return True
    return False
