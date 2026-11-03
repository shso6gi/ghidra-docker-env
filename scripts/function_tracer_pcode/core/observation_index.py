# -*- coding: utf-8 -*-
"""store の観測の番地の変数（Issue #282, I9）。

関数が書いた memory を左右で比べるとき、比べる面は「番地 `a` の 1 byte に、関数が書いたか・書いた値」で、
`a` は query の中で量化する（UNSAT なら、すべての番地で書き込みの有無と値が一致する。
`analysis.effects.observation_surface`）。`a` は入力ではなく、左右の面を **同じ番地で** 比べるための記号なので、
左右で同じ SMT の名前に描く唯一の値（`core.render_smt.sides.with_side` が側の写像に入れる）。

* 解析の側の値: 名前 `OBSERVATION_INDEX_NAME` の `VARIABLE`（幅 8 byte、ref なし）。
* SMT の名前: `OBSERVATION_INDEX_SMT_NAME`（query の header が 1 回宣言する）。
"""

from __future__ import annotations

OBSERVATION_INDEX_NAME = "__observed_store_address__"
OBSERVATION_INDEX_SMT_NAME = "obs_store_addr"
OBSERVATION_INDEX_BYTES = 8


def is_observation_index(node) -> bool:
    expr_type = getattr(node, "expr_type", None)
    return (
        getattr(expr_type, "name", None) == "VARIABLE"
        and getattr(node, "name", None) == OBSERVATION_INDEX_NAME
        and not getattr(node, "operands", None)
    )


def observation_index_expression():
    from scripts.function_tracer_pcode.core import Expression

    return Expression.variable(OBSERVATION_INDEX_NAME, size=OBSERVATION_INDEX_BYTES)
