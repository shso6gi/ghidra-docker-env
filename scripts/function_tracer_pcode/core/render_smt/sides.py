# -*- coding: utf-8 -*-
"""左右の側ごとの SMT の記号（Issue #282, I1 / I2）。

左右の関数を 1 つの query で比べるとき、次の値は **その側の program の状態** を表すので、側ごとの記号で描く。
左右で同じ記号にしてよいのは、入力対応の owner（`proof.formula.input_correspondence`）が根拠を記録した
組だけで、今回その種類の根拠は無い（共有の領域は PR-282-P）。

* pre-state の memory の配列（幅ごとの配列 `mem{bits}`。側ごとに独立なので、対応を証明できない部分の上近似）
* image の object の番地（named global の `gaddr_*`、image の block を指す定数の基準 `imgbase`）
* 関数の出口の状態の値（`PostStateReadRef` / `PostStateValueRef` / `CanonicalLocation` を持つ自前宣言の
  VARIABLE）。以前は場所の名前（`poststate_{offset}_{size}`）だけで決まり、左右で同じ記号になり得た

側の指定は、描画の記号の写像（parameter の名前 → SMT の名前）に予約 key で入れる。写像は側ごとに作られて
（`build_symbol_replacer` / `build_symbol_name_mapping`）renderer の全経路を通るので、側の指定もそれに乗せる。

* 写像が無い描画（`None`）: 1 つの側だけの query（片側の oracle・recurrence の内部）と、比較の key の描画。
  記号は側の無い名前（従来どおり）。
* 写像があり側が無い描画: 左右の query の材料かもしれないので、上の値を描けない（`UndeclaredSmtSymbolError`）。
"""

from __future__ import annotations

from typing import Mapping, Optional

#: 写像の予約 key（parameter の名前・SMT の名前には現れない文字列）
SIDE_MAPPING_KEY = "\x00smt_side"

SIDE_TAGS = {1: "s1", 2: "s2"}


def with_side(mapping: Optional[Mapping[str, str]], side: Optional[int]) -> dict:
    """`mapping` に側の指定を足した写像（`side` が None なら側を足さない）。"""

    from scripts.function_tracer_pcode.core.observation_index import (
        OBSERVATION_INDEX_NAME,
        OBSERVATION_INDEX_SMT_NAME,
    )

    result = dict(mapping or {})
    if side is not None:
        if side not in SIDE_TAGS:
            raise ValueError(f"unknown comparison side: {side!r}")
        result[SIDE_MAPPING_KEY] = SIDE_TAGS[side]
        # store の観測の番地は左右で同じ記号（入力ではなく、比べる番地の量化変数。`core.observation_index`）
        result[OBSERVATION_INDEX_NAME] = OBSERVATION_INDEX_SMT_NAME
    return result


def mapping_side_tag(mapping: Optional[Mapping[str, str]]) -> Optional[str]:
    if mapping is None:
        return None
    tag = mapping.get(SIDE_MAPPING_KEY)
    return tag if tag in SIDE_TAGS.values() else None


def side_qualified_name(name: str, tag: Optional[str]) -> str:
    """側の記号の名前（側が無ければそのまま）。"""

    return f"{name}_{tag}" if tag else str(name)


def memory_array_name(bits: int, tag: Optional[str]) -> str:
    return side_qualified_name(f"mem{int(bits)}", tag)


def image_base_symbol_name(tag: Optional[str]) -> str:
    """image の block を指す（global の identity の無い）定数の基準。側ごとに独立な記号。"""

    return side_qualified_name("imgbase", tag)


def memory_array_declaration(bits: int, tag: Optional[str]) -> str:
    return f"(declare-const {memory_array_name(bits, tag)} (Array (_ BitVec 64) (_ BitVec {int(bits)})))"
