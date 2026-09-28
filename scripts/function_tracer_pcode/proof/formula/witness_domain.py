# -*- coding: utf-8 -*-
"""反例として受け入れる witness の定義域（Issue #161）。

replay の規則「浮動小数点の引数が NaN の bit 列である反例は、非等価の証拠にしない」
（NaN の伝播・符号 bit は benchmark が固定しない実装の詳細。Issue #28）の **唯一の
定義** をここに置く。2 つの面が同じ定義を読む:

* replay（`pairwise_query_executor.counterexample_fp_nan_parameters`）が model を拒否
  するときの判定（Python の値）
* 論理式の header に置く witness の preference（SMT の項）。solver 側の witness 生成
  （`smt.witness`）は preference を満たせる witness があればそれを返すので、NaN で
  ない反例が存在するのに NaN の反例を受け取って UNKNOWN になる、という「solver が
  どの解を選んだか」への依存が残らない

preference は assert しない（論理式の意味は変わらない。等価の証明＝UNSAT は NaN を
含む全入力について成り立つまま）。
"""

from __future__ import annotations

from typing import Iterable, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.smt.witness import witness_preference_name


#: IEEE 754 binary の幅 → (exponent bits, mantissa bits)
FP_BIT_LAYOUTS = {64: (11, 52), 32: (8, 23)}

#: 優先順 0: 浮動小数点の引数がどれも NaN の bit 列でない
NON_NAN_FP_PREFERENCE = witness_preference_name(0)


def is_nan_bit_pattern(value: int, bit_width: int) -> bool:
    """`value` を `bit_width` 幅の IEEE 754 の bit 列として見たとき NaN か。"""

    layout = FP_BIT_LAYOUTS.get(int(bit_width))
    if layout is None:
        return False
    exponent_bits, mantissa_bits = layout
    value %= 1 << bit_width
    exponent = (value >> mantissa_bits) & ((1 << exponent_bits) - 1)
    mantissa = value & ((1 << mantissa_bits) - 1)
    return exponent == (1 << exponent_bits) - 1 and mantissa != 0


def fp_parameters(params: Iterable) -> Tuple:
    """NaN の規則が対象にする引数（浮動小数点で、幅が IEEE 754 binary32 / 64）。"""

    return tuple(
        param
        for param in params or ()
        if getattr(param, "type_class", None) == "fp"
        and int(getattr(param, "bit_width", 0) or 0) in FP_BIT_LAYOUTS
    )


def _nan_bit_pattern_smt(symbol: str, bit_width: int) -> str:
    exponent_bits, mantissa_bits = FP_BIT_LAYOUTS[int(bit_width)]
    top = int(bit_width) - 2
    all_ones = "#b" + "1" * exponent_bits
    return (
        f"(and (= ((_ extract {top} {mantissa_bits}) {symbol}) {all_ones}) "
        f"(not (= ((_ extract {mantissa_bits - 1} 0) {symbol}) (_ bv0 {mantissa_bits}))))"
    )


def witness_preference_lines(params1: Sequence, params2: Sequence) -> List[str]:
    """header に置く witness の preference（浮動小数点の引数が無ければ空）。

    bit-vector の式だけで書く（浮動小数点の theory を使わないので論理 名は変わらない）。
    """

    seen: set = set()
    clauses: List[str] = []
    for param in fp_parameters(list(params1 or ()) + list(params2 or ())):
        if param.smt_name in seen:
            continue
        seen.add(param.smt_name)
        clauses.append(f"(not {_nan_bit_pattern_smt(param.smt_name, param.bit_width)})")
    if not clauses:
        return []
    return [
        "; Issue #161: witness preference (not asserted): a counterexample with no NaN FP input",
        f"(define-fun {NON_NAN_FP_PREFERENCE} () Bool (and true {' '.join(clauses)}))",
    ]


__all__ = [
    "FP_BIT_LAYOUTS",
    "NON_NAN_FP_PREFERENCE",
    "fp_parameters",
    "is_nan_bit_pattern",
    "witness_preference_lines",
]
