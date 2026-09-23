# -*- coding: utf-8 -*-
"""v5 §4.5 の final relation 規則（R0〜R5）を、production と独立に書いた判定表（Issue #167）。

repo の module を import しない（``tests/unit/test_input_correspondence_decision_model.py``
が production の ``build_input_correspondence_set`` と突き合わせる）。v4 の scratch model
（``decision_model.py``、md5 先頭 ``2dfdcb1a26b2``）は取得できなかったので、v5 本文から
書き直した。単体でも実行できる:

    python3 -B scripts/function_tracer_pcode/tests/fixtures/issue167/decision_model.py

side の入力は ``Side(width, iee, demand)``:

* ``iee``: ``None`` か ``(logical_bits, "sign"|"zero")``（validator を通った IEE）。
* ``demand``: raw surface が parameter を読む最大上端 bit。``None`` は裸の occurrence
  （どの N < W でも閉じない）。closure at N は ``demand is not None and demand <= N``。

``permitted_rules`` は relation が片側に含意した extension から、その側で入力仮定を
使ってよい書き換え規則を決める（v5 §4.3 ``required(rule) ⊆ entailed(final)``）。
規則ごとに意味を保存する ext の種類をここに独立に書き、production の rule 表と突き合わせる。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

CANDIDATE_BITS = (64, 32, 16, 8)

#: 入力仮定（parameter の extension 像）を使う規則と、意味を保存する ext の種類。
#: 等値・不等は ext が単射なので両方、signed 順序は sext、unsigned 順序は zext だけ。
#: 除算・剰余は certificate が無いので規則に無い。
ASSUMPTION_CONSUMING_RULES = {
    "equality_on_extension_images": ("sign", "zero"),
    "signed_order_on_sign_extension_images": ("sign",),
    "unsigned_order_on_zero_extension_images": ("zero",),
}


@dataclass(frozen=True)
class Side:
    width: int
    iee: Optional[Tuple[int, str]] = None
    demand: Optional[int] = None

    def closed_at(self, bits: int) -> bool:
        return self.demand is not None and self.demand <= bits


@dataclass(frozen=True)
class Relation:
    kind: str
    rule: str
    tie: int
    entailed: Tuple[Tuple[str, int, str], ...]
    sufficient: bool


def decide(left: Optional[Side], right: Optional[Side]) -> Relation:
    if left is None or right is None:
        return Relation("MISSING_SIDE", "R0", 0, (), False)

    def usable(side: Side):
        if side.iee is None or not (0 < side.iee[0] < side.width):
            return None
        return side.iee

    li, ri = usable(left), usable(right)
    if li is not None and ri is not None and li[0] == ri[0]:
        return Relation(
            "EXTENSION_BOUND", "R1", li[0],
            (("left", li[0], li[1]), ("right", ri[0], ri[1])), True,
        )
    if (li is None) != (ri is None):
        iee_side, iee, other = ("left", li, right) if li is not None else ("right", ri, left)
        bits = iee[0]
        if other.width == bits:
            return Relation("EXTENSION_BOUND", "R2", bits, ((iee_side, bits, iee[1]),), True)
        if bits < other.width and other.closed_at(bits):
            return Relation("EXTENSION_BOUND", "R2'", bits, ((iee_side, bits, iee[1]),), True)

    narrow = min(left.width, right.width)
    for bits in CANDIDATE_BITS:
        if 0 < bits < narrow and left.closed_at(bits) and right.closed_at(bits):
            return Relation("SEMANTIC_PROJECTION", "R3", bits, (), True)
    if left.width == right.width:
        return Relation("FULL_REGISTER_EQUALITY", "R4", left.width, (), True)
    wide = left if left.width > right.width else right
    return Relation("WIDTH_OVERLAP", "R5", narrow, (), wide.closed_at(narrow))


def permitted_rules(relation: Relation, side: str) -> Tuple[str, ...]:
    """``side`` で入力仮定を使ってよい規則（含意が無ければ空）。"""

    kinds = {kind for entailed_side, _bits, kind in relation.entailed if entailed_side == side}
    return tuple(sorted(
        rule for rule, rule_kinds in ASSUMPTION_CONSUMING_RULES.items() if kinds & set(rule_kinds)
    ))


# v4 の 16 case（v5 §4.10 の説明から再構成）。期待値は v5 §4.5 / §4.11 の記述。
V4_CASES = (
    ("ext32_vs_identity_64", Side(64, (32, "sign"), None), Side(64), "FULL_REGISTER_EQUALITY", ()),
    ("ext32_vs_ext16", Side(64, (32, "sign"), None), Side(64, (16, "sign"), None), "FULL_REGISTER_EQUALITY", ()),
    ("ext32_vs_closed32", Side(64, (32, "sign"), None), Side(64, None, 32), "EXTENSION_BOUND", ("left",)),
    ("closed32_vs_closed16", Side(64, None, 32), Side(64, None, 16), "SEMANTIC_PROJECTION", ()),
    ("sign_vs_zero", Side(64, (32, "sign"), None), Side(64, (32, "zero"), None), "EXTENSION_BOUND", ("left", "right")),
    ("fallback_full", Side(64), Side(64), "FULL_REGISTER_EQUALITY", ()),
    ("fallback_overlap_unclosed", Side(32), Side(64), "WIDTH_OVERLAP", ()),
    ("fallback_overlap_closed", Side(32), Side(64, None, 32), "WIDTH_OVERLAP", ()),
    ("loop2_with_iee", Side(32), Side(64, (32, "sign"), None), "EXTENSION_BOUND", ("right",)),
    ("loop2_without_iee", Side(32), Side(64), "WIDTH_OVERLAP", ()),
    ("w6_bare_use", Side(64), Side(64, None, 32), "FULL_REGISTER_EQUALITY", ()),
    ("store_full_width", Side(64, None, None), Side(64, None, 32), "FULL_REGISTER_EQUALITY", ()),
    ("other_n_16", Side(64, None, 16), Side(64, None, 16), "SEMANTIC_PROJECTION", ()),
    ("missing_side", Side(64), None, "MISSING_SIDE", ()),
    ("arith_both_iee", Side(64, (32, "sign"), None), Side(64, (32, "sign"), None), "EXTENSION_BOUND", ("left", "right")),
    ("iee_wider_than_other", Side(64, (32, "sign"), None), Side(16), "WIDTH_OVERLAP", ()),
)


def main() -> int:
    failures = 0
    for name, left, right, kind, entailed_sides in V4_CASES:
        relation = decide(left, right)
        ok = relation.kind == kind and tuple(side for side, _, _ in relation.entailed) == entailed_sides
        failures += 0 if ok else 1
        print(f"{'PASS' if ok else 'FAIL'} {name}: {relation}")
    print(f"cases={len(V4_CASES)} fail={failures}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
