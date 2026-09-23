# -*- coding: utf-8 -*-
"""Semantic-width 書き換えの契約（Issue #167）。

この module が 1 箇所で決めるもの:

* **rule 表** ``REWRITE_RULES``: normalizer が適用してよい書き換え規則の全部と、
  各規則が意味を保存するために要る前提。規則は 2 種類しかない。

  - 恒等規則（``consumes_input_extension=False``）: 入力について何も仮定せず、
    式の構文だけで元式と同じ値・同じ sort になる。
  - 条件付き規則（``consumes_input_extension=True``）: 演算 operand が
    extension 像（``e == ext_k(low_N(e))``）に属するときだけ成り立つ。像は構文
    （``SEXT(e)`` / ``ZEXT(e)`` / mask）から得るか、parameter については最終
    ``InputCorrespondence`` が含意した入力仮定からだけ得る。``image_kinds`` は
    その規則が意味を保存する ext の種類。

* **authorization** ``RewriteAuthorization``: 最終 relation が片側に含意した
  入力仮定の集合。parameter の像が要る規則は ``grant(rule, parameter)`` を通して
  だけ仮定を受け取る。``grant`` が v5 §4.3 の ``required(rule) ⊆ entailed(final)``
  の実装で、normalizer は自分で仮定を作らない。

* **書き換え済み surface の印**: normalizer / 出力面の揃えが作った analysis を
  記録する。最終 relation の producer はこれを拒否する（書き換え結果から closure を
  作って書き換えを正当化する循環を API で塞ぐ）。

規則を足すときは ``REWRITE_RULES`` に 1 行足し、
``tests/unit/test_semantic_width_rule_certificates.py`` に実規則・実 lowering の
certificate を足す（表と certificate の対応は test が強制する）。
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import hashlib
from typing import Any, FrozenSet, Mapping, Optional, Tuple
import weakref


class ExtensionKind(str, Enum):
    """``p == ext_kind(low_N(p))`` の ext の種類。"""

    SIGN = "sign"
    ZERO = "zero"

    @property
    def smt_operator(self) -> str:
        return "sign_extend" if self is ExtensionKind.SIGN else "zero_extend"


# ---------------------------------------------------------------------------
# rule 表
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RewriteRule:
    """1 つの書き換え規則の契約。"""

    name: str
    #: 規則が意味を保存する extension 像の種類（空 = 像を使わない恒等規則）。
    image_kinds: FrozenSet[ExtensionKind] = frozenset()
    #: parameter の像に最終 relation の入力仮定を使ってよいか。
    consumes_input_extension: bool = False

    def __post_init__(self) -> None:
        object.__setattr__(self, "image_kinds", frozenset(self.image_kinds))
        if self.consumes_input_extension and not self.image_kinds:
            raise ValueError("a rule that consumes an input extension must name its image kinds")

    def stable_key(self) -> Tuple[object, ...]:
        return (
            "rewrite_rule_v1",
            self.name,
            tuple(sorted(kind.value for kind in self.image_kinds)),
            bool(self.consumes_input_extension),
        )


_BOTH = frozenset({ExtensionKind.SIGN, ExtensionKind.ZERO})

#: 有効な書き換え規則の全部。ここに無い規則を normalizer は適用できない。
REWRITE_RULES: Mapping[str, RewriteRule] = {
    rule.name: rule
    for rule in (
        # SUBPIECE(ext(e), 0) で取り出す幅が e の幅と同じ → e。
        RewriteRule("subpiece_of_extension"),
        # SUBPIECE(a op b, 0) → low(a) op low(b)（ADD/SUB/MULT/AND/OR/XOR、mod 2^N の環準同型）。
        RewriteRule("subpiece_of_ring_operation"),
        # W bit の p & (2^N - 1) → zext_W(low_N(p))（親の sort と全幅値を保つ）。
        RewriteRule("mask_to_zero_extension"),
        # a[N] op c[W]（W > N）: lowering は ext_k(a) op c なので、c が ext_k の像なら low_N(c)。
        RewriteRule("comparison_constant_width_alignment"),
        # 比較の定数 0 を相手の幅へ揃える（0 はどの ext でも 0）。
        RewriteRule("comparison_zero_constant_width"),
        # 両辺が同じ ext の像なら等値・不等は狭めても同じ（ext は単射）。
        RewriteRule("equality_on_extension_images", _BOTH, consumes_input_extension=True),
        # sext は signed 順序を保存する。
        RewriteRule(
            "signed_order_on_sign_extension_images",
            frozenset({ExtensionKind.SIGN}),
            consumes_input_extension=True,
        ),
        # zext は unsigned 順序を保存する。
        RewriteRule(
            "unsigned_order_on_zero_extension_images",
            frozenset({ExtensionKind.ZERO}),
            consumes_input_extension=True,
        ),
    )
}

#: 比較演算子ごとに、狭めるときに使う規則（演算子は変えない。signed/unsigned の
#: 相互変換は規則に無い: ``sext(0x80000000) <u 0`` と ``<s 0`` は食い違う）。
COMPARISON_NARROWING_RULES: Mapping[str, str] = {
    "INT_EQUAL": "equality_on_extension_images",
    "INT_NOTEQUAL": "equality_on_extension_images",
    "INT_SLESS": "signed_order_on_sign_extension_images",
    "INT_SLESSEQUAL": "signed_order_on_sign_extension_images",
    "INT_LESS": "unsigned_order_on_zero_extension_images",
    "INT_LESSEQUAL": "unsigned_order_on_zero_extension_images",
}

REWRITE_RULE_TABLE_DIGEST = hashlib.sha256(
    repr(tuple(sorted(rule.stable_key() for rule in REWRITE_RULES.values()))).encode("utf-8")
).hexdigest()


def rewrite_rule(name: str) -> RewriteRule:
    """表の規則。表に無い名前は programming error。"""

    rule = REWRITE_RULES.get(name)
    if rule is None:
        raise ValueError(f"unknown semantic-width rewrite rule: {name!r}")
    return rule


# ---------------------------------------------------------------------------
# 入力仮定と authorization
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RewriteAssumption:
    """最終 premise が含意する 1 つの入力 extension 仮定。

    意味: 幅 ``parameter_bits`` の parameter ``parameter_index`` について
    ``p == ext_kind(low_{narrow_bits}(p))``。
    """

    parameter_index: int
    parameter_bits: int
    narrow_bits: int
    kind: ExtensionKind

    def __post_init__(self) -> None:
        if type(self.kind) is not ExtensionKind:
            raise TypeError("rewrite assumption kind must be an ExtensionKind")
        if not (0 < int(self.narrow_bits) < int(self.parameter_bits)):
            raise ValueError("rewrite assumption requires 0 < narrow_bits < parameter_bits")
        if int(self.parameter_index) < 0:
            raise ValueError("rewrite assumption requires a real parameter index")

    def stable_key(self) -> Tuple[object, ...]:
        return (
            "rewrite_assumption_v1",
            int(self.parameter_index),
            int(self.parameter_bits),
            int(self.narrow_bits),
            self.kind.value,
        )


@dataclass(frozen=True)
class RewriteAuthorization:
    """片側 analysis の書き換えに最終 relation が与えた入力仮定。

    ``assumptions`` が空なら恒等規則だけが使える（常に健全なので既定値）。
    ``source_digest`` は導出元の最終 relation set の digest。``digest`` は rule 表も
    束ねるので、規則の契約が変われば certificate も変わる。
    """

    assumptions: Tuple[RewriteAssumption, ...] = ()
    source_digest: str = "no_input_correspondence"

    def __post_init__(self) -> None:
        ordered = tuple(sorted(self.assumptions, key=lambda item: item.stable_key()))
        indices = [item.parameter_index for item in ordered]
        if len(indices) != len(set(indices)):
            raise ValueError("rewrite authorization holds at most one assumption per parameter")
        object.__setattr__(self, "assumptions", ordered)

    def grant(self, rule_name: str, parameter_index: int, parameter_bits: int) -> Optional[RewriteAssumption]:
        """規則 ``rule_name`` が parameter の像として使ってよい入力仮定（無ければ None）。

        ``required(rule) ⊆ entailed(final)``: 規則が入力仮定を消費でき、最終 relation が
        この parameter（同じ幅）に仮定を含意し、その ext の種類で規則が意味を保存する
        ときだけ返す。
        """

        rule = rewrite_rule(rule_name)
        if not rule.consumes_input_extension:
            return None
        for item in self.assumptions:
            if item.parameter_index == int(parameter_index) and item.parameter_bits == int(parameter_bits):
                return item if item.kind in rule.image_kinds else None
        return None

    def permitted_rules(self) -> Tuple[Tuple[str, int], ...]:
        """入力仮定を使ってよい (規則, parameter index) の全部（診断・独立 model との照合用）。"""

        return tuple(sorted(
            (rule.name, item.parameter_index)
            for item in self.assumptions
            for rule in REWRITE_RULES.values()
            if rule.consumes_input_extension and item.kind in rule.image_kinds
        ))

    @property
    def digest(self) -> str:
        payload = repr(
            (
                "rewrite_authorization_v2",
                self.source_digest,
                REWRITE_RULE_TABLE_DIGEST,
                tuple(item.stable_key() for item in self.assumptions),
            )
        )
        return hashlib.sha256(payload.encode("utf-8")).hexdigest()


EMPTY_REWRITE_AUTHORIZATION = RewriteAuthorization()


# ---------------------------------------------------------------------------
# 書き換え済み surface の印
# ---------------------------------------------------------------------------


_REWRITTEN_SURFACES: "weakref.WeakValueDictionary[int, Any]" = weakref.WeakValueDictionary()


def mark_rewritten_surface(analysis: Any) -> Any:
    """書き換え（semantic-width normalize / 出力面の揃え）が作った analysis を記録して返す。

    これは多層防御の印で、境界そのものではない: object identity で記録するので、
    ``replace`` 等で複製した値には付かない。raw / 書き換え済みの取り違えを防ぐ主な
    境界は (1) 最終 relation を作るのが raw の入口（dispatch frame の source pair、
    checker の ``produce_final_input_correspondence``、互換経路の raw 引数）だけで、
    (2) FormulaBuilder が relation を作らず必須引数として受け取ること。
    """

    try:
        _REWRITTEN_SURFACES[id(analysis)] = analysis
    except TypeError:
        # weakref を取れない値（test の SimpleNamespace 等）は記録できない。
        pass
    return analysis


def is_rewritten_surface(analysis: Any) -> bool:
    return _REWRITTEN_SURFACES.get(id(analysis)) is analysis
