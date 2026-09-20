# -*- coding: utf-8 -*-
"""意味値の一生（Issue #22 PR-22-B）。**状態を持つのはここだけ**。

意味値（`Expression` / `Condition`）は 3 つの状態を順に通る:

.. code-block:: text

    CONSTRUCTION   組み立て・精緻化の途中。意味 field を書き換えてよい
         |
         | freeze / validation（`core/semantic_freeze.freeze_expression`）
         v
    VALIDATED      graph に閉路が無いことを確かめ、生 object を投影し終えた
                   immutable snapshot。**意味は確定したが、作った側はまだ
                   「完成した」と言っていない**
         |
         | publication（`core/semantic_freeze.publish` — producer だけが呼ぶ）
         v
    PUBLISHED      producer が「この値はもう変わらない」と宣言した。
                   solver consumer が受け取ってよいのはこれだけ

なぜ 2 つに分けるか: 「immutable だから solver へ渡してよい」と「producer が
完成を宣言したから solver へ渡してよい」は別の話。identity（candidate hash /
完全比較 / digest）は計算のために graph の健全性を要求するので、未凍結の入力を
その場で validated にする。そこで 1 bit しか持たないと、

.. code-block:: python

    expr = build_expression()
    candidate_hash(expr)   # identity の都合で validated になる
    expr.to_smt()          # producer は何も宣言していないのに通ってしまう

という迂回ができてしまい、「construction/refinement → producer publication →
solver consumption」という契約が identity API 経由で破れる。

**状態の表し方**: 意味値 1 つあたり `__dict__` の bool 2 つ（`_frozen` /
`_published`）。node 数が数百万になり得るので、状態 object を 1 つずつ持たせない。
その代わり **読み書きの規則をこの module へ集める** ので、状態遷移を知っている
場所は 1 つで済む。`_published` は単独では意味を持たない（`is_published` は
両方の bit を見る）ので、「published は validated を含む」は表現の側で閉じている。

**遷移は単調**。逆行する API は置かない。値を変えたいときは新しい値を作る
（`derive_with` / `clone_with` / `deepcopy`）。新しい値は必ず CONSTRUCTION から
始まる — 状態 field を引き継がないのは各 carrier の責務で、その一覧が
`LIFECYCLE_STATE_FIELDS`。**これから仕上げる材料だから**であって、「派生値は
公開しない」という規則ではない: `Condition.negate()` は仕上げる余地の無い派生
（条件には refinement 段階が無い）なので、公開済みの条件からは公開済みで始まる。
"""

from __future__ import annotations

from enum import IntEnum
from typing import Any, Dict


class SemanticLifecycle(IntEnum):
    """意味値が今どの段階に居るか。

    `IntEnum` にしてあるのは「後戻りしない」を `>=` で書けるようにするため
    （`state >= SemanticLifecycle.VALIDATED` が「検証は済んでいる」になる）。
    """

    CONSTRUCTION = 0
    VALIDATED = 1
    PUBLISHED = 2


#: 状態そのものを表す field。複製（`clone_with` / `deepcopy`）はこれを **引き
#: 継がない**: 複製は「これから仕上げる材料」なので、元の値の宣言を名乗れない。
LIFECYCLE_STATE_FIELDS = ("_frozen", "_published")


def state_of(fields: Dict[str, Any]) -> SemanticLifecycle:
    """`__dict__` から状態を読む。

    `_published` は単独では状態を作れない — validated を経ずに published には
    ならない、という不変条件をここで閉じている。
    """

    if not fields.get("_frozen", False):
        return SemanticLifecycle.CONSTRUCTION
    if fields.get("_published", False):
        return SemanticLifecycle.PUBLISHED
    return SemanticLifecycle.VALIDATED


def mark_validated(fields: Dict[str, Any]) -> None:
    """検証・凍結が終わった値として印を付ける（公開はしない）。"""

    fields["_frozen"] = True


def mark_published(fields: Dict[str, Any]) -> None:
    """producer の宣言として印を付ける。

    validated を経ていない値へ付けても `state_of` は PUBLISHED を返さない
    （上の不変条件）。呼ぶのは `core/semantic_freeze` の公開境界だけ。
    """

    fields["_published"] = True


def lifecycle_of(value: Any) -> SemanticLifecycle:
    """意味値の状態。`Expression` / `Condition` にだけ使う。

    任意の object には使わない: 記録再生中の Ghidra proxy に属性を尋ねると、
    記録済みの観測列に無い問い合わせを作ってしまう。呼ぶ側が `isinstance` で
    種別を確かめてから渡すこと。
    """

    fields = getattr(value, "__dict__", None)
    if not isinstance(fields, dict):
        return SemanticLifecycle.CONSTRUCTION
    return state_of(fields)


def is_validated(value: Any) -> bool:
    """検証済み（immutable snapshot 確定済み）か。公開済みかは問わない。"""

    return lifecycle_of(value) >= SemanticLifecycle.VALIDATED


def is_published(value: Any) -> bool:
    """producer が完成を宣言済みか。solver consumer が要求するのはこれ。"""

    return lifecycle_of(value) is SemanticLifecycle.PUBLISHED
