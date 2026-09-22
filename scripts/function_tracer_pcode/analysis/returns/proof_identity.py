# -*- coding: utf-8 -*-
"""証明鍵に載せる identity と、その **大きさの policy** の owner。

`core/structural` が持つのは identity の **意味**（何が同じで何が違うか）で、
大きさの上限は持たない — identity は任意の有限 DAG に対して定義できる。

上限が要るのは「作った identity を直列化して鍵に載せる」側で、費用を払うのも
そこ。だからこの module が

* 上限の値（`PROOF_KEY_MAX_SEMANTIC_NODES`）
* 上限を効かせた identity constructor

を 1 箇所で持つ。上限を超える式には identity を作らない（`None`）ので、
鍵を組む側は候補・証明を出さない（fail-closed）。

**値の owner は最終的に PR-22-D**: `BudgetPolicy` がこの定数を引き取ったら、
ここは policy から値を受け取るだけになる。PR-22-C がここに置いているのは、
上限なしにすると直列化する鍵の大きさが `main`（予算付き legacy key）より
増えてしまうからで、値そのものを PR-22-C の設計判断として主張していない。
"""

from __future__ import annotations

from typing import Any, Optional, Sequence

from scripts.function_tracer_pcode.core.structural import (
    CompleteIdentity,
    StructuralKey,
    compose_complete_identity,
    condition_identities,
    condition_identity,
    definite_atoms,
    expression_identity,
)

#: 証明鍵に載せる identity が覆う distinct な意味 node の上限。
#:
#: 値は既存の慣習に合わせてある: `expression_provenance_key` は同じ量
#: （直列化する構造 payload の node 数）を `max_digest_nodes=8192` で抑えている。
#: 新しい数を持ち込むより、同じ量には同じ上限を使う。
PROOF_KEY_MAX_SEMANTIC_NODES = 8192


def proof_condition_identity(condition: Any) -> Optional[CompleteIdentity]:
    """条件の完全 identity（証明鍵用。大きすぎるなら `None`）。"""

    return condition_identity(condition, max_semantic_nodes=PROOF_KEY_MAX_SEMANTIC_NODES)


def proof_condition_identities(conditions: Sequence[Any]) -> Optional[CompleteIdentity]:
    """条件列の完全 identity（1 つでも組めなければ `None`）。"""

    return condition_identities(
        conditions, max_semantic_nodes=PROOF_KEY_MAX_SEMANTIC_NODES
    )


def proof_expression_identity(expr: Any) -> Optional[CompleteIdentity]:
    """式の完全 identity（「式が無い」は専用の値。組めないなら `None`）。"""

    return expression_identity(expr, max_semantic_nodes=PROOF_KEY_MAX_SEMANTIC_NODES)


def compose_proof_key(tag: str, *parts: Optional[CompleteIdentity]) -> Optional[StructuralKey]:
    """部品がすべて揃っているときだけ証明鍵を組む（欠けたら `None`）。"""

    return compose_complete_identity(tag, *parts)


def definite_proof_part(tag: str, value: Any) -> CompleteIdentity:
    """identity ではない確定データ（site 名など）を部品にする。"""

    return definite_atoms(tag, value)
