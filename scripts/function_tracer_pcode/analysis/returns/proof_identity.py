# -*- coding: utf-8 -*-
"""証明鍵に載せる identity と、**内部表現 / 保存表現の境界**。

## 境界

* 解析の内部では typed な `CompleteIdentity`（構築時に「安定 plain data だけで
  できている」ことを確かめた型）
* structural proof / source key / JSON など **保存できる evidence** には
  `.key`（plain stable data）だけを入れる
* 読み手はその保存形式を契約として読む

wrapper object と保存形式を同じ field に混ぜると、読み手が黙って捨てる。実際、
`conditional_progress_guard_keys` に wrapper が入り、読み手が tuple しか受けない
ために conditional-progress proof が保存後の再検証で必ず落ちていた。

名前で境界が分かるようにしてある: **`*_key` を返すものは plain data**、
`*_identity` を返すものは typed。

## resource policy はここに無い

以前ここには `PROOF_KEY_MAX_SEMANTIC_NODES = 8192` があった。identity は任意の
有限 DAG に対して定義できるので、node 数の上限は identity の意味ではなく
resource policy で、しかも identity の有無が候補・証明の可否を決める =
correctness-visible。**budget policy と既定値の owner は PR-22-D** なので、
PR-22-C は暫定値も持たない。

上限なしで許容できる理由: 作業量は distinct node 数に比例し、凍結や snapshot が
既に同じ order で走査している。直列化した大きさが問題になるのは summary
candidate が実際に作られる場合だけで、固定 subset ではその鍵が 1 件も永続化
されない。上限を入れたくなったとき、機構は `structural_identity_form` の
`max_semantic_nodes` 引数として既にあるので、PR-22-D は値を渡すだけでよい。
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
    identity_key_of,
)


# --- typed（内部で組み立てる側） -------------------------------------------


def proof_condition_identity(condition: Any) -> Optional[CompleteIdentity]:
    """条件の完全 identity（組めなければ `None`）。"""

    return condition_identity(condition)


def proof_condition_identities(conditions: Sequence[Any]) -> Optional[CompleteIdentity]:
    """条件列の完全 identity（1 つでも組めなければ `None`）。"""

    return condition_identities(conditions)


def proof_expression_identity(expr: Any) -> Optional[CompleteIdentity]:
    """式の完全 identity（「式が無い」は専用の値。組めないなら `None`）。"""

    return expression_identity(expr)


def definite_proof_part(tag: str, value: Any) -> CompleteIdentity:
    """identity ではない確定データ（site 名など）を部品にする。"""

    return definite_atoms(tag, value)


def compose_proof_key(tag: str, *parts: Optional[CompleteIdentity]) -> Optional[StructuralKey]:
    """部品がすべて揃っているときだけ証明鍵を組む（欠けたら `None`）。

    返るのは **plain data**。保存境界を越えるのはこの形。
    """

    return compose_complete_identity(tag, *parts)


# --- plain（保存境界を越える側） ---------------------------------------------


def proof_condition_key(condition: Any) -> Optional[StructuralKey]:
    """条件の identity を **保存形式**（plain data）で。組めなければ `None`。

    structural proof や source key に入れるのはこちら。
    """

    return identity_key_of(proof_condition_identity(condition))


def proof_expression_key(expr: Any) -> Optional[StructuralKey]:
    """式の identity を **保存形式**（plain data）で。組めなければ `None`。"""

    return identity_key_of(proof_expression_identity(expr))


def proof_condition_keys(conditions: Sequence[Any]) -> Optional[StructuralKey]:
    """条件列の identity を **保存形式**で。1 つでも組めなければ `None`。"""

    return identity_key_of(proof_condition_identities(conditions))
