# -*- coding: utf-8 -*-
"""mutable な構築から validated immutable graph への境界（Issue #22 PR-22-B）。

式の一生は 4 段階で、段階ごとに責務 owner が違う:

1. **construction** — `Expression` / `Condition` を解析中に組み立てる
   （`analysis/` / `semantics/`）。この間は field を書き換えてよい。
2. **validation + freeze**（この module）— graph を 1 回だけ走査して閉路が無い
   ことを確かめ、生 object を `SemanticSnapshot` の値へ投影し、`operands` を
   tuple・PHI branch を `PhiBranch` に畳み、`tree_size` と candidate hash を
   確定させて凍結する。
3. **validated immutable graph** — 凍結済みの式は「検証済みの意味」であり、
   consumer はもう構造の健全性を確かめ直さなくてよい。
4. **immutable consumption** — structural identity / render / proof は凍結後の
   値と snapshot だけを読む。凍結後の意味 field 書き換えは
   `FrozenExpressionError`。

**閉路の判定はこの module の中だけには無い**。走査そのものは
`core/semantic_snapshot.traverse_semantic_graph` にあり、freeze と graph
snapshot が同じ 1 実装を共有する（実装を 2 つ持つと片方だけが直るため）。
この module が足すのは「失敗を pair の台帳へ記録してから raise する」ことだけで、
PR-106-0 の経路で `internal_exception` の ERROR になる。

意味 identity の安定 API（`candidate_hash` / `structural_equals` /
`structural_identity_digest` / `walk_dag`）はいずれも validated graph を前提と
する。未凍結の入力は `validated()` を通るので、閉路はどの入口から入っても同じ
ように fail closed になる。
"""

from __future__ import annotations

from typing import Any, Optional, Tuple

from scripts.function_tracer_pcode.core import structural as _structural
from scripts.function_tracer_pcode.core.errors import (
    ExpressionCycleError,
    FrozenExpressionError,
    record_internal_bug,
)
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType, PhiBranch
from scripts.function_tracer_pcode.core.semantic_snapshot import (
    build_semantic_snapshot,
    local_semantic_payload,
    ordered_semantic_edges,
    traverse_semantic_graph,
)


FREEZE_SITE = "core.semantic_freeze.freeze_expression"

#: `tree_size` の飽和上限。共有 DAG の木換算 node 数は深さに対して指数に
#: なり得るので、診断のための数値のために bignum を育てない。
TREE_SIZE_CAP = 1 << 62


def is_frozen(value: Any) -> bool:
    """`Expression` / `Condition` が凍結済み（= 検証済み）か。"""

    return bool(getattr(value, "_frozen", False))


def freeze_expression(expr: Optional[Expression]) -> Optional[Expression]:
    """式 graph を検証して凍結し、`expr` を返す（冪等）。

    凍結済み node には入り直さないので、同じ graph を何度凍結しても費用は
    「新しく足された node の数」に比例する。凍結済みの subtree に閉路が隠れる
    ことは無い（凍結できた時点で検証済みなので）。
    """

    if expr is None:
        return None
    if getattr(expr, "_frozen", False):
        return expr

    try:
        traversal = traverse_semantic_graph(expr, prune=is_frozen)
    except ExpressionCycleError as exc:
        # 記録が先、raise が後。途中の `except Exception` に握り潰されても
        # pair 境界が台帳から拾い直せる。
        record_internal_bug(exc, site=FREEZE_SITE)
        raise

    for node in traversal.post_order:
        _finalize_node(node)
    return expr


def validated(expr: Optional[Expression]) -> Optional[Expression]:
    """意味 identity の安定 API がその入口で呼ぶ検証。

    「凍結済み = 検証済み」なので、凍結済みなら何もしない。未凍結なら凍らせる
    ことで検証する。閉路はここで typed failure になるので、identity API ごとに
    判定を書き足さなくてよい。
    """

    if expr is None or getattr(expr, "_frozen", False):
        return expr
    return freeze_expression(expr)


def freeze_condition(condition: Any) -> Any:
    """条件を凍結する（式も一緒に凍る）。"""

    if condition is None:
        return None
    if not getattr(condition, "_frozen", False):
        freeze_expression(getattr(condition, "expression", None))
        object.__setattr__(condition, "_frozen", True)
    return condition


def _finalize_node(node: Expression) -> None:
    """子が全部凍った node を確定させる。"""

    if getattr(node, "_frozen", False):
        return

    fields = node.__dict__
    operands = fields.get("operands")
    if not isinstance(operands, tuple):
        fields["operands"] = tuple(operands or ())

    if node.expr_type == ExpressionType.PHI:
        fields["value"] = _frozen_branches(fields.get("value"))

    # snapshot を先に置く。candidate hash は `semantic_projection()` 経由で
    # snapshot を読むので、順番が逆だと生 object を読んでしまう。
    fields["_snapshot"] = build_semantic_snapshot(node)
    # 完全比較が何度も見る local payload はここで 1 回だけ組む。
    payload = local_semantic_payload(node)
    fields["_local_payload"] = payload

    # 子 digest と `tree_size` は **辺の正準順**（`ordered_semantic_edges`）で
    # 集める。`operands` を直接読むと PHI の欠けた条件や二項演算の欠けた
    # operand の位置がずれて、hash と完全比較が別の並びを見てしまう。
    child_digests = []
    tree_size = 1
    # 「digest だけで他と区別できるか」も子から上へ畳む。root で 1 度見れば
    # よくなるので、identity digest が走査を増やさない。
    identity_complete = payload.comparable and payload.identity_complete
    for edge in ordered_semantic_edges(node):
        child = edge.child
        if child is None:
            child_digests.append(None)
            continue
        child_digests.append(child.__dict__.get("_structural_hash"))
        tree_size += int(child.__dict__.get("_tree_size") or 1)
        identity_complete = identity_complete and bool(
            child.__dict__.get("_identity_complete", False)
        )
    fields["_structural_hash"] = _structural.compose_candidate_digest(
        node, tuple(child_digests)
    )
    fields["_tree_size"] = min(TREE_SIZE_CAP, tree_size)
    fields["_identity_complete"] = identity_complete
    fields["_frozen"] = True


def _frozen_branches(value: Any) -> Tuple[Any, ...]:
    """PHI の branch を `PhiBranch` の tuple へ畳む。

    `PhiBranch` は `tuple` の subclass なので、`isinstance(branch, tuple)` /
    `len(branch) == 2` / unpack / index を使う既存 consumer はそのまま動く。
    """

    branches = []
    for branch in value or ():
        if isinstance(branch, PhiBranch):
            frozen_branch = branch
        elif isinstance(branch, (tuple, list)) and len(branch) == 2:
            frozen_branch = PhiBranch(branch[0], branch[1])
        else:
            # 形が違う branch はここでは直さない。`to_dict()` / renderer が
            # 従来どおり typed な失敗を出す方が、ここで別の例外型に化けるより
            # 追いやすい。
            branches.append(branch)
            continue
        if frozen_branch.condition is not None:
            freeze_condition(frozen_branch.condition)
        branches.append(frozen_branch)
    return tuple(branches)


def frozen_mutation_error(node: Any, field: str) -> FrozenExpressionError:
    """凍結後の意味 field 書き換えを内部バグとして記録し、例外を作る。

    記録してから raise するので、途中の `except Exception` に握り潰されても
    pair 境界が台帳から拾い直して `internal_exception` の ERROR にできる。
    """

    exc = FrozenExpressionError(
        f"{type(node).__name__}.{field} is frozen "
        f"({getattr(getattr(node, 'expr_type', None), 'name', None)}); "
        "derive a new value with clone_with(...) instead of mutating"
    )
    record_internal_bug(exc, site=f"core.semantic_freeze.frozen_mutation:{field}")
    return exc
