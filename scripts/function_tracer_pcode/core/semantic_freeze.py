# -*- coding: utf-8 -*-
"""mutable な構築から immutable な意味 snapshot への境界（Issue #22 PR-22-B）。

式の一生は 3 段階で、段階ごとに責務 owner が違う:

1. **construction** — `Expression` / `Condition` を解析中に組み立てる
   （`analysis/` / `semantics/`）。この間は field を書き換えてよい。
2. **freeze**（この module）— graph を 1 回だけ後順で走査し、生の runtime
   object を `SemanticSnapshot` へ投影し、`operands` を tuple に、PHI の branch を
   `PhiBranch` に畳み、`tree_size` と candidate hash を確定させて凍結する。
3. **immutable consumption** — structural identity / render / proof は凍結後の
   値と snapshot だけを見る。意味 field を書き換えようとしたら
   `FrozenExpressionError`。

この module が所有するのは 2 の「いつ・どうやって凍らせるか」だけで、「node の
意味とは何か」（`core/semantic_snapshot.py`）とも「2 つの式が同じか」
（`core/structural.py`）とも別の変更軸になっている。

閉路は通常入力として認めない **内部不整合** として扱う。placeholder を置いて
意味処理を続けると、比較や SMT 生成が「見えていない部分」を無視した答えを出して
しまうので、`ExpressionCycleError` を台帳へ記録してから raise し、PR-106-0 の
経路で `internal_exception` の ERROR にする（`core/errors.py` の gate）。
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple

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
)


FREEZE_SITE = "core.semantic_freeze.freeze_expression"

#: `tree_size` の飽和上限。共有 DAG の木換算 node 数は深さに対して指数に
#: なり得るので、診断のための数値のために bignum を育てない。
TREE_SIZE_CAP = 1 << 62


def is_frozen(value: Any) -> bool:
    """`Expression` / `Condition` が凍結済みか。"""

    return bool(getattr(value, "_frozen", False))


def freeze_expression(expr: Optional[Expression]) -> Optional[Expression]:
    """式 graph を凍結して `expr` を返す（すでに凍結済みなら何もしない）。

    走査は明示 stack の後順で、深い式でも Python の再帰上限に当たらない。
    凍結済み node には入り直さないので、同じ graph を何度凍結しても費用は
    「新しく足された node の数」に比例する。
    """

    if expr is None:
        return None
    if getattr(expr, "_frozen", False):
        return expr

    # (node, exiting)。exiting=False で子を積み、True で自分を確定させる。
    stack: List[Tuple[Expression, bool]] = [(expr, False)]
    active: Dict[int, bool] = {}
    entered: Dict[int, bool] = {}

    while stack:
        node, exiting = stack.pop()
        node_id = id(node)
        if exiting:
            active.pop(node_id, None)
            _finalize_node(node)
            continue
        if getattr(node, "_frozen", False):
            continue
        if node_id in active:
            _raise_cycle(node)
        if node_id in entered:
            # 同じ node が兄弟として 2 回現れた（共有 DAG）。1 回目の確定で
            # 凍結済みになるので、ここへ来るのは同じ親の辺が複数ある場合だけ。
            continue
        entered[node_id] = True
        active[node_id] = True
        stack.append((node, True))
        for edge in reversed(ordered_semantic_edges(node)):
            child = edge.child
            if child is not None and not getattr(child, "_frozen", False):
                stack.append((child, False))

    return expr


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
    fields["_local_payload"] = local_semantic_payload(node)

    # 子 digest と `tree_size` は **辺の正準順**（`ordered_semantic_edges`）で
    # 集める。`operands` を直接読むと PHI の欠けた条件や二項演算の欠けた
    # operand の位置がずれて、hash と完全比較が別の並びを見てしまう。
    child_digests = []
    tree_size = 1
    for edge in ordered_semantic_edges(node):
        child = edge.child
        if child is None:
            child_digests.append(None)
            continue
        child_digests.append(child.__dict__.get("_structural_hash"))
        tree_size += int(child.__dict__.get("_tree_size") or 1)
    fields["_structural_hash"] = _structural.compose_candidate_digest(
        node, tuple(child_digests)
    )
    fields["_tree_size"] = min(TREE_SIZE_CAP, tree_size)
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


def _raise_cycle(node: Expression) -> None:
    exc = ExpressionCycleError(
        "semantic graph contains a cycle at "
        f"{getattr(getattr(node, 'expr_type', None), 'name', None)} "
        f"{getattr(node, 'name', None)!r}"
    )
    record_internal_bug(exc, site=FREEZE_SITE)
    raise exc


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
