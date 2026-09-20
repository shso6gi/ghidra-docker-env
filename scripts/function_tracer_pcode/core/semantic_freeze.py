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

import dataclasses
from typing import Any, Dict, Optional, Tuple

from scripts.function_tracer_pcode.core import structural as _structural
from scripts.function_tracer_pcode.core.errors import (
    ExpressionCycleError,
    FrozenExpressionError,
    record_internal_bug,
)
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType, PhiBranch
from scripts.function_tracer_pcode.core.semantic_projection import contains_unsupported_value
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

#: 公開走査で葉として扱う値（中に意味値が入らない型）。
_PUBLISH_LEAF_SCALARS = (str, bytes, int, float, bool, type)

#: この package の接頭辞（外の object の属性を探らないための判定に使う）。
_PACKAGE_PREFIX = "scripts.function_tracer_pcode."


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

    published_refs: Dict[int, bool] = {}
    for node in traversal.post_order:
        _finalize_node(node)
        _publish_runtime_ref_values(node, published_refs)
    return expr


def freeze_condition(condition: Any) -> Any:
    """条件を検証して凍結する（式も一緒に凍る）。"""

    if condition is None:
        return None
    if not getattr(condition, "_frozen", False):
        freeze_expression(getattr(condition, "expression", None))
        object.__setattr__(condition, "_frozen", True)
    return condition


def validated(expr: Optional[Expression]) -> Optional[Expression]:
    """意味 identity の安定 API がその入口で呼ぶ検証。

    「凍結済み = 検証済み」なので、凍結済みなら何もしない。未凍結なら凍らせる
    ことで検証する。閉路はここで typed failure になるので、identity API ごとに
    判定を書き足さなくてよい。

    これは identity の **計算可能性** のための検証であって、意味の公開
    （`publish`）とは別の関心。公開は producer が、検証は identity が行う。
    """

    if expr is None or getattr(expr, "_frozen", False):
        return expr
    return freeze_expression(expr)


def publish(value: Any) -> Any:
    """producer が「この意味値は確定した」と宣言する入口（**安定 interface**）。

    式・条件そのものを渡す。渡した値を公開（検証 + 凍結）して返すので、
    `value = publish(build_something())` と書ける。

    consumer（solver renderer / identity / proof）は公開済みの値しか受け取らない。
    公開するのは **値を作った側** で、consumer 側で「まだなら公開する」と救済しない
    — 救済すると「描画されたから確定」という順序になり、まだ精錬中の値が確定扱いに
    なる。
    """

    if value is None:
        return None
    if isinstance(value, Condition):
        return freeze_condition(value)
    if isinstance(value, Expression):
        return freeze_expression(value)
    return publish_semantic_values(value)


def publish_semantic_values(container: Any) -> Any:
    """`container` が抱えている意味値をすべて公開する。

    **これは carrier を探し回る仕組みではない**。「この入れ物の中身はもう確定
    した」と言えるのは入れ物を組み立てた側だけなので、呼ぶのは常に carrier 自身
    （`__post_init__` や、値を差し替える method）であって、外から container を
    見つけて回る層は無い。registry も、型ごとの登録も、注入点も持たない。

    ここが担うのは「宣言したあと、中の式と条件を漏れなく凍らせる」という機械的な
    部分だけ。どの field に式が入っているかを carrier ごとに数え上げると、field を
    1 つ足したときに公開だけが置いていかれるので、**到達できる意味値をすべて
    公開する**という 1 つの規則にしてある。

    走査の範囲は明示してある（黙って諦める経路を作らない）:

    * 式 / 条件 → 公開する
    * dataclass / NamedTuple / tuple / list / dict / set → 中へ入る
    * **この package で定義された** その他の object → `__dict__` の値へ入る。
      新しい carrier 型が dataclass でなくても取りこぼさないため
    * それ以外（Ghidra object・mock・標準ライブラリ）→ 葉。意味の入れ物ではない。
      **属性を探らない**: 記録再生中の proxy に観測を作ってしまうため

    深さで打ち切らない（明示 stack なので再帰上限も無い）。`id` で一度見た
    object は二度見ないので、循環があっても止まる。
    """

    stack: List[Any] = [container]
    seen: Dict[int, bool] = {}
    while stack:
        value = stack.pop()
        if value is None or isinstance(value, _PUBLISH_LEAF_SCALARS):
            continue
        value_id = id(value)
        if value_id in seen:
            continue
        seen[value_id] = True

        # 型は `isinstance` で見る。`hasattr` で属性を探ると、解析結果が抱えて
        # いる Ghidra object（記録再生中は proxy）に観測が走ってしまう。
        if isinstance(value, Expression):
            freeze_expression(value)
            continue
        if isinstance(value, Condition):
            freeze_condition(value)
            continue
        if isinstance(value, (tuple, list, set, frozenset)):
            stack.extend(value)
            continue
        if isinstance(value, dict):
            stack.extend(value.values())
            continue
        if dataclasses.is_dataclass(value) and not isinstance(value, type):
            stack.extend(
                getattr(value, field.name, None) for field in dataclasses.fields(value)
            )
            continue
        if _is_owned_object(value):
            owned_state = getattr(value, "__dict__", None)
            if isinstance(owned_state, dict):
                stack.extend(owned_state.values())
    return container


def _is_owned_object(value: Any) -> bool:
    """この package が定義した object か（外の object の属性は探らない）。"""

    module = type(value).__module__ or ""
    return module.startswith(_PACKAGE_PREFIX)


def _publish_runtime_ref_values(node: Any, published: Dict[int, bool]) -> None:
    """node の runtime ref が抱える式を公開する。

    ref は frozen dataclass だが、中の `Expression` は別 object なので、それを
    凍らせない限り「凍結後も意味が動く」経路が残る（loop summary の
    `transition_expr` など）。node 自身を凍らせた **後** に辿るので、ref から
    node へ戻る参照があってもそこで止まる。
    """

    runtime_ref = node.__dict__.get("runtime_ref")
    if runtime_ref is None:
        return
    if id(runtime_ref) in published:
        return
    published[id(runtime_ref)] = True
    publish_semantic_values(runtime_ref)


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
    candidate_children = []
    equivalence_children = []
    tree_size = 1
    # 「digest だけで他と区別できるか」も子から上へ畳む。root で 1 度見れば
    # よくなるので、equivalence digest が走査を増やさない。
    identity_complete = (
        payload.comparable
        and payload.identity_complete
        and not _projection_has_unsupported_value(fields["_snapshot"])
    )
    for edge in ordered_semantic_edges(node):
        child = edge.child
        if child is None:
            candidate_children.append(None)
            equivalence_children.append(None)
            continue
        candidate_children.append(child.__dict__.get("_structural_hash"))
        equivalence_children.append(child.__dict__.get("_equivalence_digest"))
        tree_size += int(child.__dict__.get("_tree_size") or 1)
        identity_complete = identity_complete and bool(
            child.__dict__.get("_identity_complete", False)
        )
    # 2 つの digest は契約が違う（bucket 専用 / 外へ出す安定 identity）ので
    # 値も分けてある。合成規則は 1 本なので、正規化が食い違うことはない。
    fields["_structural_hash"] = _structural.compose_candidate_digest(
        node, tuple(candidate_children)
    )
    fields["_equivalence_digest"] = _structural.compose_equivalence_digest(
        node, tuple(equivalence_children)
    )
    fields["_tree_size"] = min(TREE_SIZE_CAP, tree_size)
    fields["_identity_complete"] = identity_complete
    fields["_frozen"] = True


def _projection_has_unsupported_value(snapshot: Any) -> bool:
    """snapshot が「値として固定できなかったもの」を含むか。

    含むなら equivalence digest はその式を他と区別できないので、digest を
    名乗らせない（`identity_complete` を落とす）。
    """

    runtime = snapshot.runtime
    return any(
        contains_unsupported_value(value)
        for value in (
            runtime.stable_key,
            runtime.semantic_key,
            runtime.stable_origin,
            snapshot.storage.identity,
        )
    )


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
