# -*- coding: utf-8 -*-
"""検証・凍結と **公開** の境界（Issue #22 PR-22-B）。

状態そのものは `core/semantic_lifecycle.py` が定義する。この module が持つのは
**状態を進めてよい条件と、進めるときに何をするか**:

.. code-block:: text

    construction / refinement        analysis / semantics / proof が組み立てる
        |
        | freeze_expression() / freeze_condition()
        |   graph を 1 回走査して閉路が無いことを確かめ、生 object を
        |   `SemanticSnapshot` の値へ投影し、`operands` を tuple・PHI branch を
        |   `PhiBranch` に畳み、`tree_size` と 2 つの digest を確定する
        v
    VALIDATED                        immutable。identity API はここまでを要求する
        |
        | publish() / publish_semantic_values()   ← **producer だけが呼ぶ**
        |   到達できる意味値すべて（子・PHI の条件・runtime ref が抱える式）を
        |   同じ宣言に載せる
        v
    PUBLISHED                        solver consumer が受け取ってよい

**freeze は公開ではない**。identity（candidate hash / 完全比較 / digest）は
計算のために graph の健全性を要求するので、未凍結の入力を `validated()` で
その場で VALIDATED にする。ここで 1 bit しか持たないと、identity API を 1 回
呼んだだけで「producer が完成を宣言した」ことになってしまい、
construction/refinement → publication → consumption の順序が identity 経由で
迂回できる。分けてあるので、**identity consumer は公開権限を持たない**。

**閉路の判定はこの module の中だけには無い**。走査そのものは
`core/semantic_snapshot.traverse_semantic_graph` にあり、freeze・公開・graph
snapshot が同じ 1 実装を共有する（実装を 2 つ持つと片方だけが直るため）。
この module が足すのは「失敗を pair の台帳へ記録してから raise する」ことだけで、
PR-106-0 の経路で `internal_exception` の ERROR になる。

**到達できる意味値をどう数えるか**（`_walk_semantic_carriers`）も 1 実装。
freeze と公開は同じ到達規則に別の操作を載せるだけなので、「どこまでが 1 つの
意味の入れ物か」の答えが 2 つに割れない。
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
from scripts.function_tracer_pcode.core.semantic_lifecycle import (
    is_published,
    is_validated,
    mark_published,
    mark_validated,
)
from scripts.function_tracer_pcode.core.semantic_projection import contains_unsupported_value
from scripts.function_tracer_pcode.core.semantic_snapshot import (
    build_semantic_snapshot,
    local_semantic_payload,
    ordered_semantic_edges,
    traverse_semantic_graph,
)


FREEZE_SITE = "core.semantic_freeze.freeze_expression"
PUBLISH_SITE = "core.semantic_freeze.publish"

#: `tree_size` の飽和上限。共有 DAG の木換算 node 数は深さに対して指数に
#: なり得るので、診断のための数値のために bignum を育てない。
TREE_SIZE_CAP = 1 << 62

#: 公開走査で葉として扱う値（中に意味値が入らない型）。
_PUBLISH_LEAF_SCALARS = (str, bytes, int, float, bool, type)

#: この package の接頭辞（外の object の属性を探らないための判定に使う）。
_PACKAGE_PREFIX = "scripts.function_tracer_pcode."


def is_frozen(value: Any) -> bool:
    """`Expression` / `Condition` が検証済み（immutable snapshot 確定済み）か。

    **公開済みかは言っていない**。solver consumer が見るのは `is_published`。
    """

    return is_validated(value)


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

    visited_refs: Dict[int, bool] = {}
    for node in traversal.post_order:
        _finalize_node(node)
        _validate_runtime_ref_values(node, visited_refs)
    return expr


def freeze_condition(condition: Any) -> Any:
    """条件を検証して凍結する（式も一緒に凍る）。公開はしない。"""

    if condition is None:
        return None
    if not is_validated(condition):
        freeze_expression(getattr(condition, "expression", None))
        mark_validated(condition.__dict__)
    return condition


def validated(expr: Optional[Expression]) -> Optional[Expression]:
    """意味 identity の安定 API がその入口で呼ぶ検証。

    検証済みなら何もしない。未検証なら凍らせることで検証する。閉路はここで
    typed failure になるので、identity API ごとに判定を書き足さなくてよい。

    **これは公開ではない**。identity は「この graph は計算してよい形か」を
    要求しているだけで、「作った側が完成を宣言したか」は聞いていない。ここで
    公開まで進めてしまうと、candidate hash を 1 回取っただけで solver へ渡せる
    値になり、producer が宣言する契約が identity 経由で迂回できる。
    """

    if expr is None or is_validated(expr):
        return expr
    return freeze_expression(expr)


# ---------------------------------------------------------------------------
# publication — producer が完成を宣言する境界
# ---------------------------------------------------------------------------


def publish(value: Any) -> Any:
    """producer が「この意味値は確定した」と宣言する入口（**安定 interface**）。

    式・条件・それらを抱えた入れ物のいずれを渡してもよい。渡した値をそのまま
    返すので、`value = publish(build_something())` と書ける。

    公開するのは **値を作った側**。consumer（solver renderer / identity / proof）
    側で「まだなら公開する」と救済しない — 救済すると「描画されたから確定」と
    いう順序になり、まだ精錬中の値が確定扱いになる。

    公開は **検証を含む**（未検証なら先に凍らせる）。逆は成り立たない:
    `freeze()` や identity API は検証しかしないので、公開済みにはならない。
    """

    if value is None:
        return None
    if isinstance(value, Condition):
        return publish_condition(value)
    if isinstance(value, Expression):
        return publish_expression(value)
    return publish_semantic_values(value)


def publish_expression(expr: Optional[Expression]) -> Optional[Expression]:
    """式 graph を検証してから公開する（冪等）。

    公開は root だけに付ける印ではない。`to_smt()` は子も PHI の条件も
    runtime ref が抱える式も描くので、**そこから到達できる意味値が同じ宣言に
    載っていなければ「公開済みの入力だけを受ける」が成り立たない**。公開済みの
    subtree には入り直さないので、費用は新しく足された node の数に比例する。
    """

    if expr is None:
        return None
    if is_published(expr):
        return expr
    freeze_expression(expr)

    traversal = traverse_semantic_graph(expr, prune=is_published)
    visited_refs: Dict[int, bool] = {}
    for node in traversal.post_order:
        _publish_node(node, visited_refs)
    return expr


def publish_condition(condition: Any) -> Any:
    """条件を検証してから公開する（式も一緒に公開される）。"""

    if condition is None:
        return None
    if is_published(condition):
        return condition
    freeze_condition(condition)
    publish_expression(getattr(condition, "expression", None))
    mark_published(condition.__dict__)
    return condition


def publish_semantic_values(container: Any) -> Any:
    """`container` が抱えている意味値をすべて公開する。

    **これは carrier を探し回る仕組みではない**。「この入れ物の中身はもう確定
    した」と言えるのは入れ物を組み立てた側だけなので、呼ぶのは常に carrier 自身
    （`__post_init__` や、値を差し替える method）であって、外から container を
    見つけて回る層は無い。registry も、型ごとの登録も、注入点も持たない。

    ここが担うのは「宣言したあと、中の式と条件を漏れなく公開する」という機械的な
    部分だけ。どの field に式が入っているかを carrier ごとに数え上げると、field を
    1 つ足したときに公開だけが置いていかれるので、**到達できる意味値をすべて
    公開する**という 1 つの規則（`_walk_semantic_carriers`）にしてある。
    """

    return _walk_semantic_carriers(container, publish_expression, publish_condition)


def validate_semantic_values(container: Any) -> Any:
    """`container` が抱えている意味値をすべて検証・凍結する（公開はしない）。

    公開と同じ到達規則に別の操作を載せる。freeze が runtime ref の抱える式を
    固定するのにこれを使う — ref の中の式が後から変わると「凍結後も意味が動く」
    経路が残るが、**ref を凍らせたことは producer の宣言ではない**。
    """

    return _walk_semantic_carriers(container, freeze_expression, freeze_condition)


def _walk_semantic_carriers(container: Any, on_expression, on_condition) -> Any:
    """入れ物から到達できる意味値に操作を 1 回ずつ適用する。**到達規則の唯一の実装**。

    走査の範囲は明示してある（黙って諦める経路を作らない）:

    * 式 / 条件 → `on_expression` / `on_condition` を適用して、そこで止まる
      （その先は操作側が graph を辿る）
    * tuple / list / set / frozenset → 要素へ入る
    * dict → **key と value の両方へ入る**。式を鍵にした cache が実在する
      （`analysis/condition/bitvector.py` の `Dict[Expression, ...]`）ので、
      「到達できる意味値をすべて」と言う以上 key を外す理由が無い
    * dataclass / NamedTuple → field へ入る
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
            on_expression(value)
            continue
        if isinstance(value, Condition):
            on_condition(value)
            continue
        if isinstance(value, (tuple, list, set, frozenset)):
            stack.extend(value)
            continue
        if isinstance(value, dict):
            stack.extend(value.keys())
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


def _publish_node(node: Expression, visited_refs: Dict[int, bool]) -> None:
    """検証済みの node 1 つを公開する。

    印を先に付けてから ref を辿る。ref の中の式が同じ node へ戻ってくる形でも、
    そこで止まる。
    """

    if is_published(node):
        return
    mark_published(node.__dict__)
    # PHI の branch 条件は graph の辺としては「条件式」しか見えない。条件
    # object そのものも consumer（`Condition.to_smt`）が描くので、同じ宣言に
    # 載せる。
    if node.expr_type == ExpressionType.PHI:
        for branch in node.__dict__.get("value") or ():
            condition = branch[0] if isinstance(branch, (tuple, list)) and branch else None
            if isinstance(condition, Condition):
                publish_condition(condition)
    runtime_ref = node.__dict__.get("runtime_ref")
    if runtime_ref is None or id(runtime_ref) in visited_refs:
        return
    visited_refs[id(runtime_ref)] = True
    publish_semantic_values(runtime_ref)


def _is_owned_object(value: Any) -> bool:
    """この package が定義した object か（外の object の属性は探らない）。"""

    module = type(value).__module__ or ""
    return module.startswith(_PACKAGE_PREFIX)


def _validate_runtime_ref_values(node: Any, visited: Dict[int, bool]) -> None:
    """node の runtime ref が抱える式を検証・凍結する（公開はしない）。

    ref は frozen dataclass だが、中の `Expression` は別 object なので、それを
    凍らせない限り「凍結後も意味が動く」経路が残る（loop summary の
    `transition_expr` など）。node 自身を凍らせた **後** に辿るので、ref から
    node へ戻る参照があってもそこで止まる。
    """

    runtime_ref = node.__dict__.get("runtime_ref")
    if runtime_ref is None:
        return
    if id(runtime_ref) in visited:
        return
    visited[id(runtime_ref)] = True
    validate_semantic_values(runtime_ref)


def _finalize_node(node: Expression) -> None:
    """子が全部凍った node を確定させる。"""

    if is_validated(node):
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
    # 検証が終わった印。公開ではない（`core/semantic_lifecycle.py`）。
    mark_validated(fields)


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
