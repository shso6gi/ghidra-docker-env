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

**状態を進める操作は failure-atomic**。検証も公開も、派生値と印を operation
内の staging へ積んでから、失敗しない commit 段で一括して書く。「検証中」「公開
中」を公開 state で表さないので、closure の一部だけが VALIDATED / PUBLISHED で
残ることが起きない。検証と公開で transaction の粒度が違う理由は
`_run_publication` に書いてある。

**閉路の判定はこの module の中だけには無い**。走査そのものは
`core/semantic_snapshot.traverse_semantic_graph` にあり、freeze・公開・graph
snapshot が同じ 1 実装を共有する（実装を 2 つ持つと片方だけが直るため）。
この module が足すのは「失敗を pair の台帳へ記録してから raise する」ことだけで、
PR-106-0 の経路で `internal_exception` の ERROR になる。

**到達できる意味値をどう数えるか**（`_walk_semantic_carriers`）も 1 実装。
freeze と公開は同じ到達規則に別の操作を載せるだけなので、「どこまでが 1 つの
意味の入れ物か」の答えが 2 つに割れない。

**直列化の不変性**（Issue #219 C-RS2。契約は `core/semantic_lifecycle.py`）も検証の
一部として決める: storage と runtime ref の LEGACY 表現を凍結時に写し（`_storage_payload` /
`_runtime_ref_payload`。runtime ref は直列化の owner に 1 回だけ作らせた表現の不変な写しで、
ref の型の code が何を読むかは調べない）、closure 全体を積み終えた後に「LEGACY 表現が不変な
状態だけの関数か」を子から上へ 1 回だけ畳む（`_serialization_closed`、
`_derive_serialization_closure`）。どれも派生値なので、ほかの派生値と一緒に commit でだけ書く。
"""

from __future__ import annotations

import dataclasses
from types import MappingProxyType
from typing import Any, Callable, Dict, List, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.core import structural as _structural
from scripts.function_tracer_pcode.core.errors import (
    ExpressionCycleError,
    FrozenExpressionError,
    record_internal_bug,
)
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import (
    Expression,
    ExpressionType,
    PhiBranch,
    coerce_phi_branches,
    runtime_ref_source,
)
from scripts.function_tracer_pcode.core.semantic_lifecycle import (
    CONDITION_SERIALIZATION_INPUTS,
    EXPRESSION_SERIALIZATION_INPUTS,
    NON_INHERITED_FIELDS,
    SerializationInput,
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
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.core.frozen_representation import CAPTURE_MAX_BYTES, freeze_legacy_tree
from scripts.function_tracer_pcode.core.json_encoding import (
    RESULT_JSON_POLICY,
    JsonBudget,
    JsonBudgetExhausted,
    JsonValueRejected,
)


FREEZE_SITE = "core.semantic_freeze.freeze_expression"

#: `tree_size` の飽和上限。共有 DAG の木換算 node 数は深さに対して指数に
#: なり得るので、診断のための数値のために bignum を育てない。
TREE_SIZE_CAP = 1 << 62

#: 公開走査で葉として扱う値（中に意味値が入らない型）。
_PUBLISH_LEAF_SCALARS = (str, bytes, int, float, bool, type)

#: この package の接頭辞（外の object の属性を探らないための判定に使う）。
_PACKAGE_PREFIX = "scripts.function_tracer_pcode."


class _LifecycleStaging:
    """1 回の lifecycle 操作のあいだだけ生きる作業領域。

    **公開 state（`_frozen` / `_published`）を再入防止 flag に流用しない**ため
    に要る。流用すると「検証中」と「検証済み」が区別できず、途中で失敗した
    closure の root だけが検証済みとして残る（partial commit）。ここへ積んで
    おき、closure 全体が成功したときだけ一括で書く。

    `entered` は式・条件・runtime ref を `id` で覚える。back-reference（ref の
    中の式が元の node を指す）も、同じ値を 2 度積むこともここで止まる。
    """

    __slots__ = ("entered", "derived", "expressions", "conditions", "storage_records", "runtime_ref_records")

    def __init__(self) -> None:
        self.entered: Dict[int, bool] = {}
        #: `id(expression)` / `id(condition)` → 確定させる派生値（commit まで公開状態へ書かない）
        self.derived: Dict[int, Dict[str, Any]] = {}
        #: commit 順（子が先）
        self.expressions: List[Expression] = []
        self.conditions: List[Any] = []
        #: `id(StorageInfo)` → (その object, 写し)。同じ storage を共有する node は 1 つの写しを持つ
        self.storage_records: Dict[int, Tuple[Any, Any]] = {}
        #: `id(runtime ref)` → (その object, 表現の写し)。ref は多くの node が共有する
        self.runtime_ref_records: Dict[int, Tuple[Any, Any]] = {}

    def enter(self, value: Any) -> bool:
        """この操作で初めて見た値なら真。2 度目は偽（再入・back-reference）。"""

        value_id = id(value)
        if value_id in self.entered:
            return False
        self.entered[value_id] = True
        return True

    def seen(self, value: Any) -> bool:
        return id(value) in self.entered

    def derived_fields(self, node: Any) -> Dict[str, Any]:
        """子から畳み上げる値の読み口（この操作で積んだ分 → commit 済みの順）。"""

        staged = self.derived.get(id(node))
        return staged if staged is not None else node.__dict__


def freeze_expression(expr: Optional[Expression]) -> Optional[Expression]:
    """式 graph の意味 closure を検証して凍結し、`expr` を返す（冪等）。

    **失敗したら何も確定しない**。closure（graph の node・PHI の条件・runtime
    ref が抱える式と条件）を全部検証し終えてから、派生値と VALIDATED の印を
    一括で書く。途中で閉路が見つかれば staging ごと捨てるので、root だけが
    検証済みになったり、書きかけの snapshot / hash / digest が次回の成功結果
    として読まれたりしない。

    検証済みの closure には入り直さないので、同じ graph を何度凍結しても費用は
    「新しく足された node の数」に比例する。
    """

    if expr is None or is_validated(expr):
        return expr
    _run_validation(lambda staging: _stage_expression_validation(expr, staging))
    return expr


def freeze_condition(condition: Any) -> Any:
    """条件の意味 closure を検証して凍結する（式も一緒に凍る）。公開はしない。

    式と同じく failure-atomic: 式側の検証が失敗したら、条件にも印を付けない。
    """

    if condition is None or is_validated(condition):
        return condition
    _run_validation(lambda staging: _stage_condition_validation(condition, staging))
    return condition


def _run_validation(stage: Any) -> None:
    """staging → commit の 1 transaction。失敗したら 1 つも確定させない。

    閉路は記録してから raise する（PR-106-0 の経路）。記録が先なのは、途中の
    `except Exception` に握り潰されても pair 境界が台帳から拾い直せるため。
    """

    staging = _LifecycleStaging()
    try:
        stage(staging)
    except ExpressionCycleError as exc:
        record_internal_bug(exc, site=FREEZE_SITE)
        raise
    # closure をすべて積み終えてから決める（runtime ref が抱える式は graph の後に積まれる）。
    # commit の前なので、ここで失敗しても何も確定しない
    _derive_serialization_closure(staging)
    _commit_validation(staging)


def _stage_expression_validation(expr: Any, staging: _LifecycleStaging) -> None:
    """式 graph とその closure を staging へ積む（公開状態は動かさない）。"""

    if expr is None or is_validated(expr) or staging.seen(expr):
        return

    def _prune(node: Any) -> bool:
        # 検証済み（= closure ごと確定済み）と、この操作で既に積んだ node。
        return is_validated(node) or staging.seen(node)

    traversal = traverse_semantic_graph(expr, prune=_prune)
    # 先に「この操作で見た」印を付ける。ref の中の式が graph へ戻ってきても
    # ここで止まり、無限再帰にも二重計上にもならない。
    for node in traversal.post_order:
        staging.enter(node)
    # 子が先に積まれている前提で派生値を畳み上げる（post-order）。
    for node in traversal.post_order:
        staging.derived[id(node)] = _derive_node_fields(node, staging)
        staging.expressions.append(node)
    # graph の辺では見えない closure（PHI の条件 object、runtime ref が抱える値）。
    for node in traversal.post_order:
        _stage_node_closure_validation(node, staging)


def _stage_condition_validation(condition: Any, staging: _LifecycleStaging) -> None:
    if condition is None or is_validated(condition) or not staging.enter(condition):
        return
    staging.conditions.append(condition)
    # 条件の派生値（closed の bit）は closure を積み終えた後に足す
    staging.derived[id(condition)] = {}
    _stage_expression_validation(getattr(condition, "expression", None), staging)


def _stage_node_closure_validation(node: Any, staging: _LifecycleStaging) -> None:
    """graph の辺には現れない意味 closure を積む。

    * PHI の branch 条件 object（辺として見えるのは条件 **式** だけ）
    * runtime ref が抱える式と条件（`transition_expr` など。ref は frozen
      dataclass だが、中の式は別 object なので放っておくと意味が動く）
    """

    for condition in _phi_branch_conditions(node):
        _stage_condition_validation(condition, staging)
    runtime_ref = node.__dict__.get("runtime_ref")
    if runtime_ref is None or not staging.enter(runtime_ref):
        return
    _walk_semantic_carriers(
        runtime_ref,
        lambda expr: _stage_expression_validation(expr, staging),
        lambda cond: _stage_condition_validation(cond, staging),
    )


def _commit_validation(staging: _LifecycleStaging) -> None:
    """closure 全体の検証が成功したので、派生値と VALIDATED を一括で書く。

    ここは失敗しない（計算は staging で終わっている）。だから「一部だけ
    VALIDATED」は原理的に起きない。
    """

    for node in staging.expressions:
        fields = node.__dict__
        fields.update(staging.derived[id(node)])
        mark_validated(fields)
    for condition in staging.conditions:
        fields = condition.__dict__
        fields.update(staging.derived[id(condition)])
        mark_validated(fields)


def _phi_branch_conditions(node: Any):
    if node.expr_type != ExpressionType.PHI:
        return
    for branch in node.__dict__.get("value") or ():
        condition = branch[0] if isinstance(branch, (tuple, list)) and branch else None
        if isinstance(condition, Condition):
            yield condition


def validated(expr: Optional[Expression]) -> Optional[Expression]:
    """意味 identity の安定 API がその入口で呼ぶ検証。

    検証済みなら何もしない。未検証なら凍らせることで検証する。閉路はここで
    typed failure になるので、identity API ごとに判定を書き足さなくてよい。
    失敗したときは何も確定しないので、**同じ入力で呼び直せば同じように失敗
    する**（途中結果を成功扱いで拾わない）。

    **これは公開ではない**。identity は「この graph は計算してよい形か」を
    要求しているだけで、「作った側が完成を宣言したか」は聞いていない。ここで
    公開まで進めてしまうと、candidate hash を 1 回取っただけで solver へ渡せる
    値になり、producer が宣言する契約が identity 経由で迂回できる。
    """

    if expr is None or is_validated(expr):
        return expr
    return freeze_expression(expr)


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
    """式 graph を検証してから公開する（冪等・failure-atomic）。

    公開は root だけに付ける印ではない。`to_smt()` は子も PHI の条件も
    runtime ref が抱える式も描くので、**そこから到達できる意味値が同じ宣言に
    載っていなければ「公開済みの入力だけを受ける」が成り立たない**。

    宣言が途中で失敗したら **1 つも公開しない**。「producer の宣言が失敗した
    のに一部だけ solver-consumable」という状態を作らないため。公開済みの
    subtree には入り直さないので、費用は新しく足された node の数に比例する。
    """

    if expr is None or is_published(expr):
        return expr
    _run_publication(lambda staging: _stage_expression_publication(expr, staging))
    return expr


def publish_condition(condition: Any) -> Any:
    """条件を検証してから公開する（式も一緒に公開される・failure-atomic）。"""

    if condition is None or is_published(condition):
        return condition
    _run_publication(lambda staging: _stage_condition_publication(condition, staging))
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

    入れ物 1 つ分が 1 transaction。途中の値で検証が失敗したら、その入れ物からは
    1 つも公開されない（sibling だけ solver へ渡せる状態を作らない）。
    """

    _run_publication(
        lambda staging: _walk_semantic_carriers(
            container,
            lambda expr: _stage_expression_publication(expr, staging),
            lambda cond: _stage_condition_publication(cond, staging),
        )
    )
    return container


def unpublished_semantic_values(container: Any) -> Tuple[Any, ...]:
    """`container` から solver が到達する意味値のうち、**まだ公開されていない**もの。

    公開の不変条件を外から確かめるための読み取り専用の問い合わせ:

    .. code-block:: text

        PUBLISHED(value) ⇒ solver が到達する意味 closure もすべて PUBLISHED

    走査は公開とまったく同じ規則を使う（`_walk_semantic_carriers` + graph の辺
    + PHI の branch 条件 + runtime ref が抱える値）。別の走査を書くと「公開は
    辿るのに検査は辿らない」隙間ができるので、到達規則は 1 つに保つ。

    状態は動かさない。未検証の値は公開されていないので、当然ここに現れる。
    """

    found: Dict[int, Any] = {}
    seen: Dict[int, bool] = {}
    # 明示 stack（graph が深くても再帰上限に当たらない。module の他の走査と同じ形）
    pending: List[Any] = []

    def enqueue(value: Any) -> None:
        if value is None or id(value) in seen:
            return
        seen[id(value)] = True
        if not is_published(value):
            found.setdefault(id(value), value)
        pending.append(value)

    _walk_semantic_carriers(container, enqueue, enqueue)
    while pending:
        value = pending.pop()
        if isinstance(value, Condition):
            enqueue(value.expression)
            continue
        for edge in ordered_semantic_edges(value):
            enqueue(edge.child)
        for condition in _phi_branch_conditions(value):
            enqueue(condition)
        runtime_ref = value.__dict__.get("runtime_ref")
        if runtime_ref is None or id(runtime_ref) in seen:
            continue
        seen[id(runtime_ref)] = True
        _walk_semantic_carriers(runtime_ref, enqueue, enqueue)
    return tuple(found.values())


def _run_publication(stage: Any) -> None:
    """staging → commit の 1 transaction。失敗したら 1 つも公開しない。

    **検証と公開で transaction の粒度が違う**のは、答えている問いが違うから:

    * 検証は「この closure は計算してよい形か」。値ごとに閉じた事実なので、
      値の closure 1 つが 1 transaction（公開が失敗しても、検証済みの値が
      検証済みのまま残るのは正しい — 意味は確かに immutable になっている）。
    * 公開は「producer がこの宣言を出した」。宣言は producer の 1 回の意思
      表示なので、**宣言 1 回が 1 transaction**。途中で落ちたら宣言は無かった
      ことにする。

    どちらも「途中の状態を公開 state で表さない」点は同じ。
    """

    staging = _LifecycleStaging()
    stage(staging)
    _commit_publication(staging)


def _stage_expression_publication(expr: Any, staging: _LifecycleStaging) -> None:
    if expr is None or is_published(expr) or staging.seen(expr):
        return
    # 検証は別 transaction。ここで失敗したら公開 staging は捨てられる。
    freeze_expression(expr)

    def _prune(node: Any) -> bool:
        return is_published(node) or staging.seen(node)

    traversal = traverse_semantic_graph(expr, prune=_prune)
    for node in traversal.post_order:
        if staging.enter(node):
            staging.expressions.append(node)
    for node in traversal.post_order:
        for condition in _phi_branch_conditions(node):
            _stage_condition_publication(condition, staging)
        runtime_ref = node.__dict__.get("runtime_ref")
        if runtime_ref is None or not staging.enter(runtime_ref):
            continue
        _walk_semantic_carriers(
            runtime_ref,
            lambda value: _stage_expression_publication(value, staging),
            lambda value: _stage_condition_publication(value, staging),
        )


def _stage_condition_publication(condition: Any, staging: _LifecycleStaging) -> None:
    if condition is None or is_published(condition) or not staging.enter(condition):
        return
    freeze_condition(condition)
    staging.conditions.append(condition)
    _stage_expression_publication(getattr(condition, "expression", None), staging)


def _commit_publication(staging: _LifecycleStaging) -> None:
    """宣言が closure 全体で成立したので、PUBLISHED を一括で付ける。"""

    for node in staging.expressions:
        mark_published(node.__dict__)
    for condition in staging.conditions:
        mark_published(condition.__dict__)


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
    * それ以外（Ghidra object・mock・標準ライブラリ）と、外の object の代わりをすると宣言した
      この package の型（`__semantic_opaque__`。記録再生の proxy）→ 葉。意味の入れ物ではない。
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


def _is_owned_object(value: Any) -> bool:
    """この package が定義した意味の入れ物になり得る object か（外の object の属性は探らない）。

    この package が定義した型でも、**外の runtime object の代わり**をする型（記録再生の Ghidra
    object の proxy など）は `__semantic_opaque__ = True` を宣言し、外の object と同じく葉になる。
    その `__dict__` は代わりをする仕組みの状態（記録全体・観測の履歴…）で意味の入れ物ではなく、
    辿ると費用が記録の大きさに比例し、本物の object では起きない仕事になる。宣言は class の
    辞書だけから読む（instance の `__getattr__` を呼ばない）。
    """

    kind = type(value)
    module = kind.__module__ or ""
    if not module.startswith(_PACKAGE_PREFIX):
        return False
    return not any(base.__dict__.get(SEMANTIC_OPAQUE_DECLARATION) is True for base in kind.__mro__)


#: 外の runtime object の代わりをする型が宣言する class 属性（`_is_owned_object`）
SEMANTIC_OPAQUE_DECLARATION = "__semantic_opaque__"


def _derive_node_fields(node: Expression, staging: _LifecycleStaging) -> Dict[str, Any]:
    """node 1 つ分の派生値を組み立てて返す（**公開状態へは書かない**）。

    戻り値は commit のときに `__dict__` へ一括で入る。失敗して commit されな
    ければ、snapshot も hash も digest も node には残らない。

    唯一その場で書くのは **正準化**（`operands` を tuple、PHI branch を
    `PhiBranch` へ）。意味を変えず冪等で、identity の派生値でもない一方、
    snapshot と digest はこの形を前提に計算するので後回しにできない。書いても
    node は CONSTRUCTION のままなので、検証済みと誤認されることはない。

    子の派生値は `staging` 経由で読む（この操作で積んだ分 → commit 済みの順）。
    """

    fields = node.__dict__
    operands = fields.get("operands")
    if not isinstance(operands, tuple):
        fields["operands"] = tuple(operands or ())

    if node.expr_type == ExpressionType.PHI:
        # 正準化だけ（lifecycle は動かさない）。branch 条件の検証は
        # `_stage_node_closure_validation` が staging へ積む。
        fields["value"] = coerce_phi_branches(fields.get("value"))

    # snapshot を先に置く。candidate hash は `semantic_projection()` 経由で
    # snapshot を読むので、順番が逆だと生 object を読んでしまう。
    # 生 object を読むのはここ 1 回だけ。まだ node へは書いていないので、
    # payload にも同じ投影を渡す（渡さないと読み直しになる）。
    snapshot = build_semantic_snapshot(node)
    # 完全比較が何度も見る local payload はここで 1 回だけ組む。
    payload = local_semantic_payload(node, snapshot)

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
        and not _projection_has_unsupported_value(snapshot)
    )
    for edge in ordered_semantic_edges(node):
        child = edge.child
        if child is None:
            candidate_children.append(None)
            equivalence_children.append(None)
            continue
        child_fields = staging.derived_fields(child)
        candidate_children.append(child_fields.get("_structural_hash"))
        equivalence_children.append(child_fields.get("_equivalence_digest"))
        tree_size += int(child_fields.get("_tree_size") or 1)
        identity_complete = identity_complete and bool(
            child_fields.get("_identity_complete", False)
        )
    # 2 つの digest は契約が違う（bucket 専用 / 外へ出す安定 identity）ので
    # 値も分けてある。合成規則は 1 本なので、正規化が食い違うことはない。
    return {
        "_snapshot": snapshot,
        "_local_payload": payload,
        "_structural_hash": _structural.compose_candidate_digest(
            node, tuple(candidate_children), payload=payload
        ),
        "_equivalence_digest": _structural.compose_equivalence_digest(
            node, tuple(equivalence_children), payload=payload
        ),
        "_tree_size": min(TREE_SIZE_CAP, tree_size),
        "_identity_complete": identity_complete,
        # LEGACY 表現の storage は凍結時の写しから描く（生の `StorageInfo` は可変）。
        "_storage_payload": _captured_storage(fields.get("storage_info"), staging),
        # runtime ref の表現も凍結時に 1 回だけ作って写す（ref の code が何を読んでも以後は走らない）
        "_runtime_ref_payload": _captured_runtime_ref(fields.get("runtime_ref"), staging),
        # closed かは closure 全体を積んだ後に `_derive_serialization_closure` が決める
        # （runtime ref が抱える式は graph の後に積まれる）。決まるまでは closed でない
        "_serialization_closed": False,
    }


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


def frozen_mutation_error(node: Any, field: str) -> FrozenExpressionError:
    """凍結後の意味 field の書き換え・lifecycle が所有する field の書き換えを内部バグとして
    記録し、例外を作る（規則は `core/semantic_lifecycle.attribute_mutation_allowed`）。

    記録してから raise するので、途中の `except Exception` に握り潰されても
    pair 境界が台帳から拾い直して `internal_exception` の ERROR にできる。
    """

    owned = field in NON_INHERITED_FIELDS
    exc = FrozenExpressionError(
        f"{type(node).__name__}.{field} is "
        f"{'owned by the semantic lifecycle' if owned else 'frozen'} "
        f"({getattr(getattr(node, 'expr_type', None), 'name', None)}); "
        "derive a new value with clone_with(...) instead of mutating"
    )
    record_internal_bug(exc, site=f"core.semantic_freeze.frozen_mutation:{field}")
    return exc


# ---------------------------------------------------------------------------
# 直列化の不変性（Issue #219 C-RS2）
# ---------------------------------------------------------------------------


def _captured_storage(storage: Any, staging: _LifecycleStaging) -> Any:
    """storage の LEGACY 表現の不変な写し（写せなければ `None`）。

    写すのは `StorageInfo` そのもの（`_to_dict_active` が受ける唯一の型）だけ。それ以外・
    scalar でない field を持つものは写さない: その node の表現は従来どおり生の値を読んで
    同じ `TypeError` になり、closed にもならない。
    """

    if storage is None or type(storage) is not StorageInfo:
        return None
    memo = staging.storage_records
    hit = memo.get(id(storage))
    if hit is not None and hit[0] is storage:
        return hit[1]
    try:
        record = storage.frozen_record()
    except TypeError:
        record = None
    memo[id(storage)] = (storage, record)
    return record


def _captured_runtime_ref(runtime_ref: Any, staging: _LifecycleStaging) -> Any:
    """runtime ref の LEGACY 表現を **直列化の owner に 1 回だけ作らせた** 不変な写し（無ければ `None`）。

    表現を作るのは、未凍結の値を描くときと同じ source と同じ walker（`Expression._serialize_runtime_ref`
    と同じ `runtime_ref_source` を LEGACY で作る）なので、写しは凍結の時点の表現そのもの。ref の型が表現をどう作るか
    （`json_items`・そこから dispatch される method・`repr` など）をこの module は調べない: 何を
    読んでいても、読むのはこの 1 回だけになる。

    写さないもの（その node は closed にならず、従来どおり生の ref から描く）:

    * 意味値（式・条件）を抱える ref。表現は抱えた式の木を展開して含み、DAG を木に展開した大きさは
      作業量の予算の外では抑えられない（予算の owner は直列化の作業量）
    * 表現が組み込みの型そのもの以外（record・enum・scalar の subclass など、描いた後で owner が
      その型の規則で読む葉）を含むもの（`freeze_legacy_tree` が拒む）
    * 表現が上限（`CAPTURE_MAX_BYTES`）を超えるもの。写す 1 回は作業量の予算の外なので、固定の
      上限の中でだけ作る（超えれば写さない。予算の owner の勘定には入らない。値の storage の読みも
      walker がこの上限へ数えるので、固定の読みの上限を超えても限界は記録されない）
    * 表現を作ると失敗するもの（生の ref から描く経路が同じ失敗を従来どおり出す）
    """

    if runtime_ref is None:
        return None
    memo = staging.runtime_ref_records
    hit = memo.get(id(runtime_ref))
    if hit is not None and hit[0] is runtime_ref:
        return hit[1]
    record = None
    carried: List[Any] = []
    _walk_semantic_carriers(runtime_ref, carried.append, carried.append)
    if not carried:
        try:
            # 表現の source の変換も walk の中で走るので、値の storage の読みは walker がこの予算へ
            # 数える（固定の読みの上限を超えた分も、限界を記録せずにこの予算の超過になる）
            legacy = RESULT_JSON_POLICY.materialize(
                runtime_ref_source(runtime_ref),
                budget=JsonBudget(CAPTURE_MAX_BYTES, detached=True),
            )
        except _CAPTURE_FAILURES:
            legacy = _NOT_CAPTURED
        if legacy is not _NOT_CAPTURED:
            record = freeze_legacy_tree(legacy)
    memo[id(runtime_ref)] = (runtime_ref, record)
    return record


#: 表現を作る 1 回が上げ得る失敗（生の ref から描く経路が同じものを従来どおり上げる）
_CAPTURE_FAILURES = (TypeError, ValueError, RecursionError, JsonValueRejected, JsonBudgetExhausted)
_NOT_CAPTURED = object()


def _immutable_leaf(value: Any) -> bool:
    """表現にそのまま置かれる葉が、組み込みの不変な型 **そのもの** か。

    subclass・enum・任意の object は通さない: 描いた後で JSON の writer・snapshot codec・比較が
    その型の method（外の状態を読み得る code）へ dispatch し得るので、不変と証明できない。
    """

    kind = type(value)
    return value is None or kind is bool or kind is int or kind is float or kind is str or kind is bytes


def _immutable_plain(value: Any) -> bool:
    """意味値を含まない、不変な葉とその組み込みの `tuple` だけの値か（`value` の既定の形）。"""

    pending = [value]
    while pending:
        item = pending.pop()
        if _immutable_leaf(item):
            continue
        if type(item) is not tuple:
            return False
        pending.extend(tuple.__iter__(item))
    return True


def _scalar_rule(node: Any, value: Any, staging: _LifecycleStaging, dependencies: List[Any]) -> bool:
    return _immutable_leaf(value)


def _kind_rule(node: Any, value: Any, staging: _LifecycleStaging, dependencies: List[Any]) -> bool:
    # 表現は member の名前（`_name_`）を置く。member とその名前は class の定義
    return type(value) is ExpressionType


def _value_rule(node: Any, value: Any, staging: _LifecycleStaging, dependencies: List[Any]) -> bool:
    if node.__dict__.get("expr_type") is not ExpressionType.PHI:
        return _immutable_plain(value)
    # PHI: 凍結で `PhiBranch` の tuple に畳んである。branch の条件と値が closed であること
    if type(value) is not tuple:
        return False
    for branch in value:
        if type(branch) is not PhiBranch:
            return False
        condition, branch_value = branch
        if condition is not None:
            if type(condition) is not Condition:
                return False
            dependencies.append(condition)
        if type(branch_value) is not Expression:
            return False
        dependencies.append(branch_value)
    return True


def _operands_rule(node: Any, value: Any, staging: _LifecycleStaging, dependencies: List[Any]) -> bool:
    if type(value) is not tuple:
        return False
    for child in value:
        if type(child) is not Expression:
            return False
        dependencies.append(child)
    return True


def _expression_rule(node: Any, value: Any, staging: _LifecycleStaging, dependencies: List[Any]) -> bool:
    if type(value) is not Expression:
        return False
    dependencies.append(value)
    return True


def _storage_rule(node: Any, value: Any, staging: _LifecycleStaging, dependencies: List[Any]) -> bool:
    if value is None:
        return True
    payload = staging.derived_fields(node).get("_storage_payload")
    # 写しの値も葉と同じ規則（写しは `StorageInfo` の値をそのまま持つ）
    return payload is not None and all(_immutable_leaf(item) for item in payload.values)


def _runtime_ref_rule(node: Any, value: Any, staging: _LifecycleStaging, dependencies: List[Any]) -> bool:
    return value is None or staging.derived_fields(node).get("_runtime_ref_payload") is not None


SERIALIZATION_CLOSURE_RULES: Mapping[SerializationInput, Callable[..., bool]] = MappingProxyType({
    SerializationInput.SCALAR: _scalar_rule,
    SerializationInput.KIND: _kind_rule,
    SerializationInput.VALUE: _value_rule,
    SerializationInput.OPERANDS: _operands_rule,
    SerializationInput.EXPRESSION: _expression_rule,
    SerializationInput.STORAGE: _storage_rule,
    SerializationInput.RUNTIME_REF: _runtime_ref_rule,
})

#: 型 → (field, 規則) の列。表（lifecycle）と規則（上）から組み立てるだけで、field を列挙しない。
#: 表と規則はどちらも module の読み込み時に決まる（凍結は node ごとに通るので、ここで 1 度引く）。
_CLOSURE_PLANS: Mapping[type, Tuple[Tuple[str, Callable[..., bool]], ...]] = MappingProxyType({
    Expression: tuple((name, SERIALIZATION_CLOSURE_RULES[kind]) for name, kind in EXPRESSION_SERIALIZATION_INPUTS.items()),
    Condition: tuple((name, SERIALIZATION_CLOSURE_RULES[kind]) for name, kind in CONDITION_SERIALIZATION_INPUTS.items()),
})


def _serialization_dependencies(value: Any, staging: _LifecycleStaging) -> Optional[List[Any]]:
    """`value` の LEGACY 表現が読む field がすべて局所的に不変なら、closed であるべき依存の列。

    どれか 1 つでも不変でなければ `None`。読む field は lifecycle の表から取る（ここで列挙しない）。
    """

    # 表と規則が述べているのは `Expression` / `Condition` の表現（その型の method）だけ。subclass は
    # 表現を作る method を上書きし得るので closed にしない
    plan = _CLOSURE_PLANS.get(type(value))
    if plan is None:
        return None
    fields = value.__dict__
    dependencies: List[Any] = []
    for name, rule in plan:
        if name not in fields:
            # instance に無い field は class の値（共有の状態）を読むことになる
            return None
        if not rule(value, fields[name], staging, dependencies):
            return None
    return dependencies


def _committed_closed(value: Any) -> bool:
    """前の操作で確定した値の bit（`serialization_closed` と同じ答え）。

    ここで出会う値は `Expression` / `Condition` の型そのもの（依存に積むのはそれだけ）なので、
    状態の owner の module として instance の `__dict__` を直接読む（凍結は node ごとに通るので
    読み口の汎用の型の確かめを繰り返さない）。
    """

    fields = value.__dict__
    return fields.get("_frozen") is True and fields.get("_serialization_closed") is True


def _verdict_from_known_dependencies(
    value: Any, staging: _LifecycleStaging, verdicts: Dict[int, Optional[bool]],
) -> Optional[bool]:
    """依存の答えがすべて出ているなら `value` の答え、出ていない依存があれば `None`。"""

    dependencies = _serialization_dependencies(value, staging)
    if dependencies is None:
        return False
    staged = staging.derived
    for dependency in dependencies:
        known = verdicts.get(id(dependency))
        if known is None:
            if id(dependency) in staged:
                return None
            known = verdicts[id(dependency)] = _committed_closed(dependency)
        if known is not True:
            return False
    return True


def _derive_serialization_closure(staging: _LifecycleStaging) -> None:
    """この操作で積んだ式・条件の `_serialization_closed` を、子から上へ 1 回だけ畳む。

    値は、表現が読む field が局所的に不変で、依存（子・PHI の条件と値・runtime ref が抱える
    式と条件）がすべて closed のときだけ closed。依存が前の操作で確定済みなら、その bit を
    読む（入り直さない）。依存の閉路（runtime ref が祖先を指す back-reference）は closed に
    しない: 表現が経路に依存し、不変とは言えない。

    明示 stack（graph が深くても再帰上限に当たらない。module の他の走査と同じ形）。
    """

    verdicts: Dict[int, Optional[bool]] = {}
    pending_inputs: Dict[int, Optional[List[Any]]] = {}
    staged = staging.derived
    for root in (*staging.expressions, *staging.conditions):
        if id(root) in verdicts:
            continue
        # 速い経路: graph の子は post-order で先に積まれているので、たいていの値は依存の答えが
        # もう出ている（前の操作で確定済みか、この操作で先に決めた）。出ていない依存（runtime ref
        # が抱える式など、後で積まれる値）があるときだけ、下の走査で畳む
        verdict = _verdict_from_known_dependencies(root, staging, verdicts)
        if verdict is not None:
            verdicts[id(root)] = verdict
            continue
        stack: List[Tuple[Any, bool]] = [(root, False)]
        while stack:
            value, leaving = stack.pop()
            key = id(value)
            if leaving:
                dependencies = pending_inputs.pop(key)
                verdicts[key] = dependencies is not None and all(
                    verdicts.get(id(dependency)) is True for dependency in dependencies
                )
                continue
            if key in verdicts:
                # 確定済み、または今の経路の上に在る（閉路: その依存は True にならない）
                continue
            if key not in staged:
                # この操作で積んでいない値: 前の操作で確定した bit を読む（未検証なら closed でない）
                verdicts[key] = _committed_closed(value)
                continue
            verdicts[key] = None
            dependencies = _serialization_dependencies(value, staging)
            pending_inputs[key] = dependencies
            stack.append((value, True))
            for dependency in dependencies or ():
                if id(dependency) not in verdicts:
                    stack.append((dependency, False))
    for node in staging.expressions:
        staged[id(node)]["_serialization_closed"] = verdicts[id(node)] is True
    for condition in staging.conditions:
        staged[id(condition)]["_serialization_closed"] = verdicts[id(condition)] is True
