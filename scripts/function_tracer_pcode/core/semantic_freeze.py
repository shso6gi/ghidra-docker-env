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
"""

from __future__ import annotations

import dataclasses
import enum
from typing import Any, Dict, List, Optional, Tuple

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
    coerce_phi_branches,
)
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

    __slots__ = ("entered", "derived", "expressions", "conditions")

    def __init__(self) -> None:
        self.entered: Dict[int, bool] = {}
        #: `id(expression)` → 確定させる派生値（commit まで公開状態へ書かない）
        self.derived: Dict[int, Dict[str, Any]] = {}
        #: commit 順（子が先）
        self.expressions: List[Expression] = []
        self.conditions: List[Any] = []

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
        mark_validated(condition.__dict__)


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

    値をどう扱うかは `_carrier_rule` が **優先順位つきの 1 つの表** で決める（上から最初に
    当てはまる規則）:

    1. 式 / 条件 → `on_expression` / `on_condition` を適用して、そこで止まる（その先は操作側が
       graph を辿る）。意味値は宣言に依らず必ず意味値として扱う
    2. 外の runtime object の代わりをすると宣言した型（`__semantic_opaque__`。記録再生の proxy・
       test の Ghidra の代わり）→ 葉。**値を開く規則（3〜6）より先**に判定する: dataclass でも
       容器の subclass でも、宣言した型の中は辿らない（本物の Ghidra object と同じ）
    3. tuple / list / set / frozenset → 要素へ入る
    4. dict → **key と value の両方へ入る**。式を鍵にした cache が実在する
       （`analysis/condition/bitvector.py` の `Dict[Expression, ...]`）ので、
       「到達できる意味値をすべて」と言う以上 key を外す理由が無い
    5. dataclass / NamedTuple → field へ入る
    6. **この package で定義された** その他の object → `__dict__` の値へ入る。新しい carrier 型が
       dataclass でなくても取りこぼさないため
    7. それ以外（Ghidra object・mock・標準ライブラリ）→ 葉。**属性を探らない**: 記録再生中の
       proxy に観測を作ってしまうため

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
        rule = _carrier_rule(value)
        if rule is CarrierRule.EXPRESSION:
            on_expression(value)
        elif rule is CarrierRule.CONDITION:
            on_condition(value)
        elif rule is CarrierRule.SEQUENCE:
            stack.extend(value)
        elif rule is CarrierRule.MAPPING:
            stack.extend(value.keys())
            stack.extend(value.values())
        elif rule is CarrierRule.FIELDS:
            stack.extend(getattr(value, field.name, None) for field in dataclasses.fields(value))
        elif rule is CarrierRule.OWNED_STATE:
            owned_state = getattr(value, "__dict__", None)
            if isinstance(owned_state, dict):
                stack.extend(owned_state.values())
    return container


class CarrierRule(enum.Enum):
    """到達走査が値をどう扱うか（`_carrier_rule` の答え。表の順が優先順位）。"""

    EXPRESSION = "expression"
    CONDITION = "condition"
    DECLARED_OPAQUE = "declared_opaque"
    SEQUENCE = "sequence"
    MAPPING = "mapping"
    FIELDS = "fields"
    OWNED_STATE = "owned_state"
    LEAF = "leaf"


def _carrier_rule(value: Any) -> CarrierRule:
    """`value` に当てはまる最初の規則（`_walk_semantic_carriers` の表。型は `isinstance` と class の
    辞書だけで見る: `hasattr` で属性を探ると、記録再生中の proxy に観測が走る）。"""

    if isinstance(value, Expression):
        return CarrierRule.EXPRESSION
    if isinstance(value, Condition):
        return CarrierRule.CONDITION
    kind = type(value)
    if declares_semantic_opaque(kind):
        return CarrierRule.DECLARED_OPAQUE
    if isinstance(value, (tuple, list, set, frozenset)):
        return CarrierRule.SEQUENCE
    if isinstance(value, dict):
        return CarrierRule.MAPPING
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        return CarrierRule.FIELDS
    if (kind.__module__ or "").startswith(_PACKAGE_PREFIX):
        return CarrierRule.OWNED_STATE
    return CarrierRule.LEAF


def declares_semantic_opaque(kind: type) -> bool:
    """型 `kind` が外の runtime object の代わりだと宣言しているか（`SEMANTIC_OPAQUE_DECLARATION`）。

    宣言は class の辞書（MRO）だけから読む（instance の `__getattr__` を呼ばない）。subclass は
    基底の宣言を継ぐ。宣言した型の中は走査しない: その状態（記録全体・観測の履歴…）は意味の
    入れ物ではなく、辿ると費用が記録の大きさに比例し、本物の object では起きない仕事になる。
    """

    return any(base.__dict__.get(SEMANTIC_OPAQUE_DECLARATION) is True for base in kind.__mro__)


#: 外の runtime object の代わりをする型が宣言する class 属性（`declares_semantic_opaque`）
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
