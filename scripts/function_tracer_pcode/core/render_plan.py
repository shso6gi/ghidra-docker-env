# -*- coding: utf-8 -*-
"""DAG 描画の **走査・共有計画・書き出し**（renderer から描画規則を分けた層）。

renderer（人向け / SMT）が持つのは「この node をどう書くか」だけで、

* 同じ node を 2 度展開しない
* 深い式で Python の再帰に頼らない
* どの部分式に名前を付けて 1 回だけ書くか
* 名前の付け方と依存順
* 上限を超える文字列を **作らない**

はここが持つ。node 種別が増えても触るのは renderer 側の本体だけで、この層は
変わらない（逆に、共有の条件や上限の効かせ方を変えたいときに renderer 本体を
読む必要もない）。

## 断片（fragment）— 1 node 分しか作らない

node 本体は子の描画結果として **参照 1 個**（`RenderedTerm`）を受け取る。だから
本体が返す文字列（= その node の *fragment*）は常に「自分が書く分 + 子の参照」で、
部分木の大きさに比例しない。木への展開は最後の書き出しで、`CountingWriter` へ
**流しながら**行う。

上限は 3 つの場所で効く。どれも **node 種別を知らない**ので、新しい種別を足す
人が忘れる余地が無い:

1. **子を解決するたび**（`resolve`）。幅の広い node（引数の多い CALL、branch の
   多い PHI）の大きさは子の参照の数で決まるので、`" ".join(...)` が 10,000 個を
   並べ終わる前に止まる。
2. **fragment が出来たとき**（`_complete`）。子を持たずに自分だけで大きい node
   はここで止まる。
3. **書き出し**（`CountingWriter`）。木への展開は流しながら行うので、上限に
   達した時点でそれ以上は作らない。

1 と 2 が見ているのは **renderer が抱える材料の量**（`retained_fragment_bytes`）で、
出力量の下界ではない — 本体は要求した子を捨てることがある（定数条件を `true` に
畳む枝など）ので、材料 > 上限でも出力が上限を超えるとは限らない。それでも
止めるのは、出力の何倍もの材料を抱え込むこと自体が防ぎたい費用だから。出力量
そのものの上限は 3 が持つ。

## 描画 instance という単位

同じ意味の node でも、描画結果は **文脈** で変わる（幅合わせ、符号拡張、
address 文脈、float mode、symbol の対応表）。だから共有の単位は node ではなく

```text
RenderInstanceIdentity = 意味 node の identity + 描画に効く文脈
```

にする。node identity だけで共有すると、別の幅で描いた式を同じ名前に束ねて
しまい、SMT の意味が変わる。この identity は **renderer 内部に閉じた局所
identity** で、`StructuralIdentity` / `SolverQueryIdentity` / `RewriteIdentity`
とは別物。混ぜてはいけない（片方の都合で他方の一致条件が動く）。

## 子の描画結果は「文字列」ではなく「型のある項」

下流が子の描画 **文字列**を見て分岐すると（float 理論の正規化、PHI の恒真条件の
畳み込み）、参照へ置き換えた瞬間に判定が変わる。そこで子は `RenderedTerm` として
渡し、判定に要る性質は **型付きの property** で持つ。性質は renderer が与える
分類器が fragment から 1 回だけ決め、子から親へは「先頭が子ならその性質を継ぐ」
という規則で正確に伝わる（近似ではなく等値）。文字列を見る分岐は renderer に
1 つも残らない（`tests/unit/test_architecture_boundaries.py` が 0 で固定）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterator, List, Optional, Tuple

from scripts.function_tracer_pcode.core.errors import AnalysisFailureError
from scripts.function_tracer_pcode.core.render_output import (
    CountingWriter,
    RenderCounters,
    RenderOutputLimitExceeded,
    utf8_length,
)


class RenderGraphCycleError(AnalysisFailureError):
    """描画の走査が同じ node へ戻った（**停止のための検出**）。

    「閉路を受け入れない」という判定そのものは走査 owner
    （`core/semantic_snapshot.traverse_semantic_graph`）が持つ。ここが独自に
    `ExpressionCycleError` を投げると閉路判定の実装が 2 つになり、片方だけが
    直る（辺の判定順を 1 行間違えるだけで back-edge を取り逃す）。driver は
    「これ以上進めない」とだけ言い、種別の判定は renderer が owner へ回す。

    `ValueError` / `TypeError` 派生にしない（描画経路の回復 handler に吸われる）。
    """


class RenderPlanInvariantError(AnalysisFailureError):
    """計画と書き出しの前提が崩れた（内部不整合、**fail-closed**）。

    名前を付けた instance の本体が空、fragment が知らない参照を含む、参照が
    後ろの instance を指している、といった状態で書き出しを続けると、空の定義や
    未定義の symbol を含む論理式が solver へ届く。「共有が減るだけ」では済まない。
    """


class RenderedTermContractError(AnalysisFailureError):
    """型付きの性質を要求する場所へ、性質を持たない項が届いた（fail-closed）。

    「性質が無ければ文字列を見る」という後退をさせない。後退させると、参照へ
    置き換えた瞬間に下流の判定が変わる経路が復活する。
    """


#: 描画を打ち切る / 内部不整合を告げる型（**この tuple が唯一の owner**）。
#:
#: 描画経路には `except Exception` の回復 handler が実在する。そこへこれらが
#: 吸われると「上限で止めた」「閉路だった」が「その枝は描けなかった」に化け、
#: 予算も閉路検出も効かないまま解析が続く。回復 handler の手前でこの tuple を
#: 再送出すること。`tests/unit/test_architecture_boundaries.py` が、描画 module
#: の広い `except` すべてについてそれを固定している。
RENDER_FAILURES = (
    RenderGraphCycleError,
    RenderPlanInvariantError,
    RenderedTermContractError,
    RenderOutputLimitExceeded,
)


class _NeedChild(BaseException):
    """まだ解決していない子が要る、という driver 内部の合図。

    `BaseException` 派生なのは意図的。描画経路には `except Exception` の回復
    handler が実在し（`render_smt/loop_lowering.py`、`widths.py`）、そこへ吸われると
    driver が子を積めないまま同じ本体を回し続ける。合図は握り潰されない型で運ぶ。
    """


#: fragment の中で子を指す印。実テキストに現れ得ない制御文字で挟む。
PLACEHOLDER_MARK = "\x00"

#: 見積りの飽和点。これ以上は数えない（巨大整数と無駄な走査を作らない）
SATURATION = 1 << 40

#: 同じ node の本体をこの回数だけ回しても子が尽きないなら、幅の広い node と
#: 見なして「要求を一度に集める」実行へ切り替える。狭い node（ほとんど）は
#: 切り替えに入らないので、投機的な実行の費用を払わない。
#:
#: 描画 driver と node 属性の評価（`core/render_smt/attributes.py`）は同じ形の
#: 反復をするので、**切り替えの規則はここが唯一の owner**。片方だけ直ると、
#: 直っていない側が幅の 2 乗のまま残る（実際そうなっていた）。
DISCOVERY_AFTER_RETRIES = 4

#: 要求収集の実行が、まだ描いていない子の代わりに返す値。placeholder とは別物
#: （出力には決して入らない）。
#:
#: **真と偽の 2 通りで走らせる**。本体には `all(...)` / `any(...)` のように子の
#: 値で打ち切るものがあり、片方だけだと最初の 1 個しか集まらず、幅の 2 乗のまま
#: 残る（実際そうなっていた）。2 回とも O(幅) なので、集め損ねるより安い。
_UNRESOLVED_CHILD_TEXTS = ("?", "")

#: 要求収集の実行だけで無視してよい失敗。偽の子で走らせているので、本番の実行
#: では起きない失敗が出ることがある。**予算・閉路・契約違反（`AnalysisFailureError`
#: 派生）はここに入れない** — それらは本番でも起きる本物の停止理由。
DISCOVERY_IGNORED_FAILURES = (
    ArithmeticError,
    AttributeError,
    LookupError,
    TypeError,
    ValueError,
)


def child_placeholder(index: int) -> str:
    return f"{PLACEHOLDER_MARK}{index}{PLACEHOLDER_MARK}"


class RenderedTerm(str):
    """子の描画結果。文字列としては **参照 1 個**、性質は型で持つ。

    `str` の subclass なので、node 本体の f-string や `join` はそのまま動く。
    本体が見てよいのは `properties` だけで、文字そのものを見てはいけない
    （見ると、参照が名前になった / 展開されたで判定が変わる）。
    """

    __slots__ = ("properties",)

    def __new__(cls, text: str, properties: Any = None) -> "RenderedTerm":
        term = super().__new__(cls, text)
        term.properties = properties
        return term


def term_properties(term: Any) -> Any:
    """項の型付き性質。持たない項が来たら fail-closed。"""

    properties = getattr(term, "properties", None)
    if properties is None:
        raise RenderedTermContractError(
            "a rendered child term reached a typed observation without properties; "
            "render children through the driver so their properties travel with them"
        )
    return properties


@dataclass(frozen=True)
class SharingPolicy:
    """どの instance に名前を付けるか。

    2 つの理由で名前を付ける:

    * **共有** — 2 回以上参照される部分式（DAG を木に戻さないため）
    * **大きさ** — 展開したままだと書き出しが大きくなる部分式を 1 回にまとめる

    小さい式は今までどおり展開する（`min_shared_bytes` 未満）。共有だけを理由に
    葉へ名前を付けると、短い式の出力が読みにくくなるうえ、既存の観測可能な
    text が理由なく変わる。
    """

    #: これ未満の大きさの instance には名前を付けない（byte）
    min_shared_bytes: int = 32
    #: 展開したままの大きさがこれを超えたら（参照が 1 回でも）名前を付ける（byte）
    inline_max_bytes: int = 8192
    #: 共有を理由に名前を付ける最小の木 node 数
    min_shared_tree_nodes: int = 2
    #: 名前 1 個の byte 数の見積り（大きさ計算用）
    reference_bytes_estimate: int = 10

    def binds(self, *, references: int, inline_bytes: int, tree_nodes: int) -> bool:
        if inline_bytes < self.min_shared_bytes:
            return False
        if references >= 2 and tree_nodes >= self.min_shared_tree_nodes:
            return True
        return inline_bytes > self.inline_max_bytes


#: 名前を付けない方針（`let` 無しの形を作る比較用）。
NO_SHARING_POLICY = SharingPolicy(
    min_shared_bytes=1 << 62,
    inline_max_bytes=1 << 62,
    min_shared_tree_nodes=1 << 62,
)


@dataclass
class RenderInstance:
    """1 つの (意味 node, 描画文脈) の描画。"""

    index: int
    node: Any
    context: Any
    #: この node が書く分 + 子の参照。部分木の大きさには比例しない
    fragment: str = ""
    #: 本体が子を **要求した** 順（要求しても捨てることがある: 定数条件を
    #: `true` / `false` へ畳む枝など）。診断用
    child_indices: Tuple[int, ...] = ()
    #: fragment に **実際に現れる** 子（出力に効くのはこちら）
    used_children: Tuple[int, ...] = ()
    #: renderer が決めた型付きの性質（FP 項か、恒真 / 恒偽か など）
    properties: Any = None
    #: 子の参照を除いた、この node 自身が書く byte 数
    local_bytes: int = 0
    #: 木として展開したときの node 数（飽和付き）
    tree_nodes: int = 1
    #: 展開したままの byte 数の見積り（飽和付き）
    inline_bytes: int = 0
    #: 他の instance から参照された回数
    references: int = 0
    #: 名前を付けるか
    bound: bool = False


@dataclass
class RenderPlan:
    """走査の結果。書き出しはこれを読んで名前と展開を決める。"""

    instances: List[RenderInstance] = field(default_factory=list)
    #: 子が必ず先に来る順（= 依存順）
    post_order: Tuple[int, ...] = ()
    root_index: int = 0
    #: 名前を付ける instance（依存順）
    bound_order: Tuple[int, ...] = ()

    @property
    def distinct_instances(self) -> int:
        return len(self.instances)


class _Driver:
    """反復 post-order の走査。Python の再帰を使わない。

    node 本体は「子が要る」ところで `_NeedChild` を投げるので、driver はその子を
    積んでから同じ本体をもう一度走らせる。本体を書き換えずに反復化できるのが
    利点で、**最後に成功した実行だけ**が採用される。

    子が多い node（引数の多い CALL、branch の多い PHI）では「1 個ずつ積んで
    やり直す」が幅の 2 乗になる。そこで同じ node を数回回しても終わらなければ、
    **要求を一度に集める実行**へ切り替える: 未解決の子には偽の値を返して本体を
    最後まで走らせ、要求された子をまとめて積む。その実行の結果は捨てる
    （採用されるのは本物の値で走った実行だけ）ので、偽の値が出力へ混ざることは
    ない。収集が取りこぼしても、いつもの 1 個ずつの経路が続きを拾う。

    切り替えの判断は **回した回数** だけで、node の種別を知らない。新しい種別を
    足す人がここへ手を入れる必要は無い。
    """

    def __init__(self, body, classify, counters: RenderCounters, limit_bytes) -> None:
        self._body = body
        self._classify = classify
        self._counters = counters
        self._limit = limit_bytes
        self.instances: List[RenderInstance] = []
        self.post_order: List[int] = []
        self.index_by_key: Dict[Tuple[int, Any], int] = {}
        self._done: Dict[int, bool] = {}
        self._terms: Dict[int, RenderedTerm] = {}
        self._edges: Optional[List[int]] = None
        self._missing: Optional[Tuple[Any, Any]] = None
        self.retained_bytes = 0
        #: 組み立て中の node が今までに受け取った子の参照の byte 数
        self._pending_bytes = 0

    def resolve(self, node: Any, context: Any) -> RenderedTerm:
        """node 本体が子を要求する口。返るのは **参照 1 個 + 型付きの性質**。"""

        # 解決できた分だけを数えると、幅の広い node を 1 個ずつ解いて回った
        # 費用が見えなくなる。要求は要求として数える。
        self._counters.child_requests += 1
        key = (id(node), context)
        index = self.index_by_key.get(key)
        if index is None or index not in self._done or self.instances[index].node is not node:
            # 最後の条件は `id()` の使い回し避け。instance は node への強参照を
            # 持つので生きている間は起きないが、起きたときに別の式の結果を
            # 黙って返さない。
            self._missing = (node, context)
            raise _NeedChild
        term = self._terms[index]
        if self._edges is not None:
            self._edges.append(index)
            # 幅の広い node はここで止める。fragment が完成してから測ると、
            # 10,000 引数の `join` はもう出来上がっている。
            self._pending_bytes += len(term)
            self._check_material(self._pending_bytes, "render.materialize")
        return term

    def run(self, root: Any, context: Any) -> int:
        stack: List[Tuple[Any, Any]] = [(root, context)]
        # 経路は **描画 instance**（node + 文脈）で持つ。node だけで持つと、
        # 同じ node を 2 つの文脈で要求する本体（比較の被演算子と PHI の条件が
        # 同じ式、など）が、閉路でもないのに閉路と判定される。
        on_path: Dict[Tuple[int, Any], int] = {}
        attempts: Dict[int, int] = {}
        _enter_path(on_path, (id(root), context))
        while stack:
            node, ctx = stack[-1]
            key = (id(node), ctx)
            index = self.index_by_key.get(key)
            if index is not None and index in self._done:
                stack.pop()
                _leave_path(on_path, key)
                continue
            if index is None:
                index = len(self.instances)
                self.instances.append(RenderInstance(index=index, node=node, context=ctx))
                self.index_by_key[key] = index
            edges: List[int] = []
            self._edges = edges
            self._pending_bytes = 0
            self._missing = None
            try:
                fragment = self._body(node, ctx, self.resolve)
            except _NeedChild:
                self._counters.node_body_executions += 1
                attempts[index] = attempts.get(index, 0) + 1
                if self._missing is None:
                    # `_NeedChild` は `resolve` が要求を控えてから投げる合図で、
                    # 控えの無い合図は driver の不整合。何を積むか分からない
                    # まま進めない。
                    raise RenderPlanInvariantError(
                        "a child was requested without recording which one"
                    )
                pending = [self._missing]
                if attempts[index] >= DISCOVERY_AFTER_RETRIES:
                    pending = self._collect_requests(node, ctx) or pending
                for child_node, child_context in reversed(pending):
                    child_key = (id(child_node), child_context)
                    if child_key in on_path:
                        raise RenderGraphCycleError(
                            "render traversal returned to a node already on the path"
                        )
                    stack.append((child_node, child_context))
                    _enter_path(on_path, child_key)
                continue
            finally:
                self._edges = None
            self._counters.node_body_executions += 1
            self._complete(index, str(fragment), tuple(edges))
            _leave_path(on_path, key)
            stack.pop()
        return self.index_by_key[(id(root), context)]

    def _collect_requests(self, node: Any, context: Any):
        """本体を偽の子で一度走らせ、要求された未解決の子をまとめて返す。

        結果の text は使わない（採用されるのは本物の値で走った実行だけ）。偽の
        値で走らせているので本番では起きない失敗が出ることがあり、それは無視して
        いつもの 1 個ずつの経路へ戻す。予算・閉路・契約違反はここで握らない。
        """

        missing: List[Tuple[Any, Any]] = []
        seen: set = set()
        previous_edges, self._edges = self._edges, None
        try:
            for text in _UNRESOLVED_CHILD_TEXTS:
                unresolved = RenderedTerm(text, self._classify("", None, False))
                pending = [0]

                def collect(child: Any, child_context: Any, _term=unresolved, _pending=pending):
                    self._counters.child_requests += 1
                    key = (id(child), child_context)
                    index = self.index_by_key.get(key)
                    if (
                        index is not None
                        and index in self._done
                        and self.instances[index].node is child
                    ):
                        term = self._terms[index]
                    else:
                        if key not in seen:
                            seen.add(key)
                            missing.append((child, child_context))
                        term = _term
                    # 収集の実行も本体を最後まで走らせる = 幅の分だけ文字列を
                    # 組み立てる。ここを数えないと、上限より大きい fragment を
                    # 「捨てるから」という理由で作ってしまう。上限超過は収集の
                    # 失敗ではないので握らない。
                    _pending[0] += len(term)
                    self._check_material(_pending[0], "render.materialize")
                    return term

                self._counters.node_body_executions += 1
                try:
                    self._body(node, context, collect)
                except DISCOVERY_IGNORED_FAILURES:
                    pass
                except _NeedChild:  # pragma: no cover - collect never raises it
                    pass
        finally:
            self._edges = previous_edges
        return missing

    def _complete(self, index: int, fragment: str, child_indices: Tuple[int, ...]) -> None:
        instance = self.instances[index]
        instance.fragment = fragment
        instance.child_indices = child_indices
        head, exact = leading_child(fragment)
        instance.properties = self._classify(
            fragment,
            None if head is None else self.instances[head].properties,
            exact,
        )
        self._terms[index] = RenderedTerm(child_placeholder(index), instance.properties)
        self._done[index] = True
        self.post_order.append(index)

        length = utf8_length(fragment)
        self.retained_bytes += length
        if length > self._counters.max_fragment_bytes:
            self._counters.max_fragment_bytes = length
        self._check_material(0, "render.materialize")

    def _check_material(self, pending_bytes: int, site: str) -> None:
        """renderer が抱えている材料の量を上限と比べる。

        これは出力量ではなく **材料**（`retained_fragment_bytes`）。本体は要求
        した子を捨てることがあるので、材料が上限を超えても出力が超えるとは
        限らない。それでも止めるのは、出力の何倍もの材料を先に作ること自体が
        防ぎたい費用だから。出力量そのものの上限は書き出し口が持つ。
        """

        if self._limit is None:
            return
        total = self.retained_bytes + int(pending_bytes)
        if total > self._limit:
            raise RenderOutputLimitExceeded(
                limit_bytes=self._limit,
                requested_bytes=total,
                site=site,
            )


def leading_child(fragment: str) -> Tuple[Optional[int], bool]:
    """fragment の先頭が子の参照ならその index と「参照ちょうどか」を返す。

    展開後のテキストの先頭は、先頭が子ならその子の展開の先頭になる。だから
    接頭辞で決まる性質は子から継げばよく、テキスト全体が 1 つの literal かは
    「fragment が参照ちょうど」で決まる。近似ではなく等値の判定。
    """

    if not fragment.startswith(PLACEHOLDER_MARK):
        return None, False
    end = fragment.find(PLACEHOLDER_MARK, 1)
    if end < 0:
        return None, False
    try:
        index = int(fragment[1:end])
    except ValueError:
        return None, False
    return index, end == len(fragment) - 1


def _enter_path(on_path: Dict[Any, int], key: Any) -> None:
    on_path[key] = on_path.get(key, 0) + 1


def _leave_path(on_path: Dict[Any, int], key: Any) -> None:
    remaining = on_path.get(key, 0) - 1
    if remaining > 0:
        on_path[key] = remaining
    else:
        on_path.pop(key, None)


def build_render_plan(
    root: Any,
    context: Any,
    *,
    body,
    classify: Callable[[str, Any, bool], Any],
    policy: SharingPolicy,
    counters: RenderCounters,
    limit_bytes: Optional[int] = None,
) -> RenderPlan:
    """DAG を 1 回だけ辿り、fragment・参照回数・名前を付ける instance を決める。"""

    driver = _Driver(body, classify, counters, limit_bytes)
    root_index = driver.run(root, context)

    instances = driver.instances
    post_order = tuple(driver.post_order)

    # 参照回数は **fragment に実際に現れる**子で数える。要求されたが捨てられた
    # 子（定数条件を `true` へ畳む枝など）まで数えると、出力に 1 度も現れない
    # instance へ名前が付き、空の参照先を持つ `let` が残る。
    for instance in instances:
        instance.used_children = tuple(fragment_children(instance.fragment))
    for index in post_order:
        for child_index in instances[index].used_children:
            instances[child_index].references += 1

    shared_references = 0
    for index in post_order:
        instance = instances[index]
        placeholder_bytes = sum(
            len(child_placeholder(child)) for child in instance.used_children
        )
        instance.local_bytes = max(0, utf8_length(instance.fragment) - placeholder_bytes)
        tree_nodes = 1
        inline_bytes = instance.local_bytes
        for child_index in instance.used_children:
            child = instances[child_index]
            tree_nodes = min(SATURATION, tree_nodes + child.tree_nodes)
            if child.bound:
                inline_bytes += policy.reference_bytes_estimate
                shared_references += 1
            else:
                inline_bytes = min(SATURATION, inline_bytes + child.inline_bytes)
        instance.tree_nodes = tree_nodes
        instance.inline_bytes = min(SATURATION, inline_bytes)
        instance.bound = index != root_index and policy.binds(
            references=instance.references,
            inline_bytes=instance.inline_bytes,
            tree_nodes=instance.tree_nodes,
        )

    bound_order = tuple(index for index in post_order if instances[index].bound)
    counters.distinct_rendered_nodes += len(instances)
    counters.shared_bindings += len(bound_order)
    counters.shared_references += shared_references
    counters.retained_fragment_bytes = max(
        counters.retained_fragment_bytes, driver.retained_bytes
    )
    if instances:
        counters.tree_node_estimate = max(
            counters.tree_node_estimate, instances[root_index].tree_nodes
        )
    return RenderPlan(
        instances=instances,
        post_order=post_order,
        root_index=root_index,
        bound_order=bound_order,
    )


def check_plan_invariants(plan: RenderPlan, names: Dict[int, str]) -> None:
    """書き出す前に前提を確かめる（崩れていたら **落とす**）。

    * fragment に現れる参照が、走査中に要求した子の **部分集合**である
      （要求して捨てるのは正しい。要求していない子が現れるのは不整合）
    * 参照は自分より **先に完成した** instance だけを指す（入れ子の `let` の依存順）
    * 名前を付けた instance には本体があり、名前も付いていて、**実際に
      参照されている**（出力に現れない定義を残さない）

    `used_children` は fragment から導いた値なので、ここで文字列を走査し直さない
    （描画のたびに走るので、同じ走査を 2 回したくない）。導出そのものが壊れて
    いないことは test 側が fragment を読み直して確かめる。
    """

    known = len(plan.instances)
    # 番号は「最初に積まれた順」なので、依存順は完成順（post-order）で見る。
    rank = {index: position for position, index in enumerate(plan.post_order)}
    for instance in plan.instances:
        requested = set(instance.child_indices)
        for child in instance.used_children:
            if child < 0 or child >= known:
                raise RenderPlanInvariantError(
                    f"instance {instance.index} references unknown child {child}"
                )
            if rank.get(child, known) >= rank.get(instance.index, -1):
                raise RenderPlanInvariantError(
                    f"instance {instance.index} references {child}, "
                    "which did not finish first"
                )
            if child not in requested:
                raise RenderPlanInvariantError(
                    f"instance {instance.index} references child {child} it never requested"
                )
        if instance.bound and not instance.fragment:
            raise RenderPlanInvariantError(
                f"bound instance {instance.index} has an empty definition"
            )
        if instance.bound and instance.references <= 0:
            raise RenderPlanInvariantError(
                f"bound instance {instance.index} is never referenced"
            )
    for index in plan.bound_order:
        if index not in names:
            raise RenderPlanInvariantError(f"bound instance {index} has no name")


def fragment_children(fragment: str) -> Iterator[int]:
    position = 0
    while True:
        start = fragment.find(PLACEHOLDER_MARK, position)
        if start < 0:
            return
        end = fragment.find(PLACEHOLDER_MARK, start + 1)
        if end < 0:
            raise RenderPlanInvariantError("fragment has an unterminated child reference")
        yield int(fragment[start + 1 : end])
        position = end + 1


def write_expansion(
    writer: CountingWriter,
    plan: RenderPlan,
    index: int,
    names: Dict[int, str],
) -> None:
    """1 つの instance を書き出す。名前の付いた子は名前、他は展開。

    展開は明示 stack で **流しながら**行う。途中で 1 つの大きな文字列を組み立て
    ないので、上限に達した時点で `CountingWriter` が止め、それ以上は作らない。
    """

    stack: List[Tuple[str, int]] = [(plan.instances[index].fragment, 0)]
    while stack:
        fragment, position = stack.pop()
        while position < len(fragment):
            start = fragment.find(PLACEHOLDER_MARK, position)
            if start < 0:
                writer.write(fragment[position:])
                position = len(fragment)
                break
            if start > position:
                writer.write(fragment[position:start])
            end = fragment.find(PLACEHOLDER_MARK, start + 1)
            if end < 0:
                raise RenderPlanInvariantError("fragment has an unterminated child reference")
            child = int(fragment[start + 1 : end])
            position = end + 1
            name = names.get(child)
            if name is not None:
                writer.write(name)
                continue
            stack.append((fragment, position))
            stack.append((plan.instances[child].fragment, 0))
            break


class BindingNamespace:
    """生成する名前の owner。予約済み symbol と衝突しない名前を決める。

    予約済み symbol は **fragment から実際に拾う**。宣言を作る側（unknown /
    CALL / memory / global address / 対応表）を列挙して回ると、新しい symbol の
    出所が増えたときに漏れる。描かれた text に出てこない symbol は、名前を
    奪われても意味が変わらない。

    hash だけで「衝突しない」と決めない。衝突したら決定的に次の候補へ進む。
    """

    def __init__(self, reserved, *, prefix: str, template: str) -> None:
        self._reserved = frozenset(reserved)
        self._prefix = prefix
        self._template = template

    def allocate(self, count: int) -> Tuple[str, ...]:
        """`count` 個の名前を決定的に割り当てる（衝突したら prefix を進める）。"""

        count = int(count)
        if count <= 0:
            return ()
        salt = 0
        while True:
            prefix = self._prefix if salt == 0 else f"{self._prefix}{salt}"
            names = tuple(
                self._template.format(prefix=prefix, index=index) for index in range(count)
            )
            if not any(self.collides(name) for name in names):
                return names
            salt += 1

    def allocate_keyed(self, seeds, digest) -> Tuple[str, ...]:
        """種文字列から名前を決める（同じ形には同じ名前）。

        一意性の根拠は hash ではなくここ: 既に使った名前や予約済み symbol と
        ぶつかったら決定的に番号を足して次へ進む。
        """

        used: set = set()
        names: List[str] = []
        for seed in seeds:
            base = digest(seed)
            candidate = self._template.format(prefix=self._prefix, index=base)
            salt = 0
            while candidate in used or self.collides(candidate):
                salt += 1
                candidate = self._template.format(
                    prefix=self._prefix, index=f"{base}_{salt}"
                )
            used.add(candidate)
            names.append(candidate)
        return tuple(names)

    def collides(self, name: str) -> bool:
        return symbol_content(name) in self._reserved


def symbol_content(name: str) -> str:
    """引用符付き symbol `|x|` の中身。素の symbol はそのまま。"""

    if len(name) >= 2 and name.startswith("|") and name.endswith("|"):
        return name[1:-1]
    return name


def collect_reserved_symbols(plan: RenderPlan, *, pattern) -> frozenset:
    """fragment に現れる symbol（引用符付きも中身で）を集める。"""

    reserved: set = set()
    for instance in plan.instances:
        if not instance.fragment:
            continue
        for match in pattern.finditer(instance.fragment):
            quoted = match.groupdict().get("quoted")
            reserved.add(quoted if quoted is not None else match.group("bare"))
    return frozenset(reserved)
