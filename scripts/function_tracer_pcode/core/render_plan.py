# -*- coding: utf-8 -*-
"""DAG 描画の **走査と共有計画**（renderer から描画規則を分けた層）。

renderer（人向け / SMT）が持つのは「この node をどう書くか」だけで、

* 同じ node を 2 度展開しない
* 深い式で Python の再帰に頼らない
* どの部分式に名前を付けて 1 回だけ書くか
* 名前の付け方と依存順

はここが持つ。node 種別が増えても触るのは renderer 側の本体だけで、この層は
変わらない（逆に、共有の条件を変えたいときに renderer 本体を読む必要もない）。

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

## 2 段で計画する理由

「どの instance に名前を付けるか」は参照回数が分かってからでないと決まらず、
参照回数は node 本体を走らせてみないと分からない。一方、本体を実 text で
走らせると共有部分式がそのまま展開されて指数になる。そこで

1. **計画 pass** — 子の text の代わりに短い *観測 token* を返して本体を走らせ、
   辺（どの instance を何回参照したか）と local な大きさを得る。
2. **出力 pass** — 名前を決めた後、同じ本体を実 text（名前 or 展開）で走らせる。

観測 token は好きな文字列でよいわけではない。下流が子の描画 text を
**文字列として見る**箇所があるので（`TextObservation`）、token は同じ観測結果に
なる代表値でなければ、計画 pass と出力 pass で辿る分岐が食い違う。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.errors import AnalysisFailureError
from scripts.function_tracer_pcode.core.render_output import RenderCounters


class RenderGraphCycleError(AnalysisFailureError):
    """描画の走査が同じ node へ戻った（**停止のための検出**）。

    「閉路を受け入れない」という判定そのものは走査 owner
    （`core/semantic_snapshot.traverse_semantic_graph`）が持つ。ここが独自に
    `ExpressionCycleError` を投げると閉路判定の実装が 2 つになり、片方だけが
    直る（辺の判定順を 1 行間違えるだけで back-edge を取り逃す）。driver は
    「これ以上進めない」とだけ言い、種別の判定は renderer が owner へ回す。

    `ValueError` / `TypeError` 派生にしない（描画経路の回復 handler に吸われる）。
    """



class _NeedChild(BaseException):
    """まだ解決していない子が要る、という driver 内部の合図。

    `BaseException` 派生なのは意図的。描画経路には `except Exception` の回復
    handler が実在し（`render_smt/loop_lowering.py`、`widths.py`）、そこへ吸われると
    driver が子を積めないまま同じ本体を回し続ける。合図は握り潰されない型で運ぶ。
    """


#: 観測クラスの既定名（どの観測にも当たらない text）
TEXT_OBSERVATION_OTHER = "other"

#: 見積りの飽和点。これ以上は数えない（巨大整数と無駄な走査を作らない）
SATURATION = 1 << 40


@dataclass(frozen=True)
class TextObservation:
    """下流が子の描画 text を文字列として見る観測の 1 クラス。

    計画 pass は子の代わりに `token(index)` を返すので、本体の分岐は実 text の
    ときと一致する。新しく「描画 text を見る」判定を足すときは、観測を 1 つ
    足して代表 token を決める（足さないと、計画と出力で辺が食い違う）。
    """

    name: str
    matches: Callable[[str], bool]
    #: instance 番号を受け取り、この観測になる代表 token を返す
    token: Callable[[int], str]
    #: 名前（参照）へ置き換えても観測結果が変わらないか。
    #: 変わるものは共有できない（共有すると下流の判定が静かに変わる）。
    shareable: bool = True
    #: text の観測が変わっても、node 自身を見た結果が同じなら共有してよい、と
    #: 言える場合の述語。下流が「text で判定 → 駄目なら node で判定」の順に
    #: なっている観測（float 理論の正規化がそれ）で、後段と同じ答えになる node
    #: だけを共有可能にするために使う。
    shareable_when: Optional[Callable[[Any], bool]] = None

    def allows_sharing(self, node: Any) -> bool:
        if not self.shareable:
            return False
        return self.shareable_when is None or bool(self.shareable_when(node))


@dataclass(frozen=True)
class SharingPolicy:
    """どの instance に名前を付けるか。

    2 つの理由で名前を付ける:

    * **共有** — 2 回以上参照される部分式（DAG を木に戻さないため）
    * **大きさ** — 1 つの instance へ展開し続けると中間文字列が深さに比例して
      伸び、連結費用が深さの 2 乗になる。一定量で切って名前にする

    小さい式は今までどおり展開する（`min_shared_chars` 未満）。共有だけを理由に
    葉へ名前を付けると、短い式の出力が読みにくくなるうえ、既存の観測可能な
    text が理由なく変わる。
    """

    #: これ未満の大きさの instance には名前を付けない
    min_shared_chars: int = 32
    #: 展開したままの大きさがこれを超えたら（参照が 1 回でも）名前を付ける
    inline_max_chars: int = 8192
    #: 共有を理由に名前を付ける最小の木 node 数
    min_shared_tree_nodes: int = 2
    #: 名前 1 個の文字数の見積り（大きさ計算用）
    reference_chars_estimate: int = 10

    def binds(self, *, references: int, inline_chars: int, tree_nodes: int) -> bool:
        if inline_chars < self.min_shared_chars:
            return False
        if references >= 2 and tree_nodes >= self.min_shared_tree_nodes:
            return True
        return inline_chars > self.inline_max_chars


@dataclass
class RenderInstance:
    """1 つの (意味 node, 描画文脈) の描画。"""

    index: int
    node: Any
    context: Any
    #: 本体が子を要求した順（同じ instance を 2 回参照したら 2 回入る）
    child_indices: Tuple[int, ...] = ()
    #: 計画 pass の text（観測 token 入り。出力には使わない）
    planned_text: str = ""
    #: 計画 pass の text から観測したクラス名
    observation: str = TEXT_OBSERVATION_OTHER
    #: 子を除いた、この node 自身が書く文字数
    local_chars: int = 0
    #: 木として展開したときの node 数（飽和付き）
    tree_nodes: int = 1
    #: 展開したままの文字数の見積り（飽和付き）
    inline_chars: int = 0
    #: 他の instance から参照された回数
    references: int = 0
    #: 名前を付けるか
    bound: bool = False
    #: 出力 pass の text（名前を付けた instance ではその本体）
    text: str = ""


@dataclass
class RenderPlan:
    """計画 pass の結果。出力 pass はこれを読んで名前と展開を決める。"""

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

    node 本体は「子の text が要る」ところで `_NeedChild` を投げるので、driver は
    その子を積んでから同じ本体をもう一度走らせる。本体を書き換えずに反復化
    できるのが利点で、**最後に成功した実行だけ**が採用される（途中の実行の
    結果も辺も捨てる）ので、偽の子 text が出力へ混ざることはない。
    """

    def __init__(self, body, text_of, counters: RenderCounters, on_complete=None) -> None:
        self._body = body
        self._text_of = text_of
        self._counters = counters
        self._on_complete = on_complete
        self.instances: List[RenderInstance] = []
        self.post_order: List[int] = []
        self.index_by_key: Dict[Tuple[int, Any], int] = {}
        self._done: Dict[int, bool] = {}
        self._edges: Optional[List[int]] = None
        self._missing: Optional[Tuple[Any, Any]] = None

    def resolve(self, node: Any, context: Any) -> str:
        """node 本体が子の text を要求する口。"""

        key = (id(node), context)
        index = self.index_by_key.get(key)
        if index is None or index not in self._done or self.instances[index].node is not node:
            # 最後の条件は `id()` の使い回し避け。instance は node への強参照を
            # 持つので生きている間は起きないが、起きたときに別の式の text を
            # 黙って返さない。
            self._missing = (node, context)
            raise _NeedChild
        if self._edges is not None:
            self._edges.append(index)
        return self._text_of(self.instances[index])

    def run(self, root: Any, context: Any) -> int:
        stack: List[Tuple[Any, Any]] = [(root, context)]
        on_path: Dict[int, int] = {}
        _enter_path(on_path, root)
        root_index: Optional[int] = None
        while stack:
            node, ctx = stack[-1]
            key = (id(node), ctx)
            index = self.index_by_key.get(key)
            if index is not None and index in self._done:
                stack.pop()
                _leave_path(on_path, node)
                continue
            if index is None:
                index = len(self.instances)
                self.instances.append(RenderInstance(index=index, node=node, context=ctx))
                self.index_by_key[key] = index
            edges: List[int] = []
            self._edges = edges
            self._missing = None
            try:
                text = self._body(node, ctx, self.resolve)
            except _NeedChild:
                self._counters.node_body_executions += 1
                child_node, child_context = self._missing or (None, None)
                if id(child_node) in on_path:
                    raise RenderGraphCycleError(
                        "render traversal returned to a node already on the path"
                    )
                stack.append((child_node, child_context))
                _enter_path(on_path, child_node)
                continue
            finally:
                self._edges = None
            self._counters.node_body_executions += 1
            instance = self.instances[index]
            instance.child_indices = tuple(edges)
            instance.text = text
            self._done[index] = True
            self.post_order.append(index)
            if self._on_complete is not None:
                self._on_complete(instance)
            _leave_path(on_path, node)
            stack.pop()
            if not stack:
                root_index = index
        if root_index is None:
            root_index = self.index_by_key[(id(root), context)]
        return root_index


def _enter_path(on_path: Dict[int, int], node: Any) -> None:
    on_path[id(node)] = on_path.get(id(node), 0) + 1


def _leave_path(on_path: Dict[int, int], node: Any) -> None:
    node_id = id(node)
    remaining = on_path.get(node_id, 0) - 1
    if remaining > 0:
        on_path[node_id] = remaining
    else:
        on_path.pop(node_id, None)


def plan_render(
    root: Any,
    context: Any,
    *,
    body,
    observations: Sequence[TextObservation],
    policy: SharingPolicy,
    counters: RenderCounters,
) -> RenderPlan:
    """計画 pass: 辺・大きさ・観測クラスを集め、名前を付ける instance を決める。"""

    classes = {observation.name: observation for observation in observations}
    if TEXT_OBSERVATION_OTHER not in classes:
        raise ValueError("observations must include the default class")
    token_of: Dict[int, str] = {}

    def text_of(instance: RenderInstance) -> str:
        return token_of[instance.index]

    def on_complete(instance: RenderInstance) -> None:
        # 観測クラスは子が先に決まっている必要がある: 子の text をそのまま
        # 返す node（通し）では、親の観測は子の観測になる。
        instance.planned_text = instance.text
        instance.observation = _classify(instance.text, observations)
        token_of[instance.index] = classes[instance.observation].token(instance.index)

    driver = _Driver(body, text_of, counters, on_complete=on_complete)
    root_index = driver.run(root, context)

    instances = driver.instances
    post_order = tuple(driver.post_order)

    for index in post_order:
        for child_index in instances[index].child_indices:
            instances[child_index].references += 1

    shared_references = 0
    for index in post_order:
        instance = instances[index]
        child_token_chars = sum(len(token_of[child]) for child in instance.child_indices)
        instance.local_chars = max(0, len(instance.planned_text) - child_token_chars)
        tree_nodes = 1
        inline_chars = instance.local_chars
        for child_index in instance.child_indices:
            child = instances[child_index]
            tree_nodes = min(SATURATION, tree_nodes + child.tree_nodes)
            if child.bound:
                inline_chars += policy.reference_chars_estimate
                shared_references += 1
            else:
                inline_chars = min(SATURATION, inline_chars + child.inline_chars)
        instance.tree_nodes = tree_nodes
        instance.inline_chars = min(SATURATION, inline_chars)
        shareable = classes[instance.observation].allows_sharing(instance.node)
        if not shareable:
            counters.unshareable_observations += 1
        instance.bound = (
            index != root_index
            and shareable
            and policy.binds(
                references=instance.references,
                inline_chars=instance.inline_chars,
                tree_nodes=instance.tree_nodes,
            )
        )
        # 計画 pass の text は捨てる。出力 pass が実 text を作り直す。
        instance.text = ""

    bound_order = tuple(index for index in post_order if instances[index].bound)
    counters.distinct_rendered_nodes += len(instances)
    counters.shared_bindings += len(bound_order)
    counters.shared_references += shared_references
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


def emit_render(
    plan: RenderPlan,
    root: Any,
    context: Any,
    *,
    body,
    names: Dict[int, str],
    counters: RenderCounters,
) -> None:
    """出力 pass: 名前を決めた後の実 text を各 instance に入れる。

    名前を付けた instance の `text` は **その本体**（参照ではない）。参照は
    `names` の側。計画に無い子を本体が要求しても driver が普通に描くので、
    観測の取りこぼしがあっても壊れず、共有が 1 つ減るだけで済む。
    """

    def text_of(instance: RenderInstance) -> str:
        name = names.get(instance.index)
        return instance.text if name is None else name

    for instance in plan.instances:
        instance.child_indices = ()
        instance.text = ""
    driver = _Driver(body, text_of, counters)
    driver.instances = plan.instances
    driver.index_by_key = {
        (id(instance.node), instance.context): instance.index
        for instance in plan.instances
    }
    plan.root_index = driver.run(root, context)
    plan.post_order = tuple(driver.post_order)
    for instance in plan.instances:
        counters.observe_buffered(len(instance.text))


def _classify(text: str, observations: Sequence[TextObservation]) -> str:
    for observation in observations:
        if observation.name == TEXT_OBSERVATION_OTHER:
            continue
        if observation.matches(text):
            return observation.name
    return TEXT_OBSERVATION_OTHER


class BindingNamespace:
    """生成する名前の owner。予約済み symbol と衝突しない名前を決める。

    予約済み symbol は **描画 text から実際に拾う**。宣言を作る側（unknown /
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


def collect_reserved_symbols(texts, *, pattern) -> frozenset:
    """描画 text に現れる symbol（引用符付きも中身で）を集める。"""

    reserved: set = set()
    for text in texts:
        if not text:
            continue
        for match in pattern.finditer(text):
            quoted = match.groupdict().get("quoted")
            reserved.add(quoted if quoted is not None else match.group("bare"))
    return frozenset(reserved)
