# -*- coding: utf-8 -*-
"""DAG 描画の **走査・共有計画・書き出し**（renderer から描画規則を分けた層）。

renderer（人向け / SMT）が持つのは「この node をどう書くか」だけで、

* 同じ node を 2 度展開しない
* 深い式で Python の再帰に頼らない
* どの部分式に名前を付けて 1 回だけ書くか
* 名前の付け方と依存順

はここが持つ。node 種別が増えても触るのは renderer 側の本体だけで、この層は
変わらない（逆に、共有の条件を変えたいときに renderer 本体を読む必要もない）。
**出力予算はこの層の持ち物ではない**（下記）。

## 断片（fragment）— 1 node 分しか作らない

node 本体は子の描画結果として **参照 1 個**（`RenderedTerm`）を受け取る。だから
本体が返す文字列（= その node の *fragment*）は常に「自分が書く分 + 子の参照」で、
部分木の大きさに比例しない。木への展開は最後の書き出しで、`CountingWriter` へ
**流しながら**行う。

## 出力予算はこの層の持ち物ではない

役割は 3 つに分かれている:

```text
FragmentBuilder  : 幅方向の組み立てを O(n) にするだけ。予算を知らない。
RenderCounters   : 中間作業の観測（診断 / PR-22-D の既定値決定用）。判定に使わない。
CountingWriter   : 書き出した byte の **唯一の** 予算 enforcement point。
```

`render_bytes`（= 出力予算）が意味するのは **書き出した byte 数**だけ。木への
展開は流しながら行うので、予算に達したらそこで書き出しを止める（= 完成した出力
文字列を作らない）。C7 が保証するのはここまで。

この層が組み立てる fragment は **speculative**: 本体は要求した子を捨てることが
あるし、要求された instance が最終出力に一度も現れないこともある。だから

```text
捨てられる子の fragment > 出力予算   かつ   最終出力 <= 出力予算
```

が両立する。出力予算でここを裁くと **正しい描画を拒める**ので、裁かない。
中間作業に予算を付けるかどうかと、その値は PR-22-D の `BudgetPolicy` の担当で、
この層は観測値を渡すだけ（本番で使わない上限の仕組みは置かない — 置くと test
だけがそれを使って production に無い保証を主張できる）。

## 組み立ては線形に

`FragmentBuilder` は fragment を **前から 1 回で**組み立てる口。幅が子の数に
比例する node（引数の多い CALL、branch の多い PHI）を
`result = f"(ite … {result})"` のように後ろから積み直すと、文字列 copy が幅の
2 乗になる。これは renderer の書き方の問題（C2 / performance）で、予算とは別の話。

## 予定と経路は `ResolutionSchedule` が持つ

「次に何を片付けるか」（scheduled）と「今どこに居るか」（active な祖先の連鎖）は
別の状態で、**閉路判定が見るのは後者だけ**。1 つにまとめると、要求をまとめて
積んだ sibling どうしの依存が閉路に見える。描画 driver と node 属性の評価
（`render_smt/attributes.py`）は同じ予定表を使う — 写すと片方だけが直る。

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
#: 吸われると「予算で止めた」「閉路だった」が「その枝は描けなかった」に化け、
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


class ResolutionSchedule:
    """子が先に済む反復走査の **予定表**（走査 machinery の唯一の owner）。

    描画 driver と node 属性の評価は、形の同じ反復をする: 本体を走らせ、答えの
    無い子があればそれを先に片付けてから本体をやり直す。その「予定と経路」の
    管理をここ 1 箇所に置く。2 実装あると片方だけが直る。

    ## 4 つの状態を混ぜない

    * **scheduled** — 予定表に載っているが、本体はまだ 1 度も動いていない
    * **active** — 本体が動き始め、子を待って中断している = **祖先の連鎖**
    * **completed** — 答えが決まった（memo の持ち物。予定表は知らない）
    * それ以外 — まだ何も知らない

    **閉路判定が見るのは `active` だけ。** scheduled を混ぜると、要求をまとめて
    積んだ sibling どうしの依存が閉路に見える:

    ```text
    root
    ├─ A
    │  └─ x
    └─ x
    ```

    `root` の要求をまとめて積むと `A` と `x` が同時に scheduled になる。次に
    `A` の本体が `x` を要求するが、`x` は「まだ動いていない予定」であって
    `A` の祖先ではない。ここを `active` として数えると、閉路でない DAG が
    `RenderGraphCycleError` になる（実際そうなっていた）。

    ## 状態が動くのは 2 箇所だけ

    * `need()` — 本体が子を待った。呼び出し元が **active** になり、子が
      **scheduled** になる
    * `settle()` — 本体が答えを出した（または既に答えがあった）。**active** から
      外れて予定表から降りる

    `active` へ入るのは `need()` だけ、出るのは `settle()` だけ。予定表へ
    載せる操作は `active` を触らない — この分離が上の不変条件そのもの。
    """

    __slots__ = ("_key_of", "_stack", "_active", "_attempts")

    def __init__(self, root: Any, *, key_of: Callable[[Any], Any]) -> None:
        self._key_of = key_of
        self._stack: List[Tuple[Any, Any]] = [(key_of(root), root)]
        #: 本体が動き始めて子を待っている項目 = 祖先の連鎖。閉路判定はここだけを見る
        self._active: set = set()
        self._attempts: Dict[Any, int] = {}

    def __bool__(self) -> bool:
        return bool(self._stack)

    def current(self) -> Any:
        """今片付ける項目（予定表の先頭）。"""

        return self._stack[-1][1]

    def current_key(self) -> Any:
        return self._stack[-1][0]

    def is_active(self, key: Any) -> bool:
        """`key` が **祖先の連鎖**に居るか（scheduled は含まない）。"""

        return key in self._active

    def should_collect_requests(self) -> bool:
        """1 個ずつ解くのを諦めて、要求をまとめて集める実行へ切り替えるか。

        切り替えの規則はここが owner。driver 側に閾値を書かせない（片方だけが
        直って、直っていない側が幅の 2 乗のまま残る、を防ぐ）。
        """

        return self._attempts.get(self._stack[-1][0], 0) >= DISCOVERY_AFTER_RETRIES

    def need(self, items) -> None:
        """今の項目は子を待つ。自分が active になり、子が scheduled になる。

        子が **active**（= 祖先）なら閉路。scheduled な子は閉路ではないので、
        そのまま予定表の上へ積む — 先に積んだものが先に片付くので、要求元が
        本体をやり直すときには答えが揃っている。同じ項目が予定表に 2 度載っても
        害はない（2 度目は「もう答えがある」で降りるだけ）。
        """

        key = self._stack[-1][0]
        self._attempts[key] = self._attempts.get(key, 0) + 1
        self._active.add(key)
        pending = [(self._key_of(item), item) for item in items]
        for child_key, _item in pending:
            if child_key in self._active:
                raise RenderGraphCycleError(
                    "the traversal was asked for a node that is still on the active path"
                )
        self._stack.extend(reversed(pending))

    def settle(self) -> None:
        """今の項目は答えが出た（または既に答えがあった）。active から外して降りる。"""

        key, _item = self._stack.pop()
        self._active.discard(key)
        self._attempts.pop(key, None)


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


class FragmentBuilder:
    """node 1 個分の fragment を **前から 1 回で**組み立てる。

    幅が子の数に比例する node はここを通す。後ろから `result = f"(… {result})"`
    と積み直すと文字列 copy が幅の 2 乗になる（実際そうなっていた）。前から
    置いて最後に 1 回だけ連結すれば線形。

    **予算を知らない**。組み立て中の fragment は speculative（捨てられることが
    ある）ので、出力予算で裁くと正しい描画を拒める。この class が持つのは
    「どう組み立てるか」だけ。
    """

    __slots__ = ("_parts",)

    def __init__(self) -> None:
        self._parts: List[str] = []

    def literal(self, text: str) -> "FragmentBuilder":
        """自分で書く文字を置く。"""

        if text:
            self._parts.append(text)
        return self

    def term(self, term: Any) -> "FragmentBuilder":
        """項を置く（子の参照でも、本体が作った項でも）。"""

        if term:
            self._parts.append(str(term))
        return self

    def repeat(self, text: str, count: int) -> "FragmentBuilder":
        """同じ文字を `count` 回置く（入れ子の閉じ括弧など）。"""

        count = int(count)
        if count > 0 and text:
            self._parts.append(text * count)
        return self

    def build(self) -> str:
        """組み立てた fragment（連結はここで 1 回だけ）。"""

        if len(self._parts) == 1:
            return self._parts[0]
        return "".join(self._parts)


class ChildResolver:
    """node 本体が driver から受け取る口。

    本体にできるのは 2 つだけ: **子を要求する**（`__call__`）と、**自分の分を
    書く**（`fragment()`）。どちらも予算を知らない — 予算を見るのは書き出し口
    だけで、この層が組み立てるのは捨てられ得る speculative な材料。
    """

    __slots__ = ("_resolve", "_new_fragment")

    def __init__(self, resolve, new_fragment) -> None:
        self._resolve = resolve
        self._new_fragment = new_fragment

    def __call__(self, node: Any, context: Any) -> "RenderedTerm":
        return self._resolve(node, context)

    def fragment(self) -> FragmentBuilder:
        """前から 1 回で組み立てる fragment builder（予算は知らない）。"""

        return self._new_fragment()


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

    ここの閾値は **予算ではない**。値を幾つにしても、同じ式は同じ意味のまま
    描ける — 変わるのは「その部分式に名前を付けるか、その場に展開するか」
    だけで、どの値でも描画を拒んだり切り詰めたりはしない（拒む口は
    `core/render_output.CountingWriter` 1 つ）。だから既定値を動かしても
    soundness の議論は起きず、`NO_SHARING_POLICY` で名前を 1 つも付けない形も
    作れる（C1 の差分比較がそれを使う）。
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
    """描画 instance の構築。予定と経路の管理は `ResolutionSchedule` が持つ。

    node 本体は「子が要る」ところで `_NeedChild` を投げるので、driver はその子を
    予定表へ積んでから同じ本体をもう一度走らせる。本体を書き換えずに反復化
    できるのが利点で、**最後に成功した実行だけ**が採用される。

    子が多い node（引数の多い CALL、branch の多い PHI）では「1 個ずつ積んで
    やり直す」が幅の 2 乗になる。予定表が「切り替えどき」を言ってきたら、
    **要求を一度に集める実行**へ切り替える: 未解決の子には偽の値を返して本体を
    最後まで走らせ、要求された子をまとめて積む。その実行の結果は捨てる
    （採用されるのは本物の値で走った実行だけ）ので、偽の値が出力へ混ざることは
    ない。収集が取りこぼしても、いつもの 1 個ずつの経路が続きを拾う。

    この class が種別について知っていることは無い。出力予算も知らない
    （enforcement point は `CountingWriter` だけ）。
    """

    def __init__(
        self, body, classify, counters: RenderCounters
    ) -> None:
        self._body = body
        self._classify = classify
        self._counters = counters
        self.instances: List[RenderInstance] = []
        self.post_order: List[int] = []
        self.index_by_key: Dict[Tuple[int, Any], int] = {}
        self._done: Dict[int, bool] = {}
        self._terms: Dict[int, RenderedTerm] = {}
        self._edges: Optional[List[int]] = None
        self._missing: Optional[Tuple[Any, Any]] = None
        #: 観測のみ（予算ではない）。renderer が同時に抱える fragment の総量
        self.retained_bytes = 0

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
            # 子の参照（placeholder）は出力に出ないので予算には数えない。幅の
            # 広い node が止まるのは、本体が区切りを書くところ（`FragmentBuilder`）。
        return term

    def run(self, root: Any, context: Any) -> int:
        schedule = ResolutionSchedule((root, context), key_of=_instance_key)
        while schedule:
            node, ctx = schedule.current()
            key = schedule.current_key()
            index = self.index_by_key.get(key)
            if index is not None and index in self._done:
                schedule.settle()
                continue
            if index is None:
                index = len(self.instances)
                self.instances.append(RenderInstance(index=index, node=node, context=ctx))
                self.index_by_key[key] = index
            edges: List[int] = []
            self._edges = edges
            self._missing = None
            try:
                fragment = self._body(node, ctx, self._child_resolver())
            except _NeedChild:
                self._counters.node_body_executions += 1
                if self._missing is None:
                    # `_NeedChild` は `resolve` が要求を控えてから投げる合図で、
                    # 控えの無い合図は driver の不整合。何を積むか分からない
                    # まま進めない。
                    raise RenderPlanInvariantError(
                        "a child was requested without recording which one"
                    )
                pending = [self._missing]
                if schedule.should_collect_requests():
                    pending = self._collect_requests(node, ctx) or pending
                schedule.need(pending)
                continue
            finally:
                self._edges = None
            self._counters.node_body_executions += 1
            self._complete(index, str(fragment), tuple(edges))
            schedule.settle()
        return self.index_by_key[(id(root), context)]

    def _child_resolver(self) -> ChildResolver:
        return ChildResolver(self.resolve, FragmentBuilder)

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

                def collect(child: Any, child_context: Any, _term=unresolved):
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
                    return term

                self._counters.node_body_executions += 1
                try:
                    self._body(node, context, ChildResolver(collect, FragmentBuilder))
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
        # fragment に **実際に現れる** 子。要求しても捨てられた子は入らない
        # （出力に効くのはこちら）。fragment を読み直すのはここ 1 回だけ。
        instance.used_children = tuple(fragment_children(fragment))
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
        # この node が **自分で書いた** byte 数を、fragment が出来たこの 1 箇所で
        # 決める（placeholder の分は出力に出ないので差し引く）。あとで共有の
        # 見積りにも同じ値が要るが、2 度数えると「同じ量の owner が 2 つ」に
        # なるので instance に残す。
        placeholder_bytes = sum(
            len(child_placeholder(child)) for child in instance.used_children
        )
        instance.local_bytes = max(0, length - placeholder_bytes)


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


def _instance_key(item: Tuple[Any, Any]) -> Tuple[int, Any]:
    """描画 instance の同一性 = (意味 node, 描画文脈)。

    node だけを key にすると、別の幅 / 文脈で描いた式を同じ束縛に束ねてしまう。
    予定表も memo もこの同じ単位で動く（別の単位を持つと、片方が「同じ」と
    言うものを他方が「別」と言う）。
    """

    node, context = item
    return (id(node), context)


def build_render_plan(
    root: Any,
    context: Any,
    *,
    body,
    classify: Callable[[str, Any, bool], Any],
    policy: SharingPolicy,
    counters: RenderCounters,
) -> RenderPlan:
    """DAG を 1 回だけ辿り、fragment・参照回数・名前を付ける instance を決める。

    計画は出力予算を見ない（speculative な作業なので、出力予算で裁くと正しい
    描画を拒める）。
    """

    driver = _Driver(body, classify, counters)
    root_index = driver.run(root, context)

    instances = driver.instances
    post_order = tuple(driver.post_order)

    # 参照回数は **fragment に実際に現れる**子で数える（`used_children` は
    # fragment が出来たときに決めてある）。要求されたが捨てられた子（定数条件を
    # `true` へ畳む枝など）まで数えると、出力に 1 度も現れない instance へ名前が
    # 付き、空の参照先を持つ `let` が残る。
    for index in post_order:
        for child_index in instances[index].used_children:
            instances[child_index].references += 1

    shared_references = 0
    for index in post_order:
        instance = instances[index]
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
    ないので、予算に達した時点で `CountingWriter` が止められる（= 完成した出力
    文字列を作らない）。
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
