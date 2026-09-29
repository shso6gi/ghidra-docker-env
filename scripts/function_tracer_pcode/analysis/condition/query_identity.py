# -*- coding: utf-8 -*-
"""条件 oracle の solver query identity と rewrite identity（Issue #105 PR-105-A）。

この module が所有するのは **「2 つの query / rewrite が同じ入力か」** だけ:

* `RootQueryGraph` — 式 1 つ（root）の canonical な DAG 表現。`walk_dag` の graph
  （structural な local payload と順序付き辺）に、solver が node ごとに読む意味値
  （名前・演算子・凍結時の `SemanticSnapshot`）を同じ番号で添えたもの。**root だけに
  依存する** ので root 単位で memo してよい。
* `SolverQueryIdentity` — 条件の集合（conjunction）を solver に渡したときの意味の
  identity。条件ごとの（向き, root graph）を canonical な順に並べ、render context と
  schema を持つ。symbol（`objvar_<n>`）の割当はここから決まる。
* `RewriteIdentity` — root を symbol mapping の下で書き換えた結果の identity
  （root graph + mapping の全体 + render context + schema）。
* solver symbol identity の規則（`solver_symbol_identity` /
  `solver_symbol_identity_is_safe`）。symbol の同一視は query の意味そのものなので
  ここが唯一の owner で、oracle は委譲するだけ。

**hash / digest で一致を確定しない**。`fast`（外側の bucket）→ graph digest →
node ごとの local payload・辺・意味値の完全比較、の順に進み、最後の完全比較だけが
一致を決める。digest がすべて衝突しても、比較が不一致を返すので誤った cache hit には
ならない（性能の問題に留まる）。比較できない graph（未知の node 種別、値が Python
object 表現へ落ちた node）は **自分自身以外と一致しない** — cache の key にならない。

structural identity（`core/structural.py`、可換の正規化あり・runtime identity なし）とは
**別の同値関係**: 構造が同じでも solver symbol や宣言型が違えば別の query で
（計画 I-4）、逆に `ADD(a,3)` と `ADD(3,a)` は構造上同じでも表現としては別の query に
なる（cache の miss になるだけ）。相互に代用しない。

持たないもの: cache の保存と寿命（`condition_cache`）、script の組み立てと solver の実行
（`smt_oracle`）、計測（`condition_metrics`）。依存は `core` の表現（`semantic_snapshot`）
と検証（`semantic_freeze.validated`）だけで、公開（publish）はしない。
"""

from __future__ import annotations

import hashlib
import weakref
from dataclasses import dataclass
from typing import Any, Callable, Dict, FrozenSet, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.analysis.condition.condition_cache import root_memo
from scripts.function_tracer_pcode.core.condition_metrics import note
from scripts.function_tracer_pcode.core.semantic_freeze import validated
from scripts.function_tracer_pcode.core.semantic_snapshot import (
    ImmutableSemanticGraph,
    encode_stable_atoms,
    semantic_projection,
    walk_dag_nodes,
)


#: identity の schema。値の作り方（何を比べるか・symbol の割当順）を変えたら上げる。
#: 旧 cache key（`condition-smt-cache-v2`、`condition_key` の `repr` 順）とは互換が無い。
QUERY_IDENTITY_SCHEMA = "condition-smt-query-v3"
REWRITE_IDENTITY_SCHEMA = "condition-smt-rewrite-v1"

_GRAPH_PERSON = b"qgraph-v1"
_QUERY_PERSON = b"squery-v1"
_REWRITE_PERSON = b"rewrite-v1"
_MAPPING_PERSON = b"smapping-v1"

_PARAMETER = "PARAMETER"
_VARIABLE = "VARIABLE"
_CALL = "CALL"
_SYMBOL_KINDS = frozenset({_PARAMETER, _VARIABLE})

#: `root_memo` の種別名（root 単位の memo は root graph だけ）
ROOT_GRAPH_MEMO = "query_identity.root_graph"


@dataclass(frozen=True)
class RenderContext:
    """SMT 描画の文脈（描画の引数と描画の schema）。

    symbol 名は描画引数ではなく書き換え（`RewriteIdentity` の mapping）で渡すので
    ここには入らない。
    """

    float_mode: str
    render_schema: str


def _oracle_render_context() -> RenderContext:
    from scripts.function_tracer_pcode.core.render_smt import SMT_RENDER_SCHEMA

    return RenderContext(float_mode="fp", render_schema=SMT_RENDER_SCHEMA)


#: 条件 oracle の描画文脈（`Expression.to_smt(float_mode="fp")`）
ORACLE_RENDER_CONTEXT = _oracle_render_context()


# ---------------------------------------------------------------------------
# solver symbol identity（oracle の `_expression_identity_key` の本体）
# ---------------------------------------------------------------------------


def _kind_name(expr: Any) -> Optional[str]:
    return getattr(getattr(expr, "expr_type", None), "name", None)


def normalize_call_symbol(name: Optional[str]) -> str:
    from scripts.function_tracer_pcode.core.render_smt import normalize_call_symbol_name

    return normalize_call_symbol_name(name)


def runtime_identity_from_projection(projection) -> Optional[Tuple[Any, ...]]:
    """投影 1 つから runtime identity を決める（`SemanticSnapshot` でも `RuntimeRefProjection` でも）。"""

    return runtime_identity_from_parts(
        semantic_identity=projection.runtime_semantic_key
        if hasattr(projection, "runtime_semantic_key")
        else projection.semantic_key,
        stable_identity=projection.runtime_stable_key
        if hasattr(projection, "runtime_stable_key")
        else projection.stable_key,
        parameter_ref=projection.runtime_is_parameter_ref
        if hasattr(projection, "runtime_is_parameter_ref")
        else projection.is_parameter_ref,
    )


def runtime_identity_from_parts(
    *,
    semantic_identity: Any,
    stable_identity: Any,
    parameter_ref: bool,
) -> Optional[Tuple[Any, ...]]:
    """runtime identity の **決め方** はここ 1 箇所（生 object 経由も投影経由も同じ）。"""

    if semantic_identity is not None:
        return ("semantic", semantic_identity)
    if stable_identity is not None:
        if parameter_ref:
            return ("parameter_without_semantic_identity", stable_identity)
        return ("stable", stable_identity)
    if parameter_ref:
        return ("parameter_without_semantic_identity", None)
    return None


def solver_symbol_identity(expr: Any) -> Optional[Tuple[Any, ...]]:
    """solver symbol としての object identity（PARAMETER / VARIABLE / CALL）。

    凍結済みの式では runtime_ref / storage の意味 key を **凍結時に確定した投影** から
    読む。query identity が生 object の後からの変化で動くと、同じ query に別の cache
    行が当たってしまう。
    """

    kind = _kind_name(expr)
    if kind is None:
        return None
    if kind in _SYMBOL_KINDS:
        projection = semantic_projection(expr)
        runtime_identity = runtime_identity_from_projection(projection)
        if runtime_identity is not None:
            return (
                "runtime_ref",
                "parameter" if kind == _PARAMETER else "variable",
                runtime_identity,
            )
        if kind == _PARAMETER:
            parameter_name = getattr(expr, "name", None)
            try:
                parameter_index = int(getattr(expr, "value", -1))
                if parameter_index >= 0:
                    # Some synthetic/unit-test expressions can carry a
                    # placeholder index for multiple distinct parameters.
                    # Include the name when present to avoid conflating
                    # unrelated parameters in solver-backed condition
                    # implication.
                    if parameter_name:
                        return ("parameter_index_name", parameter_index, str(parameter_name))
                    return ("parameter_index", parameter_index)
            except (TypeError, ValueError):
                parameter_index = None
            if projection.storage_identity_supported:
                if projection.storage_identity is None:
                    return None
                return ("parameter_storage", projection.storage_identity)
            if parameter_name:
                return ("parameter_name", str(parameter_name))
        return None
    if kind == _CALL:
        return normalize_call_symbol(getattr(expr, "name", None))
    return None


def solver_symbol_identity_is_safe(identity: Optional[Tuple[Any, ...]]) -> bool:
    """solver symbol として同一視してよい identity か。"""

    if not isinstance(identity, tuple) or not identity:
        return False
    # Name-only parameters are not object identities. They can collide
    # across distinct storage/index/provenance sources, so SMT-backed
    # coverage and implication checks must decline instead of proving.
    if identity[0] == "parameter_name":
        return False
    if identity[0] == "parameter_generated_ordinal":
        return False
    if _identity_contains_unsafe_parameter_key(identity):
        return False
    if (
        identity[0] == "runtime_ref"
        and len(identity) >= 3
        and isinstance(identity[2], tuple)
        and identity[2]
        and identity[2][0]
        in {
            "parameter_without_semantic_identity",
            "stable_parameter_without_index",
        }
    ):
        return False
    return True


def _identity_contains_unsafe_parameter_key(value: Any) -> bool:
    if isinstance(value, tuple):
        if _is_unsafe_parameter_key(value):
            return True
        return any(_identity_contains_unsafe_parameter_key(item) for item in value)
    if isinstance(value, (list, set, frozenset)):
        return any(_identity_contains_unsafe_parameter_key(item) for item in value)
    return False


def _is_unsafe_parameter_key(value: Tuple[Any, ...]) -> bool:
    if not value or value[0] != "parameter":
        return False
    if len(value) == 1:
        return True
    if len(value) == 2:
        return value[1] is None
    if len(value) == 3:
        return value[1] is None or value[2] is None
    if len(value) >= 4:
        return value[3] is None
    return False


# ---------------------------------------------------------------------------
# root graph（root だけに依存する値。root 単位で memo してよい唯一のもの）
# ---------------------------------------------------------------------------


def _node_solver_payload(node: Any) -> Tuple[Any, ...]:
    """graph の local payload に載らない、solver / renderer が node ごとに読む値。

    `SemanticSnapshot` は凍結時に確定した pure value の dataclass（値で比較される）で、
    renderer が生 object の代わりに読む唯一の意味値（PR-22-B の single source 契約）。
    名前と演算子は種別によって structural payload に入らないので明示的に足す。
    """

    return (
        getattr(node, "name", None) or "",
        getattr(node, "operator", None) or "",
        semantic_projection(node),
    )


def _payload_digest_atoms(payload: Tuple[Any, ...]) -> Tuple[Any, ...]:
    """意味値のうち bucket に効かせる部分（**lossy**。一致は完全比較が決める）。"""

    name, operator, snapshot = payload
    return (
        name,
        operator,
        snapshot.runtime_structural_key,
        snapshot.storage_identity,
        snapshot.declared_signedness,
    )


@dataclass(frozen=True, eq=False)
class RootQueryGraph:
    """式 1 つの canonical な DAG 表現（solver が読む意味値つき）。

    `graph.nodes[i]` と `node_payloads[i]` が同じ node（番号は `walk_dag_nodes` が
    振る）。`symbols` は PARAMETER / VARIABLE の symbol identity を root からの
    first-encounter 順に重複なく並べたもの（`(identity, 最初の node 番号)`）。
    identity は oracle の旧 `symbol_names` と同じく hashable（dict の key）。
    """

    graph: ImmutableSemanticGraph
    node_payloads: Tuple[Tuple[Any, ...], ...]
    symbols: Tuple[Tuple[Any, int], ...]
    digest: bytes
    cacheable: bool

    @property
    def distinct_node_count(self) -> int:
        return self.graph.distinct_node_count

    def cache_weight(self) -> int:
        """cache の中で生かす量（node の値の複製の数。`condition_cache` が上限に使う）。"""

        return max(1, len(self.node_payloads))

    def same_as(self, other: "RootQueryGraph") -> bool:
        """完全比較（番号順に node ごと。巨大な入れ子 tuple は作らない）。"""

        if self is other:
            return True
        if not isinstance(other, RootQueryGraph):
            return False
        if not (self.cacheable and other.cacheable):
            return False
        if self.digest != other.digest:
            return False
        left = self.graph
        right = other.graph
        if left.root_no != right.root_no or len(left.nodes) != len(right.nodes):
            return False
        for left_node, right_node, left_payload, right_payload in zip(
            left.nodes, right.nodes, self.node_payloads, other.node_payloads
        ):
            if left_node.local_payload != right_node.local_payload:
                return False
            if left_node.ordered_edges != right_node.ordered_edges:
                return False
            if left_payload is not right_payload and left_payload != right_payload:
                return False
        return True


def _build_root_graph(root: Any) -> RootQueryGraph:
    note("identity.root_graph_built")
    graph, nodes = walk_dag_nodes(validated(root))
    payloads = tuple(_node_solver_payload(node) for node in nodes)
    symbols = []
    seen_symbols = set()
    digest = hashlib.blake2b(digest_size=16, person=_GRAPH_PERSON)
    digest.update(b"%d|" % len(graph.nodes))
    for record, node, payload in zip(graph.nodes, nodes, payloads):
        candidate = record.candidate_digest or b""
        digest.update(b"%d:" % len(candidate))
        digest.update(candidate)
        digest.update(
            encode_stable_atoms(
                (record.local_payload, record.ordered_edges, _payload_digest_atoms(payload))
            )
        )
        if _kind_name(node) in _SYMBOL_KINDS:
            # identity が無い symbol は割り当てない（その query は使えない:
            # `solver_symbol_identity_is_safe(None)` は偽。oracle が判定する）
            identity = solver_symbol_identity(node)
            if identity is not None and identity not in seen_symbols:
                seen_symbols.add(identity)
                symbols.append((identity, record.canonical_node_no))
    return RootQueryGraph(
        graph=graph,
        node_payloads=payloads,
        symbols=tuple(symbols),
        digest=digest.digest(),
        cacheable=bool(graph.comparable and graph.identity_complete),
    )


def root_query_graph(root: Any) -> RootQueryGraph:
    """root の graph（pair の cache scope の中では root object ごとに 1 回だけ作る）。"""

    return root_memo(ROOT_GRAPH_MEMO, root, _build_root_graph)


# ---------------------------------------------------------------------------
# SolverQueryIdentity
# ---------------------------------------------------------------------------


@dataclass(frozen=True, eq=False)
class QueryEntry:
    """query の中の条件 1 つ（向き + root graph）。"""

    negated: bool
    graph: RootQueryGraph


@dataclass(frozen=True, eq=False)
class SolverQueryIdentity:
    """条件の conjunction が solver に渡す意味の identity。

    * `entries` — 条件ごとの（向き, root graph）を canonical な順（graph digest, 向き、
      同じなら入力順）に並べたもの。conjunction は順序に依らないので、入力順だけが
      違う query は同じ identity になる。
    * `order` — `entries[i]` が入力の何番目の条件か（script を canonical な順に組むため）。
      object は持たない。
    * `symbol_names` — solver symbol identity → `objvar_<n>`。canonical な符号化の順
      （同じなら canonical な first-encounter 順）で振るので、同じ identity の query は
      必ず同じ割当・同じ script になる。
    * 宣言（symbol の幅・宣言型の符号、MEMORY の幅、CALL・UNKNOWN・float の宣言）は
      graph の node ごとの値（size・local payload・`SemanticSnapshot`）の関数なので、
      graph を完全比較すれば宣言も比べたことになる（別の field として持たない）。

    `__hash__` は `fast`（bucket 専用）、`__eq__` は `matches`（完全比較）。

    **比較できない identity**（`cacheable` が偽: graph のどれかが比較できない）は、同じ
    root object の上に作った identity とだけ一致する（`instances`、root への弱参照）。
    意味の一致ではなく「同じ入力の問いの途中か」だけを表すので、表には覚えない
    （`condition_cache` が `cacheable` で拒む）。これが無いと、再入の guard（同じ問いの
    途中で同じ問いが来たら打ち切る）が比較できない条件で効かなくなる。
    """

    fast: bytes
    schema: str
    render_context: RenderContext
    entries: Tuple[QueryEntry, ...]
    order: Tuple[int, ...]
    symbol_names: Mapping[Any, str]
    cacheable: bool
    #: 比較できない identity だけが持つ、(向き, root を指す参照) の並び（`entries` と同じ順）
    instances: Tuple[Tuple[bool, Any], ...] = ()

    @classmethod
    def from_conditions(
        cls,
        conditions: Sequence[Any],
        *,
        render_context: RenderContext = ORACLE_RENDER_CONTEXT,
    ) -> "SolverQueryIdentity":
        note("identity.query_built")
        raw = []
        for index, condition in enumerate(conditions or ()):
            expression = getattr(condition, "expression", None)
            graph = root_query_graph(expression)
            raw.append((graph.digest, bool(getattr(condition, "negated", False)), index, graph))
        raw.sort(key=lambda item: (item[0], item[1], item[2]))
        entries = tuple(QueryEntry(negated, graph) for _digest, negated, _index, graph in raw)
        order = tuple(index for _digest, _negated, index, _graph in raw)
        cacheable = all(entry.graph.cacheable for entry in entries)
        instances: Tuple[Tuple[bool, Any], ...] = ()
        if not cacheable:
            instances = tuple(
                (negated, _instance_reference(getattr(conditions[index], "expression", None)))
                for _digest, negated, index, _graph in raw
            )
        symbol_names = _canonical_symbol_names(entries)
        digest = hashlib.blake2b(digest_size=16, person=_QUERY_PERSON)
        digest.update(encode_stable_atoms((QUERY_IDENTITY_SCHEMA, _context_atoms(render_context))))
        digest.update(b"%d|" % len(entries))
        for entry in entries:
            digest.update(b"\x01" if entry.negated else b"\x00")
            digest.update(entry.graph.digest)
        return cls(
            fast=digest.digest(),
            schema=QUERY_IDENTITY_SCHEMA,
            render_context=render_context,
            entries=entries,
            order=order,
            symbol_names=symbol_names,
            cacheable=cacheable,
            instances=instances,
        )

    def cache_weight(self) -> int:
        """cache の key として生かす量（条件ごとの graph の node 数の和）。"""

        return 1 + sum(entry.graph.cache_weight() for entry in self.entries)

    def matches(self, other: Any) -> bool:
        """完全比較。`fast` は早期棄却にだけ使う。"""

        if self is other:
            return True
        if not isinstance(other, SolverQueryIdentity):
            return False
        if self.fast != other.fast:
            return False
        if self.schema != other.schema or self.render_context != other.render_context:
            return False
        if len(self.entries) != len(other.entries):
            return False
        if not (self.cacheable and other.cacheable):
            return (
                not self.cacheable
                and not other.cacheable
                and _same_instances(self.instances, other.instances)
            )
        for left, right in zip(self.entries, other.entries):
            if left.negated != right.negated:
                return False
            if not left.graph.same_as(right.graph):
                return False
        return True

    def __eq__(self, other: Any) -> bool:
        return self.matches(other)

    def __ne__(self, other: Any) -> bool:
        return not self.matches(other)

    def __hash__(self) -> int:
        return hash(self.fast)

    def __len__(self) -> int:
        return len(self.entries)

    def __repr__(self) -> str:
        return (
            f"SolverQueryIdentity(conditions={len(self.entries)}, "
            f"symbols={len(self.symbol_names)}, fast={self.fast.hex()[:12]})"
        )

    @property
    def distinct_node_count(self) -> int:
        return sum(entry.graph.distinct_node_count for entry in self.entries)

    def mapping_items(self) -> Tuple[Tuple[Any, str], ...]:
        """symbol mapping の全体（`objvar` の番号順）。rewrite identity の材料。"""

        return tuple(
            sorted(self.symbol_names.items(), key=lambda item: _objvar_index(item[1]))
        )


#: 条件に式が無いときの root の代わり（`None` は「回収済み」と区別できないので使わない）
_NO_EXPRESSION = object()


def _instance_reference(expression: Any) -> Callable[[], Any]:
    """root object を指す参照（弱参照。持てない値は強参照、式が無ければ `_NO_EXPRESSION`）。"""

    if expression is None:
        return lambda: _NO_EXPRESSION
    try:
        return weakref.ref(expression)
    except TypeError:
        return lambda: expression


def _same_instances(left: Tuple[Tuple[bool, Any], ...], right: Tuple[Tuple[bool, Any], ...]) -> bool:
    """同じ root object の多重集合か（どちらかが回収済みなら一致しない）。

    `id()` は両方の object が生きている今この瞬間の比較にだけ使い、保存しない。
    """

    def _live(instances):
        rows = []
        for negated, reference in instances:
            target = reference()
            rows.append((negated, id(target), target is None))
        return sorted(rows)

    left_rows = _live(left)
    right_rows = _live(right)
    if any(dead for _negated, _id, dead in left_rows + right_rows):
        return False
    return left_rows == right_rows


def _context_atoms(context: RenderContext) -> Tuple[Any, ...]:
    return (context.float_mode, context.render_schema)


def _objvar_index(name: str) -> int:
    """`objvar_<n>` の n（symbol 名の形はこの module の `_canonical_symbol_names` が決める）。"""

    return int(name.rsplit("_", 1)[1])


def _canonical_symbol_names(entries: Tuple[QueryEntry, ...]) -> Dict[Any, str]:
    """symbol identity の canonical な割当（`objvar_<n>`）。

    まず canonical な entry 順・root 内の first-encounter 順に identity を集め（同じ
    identity は 1 つ）、符号化の byte 列で並べ替える（同じ byte 列なら集めた順）。
    符号化は未知の型を型名に落とすので並べ替えの鍵にしか使わず、同一視は identity
    の値（`==`）で行う。
    """

    collected = []
    seen = set()
    for entry in entries:
        for identity, _node_no in entry.graph.symbols:
            if identity in seen:
                continue
            seen.add(identity)
            collected.append(identity)
    ranked = sorted(
        range(len(collected)),
        key=lambda position: (encode_stable_atoms(collected[position]), position),
    )
    names: Dict[Any, str] = {}
    for number, position in enumerate(ranked):
        names[collected[position]] = f"objvar_{number}"
    return names


# ---------------------------------------------------------------------------
# RewriteIdentity
# ---------------------------------------------------------------------------


@dataclass(frozen=True, eq=False)
class RewriteIdentity:
    """root を symbol mapping の下で書き換えた結果の identity。

    書き換えの結果は root graph **と** mapping **と** 描画文脈で決まる。root だけで
    memo すると、同じ root を別の mapping（別の query）で書き換えた結果を取り違える。

    * `mapping` — symbol mapping の **全体**（`objvar` の番号順の `(identity, 名前)`）。
      一致は tuple の完全比較で決め、`mapping_digest` は bucket にだけ使う。
    """

    fast: bytes
    schema: str
    render_context: RenderContext
    root: RootQueryGraph
    mapping: Tuple[Tuple[Any, str], ...]
    mapping_digest: bytes

    @classmethod
    def for_root(
        cls,
        root: RootQueryGraph,
        mapping: Tuple[Tuple[Any, str], ...],
        *,
        render_context: RenderContext = ORACLE_RENDER_CONTEXT,
    ) -> "RewriteIdentity":
        mapping_digest = hashlib.blake2b(
            encode_stable_atoms(mapping), digest_size=16, person=_MAPPING_PERSON
        ).digest()
        digest = hashlib.blake2b(digest_size=16, person=_REWRITE_PERSON)
        digest.update(encode_stable_atoms((REWRITE_IDENTITY_SCHEMA, _context_atoms(render_context))))
        digest.update(root.digest)
        digest.update(mapping_digest)
        return cls(
            fast=digest.digest(),
            schema=REWRITE_IDENTITY_SCHEMA,
            render_context=render_context,
            root=root,
            mapping=tuple(mapping),
            mapping_digest=mapping_digest,
        )

    @property
    def cacheable(self) -> bool:
        return self.root.cacheable

    def cache_weight(self) -> int:
        """cache の key として生かす量（root の graph の node 数 + mapping の件数）。"""

        return 1 + self.root.cache_weight() + len(self.mapping)

    def matches(self, other: Any) -> bool:
        if self is other:
            return True
        if not isinstance(other, RewriteIdentity):
            return False
        if not (self.cacheable and other.cacheable):
            return False
        if self.fast != other.fast or self.mapping_digest != other.mapping_digest:
            return False
        if self.schema != other.schema or self.render_context != other.render_context:
            return False
        if self.mapping != other.mapping:
            return False
        return self.root.same_as(other.root)

    def __eq__(self, other: Any) -> bool:
        return self.matches(other)

    def __ne__(self, other: Any) -> bool:
        return not self.matches(other)

    def __hash__(self) -> int:
        return hash(self.fast)

    def __repr__(self) -> str:
        return (
            f"RewriteIdentity(nodes={self.root.distinct_node_count}, "
            f"symbols={len(self.mapping)}, fast={self.fast.hex()[:12]})"
        )


# ---------------------------------------------------------------------------
# ImplicationIdentity（条件簡約の「文脈が条件を含意するか」の問い）
# ---------------------------------------------------------------------------


@dataclass(frozen=True, eq=False)
class ImplicationIdentity:
    """含意の問い（文脈・条件・呼び出し側が渡した正規形の集合）の identity。

    答えは 3 つすべてに依存する（正規形の集合が空か文脈から作ったものかで答えが
    変わり得る）ので、どれも落とさない。文脈と条件は `SolverQueryIdentity`
    （bucket → 完全比較）、正規形の集合は primitive の tuple の集合の完全比較。
    """

    context: SolverQueryIdentity
    condition: SolverQueryIdentity
    implied_norms: FrozenSet[Any]

    @classmethod
    def of(cls, condition: Any, context: Sequence[Any], implied_norms: Any) -> "ImplicationIdentity":
        return cls(
            context=SolverQueryIdentity.from_conditions(context),
            condition=SolverQueryIdentity.from_conditions((condition,)),
            implied_norms=frozenset(implied_norms or ()),
        )

    @property
    def cacheable(self) -> bool:
        return self.context.cacheable and self.condition.cacheable

    def cache_weight(self) -> int:
        return 1 + self.context.cache_weight() + self.condition.cache_weight() + len(self.implied_norms)

    def __eq__(self, other: Any) -> bool:
        if self is other:
            return True
        if not isinstance(other, ImplicationIdentity):
            return False
        return (
            self.condition == other.condition
            and self.context == other.context
            and self.implied_norms == other.implied_norms
        )

    def __ne__(self, other: Any) -> bool:
        return not self.__eq__(other)

    def __hash__(self) -> int:
        return hash((self.context.fast, self.condition.fast, len(self.implied_norms)))

    def __repr__(self) -> str:
        return (
            f"ImplicationIdentity(context={len(self.context)}, "
            f"implied_norms={len(self.implied_norms)}, fast={self.condition.fast.hex()[:12]})"
        )


__all__ = [
    "ImplicationIdentity",
    "ORACLE_RENDER_CONTEXT",
    "QUERY_IDENTITY_SCHEMA",
    "REWRITE_IDENTITY_SCHEMA",
    "QueryEntry",
    "RenderContext",
    "RewriteIdentity",
    "RootQueryGraph",
    "SolverQueryIdentity",
    "root_query_graph",
    "runtime_identity_from_parts",
    "runtime_identity_from_projection",
    "solver_symbol_identity",
    "solver_symbol_identity_is_safe",
]
