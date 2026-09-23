# -*- coding: utf-8 -*-
"""凍結済み意味 object の immutable な表現（Issue #22 PR-22-B）。

この module が所有するのは **「node の意味とは何か」** だけで、「生 object をどう
読むか」（`core/semantic_projection.py`）とも「いつ凍結・検証するか」
（`core/semantic_freeze.py`）とも「2 つの式が同じか」（`core/structural.py`）とも
別の変更軸になっている。

* `SemanticSnapshot` — 1 node 分の不変な意味値。**pure value しか持たない**:
  生 object への参照も、あとから生 object を読む遅延セルも無い。凍結が終わった
  時点で意味は確定していて、生 object を書き換えても動かない。
* `LocalPayload` / `local_semantic_payload` / `ordered_semantic_edges` —
  node を「子以外の意味 field」と「順序付き辺」へ分解する唯一の場所。candidate
  hash・完全比較・graph snapshot はこの 1 つの分解を共有するので、意味 field を
  足したときに 3 つが食い違うことがない。
* `NodeRecord` / `ImmutableSemanticGraph` / `walk_dag` — root から決定的な辺順で
  番号を振った DAG の **表現**。identity ではない（identity は
  `core/structural.py` が所有する）。

依存の向き: `core/semantic_projection.py` と `core/errors.py` の例外型だけ。
authority / CLI / checker / config / env も、失敗の台帳（`record_internal_bug` 等）も
読まない — 内部バグを記録するのは freeze 境界の責務。
`tests/unit/test_architecture_boundaries.py` が固定している。
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, Dict, List, NamedTuple, Optional, Tuple

from scripts.function_tracer_pcode.core.errors import ExpressionCycleError
from scripts.function_tracer_pcode.core.loop_lowering_semantics import (
    LoopLoweringSemantics,
)
from scripts.function_tracer_pcode.core.semantic_projection import (
    DeclaredTypeProjection,
    RuntimeRefProjection,
    StorageProjection,
    absent_declared_type_projection,
    absent_runtime_projection,
    absent_storage_projection,
    canonical_value_key,
    project_expression,
    value_key_is_opaque,
)


StructuralAtoms = Tuple[Any, ...]

#: `ExpressionType` を import せずに種別を判定するための名前（`core` の下位で
#: 循環 import を作らないため。値は `ExpressionType` の member 名と一致する）。
_CONSTANT = "CONSTANT"
_PARAMETER = "PARAMETER"
_VARIABLE = "VARIABLE"
_BINARY_OP = "BINARY_OP"
_UNARY_OP = "UNARY_OP"
_CALL = "CALL"
_INTRINSIC = "INTRINSIC"
_MEMORY = "MEMORY"
_PHI = "PHI"
_UNKNOWN = "UNKNOWN"
_LITERAL = "LITERAL"

#: 宣言型の signedness を読む node 種別（幅合わせがこの 2 種別でしか見ない）。
_DECLARED_TYPE_KINDS = frozenset({_PARAMETER, _VARIABLE})

#: 子の順序が意味を変えない二項演算。**node の意味の一部**なので分解の owner が
#: 持つ。ここ 1 箇所を見て candidate hash も完全比較も identity digest も同じ
#: 正規化をするので、演算子を足しても 3 つが食い違わない。
COMMUTATIVE_BINARY_OPS = frozenset(
    {
        "INT_ADD",
        "INT_MULT",
        "INT_AND",
        "INT_OR",
        "INT_XOR",
        "INT_EQUAL",
        "INT_NOTEQUAL",
        "BOOL_AND",
        "BOOL_OR",
        "BOOL_XOR",
    }
)


def children_are_commutative(expr: Any) -> bool:
    """この node の子の並びが意味を変えないか。"""

    if _kind_name(expr) != _BINARY_OP:
        return False
    return (getattr(expr, "operator", None) or "") in COMMUTATIVE_BINARY_OPS

# ---------------------------------------------------------------------------
# SemanticSnapshot
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SemanticSnapshot:
    """凍結時に確定した、1 node 分の意味値。

    ここに無い生 object（`data_type_obj`、`StorageInfo`、`runtime_ref` object）は
    **意味 consumer が読んではいけない**。ref の構造を辿る必要がある判断
    （loop lowering）も、辿った結果は `loop_lowering` に値として入っている。
    """

    #: `canonical_value_key(value)`
    canonical_value: StructuralAtoms
    #: `value` が Python object 表現へ落ちたか
    value_is_opaque: bool
    #: runtime ref から読み取った意味値（ref が無ければ absent projection）
    runtime: RuntimeRefProjection
    #: storage から読み取った意味値
    storage: StorageProjection
    #: 宣言型から読み取った意味値
    declared_type: DeclaredTypeProjection
    #: 生 object の有無（有無だけは意味に効く: 「型情報が無い」も情報）
    has_runtime_ref: bool
    has_data_type_obj: bool

    # -- consumer が使う読み口（すべて pure value） ------------------------

    @property
    def runtime_structural_key(self) -> Optional[StructuralAtoms]:
        return self.runtime.structural_key

    @property
    def runtime_stable_key(self) -> Any:
        return self.runtime.stable_key

    @property
    def runtime_semantic_key(self) -> Any:
        return self.runtime.semantic_key

    @property
    def runtime_stable_origin(self) -> Optional[Tuple[Any, ...]]:
        return self.runtime.stable_origin

    @property
    def runtime_is_parameter_ref(self) -> bool:
        return self.runtime.is_parameter_ref

    @property
    def parameter_runtime_key(self) -> Optional[StructuralAtoms]:
        return self.runtime.parameter_stable_key

    @property
    def is_address_value_ref(self) -> bool:
        return self.runtime.is_address_value_ref

    @property
    def address_offset(self) -> Optional[int]:
        return self.runtime.address_offset

    @property
    def address_object_identity(self) -> Optional[Tuple[Any, ...]]:
        return self.runtime.address_object_identity

    @property
    def runtime_lowering_identity(self) -> Optional[Tuple[Any, ...]]:
        return self.runtime.lowering_identity

    @property
    def loop_lowering(self) -> LoopLoweringSemantics:
        """loop lowering に必要な意味（`core/loop_lowering_semantics.py` が所有）。"""

        return self.runtime.loop_lowering

    @property
    def declares_variable_symbol(self) -> bool:
        return self.runtime.declares_variable_symbol

    @property
    def storage_identity(self) -> Optional[StructuralAtoms]:
        return self.storage.identity

    @property
    def storage_identity_supported(self) -> bool:
        return self.storage.supported

    @property
    def declared_signedness(self) -> Optional[bool]:
        return self.declared_type.signedness


_EMPTY_SNAPSHOT = SemanticSnapshot(
    canonical_value=("none", ""),
    value_is_opaque=False,
    runtime=absent_runtime_projection(),
    storage=absent_storage_projection(),
    declared_type=absent_declared_type_projection(),
    has_runtime_ref=False,
    has_data_type_obj=False,
)


def build_semantic_snapshot(expr: Any) -> SemanticSnapshot:
    """生 object を 1 回だけ読んで意味値にする（凍結時に呼ばれる）。

    評価する field を node 種別で絞るのは費用のためだけで、絞った field の
    consumer はその種別に存在しない。
    """

    kind = _kind_name(expr)

    if kind == _PHI:
        # PHI の `value` は branch container で、意味は辺（条件と値）が持つ。
        canonical_value: StructuralAtoms = ("phi_branches",)
    else:
        canonical_value = canonical_value_key(getattr(expr, "value", None))

    # 生 object を読むのは projection owner。ここは「どんな意味値があるか」
    # だけを知っていて、「それがどの属性から来たか」は知らない。
    projected = project_expression(expr, declared_type_kinds=_DECLARED_TYPE_KINDS)

    return SemanticSnapshot(
        canonical_value=canonical_value,
        value_is_opaque=value_key_is_opaque(canonical_value),
        runtime=projected.runtime,
        storage=projected.storage,
        declared_type=projected.declared_type,
        has_runtime_ref=projected.has_runtime_ref,
        has_data_type_obj=projected.has_data_type_obj,
    )


def semantic_projection(expr: Any) -> SemanticSnapshot:
    """意味 consumer の唯一の入口。

    凍結済みなら保存済みの値をそのまま返す（生 object を読まない）。未凍結なら
    毎回その場で作る（値も費用も従来と同じ）。
    """

    if expr is None:
        return _EMPTY_SNAPSHOT
    snapshot = getattr(expr, "_snapshot", None)
    if snapshot is not None:
        return snapshot
    return build_semantic_snapshot(expr)


def _kind_name(expr: Any) -> Optional[str]:
    expr_type = getattr(expr, "expr_type", None)
    return getattr(expr_type, "name", None)


def _int_atom(value: Any, tag: str) -> Any:
    """int として扱える field を int に、扱えなければ壊れた値として表現に残す。

    identity の構築で落とさないのが大事で、幅や opcode が壊れている node に
    **型の付いた** 失敗を出すのは renderer / 幅検証の責務。ここで `ValueError`
    にしてしまうと、その typed な失敗まで届かなくなる。
    """

    try:
        return int(value or 0)
    except (TypeError, ValueError):
        return (tag, canonical_value_key(value))


# ---------------------------------------------------------------------------
# node の分解（hash / 完全比較 / graph snapshot が共有する唯一の場所）
# ---------------------------------------------------------------------------


class LocalPayload(NamedTuple):
    """子以外の意味 field をまとめた 1 node 分の payload。

    `compare_atoms` と `identity_atoms` が違うのは 1 点だけで、`value` が Python
    object 表現へ落ちたときに前者は「同じ object か」を区別できる token を持ち、
    後者は process 非依存の tag だけを持つ。identity 側に `id()` を入れると
    digest が run 間で変わってしまい、比較側から落とすと別 object を同一視して
    しまう。

    2 つの flag は別のことを言う:

    * `comparable=False` — この node は **完全比較で一致としてはいけない**
      （`expression_key` の `opaque` 枝と同じ、未知の node 種別）。
    * `identity_complete=False` — `identity_atoms` だけでは別の値を区別でき
      ない（`value` が Python object 表現へ落ちた）。完全比較は
      `compare_atoms` を使うので影響を受けないが、graph snapshot を identity
      として使う consumer はここを見て拒否できる。
    """

    compare_atoms: StructuralAtoms
    identity_atoms: StructuralAtoms
    comparable: bool
    identity_complete: bool


class SemanticEdge(NamedTuple):
    """node から子への順序付き辺。"""

    label: Tuple[Any, ...]
    child: Any


def local_semantic_payload(
    expr: Any, snapshot: Optional[SemanticSnapshot] = None
) -> LocalPayload:
    """node の「子以外の意味 field」。`expression_key` と同じ field 集合を見る。

    ここに field を足すと candidate hash・完全比較・graph snapshot の 3 つが
    同時に追従する。`tests/unit/test_expression_structural_identity.py` の
    drift test が `expression_key` との field 集合の一致を固定している。

    凍結済みの node では凍結時に 1 回作った payload をそのまま返す。完全比較は
    同じ node の payload を何度も見る（`Condition.equals` は解析中に何万回も
    呼ばれる）ので、そのたびに tuple を組み直さない。

    `snapshot` は検証中の呼び出し（まだ node へ書いていない投影）で渡す。
    渡さないと `semantic_projection()` が生 object を読み直してしまい、
    「宣言型は凍結時に 1 回だけ読む」が崩れる。
    """

    cached = getattr(expr, "_local_payload", None)
    if cached is not None:
        return cached
    kind = _kind_name(expr)
    projection = snapshot if snapshot is not None else semantic_projection(expr)
    size = _int_atom(getattr(expr, "size", 0), "invalid_size")
    name = getattr(expr, "name", None) or ""
    operator = getattr(expr, "operator", None) or ""
    value_atoms = projection.canonical_value
    compare_value = value_atoms
    if projection.value_is_opaque:
        # 旧 `_atom_key` は object を `id()` 付きで区別していた。比較側だけ
        # その区別を残し、digest 側は tag のみにする。
        compare_value = ("opaque_value_instance", id(getattr(expr, "value", None)))

    if kind == _CONSTANT:
        atoms = ("const", compare_value, size)
        ident = ("const", value_atoms, size)
    elif kind == _LITERAL:
        atoms = ("literal", compare_value, size)
        ident = ("literal", value_atoms, size)
    elif kind in (_PARAMETER, _VARIABLE):
        tag = kind.lower()
        atoms = (tag, name, compare_value, size)
        ident = (tag, name, value_atoms, size)
    elif kind == _UNKNOWN:
        runtime = _runtime_metadata_atoms(projection)
        atoms = ("unknown", name, compare_value, size) + runtime
        ident = ("unknown", name, value_atoms, size) + runtime
    elif kind == _UNARY_OP:
        atoms = ident = ("unary", operator, size)
    elif kind == _BINARY_OP:
        atoms = ident = ("binary", operator, size)
    elif kind == _MEMORY:
        read_order_key = getattr(expr, "read_order_key", None)
        read_order = (
            ("read_order", _int_atom(read_order_key, "invalid_read_order"))
            if read_order_key is not None
            else ("read_order", None)
        )
        runtime = _runtime_metadata_atoms(projection)
        atoms = ident = ("memory", size, read_order) + runtime
    elif kind == _CALL:
        atoms = ident = ("call", name, size, len(getattr(expr, "operands", ()) or ()))
    elif kind == _INTRINSIC:
        opcode = getattr(expr, "opcode", None)
        atoms = ident = (
            "intrinsic",
            name,
            None if opcode is None else _int_atom(opcode, "invalid_opcode"),
            size,
            len(getattr(expr, "operands", ()) or ()),
        )
    elif kind == _PHI:
        branches = getattr(expr, "value", None) or ()
        negated = []
        has_condition = []
        for branch in branches:
            condition = branch[0] if len(branch) > 0 else None
            negated.append(bool(getattr(condition, "negated", False)))
            has_condition.append(condition is not None)
        atoms = ident = (
            "phi",
            size,
            len(branches),
            tuple(negated),
            tuple(has_condition),
        )
    else:
        # `expression_key` の `opaque` 枝と同じ扱い: 表現は作るが一致とはしない。
        atoms = ident = (
            "opaque",
            kind if kind is not None else str(getattr(expr, "expr_type", None)),
            operator,
            name,
            size,
        )
        return LocalPayload(atoms, ident, False, True)

    return LocalPayload(atoms, ident, True, not projection.value_is_opaque)


def _runtime_metadata_atoms(projection: SemanticSnapshot) -> StructuralAtoms:
    if projection.runtime_structural_key is None:
        return ()
    return (("runtime_ref", projection.runtime_structural_key),)


def ordered_semantic_edges(expr: Any) -> Tuple[SemanticEdge, ...]:
    """node から子への辺を決定的な順序で返す。

    `expression_key` が子を読む順序と一致させる（binary は operand 0 / 1、
    PHI は branch ごとに条件 → 値）。可換の正規化はここでは行わない:
    「表現」と「どう一致とみなすか」は別の変更軸で、後者は
    `core/structural.py` が所有する。
    """

    kind = _kind_name(expr)
    operands = getattr(expr, "operands", None) or ()
    if kind == _UNARY_OP:
        child = operands[0] if operands else None
        return (SemanticEdge(("operand", 0), child),)
    if kind == _BINARY_OP:
        left = operands[0] if operands else None
        right = operands[1] if len(operands) > 1 else None
        return (
            SemanticEdge(("operand", 0), left),
            SemanticEdge(("operand", 1), right),
        )
    if kind == _MEMORY:
        child = operands[0] if operands else None
        return (SemanticEdge(("operand", 0), child),)
    if kind in (_CALL, _INTRINSIC):
        return tuple(
            SemanticEdge(("operand", index), operand)
            for index, operand in enumerate(operands)
        )
    if kind == _PHI:
        edges: List[SemanticEdge] = []
        for index, branch in enumerate(getattr(expr, "value", None) or ()):
            condition = branch[0] if len(branch) > 0 else None
            value = branch[1] if len(branch) > 1 else None
            condition_expr = getattr(condition, "expression", None) if condition is not None else None
            edges.append(SemanticEdge(("phi_condition", index), condition_expr))
            edges.append(SemanticEdge(("phi_value", index), value))
        return tuple(edges)
    if kind in (_CONSTANT, _LITERAL, _PARAMETER, _VARIABLE, _UNKNOWN):
        return ()
    # 未知種別: 子を辿らない（`expression_key` の opaque 枝と同じ）。
    return ()


# ---------------------------------------------------------------------------
# DAG snapshot
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class NodeRecord:
    """graph snapshot の 1 node。

    `local_payload` は digest ではなく **完全な local payload**。digest だけでは
    一致を確定できない（`candidate_digest` は bucket 専用）ので、cache の hit は
    payload と辺の完全比較まで進んでから確定する。
    """

    canonical_node_no: int
    #: 候補絞り込み専用の digest（凍結時に identity owner が付けた値をそのまま運ぶ。
    #: **等価の確定にも stable identity にも使わない**）
    candidate_digest: Optional[bytes]
    local_payload: StructuralAtoms
    ordered_edges: Tuple[Tuple[Tuple[Any, ...], Optional[int]], ...]
    comparable: bool
    identity_complete: bool
    #: 子の並びが意味を変えないか（identity 側が正規化に使う）
    commutative_children: bool


@dataclass(frozen=True)
class ImmutableSemanticGraph:
    """root から到達できる distinct node の不変な snapshot。

    root からの path は保存しない（共有 DAG では path 数が指数になる）。番号は
    root から決定的な辺順の first-encounter 順で、`id()` には依存しない。
    """

    root_no: Optional[int]
    nodes: Tuple[NodeRecord, ...]

    @property
    def distinct_node_count(self) -> int:
        return len(self.nodes)

    @property
    def edge_count(self) -> int:
        return sum(len(node.ordered_edges) for node in self.nodes)

    @property
    def comparable(self) -> bool:
        return all(node.comparable for node in self.nodes)

    @property
    def identity_complete(self) -> bool:
        """graph snapshot だけで別の式と区別できるか（`id()` に頼っていないか）。"""

        return all(node.identity_complete for node in self.nodes)


class SemanticTraversal(NamedTuple):
    """1 回の走査で得た 2 つの並び。

    `entry_order` は root から決定的な辺順で最初に出会った順、`post_order` は
    子が必ず先に来る順。片方しか要らない呼び出し側も、走査を 2 回しない。
    """

    entry_order: Tuple[Any, ...]
    post_order: Tuple[Any, ...]


def traverse_semantic_graph(root: Any, *, prune=None) -> SemanticTraversal:
    """意味 graph を 1 回だけ走査する。**閉路判定の唯一の実装**。

    freeze（検証して凍らせる）も graph snapshot（表現を作る）も同じ不変条件
    「経路上の node へ戻らない」を必要とする。実装を 2 つ持つと片方だけが
    直る（実際、辺の判定順を 1 行間違えて back-edge を取り逃していた）ので、
    走査はここ 1 本にする。

    `prune(node)` が真なら、その node と配下へ入らない。凍結済みの subtree を
    再走査しないために freeze が使う（凍結済み node は検証済みなので、そこに
    閉路が隠れることはない）。

    閉路は通常入力として認めない内部不整合なので `ExpressionCycleError` を
    投げる。placeholder を置いて意味処理を続けない — 見えていない部分を無視した
    比較や論理式で判定が確定してしまうため。台帳への記録は freeze 境界の責務で、
    この module は例外型だけを知っている。
    """

    entry_order: List[Any] = []
    post_order: List[Any] = []
    if root is None:
        return SemanticTraversal((), ())
    if prune is not None and prune(root):
        return SemanticTraversal((), ())

    entered: Dict[int, bool] = {}
    active: Dict[int, bool] = {}
    stack: List[Tuple[Any, bool]] = [(root, False)]

    while stack:
        node, exiting = stack.pop()
        node_id = id(node)
        if exiting:
            active.pop(node_id, None)
            post_order.append(node)
            continue
        # **順番が大事**: 経路上に居るかを、既に見たかより先に判定する。
        # 逆にすると、入口で番号を振った node への back-edge が「共有」に
        # 見えてしまい、閉路が素通りする。
        if node_id in active:
            raise ExpressionCycleError(
                "semantic graph contains a cycle: "
                f"{_kind_name(node)} {getattr(node, 'name', None)!r}"
            )
        if node_id in entered:
            continue
        entered[node_id] = True
        active[node_id] = True
        entry_order.append(node)
        stack.append((node, True))
        for edge in reversed(ordered_semantic_edges(node)):
            child = edge.child
            if child is None:
                continue
            if prune is not None and prune(child):
                continue
            stack.append((child, False))

    return SemanticTraversal(tuple(entry_order), tuple(post_order))


#: 木として展開したときの node 数の飽和値（凍結時の `_tree_size` と同じ上限）。
TREE_NODE_ESTIMATE_CAP = 1 << 62


class SemanticGraphMeter:
    """複数の root が **合わせて** 持つ distinct node 数と、木に展開した大きさ。

    root を足すたびに、まだ数えていない node だけを辿る（累計の費用は distinct
    node + 辺に比例する）。数え方の owner はこの module（辺の分解
    `ordered_semantic_edges` と同じ規則）で、何と比べるか（予算）は呼ぶ側が持つ。

    `tree_nodes` は足した root を **木として** 展開した node 数の和（飽和付き）。
    共有 DAG では distinct より指数的に大きくなり得るので、予算ではなく証拠として
    使う。閉路はここでは検出しない（凍結の責務）: 数えた node へは戻らないので
    閉路があっても止まる。
    """

    __slots__ = ("_seen", "_tree", "distinct_nodes", "tree_nodes", "roots")

    def __init__(self) -> None:
        self._seen: Dict[int, Any] = {}
        self._tree: Dict[int, int] = {}
        self.distinct_nodes = 0
        self.tree_nodes = 0
        self.roots = 0

    def add_root(self, root: Any) -> None:
        if root is None:
            return
        self.roots += 1
        stack: List[Tuple[Any, bool]] = [(root, False)]
        while stack:
            node, exiting = stack.pop()
            node_id = id(node)
            if exiting:
                size = 1
                for edge in ordered_semantic_edges(node):
                    if edge.child is not None:
                        size += self._tree.get(id(edge.child), 1)
                self._tree[node_id] = min(TREE_NODE_ESTIMATE_CAP, size)
                continue
            if node_id in self._seen:
                continue
            # object を保持して id の再利用を防ぐ（数えている間に解放されない）
            self._seen[node_id] = node
            self.distinct_nodes += 1
            stack.append((node, True))
            for edge in ordered_semantic_edges(node):
                child = edge.child
                if child is not None and id(child) not in self._seen:
                    stack.append((child, False))
        self.tree_nodes = min(
            TREE_NODE_ESTIMATE_CAP, self.tree_nodes + self._tree.get(id(root), 1)
        )


def graph_representation_digest(graph: ImmutableSemanticGraph) -> Optional[str]:
    """**表現** としての graph に対する安定 digest。

    `walk_dag()` が作った番号・local payload・順序付き辺をそのまま digest する。
    可換演算の並びも共有の仕方も **保たれる** ので、`structural_equals` とは
    別の同値関係になる（`ADD(a,3)` と `ADD(3,a)` は別の digest）。

    用途は「この式をこの形で扱ったか」を鍵にしたい consumer —
    PR-105-A の rewrite identity が root の graph snapshot を memo する、
    といった **表現に依存する cache の前段**。意味の等価を聞きたいなら
    `core/structural.py` の `structural_identity_digest` を使うこと。

    どちらの digest も **hit を確定しない**。確定するのは完全比較だけ。
    """

    if graph.root_no is None:
        return None
    if not graph.comparable or not graph.identity_complete:
        return None
    payload = (
        "semantic_graph_representation_v1",
        graph.root_no,
        tuple(
            (node.canonical_node_no, node.local_payload, node.ordered_edges)
            for node in graph.nodes
        ),
    )
    digest = hashlib.blake2b(digest_size=32, person=b"graph-repr-v1")
    digest.update(_encode_atoms_to_bytes(payload))
    return digest.hexdigest()


def _encode_atoms_to_bytes(value: Any) -> bytes:
    """atom を **型を落とさずに** 決定的な byte 列へ符号化する。

    `repr()` を使わないのは、未知の object が混ざると `id()` が入って run 間で
    digest が変わってしまうため。未知の型は型名だけにする。
    """

    parts: List[str] = []
    _encode_atoms(value, parts)
    return "".join(parts).encode("utf-8", "surrogatepass")


def _encode_atoms(value: Any, parts: List[str]) -> None:
    if value is None:
        parts.append("n;")
    elif value is True or value is False:
        parts.append("b1;" if value else "b0;")
    elif isinstance(value, int):
        parts.append("i%d;" % value)
    elif isinstance(value, float):
        parts.append("f%r;" % value)
    elif isinstance(value, str):
        parts.append("s%d:%s;" % (len(value), value))
    elif isinstance(value, bytes):
        parts.append("y%s;" % value.hex())
    elif isinstance(value, (tuple, list)):
        parts.append("(t" if isinstance(value, tuple) else "(l")
        parts.append("%d;" % len(value))
        for item in value:
            _encode_atoms(item, parts)
        parts.append(")")
    else:
        parts.append("o%s.%s;" % (type(value).__module__, type(value).__qualname__))


def walk_dag(root: Any) -> ImmutableSemanticGraph:
    """root から到達できる DAG の canonical な **表現** を作る。

    費用は distinct node + 辺に比例する（同じ node を 2 回展開しない）。番号は
    first-encounter 順で `id()` に依存しない。閉路は受理しない
    （`traverse_semantic_graph` の契約）。

    これは表現であって identity ではない: 可換演算の順も共有の仕方もそのまま
    残る。「2 つの式が同じか」は `core/structural.py` が決める。
    """

    if root is None:
        return ImmutableSemanticGraph(root_no=None, nodes=())

    traversal = traverse_semantic_graph(root)
    numbers = {id(node): index for index, node in enumerate(traversal.entry_order)}

    records = []
    for number, node in enumerate(traversal.entry_order):
        payload = local_semantic_payload(node)
        edges = tuple(
            (edge.label, None if edge.child is None else numbers[id(edge.child)])
            for edge in ordered_semantic_edges(node)
        )
        records.append(
            NodeRecord(
                canonical_node_no=number,
                candidate_digest=node.__dict__.get("_structural_hash")
                if hasattr(node, "__dict__")
                else None,
                local_payload=payload.identity_atoms,
                ordered_edges=edges,
                comparable=payload.comparable,
                identity_complete=payload.identity_complete,
                commutative_children=children_are_commutative(node),
            )
        )

    return ImmutableSemanticGraph(root_no=0, nodes=tuple(records))
