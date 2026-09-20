# -*- coding: utf-8 -*-
"""凍結済み意味 object の immutable な表現（Issue #22 PR-22-B）。

この module が所有するのは **「node の意味とは何か」** だけで、「いつ凍結するか」
（`core/semantic_freeze.py`）とも「2 つの式が同じか」（`core/structural.py`）とも
別の変更軸になっている。

* `SemanticSnapshot` — 1 node 分の不変な意味投影。生の runtime object
  (`runtime_ref` / `storage_info` / `data_type_obj`) は freeze 時に 1 回だけ読み、
  以後の意味 consumer は snapshot だけを見る。生 object を後から書き換えても
  意味は動かない。
* `canonical_value_key` — `value` の意味内容による表現。list / tuple / dict / set
  の **container 種別を tag として保持** するので、種別違いを同一視しない。
* `LocalPayload` / `local_semantic_payload` / `ordered_semantic_edges` —
  node を「子以外の意味 field」と「順序付き辺」へ分解する唯一の場所。candidate
  hash・完全比較・graph snapshot はこの 1 つの分解を共有するので、意味 field を
  足したときに 3 つが食い違うことがない。
* `NodeRecord` / `ImmutableSemanticGraph` / `walk_dag` — root から決定的な辺順で
  番号を振った DAG の snapshot。共有部分木は 1 回しか現れず、生成コストは
  distinct node + 辺に比例する。

依存の向き: authority / CLI / checker / config / env を読まない。`core.errors` から
読むのは例外型だけで、**pair 台帳（`record_internal_bug` 等）は読まない** —
内部バグを記録するのは freeze 境界の責務。この 2 つは
`tests/unit/test_architecture_boundaries.py` が固定している。

raw → 意味の投影 helper（`_semantic_runtime_ref_key` 等）は `core/structural.py`
に置いたままにして遅延 import で借りる。あれらは既存の包括捕捉 handler を持って
いて、module を移すと `broad_except_baseline.json` の key が動いてしまうため
（baseline は delete-only）。この module が所有するのは「いつ評価して何を保存する
か」で、「どう評価するか」ではない。
"""

from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Dict, List, NamedTuple, Optional, Tuple

from scripts.function_tracer_pcode.core.errors import ExpressionCycleError


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

#: runtime_ref の意味投影を freeze 時に評価する node 種別。
#: 評価する場所を絞るのは費用のためで、意味のためではない: ここに無い種別の
#: consumer は元々 runtime_ref の semantic identity を読んでいない。
_SEMANTIC_IDENTITY_KINDS = frozenset({_PARAMETER, _VARIABLE, _UNKNOWN})
_DECLARED_TYPE_KINDS = frozenset({_PARAMETER, _VARIABLE})

_structural_helpers = None


def _helpers():
    """`core/structural.py` の raw → 意味 helper を遅延取得する。"""
    global _structural_helpers
    if _structural_helpers is None:
        from scripts.function_tracer_pcode.core import structural as _structural

        _structural_helpers = _structural
    return _structural_helpers


# ---------------------------------------------------------------------------
# canonical value
# ---------------------------------------------------------------------------


def canonical_value_key(value: Any) -> StructuralAtoms:
    """`value` の意味内容による表現。**container 種別を落とさない**。

    freeze は list を tuple へ畳むが、畳んだ事実で `["a"]` と `("a",)` を同一視
    しては意味が変わる。旧 `_atom_key` と同じ tag 体系（`list` / `tuple` /
    `dict` / `set`）を使うので、旧実装で異なった値は新実装でも異なる。

    Python object そのもの（`stable_key` も `to_dict` も持たない）は
    `("opaque_value", module, qualname)` にする。**process 依存の `id()` は
    入れない**ので、hash は run 間で決定的になる。`id()` が必要な「同じ object
    かどうか」の区別は比較用 atom 側（`LocalPayload.compare_atoms`）が持つ。
    """

    if value is None:
        return ("none", "")
    if isinstance(value, bool):
        return ("bool", int(value))
    if isinstance(value, int):
        return ("int", value)
    if isinstance(value, float):
        return ("float", repr(value))
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, tuple):
        return ("tuple", tuple(canonical_value_key(item) for item in value))
    if isinstance(value, list):
        return ("list", tuple(canonical_value_key(item) for item in value))
    if isinstance(value, frozenset):
        return ("frozenset", tuple(sorted(canonical_value_key(item) for item in value)))
    if isinstance(value, set):
        return ("set", tuple(sorted(canonical_value_key(item) for item in value)))
    if isinstance(value, (dict, MappingProxyType)):
        items = [
            (canonical_value_key(key), canonical_value_key(item))
            for key, item in value.items()
        ]
        items.sort()
        return ("dict", tuple(items))
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        helpers = _helpers()
        raw = helpers._raw_stable_key_or_none(value)
        if raw is not None:
            return ("stable", canonical_value_key(raw))
    return ("opaque_value", type(value).__module__, type(value).__qualname__)


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


def value_key_is_opaque(key: StructuralAtoms) -> bool:
    """`canonical_value_key` が object 表現へ落ちたか。"""

    return bool(key) and key[0] == "opaque_value"


# ---------------------------------------------------------------------------
# SemanticSnapshot
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SemanticSnapshot:
    """凍結時に 1 回だけ評価した、1 node 分の意味投影。

    ここに無い field（`data_type_obj` そのもの、`runtime_ref` object、
    `storage_info` object）は **意味 consumer が読んではいけない** 生 object で、
    signature 表示・debug 表示・loop lowering のような表現専用の用途に限る。
    """

    #: `canonical_value_key(value)`
    canonical_value: StructuralAtoms
    #: `value` が Python object 表現へ落ちたか（落ちたら完全比較は一致としない）
    value_is_opaque: bool
    #: `structural._semantic_runtime_ref_key(runtime_ref)`（structural key 用）
    runtime_structural_key: Optional[StructuralAtoms]
    #: `runtime_ref.stable_key()`
    runtime_stable_key: Any
    #: `runtime_ref.semantic_key()`
    runtime_semantic_key: Any
    #: `runtime_ref` が parameter を指すか（oracle identity 用）
    runtime_is_parameter_ref: bool
    #: `("parameter", ...)` 形の stable key（provenance 用）
    parameter_runtime_key: Optional[StructuralAtoms]
    #: `runtime_ref.origin_ref.stable_key()` 側の origin（unknown 宣言用）
    runtime_stable_origin: Optional[StructuralAtoms]
    #: `storage_info.storage_identity_key()`
    storage_identity: Optional[StructuralAtoms]
    #: `storage_info` が identity key を提供していたか（「提供しているが値が
    #: 取れない」と「そもそも storage が無い」は consumer にとって別の意味）
    storage_identity_supported: bool
    #: 宣言型の signedness を 1 回だけ解決して固定する cell（型が無ければ `None`）
    declared_type: Optional["DeclaredTypeSignedness"]
    #: 生 object の有無（有無だけは意味に効く: 「型情報が無い」も情報）
    has_runtime_ref: bool
    has_data_type_obj: bool

    @property
    def declared_signedness(self) -> Optional[bool]:
        """宣言型が signed か（型が無ければ `None`）。最初の 1 回で固定される。"""

        if self.declared_type is None:
            return None
        return self.declared_type.value()


_EMPTY_SNAPSHOT = SemanticSnapshot(
    canonical_value=("none", ""),
    value_is_opaque=False,
    runtime_structural_key=None,
    runtime_stable_key=None,
    runtime_semantic_key=None,
    runtime_is_parameter_ref=False,
    parameter_runtime_key=None,
    runtime_stable_origin=None,
    storage_identity=None,
    storage_identity_supported=False,
    declared_type=None,
    has_runtime_ref=False,
    has_data_type_obj=False,
)


def build_semantic_snapshot(expr: Any) -> SemanticSnapshot:
    """生 object を 1 回だけ読んで投影を作る（凍結時に呼ばれる）。

    評価する field を node 種別で絞るのは費用のためだけで、絞った field の
    consumer はその種別に存在しない。
    """

    helpers = _helpers()
    kind = _kind_name(expr)
    value = getattr(expr, "value", None)
    runtime_ref = getattr(expr, "runtime_ref", None)

    if kind == _PHI:
        # PHI の `value` は branch container で、意味は辺（条件と値）が持つ。
        # container を値として展開すると branch ごとに object 表現へ落ちるだけ
        # なので、種別 tag だけを置く。
        canonical_value: StructuralAtoms = ("phi_branches",)
    else:
        canonical_value = canonical_value_key(value)
    structural_key = None
    stable_identity = None
    semantic_identity = None
    parameter_ref = False
    parameter_runtime_key = None
    stable_origin = None

    if runtime_ref is not None:
        structural_key = helpers._semantic_runtime_ref_key(runtime_ref)
        stable_identity = helpers._raw_stable_key_or_none(runtime_ref)
        parameter_runtime_key = helpers._parameter_runtime_ref_key(expr)
        if kind in _SEMANTIC_IDENTITY_KINDS:
            semantic_identity = runtime_semantic_key(runtime_ref)
            parameter_ref = runtime_is_parameter_ref(runtime_ref)
        if kind == _UNKNOWN:
            stable_origin = runtime_stable_origin(runtime_ref)

    storage_info = getattr(expr, "storage_info", None)
    storage_identity = None
    storage_identity_supported = callable(
        getattr(storage_info, "storage_identity_key", None)
    )
    if storage_identity_supported:
        storage_identity = helpers._expression_storage_key(expr)

    data_type_obj = getattr(expr, "data_type_obj", None)
    declared_type = None
    if data_type_obj is not None and kind in _DECLARED_TYPE_KINDS:
        declared_type = DeclaredTypeSignedness(data_type_obj)

    return SemanticSnapshot(
        canonical_value=canonical_value,
        value_is_opaque=value_key_is_opaque(canonical_value),
        runtime_structural_key=structural_key,
        runtime_stable_key=stable_identity,
        runtime_semantic_key=semantic_identity,
        runtime_is_parameter_ref=parameter_ref,
        parameter_runtime_key=parameter_runtime_key,
        runtime_stable_origin=stable_origin,
        storage_identity=storage_identity,
        storage_identity_supported=storage_identity_supported,
        declared_type=declared_type,
        has_runtime_ref=runtime_ref is not None,
        has_data_type_obj=data_type_obj is not None,
    )


def semantic_projection(expr: Any) -> SemanticSnapshot:
    """意味 consumer の唯一の入口。

    凍結済みなら保存済み snapshot をそのまま返す（生 object を読まない）。
    未凍結なら毎回その場で作る（従来と同じ値・同じ費用）。
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


#: identity の評価で「意味 identity が得られなかった」と扱う失敗の範囲。
#: 既存 consumer（oracle / unknown 宣言）の包括捕捉と同じ結果になるよう選んで
#: あり、包括捕捉を新しく増やさないために型を列挙している（`RecursionError` は
#: 深い式で実際に起きるので外せない）。
IDENTITY_EVALUATION_ERRORS = (
    AttributeError,
    LookupError,
    TypeError,
    ValueError,
    ArithmeticError,
    RecursionError,
    NotImplementedError,
)


def runtime_semantic_key(runtime_ref: Any) -> Any:
    """`runtime_ref.semantic_key()`（無い・取れないなら `None`）。"""

    semantic_key = getattr(runtime_ref, "semantic_key", None)
    if not callable(semantic_key):
        return None
    try:
        return semantic_key()
    except IDENTITY_EVALUATION_ERRORS:
        return None


def runtime_stable_key(runtime_ref: Any) -> Any:
    """`runtime_ref.stable_key()`（無い・取れないなら `None`）。"""

    return _helpers()._raw_stable_key_or_none(runtime_ref)


def runtime_is_parameter_ref(runtime_ref: Any) -> bool:
    is_parameter = getattr(runtime_ref, "is_parameter", None)
    if callable(is_parameter):
        try:
            return bool(is_parameter())
        except IDENTITY_EVALUATION_ERRORS:
            return False
    helpers = _helpers()
    stable_key = helpers._raw_stable_key_or_none(runtime_ref)
    return bool(
        isinstance(stable_key, tuple) and stable_key and stable_key[0] == "parameter"
    )


def runtime_stable_origin(runtime_ref: Any) -> Optional[StructuralAtoms]:
    """`runtime_ref` の origin（種別と origin 側 stable key）。"""

    origin_kind = getattr(runtime_ref, "origin_kind", None)
    origin_ref = getattr(runtime_ref, "origin_ref", None)
    if origin_kind is None or origin_ref is None:
        return None
    helpers = _helpers()
    if not callable(getattr(origin_ref, "stable_key", None)):
        return None
    origin_key = helpers._raw_stable_key_or_none(origin_ref)
    if origin_key is None:
        return None
    # 形は unknown 宣言 identity がそのまま使うので変えない（symbol 名が動く）。
    return (origin_kind, origin_key)


class DeclaredTypeSignedness:
    """宣言型の signedness を **最初に必要になったとき 1 回だけ** 解決して固定する。

    凍結時に前倒しで解決しない理由は 2 つある。解析が一度も触らなかった型
    object へ新しく JVM 呼び出しを足すことになり、(1) 記録済みの観測列
    （`tests/fixtures/pcode/`）に無い呼び出しが増え、(2) 使われない node の分まで
    JVM を叩く。ここで守りたいのは「生 object を読むのは 1 回だけで、以後はその
    値に固定される」ことで、いつ読むかではない。
    """

    __slots__ = ("_data_type_obj", "_resolved", "_value")

    def __init__(self, data_type_obj: Any) -> None:
        self._data_type_obj = data_type_obj
        self._resolved = False
        self._value: Optional[bool] = None

    def value(self) -> Optional[bool]:
        if not self._resolved:
            from scripts.function_tracer_pcode.core.signature import (
                get_declared_type_signedness,
            )

            self._value = bool(
                get_declared_type_signedness(
                    self._data_type_obj,
                    fallback_name=None,
                    fallback_signed=False,
                )
            )
            self._resolved = True
        return self._value

    @property
    def resolved(self) -> bool:
        """すでに解決済みか（「凍結が JVM 呼び出しを増やさない」ことの確認用）。"""

        return self._resolved


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


def local_semantic_payload(expr: Any) -> LocalPayload:
    """node の「子以外の意味 field」。`expression_key` と同じ field 集合を見る。

    ここに field を足すと candidate hash・完全比較・graph snapshot の 3 つが
    同時に追従する。`tests/unit/test_expression_structural_identity.py` の
    drift test が `expression_key` との field 集合の一致を固定している。

    凍結済みの node では凍結時に 1 回作った payload をそのまま返す。完全比較は
    同じ node の payload を何度も見る（`Condition.equals` は解析中に何万回も
    呼ばれる）ので、そのたびに tuple を組み直さない。
    """

    cached = getattr(expr, "_local_payload", None)
    if cached is not None:
        return cached
    kind = _kind_name(expr)
    projection = semantic_projection(expr)
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

    `local_payload` は digest ではなく **完全な local payload** で、digest の
    衝突だけでは一致を確定できないようにしてある（`candidate_digest` は候補の
    絞り込み専用）。
    """

    canonical_node_no: int
    candidate_digest: Optional[bytes]
    local_payload: StructuralAtoms
    ordered_edges: Tuple[Tuple[Tuple[Any, ...], Optional[int]], ...]
    comparable: bool
    identity_complete: bool


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


def walk_dag(root: Any, *, with_digests: bool = True) -> ImmutableSemanticGraph:
    """root から到達できる DAG の canonical snapshot を作る。

    費用は distinct node + 辺に比例する（同じ node を 2 回展開しない）。閉路は
    通常入力として認めない内部不整合なので `ExpressionCycleError` を投げる
    （placeholder を置いて意味処理を続けない）。
    """

    if root is None:
        return ImmutableSemanticGraph(root_no=None, nodes=())

    numbers: Dict[int, int] = {}
    order: List[Any] = []
    active: Dict[int, bool] = {}
    # (node, exiting) の明示 stack。再帰にしないのは深い式で stack を割らない
    # ためで、深さ制限を増やすより表現の性質として持つ方が安全。
    stack: List[Tuple[Any, bool]] = [(root, False)]
    edges_by_number: Dict[int, Tuple[Tuple[Tuple[Any, ...], Optional[int]], ...]] = {}
    pending_edges: Dict[int, Tuple[SemanticEdge, ...]] = {}

    while stack:
        node, exiting = stack.pop()
        node_id = id(node)
        if exiting:
            active.pop(node_id, None)
            continue
        if node_id in numbers:
            continue
        if node_id in active:
            raise ExpressionCycleError(
                "semantic graph contains a cycle: "
                f"{_kind_name(node)} {getattr(node, 'name', None)!r}"
            )
        number = len(order)
        numbers[node_id] = number
        order.append(node)
        active[node_id] = True
        edges = ordered_semantic_edges(node)
        pending_edges[number] = edges
        stack.append((node, True))
        for edge in reversed(edges):
            if edge.child is not None:
                stack.append((edge.child, False))

    for number, edges in pending_edges.items():
        edges_by_number[number] = tuple(
            (edge.label, None if edge.child is None else numbers[id(edge.child)])
            for edge in edges
        )

    digests: Dict[int, bytes] = {}
    if with_digests:
        helpers = _helpers()
        for number in range(len(order) - 1, -1, -1):
            node = order[number]
            child_digests = tuple(
                None if child_no is None else digests[child_no]
                for _label, child_no in edges_by_number[number]
            )
            digests[number] = helpers.compose_candidate_digest(node, child_digests)

    records = []
    for number, node in enumerate(order):
        payload = local_semantic_payload(node)
        records.append(
            NodeRecord(
                canonical_node_no=number,
                candidate_digest=digests.get(number),
                local_payload=payload.identity_atoms,
                ordered_edges=edges_by_number[number],
                comparable=payload.comparable,
                identity_complete=payload.identity_complete,
            )
        )

    return ImmutableSemanticGraph(root_no=0, nodes=tuple(records))
