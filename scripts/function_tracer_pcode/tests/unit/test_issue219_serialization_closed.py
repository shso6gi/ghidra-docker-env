# -*- coding: utf-8 -*-
"""検証済みの意味値の直列化は不変（Issue #219 PR-219-A、契約 C-RS2）。

`lifecycle >= VALIDATED` で `serialization_closed(value)` が真の意味値では、LEGACY 表現
（`to_dict()` / snapshot の木）が **不変な状態だけの関数** になる。PR-22-B の isolation
契約（structural key・solver query identity・SMT・幅は凍結後の生 object の変化で動かない）を
LEGACY 表現へ広げたもの。ここで固定するのは次のこと:

* T-A1: 凍結は表現を変えない（凍結の前と後で `to_dict()` が同じ）。
* T-A3: closed になるのは、表現が読む状態がすべて不変なときだけ。可変な runtime ref・
  可変な容器・opaque な値・closed でない子・写し取れない storage を含む値は closed でない。
* T-A5: 表現が読む field はすべて、lifecycle の表（`EXPRESSION_SERIALIZATION_INPUTS` /
  `CONDITION_SERIALIZATION_INPUTS`）に規則があるか、凍結時の派生値である（静的な監査）。
  規則の無い field を読むようになったら、closed の判定がその field を見落とすので落ちる。
* T-A6: 凍結が失敗したら、派生値（写しと closed の bit）は 1 つも残らない。

T-A2（凍結後の `StorageInfo` の書き換え）は `test_semantic_snapshot_isolation.py`、
T-A4（複製・派生が派生値を引き継がない）は `test_semantic_lifecycle_copy.py` にある。
"""

from __future__ import annotations

import ast
import dataclasses
import enum
import inspect
import pathlib
import random
import textwrap
from typing import Any, Optional, Tuple

import pytest

from scripts.function_tracer_pcode.core import condition as condition_module
from scripts.function_tracer_pcode.core import expression as expression_module
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.errors import ExpressionCycleError, reset_pair_failure_scopes
from scripts.function_tracer_pcode.core.expression import (
    Expression,
    ExpressionType,
    estimate_legacy_dict_bytes,
)
from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, JsonEncodingPolicy
from scripts.function_tracer_pcode.core.render_output import utf8_length
from scripts.function_tracer_pcode.core.runtime_refs import PcodeOpRef
from scripts.function_tracer_pcode.core.semantic_freeze import (
    SERIALIZATION_CLOSURE_RULES,
    freeze_expression,
)
from scripts.function_tracer_pcode.core.semantic_lifecycle import (
    CONDITION_SERIALIZATION_INPUTS,
    DERIVED_STATE_FIELDS,
    EXPRESSION_SERIALIZATION_INPUTS,
    SerializationInput,
    serialization_closed,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.tests.unit._publication import published


@pytest.fixture(autouse=True)
def _clean_ledger_stack():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


# ---------------------------------------------------------------------------
# 材料
# ---------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
class _FrozenRef:
    """深く不変な runtime ref（scalar / enum / tuple / 式だけを持つ）。"""

    key: Tuple[Any, ...]
    kind: ExpressionType = ExpressionType.UNKNOWN
    inner: Optional[Expression] = None


@dataclasses.dataclass(frozen=True)
class _FrozenRefWithList:
    """frozen だが可変な容器を持つ ref（field は差し替えられないが、中身は変わる）。"""

    items: list


@dataclasses.dataclass(frozen=True)
class _FrozenRefWithDict:
    table: dict


class _MutableRef:
    def __init__(self, key: Any) -> None:
        self.key = key

    def stable_key(self) -> Any:
        return self.key


def _storage(name: str = "x0", offset: int = 8) -> StorageInfo:
    return StorageInfo(
        is_register=True,
        space_name="register",
        offset=offset,
        size=4,
        register_name=name,
        base_register_name=name,
    )


def _parameter(name: str = "a", storage: Optional[StorageInfo] = None, **fields: Any) -> Expression:
    return Expression.parameter(name, 0, size=4, storage_info=storage or _storage(name), **fields)


def _closed_expression() -> Expression:
    guard = Condition(Expression.binary_op("INT_LESS", _parameter("a"), Expression.constant(7, size=4)))
    memory = Expression.memory(_parameter("p"), size=4, read_order_key=3, runtime_ref=_FrozenRef(("mem", 1)))
    return Expression.phi([(guard, memory), (None, Expression.constant(0, size=4))])


def _written_bytes(value: Any) -> int:
    return utf8_length(JsonEncodingPolicy.dumps(RESULT_JSON_POLICY, value))


# ---------------------------------------------------------------------------
# T-A1: 凍結の前と後で表現が同じ
# ---------------------------------------------------------------------------


def _random_expression(rng: random.Random, depth: int, pool: list) -> Expression:
    """storage / PHI / runtime ref を含む式をランダムに組む（共有 DAG になるよう pool から再利用する）。"""

    if pool and rng.random() < 0.25:
        return rng.choice(pool)
    if depth <= 0:
        choice = rng.randrange(6)
        if choice == 0:
            node = Expression.constant(rng.randrange(-5, 300), size=rng.choice((1, 4, 8)))
        elif choice == 1:
            name = rng.choice("abcd")
            node = Expression.parameter(
                name, "abcd".index(name), size=4,
                storage_info=_storage("x%d" % rng.randrange(8), offset=rng.randrange(64)),
            )
        elif choice == 2:
            node = Expression.variable(
                "v%d" % rng.randrange(4), size=8,
                storage_info=StorageInfo(space_name="stack", offset=-rng.randrange(1, 64), size=8),
            )
        elif choice == 3:
            node = Expression.unknown(
                "u%d" % rng.randrange(4),
                runtime_ref=_FrozenRef(("unknown", rng.randrange(4)), ExpressionType.UNKNOWN),
            )
        elif choice == 4:
            node = Expression.unknown(
                "op",
                runtime_ref=PcodeOpRef(address_offset=rng.randrange(1 << 16), mnemonic="INT_ADD", input_sizes=(4, 4)),
            )
        else:
            node = Expression(ExpressionType.LITERAL, value=("lit", rng.randrange(4)), size=4)
    else:
        choice = rng.randrange(5)
        if choice == 0:
            node = Expression.binary_op(
                rng.choice(("INT_ADD", "INT_SUB", "INT_AND")),
                _random_expression(rng, depth - 1, pool),
                _random_expression(rng, depth - 1, pool),
            )
        elif choice == 1:
            node = Expression.unary_op("INT_NEGATE", _random_expression(rng, depth - 1, pool))
        elif choice == 2:
            guard = Condition(
                Expression.binary_op(
                    "INT_LESS", _random_expression(rng, depth - 1, pool), Expression.constant(3, size=4)
                ),
                negated=rng.random() < 0.5,
            )
            node = Expression.phi(
                [(guard, _random_expression(rng, depth - 1, pool)), (None, _random_expression(rng, depth - 1, pool))]
            )
        elif choice == 3:
            node = Expression.memory(
                _random_expression(rng, depth - 1, pool), size=4, read_order_key=rng.randrange(8),
                runtime_ref=_FrozenRef(("mem", rng.randrange(4)), inner=_random_expression(rng, 0, pool)),
            )
        else:
            node = Expression.call("f%d" % rng.randrange(3), [_random_expression(rng, depth - 1, pool)])
    pool.append(node)
    return node


@pytest.mark.parametrize("seed", range(40))
def test_freezing_does_not_change_the_legacy_representation(seed):
    rng = random.Random(seed)
    expr = _random_expression(rng, 4, [])
    before = expr.to_dict()

    freeze_expression(expr)

    assert expr.is_frozen
    assert expr.to_dict() == before
    # 見積もり（凍結済み node は写しから測る）と実出力も食い違わない
    assert estimate_legacy_dict_bytes(expr, work=None) == _written_bytes(before)
    # 生成した式はどれも不変な材料だけで出来ているので closed になる
    assert serialization_closed(expr) is True


def test_publishing_a_mock_analysis_does_not_change_its_representation():
    from scripts.function_tracer_pcode.core.analysis import ReturnInfo
    from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
    from scripts.function_tracer_pcode.tests.unit._publication import published_raw_analysis

    analysis = create_mock_analysis(
        "f",
        returns=[
            ReturnInfo(address="0x00401000", conditions=[], value=_closed_expression()),
            ReturnInfo(
                address="0x00401010",
                conditions=[Condition(Expression.binary_op("INT_EQUAL", _parameter("b"), Expression.constant(0, 4)))],
                value=_parameter("b"),
            ),
        ],
    )
    before = analysis.to_dict()

    published_raw_analysis(analysis)

    assert all(ret.value.is_published for ret in analysis.returns)
    assert analysis.to_dict() == before


# ---------------------------------------------------------------------------
# T-A3: closed になるもの・ならないもの
# ---------------------------------------------------------------------------


def _mutable_runtime_ref():
    return Expression.unknown("u", runtime_ref=_MutableRef(("u", 1)))


def _frozen_ref_holding_a_list():
    return Expression.unknown("u", runtime_ref=_FrozenRefWithList(items=[1, 2]))


def _frozen_ref_holding_a_dict():
    return Expression.unknown("u", runtime_ref=_FrozenRefWithDict(table={"k": 1}))


def _frozen_ref_holding_an_unclosed_expression():
    return Expression.unknown("u", runtime_ref=_FrozenRef(("u",), inner=_mutable_runtime_ref()))


def _frozen_ref_with_hidden_state():
    """frozen dataclass だが field 以外の状態（後から足した cache）を持つ ref。"""

    ref = _FrozenRef(("u",))
    object.__setattr__(ref, "_cache", [])
    return Expression.unknown("u", runtime_ref=ref)


def _opaque_value():
    return Expression(ExpressionType.LITERAL, value=object(), size=4)


def _mutable_container_value():
    return Expression(ExpressionType.LITERAL, value=[1, 2], size=4)


def _mutable_scalar_field():
    return Expression(ExpressionType.CONSTANT, value=1, size=4, name=["n"])


def _unclosed_child():
    return Expression.binary_op("INT_ADD", _mutable_runtime_ref(), Expression.constant(1, 4))


def _unclosed_phi_condition():
    guard = Condition(Expression.binary_op("INT_LESS", _mutable_runtime_ref(), Expression.constant(1, 4)))
    return Expression.phi([(guard, Expression.constant(1, 4)), (None, Expression.constant(2, 4))])


def _non_condition_phi_guard():
    return Expression.phi([(Expression.constant(1, 1), Expression.constant(1, 4)), (None, Expression.constant(2, 4))])


def _uncapturable_storage():
    return _parameter("a", storage=StorageInfo(space_name="register", size=4, register_name=["x0"]))


def _storage_of_another_type():
    class _LookalikeStorage:
        def storage_identity_key(self):
            return ("register", 0)

    return Expression.parameter("a", 0, size=4, storage_info=_LookalikeStorage())


def _runtime_ref_that_reaches_back():
    node = Expression.unknown("u")
    node.__dict__["runtime_ref"] = _FrozenRef(("back",), inner=node)
    return node


class _ListValuedEnum(enum.Enum):
    """値が list の enum（member は同じ object のまま、値の list が書き換わる）。"""

    MEMBER = [1]


class _TupleValuedEnum(enum.Enum):
    MEMBER = ("a", 1)


class _Flavor(enum.IntEnum):
    SWEET = 1


class _StatefulInt(int):
    """instance の `__dict__` を持つ int の subclass（その状態を読む method を持ち得る）。"""


class _SlottedInt(int):
    __slots__ = ()


class _TupleSubclass(tuple):
    pass


@dataclasses.dataclass(frozen=True)
class _UndeclaredRecord:
    """直列化の protocol（`json_items`）を持つが、field だけの関数だと宣言していない ref。"""

    key: Tuple[Any, ...]

    def json_items(self):
        yield "key", _MUTABLE_REGISTRY.get(self.key, self.key)


_MUTABLE_REGISTRY: dict = {}


@dataclasses.dataclass(frozen=True)
class _DeclaredRecord:
    """protocol を持ち、field だけの関数だと宣言した ref（宣言は静的な監査の対象）。"""

    __serialization_determined_by_fields__ = True

    key: Tuple[Any, ...]

    def json_items(self):
        yield "key", self.key


@dataclasses.dataclass(frozen=True)
class _SubclassOfDeclaredRecord(_DeclaredRecord):
    """宣言した型の subclass（宣言は継承しない: protocol を上書きし得る）。"""

    def json_items(self):
        yield "key", _MUTABLE_REGISTRY.get(self.key, self.key)


class _ExpressionSubclass(Expression):
    """表現を作る method を上書きし得る式の型（表と規則が述べるのは `Expression` の表現だけ）。"""


def _list_valued_enum_value():
    return Expression(ExpressionType.LITERAL, value=_ListValuedEnum.MEMBER, size=4)


class _AttachedStateEnum(enum.Enum):
    MEMBER = ("b", 2)


#: member の instance に後から載せた可変な状態（enum の method が読み得る）
_AttachedStateEnum.MEMBER.attached = []


def _enum_member_with_attached_state():
    return Expression(ExpressionType.LITERAL, value=_AttachedStateEnum.MEMBER, size=4)


def _stateful_int_value():
    return Expression(ExpressionType.CONSTANT, value=_StatefulInt(3), size=4)


def _tuple_subclass_value():
    return Expression(ExpressionType.LITERAL, value=_TupleSubclass((1, 2)), size=4)


def _undeclared_record_ref():
    return Expression.unknown("u", runtime_ref=_UndeclaredRecord(("k",)))


def _subclass_of_declared_record_ref():
    return Expression.unknown("u", runtime_ref=_SubclassOfDeclaredRecord(("k",)))


def _expression_subclass():
    return _ExpressionSubclass(ExpressionType.CONSTANT, value=1, size=4)


def _storage_with_a_stateful_scalar():
    storage = _storage("x0")
    storage.offset = _StatefulInt(8)
    return _parameter("a", storage=storage)


def _node_missing_a_represented_field():
    """表現が読む field（`opcode`）を instance に持たない node（読めば class の値 = 共有の状態）。"""

    node = Expression.constant(1, size=4)
    fields = dict(node.__dict__)
    fields.pop("opcode")
    partial = Expression.__new__(Expression)
    partial.__dict__.update(fields)
    return partial


_NOT_CLOSED = {
    "node_missing_a_represented_field": _node_missing_a_represented_field,
    "list_valued_enum_value": _list_valued_enum_value,
    "enum_member_with_attached_state": _enum_member_with_attached_state,
    "stateful_int_value": _stateful_int_value,
    "tuple_subclass_value": _tuple_subclass_value,
    "undeclared_record_ref": _undeclared_record_ref,
    "subclass_of_declared_record_ref": _subclass_of_declared_record_ref,
    "expression_subclass": _expression_subclass,
    "storage_with_a_stateful_scalar": _storage_with_a_stateful_scalar,
    "mutable_runtime_ref": _mutable_runtime_ref,
    "frozen_ref_holding_a_list": _frozen_ref_holding_a_list,
    "frozen_ref_holding_a_dict": _frozen_ref_holding_a_dict,
    "frozen_ref_holding_an_unclosed_expression": _frozen_ref_holding_an_unclosed_expression,
    "frozen_ref_with_hidden_state": _frozen_ref_with_hidden_state,
    "opaque_value": _opaque_value,
    "mutable_container_value": _mutable_container_value,
    "mutable_scalar_field": _mutable_scalar_field,
    "unclosed_child": _unclosed_child,
    "unclosed_phi_condition": _unclosed_phi_condition,
    "non_condition_phi_guard": _non_condition_phi_guard,
    "uncapturable_storage": _uncapturable_storage,
    "storage_of_another_type": _storage_of_another_type,
    "runtime_ref_that_reaches_back": _runtime_ref_that_reaches_back,
}


@pytest.mark.parametrize("build", list(_NOT_CLOSED.values()), ids=list(_NOT_CLOSED))
def test_values_whose_representation_reads_mutable_state_are_not_closed(build):
    expr = build()
    freeze_expression(expr)

    assert expr.is_frozen
    assert serialization_closed(expr) is False


def test_a_parent_of_an_unclosed_value_is_not_closed_either():
    leaf = _mutable_runtime_ref()
    parent = Expression.unary_op("INT_NEGATE", Expression.binary_op("INT_ADD", leaf, Expression.constant(1, 4)))
    freeze_expression(parent)

    assert serialization_closed(leaf) is False
    assert serialization_closed(parent) is False


_CLOSED = {
    "constant": lambda: Expression.constant(5, size=4),
    "parameter_with_storage": lambda: _parameter("a"),
    "variable_without_storage": lambda: Expression.variable("v", size=8),
    "tuple_value": lambda: Expression(ExpressionType.LITERAL, value=("a", 1, (2, 3)), size=4),
    "frozen_runtime_ref": lambda: Expression.unknown("u", runtime_ref=_FrozenRef(("u", 1))),
    "pcode_op_ref": lambda: Expression.unknown("op", runtime_ref=PcodeOpRef(address_offset=16, mnemonic="COPY")),
    "frozen_ref_holding_a_closed_expression": lambda: Expression.unknown(
        "u", runtime_ref=_FrozenRef(("u",), inner=_parameter("a"))
    ),
    "phi_with_closed_conditions": _closed_expression,
    "tuple_valued_enum": lambda: Expression(ExpressionType.LITERAL, value=_TupleValuedEnum.MEMBER, size=4),
    "int_enum_value": lambda: Expression(ExpressionType.LITERAL, value=_Flavor.SWEET, size=4),
    "slotted_int_value": lambda: Expression(ExpressionType.CONSTANT, value=_SlottedInt(3), size=4),
    "declared_record_ref": lambda: Expression.unknown("u", runtime_ref=_DeclaredRecord(("k", 1))),
}


@pytest.mark.parametrize("build", list(_CLOSED.values()), ids=list(_CLOSED))
def test_values_built_only_from_immutable_state_are_closed(build):
    expr = build()
    freeze_expression(expr)

    assert serialization_closed(expr) is True


def test_closed_needs_validation():
    """CONSTRUCTION の値は不変な材料だけで出来ていても closed でない（まだ書き換えられる）。"""

    expr = _parameter("a")

    assert serialization_closed(expr) is False
    freeze_expression(expr)
    assert serialization_closed(expr) is True


def test_a_condition_is_closed_exactly_when_its_expression_is():
    closed = Condition(Expression.binary_op("INT_LESS", _parameter("a"), Expression.constant(1, 4)))
    unclosed = Condition(Expression.binary_op("INT_LESS", _mutable_runtime_ref(), Expression.constant(1, 4)))

    assert serialization_closed(closed) is True
    assert serialization_closed(unclosed) is False
    # 反転も同じ式を持つので同じ答え（公開の例外とは無関係に、派生値は作り直す）
    assert serialization_closed(published(closed).negate()) is True
    assert serialization_closed(unclosed.negate()) is False


def test_closed_values_keep_their_representation_under_raw_mutation():
    """closed の意味: 表現が読む生の状態を書き換えても表現は動かない（C-RS2 の本文）。"""

    storage = _storage("x0")
    inner_storage = _storage("x1")
    expr = Expression.binary_op(
        "INT_ADD",
        _parameter("a", storage=storage),
        Expression.unknown("u", runtime_ref=_FrozenRef(("u",), inner=_parameter("b", storage=inner_storage))),
    )
    freeze_expression(expr)
    assert serialization_closed(expr) is True
    before = expr.to_dict()

    for victim in (storage, inner_storage):
        victim.register_name = "zz"
        victim.offset = 1024
        victim.is_register = False

    assert expr.to_dict() == before


@pytest.mark.parametrize("name", ["_storage_payload", "_serialization_closed", "_snapshot"])
def test_derived_state_of_a_validated_value_cannot_be_reassigned(name):
    """派生値も検証済みの状態の一部: 凍結後の代入は（意味 field と同じく）内部バグとして拒む。"""

    from scripts.function_tracer_pcode.core.errors import FrozenExpressionError

    expr = freeze_expression(_parameter("a"))
    condition = Condition(Expression.binary_op("INT_LESS", _parameter("b"), Expression.constant(1, 4)))
    before = expr.to_dict()

    for value in (expr, condition):
        with pytest.raises(FrozenExpressionError):
            setattr(value, name, None)
    assert expr.to_dict() == before
    assert serialization_closed(expr) is True and serialization_closed(condition) is True


def test_unclosed_values_may_still_follow_the_live_object():
    """closed でない値について C-RS2 は何も約束しない（従来どおり生 object を描く）。

    closed の判定が「表現が本当に動き得る値」を closed と呼ばないことの対照。
    """

    @dataclasses.dataclass
    class _Record:
        key: Any

    record = _Record(key=1)
    expr = Expression.unknown("u", runtime_ref=record)
    freeze_expression(expr)
    before = expr.to_dict()

    record.key = 2

    assert serialization_closed(expr) is False
    assert expr.to_dict() != before


# ---------------------------------------------------------------------------
# T-A5: 表現が読む field の静的な監査
# ---------------------------------------------------------------------------

#: 表現の入口（内容を作る method）。`to_dict` / `__json_tree__` / `__json_tree_metered__` はここへ入る。
_EXPRESSION_ENTRIES = ("_to_dict",)
#: 辿らない method / 関数と、辿らなくてよい理由（理由は下の test が実行で確かめる）。
_EXPRESSION_ESCAPES = {
    "structural_key": "閉路の経路だけで呼ぶ（検証済みの graph には閉路が無い）",
    "_node_local_bytes": "予算へ数える byte だけを返す（内容は `_to_dict_active` が作る）",
}
#: 表現を作る method が局所の値から読む属性と、その分類。分類の無い読みを足すと監査が落ちる。
_CHILD = "子の表現（子の `_to_dict`。子が closed であることを OPERANDS / VALUE / EXPRESSION が求める）"
_CONDITION_FIELD = "PHI の branch の条件の field（`CONDITION_SERIALIZATION_INPUTS`）"
_MACHINERY = "直列化の作業量・予算・出力の容器（意味値の状態ではない）"
_EXPRESSION_LOCAL_READS = {
    ("op", "_to_dict"): _CHILD,
    ("value", "_to_dict"): _CHILD,
    ("condition_expression", "_to_dict"): _CHILD,
    ("condition", "expression"): _CONDITION_FIELD,
    ("condition", "negated"): _CONDITION_FIELD,
    ("expr_type", "_name_"): "enum の member の名前（class の定義 = code。SCALAR の規則が型を固定する）",
    ("storage_payload", "to_dict"): "凍結時の写し（`FrozenStorageRecord`、STORAGE の規則）",
    ("storage_info", "to_dict"): "未凍結の node だけが読む生の storage（closed にならない経路）",
    ("work", "charge"): _MACHINERY,
    ("work", "remaining"): _MACHINERY,
    ("work", "runtime_ref_memo"): _MACHINERY,
    ("memo", "get"): _MACHINERY,
    ("active", "add"): _MACHINERY,
    ("active", "remove"): _MACHINERY,
    ("collect", "append"): _MACHINERY,
    ("collect", "extend"): _MACHINERY,
    ("branches", "append"): _MACHINERY,
    ("rendered", "append"): _MACHINERY,
}


def _expression_reads():
    from scripts.function_tracer_pcode.tests.unit._representation_read_audit import audit_representation_reads

    return audit_representation_reads(
        Expression, _EXPRESSION_ENTRIES, escapes=_EXPRESSION_ESCAPES, local_reads=_EXPRESSION_LOCAL_READS,
    )


def test_every_field_the_expression_representation_reads_has_a_closure_rule():
    fields, violations, used = _expression_reads()

    assert violations == []
    unclassified = fields - set(EXPRESSION_SERIALIZATION_INPUTS) - set(DERIVED_STATE_FIELDS)
    assert unclassified == set(), (
        "the LEGACY representation reads fields with no serialization-closure rule; add each to "
        "EXPRESSION_SERIALIZATION_INPUTS (semantic_lifecycle) so freeze decides whether it is immutable: "
        f"{sorted(unclassified)}"
    )
    # 表に在る field は実際に読まれている（古い行を残さない）。分類表の行も同じ
    assert set(EXPRESSION_SERIALIZATION_INPUTS) <= fields
    assert set(used) == set(_EXPRESSION_LOCAL_READS)
    # 規則の対象は凍結後に代入も削除もできない意味 field（書き換えで規則の前提が崩れない）
    assert set(EXPRESSION_SERIALIZATION_INPUTS) <= set(expression_module.SEMANTIC_FIELDS)


def test_every_field_the_condition_representation_reads_has_a_closure_rule():
    from scripts.function_tracer_pcode.tests.unit._representation_read_audit import audit_representation_reads

    # 単独の条件は `json_items` が出し、PHI の branch の条件は `_to_dict_active` が直接読む
    fields, violations, _used = audit_representation_reads(Condition, ("json_items",), escapes={}, local_reads={})
    phi_reads = {attr for (name, attr), label in _EXPRESSION_LOCAL_READS.items() if label == _CONDITION_FIELD}

    assert violations == []
    assert fields | phi_reads == set(CONDITION_SERIALIZATION_INPUTS)
    assert set(CONDITION_SERIALIZATION_INPUTS) <= set(condition_module.SEMANTIC_FIELDS)


def test_escaped_methods_are_not_reached_from_a_validated_graph(monkeypatch):
    """辿らない method の理由を実行で確かめる: 検証済みの graph の表現は、それを 1 度も呼ばない。"""

    def _forbidden(*_args, **_kwargs):
        raise AssertionError("an escaped method was reached while serializing a validated graph")

    exprs = []
    for seed in range(12):
        expr = _random_expression(random.Random(seed), 4, [])
        freeze_expression(expr)
        exprs.append(expr)
    monkeypatch.setattr(Expression, "structural_key", _forbidden)
    for expr in exprs:
        expr.to_dict()


class _AuditProbe:
    """監査そのものの反例（監査が見逃すと、表に無い依存が closed の判定から漏れる）。"""

    size = 0

    def _to_dict(self):
        return {"size": self.size}

    def via_getattr(self):
        return {"hidden": getattr(self, "hidden", None)}

    def via_dynamic_getattr(self, name):
        return getattr(self, name)

    def via_vars(self):
        return dict(vars(self))

    def via_dict(self):
        return self.__dict__.get("hidden")

    def via_escape(self):
        return _read_hidden(self)

    def via_alias(self):
        node = self
        return node.hidden

    def via_helper(self):
        return self._helper()

    def _helper(self):
        return getattr(self, "helper_hidden", None)

    def via_local_read(self, child):
        return child.hidden


def _read_hidden(value):
    return value.hidden


@pytest.mark.parametrize(
    "entry,expected_field,expect_violation",
    [
        ("via_getattr", "hidden", False),
        ("via_helper", "helper_hidden", False),
        ("via_dynamic_getattr", None, True),
        ("via_vars", None, True),
        ("via_dict", None, True),
        ("via_escape", None, True),
        ("via_alias", None, True),
        ("via_local_read", None, True),
    ],
)
def test_the_read_audit_enumerates_or_rejects_every_form_of_read(entry, expected_field, expect_violation):
    from scripts.function_tracer_pcode.tests.unit._representation_read_audit import audit_representation_reads

    fields, violations, _used = audit_representation_reads(_AuditProbe, (entry,), escapes={}, local_reads={})

    if expected_field is not None:
        assert expected_field in fields
    assert bool(violations) is expect_violation, violations


def test_every_serialization_input_kind_has_exactly_one_closure_rule():
    assert set(SERIALIZATION_CLOSURE_RULES) == set(SerializationInput)
    for table in (EXPRESSION_SERIALIZATION_INPUTS, CONDITION_SERIALIZATION_INPUTS):
        assert all(type(kind) is SerializationInput for kind in table.values())


def test_the_closure_derivation_lives_only_in_the_lifecycle_owner():
    """closed の規則を consumer 側で再実装しない（owner は semantic_freeze / semantic_lifecycle）。"""

    names = {"_serialization_closed", "_storage_payload"}
    root = pathlib.Path(expression_module.__file__).resolve().parents[1]
    owners = {root / "core" / "semantic_freeze.py", root / "core" / "semantic_lifecycle.py"}
    writers = []
    for path in sorted(root.rglob("*.py")):
        if path in owners or "tests" in path.relative_to(root).parts:
            continue
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
            # 名前を文字列で持つ（`__dict__[...]`・`getattr`・表）か、属性へ代入する
            if isinstance(node, ast.Constant) and node.value in names:
                writers.append(f"{path.relative_to(root)}:{node.lineno}")
            if isinstance(node, ast.Attribute) and node.attr in names and not isinstance(node.ctx, ast.Load):
                writers.append(f"{path.relative_to(root)}:{node.lineno}")
    assert writers == []


# ---------------------------------------------------------------------------
# T-A6: 凍結の失敗では派生値が残らない
# ---------------------------------------------------------------------------


def _assert_nothing_committed(*values: Any) -> None:
    for value in values:
        assert value.is_frozen is False
        for name in ("_serialization_closed", "_storage_payload"):
            assert name not in value.__dict__, (type(value).__name__, name)


def test_a_failed_freeze_leaves_no_serialization_state():
    leaf = _parameter("a")
    loop = Expression.unary_op("BOOL_NEGATE", leaf)
    loop.__dict__["operands"] = [loop]
    root = Expression.binary_op("INT_ADD", leaf, loop)

    with pytest.raises(ExpressionCycleError):
        freeze_expression(root)

    _assert_nothing_committed(root, loop, leaf)


def test_a_cycle_inside_a_runtime_ref_closure_leaves_no_serialization_state():
    """closure の奥（runtime ref が抱える式）で失敗しても、root を含めて何も確定しない。"""

    inner = Expression.unary_op("BOOL_NEGATE", _parameter("b"))
    inner.__dict__["operands"] = [inner]
    root = Expression.binary_op(
        "INT_ADD", _parameter("a"), Expression.unknown("u", runtime_ref=_FrozenRef(("u",), inner=inner))
    )

    with pytest.raises(ExpressionCycleError):
        freeze_expression(root)

    _assert_nothing_committed(root, *root.operands, inner)


# ---------------------------------------------------------------------------
# closed ⇒ 属性の protocol ではどこからも書き換えられない（レビューで再現した反例を含む）
# ---------------------------------------------------------------------------


def _snapshot_fingerprint_of(expr: Expression) -> str:
    from scripts.function_tracer_pcode.core.analysis import ReturnInfo
    from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot
    from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
    from scripts.function_tracer_pcode.tests.unit._publication import published_raw_analysis

    analysis = published_raw_analysis(
        create_mock_analysis("f", returns=[ReturnInfo(address="0x00401000", conditions=[], value=expr)])
    )
    return AnalysisSnapshot.from_function_analysis(analysis).semantic_fingerprint


def _reachable_semantic_values(root: Any) -> list:
    """root から表現が辿る式と条件（子・PHI の条件・runtime ref が抱える式）。"""

    from scripts.function_tracer_pcode.core.semantic_snapshot import ordered_semantic_edges

    found, seen, pending = [], set(), [root]
    while pending:
        value = pending.pop()
        if id(value) in seen:
            continue
        seen.add(id(value))
        found.append(value)
        if isinstance(value, Condition):
            pending.append(value.expression)
            continue
        pending.extend(edge.child for edge in ordered_semantic_edges(value) if edge.child is not None)
        for branch in value.__dict__.get("value") or () if value.expr_type is ExpressionType.PHI else ():
            if branch.condition is not None:
                pending.append(branch.condition)
        ref = value.__dict__.get("runtime_ref")
        if isinstance(ref, _FrozenRef) and ref.inner is not None:
            pending.append(ref.inner)
    return found


def _attribute_protocol_mutations(value: Any):
    """属性の protocol（`__dict__` を直接書かない）で試せる書き換え。"""

    from scripts.function_tracer_pcode.core.semantic_lifecycle import NON_INHERITED_FIELDS

    semantic = condition_module.SEMANTIC_FIELDS if isinstance(value, Condition) else expression_module.SEMANTIC_FIELDS
    for name in sorted(set(semantic) | set(NON_INHERITED_FIELDS)):
        yield f"set {name}", lambda value=value, name=name: setattr(value, name, None)
        yield f"del {name}", lambda value=value, name=name: delattr(value, name)
    yield "set _frozen=False", lambda value=value: setattr(value, "_frozen", False)
    yield "set __class__", lambda value=value: setattr(value, "__class__", _ExpressionSubclass if isinstance(value, Expression) else type("C", (Condition,), {}))


@pytest.mark.parametrize("seed", range(8))
def test_no_attribute_mutation_reachable_from_a_closed_value_changes_its_representation(seed):
    """closed な値から辿れるどの式・条件にも、属性の protocol の書き換えは通らない。

    レビューで再現した `del expr._storage_payload`・`del condition.negated`・子の
    `leaf._frozen = False; leaf.value = 2` はこの表の行。通れば表現と fingerprint が動く。
    """

    from scripts.function_tracer_pcode.core.errors import FrozenExpressionError

    expr = _random_expression(random.Random(seed), 4, [])
    fingerprint = _snapshot_fingerprint_of(expr)
    assert serialization_closed(expr) is True
    before = expr.to_dict()

    attempted = 0
    for value in _reachable_semantic_values(expr):
        for label, mutate in _attribute_protocol_mutations(value):
            attempted += 1
            with pytest.raises(FrozenExpressionError):
                mutate()
    # 生の storage を書き換えても（写しから描くので）動かない
    for value in _reachable_semantic_values(expr):
        storage = value.__dict__.get("storage_info") if isinstance(value, Expression) else None
        if storage is not None:
            storage.register_name = "mutated"
            storage.offset = 999

    assert attempted > 0
    assert serialization_closed(expr) is True
    assert expr.to_dict() == before
    assert _snapshot_fingerprint_of(expr) == fingerprint


def test_the_reported_enum_counterexample_is_not_closed():
    """レビュー 1: list を値に持つ enum を値にした式は closed でない（fingerprint は実際に動く）。"""

    class _Local(enum.Enum):
        MEMBER = [1]

    expr = Expression(ExpressionType.LITERAL, value=_Local.MEMBER, size=4)
    fingerprint = _snapshot_fingerprint_of(expr)

    _Local.MEMBER.value.append(2)

    assert serialization_closed(expr) is False
    assert _snapshot_fingerprint_of(expr) != fingerprint


def test_lifecycle_fields_cannot_be_written_through_attributes_in_any_state():
    """状態と派生値は構築中でも属性では書けない（書くのは lifecycle の commit だけ）。"""

    from scripts.function_tracer_pcode.core.errors import FrozenExpressionError
    from scripts.function_tracer_pcode.core.semantic_lifecycle import NON_INHERITED_FIELDS

    expr = _parameter("a")
    for name in NON_INHERITED_FIELDS:
        with pytest.raises(FrozenExpressionError):
            setattr(expr, name, True)
    assert expr.is_frozen is False
    # 意味 field と補助の属性は構築中は自由（組み立て・精緻化の途中）
    expr.size = 8
    expr.debug_note = "x"
    del expr.debug_note
    freeze_expression(expr)
    expr.debug_note = "after freeze"  # 意味にも表現にも入らない属性は凍結後も置ける
    del expr.debug_note
    assert serialization_closed(expr) is True


# ---------------------------------------------------------------------------
# 宣言（field だけで表現が決まる型）の静的な監査
# ---------------------------------------------------------------------------


def _package_types():
    import importlib
    import pkgutil

    import scripts.function_tracer_pcode as package

    seen = []
    for module_info in pkgutil.walk_packages(package.__path__, package.__name__ + "."):
        if ".tests" in module_info.name:
            continue
        module = importlib.import_module(module_info.name)
        for value in vars(module).values():
            if isinstance(value, type) and value.__module__ == module.__name__ and value not in seen:
                seen.append(value)
    return seen


def test_every_declared_type_passes_the_purity_audit():
    from scripts.function_tracer_pcode.core.semantic_lifecycle import (
        FIELD_DETERMINED_SERIALIZATION_MARKER,
        serialization_protocol_methods,
    )
    from scripts.function_tracer_pcode.tests.unit._serialization_purity_audit import PurityAudit

    declared = [kind for kind in _package_types() if kind.__dict__.get(FIELD_DETERMINED_SERIALIZATION_MARKER) is True]
    assert declared, "no type declares a field-determined serialization"
    failures = {}
    for kind in declared:
        protocols = serialization_protocol_methods(kind)
        violations = PurityAudit().audit_type(kind, protocols) if protocols else ["declares without a protocol"]
        if violations:
            failures[kind.__qualname__] = violations
    assert failures == {}


#: 直列化の protocol を持つ runtime ref の型のうち、宣言していない型と理由（宣言できない = 監査が
#: 拒否する code を持つ）。宣言しない型の値を抱える式は closed にならない（遅くなるだけ）。
_UNDECLARED_REF_TYPES = {
    "CallModelCandidateRef": "`_jsonable_key_source` が field の要素を `raw()` で置く（codec が要素の型の規則で写す）",
    "ComposedLoopSummaryRef": "`side_effect_profile` が表現の途中で別の ref を組み立てる",
    "ExpansionBudgetTruncation": "field でない instance 状態（`_owner_scope_value` など）を読む",
}


def test_every_runtime_ref_type_with_a_protocol_is_declared_or_explained():
    """ref の型を足したら、宣言するか、宣言しない理由をここへ書く（黙って closed を失わない）。"""

    from scripts.function_tracer_pcode.core.semantic_lifecycle import (
        FIELD_DETERMINED_SERIALIZATION_MARKER,
        serialization_protocol_methods,
    )

    prefixes = ("scripts.function_tracer_pcode.core.runtime_refs.", "scripts.function_tracer_pcode.core.call_target")
    undeclared = {
        kind.__qualname__
        for kind in _package_types()
        if kind.__module__.startswith(prefixes)
        and dataclasses.is_dataclass(kind)
        and serialization_protocol_methods(kind)
        and kind.__dict__.get(FIELD_DETERMINED_SERIALIZATION_MARKER) is not True
    }
    assert undeclared == set(_UNDECLARED_REF_TYPES)


_AUDIT_STATE: list = []


@dataclasses.dataclass(frozen=True)
class _ReadsModuleState:
    key: int

    def json_items(self):
        yield "key", _AUDIT_STATE


@dataclasses.dataclass(frozen=True)
class _ReadsClassState:
    registry = {}
    key: int = 0

    def json_items(self):
        yield "key", self.registry


@dataclasses.dataclass(frozen=True)
class _RawOfAField:
    key: Any

    def json_items(self):
        from scripts.function_tracer_pcode.core.json_encoding import raw

        yield "key", raw(self.key)


@dataclasses.dataclass(frozen=True)
class _UncheckedLocal:
    key: Any

    def json_items(self):
        key = self.key
        yield "key", key.anything


@dataclasses.dataclass(frozen=True)
class _DynamicRead:
    key: Any

    def json_items(self):
        yield "key", getattr(self, "hidden", None)


@dataclasses.dataclass(frozen=True)
class _WritesState:
    key: Any

    def json_items(self):
        self.key.append(1)
        yield "key", self.key


@dataclasses.dataclass(frozen=True)
class _NarrowedOnlyInOneBranch:
    key: Any

    def json_items(self):
        key = self.key
        if type(key) is _DeclaredRecord:
            yield "key", key.key
        yield "other", key.anything


@pytest.mark.parametrize(
    "kind",
    [_ReadsModuleState, _ReadsClassState, _RawOfAField, _UncheckedLocal, _DynamicRead, _WritesState, _NarrowedOnlyInOneBranch],
    ids=lambda kind: kind.__name__,
)
def test_the_purity_audit_rejects_state_the_fields_do_not_determine(kind):
    from scripts.function_tracer_pcode.tests.unit._serialization_purity_audit import PurityAudit

    assert PurityAudit().audit_type(kind, ("json_items",)) != []


def test_the_purity_audit_accepts_a_field_only_protocol():
    from scripts.function_tracer_pcode.tests.unit._serialization_purity_audit import PurityAudit

    assert PurityAudit().audit_type(_DeclaredRecord, ("json_items",)) == []
