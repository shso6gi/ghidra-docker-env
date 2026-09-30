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


_NOT_CLOSED = {
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

#: 表現を作る method が呼んでよい自分の method と、その理由（読む field は規則の表が扱う）。
_REPRESENTATION_METHODS = {
    "_to_dict": "子の描画（子は OPERANDS / VALUE / RUNTIME_REF の規則が closed を求める）",
    "_to_dict_active": "_to_dict からの 1 node 分",
    "_serialize_runtime_ref": "runtime_ref を引数で受けて描く（RUNTIME_REF の規則）",
    "structural_key": "閉路の経路だけ（検証済みの graph には閉路が無い）",
}


def _function_node(module: Any, qualified: str) -> ast.FunctionDef:
    source = textwrap.dedent(inspect.getsource(module))
    tree = ast.parse(source)
    class_name, method_name = qualified.split(".")
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and node.name == class_name:
            for item in node.body:
                if isinstance(item, ast.FunctionDef) and item.name == method_name:
                    return item
    raise AssertionError(f"{qualified} not found")


def _attribute_reads(function: ast.FunctionDef, owner: str) -> set:
    return {
        node.attr
        for node in ast.walk(function)
        if isinstance(node, ast.Attribute)
        and isinstance(node.ctx, ast.Load)
        and isinstance(node.value, ast.Name)
        and node.value.id == owner
    }


def _dict_reads(function: ast.FunctionDef, owner: str) -> set:
    """`owner.__dict__.get("x")` / `owner.__dict__["x"]` の形の読み取り。"""

    names = set()
    for node in ast.walk(function):
        target = None
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "get":
            target, key = node.func.value, node.args[0] if node.args else None
        elif isinstance(node, ast.Subscript):
            target, key = node.value, node.slice
        else:
            continue
        if (
            isinstance(target, ast.Attribute)
            and target.attr == "__dict__"
            and isinstance(target.value, ast.Name)
            and target.value.id == owner
            and isinstance(key, ast.Constant)
        ):
            names.add(key.value)
    return names


def test_every_field_the_expression_representation_reads_has_a_closure_rule():
    reads = set()
    for method in ("Expression._to_dict", "Expression._to_dict_active"):
        function = _function_node(expression_module, method)
        reads |= _attribute_reads(function, "self") | _dict_reads(function, "self")

    methods = {name for name in reads if callable(getattr(Expression, name, None))}
    fields = reads - methods

    assert methods <= set(_REPRESENTATION_METHODS), sorted(methods - set(_REPRESENTATION_METHODS))
    unclassified = fields - set(EXPRESSION_SERIALIZATION_INPUTS) - set(DERIVED_STATE_FIELDS)
    assert unclassified == set(), (
        "the LEGACY representation reads fields with no serialization-closure rule; add each to "
        "EXPRESSION_SERIALIZATION_INPUTS (semantic_lifecycle) so freeze decides whether it is immutable: "
        f"{sorted(unclassified)}"
    )
    # 表に在る field は実際に読まれている（古い行を残さない）
    assert set(EXPRESSION_SERIALIZATION_INPUTS) <= fields
    # 規則の対象は凍結後に代入できない意味 field（代入で規則の前提が崩れない）
    assert set(EXPRESSION_SERIALIZATION_INPUTS) <= set(expression_module.SEMANTIC_FIELDS)


def test_every_field_the_condition_representation_reads_has_a_closure_rule():
    # PHI の branch の条件は `_to_dict_active` が直接読み、単独の条件は `json_items` が出す
    phi_reads = _attribute_reads(_function_node(expression_module, "Expression._to_dict_active"), "condition")
    record_reads = _attribute_reads(_function_node(condition_module, "Condition.json_items"), "self")

    assert phi_reads | record_reads == set(CONDITION_SERIALIZATION_INPUTS)
    assert set(CONDITION_SERIALIZATION_INPUTS) <= set(condition_module.SEMANTIC_FIELDS)


def test_every_serialization_input_kind_has_exactly_one_closure_rule():
    assert set(SERIALIZATION_CLOSURE_RULES) == set(SerializationInput)
    for table in (EXPRESSION_SERIALIZATION_INPUTS, CONDITION_SERIALIZATION_INPUTS):
        assert all(type(kind) is SerializationInput for kind in table.values())


def test_the_closure_derivation_lives_only_in_the_lifecycle_owner():
    """closed の規則を consumer 側で再実装しない（owner は semantic_freeze / semantic_lifecycle）。"""

    root = pathlib.Path(expression_module.__file__).resolve().parents[1]
    owners = {root / "core" / "semantic_freeze.py", root / "core" / "semantic_lifecycle.py"}
    writers = []
    for path in sorted(root.rglob("*.py")):
        if path in owners or "tests" in path.relative_to(root).parts:
            continue
        text = path.read_text(encoding="utf-8")
        if '"_serialization_closed"' in text or "'_serialization_closed'" in text or '"_storage_payload"' in text:
            writers.append(str(path.relative_to(root)))
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
