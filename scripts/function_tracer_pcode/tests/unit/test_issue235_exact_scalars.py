# -*- coding: utf-8 -*-
"""式の意味 field の scalar は組み込みの型そのもの（Issue #235）。

実 Ghidra（JPype）の `varnode.getOffset()` / `getSize()` は `int` の subclass（`JInt` / `JLong`）を返す。式の
構築と代入の入口（`Expression.__init__` / `__setattr__`）が、scalar の subclass を基底型の値へ写す: 値と意味は
変えず、表現・digest・structural key・SMT の文字列は写す前と同じ。写した結果、検証済みの値が replay と同じ規則で
serialization-closed になる（#219 C-RS2 の規則は緩めない）。

JPype の型の模擬は、`int` / `str` の subclass で、上書きした method が呼ばれたら記録する型（写すときに
subclass の code を呼ばないことも確かめる）。
"""

from __future__ import annotations

import enum
import json
from typing import Any, List

import pytest

from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.semantic_freeze import seal_serialization
from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec
from scripts.function_tracer_pcode.tests.unit._publication import published

CALLS: List[str] = []


class JInt(int):
    """JPype の `JInt` の模擬（上書きした method が呼ばれたら記録する）。"""

    def __int__(self):  # pragma: no cover - must not be called
        CALLS.append("__int__")
        return int.__int__(self)

    def __index__(self):  # pragma: no cover - must not be called
        CALLS.append("__index__")
        return int.__index__(self)

    def __str__(self):
        CALLS.append("__str__")
        return int.__repr__(self)

    def __repr__(self):
        CALLS.append("__repr__")
        return "JInt(%d)" % int.__index__(self)


class JLong(JInt):
    pass


class JString(str):
    def __str__(self):  # pragma: no cover - must not be called
        CALLS.append("JString.__str__")
        return str.__str__(self)


class _Flag(enum.IntEnum):
    ON = 1


@pytest.fixture(autouse=True)
def _reset_calls():
    CALLS.clear()
    yield


def _build(scalar=int, text=str):
    """同じ形の式を、scalar の型だけを替えて作る（JPype の境界と同じく、構築の引数に subclass を渡す）。"""

    a = Expression.parameter(text("a"), scalar(0), size=scalar(4))
    b = Expression.constant(scalar(0x401000), size=scalar(8))
    expr = Expression.binary_op(text("INT_ADD"), a, Expression.constant(scalar(5), size=scalar(4)))
    return Expression.binary_op("INT_AND", expr, b)


def _inject(expr: Expression, scalar) -> Expression:
    """写す前の状態（意味 field に subclass が残る）を作る: 構築の後で `__dict__` へ直接置く（入口を通さない）。"""

    for node in _walk(expr):
        for field in ("value", "size"):
            current = node.__dict__.get(field)
            if type(current) is int:
                node.__dict__[field] = scalar(current)
    return expr


def _walk(expr: Expression):
    pending = [expr]
    seen = set()
    while pending:
        node = pending.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        yield node
        pending.extend(node.operands)


def _surfaces(expr: Expression) -> Any:
    expr = published(expr)
    return (
        json.dumps(expr.to_dict(), sort_keys=True),
        SnapshotFingerprintCodec.digest(expr.to_dict()),
        expr.structural_key(),
        expr.to_smt(),
        expr.to_string(),
    )


@pytest.mark.parametrize("scalar", [JInt, JLong])
def test_construction_writes_builtin_scalars_without_calling_the_subclass(scalar):
    expr = _build(scalar, JString)
    for node in _walk(expr):
        for field in ("value", "size", "operator", "name", "read_order_key", "opcode", "data_type"):
            value = node.__dict__.get(field)
            assert value is None or type(value) in (int, str, float, bool), (field, type(value))
    assert CALLS == []


def test_assignment_before_validation_writes_builtin_scalars():
    expr = Expression.constant(1, size=4)
    expr.size = JInt(8)
    expr.value = JLong(2)
    expr.name = JString("c")
    assert (type(expr.size), type(expr.value), type(expr.name)) == (int, int, str)
    assert (expr.size, expr.value, expr.name) == (8, 2, "c")
    assert CALLS == []


def test_values_that_are_not_scalar_subclasses_are_kept():
    enum_value = Expression(ExpressionType.CONSTANT, value=_Flag.ON, size=4)
    bool_value = Expression(ExpressionType.CONSTANT, value=True, size=1)
    tuple_value = Expression(ExpressionType.LITERAL, value=(1, 2), size=0)
    assert enum_value.value is _Flag.ON
    assert bool_value.value is True
    assert tuple_value.value == (1, 2) and type(tuple_value.value) is tuple


@pytest.mark.parametrize("scalar", [JInt, JLong])
def test_the_representation_digest_key_and_smt_are_the_same_as_before(scalar):
    """写す前（意味 field に subclass が残る式）と写した後で、表現・digest・structural key・SMT・文字列が同じ。"""

    before = _surfaces(_inject(_build(), scalar))
    after = _surfaces(_build(scalar))
    plain = _surfaces(_build())
    assert before == after == plain


@pytest.mark.parametrize("scalar", [JInt, JLong])
def test_a_validated_value_built_from_boxed_scalars_is_serialization_closed(scalar):
    """写した結果、検証済みの値が closed になる（写す前は open。closed の規則は変えていない）。"""

    built = published(_build(scalar))
    injected = published(_inject(_build(), scalar))
    assert seal_serialization(built)
    assert not seal_serialization(injected)


def test_storage_info_writes_builtin_scalars_at_construction_and_assignment():
    """式の storage（`storage_info`）の scalar も組み込みの型（実 run の register の offset・size は JPype の整数）。"""

    from scripts.function_tracer_pcode.core.storage import StorageInfo

    storage = StorageInfo(
        is_register=True, space_name=JString("register"), offset=JInt(8), size=JInt(4),
        register_name=JString("x0"), base_register_name=JString("x0"),
        base_register_offset=JLong(16), base_register_size=JInt(8),
    )
    storage.register_offset = JInt(24)
    for name, value in vars(storage).items():
        assert value is None or type(value) in (int, str, float, bool), (name, type(value))
    assert CALLS == []


def test_a_validated_value_with_a_boxed_storage_is_serialization_closed():
    from scripts.function_tracer_pcode.core.storage import StorageInfo

    def storage(scalar):
        # 実 run の `tracer_storage` は構築の後で register の offset・size を代入する（JPype の整数）
        built = StorageInfo(is_register=True, space_name="register", offset=8, size=4,
                            register_name="x0", base_register_name="x0")
        built.register_offset = scalar(24)
        built.register_size = scalar(4)
        return built

    boxed = published(Expression.parameter("a", 0, size=4, storage_info=storage(JInt)))
    plain = published(Expression.parameter("a", 0, size=4, storage_info=storage(int)))
    assert seal_serialization(boxed)
    assert boxed.to_dict() == plain.to_dict()


class JDouble(float):
    """JPype の `JDouble` の模擬（上書きした method が呼ばれたら記録する）。"""

    def __float__(self):  # pragma: no cover - must not be called
        CALLS.append("JDouble.__float__")
        return float.__float__(self)

    def __repr__(self):
        CALLS.append("JDouble.__repr__")
        return "JDouble(%r)" % float.__float__(self)


@pytest.mark.parametrize("raw", [-1, 0, 2 ** 31 - 1, -(2 ** 31), 2 ** 63 - 1, -(2 ** 63), 2 ** 63, 2 ** 64 - 1])
@pytest.mark.parametrize("box", [JInt, JLong])
def test_every_width_and_sign_keeps_its_integer_value(raw, box):
    """符号・幅の端（32 / 64 bit の符号つき・符号なしの境界）でも、写した値は同じ整数（型は `int` そのもの）。"""

    expr = Expression.constant(box(raw), size=box(8))
    assert type(expr.value) is int and expr.value == raw
    assert type(expr.size) is int and expr.size == 8
    assert CALLS == []


@pytest.mark.parametrize("raw", [1.5, -0.0, float("inf"), float("-inf"), float("nan")])
def test_a_boxed_float_keeps_its_exact_bits(raw):
    """float の subclass は基底型の値へ写し、bit の並び（`-0.0` の符号・NaN の payload）を変えない。"""

    import struct

    expr = Expression.constant(JDouble(raw), size=8)
    assert type(expr.value) is float
    assert struct.pack("<d", expr.value) == struct.pack("<d", raw)
    assert CALLS == []


@pytest.mark.parametrize("field, boxed, plain", [
    ("operator", JString("INT_ADD"), "INT_ADD"),
    ("opcode", JInt(19), 19),
    ("read_order_key", JLong(7), 7),
    ("name", JString("x"), "x"),
    ("data_type", JString("int"), "int"),
])
def test_every_scalar_field_is_written_as_the_builtin_on_assignment(field, boxed, plain):
    """代入の入口（`__setattr__`）は scalar の意味 field の全部で写す（構築の後に置く経路）。"""

    expr = Expression.parameter("a", 0, size=4)
    setattr(expr, field, boxed)
    assert type(getattr(expr, field)) is type(plain) and getattr(expr, field) == plain
    assert CALLS == []
