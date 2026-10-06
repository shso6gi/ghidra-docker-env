# -*- coding: utf-8 -*-
"""意味値の到達走査は、外の runtime object の代わりをする型を葉として扱う。

`core/semantic_freeze._walk_semantic_carriers` は、この package が定義した object の `__dict__` や dataclass の field へ
入って意味値（式・条件）を探す。記録再生の Ghidra object の proxy（`RecordedObject`）や記録器の
proxy（`RecordingProxy`）もこの package の型だが、本物の Ghidra object の代わりで、`__dict__` には
記録全体・観測の履歴が入っている。辿ると凍結 1 回ごとに記録の大きさに比例する仕事になり、本物の
Ghidra object（葉）では起きない費用が記録再生の CI の予算を超えた（PR-22-B 以降、gammln の再生が
cProfile 下で約 2.6 倍）。代わりをする型は `__semantic_opaque__ = True` を宣言し、走査は本物と同じく葉にする。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.semantic_freeze import (
    SEMANTIC_OPAQUE_DECLARATION,
    _walk_semantic_carriers,
    freeze_expression,
)


class _PackageHolder:
    """この package で定義した、意味値を抱える object（走査は `__dict__` へ入る）。"""

    def __init__(self, inner):
        self.inner = inner


class _ExternalStandIn(_PackageHolder):
    """外の runtime object の代わり（宣言は class にだけ置く。subclass も葉）。"""

    __semantic_opaque__ = True


class _DerivedStandIn(_ExternalStandIn):
    pass


#: test module は rootdir 相対の名前で import されるので、package の型として扱われる名前を明示する
_PACKAGE_MODULE = "scripts.function_tracer_pcode.tests.unit.test_semantic_carrier_walk_opaque"
for _kind in (_PackageHolder, _ExternalStandIn, _DerivedStandIn):
    _kind.__module__ = _PACKAGE_MODULE


def _carried(container):
    found = []
    _walk_semantic_carriers(container, found.append, found.append)
    return found


def test_a_package_object_is_walked_into():
    inner = Expression.constant(1, size=4)
    assert _carried(_PackageHolder(inner)) == [inner]


def test_a_declared_stand_in_is_a_leaf_like_the_external_object_it_replaces():
    inner = Expression.constant(1, size=4)
    assert _carried(_ExternalStandIn(inner)) == []
    assert _carried(_DerivedStandIn(inner)) == []
    # 凍結も stand-in の中へ入らない（本物の Ghidra object を抱える ref と同じ）
    expr = freeze_expression(Expression.unknown("u", runtime_ref=_ExternalStandIn(inner)))
    assert expr.is_frozen and not inner.is_frozen


def test_the_declaration_is_read_from_the_class_not_from_the_instance():
    """instance の `__getattr__`（記録再生の proxy は観測を作る）を呼ばずに宣言を読む。"""

    class _Proxy(_PackageHolder):
        __semantic_opaque__ = True

        def __getattr__(self, name):
            raise AssertionError(f"the walk asked the proxy for {name}")

    _Proxy.__module__ = _PACKAGE_MODULE

    assert _carried(_Proxy(Expression.constant(1, size=4))) == []

    holder = _PackageHolder(Expression.constant(1, size=4))
    holder.__dict__[SEMANTIC_OPAQUE_DECLARATION] = True
    # instance に置いた値は宣言ではない（型の宣言だけを読む）
    assert len(_carried(holder)) == 1


def test_the_recording_and_replay_proxies_declare_that_they_stand_in_for_ghidra_objects():
    from scripts.function_tracer_pcode.tests.fixtures.pcode.recorded_program import RecordedObject
    from scripts.function_tracer_pcode.tests.tools.record_pcode_fixture import RecordingProxy

    for proxy_type in (RecordedObject, RecordingProxy):
        assert proxy_type.__dict__.get(SEMANTIC_OPAQUE_DECLARATION) is True, proxy_type


# ---------------------------------------------------------------------------
# 宣言は値を開くどの規則よりも先（Issue #227 review）
# ---------------------------------------------------------------------------
#
# 契約: 宣言した型の値は、dataclass でも容器の subclass でも package の object でも葉になる。宣言の
# 無い同じ形の型（対照）は、その形の規則どおりに中へ入る（宣言だけが結果を変える: test が空振り
# しない）。式・条件は宣言に依らず意味値として扱う。


def _shapes():
    import dataclasses
    from typing import Any, NamedTuple

    @dataclasses.dataclass
    class FieldCarrier:
        payload: Any

    @dataclasses.dataclass
    class DeclaredFieldCarrier:
        payload: Any
        __semantic_opaque__ = True

    class TupleCarrier(NamedTuple):
        payload: Any

    class DeclaredTupleCarrier(NamedTuple):
        payload: Any

    DeclaredTupleCarrier.__semantic_opaque__ = True

    class ListCarrier(list):
        pass

    class DeclaredListCarrier(list):
        __semantic_opaque__ = True

    class StateCarrier:
        def __init__(self, payload):
            self.payload = payload

    class DeclaredStateCarrier(StateCarrier):
        __semantic_opaque__ = True

    for kind in (FieldCarrier, DeclaredFieldCarrier, TupleCarrier, DeclaredTupleCarrier, ListCarrier,
                 DeclaredListCarrier, StateCarrier, DeclaredStateCarrier):
        kind.__module__ = _PACKAGE_MODULE
    return {
        "dataclass_field": (FieldCarrier, DeclaredFieldCarrier, lambda kind, inner: kind(inner)),
        "namedtuple_element": (TupleCarrier, DeclaredTupleCarrier, lambda kind, inner: kind(inner)),
        "list_subclass_element": (ListCarrier, DeclaredListCarrier, lambda kind, inner: kind([inner])),
        "package_object_state": (StateCarrier, DeclaredStateCarrier, lambda kind, inner: kind(inner)),
    }


_SHAPE_NAMES = ("dataclass_field", "namedtuple_element", "list_subclass_element", "package_object_state")



@pytest.mark.parametrize("shape", _SHAPE_NAMES)
def test_a_declared_stand_in_is_a_leaf_in_every_shape_and_its_undeclared_twin_is_walked(shape):
    plain, declared, build = _shapes()[shape]
    inner = Expression.constant(1, size=4)
    # 対照: 宣言の無い同じ形の型は、その形の規則どおりに中の式へ届く
    assert _carried(build(plain, inner)) == [inner]
    assert _carried(build(declared, inner)) == []


@pytest.mark.parametrize("shape", _SHAPE_NAMES)
def test_freezing_does_not_enter_a_declared_stand_in_held_by_a_runtime_ref(shape):
    plain, declared, build = _shapes()[shape]
    walked, skipped = Expression.constant(1, size=4), Expression.constant(2, size=4)
    freeze_expression(Expression.unknown("u", runtime_ref=build(plain, walked)))
    freeze_expression(Expression.unknown("v", runtime_ref=build(declared, skipped)))
    assert walked.is_frozen and not skipped.is_frozen


def test_semantic_values_stay_semantic_whatever_they_declare():
    """式・条件の subclass が宣言を持っても、意味値として扱う（宣言は意味値を消さない）。"""

    from scripts.function_tracer_pcode.core.condition import Condition
    from scripts.function_tracer_pcode.core.semantic_freeze import CarrierRule, _carrier_rule

    class DeclaredExpression(Expression):
        __semantic_opaque__ = True

    class DeclaredCondition(Condition):
        __semantic_opaque__ = True

    expression = DeclaredExpression.constant(1, size=4)
    condition = DeclaredCondition(Expression.constant(1, size=1))
    assert _carrier_rule(expression) is CarrierRule.EXPRESSION
    assert _carrier_rule(condition) is CarrierRule.CONDITION


def test_the_shared_mock_ghidra_objects_are_leaves_when_imported_through_the_package_path():
    """`tests/conftest.py` の Ghidra の代わり（package の path で import すると package の型になる）は、
    **実際の field（dataclass）や状態** に式を置いても辿らない。"""

    import dataclasses

    from scripts.function_tracer_pcode.tests import conftest

    inner = Expression.constant(1, size=4)
    for stand_in in (conftest.MockProgram, conftest.MockDataTypeManager, conftest.MockDataType,
                     conftest.MockDataOrganization):
        assert stand_in.__dict__.get(SEMANTIC_OPAQUE_DECLARATION) is True, stand_in
        instance = stand_in.__new__(stand_in)
        if dataclasses.is_dataclass(stand_in):
            names = [field.name for field in dataclasses.fields(stand_in)]
        else:
            names = ["carried"]
        for name in names:
            object.__setattr__(instance, name, inner)
        assert _carried(instance) == [], stand_in
