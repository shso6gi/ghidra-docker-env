# -*- coding: utf-8 -*-
"""Issue #242: 構築の経路の静的な guard（`runtime_ref_construction_guard`）の適用と検出力。

guard の範囲と限界は `runtime_ref_construction_guard` の docstring に書いてある。ここでは、
(1) package の構築の経路に違反が無いこと（理由つきの例外は現に使われているものだけ）、
(2) guard が規則に反する形を検出し、規則どおりの形を受けること（合成の module で）を確かめる。
振る舞いは `test_issue242_entry_matrix.py` と `test_issue242_construction_contract.py` が実行して確かめる。
"""

from __future__ import annotations

import textwrap

import pytest

from scripts.function_tracer_pcode.tests.unit.runtime_ref_construction_guard import (
    ACCEPTED,
    ConstructionGuard,
    RefWorld,
    _FieldInfo,
)


@pytest.fixture(scope="module")
def package_guard() -> ConstructionGuard:
    return ConstructionGuard.for_package()


def test_construction_paths_consume_only_safely_read_values(package_guard):
    assert package_guard.violations() == []


def test_accepted_exceptions_are_still_needed(package_guard):
    used = {v.rsplit(" (line ", 1)[0] for v in package_guard.accepted()}
    assert used == set(ACCEPTED)


def test_the_guard_reaches_construction_entries_and_their_helpers(package_guard):
    reached = set(package_guard.reached())
    assert {
        "locations:LocationBaseRef.__post_init__", "locations:LocationBaseRef.parameter",
        "locations:CanonicalLocation.__init__", "call_target:CallTargetRef.from_function",
        "call_target:None._safe_bool_method", "call_target:None._safe_external_library_name",
        "pcode:PcodeOpRef.from_pcode_op", "pcode:None._local_op_ordinal_from_parent",
        "unknowns:UnknownValueRef.budget_exceeded", "unknowns:None._canonical_budget_value",
        "loops:None.compare_loop_summaries", "loops:None._loop_expression_semantic_key",
        "readonly:ReductionAccumulatorProof.seed_terms_for_count_value", "loops:None._bias_key",
    } <= reached


# ---------------------------------------------------------------------------
# 検出力（合成の module）
# ---------------------------------------------------------------------------


class _World(RefWorld):
    def __init__(self):
        self.classes = {
            "Ref": {
                "name": _FieldInfo("scalar", None, None),
                "flag": _FieldInfo("bool", None, None),
                "key": _FieldInfo("tuple", None, None),
                "payload": _FieldInfo("object", None, None),
            },
        }


HEADER = """
from scripts.function_tracer_pcode.core.live_values import exact_scalar, scalar_bool, scalar_int, scalar_text
@dataclass(frozen=True)
@runtime_ref_record
class Ref:
"""


def _violations(body: str) -> list:
    source = HEADER + textwrap.indent(textwrap.dedent(body), "    ")
    guard = ConstructionGuard({"scripts.function_tracer_pcode.core.runtime_refs.sample": source}, _World())
    return [v.split(": ", 2)[1] for v in guard.violations()]


@pytest.mark.parametrize(
    "body, expected",
    [
        # 引数（写していない factory の引数）の真偽・比較・format・文字列の method
        ("@classmethod\ndef make(cls, name):\n    return cls(name=name or None)\n", ["truthiness of unknown"]),
        ("@classmethod\ndef make(cls, kind):\n    return cls(name='a' if kind in {'x', 'y'} else 'b')\n", ["comparison of unknown"]),
        ("@classmethod\ndef make(cls, operation):\n    return cls(name=f'{operation}_x')\n", ["format"]),
        ("@classmethod\ndef make(cls, name):\n    return cls(name=name.strip())\n", ["method strip() on unknown"]),
        ("@classmethod\ndef make(cls, size):\n    return cls(name=str(size + 1))\n", ["arithmetic on unknown", "str() of unknown"]),
        # API の戻り値
        ("@classmethod\ndef make(cls, function):\n    return cls(flag=bool(function.isExternal()))\n", ["bool() of unknown"]),
        ("@classmethod\ndef make(cls, function):\n    names = {function.getName()}\n    return cls(name='a')\n", ["hash"]),
        # 例外の流れ: except の後の代入が try の中の値を隠さない
        (
            "@classmethod\ndef make(cls, method):\n    try:\n        value = method()\n    except Exception:\n        value = None\n"
            "    if value:\n        return cls(name='a')\n    return cls(name='b')\n",
            ["truthiness of unknown"],
        ),
        # 構築中の tuple の要素（list で来るかもしれない）
        ("def __post_init__(self):\n    if self.key and self.key[0] != 'x':\n        raise ValueError()\n", ["comparison of unknown"]),
        # 注釈が Any の field
        ("def __post_init__(self):\n    if self.payload == 1:\n        raise ValueError()\n", ["comparison of unknown"]),
        # 入れ子の関数（引数は未確認として本体を検査する）
        ("@classmethod\ndef make(cls, items):\n    def visit(item):\n        return item > 0\n    return cls(flag=all(visit(i) for i in items))\n", ["comparison of unknown"]),
    ],
)
def test_the_guard_flags_unsafe_consumption(body, expected):
    assert sorted(_violations(body)) == sorted(expected)


def test_the_guard_follows_values_into_module_helpers():
    source = HEADER + textwrap.indent(textwrap.dedent("""
        @classmethod
        def make(cls, name):
            return cls(name=_helper(name))
    """), "    ") + textwrap.dedent("""
        def _helper(value):
            return value or 'x'
    """)
    guard = ConstructionGuard({"scripts.function_tracer_pcode.core.runtime_refs.sample": source}, _World())
    assert [v.split(": ", 2)[1] for v in guard.violations()] == ["truthiness of unknown"]


@pytest.mark.parametrize(
    "body",
    [
        # reader で読んだ値
        "@classmethod\ndef make(cls, name):\n    return cls(name=exact_scalar(name) or None)\n",
        "@classmethod\ndef make(cls, function):\n    return cls(flag=scalar_bool(function.isExternal()))\n",
        "@classmethod\ndef make(cls, size):\n    return cls(name=str(scalar_int(size) + 1))\n",
        # decorator が写した引数（注釈が scalar）
        "@classmethod\n@runtime_ref_entry\ndef make(cls, name: str, size: int):\n    return cls(name=f'{name or size}')\n",
        # 構築中に写した field と、写した後の値
        "def __post_init__(self):\n    if self.name not in {'a', 'b'} or self.flag:\n        raise ValueError()\n",
        "def __post_init__(self):\n    if self.key and exact_scalar(self.key[0]) != 'x':\n        raise ValueError()\n",
        # bool への絞り込み（bool は subclass を作れない）・identity の比較
        "@classmethod\ndef make(cls, value):\n    if isinstance(value, bool) and value:\n        return cls(flag=value)\n    return cls(flag=value is True)\n",
    ],
)
def test_the_guard_accepts_safe_consumption(body):
    assert _violations(body) == []
