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
                "terms": _FieldInfo("tuple", None, "Term"),
                "child": _FieldInfo("object", "Term", None),
            },
            "Term": {
                "offset": _FieldInfo("scalar", None, None),
            },
        }


HEADER = """
from scripts.function_tracer_pcode.core.live_values import builtin_items, exact_scalar, exact_tree, scalar_bool, scalar_int, scalar_text
from scripts.function_tracer_pcode.core.runtime_ref_record import exact_field_value
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
        # 入れ子の関数（引数は未確認として本体を検査する）と、未確認の値の反復
        (
            "@classmethod\ndef make(cls, items):\n    def visit(item):\n        return item > 0\n    return cls(flag=all(visit(i) for i in items))\n",
            ["comparison of unknown", "iteration of unknown"],
        ),
        # 未確認の値の `len` / `tuple()` / 組への代入（`__len__` / `__iter__` は値の型の code）
        ("@classmethod\ndef make(cls, items):\n    return cls(name=str(len(items)))\n", ["len() iterates unknown"]),
        ("@classmethod\ndef make(cls, items):\n    return cls(key=tuple(items))\n", ["tuple() iterates unknown"]),
        ("@classmethod\ndef make(cls, pair):\n    a, b = pair\n    return cls(name='x')\n", ["unpacking of unknown"]),
        # 名前の容器への変異（append した未確認の値を後で比べる）
        (
            "@classmethod\ndef make(cls, value):\n    seen = []\n    seen.append(value)\n    return cls(flag=seen[0] == 1)\n",
            ["comparison of unknown"],
        ),
        # dict の値（key と値を分けて追う）
        (
            "@classmethod\ndef make(cls, value):\n    table = {'a': value}\n    return cls(flag=table['a'] > 0)\n",
            ["comparison of unknown"],
        ),
        # 位置ごとの tuple（2 番目だけが未確認）
        (
            "@classmethod\ndef make(cls, value):\n    first, second = (1, value)\n    return cls(flag=first > 0 and second > 0)\n",
            ["comparison of unknown"],
        ),
        # 注釈だけの値（tuple の要素・record の field）の scalar の属性と、method の戻り値
        ("def __post_init__(self):\n    for term in self.terms:\n        if term.offset > 0:\n            raise ValueError()\n", ["comparison of unknown"]),
        ("def __post_init__(self):\n    if self.child.key() == ('a',):\n        raise ValueError()\n", ["comparison of unknown"]),
        ("def __post_init__(self):\n    if self.child.ready():\n        raise ValueError()\n", ["truthiness of unknown"]),
    ],
)
def test_the_guard_flags_unsafe_consumption(body, expected):
    assert sorted(_violations(body)) == sorted(expected)


def _module(body: str, extra: str = "", term: str = "") -> ConstructionGuard:
    source = HEADER + textwrap.indent(textwrap.dedent(body), "    ")
    source += "\n@dataclass(frozen=True)\n@runtime_ref_record\nclass Term:\n" + textwrap.indent(textwrap.dedent(term or "pass\n"), "    ")
    source += textwrap.dedent(extra)
    return ConstructionGuard({"scripts.function_tracer_pcode.core.runtime_refs.sample": source}, _World())


def _found(guard: ConstructionGuard) -> list:
    return sorted(v.split(": ", 2)[1] for v in guard.violations())


def test_the_guard_follows_self_methods_from_entries():
    """入口から呼ぶ自分の method（review の反例: readonly の `_readonly_contract_seed_terms`）の本体も検査する。"""

    guard = _module("""
        @runtime_ref_entry
        def key(self, size: int):
            return self._seed(size)

        def _seed(self, size):
            return tuple(int(getattr(term, "offset", 0) or 0) for term in self.terms)
    """)
    assert "sample:Ref._seed" in guard.reached()
    assert _found(guard) == ["int() of unknown", "truthiness of unknown"]


def test_the_guard_does_not_trust_method_results_it_did_not_prove():
    """自分の method の戻り値は本体の return から決める（未確認の値を返す method の結果を比べると違反）。"""

    guard = _module("""
        @runtime_ref_entry
        def check(self, value):
            return self._raw(value) == 1

        def _raw(self, value):
            return value
    """)
    assert _found(guard) == ["comparison of unknown"]


def test_the_guard_checks_methods_reached_through_annotated_values():
    """注釈だけの値の method: 本物なら package の code が走るので本体を検査し、結果は未確認として扱う。"""

    guard = _module(
        """
        def __post_init__(self):
            if self.child is not None:
                self.child._describe()
        """,
        term="""
        payload: object = None

        def _describe(self):
            return self.payload > 0
        """,
    )
    # `_describe` は外から呼べない名前: 注釈だけの値の method として到達したときだけ検査される
    assert "sample:Term._describe" in guard.reached()
    assert _found(guard) == ["comparison of unknown"]


def test_the_guard_does_not_trust_results_of_methods_on_annotated_values():
    """注釈だけの値の method は、本体が clean な値を返しても、代わりの型なら外の code（結果は未確認）。"""

    guard = _module(
        """
        def __post_init__(self):
            if self.child is not None and self.child.key() == ("a",):
                raise ValueError()
        """,
        term="""
        def key(self):
            return ("a",)
        """,
    )
    assert "sample:Term.key" in guard.reached()
    assert _found(guard) == ["comparison of unknown"]


def test_the_guard_reads_tuple_fields_of_annotated_values_as_uncertain():
    """注釈だけの値の tuple の field は、代わりの型なら scalar の subclass かもしれない（reader で読む）。"""

    world = _World()
    world.classes["Term"]["parts"] = _FieldInfo("tuple", None, None)
    assert _found(_module_with(world, """
        def __post_init__(self):
            for term in self.child.parts:
                pass
    """)) == ["iteration of uncertain:seq:unknown"]
    assert _found(_module_with(world, """
        def __post_init__(self):
            for term in builtin_items(self.child.parts):
                pass
    """)) == []


def test_the_guard_carries_container_changes_out_of_continue_branches():
    """`continue` で終わる分岐の変異（append）も次の繰り返しとループの後へ流れる。"""

    guard = _module("""
        @classmethod
        def make(cls, items):
            seen = []
            for item in builtin_items(items):
                if item is not None:
                    seen.append(item)
                    continue
            return cls(flag=seen[0] == 1)
    """)
    assert _found(guard) == ["comparison of unknown"]


def test_the_guard_carries_container_changes_out_of_break_branches():
    guard = _module("""
        @classmethod
        def make(cls, items):
            seen = []
            for item in builtin_items(items):
                if item is not None:
                    seen.append(item)
                    break
            return cls(flag=seen[0] == 1)
    """)
    assert _found(guard) == ["comparison of unknown"]


def test_the_guard_counts_in_place_sorting_as_comparison():
    guard = _module("""
        @classmethod
        def make(cls, items):
            pairs = [("a", item) for item in builtin_items(items)]
            pairs.sort()
            return cls(name="x")
    """)
    assert _found(guard) == ['sort() compares tup:["clean", "unknown"]']


@pytest.mark.parametrize(
    "body, expected",
    [
        # 葉だけを写す reader（`exact_scalar`）の結果: 容器なら中の葉は未確認（文字列化・hash・定数でない値との比較）
        ("@classmethod\ndef make(cls, value):\n    return cls(name=str(exact_scalar(value)))\n", ["str() of leaf"]),
        ("@classmethod\ndef make(cls, value):\n    return cls(flag=exact_scalar(value) in {'a', 'b'})\n", ["comparison of leaf"]),
        ("@classmethod\ndef make(cls, left, right):\n    return cls(flag=exact_scalar(left) == exact_scalar(right))\n", ["comparison of leaf"]),
        # 定数との比較・数への変換・tuple の定数への `in` はよい
        ("@classmethod\ndef make(cls, value):\n    return cls(flag=exact_scalar(value) == 'a', name=str(int(exact_scalar(value))))\n", []),
        ("@classmethod\ndef make(cls, value):\n    return cls(flag=exact_scalar(value) in ('a', 'b'))\n", []),
        # 葉の reader の後で scalar に絞った値は exact
        ("@classmethod\ndef make(cls, value):\n    value = exact_scalar(value)\n    if isinstance(value, str):\n        return cls(name=value.strip())\n    return None\n", []),
        # 木の reader（`exact_tree` / `scalar_text`）の結果は比べても文字列化してもよい
        ("@classmethod\ndef make(cls, left, right):\n    return cls(flag=exact_tree(left) == exact_tree(right), name=scalar_text(left))\n", []),
    ],
)
def test_the_guard_tells_leaf_readers_from_tree_readers(body, expected):
    assert sorted(_violations(body)) == sorted(expected)


@pytest.mark.parametrize(
    "body, expected",
    [
        # 2 回目の独立 review の guard の穴（G1〜G6）
        ("@classmethod\ndef make(cls, value):\n    return cls(name='{}'.format(value))\n", ["format() of unknown"]),
        ("@classmethod\ndef make(cls, value):\n    match value:\n        case 1:\n            return cls(name='a')\n    return None\n", ["match of unknown"]),
        ("@classmethod\ndef make(cls, key):\n    table = {}\n    table.setdefault(key, 1)\n    return cls(flag=table.get(key) == 1)\n", ["hash", "hash"]),
        ("@classmethod\ndef make(cls, value):\n    return cls(key=(*value,))\n", ["unpacking of unknown"]),
        ("@classmethod\ndef make(cls, value):\n    return cls(flag=exact_scalar(value) == ('a', 'b'))\n", ["comparison of leaf"]),
        ("@classmethod\ndef make(cls, value):\n    return cls(name=str(exact_field_value(value, 'tuple')))\n", ["str() of leaf"]),
    ],
)
def test_the_guard_closes_the_second_review_holes(body, expected):
    assert sorted(_violations(body)) == sorted(expected)


def test_the_guard_does_not_trust_methods_of_values_narrowed_by_isinstance():
    """`isinstance(x, C)` は C の subclass も通す（method を上書きし得る）: field は写した値、method の結果は未確認。
    `type(x) is C` は C そのもの。"""

    narrowed = _module(
        """
        @classmethod
        def make(cls, value):
            if isinstance(value, Term):
                return cls(flag=value.key() == ("a",), name=str(value.offset))
            return None
        """,
        term="""
        def key(self):
            return ("a",)
        """,
    )
    assert _found(narrowed) == ["comparison of unknown"]
    exact = _module(
        """
        @classmethod
        def make(cls, value):
            if type(value) is Term:
                return cls(flag=value.key() == ("a",))
            return None
        """,
        term="""
        def key(self):
            return ("a",)
        """,
    )
    assert _found(exact) == []


def test_the_guard_trusts_readers_only_by_import():
    """reader と同じ名前でも、module で定義・代入した名前や局所変数は reader ではない。"""

    shadowed = _module("""
        @classmethod
        def make(cls, value):
            return cls(name=str(scalar_text(value)))
    """, extra="""
        def scalar_text(value):
            return value
    """)
    assert _found(shadowed) == ["str() of unknown"]
    local = _module("""
        @classmethod
        def make(cls, value, scalar_int):
            return cls(flag=scalar_int(value) > 0)
    """)
    assert _found(local) == ["comparison of unknown"]


def test_the_guard_starts_from_everything_callable_from_outside():
    """引数の無い method、ref でない class の method、公開の関数も起点（外から呼べる）。"""

    guard = _module(
        """
        def lower(self):
            return Term(offset=int(getattr(self.payload, "size", 0) or 4))
        """,
        extra="""
        class Collector:
            def __init__(self):
                self._seen = set()

            def record(self, item):
                if item.event_id in self._seen:
                    return None
                self._seen.add(item.event_id)
                return None

        def public_helper(value):
            return value > 0
        """,
    )
    assert {"sample:Ref.lower", "sample:Collector.record", "sample:None.public_helper"} <= set(guard.reached())
    assert _found(guard) == ["comparison of unknown", "comparison of unknown", "hash", "int() of unknown", "truthiness of unknown"]


def _module_with(world: RefWorld, body: str) -> ConstructionGuard:
    source = HEADER + textwrap.indent(textwrap.dedent(body), "    ")
    return ConstructionGuard({"scripts.function_tracer_pcode.core.runtime_refs.sample": source}, world)


def test_the_guard_follows_properties_and_nested_call_arguments():
    guard = _module(
        """
        @classmethod
        def make(cls, value):
            return cls(name=_helper(value))
        """,
        extra="""
        def _helper(value):
            return value or 'x'
        """,
    )
    assert _found(guard) == ["truthiness of unknown"]
    with_property = _module("""
        def __post_init__(self):
            if self.total > 1:
                raise ValueError()

        @property
        def total(self):
            return self.payload
    """)
    assert "sample:Ref.total" in with_property.reached()
    assert _found(with_property) == ["comparison of unknown"]


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
        # 本物の instance への絞り込み（scalar の field は owner が写した値）・否定の早期 return
        "@classmethod\ndef make(cls, value):\n    if not isinstance(value, Term):\n        return None\n    return cls(flag=value.offset > 0)\n",
        # reader で読んだ外の値・外の method の戻り値
        "def __post_init__(self):\n    for term in self.terms:\n        if scalar_int(term.offset) > 0:\n            raise ValueError()\n",
        "def __post_init__(self):\n    if exact_tree(self.child.key()) == ('a',):\n        raise ValueError()\n",
        "@classmethod\ndef make(cls, items):\n    return cls(key=builtin_items(items), name=str(len(builtin_items(items))))\n",
    ],
)
def test_the_guard_accepts_safe_consumption(body):
    assert _violations(body) == []
