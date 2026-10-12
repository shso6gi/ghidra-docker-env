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
from __future__ import annotations
import hashlib
from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.live_values import attribute_of, builtin_items, method_of, exact_scalar, exact_tree, is_kind, scalar_bool, scalar_int, scalar_text
from scripts.function_tracer_pcode.core.runtime_ref_record import exact_field_value, runtime_ref_key
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
        ("@classmethod\ndef make(cls, name):\n    return cls(name=name.strip())\n", ["method of unknown", "method strip() on unknown"]),
        ("@classmethod\ndef make(cls, size):\n    return cls(name=str(size + 1))\n", ["arithmetic on unknown", "str() of unknown"]),
        # API の戻り値
        ("@classmethod\ndef make(cls, function):\n    return cls(flag=bool(method_of(function, 'isExternal')()))\n", ["bool() of foreign"]),
        ("@classmethod\ndef make(cls, function):\n    names = {method_of(function, 'getName')()}\n    return cls(name='a')\n", ["hash"]),
        # 例外の流れ: except の後の代入が try の中の値を隠さない
        (
            "@classmethod\ndef make(cls, method):\n    try:\n        value = method()\n    except Exception:\n        value = None\n"
            "    if value:\n        return cls(name='a')\n    return cls(name='b')\n",
            ["truthiness of foreign"],
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
        ("def __post_init__(self):\n    for term in self.terms:\n        if term.offset > 0:\n            raise ValueError()\n", ["attribute of rtyped:Term", "comparison of unknown"]),
        ("def __post_init__(self):\n    if self.child.key() == ('a',):\n        raise ValueError()\n", ["comparison of foreign"]),
        ("def __post_init__(self):\n    if self.child.ready():\n        raise ValueError()\n", ["truthiness of foreign"]),
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
    assert _found(guard) == ["attribute of rtyped:Term", "int() of unknown", "truthiness of unknown"]


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
    assert _found(guard) == ["comparison of foreign"]


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
    # `isinstance` の判定そのものが値の `__class__` を読む（`is_kind` で絞る）
    assert _found(narrowed) == ["comparison of foreign", "isinstance reads the class of unknown"]
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
    assert _found(local) == ["comparison of foreign", "passes unknown to foreign code"]


@pytest.mark.parametrize(
    "body, extra, expected",
    [
        # module の形の reader: import した module の名前だけを信用する
        ("@classmethod\ndef make(cls, value):\n    return cls(flag=live_values.exact_tree(value) == (1,))\n", "", []),
        # 引数・局所変数・module の代入がその名前を隠すと reader ではない（review 4 の非 blocker）
        (
            "@classmethod\ndef make(cls, value, live_values):\n    return cls(flag=live_values.exact_tree(value) == (1,))\n",
            "", ["comparison of foreign", "method of unknown"],
        ),
        (
            "@classmethod\ndef make(cls, value):\n    live_values = value\n    return cls(flag=live_values.exact_tree(value) == (1,))\n",
            "", ["comparison of foreign", "method of unknown"],
        ),
        (
            "@classmethod\ndef make(cls, value):\n    return cls(flag=live_values.exact_tree(value) == (1,))\n",
            "class live_values:\n    @staticmethod\n    def exact_tree(value):\n        return value\n",
            ["comparison of foreign", "method of unknown"],
        ),
        (
            "@classmethod\ndef make(cls, value):\n    return cls(flag=live_values.exact_tree(value) == (1,))\n",
            "from scripts.function_tracer_pcode.tests.unit import fakes as live_values\n", ["comparison of foreign", "method of unknown"],
        ),
        (
            "@classmethod\ndef make(cls, value):\n    return cls(flag=exact_tree(value) == (1,))\n",
            "def _rebind():\n    global exact_tree\n    exact_tree = len\n", ["comparison of foreign"],
        ),
    ],
)
def test_the_guard_trusts_reader_modules_only_where_the_name_is_the_import(body, extra, expected):
    source = (
        HEADER
        + textwrap.indent(textwrap.dedent(body), "    ") + "\n" + extra
    )
    guard = ConstructionGuard({"scripts.function_tracer_pcode.core.runtime_refs.sample": source}, _World())
    assert [v.split(": ", 2)[1] for v in guard.violations()] == expected


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
    assert _found(guard) == [
        "attribute of unknown", "attribute of unknown", "attribute of unknown",
        "comparison of unknown", "comparison of unknown", "hash", "int() of unknown", "truthiness of unknown",
    ]


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
        "@classmethod\ndef make(cls, function):\n    return cls(flag=scalar_bool(method_of(function, 'isExternal')()))\n",
        "@classmethod\ndef make(cls, size):\n    return cls(name=str(scalar_int(size) + 1))\n",
        # decorator が写した引数（注釈が scalar）
        "@classmethod\n@runtime_ref_entry\ndef make(cls, name: str, size: int):\n    return cls(name=f'{name or size}')\n",
        # 構築中に写した field と、写した後の値
        "def __post_init__(self):\n    if self.name not in {'a', 'b'} or self.flag:\n        raise ValueError()\n",
        "def __post_init__(self):\n    if self.key and exact_scalar(self.key[0]) != 'x':\n        raise ValueError()\n",
        # bool への絞り込み（bool は subclass を作れない）・identity の比較
        "@classmethod\ndef make(cls, value):\n    if is_kind(value, bool) and value:\n        return cls(flag=value)\n    return cls(flag=value is True)\n",
        # 本物の instance への絞り込み（scalar の field は owner が写した値）・否定の早期 return
        "@classmethod\ndef make(cls, value):\n    if not is_kind(value, Term):\n        return None\n    return cls(flag=value.offset > 0)\n",
        # reader で読んだ外の値・外の method の戻り値
        "def __post_init__(self):\n    for term in self.terms:\n        if scalar_int(attribute_of(term, 'offset')) > 0:\n            raise ValueError()\n",
        "def __post_init__(self):\n    if exact_tree(self.child.key()) == ('a',):\n        raise ValueError()\n",
        "@classmethod\ndef make(cls, items):\n    return cls(key=builtin_items(items), name=str(len(builtin_items(items))))\n",
    ],
)
def test_the_guard_accepts_safe_consumption(body):
    assert _violations(body) == []


@pytest.mark.parametrize(
    "body, expected",
    [
        # 型の属性は metaclass の `__getattribute__` を呼ぶ（`type_name` / `type_module` / `defined_attribute` で読む）
        ("@classmethod\ndef make(cls, value):\n    return cls(name=type(value).__name__)\n", ["type attribute of unknown"]),
        # 未確認の値の属性の読み（`attribute_of` で読む）
        ("@classmethod\ndef make(cls, value):\n    return cls(name=scalar_text(getattr(value, 'name', '')))\n", ["attribute of unknown"]),
        ("@classmethod\ndef make(cls, value):\n    return cls(name=scalar_text(value.name))\n", ["attribute of unknown"]),
        # `isinstance` は値の `__class__` を読む（`is_kind` で絞る）
        ("@classmethod\ndef make(cls, value):\n    return cls(flag=isinstance(value, tuple))\n", ["isinstance reads the class of unknown"]),
        # 外の code の結果を読まずに外へ返す・owner が読まない field に置く
        ("@classmethod\ndef make(cls, value):\n    cls(name='a')\n    return method_of(value, 'build')()\n", ["returns an unread result of foreign code"]),
        ("@classmethod\ndef make(cls, value):\n    return cls(payload=method_of(value, 'build')())\n", ["stores an unread result of foreign code"]),
        # 値の型の code を呼ぶ文（review 5）: `with` の `__enter__`、`yield from` の反復、`del` の key の hash、追わない束縛
        ("@classmethod\ndef make(cls, value):\n    with value:\n        return cls(name='a')\n", ["with of unknown"]),
        ("def lines(self, value):\n    yield from value\n", ["yield from iterates unknown"]),
        ("@classmethod\ndef make(cls, value):\n    d = {}\n    del d[value]\n    return cls(name='a')\n", ["del hashes unknown"]),
        (
            "@classmethod\ndef make(cls, value):\n    y = 0\n    def inner():\n        nonlocal y\n        y = value\n    inner()\n"
            "    return cls(flag=y == 1)\n",
            ["nonlocal is not tracked"],
        ),
        ("@classmethod\ndef make(cls, value):\n    globals()['scalar_int'] = len\n    return cls(name='a')\n", ["globals() is not tracked"]),
        # 標準の hash は引数の buffer を読む（結果の `hexdigest()` は組み込みの `str`）
        ("@classmethod\ndef make(cls, value):\n    return cls(name=hashlib.sha256(value).hexdigest())\n", ["hashlib reads unknown"]),
    ],
)
def test_the_guard_flags_reads_that_run_the_code_of_the_value(body, expected):
    assert _violations(body) == expected


@pytest.mark.parametrize(
    "body",
    [
        "@classmethod\ndef make(cls, value):\n    return cls(name=scalar_text(attribute_of(value, 'name', '')))\n",
        "@classmethod\ndef make(cls, value):\n    return cls(flag=is_kind(value, tuple))\n",
        # 読んでから返す・owner が読む field（scalar）に置く
        "@classmethod\ndef make(cls, value):\n    cls(name='a')\n    return exact_tree(method_of(value, 'build')())\n",
        "@classmethod\ndef make(cls, value):\n    return cls(name=method_of(value, 'build')())\n",
        # key の出口（`runtime_ref_key` が組み込みの木にして返す）
        "@runtime_ref_key\ndef semantic_key(self, value):\n    return method_of(value, 'build')()\n",
        # 組み込みの値と組み込みの容器の連結は要素を読まない
        "@runtime_ref_key\ndef stable_key(self):\n    return self.semantic_key() + (self.name, self.payload)\n"
        "@runtime_ref_key\ndef semantic_key(self):\n    return ('a',)\n",
    ],
)
def test_the_guard_accepts_read_results_of_foreign_code(body):
    assert _violations(body) == []


def test_the_guard_trusts_validation_rewrites_only_when_every_path_rewrites():
    """owner が読まない field（object）へ外の code の結果を置くのは、検証がどの経路でも reader で書き直すときだけよい。"""

    always = (
        "def __post_init__(self):\n    object.__setattr__(self, 'payload', scalar_int(self.payload))\n"
        "@classmethod\ndef make(cls, f):\n    return cls(payload=method_of(f, 'x')())\n"
    )
    sometimes = (
        "def __post_init__(self):\n    if self.flag:\n        object.__setattr__(self, 'payload', scalar_int(self.payload))\n"
        "@classmethod\ndef make(cls, f):\n    return cls(payload=method_of(f, 'x')())\n"
    )
    assert _violations(always) == []
    assert _violations(sometimes) == ["stores an unread result of foreign code"]


def test_the_guard_does_not_trust_attributes_read_by_a_dynamic_name():
    body = "@classmethod\ndef make(cls, value, name):\n    return cls(flag=attribute_of(value, name) == 1)\n"
    assert _violations(body) == ["comparison of foreign"]


@pytest.mark.parametrize(
    "body, expected",
    [
        # 値の型の code を呼ぶ組み込み・属性の書き込み・型の constructor（独立 review 2 巡目）
        ("@classmethod\ndef make(cls, value):\n    if hasattr(value, 'a'):\n        return cls(name='a')\n    return None\n", ["attribute of unknown"]),
        ("@classmethod\ndef make(cls, value):\n    from collections.abc import Mapping\n    return cls(flag=issubclass(type(value), Mapping))\n",
         ["issubclass reads the class of a value (use is_kind)"]),
        ("@classmethod\ndef make(cls, value):\n    names = dir(value)\n    return cls(name='a')\n", ["dir() of unknown"]),
        ("@classmethod\ndef make(cls, value):\n    other = type(value)(1)\n    return cls(name='a')\n", ["constructs the type of unknown"]),
        ("@classmethod\ndef make(cls, value):\n    value.seen = True\n    return cls(name='a')\n", ["attribute store on unknown"]),
        ("@classmethod\ndef make(cls, value):\n    return cls(name=f'{1:{value}}')\n", ["format"]),
        # 解析しない構文は使うと違反
        ("@classmethod\ndef make(cls, value):\n    class Inner:\n        seen = value > 1\n    return cls(name='a')\n", ["ClassDef is not tracked"]),
        ("@classmethod\ndef make(cls, value):\n    def inner(a=value.foo):\n        return a\n    return cls(name='a')\n",
         ["defaults or decorators of a nested function are not tracked"]),
        # 標準の library の関数・正体の分からない callable へ読まずに渡す
        ("@classmethod\ndef make(cls, value):\n    from math import floor\n    return cls(name=scalar_text(floor(value)))\n", ["passes unknown to floor"]),
        ("@classmethod\ndef make(cls, value, choose):\n    reader = exact_tree if choose else len\n    return cls(name=scalar_text(reader(value)))\n",
         ["passes unknown to foreign code", "truthiness of unknown"]),
        # 別名・呼び先・入れ子の関数を通した容器の変異
        ("@classmethod\ndef make(cls, value):\n    items = []\n    alias = items\n    alias.append(value)\n    return cls(flag=items[0] > 1)\n", ["comparison of unknown"]),
        ("@classmethod\ndef make(cls, value):\n    items = []\n    def add(x):\n        items.append(x)\n    add(value)\n    return cls(flag=items[0] > 1)\n",
         ["comparison of unknown"]),
        # 辿れない（source の無い）package の module の関数へ読まずに渡す
        ("@classmethod\ndef make(cls, value):\n    from scripts.function_tracer_pcode.core.no_such_module import judge\n"
         "    return cls(flag=scalar_bool(judge(value)))\n", ["passes unknown to package code outside the guard"]),
        ("@classmethod\ndef make(cls, value):\n    from scripts.function_tracer_pcode.core.no_such_module import judge\n"
         "    return cls(flag=scalar_bool(judge(exact_tree(value))))\n", []),
        # 例外の照合は型の `__subclasscheck__`
        ("@classmethod\ndef make(cls, value):\n    try:\n        return cls(name='a')\n    except value:\n        return None\n", ["except matches an unread value"]),
    ],
)
def test_the_guard_closes_the_second_independent_review_holes(body, expected):
    assert _violations(body) == expected


def test_the_guard_requires_unevaluated_annotations():
    source = HEADER.replace("from __future__ import annotations\n", "") + "    name: str = ''\n"
    guard = ConstructionGuard({"scripts.function_tracer_pcode.core.runtime_refs.sample": source}, _World())
    assert [v.split(": ", 2)[1] for v in guard.violations()] == ["annotations are evaluated (line 1)"]


DEPENDENCY = """
from __future__ import annotations
from scripts.function_tracer_pcode.core import live_values


def is_void(data_type):
    length = data_type.getLength()
    return int(length) == 0


def is_void_read(data_type):
    length = live_values.method_of(data_type, "getLength")()
    return live_values.scalar_int(length) == 0
"""


@pytest.mark.parametrize(
    "call, expected",
    [
        # 依存先（ref module でない package の module）の到達した関数も同じ規則で検査する（第 5 回 P1: opaque な
        # object を読んだことを、その先で API から取得する値の安全の根拠にしない）
        ("is_void", ["dependency.py:is_void: comparison of unknown: int(length) == 0", "dependency.py:is_void: int() of foreign: int(length)"]),
        ("is_void_read", []),
    ],
)
def test_the_guard_follows_reached_package_dependencies(call, expected):
    body = (
        "@classmethod\ndef make(cls, value):\n"
        f"    from scripts.function_tracer_pcode.core.dependency import {call}\n"
        f"    return cls(flag=scalar_bool({call}(exact_tree(value))))\n"
    )
    source = HEADER + textwrap.indent(textwrap.dedent(body), "    ")
    guard = ConstructionGuard(
        {"scripts.function_tracer_pcode.core.runtime_refs.sample": source}, _World(),
        dependency_sources={"scripts.function_tracer_pcode.core.dependency": DEPENDENCY},
    )
    assert [v.rsplit(" (line ", 1)[0] for v in guard.violations()] == expected
    assert f"dependency:None.{call}" in guard.reached()


@pytest.mark.parametrize(
    "body, expected",
    [
        # `exact_tree` の結果（組み込みの木）の葉は外の object かもしれない: その method / 属性の結果は外の code の結果
        ("@classmethod\ndef make(cls, value):\n    data = exact_tree(value)\n    return cls(flag=int(data.getLength()) == 0)\n",
         ["comparison of unknown", "int() of foreign"]),
        ("@classmethod\ndef make(cls, value):\n    data = exact_tree(value)\n    return cls(flag=scalar_int(data.getLength()) == 0)\n", []),
        ("@classmethod\ndef make(cls, value):\n    data = exact_tree(value)\n    return cls(flag=bool(data.size))\n", ["bool() of foreign"]),
        # 葉を写した値（`exact_scalar`）の method の結果も、外の object なら外の code の結果
        ("@classmethod\ndef make(cls, value):\n    name = exact_scalar(value)\n    return cls(flag=name.lower() == 'x')\n",
         ["comparison of foreign"]),
        # 木そのものの消費は clean と同じ（容器と scalar の葉は組み込みの型そのもの）
        ("@classmethod\ndef make(cls, value):\n    data = exact_tree(value)\n    return cls(flag=data == (1,), name=str(data))\n", []),
        # import した外の class の静的な method・属性は読んでよい（値ではない）。結果は外の code の結果
        ("@classmethod\ndef make(cls, value):\n    from math import nan\n    from ghidra.program.model.data import VoidDataType\n"
         "    return cls(flag=bool(VoidDataType.isVoidDataType(exact_tree(value))))\n", ["bool() of foreign"]),
        ("@classmethod\ndef make(cls, value):\n    from ghidra.program.model.data import VoidDataType\n"
         "    return cls(flag=scalar_bool(VoidDataType.isVoidDataType(exact_tree(value))))\n", []),
        ("@classmethod\ndef make(cls, value):\n    from ghidra.program.model.data import VoidDataType\n"
         "    return cls(flag=bool(VoidDataType.ALL))\n", ["bool() of foreign"]),
    ],
)
def test_the_guard_does_not_trust_values_obtained_from_objects_it_only_read(body, expected):
    assert _violations(body) == expected


DEPENDENCY_LAYERS = {
    "scripts.function_tracer_pcode.core.dependency": """
from __future__ import annotations
from scripts.function_tracer_pcode.core.dependency2 import deep as reexported


def via_module(data_type):
    return int(data_type.getLength()) == 0


def via_alias(data_type):
    return int(data_type.getLength()) == 0


def via_assigned(data_type):
    return int(data_type.getLength()) == 0


def via_table(data_type):
    return int(data_type.getLength()) == 0


def via_local_table(data_type):
    return int(data_type.getLength()) == 0


def via_getattr(data_type):
    return int(data_type.getLength()) == 0


table = {"void": via_table}
via_lambda = lambda data_type: int(data_type.getLength()) == 0
""",
    "scripts.function_tracer_pcode.core.dependency2": """
from __future__ import annotations


def deep(data_type):
    return int(data_type.getLength()) == 0
""",
}


@pytest.mark.parametrize(
    "call, target",
    [
        pytest.param("from scripts.function_tracer_pcode.core import dependency\n    return dependency.via_module(exact_tree(value))",
                     "dependency.py:via_module", id="module_form"),
        pytest.param("import scripts.function_tracer_pcode.core.dependency as dep\n    return dep.via_alias(exact_tree(value))",
                     "dependency.py:via_alias", id="module_alias"),
        pytest.param("from scripts.function_tracer_pcode.core.dependency import via_assigned\n    check = via_assigned\n"
                     "    return check(exact_tree(value))", "dependency.py:via_assigned", id="assigned_alias"),
        pytest.param("from scripts.function_tracer_pcode.core.dependency import table\n    return table['void'](exact_tree(value))",
                     "dependency.py:via_table", id="table_in_dependency"),
        pytest.param("from scripts.function_tracer_pcode.core.dependency import via_local_table\n"
                     "    return {'k': via_local_table}['k'](exact_tree(value))", "dependency.py:via_local_table", id="local_table"),
        pytest.param("from scripts.function_tracer_pcode.core import dependency\n    return getattr(dependency, 'via_getattr')(exact_tree(value))",
                     "dependency.py:via_getattr", id="getattr_module"),
        pytest.param("from scripts.function_tracer_pcode.core.dependency import via_lambda\n    return via_lambda(exact_tree(value))",
                     "dependency.py:via_lambda", id="module_lambda"),
        pytest.param("from scripts.function_tracer_pcode.core.dependency import reexported\n    return reexported(exact_tree(value))",
                     "dependency2.py:deep", id="reexport"),
    ],
)
def test_the_guard_follows_dependencies_however_they_are_reached(call, target):
    """依存先の関数を名前で直接呼ぶ以外の形（module の形・別名・表・`getattr`・lambda・再 export）でも検査する。
    呼び出し以外の位置で参照される関数は、どこから何で呼ばれるか追えないので起点（引数は未確認）として検査する。
    形ごとに別の関数を置き、違反がその関数の中に出ることを確かめる（別の形が同じ関数を検査して隠さない）。"""

    body = "@classmethod\ndef make(cls, value):\n    " + call + "\n"
    source = HEADER + textwrap.indent(body, "    ")
    guard = ConstructionGuard(
        {"scripts.function_tracer_pcode.core.runtime_refs.sample": source}, _World(),
        dependency_sources=DEPENDENCY_LAYERS,
    )
    found = [v.rsplit(": ", 1)[0] for v in guard.violations()]
    assert any(v.startswith(target + ": int() of") for v in found), guard.violations()


@pytest.mark.parametrize(
    "body, expected",
    [
        # 出口で写さない key（`proven=True`）は、本体がどの経路でも読み終えた値を返すことを guard が確かめる
        ("@runtime_ref_key(proven=True)\ndef semantic_key(self, value):\n    return ('k', exact_tree(value))\n", []),
        ("@runtime_ref_key(proven=True)\ndef semantic_key(self, value):\n    return ('k', method_of(value, 'key')())\n",
         ['proven key returns tup:["clean", "foreign"]', "returns an unread result of foreign code"]),
        # 出口で写す key は外の code の結果を返してよい（出口が組み込みの木にする）
        ("@runtime_ref_key\ndef semantic_key(self, value):\n    return ('k', method_of(value, 'key')())\n", []),
    ],
)
def test_the_guard_checks_keys_that_skip_the_exit_copy(body, expected):
    assert _violations(body) == expected


def test_the_guard_reads_scalar_fields_as_trees_from_the_owner():
    """scalar / bool の field は owner が組み込みの木にした値（型の誤りの容器の葉に外の object があり得る）: その
    method の結果は外の code の結果。"""

    assert _violations("def describe(self):\n    return int(self.name.getLength())\n") == ["int() of foreign"]
    assert _violations("def describe(self):\n    return self.name == 'x'\n") == []
