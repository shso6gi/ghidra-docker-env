# -*- coding: utf-8 -*-
"""unit test は pair 1 つと同じ寿命の条件 cache の scope の中で走る（Issue #224）。

`tests/conftest.py::_pair_condition_cache_scope` が test ごとに空の `condition_cache_scope()` を
開く。production の pair 境界と同じく、test をまたいで意味の状態を持ち越さない。scope の外を
確かめる test だけが `@pytest.mark.unscoped_condition_cache` で外れ、その印を使ってよい file は
下の表に限る（scope を外すのは scope そのものの契約を確かめるときだけ）。
"""

from __future__ import annotations

import ast
import pathlib

import pytest

from scripts.function_tracer_pcode.analysis.condition.condition_cache import (
    active_condition_cache,
    cache_lookup,
    cache_store,
)
from scripts.function_tracer_pcode.tests.conftest import UNSCOPED_CONDITION_CACHE

UNIT_ROOT = pathlib.Path(__file__).resolve().parent

#: scope の外の挙動・scope の入れ子を確かめる test を持つ file（印を使ってよい file）
_UNSCOPED_ALLOWED = {
    "test_issue105a_condition_identity_cache.py",
    "test_issue105b_simplify_budgets.py",
    "test_issue224_test_condition_cache_scope.py",
}

_SEEN_STORES: list = []


def test_a_test_runs_inside_a_fresh_condition_cache_scope():
    store = active_condition_cache()
    assert store is not None
    assert cache_lookup("issue224.probe", ("k",)) == (False, None)
    cache_store("issue224.probe", ("k",), True)
    assert cache_lookup("issue224.probe", ("k",)) == (True, True)
    _SEEN_STORES.append(store)


def test_the_next_test_does_not_see_the_previous_store():
    """前の test が覚えた値は次の test に残らない（store は test ごとに新しい）。"""

    store = active_condition_cache()
    assert store is not None
    assert all(store is not previous for previous in _SEEN_STORES)
    assert cache_lookup("issue224.probe", ("k",)) == (False, None)


@pytest.mark.unscoped_condition_cache
def test_the_opt_out_runs_outside_any_scope():
    assert active_condition_cache() is None


def _marked_files():
    marked = set()
    for path in sorted(UNIT_ROOT.rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Attribute) and node.attr == UNSCOPED_CONDITION_CACHE:
                marked.add(path.name)
            elif isinstance(node, ast.Constant) and node.value == UNSCOPED_CONDITION_CACHE:
                marked.add(path.name)
    return marked


def test_only_the_scope_contract_tests_opt_out_of_the_scope():
    """印を使う file は、scope の契約を確かめる file の表に限る（test を scope から外して
    production と違う条件で走らせることを、印 1 つで黙って増やさない）。"""

    assert _marked_files() <= _UNSCOPED_ALLOWED


# ---------------------------------------------------------------------------
# 静的な guard が共有する source の AST（`tests/unit/_package_sources`）
# ---------------------------------------------------------------------------


def test_the_same_text_gives_the_same_tree_and_a_changed_text_is_parsed_again(tmp_path):
    from scripts.function_tracer_pcode.tests.unit import _package_sources

    path = tmp_path / "m.py"
    path.write_text("x = 1\n", encoding="utf-8")
    first = _package_sources.parse_source(path, filename=str(path))
    assert _package_sources.parse_source(path, filename=str(path)) is first
    assert ast.dump(first) == ast.dump(ast.parse("x = 1\n"))
    # filename が違えば別の値（SyntaxError の文面・code の filename が違う）
    assert _package_sources.parse_source(path) is not first
    # text が変われば parse し直す（共有が test の書き換えを覆い隠さない）
    path.write_text("y = 2\n", encoding="utf-8")
    second = _package_sources.parse_source(path, filename=str(path))
    assert second is not first
    assert ast.dump(second) == ast.dump(ast.parse("y = 2\n"))


def _issue_and_then(tmp_path, after):
    """木を 1 つ渡し、`after(path)`（cache の entry を増やす・捨てる操作）をした後のその木を返す。"""

    from scripts.function_tracer_pcode.tests.unit import _package_sources

    path = tmp_path / "m.py"
    path.write_text("x = 1\n", encoding="utf-8")
    tree = _package_sources.parse_source(path, filename=str(path))
    after(path)
    return tree


def _rewrite_source(path):
    from scripts.function_tracer_pcode.tests.unit import _package_sources

    path.write_text("y = 2\n", encoding="utf-8")
    _package_sources.parse_source(path, filename=str(path))


def _change_filename(path):
    from scripts.function_tracer_pcode.tests.unit import _package_sources

    _package_sources.parse_source(path)
    _package_sources.parse_source(path, filename="other.py")


def _clear_cache(_path):
    from scripts.function_tracer_pcode.tests.unit import _package_sources

    _package_sources.clear_cache()


_AFTER = {
    "nothing": lambda _path: None,
    "source_rewritten": _rewrite_source,
    "filename_changed": _change_filename,
    "cache_cleared": _clear_cache,
}
_MUTATIONS = {
    # (書き換え, 元に戻す)
    "name": (lambda t: setattr(t.body[0].targets[0], "id", "mutated"),
             lambda t: setattr(t.body[0].targets[0], "id", "x")),
    "position_only": (lambda t: setattr(t.body[0], "lineno", 99),
                      lambda t: setattr(t.body[0], "lineno", 1)),
    "appended_statement": (lambda t: t.body.append(ast.Pass(lineno=2, col_offset=0, end_lineno=2, end_col_offset=4)),
                           lambda t: t.body.pop()),
}


@pytest.mark.parametrize("after", sorted(_AFTER))
@pytest.mark.parametrize("mutation", sorted(_MUTATIONS))
def test_any_mutation_of_any_issued_tree_is_reported(tmp_path, after, mutation):
    """渡した木の書き換えは、その後に source・filename が変わっても、cache が捨てられても、位置の
    属性だけの書き換えでも、session の終わりの確かめ（`changed_trees`）が見つける。"""

    from scripts.function_tracer_pcode.tests.unit import _package_sources

    tree = _issue_and_then(tmp_path, _AFTER[after])
    mutate, restore = _MUTATIONS[mutation]
    assert _package_sources.changed_trees(among=(tree,)) == []
    mutate(tree)
    try:
        changed = _package_sources.changed_trees(among=(tree,))
        assert len(changed) == 1 and str((tmp_path / "m.py").resolve()) in changed[0]
    finally:
        # この test の書き換えを残さない（session の終わりの確かめを汚さない）
        restore(tree)
    assert _package_sources.changed_trees(among=(tree,)) == []
