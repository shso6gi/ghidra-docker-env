# -*- coding: utf-8 -*-
"""左右の binary の値を比べる式の AST 棚卸し（plan v4 PR-P、U4）。

``test_cross_binary_comparisons.py`` と baseline の再生成の両方が使う唯一の走査。左の側の名前
（``left`` / ``lhs`` / ``*1`` …）だけに結び付いた値と、右の側の名前だけに結び付いた値を比べる node
（``==`` / ``!=`` / ``in`` / ``is``、集合の演算、片側の容器を他方で引く、登録した比較 helper の左右の
引数）を数える。名前の規則で見つけるので、片側の中の lhs / rhs（二項演算の operand）も拾う: 分類は
baseline の role が持つ。
"""

from __future__ import annotations

import ast
import hashlib
import re
from pathlib import Path
from typing import Dict, Iterator, List, Tuple

PACKAGE_ROOT = Path(__file__).resolve().parents[2]

#: 左右の binary の値を比べ得る層（analysis / semantics は 1 つの関数の中しか見ない）。
SCANNED_ROOTS = ("proof", "checker", "authority", "core/runtime_refs")

_STEMS = (
    "analysis|case|function|summary|ref|key|expr|value|params|parameters|binary|program|info|effect"
    "|fact|seed|ret|cases|facts|side|keys|loop|term|count|identity|values"
)
_LEFT = re.compile(rf"(^|_)(left|lhs)(_|$)|^({_STEMS})1$|({_STEMS})1(_|$)")
_RIGHT = re.compile(rf"(^|_)(right|rhs|peer)(_|$)|^({_STEMS})2$|({_STEMS})2(_|$)")
_SET_METHODS = frozenset({"intersection", "issubset", "issuperset", "isdisjoint", "symmetric_difference", "difference"})
#: 左右の値を owner を含まない key で比べる helper（第 1・第 2 引数が左右）。
COMPARISON_HELPERS = frozenset({
    "are_structurally_equivalent", "_cross_binary_call_effect_component_key", "semantic_key",
    "pairwise_semantic_key", "pairwise_exact_key", "loop_summary_method_b_key", "compare_loop_summaries",
    "_deferred_call_match_key",
})


def _names(node: ast.AST) -> set:
    found = set()
    for item in ast.walk(node):
        if isinstance(item, ast.Name):
            found.add(item.id)
        elif isinstance(item, ast.Attribute):
            found.add(item.attr)
        elif isinstance(item, ast.arg):
            found.add(item.arg)
    return found


def _side(node: ast.AST) -> Tuple[bool, bool]:
    names = _names(node)
    return any(_LEFT.search(name) for name in names), any(_RIGHT.search(name) for name in names)


def _cross(first: ast.AST, second: ast.AST) -> bool:
    left_a, right_a = _side(first)
    left_b, right_b = _side(second)
    return (left_a and not right_a and right_b and not left_b) or (right_a and not left_a and left_b and not right_b)


def _kind(node: ast.AST) -> str:
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        if isinstance(node.ops[0], (ast.In, ast.NotIn, ast.Eq, ast.NotEq, ast.Is, ast.IsNot)) and _cross(
            node.left, node.comparators[0]
        ):
            return "compare"
    elif isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in _SET_METHODS:
        if node.args and _cross(node.func.value, node.args[0]):
            return "set_operation"
    elif isinstance(node, ast.Subscript) and not isinstance(node.slice, (ast.Constant, ast.Slice)):
        if _cross(node.value, node.slice):
            return "lookup"
    elif isinstance(node, ast.Call) and len(node.args) >= 2:
        name = node.func.attr if isinstance(node.func, ast.Attribute) else getattr(node.func, "id", "")
        if name in COMPARISON_HELPERS and _cross(node.args[0], node.args[1]):
            return "helper:" + name
    return ""


def _qualnames(tree: ast.AST) -> Dict[int, str]:
    owners: Dict[int, str] = {}

    def visit(node: ast.AST, prefix: str) -> None:
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                name = f"{prefix}.{child.name}" if prefix else child.name
                for item in ast.walk(child):
                    owners[id(item)] = name
                visit(child, name)
            else:
                visit(child, prefix)

    visit(tree, "")
    return owners


def _normalized_digest(source: str) -> str:
    return hashlib.sha256(" ".join(source.split()).encode("utf-8")).hexdigest()[:16]


def scan() -> Iterator[Tuple[str, str, str, str]]:
    """(相対 path, 関数の qualname, node の種類, 正規化した source の digest) を 1 node ずつ。"""

    for root in SCANNED_ROOTS:
        for path in sorted((PACKAGE_ROOT / root).rglob("*.py")):
            text = path.read_text(encoding="utf-8")
            tree = ast.parse(text)
            owners = _qualnames(tree)
            relative = path.relative_to(PACKAGE_ROOT).as_posix()
            for node in ast.walk(tree):
                kind = _kind(node)
                if kind:
                    source = ast.get_source_segment(text, node) or ""
                    yield relative, owners.get(id(node), "<module>"), kind, _normalized_digest(source)


def scan_keys() -> List[Tuple[str, str, str, str]]:
    return sorted(scan())
