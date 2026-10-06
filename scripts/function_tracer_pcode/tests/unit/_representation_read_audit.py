"""LEGACY 表現が意味値から何を読むかの静的な監査（Issue #219 T-A5）。

表現を作る method（入口と、そこから `self.<method>(...)` で辿る method）について、意味値の状態の
読みを **すべて** 列挙する。列挙できない記法は violation にする（監査の外へ依存を逃がさない）:

* `self.<name>` の読み → field の読み（method なら辿る。`escapes` に理由つきで挙げた method は辿らない）
* `getattr(self, "<定数>"[, 既定値])` → その名前の読み。名前が定数でない `getattr` は violation
* `self` を上のどれでもない形で使う（他の関数へ渡す・別名に入れる・`vars(self)` /
  `self.__dict__`）→ violation。ただし `id(self)` / `type(self)` と、`escapes` に挙げた関数への受け渡しは許す
* 局所の値（子・分岐の条件・直列化の作業量など）の属性の読み → `local_reads` に分類があるものだけ。
  分類の無い読み・`getattr(<局所>, ...)` は violation
* 定数でない既定引数（呼び出しをまたいで共有される可変な状態になり得る）→ violation

返す field の集合を、呼ぶ側が lifecycle の表（`*_SERIALIZATION_INPUTS`）と照合する。
"""

from __future__ import annotations

import ast
import inspect
import textwrap
import types
from typing import Dict, List, Mapping, Set, Tuple

_SELF_SAFE_BUILTINS = frozenset({"id", "type"})
_DYNAMIC_READS = frozenset({"getattr", "vars", "hasattr", "setattr", "delattr"})


def _method_tree(kind: type, name: str) -> ast.FunctionDef:
    member = kind.__dict__[name]
    function = getattr(member, "__func__", member)
    tree = ast.parse(textwrap.dedent(inspect.getsource(function)))
    node = tree.body[0]
    assert isinstance(node, ast.FunctionDef), (kind, name)
    return node


def audit_representation_reads(
    kind: type,
    entries: Tuple[str, ...],
    *,
    escapes: Mapping[str, str],
    local_reads: Mapping[Tuple[str, str], str],
) -> Tuple[Set[str], List[str], Dict[Tuple[str, str], Set[str]]]:
    """`(読む field, violation, 実際に使った local_reads の分類)` を返す。"""

    fields: Set[str] = set()
    violations: List[str] = []
    used_local: Dict[Tuple[str, str], Set[str]] = {}
    pending = list(entries)
    audited: Set[str] = set()
    while pending:
        name = pending.pop()
        if name in audited:
            continue
        audited.add(name)
        if name not in kind.__dict__:
            violations.append(f"{kind.__name__}.{name}: not defined on the class")
            continue
        function = _method_tree(kind, name)
        self_name = function.args.args[0].arg
        where = f"{kind.__name__}.{name}"
        # 既定引数は呼び出しをまたいで共有される状態: 不変な定数だけを許す
        for default in (*function.args.defaults, *(d for d in function.args.kw_defaults if d is not None)):
            if not isinstance(default, ast.Constant):
                violations.append(f"{where}:{default.lineno}: a default argument that is not a constant")
        parents: Dict[int, ast.AST] = {}
        for node in ast.walk(function):
            for child in ast.iter_child_nodes(node):
                parents[id(child)] = node
        for node in ast.walk(function):
            if not isinstance(node, ast.Name):
                continue
            if node.id in _DYNAMIC_READS and isinstance(node.ctx, ast.Load):
                call = parents.get(id(node))
                if (
                    node.id == "getattr"
                    and isinstance(call, ast.Call)
                    and call.func is node
                    and len(call.args) >= 2
                    and isinstance(call.args[0], ast.Name)
                    and call.args[0].id == self_name
                    and isinstance(call.args[1], ast.Constant)
                    and isinstance(call.args[1].value, str)
                ):
                    fields.add(call.args[1].value)
                    continue
                violations.append(f"{where}:{node.lineno}: {node.id}() is not an auditable read")
                continue
            if node.id != self_name or not isinstance(node.ctx, ast.Load):
                continue
            parent = parents.get(id(node))
            if isinstance(parent, ast.Attribute) and parent.value is node:
                attribute = parent.attr
                if attribute == "__dict__":
                    violations.append(f"{where}:{node.lineno}: reads self.__dict__")
                    continue
                if _is_method(kind, attribute):
                    if attribute not in escapes:
                        pending.append(attribute)
                    continue
                fields.add(attribute)
                continue
            if isinstance(parent, ast.Call) and node in parent.args:
                callee = parent.func
                if isinstance(callee, ast.Name) and callee.id in _SELF_SAFE_BUILTINS:
                    continue
                if isinstance(callee, ast.Name) and callee.id == "getattr":
                    continue  # 上で数えた（定数の名前）/ 拒否した
                if isinstance(callee, ast.Name) and callee.id in escapes:
                    continue
            violations.append(f"{where}:{node.lineno}: self is used in a form the audit cannot enumerate")
        for node in ast.walk(function):
            if (
                isinstance(node, ast.Attribute)
                and isinstance(node.ctx, ast.Load)
                and isinstance(node.value, ast.Name)
                and node.value.id != self_name
                and node.value.id in _local_names(function)
            ):
                key = (node.value.id, node.attr)
                if key not in local_reads:
                    violations.append(f"{where}:{node.lineno}: unclassified read {node.value.id}.{node.attr}")
                else:
                    used_local.setdefault(key, set()).add(where)
    return fields, violations, used_local


def _is_method(kind: type, name: str) -> bool:
    for base in kind.__mro__:
        if name in base.__dict__:
            return isinstance(base.__dict__[name], (types.FunctionType, staticmethod, classmethod, property))
    return False


def _local_names(function: ast.FunctionDef) -> Set[str]:
    names = {arg.arg for arg in (*function.args.posonlyargs, *function.args.args, *function.args.kwonlyargs)}
    for arg in (function.args.vararg, function.args.kwarg):
        if arg is not None:
            names.add(arg.arg)
    for node in ast.walk(function):
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
            names.add(node.id)
    return names
