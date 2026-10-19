# -*- coding: utf-8 -*-
"""digest（と型を落とす再符号化）の値を lookup / 束ねの key にする node の走査（`test_digest_lookup_keys.py` 用）。

source: 名前に digest を含む呼び出し・属性、`json.dumps`・`_jsonable`・`canonical_value`・`repr` の結果と、
それを代入・for で受けた名前（tuple の要素を含む）、digest を返す同じ package の関数の結果。
sink: `in` / `.add` / `.get` / `.setdefault` / `.pop` / `.fromkeys` / `.discard` / `.remove` / subscript /
dict・set の literal と内包 / `sorted`・`Counter`・`set` の等値比較。test は対象外。
"""

import ast, pathlib, sys, collections
SOURCE_CALLS = {"dumps", "_jsonable", "canonical_value", "repr"}
LOOKUP = {"add", "setdefault", "get", "pop", "fromkeys", "discard", "remove", "__contains__"}
def call_name(node):
    f = node.func
    return f.attr if isinstance(f, ast.Attribute) else (f.id if isinstance(f, ast.Name) else "")

def _own_nodes(scope):
    """scope の node（入れ子の関数・lambda・class の中は除く: それぞれ自分の scope で数える）。"""

    nodes = []
    stack = list(scope.body) if isinstance(scope.body, list) else [scope.body]
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        if isinstance(node, ast.ClassDef):
            stack.extend(node.body)
            continue
        nodes.append(node)
        for child in ast.iter_child_nodes(node):
            stack.append(child)
    return nodes

def scan_tree(tree, rel, found, returning):
    scopes = [tree] + [n for n in ast.walk(tree) if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))]
    for scope in scopes:
        body_nodes = _own_nodes(scope)
        tainted = set()
        def src(e):
            if isinstance(e, ast.Call):
                n = call_name(e)
                if "digest" in n.lower() or n in SOURCE_CALLS or n in returning: return True
            if isinstance(e, ast.Attribute) and "digest" in e.attr.lower(): return True
            if isinstance(e, ast.Name) and e.id in tainted: return True
            if isinstance(e, (ast.Tuple, ast.List)) and any(src(x) for x in e.elts): return True
            if isinstance(e, ast.JoinedStr): return False
            return False
        for _ in range(3):
            for n in body_nodes:
                if isinstance(n, ast.Assign) and src(n.value):
                    for t in n.targets:
                        elts = t.elts if isinstance(t, (ast.Tuple, ast.List)) else [t]
                        for x in elts:
                            if isinstance(x, ast.Name): tainted.add(x.id)
                elif isinstance(n, ast.AnnAssign) and n.value is not None and src(n.value) and isinstance(n.target, ast.Name):
                    tainted.add(n.target.id)
                elif isinstance(n, (ast.For, ast.comprehension)):
                    it = n.iter
                    if src(it) or (isinstance(it, ast.Call) and call_name(it) in {"sorted", "tuple", "list", "set", "reversed"} and any(src(a) for a in it.args)):
                        elts = n.target.elts if isinstance(n.target, (ast.Tuple, ast.List)) else [n.target]
                        for x in elts:
                            if isinstance(x, ast.Name): tainted.add(x.id)
        fn = getattr(scope, "name", "<module>" if isinstance(scope, ast.Module) else "<lambda>")
        for n in body_nodes:
            kind = None
            if isinstance(n, ast.Compare):
                ops = n.ops
                if any(isinstance(o, (ast.In, ast.NotIn)) for o in ops) and src(n.left): kind = "in"
                elif any(isinstance(o, (ast.Eq, ast.NotEq)) for o in ops):
                    sides = [n.left] + n.comparators
                    def coll(e):
                        return isinstance(e, ast.Call) and call_name(e) in {"sorted", "Counter", "set", "frozenset", "tuple"} and e.args and (src(e.args[0]) or (isinstance(e.args[0], (ast.GeneratorExp, ast.ListComp, ast.SetComp)) and src(e.args[0].elt)))
                    if sum(1 for e in sides if coll(e)) >= 1 and all(coll(e) or src(e) for e in sides): kind = "collection_eq"
            elif isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr in LOOKUP and n.args and src(n.args[0]): kind = n.func.attr
            elif isinstance(n, ast.Subscript) and isinstance(n.ctx, (ast.Load, ast.Store, ast.Del)) and src(n.slice): kind = "subscript"
            elif isinstance(n, ast.Dict) and any(k is not None and src(k) for k in n.keys): kind = "dict_key"
            elif isinstance(n, ast.DictComp) and src(n.key): kind = "dict_comp_key"
            elif isinstance(n, ast.SetComp) and src(n.elt): kind = "set_comp"
            elif isinstance(n, ast.Set) and any(src(e) for e in n.elts): kind = "set_literal"
            elif isinstance(n, ast.Call) and call_name(n) in {"set", "frozenset", "Counter"} and n.args and isinstance(n.args[0], (ast.GeneratorExp, ast.ListComp)) and src(n.args[0].elt): kind = "set_of"
            if kind: found[(rel, fn, kind)] += 1
def returning_helpers(trees):
    names = set()
    for tree in trees:
        for f in ast.walk(tree):
            if isinstance(f, (ast.FunctionDef,)):
                for r in ast.walk(f):
                    if isinstance(r, ast.Return) and isinstance(r.value, ast.Call) and "digest" in call_name(r.value).lower():
                        names.add(f.name)
    return names
def scan(root):
    root = pathlib.Path(root)
    files = [p for p in sorted(root.rglob("*.py")) if p.relative_to(root).parts[0] != "tests"]
    trees = {p: ast.parse(p.read_text(encoding="utf-8")) for p in files}
    returning = returning_helpers(trees.values())
    found = collections.Counter()
    for p, t in trees.items(): scan_tree(t, str(p.relative_to(root)), found, returning)
    return found
