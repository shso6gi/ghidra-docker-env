"""bounded path の live な値の流れの静的な監査（J19 の本体。Issue #22 PR-22-D）。

**許す能力（positive capability）**: bounded path の関数が live な値（record の field・converter /
reducer の引数・出力の入口が受け取る結果）にしてよいことは、次だけ。

* `core.live_values` / `core.json_encoding`（owner）の関数・walker の API に渡す
* yield / return する・変数に入れる・組み込みの tuple / list に入れて渡す
* `is` / `is not` で比べる・`type(x)` を取る・`issubclass(type(x), T)` で型を調べる
* `type(x) is C`（C は package の型）で確かめた後に、C の method / field を使う
* `type(x) is str` などで確かめた後に、組み込みの値として使う

それ以外（属性・添字・呼び出し・反復・真偽・比較・演算・hash・format・組み込み関数・未解決の
method への引数）は違反として列挙する。関数を跨ぐ流れは、package の関数の引数・戻り値として
追う（呼び出し先を同じ規則で監査する）。owner の module の中は監査しない（owner の規則は
J20 と adversarial test が守る）。
"""

from __future__ import annotations

import ast
import collections
import pathlib
from typing import Dict, Iterable, List, Optional, Set, Tuple

PKG = "scripts.function_tracer_pcode"
OWNER_MODULES = frozenset({PKG + ".core.json_encoding", PKG + ".core.live_values"})
#: 外部の依存（D）: live な値を渡すこと自体を違反にする
EXTERNAL_PREFIXES = (PKG + ".authority.", PKG + ".cli.")

LIVE = "LIVE"  # live な値
ITER = "ITER"  # 組み込みの iterator（要素が live）
CONT = "CONT"  # package が作った組み込みの容器（要素が live）
SELF = "SELF"  # package の object 自身の状態（record でない method の self）
WORK = "WORK"  # 作業量 / 予算 / policy（owner の object）
REC = "REC"    # "REC:<module>:<class>": 型を確かめた package の object（field は live）
OBJ = "OBJ"    # "OBJ:<module>:<class>": package が plain な引数で作った object（field は自身の状態）
VER = "VER"    # live だが組み込みの振る舞いを確かめた容器（反復・`len`・真偽は組み込みの slot）

RECORD_METHODS = frozenset({"json_items", "__json_tree__", "__json_tree_bytes__", "__json_tree_metered__", "__json_identity__"})
WORK_PARAMETER_NAMES = frozenset({"work", "budget", "effort", "meter", "units"})

#: live_values の関数の戻り値の種類（書いていない関数は plain な値を返す）
LIVE_VALUES_RESULTS = {
    "attribute": LIVE,
    "instance_state": LIVE,
    "field_value": LIVE,
    "enum_value": LIVE,
    "lookup": LIVE,
    "merged_mappings": CONT,
    "items_of": ITER,
    "values_of": ITER,
    "elements_of": ITER,
    "builtin_mapping": VER,
}
#: 真のとき引数を VER にする live_values の述語
VERIFYING_PREDICATES = frozenset({"builtin_sequence", "builtin_set", "builtin_iterator", "builtin_container"})
#: owner の関数 / method の戻り値の種類（書いていないものは plain な値を返す）。`materialize` の
#: LEGACY の写しは `raw` の葉を live なまま持つ
OWNER_RESULTS = {"_walk_iter": ITER, "materialize": CONT}

_PLAIN_TYPES = frozenset({"str", "int", "float", "bool", "bytes", "NoneType"})
_CONTAINER_TYPES = frozenset({"tuple", "list", "dict", "set", "frozenset"})
_BUILTIN_TYPE_NAMES = _PLAIN_TYPES | _CONTAINER_TYPES | {"object", "type", "BaseException", "Enum", "OrderedDict"}
_SAFE_BUILTINS = frozenset({"type", "id", "issubclass", "super", "range"})
_EXCEPTION_NAMES = frozenset({
    "ValueError", "TypeError", "KeyError", "RuntimeError", "AttributeError", "AssertionError",
    "IndexError", "OverflowError", "NotImplementedError",
})
_APPEND_METHODS = frozenset({"append", "insert", "appendleft"})


def is_rec(kind) -> bool:
    return isinstance(kind, str) and kind.startswith(REC)


def rec(module: str, cls: str) -> str:
    return f"{REC}:{module}:{cls}"


def obj(module: str, cls: str) -> str:
    return f"{OBJ}:{module}:{cls}"


def is_obj(kind) -> bool:
    return isinstance(kind, str) and kind.startswith(OBJ)


def rec_class(kind: str) -> Tuple[str, str]:
    _, module, cls = kind.split(":")
    return module, cls


def bad(kind) -> bool:
    """その値への操作が live な object の code を呼び得るか。"""

    return kind == LIVE or kind == VER or is_rec(kind)


def tainted(kind) -> bool:
    return bad(kind) or kind in (CONT, ITER)


def join(*kinds):
    present = {k for k in kinds if k is not None}
    if len(present) == 1:
        return present.pop()
    for kind in kinds:
        if kind == LIVE:
            return LIVE
    for kind in kinds:
        if is_rec(kind):
            return LIVE if len({k for k in kinds if k is not None}) > 1 else kind
    for kind in (ITER, CONT):
        if kind in kinds:
            return kind
    objects = {k for k in kinds if is_obj(k)}
    if len(objects) == 1 and all(k is None or is_obj(k) for k in kinds):
        return objects.pop()
    return None


class PackageIndex:
    """package（tests を除く）の module / 関数 / class / import の表。"""

    def __init__(self, package_root: pathlib.Path):
        self.modules: Dict[str, ast.Module] = {}
        for path in sorted(package_root.rglob("*.py")):
            rel = path.relative_to(package_root)
            if rel.parts[0] == "tests":
                continue
            name = ".".join((PKG,) + rel.with_suffix("").parts)
            if name.endswith(".__init__"):
                name = name[: -len(".__init__")]
            self.modules[name] = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        self.functions: Dict[Tuple[str, str], ast.AST] = {}
        self.classes: Dict[Tuple[str, str], ast.ClassDef] = {}
        self.imports: Dict[str, Dict[str, Tuple[str, str]]] = collections.defaultdict(dict)
        self.module_alias: Dict[str, Dict[str, str]] = collections.defaultdict(dict)
        self.aliases: Dict[Tuple[str, str], ast.expr] = {}
        self.values: Set[Tuple[str, str]] = set()
        for module, tree in self.modules.items():
            for node in ast.walk(tree):
                if isinstance(node, ast.ImportFrom) and node.module:
                    for alias in node.names:
                        target = node.module + "." + alias.name
                        local = alias.asname or alias.name
                        if target in self.modules:
                            self.module_alias[module][local] = target
                        else:
                            self.imports[module][local] = (node.module, alias.name)
                elif isinstance(node, ast.Import):
                    for alias in node.names:
                        local = alias.asname or alias.name.split(".")[0]
                        self.module_alias[module][local] = alias.name
            for node in tree.body:
                if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                    # module の変数: 別の関数への別名（`_f = other.f`）か、値（policy などの object）
                    name = node.targets[0].id
                    if isinstance(node.value, (ast.Name, ast.Attribute)):
                        self.aliases[(module, name)] = node.value
                    else:
                        self.values.add((module, name))
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    self.functions[(module, node.name)] = node
                elif isinstance(node, ast.ClassDef):
                    self.classes[(module, node.name)] = node
                    for item in node.body:
                        if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            self.functions[(module, node.name + "." + item.name)] = item

    def resolve(self, module: str, name: str, depth: int = 0):
        """名前 → ("func" | "class" | "module" | "external", module, name)。"""

        if depth > 8:
            return None
        if (module, name) in self.functions:
            return ("func", module, name)
        if (module, name) in self.classes:
            return ("class", module, name)
        if name in self.module_alias[module]:
            return ("module", self.module_alias[module][name], None)
        if name in self.imports[module]:
            target_module, target_name = self.imports[module][name]
            if target_module in self.modules:
                return self.resolve(target_module, target_name, depth + 1)
            return ("external", target_module, target_name)
        alias = self.aliases.get((module, name))
        if alias is not None:
            if isinstance(alias, ast.Name):
                return self.resolve(module, alias.id, depth + 1)
            if isinstance(alias.value, ast.Name):
                owner = self.resolve(module, alias.value.id, depth + 1)
                if owner and owner[0] == "module" and owner[1] in self.modules:
                    return self.resolve(owner[1], alias.attr, depth + 1)
                if owner and owner[0] == "class":
                    method = self.method(owner[1], owner[2], alias.attr)
                    if method is not None:
                        return ("func",) + method
            return ("value", module, name)
        if (module, name) in self.values:
            return ("value", module, name)
        return None

    def method_kind(self, key) -> str:
        """"static" / "class" / "instance"（decorator から）。"""

        for decorator in self.functions[key].decorator_list:
            if isinstance(decorator, ast.Name) and decorator.id == "staticmethod":
                return "static"
            if isinstance(decorator, ast.Name) and decorator.id == "classmethod":
                return "class"
        return "instance"

    def bases(self, module: str, cls: str) -> List[Tuple[str, str]]:
        node = self.classes.get((module, cls))
        out = []
        if node is None:
            return out
        for base in node.bases:
            resolved = None
            if isinstance(base, ast.Name):
                resolved = self.resolve(module, base.id)
            elif isinstance(base, ast.Attribute) and isinstance(base.value, ast.Name):
                owner = self.resolve(module, base.value.id)
                if owner and owner[0] == "module":
                    resolved = self.resolve(owner[1], base.attr)
            if resolved and resolved[0] == "class":
                out.append((resolved[1], resolved[2]))
        return out

    def mro(self, module: str, cls: str) -> List[Tuple[str, str]]:
        seen, order, pending = set(), [], [(module, cls)]
        while pending:
            item = pending.pop(0)
            if item in seen:
                continue
            seen.add(item)
            order.append(item)
            pending.extend(self.bases(*item))
        return order

    def method(self, module: str, cls: str, name: str):
        for owner_module, owner in self.mro(module, cls):
            if (owner_module, owner + "." + name) in self.functions:
                return (owner_module, owner + "." + name)
        return None

    def is_property(self, key) -> bool:
        node = self.functions[key]
        for decorator in node.decorator_list:
            name = decorator.id if isinstance(decorator, ast.Name) else getattr(decorator, "attr", None)
            if name in ("property", "cached_property"):
                return True
        return False

    def subclass_of(self, module: str, cls: str, base: Tuple[str, str]) -> bool:
        return base in self.mro(module, cls)


class Violation(tuple):
    """(module, qualname, line, message)"""


class LiveFlowAudit:
    def __init__(self, index: PackageIndex):
        self.index = index
        self.violations: Set[Tuple[str, str, int, str]] = set()
        self.cache: Dict = {}
        self.stack: Set = set()
        self.analyzed: Set[Tuple[str, str]] = set()
        self.live_fields: Dict[Tuple[str, str], Set[str]] = collections.defaultdict(set)
        self.declared_callees_used: Set[Tuple[str, str]] = set()
        self.identity_key_callers: Set[Tuple[str, str]] = set()
        self.changed = False

    def report(self, key, node, message: str) -> None:
        self.violations.add((key[0][len(PKG) + 1:], key[1], getattr(node, "lineno", 0), message))

    def analyze(self, key, taint: Dict[str, str]):
        frozen = (key, tuple(sorted(taint.items())))
        if frozen in self.cache:
            return self.cache[frozen]
        if frozen in self.stack:
            return LIVE
        self.stack.add(frozen)
        self.analyzed.add(key)
        result = _FunctionAudit(self, key, dict(taint)).run()
        self.stack.discard(frozen)
        self.cache[frozen] = result
        return result

    def run(self, roots: Iterable[Tuple[Tuple[str, str], Dict[str, str]]]) -> None:
        roots = list(roots)
        for _ in range(6):
            self.changed = False
            self.cache.clear()
            self.violations.clear()
            for key, taint in roots:
                self.analyze(key, taint)
            if not self.changed:
                break


class _FunctionAudit:
    def __init__(self, audit: LiveFlowAudit, key, taint: Dict[str, str]):
        self.audit = audit
        self.index = audit.index
        self.key = key
        self.module, self.qual = key
        self.cls = self.qual.split(".")[0] if "." in self.qual else None
        self.node = self.index.functions[key]
        self.env: Dict[str, object] = {}
        self.type_of: Dict[str, str] = {}
        self.returns: Set = set()
        self.silent = False
        self.self_name: Optional[str] = None
        args = self.node.args
        positional = args.posonlyargs + args.args
        static = any(isinstance(d, ast.Name) and d.id == "staticmethod" for d in self.node.decorator_list)
        if self.cls and positional and not static:
            self.self_name = positional[0].arg
            self.env[self.self_name] = SELF
        for arg in (*positional, *args.kwonlyargs):
            if arg.arg in WORK_PARAMETER_NAMES:
                self.env[arg.arg] = WORK
        self.env.update(taint)
        self.initial = dict(self.env)
        self.local_callables: Dict[str, Tuple[str, str, str]] = {}
        if self.cls and positional and not static and any(
            isinstance(d, ast.Name) and d.id == "classmethod" for d in self.node.decorator_list
        ):
            # classmethod の cls: 呼べば自分の型の構築、属性は自分の型の method
            self.local_callables[positional[0].arg] = ("class", self.module, self.cls)
            self.cls_name = positional[0].arg
        else:
            self.cls_name = None
        self.parameters = {
            arg.arg for arg in (*positional, *args.kwonlyargs, *(a for a in (args.vararg, args.kwarg) if a))
        }
        self.is_generator = any(
            isinstance(n, (ast.Yield, ast.YieldFrom)) for n in _own_nodes(self.node)
        )

    # -- 報告 --------------------------------------------------------------
    def v(self, node, message: str) -> None:
        if not self.silent:
            self.audit.report(self.key, node, message)

    def run(self):
        # flow-insensitive: 後の代入が前の読みに効くよう 2 回（1 回目は報告しない）
        for round_ in range(2):
            self.silent = round_ == 0
            self.returns = set()
            self.block(self.node.body)
        if self.is_generator:
            return ITER if any(tainted(k) for k in self.returns) else None
        return join(*self.returns)

    # -- 文 ----------------------------------------------------------------
    def block(self, body) -> None:
        for index, stmt in enumerate(body):
            self.stmt(stmt)
            # `if type(x) is not C: return` の後は x を C として扱う
            if isinstance(stmt, ast.If) and not stmt.orelse and _exits(stmt.body):
                _, negative = self.narrowing(stmt.test)
                for name, kind in negative.items():
                    self.env[name] = kind

    def stmt(self, s) -> None:
        if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            self.v(s, "nested function / class in the bounded path")
        elif isinstance(s, ast.Expr):
            self.expr(s.value)
        elif isinstance(s, ast.Return):
            if s.value is not None:
                self.returns.add(self.expr(s.value))
        elif isinstance(s, ast.Assign):
            kind = self.expr(s.value)
            for target in s.targets:
                self.assign(target, kind, s.value)
        elif isinstance(s, ast.AnnAssign):
            if s.value is not None:
                self.assign(s.target, self.expr(s.value), s.value)
        elif isinstance(s, ast.AugAssign):
            value = self.expr(s.value)
            target = self.expr(s.target)
            if bad(value) or bad(target):
                self.v(s, "augmented assignment with a live value")
        elif isinstance(s, (ast.For, ast.AsyncFor)):
            element = self.iterate(s.iter, s)
            self.assign(s.target, element, None, element_of_iteration=True)
            self.block(s.body)
            self.block(s.orelse)
        elif isinstance(s, ast.While):
            self.test(s.test)
            self.block(s.body)
            self.block(s.orelse)
        elif isinstance(s, ast.If):
            self.test(s.test)
            positive, negative = self.narrowing(s.test)
            saved = dict(self.env)
            self.env.update(positive)
            self.block(s.body)
            after_body = self.env
            self.env = dict(saved)
            self.env.update(negative)
            self.block(s.orelse)
            merged = {}
            for name in set(after_body) | set(self.env):
                merged[name] = join(after_body.get(name), self.env.get(name)) if name in after_body and name in self.env else after_body.get(name, self.env.get(name))
            for name in positive:
                merged[name] = join(saved.get(name), merged.get(name)) if saved.get(name) is not None else merged.get(name)
            self.env = merged
        elif isinstance(s, (ast.With, ast.AsyncWith)):
            for item in s.items:
                if bad(self.expr(item.context_expr)):
                    self.v(s, "with statement on a live value")
                if item.optional_vars is not None:
                    self.assign(item.optional_vars, None, None)
            self.block(s.body)
        elif isinstance(s, ast.Try):
            self.block(s.body)
            for handler in s.handlers:
                if handler.type is not None:
                    self.expr(handler.type)
                self.block(handler.body)
            self.block(s.orelse)
            self.block(s.finalbody)
        elif isinstance(s, ast.Raise):
            if s.exc is not None:
                self.expr(s.exc)
            if s.cause is not None:
                self.expr(s.cause)
        elif isinstance(s, ast.Assert):
            self.test(s.test)
            if s.msg is not None:
                self.expr(s.msg)
        elif isinstance(s, ast.Delete):
            for target in s.targets:
                if not isinstance(target, ast.Name):
                    self.expr(target)
        elif isinstance(s, (ast.Pass, ast.Break, ast.Continue, ast.Global, ast.Nonlocal, ast.Import, ast.ImportFrom)):
            pass
        else:
            self.v(s, "unsupported statement " + type(s).__name__)

    def assign(self, target, kind, value, element_of_iteration: bool = False) -> None:
        if isinstance(target, ast.Name):
            self.env[target.id] = kind
            # 関数・型の別名（`constructor = make_unknown_reason`）: 呼び出しをその関数へ辿る
            alias = self._callable_alias(value)
            if alias is not None:
                self.local_callables[target.id] = alias
            else:
                self.local_callables.pop(target.id, None)
            if isinstance(value, ast.Call) and isinstance(value.func, ast.Name) and value.func.id == "type" and len(value.args) == 1 and isinstance(value.args[0], ast.Name):
                self.type_of[target.id] = value.args[0].id
            else:
                self.type_of.pop(target.id, None)
        elif isinstance(target, (ast.Tuple, ast.List)):
            if bad(kind) and not (element_of_iteration and self._pairs):
                self.v(target, "unpacking a live value")
            element = LIVE if tainted(kind) else None
            for item in target.elts:
                self.assign(item.value if isinstance(item, ast.Starred) else item, element, None)
        elif isinstance(target, ast.Attribute):
            receiver = self.expr(target.value)
            if bad(receiver) and not self._is_self(target.value):
                self.v(target, "setting an attribute of a live value")
            if self._is_self(target.value) and tainted(kind):
                self._mark_field(target.attr)
        elif isinstance(target, ast.Subscript):
            receiver = self.expr(target.value)
            index = self.expr(target.slice)
            if bad(receiver):
                self.v(target, "item assignment on a live value")
            if bad(index) and not self.identity_hashed(index):
                self.v(target, "live value used as a key")
            if tainted(kind) and isinstance(target.value, ast.Attribute) and self._is_self(target.value.value):
                self._mark_field(target.value.attr)
        elif isinstance(target, ast.Starred):
            self.assign(target.value, kind, value)

    _pairs = False

    def _callable_alias(self, value):
        """代入の右辺が package の関数・型の名前なら、その解決（呼び出しを辿る先）。"""

        if isinstance(value, ast.Name) and value.id not in self.env and value.id not in self.parameters:
            resolved = self.index.resolve(self.module, value.id)
            if resolved and resolved[0] in ("func", "class"):
                return resolved
        if (
            isinstance(value, ast.Attribute) and isinstance(value.value, ast.Name) and self.cls
            and value.value.id in (self.self_name, self.cls_name)
        ):
            method = self.index.method(self.module, self.cls, value.attr)
            if method is not None and self.index.method_kind(method) != "instance":
                return ("func",) + method
        if isinstance(value, ast.Attribute) and isinstance(value.value, ast.Name) and value.value.id not in self.env:
            owner = self.index.resolve(self.module, value.value.id)
            if owner and owner[0] == "module":
                resolved = self.index.resolve(owner[1], value.attr)
                if resolved and resolved[0] in ("func", "class"):
                    return resolved
        return None

    def _is_self(self, node) -> bool:
        return isinstance(node, ast.Name) and node.id == self.self_name

    def _mark_field(self, attr: str) -> None:
        if self.cls is None:
            return
        fields = self.audit.live_fields[(self.module, self.cls)]
        if attr not in fields:
            fields.add(attr)
            self.audit.changed = True

    def test(self, node) -> None:
        kind = self.expr(node)
        if kind == LIVE:
            self.v(node, "truth test of a live value")

    def iterate(self, node, where):
        kind = self.expr(node)
        self._pairs = False
        if kind == VER:
            return LIVE
        if bad(kind):
            self.v(where, "iterating a live value")
            return LIVE
        if kind in (ITER, CONT):
            self._pairs = True
            return LIVE
        return None

    # -- 型の絞り込み ------------------------------------------------------
    def narrowing(self, test):
        """`type(x) is C` / `type(x) in (A, B)` / `kind is C`（kind = type(x)）→ (真のとき, 偽のとき)。"""

        positive: Dict[str, object] = {}
        negative: Dict[str, object] = {}
        if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
            for value in test.values:
                p, _ = self.narrowing(value)
                positive.update(p)
            return positive, negative
        if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.Or):
            for value in test.values:
                _, n = self.narrowing(value)
                negative.update(n)
            return positive, negative
        if isinstance(test, ast.Call) and len(test.args) == 1 and isinstance(test.args[0], ast.Name):
            if self._live_values_function(test.func) in VERIFYING_PREDICATES:
                positive[test.args[0].id] = VER
            return positive, negative
        if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
            positive, negative = self.narrowing(test.operand)
            return negative, positive
        if (
            isinstance(test, ast.Compare) and len(test.ops) == 1 and isinstance(test.ops[0], (ast.Is, ast.IsNot))
            and isinstance(test.comparators[0], ast.Constant) and test.comparators[0].value is None
            and isinstance(test.left, ast.Call) and len(test.left.args) == 1 and isinstance(test.left.args[0], ast.Name)
            and self._live_values_function(test.left.func) == "builtin_mapping"
        ):
            (positive if isinstance(test.ops[0], ast.IsNot) else negative)[test.left.args[0].id] = VER
            return positive, negative
        if not (isinstance(test, ast.Compare) and len(test.ops) == 1):
            return positive, negative
        subject = self._type_subject(test.left)
        if subject is None:
            return positive, negative
        op = test.ops[0]
        right = test.comparators[0]
        kinds = []
        if isinstance(op, (ast.Is, ast.IsNot, ast.Eq, ast.NotEq)):
            kinds = [self._narrowed_kind(right)]
        elif isinstance(op, (ast.In, ast.NotIn)) and isinstance(right, (ast.Tuple, ast.Set, ast.List)):
            kinds = [self._narrowed_kind(item) for item in right.elts]
        if not kinds or any(k == "?" for k in kinds):
            return positive, negative
        kind = kinds[0] if len(set(kinds)) == 1 else (CONT if all(k in (None, CONT) for k in kinds) else "?")
        if kind == "?":
            return positive, negative
        if isinstance(op, (ast.Is, ast.Eq, ast.In)):
            positive[subject] = kind
        else:
            negative[subject] = kind
        return positive, negative

    def _live_values_function(self, func) -> Optional[str]:
        """呼び出し先が live_values の関数ならその名前。"""

        live_values = PKG + ".core.live_values"
        if isinstance(func, ast.Name):
            resolved = self.index.resolve(self.module, func.id)
            if resolved and resolved[0] == "func" and resolved[1] == live_values:
                return resolved[2]
        if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
            resolved = self.index.resolve(self.module, func.value.id)
            if resolved and resolved[0] == "module" and resolved[1] == live_values:
                return func.attr
        return None

    def _type_subject(self, node) -> Optional[str]:
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "type" and len(node.args) == 1 and isinstance(node.args[0], ast.Name):
            return node.args[0].id
        if isinstance(node, ast.Name) and node.id in self.type_of:
            return self.type_of[node.id]
        return None

    def _narrowed_kind(self, node):
        """`type(x) is <node>` のとき x の種類。分からなければ "?"。"""

        if isinstance(node, ast.Constant) and node.value is None:
            return "?"
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "type":
            return None if node.args and isinstance(node.args[0], ast.Constant) else "?"
        if isinstance(node, ast.Name):
            if node.id in _PLAIN_TYPES and self.index.resolve(self.module, node.id) is None:
                return None
            if node.id in _CONTAINER_TYPES and self.index.resolve(self.module, node.id) is None:
                return CONT
            resolved = self.index.resolve(self.module, node.id)
            if resolved and resolved[0] == "class":
                return rec(resolved[1], resolved[2])
            return "?"
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            owner = self.index.resolve(self.module, node.value.id)
            if owner and owner[0] == "module":
                resolved = self.index.resolve(owner[1], node.attr)
                if resolved and resolved[0] == "class":
                    return rec(resolved[1], resolved[2])
        return "?"

    # -- 式 ----------------------------------------------------------------
    def expr(self, node):
        handler = getattr(self, "e_" + type(node).__name__, None)
        if handler is None:
            for child in ast.iter_child_nodes(node):
                if isinstance(child, ast.expr):
                    self.expr(child)
            return None
        return handler(node)

    def e_Constant(self, node):
        return None

    def e_Name(self, node):
        return self.env.get(node.id)

    def _receiver_class(self, receiver, receiver_node):
        if is_rec(receiver) or is_obj(receiver):
            return rec_class(receiver)
        if receiver == SELF and self._is_self(receiver_node) and self.cls:
            return (self.module, self.cls)
        return None

    def e_Attribute(self, node):
        receiver = self.expr(node.value)
        if receiver == LIVE:
            self.v(node, f"attribute .{node.attr} of a live value")
            return LIVE
        if receiver in (ITER, CONT):
            self.v(node, f"attribute .{node.attr} of a container of live values")
            return None
        owner = self._receiver_class(receiver, node.value)
        if owner is not None:
            method = self.index.method(owner[0], owner[1], node.attr)
            if method is not None:
                if self.index.is_property(method):
                    params = self.index.functions[method].args.args
                    return self.audit.analyze(method, {params[0].arg: receiver})
                return None
            if is_rec(receiver):
                return LIVE
            if node.attr in self.audit.live_fields[owner]:
                return CONT
            return None
        return None

    def e_Subscript(self, node):
        receiver = self.expr(node.value)
        index = self.expr(node.slice)
        if bad(receiver):
            self.v(node, "subscript of a live value")
            return LIVE
        if bad(index) and not self.identity_hashed(index):
            self.v(node, "live value used as an index / key")
        if receiver in (CONT, ITER):
            return LIVE
        return None

    def identity_hashed(self, kind) -> bool:
        """型を確かめた package の object で、hash / 比較が object の identity のもの（その値の code を呼ばない）。"""

        if not is_rec(kind):
            return False
        for owner in self.index.mro(*rec_class(kind)):
            if self.index.method(owner[0], owner[1], "__hash__") or self.index.method(owner[0], owner[1], "__eq__"):
                return False
            node = self.index.classes.get(owner)
            if node is not None and any(_is_eq_dataclass(d) for d in node.decorator_list):
                return False
        return True

    def e_BinOp(self, node):
        left, right = self.expr(node.left), self.expr(node.right)
        if bad(left) or bad(right):
            self.v(node, "operator on a live value")
            return LIVE
        if isinstance(node.op, ast.Mod) and tainted(right):
            self.v(node, "%-formatting a live value")
        return None

    def e_UnaryOp(self, node):
        kind = self.expr(node.operand)
        if bad(kind):
            self.v(node, "unary operator on a live value")
            return LIVE
        return None

    def e_BoolOp(self, node):
        kinds = [self.expr(value) for value in node.values]
        for value, kind in zip(node.values[:-1], kinds[:-1]):
            if kind == LIVE:
                self.v(value, "truth test of a live value (and / or)")
        return join(*kinds)

    def e_Compare(self, node):
        kinds = [self.expr(node.left)] + [self.expr(c) for c in node.comparators]
        for op, left, right in zip(node.ops, kinds, kinds[1:]):
            if isinstance(op, (ast.Is, ast.IsNot)):
                continue
            if bad(left) or bad(right):
                self.v(node, f"comparison ({type(op).__name__}) with a live value")
            elif isinstance(op, (ast.In, ast.NotIn)) and right in (CONT, ITER):
                self.v(node, "membership test in a container of live values")
        return None

    def e_IfExp(self, node):
        self.test(node.test)
        positive, negative = self.narrowing(node.test)
        saved = dict(self.env)
        self.env.update(positive)
        body = self.expr(node.body)
        self.env = dict(saved)
        self.env.update(negative)
        orelse = self.expr(node.orelse)
        self.env = saved
        return join(body, orelse)

    def e_Tuple(self, node):
        kinds = [self.expr(e) for e in node.elts]
        for element, kind in zip(node.elts, kinds):
            if isinstance(element, ast.Starred) and bad(kind):
                self.v(element, "unpacking a live value")
        return CONT if any(tainted(k) for k in kinds) else None

    e_List = e_Tuple

    def e_Set(self, node):
        if any(bad(self.expr(e)) for e in node.elts):
            self.v(node, "live value hashed into a set")
        return None

    def e_Dict(self, node):
        for key in node.keys:
            if key is not None and bad(self.expr(key)):
                self.v(node, "live value hashed as a dict key")
        kinds = [self.expr(value) for value in node.values]
        for key, kind in zip(node.keys, kinds):
            if key is None and bad(kind):
                self.v(node, "unpacking a live mapping")
        return CONT if any(tainted(k) for k in kinds) else None

    def e_Starred(self, node):
        return self.expr(node.value)

    def e_JoinedStr(self, node):
        for value in node.values:
            if isinstance(value, ast.FormattedValue):
                if tainted(self.expr(value.value)):
                    self.v(node, "formatting a live value")
                if value.format_spec is not None:
                    self.expr(value.format_spec)
        return None

    def e_Lambda(self, node):
        self.v(node, "lambda in the bounded path")
        return None

    def e_NamedExpr(self, node):
        kind = self.expr(node.value)
        self.assign(node.target, kind, node.value)
        return kind

    def e_Yield(self, node):
        if node.value is not None:
            self.returns.add(self.expr(node.value))
        return None

    def e_YieldFrom(self, node):
        kind = self.expr(node.value)
        if bad(kind):
            self.v(node, "yield from a live value")
        self.returns.add(LIVE if tainted(kind) else None)
        return None

    def e_Await(self, node):
        return self.expr(node.value)

    def _comprehension(self, node, elements):
        saved = dict(self.env)
        for generator in node.generators:
            element = self.iterate(generator.iter, node)
            self.assign(generator.target, element, None, element_of_iteration=True)
            for condition in generator.ifs:
                self.test(condition)
        kinds = [self.expr(e) for e in elements]
        self.env = saved
        return kinds

    def e_ListComp(self, node):
        (kind,) = self._comprehension(node, [node.elt])
        return CONT if tainted(kind) else None

    def e_GeneratorExp(self, node):
        (kind,) = self._comprehension(node, [node.elt])
        return ITER if tainted(kind) else None

    def e_SetComp(self, node):
        (kind,) = self._comprehension(node, [node.elt])
        if bad(kind):
            self.v(node, "live value hashed into a set comprehension")
        return None

    def e_DictComp(self, node):
        key, value = self._comprehension(node, [node.key, node.value])
        if bad(key):
            self.v(node, "live value hashed as a dict comprehension key")
        return CONT if tainted(value) else None

    # -- 呼び出し ----------------------------------------------------------
    def e_Call(self, node):
        args = []
        for argument in node.args:
            kind = self.expr(argument.value if isinstance(argument, ast.Starred) else argument)
            if isinstance(argument, ast.Starred) and bad(kind):
                self.v(argument, "unpacking a live value into arguments")
            args.append(kind)
        kwargs = {}
        for keyword in node.keywords:
            kind = self.expr(keyword.value)
            if keyword.arg is None and bad(kind):
                self.v(node, "unpacking a live mapping into keywords")
            kwargs[keyword.arg] = kind
        live = [k for k in (*args, *kwargs.values()) if tainted(k)]
        func = node.func
        if isinstance(func, ast.Name):
            if func.id in self.local_callables:
                target = self.local_callables[func.id]
                if target[0] == "func" and self.index.method_kind((target[1], target[2])) == "class":
                    # classmethod の別名: cls を先頭に補う
                    return self.resolved_call(node, target, [None, *args], kwargs, live, bound=True)
                return self.resolved_call(node, target, args, kwargs, live)
            if func.id in self.env or func.id in self.parameters:
                if bad(self.env.get(func.id)):
                    self.v(node, "calling a live value")
                    return LIVE
                # 引数・変数に入った callable は何を実行するか分からない（任意の callable の経路）
                self.v(node, f"calling an unresolved callable {func.id}()")
                return None
            resolved = self.index.resolve(self.module, func.id)
            if resolved is None:
                return self.builtin_call(node, func.id, args, live)
            return self.resolved_call(node, resolved, args, kwargs, live)
        if isinstance(func, ast.Attribute):
            receiver_node = func.value
            if isinstance(receiver_node, ast.Name) and receiver_node.id not in self.env:
                resolved = self.index.resolve(self.module, receiver_node.id)
                if resolved and resolved[0] == "module":
                    target = self.index.resolve(resolved[1], func.attr)
                    if target is not None:
                        return self.resolved_call(node, target, args, kwargs, live)
                    return self.external_call(node, f"{resolved[1]}.{func.attr}", live)
                if resolved and resolved[0] == "class":
                    method = self.index.method(resolved[1], resolved[2], func.attr)
                    if method is not None:
                        # `C.m(...)`: classmethod は cls を先頭に補う（staticmethod・関数は引数のまま）
                        if self.index.method_kind(method) == "class":
                            return self.resolved_call(node, ("func",) + method, [None, *args], kwargs, live, bound=True)
                        return self.resolved_call(node, ("func",) + method, args, kwargs, live)
                    if resolved[1] in OWNER_MODULES:
                        return None
                    return self.external_call(node, f"{resolved[2]}.{func.attr}", live)
                if resolved and resolved[0] == "external":
                    return self.external_call(node, f"{resolved[1]}.{resolved[2]}.{func.attr}", live)
                if resolved and resolved[0] == "func" and resolved[1] in OWNER_MODULES:
                    return None
                if resolved is None and receiver_node.id in _BUILTIN_TYPE_NAMES:
                    constructing = (
                        receiver_node.id == "object" and func.attr == "__setattr__" and node.args
                        and self._is_self(node.args[0]) and self.qual.split(".")[-1] in ("__init__", "__post_init__")
                    )
                    if live and not constructing:
                        self.v(node, f"{receiver_node.id}.{func.attr}() on a live value outside the owner")
                    return None
            receiver = self.expr(receiver_node)
            owner = self._receiver_class(receiver, receiver_node)
            if owner is not None:
                method = self.index.method(owner[0], owner[1], func.attr)
                if method is not None:
                    return self.resolved_call(node, ("func",) + method, [receiver, *args], kwargs, live, bound=True)
                if is_rec(receiver):
                    self.v(node, f"unresolved method .{func.attr}() of a package object")
                    return LIVE
                if live:
                    self.v(node, f"live value passed to unresolved self.{func.attr}()")
                return None
            if receiver == LIVE:
                self.v(node, f"method .{func.attr}() of a live value")
                return LIVE
            if receiver == WORK or self._owner_object(receiver_node):
                return OWNER_RESULTS.get(func.attr) if func.attr == "materialize" else None
            if receiver in (CONT, ITER):
                return self.container_method(node, func.attr, args)
            if live:
                return self.plain_method(node, func.attr, args)
            return None
        if bad(self.expr(func)):
            self.v(node, "calling a live value")
        return None

    def _owner_object(self, receiver_node) -> bool:
        base = receiver_node
        while True:
            if isinstance(base, ast.Attribute):
                base = base.value
            elif isinstance(base, ast.Call):
                base = base.func
            else:
                break
        if isinstance(base, ast.Name) and base.id not in self.env:
            resolved = self.index.resolve(self.module, base.id)
            return bool(resolved and resolved[1] in OWNER_MODULES)
        return False

    def container_method(self, node, attr, args):
        if attr in _APPEND_METHODS:
            return None
        if attr in ("get", "pop", "setdefault"):
            if args and bad(args[0]) and not self.identity_hashed(args[0]):
                self.v(node, f"live value used as a key in .{attr}()")
            return LIVE
        if attr in ("items", "values", "keys"):
            return ITER
        if attr == "extend":
            if any(bad(k) for k in args):
                self.v(node, "extending with a live value")
            return None
        self.v(node, f"method .{attr}() of a container of live values")
        return None

    def plain_method(self, node, attr, args):
        if attr in _APPEND_METHODS:
            return None
        if attr in ("get", "pop", "setdefault") and args and all(
            not tainted(k) or self.identity_hashed(k) for k in args[:1]
        ) and not any(bad(k) and not self.identity_hashed(k) for k in args[1:]):
            # package の容器を identity で hash される key で引く（key の code を呼ばない）
            return None
        if attr == "extend" and not any(bad(k) for k in args):
            return None
        self.v(node, f"live value passed to unresolved method .{attr}()")
        return None

    def builtin_call(self, node, name, args, live):
        if name in _SAFE_BUILTINS:
            return None
        if name in ("iter", "len") and args and args[0] == VER and len(args) == 1:
            return ITER if name == "iter" else None
        if name == "next":
            if args and bad(args[0]):
                self.v(node, "next() of a live value")
            return LIVE if args and args[0] in (ITER, CONT) else None
        if name in ("enumerate", "zip", "reversed"):
            if any(bad(k) for k in args):
                self.v(node, f"{name}() of a live value")
            return ITER if live else None
        if name in ("tuple", "list"):
            if any(bad(k) for k in args):
                self.v(node, f"{name}() of a live value")
            return CONT if live else None
        if name in _EXCEPTION_NAMES:
            if live:
                self.v(node, f"live value stored in {name}")
            return None
        if live:
            self.v(node, f"builtin {name}() of a live value")
        return None

    def external_call(self, node, name, live):
        if live:
            self.v(node, f"live value passed to external {name}")
        return None

    def resolved_call(self, node, resolved, args, kwargs, live, bound: bool = False):
        kind, module, name = resolved
        if kind == "external":
            return self.external_call(node, f"{module}.{name}", live)
        if kind == "value":
            if module in OWNER_MODULES:
                return None
            return self.external_call(node, f"{module[len(PKG) + 1:]}.{name}", live)
        if module in OWNER_MODULES:
            if kind == "func" and name == "identity_key_of":
                # #194: owner の identity key の読み（package の `stable_key()` / `to_key()` を呼ぶ）。
                # 呼ぶ場所を記録する（test が集合を固定する）
                self.audit.identity_key_callers.add((self.module[len(PKG) + 1:], self.qual))
            if kind == "func" and module == PKG + ".core.live_values":
                return LIVE_VALUES_RESULTS.get(name)
            if kind == "func":
                return OWNER_RESULTS.get(name)
            return None
        if module.startswith(EXTERNAL_PREFIXES):
            # authority が自分の record（型を確かめた authority の型の object）を読むのは許す
            foreign = [k for k in live if not (is_rec(k) and rec_class(k)[0].startswith(EXTERNAL_PREFIXES))]
            if foreign:
                self.v(node, f"live value passed to {module[len(PKG) + 1:]}.{name}")
            return None
        if kind == "module":
            return None
        if kind == "class":
            if not live:
                return obj(module, name)
            # package の型の構築: 生成された `__init__` は値を入れるだけ。package が書いた
            # `__init__` / `__post_init__` は、live な引数 / field を受けるものとして監査する
            instance = rec(module, name)
            init = self.index.method(module, name, "__init__")
            if init is not None:
                self.resolved_call(node, ("func",) + init, [instance, *args], kwargs, live, bound=True)
            post = self.index.method(module, name, "__post_init__")
            if post is not None:
                params = self.index.functions[post].args.args
                self.audit.analyze(post, {params[0].arg: instance})
            return instance
        key = (module, name)
        declared = (module[len(PKG) + 1:], name)
        if declared in DECLARED_CALLEES:
            self.audit.declared_callees_used.add(declared)
            return LIVE
        function = self.index.functions[key]
        params = function.args.posonlyargs + function.args.args
        if bound and self.index.method_kind(key) == "static":
            # `self.m(...)` / `cls.m(...)` の staticmethod は receiver を受けない
            args = list(args[1:])
            bound = False
        taint: Dict[str, object] = {}
        for index, arg_kind in enumerate(args):
            if index < len(params):
                if arg_kind is not None and arg_kind != SELF:
                    taint[params[index].arg] = arg_kind
            elif tainted(arg_kind) and function.args.vararg is not None:
                taint[function.args.vararg.arg] = CONT
        names = {p.arg for p in (*params, *function.args.kwonlyargs)}
        for keyword, arg_kind in kwargs.items():
            if keyword in names and arg_kind is not None:
                taint[keyword] = arg_kind
            elif keyword not in names and tainted(arg_kind) and function.args.kwarg is not None:
                taint[function.args.kwarg.arg] = CONT
        if bound and params and args and (args[0] == SELF or args[0] is None or is_obj(args[0])):
            taint.pop(params[0].arg, None)
        taint = {k: v for k, v in taint.items() if tainted(v) or v == WORK}
        return self.audit.analyze(key, taint)


#: 出力 / 証拠 / digest / snapshot の入口（module, qualname, live な引数）。record の protocol・
#: converter・reducer は `protocol_roots` が型と decorator から見つける
ENTRY_ROOTS = (
    ("checker.output_preparation", "prepare_pair_output", ("checker", "result")),
    ("checker.output_preparation", "build_final_result_envelope", ("result",)),
    ("checker.output_preparation", "compose_result_preimage", ("result",)),
    ("checker.output_preparation", "finitize_legacy_reasons", ("result",)),
    ("checker.output_preparation", "check_prepared_field_bounds", ("result",)),
    ("checker.cause_aggregate", "attach_cause_aggregate", ("result",)),
    ("checker.cause_aggregate", "build_trace_cause_evidence", ("result",)),
    ("checker.diagnostics", "result_diagnostics_payload", ("result",)),
    ("checker.diagnostics", "trace_timings_payload", ("result",)),
    ("checker.diagnostics", "unknown_reason_ids", ("result",)),
    ("checker.output_schema", "superseded_decision_receipt_record", ("result",)),
    ("checker.output_schema", "superseded_digest_record", ("result",)),
    ("checker.unknown_reason", "build_projection_diagnostic",
     ("receipt", "cause_occurrence", "legacy_reasons", "function_names", "binary_names")),
    ("checker.unknown_reason", "legacy_reason_index", ("legacy_reasons",)),
    ("proof.obligations.snapshot", "SnapshotFingerprintCodec.freeze", ("value",)),
    ("proof.obligations.snapshot", "SnapshotFingerprintCodec.digest", ("value",)),
    ("core.canonical_digest", "canonical_fingerprint", ("value",)),
)


def _is_eq_dataclass(decorator) -> bool:
    """`@dataclass`（eq=False でない）: 生成された `__eq__` / `__hash__` は field を比べる。"""

    if isinstance(decorator, ast.Name):
        return decorator.id == "dataclass"
    if isinstance(decorator, ast.Call) and isinstance(decorator.func, ast.Name) and decorator.func.id == "dataclass":
        return not any(k.arg == "eq" and isinstance(k.value, ast.Constant) and k.value.value is False for k in decorator.keywords)
    return False


#: 宣言した作業量の外の依存（owner の Issue が引き継ぐ）: (module, qualname, 違反の文の先頭) → 理由。
#: 監査はこの場所の違反だけを除き、除いた場所が 1 つでも使われなくなれば（stale）落ちる。
DECLARED_DEPENDENCIES = {
    ("checker.output_preparation", "finalize_result_envelope", "live value passed to unresolved method .seal()"):
        "#110: AuthoritySeal.seal(preimage) が作業量を受け取らない（`seal(preimage, work=...)` で撤去）",
    ("checker.result_assembly", "analysis_limitation_result_for_pair",
     "live value passed to authority.decision.limitation_attribution.attribute_analysis_limitation"):
        "#110: 限界の帰属は authority の event（`observe_analysis_limitation`）を発行する（event の大きさと件数は"
        " AC-110-S2 の owner）",
}

#: 宣言した作業量の外の依存の **呼び先**（(module, qualname) → 理由）。監査はここへ入らない
#: （中の仕事は依存の owner の Issue の範囲）。呼ばれなくなれば stale として落ちる。
DECLARED_CALLEES = {
    ("core.expression", "Expression.structural_key"):
        "#194: 閉路のある未凍結の式の cycle_ref は structural_key を組み立てる（identity key の owner）",
    ("core.structural", "_validated"):
        "#194: 構造 identity の入口の検証（未検証の式だけ graph を 1 度凍らせる。identity の owner）",
}


def _own_nodes(function):
    """関数の本体の node（入れ子の関数 / lambda の中を除く）。"""

    pending = list(function.body)
    while pending:
        node = pending.pop()
        yield node
        for child in ast.iter_child_nodes(node):
            if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)):
                pending.append(child)


def _exits(body) -> bool:
    return bool(body) and isinstance(body[-1], (ast.Return, ast.Raise, ast.Continue, ast.Break))


def protocol_roots(index: PackageIndex):
    """walker が live な値を渡して呼ぶ package の callback（record の protocol・converter・reducer）。"""

    reducer = (PKG + ".core.json_encoding", "Reducer")
    for (module, qual), node in sorted(index.functions.items()):
        if module in OWNER_MODULES:
            continue
        last = qual.split(".")[-1]
        cls = qual.split(".")[0] if "." in qual else None
        params = node.args.posonlyargs + node.args.args
        if cls and last in RECORD_METHODS:
            yield (module, qual), {params[0].arg: rec(module, cls)}
        elif any(isinstance(d, ast.Name) and d.id == "source_converter" for d in node.decorator_list):
            yield (module, qual), {params[0].arg: LIVE}
        elif cls and index.subclass_of(module, cls, reducer) and last == "add":
            yield (module, qual), {params[1].arg: LIVE}
        elif cls and index.subclass_of(module, cls, reducer) and last == "result":
            yield (module, qual), {}


def audit(package_root: pathlib.Path, entry_roots: Iterable[Tuple[str, str, Tuple[str, ...]]] = ENTRY_ROOTS):
    """(violations, analyzed, index)。`entry_roots` は (module, qualname, live な引数の名前)。"""

    index = PackageIndex(package_root)
    roots = list(protocol_roots(index))
    missing = []
    for module, qual, params in entry_roots:
        key = (PKG + "." + module, qual)
        if key not in index.functions:
            missing.append(key)
            continue
        function = index.functions[key]
        first = (function.args.posonlyargs + function.args.args)[:1]
        taint = {}
        for name in params:
            if "." in qual and first and first[0].arg == name:
                # method の self: 型を確かめて呼ぶ package の record（field は live）
                taint[name] = rec(key[0], qual.split(".")[0])
            else:
                taint[name] = LIVE
        roots.append((key, taint))
    flow = LiveFlowAudit(index)
    flow.run(roots)
    audit.last = flow
    return sorted(flow.violations), flow.analyzed, index, missing


def undeclared(violations):
    """宣言した依存の場所を除いた違反と、使われた宣言の集合。"""

    used = set()
    rest = []
    for module, qual, line, message in violations:
        match = next(
            (declared for declared in DECLARED_DEPENDENCIES
             if declared[0] == module and declared[1] == qual and message.startswith(declared[2])),
            None,
        )
        if match is None:
            rest.append((module, qual, line, message))
        else:
            used.add(match)
    return rest, used


def main(argv=None) -> int:
    """`python3 -B -m scripts.function_tracer_pcode.tests.unit._live_flow_audit [module の部分文字列]`"""

    import sys

    argv = sys.argv[1:] if argv is None else argv
    package_root = pathlib.Path(__file__).resolve().parents[2]
    violations, analyzed, _index, missing = audit(package_root)
    violations, used = undeclared(violations)
    stale = (set(DECLARED_DEPENDENCIES) - used) | (set(DECLARED_CALLEES) - audit.last.declared_callees_used)
    if stale:
        print(f"stale declared dependencies: {sorted(stale)}")
    only = argv[0] if argv else None
    counts = collections.Counter()
    for module, qual, line, message in violations:
        counts[module] += 1
        if only is None or only in module:
            print(f"{module}::{qual}:{line} {message}")
    print(f"missing roots: {missing}")
    print(f"analyzed {len(analyzed)} functions, {len(violations)} violations")
    for module, count in counts.most_common():
        print(f"{count:6d} {module}")
    return 1 if violations or missing else 0


if __name__ == "__main__":
    raise SystemExit(main())


# ---------------------------------------------------------------------------
# J22: 入力に比例する仕事の owner（ループ・内包・列を完了させる組み込み）
# ---------------------------------------------------------------------------

#: 列を先に完了させる組み込み（引数の列を全部引き出す）
COMPLETING_BUILTINS = frozenset({
    "tuple", "list", "dict", "set", "frozenset", "sorted", "sum", "min", "max", "any", "all",
})
COMPLETING_METHODS = frozenset({"join", "sort", "extend", "update"})


def proportional_constructs(function) -> List[str]:
    """関数の本体の、入力に比例し得る構文（`For@行` など）。入れ子の関数の中は除く。"""

    found = []
    for node in _own_nodes(function):
        if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            found.append(f"{type(node).__name__}@{node.lineno}")
        elif isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            found.append(f"{type(node).__name__}@{node.lineno}")
        elif isinstance(node, ast.Call):
            func = node.func
            if isinstance(func, ast.Name) and func.id in COMPLETING_BUILTINS and node.args:
                found.append(f"{func.id}()@{node.lineno}")
            elif isinstance(func, ast.Attribute) and func.attr in COMPLETING_METHODS and node.args:
                found.append(f".{func.attr}()@{node.lineno}")
    return sorted(set(found))


def work_owner(index: PackageIndex, key) -> Optional[str]:
    """関数が自分で作業量の owner を持つか: "B"（作業量 / 予算を引数に取る）、"C"（反復ごとに yield
    する generator）、どちらでもなければ `None`。"""

    function = index.functions[key]
    args = function.args
    if any(arg.arg in WORK_PARAMETER_NAMES for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs)):
        return "B"
    loops = [n for n in _own_nodes(function) if isinstance(n, (ast.For, ast.AsyncFor, ast.While))]
    if loops and all(any(isinstance(inner, (ast.Yield, ast.YieldFrom)) for inner in ast.walk(loop)) for loop in loops):
        if all(not isinstance(n, (ast.ListComp, ast.SetComp, ast.DictComp)) for n in _own_nodes(function)):
            return "C"
    return None


def unowned_proportional_work(package_root: pathlib.Path, analyzed: Iterable[Tuple[str, str]], index: PackageIndex):
    """bounded path の関数のうち、入力に比例し得る構文を持ち、作業量の owner を持たないもの。"""

    out = {}
    for key in sorted(set(analyzed)):
        constructs = proportional_constructs(index.functions[key])
        if constructs and work_owner(index, key) is None:
            out[(key[0][len(PKG) + 1:], key[1])] = constructs
    return out
