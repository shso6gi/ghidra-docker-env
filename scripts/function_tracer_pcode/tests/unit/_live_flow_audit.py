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
追う（呼び出し先を同じ規則で監査する）。owner の module（`OWNER_MODULES`）の中はこの監査では辿らない。
owner の規則は次が守る: owner 自身への J22（`test_issue22d_live_values_bounds.py` の `OWNER_WORK`:
入力に比例する関数の分類と、上限の比較が辿るより前にあること）、owner の API が読む値の code を
呼ばないことの adversarial test（`test_issue22d_capabilities.py` の
`test_the_owner_api_never_runs_the_code_of_the_values_it_reads` ほか、`test_issue22d_live_values*.py`・
`test_issue22d_read_bound_contract.py`）、owner が `inspect.getattr_static` を使わないことの静的 test。
"""

from __future__ import annotations

import ast
import collections
import pathlib
from typing import Dict, Iterable, List, Optional, Set, Tuple

PKG = "scripts.function_tracer_pcode"
#: 作業量か authority の event の契約が仕事を抑える authority の入口（その owner の表）
from scripts.function_tracer_pcode.authority.event_contract import BOUNDED_ENTRY_POINTS  # noqa: E402
OWNER_MODULES = frozenset({PKG + ".core.json_encoding", PKG + ".core.live_values", PKG + ".core.read_limits"})
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
TYPE = "TYPE"  # live な値の型（`type(x)`）: `is` / `issubclass` / owner の関数にだけ渡してよい

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
    "copied_container": CONT,
    "items_of": ITER,
    "values_of": ITER,
    "elements_of": ITER,
    "builtin_mapping": VER,
}
#: `core/read_limits`（作業量を受け取らない読みの固定の上限）の関数の戻り値の種類（書いていない関数は plain）
READ_LIMITS_RESULTS = {
    "elements_within_limit": ITER,
    "items_within_limit": ITER,
    "prefix_within_limit": CONT,
    "copied_within_limit": CONT,
}
#: 真のとき引数を VER にする live_values の述語
VERIFYING_PREDICATES = frozenset({"builtin_sequence", "builtin_set", "builtin_iterator", "builtin_container"})
#: owner の関数 / method の戻り値の種類（書いていないものは plain な値を返す）。`materialize` の
#: LEGACY の写しは `raw` の葉を live なまま持つ
OWNER_RESULTS = {"_walk_iter": ITER, "materialize": CONT}
#: owner の上限の無い API（大きさの分かった小さい値にだけ使う: live な値を渡さない）
UNBOUNDED_OWNER_METHODS = frozenset({"dumps", "encode_bounded", "scalar_record_dict"})

_PLAIN_TYPES = frozenset({"str", "int", "float", "bool", "bytes", "NoneType"})
_CONTAINER_TYPES = frozenset({"tuple", "list", "dict", "set", "frozenset"})
_BUILTIN_TYPE_NAMES = _PLAIN_TYPES | _CONTAINER_TYPES | {"object", "type", "BaseException", "Enum", "OrderedDict"}
_SAFE_BUILTINS = frozenset({"type", "id", "issubclass", "super", "range"})
_EXCEPTION_NAMES = frozenset({
    "ValueError", "TypeError", "KeyError", "RuntimeError", "AttributeError", "AssertionError",
    "IndexError", "OverflowError", "NotImplementedError",
})
_APPEND_METHODS = frozenset({"append", "insert", "appendleft"})
#: 容器へ値を足す method（足した値が live なら容器の要素も live）
_FILLING_METHODS = frozenset({"append", "insert", "appendleft", "extend", "add", "update", "setdefault"})


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
                if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.value is not None:
                    # 型注釈つきの module の変数（`_CACHE: dict = {}`）も値
                    self.values.add((module, node.target.id))
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
            if name in ("property", "cached_property", "readable_property"):
                return True
        return False

    def is_state_setter(self, key) -> bool:
        """`live_values.state_setter` で宣言した `__setattr__` か（`set_state()` が呼ぶ関数）。"""

        return any(
            (decorator.id if isinstance(decorator, ast.Name) else getattr(decorator, "attr", None))
            == "state_setter"
            for decorator in self.functions[key].decorator_list
        )

    def is_readable_property(self, key) -> bool:
        """`live_values.readable_property` で宣言した property か（`attribute()` が呼ぶ getter）。"""

        return any(
            (decorator.id if isinstance(decorator, ast.Name) else getattr(decorator, "attr", None))
            == "readable_property"
            for decorator in self.functions[key].decorator_list
        )

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
        self.field_kinds: Dict[Tuple[str, str], Dict[str, Set[str]]] = collections.defaultdict(dict)
        self.identity_key_callers: Set[Tuple[str, str]] = set()
        #: bounded path の呼び出しの辺（呼ばれる関数 → 呼ぶ関数の集合。監査が解決した呼び出しだけ）
        self.callers: Dict[Tuple[str, str], Set[Tuple[str, str]]] = collections.defaultdict(set)
        self._running: List[Tuple[str, str]] = []
        self.changed = False

    def report(self, key, node, message: str) -> None:
        self.violations.add((key[0][len(PKG) + 1:], key[1], getattr(node, "lineno", 0), message))

    def analyze(self, key, taint: Dict[str, str]):
        if self._running:
            self.callers[key].add(self._running[-1])
        frozen = (key, tuple(sorted(taint.items())))
        if frozen in self.cache:
            return self.cache[frozen]
        if frozen in self.stack:
            return LIVE
        self.stack.add(frozen)
        self.analyzed.add(key)
        self._running.append(key)
        try:
            result = _FunctionAudit(self, key, dict(taint)).run()
        finally:
            self._running.pop()
        self.stack.discard(frozen)
        self.cache[frozen] = result
        return result

    def run(self, roots: Iterable[Tuple[Tuple[str, str], Dict[str, str]]]) -> None:
        roots = list(roots)
        for _ in range(30):  # field の種類が増えなくなるまで（収束しなければ最後の結果）
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
            self.local_callables[positional[0].arg] = {("class", self.module, self.cls)}
            self.cls_name = positional[0].arg
        else:
            self.cls_name = None
        self.parameters = {
            arg.arg for arg in (*positional, *args.kwonlyargs, *(a for a in (args.vararg, args.kwarg) if a))
        }
        #: `global` / `nonlocal` で宣言した名前（代入は関数の外の状態）
        self.globals: Set[str] = set()
        #: 関数の中で束縛する名前（それ以外の名前は module の値）
        self.local_names: Set[str] = set(self.parameters) | {
            node.id for node in _own_nodes(self.node)
            if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del))
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
                for name, kind in self._narrow(negative).items():
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
            positive, negative = self._narrow(positive), self._narrow(negative)
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
                if handler.name is not None:
                    # 捕まえた例外は live な値を引数に持ち得る（package の例外の型だけのときは package の値）
                    self.env[handler.name] = None if self._package_exceptions(handler.type) else LIVE
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
        elif isinstance(s, (ast.Global, ast.Nonlocal)):
            self.globals.update(s.names)
        elif isinstance(s, (ast.Pass, ast.Break, ast.Continue, ast.Import, ast.ImportFrom)):
            pass
        else:
            self.v(s, "unsupported statement " + type(s).__name__)

    @staticmethod
    def _unbounded_owner_call(name: str, node) -> bool:
        """owner の上限の無い API か（書く量を数えない）。上限を引数に取る API（`prepare` / `measure` /
        `materialize` / `plain_bytes`）の上限なしの呼び出しは J10（`test_architecture_boundaries`）が
        場所を登録して固定する。"""

        return name in UNBOUNDED_OWNER_METHODS

    def _module_value(self, name: str) -> bool:
        """`name` が関数の中で束縛しない、package の module の値か（owner の module の値を除く）。"""

        if name in self.local_names:
            return False
        resolved = self.index.resolve(self.module, name)
        return bool(resolved) and resolved[0] == "value" and resolved[1] not in OWNER_MODULES

    def _package_exceptions(self, node) -> bool:
        """except の型が全部 package の class か（その例外の引数は package が作った値）。"""

        if node is None:
            return False
        parts = node.elts if isinstance(node, ast.Tuple) else [node]
        for part in parts:
            if not isinstance(part, ast.Name):
                return False
            resolved = self.index.resolve(self.module, part.id)
            if not resolved or resolved[0] != "class":
                return False
        return True

    def assign(self, target, kind, value, element_of_iteration: bool = False) -> None:
        if isinstance(target, ast.Name):
            if target.id in self.globals and tainted(kind):
                self.v(target, "live value stored in module state")
            self.env[target.id] = kind
            # 関数・型の別名（`constructor = make_unknown_reason`）: 呼び出しをその関数へ辿る
            alias = self._callable_alias(value)
            # flow-insensitive: 同じ名前へ入る関数の全部を辿る（枝ごとに違う関数を入れる形）。関数で
            # ない値も入るなら、その名前の呼び出しは解決できない callable
            self.local_callables.setdefault(target.id, set()).add(alias)
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
            elif tainted(kind) and not self._is_self(target.value):
                # 他の object の属性へ live な値を置くと、そこから読んだ値の種類を追えない（洗浄）
                self.v(target, "live value stored in an attribute of another object")
            if self._is_self(target.value) and tainted(kind):
                self._mark_field(target.attr)
            if self._is_self(target.value) and (is_obj(kind) or kind == WORK) and self.cls:
                # package が作った object / 作業量を自分の field に置いた: その field の読みはその種類
                kinds = self.audit.field_kinds[(self.module, self.cls)].setdefault(target.attr, set())
                if kind not in kinds:
                    kinds.add(kind)
                    self.audit.changed = True
        elif isinstance(target, ast.Subscript):
            receiver = self.expr(target.value)
            index = self.expr(target.slice)
            if bad(receiver):
                self.v(target, "item assignment on a live value")
            if self.hashes_live(index):
                self.v(target, "live value used as a key")
            if tainted(kind) and isinstance(target.value, ast.Attribute) and self._is_self(target.value.value):
                self._mark_field(target.value.attr)
            if tainted(kind) and isinstance(target.value, ast.Name) and self._module_value(target.value.id):
                self.v(target, "live value stored in module state")
            if tainted(kind) and isinstance(target.value, ast.Name) and self.env.get(target.value.id) in (None, CONT):
                # 変数の容器へ live な値を入れた: その容器の要素は live
                self.env[target.value.id] = CONT
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
            branches = []
            for value in test.values:
                p, n = self.narrowing(value)
                negative.update(n)
                branches.append(p)
            # `type(x) is A or type(x) is B`: 全部の枝が同じ名前を絞るなら、その合流
            subjects = {name for branch in branches for name in branch}
            if len(subjects) == 1 and all(len(branch) == 1 for branch in branches):
                (subject,) = subjects
                kinds = {branch[subject] for branch in branches}
                if kinds <= {None, CONT}:
                    positive[subject] = CONT if CONT in kinds else None
                elif len(kinds) == 1:
                    positive[subject] = kinds.pop()
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
        # 型の絞り込みは identity（`is`）だけ: `==` / `in` は metaclass の `__eq__` を呼び得る
        if isinstance(op, (ast.Is, ast.IsNot)):
            kinds = [self._narrowed_kind(right)]
        if not kinds or any(k == "?" for k in kinds):
            return positive, negative
        kind = kinds[0] if len(set(kinds)) == 1 else (CONT if all(k in (None, CONT) for k in kinds) else "?")
        if kind == "?":
            return positive, negative
        if isinstance(op, ast.Is):
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

    def _narrow(self, updates: Dict[str, object]) -> Dict[str, object]:
        """絞り込みを今の種類に合わせる: plain な値を package の型へ絞っても live にはしない（OBJ）。"""

        out = {}
        for name, kind in updates.items():
            current = self.env.get(name)
            if is_rec(kind) and not tainted(current):
                kind = OBJ + kind[len(REC):]
            elif kind == VER and not tainted(current):
                kind = None
            out[name] = kind
        return out

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
        if node.id not in self.env and node.id not in self.parameters:
            resolved = self.index.resolve(self.module, node.id)
            if resolved and resolved[0] == "value" and resolved[1] in OWNER_MODULES:
                # owner の module の値（`RESULT_JSON_POLICY` など）: owner の object
                return WORK
        return self.env.get(node.id)

    def _receiver_class(self, receiver, receiver_node):
        if is_rec(receiver) or is_obj(receiver):
            return rec_class(receiver)
        if receiver == SELF and self._is_self(receiver_node) and self.cls:
            return (self.module, self.cls)
        return None

    def e_Attribute(self, node):
        receiver = self.expr(node.value)
        if receiver == TYPE:
            # 型の属性は metaclass の `__getattribute__` / property を通る（`type_name` / `type_module`）
            self.v(node, f"attribute .{node.attr} of the type of a live value")
            return None
        if receiver == LIVE or receiver == VER:
            # 確かめた容器（VER）も属性は live（組み込みの振る舞いは反復・長さ・真偽だけ。subclass の
            # property は外の code）
            self.v(node, f"attribute .{node.attr} of a live value")
            return LIVE
        if receiver in (ITER, CONT):
            # package が作った組み込みの容器の属性（組み込みの method。中の live な値には触れない）
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
            kinds = self.audit.field_kinds[owner].get(node.attr)
            if kinds and len(kinds) == 1:
                return next(iter(kinds))
            return None
        return None

    def e_Subscript(self, node):
        receiver = self.expr(node.value)
        index = self.expr(node.slice)
        if bad(receiver):
            self.v(node, "subscript of a live value")
            return LIVE
        if self.hashes_live(index):
            self.v(node, "live value used as an index / key")
        if receiver in (CONT, ITER):
            return LIVE
        return None

    def hashes_live(self, kind) -> bool:
        """hash・比較するとその値の code を呼び得るか（live な値・live な値を持つ容器。identity で
        hash される package の object は呼ばない）。"""

        if kind in (CONT, ITER, TYPE):
            return True
        return bad(kind) and not self.identity_hashed(kind)

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
        if left in (CONT, ITER) or right in (CONT, ITER):
            # 容器の連結・繰り返しの結果も live な値を持つ容器
            return CONT
        if left == TYPE or right == TYPE:
            self.v(node, "operator on the type of a live value")
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
        operands = [node.left, *node.comparators]
        for index, op in enumerate(node.ops):
            if isinstance(op, (ast.Is, ast.IsNot)):
                continue
            for operand in operands[index:index + 2]:
                subject = self._type_subject(operand)
                of_live = subject is not None and bad(self.env.get(subject))
                if (
                    isinstance(operand, ast.Call) and isinstance(operand.func, ast.Name) and operand.func.id == "type"
                    and len(operand.args) == 1 and bad(self.expr(operand.args[0]))
                ):
                    of_live = True
                if of_live:
                    # live な値の型を `==` / `in` で比べると、metaclass の `__eq__` を呼び得る（`is` で比べる）
                    self.v(node, f"type of a live value compared with {type(op).__name__}")
        for op, left, right in zip(node.ops, kinds, kinds[1:]):
            if isinstance(op, (ast.Is, ast.IsNot)):
                continue
            if bad(left) or bad(right):
                self.v(node, f"comparison ({type(op).__name__}) with a live value")
            elif isinstance(op, (ast.In, ast.NotIn)) and right in (CONT, ITER):
                self.v(node, "membership test in a container of live values")
            elif isinstance(op, (ast.In, ast.NotIn)) and left in (CONT, ITER):
                self.v(node, "a container of live values hashed by a membership test")
        return None

    def e_IfExp(self, node):
        self.test(node.test)
        positive, negative = self.narrowing(node.test)
        positive, negative = self._narrow(positive), self._narrow(negative)
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
        if any(self.hashes_live(self.expr(e)) for e in node.elts):
            self.v(node, "live value hashed into a set")
        return None

    def e_Dict(self, node):
        for key in node.keys:
            if key is not None and self.hashes_live(self.expr(key)):
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
        if self.hashes_live(kind):
            self.v(node, "live value hashed into a set comprehension")
        return None

    def e_DictComp(self, node):
        key, value = self._comprehension(node, [node.key, node.value])
        if self.hashes_live(key):
            self.v(node, "live value hashed as a dict comprehension key")
        return CONT if tainted(value) else None

    # -- 呼び出し ----------------------------------------------------------
    def e_Call(self, node):
        args = []
        starred_live = False
        for argument in node.args:
            kind = self.expr(argument.value if isinstance(argument, ast.Starred) else argument)
            if isinstance(argument, ast.Starred) and bad(kind):
                self.v(argument, "unpacking a live value into arguments")
            if isinstance(argument, ast.Starred) and tainted(kind):
                # `f(*rows)`: 容器の要素（live）が残りの引数へ入る
                starred_live = True
                kind = LIVE
            args.append(kind)
        if starred_live:
            args.extend([LIVE] * 8)
        kwargs = {}
        for keyword in node.keywords:
            kind = self.expr(keyword.value)
            if keyword.arg is None and bad(kind):
                self.v(node, "unpacking a live mapping into keywords")
            kwargs[keyword.arg] = kind
        live = [k for k in (*args, *kwargs.values()) if tainted(k)]
        self._callable_arguments(node)
        func = node.func
        if (
            isinstance(func, ast.Attribute) and func.attr in _FILLING_METHODS and isinstance(func.value, ast.Name)
            and any(tainted(k) for k in args) and self._module_value(func.value.id)
        ):
            self.v(node, "live value stored in module state")
        elif (
            isinstance(func, ast.Attribute) and func.attr in _FILLING_METHODS and isinstance(func.value, ast.Name)
            and any(tainted(k) for k in args) and self.env.get(func.value.id) in (None, CONT)
            and func.value.id != self.self_name
        ):
            # 変数の容器へ live な値を足した（`rows.append(record)`）: その容器の要素は live
            self.env[func.value.id] = CONT
        if (
            isinstance(func, ast.Attribute) and func.attr in _FILLING_METHODS
            and isinstance(func.value, ast.Attribute) and self._is_self(func.value.value)
            and any(tainted(k) for k in args)
        ):
            # 自分の field の容器へ live な値を足した（`self.items.append(value)`）: その field の要素は live
            self._mark_field(func.value.attr)
        if isinstance(func, ast.Name):
            if func.id in self.local_callables and None not in self.local_callables[func.id]:
                results = []
                for target in sorted(self.local_callables[func.id]):
                    if target[0] == "func" and self.index.method_kind((target[1], target[2])) == "class":
                        # classmethod の別名: cls を先頭に補う
                        results.append(self.resolved_call(node, target, [None, *args], kwargs, live, bound=True))
                    else:
                        results.append(self.resolved_call(node, target, args, kwargs, live))
                return join(*results)
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
                        and self._is_self(node.args[0])
                        and self.qual.split(".")[-1] in ("__init__", "__post_init__", "__setattr__")
                    )
                    if live and not constructing:
                        self.v(node, f"{receiver_node.id}.{func.attr}() on a live value outside the owner")
                    return None
            if (
                isinstance(receiver_node, ast.Call) and isinstance(receiver_node.func, ast.Name)
                and receiver_node.func.id == "super" and self.cls and self.self_name
            ):
                # `super().m(...)`: 自分の型の MRO の次の型の method を辿る
                for base_module, base in self.index.mro(self.module, self.cls)[1:]:
                    if (base_module, base + "." + func.attr) in self.index.functions:
                        method = (base_module, base + "." + func.attr)
                        return self.resolved_call(
                            node, ("func",) + method, [self.env.get(self.self_name), *args], kwargs, live, bound=True,
                        )
                if live:
                    self.v(node, f"live value passed to unresolved super().{func.attr}()")
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
            if receiver == LIVE or receiver == VER or receiver == TYPE:
                self.v(node, f"method .{func.attr}() of a live value")
                return LIVE
            if receiver == WORK or self._owner_object(receiver_node):
                if live and self._unbounded_owner_call(func.attr, node):
                    self.v(node, f"live value passed to the unbounded owner API .{func.attr}()")
                return OWNER_RESULTS.get(func.attr) if func.attr == "materialize" else None
            if receiver in (CONT, ITER):
                return self.container_method(node, func.attr, args)
            if live:
                return self.plain_method(node, func.attr, args)
            return None
        if (
            isinstance(func, ast.Call) and isinstance(func.func, ast.Name)
            and self.index.resolve(self.module, func.func.id) == ("func", PKG + ".core.json_encoding", "protocol_method")
        ):
            # owner が型の MRO から引いた package の protocol の関数（record の protocol は root として監査済み）
            self.expr(func)
            return None
        if bad(self.expr(func)):
            self.v(node, "calling a live value")
        else:
            # 添字・呼び出しの結果など、名前で解決できない callable（関数の表・callback の値）
            self.v(node, "calling an unresolved callable expression")
        return None

    def _callable_arguments(self, node) -> None:
        """引数として渡した package の関数（`key=` / `functools.partial` / `default=`）も監査する。

        `sorted` / `min` / `max` / `.sort` の `key=` は並べる列の要素を受ける（要素の種類で辿る）。
        それ以外は呼ばれ方が分からないので、作業量でない引数は全部 live を受けるものとして辿る。
        """

        key_element = None
        func = node.func
        if isinstance(func, ast.Name) and func.id in ("sorted", "min", "max") and node.args:
            key_element = LIVE if tainted(self.expr(node.args[0])) else "plain"
        elif isinstance(func, ast.Attribute) and func.attr == "sort":
            key_element = LIVE if tainted(self.expr(func.value)) else "plain"
        for keyword in node.keywords:
            if keyword.arg == "key" and key_element is not None:
                self._analyze_callable(keyword.value, None if key_element == "plain" else LIVE)
            if (
                keyword.arg == "key" and isinstance(keyword.value, ast.Attribute)
                and tainted(self.expr(keyword.value.value))
            ):
                # 容器の bound method を key に: 並べるのは容器の中の live な値（比較が live な code）
                self.v(node, "a container of live values used as a sort key")
        for argument in (*node.args, *(keyword.value for keyword in node.keywords if keyword.arg != "key" or key_element is None)):
            self._analyze_callable(argument, LIVE)

    def _analyze_callable(self, argument, kind) -> None:
        """引数の式が package の関数なら、その関数を `kind` の引数で監査する。"""

        if True:
            target = None
            if isinstance(argument, ast.Name) and argument.id not in self.env and argument.id not in self.parameters:
                target = self.index.resolve(self.module, argument.id)
            elif isinstance(argument, ast.Attribute) and isinstance(argument.value, ast.Name):
                owner = self.index.resolve(self.module, argument.value.id) if argument.value.id not in self.env else None
                if owner and owner[0] == "module":
                    target = self.index.resolve(owner[1], argument.attr)
                elif owner and owner[0] == "class":
                    method = self.index.method(owner[1], owner[2], argument.attr)
                    target = ("func",) + method if method else None
            if not target or target[0] != "func" or target[1] in OWNER_MODULES or target[1].startswith(EXTERNAL_PREFIXES):
                return
            function = self.index.functions[(target[1], target[2])]
            params = function.args.posonlyargs + function.args.args + function.args.kwonlyargs
            self.audit.analyze(
                (target[1], target[2]),
                {} if kind is None else {
                    param.arg: kind for param in params
                    if param.arg not in WORK_PARAMETER_NAMES and param.arg not in ("self", "cls")
                },
            )

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
            if args and self.hashes_live(args[0]):
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
        if name == "range" and any(bad(k) for k in args):
            self.v(node, "range() of a live value")
            return None
        if name == "type" and args and tainted(args[0]):
            return TYPE
        if name in _SAFE_BUILTINS:
            return None
        if name in ("iter", "len") and args and args[0] in (VER, CONT, ITER) and len(args) == 1:
            # 組み込みの振る舞いを確かめた容器・package が作った組み込みの容器: 長さと反復は組み込みの slot
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
            if kind == "func" and module == PKG + ".core.read_limits":
                return READ_LIMITS_RESULTS.get(name)
            if kind == "func":
                return OWNER_RESULTS.get(name)
            return None
        if module.startswith(EXTERNAL_PREFIXES):
            bound = BOUNDED_ENTRY_POINTS.get(f"{module[len(PKG) + 1:]}.{name}")
            if bound == "work":
                # Issue #110: 作業量を必ず受け取る authority の入口。呼ぶ側の有限の作業量を渡すこと
                if kwargs.get("work") != WORK:
                    self.v(node, f"metered authority API {module[len(PKG) + 1:]}.{name} called without a work budget")
                return None
            if bound == "event_contract":
                # Issue #110: authority の event の契約が入力を作る前に測り、件数と大きさを抑える入口
                return None
            # authority が自分の record（型を確かめた authority の型の object）を読むのは許す
            foreign = [k for k in live if not (is_rec(k) and rec_class(k)[0].startswith(EXTERNAL_PREFIXES))]
            if foreign:
                self.v(node, f"live value passed to {module[len(PKG) + 1:]}.{name}")
            return None
        if kind == "module":
            return None
        if kind == "class":
            if not live:
                # plain な引数での構築: `__init__` を辿って field の種類（作業量・package の object）を覚える
                init = self.index.method(module, name, "__init__")
                if init is not None:
                    self.resolved_call(node, ("func",) + init, [obj(module, name), *args], kwargs, live, bound=True)
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
            if keyword is None:
                if tainted(arg_kind):
                    # `**kwargs` の転送: 名前で渡していない引数は全部 live を受け得る
                    for param in (*params[len(args):], *function.args.kwonlyargs):
                        if param.arg not in kwargs and param.arg not in WORK_PARAMETER_NAMES:
                            taint.setdefault(param.arg, LIVE)
                    if function.args.kwarg is not None:
                        taint[function.args.kwarg.arg] = CONT
                continue
            if keyword in names and arg_kind is not None:
                taint[keyword] = arg_kind
            elif keyword not in names and tainted(arg_kind) and function.args.kwarg is not None:
                taint[function.args.kwarg.arg] = CONT
        if bound and params and args and (args[0] == SELF or args[0] is None or is_obj(args[0])):
            taint.pop(params[0].arg, None)
        taint = {k: v for k, v in taint.items() if tainted(v) or v == WORK or is_obj(v)}
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
    # 作業量の object の method（名前で WORK として信頼する引数の、package の側の本体）
    ("proof.obligations.snapshot", "_FreezeMeter.scalar", ("value",)),
    ("proof.obligations.snapshot", "_FreezeMeter.count_value", ("value",)),
    ("proof.obligations.snapshot", "_FreezeMeter.frame", ("count",)),
    ("proof.obligations.snapshot", "_FreezeMeter.scalar_bytes", ("size_bytes",)),
    ("core.budget_policy", "SerializationWork.charge", ("size",)),
    ("core.budget_policy", "SerializationWork.tree", ("leaf",)),
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
    ("proof.obligations.snapshot", "_fingerprint_json", "live value passed to the unbounded owner API .dumps()"):
        "#194: 凍結した値（snapshot の作成では `freeze(budget=)` が数えた写し）を書く。proof の obligation の"
        " digest（`SnapshotFingerprintCodec.digest` の解析時の呼び出し）は凍結を数えない（identity の owner）",
}

#: 宣言した依存の場所ごとの違反の数（それより多い同じ違反は宣言の外）
DECLARED_DEPENDENCY_SITES = {
    ("proof.obligations.snapshot", "_fingerprint_json", "live value passed to the unbounded owner API .dumps()"): 1,
}

#: 宣言した作業量の外の依存の **呼び先**（(module, qualname) → 理由）。監査はここへ入らない
#: （中の仕事は依存の owner の Issue の範囲）。呼ばれなくなれば stale として落ちる。
DECLARED_CALLEES = {
    ("core.expression", "Expression.structural_key"):
        "#194: 閉路のある未凍結の式の cycle_ref は structural_key を組み立てる（identity key の owner）",
    ("core.semantic_snapshot", "SemanticGraphMeter.add_root"):
        "#194: 式の意味の graph（identity の owner の `core/semantic_snapshot`）を辿る distinct node の"
        " 計数。上限（`max_distinct`）で止まる",
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
        elif cls and index.is_readable_property((module, qual)) and params:
            # `live_values.attribute` が呼ぶ property（`readable_property` で宣言したものだけ。field は live）
            yield (module, qual), {params[0].arg: rec(module, cls)}
        elif cls and last == "__setattr__" and len(params) >= 3 and index.is_state_setter((module, qual)):
            # `live_values.set_state` が呼ぶ `state_setter` で宣言した `__setattr__`（書く値は live）
            yield (module, qual), {params[0].arg: rec(module, cls), params[2].arg: LIVE}



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
    seen = collections.Counter()
    for module, qual, line, message in violations:
        match = next(
            (declared for declared in DECLARED_DEPENDENCIES
             if declared[0] == module and declared[1] == qual and message.startswith(declared[2])),
            None,
        )
        if match is not None:
            seen[match] += 1
        if match is None or seen[match] > DECLARED_DEPENDENCY_SITES[match]:
            # 宣言した数より多い同じ違反は宣言の外（新しい呼び出しを宣言に紛れ込ませない）
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
    """関数の本体の、入力に比例し得る構文（`For@行` など）。入れ子の関数の中は除く。

    反復（for / while / 内包）・列を完了させる組み込みと method（`sorted` / `.join` / 引数無しの
    `.sort()` も）・値全体を書く組み込み（`repr` / `dumps`）・`*` の展開・列の繰り返し（`[x] * n`）・
    切り出し（`x[a:b]`）・自分自身の呼び出し（再帰）。
    """

    found = []
    name = getattr(function, "name", None)
    for node in _own_nodes(function):
        if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            found.append(f"{type(node).__name__}@{node.lineno}")
        elif isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            found.append(f"{type(node).__name__}@{node.lineno}")
        elif isinstance(node, ast.Call):
            func = node.func
            if isinstance(func, ast.Name) and func.id in COMPLETING_BUILTINS and node.args:
                found.append(f"{func.id}()@{node.lineno}")
            elif isinstance(func, ast.Name) and func.id in WRITING_BUILTINS:
                found.append(f"{func.id}()@{node.lineno}")
            elif isinstance(func, ast.Attribute) and func.attr in COMPLETING_METHODS and (node.args or func.attr == "sort"):
                found.append(f".{func.attr}()@{node.lineno}")
            elif isinstance(func, ast.Attribute) and func.attr in WRITING_METHODS:
                found.append(f".{func.attr}()@{node.lineno}")
            elif isinstance(func, ast.Name) and func.id == name:
                found.append(f"recursion@{node.lineno}")
        elif isinstance(node, ast.Starred):
            found.append(f"starred@{node.lineno}")
        elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult) and (
            isinstance(node.left, (ast.List, ast.Tuple)) or isinstance(node.right, (ast.List, ast.Tuple))
        ):
            found.append(f"repeat@{node.lineno}")
        elif isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Slice) and not _fixed_slice(node.slice):
            found.append(f"slice@{node.lineno}")
    return sorted(set(found))


#: 値全体を書く組み込み・method（書く量は値の大きさに比例する）
WRITING_BUILTINS = frozenset({"repr"})
WRITING_METHODS = frozenset({"dumps"})


def _fixed_slice(node) -> bool:
    """`x[:N]` / `x[a:N]`（N は定数・大文字の名前の定数）: 写す量は固定の上限まで。"""

    def constant(bound) -> bool:
        if isinstance(bound, ast.Constant):
            return True
        name = bound.id if isinstance(bound, ast.Name) else bound.attr if isinstance(bound, ast.Attribute) else None
        return name is not None and name.isupper()

    return node.upper is not None and constant(node.upper) and (node.lower is None or constant(node.lower))


def _loops_with_preceding(body, preceding=()):
    """関数の本体の反復と、それより前に在る（同じ段か外側の段の）文の組。"""

    for position, statement in enumerate(body):
        before = (*preceding, *body[:position])
        if isinstance(statement, (ast.For, ast.AsyncFor, ast.While)):
            yield statement, before
        if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        for field in ("body", "orelse", "finalbody"):
            inner = getattr(statement, field, None)
            if isinstance(inner, list):
                yield from _loops_with_preceding(inner, before)
        for handler in getattr(statement, "handlers", ()) or ():
            yield from _loops_with_preceding(handler.body, before)


def _names_in(node) -> frozenset:
    """式の中の名前（`None` なら空）。"""

    if node is None:
        return frozenset()
    return frozenset(inner.id for inner in _walk_own(node) if isinstance(inner, ast.Name))


def _assigned_names(function) -> dict:
    """関数の中の `name = 式` の、名前 → 式の中の名前（1 段の遡りに使う）。"""

    found: dict = {}
    for node in _walk_own(function):
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            found.setdefault(node.targets[0].id, set()).update(_names_in(node.value))
    return found


def _measured_assignment_map(function) -> dict:
    """関数の中の `name = 式` の、名前 → 式の中で幅を測った名前（`count = size(values)` なら values）。"""

    found: dict = {}
    for node in _walk_own(function):
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            found.setdefault(node.targets[0].id, set()).update(_measured_names(node.value))
    return found


def _charges_for(nodes, names, iterated, assigned, measured_assignments=None) -> bool:
    """`nodes` の中に、`iterated` の名前（または 1 段の代入でそれを参照する名前）を引数に持つ
    `work.charge(...)` が在るか。辿る値に名前が無い（定数の列など）ときは、どれかの charge で足りる。"""

    measured_assignments = measured_assignments or {}
    iterated = iterated - {name for name in iterated if name in names}
    # 辿る側も 1 段遡る（`positions = sorted(found)` を辿る内包表記は、`found` を数えた charge で足りる）
    iterated = set(iterated)
    for name in tuple(iterated):
        iterated.update(assigned.get(name, ()))
    for node in nodes:
        for inner in ast.walk(node):
            func = getattr(inner, "func", None) if isinstance(inner, ast.Call) else None
            if not (
                isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)
                and func.value.id in names and func.attr == "charge"
            ):
                continue
            if not iterated:
                return True
            # 数えるのは測った幅（`len(x)` / `size(x)` などの引数の名前、または測った値を 1 段の代入で
            # 束ねた名前）: `work.charge(values is None)` は幅を数えていない
            charged = set()
            for argument in (*inner.args, *(keyword.value for keyword in inner.keywords)):
                charged |= _measured_names(argument)
                for name in _names_in(argument):
                    if name in measured_assignments:
                        charged |= measured_assignments[name]
            if charged & iterated:
                return True
    return False


#: 列の幅を測る呼び出し（`work.charge(...)` の引数でこれに渡した名前が「数えた幅」）
_MEASURING_CALLS = frozenset({"len", "size", "storage_count", "storage_extent", "container_frame_bytes"})


def _measured_names(node) -> set:
    """式の中で幅を測る呼び出し（`len(x)` / `size(x)` / `x.__len__()`）に渡した名前。"""

    found = set()
    for inner in _walk_own(node):
        if isinstance(inner, ast.Call):
            func = inner.func
            called = func.id if isinstance(func, ast.Name) else func.attr if isinstance(func, ast.Attribute) else None
            if called in _MEASURING_CALLS:
                for argument in inner.args:
                    found |= _names_in(argument)
            if called == "__len__" and isinstance(func, ast.Attribute):
                found |= _names_in(func.value)
    return found


def _charges(nodes, names) -> bool:
    for node in nodes:
        for inner in ast.walk(node):
            func = getattr(inner, "func", None) if isinstance(inner, ast.Call) else None
            if (
                isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)
                and func.value.id in names and func.attr == "charge"
            ):
                return True
    return False


def _uses_work(nodes, names) -> bool:
    """`nodes` の中で作業量の引数を数える（`work.charge(...)`）か、呼び先へ渡すか。"""

    for node in nodes:
        for inner in ast.walk(node):
            if not isinstance(inner, ast.Call):
                continue
            func = inner.func
            if (
                isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)
                and func.value.id in names and func.attr == "charge"
            ):
                return True
            # 渡すのは作業量を受け取る呼び先へだけ（`repr(work)` / `str(work)` のような組み込みへ渡しても
            # 数えたことにならない）
            if isinstance(func, ast.Name) and func.id in _PYTHON_BUILTINS:
                continue
            arguments = [*inner.args, *(keyword.value for keyword in inner.keywords)]
            if any(isinstance(argument, ast.Name) and argument.id in names for argument in arguments):
                return True
    return False


_PYTHON_BUILTINS = frozenset(dir(__import__("builtins")))


_EMPTY_CONTAINER_CALLS = frozenset({"list", "set", "dict"})


def _local_containers(function) -> frozenset:
    """関数の中で作った容器の名前: 空の容器（`[]` / `set()` / `{}`）・内包表記・それらだけから作った値
    （`order = sorted(keyed)`）。大きさは関数の中で詰めた反復・内包表記が決め、それらは同じ規則で確かめる。"""

    assignments = []
    for node in _walk_own(function):
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target, value = node.targets[0], node.value
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            target, value = node.target, node.value
        else:
            continue
        if isinstance(target, ast.Name):
            assignments.append((target.id, value))
    def _created(value) -> bool:
        return (
            (isinstance(value, (ast.List, ast.Set)) and not value.elts)
            or (isinstance(value, ast.Dict) and not value.keys)
            or (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
                and value.func.id in _EMPTY_CONTAINER_CALLS and not value.args and not value.keywords)
            or isinstance(value, (ast.ListComp, ast.SetComp, ast.DictComp))
        )

    bindings: dict = {}
    for name, value in assignments:
        bindings.setdefault(name, []).append(value)
    # 名前ごとに **全部の** 代入を見る（`kept = []` の後に `kept = values` と束ね直した名前は local でない）。
    # 添字（`box[0]`）は local の容器の中の値で、容器ではない
    found = {name for name, values in bindings.items() if all(_created(value) for value in values)}
    changed = True
    while changed:
        changed = False
        for name, values in bindings.items():
            if name in found:
                continue
            if all(
                _created(value) or (
                    not any(isinstance(inner, ast.Subscript) for inner in _walk_own(value))
                    and (_names_in(value) - _PYTHON_BUILTINS)
                    and (_names_in(value) - _PYTHON_BUILTINS) <= found
                )
                for value in values
            ):
                found.add(name)
                changed = True
    return frozenset(found)


def _traversed_sources(node) -> frozenset:
    """反復・完成させる構文が辿る元の名前（反復の対象・内包表記の `iter`・呼び出しの引数と method の受け手）。"""

    if isinstance(node, (ast.For, ast.AsyncFor)):
        found = _names_in(node.iter)
    elif isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
        found = frozenset().union(*(_names_in(generator.iter) for generator in node.generators))
    elif isinstance(node, ast.Call):
        parts = [*node.args, *(keyword.value for keyword in node.keywords)]
        if isinstance(node.func, ast.Attribute):
            parts.append(node.func.value)
        found = frozenset().union(*(_names_in(part) for part in parts)) if parts else frozenset()
    elif isinstance(node, ast.AugAssign):
        found = _names_in(node.value) | _names_in(node.target)
    elif isinstance(node, ast.While):
        found = _names_in(node.test)
    else:
        found = frozenset()
    return found - _PYTHON_BUILTINS


def _counter_update(node, local) -> bool:
    """累算の代入のうち、関数の中で作った容器を詰めるもの（`kept += values`）以外（数の counter・属性の更新）。
    容器を詰める `+=` は、右辺が同じ規則（local だけ・数えた幅）を満たすときだけ。"""

    return isinstance(node, ast.AugAssign) and not (isinstance(node.target, ast.Name) and node.target.id in local)


def _completes_local(node, local) -> bool:
    """関数の中で作った容器だけを辿る構文（`tuple(kept)` / `keyed.sort()` / `[t for t in keyed]`）:
    大きさは詰めた反復・内包表記が決める。"""

    sources = _traversed_sources(node)
    return bool(sources) and sources <= local


def _completing(node) -> bool:
    """列を完成させる構文（内包表記・`sorted` / `tuple` などの組み込み・`.join` / `.sort()` などの method・
    `+=` / `|=` などの累算の代入）。"""

    if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp)):
        return True
    if isinstance(node, ast.AugAssign):
        return True
    if isinstance(node, ast.Call):
        func = node.func
        if isinstance(func, ast.Name) and func.id in COMPLETING_BUILTINS and node.args:
            return True
        if isinstance(func, ast.Attribute) and func.attr in COMPLETING_METHODS and (node.args or func.attr == "sort"):
            return True
    return False


def _own_expressions(statement):
    """文そのものの式（複合文は本体を除いた部分: 条件・反復の対象・with の項目）。"""

    if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return []
    if isinstance(statement, (ast.For, ast.AsyncFor)):
        return [statement.iter]
    if isinstance(statement, (ast.While, ast.If)):
        return [statement.test]
    if isinstance(statement, (ast.With, ast.AsyncWith)):
        return [item.context_expr for item in statement.items]
    if isinstance(statement, ast.Try):
        return []
    return [statement]


def _completions_with_preceding(body, preceding=()):
    """関数の本体の、列を完成させる構文と、それを含む文より前に在る（同じ段か外側の段の）文の組。"""

    for position, statement in enumerate(body):
        before = (*preceding, *body[:position])
        for expression in _own_expressions(statement):
            for node in _walk_own(expression):
                if _completing(node):
                    yield node, before
        if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        for field in ("body", "orelse", "finalbody"):
            inner = getattr(statement, field, None)
            if isinstance(inner, list):
                yield from _completions_with_preceding(inner, before)
        for handler in getattr(statement, "handlers", ()) or ():
            yield from _completions_with_preceding(handler.body, before)


def _walk_own(node):
    """`node` の中の node（入れ子の関数・lambda の中は除く）。"""

    pending = [node]
    while pending:
        current = pending.pop()
        yield current
        for child in ast.iter_child_nodes(current):
            if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
                pending.append(child)


def work_owner(index: PackageIndex, key) -> Optional[str]:
    """関数が自分で作業量の owner を持つか: "B"（作業量 / 予算を引数に取り、反復ごとに数えるか渡す）、
    "C"（反復ごとに必ず 1 つ yield する generator）、どちらでもなければ `None`。

    B は構文の規則: 反復・列を完成させる構文（内包表記・完成させる組み込み / method・local の容器を詰める
    `+=`）は、その中で作業量を数えるか作業量を受け取る呼び先へ渡すか、それより前に辿る値の幅を測って
    数える（`len` / `size` などの引数・1 段の代入）か、関数の中で作った容器だけを辿る。静的な規則の限界:
    解決できない呼び先（method）へ作業量を渡す形は「渡した」と数え、B の関数の中の `repr` / 切り出し /
    `*` / 繰り返し / 再帰は見ない。これらは bounded path の入口を実行する動的な test
    （`test_record_walks_on_the_bounded_path_never_see_uncounted_input` ほか）が補う。
    """

    function = index.functions[key]
    args = function.args
    names = {
        arg.arg for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs) if arg.arg in WORK_PARAMETER_NAMES
    }
    own = list(_own_nodes(function))
    loops = [n for n in own if isinstance(n, (ast.For, ast.AsyncFor, ast.While))]
    local = _local_containers(function)
    if names:
        # 引数に取るだけでは owner でない: 関数の中で数えるか（作業量を受け取る呼び先へ）渡し、反復と
        # 列を完成させる構文（内包表記・`sorted` など）は、その中で数えるか渡すか、それより前に（辿る幅を）
        # 数える
        # 前に数える形は、数える呼び出しの引数が辿る値（の名前、または 1 段の代入の元）を参照すること
        # （`work.charge(1)` の後の `sorted(values)` は数えていない）
        assigned = _assigned_names(function)
        measured = _measured_assignment_map(function)
        if (
            _uses_work(function.body, names)
            and all(
                _uses_work(loop.body, names)
                or _charges_for(before, names, _traversed_sources(loop), assigned, measured)
                or _completes_local(loop, local)
                for loop, before in _loops_with_preceding(function.body)
            )
            and all(
                _counter_update(node, local)
                or _uses_work([node], names)
                or _charges_for(before, names, _names_in(node), assigned, measured)
                or _completes_local(node, local)
                for node, before in _completions_with_preceding(function.body)
            )
        ):
            return "B"
        return None
    if loops and all(_yields_every_iteration(loop) for loop in loops):
        completing = any(
            isinstance(n, (ast.ListComp, ast.SetComp, ast.DictComp))
            or (isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in COMPLETING_BUILTINS and n.args)
            for n in own
        )
        if not completing:
            return "C"
    return None


def _yields_every_iteration(loop) -> bool:
    """反復の本体の直下に yield の文があり、`continue` で飛ばさない（1 回ごとに必ず 1 つ渡す）。"""

    direct = any(
        isinstance(statement, ast.Expr) and isinstance(statement.value, (ast.Yield, ast.YieldFrom))
        for statement in loop.body
    )
    skips = any(isinstance(inner, ast.Continue) for statement in loop.body for inner in ast.walk(statement))
    return direct and not skips


def unowned_proportional_work(package_root: pathlib.Path, analyzed: Iterable[Tuple[str, str]], index: PackageIndex):
    """bounded path の関数のうち、入力に比例し得る構文を持ち、作業量の owner を持たないもの。"""

    out = {}
    for key in sorted(set(analyzed)):
        constructs = proportional_constructs(index.functions[key])
        if constructs and work_owner(index, key) is None:
            out[(key[0][len(PKG) + 1:], key[1])] = constructs
    return out
