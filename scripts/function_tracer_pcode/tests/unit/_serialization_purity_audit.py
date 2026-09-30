"""直列化の protocol が field だけの関数であることの静的な監査（Issue #219 C-RS2）。

`core/semantic_lifecycle.FIELD_DETERMINED_SERIALIZATION_MARKER` を宣言した型について、直列化の
owner がその型の値に使う method（`serialization_protocol_methods`）と、そこから辿る package の
関数・method が **次のものだけを読む** ことを確かめる:

* `self` の dataclass field と、同じ型の method（method は同じ規則で辿る）
* 引数・局所変数。局所の値の属性は、**その場所で** `type(x) is C` / `isinstance(x, C)` によって
  型を確かめた値の field・method だけ（確かめる分岐の外の読みは許さない）
* 組み込みの関数のうち、渡した値の状態だけを読むもの（`_PURE_BUILTINS`）
* 読みの owner（`core.json_encoding` / `core.live_values` / `core.read_limits`）の関数。owner の
  読み方は owner 自身の監査（J19 / J22）と adversarial test が固定している
* module の不変な定数（組み込みの scalar とその tuple・frozenset）、package の関数（同じ規則で
  辿る）、class（型の比較・`isinstance`・例外にだけ使う）

**許さないもの**（監査できない記法も含めて拒否する）: `global` / `nonlocal`、閉包、可変な module
global・class 属性の読み取り、引数・`self` の状態への書き込み、`getattr` / `vars` / `setattr` /
`super` など、`__dict__` / `__class__`、型を確かめていない値の属性・method、package の外の関数、
組み込みの値と構文で言えない値の `raw()`（snapshot codec がその値の型の規則で写すため）。

監査は **拒否側に倒す**: 監査が読めない形の code は violation になり、その型は宣言できない
（宣言しなければ closed にならないだけで、誤りにはならない）。
"""

from __future__ import annotations

import ast
import builtins
import dataclasses
import enum
import inspect
import textwrap
import types
from typing import Any, Dict, List, Optional, Set, Tuple

PKG = "scripts.function_tracer_pcode."
#: 読みの owner（値の状態の読み方を owner 自身が監査している module）
OWNER_MODULES = frozenset(
    {PKG + "core.json_encoding", PKG + "core.live_values", PKG + "core.read_limits"}
)
#: 渡した値の状態だけを読む組み込みの関数・型・例外
_PURE_BUILTINS = frozenset(
    {
        "type", "isinstance", "issubclass", "len", "max", "min", "abs", "any", "all", "sorted",
        "tuple", "list", "dict", "set", "frozenset", "str", "int", "float", "bool", "bytes",
        "range", "enumerate", "zip", "reversed", "repr", "hex", "round", "divmod", "sum",
        "iter", "next", "callable",
        "TypeError", "ValueError", "KeyError", "IndexError", "AttributeError", "RecursionError",
        "OverflowError", "ArithmeticError", "NotImplementedError", "Exception",
        "None", "True", "False", "NotImplemented",
    }
)
#: 監査できない読み方・外の状態に届く組み込み
_FORBIDDEN_NAMES = frozenset(
    {"getattr", "setattr", "delattr", "hasattr", "vars", "globals", "locals", "eval", "exec",
     "compile", "super", "__import__", "open", "id", "hash", "object", "print", "input"}
)
_RAW = (PKG + "core.json_encoding", "raw")


def _immutable_constant(value: Any) -> bool:
    kind = type(value)
    if value is None or kind in (bool, int, float, str, bytes):
        return True
    if kind in (tuple, frozenset):
        return all(_immutable_constant(item) for item in value)
    return False


def _function_tree(function: Any) -> Optional[ast.AST]:
    try:
        source = textwrap.dedent(inspect.getsource(function))
    except (OSError, TypeError):
        return None
    tree = ast.parse(source)
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _strip_annotations(node)
            return node
    return None


def _strip_annotations(function: ast.AST) -> None:
    """型注釈は実行時に読まれない（`from __future__ import annotations`）ので監査しない。"""

    for node in ast.walk(function):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            if not isinstance(node, ast.Lambda):
                node.returns = None
                node.decorator_list = []
            args = node.args
            for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs, args.vararg, args.kwarg):
                if arg is not None:
                    arg.annotation = None
        if isinstance(node, ast.AnnAssign):
            node.annotation = ast.Constant(value=None)


def _parameters(function: ast.AST) -> List[str]:
    args = function.args
    names = [arg.arg for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs)]
    names.extend(arg.arg for arg in (args.vararg, args.kwarg) if arg is not None)
    return names


def _bound_names(function: ast.AST) -> Set[str]:
    names: Set[str] = set(_parameters(function))
    for node in ast.walk(function):
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
            names.add(node.id)
        elif isinstance(node, (ast.FunctionDef, ast.Lambda)) and node is not function:
            names.update(_parameters(node))
            if isinstance(node, ast.FunctionDef):
                names.add(node.name)
        elif isinstance(node, ast.ExceptHandler) and node.name:
            names.add(node.name)
    return names


# ---------------------------------------------------------------------------
# 型の確かめ（flow-sensitive）
# ---------------------------------------------------------------------------

Narrowing = Dict[str, Tuple[type, ...]]


def _resolve_types(node: ast.AST, namespace: Dict[str, Any]) -> Tuple[type, ...]:
    if isinstance(node, ast.Name) and isinstance(namespace.get(node.id), type):
        return (namespace[node.id],)
    if isinstance(node, ast.Tuple):
        return tuple(kind for item in node.elts for kind in _resolve_types(item, namespace))
    return ()


def _test_narrowing(test: ast.AST, namespace: Dict[str, Any], positive: bool) -> Narrowing:
    """`test` が真（`positive`）/ 偽のときに型が確かめられる名前。"""

    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _test_narrowing(test.operand, namespace, not positive)
    if isinstance(test, ast.BoolOp):
        if isinstance(test.op, ast.And) and positive:
            merged: Narrowing = {}
            for value in test.values:
                merged.update(_test_narrowing(value, namespace, True))
            return merged
        if isinstance(test.op, ast.Or) and not positive:
            merged = {}
            for value in test.values:
                merged.update(_test_narrowing(value, namespace, False))
            return merged
        return {}
    if (
        isinstance(test, ast.Compare)
        and len(test.ops) == 1
        and isinstance(test.ops[0], (ast.Is, ast.IsNot))
        and isinstance(test.left, ast.Call)
        and isinstance(test.left.func, ast.Name)
        and test.left.func.id == "type"
        and len(test.left.args) == 1
        and isinstance(test.left.args[0], ast.Name)
    ):
        holds = isinstance(test.ops[0], ast.Is)
        if holds == positive:
            kinds = _resolve_types(test.comparators[0], namespace)
            if kinds:
                return {test.left.args[0].id: kinds}
        return {}
    if (
        positive
        and isinstance(test, ast.Call)
        and isinstance(test.func, ast.Name)
        and test.func.id == "isinstance"
        and len(test.args) == 2
        and isinstance(test.args[0], ast.Name)
    ):
        kinds = _resolve_types(test.args[1], namespace)
        if kinds:
            return {test.args[0].id: kinds}
    return {}


def _always_exits(body: List[ast.stmt]) -> bool:
    return bool(body) and isinstance(body[-1], (ast.Raise, ast.Return, ast.Continue, ast.Break))


def _narrowings_in_scope(function: ast.AST, namespace: Dict[str, Any]) -> Dict[int, Narrowing]:
    """AST の node（`id`）→ その場所で確かめられている型。"""

    scopes: Dict[int, Narrowing] = {}

    def visit(node: ast.AST, env: Narrowing) -> None:
        scopes[id(node)] = env
        if isinstance(node, ast.If):
            visit(node.test, env)
            visit_block(node.body, {**env, **_test_narrowing(node.test, namespace, True)})
            visit_block(node.orelse, {**env, **_test_narrowing(node.test, namespace, False)})
            return
        if isinstance(node, ast.IfExp):
            visit(node.test, env)
            visit(node.body, {**env, **_test_narrowing(node.test, namespace, True)})
            visit(node.orelse, {**env, **_test_narrowing(node.test, namespace, False)})
            return
        if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
            current = env
            for value in node.values:
                visit(value, current)
                current = {**current, **_test_narrowing(value, namespace, True)}
            return
        for _field_name, value in ast.iter_fields(node):
            if isinstance(value, list) and value and isinstance(value[0], ast.stmt):
                visit_block(value, env)
            elif isinstance(value, list):
                for item in value:
                    if isinstance(item, ast.AST):
                        visit(item, env)
            elif isinstance(value, ast.AST):
                visit(value, env)

    def visit_block(statements: List[ast.stmt], env: Narrowing) -> None:
        current = env
        for statement in statements:
            visit(statement, current)
            # `if type(x) is not C: raise` の後は x が C
            if isinstance(statement, ast.If) and _always_exits(statement.body) and not statement.orelse:
                current = {**current, **_test_narrowing(statement.test, namespace, False)}

    visit(function, {})
    return scopes


# ---------------------------------------------------------------------------
# 監査
# ---------------------------------------------------------------------------


class PurityAudit:
    """宣言した型ごとの監査。`violations` が空なら宣言してよい。"""

    def __init__(self) -> None:
        self.violations: List[str] = []
        self._visited: Set[Any] = set()

    def audit_type(self, kind: type, protocol_methods: Tuple[str, ...]) -> List[str]:
        if not dataclasses.is_dataclass(kind) or not kind.__dataclass_params__.frozen:
            self.violations.append(f"{kind.__qualname__}: not a frozen dataclass")
            return self.violations
        for name in protocol_methods:
            function = _class_function(kind, name)
            if function is None:
                self.violations.append(f"{kind.__qualname__}.{name}: not a plain function")
            else:
                self.audit_function(function, kind)
        return self.violations

    def audit_function(self, function: types.FunctionType, owner: Optional[type]) -> None:
        key = (function, owner)
        if key in self._visited:
            return
        self._visited.add(key)
        where = f"{function.__module__}.{function.__qualname__}"
        if function.__closure__:
            self.violations.append(f"{where}: closes over outer state")
        tree = _function_tree(function)
        if tree is None:
            self.violations.append(f"{where}: source not available")
            return
        namespace = dict(function.__globals__)
        parameters = _parameters(tree)
        context = _Context(
            audit=self,
            where=where,
            namespace=namespace,
            bound=_bound_names(tree),
            parameters=set(parameters),
            scopes=_narrowings_in_scope(tree, namespace),
            owner=owner,
            self_name=(parameters[0] if owner is not None and parameters else None),
        )
        for node in ast.walk(tree):
            context.check(node)

    def audit_callable(self, function: types.FunctionType, lineno: Any, where: str) -> None:
        module = function.__module__ or ""
        if module in OWNER_MODULES:
            return
        if not module.startswith(PKG):
            self.violations.append(f"{where}:{lineno}: calls {module}.{function.__qualname__} outside the package")
            return
        self.audit_function(function, None)


class _Context:
    def __init__(self, *, audit, where, namespace, bound, parameters, scopes, owner, self_name) -> None:
        self.audit = audit
        self.where = where
        self.namespace = namespace
        self.bound = bound
        self.parameters = parameters
        self.scopes = scopes
        self.owner = owner
        self.self_name = self_name

    def fail(self, node: ast.AST, message: str) -> None:
        self.audit.violations.append(f"{self.where}:{getattr(node, 'lineno', '?')}: {message}")

    def check(self, node: ast.AST) -> None:
        if isinstance(node, (ast.Global, ast.Nonlocal)):
            self.fail(node, "global/nonlocal")
        elif isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign, ast.Delete)):
            targets = node.targets if isinstance(node, (ast.Assign, ast.Delete)) else [node.target]
            for target in targets:
                self._check_store(target)
        elif isinstance(node, ast.Call):
            self._check_call(node)
        elif isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Load):
            self._check_attribute(node)
        elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
            self._check_name(node)

    # -- 書き込み -----------------------------------------------------------
    def _check_store(self, target: ast.AST) -> None:
        for node in ast.walk(target):
            if isinstance(node, (ast.Attribute, ast.Subscript)) and isinstance(node.ctx, (ast.Store, ast.Del)):
                base = node.value
                while isinstance(base, (ast.Attribute, ast.Subscript)):
                    base = base.value
                if not isinstance(base, ast.Name) or base.id in self.parameters or base.id not in self.bound:
                    self.fail(node, "writes the state of an argument, of self or of a global")

    # -- 名前 ---------------------------------------------------------------
    def _check_name(self, node: ast.Name) -> None:
        name = node.id
        if name in self.bound:
            return
        if name in _FORBIDDEN_NAMES:
            self.fail(node, f"uses {name}")
            return
        if name in _PURE_BUILTINS:
            return
        if name not in self.namespace:
            self.fail(node, f"builtin {name} is not in the pure list" if hasattr(builtins, name) else f"unresolved name {name}")
            return
        value = self.namespace[name]
        if _immutable_constant(value):
            return
        if isinstance(value, types.ModuleType):
            if value.__name__ not in OWNER_MODULES:
                self.fail(node, f"module {value.__name__} is not a reading owner")
            return
        if isinstance(value, types.FunctionType):
            self.audit.audit_callable(value, node.lineno, self.where)
            return
        if isinstance(value, type):
            return
        self.fail(node, f"reads module state {name} ({type(value).__name__})")

    # -- 呼び出し -----------------------------------------------------------
    def _check_call(self, node: ast.Call) -> None:
        func = node.func
        if isinstance(func, ast.Name):
            value = self.namespace.get(func.id) if func.id not in self.bound else None
            if isinstance(value, types.FunctionType) and (value.__module__, value.__name__) == _RAW:
                self._check_raw(node)
            if (
                isinstance(value, type)
                and func.id not in _PURE_BUILTINS
                and not issubclass(value, BaseException)
            ):
                self.fail(node, f"constructs {func.id} (its representation is not audited here)")
            return
        if isinstance(func, ast.Attribute):
            if isinstance(func.value, ast.Constant):
                # 組み込みの値の method（`", ".join(...)` など）
                return
            if isinstance(func.value, ast.Name):
                # 属性の読みとして `_check_attribute` が裁く（method なら辿る）
                return
            self.fail(node, "calls a method of a computed value")
            return
        self.fail(node, "calls a computed callable")

    def _check_raw(self, node: ast.Call) -> None:
        """`raw(x)` は x をそのまま出力へ置き、snapshot codec が x を x の型の規則（`stable_key`
        など）で写す: x が組み込みの値だけから成ると **構文で** 言えるときだけ許す。

        許す形: package の関数の呼び出しで、その関数のすべての `return` が組み込みの値の literal
        （定数・tuple・f-string・文字列の連結）で、中の呼び出しが型の名前の読み（owner）だけのもの。
        """

        argument = node.args[0] if len(node.args) == 1 and not node.keywords else None
        if (
            isinstance(argument, ast.Call)
            and isinstance(argument.func, ast.Name)
            and isinstance(self.namespace.get(argument.func.id), types.FunctionType)
        ):
            helper = self.namespace[argument.func.id]
            tree = _function_tree(helper)
            if tree is not None and _returns_builtin_literals(tree, helper.__globals__):
                return
        self.fail(node, "raw() of a value the audit cannot prove built-in")

    # -- 属性 ---------------------------------------------------------------
    def _check_attribute(self, node: ast.Attribute) -> None:
        if not isinstance(node.value, ast.Name):
            if not isinstance(node.value, ast.Constant):
                self.fail(node, f"reads .{node.attr} of a computed value")
            return
        base = node.value.id
        if node.attr in ("__dict__", "__class__"):
            self.fail(node, f"reads {base}.{node.attr}")
            return
        if base == self.self_name and self.owner is not None:
            self._check_member(node, self.owner, f"self.{node.attr}")
            return
        if base in self.bound:
            kinds = self.scopes.get(id(node), {}).get(base, ())
            if not kinds:
                self.fail(node, f"reads {base}.{node.attr} on a value whose type is not checked here")
                return
            for kind in kinds:
                self._check_member(node, kind, f"{kind.__qualname__}.{node.attr}")
            return
        value = self.namespace.get(base)
        if isinstance(value, types.ModuleType) and value.__name__ in OWNER_MODULES:
            return
        if isinstance(value, type):
            member = _class_value(value, node.attr)
            function = getattr(member, "__func__", member)
            if isinstance(value, enum.EnumMeta) and isinstance(member, value):
                # enum の member（class の定義）
                return
            if _immutable_constant(member):
                return
            if isinstance(function, types.FunctionType):
                self.audit.audit_callable(function, node.lineno, self.where)
                return
        self.fail(node, f"reads {base}.{node.attr} that cannot be resolved")

    def _check_member(self, node: ast.Attribute, kind: type, label: str) -> None:
        fields = {field.name for field in dataclasses.fields(kind)} if dataclasses.is_dataclass(kind) else set()
        if node.attr in fields:
            return
        method = _class_function(kind, node.attr)
        if method is not None:
            self.audit.audit_function(method, kind)
            return
        if _immutable_constant(_class_value(kind, node.attr)):
            return
        self.fail(node, f"reads {label}, not a field, method or constant")


def _class_function(kind: type, name: str) -> Optional[types.FunctionType]:
    for base in kind.__mro__:
        if name in base.__dict__:
            member = base.__dict__[name]
            if isinstance(member, property):
                member = member.fget
            function = getattr(member, "__func__", member)
            return function if isinstance(function, types.FunctionType) else None
    return None


_ABSENT = object()


def _class_value(kind: type, name: str) -> Any:
    for base in kind.__mro__:
        if name in base.__dict__:
            return base.__dict__[name]
    return _ABSENT


def _returns_builtin_literals(function: ast.AST, namespace: Dict[str, Any]) -> bool:
    returns = [node for node in ast.walk(function) if isinstance(node, ast.Return)]
    return bool(returns) and all(
        node.value is not None and _builtin_literal(node.value, namespace) for node in returns
    )


def _builtin_literal(node: ast.AST, namespace: Dict[str, Any]) -> bool:
    if isinstance(node, ast.Constant):
        return True
    if isinstance(node, ast.Tuple):
        return all(_builtin_literal(item, namespace) for item in node.elts)
    if isinstance(node, ast.JoinedStr):
        return all(
            _builtin_literal(item.value if isinstance(item, ast.FormattedValue) else item, namespace)
            for item in node.values
        )
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return _builtin_literal(node.left, namespace) and _builtin_literal(node.right, namespace)
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        function = namespace.get(node.func.id)
        # 読みの owner の、型の名前を組み込みの str で返す関数（型の名前は class の定義）
        return (
            isinstance(function, types.FunctionType)
            and function.__module__ in OWNER_MODULES
            and function.__name__ in ("type_module", "type_name")
            and all(_type_argument(argument) for argument in node.args)
        )
    return False


def _type_argument(node: ast.AST) -> bool:
    if isinstance(node, ast.Name):
        return True
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "type"
