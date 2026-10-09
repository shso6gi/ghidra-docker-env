# -*- coding: utf-8 -*-
"""runtime ref の構築の経路が、外の値を **安全な読み方でだけ** 消費することを確かめる静的な解析（Issue #242）。

構築の契約: ref の構築（`__post_init__`・自前の `__init__`・factory と、ref から ref を作る入口）と、そこから
呼ぶ関数は、scalar の subclass の code（`__bool__` / `__eq__` / `__hash__` / `__format__` / 算術 / 文字列の
method / `__int__` など）を呼ばない。外の値は消費の前に次のどれかで読む:

- 入口の引数のうち注釈が scalar / tuple のもの: `runtime_ref_entry` が本体の前に写す（生成された `__init__` の
  field は `runtime_ref_record` が `__post_init__` の前に写す）
- それ以外（注釈が `Any` の引数・field、構築中の tuple の要素、API の戻り値）: `live_values` の reader
  （`exact_scalar` / `scalar_int` / `scalar_text` / `scalar_bool` / `sequence_or_empty` など）

この module は、上の規則に反する **消費** を構文から探す。値の状態を 5 つで追う:

- clean: 消費してよい（定数、reader の結果、写した field、写した引数、比較や `not` の結果、組み込み関数を
  clean な値に当てた結果）
- clean_container: 要素も clean な容器（定数の tuple、clean な値で作った tuple / list / 内包）
- ref:C / elem:C: ref の class C の値 / C を要素に持つ容器（属性の読みは C の field の分類で決まる）
- container: 容器としては組み込みの振る舞い（真偽・長さ・反復）で読めるが、要素は未確認
- unknown: 上のどれでもない（消費すると違反）

消費として数えるもの: 真偽（`if` / `while` / `and` / `or` の左 / `not` / 条件式 / `assert`）、`is` 以外の比較・
`in`、算術・単項演算・累算代入、f-string の値、集合・dict の key（hash）、文字列の method、組み込みの変換・
集計（`int` / `str` / `bool` / `float` / `repr` / `format` / `hash` / `sorted` / `min` / `max` / `sum` / `set` など）。

**解析の範囲と限界**（PASS をこれ以上の保証と読まない）:

- 起点: `@runtime_ref_record` の class の `__post_init__`・自前の `__init__`・classmethod / staticmethod と、
  `@runtime_ref_entry` の関数・method。そこから同じ module と import した ref module の関数、入れ子の関数、
  `key=` の lambda を辿る。構築（`__post_init__`・自前の `__init__`・factory）からは自分の class の method も
  辿る。ref から ref を作る method からは自分の method を辿らない（その結果は下の 3 つ目）。
- owner が写したと言えるのは **自分の** field だけ（scalar は exact）。tuple の field の要素は常に未確認
  （list のまま受理した値は owner が写さない）。他の object の属性は、注釈が ref の class でも scalar としては
  未確認（実際の値は代わりの型・外の object かもしれない）。ref の field を指す属性は ref として辿る。
- ref の method / property の **呼び出しの結果**と、ref module の関数（同じ module・import・入れ子）の戻り値は
  clean として扱う（それぞれが自分の本体で検査される。注釈が Any の field を結果に含める ref は、自分の検証で
  その field の読み方を決める: 例 `PcodeOpRef.binary_id`）。関数の引数の状態は、到達した呼び出し元の実引数の
  状態の meet（fixpoint）。
- 制御の流れは分岐ごとに追い、合流で悪い方に寄せる（`return` / `raise` / `break` / `continue` で終わる分岐は
  合流に入れない）。`isinstance(x, C)` は C が ref の class か `bool` のときだけ絞り込む（`and` の右にも伝える）。
- 代入以外の変異（`list.append` など）は追わない。`getattr` は定数の名前だけを追う。`setattr` / `exec` /
  動的な名前は追わない。呼び出し元の層（analysis など）が入口に渡す前の加工はこの解析の外。
- 振る舞いは `test_issue242_entry_matrix.py` の行列（入口 × 消費 × 入力の形）と、review の反例の test が
  実行して確かめる（helper の戻り値の中身など、この解析が信用する位置を含む）。
"""

from __future__ import annotations

import ast
import dataclasses
import importlib
import pathlib
import typing
from typing import Any, Dict, Iterable, List, Optional, Set, Tuple

CLEAN = "clean"
CLEAN_CONTAINER = "clean_container"
CONTAINER = "container"
UNKNOWN = "unknown"

PACKAGE = pathlib.Path(__file__).resolve().parents[2]
REF_MODULE_PREFIXES = (
    "scripts.function_tracer_pcode.core.runtime_refs",
    "scripts.function_tracer_pcode.core.call_target",
)

#: 値を clean にする reader（`live_values` / owner）
READERS = frozenset({
    "exact_scalar", "scalar_int", "scalar_text", "scalar_bool", "as_bool", "as_int", "as_str", "str_value",
    "int_value", "plain_scalar", "json_scalar", "exact_field_value", "is_kind", "type_name", "type_module",
    "builtin_str", "builtin_sequence", "size", "scalar_int_or",
})
#: 値を「組み込みの振る舞いの容器（要素は未確認）」にする reader
CONTAINER_READERS = frozenset({"builtin_items", "elements_of"})
#: どの値に当てても外の型の code を呼ばない組み込み
SAFE_ANY = frozenset({"isinstance", "issubclass", "callable", "id", "type", "len_of_builtin"})
#: 引数が clean なら結果も clean な組み込み（それ自体が消費: 引数が clean でなければ違反）
CONSUMING_BUILTINS = frozenset({
    "int", "str", "float", "bool", "repr", "format", "hash", "sorted", "min", "max", "sum", "abs", "round",
    "set", "frozenset", "dict", "divmod", "pow", "any", "all",
})
#: 容器を作り直す組み込み（要素は読まない。要素の状態を引き継ぐ）
CONTAINER_BUILTINS = frozenset({"tuple", "list", "enumerate", "zip", "reversed", "iter", "range"})
#: 組み込みの型（`bytes.hex(value)` のように型から method を引くと、基底型の slot の実装を呼ぶ）
BUILTIN_TYPES = frozenset({"int", "str", "bytes", "float", "tuple", "list", "dict", "bool"})
#: scalar の値に当てると subclass の code を呼ぶ method（文字列・整数）
SCALAR_METHODS = frozenset({
    "strip", "lstrip", "rstrip", "lower", "upper", "startswith", "endswith", "split", "rsplit", "join",
    "replace", "format", "encode", "isdigit", "bit_length", "to_bytes", "hex", "casefold", "partition",
    "find", "index", "count", "zfill", "title", "capitalize", "splitlines",
})


def _decorated(node: Any, names: Iterable[str]) -> bool:
    names = set(names)
    return any(
        (isinstance(d, ast.Name) and d.id in names) or (isinstance(d, ast.Attribute) and d.attr in names)
        for d in node.decorator_list
    )


@dataclasses.dataclass
class _FieldInfo:
    kind: str  # scalar / bool / tuple / object（owner の分類）
    ref: Optional[str]  # 注釈が ref の class ならその名前
    element: Optional[str]  # tuple の要素が ref ならその名前、葉が全部 scalar なら "scalar"


class RefWorld:
    """ref の class とその field の分類（実行して読む: owner の分類そのもの）。"""

    def __init__(self, modules: Iterable[Any]):
        from scripts.function_tracer_pcode.core.runtime_ref_record import _field_hints, _kind_of

        self.classes: Dict[str, Dict[str, _FieldInfo]] = {}
        for module in modules:
            for value in vars(module).values():
                if isinstance(value, type) and dataclasses.is_dataclass(value) and value.__module__ == module.__name__:
                    hints = _field_hints(value)
                    self.classes[value.__name__] = {
                        item.name: _FieldInfo(
                            _kind_of(hints[item.name]), self._ref(hints[item.name]), self._element(hints[item.name])
                        )
                        for item in dataclasses.fields(value)
                    }

    @staticmethod
    def _unwrap(hint: Any) -> Any:
        if typing.get_origin(hint) is typing.Union:
            rest = [arg for arg in typing.get_args(hint) if arg is not type(None)]
            return rest[0] if len(rest) == 1 else None
        return hint

    def _ref(self, hint: Any) -> Optional[str]:
        hint = self._unwrap(hint)
        return hint.__name__ if isinstance(hint, type) and dataclasses.is_dataclass(hint) else None

    def _element(self, hint: Any) -> Optional[str]:
        hint = self._unwrap(hint)
        if typing.get_origin(hint) is not tuple:
            return None
        args = [arg for arg in typing.get_args(hint) if arg is not Ellipsis]
        if args and isinstance(args[0], type) and dataclasses.is_dataclass(args[0]):
            return args[0].__name__

        def leaves(t: Any):
            if typing.get_origin(t) is tuple:
                for arg in typing.get_args(t):
                    if arg is not Ellipsis:
                        yield from leaves(arg)
            else:
                yield t

        found = list(leaves(hint))
        return "scalar" if found and all(t in (int, str, bool, float) for t in found) else None


@dataclasses.dataclass(frozen=True)
class _Unit:
    module: str
    owner: Optional[str]
    function: ast.FunctionDef

    @property
    def key(self) -> Tuple[str, Optional[str], str]:
        return (self.module, self.owner, self.function.name)


class _Module:
    def __init__(self, name: str, tree: ast.Module, ref_module_names: Set[str]):
        self.name = name
        self.tree = tree
        self.functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
        self.methods: Dict[Tuple[str, str], ast.FunctionDef] = {}
        self.record_classes: List[ast.ClassDef] = []
        for node in tree.body:
            if isinstance(node, ast.ClassDef) and _decorated(node, {"runtime_ref_record"}):
                self.record_classes.append(node)
                for item in node.body:
                    if isinstance(item, ast.FunctionDef):
                        self.methods[(node.name, item.name)] = item
        #: import した ref module の関数: 名前 → (module, 名前)
        self.imports: Dict[str, Tuple[str, str]] = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.module in ref_module_names:
                for alias in node.names:
                    self.imports[alias.asname or alias.name] = (node.module, alias.name)
        self.constants: Dict[str, str] = {}
        for node in tree.body:
            if isinstance(node, ast.Assign) and all(isinstance(t, ast.Name) for t in node.targets):
                state = _literal_state(node.value)
                if state is not None:
                    for target in node.targets:
                        self.constants[target.id] = state


def _literal_state(value: ast.AST) -> Optional[str]:
    if isinstance(value, ast.Constant):
        return CLEAN
    if isinstance(value, (ast.Set, ast.Tuple, ast.List)) and all(_literal_state(x) for x in value.elts):
        return CLEAN_CONTAINER
    if (
        isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
        and value.func.id in ("frozenset", "tuple", "set") and all(_literal_state(x) for x in value.args)
    ):
        return CLEAN_CONTAINER
    return None


class ConstructionGuard:
    """構築の経路の消費を検査する（`violations()` が違反の一覧）。"""

    def __init__(self, sources: Dict[str, str], world: RefWorld):
        self.world = world
        names = set(sources)
        self.modules = {name: _Module(name, ast.parse(text), names) for name, text in sources.items()}
        self._violations: List[str] = []
        self._reached: List[str] = []
        self._run()

    @classmethod
    def for_package(cls) -> "ConstructionGuard":
        paths = sorted((PACKAGE / "core" / "runtime_refs").glob("*.py")) + [PACKAGE / "core" / "call_target.py"]
        sources = {}
        modules = []
        for path in paths:
            relative = path.relative_to(PACKAGE.parents[1]).with_suffix("")
            name = ".".join(relative.parts)
            if name.endswith(".__init__"):
                continue
            sources[name] = path.read_text()
            modules.append(importlib.import_module(name))
        return cls(sources, RefWorld(modules))

    def ref_producing_functions(self) -> List[str]:
        """引数を持ち、ref を（推移的に）作る公開の関数・method（入口でなければならない）。

        「作る」: ref の class・`cls` の呼び出し、`replace`、ref の class の classmethod / staticmethod の呼び出し、
        またはそれらをする同じ module の関数・自分の method・import した ref module の関数の呼び出し。
        """

        units: Dict[Tuple[str, Optional[str], str], ast.FunctionDef] = {}
        for module in self.modules.values():
            for name, function in module.functions.items():
                units[(module.name, None, name)] = function
            for (owner, name), function in module.methods.items():
                units[(module.name, owner, name)] = function
        builds = {key: False for key in units}

        def direct(function: ast.FunctionDef) -> bool:
            for node in ast.walk(function):
                if isinstance(node, ast.Call):
                    callee = node.func
                    if isinstance(callee, ast.Name) and (callee.id in self.world.classes or callee.id in ("replace", "cls")):
                        return True
                    if isinstance(callee, ast.Attribute) and isinstance(callee.value, ast.Name) and (
                        callee.value.id in self.world.classes or callee.value.id == "cls"
                    ):
                        return True
            return False

        changed = True
        while changed:
            changed = False
            for (module_name, owner, name), function in units.items():
                if builds[(module_name, owner, name)]:
                    continue
                result = direct(function)
                module = self.modules[module_name]
                for node in ast.walk(function):
                    if result or not isinstance(node, ast.Call):
                        continue
                    callee = node.func
                    if isinstance(callee, ast.Name):
                        target = self._resolve(module, callee.id)
                        result = target is not None and builds.get(target.key, False)
                    elif isinstance(callee, ast.Attribute) and isinstance(callee.value, ast.Name) and callee.value.id in ("self", "cls"):
                        result = builds.get((module_name, owner, callee.attr), False)
                if result:
                    builds[(module_name, owner, name)] = True
                    changed = True
        out = []
        for (module_name, owner, name), function in units.items():
            params = [a.arg for a in function.args.posonlyargs + function.args.args + function.args.kwonlyargs if a.arg not in ("self", "cls")]
            if builds[(module_name, owner, name)] and params and not name.startswith("_"):
                out.append(f"{module_name.rsplit('.', 1)[-1]}:{owner}.{name}")
        return sorted(out)

    def violations(self) -> List[str]:
        """違反（`ACCEPTED` に理由つきで載せたものを除く）。"""

        return [v for v in self._violations if v.rsplit(" (line ", 1)[0] not in ACCEPTED]

    def accepted(self) -> List[str]:
        return [v for v in self._violations if v.rsplit(" (line ", 1)[0] in ACCEPTED]

    def reached(self) -> List[str]:
        return list(self._reached)

    # -- 起点と到達 -------------------------------------------------------------------------------

    def _seeds(self) -> List[Tuple[_Unit, str]]:
        seeds = []
        for module in self.modules.values():
            for node in module.record_classes:
                for item in node.body:
                    if not isinstance(item, ast.FunctionDef):
                        continue
                    unit = _Unit(module.name, node.name, item)
                    factory = _decorated(item, {"classmethod", "staticmethod"})
                    if item.name == "__post_init__":
                        seeds.append((unit, "construct"))
                    elif item.name == "__init__" or factory:
                        seeds.append((unit, "construct_entry"))
                    elif _decorated(item, {"runtime_ref_entry"}):
                        seeds.append((unit, "entry"))
            for function in module.functions.values():
                if _decorated(function, {"runtime_ref_entry"}):
                    seeds.append((_Unit(module.name, None, function), "entry"))
        return seeds

    def _resolve(self, module: _Module, name: str) -> Optional[_Unit]:
        if name in module.functions:
            return _Unit(module.name, None, module.functions[name])
        target = module.imports.get(name)
        if target is not None and target[0] in self.modules and target[1] in self.modules[target[0]].functions:
            other = self.modules[target[0]]
            return _Unit(other.name, None, other.functions[target[1]])
        return None

    def _run(self) -> None:
        seeds = self._seeds()
        roles = {unit.key: role for unit, role in seeds}
        order: List[Tuple[_Unit, str]] = []
        seen: Set[Tuple[str, Optional[str], str]] = set()
        pending = list(seeds)
        while pending:
            unit, role = pending.pop(0)
            if unit.key in seen:
                continue
            seen.add(unit.key)
            order.append((unit, role))
            module = self.modules[unit.module]
            for node in ast.walk(unit.function):
                if not isinstance(node, ast.Call):
                    continue
                callee = node.func
                target = None
                if isinstance(callee, ast.Name):
                    target = self._resolve(module, callee.id)
                elif (
                    role in ("construct", "construct_entry") and isinstance(callee, ast.Attribute)
                    and isinstance(callee.value, ast.Name) and callee.value.id in ("self", "cls")
                    and (unit.owner, callee.attr) in module.methods
                ):
                    target = _Unit(module.name, unit.owner, module.methods[(unit.owner, callee.attr)])
                if target is not None and target.key not in roles:
                    pending.append((target, "helper"))
                    roles[target.key] = "helper"
        # 引数の状態の fixpoint（楽観的に clean から始め、呼び出し元の実引数の meet へ下げる）
        params: Dict[Tuple[str, Optional[str], str], Dict[str, str]] = {}
        for unit, role in order:
            if role == "helper":
                params[unit.key] = {name: CLEAN for name in _parameter_names(unit.function)}
        for _ in range(20):
            calls: Dict[Tuple[str, Optional[str], str], List[Tuple[Dict[int, str], Dict[str, str]]]] = {}
            for unit, role in order:
                _FunctionCheck(self, unit, role, params.get(unit.key, {}), calls, report=None).run()
            new = {key: _meet_parameters(self._unit_of(key), calls.get(key, [])) for key in params}
            if new == params:
                break
            params = new
        report: List[str] = []
        for unit, role in order:
            _FunctionCheck(self, unit, role, params.get(unit.key, {}), {}, report=report).run()
            self._reached.append(f"{unit.module.rsplit('.', 1)[-1]}:{unit.owner}.{unit.function.name}")
        self._violations = sorted(set(report))

    def _unit_of(self, key: Tuple[str, Optional[str], str]) -> _Unit:
        module = self.modules[key[0]]
        function = module.functions[key[2]] if key[1] is None else module.methods[(key[1], key[2])]
        return _Unit(key[0], key[1], function)


def _parameter_names(function: ast.FunctionDef) -> List[str]:
    args = function.args.posonlyargs + function.args.args + function.args.kwonlyargs
    return [a.arg for a in args if a.arg not in ("self", "cls")]


def _meet_parameters(unit: _Unit, calls: List[Tuple[Dict[int, str], Dict[str, str]]]) -> Dict[str, str]:
    args = unit.function.args.posonlyargs + unit.function.args.args + unit.function.args.kwonlyargs
    if args and args[0].arg in ("self", "cls"):
        args = args[1:]
    states = {}
    for index, arg in enumerate(args):
        seen = []
        for positional, keywords in calls:
            if index in positional:
                seen.append(positional[index])
            elif arg.arg in keywords:
                seen.append(keywords[arg.arg])
        if not seen:
            continue
        kinds = set(seen)
        if kinds == {CLEAN}:
            states[arg.arg] = CLEAN
        elif kinds <= {CLEAN_CONTAINER}:
            states[arg.arg] = CLEAN_CONTAINER
        elif len(kinds) == 1 and next(iter(kinds)).startswith(("ref:", "elem:")) and "?" not in next(iter(kinds)):
            states[arg.arg] = next(iter(kinds))
    return states


class _FunctionCheck:
    def __init__(self, guard: ConstructionGuard, unit: _Unit, role: str, params: Dict[str, str],
                 calls: Dict[Any, List[Any]], report: Optional[List[str]]):
        self.guard, self.unit, self.role, self.params = guard, unit, role, params
        self.module = guard.modules[unit.module]
        self.world = guard.world
        self.calls = calls
        self.report = report
        self.construction = role in ("construct", "construct_entry") and unit.function.name in ("__post_init__", "__init__")
        self.local_functions: Set[str] = set()

    # -- 入口 ---------------------------------------------------------------------------------------

    def run(self) -> None:
        env: Dict[str, str] = {}
        function = self.unit.function
        args = function.args.posonlyargs + function.args.args + function.args.kwonlyargs
        entry = self.role in ("entry", "construct_entry") and (
            _decorated(function, {"runtime_ref_entry"}) or function.name == "__init__"
        )
        for index, arg in enumerate(args):
            if index == 0 and arg.arg == "self" and self.unit.owner:
                env["self"] = f"ref:{self.unit.owner}"
            elif index == 0 and arg.arg == "cls" and self.unit.owner:
                env["cls"] = f"class:{self.unit.owner}"
            elif arg.arg in self.params:
                env[arg.arg] = self.params[arg.arg]
            else:
                env[arg.arg] = self._annotation_state(arg.annotation, normalized=entry)
        self._block(function.body, env)

    def _annotation_state(self, annotation: Optional[ast.AST], *, normalized: bool) -> str:
        if annotation is None:
            return UNKNOWN
        text = ast.unparse(annotation).replace('"', "").replace("'", "").replace(" ", "")
        bare = text[len("Optional["):-1] if text.startswith("Optional[") else text
        if bare.endswith("|None"):
            bare = bare[: -len("|None")]
        if bare in self.world.classes:
            return f"ref:{bare}"
        if not normalized:
            return UNKNOWN
        # `runtime_ref_entry` が写した引数（owner の分類と同じ: scalar / bool / tuple）
        if bare in ("int", "str", "bool", "float"):
            return CLEAN
        for name in self.world.classes:
            if bare in (f"Tuple[{name},...]", f"tuple[{name},...]"):
                return f"elem:{name}"
        if bare.startswith(("Tuple[", "tuple[")) or bare in ("Tuple", "tuple"):
            return CLEAN_CONTAINER
        return UNKNOWN

    def flag(self, node: ast.AST, what: str) -> None:
        if self.report is not None:
            key = f"{self.unit.module.rsplit('.', 1)[-1]}.py:{self.unit.function.name}: {what}: {ast.unparse(node)[:100]}"
            self.report.append(f"{key} (line {node.lineno})")

    # -- 値の状態 -----------------------------------------------------------------------------------

    def state(self, e: ast.AST, env: Dict[str, str]) -> str:
        if isinstance(e, ast.Constant):
            return CLEAN
        if isinstance(e, ast.Name):
            if e.id in env:
                return env[e.id]
            if e.id in self.world.classes:
                return f"class:{e.id}"
            if e.id in self.module.constants:
                return self.module.constants[e.id]
            return UNKNOWN
        if isinstance(e, ast.Attribute):
            on_self = isinstance(e.value, ast.Name) and e.value.id == "self"
            return self._attribute(self.state(e.value, env), e.attr, env, on_self)
        if isinstance(e, (ast.Tuple, ast.List, ast.Set)):
            states = [self.state(x, env) for x in e.elts]
            return CLEAN_CONTAINER if all(_element_ok(s) for s in states) else CONTAINER
        if isinstance(e, ast.Dict):
            return CLEAN_CONTAINER
        if isinstance(e, ast.Compare):
            return CLEAN
        if isinstance(e, ast.UnaryOp):
            return CLEAN if isinstance(e.op, ast.Not) or self.state(e.operand, env) == CLEAN else UNKNOWN
        if isinstance(e, ast.BoolOp):
            states = [self.state(x, env) for x in e.values]
            if all(s == CLEAN for s in states):
                return CLEAN
            typed = {s for s in states if s != CLEAN_CONTAINER}
            if not typed:
                return CLEAN_CONTAINER
            return typed.pop() if len(typed) == 1 else UNKNOWN
        if isinstance(e, ast.BinOp):
            ok = all(self.state(x, env) in (CLEAN, CLEAN_CONTAINER) for x in (e.left, e.right))
            return CLEAN if ok else UNKNOWN
        if isinstance(e, ast.IfExp):
            a, b = self.state(e.body, env), self.state(e.orelse, env)
            return a if a == b else UNKNOWN
        if isinstance(e, ast.JoinedStr):
            return CLEAN
        if isinstance(e, ast.Subscript):
            base = self.state(e.value, env)
            if isinstance(e.slice, ast.Slice):
                return base if base in (CLEAN_CONTAINER, CONTAINER) or base.startswith("elem:") else UNKNOWN
            if base in (CLEAN, CLEAN_CONTAINER):
                return CLEAN
            return f"ref:{base[5:]}" if base.startswith("elem:") and base[5:] != "scalar" else UNKNOWN
        if isinstance(e, (ast.ListComp, ast.GeneratorExp, ast.SetComp)):
            inner = self._comprehension_env(e, env, check=False)
            element = self.state(e.elt, inner)
            if element.startswith("ref:") and element != "ref:?":
                return f"elem:{element[4:]}"  # ref の容器（要素の属性の読みを追う）
            return CLEAN_CONTAINER if _element_ok(element) else CONTAINER
        if isinstance(e, ast.DictComp):
            return CLEAN_CONTAINER
        if isinstance(e, ast.Call):
            return self._call(e, env)
        if isinstance(e, ast.Lambda):
            return CLEAN
        if isinstance(e, ast.Starred):
            return self.state(e.value, env)
        return UNKNOWN

    def _attribute(self, base: str, name: str, env: Dict[str, str], on_self: bool) -> str:
        if on_self and self.construction and f"self.{name}" in env:
            return env[f"self.{name}"]
        if base.startswith("ref:") and not on_self:
            # 他の object の属性: 注釈が ref の class でも、実際の値は代わりの型（duck typing）や外の object
            # かもしれない（dataclass の field の型は実行時に確かめられない）。owner が写したと言えるのは
            # 自分の field だけ。ref の field を指す属性の値（ref:…）は辿ってよいが、scalar は reader で読む
            fields = self.world.classes.get(base[4:], {})
            info = fields.get(name)
            if info is not None and info.ref:
                return f"ref:{info.ref}"
            if info is not None and info.kind == "tuple" and info.element and info.element != "scalar":
                return f"elem:{info.element}"
            return UNKNOWN if info is not None and info.kind != "tuple" else (CONTAINER if info is not None else f"method:{base[4:]}")
        if base.startswith("ref:"):
            fields = self.world.classes.get(base[4:], {})
            info = fields.get(name)
            if info is None:
                return f"method:{base[4:]}"  # method / property: 結果は ref の code が作る（信用する）
            if info.ref:
                return f"ref:{info.ref}"
            if info.kind in ("scalar", "bool"):
                return CLEAN
            if info.kind == "tuple":
                if info.element and info.element != "scalar":
                    return f"elem:{info.element}"
                # 要素は未確認: list のまま受理した値は owner が写さない（exact な tuple だけを写す）
                return CONTAINER
            return UNKNOWN
        if base.startswith("class:"):
            return f"classattr:{base[6:]}"
        return UNKNOWN

    def _call(self, call: ast.Call, env: Dict[str, str]) -> str:
        callee = call.func
        name = callee.id if isinstance(callee, ast.Name) else callee.attr if isinstance(callee, ast.Attribute) else ""
        base = self.state(callee.value, env) if isinstance(callee, ast.Attribute) else ""
        through_owner = isinstance(callee, ast.Name) or (
            isinstance(callee, ast.Attribute) and isinstance(callee.value, ast.Name) and callee.value.id == "live_values"
        )
        if through_owner and (name in READERS or name in CONTAINER_READERS):
            return CONTAINER if name in CONTAINER_READERS else CLEAN
        if isinstance(callee, ast.Name) and name in SAFE_ANY:
            return CLEAN
        if isinstance(callee, ast.Name) and (name in self.world.classes or name == "cls"):
            return f"ref:{name}" if name != "cls" else f"ref:{self.unit.owner}"
        if base.startswith(("class:", "classattr:")):
            return "ref:?"
        if isinstance(callee, ast.Name) and name == "getattr" and len(call.args) >= 2 and isinstance(call.args[1], ast.Constant):
            target = call.args[0]
            on_self = isinstance(target, ast.Name) and target.id == "self"
            found = self._attribute(self.state(target, env), call.args[1].value, env, on_self)
            if len(call.args) == 3 and found == CLEAN and self.state(call.args[2], env) != CLEAN:
                return UNKNOWN
            return found
        if isinstance(callee, ast.Name) and name == "len":
            return CLEAN
        if isinstance(callee, ast.Attribute) and isinstance(callee.value, ast.Name) and callee.value.id in BUILTIN_TYPES:
            return CLEAN  # 基底型の slot の実装（subclass の上書きを呼ばない）
        if isinstance(callee, ast.Name) and name == "next" and call.args:
            return self._element_of(self.state(call.args[0], env))
        if isinstance(callee, ast.Name) and name in CONTAINER_BUILTINS:
            inner = [self.state(a, env) for a in call.args]
            if len(inner) == 1 and (inner[0].startswith("elem:") or inner[0] == CLEAN_CONTAINER):
                return inner[0]
            return CLEAN_CONTAINER if all(_element_ok(s) for s in inner) else CONTAINER
        if isinstance(callee, ast.Name) and name in CONSUMING_BUILTINS:
            inner = [self.state(a, env) for a in call.args]
            if all(_element_ok(s) or s == CLEAN_CONTAINER for s in inner):
                return CLEAN_CONTAINER if name in ("sorted", "set", "frozenset", "dict") else CLEAN
            return UNKNOWN
        if base in (CLEAN, CLEAN_CONTAINER):
            return CLEAN  # clean な値（組み込みの値）の method
        if base.startswith(("ref:", "method:")) or (isinstance(callee, ast.Name) and env.get(name, "").startswith("method:")):
            # ref の method の結果（信用する: その ref の field は owner と自分の検証が写した値。注釈が Any の
            # field を scalar として結果に含める ref は、自分の検証でその field の読み方を決める）
            return CLEAN
        if isinstance(callee, ast.Name) and (self.guard._resolve(self.module, name) is not None or name in self.local_functions):
            return CLEAN  # ref module の関数（それ自身が検査される）
        return UNKNOWN  # API の戻り値・注入された callable の戻り値

    def _consumable(self, state: str) -> bool:
        return state in (CLEAN, CLEAN_CONTAINER) or state.startswith(("ref:", "class"))

    # -- 文 -----------------------------------------------------------------------------------------

    def _block(self, body: List[ast.stmt], env: Dict[str, str]) -> None:
        for statement in body:
            self._statement(statement, env)

    @staticmethod
    def _ends(body: List[ast.stmt]) -> bool:
        return bool(body) and isinstance(body[-1], (ast.Return, ast.Raise, ast.Continue, ast.Break))

    @staticmethod
    def _merge(env: Dict[str, str], *branches: Dict[str, str]) -> None:
        for name in set().union(*branches):
            states = {branch.get(name, "absent") for branch in branches} - {"absent"}
            if len(states) == 1:
                env[name] = states.pop()
            elif all(s in (CONTAINER, CLEAN_CONTAINER) or s.startswith("elem:") for s in states):
                env[name] = CONTAINER  # どれも組み込みの容器（要素は未確認）
            else:
                env[name] = UNKNOWN

    def _narrowed(self, test: ast.AST, env: Dict[str, str]) -> Dict[str, str]:
        out = dict(env)
        tests = test.values if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And) else [test]
        for t in tests:
            if (
                isinstance(t, ast.Call) and isinstance(t.func, ast.Name) and t.func.id == "isinstance"
                and len(t.args) == 2 and isinstance(t.args[0], ast.Name)
            ):
                kinds = t.args[1].elts if isinstance(t.args[1], ast.Tuple) else [t.args[1]]
                names = [k.id for k in kinds if isinstance(k, ast.Name)]
                if len(names) == 1 and names[0] in self.world.classes:
                    out[t.args[0].id] = f"ref:{names[0]}"
                elif names and set(names) == {"bool"}:
                    out[t.args[0].id] = CLEAN  # bool は subclass を作れない
        return out

    def _bind(self, target: ast.AST, state: str, env: Dict[str, str]) -> None:
        if isinstance(target, ast.Name):
            env[target.id] = state
        elif isinstance(target, (ast.Tuple, ast.List)):
            inner = CLEAN if state in (CLEAN, CLEAN_CONTAINER) else UNKNOWN
            for item in target.elts:
                self._bind(item, inner, env)

    def _element_of(self, state: str) -> str:
        if state == CLEAN_CONTAINER:
            return CLEAN
        if state.startswith("elem:") and state[5:] != "scalar":
            return f"ref:{state[5:]}"
        return UNKNOWN

    def _statement(self, s: ast.stmt, env: Dict[str, str]) -> None:
        if isinstance(s, ast.Assign):
            self._expr(s.value, env)
            state = self.state(s.value, env)
            for target in s.targets:
                self._bind(target, state, env)
        elif isinstance(s, ast.AnnAssign):
            if s.value is not None:
                self._expr(s.value, env)
                self._bind(s.target, self.state(s.value, env), env)
        elif isinstance(s, ast.AugAssign):
            if self.state(s.target, env) != CLEAN or self.state(s.value, env) != CLEAN:
                self.flag(s, "arithmetic")
            self._expr(s.value, env)
        elif isinstance(s, (ast.If, ast.While)):
            self._test(s.test, env)
            body_env, else_env = self._narrowed(s.test, env), dict(env)
            self._block(s.body, body_env)
            if isinstance(s, ast.While):
                self._block(s.body, body_env)
            self._block(s.orelse, else_env)
            live = [b for b, body in ((body_env, s.body), (else_env, s.orelse)) if not self._ends(body)]
            if live:
                self._merge(env, *live)
        elif isinstance(s, ast.For):
            self._expr(s.iter, env)
            loop_env = dict(env)
            element = self._element_of(self.state(s.iter, env))
            self._bind(s.target, element if isinstance(s.target, ast.Name) else (CLEAN_CONTAINER if element == CLEAN else UNKNOWN), loop_env)
            self._block(s.body, loop_env)
            self._block(s.body, loop_env)
            else_env = dict(env)
            self._block(s.orelse, else_env)
            self._merge(env, env, loop_env, else_env)
        elif isinstance(s, ast.Try):
            body_env = dict(env)
            self._block(s.body, body_env)
            self._block(s.orelse, body_env)
            branches = [body_env]
            for handler in s.handlers:
                handler_env = dict(env)
                self._merge(handler_env, env, body_env)
                if handler.name:
                    handler_env[handler.name] = UNKNOWN
                self._block(handler.body, handler_env)
                if not self._ends(handler.body):
                    branches.append(handler_env)
            self._merge(env, *branches)
            self._block(s.finalbody, env)
        elif isinstance(s, (ast.Return, ast.Expr)):
            if s.value is not None:
                self._expr(s.value, env)
                value = s.value
                if (
                    isinstance(s, ast.Expr) and isinstance(value, ast.Call)
                    and ast.unparse(value.func) == "object.__setattr__" and len(value.args) == 3
                    and isinstance(value.args[0], ast.Name) and value.args[0].id == "self"
                    and isinstance(value.args[1], ast.Constant)
                ):
                    # 検証が写し直した field（以後の `self.<field>` の読みはこの状態）
                    env[f"self.{value.args[1].value}"] = self.state(value.args[2], env)
        elif isinstance(s, ast.Raise):
            if s.exc is not None:
                self._expr(s.exc, env)
        elif isinstance(s, ast.Assert):
            self._test(s.test, env)
        elif isinstance(s, ast.With):
            self._block(s.body, env)
        elif isinstance(s, ast.FunctionDef):
            # 入れ子の関数: 引数は未確認として本体を検査する。呼び出しの結果は信用する
            self.local_functions.add(s.name)
            inner = dict(env)
            for arg in s.args.posonlyargs + s.args.args + s.args.kwonlyargs:
                inner[arg.arg] = UNKNOWN
            self._block(s.body, inner)

    def _test(self, e: ast.AST, env: Dict[str, str]) -> None:
        if isinstance(e, ast.BoolOp):
            scope = env
            for value in e.values:
                self._test(value, scope)
                if isinstance(e.op, ast.And):
                    scope = self._narrowed(value, scope)  # `isinstance(x, bool) and x`: 右は絞った値を読む
            return
        if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.Not):
            self._test(e.operand, env)
            return
        state = self.state(e, env)
        if not (self._consumable(state) or state == CONTAINER or state.startswith(("elem:", "method:"))):
            self.flag(e, f"truthiness of {state}")
        self._expr(e, env)

    def _record_call(self, call: ast.Call, env: Dict[str, str]) -> None:
        callee = call.func
        target = None
        if isinstance(callee, ast.Name):
            target = self.guard._resolve(self.module, callee.id)
        elif (
            isinstance(callee, ast.Attribute) and isinstance(callee.value, ast.Name)
            and callee.value.id in ("self", "cls") and (self.unit.owner, callee.attr) in self.module.methods
        ):
            target = _Unit(self.module.name, self.unit.owner, self.module.methods[(self.unit.owner, callee.attr)])
        if target is not None:
            self.calls.setdefault(target.key, []).append((
                {index: self.state(a, env) for index, a in enumerate(call.args)},
                {k.arg: self.state(k.value, env) for k in call.keywords if k.arg},
            ))

    def _comprehension_env(self, e: Any, env: Dict[str, str], *, check: bool) -> Dict[str, str]:
        inner = dict(env)
        for generator in e.generators:
            if check:
                self._expr(generator.iter, inner)
            element = self._element_of(self.state(generator.iter, inner))
            if isinstance(generator.target, ast.Name):
                inner[generator.target.id] = element
            else:
                for node in ast.walk(generator.target):
                    if isinstance(node, ast.Name):
                        inner[node.id] = CLEAN if element == CLEAN else UNKNOWN
            if check:
                for condition in generator.ifs:
                    self._test(condition, inner)
        return inner

    def _expr(self, e: ast.AST, env: Dict[str, str]) -> None:
        if isinstance(e, ast.BoolOp):
            for value in e.values[:-1]:
                self._test(value, env)
            self._expr(e.values[-1], env)
        elif isinstance(e, ast.UnaryOp):
            if isinstance(e.op, ast.Not):
                self._test(e.operand, env)
            else:
                if self.state(e.operand, env) != CLEAN:
                    self.flag(e, "arithmetic")
                self._expr(e.operand, env)
        elif isinstance(e, ast.IfExp):
            self._test(e.test, env)
            self._expr(e.body, env)
            self._expr(e.orelse, env)
        elif isinstance(e, ast.Compare):
            if not all(isinstance(op, (ast.Is, ast.IsNot)) for op in e.ops):
                for operand in (e.left, *e.comparators):
                    if not self._consumable(self.state(operand, env)):
                        self.flag(e, f"comparison of {self.state(operand, env)}")
                        break
            for operand in (e.left, *e.comparators):
                self._expr(operand, env)
        elif isinstance(e, ast.BinOp):
            for operand in (e.left, e.right):
                if self.state(operand, env) not in (CLEAN, CLEAN_CONTAINER):
                    self.flag(e, f"arithmetic on {self.state(operand, env)}")
                    break
            self._expr(e.left, env)
            self._expr(e.right, env)
        elif isinstance(e, ast.JoinedStr):
            for value in e.values:
                if isinstance(value, ast.FormattedValue):
                    if not self._consumable(self.state(value.value, env)):
                        self.flag(value, "format")
                    self._expr(value.value, env)
        elif isinstance(e, (ast.Set, ast.Dict)):
            keys = e.elts if isinstance(e, ast.Set) else [k for k in e.keys if k is not None]
            if any(not self._consumable(self.state(k, env)) for k in keys):
                self.flag(e, "hash")
            for item in (e.elts if isinstance(e, ast.Set) else [*keys, *e.values]):
                self._expr(item, env)
        elif isinstance(e, (ast.ListComp, ast.GeneratorExp, ast.SetComp, ast.DictComp)):
            inner = self._comprehension_env(e, env, check=True)
            if isinstance(e, ast.SetComp) and not self._consumable(self.state(e.elt, inner)):
                self.flag(e, "hash")
            if isinstance(e, ast.DictComp):
                if not self._consumable(self.state(e.key, inner)):
                    self.flag(e, "hash")
                self._expr(e.key, inner)
                self._expr(e.value, inner)
            else:
                self._expr(e.elt, inner)
        elif isinstance(e, ast.Call):
            callee = e.func
            name = callee.id if isinstance(callee, ast.Name) else ""
            states = [self.state(a, env) for a in e.args]
            if name in CONSUMING_BUILTINS:
                keyed = any(k.arg == "key" for k in e.keywords) and name in ("sorted", "min", "max")
                for state in states:
                    if not self._consumable(state) and not keyed and not (
                        name in ("bool", "any", "all") and (state == CONTAINER or state.startswith("elem:"))
                    ):
                        self.flag(e, f"{name}() of {state}")
                        break
            builtin_slot = isinstance(callee, ast.Attribute) and isinstance(callee.value, ast.Name) and callee.value.id in BUILTIN_TYPES
            if isinstance(callee, ast.Attribute) and callee.attr in SCALAR_METHODS and not builtin_slot:
                base = self.state(callee.value, env)
                if not self._consumable(base):
                    self.flag(e, f"method {callee.attr}() on {base}")
            self._record_call(e, env)
            if isinstance(callee, ast.Attribute):
                self._expr(callee.value, env)
            for a in e.args:
                self._expr(a, env)
            for k in e.keywords:
                if isinstance(k.value, ast.Lambda):
                    # `sorted(..., key=lambda x: ...)` など: 引数は未確認（要素の状態は追わない）として本体を検査する
                    inner = dict(env)
                    element = self._element_of(states[0]) if states else UNKNOWN
                    for arg in k.value.args.args:
                        inner[arg.arg] = element
                    self._expr(k.value.body, inner)
                else:
                    self._expr(k.value, env)
        elif isinstance(e, ast.Subscript):
            self._expr(e.value, env)
            self._expr(e.slice, env)
        elif isinstance(e, ast.Attribute):
            self._expr(e.value, env)
        elif isinstance(e, (ast.Tuple, ast.List)):
            for item in e.elts:
                self._expr(item, env)
        elif isinstance(e, ast.Starred):
            self._expr(e.value, env)


def _element_ok(state: str) -> bool:
    return state in (CLEAN, CLEAN_CONTAINER) or state.startswith("ref:")


#: 構文から安全と言えないが、scalar の契約の外として受理する消費（理由つき。field / 引数の scalar ではない）
ACCEPTED: Dict[str, str] = {
    "pcode.py:_local_op_ordinal_from_parent: comparison of unknown: candidate == pcode_op":
        "Ghidra の PcodeOp object どうしの等しさ（Java の equals）。scalar ではなく、ref の field にも入らない",
}
