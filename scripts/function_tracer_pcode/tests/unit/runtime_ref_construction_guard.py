# -*- coding: utf-8 -*-
"""runtime ref の構築の経路が、外の値を **安全な読み方でだけ** 消費することを確かめる静的な解析（Issue #242）。

構築の契約: ref の構築（`__post_init__`・自前の `__init__`・factory と `@runtime_ref_entry` の入口）と、ref module の
**外から呼べるすべての** 関数・method・property（公開の名前と、外の module が import する `_` の名前。引数の有無、
ref の class かどうかに依らない）、およびそこから **実際に到達する** 関数は、scalar の subclass の code
（`__bool__` / `__eq__` / `__hash__` / `__format__` / `__str__` / 算術 / 文字列の method / `__int__` / `__len__` /
`__iter__` など）を呼ばない。外の値は消費の前に `live_values` などの reader（import した名前だけを信用する）で読む。

**値の状態**（文字列で表す）:

- `clean`: 組み込みの値、または葉まで組み込みの値の容器（定数、`scalar_*` / `exact_tree` の結果、owner が写した
  scalar の field、写した引数、比較や `not` の結果）
- `leaf`: 葉だけを写した値（`exact_scalar` / `exact_field_value` の結果）。scalar の subclass ではないが、容器なら
  中の葉は未確認。真偽・scalar の定数との比較（と定数の tuple / list への `in`）・数への変換・反復はよい。
  文字列化・hash・定数でない値との比較は違反
- `scalar?`: `isinstance(x, str)` などで絞った値（subclass かもしれない）。葉の reader で読むと clean
- `seq:<要素>` / `tup:[位置ごと]` / `map:[key, 値]`: 組み込みの容器（真偽・長さ・反復・連結は要素の code を呼ばない）
- `ref:C`: ref の class C の本物の instance（`self`、構築の結果、`type(x) is C` で絞った値）。field は構築を終えた
  後の値（scalar / bool は owner が写した値、検証が書き直した field は書き直した値の状態）。method は本体を辿る
- `nref:C`: `isinstance(x, C)` で絞った値（C か C の subclass の instance）。field は `ref:C` と同じ、method は
  subclass が上書きし得るので本体（C の code）を検査し、結果は未確認
- `typed:C`: 注釈が C なだけの値（代わりの型かもしれない）。scalar の属性は未確認、tuple の field は `uncertain:`
  （容器かどうかも未確認: reader で読むと容器）、method / property は本体を検査するが結果は未確認
- `obj:C`: ref でない class（`ExpansionBudgetCollector` など）の instance。`__init__` で組み込みの容器を置いた属性は
  容器（要素はその class の method が入れた値の meet）、それ以外の属性は未確認
- `unknown`: 上のどれでもない（消費すると違反）

**消費として数えるもの**: 真偽、`is` 以外の比較・`in`・`match`、算術・累算代入、f-string・`str` / `repr` /
`format` / `"...".format()` / `json.dumps`、`*x` / `**x` の展開、set / dict の `add` / `get` / `setdefault` の key、集合・dict の key（hash）、文字列・整数の method、組み込みの変換・集計、`sorted` / `min` / `max` /
`list.sort` が比べる値（`key=` の結果を含む）、`len` / `tuple` / `list` / 反復 / 組への代入（`__len__` / `__iter__`）、
ref の `==` / hash（比べる field に未確認の値を持ち得る class）。

**到達**: 同じ module の関数、import した ref module の関数、入れ子の関数、別の呼び出しの引数の中の呼び出し、
`self.m()` / `cls.m()` / `C.m()`、`ref:C` / `typed:C` / `obj:C` の値の method と property。戻り値の状態は本体の
`return` / `yield` の meet、引数の状態は呼び出し元の実引数（と既定値）の meet（fixpoint）。外から呼べる関数の
引数は注釈の状態（入口なら写した後の状態）から始める。制御の流れは分岐ごとに追い、`continue` / `break` の状態は
繰り返しの先頭とループの後へ流す（`return` / `raise` だけが経路を終える）。

**限界**（PASS をこれ以上の保証と読まない）:

- 容器の変異は名前（と ref でない class の自分の属性）への `append` / `add` / `insert` / `extend` / `update` /
  `setdefault` / 添字の代入だけを追う（別名を通した変異・関数に渡した容器の変異は追わない）。`getattr` は定数の
  名前だけを追い、`setattr` / `exec` / 動的な名前は追わない。
- method は `self` が C の instance のときの C の code として検査し、`self.m()` は C の `m` を辿る（package の外で
  ref の class を継承して `self` から呼ぶ method を上書きする使い方と、`C.method(代わりの型)` のように class から
  外の object を渡して呼ぶ使い方は対象外）。`ref:C` の field は構築のときの値として扱う（後から
  `object.__setattr__` で書き換えた値は追わない）。
- `exact_tree` の結果は clean として扱う: 辿らない値は scalar でも組み込みの容器（subclass・`deque` を含む）でも
  ない object（外の code）だけ。
- 外の object の method の中の code（外の code）は検査しない。その結果は未確認として扱い、消費する前に reader で
  読ませる（消費せずに返す・field に置くだけの値は対象外: 注釈が Any の位置と同じく、受け取った側が読む）。
  `scalar_text` / `str()` は外の object の `__str__` を呼ぶ（組み込みの容器と例外の引数は reader が葉を写す）。
- 呼び出し元の層（analysis など）が入口に渡す前の加工はこの解析の外。
- 振る舞いは `test_issue242_entry_matrix.py` の行列（入口 × 呼び出しの形 × 受け手 × 入力の形）が実行して確かめる。
"""

from __future__ import annotations

import ast
import dataclasses
import importlib
import json
import pathlib
import types
import typing
from typing import Any, Dict, Iterable, List, Optional, Set, Tuple

CLEAN = "clean"
UNKNOWN = "unknown"
BOTTOM = "bottom"  # まだ値が流れていない（fixpoint の初期値）
CLEAN_CONTAINER = "seq:clean"
#: 葉だけを写した値（`exact_scalar` の結果）: scalar の subclass ではないが、容器なら中の葉は未確認。真偽・
#: scalar の定数との `==` / 順序・数への変換はよい（容器と scalar の比較は要素を読まない）。文字列化・hash・
#: 定数でない値との比較は要素の code を呼び得る
LEAF = "leaf"
CONTAINER = "seq:unknown"

PACKAGE = pathlib.Path(__file__).resolve().parents[2]

#: reader を定義する module（ここから import した名前だけを reader として信用する）
READER_MODULES = frozenset({
    "scripts.function_tracer_pcode.core.live_values",
    "scripts.function_tracer_pcode.core.runtime_ref_record",
    "scripts.function_tracer_pcode.core.read_limits",
    "scripts.function_tracer_pcode.core.json_encoding",
})
#: `isinstance` で絞ると「scalar（subclass かもしれない）」になる型
SCALAR_TYPES = frozenset({"int", "str", "float", "bytes"})
#: scalar かもしれない値（`isinstance(x, str)` で絞った値）: 消費は未確認と同じ、葉の reader で読むと clean
MAYBE_SCALAR = "scalar?"
#: 値を clean にする reader（`live_values` / owner）
#: 葉だけを写す reader（scalar の subclass は基底型の値になるが、容器・object はそのまま: 状態 `leaf`）
LEAF_READERS = frozenset({"exact_scalar", "plain_scalar", "exact_field_value"})
READERS = frozenset({
    "scalar_int", "scalar_text", "scalar_bool", "as_bool", "as_int", "as_str", "str_value",
    "int_value", "json_scalar", "is_kind", "type_name", "type_module",
    "builtin_str", "builtin_sequence", "size", "scalar_int_or", "is_json_record",
})
#: 値を「組み込みの容器（要素は未確認）」にする reader
CONTAINER_READERS = frozenset({"builtin_items", "elements_of", "elements_within_limit"})
#: 値を「比べてよい容器」にする reader（組み込みの tuple / list を辿り、scalar の subclass の葉を基底型の値にする）
TREE_READERS = frozenset({"exact_tree"})
#: 組み込みの容器の型（`isinstance(x, tuple)` などで絞ると、反復・長さ・真偽は組み込みの振る舞い）
CONTAINER_TYPES = frozenset({"tuple", "list", "dict", "set", "frozenset", "Mapping"})
#: どの値に当てても外の型の code を呼ばない組み込み
SAFE_ANY = frozenset({"isinstance", "issubclass", "callable", "id", "type"})
#: 引数が clean なら結果も clean な組み込み（それ自体が消費: 引数が clean でなければ違反）
CONSUMING_BUILTINS = frozenset({
    "int", "str", "float", "bool", "repr", "format", "hash", "sorted", "min", "max", "sum", "abs", "round",
    "set", "frozenset", "dict", "divmod", "pow", "any", "all",
})
#: 要素を比べる / hash する組み込み（`key=` があれば key の結果を比べる）
ORDERING_BUILTINS = frozenset({"sorted", "min", "max"})
#: 容器を作り直す組み込み（要素は読まない。要素の状態を引き継ぐ）
CONTAINER_BUILTINS = frozenset({"tuple", "list", "enumerate", "zip", "reversed", "iter", "range"})
#: 組み込みの型（`bytes.hex(value)` のように型から method を引くと、基底型の slot の実装を呼ぶ）
BUILTIN_TYPES = frozenset({"int", "str", "bytes", "float", "tuple", "list", "dict", "bool", "object"})
#: scalar の値に当てると subclass の code を呼ぶ method（文字列・整数）
SCALAR_METHODS = frozenset({
    "strip", "lstrip", "rstrip", "lower", "upper", "startswith", "endswith", "split", "rsplit", "join",
    "replace", "format", "encode", "isdigit", "bit_length", "to_bytes", "hex", "casefold", "partition",
    "find", "index", "count", "zfill", "title", "capitalize", "splitlines",
})
#: 名前の容器を変異させる method（要素の状態を meet する）
MUTATORS = frozenset({"append", "add", "insert", "extend", "update", "setdefault"})


def _decorated(node: Any, names: Iterable[str]) -> bool:
    names = set(names)
    return any(
        (isinstance(d, ast.Name) and d.id in names) or (isinstance(d, ast.Attribute) and d.attr in names)
        for d in node.decorator_list
    )


def is_container(state: str) -> bool:
    return state.startswith(("seq:", "tup:", "map:"))


def make_map(key: str, value: str) -> str:
    """組み込みの dict（key と値の状態）。反復は key、`items()` は (key, 値) の組。"""

    return widen("map:" + json.dumps([CLEAN if key == BOTTOM else key, CLEAN if value == BOTTOM else value]))


def map_parts(state: str) -> Tuple[str, str]:
    key, value = json.loads(state[4:])
    return key, value


def tup_items(state: str) -> List[str]:
    return json.loads(state[4:])


def make_tup(states: List[str]) -> str:
    """位置ごとの状態を持つ tuple（tuple の literal・tuple を返す関数）。深い・長いものは `seq:` へ。"""

    if len(states) > 8:
        element = BOTTOM
        for state in states:
            element = _meet(element, state)
        return widen("seq:" + (CLEAN if element == BOTTOM else element))
    return widen("tup:" + json.dumps(states))


def as_seq(state: str) -> str:
    return "seq:" + element_of(state) if state.startswith("tup:") else state


def clean_tree(state: str) -> bool:
    """組み込みの値と、葉まで組み込みの値の容器。"""

    if state in (CLEAN, BOTTOM):
        return True
    if state.startswith("seq:"):
        return clean_tree(state[4:])
    if state.startswith("tup:"):
        return all(clean_tree(item) for item in tup_items(state))
    if state.startswith("map:"):
        return all(clean_tree(part) for part in map_parts(state))
    return False


def widen(state: str, depth: int = 3) -> str:
    """容器の入れ子を `depth` 段で打ち切る（再帰で組む key の状態を有限にする: 深い段は葉の状態で代表する）。"""

    if state.count("seq:") + state.count("tup:") + state.count("map:") <= depth:
        return state
    return "seq:" * depth + (CLEAN if clean_tree(state) else UNKNOWN)


def meet(a: str, b: str) -> str:
    """2 つの経路の状態の合流（悪い方へ寄せる）。`clean` と容器・ref の合流は容器・ref（`None` との合流）。"""

    return widen(_meet(a, b))


def _meet(a: str, b: str) -> str:
    if a == b:
        return a
    if {a, b} == {LEAF, CLEAN}:
        return LEAF
    if a == BOTTOM:
        return b
    if b == BOTTOM:
        return a
    if a == CLEAN and b.startswith(("seq:", "tup:", "map:", "ref:", "nref:", "typed:")):
        return b
    if b == CLEAN and a.startswith(("seq:", "tup:", "map:", "ref:", "nref:", "typed:")):
        return a
    if a.startswith("map:") and b.startswith("map:"):
        (ak, av), (bk, bv) = map_parts(a), map_parts(b)
        return make_map(_meet(ak, bk), _meet(av, bv))
    if a.startswith("tup:") and b.startswith("tup:"):
        left, right = tup_items(a), tup_items(b)
        if len(left) == len(right):
            return make_tup([_meet(x, y) for x, y in zip(left, right)])
    if is_container(a) and is_container(b):
        return "seq:" + _meet(element_of(a), element_of(b))
    for x, y in ((a, b), (b, a)):
        if x.startswith("ref:") and y in (f"typed:{x[4:]}", f"nref:{x[4:]}"):
            return y
        if x.startswith("nref:") and y == f"typed:{x[5:]}":
            return y
    return UNKNOWN


def element_of(state: str) -> str:
    if state.startswith("seq:"):
        return state[4:]
    if state.startswith("tup:"):
        element = BOTTOM
        for item in tup_items(state):
            element = _meet(element, item)
        return CLEAN if element == BOTTOM else element
    if state.startswith("map:"):
        return map_parts(state)[0]
    return UNKNOWN


@dataclasses.dataclass
class _FieldInfo:
    kind: str  # scalar / bool / tuple / object（owner の分類）
    ref: Optional[str]  # 注釈が ref の class ならその名前
    element: Optional[str]  # tuple の要素が ref ならその名前、葉が全部 scalar なら "scalar"
    compare: bool = True  # dataclass の `__eq__` / `__hash__` が比べる field か


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
                            _kind_of(hints[item.name]), self._ref(hints[item.name]), self._element(hints[item.name]),
                            item.compare,
                        )
                        for item in dataclasses.fields(value)
                    }

    @staticmethod
    def _unwrap(hint: Any) -> Any:
        if typing.get_origin(hint) is typing.Union or typing.get_origin(hint) is types.UnionType:
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

    def eq_unsafe(self, name: str) -> List[str]:
        """dataclass の `==` / hash が比べる field のうち、未確認の値を持ち得るもの（Any / record / 容器）。

        owner が写すのは scalar / bool の field と exact な tuple の葉だけ。tuple の注釈の field に list のまま
        受理した値や、注釈が `Any` / record の field の値は、比べると要素・値の型の code を呼び得る。
        """

        return [
            field for field, info in self.classes.get(name, {}).items()
            if info.compare and info.kind not in ("scalar", "bool")
        ]


@dataclasses.dataclass(frozen=True)
class _Unit:
    module: str
    owner: Optional[str]
    function: ast.FunctionDef

    @property
    def key(self) -> Tuple[str, Optional[str], str]:
        return (self.module, self.owner, self.function.name)

    @property
    def label(self) -> str:
        return f"{self.module.rsplit('.', 1)[-1]}:{self.owner}.{self.function.name}"


class _Module:
    def __init__(self, name: str, tree: ast.Module, ref_module_names: Set[str]):
        self.name = name
        self.tree = tree
        self.functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
        self.methods: Dict[Tuple[str, str], ast.FunctionDef] = {}
        self.record_classes: List[ast.ClassDef] = []
        #: ref でない class（`ExpansionBudgetCollector` など）: method は辿るが、field は owner が写した値ではない
        self.plain_classes: List[ast.ClassDef] = []
        for node in tree.body:
            if isinstance(node, ast.ClassDef):
                (self.record_classes if _decorated(node, {"runtime_ref_record"}) else self.plain_classes).append(node)
                for item in node.body:
                    if isinstance(item, ast.FunctionDef):
                        self.methods[(node.name, item.name)] = item
        #: reader として信用する名前（`live_values` / owner から import した名前と、`live_values` の module。
        #: 同じ名前を自分で定義・代入したものは reader ではない）
        self.reader_names: Set[str] = set()
        self.reader_modules: Set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.module in READER_MODULES:
                self.reader_names.update(alias.asname or alias.name for alias in node.names)
            if isinstance(node, ast.ImportFrom) and node.module == "scripts.function_tracer_pcode.core":
                self.reader_modules.update(alias.asname or alias.name for alias in node.names if alias.name == "live_values")
        # module の名前空間で上書きした名前は reader ではない（関数の中の局所変数は呼び出しのときに env で見分ける）
        defined = set(self.functions) | {
            target.id for node in tree.body if isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign))
            for target in (node.targets if isinstance(node, ast.Assign) else [node.target]) if isinstance(target, ast.Name)
        }
        self.reader_names -= defined
        #: ref でない class の instance の属性（`__init__` で組み込みの容器を置いたもの: 要素は未確認）
        self.plain_attributes: Dict[Tuple[str, str], str] = {}
        for node in self.plain_classes:
            for item in node.body:
                if isinstance(item, ast.FunctionDef) and item.name == "__init__":
                    for statement in ast.walk(item):
                        if isinstance(statement, (ast.Assign, ast.AnnAssign)):
                            targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
                            value = statement.value
                            container = isinstance(value, (ast.List, ast.Set, ast.Dict)) or (
                                isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
                                and value.func.id in ("list", "set", "dict") and not value.args
                            )
                            for target in targets:
                                if isinstance(target, ast.Attribute) and isinstance(target.value, ast.Name) and target.value.id == "self":
                                    key = (node.name, target.attr)
                                    state = CONTAINER if container else UNKNOWN
                                    self.plain_attributes[key] = state if key not in self.plain_attributes else meet(self.plain_attributes[key], state)
        #: import した ref module の名前: 名前 → (module, 名前)
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
    if isinstance(value, ast.Dict) and all(
        k is not None and _literal_state(k) and _literal_state(v) for k, v in zip(value.keys, value.values)
    ):
        return CLEAN_CONTAINER
    if (
        isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
        and value.func.id in ("frozenset", "tuple", "set") and all(_literal_state(x) for x in value.args)
    ):
        return CLEAN_CONTAINER
    return None


def _all_args(function: Any) -> List[ast.arg]:
    args = function.args
    out = args.posonlyargs + args.args + args.kwonlyargs
    if args.vararg is not None:
        out = out + [args.vararg]
    if args.kwarg is not None:
        out = out + [args.kwarg]
    return out


def _has_receiver(unit: _Unit) -> bool:
    return unit.owner is not None and not _decorated(unit.function, {"staticmethod"})


def _parameters(unit: _Unit) -> List[ast.arg]:
    """receiver を除いた、位置で渡せる引数とキーワード専用の引数。"""

    args = unit.function.args
    positional = args.posonlyargs + args.args
    if _has_receiver(unit):
        positional = positional[1:]
    return positional + args.kwonlyargs


class ConstructionGuard:
    """構築の経路の消費を検査する（`violations()` が違反の一覧）。"""

    def __init__(self, sources: Dict[str, str], world: RefWorld, external: Iterable[str] = ()):
        self.world = world
        names = set(sources)
        self.modules = {name: _Module(name, ast.parse(text), names) for name, text in sources.items()}
        #: ref module の外から import される `_` で始まる名前（外から呼べるので起点にする）
        self.external = set(external)
        #: class の名前 → 定義した module（ref の class と、ref でない class）
        self.class_modules: Dict[str, str] = {}
        self.plain_classes: Set[str] = set()
        for module in self.modules.values():
            for node in module.record_classes:
                self.class_modules[node.name] = module.name
            for node in module.plain_classes:
                self.class_modules[node.name] = module.name
                self.plain_classes.add(node.name)
        self._violations: List[str] = []
        self._reached: List[str] = []
        self.edges: Set[Tuple[str, str]] = set()
        #: ref の class → `__post_init__` を抜けたときの field の状態（検証が写し直した field を含む）
        self.post_states: Dict[str, Dict[str, str]] = {}
        #: ref でない class の自分の容器 → 入れた要素の状態
        self.plain_elements: Dict[Tuple[str, str], str] = {}
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
        return cls(sources, RefWorld(modules), _externally_imported(set(sources)))

    # -- 公開の読み口 ------------------------------------------------------------------------------

    def ref_producing_functions(self, *, with_arguments: bool = True) -> List[str]:
        """ref を（推移的に）作る、外から呼べる関数・method（`with_arguments` なら引数を持つものだけ: 入口で
        なければならない。そうでなければ引数の無いものも含む: 行列が実行しなければならない）。

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
            params = [a.arg for a in _all_args(function) if a.arg not in ("self", "cls")]
            if builds[(module_name, owner, name)] and (params or not with_arguments) and self._callable_from_outside(name) and not (name.startswith("__") and name.endswith("__") and name != "__init__"):
                out.append(f"{module_name.rsplit('.', 1)[-1]}:{owner}.{name}")
        return sorted(out)

    def violations(self) -> List[str]:
        """違反（`ACCEPTED` に理由つきで載せたものを除く）。"""

        return [v for v in self._violations if v.rsplit(" (line ", 1)[0] not in ACCEPTED]

    def accepted(self) -> List[str]:
        return [v for v in self._violations if v.rsplit(" (line ", 1)[0] in ACCEPTED]

    def reached(self) -> List[str]:
        return list(self._reached)

    # -- 名前の解決 ----------------------------------------------------------------------------------

    def _resolve(self, module: _Module, name: str) -> Optional[_Unit]:
        if name in module.functions:
            return _Unit(module.name, None, module.functions[name])
        target = module.imports.get(name)
        if target is not None and target[0] in self.modules and target[1] in self.modules[target[0]].functions:
            other = self.modules[target[0]]
            return _Unit(other.name, None, other.functions[target[1]])
        return None

    def method(self, owner: str, name: str) -> Optional[_Unit]:
        module_name = self.class_modules.get(owner)
        if module_name is None:
            return None
        function = self.modules[module_name].methods.get((owner, name))
        return None if function is None else _Unit(module_name, owner, function)

    def _unit_of(self, key: Tuple[str, Optional[str], str]) -> _Unit:
        module = self.modules[key[0]]
        function = module.functions[key[2]] if key[1] is None else module.methods[(key[1], key[2])]
        return _Unit(key[0], key[1], function)

    # -- 起点と fixpoint -----------------------------------------------------------------------------

    def _callable_from_outside(self, name: str) -> bool:
        return not name.startswith("_") or name in self.external or (name.startswith("__") and name.endswith("__"))

    def _seeds(self) -> List[Tuple[_Unit, str]]:
        """起点: 構築（`__post_init__`）、入口（`runtime_ref_entry` と自前の `__init__`）、外から呼べるすべての
        関数・method・property（公開の名前と、外から import される名前。引数の有無・ref の class かどうかに依らない）。
        外から呼べるものの引数は呼び出し元が何でも渡せるので、注釈の状態（写さない）で検査する。"""

        seeds = []
        for module in self.modules.values():
            for node in module.record_classes + module.plain_classes:
                for item in node.body:
                    if not isinstance(item, ast.FunctionDef):
                        continue
                    unit = _Unit(module.name, node.name, item)
                    if item.name == "__post_init__" and node in module.record_classes:
                        seeds.append((unit, "construct"))
                    elif _decorated(item, {"runtime_ref_entry"}) or (item.name == "__init__" and node in module.record_classes):
                        seeds.append((unit, "entry"))
                    elif self._callable_from_outside(item.name):
                        seeds.append((unit, "external"))
            for function in module.functions.values():
                if _decorated(function, {"runtime_ref_entry"}):
                    seeds.append((_Unit(module.name, None, function), "entry"))
                elif self._callable_from_outside(function.name):
                    seeds.append((_Unit(module.name, None, function), "external"))
        return seeds

    def _run(self) -> None:
        roles: Dict[Tuple[str, Optional[str], str], str] = {}
        units: Dict[Tuple[str, Optional[str], str], _Unit] = {}
        for unit, role in self._seeds():
            roles.setdefault(unit.key, role)
            units[unit.key] = unit
        params: Dict[Tuple[str, Optional[str], str], Dict[str, str]] = {}
        summaries: Dict[Tuple[str, Optional[str], str], str] = {}
        for _ in range(60):
            calls: Dict[Any, List[Tuple[Dict[int, str], Dict[str, str]]]] = {}
            returns: Dict[Any, str] = {}
            found: Dict[Any, _Unit] = {}
            post_states: Dict[str, Dict[str, str]] = {}
            plain_elements: Dict[Tuple[str, str], str] = {}
            for key in list(units):
                check = _FunctionCheck(self, units[key], roles[key], params.get(key, {}), summaries, calls, found, None)
                check.run()
                returns[key] = check.returned
                for attribute, element in check.plain_found.items():
                    plain_elements[attribute] = meet(plain_elements.get(attribute, BOTTOM), element)
                if roles[key] == "construct":
                    post_states[units[key].owner] = check.exit_fields
            for key, unit in found.items():
                if key not in units:
                    units[key] = unit
                    roles[key] = "helper"
            new_params = {
                key: _meet_parameters(units[key], calls.get(key, [])) for key in units if roles[key] == "helper"
            }
            if (
                new_params == params and returns == summaries and post_states == self.post_states
                and plain_elements == self.plain_elements and not (set(found) - set(summaries))
            ):
                break
            changing = sorted(
                [f"return {k}: {summaries.get(k)} -> {v}" for k, v in returns.items() if summaries.get(k) != v]
                + [f"params {k}: {params.get(k)} -> {v}" for k, v in new_params.items() if params.get(k) != v]
            )
            params, summaries = new_params, returns
            self.post_states = post_states
            self.plain_elements = plain_elements
        else:  # pragma: no cover - 解析の発散は guard の不具合
            raise RuntimeError("construction guard did not reach a fixpoint: " + "; ".join(changing[:6]))
        #: 到達した関数 → 戻り値の状態（検査と説明のための読み口）
        self.summaries = {units[key].label: state for key, state in summaries.items() if key in units}
        report: List[str] = []
        for key in sorted(units, key=lambda k: (k[0], k[1] or "", k[2])):
            unit = units[key]
            _FunctionCheck(self, unit, roles[key], params.get(key, {}), summaries, {}, {}, report).run()
            self._reached.append(unit.label)
        self._violations = sorted(set(report))


def _defaults(function: Any) -> Dict[str, str]:
    """既定値を持つ引数 → 既定値の状態（定数なら clean）。"""

    args = function.args
    positional = args.posonlyargs + args.args
    out = {}
    for arg, default in zip(positional[len(positional) - len(args.defaults):], args.defaults):
        out[arg.arg] = _literal_state(default) or UNKNOWN
    for arg, default in zip(args.kwonlyargs, args.kw_defaults):
        if default is not None:
            out[arg.arg] = _literal_state(default) or UNKNOWN
    return out


def _env_name(node: ast.AST) -> Optional[str]:
    """絞り込みで状態を書き換える名前（局所変数、または `self.<field>`）。"""

    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == "self":
        return f"self.{node.attr}"
    return None


def _scalar_constant(node: ast.AST) -> bool:
    return isinstance(node, ast.Constant) and (node.value is None or type(node.value) in (int, str, bool, float))


def _externally_imported(ref_modules: Set[str]) -> Set[str]:
    """ref module の外（tests を除く production）から import される `_` で始まる名前。"""

    names: Set[str] = set()
    for path in PACKAGE.rglob("*.py"):
        relative = ".".join(path.relative_to(PACKAGE.parents[1]).with_suffix("").parts)
        if relative in ref_modules or ".tests." in relative + ".":
            continue
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.ImportFrom) and node.module in ref_modules:
                names.update(alias.name for alias in node.names if alias.name.startswith("_"))
    return names


def _meet_parameters(unit: _Unit, calls: List[Tuple[Dict[int, str], Dict[str, str]]]) -> Dict[str, str]:
    states: Dict[str, str] = {}
    defaults = _defaults(unit.function)
    for index, arg in enumerate(_parameters(unit)):
        state = BOTTOM
        for positional, keywords in calls:
            if index in positional and arg not in unit.function.args.kwonlyargs:
                state = meet(state, positional[index])
            elif arg.arg in keywords:
                state = meet(state, keywords[arg.arg])
            elif "*" in keywords:
                state = meet(state, keywords["*"])  # `**kwargs` / `*args` で渡した値（中身は分からない）
            elif arg.arg in defaults:
                state = meet(state, defaults[arg.arg])
        states[arg.arg] = state
    for extra in (unit.function.args.vararg, unit.function.args.kwarg):
        if extra is not None:
            states[extra.arg] = CONTAINER
    return states


class _FunctionCheck:
    def __init__(self, guard: ConstructionGuard, unit: _Unit, role: str, params: Dict[str, str],
                 summaries: Dict[Any, str], calls: Dict[Any, List[Any]], found: Dict[Any, _Unit],
                 report: Optional[List[str]]):
        self.guard, self.unit, self.role, self.params = guard, unit, role, params
        self.module = guard.modules[unit.module]
        self.world = guard.world
        self.summaries = summaries
        self.calls = calls
        self.found = found
        self.report = report
        self.local_functions: Dict[str, str] = {}
        #: 見つけた ref でない class の自分の容器への追加（`(class, attr)` → 要素の状態）
        self.plain_found: Dict[Tuple[str, str], str] = {}
        self._continues: List[List[Dict[str, str]]] = []
        self._breaks: List[List[Dict[str, str]]] = []
        self.returned = BOTTOM
        #: `__post_init__` を抜けたときの `self.<field>` の状態
        self.exit_fields: Dict[str, str] = {}
        self.generator = any(isinstance(n, (ast.Yield, ast.YieldFrom)) for n in ast.walk(unit.function))

    # -- 入口 ---------------------------------------------------------------------------------------

    def run(self) -> None:
        env: Dict[str, str] = {}
        function = self.unit.function
        normalized = self.role == "entry"
        receiver = _has_receiver(self.unit)
        positional = function.args.posonlyargs + function.args.args
        for index, arg in enumerate(_all_args(function)):
            if receiver and index == 0 and arg in positional:
                classmethod_ = _decorated(function, {"classmethod"})
                plain = self.unit.owner in self.guard.plain_classes
                env[arg.arg] = f"class:{self.unit.owner}" if classmethod_ else (f"obj:{self.unit.owner}" if plain else f"ref:{self.unit.owner}")
            elif self.role == "helper":
                env[arg.arg] = self.params.get(arg.arg, BOTTOM)
            elif arg is function.args.vararg or arg is function.args.kwarg:
                env[arg.arg] = CLEAN_CONTAINER if normalized and self._annotation_state(arg.annotation, normalized=True) == CLEAN else CONTAINER
            else:
                env[arg.arg] = self._annotation_state(arg.annotation, normalized=normalized)
        if self.role == "construct":
            # 検証の前に owner が写した field（検証が書き直すと、その状態で上書きする）
            for field in self.world.classes.get(self.unit.owner or "", {}):
                env[f"self.{field}"] = self._field(self.unit.owner, field, proven=True, after_validation=False)
        self._block(function.body, env)
        if not self._ends(function.body):
            self._returns(CLEAN, env)

    def _returns(self, state: str, env: Optional[Dict[str, str]] = None) -> None:
        self.returned = meet(self.returned, state)
        if self.role == "construct" and env is not None:
            for name, value in env.items():
                if name.startswith("self."):
                    field = name[5:]
                    self.exit_fields[field] = meet(self.exit_fields.get(field, BOTTOM), value)

    def _annotation_state(self, annotation: Optional[ast.AST], *, normalized: bool) -> str:
        if annotation is None:
            return UNKNOWN
        text = ast.unparse(annotation).replace('"', "").replace("'", "").replace(" ", "")
        bare = text[len("Optional["):-1] if text.startswith("Optional[") else text
        if bare.endswith("|None"):
            bare = bare[: -len("|None")]
        if bare in self.world.classes:
            return f"typed:{bare}"  # 注釈だけ（呼び出し元は代わりの型を渡せる）
        for name in self.world.classes:
            if bare in (f"Tuple[{name},...]", f"tuple[{name},...]"):
                return f"seq:typed:{name}" if normalized else CONTAINER
        if not normalized:
            return UNKNOWN
        # `runtime_ref_entry` が写した引数（owner の分類と同じ: scalar / bool / tuple）
        if bare in ("int", "str", "bool", "float"):
            return CLEAN
        if bare.startswith(("Tuple[", "tuple[")) or bare in ("Tuple", "tuple"):
            return CONTAINER  # exact な tuple の葉は写すが、list のまま渡された値の要素は写さない
        return UNKNOWN

    def flag(self, node: ast.AST, what: str) -> None:
        if self.report is not None:
            key = f"{self.unit.module.rsplit('.', 1)[-1]}.py:{self.unit.function.name}: {what}: {ast.unparse(node)[:100]}"
            self.report.append(f"{key} (line {node.lineno})")

    # -- 到達 ---------------------------------------------------------------------------------------

    def _follow(self, target: _Unit, call: Optional[ast.Call], env: Dict[str, str]) -> str:
        """到達した関数・method・property: 呼び出しを記録し、戻り値の状態（summary）を返す。"""

        self.found[target.key] = target
        self.guard.edges.add((self.unit.label, target.label))
        if call is not None:
            positional: Dict[int, str] = {}
            keywords: Dict[str, str] = {}
            index = 0
            for a in call.args:
                if isinstance(a, ast.Starred):
                    keywords["*"] = meet(keywords.get("*", BOTTOM), element_of(self.state(a.value, env)))
                    continue
                positional[index] = self.state(a, env)
                index += 1
            for k in call.keywords:
                if k.arg is None:
                    keywords["*"] = meet(keywords.get("*", BOTTOM), UNKNOWN)
                else:
                    keywords[k.arg] = self.state(k.value, env)
            self.calls.setdefault(target.key, []).append((positional, keywords))
        else:
            self.calls.setdefault(target.key, []).append(({}, {}))
        return self.summaries.get(target.key, BOTTOM)

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
            return self._attribute(e, env)
        if isinstance(e, ast.Tuple) and not any(isinstance(x, ast.Starred) for x in e.elts):
            return make_tup([self.state(x, env) for x in e.elts])
        if isinstance(e, (ast.Tuple, ast.List, ast.Set)):
            element = BOTTOM
            for x in e.elts:
                element = meet(element, element_of(self.state(x.value, env)) if isinstance(x, ast.Starred) else self.state(x, env))
            return "seq:" + (CLEAN if element == BOTTOM else element)
        if isinstance(e, ast.Dict):
            key, value = BOTTOM, BOTTOM
            for k, v in zip(e.keys, e.values):
                if k is None:  # `**other`
                    other = self.state(v, env)
                    ok, ov = map_parts(other) if other.startswith("map:") else (UNKNOWN, UNKNOWN)
                    key, value = meet(key, ok), meet(value, ov)
                    continue
                key, value = meet(key, self.state(k, env)), meet(value, self.state(v, env))
            return make_map(key, value)
        if isinstance(e, ast.Compare):
            return CLEAN
        if isinstance(e, ast.UnaryOp):
            return CLEAN if isinstance(e.op, ast.Not) or self.state(e.operand, env) == CLEAN else UNKNOWN
        if isinstance(e, ast.BoolOp):
            result = BOTTOM
            for x in e.values:
                result = meet(result, self.state(x, env))
            return result
        if isinstance(e, ast.BinOp):
            left, right = self.state(e.left, env), self.state(e.right, env)
            if left in (CLEAN, BOTTOM) and right in (CLEAN, BOTTOM):
                return CLEAN
            if is_container(left) and is_container(right) and isinstance(e.op, (ast.Add, ast.BitOr, ast.BitAnd, ast.Sub, ast.BitXor)):
                return meet(as_seq(left), as_seq(right))
            if is_container(left) and right == CLEAN and isinstance(e.op, ast.Mult):
                return as_seq(left)
            return UNKNOWN
        if isinstance(e, ast.IfExp):
            return meet(self.state(e.body, self._narrowed(e.test, env)), self.state(e.orelse, env))
        if isinstance(e, ast.JoinedStr):
            return CLEAN
        if isinstance(e, ast.Subscript):
            base = self.state(e.value, env)
            if isinstance(e.slice, ast.Slice):
                return as_seq(base) if is_container(base) else UNKNOWN
            if base == CLEAN:
                return CLEAN  # 組み込みの文字列の 1 文字
            if base.startswith("map:"):
                return map_parts(base)[1]
            if base.startswith("tup:") and isinstance(e.slice, ast.Constant) and isinstance(e.slice.value, int):
                items = tup_items(base)
                if -len(items) <= e.slice.value < len(items):
                    return items[e.slice.value]
            if base.startswith("tup:") and isinstance(e.slice, ast.UnaryOp) and isinstance(e.slice.op, ast.USub) and isinstance(e.slice.operand, ast.Constant):
                items = tup_items(base)
                if 0 < e.slice.operand.value <= len(items):
                    return items[-e.slice.operand.value]
            return element_of(base)
        if isinstance(e, (ast.ListComp, ast.GeneratorExp, ast.SetComp)):
            inner = self._comprehension_env(e, env, check=False)
            return "seq:" + self.state(e.elt, inner)
        if isinstance(e, ast.DictComp):
            inner = self._comprehension_env(e, env, check=False)
            return make_map(self.state(e.key, inner), self.state(e.value, inner))
        if isinstance(e, ast.Call):
            return self._call(e, env)
        if isinstance(e, ast.Lambda):
            return CLEAN
        if isinstance(e, ast.Starred):
            return self.state(e.value, env)
        if isinstance(e, ast.NamedExpr):
            return self.state(e.value, env)
        return UNKNOWN

    def _field(self, owner: str, name: str, proven: bool, after_validation: bool = True) -> Optional[str]:
        """C の field `name` の値の状態（field でなければ `None`）。

        本物の instance（`proven`）の field は、構築を終えた後の値: scalar / bool は owner が写した値、検証
        （`__post_init__`）が書き直した field は書き直した値の状態（owner はその後でもう一度写す）。
        """

        info = self.world.classes.get(owner, {}).get(name)
        if info is None:
            return None
        if not proven and info.kind == "tuple":
            # 注釈だけの値の tuple の field: 代わりの型なら何でもあり得る（scalar の subclass も）。reader で
            # 読むと要素の注釈の状態の容器になる
            inner = f"seq:typed:{info.element}" if info.element and info.element != "scalar" else CONTAINER
            return "uncertain:" + inner
        if proven and after_validation:
            post = self.guard.post_states.get(owner, {}).get(name)
            if info.kind in ("scalar", "bool"):
                return CLEAN
            if post is not None and post != BOTTOM:
                if info.kind == "tuple" and not is_container(post) and post != CLEAN:
                    post = CONTAINER
                return post
        if info.ref:
            return f"typed:{info.ref}"  # record の field の値は注釈どおりとは限らない
        if info.kind == "tuple":
            if info.element and info.element != "scalar":
                return f"seq:typed:{info.element}"
            return CONTAINER  # exact な tuple の葉は写すが、list のまま受理した値の要素は写さない
        if proven and info.kind in ("scalar", "bool"):
            return CLEAN  # 本物の instance の scalar の field は owner が写した値
        return UNKNOWN

    def _attribute(self, e: ast.Attribute, env: Dict[str, str], *, default: Optional[ast.AST] = None) -> str:
        on_self = isinstance(e.value, ast.Name) and e.value.id == "self"
        if on_self and f"self.{e.attr}" in env:
            return env[f"self.{e.attr}"]
        return self._attribute_of(self.state(e.value, env), e.attr, env)

    def _attribute_of(self, base: str, name: str, env: Dict[str, str]) -> str:
        if base.startswith("ref:"):
            owner = base[4:]
            found = self._field(owner, name, proven=True)
            if found is not None:
                return found
            target = self.guard.method(owner, name)
            if target is not None and _decorated(target.function, {"property"}):
                return self._follow(target, None, env)
            if target is not None:
                return f"bound:{owner}.{name}"
            return UNKNOWN
        if base.startswith("nref:"):
            # `isinstance` で絞った値: C か C の subclass の本物の instance（field は owner が写した値）。method は
            # subclass が上書きし得るので、本体（C の code）は検査し、結果は未確認として扱う
            owner = base[5:]
            found = self._field(owner, name, proven=True)
            if found is not None:
                return found
            target = self.guard.method(owner, name)
            if target is not None and _decorated(target.function, {"property"}):
                self._follow(target, None, env)
                return UNKNOWN
            if target is not None:
                return f"tbound:{owner}.{name}"
            return UNKNOWN
        if base.startswith("typed:"):
            found = self._field(base[6:], name, proven=False)
            if found is not None:
                return found
            target = self.guard.method(base[6:], name)
            if target is not None and _decorated(target.function, {"property"}):
                self._follow(target, None, env)  # 本物なら package の code が走る: 本体は検査する
                return UNKNOWN  # 代わりの型なら外の code: 結果は未確認
            if target is not None:
                return f"tbound:{base[6:]}.{name}"
            return UNKNOWN
        if base.startswith("class:"):
            return f"classattr:{base[6:]}.{name}"
        if base.startswith("obj:"):
            owner = base[4:]
            module = self.guard.modules[self.guard.class_modules[owner]]
            if (owner, name) in module.plain_attributes:
                if module.plain_attributes[(owner, name)] == CONTAINER:
                    # 自分の容器: 要素はこの class の method が入れた値（`self.<attr>.add(x)` などの meet）
                    element = self.guard.plain_elements.get((owner, name), BOTTOM)
                    return "seq:" + (CLEAN if element == BOTTOM else element)
                return module.plain_attributes[(owner, name)]
            target = self.guard.method(owner, name)
            if target is not None and _decorated(target.function, {"property"}):
                return self._follow(target, None, env)
            if target is not None:
                return f"bound:{owner}.{name}"
            return UNKNOWN
        if base == CLEAN:
            return CLEAN  # 組み込みの値・型の属性（`type(x).__qualname__` など）
        return UNKNOWN

    def _call(self, call: ast.Call, env: Dict[str, str]) -> str:
        callee = call.func
        name = callee.id if isinstance(callee, ast.Name) else callee.attr if isinstance(callee, ast.Attribute) else ""
        through_owner = (isinstance(callee, ast.Name) and name in self.module.reader_names and name not in env) or (
            isinstance(callee, ast.Attribute) and isinstance(callee.value, ast.Name) and callee.value.id in self.module.reader_modules
        )
        if through_owner and name in CONTAINER_READERS:
            argument = self.state(call.args[0], env) if call.args else UNKNOWN
            if argument.startswith("uncertain:"):
                return argument[len("uncertain:"):]
            return argument if is_container(argument) and name != "elements_within_limit" else CONTAINER
        if through_owner and name in TREE_READERS:
            return CLEAN  # 組み込みの値か、葉まで組み込みの値の容器（形は分からない: 反復・添字・method は clean）
        if through_owner and name in LEAF_READERS:
            argument = self.state(call.args[0], env) if call.args else UNKNOWN
            if argument == MAYBE_SCALAR:
                return CLEAN
            return argument if clean_tree(argument) or argument.startswith(("ref:", "nref:", "typed:")) else LEAF
        if through_owner and name in READERS:
            return CLEAN
        if isinstance(callee, ast.Name):
            if name in SAFE_ANY:
                return CLEAN
            if name in self.world.classes:
                return f"ref:{name}"
            if name == "cls" and self.unit.owner:
                return f"ref:{self.unit.owner}"
            if name == "replace" and call.args:
                base = self.state(call.args[0], env)
                return base if base.startswith(("ref:", "nref:")) else UNKNOWN
            if name == "getattr" and len(call.args) >= 2 and isinstance(call.args[1], ast.Constant):
                found = self._attribute_of(self.state(call.args[0], env), call.args[1].value, env)
                if len(call.args) == 3:
                    found = meet(found, self.state(call.args[2], env))
                return found
            if name == "len":
                return CLEAN
            if name == "next" and call.args:
                return element_of(self.state(call.args[0], env))
            if name in CONTAINER_BUILTINS:
                inner = [self.state(a, env) for a in call.args]
                if name == "range":
                    return CLEAN_CONTAINER
                if name == "enumerate" and inner:
                    return "seq:" + make_tup([CLEAN, element_of(inner[0]) if is_container(inner[0]) else UNKNOWN])
                if name == "zip":
                    return "seq:" + make_tup([element_of(s) if is_container(s) else UNKNOWN for s in inner])
                if not inner:
                    return CLEAN_CONTAINER
                return inner[0] if is_container(inner[0]) else CONTAINER
            if name in CONSUMING_BUILTINS:
                inner = [self.state(a, env) for a in call.args]
                if name in ("sorted", "set", "frozenset", "dict"):
                    return inner[0] if inner and is_container(inner[0]) else CLEAN_CONTAINER
                if name in ("min", "max") and len(inner) == 1:
                    return element_of(inner[0])
                if name in ("min", "max"):
                    result = BOTTOM
                    for state in inner:
                        result = meet(result, state)
                    return result
                if name in ("int", "float", "abs", "round") and inner and all(clean_tree(s) or s == LEAF for s in inner):
                    return CLEAN  # 数への変換の結果は組み込みの数（容器なら例外）
                return CLEAN if all(clean_tree(s) for s in inner) else UNKNOWN
            if name in self.local_functions:
                return self.local_functions[name]
            target = self.guard._resolve(self.module, name)
            if target is not None:
                return self._follow(target, call, env)
            state = env.get(name, "")
            if state.startswith("bound:"):
                return self._call_bound(state, call, env)
            return UNKNOWN
        if isinstance(callee, ast.Attribute):
            if isinstance(callee.value, ast.Name) and callee.value.id in BUILTIN_TYPES:
                return CLEAN  # 基底型の slot の実装（subclass の上書きを呼ばない）
            if ast.unparse(callee) == "json.dumps":
                return CLEAN  # 引数の消費は `_expr` が見る
            base = self.state(callee.value, env)
            if base.startswith(("ref:", "nref:", "typed:", "obj:")):
                found = self._attribute_of(base, callee.attr, env)
                if found.startswith("bound:"):
                    return self._call_bound(found, call, env)
                if found.startswith("tbound:"):
                    # 注釈だけの値の method: 本物なら package の code が走るので本体を検査し、結果は未確認
                    self._call_bound("bound:" + found[len("tbound:"):], call, env)
                    return UNKNOWN
                return UNKNOWN  # field の値の呼び出し
            if base.startswith("class:"):
                target = self.guard.method(base[6:], callee.attr)
                if target is not None:
                    return self._follow(target, call, env)
                return UNKNOWN
            if base == CLEAN:
                return CLEAN  # clean な値（組み込みの値）の method
            if base == LEAF:
                return LEAF  # 基底型の str なら基底型の method、外の object なら外の code
            if base.startswith("map:"):
                key, value = map_parts(base)
                if callee.attr in ("get", "pop", "setdefault"):
                    default = self.state(call.args[1], env) if len(call.args) > 1 else CLEAN
                    return meet(value, default)
                if callee.attr == "items":
                    return "seq:" + make_tup([key, value])
                if callee.attr == "values":
                    return "seq:" + value
                if callee.attr == "keys":
                    return "seq:" + key
                if callee.attr == "copy":
                    return base
                if callee.attr in MUTATORS:
                    return CLEAN
                return UNKNOWN
            if is_container(base):
                base = as_seq(base)
                if callee.attr in ("get", "pop", "setdefault"):
                    return element_of(base)
                if callee.attr == "items":
                    element = element_of(base)
                    return "seq:" + make_tup([element, element])  # 組み込みの mapping の items は 2 要素の tuple
                if callee.attr in ("values", "keys", "copy"):
                    return base
                if callee.attr in MUTATORS:
                    return CLEAN
                return UNKNOWN
            return UNKNOWN  # API の戻り値・外の object（`typed:C` を含む）の method の戻り値
        return UNKNOWN

    def _call_bound(self, bound: str, call: ast.Call, env: Dict[str, str]) -> str:
        owner, name = bound[len("bound:"):].split(".", 1)
        target = self.guard.method(owner, name)
        return self._follow(target, call, env) if target is not None else UNKNOWN

    # -- 消費の判定 ----------------------------------------------------------------------------------

    @staticmethod
    def _truth_ok(state: str) -> bool:
        return state in (CLEAN, BOTTOM, LEAF) or state.startswith(("seq:", "tup:", "map:", "ref:", "nref:", "class:", "bound:", "classattr:"))

    def _compare_ok(self, state: str) -> bool:
        """`==` / 順序 / hash に渡してよい値（組み込みの値、比べても未確認の値に届かない ref と、その容器）。"""

        if clean_tree(state) or state.startswith(("class:", "classattr:")):
            return True
        if state.startswith(("ref:", "nref:")):
            return not self.world.eq_unsafe(state.split(":", 1)[1])
        if state.startswith("seq:"):
            return self._compare_ok(state[4:])
        if state.startswith("tup:"):
            return all(self._compare_ok(item) for item in tup_items(state))
        return False

    def _value_ok(self, state: str) -> bool:
        """変換・format・算術に渡してよい値（組み込みの値と、葉まで組み込みの値の容器）。"""

        return clean_tree(state)

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
            state = BOTTOM
            for branch in branches:
                if name in branch:
                    state = meet(state, branch[name])
            env[name] = state

    def _narrow_one(self, t: ast.AST, out: Dict[str, str], positive: bool) -> None:
        if (
            positive and isinstance(t, ast.Call) and isinstance(t.func, ast.Name) and t.func.id == "isinstance"
            and len(t.args) == 2 and isinstance(t.args[0], ast.Name)
        ):
            kinds = t.args[1].elts if isinstance(t.args[1], ast.Tuple) else [t.args[1]]
            names = [k.id for k in kinds if isinstance(k, ast.Name)]
            if len(names) == 1 and names[0] in self.world.classes:
                out[t.args[0].id] = f"nref:{names[0]}"  # C か C の subclass（`type(x) is C` なら C そのもの）
            elif names and set(names) == {"bool"}:
                out[t.args[0].id] = CLEAN  # bool は subclass を作れない
            elif names and set(names) <= CONTAINER_TYPES:
                current = out.get(t.args[0].id, UNKNOWN)
                out[t.args[0].id] = current if is_container(current) else CONTAINER
            elif names and set(names) <= SCALAR_TYPES | {"bool"}:
                current = out.get(t.args[0].id, UNKNOWN)
                # 葉だけを写した値は exact な scalar。それ以外は subclass かもしれない（葉の reader で読む）
                out[t.args[0].id] = CLEAN if current in (CLEAN, LEAF) else MAYBE_SCALAR
        elif (
            positive and isinstance(t, ast.Compare) and len(t.ops) == 1 and isinstance(t.ops[0], ast.Is)
            and isinstance(t.left, ast.Call) and isinstance(t.left.func, ast.Name) and t.left.func.id == "type"
            and len(t.left.args) == 1 and isinstance(t.left.args[0], ast.Name)
            and isinstance(t.comparators[0], ast.Name)
        ):
            kind = t.comparators[0].id
            if kind in self.world.classes:
                out[t.left.args[0].id] = f"ref:{kind}"
            elif kind in ("int", "str", "bool", "float"):
                out[t.left.args[0].id] = CLEAN
            elif kind in CONTAINER_TYPES:
                current = out.get(t.left.args[0].id, UNKNOWN)
                out[t.left.args[0].id] = current if is_container(current) else CONTAINER
        elif (
            isinstance(t, ast.Compare) and len(t.ops) == 1 and isinstance(t.ops[0], (ast.Is, ast.IsNot))
            and isinstance(t.comparators[0], ast.Constant) and t.comparators[0].value is None
        ):
            # `x is None` が成り立つ側では x は `None`（clean）
            is_none = positive if isinstance(t.ops[0], ast.Is) else not positive
            name = _env_name(t.left)
            if is_none and name is not None:
                out[name] = CLEAN
        elif isinstance(t, ast.UnaryOp) and isinstance(t.op, ast.Not):
            self._narrow_one(t.operand, out, not positive)

    def _narrowed(self, test: ast.AST, env: Dict[str, str], positive: bool = True) -> Dict[str, str]:
        out = dict(env)
        if isinstance(test, ast.BoolOp):
            conjunction = isinstance(test.op, ast.And) == positive
            if conjunction:
                # `a and b` が真 / `a or b` が偽: どの項も（その向きで）成り立つ
                for t in test.values:
                    out = self._narrowed(t, out, positive)
                return out
            # `a or b` が真 / `a and b` が偽: どれか 1 つの項が成り立つ（前の項は逆向き）。合流は悪い方へ
            branches = []
            current = dict(env)
            for t in test.values:
                branches.append(self._narrowed(t, current, positive))
                current = self._narrowed(t, current, not positive)
            self._merge(out, *branches)
            return out
        self._narrow_one(test, out, positive)
        return out

    def _unpack(self, target: ast.AST, state: str, node: ast.AST) -> None:
        """tuple の target への代入は値を反復する（組み込みの容器か clean な値でなければ違反）。"""

        if isinstance(target, (ast.Tuple, ast.List)) and not is_container(state) and state not in (CLEAN, BOTTOM):
            self.flag(node, f"unpacking of {state}")

    def _bind(self, target: ast.AST, state: str, env: Dict[str, str]) -> None:
        if isinstance(target, ast.Name):
            env[target.id] = state
        elif isinstance(target, (ast.Tuple, ast.List)):
            if state.startswith("tup:") and not any(isinstance(item, ast.Starred) for item in target.elts):
                items = tup_items(state)
                if len(items) == len(target.elts):
                    for item, item_state in zip(target.elts, items):
                        self._bind(item, item_state, env)
                    return
            inner = CLEAN if state == CLEAN else element_of(state)
            for item in target.elts:
                self._bind(item.value if isinstance(item, ast.Starred) else item, inner, env)
        elif isinstance(target, ast.Subscript) and isinstance(target.value, ast.Name):
            current = env.get(target.value.id, UNKNOWN)
            if current.startswith("map:"):
                key, value = map_parts(current)
                env[target.value.id] = make_map(meet(key, self.state(target.slice, env)), meet(value, state))
            elif is_container(current):
                env[target.value.id] = "seq:" + meet(element_of(current), meet(state, self.state(target.slice, env)))

    def _statement(self, s: ast.stmt, env: Dict[str, str]) -> None:
        if isinstance(s, ast.Assign):
            self._expr(s.value, env)
            state = self.state(s.value, env)
            for target in s.targets:
                if isinstance(target, ast.Subscript):
                    self._key(target.slice, env, target)
                self._unpack(target, state, s)
                self._bind(target, state, env)
        elif isinstance(s, ast.AnnAssign):
            if s.value is not None:
                self._expr(s.value, env)
                self._bind(s.target, self.state(s.value, env), env)
        elif isinstance(s, ast.AugAssign):
            target, value = self.state(s.target, env), self.state(s.value, env)
            container = is_container(target) and is_container(value) and isinstance(s.op, ast.Add)
            if not container and not (self._value_ok(target) and self._value_ok(value)):
                self.flag(s, "arithmetic")
            self._expr(s.value, env)
            if container and isinstance(s.target, ast.Name):
                env[s.target.id] = meet(target, value)
        elif isinstance(s, ast.If):
            self._test(s.test, env)
            body_env, else_env = self._narrowed(s.test, env), self._narrowed(s.test, env, positive=False)
            self._block(s.body, body_env)
            self._block(s.orelse, else_env)
            # `return` / `raise` / `continue` / `break` で終わる分岐は次の文へ流れない（`continue` / `break` の
            # 状態は `_loop` が繰り返しの先頭・ループの後へ流す）
            live = [b for b, body in ((body_env, s.body), (else_env, s.orelse)) if not self._ends(body)]
            if live:
                self._merge(env, *live)
            else:
                env.clear()
                env.update(else_env)  # どちらも抜ける（以後は到達しない）
        elif isinstance(s, ast.While):
            self._test(s.test, env)
            self._loop(s, env, lambda loop_env: self._test(s.test, loop_env), self._narrowed(s.test, env))
        elif isinstance(s, ast.For):
            self._expr(s.iter, env)
            iterated = self.state(s.iter, env)
            if not is_container(iterated) and iterated not in (CLEAN, BOTTOM, LEAF):
                self.flag(s.iter, f"iteration of {iterated}")
            element = element_of(iterated) if iterated != CLEAN else CLEAN
            self._unpack(s.target, element, s.iter)
            self._loop(s, env, lambda loop_env: self._bind(s.target, element, loop_env), dict(env))
        elif isinstance(s, ast.Continue):
            if self._continues:
                self._continues[-1].append(dict(env))
        elif isinstance(s, ast.Break):
            if self._breaks:
                self._breaks[-1].append(dict(env))
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
        elif isinstance(s, ast.Return):
            if s.value is not None:
                self._expr(s.value, env)
                self._returns(self.state(s.value, env), env)
            else:
                self._returns(CLEAN, env)
        elif isinstance(s, ast.Expr):
            value = s.value
            if isinstance(value, (ast.Yield, ast.YieldFrom)):
                if value.value is not None:
                    self._expr(value.value, env)
                    state = self.state(value.value, env)
                    self._returns("seq:" + (element_of(state) if isinstance(value, ast.YieldFrom) else state))
                return
            self._expr(value, env)
            if (
                isinstance(value, ast.Call) and ast.unparse(value.func) == "object.__setattr__" and len(value.args) == 3
                and isinstance(value.args[0], ast.Name) and value.args[0].id == "self"
                and isinstance(value.args[1], ast.Constant)
            ):
                # 検証が写し直した field（以後の `self.<field>` の読みはこの状態。owner は検証の後にもう一度写す）
                env[f"self.{value.args[1].value}"] = self.state(value.args[2], env)
            elif (
                isinstance(value, ast.Call) and isinstance(value.func, ast.Attribute) and value.func.attr in MUTATORS
                and isinstance(value.func.value, ast.Attribute) and isinstance(value.func.value.value, ast.Name)
                and env.get(value.func.value.value.id, "").startswith("obj:")
            ):
                key = (env[value.func.value.value.id][4:], value.func.value.attr)
                added = BOTTOM
                for a in value.args:
                    added = meet(added, element_of(self.state(a, env)) if value.func.attr in ("extend", "update") else self.state(a, env))
                self.plain_found[key] = meet(self.plain_found.get(key, BOTTOM), added)
            elif (
                isinstance(value, ast.Call) and isinstance(value.func, ast.Attribute)
                and value.func.attr in MUTATORS and isinstance(value.func.value, ast.Name)
            ):
                current = env.get(value.func.value.id, UNKNOWN)
                if current.startswith("map:"):
                    key, item = map_parts(current)
                    if value.func.attr == "setdefault" and value.args:
                        key = meet(key, self.state(value.args[0], env))
                        item = meet(item, self.state(value.args[1], env) if len(value.args) > 1 else CLEAN)
                    elif value.func.attr == "update":
                        for a in value.args:
                            other = self.state(a, env)
                            ok, ov = map_parts(other) if other.startswith("map:") else (UNKNOWN, UNKNOWN)
                            key, item = meet(key, ok), meet(item, ov)
                        for k in value.keywords:
                            item = meet(item, self.state(k.value, env))
                    env[value.func.value.id] = make_map(key, item)
                elif is_container(current):
                    added = BOTTOM
                    for a in value.args[-1:] if value.func.attr != "update" else value.args:
                        state = self.state(a, env)
                        added = meet(added, element_of(state) if value.func.attr in ("extend", "update") else state)
                    if value.func.attr == "setdefault" and value.args:
                        added = meet(added, self.state(value.args[0], env))
                    env[value.func.value.id] = "seq:" + meet(element_of(current), added)
        elif isinstance(s, ast.Match):
            # `match x:` の case は値と比べる（`==` / hash / 型の判定）: 主語は比べてよい値でなければ違反
            subject = self.state(s.subject, env)
            if not self._compare_ok(subject):
                self.flag(s.subject, f"match of {subject}")
            self._expr(s.subject, env)
            branches = []
            for case in s.cases:
                case_env = dict(env)
                for node in ast.walk(case.pattern):
                    if isinstance(node, (ast.MatchAs, ast.MatchStar)) and node.name:
                        case_env[node.name] = UNKNOWN
                if case.guard is not None:
                    self._test(case.guard, case_env)
                self._block(case.body, case_env)
                if not self._ends(case.body):
                    branches.append(case_env)
            self._merge(env, env, *branches)
        elif isinstance(s, ast.Raise):
            if s.exc is not None:
                self._expr(s.exc, env)
        elif isinstance(s, ast.Assert):
            self._test(s.test, env)
        elif isinstance(s, ast.With):
            for item in s.items:
                self._expr(item.context_expr, env)
            self._block(s.body, env)
        elif isinstance(s, ast.FunctionDef):
            # 入れ子の関数: 引数は未確認として本体を検査し、戻り値の状態を名前に結びつける
            inner = dict(env)
            for arg in _all_args(s):
                inner[arg.arg] = UNKNOWN
            nested = _FunctionCheck(self.guard, _Unit(self.unit.module, self.unit.owner, s), "nested", {},
                                    self.summaries, self.calls, self.found, self.report)
            nested.local_functions = dict(self.local_functions)
            nested.local_functions[s.name] = BOTTOM
            nested._block(s.body, inner)
            if not nested._ends(s.body):
                nested._returns(CLEAN)
            self.local_functions[s.name] = nested.returned

    def _loop(self, s: Any, env: Dict[str, str], enter: Any, loop_env: Dict[str, str]) -> None:
        """ループの本体を 2 回辿る（2 回目は 1 回目の終わりと `continue` の状態から）。抜けた後は、入る前・
        本体の終わり・`continue`・`break`・`else` の状態の合流。"""

        self._continues.append([])
        self._breaks.append([])
        enter(loop_env)
        self._block(s.body, loop_env)
        for _ in range(2):
            self._merge(loop_env, loop_env, *self._continues[-1])
            enter(loop_env)
            self._block(s.body, loop_env)
        self._merge(loop_env, loop_env, *self._continues.pop())
        breaks = self._breaks.pop()
        else_env = dict(env)
        self._merge(else_env, env, loop_env)
        self._block(s.orelse, else_env)
        self._merge(env, env, loop_env, else_env, *breaks)

    def _key(self, e: ast.AST, env: Dict[str, str], node: ast.AST) -> None:
        if not self._compare_ok(self.state(e, env)):
            self.flag(node, "hash")

    def _test(self, e: ast.AST, env: Dict[str, str]) -> None:
        if isinstance(e, ast.BoolOp):
            scope = env
            for value in e.values:
                self._test(value, scope)
                scope = self._narrowed(value, scope, positive=isinstance(e.op, ast.And))
            return
        if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.Not):
            self._test(e.operand, env)
            return
        state = self.state(e, env)
        if not self._truth_ok(state):
            self.flag(e, f"truthiness of {state}")
        self._expr(e, env)

    def _comprehension_env(self, e: Any, env: Dict[str, str], *, check: bool) -> Dict[str, str]:
        inner = dict(env)
        for generator in e.generators:
            if check:
                self._expr(generator.iter, inner)
            iterated = self.state(generator.iter, inner)
            if check and not is_container(iterated) and iterated not in (CLEAN, BOTTOM, LEAF):
                self.flag(generator.iter, f"iteration of {iterated}")
            if check:
                self._unpack(generator.target, element_of(iterated) if iterated != CLEAN else CLEAN, generator.iter)
            self._bind(generator.target, element_of(iterated) if iterated != CLEAN else CLEAN, inner)
            for condition in generator.ifs:
                if check:
                    self._test(condition, inner)
                inner = self._narrowed(condition, inner)
        return inner

    def _ordering(self, call: ast.Call, name: str, states: List[str], env: Dict[str, str]) -> None:
        """`sorted` / `min` / `max` が比べる値（`key=` があれば key の結果）が clean か。"""

        key = next((k.value for k in call.keywords if k.arg == "key"), None)
        if key is None:
            compared = element_of(states[0]) if len(states) == 1 else BOTTOM
            if len(states) > 1:
                for state in states:
                    compared = meet(compared, state)
            if not self._compare_ok(compared):
                self.flag(call, f"{name}() compares {compared}")
            return
        element = element_of(states[0]) if len(states) == 1 else UNKNOWN
        if isinstance(key, ast.Lambda):
            inner = dict(env)
            for arg in key.args.args:
                inner[arg.arg] = element
            self._expr(key.body, inner)
            result = self.state(key.body, inner)
        elif isinstance(key, ast.Name) and self.guard._resolve(self.module, key.id) is not None:
            target = self.guard._resolve(self.module, key.id)
            self.found[target.key] = target
            self.guard.edges.add((self.unit.label, target.label))
            self.calls.setdefault(target.key, []).append(({0: element}, {}))
            result = self.summaries.get(target.key, BOTTOM)
        else:
            result = UNKNOWN
        if not self._compare_ok(result):
            self.flag(call, f"{name}() key compares {result}")

    def _expr(self, e: ast.AST, env: Dict[str, str]) -> None:
        if isinstance(e, ast.BoolOp):
            scope = env
            for value in e.values[:-1]:
                self._test(value, scope)
                scope = self._narrowed(value, scope, positive=isinstance(e.op, ast.And))
            self._expr(e.values[-1], scope)
        elif isinstance(e, ast.UnaryOp):
            if isinstance(e.op, ast.Not):
                self._test(e.operand, env)
            else:
                if not self._value_ok(self.state(e.operand, env)):
                    self.flag(e, "arithmetic")
                self._expr(e.operand, env)
        elif isinstance(e, ast.IfExp):
            self._test(e.test, env)
            self._expr(e.body, self._narrowed(e.test, env))
            self._expr(e.orelse, self._narrowed(e.test, env, positive=False))
        elif isinstance(e, ast.Compare):
            if not all(isinstance(op, (ast.Is, ast.IsNot)) for op in e.ops):
                operands = (e.left, *e.comparators)
                for index, operand in enumerate(operands):
                    state = self.state(operand, env)
                    if state == LEAF:
                        # 葉だけを写した値: scalar の定数（と定数の tuple / list への `in`）との比較は要素を読まない
                        others = [o for o in operands if o is not operand]
                        # 定数の tuple / list は `in` の右だけ（`==` の右なら容器どうしの比較で要素を読む）
                        in_literal = len(e.ops) == 1 and isinstance(e.ops[0], (ast.In, ast.NotIn)) and operand is e.left
                        if all(
                            _scalar_constant(o)
                            or (in_literal and isinstance(o, (ast.Tuple, ast.List)) and all(_scalar_constant(x) for x in o.elts))
                            for o in others
                        ):
                            continue
                        self.flag(e, "comparison of leaf")
                        break
                    container_side = index > 0 and isinstance(e.ops[index - 1], (ast.In, ast.NotIn))
                    if container_side:
                        state = element_of(state) if is_container(state) else state
                    if not self._compare_ok(state):
                        self.flag(e, f"comparison of {state}")
                        break
            for operand in (e.left, *e.comparators):
                self._expr(operand, env)
        elif isinstance(e, ast.BinOp):
            left, right = self.state(e.left, env), self.state(e.right, env)
            set_op = isinstance(e.op, (ast.BitOr, ast.BitAnd, ast.Sub, ast.BitXor)) and is_container(left) and is_container(right)
            if set_op and not (self._compare_ok(element_of(left)) and self._compare_ok(element_of(right))):
                self.flag(e, "set operation hashes " + meet(as_seq(left), as_seq(right)))
            container = set_op or (
                is_container(left) and (is_container(right) or (right == CLEAN and isinstance(e.op, ast.Mult)))
                and isinstance(e.op, (ast.Add, ast.Mult))
            )
            if not container:
                for state in (left, right):
                    if state == LEAF and not isinstance(e.op, ast.Mod):
                        continue  # 容器と数の算術は要素を読まない（`%` は文字列化し得る）
                    if not self._value_ok(state):
                        self.flag(e, f"arithmetic on {state}")
                        break
            self._expr(e.left, env)
            self._expr(e.right, env)
        elif isinstance(e, ast.JoinedStr):
            for value in e.values:
                if isinstance(value, ast.FormattedValue):
                    if not self._value_ok(self.state(value.value, env)):
                        self.flag(value, "format")
                    self._expr(value.value, env)
        elif isinstance(e, (ast.Set, ast.Dict)):
            if isinstance(e, ast.Dict):
                for k, v in zip(e.keys, e.values):
                    if k is None:  # `{**x}`: mapping の key と値を読む
                        state = self.state(v, env)
                        if not state.startswith("map:") and state not in (CLEAN, BOTTOM):
                            self.flag(e, f"unpacking of {state}")
            keys = e.elts if isinstance(e, ast.Set) else [k for k in e.keys if k is not None]
            if any(not self._compare_ok(self.state(k, env)) for k in keys):
                self.flag(e, "hash")
            for item in (e.elts if isinstance(e, ast.Set) else [*keys, *e.values]):
                self._expr(item, env)
        elif isinstance(e, (ast.ListComp, ast.GeneratorExp, ast.SetComp, ast.DictComp)):
            inner = self._comprehension_env(e, env, check=True)
            if isinstance(e, ast.SetComp) and not self._compare_ok(self.state(e.elt, inner)):
                self.flag(e, "hash")
            if isinstance(e, ast.DictComp):
                if not self._compare_ok(self.state(e.key, inner)):
                    self.flag(e, "hash")
                self._expr(e.key, inner)
                self._expr(e.value, inner)
            else:
                self._expr(e.elt, inner)
        elif isinstance(e, ast.Call):
            callee = e.func
            name = callee.id if isinstance(callee, ast.Name) else ""
            self.state(e, env)  # 結果を読まない呼び出しも辿る（引数の状態を呼び先へ渡す）
            states = [self.state(a, env) for a in e.args]
            if name in ORDERING_BUILTINS and states:
                self._ordering(e, name, states, env)
            elif name in ("set", "frozenset", "dict") and states:
                if not self._compare_ok(element_of(states[0]) if is_container(states[0]) else states[0]):
                    self.flag(e, f"{name}() hashes {states[0]}")
            elif name in ("sum", "any", "all") and states:
                element = element_of(states[0]) if is_container(states[0]) else states[0]
                ok = self._value_ok(element) if name == "sum" else self._truth_ok(element)
                if not ok:
                    self.flag(e, f"{name}() of {states[0]}")
            elif ast.unparse(callee) == "json.dumps" and states:
                if not self._value_ok(states[0]):
                    self.flag(e, f"json.dumps() of {states[0]}")  # key の並べ替え・値の repr
            elif name in ("len", *CONTAINER_BUILTINS) and name != "range" and states:
                for state in states:
                    if not is_container(state) and state not in (CLEAN, BOTTOM, LEAF):
                        self.flag(e, f"{name}() iterates {state}")  # `__len__` / `__iter__` は値の型の code
                        break
            elif name == "bool" and states:
                if not self._truth_ok(states[0]):
                    self.flag(e, f"bool() of {states[0]}")
            elif name in CONSUMING_BUILTINS:
                for state in states:
                    if state == LEAF and name in ("int", "float", "abs", "round", "divmod", "pow"):
                        continue  # 数への変換は容器なら例外（要素を読まない）
                    if not self._value_ok(state):
                        self.flag(e, f"{name}() of {state}")
                        break
            if isinstance(callee, ast.Attribute) and isinstance(callee.value, ast.Name) and callee.value.id in BUILTIN_TYPES:
                pass  # 基底型の slot の実装
            elif isinstance(callee, ast.Attribute) and callee.attr in SCALAR_METHODS:
                base = self.state(callee.value, env)
                if base not in (CLEAN, LEAF) and not base.startswith(("seq:", "ref:", "class:")):
                    self.flag(e, f"method {callee.attr}() on {base}")
                elif callee.attr == "join" and base == CLEAN and states and not self._value_ok(states[0]):
                    self.flag(e, f"join() of {states[0]}")
                elif callee.attr == "format" and base == CLEAN:
                    # `"{}".format(x)`: 引数を文字列にする（`__format__`）
                    for state in states + [self.state(k.value, env) for k in e.keywords]:
                        if not self._value_ok(state):
                            self.flag(e, f"format() of {state}")
                            break
            if isinstance(callee, ast.Attribute) and callee.attr in ("add", "setdefault", "get", "pop", "discard", "remove"):
                container = self.state(callee.value, env)
                if is_container(container) and e.args and not self._compare_ok(states[0]):
                    self.flag(e, "hash")  # set / dict の key（hash と `==`）
            if isinstance(callee, ast.Attribute) and callee.attr == "sort":
                base = self.state(callee.value, env)
                if is_container(base) and not any(k.arg == "key" for k in e.keywords) and not self._compare_ok(element_of(base)):
                    self.flag(e, f"sort() compares {element_of(base)}")
                elif not is_container(base) and base not in (CLEAN, BOTTOM):
                    self.flag(e, f"sort() on {base}")
            if isinstance(callee, ast.Attribute) and callee.attr in ("index", "count", "remove") and e.args:
                base = self.state(callee.value, env)
                if is_container(base) and not (self._compare_ok(element_of(base)) and self._compare_ok(states[0])):
                    self.flag(e, f"{callee.attr}() compares {base}")
            if isinstance(callee, ast.Attribute):
                self._expr(callee.value, env)
            for a in e.args:
                self._expr(a, env)
            for k in e.keywords:
                if k.arg == "key" and name in ORDERING_BUILTINS:
                    continue  # `_ordering` が本体を検査した
                if isinstance(k.value, ast.Lambda):
                    inner = dict(env)
                    for arg in k.value.args.args:
                        inner[arg.arg] = UNKNOWN
                    self._expr(k.value.body, inner)
                else:
                    self._expr(k.value, env)
        elif isinstance(e, ast.Subscript):
            base = self.state(e.value, env)
            if is_container(base) and not isinstance(e.slice, ast.Slice) and not self._compare_ok(self.state(e.slice, env)):
                self.flag(e, "hash")  # dict の key / list の添字（`__index__`）
            if not is_container(base) and base not in (CLEAN, BOTTOM, LEAF):
                self.flag(e, f"subscript of {base}")
            self._expr(e.value, env)
            self._expr(e.slice, env)
        elif isinstance(e, ast.Attribute):
            self._expr(e.value, env)
        elif isinstance(e, (ast.Tuple, ast.List)):
            for item in e.elts:
                self._expr(item, env)
        elif isinstance(e, ast.Starred):
            state = self.state(e.value, env)
            if not is_container(state) and state not in (CLEAN, BOTTOM, LEAF):
                self.flag(e, f"unpacking of {state}")  # `*x` は反復する
            self._expr(e.value, env)
        elif isinstance(e, ast.NamedExpr):
            self._expr(e.value, env)
            env[e.target.id] = self.state(e.value, env)
        elif isinstance(e, ast.Lambda):
            inner = dict(env)
            for arg in e.args.args:
                inner[arg.arg] = UNKNOWN
            self._expr(e.body, inner)


#: 構文から安全と言えないが、scalar の契約の外として受理する消費（理由つき。field / 引数の scalar ではない）
ACCEPTED: Dict[str, str] = {
    "_reading.py:items: tuple() iterates unknown: tuple(value)":
        "組み込みの列・scalar でない iterable（generator・deque など）の反復は置き換える前と同じくその object の code"
        "（scalar の subclass はその前の分岐が基底型の値で読む）",
    "pcode.py:_local_op_ordinal_from_parent: comparison of unknown: candidate == pcode_op":
        "Ghidra の PcodeOp object どうしの等しさ（Java の equals）。scalar ではなく、ref の field にも入らない",
}
