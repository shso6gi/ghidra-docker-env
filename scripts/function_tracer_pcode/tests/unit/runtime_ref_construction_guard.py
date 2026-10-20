# -*- coding: utf-8 -*-
"""runtime ref の構築の経路が、外の値を **安全な読み方でだけ** 消費することを確かめる静的な解析（Issue #242）。

構築の契約: ref の構築（`__post_init__`・自前の `__init__`・factory と `@runtime_ref_entry` の入口）と、ref module の
**外から呼べるすべての** 関数・method・property（公開の名前と、外の module が import する `_` の名前。引数の有無、
ref の class かどうかに依らない）、およびそこから **実際に到達する** 関数は、scalar の subclass の code
（`__bool__` / `__eq__` / `__hash__` / `__format__` / `__str__` / 算術 / 文字列の method / `__int__` / `__len__` /
`__iter__` など）を呼ばない。外の値は消費の前に `live_values` などの reader（import した名前だけを信用する）で読む。

**値の状態**（文字列で表す）:

- `clean`: 組み込みの値、または葉まで組み込みの値の容器（定数、`scalar_*` の結果、owner が写した scalar の field、
  写した引数、比較や `not` の結果）
- `tree`: `exact_tree` の結果（組み込みの木）。容器と scalar の葉は組み込みの型そのもの、それ以外の葉は読んでいない
  外の object。真偽・数への変換・反復は `clean` と同じ。属性・method の結果は `foreign`（object を読んだことを、その先で
  API から取得する値の安全の根拠にしない）。**不活性でない**: 比較・`in`・並べる・hash の容器（dict の key・set の
  要素）は、葉の外の object の `__eq__` / `__lt__` の戻り値を C が真偽で読む（暗黙の callback）ので違反
  （`live_values.equal` / `unequal` / `contains` / `less` / `sorted_trees` / `inert_key` で読む）。`str` / `repr` /
  `format` / 1 つの値だけの f-string / `abs` / `round` / `sum` の結果は葉の callback の戻り値なので `foreign`
  （`scalar_text` / `scalar_repr` で読む）。注釈が scalar / bool の field と入口の引数も `tree`（owner は scalar の
  subclass だけを写し、外の object はそのまま残る）
- `leaf`: 葉だけを写した値（`exact_scalar` / `exact_field_value` の結果）。scalar の subclass ではないが、外の object
  かもしれない。真偽・数への変換・反復はよい。比較（定数との比較・定数の容器への `in` を含む）・文字列化・hash は違反。
  method の結果は `foreign`
- `imported`: 外の module から import した名前（Ghidra の class など）。値ではない: 属性・method の読みはよく、
  結果は `foreign`
- `scalar?`: `isinstance(x, str)` などで絞った値（subclass かもしれない）。葉の reader で読むと clean
- `seq:<要素>` / `tup:[位置ごと]` / `map:[key, 値]`: 組み込みの容器（真偽・長さ・反復・連結は要素の code を呼ばない）
- `ref:C`: ref の class C の本物の instance（`self`、構築の結果、`type(x) is C` で絞った値）。field は構築を終えた
  後の値（scalar / bool は owner が写した値、検証が書き直した field は書き直した値の状態）。method は本体を辿る
- `nref:C`: `is_kind(x, C)`（と `isinstance`）で絞った値（C か C の subclass の instance）。field は `ref:C` と同じ、method は
  subclass が上書きし得るので本体（C の code）を検査し、結果は未確認
- `typed:C`: 注釈が C で、scalar の subclass ではないと分かっている値（入口が写した record の引数・本物の
  instance の record の field・`attribute_of` / 葉の reader で読んだ値）。代わりの型かもしれない: scalar の属性は
  未確認、tuple の field は `uncertain:`（容器かどうかも未確認: reader で読むと容器）、method / property は本体を
  検査するが結果は外の code の結果（`foreign`）
- `rtyped:C`: 注釈が C なだけの値（写していない引数・list のまま受理したかもしれない tuple の field の要素）。
  scalar の subclass かもしれないので、属性は `attribute_of` で読む（そのほかは `typed:C` と同じ）
- `obj:C`: ref でない class（`ExpansionBudgetCollector` など）の instance。`__init__` で組み込みの容器を置いた属性は
  容器（要素はその class の method が入れた値の meet）、それ以外の属性は未確認
- `unknown`: 上のどれでもない（消費すると違反）

**外の code の結果**（`foreign`）: 注釈だけの値・`is_kind` で絞った値・外の object の method と property、正体の
分からない callable の戻り値。消費は `unknown` と同じ。加えて **読まずに ref の層の外へ出すと違反**: 外から呼べる
関数の戻り値（`runtime_ref_key` の key の出口は owner が組み込みの木にするので除く。ただし出口で写さない
`runtime_ref_key(proven=True)` の key は除かず、さらに本体の戻り値の状態が clean でなければ違反）、ref の構築の引数のうち owner
が読まない field（分類が scalar / bool / record の field と、検証がどの経路でも reader で書き直す field は owner が
読む）、`object.__setattr__` で置く値。

**消費として数えるもの**: 真偽、`is` 以外の比較・`in`・`match`、算術・累算代入、f-string・`str` / `repr` /
`format` / `"...".format()` / `json.dumps`、`*x` / `**x` の展開、set / dict の `add` / `get` / `setdefault` の key、集合・dict の key（hash）、文字列・整数の method、組み込みの変換・集計、`sorted` / `min` / `max` /
`list.sort` が比べる値（`key=` の結果を含む）、`len` / `tuple` / `list` / 反復 / 組への代入（`__len__` / `__iter__`）、
ref の `==` / hash（比べる field に未確認の値を持ち得る class）。値の型の code を呼ぶ読み: 未確認の値
（`unknown` / `foreign` / `scalar?` / `rtyped:` / `uncertain:`）の属性（`x.a` / `getattr`）と `isinstance`（`type(x)` が
型の subclass でなければ `x.__class__` を値の `__getattribute__` で読む）、確かめていない値の型の属性
（`type(x).__name__` は metaclass の `__getattribute__`）、未確認の値の method の名前の読み（`x.m()` の `x.m`）。
それぞれ `attribute_of` / `is_kind` / `type_name` / `type_module` / `defined_attribute` / `method_of`（`method_of(x, "m")(...)`） で読む。
`with x`（`__enter__`）・`yield from x`（反復）・`del d[x]`（hash）、package の中でこの解析が辿らない module の関数
（`core/signature` など）と `import` した module の関数（`json.dumps` / `hashlib` を除く）へ読まずに渡すこと。
`nonlocal` / `global`、`globals()` / `vars()` / `locals()` / `exec` / `eval` / `__import__` は追わない束縛なので、
使うと違反。値の型の code を呼ぶ組み込み（`hasattr` / `setattr` / `delattr` / `dir` など: 個別の規則と読みだけの組み込み
を除く）、`issubclass`（基底の `__subclasscheck__` が値の型の属性を読む: `is_kind` を使う）、`type(x)(...)`、未確認の
値の属性への書き込み、`except` で照合する未確認の値、`from x import f`（標準の library など）の関数・局所の名前に
束縛した正体の分からない callable・呼び出しが返した callable（`method_of(x, "m")` を含む）へ読まずに渡すこと、
f-string の入れ子の format の指定も消費。入れ子の class の本体・async の本体・入れ子の関数の既定値と decorator・
`except*` / `type` 文は解析しないので、使うと違反。module は `from __future__ import annotations`（注釈を評価しない）が
要る。組み込みの容器どうし・clean な値と容器の連結（`+`）は要素を読まない。

**reader の識別**: reader を定義する module から import した名前と、`live_values` の module の名前だけを reader と
して信用する。その名前を module の名前空間で束縛し直したもの（定義・代入・別の import・`for` / `with` / `except` の
target・関数の中の `global`）と、関数の中で同じ名前の局所変数・引数が隠すもの（名前の形・module の形の両方）は
reader ではない。

**到達**: 同じ module の関数、import した ref module の関数、**到達した package の module（依存先: `core/signature`
など。ref module でも reader でもないもの）の関数**（起点にはしないが、到達した関数は同じ規則で検査する。名前の形・
module の形（`dep.f(...)`）・再 export・module の名前空間の `name = lambda` を辿る）、**呼び出し以外の位置で参照
される関数**（別名・表・値として渡す・`getattr` で読む module の関数: どこから何で呼ばれるか追えないので、引数を
未確認とした起点として検査する）、入れ子の関数、
別の呼び出しの引数の中の呼び出し、
`self.m()` / `cls.m()` / `C.m()`、`ref:C` / `typed:C` / `obj:C` の値の method と property。戻り値の状態は本体の
`return` / `yield` の meet、引数の状態は呼び出し元の実引数（と既定値）の meet（fixpoint）。外から呼べる関数の
引数は注釈の状態（入口なら写した後の状態）から始める。制御の流れは分岐ごとに追い、`continue` / `break` の状態は
繰り返しの先頭とループの後へ流す（`return` / `raise` だけが経路を終える）。

**限界**（PASS をこれ以上の保証と読まない）:

- 容器の変異は名前（と ref でない class の自分の属性）への `append` / `add` / `insert` / `extend` / `update` /
  `setdefault` / 添字の代入を追う。別名に代入した・関数に渡した・入れ子の関数が参照する、変異できる容器（list /
  dict / set の表示・内包・constructor で束縛した名前）は、関数全体で要素を未確認として扱う（flow によらない）。`getattr` は定数の
  名前だけを追い、`setattr` / `exec` / 動的な名前は追わない。
- method は `self` / `cls` が C（の instance）のときの C の code として検査し、`self.m()` / `cls.m()` は C の `m`
  を辿り、`self` の field は owner が写した値として扱う。ref の class を継承して method・field（setter 付きの
  property）・`__getattribute__` を上書きした型の instance を `self` として走る C の code は対象外（Python では
  上書きを封じられず、method の結果だけを読んでも field の読みが残る。package に ref の class の subclass は無い）。
  引数・field など `self` 以外の位置に来る subclass の instance は対象（`typed:` / `rtyped:` / `nref:` の規則）。
  `C.method(代わりの型)` のように class から外の object を渡して呼ぶ使い方も対象外。`ref:C` の field は構築のときの値として扱う（後から
  `object.__setattr__` で書き換えた値は追わない）。
- `exact_tree` の結果は `tree` として扱う（消費は clean と同じ、属性・method の結果は foreign）: 容器は組み込みの
  型そのもの、scalar の葉は組み込みの型そのもの
  （`live_values.exact_tree` の保証。外の constructor / `_make` を呼ばない）。辿らない値は scalar でも組み込みの容器
  （subclass・named tuple・`deque`・dict の view を含む）でもない object（外の code: その `__eq__` / `repr` などは
  検査しない。`OrderedDict` の view は反復が key を hash するので `exact_tree` が拒む（`TypeError`）。`MappingProxyType` / `UserList` / `ChainMap` は中身を写さずに残る: その `repr` は中の値の `repr` を呼ぶ）だけ。
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
#: 葉だけを写した値（`exact_scalar` の結果）: scalar の subclass ではないが、外の object かもしれない。真偽・数への
#: 変換はよい。比較（定数との `==` / `in` を含む）は外の object の `__eq__` を呼び、その戻り値の真偽を C が読む
#: （暗黙の callback: 不活性でない値の比較は `equal` / `contains` で読む）。文字列化・hash は要素の code を呼び得る
LEAF = "leaf"
#: 外の code（注釈だけの値・`isinstance` で絞った値・外の object の method、正体の分からない callable）が返した値。
#: 消費は `unknown` と同じ。加えて、読まずに ref の層の外へ出す（外から呼べる関数の戻り値・ref の構築の引数・
#: field への書き込み）と違反（外の constructor / method は作り直すときに scalar の subclass を混ぜ得る）
FOREIGN = "foreign"
CONTAINER = "seq:unknown"
#: 標準の library・外の package（Ghidra の class など）から `from x import Name` した名前: 値ではない（scalar の
#: subclass ではない）。属性・method の読みはよいが、その結果は外の code の結果（`foreign`）
IMPORTED = "imported"
#: `exact_tree` の結果（組み込みの木）: 容器は組み込みの型そのもの、scalar の葉は組み込みの型そのもの、それ以外の葉は
#: 外の object（読んでいない）。変換・文字列化・真偽は `clean` と同じ。ただし属性・method の結果（外の object が API から
#: 返す値）は外の code の結果（`foreign`）: object を読んだことを、その先で取得する値の安全の根拠にしない。比較・
#: hash の容器（dict の key・set の要素）・並べることは **不活性でない** 値の扱い（葉の外の object の `__eq__` / `__lt__`
#: の戻り値を C が真偽で読む: 暗黙の callback）。`equal` / `contains` / `less` / `sorted_trees` / `inert_key` で読む
TREE = "tree"

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
    "builtin_str", "builtin_sequence", "size", "scalar_int_or", "is_json_record", "type_name", "type_module",
    "is_kind", "materialize", "defined_attribute", "holds_scalar_subclass", "scalar_repr", "exception_text",
    # 比べる側の契約（`live_values` の比較・所属・順序）: 暗黙の callback の戻り値を基底型の値の真偽で読む
    "equal", "unequal", "same", "contains", "less", "truth", "inert", "inert_key", "hash_tree", "deciding",
    "undecided_is_absent", "package_instance",
})
#: 比べた結果の並びを返す reader（要素は組み込みの木: 葉の外の object は読んでいない）
TREE_SEQUENCE_READERS = frozenset({"sorted_trees"})
#: 出力の記述を作る `json_encoding` の関数（`_Source`: 値は `json_encoding` が書くときに読む）
JSON_SOURCES = frozenset({"each", "inline", "raw", "mapping_of", "as_list", "as_dict", "pairs_of", "nested"})
#: 値を「組み込みの容器（要素は未確認）」にする reader
CONTAINER_READERS = frozenset({"builtin_items", "elements_of", "elements_within_limit"})
#: 値を「比べてよい容器」にする reader（組み込みの tuple / list を辿り、scalar の subclass の葉を基底型の値にする）
TREE_READERS = frozenset({"exact_tree"})
#: 個別の規則で判定する組み込み（`_expr` / `state` の中）
HANDLED_BUILTINS = frozenset({
    "getattr", "hasattr", "setattr", "delattr", "issubclass", "len", "print", "next", "iter", "super", "object",
    "globals", "vars", "locals", "exec", "eval", "__import__", "NotImplementedError", "staticmethod", "classmethod",
    "property",
})
#: 解析しない文（版によっては無い構文）
_UNTRACKED_STATEMENTS = tuple(getattr(ast, name) for name in ("TryStar", "TypeAlias") if hasattr(ast, name))
#: 動的な束縛・名前空間の書き換え（追わない: 使うと違反）
UNTRACKED_CALLS = frozenset({"globals", "vars", "locals", "exec", "eval", "__import__"})
#: 組み込みの容器の型（`isinstance(x, tuple)` などで絞ると、反復・長さ・真偽は組み込みの振る舞い）
CONTAINER_TYPES = frozenset({"tuple", "list", "dict", "set", "frozenset", "Mapping"})
#: どの値に当てても外の型の code を呼ばない組み込み
SAFE_ANY = frozenset({"isinstance", "callable", "id", "type"})
#: 値の型の code を呼ぶ・属性を読む組み込み（引数が clean / 確かめた値でなければ違反。上の組と個別の規則のものを除く）
import builtins as _builtins
BUILTIN_NAMES = frozenset(name for name in dir(_builtins) if not name.startswith("_"))
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
        or (isinstance(d, ast.Call) and _decorated(ast.FunctionDef(decorator_list=[d.func]), names))
        for d in node.decorator_list
    )


def _proven_key(node: Any) -> bool:
    """`@runtime_ref_key(proven=True)`: 出口で写さない key（本体の戻り値が clean であることを guard が確かめる）。"""

    return any(
        isinstance(d, ast.Call) and _decorated(ast.FunctionDef(decorator_list=[d.func]), {"runtime_ref_key"})
        and any(k.arg == "proven" and isinstance(k.value, ast.Constant) and k.value.value is True for k in d.keywords)
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


def _holds_tree(state: str) -> bool:
    """状態が `exact_tree` の結果（葉に外の object を持ち得る木）を含むか。"""

    if state == TREE:
        return True
    if state.startswith("seq:"):
        return _holds_tree(state[4:])
    if state.startswith("tup:"):
        return any(_holds_tree(item) for item in tup_items(state))
    if state.startswith("map:"):
        return any(_holds_tree(part) for part in map_parts(state))
    return False


def clean_tree(state: str) -> bool:
    """組み込みの値と、葉まで組み込みの値の容器。"""

    if state in (CLEAN, BOTTOM, TREE):
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
    return "seq:" * depth + ((TREE if TREE in state else CLEAN) if clean_tree(state) else UNKNOWN)


def meet(a: str, b: str) -> str:
    """2 つの経路の状態の合流（悪い方へ寄せる）。`clean` と容器・ref の合流は容器・ref（`None` との合流）。"""

    return widen(_meet(a, b))


def _meet(a: str, b: str) -> str:
    if a == b:
        return a
    if TREE in (a, b):
        other = b if a == TREE else a
        if clean_tree(other):
            return TREE  # 組み込みの値・木との合流は木（葉に外の object があり得る）
    if (FOREIGN in a or FOREIGN in b) and not (is_container(a) and is_container(b)):
        # 外の code の結果を含む値: 由来を落とさない（消費は unknown と同じ、出口で違反）。組み込みの容器どうしは
        # 容器のまま（要素の状態で由来を持つ）
        if a in (BOTTOM, CLEAN) or b in (BOTTOM, CLEAN):
            return b if a in (BOTTOM, CLEAN) else a
        return FOREIGN
    if {a, b} == {LEAF, CLEAN}:
        return LEAF
    if a == BOTTOM:
        return b
    if b == BOTTOM:
        return a
    if a == CLEAN and b.startswith(("seq:", "tup:", "map:", "ref:", "nref:", "typed:", "rtyped:")):
        return b
    if b == CLEAN and a.startswith(("seq:", "tup:", "map:", "ref:", "nref:", "typed:", "rtyped:")):
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
        if x.startswith("ref:") and y in (f"typed:{x[4:]}", f"nref:{x[4:]}", f"rtyped:{x[4:]}"):
            return y
        if x.startswith("nref:") and y in (f"typed:{x[5:]}", f"rtyped:{x[5:]}"):
            return y
        if x.startswith("typed:") and y == f"rtyped:{x[6:]}":
            return y
    return UNKNOWN


def element_of(state: str) -> str:
    if state == TREE:
        return TREE
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


def _module_bindings(tree: ast.Module) -> Set[str]:
    """module の名前空間を reader の import 以外で束縛する名前（定義・代入・import・`for` / `with` / `except` /
    walrus の target、関数の中の `global` 宣言）。関数・class の本体の中の束縛（`global` を除く）は数えない。"""

    names: Set[str] = set()

    def visit(node: ast.AST, top: bool) -> None:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if top:
                names.add(node.name)
            for child in ast.walk(node):
                if isinstance(child, ast.Global):
                    names.update(child.names)
            return
        if top and isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
            names.add(node.id)
        if top and isinstance(node, ast.ExceptHandler) and node.name:
            names.add(node.name)
        if top and isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                reader_import = isinstance(node, ast.ImportFrom) and (
                    node.module in READER_MODULES
                    or (node.module == "scripts.function_tracer_pcode.core" and alias.name == "live_values")
                )
                if not reader_import:
                    names.add((alias.asname or alias.name).split(".")[0])
        for child in ast.iter_child_nodes(node):
            visit(child, top)

    for statement in tree.body:
        visit(statement, True)
    return names


class _Module:
    def __init__(self, name: str, tree: ast.Module, ref_module_names: Set[str]):
        self.name = name
        self.tree = tree
        self.functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
        # module の名前空間の `name = lambda ...` も関数として辿る（本体は 1 つの式の `return`）
        for node in tree.body:
            if (
                isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                and isinstance(node.value, ast.Lambda) and node.targets[0].id not in self.functions
            ):
                body = ast.Return(value=node.value.body)
                function = ast.FunctionDef(name=node.targets[0].id, args=node.value.args, body=[body], decorator_list=[], returns=None)
                ast.copy_location(body, node.value.body)
                ast.copy_location(function, node)
                function.type_comment = None
                self.functions[function.name] = function
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
                self.reader_modules.update(
                    alias.asname or alias.name for alias in node.names
                    if f"scripts.function_tracer_pcode.core.{alias.name}" in READER_MODULES
                )
        # module の名前空間で束縛し直した名前は reader ではない（関数の中の局所変数は呼び出しのときに env で見分ける）
        defined = _module_bindings(tree)
        # reader の名前と reader の module の名前を同じ名前に束縛した import も、どちらも信用しない
        defined |= self.reader_names & self.reader_modules
        self.reader_names -= defined
        self.reader_modules -= defined
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
        #: package の中で、この解析が辿らない module（ref module でも reader でもない）から import した名前
        self.outside_names: Set[str] = set()
        #: package の module（reader でない）から import した名前: 名前 → (module, 名前)。到達したら辿る（依存先）
        self.package_imports: Dict[str, Tuple[str, str]] = {}
        #: `import x` で束縛した module の名前（標準の library など）
        self.module_names: Set[str] = set()
        #: 標準の library などから `from x import name` した関数（引数は読んでから渡す）
        self.stdlib_names: Set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.module in ref_module_names:
                for alias in node.names:
                    self.imports[alias.asname or alias.name] = (node.module, alias.name)
            elif (
                isinstance(node, ast.ImportFrom) and node.module
                and node.module.startswith("scripts.function_tracer_pcode.")
                and node.module not in READER_MODULES
            ):
                self.outside_names.update(alias.asname or alias.name for alias in node.names)
                for alias in node.names:
                    self.package_imports[alias.asname or alias.name] = (node.module, alias.name)
            elif isinstance(node, ast.Import):
                self.module_names.update((alias.asname or alias.name).split(".")[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module and not node.module.startswith("scripts.") and node.module not in (
                "__future__", "typing", "dataclasses", "enum", "collections.abc",
            ):
                self.stdlib_names.update(alias.asname or alias.name for alias in node.names)
        #: package の module（reader でない）を束縛した名前: 名前 → module（`dep.f(...)` を辿る）
        self.package_modules: Dict[str, str] = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name.startswith("scripts.function_tracer_pcode.") and alias.name not in READER_MODULES and alias.asname:
                        self.package_modules[alias.asname] = alias.name
            elif isinstance(node, ast.ImportFrom) and node.module and node.module.startswith("scripts.function_tracer_pcode"):
                for alias in node.names:
                    full = f"{node.module}.{alias.name}"
                    if full not in READER_MODULES:
                        # module かどうかは guard が読めるかで決める（`from pkg import func` の関数は読めない）
                        self.package_modules[alias.asname or alias.name] = full
        #: 呼び出し以外の位置で参照する関数の名前・package の module の名前（別名・表・値として渡す: どこから何で
        #: 呼ばれるか追えない）。guard はその関数を起点（引数は未確認）として検査する
        callee_ids = {id(node.func) for node in ast.walk(tree) if isinstance(node, ast.Call)}
        callee_ids |= {
            id(node.func.value) for node in ast.walk(tree)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name)
        }
        self.escaping: Set[str] = {
            node.id for node in ast.walk(tree)
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load) and id(node) not in callee_ids
        }
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

    def __init__(
        self, sources: Dict[str, str], world: RefWorld, external: Iterable[str] = (),
        dependency_sources: Optional[Dict[str, str]] = None,
    ):
        self.world = world
        #: 依存先の source（test が与える。無ければ package の file を読む）
        self.dependency_sources = dict(dependency_sources or {})
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
        #: 到達して足した依存先の module（`core/signature` など）
        self.dependencies: Set[str] = set()
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
        for module in [m for name, m in self.modules.items() if name not in self.dependencies]:
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

        return [v for v in self._module_violations() + self._violations if v.rsplit(" (line ", 1)[0] not in ACCEPTED]

    def _module_violations(self) -> List[str]:
        """module の規則: 注釈を評価しない（`from __future__ import annotations`）。評価する注釈の式は解析しない。"""

        out = []
        for module_name, module in self.modules.items():
            future = any(
                isinstance(node, ast.ImportFrom) and node.module == "__future__"
                and any(alias.name == "annotations" for alias in node.names)
                for node in module.tree.body
            )
            has_code = any(isinstance(node, (ast.FunctionDef, ast.ClassDef)) for node in module.tree.body)
            if has_code and not future:
                out.append(f"{module_name.rsplit('.', 1)[-1]}.py:<module>: annotations are evaluated (line 1)")
        return out

    def accepted(self) -> List[str]:
        return [v for v in self._violations if v.rsplit(" (line ", 1)[0] in ACCEPTED]

    def reached(self) -> List[str]:
        return list(self._reached)

    # -- 名前の解決 ----------------------------------------------------------------------------------

    def _escaped_units(self) -> List[_Unit]:
        """呼び出し以外の位置で参照される関数（別名・表・値として渡す関数・`getattr` で読む module の関数）。"""

        out = []
        for module in list(self.modules.values()):
            for name in module.escaping:
                if name in module.reader_names or name in module.reader_modules:
                    continue
                if name in module.package_modules and self._load_dependency(module.package_modules[name]):
                    target = self.modules[module.package_modules[name]]
                    out.extend(_Unit(target.name, None, function) for function in target.functions.values())
                    continue
                unit = self._resolve(module, name)
                if unit is not None:
                    out.append(unit)
        return out

    def _load_dependency(self, module_name: str) -> bool:
        """到達した package の module（ref module・reader でない依存先）を解析の対象に足す（起点にはしない: 到達した
        関数だけを辿る）。source が無ければ足さない（呼ぶ側は辿れない呼び先として扱う）。"""

        if module_name in self.modules:
            return True
        path = PACKAGE.parents[1].joinpath(*module_name.split(".")).with_suffix(".py")
        if module_name in self.dependency_sources:
            text = self.dependency_sources[module_name]
        elif module_name.startswith("scripts.function_tracer_pcode.") and path.exists():
            text = path.read_text()
        else:
            return False
        module = _Module(module_name, ast.parse(text), set(self.modules) | {module_name})
        self.modules[module_name] = module
        self.dependencies.add(module_name)
        for node in module.record_classes + module.plain_classes:
            self.class_modules.setdefault(node.name, module_name)
            if node in module.plain_classes:
                self.plain_classes.add(node.name)
        return True

    def _resolve(self, module: _Module, name: str, depth: int = 0) -> Optional[_Unit]:
        if name in module.functions:
            return _Unit(module.name, None, module.functions[name])
        target = module.imports.get(name) or module.package_imports.get(name)
        if target is not None and target[0] not in self.modules:
            self._load_dependency(target[0])
        if (
            target is not None and target[0] in self.modules and target[1] not in self.modules[target[0]].functions
            and depth < 8
        ):
            # 再 export（`from dep2 import f as g` を import した名前）: 定義した module まで辿る
            return self._resolve(self.modules[target[0]], target[1], depth + 1)
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
        for module in [m for name, m in self.modules.items() if name not in self.dependencies]:
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
            for unit in self._escaped_units():
                if roles.get(unit.key) != "external" and roles.get(unit.key) not in ("entry", "construct"):
                    units[unit.key] = unit
                    roles[unit.key] = "external"  # どこから何で呼ばれるか追えない: 引数は未確認
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
        for key, unit in units.items():
            if _proven_key(unit.function) and not clean_tree(summaries.get(key, BOTTOM)):
                # 出口で写さない key は、本体がどの経路でも読み終えた値（clean / 組み込みの木）を返すこと
                report.append(
                    f"{unit.module.rsplit('.', 1)[-1]}.py:{unit.function.name}: proven key returns {summaries.get(key)}: "
                    f"{unit.function.name} (line {unit.function.lineno})"
                )
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


def _callee_name(call: ast.Call) -> str:
    func = call.func
    return func.id if isinstance(func, ast.Name) else func.attr if isinstance(func, ast.Attribute) else ""


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
        #: 変異を追えない名前（別名に代入した・関数に渡した・入れ子の関数が参照する）: その名前の容器の要素は未確認
        self.escaped: Set[str] = set()
        #: 見つけた ref でない class の自分の容器への追加（`(class, attr)` → 要素の状態）
        self.plain_found: Dict[Tuple[str, str], str] = {}
        self._continues: List[List[Dict[str, str]]] = []
        self._breaks: List[List[Dict[str, str]]] = []
        self.returned = BOTTOM
        #: `__post_init__` を抜けたときの `self.<field>` の状態
        self.exit_fields: Dict[str, str] = {}
        self.generator = any(isinstance(n, (ast.Yield, ast.YieldFrom)) for n in ast.walk(unit.function))

    # -- 入口 ---------------------------------------------------------------------------------------

    def _escaping_names(self, function: ast.AST) -> Set[str]:
        """変異を追えない名前（flow によらない）: `a = b` の両方、呼び出しの引数に渡す名前（reader・組み込みの読み・
        自分の容器の method を除く）、入れ子の関数・lambda が参照する外の名前。"""

        names: Set[str] = set()
        reading = READERS | LEAF_READERS | CONTAINER_READERS | TREE_READERS | TREE_SEQUENCE_READERS | CONSUMING_BUILTINS | CONTAINER_BUILTINS | SAFE_ANY | {
            "len", "getattr", "hasattr", "method_of", "attribute_of", "attribute",
        }
        for node in ast.walk(function):
            if isinstance(node, ast.Assign) and isinstance(node.value, ast.Name):
                names.add(node.value.id)
                names.update(t.id for t in node.targets if isinstance(t, ast.Name))
            elif isinstance(node, ast.Call):
                func = node.func
                callee = func.id if isinstance(func, ast.Name) else func.attr if isinstance(func, ast.Attribute) else ""
                if callee in reading:
                    continue
                for argument in [*node.args, *(k.value for k in node.keywords)]:
                    argument = argument.value if isinstance(argument, ast.Starred) else argument
                    if isinstance(argument, ast.Name):
                        names.add(argument.id)
            elif node is not function and isinstance(node, (ast.FunctionDef, ast.Lambda)):
                inner_args = {a.arg for a in _all_args(node)}
                for inner in ast.walk(node):
                    if isinstance(inner, ast.Name) and inner.id not in inner_args:
                        names.add(inner.id)
        # 変異できる容器を束縛した名前だけ（list / dict / set の表示・内包と、その組み込みの constructor）
        mutable: Set[str] = set()
        for node in ast.walk(function):
            if isinstance(node, (ast.Assign, ast.AnnAssign)) and node.value is not None:
                value = node.value
                if isinstance(value, (ast.List, ast.Dict, ast.Set, ast.ListComp, ast.DictComp, ast.SetComp)) or (
                    isinstance(value, ast.Call) and isinstance(value.func, ast.Name) and value.func.id in ("list", "dict", "set")
                ):
                    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                    mutable.update(t.id for t in targets if isinstance(t, ast.Name))
        return names & mutable

    def run(self) -> None:
        env: Dict[str, str] = {}
        function = self.unit.function
        self.escaped = self._escaping_names(function)
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
                env[arg.arg] = "seq:" + TREE if normalized and self._annotation_state(arg.annotation, normalized=True) == TREE else CONTAINER
            else:
                env[arg.arg] = self._annotation_state(arg.annotation, normalized=normalized)
        if self.role == "construct":
            # 検証の前に owner が写した field（検証が書き直すと、その状態で上書きする）
            for field in self.world.classes.get(self.unit.owner or "", {}):
                env[f"self.{field}"] = self._field(self.unit.owner, field, proven=True, after_validation=False)
        for node in ast.walk(function):
            # 解析しない構文: 入れ子の class の本体・async の本体・既定値と decorator の式（定義のときに評価される）
            if node is not function and isinstance(node, (ast.ClassDef, ast.AsyncFunctionDef, *_UNTRACKED_STATEMENTS)):
                self.flag(node, f"{type(node).__name__} is not tracked")
            elif isinstance(node, (ast.FunctionDef, ast.Lambda)) and node is not function and (
                node.args.defaults or any(d is not None for d in node.args.kw_defaults)
                or (isinstance(node, ast.FunctionDef) and node.decorator_list)
            ):
                self.flag(node, "defaults or decorators of a nested function are not tracked")
            # 動的な束縛・名前空間の書き換え（どの文の中でも: 代入の target の中を含む）。reader の識別を崩す
            if (
                isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in UNTRACKED_CALLS
                and node.func.id not in env
            ):
                self.flag(node, f"{node.func.id}() is not tracked")
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
            # 注釈だけ（呼び出し元は代わりの型を渡せる）。入口は scalar の subclass を写す（`record` の規則）
            return f"typed:{bare}" if normalized else f"rtyped:{bare}"
        for name in self.world.classes:
            if bare in (f"Tuple[{name},...]", f"tuple[{name},...]"):
                return f"seq:rtyped:{name}" if normalized else CONTAINER
        if not normalized:
            return UNKNOWN
        # `runtime_ref_entry` が写した引数（owner の分類と同じ: scalar / bool / tuple）。owner は scalar の subclass を基底型の
        # 値に、型の誤りの容器を組み込みの木にするが、外の object（scalar でない値）はそのまま: 状態は field と同じ `tree`
        # （比べると葉の外の object の callback の戻り値を読む。Issue #242 第 6 回）
        if bare in ("int", "str", "bool", "float"):
            return TREE
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
        if _decorated(target.function, {"runtime_ref_key"}) and not _proven_key(target.function):
            return CLEAN  # key の出口は owner が組み込みの木にして返す（`runtime_ref_key`）
        return self.summaries.get(target.key, BOTTOM)

    # -- 値の状態 -----------------------------------------------------------------------------------

    def state(self, e: ast.AST, env: Dict[str, str]) -> str:
        if isinstance(e, ast.Constant):
            return CLEAN
        if isinstance(e, ast.Name):
            if e.id in env:
                state = env[e.id]
                if e.id in self.escaped and (state.startswith(("seq:", "map:"))):
                    return CONTAINER  # 別名・呼び先・入れ子の関数を通した変異は追わない: 要素は未確認
                return state
            if e.id in self.world.classes:
                return f"class:{e.id}"
            if e.id in self.module.constants:
                return self.module.constants[e.id]
            if e.id in self.module.stdlib_names:
                return IMPORTED
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
            if isinstance(e.op, ast.Add) and CLEAN in (left, right) and (is_container(left) or is_container(right)):
                return meet(CLEAN_CONTAINER, as_seq(left if is_container(left) else right))
            return UNKNOWN
        if isinstance(e, ast.IfExp):
            return meet(self.state(e.body, self._narrowed(e.test, env)), self.state(e.orelse, env))
        if isinstance(e, ast.JoinedStr):
            # 1 つの値だけの f-string（`f"{x}"`）は `__format__` の戻り値そのもの（str の subclass かもしれない）。
            # 文字列の定数を含むなら、組み込みの code が部分を読んで作った組み込みの `str`
            if len(e.values) == 1 and isinstance(e.values[0], ast.FormattedValue):
                inner = self.state(e.values[0].value, env)
                if not (clean_tree(inner) and not _holds_tree(inner)):
                    return FOREIGN
            return CLEAN
        if isinstance(e, ast.Subscript):
            base = self.state(e.value, env)
            if isinstance(e.slice, ast.Slice):
                return as_seq(base) if is_container(base) else UNKNOWN
            if base == CLEAN:
                return CLEAN  # 組み込みの文字列の 1 文字
            if base == TREE:
                return TREE  # 組み込みの木の要素
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
            inner = f"seq:rtyped:{info.element}" if info.element and info.element != "scalar" else CONTAINER
            return "uncertain:" + inner
        if proven and after_validation:
            post = self.guard.post_states.get(owner, {}).get(name)
            if info.kind in ("scalar", "bool"):
                return TREE  # owner が写した値（型の誤りの容器は組み込みの木: 葉に外の object があり得る）
            if post is not None and post != BOTTOM:
                if info.kind == "tuple" and not is_container(post) and post not in (CLEAN, TREE):
                    post = CONTAINER
                return post
        if info.ref:
            # record の field の値は注釈どおりとは限らない（代わりの型）。本物の instance の field は owner が scalar の
            # subclass を写した値（`typed`: 属性を読んでよい）、代わりの型の属性は何でもあり得る（`rtyped`）
            return f"typed:{info.ref}" if proven else f"rtyped:{info.ref}"
        if info.kind == "tuple":
            if info.element and info.element != "scalar":
                # 要素は list のまま受理した値かもしれない（owner は list を写さない）: 属性は reader で読む
                return f"seq:rtyped:{info.element}"
            return CONTAINER  # exact な tuple の葉は写すが、list のまま受理した値の要素は写さない
        if proven and info.kind in ("scalar", "bool"):
            return TREE  # 本物の instance の scalar の field は owner が写した値
        return UNKNOWN

    def _attribute(self, e: ast.Attribute, env: Dict[str, str], *, default: Optional[ast.AST] = None) -> str:
        on_self = isinstance(e.value, ast.Name) and e.value.id == "self"
        if on_self and f"self.{e.attr}" in env:
            return env[f"self.{e.attr}"]
        return self._attribute_of(self.state(e.value, env), e.attr, env)

    def _attribute_of(self, base: str, name: str, env: Dict[str, str]) -> str:
        if base == IMPORTED:
            return FOREIGN  # import した class / 関数の属性: 外の code の値
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
                return FOREIGN
            if target is not None:
                return f"tbound:{owner}.{name}"
            return UNKNOWN
        if base.startswith(("typed:", "rtyped:")):
            base = "typed:" + base.split(":", 1)[1]
            found = self._field(base[6:], name, proven=False)
            if found is not None:
                return found
            target = self.guard.method(base[6:], name)
            if target is not None and _decorated(target.function, {"property"}):
                self._follow(target, None, env)  # 本物なら package の code が走る: 本体は検査する
                return FOREIGN  # 代わりの型なら外の code: 結果は未確認
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
        if base == TREE:
            return FOREIGN  # 木の葉の外の object の属性（API の値）: 読んでいない
        return UNKNOWN

    def _reader_call(self, node: ast.AST, reader: str, env: Dict[str, str]) -> bool:
        """`node` が import した reader `reader` の呼び出しか（名前の形・module の形。局所の名前が隠すものは除く）。"""

        if not isinstance(node, ast.Call):
            return False
        func = node.func
        if isinstance(func, ast.Name):
            return func.id == reader and func.id in self.module.reader_names and func.id not in env
        return (
            isinstance(func, ast.Attribute) and func.attr == reader and isinstance(func.value, ast.Name)
            and func.value.id in self.module.reader_modules and func.value.id not in env
        )

    def _call(self, call: ast.Call, env: Dict[str, str]) -> str:
        callee = call.func
        if self._reader_call(callee, "method_of", env) and len(callee.args) == 2:
            # `method_of(x, "m")(...)`: 名前は葉を写してから読む。本物なら package の code が走るので本体を辿り、
            # 結果は外の code の結果
            target = self.state(callee.args[0], env)
            if target.startswith("rtyped:"):
                target = "typed:" + target[len("rtyped:"):]
            if isinstance(callee.args[1], ast.Constant) and target.startswith(("ref:", "nref:", "typed:", "obj:")):
                found = self._attribute_of(target, callee.args[1].value, env)
                if found.startswith("bound:"):
                    self._call_bound(found, call, env)
                elif found.startswith("tbound:"):
                    self._call_bound("bound:" + found[len("tbound:"):], call, env)
            return FOREIGN
        name = callee.id if isinstance(callee, ast.Name) else callee.attr if isinstance(callee, ast.Attribute) else ""
        through_owner = (isinstance(callee, ast.Name) and name in self.module.reader_names and name not in env) or (
            isinstance(callee, ast.Attribute) and isinstance(callee.value, ast.Name)
            and callee.value.id in self.module.reader_modules and callee.value.id not in env
        )
        if through_owner and name == "attribute_of" and len(call.args) >= 2:
            # 葉を写してから読む属性: 値は scalar の subclass ではない（`rtyped` は `typed`、未確認の値の属性は外の値）
            target = self.state(call.args[0], env)
            if target.startswith("rtyped:"):
                target = "typed:" + target[len("rtyped:"):]
            if not isinstance(call.args[1], ast.Constant):
                return FOREIGN
            found = self._attribute_of(target, call.args[1].value, env)
            if len(call.args) == 3:
                found = meet(found, self.state(call.args[2], env))
            return found
        if through_owner and name in JSON_SOURCES:
            return CLEAN  # 出力の記述（`json_encoding` の `_Source`）。中の値は書くときに reader が読む
        if through_owner and name == "items_of":
            return "seq:" + make_tup([UNKNOWN, UNKNOWN])  # 組み込みの mapping の (key, 値): 中身は未確認
        if through_owner and name == "method_of":
            return FOREIGN  # 葉を写してから読んだ属性（呼ぶ前の method）: 外の code
        if through_owner and name in CONTAINER_READERS:
            argument = self.state(call.args[0], env) if call.args else UNKNOWN
            if argument.startswith("uncertain:"):
                return argument[len("uncertain:"):]
            return argument if is_container(argument) and name != "elements_within_limit" else CONTAINER
        if through_owner and name in TREE_READERS:
            return TREE  # 組み込みの木（形は分からない: 反復・添字は木、属性・method の結果は外の code）
        if through_owner and name in TREE_SEQUENCE_READERS:
            return "seq:" + TREE  # 並べた木の list（比べた順。要素の葉の外の object は読んでいない）
        if through_owner and name in LEAF_READERS:
            argument = self.state(call.args[0], env) if call.args else UNKNOWN
            if argument == MAYBE_SCALAR:
                return CLEAN
            if argument.startswith("rtyped:"):
                return "typed:" + argument[len("rtyped:"):]  # 葉を写した値は scalar の subclass ではない
            return argument if clean_tree(argument) or argument.startswith(("ref:", "nref:", "typed:")) else LEAF
        if through_owner and name in READERS:
            return CLEAN
        if isinstance(callee, ast.Name):
            if name in SAFE_ANY or name == "hasattr":
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
                if name in ("int", "float", "bool", "len", "hash") and inner and all(clean_tree(s) or s == LEAF for s in inner):
                    # 結果は組み込みの値そのもの（`__int__` / `__float__` が返す subclass は CPython が組み込みの値へ写し、
                    # `__bool__` は `bool` を返すことを強制され、`__len__` / `__hash__` の戻り値は C が基底型の値で読む）
                    return CLEAN
                if all(clean_tree(s) and not _holds_tree(s) for s in inner):
                    return CLEAN  # 不活性な値だけ: 組み込みの code の結果
                if all(clean_tree(s) or s == LEAF for s in inner):
                    # 葉の外の object の callback（`__str__` / `__repr__` / `__format__` / `__abs__` / `__round__` /
                    # `__add__` など）が返した値: scalar の subclass かもしれない（暗黙の callback の戻り値）
                    return FOREIGN
                return UNKNOWN
            if name in self.local_functions:
                return self.local_functions[name]
            target = self.guard._resolve(self.module, name)
            if target is not None:
                return self._follow(target, call, env)
            state = env.get(name, "")
            if state.startswith("bound:"):
                return self._call_bound(state, call, env)
            return FOREIGN  # 正体の分からない callable（`getattr` で取った method など）の戻り値
        if isinstance(callee, ast.Attribute):
            if (
                isinstance(callee.value, ast.Name) and callee.value.id in self.module.package_modules
                and callee.value.id not in env and callee.value.id not in self.module.reader_modules
            ):
                # package の module の関数（`dep.f(...)`）: 依存先として辿る。辿れなければ外の code
                module_name = self.module.package_modules[callee.value.id]
                if self.guard._load_dependency(module_name):
                    unit = self.guard._resolve(self.guard.modules[module_name], callee.attr)
                    if unit is not None:
                        return self._follow(unit, call, env)
                    return FOREIGN
            if isinstance(callee.value, ast.Name) and callee.value.id in BUILTIN_TYPES:
                return CLEAN  # 基底型の slot の実装（subclass の上書きを呼ばない）
            if ast.unparse(callee) == "json.dumps":
                return CLEAN  # 引数の消費は `_expr` が見る
            if ast.unparse(callee).startswith("hashlib."):
                return CLEAN  # 標準の hash の object と、その `hexdigest()` の組み込みの `str`
            base = self.state(callee.value, env)
            if base.startswith(("ref:", "nref:", "typed:", "rtyped:", "obj:")):
                found = self._attribute_of(base, callee.attr, env)
                if found.startswith("bound:"):
                    return self._call_bound(found, call, env)
                if found.startswith("tbound:"):
                    # 注釈だけの値の method: 本物なら package の code が走るので本体を検査し、結果は未確認
                    self._call_bound("bound:" + found[len("tbound:"):], call, env)
                    return FOREIGN
                return FOREIGN  # field の値（Any）の呼び出し
            if base.startswith("class:"):
                target = self.guard.method(base[6:], callee.attr)
                if target is not None:
                    return self._follow(target, call, env)
                return UNKNOWN
            if base == CLEAN:
                return CLEAN  # clean な値（組み込みの値）の method
            if base == TREE:
                return FOREIGN  # 木の葉の外の object の method（API の戻り値）: 読んでから消費する
            if base == LEAF:
                return FOREIGN  # 基底型の str なら基底型の method だが、外の object なら外の code の結果（読んでから消費する）
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
            return FOREIGN  # API の戻り値・外の object（`typed:C` を含む）の method の戻り値
        return UNKNOWN

    def _call_bound(self, bound: str, call: ast.Call, env: Dict[str, str]) -> str:
        owner, name = bound[len("bound:"):].split(".", 1)
        target = self.guard.method(owner, name)
        return self._follow(target, call, env) if target is not None else UNKNOWN

    def _argument_states(self, call: ast.Call, env: Dict[str, str]) -> List[str]:
        return [
            self.state(a.value if isinstance(a, ast.Starred) else a, env) for a in [*call.args, *(k.value for k in call.keywords)]
        ]

    def _call_consumption(self, call: ast.Call, callee: ast.AST, name: str, env: Dict[str, str]) -> None:
        """呼び出しが引数の値の型の code を呼ぶか（組み込み・標準 library の関数・正体の分からない callable）。"""

        states = self._argument_states(call, env)
        if isinstance(callee, ast.Name) and name not in env and name not in self.module.reader_names:
            if name in ("hasattr", "setattr", "delattr") and states and self._attribute_read_unsafe(states[0]):
                self.flag(call, f"attribute of {states[0]}")  # `getattr` と同じ（値の型の `__getattribute__` など）
            elif name == "issubclass":
                # 基底の metatype の `__subclasscheck__`（ABC）は値の型の属性を読む: `is_kind` で判定する
                first = call.args[0] if call.args else None
                if not (isinstance(first, ast.Name) and first.id in BUILTIN_TYPES):
                    self.flag(call, "issubclass reads the class of a value (use is_kind)")
            elif name in self.module.stdlib_names:
                for state in states:
                    if not self._value_ok(state):
                        self.flag(call, f"passes {state} to {name}")
            elif (
                name in BUILTIN_NAMES and name not in SAFE_ANY and name not in CONSUMING_BUILTINS
                and name not in CONTAINER_BUILTINS and name not in HANDLED_BUILTINS
                and name not in self.world.classes and name not in self.module.functions
                and name not in self.local_functions and name not in self.module.imports
            ):
                for state in states:
                    if not self._value_ok(state) and not is_container(state):
                        self.flag(call, f"{name}() of {state}")
        elif isinstance(callee, ast.Call) and isinstance(callee.func, ast.Name) and callee.func.id == "type" and callee.func.id not in env:
            if callee.args and not self._value_ok(self.state(callee.args[0], env)):
                self.flag(call, f"constructs the type of {self.state(callee.args[0], env)}")  # 値の型の constructor
        elif (isinstance(callee, ast.Name) and name in env and env[name] in (FOREIGN, UNKNOWN)) or isinstance(callee, ast.Call):
            # 局所の名前に束縛した正体の分からない callable・呼び出しが返した callable（`method_of(x, "m")` を含む）:
            # 外の code へ渡す値は読んでから渡す
            for state in states:
                if not self._value_ok(state) and not state.startswith(("ref:", "nref:", "typed:", "obj:", "class:")):
                    self.flag(call, f"passes {state} to foreign code")

    def _method_receiver(self, call: ast.Call, callee: ast.Attribute, env: Dict[str, str]) -> None:
        """`x.m(...)` の `x.m` の読み: 属性の読みと同じく、未確認の値・確かめていない値の型の属性は違反。"""

        receiver = callee.value
        if isinstance(receiver, ast.Name) and receiver.id not in env and (
            receiver.id in self.module.reader_modules or receiver.id in BUILTIN_TYPES
        ):
            return  # reader の module・組み込みの型の slot
        if isinstance(receiver, ast.Name) and receiver.id not in env and receiver.id in self.module.module_names:
            if ast.unparse(callee) not in ("json.dumps",) and not ast.unparse(callee).startswith("hashlib."):
                for argument in [*call.args, *(k.value for k in call.keywords)]:
                    state = self.state(argument.value if isinstance(argument, ast.Starred) else argument, env)
                    if not self._value_ok(state):
                        self.flag(call, f"passes {state} to {ast.unparse(callee)}")
            return
        if (
            isinstance(receiver, ast.Call) and isinstance(receiver.func, ast.Name) and receiver.func.id == "type"
            and receiver.args and not self._value_ok(self.state(receiver.args[0], env))
        ):
            self.flag(call, f"type attribute of {self.state(receiver.args[0], env)}")
            return
        state = self.state(receiver, env)
        if self._attribute_read_unsafe(state):
            # method の名前の読みは値の型の `__getattribute__` / `__getattr__`（`attribute_of(x, "m")(...)` で読む）
            self.flag(call, f"method of {state}")

    #: owner が構築のときに読む field の分類（scalar の subclass は基底型の値: `exact_field_value`）。tuple の field は
    #: tuple の木だけを写し、list・object の要素は読まない。object の field は読まない
    _OWNER_READ_KINDS = frozenset({"scalar", "bool", "record"})

    def _stores_foreign(self, call: ast.Call, name: str, env: Dict[str, str]) -> bool:
        """ref の構築の引数に、owner が読まない位置へ渡す外の code の結果があるか。"""

        callee = call.func
        args = list(call.args)
        if isinstance(callee, ast.Name) and name == "replace":
            target = self.state(args[0], env) if args else UNKNOWN
            owner = target.split(":", 1)[1] if target.startswith(("ref:", "nref:", "typed:", "rtyped:")) else None
            args = args[1:]
        elif isinstance(callee, ast.Name) and name == "cls":
            owner = self.unit.owner
        elif isinstance(callee, ast.Name):
            owner = name
        else:
            owner = self.state(callee.value, env)[len("class:"):]
        fields = self.world.classes.get(owner or "", {})
        order = list(fields)
        posts = self.guard.post_states.get(owner or "", {})

        def read_by_owner(field: Optional[str]) -> bool:
            info = fields.get(field) if field is not None else None
            if info is not None and info.kind in self._OWNER_READ_KINDS:
                return True
            # 検証（`__post_init__`）がどの経路でも reader で書き直す field（書き直した値の状態が clean）
            post = posts.get(field) if field is not None else None
            return post is not None and post != BOTTOM and clean_tree(post)

        for index, argument in enumerate(args):
            if isinstance(argument, ast.Starred):
                if FOREIGN in self.state(argument.value, env):
                    return True
                continue
            field = order[index] if index < len(order) else None
            if FOREIGN in self.state(argument, env) and not read_by_owner(field):
                return True
        for keyword in call.keywords:
            if FOREIGN in self.state(keyword.value, env) and not read_by_owner(keyword.arg):
                return True
        return False

    # -- 消費の判定 ----------------------------------------------------------------------------------

    @staticmethod
    def _attribute_read_unsafe(state: str) -> bool:
        """属性を読むと scalar の subclass の code（`__getattribute__` / class の descriptor）を呼び得る値か。"""

        return state in (UNKNOWN, FOREIGN, MAYBE_SCALAR) or state.startswith(("rtyped:", "uncertain:"))

    @staticmethod
    def _truth_ok(state: str) -> bool:
        return state in (CLEAN, BOTTOM, LEAF, TREE) or state.startswith(("seq:", "tup:", "map:", "ref:", "nref:", "class:", "bound:", "classattr:"))

    def _compare_ok(self, state: str) -> bool:
        """`==` / `in` / 順序 / hash の容器に渡してよい値: 不活性な値（組み込みの値と、葉まで組み込みの値の容器）と ref。

        `exact_tree` の結果（`tree`）・葉だけを写した値（`leaf`）は不活性でない（葉の外の object の比較の戻り値を C が
        真偽で読む）。ref の `==` は owner の `__eq__`（`live_values.equal`）か、guard が本体を検査する class 自身の `__eq__`、
        hash は比べる field の値の hash（戻り値は C が基底型の値で読む）。
        """

        if (clean_tree(state) and not _holds_tree(state)) or state.startswith(("class:", "classattr:")):
            return True
        if state.startswith(("ref:", "nref:")):
            return True
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
            positive and isinstance(t, ast.Call) and len(t.args) == 2 and isinstance(t.args[0], ast.Name)
            and _callee_name(t) == "package_instance" and isinstance(t.args[1], ast.Name)
            and t.args[1].id in self.world.classes
        ):
            # `live_values.package_instance(x, C)`: `type(x) is C` で、C の今の信頼も確かめた（Issue #242 第 11 回）
            out[t.args[0].id] = f"ref:{t.args[1].id}"
        elif (
            positive and isinstance(t, ast.Call) and len(t.args) == 2 and isinstance(t.args[0], ast.Name)
            and _callee_name(t) in ("isinstance", "is_kind")
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
                out[t.args[0].id] = CLEAN if current in (CLEAN, LEAF, TREE) else MAYBE_SCALAR
        elif (
            isinstance(t, ast.Compare) and len(t.ops) == 1
            and isinstance(t.ops[0], ast.Is if positive else ast.IsNot)  # `type(x) is C` が成り立つ側
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

        if isinstance(target, (ast.Tuple, ast.List)) and not is_container(state) and state not in (CLEAN, BOTTOM, TREE):
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

    def _attribute_targets(self, s: ast.stmt, env: Dict[str, str]) -> None:
        """`x.a = v` / `del x.a` / `x.a += v`: 未確認の値の属性への書き込みは値の型の `__setattr__` / descriptor。"""

        targets = s.targets if isinstance(s, (ast.Assign, ast.Delete)) else [s.target]
        for target in targets:
            for node in ast.walk(target):
                if isinstance(node, ast.Attribute) and isinstance(node.ctx, (ast.Store, ast.Del)):
                    base = self.state(node.value, env)
                    if self._attribute_read_unsafe(base):
                        self.flag(node, f"attribute store on {base}")

    def _statement(self, s: ast.stmt, env: Dict[str, str]) -> None:
        if isinstance(s, (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Delete)):
            self._attribute_targets(s, env)
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
            if not is_container(iterated) and iterated not in (CLEAN, BOTTOM, LEAF, TREE):
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
                if handler.type is not None:
                    # 例外の照合は型の `__subclasscheck__` を呼ぶ: 照合する型は class の名前か、その tuple だけ
                    # （module の名前空間の class の名前・`module.Class` だけ。局所の名前・式の値は未確認）
                    for node in (handler.type.elts if isinstance(handler.type, ast.Tuple) else [handler.type]):
                        named = (isinstance(node, ast.Name) and node.id not in env) or (
                            isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id not in env
                        )
                        if not named:
                            self.flag(handler, "except matches an unread value")
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
                state = self.state(s.value, env)
                if (
                    FOREIGN in state and self.role in ("entry", "external", "construct")
                    and not (_decorated(self.unit.function, {"runtime_ref_key"}) and not _proven_key(self.unit.function))
                ):
                    self.flag(s, "returns an unread result of foreign code")
                self._returns(state, env)
            else:
                self._returns(CLEAN, env)
        elif isinstance(s, ast.Expr):
            value = s.value
            if isinstance(value, (ast.Yield, ast.YieldFrom)):
                if value.value is not None:
                    self._expr(value.value, env)
                    state = self.state(value.value, env)
                    if isinstance(value, ast.YieldFrom) and not is_container(state) and state not in (CLEAN, BOTTOM, LEAF, TREE):
                        self.flag(value, f"yield from iterates {state}")  # `__iter__` は値の型の code
                    self._returns("seq:" + (element_of(state) if isinstance(value, ast.YieldFrom) else state))
                return
            self._expr(value, env)
            if (
                isinstance(value, ast.Call) and ast.unparse(value.func) == "object.__setattr__" and len(value.args) == 3
                and FOREIGN in self.state(value.args[2], env)
            ):
                self.flag(value, "stores an unread result of foreign code")
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
                state = self.state(item.context_expr, env)
                if not self._value_ok(state):
                    self.flag(item.context_expr, f"with of {state}")  # `__enter__` / `__exit__` は値の型の code
                if item.optional_vars is not None:
                    for name in ast.walk(item.optional_vars):
                        if isinstance(name, ast.Name):
                            env[name.id] = FOREIGN  # `__enter__` の戻り値
            self._block(s.body, env)
        elif isinstance(s, ast.Delete):
            for target in s.targets:
                if isinstance(target, ast.Subscript):
                    self._expr(target.value, env)
                    self._expr(target.slice, env)
                    key = self.state(target.slice, env)
                    if not self._compare_ok(key):
                        self.flag(target, f"del hashes {key}")  # dict の key・list の添字（`__index__`）
                elif isinstance(target, ast.Name):
                    env.pop(target.id, None)
        elif isinstance(s, (ast.Nonlocal, ast.Global)):
            # 外の scope への代入は追わない: 使わない（追わない束縛で状態を失わない）
            self.flag(s, f"{type(s).__name__.lower()} is not tracked")
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
            if check and not is_container(iterated) and iterated not in (CLEAN, BOTTOM, LEAF, TREE):
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
            ) or (
                # clean な値（組み込みの値・木）と組み込みの容器の連結: 連結は要素を読まない（型が違えば TypeError）
                isinstance(e.op, ast.Add) and CLEAN in (left, right) and (is_container(left) or is_container(right))
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
                    if value.format_spec is not None:
                        self._expr(value.format_spec, env)  # 入れ子の format の指定も文字列化する
        elif isinstance(e, (ast.Set, ast.Dict)):
            if isinstance(e, ast.Dict):
                for k, v in zip(e.keys, e.values):
                    if k is None:  # `{**x}`: mapping の key と値を読む
                        state = self.state(v, env)
                        if not state.startswith("map:") and state not in (CLEAN, BOTTOM, TREE):
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
            if isinstance(callee, ast.Attribute):
                self._method_receiver(e, callee, env)
            self._call_consumption(e, callee, name, env)
            if (
                isinstance(callee, ast.Name) and name in self.module.outside_names and name not in env
                and self.guard._resolve(self.module, name) is None
            ):
                # package の中でこの解析が辿らない関数（`core/signature` など）: 渡す値は読んでから渡す
                for argument in [*e.args, *(k.value for k in e.keywords)]:
                    state = self.state(argument.value if isinstance(argument, ast.Starred) else argument, env)
                    if not self._value_ok(state):
                        self.flag(e, f"passes {state} to package code outside the guard")
            if name == "isinstance" and e.args and self._attribute_read_unsafe(self.state(e.args[0], env)):
                # `type(x)` が型の subclass でなければ `x.__class__` を値の `__getattribute__` で読む: `is_kind` を使う
                self.flag(e, f"isinstance reads the class of {self.state(e.args[0], env)}")
            if name == "getattr" and e.args and self._attribute_read_unsafe(self.state(e.args[0], env)):
                self.flag(e, f"attribute of {self.state(e.args[0], env)}")
            builds_ref = (isinstance(callee, ast.Name) and (name in self.world.classes or name in ("cls", "replace"))) or (
                isinstance(callee, ast.Attribute) and self.state(callee.value, env).startswith("class:")
            )
            if builds_ref and self._stores_foreign(e, name, env):
                self.flag(e, "stores an unread result of foreign code")  # ref の構築へ読まずに渡す
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
            elif ast.unparse(callee).startswith("hashlib.") and states:
                for state in states:
                    if state not in (CLEAN, BOTTOM, TREE):
                        self.flag(e, f"hashlib reads {state}")  # buffer の読み（`bytes` の subclass の `__buffer__`）
            elif name in ("len", *CONTAINER_BUILTINS) and name != "range" and states:
                for state in states:
                    if not is_container(state) and state not in (CLEAN, BOTTOM, LEAF, TREE):
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
                if base not in (CLEAN, LEAF, TREE) and not base.startswith(("seq:", "ref:", "class:")):
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
                elif not is_container(base) and base not in (CLEAN, BOTTOM, TREE):
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
            if not is_container(base) and base not in (CLEAN, BOTTOM, LEAF, TREE):
                self.flag(e, f"subscript of {base}")
            self._expr(e.value, env)
            self._expr(e.slice, env)
        elif isinstance(e, ast.Attribute):
            base = self.state(e.value, env)
            if (
                isinstance(e.value, ast.Call) and isinstance(e.value.func, ast.Name) and e.value.func.id == "type"
                and e.value.args and not self._value_ok(self.state(e.value.args[0], env))
            ):
                # `type(x).__name__` などは型の metaclass の `__getattribute__` を呼ぶ: `type_name` / `type_module`
                self.flag(e, f"type attribute of {self.state(e.value.args[0], env)}")
            if self._attribute_read_unsafe(base):
                self.flag(e, f"attribute of {base}")  # 値の型の `__getattribute__` / descriptor（scalar の subclass かもしれない）
            self._expr(e.value, env)
        elif isinstance(e, (ast.Tuple, ast.List)):
            for item in e.elts:
                self._expr(item, env)
        elif isinstance(e, ast.Starred):
            state = self.state(e.value, env)
            if not is_container(state) and state not in (CLEAN, BOTTOM, LEAF, TREE):
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
}
