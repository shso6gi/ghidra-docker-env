# -*- coding: utf-8 -*-
"""atom の語彙と妥当性の判定（Issue #215 SN3: 構造 identity と solver の identity が共有する唯一の規則）。

値は `core/semantic_projection.canonical_atom` が 1 回の走査で **型・対応を落とさない atom**
（exact な str / int だけを中身に持つ tuple の木）に読む。この module は、その atom が

* identified — 値を識別する（`id()` だけの印・型名だけの印・exact でない中身・識別不能 token を、
  `canonical_atom` に何重に包まれていても含まない）
* placeholder_free — 構造 key の placeholder（打ち切り・閉路・opaque・識別不能）を含まない
* comparable — identified で placeholder_free、しかも process の中でだけ意味を持つ token を含まない

かを判定する（`atom_validity`）。判定は値の型を読まない: atom の形だけを照合する。

同一性の **規則** は consumer ごとに別で、この module は持たない:

* 構造 identity（`core/structural`）は comparable な atom だけを比較可能な key に入れ、identified で
  ない atom は毎回新しい識別不能 token に置き換える
* solver の symbol identity（`core/semantic_projection.identity_value` → 条件 oracle・SMT 宣言・
  provenance）は identified かつ placeholder_free な atom だけを identity に使う（process の中だけの
  token は同じ process の中では同じものを指すので、symbol の共有に使ってよい）

tag の語彙（構造 key の token・placeholder・値を識別しない印）の定義もここに置く: 構造 key の
token を作るのは `core/structural` だが、token が別の値の中に入って runtime ref の key として
戻ってくると、projection の判定も同じ語彙で読む必要がある。
"""

from __future__ import annotations

from typing import Any, NamedTuple, Tuple

from scripts.function_tracer_pcode.core import live_values


#: 識別済みの tail token の tag
EXACT_TAIL_TAG = "exact_tail"
#: 識別できない token の tag（C-K5）
UNIDENTIFIED_TAG = "exact_tail_unidentified"
#: object identity fallback の token の tag（`expression_key_or_identity`）
PROCESS_OBJECT_TAG = "process_object"
#: record の bytes を厳密比較で intern した token の tag（`core.structural.exact_record_token`）
EXACT_RECORD_TAG = "exact_record"

#: 比較に使ってはいけない（どこまで見えているかを表す）key の tag（C-K3）
PLACEHOLDER_TAGS = frozenset({"truncated", "cycle", "opaque", UNIDENTIFIED_TAG})
#: その値が process の中でだけ意味を持つ token の tag（Gate A）
PROCESS_SCOPED_TAGS = frozenset({EXACT_TAIL_TAG, UNIDENTIFIED_TAG, PROCESS_OBJECT_TAG, EXACT_RECORD_TAG})
#: 構造ではなく「新しく発行した印」か「live object の identity」を表す tag。旧実装の
#: `("object_id", …, id(value))` が担っていた意味の置き換えなので、`object_id` を
#: 「安定しない identity」として拒んでいた consumer は同じくこれを拒む
NON_STRUCTURAL_IDENTITY_TAGS = frozenset({UNIDENTIFIED_TAG, PROCESS_OBJECT_TAG})

#: `canonical_atom` が「値として固定できない」ことを表す印の tag（型名だけが残る: 閉路・
#: 要素の衝突・読めない容器）
UNSUPPORTED_VALUE_TAG = "unsupported_value"
#: `canonical_atom` が状態を読めない object を表す印の tag（`id()` で「同じ object か」だけを言う）
OBJECT_ID_TAG = "object_id"
#: `canonical_atom` が型の宣言した `to_dict()` で表した object の tag。`to_dict()` は直列化の宣言で
#: identity の宣言ではない（状態の一部を落とし得る）ので、値を識別しない
OBJECT_DICT_TAG = "object_dict"

#: atom の中身として受け付ける exact な型（`canonical_atom` は str / int しか出さない）
EXACT_ATOM_SCALARS = (str, int)
#: 子を持たない `canonical_atom` の atom の tag と、その中身の型（分類の近道）
_SCALAR_ATOM_PAYLOAD = {"none": str, "bool": int, "int": int, "float": str, "str": str, "bytes": str}
#: `canonical_atom` が列を包むときの tag
CANONICAL_SEQUENCE_TAGS = frozenset({"tuple", "list"})

_NOT_COMPARABLE_TAGS = PLACEHOLDER_TAGS | PROCESS_SCOPED_TAGS
#: 値を識別しない `canonical_atom` の atom の tag（`is_unidentified_atom` が生の段で形を照合する）
_UNIDENTIFIED_ATOM_TAGS = frozenset({OBJECT_ID_TAG, UNSUPPORTED_VALUE_TAG, OBJECT_DICT_TAG})
_UNIDENTIFIED_TOKEN_TAGS = frozenset({UNIDENTIFIED_TAG})


class AtomValidity(NamedTuple):
    """`atom_validity` の判定（意味は module の docstring）。"""

    identified: bool
    placeholder_free: bool
    comparable: bool


_VALID = AtomValidity(identified=True, placeholder_free=True, comparable=True)
_INVALID = AtomValidity(identified=False, placeholder_free=False, comparable=False)


def is_scalar_atom(item: Any) -> bool:
    """`canonical_atom` の scalar の atom（``("int", 3)`` など）か。形（2 要素・中身の型）まで照合する。

    dataclass の atom の field の組 `(name, atom)` は、name が偶然 `int` などでも中身が atom
    （tuple）なので scalar ではない（その下の `object_id` を見落とさない）。
    """

    if type(item) is not tuple or len(item) != 2 or type(item[0]) is not str:
        return False
    payload = _SCALAR_ATOM_PAYLOAD.get(item[0])
    return payload is not None and type(item[1]) is payload


def is_unidentified_atom(item: tuple) -> bool:
    """`canonical_atom` の `("object_id", module, qualname, id)` / `("unsupported_value", module, qualname)` /
    `("object_dict", atom)`。

    `object_id` は「同じ object か」しか言わず、object の死後に `id()` が再利用されると別物と
    一致する。`unsupported_value` は型名しか残っていない。形（要素数と型）まで照合する:
    dataclass の atom の field の組 `(name, atom)` の name が偶然 `object_id` でも取り違えない。
    """

    if not item or type(item[0]) is not str:
        return False
    tag = item[0]
    if tag == OBJECT_ID_TAG:
        return len(item) == 4 and type(item[1]) is str and type(item[2]) is str and type(item[3]) is int
    if tag == UNSUPPORTED_VALUE_TAG:
        return len(item) == 3 and type(item[1]) is str and type(item[2]) is str
    if tag == OBJECT_DICT_TAG:
        return len(item) == 2 and type(item[1]) is tuple
    return False


def atom_validity(atom: Any) -> AtomValidity:
    """`canonical_atom` の値（あるいはそれを含む key）を判定する。明示 stack で辿り、共有部分は 1 度だけ見る。

    tag は `tags_of` で、`canonical_atom` に何重に包まれていても読む。exact でない中身（str / int /
    tuple 以外）は識別できない。
    """

    if is_scalar_atom(atom):
        return _VALID
    if type(atom) is not tuple:
        return _VALID if type(atom) in EXACT_ATOM_SCALARS else _INVALID
    identified = True
    placeholder_free = True
    comparable = True
    stack = [atom]
    seen: set = set()
    while stack:
        item = stack.pop()
        item_id = id(item)
        if item_id in seen:
            continue
        seen.add(item_id)
        if is_unidentified_atom(item):
            return _INVALID
        tags = tags_of(item)
        if not _UNIDENTIFIED_TOKEN_TAGS.isdisjoint(tags) or not _UNIDENTIFIED_ATOM_TAGS.isdisjoint(tags[1:]):
            # 既にある識別不能 token と、`canonical_atom` に包み直された `object_id` / 型名だけの
            # 印（包んだ段の先頭。生の段は上の形の照合が見る）は、どの深さでも識別できない
            return _INVALID
        if not PLACEHOLDER_TAGS.isdisjoint(tags):
            placeholder_free = False
        if not _NOT_COMPARABLE_TAGS.isdisjoint(tags):
            comparable = False
        for child in item:
            if type(child) is tuple:
                if child and not is_scalar_atom(child):
                    stack.append(child)
            elif type(child) not in EXACT_ATOM_SCALARS:
                return _INVALID
    return AtomValidity(identified=identified, placeholder_free=placeholder_free, comparable=comparable)


def tags_of(item: Any) -> Tuple[str, ...]:
    """列 `item` の tag（生の形の先頭と、`canonical_atom` が何重に包んでも見える先頭）。

    構造 key の token と placeholder は、別の値の atom として `canonical_atom` に包まれると
    ``("tuple", (("str", tag), …))`` になる（runtime ref の `stable_key()` が構造 key を持つ
    場合など）。その key を持つ式の key がさらに別の ref に包まれると二重に包まれる。何重に
    包まれても検出（C-K3）と昇格規則（Gate A）から見えなくならないよう、tag はこの 1 か所で
    包みを外しながら読む。組み込みの型の値だけを読む（`live_values`）。

    段は (body, depth) で表す: 要素 i は `body[i]` の包みを depth 回外した値（`decoded`）。
    段の数は包みの深さまで（key の入れ子より深くならない）。
    """

    tags: list = []
    body: Any = item
    depth = 0
    while True:
        if not (type(body) is tuple or type(body) is list):
            break
        if len(body) == 0:
            break
        head = decoded(body[0], depth)
        if type(head) is not str:
            break
        tags.append(head)
        if head not in CANONICAL_SEQUENCE_TAGS or len(body) != 2:
            break
        # この段は包んだ列 ("tuple" | "list", (atom(v0), …)): 次の段は包まれていた列 V
        inner = decoded(body[1], depth)
        if type(inner) is not tuple:
            break
        inner_depth = inner[2]
        if type(inner_depth) is not int:
            break
        body, depth = inner[1], inner_depth + 1
    return tuple(tags)


def decoded(atom: Any, depth: Any) -> Any:
    """`atom` の `canonical_atom` の包みを depth 回外した値。

    str はその str、列は ``("level", body, d)``（要素 k は `body[k]` を d 回外した値）、
    どちらでもなければ None。包みの段ごとに 2 要素（種類と中身）だけを外す。再帰の深さは
    depth（包みの段の数）まで。
    """

    if type(depth) is not int:
        return None
    if depth <= 0:
        if type(atom) is str:
            return atom
        if type(atom) is tuple or type(atom) is list:
            return ("level", atom, 0)
        plain = live_values.plain_scalar(atom)
        return plain if type(plain) is str else None
    value = decoded(atom, depth - 1)
    if type(value) is not tuple:
        return None
    body = value[1]
    inner_depth = value[2]
    if type(inner_depth) is not int:
        return None
    if not (type(body) is tuple or type(body) is list):
        return None
    if len(body) != 2:
        return None
    kind = decoded(body[0], inner_depth)
    if type(kind) is not str:
        return None
    payload = decoded(body[1], inner_depth)
    if kind == "str":
        return payload if type(payload) is str else None
    if kind not in CANONICAL_SEQUENCE_TAGS or type(payload) is not tuple:
        return None
    payload_depth = payload[2]
    if type(payload_depth) is not int:
        return None
    return ("level", payload[1], payload_depth + 1)


# ---------------------------------------------------------------------------
# identity の schema（記号の共有に使ってよいか）
# ---------------------------------------------------------------------------
#
# 値として識別できても、schema の成分が欠けた key は「どの object か」を決めない。`("parameter", …)`
# の index などが欠けた key は、別々の parameter に同じ値として現れる。そのような key を含む値を
# solver の記号・unknown 宣言の記号の共有の根拠にすると、別の object が 1 つの記号になる（Issue #215）。
# 判定はここ 1 か所に置き、projection の identity の入口（`semantic_projection._identity_of`）と、
# solver symbol の安全性の判定（`query_identity.solver_symbol_identity_is_safe`）が呼ぶ。生の key と
# `canonical_atom` の atom（何重に包まれていても）、どの入れ子でも同じ規則で読む。

#: parameter の schema の先頭の tag
PARAMETER_SCHEMA_TAG = "parameter"
#: 包みの段の上限（`canonical_atom` の入れ子の上限より深い包みは作られない）
_MAX_SCHEMA_WRAP = 8


def _none_at(depth: int) -> Any:
    """`None` を `canonical_atom` で depth 回包んだ値（depth 0 は `None` そのもの）。"""

    value: Any = None
    for level in range(depth):
        value = ("none", "") if level == 0 else _atom_of_plain(value)
    return value


def _atom_of_plain(value: Any) -> Any:
    """str と tuple だけからなる値の `canonical_atom`（`_none_at` の包みを作るためだけに使う）。"""

    if type(value) is str:
        return ("str", value)
    return ("tuple", tuple(_atom_of_plain(part) for part in value))


_NONE_AT = tuple(_none_at(depth) for depth in range(_MAX_SCHEMA_WRAP + 1))


def _parameter_component_absence(item: Any) -> Any:
    """`item` が parameter の schema なら、先頭の後の各成分が欠けているか（bool の list）。違えば None。

    生の ``("parameter", c1, …)`` と、`canonical_atom` が何重に包んだ形の両方を読む（`decoded`）。
    """

    for depth in range(_MAX_SCHEMA_WRAP + 1):
        level = decoded(item, depth)
        if type(level) is not tuple or len(level) != 3 or level[0] != "level":
            return None
        body, body_depth = level[1], level[2]
        if not (type(body) is tuple or type(body) is list) or not body or type(body_depth) is not int:
            return None
        if body_depth > _MAX_SCHEMA_WRAP:
            return None
        if decoded(body[0], body_depth) == PARAMETER_SCHEMA_TAG:
            absent = _NONE_AT[body_depth]
            return [component == absent and type(component) is type(absent) for component in body[1:]]
    return None


def _parameter_schema_incomplete(absent: list) -> bool:
    """parameter の schema の欠けの規則（成分は `(program, entry, index, …)` / `(index, width)` の形）。"""

    if not absent:
        return True
    if len(absent) == 1:
        return absent[0]
    if len(absent) == 2:
        return absent[0] or absent[1]
    return absent[2]


def parameter_schema_complete(value: Any) -> bool:
    """`value`（生の key・atom・identity の組）の中のどの parameter の schema も、成分が欠けていないか。

    明示 stack で辿り、共有部分は 1 度だけ見る。tuple・list・set・frozenset・dict（exact な型）を辿る。
    """

    stack = [value]
    seen: set = set()
    while stack:
        item = stack.pop()
        elements = _base_elements(item)
        if elements is None:
            continue
        item_id = id(item)
        if item_id in seen:
            continue
        seen.add(item_id)
        kind, members = elements
        if kind is tuple:
            absent = _parameter_component_absence(members)
            if absent is not None and _parameter_schema_incomplete(absent):
                return False
        stack.extend(members)
    return True


def _base_elements(item: Any) -> Any:
    """容器の要素を基底型の実装で読む: (列なら tuple・それ以外は None, 要素の tuple)。容器でなければ None。

    subclass（NamedTuple など）の `__iter__` を呼ばない（`semantic_projection.read_container` と同じ規則。
    この module は projection に依存しないので、同じ読み方をここに持つ）。列は exact な tuple に直して
    schema を照合する。
    """

    kind = type(item)
    if issubclass(kind, tuple):
        return tuple, (item if kind is tuple else tuple(tuple.__iter__(item)))
    if issubclass(kind, list):
        return tuple, tuple(list.__iter__(item))
    if issubclass(kind, frozenset):
        return None, tuple(frozenset.__iter__(item))
    if issubclass(kind, set):
        return None, tuple(set.__iter__(item))
    if issubclass(kind, dict):
        return None, tuple(element for pair in dict.items(item) for element in pair)
    return None


def usable_as_symbol_identity(atom: Any) -> bool:
    """`canonical_atom` の atom を、記号の共有の根拠（solver の identity）に使ってよいか。

    identified（値を識別する）・placeholder_free（構造 key の打ち切りなどの印を含まない）・schema が
    完全（`parameter_schema_complete`）の 3 つ。process の中だけの識別済み token は受け付ける。
    """

    validity = atom_validity(atom)
    return validity.identified and validity.placeholder_free and parameter_schema_complete(atom)
