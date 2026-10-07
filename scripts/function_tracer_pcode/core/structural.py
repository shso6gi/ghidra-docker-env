# -*- coding: utf-8 -*-
"""Structural keys for Expression / Condition.

These helpers keep normalization and equivalence internals on the AST/P-code
side instead of round-tripping through rendered strings.
"""

from __future__ import annotations

from dataclasses import astuple, dataclass
import hashlib
import json
import secrets
import struct
from typing import Any, Optional, Tuple

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.atomic_tables import (
    AppendOnlyBuckets,
    SerialCounter,
    WeakKeyedTable,
)
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.semantic_lifecycle import is_validated
from scripts.function_tracer_pcode.core.semantic_projection import (
    UNSUPPORTED_VALUE_TAG,
    canonical_atom as _atom_key,
)
from scripts.function_tracer_pcode.core.semantic_snapshot import (
    COMMUTATIVE_BINARY_OPS,
    children_are_commutative,
    local_semantic_payload,
    ordered_semantic_edges,
    semantic_projection,
)


StructuralKey = Tuple[Any, ...]
#: 可換演算の集合は node の意味なので `semantic_snapshot` が owner。
#: `expression_key` の正規化がそれを読む（再 export は既存 import のため）。
WIDTH_ADAPTER_OPS = frozenset({"INT_ZEXT", "INT_SEXT"})


def _is_all_ones_mask_for_size(expr: Optional[Expression], size: int) -> bool:
    if expr is None or size <= 0 or _node_kind(expr) is not ExpressionType.CONSTANT:
        return False
    mask = (1 << (size * 8)) - 1
    value = _plain_int(expr.value)
    return value is not None and (value & mask) == mask


# ---------------------------------------------------------------------------
# 予算付きの構造 key と、打ち切った先の厳密な tail token（Issue #215）
# ---------------------------------------------------------------------------
#
# この節が構造 key の **唯一の owner**。consumer（cache / dedup / case merge /
# 含意 / identity）は key を `==` / `hash` で比べるだけで、Expression へ戻って
# 確かめ直さない。そのため次の契約をここで無条件に守る（記号は Issue #215）:
#
#   C-K1  key が等しい ⇒ 予算に依らない展開 T_o が等しい。暗号の仮定を置かない
#   C-K2  (a) placeholder の無い key は ⇔。(b) 非巡回で識別済みの tail token は ⇔。
#         (c) 打ち切り位置が違う key・cycle の距離が違う graph の一致は保証しない
#   C-K3  placeholder の検出は深さを問わない（`key_contains_placeholder`）
#   C-K4  memo は tail の入力（`ExactTailOptions`）で分ける。budget は入力ではない
#   C-K5  識別できないもの（値として固定できない atom・未知の node 種別）は
#         毎回新しい token になり、何とも等しくならない。`hash()` / `None` に潰さない
#   C-K6  識別済みの token は PYTHONHASHSEED / `id()` / `repr()` / dict 順に依存しない。
#         digest が衝突しても intern が別の index を割り当てる（C-K1 は崩れない）
#   C-K7  canonical encoding はこの module に 1 実装だけ置く
#   C-K8  token と打ち切りの無い key は共有の有無に依存しない。cycle は現在の path
#         上の距離（back_ref）で表す
#
# **token は process の中でだけ identity になる**（Issue #215 Gate A）。3 種類ある:
#
#   * 識別済み tail token `("exact_tail", digest, index)`: 決定的（C-K6。index は digest が
#     衝突したときだけ 0 以外）。ただし index は「この process で同じ digest に何番目に来た
#     record か」なので、衝突があれば別の process は同じ値を別の record に割り当て得る
#     （A: X→0, Y→1 / B: Y→0, X→1）。
#   * 識別不能 token `("exact_tail_unidentified", reason, n, nonce)` と object identity
#     `("process_object", serial, nonce)`: n / serial は process の中の通し番号、nonce は
#     token ごとの 128 bit の乱数。通し番号が process の中の一意性を、nonce が別の process
#     （fork した子を含む）の token と一致しないことを与える。したがって別の encoding の
#     中（`canonical_atom` の包み・digest の preimage）に埋め込まれて昇格規則から見えなく
#     なっても、別の process の token と等しくならない。
#
# 見える形の token を process をまたいで比べる規則は `cross_process_node` 1 つで、それを
# 適用する normalizer は `checker/cause_aggregate.freeze_identity` 1 つ。既定で適用し
# （fail-closed）、token を作った process 自身の集計だけが明示の scope で外す。reporting は
# 生の key を比べない（`test_sn3_cross_process_identity.py` の登録表と static test が固定する）。
# digest の中に見えなくなった識別済み token が process をまたいで一致するのは digest が一致
# するときだけで、その digest 自身が置く衝突の仮定と同じ（それ以上の仮定を足さない）。

#: tail token の domain separation（record の digest 専用）
_EXACT_TAIL_DOMAIN = b"sn3-exact-structural-tail-v1\x00"

#: 識別済みの tail token の tag
EXACT_TAIL_TAG = "exact_tail"
#: 識別できない token の tag（C-K5）
UNIDENTIFIED_TAG = "exact_tail_unidentified"
#: object identity fallback の token の tag（`expression_key_or_identity`）
PROCESS_OBJECT_TAG = "process_object"

#: 比較に使ってはいけない（どこまで見えているかを表す）key の tag（C-K3）
PLACEHOLDER_TAGS = frozenset({"truncated", "cycle", "opaque", UNIDENTIFIED_TAG})
#: その値が process の中でだけ意味を持つ token の tag（Gate A）
PROCESS_SCOPED_TAGS = frozenset({EXACT_TAIL_TAG, UNIDENTIFIED_TAG, PROCESS_OBJECT_TAG})
#: 構造ではなく「新しく発行した印」か「live object の identity」を表す tag。旧実装の
#: `("object_id", …, id(value))` が担っていた意味の置き換えなので、`object_id` を
#: 「安定しない identity」として拒んでいた consumer は同じくこれを拒む
NON_STRUCTURAL_IDENTITY_TAGS = frozenset({UNIDENTIFIED_TAG, PROCESS_OBJECT_TAG})


@dataclass(frozen=True)
class ExactTailOptions:
    """tail の展開 T_o を決める option（budget は含めない: tail の入力ではない）。

    option を足すときはここと `_key_view` だけを変える。memo の分割（C-K4）は
    この値の全 field（`memo_key`）で行うので、足し忘れて memo が混線することは無い。
    """

    normalize_commutative: bool = True
    strip_width_adapters: bool = False
    collapse_full_masks: bool = False
    include_memory_read_order: bool = True
    include_semantic_runtime_refs: bool = True

    @classmethod
    def of(cls, **options: Any) -> "ExactTailOptions":
        """key の option（未知の名前は TypeError）。値は真偽に正規化する（`1` と `True` を分けない）。"""

        return cls(**{name: bool(value) for name, value in options.items()})

    @property
    def memo_key(self) -> tuple:
        """memo の分割に使う plain な値（全 field を宣言順に。`core.atomic_tables` の subkey）。"""

        return astuple(self)


#: canonical encoding が 10 進で書く int の範囲（それより大きい int は 16 進の tag で書く）
_DECIMAL_ENCODING_LIMIT = 10 ** 4000


class _NotCanonical(Exception):
    """canonical encoding が受け付けない値（C-K5 で識別不能になる）。"""


def _encode_canonical(value: Any, out: bytearray) -> None:
    """長さ前置・型 tag 付きの canonical encoding（C-K7）。

    受け付けるのは exact type の None / bool / int / str / bytes / float / tuple /
    list だけ。subclass（IntEnum 等）も、`__eq__` が構造と一致する保証が無いので
    受け付けない。`repr()` / `hash()` / `id()` は使わない。
    """

    kind = type(value)
    if value is None:
        out += b"N"
    elif kind is bool:
        out += b"T" if value else b"F"
    elif kind is int:
        if -_DECIMAL_ENCODING_LIMIT < value < _DECIMAL_ENCODING_LIMIT:
            text = b"%d" % value
            out += b"I%d:" % len(text)
        else:
            # 10 進の変換に上限がある大きさの int は 16 進（tag で範囲を分けるので単射のまま）
            text = b"%x" % value
            out += b"H%d:" % len(text)
        out += text
    elif kind is str:
        data = value.encode("utf-8", "surrogatepass")
        out += b"S%d:" % len(data)
        out += data
    elif kind is bytes:
        out += b"B%d:" % len(value)
        out += value
    elif kind is float:
        # 値の bit 列そのもの（-0.0 と 0.0、NaN の payload も区別する）
        out += b"D"
        out += struct.pack(">d", value)
    elif kind is tuple or kind is list:
        out += b"(%d:" % len(value) if kind is tuple else b"[%d:" % len(value)
        for item in value:
            _encode_canonical(item, out)
        out += b")"
    else:
        raise _NotCanonical(kind.__qualname__)


def _canonical_bytes(value: Any) -> bytes:
    out = bytearray()
    _encode_canonical(value, out)
    return bytes(out)


class _ExactTailIntern:
    """record → 識別済み token の intern（C-K6）。**意味の owner**。

    ここが決めるのは token の意味だけ: digest の domain、record と token の対応、
    衝突を index で解決すること、識別不能 token と object identity serial の形。
    「表を読む → index を決める → 登録する」の不可分性は `core/atomic_tables` の
    `AppendOnlyBuckets.position` が 1 操作として保証する（Gate B: 個々の
    `dict.setdefault` / `list.append` の atomicity を合成しても不可分にならない）。
    同期の方式を変えてもこの class は変わらない。

    record は削除しない。したがって index は process の中で安定で、record に対して
    単射。**別の process の index とは対応しない**（Gate A、`cross_process_node`）。
    """

    def __init__(self, buckets: Optional[AppendOnlyBuckets] = None) -> None:
        self._buckets = buckets if buckets is not None else AppendOnlyBuckets()
        self._unidentified = SerialCounter()
        self._process_objects = SerialCounter()

    @staticmethod
    def digest(record: bytes) -> str:
        return hashlib.sha256(_EXACT_TAIL_DOMAIN + record).hexdigest()

    def intern(self, record: bytes) -> StructuralKey:
        digest = self.digest(record)
        return (EXACT_TAIL_TAG, digest, self._buckets.position(digest, record))

    def unidentified(self, reason: str) -> StructuralKey:
        return (UNIDENTIFIED_TAG, str(reason), self._unidentified.next(), _token_nonce())

    def process_object_serial(self) -> Tuple[int, str]:
        return (self._process_objects.next(), _token_nonce())

    def statistics(self) -> dict:
        table = self._buckets.statistics(size=len)
        return {
            "digests": table["buckets"],
            "records": table["items"],
            "record_bytes": table["item_bytes"],
            "collisions": table["items"] - table["buckets"],
            "unidentified_tokens": self._unidentified.issued(),
        }


def _token_nonce() -> str:
    """識別不能 token / object identity に付ける乱数（別の process の token と一致させない）。"""

    return secrets.token_hex(16)


_TAIL_INTERN = _ExactTailIntern()

#: validated（凍結済み）node の tail token の process 全体の memo（C-K4）。
#: 凍結済みの node と closure は immutable かつ非巡回なので、token は node と
#: option だけで決まる。未凍結の node は入れない（生成後に `size` 等が書き換わる）。
_VALIDATED_TAIL_MEMO = WeakKeyedTable()

#: validated node の runtime ref の意味 key（`_expression_runtime_metadata`）の memo
_VALIDATED_METADATA_MEMO = WeakKeyedTable()

#: `expression_key_or_identity` の object identity（同じ live object → 同じ serial、
#: serial は再利用しない。`id()` は object の死後に再利用されるので使わない）
_PROCESS_OBJECT_SERIALS = WeakKeyedTable()


def unidentified_identity(reason: str) -> StructuralKey:
    """毎回新しい「識別できない」token（C-K5）。自分自身の再計算とも等しくならない。

    consumer が key を作れなかったときの identity はこれを使う（`hash()` / `id()` /
    `None` に潰さない）。
    """

    return _TAIL_INTERN.unidentified(reason)


def exact_tail_statistics() -> dict:
    """intern の統計（診断・性能計測用。判定には使わない）。"""

    return _TAIL_INTERN.statistics()


# ---------------------------------------------------------------------------
# atom と label の分類（Issue #215: 通常 key・tail・memo・consumer が使う唯一の規則）
# ---------------------------------------------------------------------------
#
# node の label に入る値（leaf の値・runtime ref の意味 key・名前・大きさ・読み順・opcode）は、
# ここで 1 度だけ分類する。通常 key（`_assemble_key`）・tail の record（`_exact_tail_token`）・
# memo（`_VALIDATED_TAIL_MEMO` / `_VALIDATED_METADATA_MEMO`）・比較可否（`expression_key_status`）は
# 同じ `_KeyView` の分類（`identified` / `comparable`）だけを読み、別の受理規則を持たない。
#
#   identified  値が exact な組み込みの値だけで決まり、値を識別しない部分（`id()`・型名だけの印・
#               exact でない中身・既にある識別不能 token）を、何重に包まれていても含まない。
#               偽なら tail は識別不能 token（毎回新しい。memo しない）。C-K5
#   comparable  identified で、しかも placeholder（打ち切り・閉路・opaque・識別不能）も process の
#               中でだけ意味を持つ token も含まない。偽なら key は比較に使えない。C-K3 / Gate A
#
# 「置き換えたか」（object が変わったか）は分類の代わりにしない: 識別不能 token を持つ値は
# 置き換えなくても identified ではない。scalar の値は `live_values` の規則（基底型の slot）で読み、
# subclass の `__eq__` / `__hash__` / `__int__` を呼ばない（`canonical_atom` も同じ規則）。

#: atom の中身として受け付ける exact な型（`canonical_atom` は str / int しか出さない）
_EXACT_ATOM_SCALARS = (str, int)
#: 子を持たない `canonical_atom` の atom の tag と、その中身の型（分類の近道）
_SCALAR_ATOM_PAYLOAD = {"none": str, "bool": int, "int": int, "float": str, "str": str, "bytes": str}


def _is_scalar_atom(item: Any) -> bool:
    """`canonical_atom` の scalar の atom（``("int", 3)`` など）か。形（2 要素・中身の型）まで照合する。

    dataclass の atom の field の組 `(name, atom)` は、name が偶然 `int` などでも中身が atom
    （tuple）なので scalar ではない（その下の `object_id` を見落とさない）。
    """

    if type(item) is not tuple or len(item) != 2 or type(item[0]) is not str:
        return False
    payload = _SCALAR_ATOM_PAYLOAD.get(item[0])
    return payload is not None and type(item[1]) is payload


def _is_unidentified_atom(item: tuple) -> bool:
    """`canonical_atom` の `("object_id", module, qualname, id)` / `("unsupported_value", module, qualname)`。

    `object_id` は「同じ object か」しか言わず、object の死後に `id()` が再利用されると別物と
    一致する。`unsupported_value` は型名しか残っていない。形（要素数と型）まで照合する:
    dataclass の atom の field の組 `(name, atom)` の name が偶然 `object_id` でも取り違えない。
    """

    if not item or type(item[0]) is not str:
        return False
    tag = item[0]
    if tag == "object_id":
        return len(item) == 4 and type(item[1]) is str and type(item[2]) is str and type(item[3]) is int
    if tag == UNSUPPORTED_VALUE_TAG:
        return len(item) == 3 and type(item[1]) is str and type(item[2]) is str
    return False


_NOT_COMPARABLE_TAGS = PLACEHOLDER_TAGS | PROCESS_SCOPED_TAGS
#: 値を識別しない `canonical_atom` の atom の tag（`_is_unidentified_atom` が生の段で形を照合する）
_UNIDENTIFIED_ATOM_TAGS = frozenset({"object_id", UNSUPPORTED_VALUE_TAG})


def _classify_atom(atom: Any) -> Tuple[Any, bool, bool]:
    """`canonical_atom` の値を分類する: (key に入れる atom, identified, comparable)。

    identified でない atom（値を識別しない atom・exact でない中身・既にある識別不能 token を
    どこかに含む）は、atom ごと毎回新しい識別不能 token にする（その key は自分自身の再計算とも
    等しくならない）。tag は `_tags_of` で、`canonical_atom` に何重に包まれていても読む。明示
    stack で辿る。
    """

    if _is_scalar_atom(atom):
        return atom, True, True
    if type(atom) is not tuple:
        if type(atom) in _EXACT_ATOM_SCALARS:
            return atom, True, True
        return unidentified_identity("non_exact_atom"), False, False
    identified = True
    comparable = True
    stack = [(atom, False)]
    rebuilt: dict = {}
    while stack:
        item, exiting = stack.pop()
        item_id = id(item)
        if not exiting:
            if item_id in rebuilt:
                continue
            if _is_unidentified_atom(item):
                rebuilt[item_id] = unidentified_identity("unidentified_atom")
                identified = comparable = False
                continue
            tags = _tags_of(item)
            if UNIDENTIFIED_TAG in tags or not _UNIDENTIFIED_ATOM_TAGS.isdisjoint(tags[1:]):
                # 既にある識別不能 token と、`canonical_atom` に包み直された `object_id` / 型名だけの
                # 印（包んだ段の先頭。生の段は上の形の照合が見る）は、どの深さでも識別できない
                identified = False
            if not _NOT_COMPARABLE_TAGS.isdisjoint(tags):
                comparable = False
            stack.append((item, True))
            for child in item:
                if type(child) is tuple:
                    if child and id(child) not in rebuilt and not _is_scalar_atom(child):
                        stack.append((child, False))
                elif type(child) not in _EXACT_ATOM_SCALARS:
                    identified = comparable = False
            continue
        changed = False
        items = []
        for child in item:
            if type(child) is tuple:
                replaced = rebuilt.get(id(child), child) if child else child
            elif type(child) in _EXACT_ATOM_SCALARS:
                replaced = child
            else:
                replaced = unidentified_identity("non_exact_atom")
            changed = changed or replaced is not child
            items.append(replaced)
        rebuilt[item_id] = tuple(items) if changed else item
    if not identified:
        # 識別できない atom は、key の中でも毎回新しい識別不能 token 1 つで表す: 既にある token を
        # そのまま持つと、同じ値を持つ別の node・自分自身の再計算と key が等しくなる（C-K5）
        return unidentified_identity("unidentified_atom"), False, False
    return rebuilt[id(atom)], True, comparable


class _LabelReader:
    """1 つの node の label の値を分類しながら読む（`_key_view` だけが使う）。

    読めなかった値（scalar の規則で exact な値にならない名前・大きさなど）は識別不能 token を
    label に置き、その node を identified でなくする（通常 key も tail も同じ判断を受け取る）。
    """

    __slots__ = ("identified", "comparable")

    def __init__(self) -> None:
        self.identified = True
        self.comparable = True

    def _reject(self, reason: str) -> StructuralKey:
        self.identified = False
        self.comparable = False
        return unidentified_identity(reason)

    def text(self, value: Any) -> Any:
        if type(value) is str:
            return value
        if value is None:
            return ""
        scalar = live_values.json_scalar(value)
        return scalar if type(scalar) is str else self._reject("non_text_label")

    def integer(self, value: Any) -> Any:
        if type(value) is int:
            return value
        scalar = live_values.json_scalar(value)
        if scalar is True or scalar is False:
            return int(scalar)
        return scalar if type(scalar) is int else self._reject("non_integer_label")

    def size(self, value: Any) -> Any:
        if type(value) is int:
            return value
        return 0 if value is None else self.integer(value)

    def flag(self, value: Any) -> Any:
        if value is None:
            return False
        scalar = live_values.json_scalar(value)
        if scalar is True or scalar is False:
            return scalar
        return bool(scalar) if type(scalar) is int else self._reject("non_flag_label")

    def atom(self, value: Any) -> Any:
        atom, identified, comparable = _classify_atom(_atom_key(value))
        self._merge(identified, comparable)
        return atom

    def runtime_metadata(self, expr: Expression) -> tuple:
        metadata, identified, comparable = _expression_runtime_metadata(expr)
        self._merge(identified, comparable)
        return metadata

    def _merge(self, identified: bool, comparable: bool) -> None:
        self.identified = self.identified and identified
        self.comparable = self.comparable and comparable

    def view(self, kind: str, label: tuple, children: tuple = (), commutative: bool = False) -> "_KeyView":
        return _KeyView(
            kind, label, children, commutative, identified=self.identified, comparable=self.comparable,
        )


def _expression_runtime_metadata(expr: Expression) -> Tuple[tuple, bool, bool]:
    """structural key に載せる runtime ref の意味 key と、その分類 (metadata, identified, comparable)。

    生 object は読まない。`semantic_projection()` は凍結済みなら固定済みの値を、未凍結ならその場で
    作った値を返す（どちらも pure value）。意味 key は `canonical_atom` の値なので、leaf の値と
    同じ規則（`_classify_atom`）で分類する。
    """

    validated = is_validated(expr)
    if validated:
        cached = _VALIDATED_METADATA_MEMO.get(expr, "runtime_metadata")
        if cached is not None:
            return cached
    runtime_key = semantic_projection(expr).runtime_structural_key
    if runtime_key is None:
        result = ((), True, True)
    else:
        atom, identified, comparable = _classify_atom(runtime_key)
        result = ((("runtime_ref", atom),), identified, comparable)
    # 凍結済みの node の意味 key は変わらないので 1 回だけ分類する。identified でない結果は覚えない
    # （置き換えた識別不能 token は毎回新しい: C-K5）
    if validated and result[1]:
        _VALIDATED_METADATA_MEMO.put(expr, "runtime_metadata", result)
    return result


class _Redirect:
    """V_o(n) が別の node（全 bit の mask を剥がした operand）であること。"""

    __slots__ = ("target",)

    def __init__(self, target: Optional[Expression]) -> None:
        self.target = target


class _KeyView:
    """V_o(n) の局所 label L_o と、`ordered_semantic_edges` 順の子（C-K1 の T_o）。

    `kind` は key の組み立て方（`_assemble_key`）を選ぶ。label は子を除いた部分で、
    key にも tail の record にも同じ値が入る（2 つの表現が別の T_o を見ないように、
    node の読み方はこの 1 か所にしかない）。`identified` / `comparable` は label の分類
    （`_LabelReader`）で、通常 key・tail・memo はこの 2 つだけを読む。
    """

    __slots__ = ("kind", "label", "children", "commutative", "identified", "comparable", "reason")

    def __init__(
        self, kind: str, label: tuple, children: tuple = (), commutative: bool = False,
        *, identified: bool = True, comparable: bool = True, reason: str = "unknown_node_kind",
    ) -> None:
        self.kind = kind
        self.label = label
        self.children = children
        self.commutative = commutative
        # label が値を識別する: 偽なら tail は識別不能 token（C-K5）
        self.identified = identified
        # key を比較に使える（識別済みで placeholder・process の中だけの token が無い）: C-K3
        self.comparable = comparable and identified
        # kind が "opaque" のとき、識別不能 token に記録する理由
        self.reason = reason


def _node_kind(node: Any) -> Optional[ExpressionType]:
    """node の種別（exact な `ExpressionType` のときだけ。それ以外は None: 種別を識別できない）。"""

    kind = getattr(node, "expr_type", None)
    return kind if type(kind) is ExpressionType else None


_UNREADABLE = object()


def _sequence_of(value: Any) -> Any:
    """容器の中身を基底型の実装で読んだ tuple（None は空）。list / tuple（と subclass）以外は `_UNREADABLE`。

    subclass の `__getitem__` / `__len__` / `__iter__` を呼ばない（未凍結の node は任意の容器を
    持ち得る）。
    """

    if value is None:
        return ()
    kind = type(value)
    if kind is tuple:
        return value
    if kind is list:
        return tuple(list.__iter__(value))
    # subclass（PHI の `PhiBranch` は NamedTuple）は基底型の storage を読む: scalar と同じく、容器の
    # 中身は基底型の実装が持つ値（subclass の `__iter__` / `__getitem__` / `__len__` を呼ばない）
    if issubclass(kind, tuple):
        return tuple(tuple.__iter__(value))
    if issubclass(kind, list):
        return tuple(list.__iter__(value))
    return _UNREADABLE


def _key_view(node: Expression, options: ExactTailOptions):
    """node を option の下で読む（`_Redirect` か `_KeyView`）。

    label の値は `_LabelReader` が分類する。node の種別と子の容器も exact な型のときだけ読み、
    読めなければ識別不能（opaque）にする（値の user code を呼ばない）。
    """

    current = node
    if options.strip_width_adapters:
        stripped = set()
        while _node_kind(current) is ExpressionType.UNARY_OP and _plain_text(current.operator) in WIDTH_ADAPTER_OPS:
            operands = _sequence_of(current.operands)
            if operands is _UNREADABLE:
                return _KeyView("opaque", _opaque_label(current), reason="unreadable_operands")
            if not operands:
                break
            if id(current) in stripped:
                # 幅 adapter だけの閉路: 剥がした先の node が無い（未凍結の graph だけで起き得る）
                return _KeyView("opaque", _opaque_label(node), reason="width_adapter_cycle")
            stripped.add(id(current))
            current = operands[0]
            if current is None:
                return _Redirect(None)

    expr_type = _node_kind(current)
    if expr_type is None:
        return _KeyView("opaque", _opaque_label(current), reason="unknown_node_kind")
    operands = _sequence_of(current.operands)
    if operands is _UNREADABLE:
        return _KeyView("opaque", _opaque_label(current), reason="unreadable_operands")

    if (
        options.collapse_full_masks
        and expr_type is ExpressionType.BINARY_OP
        and _plain_text(current.operator) == "INT_AND"
        and len(operands) == 2
    ):
        left, right = operands
        mask_size = (
            _plain_int(current.size)
            or (_plain_int(right.size) if right is not None else None)
            or (_plain_int(left.size) if left is not None else None)
            or 0
        )
        if _is_all_ones_mask_for_size(left, mask_size):
            return _Redirect(right)
        if _is_all_ones_mask_for_size(right, mask_size):
            return _Redirect(left)

    read = _LabelReader()
    size = read.size(current.size)

    if expr_type is ExpressionType.CONSTANT:
        return read.view("leaf", ("const", read.atom(current.value), size))

    if expr_type is ExpressionType.LITERAL:
        return read.view("leaf", ("literal", read.atom(current.value), size))

    if expr_type is ExpressionType.PARAMETER or expr_type is ExpressionType.VARIABLE:
        name = read.text(current.name)
        return read.view("leaf", (expr_type.name.lower(), name, read.atom(current.value), size))

    if expr_type is ExpressionType.UNKNOWN:
        name = read.text(current.name)
        atom = read.atom(current.value)
        runtime_metadata = read.runtime_metadata(current) if options.include_semantic_runtime_refs else ()
        return read.view("leaf", ("unknown", name, atom, size, *runtime_metadata))

    first = operands[0] if operands else None

    if expr_type is ExpressionType.UNARY_OP:
        return read.view("unary", ("unary", read.text(current.operator), size), (first,))

    if expr_type is ExpressionType.BINARY_OP:
        second = operands[1] if len(operands) > 1 else None
        operator = read.text(current.operator)
        return read.view(
            "binary",
            ("binary", operator, size),
            (first, second),
            commutative=bool(
                options.normalize_commutative and type(operator) is str and operator in COMMUTATIVE_BINARY_OPS
            ),
        )

    if expr_type is ExpressionType.MEMORY:
        runtime_metadata = read.runtime_metadata(current) if options.include_semantic_runtime_refs else ()
        read_order = (
            ("read_order", read.integer(current.read_order_key))
            if options.include_memory_read_order and current.read_order_key is not None
            else ("read_order", None)
        )
        return read.view("memory", ("memory", size, read_order, runtime_metadata), (first,))

    if expr_type is ExpressionType.CALL:
        return read.view("call", ("call", read.text(current.name), size), operands)

    if expr_type is ExpressionType.INTRINSIC:
        opcode = getattr(current, "opcode", None)
        return read.view(
            "call",
            ("intrinsic", read.text(current.name), None if opcode is None else read.integer(opcode), size),
            operands,
        )

    if expr_type is ExpressionType.PHI:
        branches = _sequence_of(current.value)
        if branches is _UNREADABLE:
            return _KeyView("opaque", _opaque_label(current), reason="unreadable_phi")
        shape = []
        children = []
        for branch in branches:
            pair = _sequence_of(branch)
            if pair is _UNREADABLE or len(pair) != 2:
                return _KeyView("opaque", _opaque_label(current), reason="unreadable_phi")
            condition, value = pair
            if condition is not None and type(condition) is not Condition:
                # 条件は exact な `Condition` のときだけ読む（subclass の property を呼ばない）
                return _KeyView("opaque", _opaque_label(current), reason="unreadable_phi")
            if condition is None:
                shape.append((False, False))
            else:
                shape.append((True, read.flag(condition.negated)))
                children.append(condition.expression)
            children.append(value)
        return read.view("phi", ("phi", size, tuple(shape)), tuple(children))

    return _KeyView("opaque", _opaque_label(current))


def _plain_text(value: Any) -> Any:
    """名前・演算子の基底型の str（読めなければ None）。判定の近道と placeholder の記述だけに使う。"""

    if type(value) is str:
        return value
    scalar = live_values.json_scalar(value)
    return scalar if type(scalar) is str else None


def _plain_int(value: Any) -> Any:
    """大きさなどの基底型の int（読めなければ None）。判定の近道と placeholder の記述だけに使う。"""

    if type(value) is int:
        return value
    scalar = live_values.json_scalar(value)
    if scalar is True or scalar is False:
        return int(scalar)
    return scalar if type(scalar) is int else None


def _kind_name(node: Any) -> str:
    kind = _node_kind(node)
    return kind.name if kind is not None else "?"


def _opaque_label(node: Expression) -> tuple:
    return (
        "opaque", _kind_name(node), _plain_text(node.operator) or "", _plain_text(node.name) or "",
        _plain_int(node.size) or 0,
    )


def _assemble_key(view: _KeyView, child_keys: list) -> StructuralKey:
    """label と子の key から、main 以来の形の key を組む（C-K2(a): 形を変えない）。"""

    kind = view.kind
    label = view.label
    if kind == "leaf":
        return label
    if kind == "unary":
        return (*label, child_keys[0])
    if kind == "binary":
        left_key, right_key = child_keys
        if view.commutative and _key_precedes(right_key, left_key):
            left_key, right_key = right_key, left_key
        return (*label, left_key, right_key)
    if kind == "memory":
        tag, size, read_order, runtime_metadata = label
        return (tag, size, child_keys[0], read_order, *runtime_metadata)
    if kind == "call":
        return (*label, tuple(child_keys))
    if kind == "phi":
        tag, size, shape = label
        branches = []
        position = 0
        for has_condition, negated in shape:
            if has_condition:
                cond_key = ("cond", child_keys[position], negated)
                position += 1
            else:
                cond_key = ("none",)
            branches.append((cond_key, child_keys[position]))
            position += 1
        return (tag, size, tuple(branches))
    raise AssertionError(kind)


def _key_precedes(first: StructuralKey, second: StructuralKey) -> bool:
    """可換演算の 2 子の順序（key の値の全順序）。

    比べられる key どうしは main と同じ tuple の `<`（C-K2(a): 値を変えない）。tuple の `<` が
    比べられない要素（`("read_order", None)` と `("read_order", 3)` など）に当たる組は、
    main では `TypeError` で key を作れなかった。その組だけ canonical encoding の bytes で
    順序を決める（2 つの key に対して向きが一意に決まれば、可換の正規化には十分）。
    """

    try:
        return first < second
    except TypeError:
        pass
    try:
        return _canonical_bytes(first) < _canonical_bytes(second)
    except _NotCanonical as exc:
        raise TypeError("commutative operand keys have no canonical order") from exc


def _cycle_descriptor(node: Expression) -> tuple:
    return (_kind_name(node), _plain_text(node.name) or "", _plain_int(node.size) or 0)


def _node_descriptor(node: Expression) -> tuple:
    # placeholder の記述（比較可否・同一性は tail token / back_ref が決める）。値は exact に読む
    return (_kind_name(node), _plain_text(node.operator) or "", _plain_text(node.name) or "", _plain_int(node.size) or 0)


class _TailFrame:
    __slots__ = ("node", "view", "position", "tokens", "min_ref")

    def __init__(self, node, view) -> None:
        self.node = node
        self.view = view
        self.position = 0
        self.tokens: list = []
        # この frame の部分木の back_ref が指す最も浅い path 上の深さ
        self.min_ref = None


def _exact_tail_token(
    root: Expression,
    options: ExactTailOptions,
    *,
    outer_path: Tuple[int, ...] = (),
    memo: Optional[dict] = None,
) -> StructuralKey:
    """root から下を予算無しに展開した T_o(root) の識別済み token（C-K1 / C-K2(b)）。

    明示 stack で辿るので深さに上限は無い。共有部分木は `memo`（1 回の key 計算の
    間だけ `id()` で引く）で 1 度だけ辿る。`outer_path` は呼び出し側の key が今いる
    path（root の祖先）で、閉路がそこへ戻るときの back_ref の距離に使う。

    返すのは `("exact_tail", digest, index)`、`("back_ref", k)`（root 自身が path 上に
    いるとき）、`("exact_tail_unidentified", reason, n, nonce)` のどれか。
    """

    if memo is None:
        memo = {}
    path: list = list(outer_path)
    depth_of: dict = {node_id: depth for depth, node_id in enumerate(path)}

    def _start(node):
        """node の結果が既に決まっていればそれを、未着手なら frame を返す。"""

        seen_redirects = set()
        while True:
            node_id = id(node)
            depth = depth_of.get(node_id)
            if depth is not None:
                return (("ref", depth), None), None
            cached = memo.get(node_id)
            if cached is not None:
                return cached, None
            if is_validated(node):
                token = _VALIDATED_TAIL_MEMO.get(node, options.memo_key)
                if token is not None:
                    memo[node_id] = (token, None)
                    return (token, None), None
            view = _key_view(node, options)
            if isinstance(view, _Redirect):
                if node_id in seen_redirects:
                    return (unidentified_identity("redirect_cycle"), None), None
                seen_redirects.add(node_id)
                if view.target is None:
                    return (None, None), None
                node = view.target
                continue
            if view.kind == "opaque":
                return (unidentified_identity(view.reason), None), None
            return None, _TailFrame(node, view)


    first, frame = _start(root)
    if frame is None:
        token = first[0]
        if token is not None and token[0] == "ref":
            return ("back_ref", len(path) - token[1])
        return token if token is not None else ("none",)

    # path に積むのは V_o を解いた後の node（redirect 先を経由する閉路もここで止まる）
    stack = [frame]
    path.append(id(frame.node))
    depth_of[id(frame.node)] = len(path) - 1
    final = None
    while stack:
        frame = stack[-1]
        children = frame.view.children
        if frame.position < len(children):
            child = children[frame.position]
            frame.position += 1
            if child is None:
                frame.tokens.append(b"0")
                continue
            result, child_frame = _start(child)
            if child_frame is not None:
                stack.append(child_frame)
                path.append(id(child_frame.node))
                depth_of[id(child_frame.node)] = len(path) - 1
                continue
            _absorb(frame, result, len(path))
            if frame.tokens and frame.tokens[-1] is None:
                final = unidentified_identity("unidentified_child")
                break
            continue

        # すべての子が決まった: record を作って intern する
        stack.pop()
        node_id = path.pop()
        depth = len(path)
        del depth_of[node_id]
        if any(item is None for item in frame.tokens):
            final = unidentified_identity("unidentified_child")
            break
        if not frame.view.identified:
            # label に識別不能な atom（旧 `object_id`）がある: tail も識別できない
            final = unidentified_identity("unidentified_atom")
            break
        try:
            label_bytes = _canonical_bytes(frame.view.label)
        except _NotCanonical:
            final = unidentified_identity("non_canonical_atom")
            break
        tokens = list(frame.tokens)
        if frame.view.commutative and len(tokens) == 2:
            tokens.sort()
        record = b"L%d:" % len(label_bytes) + label_bytes + b"#%d:" % len(tokens) + b"".join(tokens)
        token = _TAIL_INTERN.intern(record)
        path_independent = frame.min_ref is None or frame.min_ref >= depth
        if path_independent:
            memo[node_id] = (token, None)
            if frame.min_ref is None and is_validated(frame.node):
                _VALIDATED_TAIL_MEMO.put(frame.node, options.memo_key, token)
        result = (token, frame.min_ref if not path_independent else None)
        if not stack:
            final = token
            break
        _absorb(stack[-1], result, len(path))
    return final


def _absorb(frame: "_TailFrame", result, path_length: int) -> None:
    """子の結果を親 frame の record 片にする（back_ref は現在の path 上の距離）。"""

    token, child_min_ref = result
    if token is None:
        frame.tokens.append(b"0")
        return
    if token[0] == "ref":
        target_depth = token[1]
        frame.tokens.append(b"R%d;" % (path_length - target_depth))
        frame.min_ref = target_depth if frame.min_ref is None else min(frame.min_ref, target_depth)
        return
    if token[0] != EXACT_TAIL_TAG:
        frame.tokens.append(None)
        return
    frame.tokens.append(b"X" + token[1].encode("ascii") + b".%d;" % token[2])
    if child_min_ref is not None:
        frame.min_ref = child_min_ref if frame.min_ref is None else min(frame.min_ref, child_min_ref)


def exact_tail_token(expr: Optional[Expression], options: Optional[ExactTailOptions] = None) -> StructuralKey:
    """式全体の tail token（C-K2(b): 非巡回なら token が等しい ⇔ T_o が等しい）。"""

    if expr is None:
        return ("none",)
    return _exact_tail_token(expr, options or ExactTailOptions())


def expression_key(
    expr: Optional[Expression],
    *,
    budget: int = 256,
    **options: bool,
) -> StructuralKey:
    """Return a stable, hashable structural key for an expression tree.

    The traversal is DAG-aware: a node reached twice is built once and its key
    object is reused, so ``budget`` counts *distinct* nodes instead of tree
    positions and a shared subgraph is not re-walked per parent.  Sharing the
    key objects also makes comparing two keys cheap, because tuple comparison
    short-circuits on identical elements.

    A key that carries a placeholder (``truncated`` / ``cycle`` / ``opaque``) is
    deliberately *not* memoised: a placeholder describes the position it was
    produced in -- the remaining budget, or the path that reached the node --
    and reusing it elsewhere would report a node as unresolved when it is not.

    **予算を使い切った先は捨てない**（Issue #215）。打ち切った node は
    ``("truncated", type, op, name, size, token)`` になり、token は打ち切った先を
    予算無しに展開した構造の識別済み token（`_exact_tail_token`）。したがって
    key が等しければ展開も等しい（C-K1）。閉路は ``("cycle", type, name, size,
    ("back_ref", k))``（k は現在の path 上の距離）、未知の node 種別は識別できない
    token を持つ ``opaque`` になる。

    **これは construction-safe な legacy key であって、validated identity API
    ではない**。lifecycle を進めない（`validated()` を呼ばない）し、未検証の
    graph でも答えを返す。consumer は `key_contains_placeholder()` で「どこま
    で見えているか」を判断する。

    意図的にそうしてある理由は 2 つ:

    * 解析の途中（まだ組み立て中の式）を鍵にする consumer が居る。ここで
      検証を要求すると、構築中の graph に identity の契約を持ち込むことになる
    * この key は `object_target_key` 等の preimage に入っていて、reason
      identity として外へ出る。形を変えると判定名が広く動く

    「この graph は identity を計算してよい形か」を要求するのは
    `candidate_hash()` / `structural_equals()` / `structural_identity_digest()`
    の 3 つで、そちらは入口で `validated()` を通し、閉路は typed failure に
    なる（placeholder を作らない）。
    """

    # option は `ExactTailOptions` だけが定義する（未知の名前は TypeError）。足すときに
    # 公開 API の引数列を複製して直す必要が無いよう、ここより上では列挙しない
    return expression_key_status(expr, budget=budget, **options)[0]


def expression_key_status(
    expr: Optional[Expression],
    *,
    budget: int = 256,
    **options: bool,
) -> Tuple[StructuralKey, bool]:
    """(`expression_key` の key, その key が比較可能か) を 1 回の走査で返す。

    比較可能 ⇔ `key_is_comparable(key)`（C-K3）。key を保持して何度も比較可否を問う
    呼び出し側は、key を全走査し直さずにこの組を保持する。
    """

    key, has_placeholder = _build_expression_key(expr, int(budget), ExactTailOptions.of(**options))
    return key, not has_placeholder


class _PlaceholderReached(Exception):
    """`stop_at_placeholder` の build が最初の placeholder に達した（key は作らない）。"""


def _build_expression_key(
    expr: Optional[Expression],
    budget: int,
    options: ExactTailOptions,
    *,
    stop_at_placeholder: bool = False,
) -> Tuple[StructuralKey, bool]:
    """key と「placeholder を含むか」を 1 回の走査で求める（`expression_key` の本体）。

    `stop_at_placeholder` なら、最初の placeholder で `_PlaceholderReached` を送出する。
    比較可能な key だけが要る呼び出し（`expression_key_safe`）が、捨てる key のために
    打ち切った先の tail token を計算しないようにするため。
    """

    # `path` は key の入れ子の 1 段ごとに 1 要素（back_ref の距離 = key の段数）。全 bit の mask を
    # 剥がす redirect は key の段を作らないので path に積まない（`_exact_tail_token` と同じ規則）。
    # redirect だけの閉路は `redirecting` で止める。明示 stack で辿る（予算が大きくても
    # `RecursionError` にならない）。予算は従来どおり訪れた node（redirect を含む）ごとに 1 減らす。
    path: list = []
    path_nodes: list = []
    depth_of: dict = {}
    #: 辿っている redirect → それを辿り始めたときの path の長さ（解いた先の node が積まれる位置）
    redirecting: dict = {}
    memo: dict[int, StructuralKey] = {}
    tail_memo: dict = {}
    remaining = budget
    placeholders = 0

    def _placeholder() -> None:
        nonlocal placeholders
        if stop_at_placeholder:
            raise _PlaceholderReached()
        placeholders += 1

    def _enter(node: Optional[Expression]):
        """(決まった key, None) か (None, 子を辿る frame) を返す。"""

        nonlocal remaining
        if node is None:
            return ("none",), None
        node_id = id(node)
        cached = memo.get(node_id)
        if cached is not None:
            return cached, None
        depth = depth_of.get(node_id)
        if depth is not None:
            _placeholder()
            return ("cycle", *_cycle_descriptor(node), ("back_ref", len(path) - depth)), None
        redirect_depth = redirecting.get(node_id)
        if redirect_depth is not None:
            _placeholder()
            if redirect_depth >= len(path):
                # 間に key の段が無い: redirect だけの閉路（解いた先の node が無い）
                return ("cycle", *_cycle_descriptor(node), unidentified_identity("redirect_cycle")), None
            # redirect を解いた先の node（path の redirect_depth 段目）への閉路
            target = path_nodes[redirect_depth]
            return ("cycle", *_cycle_descriptor(target), ("back_ref", len(path) - redirect_depth)), None
        if remaining <= 0:
            _placeholder()
            return (
                "truncated",
                *_node_descriptor(node),
                _exact_tail_token(node, options, outer_path=tuple(path), memo=tail_memo),
            ), None
        remaining -= 1
        before = placeholders
        view = _key_view(node, options)
        if isinstance(view, _Redirect):
            redirecting[node_id] = len(path)
            return None, [node, view, (view.target,), [], before]
        if view.kind == "opaque":
            _placeholder()
            return (*view.label, unidentified_identity(view.reason)), None
        if not view.comparable:
            _placeholder()
        depth_of[node_id] = len(path)
        path.append(node_id)
        path_nodes.append(node)
        return None, [node, view, view.children, [], before]

    first, frame = _enter(expr)
    if frame is None:
        return first, placeholders > 0
    stack = [frame]
    while True:
        frame = stack[-1]
        node, view, children, child_keys, before = frame
        if len(child_keys) < len(children):
            child_key, child_frame = _enter(children[len(child_keys)])
            if child_frame is not None:
                stack.append(child_frame)
            else:
                child_keys.append(child_key)
            continue
        stack.pop()
        node_id = id(node)
        if isinstance(view, _Redirect):
            del redirecting[node_id]
            key = child_keys[0]
        else:
            path.pop()
            path_nodes.pop()
            del depth_of[node_id]
            key = _assemble_key(view, child_keys)
        if placeholders == before:
            memo[node_id] = key
        if not stack:
            return key, placeholders > 0
        stack[-1][3].append(key)


def exact_structural_identity(expr: Optional[Expression], **options: bool) -> StructuralKey:
    """予算を持たない厳密な identity（大きさは O(1)）。

    等しい ⇔ option の下の展開 T_o が等しい（非巡回で識別済みのとき。C-K2(b)）。識別
    できない部分を含めば何とも等しくならない（C-K5）。予算付き key が打ち切られて比較
    に使えない式の identity（dedup / memo の key）に使う: 予算 256 の key を丸ごと持つ
    より小さく、object identity と違って構造が等しい式どうしは一致する。
    """

    if expr is None:
        return ("none",)
    return ("exact_identity", _exact_tail_token(expr, ExactTailOptions.of(**options)))


def condition_key(
    condition: Optional[Condition],
    *,
    budget: int = 256,
    **options: bool,
) -> StructuralKey:
    if condition is None:
        return ("none",)
    return (
        "condition",
        expression_key(condition.expression, budget=budget, **options),
        bool(condition.negated),
    )


def condition_key_safe(
    condition: Optional[Condition],
    *,
    budget: int = 256,
    **options: bool,
) -> Optional[StructuralKey]:
    """比較可能なときだけ `condition_key` と同じ key、そうでなければ None（`expression_key_safe` と同じ打ち切り）。"""

    if condition is None:
        return ("none",)
    expression = expression_key_safe(condition.expression, budget=budget, **options)
    if expression is None:
        return None
    return ("condition", expression, bool(condition.negated))


def _key_has_tag(key: Any, tags: frozenset) -> bool:
    """key のどこか（深さを問わない）に、第 1 要素が tags の tuple / list があるか。

    反復で辿り、共有されている部分 key は 1 度だけ見る。永続化で list になった
    key もそのまま辿れる。
    """

    stack = [key]
    seen: set = set()
    while stack:
        item = stack.pop()
        kind = type(item)
        if kind is not tuple and kind is not list:
            continue
        item_id = id(item)
        if item_id in seen:
            continue
        seen.add(item_id)
        if not tags.isdisjoint(_tags_of(item)):
            return True
        stack.extend(item)
    return False


#: `canonical_atom`（`core/semantic_projection`）が列を包むときの tag
_CANONICAL_SEQUENCE_TAGS = frozenset({"tuple", "list"})


def _tags_of(item: Any) -> Tuple[str, ...]:
    """列 `item` の tag（生の形の先頭と、`canonical_atom` が何重に包んでも見える先頭）。

    構造 key の token と placeholder は、別の値の atom として `canonical_atom` に包まれると
    ``("tuple", (("str", tag), …))`` になる（runtime ref の `stable_key()` が構造 key を持つ
    場合など）。その key を持つ式の key がさらに別の ref に包まれると二重に包まれる。何重に
    包まれても検出（C-K3）と昇格規則（Gate A）から見えなくならないよう、tag はこの 1 か所で
    包みを外しながら読む。組み込みの型の値だけを読む（`live_values`）。

    段は (body, depth) で表す: 要素 i は `body[i]` の包みを depth 回外した値（`_decoded`）。
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
        head = _decoded(body[0], depth)
        if type(head) is not str:
            break
        tags.append(head)
        if head not in _CANONICAL_SEQUENCE_TAGS or len(body) != 2:
            break
        # この段は包んだ列 ("tuple" | "list", (atom(v0), …)): 次の段は包まれていた列 V
        inner = _decoded(body[1], depth)
        if type(inner) is not tuple:
            break
        inner_depth = inner[2]
        if type(inner_depth) is not int:
            break
        body, depth = inner[1], inner_depth + 1
    return tuple(tags)


def _decoded(atom: Any, depth: Any) -> Any:
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
    value = _decoded(atom, depth - 1)
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
    kind = _decoded(body[0], inner_depth)
    if type(kind) is not str:
        return None
    payload = _decoded(body[1], inner_depth)
    if kind == "str":
        return payload if type(payload) is str else None
    if kind not in _CANONICAL_SEQUENCE_TAGS or type(payload) is not tuple:
        return None
    payload_depth = payload[2]
    if type(payload_depth) is not int:
        return None
    return ("level", payload[1], payload_depth + 1)


def key_contains_placeholder(key: StructuralKey) -> bool:
    """key のどこかに placeholder（truncated / cycle / opaque / 識別不能）があるか（C-K3）。"""

    return _key_has_tag(key, PLACEHOLDER_TAGS)


def key_is_comparable(key: StructuralKey) -> bool:
    """Return False if the structural key contains placeholders/truncated markers."""

    return not key_contains_placeholder(key)


def key_is_process_independent(key: Any) -> bool:
    """key の等しさが process をまたいで identity の意味を持つか（Issue #215 Gate A）。

    tail token・識別不能 token・object identity token を含む key は、その値が
    発行した process の中でだけ identity になる。別の process が同じ値を別の構造に
    割り当て得る。process をまたぐ比較そのものは `cross_process_node`（を適用する
    `freeze_identity`）が fail-closed にするので、これは「その key を identity として
    解決してよいか」を問う側（`resolve_cause_identity`）が使う判定。
    """

    return not _key_has_tag(key, PROCESS_SCOPED_TAGS)


def key_contains_unidentified(key: Any) -> bool:
    """key のどこかに識別不能 token があるか（その key は自分自身の写しとも一致しない: C-K5）。"""

    return _key_has_tag(key, _UNIDENTIFIED_TAGS)


_UNIDENTIFIED_TAGS = frozenset({UNIDENTIFIED_TAG})


def identity_is_memoizable(key: Any) -> bool:
    """この key / identity を memo して再利用してよいか（C-K4 / C-K5 の memo の契約）。

    識別不能 token を含む値は「自分自身の再計算とも等しくならない」ので、memo して同じ値を
    返してはいけない（memo すると、次の呼び出しが同じ token を受け取り一致してしまう）。
    構造 key / identity を自分で memo する consumer は、保存の前にこれを問う。
    """

    return not key_contains_unidentified(key)


def cross_process_node(node: Any) -> Any:
    """永続化した値を process をまたぐ identity にするときの **唯一の規則**（Gate A）。

    tail token・識別不能 token・object identity token は、発行した process の中でだけ
    identity になる（別の process は同じ値を別の構造へ割り当て得る）。そのような node は
    毎回新しい識別不能 token に置き換え、何とも等しくならないようにする（過分割に倒す）。
    それ以外の node はそのまま返す。

    子から先に正規化する normalizer が node ごとに呼ぶ（O(1)）。結果 JSON などから読んだ
    identity を比べる側は、自分で key を比べず、この規則を適用する normalizer
    （`checker/cause_aggregate.freeze_identity`）を通すこと。
    """

    if (type(node) is tuple or type(node) is list) and not PROCESS_SCOPED_TAGS.isdisjoint(_tags_of(node)):
        # 生の形でも `canonical_atom` に包まれた形でも同じ規則（`_tags_of`）
        return unidentified_identity("process_scoped")
    return node


def expression_key_safe(
    expr: Optional[Expression],
    *,
    budget: int = 256,
    **options: bool,
) -> Optional[StructuralKey]:
    """Return structural key only when it is safe for semantic equality.

    If a bounded traversal is truncated/cycle-detected/opaque, the result is None
    so callers can avoid treating two unrelated deep expressions as equal.

    最初の placeholder で走査を止める（捨てる key のために tail token を計算しない）。
    値は `expression_key` の結果が placeholder を含まないときのその key と同じ。
    """

    try:
        key, _has_placeholder = _build_expression_key(
            expr, int(budget), ExactTailOptions.of(**options), stop_at_placeholder=True,
        )
    except _PlaceholderReached:
        return None
    return key


def expression_key_or_identity(
    expr: Optional[Expression],
    *,
    budget: int = 256,
    **options: bool,
) -> StructuralKey:
    """Safe structural key with identity fallback for non-comparable inputs.

    This avoids collapsing semantically unknown/truncated keys into equality.

    fallback は **同じ live object だけが等しい** identity（Issue #215）。`id()` は
    object の死後に再利用されるので使わず、object に弱参照で結び付けた serial を
    使う（serial は再利用しない）。弱参照できない値は識別不能 token（C-K5）。
    """

    safe = expression_key_safe(
        expr,
        budget=budget,
        **options,
    )
    if safe is not None:
        return safe
    if expr is None:
        return ("uncomparable_expression", "none")
    return ("uncomparable_expression", type(expr).__name__, _process_object_identity(expr))


def _process_object_identity(expr: Any) -> StructuralKey:
    try:
        serial = _PROCESS_OBJECT_SERIALS.get_or_create(expr, "serial", _TAIL_INTERN.process_object_serial)
    except TypeError:
        return unidentified_identity("object_not_weakly_referenceable")
    return (PROCESS_OBJECT_TAG, *serial)


def expression_provenance_key(
    expr: Optional[Expression],
    *,
    safe_budget: int = 256,
    max_digest_nodes: int = 8192,
    include_memory_read_order: bool = True,
    include_semantic_runtime_refs: bool = True,
) -> StructuralKey:
    """Stable key for object-target provenance.

    Unlike expression_key_or_identity(), this never falls back to process-local
    object ids. If the semantic structural key is too deep or otherwise
    uncomparable, use a stable digest over a full object-derived expression
    payload and include source atoms for diagnostics.
    """

    if expr is None:
        return ("none",)

    projection = semantic_projection(expr)
    if projection.parameter_runtime_key is not None:
        return ("runtime_ref", projection.parameter_runtime_key)

    if projection.storage_identity is not None:
        return ("storage", projection.storage_identity)

    if projection.runtime_stable_key is not None:
        return ("runtime_ref", projection.runtime_stable_key)

    safe = expression_key_safe(
        expr,
        budget=safe_budget,
        include_memory_read_order=include_memory_read_order,
        include_semantic_runtime_refs=include_semantic_runtime_refs,
    )
    if safe is not None:
        return ("expression", safe)

    payload, source_atoms, complete = _expression_provenance_payload(
        expr,
        max_nodes=max_digest_nodes,
    )
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return (
        "expression_digest",
        hashlib.sha256(encoded).hexdigest(),
        ("complete", bool(complete)),
        ("root", _expression_descriptor(expr)),
        ("source_atoms", tuple(sorted(source_atoms, key=repr))),
    )


def _expression_provenance_payload(
    expr: Expression,
    *,
    max_nodes: int,
) -> Tuple[StructuralKey, Tuple[StructuralKey, ...], bool]:
    count = 0
    complete = True
    active: set[int] = set()
    source_atoms: set[StructuralKey] = set()
    digest_by_id: dict[int, str] = {}
    stack: list[Tuple[Optional[Expression], bool]] = [(expr, False)]

    none_digest = _digest_structural_payload(("none",))

    while stack:
        node, exiting = stack.pop()
        if node is None:
            continue

        node_id = id(node)
        if exiting:
            active.discard(node_id)
            operand_digests = []
            for operand in getattr(node, "operands", ()) or ():
                operand_digests.append(
                    none_digest if operand is None else digest_by_id.get(id(operand), none_digest)
                )
            payload = (
                "expr",
                _expression_descriptor(node),
                ("value", _stable_value_key(getattr(node, "value", None))),
                ("data_type", getattr(node, "data_type", None)),
                ("storage", semantic_projection(node).storage_identity),
                ("runtime_ref", semantic_projection(node).runtime_structural_key),
                ("read_order", getattr(node, "read_order_key", None)),
                ("opcode", getattr(node, "opcode", None)),
                ("operands", tuple(operand_digests)),
            )
            digest_by_id[node_id] = _digest_structural_payload(payload)
            continue

        if node_id in digest_by_id:
            continue
        if count >= max_nodes:
            complete = False
            tail_digest, tail_source_atoms, tail_complete, tail_count = (
                _expression_subtree_digest_and_source_atoms(node)
            )
            source_atoms.update(tail_source_atoms)
            digest_by_id[node_id] = _digest_structural_payload(
                (
                    "truncated",
                    _expression_descriptor(node),
                    ("tail_digest", tail_digest),
                    ("tail_complete", bool(tail_complete)),
                    ("tail_nodes", int(tail_count)),
                )
            )
            continue

        if node_id in active:
            complete = False
            digest_by_id[node_id] = _digest_structural_payload(
                ("cycle", _expression_descriptor(node))
            )
            continue

        count += 1
        active.add(node_id)
        source_atom = _expression_source_atom(node)
        if source_atom is not None:
            source_atoms.add(source_atom)

        stack.append((node, True))
        for operand in reversed(getattr(node, "operands", ()) or ()):
            if operand is not None:
                stack.append((operand, False))

    root_digest = digest_by_id.get(id(expr), none_digest)
    payload = (
        "digest_payload",
        root_digest,
        ("nodes", int(count)),
    )
    return payload, tuple(source_atoms), bool(complete)


def _expression_subtree_digest_and_source_atoms(
    expr: Expression,
) -> Tuple[str, set[StructuralKey], bool, int]:
    count = 0
    complete = True
    active: set[int] = set()
    source_atoms: set[StructuralKey] = set()
    digest_by_id: dict[int, str] = {}
    stack: list[Tuple[Optional[Expression], bool]] = [(expr, False)]
    none_digest = _digest_structural_payload(("none",))

    while stack:
        node, exiting = stack.pop()
        if node is None:
            continue

        node_id = id(node)
        if exiting:
            active.discard(node_id)
            operand_digests = []
            for operand in getattr(node, "operands", ()) or ():
                operand_digests.append(
                    none_digest if operand is None else digest_by_id.get(id(operand), none_digest)
                )
            payload = (
                "expr",
                _expression_descriptor(node),
                ("value", _stable_value_key(getattr(node, "value", None))),
                ("data_type", getattr(node, "data_type", None)),
                ("storage", semantic_projection(node).storage_identity),
                ("runtime_ref", semantic_projection(node).runtime_structural_key),
                ("read_order", getattr(node, "read_order_key", None)),
                ("opcode", getattr(node, "opcode", None)),
                ("operands", tuple(operand_digests)),
            )
            digest_by_id[node_id] = _digest_structural_payload(payload)
            continue

        if node_id in digest_by_id and node_id not in active:
            continue
        if node_id in active:
            complete = False
            digest_by_id.setdefault(
                node_id,
                _digest_structural_payload(("cycle", _expression_descriptor(node))),
            )
            continue

        count += 1
        active.add(node_id)
        source_atom = _expression_source_atom(node)
        if source_atom is not None:
            source_atoms.add(source_atom)

        stack.append((node, True))
        for operand in reversed(getattr(node, "operands", ()) or ()):
            if operand is not None:
                stack.append((operand, False))

    return digest_by_id.get(id(expr), none_digest), source_atoms, bool(complete), int(count)


def _digest_structural_payload(payload: StructuralKey) -> str:
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _expression_descriptor(expr: Expression) -> StructuralKey:
    expr_type = getattr(expr, "expr_type", None)
    expr_type_name = getattr(expr_type, "name", None) or (
        str(expr_type) if expr_type is not None else None
    )
    return (
        expr_type_name,
        getattr(expr, "operator", None),
        getattr(expr, "name", None),
        int(getattr(expr, "size", 0) or 0),
    )


def _expression_source_atom(expr: Expression) -> Optional[StructuralKey]:
    projection = semantic_projection(expr)
    semantic_runtime_key = projection.runtime_structural_key
    if projection.parameter_runtime_key is not None:
        return ("runtime_ref", semantic_runtime_key)

    if projection.storage_identity is not None:
        return ("storage", projection.storage_identity)
    if semantic_runtime_key is not None:
        return ("runtime_ref", semantic_runtime_key)
    expr_type = getattr(expr, "expr_type", None)
    expr_type_name = getattr(expr_type, "name", None)
    if expr_type in {
        ExpressionType.PARAMETER,
        ExpressionType.VARIABLE,
        ExpressionType.UNKNOWN,
        ExpressionType.CONSTANT,
        ExpressionType.LITERAL,
    }:
        return (
            "expr_source",
            expr_type_name,
            getattr(expr, "name", None),
            _stable_value_key(getattr(expr, "value", None)),
            int(getattr(expr, "size", 0) or 0),
        )
    return None


def _stable_value_key(value: Any) -> StructuralKey:
    if value is None:
        return ("none",)
    if isinstance(value, bool):
        return ("bool", int(value))
    if isinstance(value, int):
        return ("int", value)
    if isinstance(value, float):
        return ("float", repr(value))
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, Expression):
        return ("expression_ref", _expression_descriptor(value))
    if isinstance(value, Condition):
        return (
            "condition",
            _stable_value_key(value.expression),
            ("negated", bool(value.negated)),
        )
    if isinstance(value, tuple):
        return ("tuple", tuple(_stable_value_key(item) for item in value))
    if isinstance(value, list):
        return ("list", tuple(_stable_value_key(item) for item in value))
    if isinstance(value, dict):
        items = [
            (_stable_value_key(key), _stable_value_key(item))
            for key, item in value.items()
        ]
        items.sort()
        return ("dict", tuple(items))
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return ("stable", _stable_value_key(stable_key()))
        except Exception:
            pass
    return ("opaque", type(value).__module__, type(value).__qualname__)


# ---------------------------------------------------------------------------
# structural identity（Issue #22 PR-22-B）
# ---------------------------------------------------------------------------
#
# ここは **「2 つの式が同じか」だけ** を所有する。node の意味の分解は
# `core/semantic_snapshot.py`（`local_semantic_payload` / `ordered_semantic_edges`）
# にあり、hash・完全比較・graph snapshot の 3 つは同じ分解を共有する。
#
# 3 つの層を混ぜないこと:
#
#   candidate hash        16 byte。bucket / 早期棄却だけ。**等価の確定にも
#                         外部 identity にも使わない**。衝突は設計上あり得る。
#   equivalence digest    32 byte。完全比較と同じ同値関係を持つ安定 digest。
#                         prefilter に使ってよいが hit は確定しない。
#   完全比較              `structural_equals`。distinct な node 組の数に比例し、
#                         共有部分木を親ごとに再走査しない。**唯一の決定者**。
#
# 表現の digest（辺の順と共有の仕方を残す）は別概念で、graph の owner が持つ:
# `semantic_snapshot.graph_representation_digest()`。
#
# PR-105-A の `SolverQueryIdentity` / `RewriteIdentity` が再利用してよいのは
# `walk_dag()` の graph と `graph_representation_digest()` / `candidate_hash()`
# の **prefilter** まで。一致の確定は各々が自分の完全比較で行う（solver 宣言や
# rewrite 文脈は structural identity が見ていないので、ここの digest では
# 足りない）。

#: 完全比較の既定予算（distinct な node 組の数）。従来の `condition_key`
#: （木の訪問回数 256）と同じ桁で、共有 DAG ではより深くまで比較できる。
DEFAULT_STRUCTURAL_COMPARISON_BUDGET = 256

#: candidate hash の長さ。候補の絞り込み専用なので 16 byte で足りる。
CANDIDATE_DIGEST_SIZE = 16

#: equivalence digest の長さ。外へ出す安定 identity なので広く取る。
EQUIVALENCE_DIGEST_SIZE = 32

#: 2 つの digest が **別物であること** を byte 列の段階で担保する domain
#: separation。同じ入力でも値が一致しないので、片方を他方の代わりに使うと
#: すぐ気づく（どちらも Merkle で同じ正規化を使うが、契約が違う）。
_CANDIDATE_PERSON = b"cand-v1"
_EQUIVALENCE_PERSON = b"equiv-v1"

_NULL_CHILD_DIGEST = b"\x00" * CANDIDATE_DIGEST_SIZE
_NULL_EQUIVALENCE_CHILD_DIGEST = b"\x00" * EQUIVALENCE_DIGEST_SIZE

#: memo の「まだ評価していない」を「評価中（None）」と区別するための番兵。
_MISSING = object()

_validate = None


def _validated(expr: Optional[Expression]) -> Optional[Expression]:
    """identity API の入口で graph を検証する（`core/semantic_freeze.py` が owner）。

    検証済みなら費用ゼロ。未検証なら凍らせることで検証し、閉路はそこで typed
    failure になる。ここで各 API ごとに閉路判定を書かないのは、判定が 2 つある
    と片方だけ直るから。

    **identity layer は公開権限を持たない**。ここで進めるのは VALIDATED まで
    で、`publish` にも `mark_published` にも触れない（`test_architecture_
    boundaries.py` が固定している）。candidate hash を取っただけの精錬中の値が
    solver へ渡せるようになってはいけない。
    """

    global _validate
    if expr is None or is_validated(expr):
        return expr
    if _validate is None:
        from scripts.function_tracer_pcode.core.semantic_freeze import validated

        _validate = validated
    return _validate(expr)


def _encode_atoms(value: Any, parts: list) -> None:
    """atom を **型を落とさずに** 決定的な文字列へ符号化する。

    `repr()` を使わないのは、未知の object が混ざると `id()` が入って run 間で
    digest が変わってしまうため。未知の型は型名だけにする（区別できなくなるが、
    hash は候補の絞り込みなので完全比較が正しく不一致にする）。
    """

    if value is None:
        parts.append("n;")
    elif value is True or value is False:
        parts.append("b1;" if value else "b0;")
    elif isinstance(value, int):
        parts.append("i%d;" % value)
    elif isinstance(value, float):
        parts.append("f%r;" % value)
    elif isinstance(value, str):
        parts.append("s%d:%s;" % (len(value), value))
    elif isinstance(value, bytes):
        parts.append("y%s;" % value.hex())
    elif isinstance(value, (tuple, list)):
        parts.append("(t" if isinstance(value, tuple) else "(l")
        parts.append("%d;" % len(value))
        for item in value:
            _encode_atoms(item, parts)
        parts.append(")")
    else:
        parts.append("o%s.%s;" % (type(value).__module__, type(value).__qualname__))


def _atoms_to_bytes(value: Any) -> bytes:
    parts: list = []
    _encode_atoms(value, parts)
    return "".join(parts).encode("utf-8", "surrogatepass")


def _compose_merkle_digest(
    node: Any,
    child_digests: Tuple[Optional[bytes], ...],
    *,
    digest_size: int,
    person: bytes,
    null_child: bytes,
    payload: Any = None,
) -> bytes:
    """local payload と子 digest から Merkle digest を O(1) で合成する。

    `child_digests` は `ordered_semantic_edges(node)` と同じ並びであること。
    可換二項演算は子 digest を整列してから混ぜるので、完全比較が一致とみなす式は
    同じ digest になる。合成規則を 1 本にしてあるのは、candidate hash と
    equivalence digest で正規化が食い違わないようにするため — 値が違うのは
    `person` による domain separation の結果で、規則の違いではない。

    `payload` は検証中の呼び出し（まだ node へ書いていない local payload）で
    渡す。渡さないと組み直しになり、生 object を読み直してしまう。
    """

    if payload is None:
        payload = local_semantic_payload(node)
    digest = hashlib.blake2b(digest_size=digest_size, person=person)
    digest.update(_atoms_to_bytes(payload.identity_atoms))
    resolved = [null_child if child is None else child for child in child_digests]
    if len(resolved) == 2 and children_are_commutative(node):
        resolved.sort()
    digest.update(b"|%d|" % len(resolved))
    for child in resolved:
        digest.update(child)
    return digest.digest()


def compose_candidate_digest(
    node: Any, child_digests: Tuple[Optional[bytes], ...], *, payload: Any = None
) -> bytes:
    """**候補絞り込み専用** の 16 byte hash（freeze が各 node に付ける）。

    用途は bucket と早期棄却だけ。衝突は起こり得るものとして設計してあり、
    一致の確定にも、外へ出す stable identity にも使ってはいけない。
    """

    return _compose_merkle_digest(
        node,
        child_digests,
        digest_size=CANDIDATE_DIGEST_SIZE,
        person=_CANDIDATE_PERSON,
        null_child=_NULL_CHILD_DIGEST,
        payload=payload,
    )


def compose_equivalence_digest(
    node: Any, child_digests: Tuple[Optional[bytes], ...], *, payload: Any = None
) -> bytes:
    """**完全比較と同じ同値関係** を持つ 32 byte digest（freeze が各 node に付ける）。

    `structural_equals(a, b)` が真なら値が一致する。prefilter として使ってよいが、
    一致の確定は完全比較が行う（逆向きは保証しない）。
    """

    return _compose_merkle_digest(
        node,
        child_digests,
        digest_size=EQUIVALENCE_DIGEST_SIZE,
        person=_EQUIVALENCE_PERSON,
        null_child=_NULL_EQUIVALENCE_CHILD_DIGEST,
        payload=payload,
    )


def candidate_hash(expr: Optional[Expression]) -> Optional[bytes]:
    """式の candidate hash（`None` は式が無いとき）。

    validated graph を前提にする: 未凍結なら入口で検証して凍らせるので、閉路は
    ここで typed failure になり、placeholder の hash が出回ることはない。

    **この値だけで等価を確定しないこと**。候補の絞り込み（bucket / 早期棄却）
    専用で、衝突は `structural_equals` が食い止める。
    """

    expr = _validated(expr)
    if expr is None:
        return None
    return expr.__dict__.get("_structural_hash")


class _ComparisonFrame:
    """完全比較 1 組分の作業状態（明示 stack 用）。"""

    __slots__ = ("key", "alternatives", "alt_index", "pair_index")

    def __init__(self, key, alternatives):
        self.key = key
        self.alternatives = alternatives
        self.alt_index = 0
        self.pair_index = 0


def structural_equals(
    left: Optional[Expression],
    right: Optional[Expression],
    *,
    budget: int = DEFAULT_STRUCTURAL_COMPARISON_BUDGET,
) -> bool:
    """2 つの式が構造的に同じか（DAG-aware な完全比較）。

    費用は **distinct な node 組** の数に比例する。同じ組を 2 回評価しないので、
    共有部分木を親ごとに展開しない。candidate hash は凍結済みどうしの早期棄却に
    だけ使い、一致の確定には使わない（hash を定数にしても判定は変わらない）。

    一致としない場合:

    * 予算超過（比較不能 → cache miss。誤って一致としない）
    * 未知の node 種別（`expression_key` の `opaque` 枝と同じ）
    * 閉路（凍結できない graph。内部不整合なので一致としない）

    互換契約: 旧実装が木の予算内で比較できた式は同じ結果になり、旧実装が予算
    超過で比較不能だった式が新しい DAG 予算で比較できるようになった場合だけ、
    一致を認める（判定能力の改善）。
    """

    # 検証が先、identity shortcut が後。逆にすると `structural_equals(x, x)` が
    # 閉路を含む x でも True を返してしまい、壊れた graph が「同じ」として
    # 通過する。
    left = _validated(left)
    right = _validated(right)
    if left is right:
        # 同じ object、または「両方とも無い」。旧実装の key も `("none",)`
        # どうしを一致として扱っていた。
        return True
    if left is None or right is None:
        return False

    memo: dict[tuple, Optional[bool]] = {}
    remaining = [int(budget)]
    exhausted = [False]

    def _quick(x, y) -> Optional[bool]:
        if x is y:
            # 欠けた operand（二項演算の右辺が無い等）は「両方とも無い」なら
            # 一致。片方だけ無いなら下で不一致になる。
            return True
        if x is None or y is None:
            return False
        known = memo.get((id(x), id(y)), _MISSING)
        if known is _MISSING:
            return None
        if known is None:
            # 評価中の組へ戻ってきた = 閉路。一致としない。
            return False
        return known

    def _open(x, y) -> Optional[_ComparisonFrame]:
        """組の局所比較を行い、子の組み合わせ候補を作る（不一致なら `None`）。"""

        key = (id(x), id(y))
        if remaining[0] <= 0:
            exhausted[0] = True
            memo[key] = False
            return None
        remaining[0] -= 1
        memo[key] = None

        left_payload = local_semantic_payload(x)
        right_payload = local_semantic_payload(y)
        if not left_payload.comparable or not right_payload.comparable:
            memo[key] = False
            return None
        if left_payload.compare_atoms != right_payload.compare_atoms:
            memo[key] = False
            return None

        left_digest = x.__dict__.get("_structural_hash") if hasattr(x, "__dict__") else None
        right_digest = y.__dict__.get("_structural_hash") if hasattr(y, "__dict__") else None
        if left_digest is not None and right_digest is not None and left_digest != right_digest:
            memo[key] = False
            return None

        left_edges = ordered_semantic_edges(x)
        right_edges = ordered_semantic_edges(y)
        if len(left_edges) != len(right_edges):
            memo[key] = False
            return None
        straight = [
            (left_edge.child, right_edge.child)
            for left_edge, right_edge in zip(left_edges, right_edges)
        ]
        alternatives = [straight]
        if len(straight) == 2 and children_are_commutative(x):
            # 可換演算は入れ替えた組み合わせも試す。hash で並びを決めないのは、
            # hash が衝突している場合に取り違えて「違う」と言ってしまうため。
            alternatives.append(
                [(straight[0][0], straight[1][1]), (straight[1][0], straight[0][1])]
            )
        return _ComparisonFrame(key, alternatives)

    frame = _open(left, right)
    if frame is None:
        return False
    stack = [frame]
    result: Optional[bool] = None

    while stack:
        if exhausted[0]:
            return False
        frame = stack[-1]
        if result is not None:
            if result:
                frame.pair_index += 1
            else:
                frame.alt_index += 1
                frame.pair_index = 0
            result = None
        if frame.alt_index >= len(frame.alternatives):
            memo[frame.key] = False
            stack.pop()
            result = False
            continue
        alternative = frame.alternatives[frame.alt_index]
        if frame.pair_index >= len(alternative):
            memo[frame.key] = True
            stack.pop()
            result = True
            continue
        child_left, child_right = alternative[frame.pair_index]
        known = _quick(child_left, child_right)
        if known is not None:
            result = known
            continue
        child_frame = _open(child_left, child_right)
        if child_frame is None:
            result = False
            continue
        stack.append(child_frame)

    return bool(result)


def structural_identity_digest(expr: Optional[Expression]) -> Optional[str]:
    """完全比較と **同じ同値関係** を持つ安定 digest（equivalence digest）。

    `structural_equals(a, b)` が真なら `identity_digest(a) == identity_digest(b)`。
    これは「完全比較の前置き（prefilter）として使ってよい」という契約そのもので、
    逆向き（digest 一致 ⇒ 等価）は保証しない。

    candidate hash とは **別の値**（domain separation 済み）で、契約も違う:
    candidate hash は bucket 専用の 16 byte、こちらは外へ出せる 32 byte の
    安定 identity。混同すると「bucket が一致したから同じ式」という誤用が通って
    しまうので、値そのものを分けてある。

    `id()` にも process 状態にも依存しない。graph のどこかが値として固定でき
    ない object を含み digest だけでは区別できない場合は `None` を返す。
    辺の順や共有の仕方が残る **表現** の digest が要るなら
    `semantic_snapshot.graph_representation_digest()`（別の同値関係）。
    """

    expr = _validated(expr)
    if expr is None:
        return None
    # 凍結が `__dict__` に置いた値だけを owner の API で読む（出力の入口から live な値が渡る）
    complete = live_values.instance_state(expr, "_identity_complete", False)
    if complete is not True and (complete is False or not live_values.as_bool(complete)):
        return None
    digest = live_values.instance_state(expr, "_equivalence_digest", None)
    if type(digest) is bytes:
        return digest.hex()
    if digest is None:
        return None
    # 凍結が置くのは `bytes` だけ（それ以外の値の method は呼ばない）
    raise TypeError(f"equivalence digest is not bytes ({live_values.type_name(type(digest))})")


class StructuralIdentity:
    """structural identity の安定 interface（この module が唯一の owner）。

    比較方針を変えたいときに触るのはこの class の実装だけで、consumer
    （`Condition.equals` / dedup / cache）は変わらない。solver query identity や
    rewrite identity と **統合しない**: 同じ式でも solver 宣言や rewrite 文脈が
    違えば別物で、片方の都合で他方の一致条件を動かしてはいけない。
    """

    #: bucket / 早期棄却の専用値（16 byte）。等価の確定にも外部 identity にも
    #: 使わない。衝突は設計上あり得る。
    candidate_hash = staticmethod(candidate_hash)
    #: 完全比較（distinct な node 組に比例、可換正規化あり）。**唯一の決定者**。
    equals = staticmethod(structural_equals)
    #: 予算付きの canonical key（placeholder を含むものは比較に使わない）
    key = staticmethod(expression_key)
    #: 完全比較と同じ同値関係を持つ安定 digest（32 byte、prefilter に使える）
    identity_digest = staticmethod(structural_identity_digest)


# ---------------------------------------------------------------------------
# 条件の集合の structural identity（Issue #105 PR-105-A）
# ---------------------------------------------------------------------------

_CONDITIONS_SIGNATURE_PERSON = b"conds-sig-v1"


def _condition_bucket(condition: Condition) -> bytes:
    """条件 1 つの bucket 値（candidate hash + 向き）。**一致の確定には使わない**。"""

    digest = candidate_hash(condition.expression) or b""
    return (b"\x01" if condition.negated else b"\x00") + digest


class ConditionsSignature:
    """条件の **多重集合** の structural identity（dedup / dict key 用）。

    旧 `object_centric_conditions_signature` は予算付き `condition_key` の tuple を
    `repr` 順に並べた値で、予算を超えた 2 つの条件は同じ `("truncated", …)` の
    placeholder になり **別の条件なのに一致** していた。ここでは:

    * `fast` — 各条件の candidate hash と向きから作る bucket 値（`__hash__` だけが
      使う）。衝突は設計上あり得るので **等価の確定には使わない**。
    * 等価（`__eq__`）— 同じ bucket 値の条件どうしを `Condition.equals`（DAG-aware な
      完全比較、`structural_equals`）で 1 対 1 に対応付けられたときだけ一致。
      `Condition.equals` は同値関係なので、同じ bucket の中で貪欲に対応付けても
      多重集合の一致を取り逃さない。比較予算を超えた組は不一致（cache / dedup の
      miss になるだけで、別の条件を同一視しない）。

    順序は意味を持たない（条件の conjunction）。条件 object は保持するので、
    `id()` の再利用で別の条件と取り違えることはない。
    """

    __slots__ = ("fast", "_conditions", "_buckets")

    def __init__(self, conditions) -> None:
        items = [(_condition_bucket(condition), condition) for condition in conditions or ()]
        items.sort(key=lambda item: item[0])
        digest = hashlib.blake2b(digest_size=16, person=_CONDITIONS_SIGNATURE_PERSON)
        digest.update(b"%d|" % len(items))
        for bucket, _condition in items:
            digest.update(b"%d:" % len(bucket))
            digest.update(bucket)
        self.fast = digest.digest()
        self._buckets = tuple(bucket for bucket, _condition in items)
        self._conditions = tuple(condition for _bucket, condition in items)

    def __len__(self) -> int:
        return len(self._conditions)

    @property
    def conditions(self) -> Tuple[Condition, ...]:
        """bucket 値の順に並べた条件（同じ bucket の中は入力順）。"""

        return self._conditions

    def __hash__(self) -> int:
        return hash(self.fast)

    def __eq__(self, other: Any) -> bool:
        if self is other:
            return True
        if not isinstance(other, ConditionsSignature):
            return NotImplemented
        if self.fast != other.fast or self._buckets != other._buckets:
            return False
        # bucket 値の列が同じなので、同じ bucket の区間どうしを対応付ければよい
        index = 0
        count = len(self._conditions)
        while index < count:
            end = index + 1
            while end < count and self._buckets[end] == self._buckets[index]:
                end += 1
            unmatched = list(other._conditions[index:end])
            for condition in self._conditions[index:end]:
                for position, candidate in enumerate(unmatched):
                    if condition is candidate or condition.equals(candidate):
                        del unmatched[position]
                        break
                else:
                    return False
            index = end
        return True

    def __ne__(self, other: Any) -> bool:
        equal = self.__eq__(other)
        return equal if equal is NotImplemented else not equal

    def __repr__(self) -> str:
        # logging / 例外から暗黙に呼ばれるので条件を描画しない（Issue #22 の有界性）
        return f"ConditionsSignature(conditions={len(self._conditions)}, fast={self.fast.hex()[:12]})"


def conditions_signature(conditions) -> ConditionsSignature:
    """条件の多重集合の structural identity（`ConditionsSignature`）。"""

    return ConditionsSignature(conditions)
