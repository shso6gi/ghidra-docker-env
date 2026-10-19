"""bounded path が live な値を読む **唯一の** 規則（Issue #22 PR-22-D）。

bounded path（walker・canonical digest・snapshot の codec・有界な証拠・key・出力の準備）は、
解析が持ってきた値（JPype の `JInt`・Ghidra の object・test の object・上書きした容器）を
この module の関数だけで読む。ここに無い読み方（`int(x)` / `float(x)` / `str(x)` /
`repr(x)` / `hash(x)` / `len(x)` / `iter(x)` / `isinstance(x, T)` / `getattr(x, name)` /
`dataclasses.fields(x)`）は live な値の user code（`__int__` / `__float__` / `__str__` /
`__repr__` / `__hash__` / `__len__` / `__iter__` / `__class__` / `__getattr__` / property /
metaclass の `__getattribute__`）を呼び得る。`tests/unit/test_issue22d_capabilities.py` の
J19（`tests/unit/_live_flow_audit.py`）が bounded path の関数からそれらの直接の呼び出しを拒む。

規則:

* 型は `type(x)` だけで決める（`isinstance` は上書きした `__class__` を読む）。型の属性は
  `type_attribute`（組み込みの slot `type.__dict__["__mro__"]` / `["__dict__"]` だけを読む）で読む。
  `inspect.getattr_static` は使わない（`klass.__dict__` を普通の属性の読みで引くので metaclass の
  `__getattribute__` を呼び、名前の比較で namespace の key の `__eq__` を呼び得る）。
* scalar の subclass（`bool` / `int` / `float` / `str`）は基底型の slot で基底型の値にする
  （`int.__index__` / `float.__float__` / `str.__str__`）。enum は scalar として扱わない。
* 容器は組み込みの振る舞い（`items` / `__iter__` / `__len__` / `__getitem__` を上書きしない
  dict / OrderedDict / list / tuple / set / frozenset、組み込みの dict を包む `MappingProxyType`、
  組み込みの容器の iterator）だけを辿る。
* instance の属性は instance の `__dict__` / slot から読む。property は package の型のもの
  （record の API）だけを呼ぶ。
"""

from __future__ import annotations

import functools
import gc
import itertools
import math
import operator
import os
import sys
import threading
import weakref
import types
import contextvars
from collections import OrderedDict
import collections
from enum import Enum
from typing import Any, Dict, Iterator, List, NoReturn, Optional, Tuple

#: 基底型でない値に `plain_scalar` / `*_value` が返す印
NOT_PLAIN = object()
#: package の directory（この file の 1 つ上）。package の code（関数・generator・property）の判定に使う
PACKAGE_DIR = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")) + os.sep
#: package の中でも package の code として信頼しない directory（test / fixture: 記録した Ghidra の
#: 値の代わりの object は live な値と同じに扱う）。test の harness だけが `trust_code_directory` で足す
_UNTRUSTED_DIRS = (os.path.join(PACKAGE_DIR, "tests") + os.sep,)
_TRUSTED_EXTRA_DIRS: list = []
_PACKAGE_FILES: dict = {}

#: 作業量を受け取らずに読む live な storage の数の上限（**固定の上限の型の契約**）。長さは組み込みの
#: slot で O(1) に読み、辿る前に比べる。上限の意味は読むものの種類で 2 つに分ける:
#:
#: * **型**（class の namespace と MRO・closure の cell・dataclass の field の表）: 型の信頼の判定の
#:   一部で、型ごとに cache する。上限の外は「確かめられない」= 信頼しない（述語）/ `TypeError`（型の
#:   属性を読む関数）。文脈（作業量の有無）に依らない値にする（cache の判定が履歴で変わらない）。
#: * **値の storage**（dict / instance の `__dict__` の key・key の tuple の node・包んだ
#:   `MappingProxyType` の段・写す容器）: 上限の外は安全でないという判定ではなく **量** の問題で、
#:   意味はこの module が決めない。量は種類ごとに別（容器の要素・key の tuple の node・包んだ proxy の段）で、
#:   1 回の走査の中の和をそれぞれ上限と比べる（上限の積にしない）。上限の外の意味は今の文脈の量の owner が
#:   決める（`_StorageRead.admit` の 1 箇所）:
#:
#:   - 作業量を持つ owner の読み（`metered_storage_reads`）: 超えた分をその作業量へ数えて読む（超過の
#:     意味はその作業量の owner のもの。上限の無い作業量は組み込みの容器と同じく上限なしで読む）。
#:   - 意味を自分で決めると宣言した読み（`signalled_storage_reads`）: 量の信号
#:     `StorageBeyondReadBound` を呼ぶ側へ上げる（型の信頼の判定・診断の写し）。
#:   - 固定の上限の owner の読み（`fixed_bound_reads`: `core/read_limits` の入口）と、量の owner の
#:     無い文脈の **隠れた読み**（呼ぶ側が辿ると頼んでいない走査: key で引く・名前で属性を読む・1 つの
#:     key を確かめる・proxy を剥がす）: 登録した量の意味の owner（`core/read_limits`）が型つきの限界を
#:     台帳へ記録して上げる（`register_unmetered_read_owner`）。
#:   - 量の owner の無い文脈の **反復の確かめ**（反復・写しの前に、これから辿る要素の key の hash を
#:     確かめる走査）: その反復の一部（量の owner は反復の owner）。量の owner の無い反復は組み込みの容器を
#:     上限なしで辿る（J22 が呼ぶ側を分類する）ので、確かめも上限なしで読む（dict と `OrderedDict` で
#:     結果を変えない）。
#:
#:   述語は量のせいで「安全でない」（False / None / `TypeError`）とは答えない。
#:
#: 上限は package と実行環境の型の namespace・record の instance の状態・解析の record の key の実測の
#: 最大に対して十分大きい 2 の冪（実測は test ではなく PR-22-D の検証の固定 subset: 結果 JSON の列の長さ
#: 177・mapping の key 57・入れ子の深さ 30。固定 subset で読みの上限の限界は 0 件）
SCAN_LIMIT = 1 << 12


def _within_scan(count: int) -> bool:
    """**型の** storage の数 `count`（組み込みの slot で読んだ長さ）が上限の中か（述語の側）。"""

    return count <= SCAN_LIMIT


def _require_scan(count: int, what: str) -> None:
    """**型の** storage の数が上限の中でなければ `TypeError`（型の属性を読む関数の側。辿る前に O(1) で比べる）。"""

    if count > SCAN_LIMIT:
        raise TypeError(f"{what} has {count} entries, more than the bounded path reads ({SCAN_LIMIT})")


class StorageBeyondReadBound(Exception):
    """値の storage の読みが固定の上限（`SCAN_LIMIT`）を超えた（**量の信号**）。

    「安全に読めない」という判定（`TypeError`）ではなく、意味の限界（`AnalysisLimitation`）でもない:
    どちらの型からも派生しない（`except TypeError` の回復用の handler が「安全でない値」と読み替えない、
    限界の種類を live な値の owner が決めない）。上がるのは `signalled_storage_reads` の中（呼ぶ側が
    その場で意味を決める）と、量の意味の owner が登録されていない process（この module だけを使う
    test）だけ。pair の境界へは届かない（作業量を受け取らない読みは登録した owner が限界にする）。
    """

    def __init__(self, what: str, observed: int) -> None:
        super().__init__(f"{what} has at least {observed} entries, more than a read without a work budget reads ({SCAN_LIMIT})")
        self.what = what
        self.observed = observed
        self.limit = SCAN_LIMIT


#: 値の storage の読みを数える作業量の型（`register_storage_meter` で owner が登録する: `JsonBudget`）
_STORAGE_METER_TYPES: list = []
#: 今の読みの量の owner（context ごと）: 作業量（`metered_storage_reads`）・`_SIGNALLED`
#: （`signalled_storage_reads`）・`_FixedReads`（`fixed_bound_reads`: 入れ子の量の和）・`None`（量の owner の無い文脈）
_STORAGE_METER = contextvars.ContextVar("live_values_storage_meter", default=None)
#: `signalled_storage_reads` の中の印（量の信号を呼ぶ側へ上げる）
_SIGNALLED = object()
#: 作業量を受け取らない読みの量の意味の owner（`register_unmetered_read_owner` で 1 つだけ）
_UNMETERED_READ_OWNER: list = []


def register_storage_meter(kind: type) -> None:
    """値の storage の読みを数えてよい作業量の型を登録する（作業量の owner が import のときに 1 度）。

    その型（と subclass）の `charge(units)` は、上限を超えたら自分の超過（`JsonBudgetExhausted` /
    terminal な作業量の限界）を上げる owner の method（上限の無い作業量は数えるだけ）。
    """

    if type(kind) is not type or not package_type(kind):
        raise TypeError("a storage meter is a package type")
    if not any(kind is known for known in _STORAGE_METER_TYPES):
        _STORAGE_METER_TYPES.append(kind)


def register_unmetered_read_owner(owner: Any) -> None:
    """作業量を受け取らない読みが固定の上限を超えたときの意味の owner を登録する（`core/read_limits` が
    import のときに 1 度。2 つ目の owner は `ValueError`）。

    `owner(what, observed)` は型つきの限界を台帳へ記録して上げる package の関数（戻らない。戻れば量の
    信号を上げる）。この module は限界の種類を知らない（標準 library だけを import する）ので、owner の
    側が自分を登録する。
    """

    if type(owner) is not types.FunctionType or not package_code(owner.__code__):
        raise TypeError("an unmetered read owner is a package function")
    if _UNMETERED_READ_OWNER:
        if _UNMETERED_READ_OWNER[0] is not owner:
            raise ValueError("the unmetered read owner is already registered")
        return
    _UNMETERED_READ_OWNER.append(owner)


def _registered_meter(meter: Any) -> bool:
    kind = type(meter)
    # 登録した型そのもの（walk ごとに作る owner の作業量の大半）は同一性だけで。subclass は MRO を辿る
    for base in _STORAGE_METER_TYPES:
        if kind is base:
            return True
    return any(_in_mro(base, kind) for base in _STORAGE_METER_TYPES)


class metered_storage_reads:
    """この中の値の storage の読みは、固定の上限を超えた分を `meter` へ数えて読む（作業量を持つ owner だけが使う）。

    固定の上限の中の分は数えず、超えた分だけを `meter.charge` へ（上限の内側の入力の勘定を変えない）。
    上限の無い作業量の読みは上限なしで読む（その owner は組み込みの容器も上限なしで辿る: 容器の種類で
    結果を変えない）。入れ子では内側の作業量で数える（読むのは内側の owner の走査）。`meter` が `None`
    なら何もしない（外の owner をそのまま使う: 作業量の無い入れ子の owner が、外の作業量で数えている
    読みを数えない読みへ戻さない）。
    """

    __slots__ = ("meter", "_token")

    def __init__(self, meter: Any) -> None:
        if meter is not None and not _registered_meter(meter):
            # 回復用の `except TypeError` に吸われないように `ValueError`（owner の不備で、値の判定ではない）
            raise ValueError(f"{type_name(type(meter))} is not a registered storage meter")
        self.meter = meter
        self._token = None

    def __enter__(self) -> Any:
        if self.meter is not None:
            self._token = _STORAGE_METER.set(self.meter)
        return self.meter

    def __exit__(self, *_exc: Any) -> None:
        if self._token is not None:
            _STORAGE_METER.reset(self._token)
            self._token = None


class _FixedReads:
    """固定の上限の owner の文脈の、走査の中でしか数えられない入れ子の量（key の tuple の node）の和。
    文脈の中の読み全部で共有する（入口が共有の scan の `fixed_reads()` を渡せば、その scan の読み全部で:
    入れ子の読みを呼び出しごとに上限まで辿ると上限の積になる）。"""

    __slots__ = ("nodes",)

    def __init__(self) -> None:
        self.nodes = _StorageRead(_KEY_NODES)


def fixed_reads() -> _FixedReads:
    """`fixed_bound_reads` が共有する入れ子の量（`core/read_limits` の共有の scan が 1 つ持つ）。"""

    return _FixedReads()


class fixed_bound_reads:
    """この中の値の storage の読みは、反復の確かめも含めて固定の上限で読み、上限の外は登録した量の意味の
    owner の限界（作業量を受け取らない読みの入口 `core/read_limits` だけが使う: 入口が O(1) で数えた要素の
    中の、走査の中でしか数えられない量（key の tuple の node）も同じ上限にする）。使うたびに作る。
    `reads` を渡すと、その入れ子の量の和を呼び出しをまたいで共有する。"""

    __slots__ = ("reads", "_token")

    def __init__(self, reads: Optional[_FixedReads] = None) -> None:
        if reads is not None and type(reads) is not _FixedReads:
            raise TypeError("fixed bound reads share a fixed_reads() accumulator")
        self.reads = _FixedReads() if reads is None else reads
        self._token = None

    def __enter__(self) -> None:
        self._token = _STORAGE_METER.set(self.reads)

    def __exit__(self, *_exc: Any) -> None:
        _STORAGE_METER.reset(self._token)
        self._token = None


class signalled_storage_reads:
    """この中の値の storage の読みは、上限を超えたら量の信号 `StorageBeyondReadBound` を呼ぶ側へ上げる
    （作業量で数えず、限界も記録しない）。量の意味をその場で決める owner だけが使い、同じ関数の中で
    信号を捕まえる（型の信頼の判定: 文脈に依らない「信頼しない」。診断の写し: 写せた先頭まで）。
    使うたびに作る（token を instance が持つ: thread・入れ子の間で共有しない）。
    """

    __slots__ = ("_token",)

    def __init__(self) -> None:
        self._token = None

    def __enter__(self) -> None:
        self._token = _STORAGE_METER.set(_SIGNALLED)

    def __exit__(self, *_exc: Any) -> None:
        _STORAGE_METER.reset(self._token)
        self._token = None


class _StorageRead:
    """値の storage を 1 回読む走査の 1 つの量の数（上限までは固定の上限の中。超えた分の意味は文脈の owner）。

    `traversal` は反復の確かめ（反復・写しの前に、これから辿る要素を確かめる走査）: 量の owner の無い
    文脈では反復と同じく上限なしで読む。それ以外は隠れた読み（呼ぶ側が辿ると頼んでいない走査）。確かめの
    中の隠れた読み（key が enum の member なら、その hash が読む member の状態を名前で読む）は隠れた読みの
    まま（key を hash する容器だけが読む量で、key の tuple の node と同じ種類の違い）。
    """

    __slots__ = ("what", "used", "traversal")

    def __init__(self, what: str, traversal: bool = False) -> None:
        self.what = what
        self.used = 0
        self.traversal = traversal

    def admit(self, count: int) -> None:
        before = self.used
        used = before + count
        self.used = used
        if used <= SCAN_LIMIT:
            return
        # 上限の外の意味は今の文脈の量の owner が決める（この 1 箇所だけ）
        meter = _STORAGE_METER.get()
        if meter is None:
            if self.traversal:
                # 量の owner の無い反復の確かめ: 反復の一部で、反復と同じく上限なしで読む
                return
            self._beyond_fixed_bound(used)
        if type(meter) is _FixedReads:
            self._beyond_fixed_bound(used)
        if meter is _SIGNALLED:
            raise StorageBeyondReadBound(self.what, used)
        charge = _type_lookup(type(meter), "charge", None)
        if type(charge) is not types.FunctionType:
            raise ValueError(f"{type_name(type(meter))} has no charge method")
        # 固定の上限の中の分は数えない（上限の内側の入力の勘定を変えない）: 超えた分だけ
        charge(meter, used - max(before, SCAN_LIMIT))


    def _beyond_fixed_bound(self, used: int) -> NoReturn:
        # 固定の上限の外: 登録した量の意味の owner が限界を記録して上げる（戻れば量の信号）
        if _UNMETERED_READ_OWNER:
            _UNMETERED_READ_OWNER[0](self.what, used)
        raise StorageBeyondReadBound(self.what, used)


#: key の tuple の node（容器の要素の数と別の量）の読みの名前
_KEY_NODES = "a mapping's key tuple nodes"
#: 包んだ proxy の段（容器の要素の数と別の量）の読みの名前
_PROXY_LAYERS = "a chain of mapping proxies"


def _key_nodes(traversal: bool = False) -> "_StorageRead":
    """1 回の走査の key の tuple の node の読み（固定の上限の文脈では文脈の中の読み全部で共有する）。"""

    context = _STORAGE_METER.get()
    if type(context) is _FixedReads:
        return context.nodes
    return _StorageRead(_KEY_NODES, traversal)


def _admit_storage(count: int, what: str, traversal: bool = False) -> None:
    """値の storage `count` 個を 1 回の走査の 1 つの量として読んでよいか（`_StorageRead` の 1 回分）。"""

    if count <= SCAN_LIMIT:
        # 上限の内側（よくある形）は数えるものが無い
        return
    _StorageRead(what, traversal).admit(count)


class _Scan:
    """入れ子の走査（class の body の値・包んだ callable）が共有する 1 つの上限（`SCAN_LIMIT`）。

    入れ子のそれぞれを別に上限まで辿ると上限の積になる: 1 つの判定の中で辿る数の和を上限にする。
    """

    __slots__ = ("used",)

    def __init__(self) -> None:
        self.used = 0

    def admit(self, count: int) -> bool:
        """`count` 個をこの判定の上限の中で辿ってよいか（よければ数える）。"""

        if self.used + count > SCAN_LIMIT:
            return False
        self.used += count
        return True


#: 型の信頼の判定の入れ子（class の中の値が別の型を指し、その型の判定が始まる）の深さの上限。
#: 判定は型ごとに 1 度だけで（cache）、入れ子は Python の stack を使うので、その余裕の中の小さい値
NESTING_LIMIT = 32


class _Nesting(threading.local):
    """型の信頼の判定の途中の状態（thread ごと。途中の仮の「信頼」を他の thread の判定へ見せない）。

    信頼は単調（信頼すると仮定する型が増えれば、信頼する型は増えるだけ）で、判定は最大不動点:
    循環の途中の型（自分・祖先）は判定の間だけ信頼する側に置く。

    * `active`: 判定の途中の型 → 入れ子の深さ
    * `assumed`: 今の判定が仮定した途中の型の深さの最小（仮定しなければ `NESTING_LIMIT + 1`）
    * `cut`: 今の判定が入れ子の上限に当たったか（上限で切った「信頼しない」は悲観的な値: 残さない）
    * `provisional_types` / `provisional_bodies`: 途中の祖先を仮定して「信頼」と出した判定 → 仮定した深さ。
      同じ判定の中では仮定ごと使い回し（循環の中の型を何度も判定し直さない）、仮定した深さの判定が
      終わるときに確定させる（その判定が「信頼」なら残し、そうでなければ捨てる）。`by_depth` はその深さ
      ごとの組（1 つの判定は高々 `NESTING_LIMIT` 回しか組を移らない）
    * 楽観的な仮定の下で「信頼しない」と出た判定は（上限で切っていなければ）仮定に依らず確定

    同じ thread の判定の途中に割り込んで判定を呼ぶ code（finalizer・weakref の callback）は、途中の型を
    仮の「信頼」として読む（threat model の外: 解析の値は判定の途中に code を実行しない）。
    """

    def __init__(self) -> None:
        self.active: dict = {}
        self.assumed = NESTING_LIMIT + 1
        self.cut = False
        #: 1 つの最も外の判定の中で読んだ class ごとの名前空間の snapshot（`_namespace_part`。判定は型を読むだけで外の code を呼ばない:
        #: 判定の間は class が変わらないので、祖先を何度辿っても 1 度だけ読む）
        self.class_states: dict = {}
        #: 1 つの最も外の判定の中で名前空間を読んだ heap class の列（判定の途中に引いた記録の依存も足す）。1 つの判定の
        #: 結果は、判定を始めたときの長さから後の class の名前空間に依る（値の型の `__get__`・入れ子の型）: 記録は
        #: その class 全部の状態を比べる（`_TypeFactTable.record`）
        self.reads: list = []
        #: 1 つの最も外の判定の中で、判定が型・中身を読んだ object の列（名前空間の値が包む関数・accessor・closure の
        #: 中身・wrapper が包む callable）。identity が同じでも変わる状態（`_watch`）を記録が確かめる
        self.objects: list = []
        self.provisional_types: dict = {}
        self.provisional_bodies: dict = {}
        self.by_depth: list = [[] for _ in range(NESTING_LIMIT + 1)]


def _settle(state: "_Nesting", depth: int, *, commit: bool, retag: Optional[int] = None) -> None:
    """深さ `depth` の判定が終わった: それを仮定した仮の判定を確定する（残す / 捨てる / さらに外の仮定へ）。"""

    group = state.by_depth[depth]
    state.by_depth[depth] = []
    for table, key in group:
        if table.get(key) != depth:
            continue
        if retag is not None:
            table[key] = retag
            state.by_depth[retag].append((table, key))
            continue
        del table[key]
        if commit:
            # 仮の判定の依存は、最も外の判定が読んだ class 全部（上位集合: 捨てる機会が増えるだけ）
            (_PACKAGE_TYPES if table is state.provisional_types else _TRUSTED_BODIES).record(
                key, True, state.reads, state.class_states, state.objects
            )


def _provisionally(state: "_Nesting", table: dict, key: Any, assumed: int) -> None:
    table[key] = assumed
    state.by_depth[assumed].append((table, key))


_NESTING = _Nesting()


def trust_code_directory(path: str) -> None:
    """test の harness が自分の code（test の module の record・converter・reducer）を信頼する。

    **test の harness（`tests/conftest.py`）だけが呼ぶ**。production は呼ばない（信頼は package の
    code だけ。`tests/unit/test_issue22d_capabilities.py` が呼び出し元を固定する）。足すだけで
    取り消さない。code の file 名は `compile` で偽れるが、それは code を書いて実行できる側の操作で
    （live な値の側からはできない）、この信頼の境界の外。
    """

    directory = os.path.normpath(os.path.abspath(path)) + os.sep
    if directory not in _TRUSTED_EXTRA_DIRS:
        _TRUSTED_EXTRA_DIRS.append(directory)
        _PACKAGE_FILES.clear()


def package_file(path: Any) -> bool:
    """file の path が package の code か（正規化して 1 度だけ調べる。test / fixture は除く）。"""

    if type(path) is not str:
        return False
    known = _PACKAGE_FILES.get(path)  # 組み込みの str の key（hash・比較は組み込みの実装）
    if known is None:
        if not os.path.isabs(path):
            # 相対の file 名（`<string>`・cwd に依る名前）は package の code ではない
            known = False
        else:
            normalized = os.path.normpath(os.path.abspath(path))
            known = any(normalized.startswith(directory) for directory in _TRUSTED_EXTRA_DIRS) or (
                normalized.startswith(PACKAGE_DIR)
                and not any(normalized.startswith(directory) for directory in _UNTRUSTED_DIRS)
            )
        _PACKAGE_FILES[path] = known
    return known


def package_code(code: Any) -> bool:
    """code object が package の file のものか（code の file 名は型の `__module__` と違い書き換えられない）。"""

    return type(code) is types.CodeType and package_file(code.co_filename)


def package_function(value: Any) -> bool:
    """package の code の関数か（型の MRO から引いた protocol の method・converter を呼んでよいかの判定）。"""

    return type(value) is types.FunctionType and package_code(value.__code__)


def _note_read(klass: type) -> None:
    """型の信頼の判定の途中なら、名前空間を読んだ heap class を判定の依存に足す（`_Nesting.reads`）。"""

    state = _NESTING
    if state.active:
        state.reads.append(klass)


class _TypeFactTable:
    """型ごとの事実（型の名前空間から決めた判定）の表。**引くたびに** 事実が依る状態が記録したときと同じかを確かめる。

    型の状態（`_class_snapshot` / `_state_check` / `_state_holds`）: 型の metaclass と MRO の identity、MRO の heap type の class ごとの metaclass と名前空間の
    key と値の identity。外の code は class の名前空間・`__bases__`・`__class__` を書き換えられるので、状態が変われば
    記録を捨てて判定し直す（古い判定を使わない）。記録は key の型と名前空間の key・値を生かす（`id` を再利用させない）。
    組み込みの型（heap type でない）の名前空間は変わらない。key は型か型の tuple で、`id` で引く（型の metaclass の
    `__hash__` / `__eq__` を呼ばない）。

    依存（`record` の `depends`）: 判定が key の型の MRO の外の class の名前空間も読んだとき（型の信頼の判定: 名前空間
    の値の型・入れ子の型。`_Nesting.reads`）、その class ごとの状態（metaclass・MRO の identity と名前空間）も比べる。
    判定の途中に引いた記録は、その依存を今の判定の依存へ足す（入れ子の判定の結果を cache から使っても、外の判定の
    依存から落ちない）。
    """

    __slots__ = ("entries", "extra")

    def __init__(self, extra: Any = None) -> None:
        #: slot → (key, 型と依存の class の状態の確かめ（`_state_check`）, 値, 依存の class, extra の状態, extra の生かす object,
        #: 判定が読んだ object)
        self.entries: Dict[Any, Tuple[Any, Any, Any, Tuple[type, ...], Any, Any]] = {}
        #: 判定が名前空間の値の **中身** も読むとき、その中身の状態（`(identity の tuple, 生かす list)` を返す関数）
        self.extra = extra

    @staticmethod
    def _key(key: Any) -> Tuple[Any, type]:
        if type(key) is tuple:
            return tuple(map(id, key)), key[0]
        return id(key), key

    def get(self, key: Any, default: Any = None) -> Any:
        slot, kind = self._key(key)
        entry = self.entries.get(slot)
        if entry is None:
            return default
        recorded = entry[0]
        same = all(map(_IS, recorded, key)) if type(key) is tuple else recorded is key
        if not same:
            return default
        if not _state_holds(entry[1]):
            return default
        if self.extra is not None and self.extra(kind)[0] != entry[4]:
            return default
        nesting = _NESTING
        if nesting.active:
            # 判定の途中に記録を使った: その記録が依る class（記録の依存と key の型の MRO）は今の判定の依存
            nesting.reads.extend(entry[3])
            nesting.reads.extend(_TYPE_MRO.__get__(kind))
            nesting.objects.extend(entry[6])
        return entry[2]

    def __setitem__(self, key: Any, value: Any) -> None:
        self.record(key, value)

    def record(
        self, key: Any, value: Any, reads: Any = (), memo: Optional[dict] = None, objects: Any = (),
    ) -> None:
        """事実を記録する。`reads` は判定が名前空間を読んだ class の列（重複・key の型の MRO の class は除いて持つ）。
        `memo` は記録の直前に終わった判定が読んだ名前空間の snapshot（その間に外の code は走っていない: 使い回す）。
        `objects` は判定が型・中身を読んだ object の列（`_Nesting.objects`: その状態も確かめる）。"""

        slot, kind = self._key(key)
        depends: Tuple[type, ...] = ()
        if reads:
            mro = _TYPE_MRO.__get__(kind)
            if not _within_scan(tuple.__len__(mro)) or not _within_scan(len(reads)):
                return  # 依存を上限の中で読めない: 記録しない（毎回判定する）
            own = {id(klass) for klass in mro}
            unique: Dict[int, type] = {}
            for klass in reads:
                if id(klass) not in own:
                    unique[id(klass)] = klass
            depends = tuple(unique.values())
        snapshot = _class_snapshot(kind, memo)
        if snapshot is None:
            return  # 状態を読めない型の事実は記録しない（毎回判定する）
        parts = []
        for klass in depends:
            part = _dependency_part(klass, memo)
            if part is None:
                return
            parts.append(part)
        extra, extra_held = self.extra(kind) if self.extra is not None else (None, None)
        if len(self.entries) >= _TYPE_FACTS_LIMIT:
            self.entries.clear()
        objects = tuple({id(item): item for item in objects}.values())
        if not _within_scan(tuple.__len__(objects)):
            return  # 読んだ object を上限の中で確かめられない: 記録しない（毎回判定する）
        check = _state_check(snapshot, parts, _watch(objects))
        if check is None:
            return
        self.entries[slot] = (key, check, value, depends, extra, extra_held, objects)

    def clear(self) -> None:
        self.entries.clear()

    def __len__(self) -> int:
        return len(self.entries)


def _dependency_part(klass: type, memo: Optional[dict] = None) -> Optional[Tuple[Any, ...]]:
    """依存の class 1 つの snapshot（`_state_check` にまとめ、`_state_holds` が確かめる）。組み込みの型は MRO の identity だけ。読めない（上限の外）は
    `None`。"""

    if not _TYPE_FLAGS.__get__(klass) & _HEAP_TYPE:
        return (klass, _TYPE_MRO.__get__(klass), None)
    part = _namespace_part(klass, memo)
    if part is None:
        return None
    return (klass, _TYPE_MRO.__get__(klass), part)


#: 型の事実の表の大きさの上限（超えたら空にする: 正しさは引くときの確かめが持つ）
_TYPE_FACTS_LIMIT = 4096


def _class_snapshot(kind: type, memo: Optional[dict] = None) -> Optional[Tuple[Any, Any, Any, Tuple[Any, ...]]]:
    """型の snapshot（型・MRO の tuple・metaclass と、MRO の heap type ごとの名前空間の snapshot）。`_state_holds` が
    今も同じかを確かめる。読めない（MRO・名前空間が型の上限を超える）型は `None`: その型の事実は記録しない（型の判定は
    文脈に依らない: 量の信号にしない）。snapshot は読んだ object（MRO・名前空間の storage・key・値）を生かす（`id` を
    再利用させない）。

    hook を呼ばない: 名前空間は storage の dict を C の反復で読む（key の `__hash__` / `__eq__` を呼ばない）。型の信頼の
    判定の途中（`_NESTING.active`）は、読んだ class の snapshot を判定の間だけ使い回す。
    """

    mro = _TYPE_MRO.__get__(kind)
    if not _within_scan(tuple.__len__(mro)):
        return None
    parts = []
    for klass in mro:
        if not _TYPE_FLAGS.__get__(klass) & _HEAP_TYPE:
            continue
        part = _namespace_part(klass, memo)
        if part is None:
            return None
        parts.append(part)
    return (kind, mro, type(kind), tuple(parts))


def _state_check(
    snapshot: Tuple[Any, Any, Any, Tuple[Any, ...]], dependencies: Any = (), objects_watch: Any = (),
) -> Optional[Tuple[Any, ...]]:
    """型の snapshot（`_class_snapshot`）と依存の class の snapshot（`_dependency_part`）を、確かめる列にまとめる
    （`_state_holds` が確かめる）: MRO を確かめる class と MRO の tuple・metaclass を確かめる class と metaclass・名前空間の
    storage と大きさ・全部の名前空間の key と値（並べた列）・読んだ値の状態（`_watch`）。列は読んだ object を生かす。class の数が上限の外は
    `None`（記録しない）。"""

    kind, mro, metatype, own_parts = snapshot
    if not _within_scan(tuple.__len__(own_parts) + len(dependencies)):
        return None
    owners = [kind]
    mros = [mro]
    parts = list(own_parts)
    for klass, klass_mro, part in dependencies:
        owners.append(klass)
        mros.append(klass_mro)
        if part is not None:
            parts.append(part)
    classes = [kind]
    metas = [metatype]
    raws = []
    lengths = []
    keys: List[Any] = []
    values: List[Any] = []
    watches = []
    for klass, meta, raw, part_keys, part_values, watched in parts:
        classes.append(klass)
        metas.append(meta)
        raws.append(raw)
        lengths.append(tuple.__len__(part_keys))
        keys.extend(part_keys)
        values.extend(part_values)
        if watched is not _NO_WATCH:
            watches.append(watched)
    if objects_watch:
        watches.append(objects_watch)  # 判定が型・中身を読んだ object（`_Nesting.objects`）
    watch = _merged_watch(watches)
    if watch is _NO_WATCH:
        watch = ((),) * _WATCH_COLUMNS
    (
        heap_objects, heap_types, props, fgets, fsets, fdels, statics, static_funcs, methods, method_funcs, others, states,
        functions, codes,
    ) = watch
    # 確かめる object と、読んで得るはずの object を 1 つの列に並べる（`_state_holds` が 1 度の C の反復で比べる）
    expected = (
        tuple(mros) + tuple(metas) + heap_types + tuple(keys) + tuple(values) + fgets + fsets + fdels + static_funcs
        + method_funcs + codes
    )
    # `_state_holds` は `expected` と読み直す列を 1 つの `map` で比べる（短い方で止まる）: 列の長さが揃うことをここで確かめる
    read_count = (
        len(owners) + len(classes) + len(heap_objects) + 2 * sum(lengths) + 3 * len(props) + len(statics) + len(methods)
        + len(functions)
    )
    if read_count != tuple.__len__(expected):
        raise RuntimeError("type fact check columns are misaligned")
    return (
        tuple(raws), tuple(lengths), tuple(owners), tuple(classes) + heap_objects, props, statics, methods, functions,
        expected, others, states,
    )


def _state_holds(check: Tuple[Any, ...]) -> bool:
    """`_state_check` の列が今も同じか（MRO の tuple・metaclass が同じ object で、どの名前空間も同じ大きさで同じ key と値を
    同じ順に持ち、読んだ値の状態も同じ）。比べるのは identity と大きさだけ（C の反復: object を作らない。値の `__eq__` を
    呼ばない。名前空間の storage は組み込みの `dict`）。大きさを先に比べる: 並べた列の長さは記録したときと同じ（途中で
    ずれない）。名前空間の数は記録したときに上限と比べた（大きさが同じなら辿る数も同じ）。"""

    raws, lengths, owners, typed, props, statics, methods, functions, expected, others, states = check
    if not _within_scan(tuple.__len__(raws)) or tuple(map(dict.__len__, raws)) != lengths:
        return False
    if not all(map(_IS, itertools.chain(
        map(_TYPE_MRO.__get__, owners), map(type, typed),
        itertools.chain.from_iterable(map(dict.__iter__, raws)), itertools.chain.from_iterable(map(dict.values, raws)),
        map(_PROPERTY_FGET, props), map(_PROPERTY_FSET, props), map(_PROPERTY_FDEL, props),
        map(_STATICMETHOD_FUNC, statics), map(_CLASSMETHOD_FUNC, methods), map(_FUNCTION_CODE, functions),
    ), expected)):
        return False
    return _accessors_hold(others, states)


def _namespace_part(klass: type, memo: Optional[dict] = None) -> Optional[Tuple[Any, ...]]:
    """1 つの heap type の名前空間の snapshot（class・metaclass・storage・key・値）。上限の外は `None`。判定の途中は判定の
    間だけ使い回す（判定は型を読むだけで外の code を呼ばない）。"""

    if memo is None:
        nesting = _NESTING
        memo = nesting.class_states if nesting.active else None
    if memo is not None:
        found = memo.get(id(klass))
        if found is not None and found[0] is klass:
            return found
    known = _STR_KEYED_NAMESPACES.get(id(klass))
    raw = known[1] if known is not None and known[0] is klass else _unwrapped(_TYPE_DICT.__get__(klass))
    if not _within_scan(dict.__len__(raw)):
        return None
    _require_scan(dict.__len__(raw), "a class namespace's values")
    values = tuple(dict.values(raw))
    part = (klass, type(klass), raw, tuple(dict.__iter__(raw)), values, _watch(values))
    if memo is not None:
        memo[id(klass)] = part
    return part


def _watch(objects: Any) -> Any:
    """判定が読んだ object の、identity の外の状態の記録（`_watch_holds` が確かめる）。identity が同じでも変わり得るもの:

    - heap type の instance の型（`__class__` の代入で変わる。組み込みの型の instance は変えられない。module は
      `__class__` を ModuleType の subclass にできる）。
    - 組み込みの descriptor の中身（`property`（subclass を含む）の accessor・`staticmethod` / `classmethod` の関数:
      `__init__` を呼び直すと差し替わる）。heap type の descriptor（`types.DynamicClassAttribute`）の accessor（instance の
      属性）。
    - 信頼していない関数（code が package の file のものでない: 外の関数・実行環境の関数・生成された関数）の `__code__`
      （代入できる: 信頼しない判定（偽 / 中を辿る）は code に依る）と、判定が中を辿った closure の cell の中身
      （`cell_contents` は代入できる）。信頼した関数（package の code）の code・closure の書き換えは契約の外（呼ぶ code を
      書き換える操作）。

    状態は種類ごとの列（object の列と、その状態の列）にし、確かめは C の反復で identity だけを比べる（値・型の `__eq__` を
    呼ばない）。状態を持つ object が無ければ `_NO_WATCH`。読みは組み込みの descriptor の slot と型だけ。
    """

    objects = tuple(objects)
    _require_scan(tuple.__len__(objects), "the objects a type fact read")
    flags = _TYPE_FLAGS.__get__
    heap_objects: List[Any] = []
    props: List[Any] = []
    statics: List[Any] = []
    classes: List[Any] = []
    others: List[Any] = []
    functions: List[Any] = []
    for value in objects:
        kind = type(value)
        heap = flags(kind) & _HEAP_TYPE
        if heap or kind is types.ModuleType:
            heap_objects.append(value)
        if kind is property or (heap and issubclass(kind, property)):
            props.append(value)
        elif kind is staticmethod:
            statics.append(value)
        elif kind is classmethod:
            classes.append(value)
        elif kind is types.DynamicClassAttribute or kind is types.CellType:
            others.append(value)  # 状態は `_object_state`
        elif kind is types.FunctionType and not package_code(_FUNCTION_CODE(value)):
            functions.append(value)  # 信頼していない関数: 判定は `__code__` に依る
    if not (heap_objects or props or statics or classes or others or functions):
        return _NO_WATCH
    heap_objects_t, props_t, statics_t, classes_t, others_t, functions_t = (
        tuple(heap_objects), tuple(props), tuple(statics), tuple(classes), tuple(others), tuple(functions)
    )
    return (
        heap_objects_t, tuple(map(type, heap_objects_t)),
        props_t, tuple(map(_PROPERTY_FGET, props_t)), tuple(map(_PROPERTY_FSET, props_t)), tuple(map(_PROPERTY_FDEL, props_t)),
        statics_t, tuple(map(_STATICMETHOD_FUNC, statics_t)),
        classes_t, tuple(map(_CLASSMETHOD_FUNC, classes_t)),
        others_t, tuple(map(_object_state, others_t)),
        functions_t, tuple(map(_FUNCTION_CODE, functions_t)),
    )


#: 状態を持つ object が無い記録
_NO_WATCH = ()
#: `_watch` の記録の列の数（object と状態の組: heap の instance・property・staticmethod・classmethod・その他・関数）
_WATCH_COLUMNS = 14


def _object_state(value: Any) -> Tuple[Any, ...]:
    """identity の外の状態を Python の読みで取る object の状態（`_watch` の「その他」）。読めなければ毎回違う印（確かめは
    いつも偽: 判定し直す）。

    - `types.DynamicClassAttribute`（heap type の descriptor）: accessor（instance の属性）。
    - closure の cell: 中身（空の cell は `_EMPTY_CELL`）。
    """

    kind = type(value)
    try:
        if kind is types.CellType:
            try:
                return (_CELL_CONTENTS(value),)
            except ValueError:
                return (_EMPTY_CELL,)
        return tuple(instance_state(value, name, None) for name in ("fget", "fset", "fdel"))
    except TypeError:
        return (object(),)  # 読めない: 確かめはいつも偽（判定し直す）


_FUNCTION_CODE = types.FunctionType.__dict__["__code__"].__get__
_CELL_CONTENTS = types.CellType.__dict__["cell_contents"].__get__
#: 空の closure の cell の状態の印
_EMPTY_CELL = object()


def _merged_watch(watches: List[Any]) -> Any:
    """`_watch` の記録をまとめた 1 つの記録（種類ごとの列をつなぐ）。"""

    if not watches:
        return _NO_WATCH
    _require_scan(len(watches), "the records a type fact watches")  # 呼ぶ側が class の数を上限と比べた
    if len(watches) == 1:
        return watches[0]
    return tuple(tuple(itertools.chain.from_iterable(column)) for column in zip(*watches))


def _watch_holds(watch: Any) -> bool:
    """記録した状態が今も同じか（`_watch`）。"""

    if watch is _NO_WATCH:
        return True
    (
        heap_objects, heap_types, props, fgets, fsets, fdels, statics, static_funcs, classes, class_funcs, others, states,
        functions, codes,
    ) = watch
    if not _within_scan(
        tuple.__len__(heap_objects) + tuple.__len__(props) + tuple.__len__(others) + tuple.__len__(functions)
    ):
        return False
    if not all(map(_IS, itertools.chain(
        map(type, heap_objects), map(_PROPERTY_FGET, props), map(_PROPERTY_FSET, props), map(_PROPERTY_FDEL, props),
        map(_STATICMETHOD_FUNC, statics), map(_CLASSMETHOD_FUNC, classes), map(_FUNCTION_CODE, functions),
    ), heap_types + fgets + fsets + fdels + static_funcs + class_funcs + codes)):
        return False
    return _accessors_hold(others, states)


def _accessors_hold(others: Tuple[Any, ...], states: Tuple[Any, ...]) -> bool:
    """「その他」の object の状態（`_object_state`）が記録したときと同じか。"""

    if not _within_scan(tuple.__len__(others)):
        return False
    for value, state in zip(others, states):
        now = _object_state(value)
        if tuple.__len__(now) != tuple.__len__(state) or not all(map(_IS, now, state)):
            return False
    return True


_PROPERTY_FGET = property.__dict__["fget"].__get__
_PROPERTY_FSET = property.__dict__["fset"].__get__
_PROPERTY_FDEL = property.__dict__["fdel"].__get__
_STATICMETHOD_FUNC = staticmethod.__dict__["__func__"].__get__
_CLASSMETHOD_FUNC = classmethod.__dict__["__func__"].__get__


_PACKAGE_TYPES = _TypeFactTable()


def package_type(kind: type) -> bool:
    """`kind` とその MRO の class 文で作った型（heap type）の中身が、どれも信頼する code とデータだけか。

    package の外で package の型を継承した型（`__getattribute__` / property / descriptor / 関数を
    外の code で足した型）は信頼しない: 型の MRO から引いた package の関数を呼んでも、その中の
    `self.x` / `self.f()` が外の code を呼び得る。heap type ごとに `__dict__` の値を **許した種類
    だけ** に限る（`_trusted_namespace_value`）。中身を足さない subclass（空の body）は信頼する
    （足した code が無い）。組み込みの型（C で定義した型）はそのまま信頼する。
    """

    # 監査済みの code の間に確かめた型（`_Reliance.trusted`: 外の code の数が同じ間だけ）。外の code は外の code の区間で
    # だけ走り、区間を抜けるたびに数が変わる: 数が同じ間は、確かめた後に型を書き換えた code は無い
    reliance_state = _FOREIGN_EPOCH.s
    trusted = reliance_state.trusted.get(id(kind))
    if trusted is not None and trusted[0] is kind and trusted[1] == reliance_state.count:
        return True
    if not _plain_metatype(kind):
        return False
    known = _PACKAGE_TYPES.get(kind)
    if known is not None:
        return known
    state = _NESTING
    depth = state.active.get(kind)
    if depth is None:
        depth = state.provisional_types.get(kind)
    if depth is not None:
        # 判定の途中の型（自分・祖先）か、途中の祖先を仮定して「信頼」と出した型: 仮定ごと使う
        state.assumed = min(state.assumed, depth)
        return True
    depth = len(state.active)
    if depth >= NESTING_LIMIT:
        # 型の中の値が指す型の判定の入れ子が深すぎる: 信頼しない（この判定を含む判定は残さない）
        state.cut = True
        return False
    if depth == 0:
        # 最も外の判定: 前の判定の状態を持ち越さない（読んだ class の状態・読んだ class の集合も）
        state.assumed, state.cut = NESTING_LIMIT + 1, False
        state.class_states = {}
        state.reads = []
        state.objects = []
    outer_assumed, outer_cut = state.assumed, state.cut
    state.assumed, state.cut = NESTING_LIMIT + 1, False
    state.active[kind] = depth
    mark = len(state.reads)  # この判定が読む class（入れ子の判定・引いた記録の依存を含む）は、ここから後
    seen = len(state.objects)  # この判定が型・中身を読んだ object も、ここから後
    known = False
    decided = False
    try:
        known = _package_type_uncached(kind)
        decided = True
    finally:
        del state.active[kind]
        assumed, cut = state.assumed, state.cut
        # 外の判定へ渡す仮定は、終わった自分（とその内）より外の型のものだけ（自分を仮定した分は下で決まる）
        state.assumed = min(outer_assumed, assumed if assumed < depth else NESTING_LIMIT + 1)
        state.cut = outer_cut or cut
        if not decided or cut:
            # 例外で抜けた・上限で切った判定: この判定を仮定した仮の判定も残さない
            _settle(state, depth, commit=False)
    if not decided or cut:
        return known
    if assumed >= depth:
        # 自分より外を仮定していない（自分が循環の根）: 判定は確定し、自分を仮定した仮の判定も決まる
        _settle(state, depth, commit=known)
        _PACKAGE_TYPES.record(kind, known, state.reads[mark:], state.class_states, state.objects[seen:])
    elif known is False:
        # 楽観的な仮定の下でも信頼しない: 確定（自分を仮定した仮の判定は仮定が崩れたので捨てる）
        _settle(state, depth, commit=False)
        _PACKAGE_TYPES.record(kind, False, state.reads[mark:], state.class_states, state.objects[seen:])
    else:
        # 外の祖先を仮定した「信頼」: 仮の判定（自分を仮定した仮の判定もその祖先の仮定へ移す）
        _settle(state, depth, commit=False, retag=assumed)
        _provisionally(state, state.provisional_types, kind, assumed)
    return known


def _package_type_uncached(kind: type) -> bool:
    try:
        mro = _TYPE_MRO.__get__(kind)
        if not _within_scan(tuple.__len__(mro)):
            return False
        for klass in mro:
            if not (_TYPE_FLAGS.__get__(klass) & _HEAP_TYPE):
                continue
            # class の body の値（値の storage を読む唯一の場所）は `_trusted_class_body` が文脈に依らずに
            # 確かめる（作業量で数えない。上限の外は信頼しない）
            if not _trusted_class_body(klass):
                return False
        return True
    except TypeError:
        # 上限の外の型を読もうとした（型の属性を読む関数は `TypeError`）: 確かめられない型は信頼しない
        return False


#: `dataclasses` が class の中に作る関数の名前（code の file は `<string>`。定義した class の code）
_DATACLASS_GENERATED = frozenset({
    "__init__", "__repr__", "__eq__", "__hash__", "__setattr__", "__delattr__",
    "__lt__", "__le__", "__gt__", "__ge__", "__getstate__", "__setstate__", "__match_args__",
})

#: 実行環境（Python の標準 library）の code の directory。`enum` / `dataclasses` / `collections` /
#: `contextlib` / `typing` / `abc` が package の型の MRO や class の中に置く関数の code（site-packages
#: の外）。live な値の側からは書き換えられない実行環境の code として信頼する
_STDLIB_DIR = os.path.normpath(__import__("sysconfig").get_paths()["stdlib"]) + os.sep


def _runtime_file(path: Any) -> bool:
    return (
        type(path) is str and os.path.isabs(path)
        and os.path.normpath(path).startswith(_STDLIB_DIR)
        and "-packages" + os.sep not in path
    )


def _function_verdict(function: Any, *, generated: bool) -> Optional[bool]:
    """関数の code だけで決まる判定（`None` は「実行環境の wrapper: 包んだ callable も確かめる」）。"""

    filename = function.__code__.co_filename
    if package_code(function.__code__):
        return True
    if filename == "<string>":
        return generated
    if not _runtime_file(filename):
        return False
    return None


#: C で定義した descriptor・callable の型（包んだ Python の callable を持たない）
_C_CODE_TYPES = (
    types.GetSetDescriptorType, types.MemberDescriptorType, types.WrapperDescriptorType,
    types.MethodDescriptorType, types.ClassMethodDescriptorType, types.BuiltinFunctionType,
    type(__import__("collections").namedtuple("_T", "a").a),
)


def _trusted_callable(value: Any, *, generated: bool, scan: Any = None) -> bool:
    """closure・class の中の値として信頼する callable か（callable でない値は信頼する）。

    実行環境の wrapper（`contextmanager`・`dataclasses` の `__repr__`・`typing` の cache・`lru_cache`）は
    包んだ callable を呼ぶ: それも信頼するものだけ。包んだものは 1 つの作業の列で辿り（再帰しない）、
    辿る数は `SCAN_LIMIT` まで（それを超える入れ子は信頼しない）。
    """

    scan = _Scan() if scan is None else scan
    try:
        return _trusted_callables([value], generated=generated, scan=scan)
    except TypeError:
        # 上限の外の値を読もうとした: 確かめられない callable は信頼しない
        return False


def _trusted_callables(pending: list, *, generated: bool, scan: Any) -> bool:
    while pending:
        if not scan.admit(1):
            return False
        item = pending.pop()
        _note_object(item)  # 判定がこの object の型・中身を読む: 記録が状態を確かめる（`_Nesting.objects`）
        holder = type(item)
        if holder is types.MethodType:
            item = item.__func__
            _note_object(item)  # 包んだ関数の判定も記録が確かめる
            holder = type(item)
        if holder is types.FunctionType:
            verdict = _function_verdict(item, generated=generated)
            if verdict is False:
                return False
            if verdict is None:
                cells = item.__closure__ or ()
                if not _within_scan(scan.used + len(pending) + tuple.__len__(cells)):
                    return False
                # 関数の中を辿る: cell の中身も判定が読んだ状態（関数の code は上で記録した: `_watch`）
                for cell in cells:
                    _note_object(cell)
                    try:
                        pending.append(cell.cell_contents)
                    except ValueError:
                        continue
            continue
        if _one_of(holder, _C_CODE_TYPES):
            continue
        if issubclass(holder, type):
            if (_TYPE_FLAGS.__get__(item) & _HEAP_TYPE) and not package_type(item):
                return False
            continue
        if holder is _LRU_WRAPPER:
            # `functools.lru_cache` の wrapper（C）: 呼ぶのは C の struct が持つ関数（`__wrapped__` は instance の属性で
            # 書き換えられる: 根拠にしない）。その関数を信頼するものだけ
            callee = _lru_callee(item)
            if callee is None:
                return False
            pending.append(callee)
            continue
        if not _inert_value(item):
            return False
    return True


_LRU_WRAPPER = type(__import__("functools").lru_cache(maxsize=None)(len))


def _lru_callee(wrapper: Any) -> Any:
    """`lru_cache` の wrapper が呼ぶ callable（C の struct の `func`: wrapper が直接参照する object（C の struct の固定の
    field と instance の `__dict__`）のうちの唯一の Python の関数か C の callable。`gc.get_referents` は C の traverse を
    読む: hook を呼ばない）。1 つに決まらなければ `None`（型を包んだ wrapper など: 信頼しない）。"""

    found = [
        item for item in gc.get_referents(wrapper)
        if type(item) is types.FunctionType or _one_of(type(item), _C_CODE_TYPES)
    ]
    return found[0] if len(found) == 1 else None


def _note_object(item: Any) -> None:
    """型の信頼の判定の途中なら、型・中身を読んだ object を判定の依存に足す（`_Nesting.objects`）。"""

    state = _NESTING
    if state.active:
        state.objects.append(item)


def _inert_value(value: Any) -> bool:
    """属性として読んでも呼んでも code を実行しないデータか（型が descriptor・callable でない）。

    型を上限の中で読めなければ（`TypeError`）データとは確かめられない: 信頼しない。
    """

    holder = type(value)
    if not _plain_metatype(holder):
        return False
    try:
        return (
            _type_lookup(holder, "__get__", _ABSENT) is _ABSENT
            and _type_lookup(holder, "__set__", _ABSENT) is _ABSENT
            and _type_lookup(holder, "__delete__", _ABSENT) is _ABSENT
            and _type_lookup(holder, "__call__", _ABSENT) is _ABSENT
        )
    except TypeError:
        return False


def _trusted_namespace_value(name: Any, value: Any, *, dataclass_body: bool, scan: Any = None) -> bool:
    """class の `__dict__` の値として許した種類か（それ以外は信頼しない）。"""

    holder = type(value)
    generated = dataclass_body and type(name) is str and name in _DATACLASS_GENERATED
    if holder is types.FunctionType:
        return _trusted_callable(value, generated=generated, scan=scan)
    if holder is staticmethod or holder is classmethod:
        inner = value.__func__
        if type(inner) is types.FunctionType:
            # `namedtuple` の `__new__` も `<string>` の生成された関数
            return _trusted_callable(inner, generated=generated or name == "__new__", scan=scan)
        return _trusted_callable(inner, generated=False, scan=scan)
    if holder is property or holder is readable_property or holder is types.DynamicClassAttribute:
        # 読むと accessor を呼ぶ: accessor も信頼する関数だけ
        return all(
            accessor is None or (
                type(accessor) is types.FunctionType
                and _trusted_callable(accessor, generated=False, scan=scan)
            )
            for accessor in (value.fget, value.fset, value.fdel)
        )
    return _trusted_callable(value, generated=False, scan=scan)


def _trusted_class_body(klass: type) -> bool:
    """class の body（`__dict__`）の値が全部許した種類か（class ごとに 1 度だけ。辿る数の和は上限まで）。"""

    # cache の key にするのは metaclass が `__eq__` / `__hash__` を持たない class だけ（その code を呼ばない）
    cacheable = _plain_metatype(klass)
    state = _NESTING
    if cacheable:
        known = _TRUSTED_BODIES.get(klass)
        if known is not None:
            return known
        assumed = state.provisional_bodies.get(klass)
        if assumed is not None:
            state.assumed = min(state.assumed, assumed)
            return True
    outer_assumed, outer_cut = state.assumed, state.cut
    state.assumed, state.cut = NESTING_LIMIT + 1, False
    mark = len(state.reads)
    seen = len(state.objects)
    try:
        known = _trusted_class_body_uncached(klass)
    finally:
        assumed, cut = state.assumed, state.cut
        state.assumed, state.cut = min(outer_assumed, assumed), outer_cut or cut
    # 型の判定と同じ規則で残す（class の body は型の判定の内側）: 上限で切った判定は残さない、仮定の
    # 無い判定と楽観的な仮定の下の「信頼しない」は確定、途中の祖先を仮定した「信頼」は仮の判定
    if not cacheable or cut:
        return known
    if assumed > NESTING_LIMIT or known is False:
        _TRUSTED_BODIES.record(klass, known, state.reads[mark:], state.class_states, state.objects[seen:])
    else:
        _provisionally(state, state.provisional_bodies, klass, assumed)
    return known


#: class ごとの `_trusted_class_body` の結果（hash・比較が組み込みの実装の metaclass の class だけ）
_TRUSTED_BODIES = _TypeFactTable()


def _trusted_class_body_uncached(klass: type) -> bool:
    # 型の信頼の判定は文脈に依らない（class ごとに cache する）: class の中の値の storage の読みは作業量で
    # 数えず限界も記録せず、上限の外は「確かめられない」= 信頼しない（量の信号を型の判定の答えにする場所）
    with signalled_storage_reads():
        try:
            return _trusted_class_body_values(klass)
        except StorageBeyondReadBound:
            return False


def _trusted_class_body_values(klass: type) -> bool:
    _note_read(klass)
    raw = _unwrapped(_TYPE_DICT.__get__(klass))
    if not _exact_str_keys(raw):
        return False
    scan = _Scan()
    if not scan.admit(dict.__len__(raw)):
        return False
    dataclass_body = "__dataclass_fields__" in raw and "__dataclass_params__" in raw
    for name, value in dict.items(raw):
        if not _trusted_namespace_value(name, value, dataclass_body=dataclass_body, scan=scan):
            return False
    return True


#: 組み込みの mapping の型（より特殊な型を先に: `OrderedDict` の subclass は `OrderedDict` の
#: method と比べる）
_BUILTIN_DICTS = (OrderedDict, dict)
_TYPE_QUALNAME = type.__dict__["__qualname__"]
_TYPE_MODULE = type.__dict__["__module__"]
_TYPE_MRO = type.__dict__["__mro__"]
#: 組み込みの容器の iterator（中身を辿るのは C の実装。generator のような code を持たない）。
#: 型そのものの容器の iterator だけ: `reversed(seq)` の汎用の型（`reversed`）は包んだ値の
#: `__len__` / `__getitem__` を呼ぶので含めない（`reversed([])` は list 専用の iterator）。
#: 文字列の iterator は版で型が分かれる（3.12 の ASCII 専用の型）ので ASCII と非 ASCII の両方
_BUILTIN_ITERATOR_TYPES = frozenset(
    type(iter(sample)) for sample in (
        (), [], {}, set(), frozenset(), "", "\u00e9", b"", range(0), {}.keys(), {}.values(), {}.items(),
        reversed([]),
    )
) - {reversed}
_BUILTIN_VIEW_TYPES = frozenset(type(view) for view in ({}.keys(), {}.values(), {}.items()))
_TUPLE_ITERATOR = type(iter(()))


# ---------------------------------------------------------------------------
# 型
# ---------------------------------------------------------------------------


_TYPE_DICT = type.__dict__["__dict__"]
_MISSING = object()
_ABSENT = object()
#: `_exact_str_keys` の identity の比較（C の実装だけで key の型を確かめる）
_IS = operator.is_
_REPEAT_STR = itertools.repeat(str)
#: 型の flag（`Py_TPFLAGS_HEAPTYPE`: class 文で作った型。無ければ C で定義した組み込みの型）
_TYPE_FLAGS = type.__dict__["__flags__"]
_HEAP_TYPE = 1 << 9


def type_attribute(kind: type, name: str) -> Any:
    """型 `kind` の属性（MRO の各 class の `__dict__` から。metaclass の hook を呼ばない）。無ければ `None`。

    `inspect.getattr_static(kind, name)` の instance 向けの部分と同じ値（metaclass の属性は含めない）を、
    組み込みの slot（`__mro__` / `__dict__`）だけで読む（`getattr_static` と違い metaclass の hook を呼ばない）。
    """

    return _type_lookup(kind, name, None)


def _type_lookup(kind: type, name: str, missing: Any) -> Any:
    """`type_attribute` と同じ（無ければ `missing`。値が `None` の属性と区別する）。

    名前空間は **使うたびに** 読む（型の事実を cache しない: 外の code は class を書き換えられる）。読みは
    `_namespace_value`（key の hook を呼ばない）。組み込みの `str` でない key を持つ class に当たれば `TypeError`
    （Python の引きは hash の等しい key の `__eq__` を key の文字列に依らず呼ぶ: どの値か決めない）。
    """

    mro = _TYPE_MRO.__get__(kind)
    plain = _PLAIN_MROS.get(id(kind))
    if plain is not None and plain[0] is kind and plain[1] is mro:
        # MRO の名前空間が全部確かめた storage（`_PLAIN_MROS`）: storage を組み込みの `str` の名前で直接引く
        nesting = _NESTING
        if nesting.active:
            nesting.reads.extend(plain[3])  # 名前空間を読んだ heap class は判定の依存（`_note_read`）
        witness = _LOOKUPS.active
        if witness is None:
            for raw in plain[2]:
                found = dict.get(raw, name, _MISSING_DUNDER)
                if found is not _MISSING_DUNDER:
                    return found
            return missing
        witness.append((_MRO_READ, kind, mro))  # 引いた storage の列は `kind` の MRO が決める（`_LookupFactTable`）
        for raw, heap in zip(plain[2], plain[4]):
            found = dict.get(raw, name, _MISSING_DUNDER)
            if heap:
                witness.append((raw, name, found))  # 判定が読んだ名前と見つけた object（`_LookupFactTable`）
            if found is not _MISSING_DUNDER:
                return found
        return missing
    _require_scan(tuple.__len__(mro), "a type's MRO")
    _remember_plain_mro(mro, kind)
    witness = _LOOKUPS.active
    if witness is not None:
        witness.append((_MRO_READ, kind, mro))  # 引いた storage の列は `kind` の MRO が決める（`_LookupFactTable`）
    noting = _NESTING.active
    for klass in mro:
        known = _STR_KEYED_NAMESPACES.get(id(klass))
        if known is not None and known[0] is klass and not noting:
            # 確かめた名前空間（key は組み込みの `str` のまま）: storage を組み込みの `str` の名前で直接引く
            raw = known[1]
            found = dict.get(raw, name, _MISSING_DUNDER)
            if witness is not None:
                witness.append((raw, name, found))  # 判定が読んだ名前と見つけた object（`_LookupFactTable`）
            if found is not _MISSING_DUNDER:
                return found
            continue
        static = _STATIC_NAMESPACES.get(id(klass))
        if static is not None and static[0] is klass:
            # 組み込みの型の名前空間（変わらない: 読みの記録も要らない）
            found = dict.get(static[1], name, _MISSING_DUNDER)
            if found is not _MISSING_DUNDER:
                return found
            continue
        # 組み込みの `str` でない key を持つ名前空間に当たれば、その class で止める（key を辿らない: 量は class の数だけ）
        reader = _NamespaceReader(klass)
        found = reader.value(name)
        if found is _AMBIGUOUS_NAME:
            if witness is not None:
                # 決めない名前空間に当たった計算は記録しない（組み込みでない key は `delattr` で後から消せる: 記録した答えが
                # 古くなる。この名前空間を `dict.get` で確かめると key の hook を呼ぶ）
                witness.append(_UNRECORDABLE)
            raise TypeError(f"a class namespace holds a key that is not a builtin str (looking up {name!r})")
        if witness is not None and not reader.static:
            witness.append((reader.raw, name, found))  # 判定が読んだ名前と見つけた object（`_LookupFactTable`）
        if found is not _MISSING_DUNDER:
            return found
    return missing


def _remember_plain_mro(mro: Tuple[type, ...], kind: type) -> None:
    """MRO のどの class の名前空間も key が全部組み込みの `str` なら、その storage の列を記録する（`_PLAIN_MROS`）。"""

    raws = []
    heaps = []
    for klass in mro:
        reader = _NamespaceReader(klass)
        if not reader.plain:
            return  # 組み込みの `str` でない key（引きを決めない名前空間）: 記録しない（毎回 class ごとに引く）
        heap = not reader.static
        if heap:
            raws.append(reader.raw)
        else:
            static = _STATIC_NAMESPACES.get(id(klass))
            if static is None or static[0] is not klass:
                return  # 表が上限: 記録しない
            raws.append(static[1])
        heaps.append(heap)
    if len(_PLAIN_MROS) >= _TYPE_FACTS_LIMIT:
        _PLAIN_MROS.clear()
    heap_classes = tuple(klass for klass, heap in zip(mro, heaps) if heap)
    _PLAIN_MROS[id(kind)] = (kind, mro, tuple(raws), heap_classes, tuple(heaps))


#: 型ごとの MRO の名前空間の storage の列（`id(型)` → (型, MRO, storage の列, heap class の列, heap type か の列)）。
#: MRO の tuple が同じ object の間（`__bases__` の書き換えは MRO を作り直す）だけ使う。class の名前空間の storage は class
#: が生きている間同じ dict で、確かめた storage の key は組み込みの `str` のまま（`_STR_KEYED_NAMESPACES` の前提）・組み込み
#: の型の名前空間は変わらない（`_STATIC_NAMESPACES`）: 名前の引きは記録した storage を直接引くのと同じ。記録は型・MRO・
#: storage を生かす（`id` を再利用させない）
_PLAIN_MROS: Dict[int, Tuple[type, Tuple[type, ...], Tuple[dict, ...], Tuple[type, ...], Tuple[bool, ...]]] = {}


class _Lookups(threading.local):
    """thread ごとの、計算中の型の事実が名前で引いた (名前空間の storage, 名前, 見つけた object) の列（`_witnessed`）。"""

    def __init__(self) -> None:
        self.active: Optional[List[Tuple[dict, str, Any]]] = None


_LOOKUPS = _Lookups()
#: 読みの記録の印: 計算が決めない名前空間に当たった（`_witnessed` は記録しない）
_UNRECORDABLE = ("unrecordable",)
#: 読みの記録の印: `(_MRO_READ, 型, MRO)` は、名前を引いた型の MRO（引く storage の列を決める）。key の型でない型の
#: `__bases__` の書き換えも、記録を古くする
_MRO_READ = object()


def _witnessed(compute: Any, *args: Any) -> Tuple[Any, Optional[Tuple[Tuple[dict, str, Any], ...]]]:
    """`compute(*args)` と、それが型の名前空間を名前で引いた記録（入れ子の計算の記録は外の計算にも足す）。記録が上限を
    超えたら `None`（記録しない: 毎回計算する）。"""

    outer = _LOOKUPS.active
    _LOOKUPS.active = []
    try:
        value = compute(*args)
        active = _LOOKUPS.active
        witness = (
            tuple(active) if _within_scan(len(active)) and not any(item is _UNRECORDABLE for item in active) else None
        )
    finally:
        inner = _LOOKUPS.active
        _LOOKUPS.active = outer
        if outer is not None:
            outer.extend(inner)
    return value, witness


class _LookupFactTable:
    """名前の引き（`_type_lookup`）だけで決まる型の事実の表。記録は key の型の MRO と、計算が引いた (storage, 名前,
    見つけた object) の列（読みの集合）を持ち、引くたびにその読みだけを確かめる（MRO が同じ object で、どの名前も同じ
    object を引く）: 名前空間を全部読み直さない。

    確かめは hook を呼ばない: 記録する storage は key が全部組み込みの `str` の heap type の名前空間（`_NamespaceReader`
    が確かめた: 組み込みでない key があれば計算は `TypeError` で記録しない）で、class の名前空間の書き換えは名前を
    組み込みの `str` にして置く（`_STR_KEYED_NAMESPACES` の前提）: 組み込みの `str` の名前で引く `dict.get` は key の
    `__eq__` を呼ばない。組み込みの型の名前空間は変わらない（記録しない）。記録は key・MRO・storage・見つけた object を
    生かす（`id` を再利用させない）。key は型だけ（記録は `id(key)` で引き、identity で確かめる）。

    記録を使った計算の外側（読みを記録している外の計算・型の事実の判定）へは、記録の読みを渡す（`lookup_fact`）: 外の
    記録が内の記録の読みを確かめないまま古くならない。
    """

    __slots__ = ("entries",)

    def __init__(self) -> None:
        self.entries: Dict[int, Tuple[type, Any, Tuple[Any, ...], Any]] = {}

    def record(self, key: Any, value: Any, witness: Optional[Tuple[Tuple[dict, str, Any], ...]]) -> None:
        if witness is None:
            return  # 読みの記録が上限の外: 記録しない
        if not issubclass(type(key), type):  # 値の `__class__` を読まない
            raise TypeError("a lookup fact is keyed by a type")
        if len(self.entries) >= _TYPE_FACTS_LIMIT:
            self.entries.clear()
        reads = [item for item in witness if item[0] is not _MRO_READ]
        mro_reads = {id(item[1]): item for item in witness if item[0] is _MRO_READ}.values()
        raws = tuple(item[0] for item in reads)
        names = tuple(item[1] for item in reads)
        founds = tuple(item[2] for item in reads)
        owners = tuple(item[1] for item in mro_reads)
        mros = tuple(item[2] for item in mro_reads)
        if not all(map(_IS, map(_TYPE_MRO.__get__, owners), mros)):
            return  # 計算の途中で MRO が変わった（外の code は走らないはず）: 記録しない
        checks = (raws, names, founds, _watch(found for found in founds if found is not _MISSING_DUNDER), owners, mros)
        self.entries[id(key)] = (key, _TYPE_MRO.__get__(key), checks, value)

    def clear(self) -> None:
        self.entries.clear()

    def __len__(self) -> int:
        return len(self.entries)


#: 公開の名前（package の他の層が名前の引きだけで決まる型の事実を記録する表: `lookup_fact` と使う）
LookupFactTable = _LookupFactTable


def lookup_fact(table: "LookupFactTable", key: Any, compute: Any, *args: Any) -> Any:
    """名前の引き（`type_attribute` / `_type_lookup`）だけで決まる型の事実を、表に記録して引く（引くたびに引いた名前と
    MRO を確かめる: `_LookupFactTable`）。`compute(*args)` は型の名前空間を名前で引くだけで決める関数。型の事実の cache を
    足すときの唯一の入口（記録の確かめを各所で書かない）。"""

    entry = table.entries.get(id(key))
    if entry is not None and entry[0] is key and _TYPE_MRO.__get__(key) is entry[1]:  # MRO: `__bases__` の書き換え
        raws, names, founds, watch, owners, mros = entry[2]
        if (
            all(map(_IS, map(_TYPE_MRO.__get__, owners), mros))
            and all(map(_IS, map(dict.get, raws, names, _REPEAT_MISSING), founds))
            and (watch is _NO_WATCH or _watch_holds(watch))
        ):
            # 計算の途中で記録を使った: 記録の読みは外の計算の読みでもある（外の記録も同じ読みを確かめる）
            outer = _LOOKUPS.active
            if outer is not None:
                outer.extend(zip(raws, names, founds))
                outer.extend(zip(_REPEAT_MRO_READ, owners, mros))
            nesting = _NESTING
            if nesting.active:
                nesting.reads.extend(entry[1])
                nesting.reads.extend(owners)
            return entry[3]
    known, witness = _witnessed(compute, *args)
    table.record(key, known, witness)
    return known


#: `lookup_fact` の「記録が無い」印（記録する値は `None` もある）
_MISSING_FACT = object()


def _exact_str_keys(raw: dict) -> bool:
    """**型の** namespace の key が全部組み込みの `str` か（固定の上限の外は False: 型の信頼の判定の側）。"""

    if not _within_scan(dict.__len__(raw)):
        return False
    return _exact_str_raw(raw)


def _exact_str_raw(raw: dict) -> bool:
    """dict の storage の key が全部組み込みの `str` か（`dict.__iter__` は storage を読む。key の
    `__hash__` / `__eq__` を呼ばない。型は identity で比べる）。数は呼ぶ側が先に比べる（型の上限か値の読み）。"""

    return all(map(_IS, map(type, dict.__iter__(raw)), _REPEAT_STR))


_TYPE_NAME = type.__dict__["__name__"]


def type_name(kind: type) -> str:
    """型の `__qualname__`（metaclass の property を通らない組み込みの slot で読む）。"""

    return exact_scalar(_TYPE_QUALNAME.__get__(kind))


def type_module(kind: type) -> str:
    """型の `__module__`（metaclass の hook を通らない slot で読み、組み込みの `str` そのもので返す）。"""

    return exact_scalar(_TYPE_MODULE.__get__(kind))


def is_kind(value: Any, base: Any) -> bool:
    """`value` の型が `base`（型か型の tuple）の subclass か（`isinstance` の代わり）。

    読み方: 値の `__class__` を読まない（`type(value)` の MRO）。`base` の metatype が `type` そのもの（組み込みの型・
    素の class）なら C の MRO の比較だけで、値の型の metaclass の hook を呼ばない。それ以外（ABC の `Mapping`・
    `Enum` など、metatype の `__subclasscheck__` が値の型の属性を読む）は、値の葉を写してから判定する（scalar の
    subclass の metaclass の hook を呼ばない。scalar でない値の型の hook は外の code）。返す値は `bool`。
    """

    if type(base) is type:  # 最も多い形（組み込みの型・素の class）
        return issubclass(type(value), base)
    if type(base) is tuple:
        for item in base:
            if is_kind(value, item):
                return True
        return False
    return issubclass(type(exact_scalar(value)), base)


def is_enum(value: Any) -> bool:
    return issubclass(type(value), Enum)


# ---------------------------------------------------------------------------
# scalar
# ---------------------------------------------------------------------------


def plain_scalar(value: Any) -> Any:
    """scalar なら基底型の値（subclass は基底型の slot で写す）、それ以外は `NOT_PLAIN`。"""

    if value is None or value is True or value is False:
        return value
    kind = type(value)
    if kind is str or kind is int or kind is float:
        return value
    if issubclass(kind, Enum):
        return NOT_PLAIN
    if issubclass(kind, bool):
        return bool.__bool__(value)
    if issubclass(kind, int):
        return int.__index__(value)
    if issubclass(kind, float):
        plain = float.__float__(value)
        return plain if plain == plain else _canonical_nan(value, plain)
    if issubclass(kind, str):
        return str.__str__(value)
    return NOT_PLAIN


#: scalar の subclass の NaN の葉 → その写し（`id(元の葉)` → (元の葉の weakref, 写し)）。NaN は identity で比べ・hash
#: する唯一の組み込みの値: 同じ元の葉はいつ読んでも同じ写しにする（写しの identity が元の葉の identity に従う: 比べる・
#: hash する・key にする読みが、呼び出しの間で双子と同じに振る舞う）。表は元の葉を持たない（weakref だけ）: entry は
#: 元の葉が消えると消える（weakref の callback。循環の中の葉も GC が集めれば消える）。写しの寿命は「元の葉が生きている
#: 間」で、その間だけ同じ写しを保てばよい。weakref を作れない型の葉はこの規則を持てない（寿命を知るには葉を持つしか
#: ない: 持てば手放した後も残る）: 判定不能（`_canonical_nan`）。lock は再入できる（callback は GC が lock の中の割り当て
#: で走らせることがある）
_NAN_COPIES: Dict[int, Tuple[Any, float]] = {}
_NAN_COPIES_LOCK = threading.RLock()


def _canonical_nan(source: Any, fresh: float) -> float:
    """`source`（NaN の scalar の subclass）の写し。同じ `source` には、それが生きている間同じ写しを返す（hook を呼ばない）。

    weakref を作れない型の `source` は判定不能（D20: 写しの identity を元の葉の寿命に結べない。元の葉を持ち続けずに同じ
    写しを返す方法が無い）。production の JPype の浮動小数の型（`JDouble` / `JFloat`）は weakref を作れる。
    """

    key = id(source)
    with _NAN_COPIES_LOCK:
        entry = _NAN_COPIES.get(key)
        if entry is not None and entry[0]() is source:
            return entry[1]
        try:
            held = weakref.ref(source, lambda gone, key=key: _forget_nan(key, gone))
        except TypeError:
            raise undecidable(
                f"a NaN leaf of {type_name(type(source))} has no weak reference: its copy cannot follow its lifetime"
            ) from None
        _NAN_COPIES[key] = (held, fresh)
        return fresh


def _forget_nan(key: int, gone: Any) -> None:
    with _NAN_COPIES_LOCK:
        entry = _NAN_COPIES.get(key)
        if entry is not None and entry[0] is gone:
            del _NAN_COPIES[key]


def json_scalar(value: Any) -> Any:
    """JSON の scalar としての基底型の値（`None` / bool / str・int・float とその subclass）。それ以外は `NOT_PLAIN`。

    JSON の規則（`json.dumps` と同じ）: mixin の enum（`IntEnum` / `str` の enum）も基底型の値で
    書く。`plain_scalar`（`str()` / `int()` の規則）は enum を除く。どちらも基底型の slot で読む。
    """

    if value is None or value is True or value is False:
        return value
    kind = type(value)
    if kind is str or kind is int or kind is float:
        return value
    if issubclass(kind, str):
        return str.__str__(value)
    if issubclass(kind, int):
        return int.__index__(value)
    if issubclass(kind, float):
        return float.__float__(value)
    return NOT_PLAIN


def str_value(value: Any) -> Any:
    """文字列（subclass を含む。enum を除く）なら基底型の `str`、それ以外は `NOT_PLAIN`。"""

    kind = type(value)
    if kind is str:
        return value
    if issubclass(kind, str) and not issubclass(kind, Enum):
        return str.__str__(value)
    return NOT_PLAIN


def int_value(value: Any) -> Any:
    """整数（bool を除く。subclass を含む。enum を除く）なら基底型の `int`、それ以外は `NOT_PLAIN`。"""

    kind = type(value)
    if kind is int:
        return value
    if issubclass(kind, int) and not issubclass(kind, (bool, Enum)):
        return int.__index__(value)
    return NOT_PLAIN


def float_value(value: Any) -> Any:
    kind = type(value)
    if kind is float:
        return value
    if issubclass(kind, float) and not issubclass(kind, Enum):
        return float.__float__(value)
    return NOT_PLAIN


#: scalar の subclass を見分ける基底の型（`exact_scalar` と、1 つの frame で読む reader が同じ判定を使う）
_SCALAR_BASES = (int, float, str)


def exact_scalar(value: Any) -> Any:
    """scalar の subclass（JPype の `JInt` / `JLong` / `JDouble` など、組み込みの scalar の型を継承する外の
    runtime の型）を、基底型の値へ写す（写し方は `plain_scalar` が唯一の owner）。

    基底型の slot で読む（subclass の `__int__` / `__str__` を呼ばない）。値と意味（整数値・文字列）は変えず、
    JSON・digest・式の文字列が読む基底型の値と同じ。bool・enum の member・scalar でない値はそのまま返す
    （Issue #235: 意味の値の scalar を組み込みの型そのものにする入口が使う）。
    """

    kind = type(value)
    if value is None or kind is int or kind is str or kind is bool or kind is float:
        return value  # exact な scalar
    if not issubclass(kind, _SCALAR_BASES):
        return value  # scalar でない値（MRO は C の slot で見る: hook を呼ばない）
    plain = plain_scalar(value)
    return value if plain is NOT_PLAIN else plain


def scalar_int(value: Any) -> int:
    """`int(value)` と同じ値。scalar の subclass は基底型の値にしてから整数にする（`exact_scalar`）。

    subclass の `__int__` / `__index__` を呼ばない（JPype の `JInt` などが値を変える code を持っていても、
    整数は基底型の slot の値）。exact な値・enum の member・scalar でない値は `int()` のまま（`as_int` と
    違い、`int()` が受ける値をすべて受け、例外も `int()` と同じ）。runtime ref の構築（Issue #242）が
    容器の中や注釈が `Any` の値を整数として読む入口。
    """

    if type(value) is int:
        return value
    return int(exact_scalar(value))


def scalar_int_or(value: Any, default: int = 0) -> int:
    """`int(value or default)` と同じ値。真偽も整数も基底型の値で読む（subclass の `__bool__` / `__int__` を呼ばない）。"""

    base = exact_scalar(value)
    return scalar_int(base if base else default)


def scalar_bool(value: Any) -> bool:
    """`bool(value)` と同じ値。scalar の subclass は基底型の値にしてから真偽にする（`exact_scalar`）。

    subclass の `__bool__` / `__len__` を呼ばない。JPype の `JBoolean`（int の subclass）は基底型の整数の真偽。
    それ以外は `bool()` のまま（Issue #242、`scalar_int` と同じ）。
    """

    if value is True or value is False or value is None:
        return bool(value)
    return bool(exact_scalar(value))


def scalar_text(value: Any) -> str:
    """`str(value)` と同じ値。scalar の subclass は基底型の値にしてから文字列にする（容器の中の葉も）。

    読み方: `exact_tree` と同じに辿り、葉に scalar の subclass が無ければ元の値の `str()`（双子と同じ文字列。容器の
    型の `repr` を保つ）、在れば写した組み込みの木の `str()`（subclass の `__str__` / `__repr__` を呼ばない。元の
    容器の型では作り直さないので、`deque` などの `repr` は基底の容器のもの: 意図した差 D5）。
    返す値の保証: 組み込みの `str` そのもの（外の object の `__str__` が返した `str` の subclass も写す）。
    """

    if type(value) is str:
        return value
    tree, leaves = _exact_tree_read(value)
    # 葉に scalar の subclass が無ければ元の値の `str()`（双子と同じ文字列: 容器の型の `repr` を保つ）。在れば写した木の
    # `str()`（組み込みの容器の `repr`）。外の object の `__str__` は str の subclass を返し得る: 返した値も基底型の slot で読む
    return exact_scalar(str(tree if leaves else value))


def exception_text(error: Any) -> str:
    """`str(error)` と同じ文字列（例外の文字列化が読む状態を基底型の値で。Issue #242）。

    読み方: 例外の状態を descriptor の slot で読む: `args`、MRO の名前空間の C の field（`OSError` の `filename` /
    `filename2`・`UnicodeError` の `object`・`__slots__` の field など）、連鎖の field（`__cause__` / `__context__` /
    `__suppress_context__`）、`__traceback__`、instance の `__dict__`、その中の例外の状態。どれにも scalar の subclass が
    無ければ `str(error)`（双子と同じ）。在れば、**同じ型**の例外を組み込みの `__new__` で作り（`__init__` は呼ばない）、
    状態を基底型の値で置いて（中の例外も同じ規則で写す）、その `str()` にする: 文字列化の dispatch（組み込みの
    `__str__`・別名の slot・自前の `__str__`）は双子と同じ。

    状態は field ごとに「無い」「明示的な `None`」「値」を区別して写す（文字列化が観測するのはこの 3 つ）:
    - `__slots__` の field: 読んで `AttributeError` なら無い。`None` は明示的な `None`（置く）。
    - getset の field（`args` / `__traceback__` / `__cause__` / `__context__`）: setter が `None` を「無い」に写すので、読んだ
      値を置く（`None` は置かない）。
    - 組み込みの例外の C の field（`OSError.filename` など）: 「無い」（C の NULL）も `None` と読める。組み込みの
      `__str__` は区別する（`'[Errno 2] m'` と `'[Errno 2] m: None'`）ので、型の traverse が辿る参照
      （`gc.get_referents`: NULL でない field だけ）の `None` の数から決める。決まらなければ判定しない。
    写した後に、写しの状態（無い / `None` / 値の別と参照の `None` の数）が元と同じことを確かめる。

    状態の値は全部を 1 回の読みで写す（field 間・容器の中の共有は写しでも共有。写した後に identity の関係も確かめる）。
    例外の閉路（`__context__` の環・自分を持つ slot）は 2 段で写す（先に全部の例外を作り、次に field を置く）。

    返す値の保証: 組み込みの `str` そのもの。忠実に写せない例外（`__new__` を自分で持つ型・状態の中の容器の閉路・型の
    検査に通らない状態・NULL と `None` を決められない C の field・写しの状態が元と違う）は判定しない: CPython が文字列化できない
    例外に使う `<unprintable ... object>`（推測した文を返さない。写しの途中の例外で元の例外を置き換えない）。写しの
    `__str__` が投げる例外は双子の `__str__` と同じ（そのまま）。型の class の属性（自前の `__str__` が読む class の
    値）は型の code と data（外の code）で、写さない。範囲の外: 例外 object 自身の identity を観測する `__str__`
    （例: `self in registry`。写しは別の object）。
    """

    kind = type(error)
    if not issubclass(kind, BaseException):
        return scalar_text(error)
    unprintable = f"<unprintable {type_name(kind)} object>"
    try:
        graph = _exception_graph(error)
        holds = holds_scalar_subclass(tuple(_graph_values(graph)))
    except (TypeError, RecursionError, UndecidableComparison):
        return unprintable  # 状態を読めない（閉路・写せない値・辿れない view）
    if not holds:
        return scalar_text(error)
    try:
        # `str()` は型の `__str__` を名前で引く（名前空間に組み込みの `str` でない key があれば、hash の等しい key の
        # `__eq__` を Python 自身が呼ぶ）: そういう型は文字列にしない（`_type_lookup` が `TypeError`）
        _type_lookup(kind, "__str__", None)
        candidates = _none_assignments(error, graph[-1][1])
        if len(candidates) > 1 and not _builtin_str(kind):
            return unprintable  # 型の Python の `__str__` が何を観測するか決められない: 判定しない
        clones = [_copy_graph(graph, chosen) for chosen in candidates]
    except (TypeError, ValueError, AttributeError, RecursionError, UndecidableComparison):
        return unprintable
    if not clones:
        return unprintable
    if len(clones) == 1:
        return exact_scalar(str(clones[0]))  # 写しの `__str__` が投げる例外は双子と同じ（そのまま）
    # 観測と矛盾しない割り当てが複数: 組み込みの `__str__`（C の code）での文字列が全部同じときだけ決まる。どれかの
    # 割り当てで投げるなら（例: `UnicodeError` の `object` の NULL と `None`）、結果は割り当てによる: 判定しない
    texts = set()
    for clone in clones:
        try:
            texts.add(exact_scalar(str(clone)))
        except (TypeError, ValueError, AttributeError, RecursionError, OverflowError):
            return unprintable
    return texts.pop() if len(texts) == 1 else unprintable


#: 1 つの例外の状態: (例外, field の (descriptor, 値 | `_UNSET`) の列, instance の `__dict__` の (名前, 値) の列)
_ExceptionState = Tuple[Any, List[Tuple[Any, Any]], List[Tuple[Any, Any]]]


def _exception_graph(error: Any) -> List[_ExceptionState]:
    """例外とその状態から辿れる例外の状態の列（中の例外が先: 後順。閉路の戻る辺は辿らない: 写しは 2 段で作る）。"""

    order: List[_ExceptionState] = []
    state: Dict[int, int] = {}  # id(例外) → 0: 辿っている途中 / 1: 済み
    alive: List[Any] = [error]
    stack: List[Tuple[Any, bool]] = [(error, False)]
    while stack:
        node, leaving = stack.pop()
        if leaving:
            state[id(node)] = 1
            order.append((node, _exception_fields(node, type(node)), _exception_instance_dict(node)))
            continue
        mark = state.get(id(node))
        if mark is not None:
            continue  # 済み、または辿っている途中（閉路: 写しは全部作ってから field を置く）
        state[id(node)] = 0
        alive.append(node)
        if not _within_scan(len(alive)):
            raise TypeError("an exception state beyond the scan limit is not copied")
        stack.append((node, True))
        values = [value for _descriptor, value in _exception_fields(node, type(node)) if value is not _UNSET]
        for name, value in _exception_instance_dict(node):
            values.append(name)
            values.append(value)
        for value in values:
            for nested in _nested_exceptions(exact_tree(value)):
                if state.get(id(nested)) is None:
                    stack.append((nested, False))
    return order


def _graph_values(graph: List[_ExceptionState]) -> List[Any]:
    """例外の状態の値を全部、決まった順に（field の値、`__dict__` の名前と値）。"""

    values: List[Any] = []
    _require_scan(len(graph), "an exception state")
    for _error, fields, items in graph:
        values.extend(value for _descriptor, value in fields if value is not _UNSET)
        for name, value in items:
            values.append(name)
            values.append(value)
    return values


def _copy_graph(graph: List[_ExceptionState], explicit: Tuple[Any, ...]) -> Any:
    """例外の状態の木を写す（最後が元の例外）。状態の値は全部を **1 回の読み** で写す（共有された葉・容器は写しでも共有:
    field 間の identity を保つ）。中の例外は同じ規則で写した例外に置き換える（共有された容器は 1 度だけ）。写しは 2 段:
    先に全部の例外を（`__new__` だけが置ける field とともに）作り、次に field を置く（閉路の状態も写せる）。元の例外の
    `None` と読める C の field の割り当ては `explicit`、中の例外は観測と矛盾しない割り当てが 1 つのときだけ写す。
    写せなければ `TypeError`。"""

    _require_scan(len(graph), "an exception state")
    raw = _graph_values(graph)
    read = exact_tree(tuple(raw))
    copies: Dict[int, Any] = {}  # id(元の例外) → 写し
    replaced: Dict[int, Any] = {}  # id(読んだ容器) → 中の例外を置き換えた容器（共有を保つ）
    alive: List[Any] = [read]
    plans: List[Tuple[Any, List[Tuple[Any, Any]], List[Tuple[Any, Any]], Tuple[Any, ...], int]] = []
    position = 0
    for index, (error, fields, items) in enumerate(graph):
        kind = type(error)
        owner = _defining_class(kind, "__new__")
        if type(owner) is not type or _TYPE_MODULE.__get__(owner) != "builtins" or not issubclass(owner, BaseException):
            raise TypeError("an exception type with its own __new__ is not copied")
        chosen = explicit if index == len(graph) - 1 else None
        if chosen is None:
            candidates = _none_assignments(error, fields)
            if len(candidates) != 1:
                raise TypeError("whether a builtin exception field holds None or nothing is not decided")
            chosen = candidates[0]
        plans.append((error, fields, items, chosen, position))
        position += sum(1 for _descriptor, value in fields if value is not _UNSET) + 2 * len(items)
    # 1 段目: 写しを作る。`__new__` だけが置ける field（`BaseExceptionGroup` の `message` / `exceptions`）は作るときに
    # 要るので、その field が持つ例外の写しを先に作る（読みだけの field の依存の順）。普通の状態（`__context__` など）
    # の閉路は 2 段目で置くので順に効かない。読みだけの field の依存の閉路は作れない（`TypeError`）
    by_id = {id(plan[0]): plan for plan in plans}
    state: Dict[int, int] = {}  # id(例外) → 0: 作っている途中 / 1: 済み
    for plan in plans:
        stack: List[Tuple[Any, bool]] = [(plan, False)]
        while stack:
            current, leaving = stack.pop()
            error = current[0]
            if leaving:
                copies[id(error)] = _new_exception(type(error), _readonly_values(current, read, copies, replaced, alive))
                state[id(error)] = 1
                continue
            mark = state.get(id(error))
            if mark == 1:
                continue
            if mark == 0:
                raise TypeError("exceptions that hold each other in read-only fields are not copied")
            state[id(error)] = 0
            stack.append((current, True))
            for nested in _readonly_exceptions(current, read):
                if id(nested) in by_id and state.get(id(nested)) != 1:
                    stack.append((by_id[id(nested)], False))
    clone = None
    for error, fields, items, chosen, start in plans:
        kind = type(error)
        clone = copies[id(error)]
        copied: List[Tuple[Any, Any]] = []
        cursor = start
        for descriptor, value in fields:
            if value is _UNSET:
                copied.append((descriptor, _UNSET))
                continue
            copied.append((descriptor, _replace_exceptions(read[cursor], copies, replaced, alive)))
            cursor += 1
        state_items: List[Tuple[Any, Any]] = []
        for _name, _value in items:
            state_items.append((read[cursor], _replace_exceptions(read[cursor + 1], copies, replaced, alive)))
            cursor += 2
        # getset の setter は他の field も書く（`__cause__` の setter は `__suppress_context__` を真にする）: getset を先に、
        # C の field・slot を後に置き、最後に field ごとに元と同じか確かめる
        ordered = [item for item in copied if type(item[0]) is _FIELD_DESCRIPTORS[1]]
        ordered += [item for item in copied if type(item[0]) is not _FIELD_DESCRIPTORS[1]]
        for descriptor, value in ordered:
            if _is_readonly_member(descriptor):
                if value is not _UNSET and not equal(exact_tree(descriptor.__get__(clone, kind)), value):
                    raise TypeError("a read-only exception field differs after rebuilding")
                continue
            if value is _UNSET:
                continue  # 無い field: 写しでも置かない（確かめは下）
            if value is None:
                if type(descriptor) is _FIELD_DESCRIPTORS[1]:
                    continue  # getset: setter が `None` を「無い」に写す（読めば `None`）
                if _builtin_member(descriptor) and not any(item is descriptor for item in chosen):
                    continue  # 組み込みの C の field の NULL（読めば `None`）
            descriptor.__set__(clone, value)
        if state_items:
            target = _dict_holder(kind).__get__(clone, kind)  # 元と同じ型の `__dict__` の getset（hook を呼ばずに引いた）
            for name, value in state_items:
                dict.__setitem__(target, name, value)
        if not _exception_state_matches(error, clone, fields, kind, copied, items, state_items):
            raise TypeError("the copied exception state differs from the original")
    return clone


def _readonly_positions(plan: Tuple[Any, ...]) -> List[int]:
    """例外の計画の、読みだけの field の読みの位置（`_graph_values` の順）。"""

    _error, fields, _items, _chosen, start = plan
    positions = []
    cursor = start
    for descriptor, value in fields:
        if value is _UNSET:
            continue
        if _is_readonly_member(descriptor):
            positions.append(cursor)
        cursor += 1
    return positions


def _readonly_exceptions(plan: Tuple[Any, ...], read: Tuple[Any, ...]) -> List[Any]:
    """読みだけの field が持つ例外（写す前に写しが要る例外）。"""

    found: List[Any] = []
    for position in _readonly_positions(plan):
        found.extend(_nested_exceptions(read[position]))
    return found


def _readonly_values(
    plan: Tuple[Any, ...], read: Tuple[Any, ...], copies: Dict[int, Any], replaced: Dict[int, Any], alive: List[Any],
) -> List[Any]:
    """読みだけの field の写した値（中の例外は写しに置き換える: 写しは依存の順で先に作った）。"""

    return [_replace_exceptions(read[position], copies, replaced, alive) for position in _readonly_positions(plan)]


def _replace_exceptions(node: Any, copies: Dict[int, Any], replaced: Dict[int, Any], alive: List[Any]) -> Any:
    """読んだ木の葉の例外を、写した例外に置き換えた木（共有された容器は 1 度だけ置き換え、置き換えも共有する）。"""

    kind = type(node)
    if issubclass(kind, BaseException):
        if id(node) not in copies:
            raise TypeError("a nested exception is not copied before its container")
        return copies[id(node)]
    if not (kind is tuple or kind is list or kind is set or kind is frozenset or kind is dict):
        return node
    if not _nested_exceptions(node):
        return node
    done = replaced
    stack: List[Tuple[Any, bool]] = [(node, False)]
    count = 0
    while stack:
        current, leaving = stack.pop()
        holder = type(current)
        if leaving:
            children = list(dict.items(current)) if holder is dict else list(holder.__iter__(current))

            def swap(item: Any) -> Any:
                if issubclass(type(item), BaseException):
                    return copies[id(item)]
                return done.get(id(item), item)

            # 作り直しは `exact_tree` と同じ規則（`_rebuild_container`: hash で置く位置の要素は比べても hash しても
            # Python の code を呼ばない値だけ）
            if holder is dict:
                swapped = [item for k, v in children for item in (swap(k), swap(v))]
            else:
                swapped = [swap(item) for item in children]
            done[id(current)] = _rebuild_container(holder, swapped)
            alive.append(current)
            continue
        if id(current) in done:
            continue
        count += 1
        if count > SCAN_LIMIT:
            raise TypeError("an exception state beyond the scan limit is not copied")
        if not (holder is tuple or holder is list or holder is set or holder is frozenset or holder is dict):
            continue
        stack.append((current, True))
        children = [k for pair in dict.items(current) for k in pair] if holder is dict else list(holder.__iter__(current))
        for child in children:
            if issubclass(type(child), BaseException) and id(child) not in copies:
                raise TypeError("a nested exception is not copied before its container")
            child_kind = type(child)
            if child_kind is tuple or child_kind is list or child_kind is set or child_kind is frozenset or child_kind is dict:
                stack.append((child, False))
    return done[id(node)]


def _nested_exceptions(tree: Any) -> List[Any]:
    """組み込みの木（`exact_tree` の結果）の葉の例外。"""

    found: List[Any] = []
    stack = [tree]
    count = 0
    while stack:
        node = stack.pop()
        count += 1
        if count > SCAN_LIMIT:
            raise TypeError("an exception state beyond the scan limit is not read")
        kind = type(node)
        if kind is tuple or kind is list or kind is set or kind is frozenset:
            stack.extend(kind.__iter__(node))
        elif kind is dict:
            for key, item in dict.items(node):
                stack.append(key)
                stack.append(item)
        elif issubclass(kind, BaseException):
            found.append(node)
    return found


def _exception_instance_dict(error: Any) -> List[Tuple[Any, Any]]:
    """instance の `__dict__` の (名前, 値) の列（無ければ空）。`__dict__` の getset を型の名前空間から hook を呼ばずに引いて
    読み（`_dict_holder`: Python の属性の引きは名前空間の key の `__eq__` を呼び得る）、dict の subclass も dict の slot で
    辿る（例外の型の `__getattribute__` を呼ばない。名前を hash し直さない）。"""

    holder = _dict_holder(type(error))  # 型の名前空間を hook を呼ばずに引く（組み込みでない key なら `TypeError`）
    if holder is None:
        return []
    try:
        state = holder.__get__(error, type(error))
    except AttributeError:
        return []
    if not issubclass(type(state), dict):
        raise TypeError("an exception __dict__ that is not a dict is not read")
    return list(dict.items(state))


#: 例外の field に値が無い印（読むと `AttributeError`: `__slots__` の field・`OSError.characters_written` など）
_UNSET = object()


def _none_referents(value: Any) -> int:
    """`value` の型の traverse が辿る参照（`gc.get_referents`: NULL でない C の field・slot・`__dict__`）のうち `None` の数。

    型の field の数（型が決める）だけを辿る（C の code。値の型の Python の code は呼ばない）。
    """

    return sum(1 for item in gc.get_referents(value) if item is None)


def _traceback_keeps_none() -> bool:
    """`__traceback__` の setter が `None` を参照として残す版か（CPython 3.10 は残し、3.12 は NULL にする）。"""

    probe = BaseException()
    probe.__traceback__ = None
    return _none_referents(probe) == 1


_TRACEBACK_KEEPS_NONE = _traceback_keeps_none()


def _builtin_member(descriptor: Any) -> bool:
    """組み込みの例外の型の C の field（member の descriptor の owner が組み込みの型: NULL も `None` と読める）。"""

    return type(descriptor) is _FIELD_DESCRIPTORS[0] and _TYPE_MODULE.__get__(descriptor.__objclass__) == "builtins"


#: 観測と矛盾しない NULL / `None` の割り当てを数える上限（それより多ければ判定しない）
_ASSIGNMENT_LIMIT = 16


def _none_assignments(error: Any, fields: List[Tuple[Any, Any]]) -> List[Tuple[Any, ...]]:
    """`None` と読める組み込みの C の field のうち、明示的な `None` の field の組の候補（観測と矛盾しないもの全部）。

    型の traverse は NULL でない field だけを参照として辿るので、参照の `None` の数 = 明示的な `None` の `__slots__` の
    field の数 + 明示的な `None` の C の field の数 + `None` を残す getset（版による `__traceback__`）。その数に合う C の
    field の組を全部返す（1 つなら決まる。`_ASSIGNMENT_LIMIT` を超えれば `TypeError`: 判定しない）。
    """

    ambiguous: List[Any] = []
    slots = 0
    traceback_none = False
    for descriptor, value in fields:
        if value is not None:
            continue
        if _builtin_member(descriptor):
            ambiguous.append(descriptor)
        elif type(descriptor) is _FIELD_DESCRIPTORS[0]:
            slots += 1
        elif descriptor.__name__ == "__traceback__":
            traceback_none = True
    total = _none_referents(error)
    sizes = []
    for kept in ((0, 1) if traceback_none and _TRACEBACK_KEEPS_NONE else (0,)):
        explicit = total - slots - kept
        if 0 <= explicit <= len(ambiguous) and explicit not in sizes:
            sizes.append(explicit)
    count = sum(math.comb(len(ambiguous), size) for size in sizes)
    if count > _ASSIGNMENT_LIMIT:
        raise TypeError("too many assignments of None and nothing to builtin exception fields")
    return [chosen for size in sizes for chosen in itertools.combinations(ambiguous, size)]


def _builtin_str(kind: type) -> bool:
    """型の `__str__` が組み込みの C の実装（slot の wrapper）か（観測するのは C の field そのもの: 例外を投げない）。"""

    return type(_type_lookup(kind, "__str__", None)) is types.WrapperDescriptorType


def _new_exception(kind: type, args: List[Any]) -> Any:
    """`kind` の例外を組み込みの `__new__` で作る（`__init__` は呼ばない）。組み込みの基底を複数持つ型は、instance の
    形が合う組み込みの class の `__new__` を MRO の順に試す（`LookupError.__new__(X)` は形が違えば `TypeError`）。"""

    last: Optional[BaseException] = None
    mro = _TYPE_MRO.__get__(kind)
    if not _within_scan(tuple.__len__(mro)):
        raise TypeError("the MRO of the type is beyond the scan limit")
    for klass in mro:
        if type(klass) is not type or _TYPE_MODULE.__get__(klass) != "builtins" or not issubclass(klass, BaseException):
            continue
        if _namespace_value(klass, "__new__") is _MISSING_DUNDER:
            continue
        try:
            return klass.__new__(kind, *args)
        except TypeError as error:
            last = error
    raise TypeError(f"no builtin __new__ makes the exception: {last}")


def _is_readonly_member(descriptor: Any) -> bool:
    """`__new__` だけが置ける読みだけの field（`BaseExceptionGroup` の `message` / `exceptions`。名前空間の順に渡す）。"""

    return (
        _BASE_EXCEPTION_GROUP is not None and type(descriptor) is _FIELD_DESCRIPTORS[0]
        and descriptor.__objclass__ is _BASE_EXCEPTION_GROUP
    )


_BASE_EXCEPTION_GROUP = getattr(__import__("builtins"), "BaseExceptionGroup", None)


def _defining_class(kind: type, name: str) -> type:
    """`kind` の MRO で `name` を名前空間に持つ最初の class（metaclass の hook を呼ばない。無ければ `object`）。"""

    mro = _TYPE_MRO.__get__(kind)
    if not _within_scan(tuple.__len__(mro)):
        raise TypeError("the MRO of the type is beyond the scan limit")
    for klass in mro:
        found = _namespace_value(klass, name)
        if found is _AMBIGUOUS_NAME:
            raise TypeError(f"a class namespace holds a key that is not a builtin str (looking up {name!r})")
        if found is not _MISSING_DUNDER:
            return klass
    return object


def _exception_state_matches(
    error: Any, clone: Any, fields: List[Tuple[Any, Any]], kind: type, intended: List[Tuple[Any, Any]],
    items: List[Tuple[Any, Any]], state_items: List[Tuple[Any, Any]],
) -> bool:
    """写しの状態が元と同じか: field ごとの無い / `None` / 値の別と置いた値、field 間・`__dict__` の値の identity の関係
    （元で同じ object の値は、写しでも同じ object）、参照の `None` の数（`None` を残す getset の差だけ許す）。"""

    copied = _exception_fields(clone, kind)
    if len(copied) != len(fields) or len(intended) != len(fields):
        return False
    traceback_none = False
    for (descriptor, value), (other, copy), (_same, wanted) in zip(fields, copied, intended):
        if descriptor is not other:
            return False
        if (value is _UNSET) != (copy is _UNSET) or (value is None) != (copy is None):
            return False
        if (
            wanted is not _UNSET and wanted is not None and not _is_readonly_member(descriptor)
            and not (copy is wanted or (_exact_leaf(copy) and equal(copy, wanted)))
        ):
            return False  # 置いた値が残っていない（他の field の setter が書き換えた）
        if value is None and type(descriptor) is _FIELD_DESCRIPTORS[1] and descriptor.__name__ == "__traceback__":
            traceback_none = True
    # identity の関係（元で同じ object の値は写しでも同じ object）
    originals = [value for _d, value in fields] + [value for _n, value in items]
    copies = [value for _d, value in copied] + [value for _n, value in state_items]
    if not _within_scan(len(originals)):
        return False
    if not _identity_kept(list(zip(originals, copies))):
        return False
    difference = _none_referents(error) - _none_referents(clone)
    return difference == 0 or (difference == 1 and traceback_none and _TRACEBACK_KEEPS_NONE)


def _identity_kept(pairs: List[Tuple[Any, Any]]) -> bool:
    """(元, 写し) の組から辿れる node の identity の関係が写しで保たれているか: 元で同じ object の node は、写しでも
    同じ object（field の値どうしと、tuple / list / dict の中の共有）。順序の無い set の中は辿らない。"""

    read = _StorageRead(_COMPARISON_NODES, traversal=True)
    partner: Dict[int, Any] = {}
    alive: List[Any] = []
    pending = list(pairs)
    while pending:
        original, copy = pending.pop()
        if original is _UNSET or original is None:
            continue
        found = partner.get(id(original), _MISSING_DUNDER)
        if found is not _MISSING_DUNDER:
            if found is not copy:
                return False
            continue
        partner[id(original)] = copy
        alive.append(original)
        base = _subclass_tree_kind(type(original))
        if base is tuple or base is list:
            if type(copy) is not base or base.__len__(original) != base.__len__(copy):
                return False
            read.admit(base.__len__(original))
            pending.extend(zip(base.__iter__(original), base.__iter__(copy)))
        elif base is dict:
            if type(copy) is not dict or dict.__len__(original) != dict.__len__(copy):
                return False
            read.admit(2 * dict.__len__(original))
            pending.extend(zip(itertools.chain.from_iterable(dict.items(original)), itertools.chain.from_iterable(dict.items(copy))))
    return True


#: 組み込みの例外の C の field の descriptor の型
_FIELD_DESCRIPTORS = (types.MemberDescriptorType, types.GetSetDescriptorType)
#: 状態の dunder の getset（組み込みの `__str__` は読まないが、自前の `__str__` が読み得る状態）
_STATE_GETSETS = frozenset({"__cause__", "__context__", "__traceback__"})


def _exception_fields(error: Any, owner: type) -> List[Tuple[Any, Any]]:
    """`owner`（例外の型）の MRO の名前空間の field の descriptor と、その値（descriptor の slot で読む）。

    member の descriptor（組み込みの C の field・`__slots__` の field: 名前を問わない。`__payload__` のような dunder の
    名前の slot も状態）は全部。getset は `args` などの dunder でない名前と、状態の dunder（`_STATE_GETSETS`）だけ
    （`__dict__` / `__weakref__` は除く: `__dict__` は別に読む）。読むと `AttributeError` の field は `_UNSET`（無い）。
    明示的な `None` は `None`。
    """

    fields: List[Tuple[Any, Any]] = []
    for klass in _TYPE_MRO.__get__(owner):
        for name, descriptor in _TYPE_DICT.__get__(klass).items():
            holder = type(descriptor)
            if type(name) is not str:
                continue
            if holder is _FIELD_DESCRIPTORS[1]:
                if name.startswith("__") and name not in _STATE_GETSETS:
                    continue
            elif holder is not _FIELD_DESCRIPTORS[0]:
                continue
            try:
                fields.append((descriptor, descriptor.__get__(error, type(error))))
            except AttributeError:
                fields.append((descriptor, _UNSET))
    return fields


def scalar_repr(value: Any) -> str:
    """`repr(value)` と同じ値（規則は `scalar_text` と同じ。組み込みの `str` そのもので返す）。"""

    tree, leaves = _exact_tree_read(value)
    return exact_scalar(repr(tree if leaves else value))


#: `exact_tree` が 1 回の写しで読む容器の要素の量の名前
_TREE_NODES = "a value tree's container items"


#: `exact_tree` が辿る容器の基底の型（値の型の MRO で見る。subclass は基底の型の容器へ写す）
_TREE_BASES = (tuple, list, dict, set, frozenset, collections.deque)
#: dict の view（subclass を作れない組み込みの型）。要素を組み込みの slot で辿り、list に写す
_DICT_VIEWS = (type({}.keys()), type({}.values()), type({}.items()))
#: `OrderedDict` の view: 反復が key ごとに連結 list の node を hash で引き直す（key の型の `__hash__` / `__eq__`）。
#: 辿れないので判定しない（`TypeError`。成功にも「葉」にもしない）
_ODICT_VIEWS = (
    type(collections.OrderedDict().keys()), type(collections.OrderedDict().values()), type(collections.OrderedDict().items()),
)


def _tree_kind(value: Any) -> Optional[type]:
    """`exact_tree` が辿る容器の基底の型（組み込みの tuple / list / dict / set / frozenset と `deque`。subclass を含む）。

    型は `type(value)` の MRO で見る（`isinstance` と違い、値の `__class__` / `__getattribute__` を読まない）。
    """

    kind = type(value)
    if kind is tuple or kind is list or kind is dict or kind is set or kind is frozenset:
        return kind
    if kind is _DICT_VIEWS[0] or kind is _DICT_VIEWS[1] or kind is _DICT_VIEWS[2]:
        return kind
    if kind is _ODICT_VIEWS[0] or kind is _ODICT_VIEWS[1] or kind is _ODICT_VIEWS[2]:
        raise TypeError("an OrderedDict view is not read without hashing its keys")
    return _subclass_tree_kind(kind)


#: 型ごとの `_subclass_tree_kind` の結果（`id(型)` → (型, 結果)。型の `__hash__` / `__eq__` を呼ばない。型は生かしておく）
_KIND_CACHE: Dict[int, Tuple[type, Optional[type], bool]] = {}
_KIND_CACHE_LIMIT = 4096


def _kind_entry(kind: type) -> Tuple[type, Optional[type], bool]:
    """(型, 辿る容器の基底の型, scalar でも容器でもない葉か)。MRO は C の slot で見る（hook を呼ばない）。"""

    entry = _KIND_CACHE.get(id(kind))
    if entry is not None and entry[0] is kind:
        return entry
    base_kind: Optional[type] = None
    for base in _TREE_BASES:
        if issubclass(kind, base):
            base_kind = base
            break
    opaque = base_kind is None and not issubclass(kind, (int, float, str))
    entry = (kind, base_kind, opaque)
    if len(_KIND_CACHE) >= _KIND_CACHE_LIMIT:
        _KIND_CACHE.clear()
    _KIND_CACHE[id(kind)] = entry
    return entry


def _subclass_tree_kind(kind: type) -> Optional[type]:
    return _kind_entry(kind)[1]


class _VerifiedTrees:
    """1 回の ref の層の呼び出しの間（入口・key の出口の包み: `runtime_ref_record` が `depth` を数える）に確かめた、
    変わらない組み込みの木の memo（Issue #242）。

    入れ子の key の出口と子の key の読みは、同じ部分木を何度も `exact_tree` に通す。`depth` が 0 でない間は、確かめ済みの
    tuple / frozenset（部分木に変わる容器が無いもの）を辿らずに組み込みの木として扱い、1 回の呼び出し全体の走査を
    作った容器の数に比例させる。変わる容器（list / dict / set）とそれを部分木に持つ tuple は毎回確かめる（外の code が
    途中で変え得る: 健全さのための読み直し）。各段に新しい変わる容器を持つ鎖だけは段の 2 乗の走査になる（production
    の鎖の key は tuple だけ）。最も外の呼び出しが抜けるとき（例外を含む）に memo を捨てる。

    入れるのは tuple / frozenset で、その部分木に変わる容器（list / dict / set）を持たないもの（葉は exact な scalar か
    辿らない外の object）: 確かめた後に外の code が中身を変えられない。memo の key は `id` で、object を持って生かす
    （走査の間に `id` が別の object に再利用されない）。最も外の呼び出しが抜けると空にする（長く持つ cache ではない）。
    thread ごとに 1 つ（`threading.local`）: 同じ thread の中の呼び出しは同期で、入れ子だけが重なる。
    """

    __slots__ = ("nodes", "depth")

    def __init__(self) -> None:
        self.nodes: Dict[int, Any] = {}
        self.depth = 0


_VERIFIED_LOCAL = threading.local()
#: `exact_tree` が確かめた容器の数（走査量: test が読む。scope の memo で飛ばした容器は数えない）
_TREE_VISITS = [0]


def _verified_trees() -> _VerifiedTrees:
    holder = getattr(_VERIFIED_LOCAL, "holder", None)
    if holder is None:
        holder = _VERIFIED_LOCAL.holder = _VerifiedTrees()
    return holder


def _active_memo() -> Optional[_VerifiedTrees]:
    """今の thread の scope の memo（scope の外なら `None`）。"""

    holder = getattr(_VERIFIED_LOCAL, "holder", None)
    return holder if holder is not None and holder.depth else None


def verified_tree_holder() -> _VerifiedTrees:
    """今の thread の memo の入れ物（入口・key の出口の包みが深さを数え、最も外の呼び出しが抜けるときに空にする）。"""

    holder = getattr(_VERIFIED_LOCAL, "holder", None)
    if holder is None:
        holder = _VERIFIED_LOCAL.holder = _VerifiedTrees()
    return holder


def exact_tree_in(value: Any, holder: _VerifiedTrees) -> Any:
    """`exact_tree(value)` を、包みが既に持つ scope の入れ物で読む（保証と読み方は `exact_tree` と同じ）。

    葉が exact な scalar だけの平らな tuple（最も多い key の形）は、ここで確かめて memo に入れる。
    """

    kind = type(value)
    if value is None or kind is int or kind is str or kind is bool or kind is float:
        return value
    if kind is tuple and tuple.__len__(value) <= SCAN_LIMIT:
        for item in value:
            held = type(item)
            if not (item is None or held is int or held is str or held is bool or held is float):
                break
        else:
            _TREE_VISITS[0] += 1
            if holder.depth:
                holder.nodes[id(value)] = value
            return value
    tree = _exact_tree_read(value, holder if holder.depth else None)[0]
    if tree is _CYCLIC:
        raise TypeError("a cyclic container of container subclasses is not copied to a plain tree")
    return tree


def _already_plain(value: Any, memo: Optional[_VerifiedTrees] = None) -> bool:
    """`value` が既に組み込みの木か（容器は組み込みの型そのもの・共有と閉路が無い・葉は exact な scalar か scalar でも
    容器でもない object・要素の数は `SCAN_LIMIT` まで）。確かめるだけで何も作らない（`exact_tree` の速い経路。
    当てはまらなければ遅い経路が同じ規則で読む）。`memo` の確かめ済みの木は辿らない。確かめた tuple / frozenset の
    うち、部分木に変わる容器（list / dict / set）を持たないものを `memo` に入れる（変わる容器が無ければ全部、在れば
    部分木ごとに: 先順の逆で子から決める）。"""

    stack: List[Any] = [value]
    seen: set = set()
    count = 0
    frozen: List[Any] = []
    mutable_seen = False
    while stack:
        node = stack.pop()
        kind = type(node)
        if node is None or kind is int or kind is str or kind is bool or kind is float:
            continue
        if kind is tuple or kind is list or kind is set or kind is frozenset or kind is dict:
            if memo is not None and id(node) in memo.nodes:
                continue  # 確かめ済みの変わらない木
            if id(node) in seen:
                if kind is tuple or kind is frozenset:
                    continue  # 共有された変わらない容器は確かめ済み（閉路は変わる容器を通るので、そこで見つかる）
                return False  # 変わる容器の共有・閉路は遅い経路（memo と閉路の規則）
            seen.add(id(node))
            _TREE_VISITS[0] += 1
            count += kind.__len__(node) * (2 if kind is dict else 1)
            if count > SCAN_LIMIT:
                return False  # 上限の外の意味は遅い経路の読み（文脈の owner）
            if kind is tuple or kind is frozenset:
                frozen.append(node)
                stack.extend(kind.__iter__(node))
            elif kind is dict:
                mutable_seen = True
                for key, item in dict.items(node):
                    stack.append(key)
                    stack.append(item)
            else:
                mutable_seen = True
                stack.extend(kind.__iter__(node))
            continue
        if (
            kind is _DICT_VIEWS[0] or kind is _DICT_VIEWS[1] or kind is _DICT_VIEWS[2]
            or kind is _ODICT_VIEWS[0] or kind is _ODICT_VIEWS[1] or kind is _ODICT_VIEWS[2]
            or not _kind_entry(kind)[2]
        ):
            return False
    if memo is not None:
        if not mutable_seen:
            for node in frozen:
                memo.nodes[id(node)] = node
        else:
            # 先順の逆（子が親より先）: 子の容器がどれも変わらない木なら、その tuple / frozenset も変わらない木
            immutable: set = set()
            for node in reversed(frozen):
                for child in type(node).__iter__(node):
                    held = type(child)
                    if held is list or held is dict or held is set:
                        break
                    if (held is tuple or held is frozenset) and not (id(child) in immutable or id(child) in memo.nodes):
                        break
                else:
                    immutable.add(id(node))
                    memo.nodes[id(node)] = node
    return True


def _tree_length(node: Any, kind: type) -> int:
    """容器の要素の数（基底型の slot で O(1)。dict は key と値の 2 つずつ）。"""

    if kind is dict:
        return 2 * dict.__len__(node)
    return kind.__len__(node)


def _tree_children(node: Any, kind: type) -> List[Any]:
    """容器の要素（dict は key と値を交互に）を基底型の slot で読む（呼ぶ側が先に数を上限と比べる）。"""

    if kind is dict:
        children: List[Any] = []
        for key, item in dict.items(node):
            children.append(key)
            children.append(item)
        return children
    return list(kind.__iter__(node))


def _tree_rebuild(node: Any, kind: type, items: List[Any]) -> Any:
    """写した要素から **組み込みの型そのもの** の容器を作る（呼ぶ側が先に数を上限と比べる）。

    外の constructor / `_make` は呼ばない（作り直すときに葉を scalar の subclass へ包み直し得る）。subclass の容器・
    named tuple・`OrderedDict` / `defaultdict` / `Counter` は基底の型（tuple / list / dict / set / frozenset）の
    容器になり、`deque` は list になる（値は同じ。型は保たない）。
    """

    if (
        kind is collections.deque or kind is _DICT_VIEWS[0] or kind is _DICT_VIEWS[1] or kind is _DICT_VIEWS[2]
    ):
        return list(items)
    return _rebuild_container(kind, items)


def _rebuild_container(kind: type, items: List[Any]) -> Any:
    """組み込みの容器を要素から作り直す（**作り直す経路の唯一の規則**: `exact_tree`・例外の写し）。dict の `items` は
    key と値の交互の列。

    hash で置く位置（set / frozenset の要素・dict の key）の要素は、比べても hash しても Python の code を呼ばない値
    だけ（`_rebuildable`）。そうでなければ `TypeError`（作り直すと要素の hash・`==` を双子に無い時点で呼び、`==` の戻り値
    を組み込みの code が真偽で読む: 写せない値）。
    """

    _admit_storage(len(items), _COMPARISON_NODES, traversal=True)
    if kind is dict:
        keys = items[0::2]
        if not all(_rebuildable(key) for key in keys):
            raise TypeError("a mapping whose keys may run code when hashed or compared is not rebuilt")
        return dict(zip(keys, items[1::2]))
    if kind is set or kind is frozenset:
        if not all(_rebuildable(item) for item in items):
            raise TypeError("a set whose elements may run code when hashed or compared is not rebuilt")
        return kind(items)
    if kind is tuple or kind is list:
        return kind(items)
    raise TypeError(f"{type_name(kind)} is not rebuilt")


def _rebuildable(value: Any) -> bool:
    """hash で置く位置に作り直してよい値か: exact な scalar とその tuple / frozenset、または比較と hash の dunder が全部
    不活性（`object` / 自己完結の組み込みの実装: Python の code を呼ばない）な object。分類は今の名前空間で読む。"""

    read = _StorageRead(_COMPARISON_NODES, traversal=True)
    pending = [value]
    while pending:
        node = pending.pop()
        kind = type(node)
        if node is None or kind is int or kind is str or kind is bool or kind is float:
            continue
        if kind is tuple or kind is frozenset:
            read.admit(kind.__len__(node))
            pending.extend(kind.__iter__(node))
            continue
        if _leaf_trust(node, _HASHING_DUNDERS) != _TRUSTED:
            return False
    return True


def exact_tree(value: Any) -> Any:
    """比べる・hash する・文字列にする前の値の写し（**組み込みの木**）。

    **読み方**: 組み込みの tuple / list / dict（key と値）/ set / frozenset とその subclass（named tuple・
    `OrderedDict` / `defaultdict` / `Counter` を含む）と `deque`・dict の view を（`OrderedDict` の view は反復が key を
    hash で引き直すので辿らずに `TypeError`）、型の MRO（型は identity で比べる:
    metaclass の `__eq__` を呼ばない）で見分けて基底型の slot で辿る
    （値の `__class__`・容器の `__iter__` / `__getitem__` の上書きを呼ばない）。辿る要素の数の和は値の storage の
    読みの 1 つの量（反復の確かめ）として上限と比べる（#22）。

    **返す値の保証**: 容器は組み込みの tuple / list / dict / set / frozenset **そのもの**（subclass は基底の型、
    `deque` と dict の view は list。外の constructor / `_make` を呼ばずに組み込みの型の constructor で作る）、scalar の葉は組み込み
    の型そのもの（`exact_scalar`。1 回の読みの中で共有された葉は 1 度だけ写し、写しも共有する）、それ以外の葉（enum の member・scalar でない object）は同じ object（その object
    の code は外の code）。葉と容器がどれも既に組み込みの型そのものなら同じ object を返す。共有された容器は 1 度
    だけ辿って結果も共有する（辿った容器は走査の終わりまで生かす: memo の `id` を再利用させない）。写しが要る閉路は
    `TypeError`（元の容器を指す写しを作らない: fail-closed）。それ以外の葉の object から後で取得する値（その method /
    属性の結果）は保証しない（読んだ側が reader で読む）。

    **走査量**: ref の層の呼び出しの中（`_VerifiedTrees`）では、確かめ済みの変わらない木（部分木に変わる容器の無い
    tuple / frozenset）を辿らない。1 回の ref の層の呼び出しの走査は、作った容器の数に比例する。

    外の object（代わりの型・API の object）の method の戻り値（key など）や、受理したまま持つ容器を、比べる・
    並べる・dict の key にする・`str()` にする前に読む reader（Issue #242）。型を保たないことの影響: subclass の
    容器の型・`repr` は基底の型のもの（named tuple は tuple、`deque` は list: `deque` と list は `==` が違う）。
    """

    kind = type(value)
    if value is None or kind is int or kind is str or kind is bool or kind is float:
        return value  # exact な scalar（最も多い形: 読みの層を通らない）
    entry = _KIND_CACHE.get(id(kind))
    if entry is not None and entry[0] is kind and entry[2]:
        return value  # 型を確かめ済みの、scalar でも容器でもない葉（API の object）: 同じ object（`_exact_tree_read` と同じ）
    tree = _exact_tree_read(value)[0]
    if tree is _CYCLIC:
        raise TypeError("a cyclic container of container subclasses is not copied to a plain tree")
    return tree


def holds_scalar_subclass(value: Any) -> bool:
    """`exact_tree` が辿る木の葉に scalar の subclass が在るか（読み方は `exact_tree` と同じ。返す値は `bool`）。

    在らなければ、元の値の文字列化・`repr` は双子と同じ（容器の型の `repr` を保つために、元の値で文字列にする
    reader が使う）。
    """

    return _exact_tree_read(value)[1]


#: 組み込みの木を作れない閉路（葉に scalar の subclass は無い）
_CYCLIC = object()


_ACTIVE = object()


def _exact_tree_read(value: Any, memo: Any = _ACTIVE) -> Tuple[Any, bool]:
    """`exact_tree` の本体: (組み込みの木, scalar の葉を写したか)。`memo` は今の scope（渡されなければ読む）。"""

    kind = type(value)
    if value is None or kind is int or kind is str or kind is bool or kind is float:
        return value, False  # exact な scalar（最も多い形）
    if memo is _ACTIVE:
        memo = _active_memo()
    if kind is tuple or kind is list or kind is set or kind is frozenset or kind is dict:
        if memo is not None and id(value) in memo.nodes:
            return value, False  # この scope で確かめ済みの変わらない木
        # よくある形（既に組み込みの木）: 確かめるだけで何も作らずに同じ object を返す。葉が exact な scalar だけの
        # 平らな tuple / list はさらに短い経路
        if (kind is tuple or kind is list) and len(value) <= SCAN_LIMIT:
            for item in value:
                holder = type(item)
                if not (item is None or holder is int or holder is str or holder is bool or holder is float):
                    break
            else:
                _TREE_VISITS[0] += 1
                if memo is not None and kind is tuple:
                    memo.nodes[id(value)] = value
                return value, False
        if _already_plain(value, memo):
            return value, False
    elif _tree_kind(value) is None:
        leaf = exact_scalar(value)
        return leaf, leaf is not value
    read = _StorageRead(_TREE_NODES, traversal=True)
    done: Dict[int, Any] = {}
    children_of: Dict[int, List[Any]] = {}
    active: set = set()  # 入って、まだ出ていない容器（ここへ戻る要素は閉路）
    alive: List[Any] = []  # 入った容器（memo の key の `id` が指す object を走査の間は生かす）
    cyclic = False
    changed = False
    leaves = False  # scalar の葉を写したか
    frozen_out: set = set()  # 部分木に変わる容器の無い結果の tuple / frozenset（後順で決める: memo に入れる）
    stack: List[Tuple[Any, bool]] = [(value, False)]
    while stack:
        node, leaving = stack.pop()
        kind = _tree_kind(node)
        if not leaving:
            if id(node) in done:
                continue
            done[id(node)] = node  # 入った印（同じ容器に再び出会うのは共有か閉路: 閉路は辿り直さない）
            alive.append(node)  # `id` を走査の終わりまで再利用させない（view が反復のたびに作る組を含む）
            active.add(id(node))
            _TREE_VISITS[0] += 1
            read.admit(_tree_length(node, kind))
            children = _tree_children(node, kind)
            children_of[id(node)] = children
            stack.append((node, True))
            for item in children:
                if memo is not None and id(item) in memo.nodes:
                    continue  # 確かめ済みの変わらない木（辿らない）
                if _tree_kind(item) is not None and id(item) not in done:
                    stack.append((item, False))
            continue
        children = children_of.pop(id(node))
        # 組み込みの型そのものでない容器（subclass・named tuple・`deque`）は、葉が変わらなくても基底の型へ写す
        # 型は identity で比べる（`in` は metaclass の `__eq__` を呼ぶ）
        node_type = type(node)
        plain = node_type is tuple or node_type is list or node_type is dict or node_type is set or node_type is frozenset
        items: Optional[List[Any]] = None if plain else list(children)
        for index, item in enumerate(children):
            holder = type(item)
            if item is None or holder is int or holder is str or holder is bool or holder is float:
                continue
            if memo is not None and id(item) in memo.nodes:
                new = item
            elif _tree_kind(item) is not None:
                cyclic = cyclic or id(item) in active
                new = done[id(item)]
            else:
                # 共有された scalar の subclass の葉は 1 度だけ写し、写しも共有する（容器と同じ: 写した木の葉の identity
                # は元の木の葉の identity に従う。比べる側の identity の規則が双子と同じになる）
                new = done.get(id(item), _MISSING)
                if new is _MISSING:
                    new = exact_scalar(item)
                    done[id(item)] = new
                leaves = leaves or new is not item
            if new is not item:
                if items is None:
                    items = list(children)
                items[index] = new
        active.discard(id(node))
        if items is not None:
            changed = True
            done[id(node)] = _tree_rebuild(node, kind, items)
        result = done[id(node)]
        if type(result) is tuple or type(result) is frozenset:
            whole = True
            for child in type(result).__iter__(result):
                held = type(child)
                if held is list or held is dict or held is set:
                    whole = False
                    break
                if (held is tuple or held is frozenset) and not (
                    id(child) in frozen_out or (memo is not None and id(child) in memo.nodes)
                ):
                    whole = False
                    break
            if whole:
                frozen_out.add(id(result))
    if cyclic and changed:
        # 閉路を持つ容器の写しは元の容器を指してしまう: 組み込みの木を作れない（空や元の値にしない）。葉に scalar の
        # subclass が無ければ、元の値の文字列化だけは双子と同じにできる（呼ぶ側が `_CYCLIC` を見る）
        if leaves:
            raise TypeError("a cyclic container holding scalar subclasses is not copied")
        return _CYCLIC, False
    if memo is not None and not cyclic:
        for result in done.values():
            if id(result) in frozen_out:
                memo.nodes[id(result)] = result
    return done[id(value)], leaves


# ---------------------------------------------------------------------------
# 比較・所属・順序・hash（Issue #242: 暗黙の callback が返す値を読む）
# ---------------------------------------------------------------------------
#
# `exact_tree` の保証は「木の正規化」（容器は組み込みの型そのもの、scalar の葉は組み込みの型そのもの）で、葉の外の
# object は外の code のまま残る。その木を比べる・`in` で探す・並べる・hash で置くと、組み込みの code が葉の型の
# `__eq__` / `__lt__` などを呼び、その戻り値（scalar の subclass かもしれない値）の真偽を C で読む（`__bool__` の hook）。
#
# この節が比べる側の契約の owner。比較そのもの（要素を読む時点・長さ・identity・hash の衝突の探索の順・再帰の上限）は
# **Python の組み込みの処理に任せ**、再実装しない。外の code に渡るのは元の値で、渡る順も双子と同じ。
#
# 変更軸ごとの interface:
# - 値の読み: `exact_tree` / `_compared_tree`（比べる値を 1 回の読みで写す。共有は保つ。読めない値は判定不能）。
# - 比較・hash: `equal` / `unequal` / `less` / `contains` / `sorted_trees` / `hash_tree`、`@trusted_comparison`。
# - 型の判定: `_leaf_trust`（使う時点の分類）・`_NamespaceReader`（名前空間の読み）・`_TypeFactTable`（引くたびに
#   型の状態を確かめる型の事実の表）。
# - 判定不能: `UndecidableComparison` / `undecidable()`（owner `core/comparison_limits` が pair の台帳へ記録する）。
# - 作り直し: `_rebuild_container`（`exact_tree`・例外の写しの唯一の規則）。
#
# 前提と、それが成り立つ間（いつまで安全か）・変える操作・失敗の伝わり方:
# | 前提 | 成り立つ間 | 変える操作 | 確かめ / 失敗したとき |
# |---|---|---|---|
# | 葉の比較の分類（不活性・package の比較・外の code・不透明） | 次に外の code を呼ぶまで | class の名前空間・`__bases__`・instance の `__class__` の書き換え | 分類は使う時点で読む（`_ComparisonScope` の memo は外の code の呼び出しで捨てる）。不活性は比較と hash の dunder が全部 Python の code を呼ばないこと（`in`・set の引きは葉を hash する）。葉のどれかが Python の code を呼び得るなら、exact でない葉を全部包む |
# | 名前空間の読みが hook を呼ばない | 確かめた名前空間は class が生きている間（書き換えは名前を組み込みの `str` にして置く: `_STR_KEYED_NAMESPACES`） | 組み込みでない key を持つ class を作る（`type()` の dict・`__prepare__`）。storage への直接の書き込みは前提の外 | key が全部組み込みの `str` かを使うたびに C の反復で確かめる。組み込みの `str` でない key（文字列に依らない: 引きは hash の等しい key の `__eq__` を呼ぶ）があればどの名前も決めない（不透明 / `TypeError`） |
# | 型の事実の表（`package_type` など） | 型の状態が記録したときと同じ間 | 名前空間・`__bases__`・metaclass の書き換え、表の値の中身の書き換え | 引くたびに型の状態（identity の tuple、object は生かす）と、判定が読んだ key の型の MRO の外の class（値の型・入れ子の型: `_Nesting.reads`）の状態と、判定が型・中身を読んだ object（名前空間の値と、それが包む関数・accessor・判定が中を辿った実行環境の関数とその closure の cell・cell の中身・`lru_cache` が呼ぶ関数: `_Nesting.objects`）の identity の外の状態（`_watch`: heap type の instance の `__class__`・組み込みの descriptor の中身・信頼していない関数（判定が偽・中を辿る）の `__code__`・cell の中身）を比べ、違えば判定し直す。判定の途中に引いた記録の依存は今の判定の依存へ足す。`lru_cache` の wrapper は C の struct が呼ぶ関数で判定する（`__wrapped__` は書き換えられる） |
# | 写しと元が同じ | 外の code が元を変えない間 | 写した容器の元・包まない値・基底型の値で比べる容器の subclass の元の、中身・`__class__`・型の名前空間の変更 | 外の code の呼び出しごとに確かめ（`_CopyFrame`）、変わっていれば判定不能 |
# | hash が同じ値の間で変わらない | 値と値が持つ葉の object が変わらない間 | （読みが作る object の identity: NaN の hash） | NaN は identity で比べ・hash する: exact な NaN は読まずにその object、scalar の subclass の NaN は元の葉ごとに 1 つの写し（`_canonical_nan`: 元の葉が生きている間は同じ写し。表は元の葉を weakref でだけ持ち、葉が消えれば entry も消える）。weakref を作れない型の NaN の葉は判定不能（D20: 写しを葉の寿命に結ぶには葉を持ち続けるしかない）。比較・正規化・hash は同じ写しを見る |
# | 名前の引きだけで決まる型の事実（`lookup_fact`: `_BUILTIN_HASHED`・`_builtin_behaviour`・JSON の protocol） | 引いた名前が同じ object を引く間 | 名前空間・`__bases__` の書き換え、引いた object の `__class__`・descriptor の中身の書き換え | 引くたびに key の型の MRO の identity・引いた (storage, 名前, 見つけた object)・見つけた object 自身の identity の外の状態（`_watch`。計算は見つけた object の中身を読まない）を確かめ、違えば計算し直す。計算の途中に引いた記録の読みは外の計算の読みへ足す |
# | 名前空間の storage の列（`_PLAIN_MROS`・`_STATIC_NAMESPACES`） | MRO の tuple が同じ object の間 | `__bases__` の書き換え（MRO を作り直す） | 引くたびに MRO の identity を比べる。storage は class が生きている間同じ dict・key は組み込みの `str` のまま（上の行の前提）・組み込みの型の名前空間は変わらない |
# | 監査済みの区間の記録（`audited_region` / `region_cache`: JSON の型の protocol の判定など） | 区間（最も外の `audited_region`）の間、外の code が走っていない間（区間を開けた thread の中の code。他の thread は前提の外の段落） | 外の code（監査の外の code: identity key の method・宣言していない package の generator・値の code を呼ぶ境界・比べる側の契約が呼ぶ外の比較と hash）。J19 の監査が辿る code が live な値を渡す owner の関数は値の code を呼ばない（呼ぶものは `value_code_boundary` で宣言し、その呼び出しを `outside_audit` の下に置く） | 外の code が走るのは外の code の区間（`outside_audit`）の中だけ: 走る間ずっと区間の外（入り直しても記録を見ない）。抜ければ（例外・中断でも）記録を捨てる。区間を閉じれば捨てる。区間の外は引くたびに上の行の確かめ。開ける場所・境界・owner の関数の分類は static test が監査の結果と突き合わせる |
# | 監査済みの code が頼る値の型（walker の receiver: record・reducer・sized leaf・property / state setter の持ち主、`package_instance` で絞り込んだ値。第 11 回） | 頼り始めてから外の code の区間を抜けるまで。generator の中の絞り込みは次の `yield` まで | 外の code（区間の中）が型の名前空間・`__bases__`・値の `__class__`・protocol の method を書き換える。監査済みの code の外（activation の無い間）の書き換え | 頼る事実は activation（`relying_on` / `audited_entry` / walk 自身）に記録し、外の code の区間を抜けるときに走っている activation を全部確かめ直す（`_recheck_reliance`）。walker が進める監査済みの generator（record の `json_items`・`receiver_items`・宣言した generator。止まっているものを含む）は frame が receiver（型・protocol・method）を持ち、走っている walk（`_Reliance.walks`）の frame を同じ区間の出口で確かめ直す（`json_encoding._Walk.recheck`。token の digest の整列で frame を積む前に引き出す列も含む）。walk の中の 1 歩・converter の中の絞り込みは歩の後に捨てる。`package_instance` は監査済みの code の中（activation がある）で絞り込むたびに型の信頼を確かめる（外は契約の外: 型の identity だけ。監査済みの code は必ず activation の中で走る: test が root ごとに確かめる。activation のstack が続き、外の code の数が同じ間だけ記録を使い回す）。落ちればその型の code を呼ぶ前に判定不能。J19 の監査は `type(x) is C`（C は package の型）を絞り込みに数えず、絞り込みが `yield` をまたぐ読みと、receiver を新しい generator へ渡して yield の後に読む形を拒む。絞り込む entry root は`audited_entry` の宣言が要る（test が辿る関数から決める） |
# | 組（(key, 値)。`inline` / `pairs_of` / record の `json_items` / `mapping_of`）の中の構造 | いつも | tuple / list の subclass の `__iter__` / `__getitem__` / `__len__`（unpack・添字が呼ぶ） | 組は `read_pair` で読む（基底型の slot。exact な tuple はそのまま）。組でない値・長さが 2 でない組は値の code を呼ぶ前に拒む。J19 の監査は、要素が組み込みの tuple と分かる列（owner の組の読み・package の容器の `.items()`・`enumerate` / `zip`）の要素だけの unpack を許す |
# | instance の `__dict__` を読む descriptor（`_DICT_HOLDERS`） | MRO の tuple が同じ object の間 | `__bases__` の書き換え | metaclass が `type` の class の `__dict__` の entry は作った後に書けも消せもしない（`_fixed_dict_entries`: CPython 3.10 / 3.12 で確かめる test）。そうでない MRO は記録しない。引くたびに MRO の identity を比べる |
# | 判定不能が確定判定にならない | いつも | helper・`except` の捕捉 | 普通の例外の派生でない。作るときに pair の台帳へ記録（登録した reason `comparison_undecidable`、`blocks_decision`）。名指しの捕捉は分類した場所だけ |
# | ref の比べる field（owner `core/runtime_ref_record`） | 固定した後はずっと（class ごとに最初の使用で固定。自分の表を持たない subclass は親の表の固定を共有） | `__dataclass_fields__`・`Field.compare` / `repr` の書き換え | 書き換えは使わない（固定した表で比べ・hash し・写す: 同じ ref の比べ方と hash は使う間変わらない。PR の D17）。表は固定するときに hook を呼ばずに読み（`dataclass_field_specs`）、読めない表は決めない（比較・hash は判定不能、作るのは `TypeError`） |
# | dataclass の field の名前（`dataclass_field_names`: owner の外の読み手） | 記録した表の中身と同じ間 | 同上 | 引くたびに表の中身（key・`Field`・種類の slot）を確かめ（`_dataclass_table_state`）、違えば読み直す（今の表に従う） |
#
# 前提の外（この契約が守らないもの。破られると分類の根拠が無くなる）: 監査済みの code が **自分で作った** package の object（名前で呼んだ package の class の instance と、その method の self: J19 の監査の OBJ / SELF / 構築した REC）の型の名前空間を外の code が書き換えること（監査済みの code が名前で呼ぶ code の書き換え: module の global の書き換えと同じ。値として受け取った object の型は上の行の確かめの内。作った object の型まで外の code の後に確かめ直すと、型の確かめ 1 つ 4〜6 µs × 外の code の区間の数 2 千〜1 万 3 千（replay のprocess ごと）× 型の数 約 60 の費用になる: 第 11 回の決定、PR の本文に選択肢と根拠）。信頼する関数（package の code・`Enum.__hash__`・
# 登録した比較）の code object・closure の中身・module の global・interpreter の builtin を書き換えること（code を書いて
# 実行できる側の操作: `trust_code_directory` の境界と同じ）。実行環境（標準 library の file）の関数の module の global・
# 既定値（`__defaults__` / `__kwdefaults__`）を書き換えること（interpreter の builtin と同じ実行環境の code: 判定は
# 実行環境の関数を、closure の中身だけを確かめて信頼する）。owner の基盤の object（walker が仕事を数える相手・policy:
# J19 の監査の `WORK`）の型の名前空間や、owner の object の状態を書き換えること（walker の source・`Tally`・`PreparedJson`
# は作った後に field を変えない。作業量（budget）の状態は owner の code が数えるたびに変え、package の外の code は参照を
# 持たない: 外の code がそれを書き換えるのは owner の code の書き換えと同じ。作業量・source を作る package の code は、
# 構成子が上限などを組み込みの値へ写す。producer が渡す object（record・
# `Reducer`）の型は前提の内: 呼ぶ時点で型から引いて確かめる）。割り当ての時点で走る finalizer・weakref の callback、
# bytecode の境目で走る Python の signal handler が class を書き換えること（`_Nesting` と同じ: 解析の値は判定の途中に
# code を実行しない。走れば分類の根拠が無くなる: その比較の答えは保証しない）。他の thread が判定の途中・監査済みの区間の
# 間に値の code を走らせて class・値を書き換えること（判定の記録・区間の記録・比較の memo は thread ごとで、外の code を
# 呼んだことを同じ thread の中でだけ知る: 他の thread の書き換えは引くたびの確かめの外。製品の code が始める thread は
# 値の code を走らせない場所だけ: `test_issue242_audited_regions.PRODUCTION_THREAD_STARTS` が始める場所を固定する）。interpreter を `-b` で動かすこと（`bytes`
# と `str` の比較が warning の filter・`showwarning`（Python の code）を呼ぶ: `bytes` を自己完結の型に数える前提）。
# 自己完結の型（`_SELF_CONTAINED`）は、比較と hash の C の実装が相手の protocol（`__buffer__`・`__index__` など）を呼ばない
# 型だけ（`bytearray` は相手の buffer を読むので数えない）。
#
# 保証する入力の範囲と判定不能（`UndecidableComparison`。等しい・違うの根拠にしない。判定不能を投げるのは、双子に無い
# 外の code の呼び出しの前: それまでの呼び出しは双子の呼び出しの先頭）:
# - 外の code が比較の途中で、比べている値の変わる容器（写した list / dict / set の元）を変えた、hash で置く位置の
#   包まない値の型・`__class__` を変えた（`_CopyFrame`）。
# - hash で置く位置（set / frozenset の要素・dict の key）に、比較が外の code の値（戻り値を組み込みの code が真偽で
#   読む）がある（写すと外の `__hash__` を双子に無い時点で呼ぶ）。dict の key が不活性でないのに値を包む必要がある。
# - 閉路の容器（写しが元へ戻り、包まない葉を組み込みの比較が読む）。
# - 比べ方が読む基底型と違う容器（比較・hash・`in` の dunder を変えた subclass・`deque`・dict の view・`OrderedDict`
#   など: `_comparison_shape`）。
# - 不透明な葉（interpreter と標準 library の C の比較が持っている値を比べる型: `slice`・`mappingproxy`・
#   `SimpleNamespace` など。名前空間に組み込みの `str` でない key がある型）の比較が実際に走るとき
#   （identity の近道は双子と同じに通す）。
# - `exact_tree` が写した容器を外の code に渡すとき、`exact_tree` が読めない値（作り直せない key・要素）。
# 範囲の外（契約が扱わない）: 外の object 自身の code が中で読む値（外の code の振る舞い）。
# 費用: 写した変わる容器の確かめは外の code の呼び出しごとに写した量に比例（C の反復で読む。1 回は `SCAN_LIMIT` の
# 読みの上限の中）。外の葉を持つ大きな list どうしの比較は呼び出しの数 × 量になる（production の key は tuple）。


class UndecidableComparison(Exception):
    """比べる値に、組み込みの code だけでは双子と同じに比べられない部分がある（判定しない。推測で等しい / 違うとしない）。

    `TypeError` / `ValueError` などの「回復できる」普通の例外の派生に **しない**（`core/errors` の型つきの失敗と同じ
    理由）: 派生にすると、helper の `except (TypeError, ...)` が判定不能を「値が無い」に変えてしまう。作るのは
    `undecidable()` だけ（owner が登録されていれば、owner の型を pair の台帳へ記録してから返す）。
    """


#: 判定不能の意味の owner（`register_undecidable_owner` で 1 つだけ。`core/comparison_limits`）
_UNDECIDABLE_OWNER: list = []


def register_undecidable_owner(owner: Any) -> None:
    """判定不能の owner を登録する（`core/comparison_limits` が import のときに 1 度。2 つ目の owner は `ValueError`）。

    `owner(detail)` は `UndecidableComparison` でもある型つきの限界を pair の台帳へ **記録してから** 返す package の
    関数（記録が先: 途中の `except Exception` が例外を握り潰しても、pair の境界が「判定不能があった」事実を読む）。
    この module は限界の種類を知らない（標準 library だけを import する）ので、owner の側が自分を登録する。
    """

    if type(owner) is not types.FunctionType or not package_code(owner.__code__):
        raise TypeError("an undecidable owner is a package function")
    if _UNDECIDABLE_OWNER:
        if _UNDECIDABLE_OWNER[0] is not owner:
            raise ValueError("the undecidable owner is already registered")
        return
    _UNDECIDABLE_OWNER.append(owner)


def undecidable(detail: str) -> UndecidableComparison:
    """判定不能の例外（`raise undecidable(...)`）。owner が登録されていれば、owner が台帳へ記録した型つきの限界。"""

    if _UNDECIDABLE_OWNER:
        found = _UNDECIDABLE_OWNER[0](detail)
        if isinstance(found, UndecidableComparison):
            return found
    return UndecidableComparison(detail)


#: 比べる側の契約が読む木の node の量の名前（`exact_tree` と同じ反復の確かめ: 量の owner の無い文脈では上限なし）
_COMPARISON_NODES = "a comparison's tree nodes"

#: 比較の dunder（信頼する葉はこの全部が `object` / 組み込みの型 / 登録した実装）
_COMPARISON_DUNDERS = ("__eq__", "__ne__", "__lt__", "__le__", "__gt__", "__ge__")

#: 信頼する比較の実装（package の関数: 組み込みの `bool` か `NotImplemented` を返し、外の code の戻り値を reader で読む）。
#: 比較の dunder の名前の下でだけ信頼する（`_classify_dunder`）
_TRUSTED_COMPARISONS: List[Any] = []
#: 信頼する hash の実装（`trusted_hash`）。`__hash__` の名前の下でだけ信頼する
_TRUSTED_HASHES: List[Any] = []


def trusted_comparison(function: Any) -> Any:
    """比べてよい `__eq__` などの実装として登録する（ref の owner の `__eq__`・ref の class の自前の `__eq__`）。

    登録した実装を持つ値は「信頼する葉」: 組み込みの比較がその実装を呼んでも、戻り値は組み込みの `bool` で、外の
    code の戻り値は実装の中で reader が読む（構築の guard が本体を検査する package の code に限る）。返す関数は包みを
    元の値に戻して実装を呼び、相手が自分の型の subclass の包みなら `NotImplemented`（Python の subclass 優先の規則を
    包みの反射で保つ）。実装が外の code を呼んだ後に `NotImplemented` を返したら判定不能（反射で後に呼ばれる相手の
    実装は、その外の code が書き換えた型のもの: `_require_explicit_ne`）。
    """

    if type(function) is not types.FunctionType or not package_code(function.__code__):
        raise TypeError("a trusted comparison is a package function")

    def comparison(self: Any, other: Any) -> Any:
        if type(other) is _Comparand:
            value = other.value
            kind = type(value)
            if kind is not type(self) and _in_mro(type(self), kind):  # metaclass の `__subclasscheck__` を呼ばない
                # Python は右が左の型の subclass なら右の反射を先に呼ぶ（包みの型ではその規則が働かない）: 包みの反射へ
                # 渡し、元の値どうしの比較（`value == self`）で同じ順にする
                return NotImplemented
            other = value  # 包みでなく元の値と比べる（双子と同じ相手）
        epoch = _FOREIGN_EPOCH.s.count
        result = function(self, other)
        if result is NotImplemented and _FOREIGN_EPOCH.s.count != epoch:
            # 外の code を呼んだ後に断ると、反射で後から呼ばれる相手の実装はその code が書き換えた型のもの（`object.__ne__`
            # の真偽の読みを含む）: 判定しない。登録した比較は外の code を呼ぶ前に断る
            raise undecidable("a registered comparison declined after running foreign code")
        # 実装の中の外の code は比べる側の契約を通って走り、その都度確かめる（`_checked`）。実装を継承した型の中身が外の
        # code なら、その型は登録した比較の分類にならない（`_leaf_trust` の `package_type`）: ここで確かめ直さない（容器の
        # 要素ごとに確かめ直すと比較が要素数の 2 乗になる）
        return result

    comparison.__name__ = function.__name__
    comparison.__qualname__ = function.__qualname__
    comparison.__module__ = function.__module__
    comparison.__doc__ = function.__doc__
    comparison.__wrapped__ = function  # type: ignore[attr-defined]
    _TRUSTED_COMPARISONS.append(comparison)
    return comparison


def trusted_hash(function: Any) -> Any:
    """`__hash__` の実装として登録する（ref の owner の `__hash__`・ref の class の自前の `__hash__`）。登録した比較
    （`trusted_comparison`）と同じ分類（package の比較）: 本体は比べる側の契約（`hash_tree`）で読み、組み込みの `int` を
    返す（構築の guard が本体を検査する package の code に限る）。hash は相手を取らないので包まずにそのまま登録する。"""

    if type(function) is not types.FunctionType or not package_code(function.__code__):
        raise TypeError("a trusted hash is a package function")
    _TRUSTED_HASHES.append(function)
    return function


#: 比較の C の実装が、持っている値の比較（外の code）を呼ばない組み込みの型（`object` の identity・数・bytes・range）
#: （`bytearray` は含めない: その `==` は相手の buffer を読む: 相手の `__buffer__` は Python の code であり得る）
_SELF_CONTAINED = frozenset({object, type, int, str, float, bool, complex, bytes, range, type(None)})
#: 標準 library の module の名前（`sys.stdlib_module_names`、python 3.10 以降）
_STDLIB_MODULES = frozenset(getattr(sys, "stdlib_module_names", ()))
#: 葉の比較の分類（強い順に: 不透明 > 外の code > package の比較 > 不活性）。不活性（`_TRUSTED`）は比べても hash しても
#: Python の code を呼ばない（`object` の identity・自己完結の組み込み）。package の比較（`_CALLS`）は登録した実装で、
#: 中で外の code を呼び得る（ref の field の比較）。分類は **使う時点の** 型の名前空間から決める（外の code は class を
#: 書き換えられる: 外の code の後に前の分類を使わない。`_ComparisonScope`）
_TRUSTED, _CALLS, _FOREIGN, _OPAQUE = "trusted", "calls", "foreign", "opaque"
_TRUST_RANK = {_TRUSTED: 0, _CALLS: 1, _FOREIGN: 2, _OPAQUE: 3}


#: `_dunder_trust` の結果の memo（(`id(実装)`, dunder の名前) → (実装, 分類)。実装の object を生かす: `id` を再利用させない）。
#: 分類は実装の object と、それを置いた dunder の名前で決まる（同じ組み込みの実装も、別の名前の下では別の振る舞い:
#: `__eq__ = object.__getattribute__`。型の名前空間の変化は `_leaf_trust` が毎回引き直す）
_DUNDER_TRUST: Dict[Tuple[int, str], Tuple[Any, str]] = {}


def _dunder_trust(implementation: Any, name: str) -> str:
    """比較の dunder の実装の分類: 信頼する（`object` / 自己完結の組み込み / 登録した実装）・外の code（Python の関数・
    外の拡張の C）・不透明（持っている値を C の中で比べる組み込みの型: `slice`・`mappingproxy` など。中の比較の戻り値を
    C が真偽で読むが、包めない）。"""

    key = (id(implementation), name)
    found = _DUNDER_TRUST.get(key)
    if found is not None:
        return found[1]  # memo が実装を生かしているので、同じ `id` は同じ object
    trust = _classify_dunder(implementation, name)
    if len(_DUNDER_TRUST) >= SCAN_LIMIT:
        _DUNDER_TRUST.clear()
    _DUNDER_TRUST[key] = (implementation, trust)
    return trust


#: Python で書かれた実装のうち、値の状態が条件を満たせば Python の外の code を呼ばない実装と、その条件（値ごとに使う時点で
#: 確かめる: `_leaf_trust`）。`Enum.__hash__` は `hash(self._name_)`: member の名前が組み込みの `str` のときだけ自己完結
#: （名前は instance の状態: 外の code が `str` の subclass に置き換えられる）
_SELF_CONTAINED_FUNCTIONS = (vars(Enum).get("__hash__"),)
#: 条件つきの実装を持ち得る型（分類を型ごとに覚えない: `_ComparisonScope.trust`）
_VALUE_CONDITIONED_BASES = (Enum,)


def _self_contained_for(implementation: Any, value: Any) -> bool:
    """条件つきの自己完結の実装が、この値で自己完結か（hook を呼ばずに読む）。"""

    if implementation is _SELF_CONTAINED_FUNCTIONS[0]:
        # `hash(self._name_)` は普通の属性の読み: 型の MRO（`object` を除く）に `__getattribute__` / `__getattr__` も
        # `_name_`（descriptor）も無く、instance の名前が組み込みの `str` のときだけ自己完結
        mro = _TYPE_MRO.__get__(type(value))
        if not _within_scan(tuple.__len__(mro)):
            return False
        for klass in mro:
            if klass is object:
                break
            reader = _NamespaceReader(klass)
            for name in ("__getattribute__", "__getattr__", "_name_"):
                if reader.value(name) is not _MISSING_DUNDER:
                    return False
        try:
            name = instance_state(value, "_name_", None)
        except TypeError:
            return False
        return name is None or type(name) is str  # `Flag` の合成・0 の member は名前が `None`（`hash(None)` は自己完結）
    return True


def _classify_dunder(implementation: Any, name: str) -> str:
    if implementation is None:
        return _TRUSTED  # `__hash__ = None` など: 呼ぶと C が `TypeError`（Python の code を呼ばない）
    if name == "__hash__":
        if any(implementation is trusted for trusted in _TRUSTED_HASHES):
            return _CALLS
        if any(implementation is known for known in _SELF_CONTAINED_FUNCTIONS if known is not None):
            return _TRUSTED
    elif any(implementation is trusted for trusted in _TRUSTED_COMPARISONS):
        return _CALLS
    holder = type(implementation)
    if holder is types.WrapperDescriptorType or holder is types.MethodDescriptorType:
        owner = implementation.__objclass__
        if any(owner is kind for kind in _SELF_CONTAINED):
            # 自己完結の型の、その名前そのものの実装だけ（別の名前の下の組み込みの実装は別の振る舞い: 属性の読み・
            # 外の protocol を呼ぶ）
            if _TYPE_DICT.__get__(owner).get(name) is implementation:
                return _TRUSTED
            return _FOREIGN
        module = _TYPE_MODULE.__get__(owner)
        top = module.split(".", 1)[0] if type(module) is str else ""
        # interpreter と標準 library の C の比較（`slice`・`mappingproxy`・`SimpleNamespace`・`GenericAlias` など）は、
        # 持っている Python の値を C の中で比べる。外の拡張の C の比較（JPype の Java の `equals` など）は外の code
        return _OPAQUE if top == "builtins" or top in _STDLIB_MODULES else _FOREIGN
    return _FOREIGN


def _leaf_trust(value: Any, names: Tuple[str, ...] = None) -> str:  # type: ignore[assignment]
    """葉の比較の分類（`names` の dunder の分類の最も強いもの）。型の MRO の名前空間を **今** 読む（cache しない）。

    名前空間の読みは hook を呼ばない（`_namespace_value`）。組み込みの `str` でない key がその名前と同じ文字列なら、
    Python の属性の引きが key の `__eq__` を呼ぶ型: 不透明（判定しない）。scalar の subclass は外の code（読みで基底型の
    値にしてから比べる）。
    """

    if names is None:
        names = _HASHING_DUNDERS  # 不活性は比べても hash しても Python の code を呼ばない（`in`・set の引きが hash する）
    kind = type(value)
    if value is None or kind is int or kind is str or kind is bool or kind is float:
        return _TRUSTED
    if issubclass(kind, _SCALAR_BASES) and not issubclass(kind, Enum):
        return _FOREIGN
    mro = _TYPE_MRO.__get__(kind)
    if not _within_scan(len(mro)):
        return _OPAQUE
    # MRO を 1 回辿り、dunder を最初に定義する class の実装を分類する（`object` の実装は不活性: そこで止める）
    trust = _TRUSTED
    pending = names
    for klass in mro:
        if klass is object:
            break
        reader = _NamespaceReader(klass)
        unresolved = []
        for name in pending:
            implementation = reader.value(name)
            if implementation is _MISSING_DUNDER:
                unresolved.append(name)
                continue
            found = _OPAQUE if implementation is _AMBIGUOUS_NAME else _dunder_trust(implementation, name)
            if found == _TRUSTED and not _self_contained_for(implementation, value):
                found = _FOREIGN  # 条件つきの実装: この値では外の code を呼び得る
            if found == _OPAQUE:
                return _OPAQUE
            if _TRUST_RANK[found] > _TRUST_RANK[trust]:
                trust = found
        if not unresolved:
            break
        pending = tuple(unresolved)
    if trust == _CALLS and not package_type(kind):
        # 登録した比較を継承しても、型の中身（field の descriptor・上書きした method）が外の code なら、実装が読む
        # `self.x` / `self.f()` が外の code を呼ぶ: 外の code として包む
        return _FOREIGN
    return trust


def plain_attribute_lookup(kind: type) -> bool:
    """型の MRO（`object` まで）の class が `__getattribute__` / `__getattr__` を名前空間に持たないか（そのときの属性の読みは
    `object.__getattribute__` と同じ）。使うたびに今の名前空間を読む（後から足した hook も見る）。hook を呼ばない。

    確かめた名前空間（`_STR_KEYED_NAMESPACES`: key が全部組み込みの `str` のまま）は storage の dict を組み込みの `str` の
    名前で直接引く（key の hook を呼ばない・O(1)）。そうでない class は `class_defines`（組み込みでない key は決めない）。
    """

    mro = _TYPE_MRO.__get__(kind)
    if not _within_scan(tuple.__len__(mro)):
        return False
    for klass in mro:
        if klass is object:
            return True
        known = _STR_KEYED_NAMESPACES.get(id(klass))
        if known is not None and known[0] is klass:
            raw = known[1]
            if "__getattribute__" in raw or "__getattr__" in raw:
                return False
            continue
        found = class_defines(klass, "__getattribute__", "__getattr__")
        if found is None or found:
            return False  # 組み込みでない key（決めない）か、`object` でない class の hook
    return True


def class_defines(klass: type, *names: str) -> Optional[bool]:
    """class の名前空間（その class だけ。MRO は辿らない）に `names` のどれかがあるか。組み込みの `str` でない key が
    あれば `None`（Python の引きが hash の等しい key の `__eq__` を呼ぶ: 決めない）。名前空間を使うたびに読み（1 度の走査）、
    key の hook を呼ばない。"""

    reader = _NamespaceReader(klass)
    defined = False
    for name in names:
        found = reader.value(name)
        if found is _AMBIGUOUS_NAME:
            return None
        if found is not _MISSING_DUNDER:
            defined = True
    return defined


#: 名前空間に組み込みの `str` でない key がある印（引きが hash の等しい key の `__eq__` を key の文字列に依らず呼ぶ）
_AMBIGUOUS_NAME = object()


class _NamespaceReader:
    """1 つの class の名前空間を、今の状態で何度か引く読み手（key が全部組み込みの `str` かの確かめは 1 度）。

    作ってから外の code を呼ばない間だけ使う（1 回の分類の中）。引きは `_namespace_value` と同じ規則。
    """

    __slots__ = ("raw", "plain", "static")

    def __init__(self, klass: type) -> None:
        namespace = _TYPE_DICT.__get__(klass)
        self.static = not _TYPE_FLAGS.__get__(klass) & _HEAP_TYPE
        if self.static:
            self.raw = namespace
            self.plain = True
            if _STATIC_NAMESPACES.get(id(klass)) is None and len(_STATIC_NAMESPACES) < _TYPE_FACTS_LIMIT:
                _STATIC_NAMESPACES[id(klass)] = (klass, _unwrapped(namespace))
            return
        _note_read(klass)
        known = _STR_KEYED_NAMESPACES.get(id(klass))
        if known is not None and known[0] is klass:
            # 前に確かめた名前空間: key は組み込みの `str` のまま（`_STR_KEYED_NAMESPACES`）。型の名前空間の storage は
            # class が生きている間同じ dict
            self.raw = known[1]
            self.plain = True
            return
        raw = _unwrapped(namespace)
        self.raw = raw
        self.plain = _within_scan(dict.__len__(raw)) and _exact_str_raw(raw)
        if self.plain:
            if len(_STR_KEYED_NAMESPACES) >= _TYPE_FACTS_LIMIT:
                _STR_KEYED_NAMESPACES.clear()
            _STR_KEYED_NAMESPACES[id(klass)] = (klass, raw)

    def value(self, name: str) -> Any:
        if self.static:
            return self.raw.get(name, _MISSING_DUNDER)
        if self.plain:
            return dict.get(self.raw, name, _MISSING_DUNDER)
        # 組み込みの `str` でない key（`str` の subclass に限らない）が 1 つでもあれば、どの名前の引きも決めない:
        # Python の引きは hash の等しい key の `__eq__` を **key の文字列に依らず** 呼び、key の hash は
        # その key の code が決める（hook を呼ばずに読めない）
        return _AMBIGUOUS_NAME


#: key が全部組み込みの `str` だと確かめた heap type の名前空間（`id(class)` → (class, storage)。class を生かす: `id` を
#: 再利用させない。型の名前空間の storage は class が生きている間同じ dict）。確かめた後も key は組み込みの `str` のまま: class の名前空間の書き換え（`setattr` /
#: `type.__setattr__` / `delattr`）は名前を組み込みの `str` にしてから置く（CPython 3.10 / 3.12 で確かめる test:
#: `test_issue242_assumptions`）。組み込みでない key は class を作るときにだけ入る。storage への直接の書き込み
#: （`gc.get_referents` で得た dict を書く）は前提の外（code の書き換えと同じ: 型の cache も壊す操作）
_STR_KEYED_NAMESPACES: Dict[int, Tuple[type, dict]] = {}
#: 組み込みの型（heap type でない）の名前空間の storage（`id(class)` → (class, storage)。class を生かす）。組み込みの型の
#: 名前空間は書き換えられない（`type.__setattr__` が拒む）・key は組み込みの `str`: `_type_lookup` が直接引く
_STATIC_NAMESPACES: Dict[int, Tuple[type, dict]] = {}


def _namespace_value(klass: type, name: str) -> Any:
    """class の名前空間（`__dict__` の storage）の `name` の値。無ければ `_MISSING_DUNDER`。**hook を呼ばない**。

    組み込みの型（heap type でない）の名前空間は変わらず、key は組み込みの `str`: そのまま引く。heap type は使うたびに
    key が全部組み込みの `str` かを C の反復で確かめてから引く（`str` の subclass の key があると、hash の等しい key の
    `__eq__` を、key の文字列に依らず dict の引きが呼ぶ）。そうでなければどの名前も `_AMBIGUOUS_NAME`。
    """

    return _NamespaceReader(klass).value(name)


class _Comparand:
    """比べる値の葉（exact な scalar でない葉）の包み: 組み込みの比較がこの dunder を呼ぶと、元の値どうしを Python の
    比較の手順（反射・subclass 優先を含む）で比べ、戻り値を `truth` で読む。

    分類は **呼ばれた時点で** 読む（`_ComparisonScope.trust`: 前の外の code が class を書き換えていても、今の実装で
    比べる）。どちらかが不透明（持っている値を C の中で比べる組み込みの型）なら判定しない。外の code の後は、比べて
    いる値の変わる容器が変わっていないことを確かめる（`_checked`）。hash は元の値の hash（C が基底型の値で読む）。
    """

    __slots__ = ("value", "scope")

    def __init__(self, value: Any, scope: "_ComparisonScope") -> None:
        self.value = value
        self.scope = scope

    def _other(self, other: Any) -> Any:
        """相手の元の値（包みは元の値、この比較が作った写しの容器は写す前の容器: 外の code に写しを渡さない）。"""

        if type(other) is _Comparand:
            return other.value
        found = self.scope.origins.get(id(other))
        if found is None or found[0] is not other:
            return other
        if found[1] is _READ_COPY:
            return _READ_COPY  # 写す前の容器が無い（`exact_tree` の写し）: 渡してよいかは `_operands` が決める
        return found[1]

    def _operands(self, other: Any) -> Tuple[Any, Any, bool]:
        other_value = self._other(other)
        scope = self.scope
        trust = scope.trust(self.value)
        if other_value is _READ_COPY:
            if trust == _FOREIGN:
                # `exact_tree` が写した容器（scalar の subclass の葉を読んだ）: 双子の容器と別の object を外の code に
                # 渡すことになる。呼ぶ前に判定しない（ここまでの外の code の呼び出しは双子の先頭）
                raise undecidable("a foreign callback would receive a read copy instead of the twin's container")
            # 不活性な比較・登録した比較は相手の容器を外の code に渡さない（型の違う相手は `NotImplemented`）
            other_value = other
        other_trust = scope.trust(other_value)
        if trust == _OPAQUE or other_trust == _OPAQUE:
            raise undecidable("a value that compares what it holds inside builtin code is compared")
        return self.value, other_value, trust == _FOREIGN or other_trust == _FOREIGN

    def __eq__(self, other: Any) -> bool:
        x, y, foreign = self._operands(other)
        return _checked(truth(_compare(foreign, operator.eq, x, y)))

    def __ne__(self, other: Any) -> bool:
        x, y, foreign = self._operands(other)
        _require_explicit_ne(x, y)
        return _checked(truth(_compare(foreign, operator.ne, x, y)))

    def __lt__(self, other: Any) -> bool:
        x, y, foreign = self._operands(other)
        return _checked(truth(_compare(foreign, operator.lt, x, y)))

    def __le__(self, other: Any) -> bool:
        x, y, foreign = self._operands(other)
        return _checked(truth(_compare(foreign, operator.le, x, y)))

    def __gt__(self, other: Any) -> bool:
        x, y, foreign = self._operands(other)
        return _checked(truth(_compare(foreign, operator.gt, x, y)))

    def __ge__(self, other: Any) -> bool:
        x, y, foreign = self._operands(other)
        return _checked(truth(_compare(foreign, operator.ge, x, y)))

    def __hash__(self) -> int:
        _require_named_lookup(self.value, "__hash__")
        if self.scope.trust(self.value) == _FOREIGN:
            with outside_audit():
                return _checked(hash(self.value))
        return _checked(hash(self.value))


def _require_explicit_ne(left: Any, right: Any) -> None:
    """葉どうしの `!=` が、外の `__eq__` の戻り値の真偽を C の中で読まないこと。

    `__ne__` を MRO のどこにも持たない（または `object.__ne__` そのものを置いた）型の `!=` は `object.__ne__`: 型の
    `__eq__` を呼び、その戻り値を C が真偽で読んで反転する（`truth` で包めない）。判定しない場面:

    - その `__eq__` が外の code（戻り値が値を偽る scalar の subclass かもしれない）。
    - もう一方の葉の比較が外の code: 同じ `!=` の中で先に呼ばれた外の code が、反射で後から呼ばれる `object.__ne__` の
      型に外の `__eq__` を足して `NotImplemented` を返せる（呼ぶ前の分類は、呼ばれた時点の型を表さない）。登録した比較は
      外の code を呼んだ後に `NotImplemented` を返さない（`trusted_comparison` が判定不能にする）ので数えない。

    `==` の比較はこの規則に当たらない（戻り値は `truth` が読む）。容器は要素を `==` で比べる。"""

    implicit = []
    active = []
    for value in (left, right):
        kind = type(value)
        if value is None or kind is int or kind is str or kind is bool or kind is float:
            implicit.append(False)
            active.append(False)
            continue
        if _kind_entry(kind)[1] is not None:
            implicit.append(False)  # 容器: 要素は `==` で比べる（戻り値は包みの `truth` が読む）
            active.append(False)
            continue
        ne_trust = _leaf_trust(value, ("__ne__",))
        if ne_trust == _OPAQUE:
            raise undecidable(f"{type_name(kind)} compares what it holds inside builtin code")
        eq_trust = _leaf_trust(value, ("__eq__",))
        resolved = _resolved_comparison(kind, "__ne__")
        derived = resolved is _MISSING_DUNDER or resolved is _OBJECT_NE
        if derived and _TRUST_RANK[eq_trust] > _TRUST_RANK[_CALLS]:
            raise undecidable(f"{type_name(kind)} derives != from a foreign __eq__ inside builtin code")
        implicit.append(derived)
        active.append(_TRUST_RANK[max(ne_trust, eq_trust, key=_TRUST_RANK.__getitem__)] > _TRUST_RANK[_CALLS])
    if (implicit[0] and active[1]) or (implicit[1] and active[0]):
        raise undecidable("a != derived inside builtin code may run after foreign code changed its type")


#: `object` の `!=` の実装（`__eq__` の戻り値を C が真偽で読んで反転する）
_OBJECT_NE = object.__dict__["__ne__"]


def _resolved_comparison(kind: type, name: str) -> Any:
    """型の MRO（`object` を除く）の名前空間で最初に見つかる `name` の実装（無ければ `_MISSING_DUNDER`。hook を呼ばない。
    組み込みでない key の名前空間は `TypeError` の代わりに判定不能）。"""

    mro = _TYPE_MRO.__get__(kind)
    if not _within_scan(tuple.__len__(mro)):
        raise undecidable("a type with a long MRO is not compared")
    for klass in mro:
        if klass is object:
            break
        found = _NamespaceReader(klass).value(name)
        if found is _AMBIGUOUS_NAME:
            raise undecidable(f"a class namespace holds a key that is not a builtin str (looking up {name!r})")
        if found is not _MISSING_DUNDER:
            return found
    return _MISSING_DUNDER


def _require_named_lookup(value: Any, name: str) -> None:
    """Python 自身が `value` の型の `name` を名前で引いてよいか（引きが名前空間の key の hook を呼ばないか）。そうで
    なければ判定不能（組み込みの `str` でない key の `__eq__` を Python の引きが呼ぶ）。"""

    kind = type(value)
    if value is None or kind is int or kind is str or kind is bool or kind is float:
        return
    try:
        _type_lookup(kind, name, None)
    except TypeError:
        raise undecidable(f"the type's {name} is looked up through a namespace key that runs code") from None


class _Reliance:
    """thread ごとの、外の code の区間を抜けた回数（`outside_audit` だけが数える: 外の code は区間でだけ走る）と、今走っている
    監査済みの code が頼る事実（`active`: activation の stack。activation は (値, 型) の list）と、`package_instance` の
    型の確かめの記録（`trusted`: `id(型)` → (型, 数)。activation の stack が空になれば捨てる: 監査済みの code の外では
    外の code の区間を通らずに class を書き換えられる）。分類の memo・止まっている監査済みの code は、数が変わると
    確かめ直す。thread ごとの object を 1 度引いて使う（属性は普通の slot: hot path で thread local を何度も引かない）。"""

    __slots__ = ("count", "active", "trusted", "walks")

    def __init__(self) -> None:
        self.count = 0
        self.active: List[List[Tuple[Any, type]]] = []
        self.trusted: Dict[int, Tuple[type, int]] = {}
        #: 走っている walk（`json_encoding._Walk`: `recheck()` で積んでいる frame の receiver を確かめ直す）
        self.walks: List[Any] = []


class _ForeignEpoch(threading.local):
    """thread ごとの `_Reliance`（`.s`）。"""

    def __init__(self) -> None:
        self.s = _Reliance()


_FOREIGN_EPOCH = _ForeignEpoch()


# ---------------------------------------------------------------------------
# 監査済みの区間（第 10 回）: 区間の記録の所有と、区間の外の code の間の切り替えの唯一の owner
# ---------------------------------------------------------------------------
#
# 区間（`audited_region`）の中で走るのは owner の code と、J19 の監査（`tests/unit/_live_flow_audit.py`）が live な値に
# 許した操作だけをする package の code。その code が live な値を渡す owner の関数は、値の code を呼ばない関数か、区間を
# 外す境界（`value_code_boundary`）だけ（`test_issue242_audited_regions` が監査の結果と突き合わせる）。だから区間の
# 間は外の code が走らず、class は変わらない: 区間の記録（`region_cache`）を区間の間使ってよい。
#
# 区間の外の code（identity key の method・宣言していない package の generator）は、走る間ずっと区間の外
# （`outside_audit`: 区間が無い）。その中から API に入り直せば、記録の無い状態で判定する（入り直した API が開く区間は
# その中だけのもの）。外の code から戻れば（例外・generator の中断を含む）元の区間に戻り、記録を捨てる（外の code は
# class を書き換えたかもしれない）。記録の持ち主は区間（最も外の `audited_region` が作り、閉じると捨てる）。

#: 今の監査済みの区間の記録（slot → dict。区間の外・区間の外の code の間は `None`）
_REGION: "contextvars.ContextVar[Optional[Dict[Any, dict]]]" = contextvars.ContextVar(
    "live_values_audited_region", default=None,
)


class audited_region:
    """監査済みの区間を開く（入れ子は外の区間を使う）。開けてよいのは walk と J19 の監査の entry root の本体だけ
    （`test_issue242_assumptions` の static test が場所を固定する）。"""

    __slots__ = ("token",)

    def __enter__(self) -> "audited_region":
        self.token = _REGION.set({}) if _REGION.get() is None else None
        return self

    def __exit__(self, *exc: Any) -> None:
        if self.token is not None:
            _REGION.reset(self.token)


class outside_audit:
    """外の code（監査の外の code: identity key の method・宣言していない package の generator・値の code を呼ぶ境界・
    比べる側の契約が呼ぶ外の比較と hash）を走らせる区間。外の code が走るのはこの区間の中だけ（唯一の境界）。

    走る間は監査済みの区間を外す（区間の記録を見せない）。抜けるとき（例外・generator の中断でも）は、外の code が
    class・値の型を書き換えたかもしれないので: 元の区間に戻して記録を全部捨て、外の code の回数を数え、今走っている
    監査済みの code が頼る事実（`_FOREIGN_EPOCH.s.active`: walker の receiver・`package_instance` の絞り込み）を確かめ
    直す。落ちれば、頼った型の code を呼ぶ前に判定不能（監査済みの code はそのまま続けない）。止まっている監査済みの
    code（walker の frame の generator）も、走っている walk（`_Reliance.walks`）の frame の receiver をここで確かめる。"""

    __slots__ = ("token", "region")

    def __enter__(self) -> "outside_audit":
        self.region = _REGION.get()
        self.token = _REGION.set(None)
        return self

    def __exit__(self, *exc: Any) -> None:
        _REGION.reset(self.token)
        region = self.region
        if region:
            # 外の code は class を書き換えたかもしれない: 区間の記録は全部捨てる（slot の dict を持つ読み手にも見せない）
            for cache in region.values():
                cache.clear()
            region.clear()
        state = _FOREIGN_EPOCH.s
        state.count += 1
        if state.active:
            _recheck_reliance(state)


#: activation の (値, 型) の値の欄が「型だけに頼る」ことを表す印
_NO_RECEIVER = object()


def _recheck_reliance(state: "_Reliance") -> None:
    """外の code の後: 走っている監査済みの code が頼る事実（値の型がまだその型で、その型がまだ package の型）を確かめる。
    落ちれば判定不能（記録してから投げる）。型の確かめは型ごとに 1 回（`package_type` の記録の確かめ）。"""

    seen: Dict[int, type] = {}
    for activation in state.active:
        if not activation:
            continue
        # 値の型は C の反復で比べる（1 つの値につき Python の frame を作らない）。型の確かめは型ごとに 1 回
        if not all(map(_IS, map(type, map(_FIRST, activation)), map(_SECOND, activation))):
            raise undecidable("a value audited code relies on changed its class in foreign code")
        seen.update(zip(map(id, map(_SECOND, activation)), map(_SECOND, activation)))
    for kind in seen.values():
        if not package_type(kind):
            raise undecidable(f"{type_name(kind)}, which audited code relies on, was changed by foreign code")
    if state.walks:
        for walk in state.walks:
            walk.recheck(seen)  # walk の frame の receiver（止まっている generator を含む）。確かめた型は確かめ直さない
    trusted = state.trusted
    count = state.count
    for kind in seen.values():
        trusted[id(kind)] = (kind, count)  # 確かめた型: 次の絞り込み・型の信頼の判定は確かめ直さない（数が同じ間）


_FIRST = operator.itemgetter(0)
_SECOND = operator.itemgetter(1)


def reliance() -> "_Reliance":
    """今の thread の、外の code の回数（`.count`）と、監査済みの code が頼る事実の stack（`.active`）。walker の
    hot path が 1 度だけ引いて使う（owner の API: 監査済みの code を走らせる owner だけが activation を積む）。"""

    return _FOREIGN_EPOCH.s


class relying_on:
    """監査済みの code（package の code）を 1 回走らせる間の activation。`value` を渡せば、その値と型（`kind`、省けば
    `type(value)`）に頼ることを記録する（呼ぶ側は呼ぶ前に型を確かめ済み）。中の `package_instance` の絞り込みも
    この activation に入る。抜ければ捨てる（中断した generator の絞り込みは再開の後に使わない: J19 の規則）。"""

    __slots__ = ("activation",)

    def __init__(self, value: Any = _NO_RECEIVER, kind: Optional[type] = None) -> None:
        self.activation = [] if value is _NO_RECEIVER else [(value, type(value) if kind is None else kind)]

    def __enter__(self) -> "relying_on":
        _FOREIGN_EPOCH.s.active.append(self.activation)
        return self

    def __exit__(self, *exc: Any) -> None:
        end_activation(_FOREIGN_EPOCH.s)


def begin_activation(receiver: Any = _NO_RECEIVER, kind: Optional[type] = None) -> "_Reliance":
    """activation を 1 つ積む（`relying_on` の hot path 版: 呼ぶ側が `end_activation(state)` を finally で呼ぶ）。"""

    state = _FOREIGN_EPOCH.s
    state.active.append([] if receiver is _NO_RECEIVER else [(receiver, type(receiver) if kind is None else kind)])
    return state


def end_activation(state: "_Reliance") -> None:
    """activation を 1 つ降ろす（唯一の降ろし方）。stack が空になれば `package_instance` の型の確かめの記録を捨てる。"""

    active = state.active
    active.pop()
    if not active:
        state.trusted.clear()


def begin_reliance(receiver: Any, kind: type) -> Tuple[Any, Any]:
    """監査済みの code が `receiver`（型 `kind`）に頼り始める（`end_reliance(token)` を finally で呼ぶ）。activation が既に
    あれば今の activation に記録し、終わりにその位置から後ろを捨てる（間の絞り込みも、頼る間だけのもの）。無ければ
    activation を 1 つ積む。外の code の区間の出口で確かめ直す対象になる点は `begin_activation` と同じ（短い呼び出しを
    1 件ごとに積み降ろししない hot path 版）。"""

    state = _FOREIGN_EPOCH.s
    active = state.active
    if active:
        top = active[-1]
        mark = len(top)
        top.append((receiver, kind))
        return top, mark
    active.append([(receiver, kind)])
    return None, state


def end_reliance(token: Tuple[Any, Any]) -> None:
    """`begin_reliance` の終わり（唯一の終わり方）。"""

    top, mark = token
    if top is None:
        end_activation(mark)
    else:
        del top[mark:]


def audited_entry(function: Any) -> Any:
    """J19 の監査の entry root（`tests/unit/_live_flow_audit.ENTRY_ROOTS`）を宣言する: 呼ぶ間 activation を積む（中の
    `package_instance` の絞り込みを、外の code の後に確かめ直す対象にする）。宣言した関数と `ENTRY_ROOTS` が同じ集合で
    あることは `test_issue242_continuations` が確かめる。"""

    @functools.wraps(function)
    def entry(*args: Any, **kwargs: Any) -> Any:
        state = _FOREIGN_EPOCH.s
        state.active.append([])
        try:
            return function(*args, **kwargs)
        finally:
            end_activation(state)

    entry.__audited_entry__ = True
    return entry


def read_pair(value: Any) -> Tuple[Any, Any]:
    """組（(key, 値)）の読み: 組み込みの tuple / list（subclass を含む）を基底型の slot で読む（Issue #242 第 11 回）。

    読み方: 長さと要素は `tuple` / `list` の slot（`__len__` / `__getitem__`）で読む。subclass の `__iter__` /
    `__getitem__` / `__len__`（unpack・添字が呼ぶ）を呼ばない: 読んだ値は基底の tuple の双子と同じ。exact な tuple は
    そのまま返す（呼ぶ側の unpack は組み込みの tuple の速い経路で、Python の code を呼ばない）。
    返す値の保証: 組み込みの tuple（長さ 2）。組み込みの tuple / list でない値は `TypeError`、長さが 2 でない組は
    `ValueError`（unpack と同じ種類）: どちらも値の code を呼ぶ前。"""

    kind = type(value)
    if kind is tuple:
        if tuple.__len__(value) != 2:
            raise ValueError(f"a pair has 2 items, not {tuple.__len__(value)}")
        return value
    if issubclass(kind, tuple):
        size, item = tuple.__len__, tuple.__getitem__
    elif issubclass(kind, list):
        size, item = list.__len__, list.__getitem__
    else:
        raise TypeError(f"a pair is a builtin tuple or list, not {type_name(kind)}")
    if size(value) != 2:
        raise ValueError(f"a pair has 2 items, not {size(value)}")
    return item(value, 0), item(value, 1)


def package_instance(value: Any, kind: type) -> bool:
    """`type(value) is kind` で、監査済みの code の中（activation がある）なら `kind` が今 package の型（`package_type`）か。
    監査済みの code が値を package の型へ絞り込む唯一の判定（J19 の監査は `type(x) is C` を絞り込みに数えない）: 絞り込んだ値の field・method を使ってよいのは、
    次に外の code が走るまで（外の code から戻るときに確かめ直す: 今の activation に記録する）と、generator なら次の
    `yield` まで（J19 の規則）。`kind` が package の型でなくなっていれば判定不能（その型の code を呼ぶ前に止める）。"""

    if type(value) is not kind:
        return False
    state = _FOREIGN_EPOCH.s
    active = state.active
    if active:
        # 監査済みの code の間（activation がある）は、外の code は外の code の区間でだけ走り、区間を抜けると数が変わる:
        # 型の確かめは、数が同じ間は使い回す（activation の stack が空になれば捨てる: `end_activation`）
        known = state.trusted.get(id(kind))
        if known is None or known[0] is not kind or known[1] != state.count:
            if not package_type(kind):
                raise undecidable(f"{type_name(kind)} is relied on by audited code but is not a package type now")
            state.trusted[id(kind)] = (kind, state.count)
        activation = active[-1]
        if not activation or activation[-1][0] is not value:  # 続けて同じ値を絞り込む形（loop の中）は 1 度だけ
            activation.append((value, kind))
        return True
    # 監査済みの code の外（activation が無い: walk・`audited_entry`・owner が呼ぶ root の外。analysis の code が同じ関数を
    # 呼ぶとき）: 契約の外なので型の identity だけ（監査済みの code が走るときは必ず activation がある）
    return True


def region_cache(slot: Any) -> Optional[dict]:
    """今の区間の、`slot`（記録の持ち主が持つ object）ごとの記録（区間の外・区間の外の code の間は `None`）。"""

    region = _REGION.get()
    if region is None:
        return None
    cache = region.get(slot)
    if cache is None:
        cache = region[slot] = {}
    return cache


#: 区間を外す境界（`value_code_boundary` で宣言した owner の関数）。J19 の監査が辿る code が live な値を渡してよい owner
#: の関数のうち、値の code（監査の外の code）を呼ぶもの: その呼び出しは関数の中で `outside_audit` の下だけ（本体が
#: `outside_audit` を使うことは static test が確かめる。区間の記録を使う部分は区間の中に残せる）
VALUE_CODE_BOUNDARIES: List[Any] = []


def value_code_boundary(function: Any) -> Any:
    """`function` を、値の code を `outside_audit` の下でだけ呼ぶ owner の関数として宣言する（包まない）。"""

    VALUE_CODE_BOUNDARIES.append(function)
    return function


class _ComparisonScope:
    """1 回の比較の包みが共有する状態: 写しの元（`origins`）と、葉の型の分類の memo。

    memo は、作ってから外の code が呼ばれていない間だけ使う（`_FOREIGN_EPOCH`）: 外の code は class の名前空間・
    instance の `__class__` を書き換えられる。memo は型を生かす（`id` を再利用させない）。組み込みの容器そのものは
    不活性（比べる相手として外の code に渡るだけ）。
    """

    __slots__ = ("origins", "memo", "epoch")

    def __init__(self) -> None:
        self.origins: Dict[int, Tuple[Any, Any]] = {}
        self.memo: Dict[int, Tuple[type, str]] = {}
        self.epoch = _FOREIGN_EPOCH.s.count

    def trust(self, value: Any) -> str:
        kind = type(value)
        if (
            value is None or kind is int or kind is str or kind is bool or kind is float
            or kind is tuple or kind is list or kind is dict or kind is set or kind is frozenset
        ):
            return _TRUSTED
        if self.epoch != _FOREIGN_EPOCH.s.count:
            self.memo.clear()
            self.epoch = _FOREIGN_EPOCH.s.count
        if issubclass(kind, _VALUE_CONDITIONED_BASES):
            return _leaf_trust(value)  # 分類が値の状態に依る: 型ごとに覚えない
        found = self.memo.get(id(kind))
        if found is not None and found[0] is kind:
            return found[1]
        trust = _leaf_trust(value)
        self.memo[id(kind)] = (kind, trust)
        return trust


class _CopyFrame:
    """1 つの比較が確かめる状態: 写した変わる容器（list / dict / set とその subclass）の中身と、組み込みの code が包まずに
    比べる値（hash で置く位置の要素・key）の型と型の状態。

    外の code が呼ばれるたびに確かめる（`_checked`）: 容器が変わる・包まない値の `__class__` や型の名前空間が変わると、
    組み込みの code が読む写し・分類が双子と食い違う（判定不能）。容器の確かめは種類ごとに C の反復で中身の `id` の列と
    長さの列を作って比べる（長さの列が要るのは、容器の間で要素が移っても `id` の連結が変わらないため）。確かめ始めの
    中身は生かす（`id` を再利用させない）。
    """

    __slots__ = ("lists", "dicts", "sets", "snapshot", "held", "members", "member_types", "type_states")

    def __init__(self, containers: List[Any], members: List[Any] = ()) -> None:  # type: ignore[assignment]
        _admit_storage(len(containers), _COMPARISON_NODES, traversal=True)
        self.lists = [c for c in containers if issubclass(type(c), list)]
        self.dicts = [c for c in containers if issubclass(type(c), dict)]
        self.sets = [c for c in containers if issubclass(type(c), set)]
        self.snapshot = self._read()
        # 確かめ始めのときの中身を生かす: 外の code が要素を外して捨てても、その `id` を別の object が再利用しない
        self.held = (
            list(itertools.chain.from_iterable(map(list.__iter__, self.lists))),
            list(itertools.chain.from_iterable(itertools.chain.from_iterable(map(dict.items, self.dicts)))),
            list(itertools.chain.from_iterable(map(set.__iter__, self.sets))),
        )
        self.members = list(members)
        self.member_types = tuple(map(type, self.members))
        kinds = {id(kind): kind for kind in self.member_types}
        snapshots = [_class_snapshot(kind) for kind in kinds.values()]
        self.type_states = [None if snapshot is None else _state_check(snapshot) for snapshot in snapshots]

    def _read(self) -> Tuple[Any, ...]:
        lengths = (
            tuple(map(list.__len__, self.lists)), tuple(map(dict.__len__, self.dicts)), tuple(map(set.__len__, self.sets))
        )
        _admit_storage(sum(lengths[0]) + 2 * sum(lengths[1]) + sum(lengths[2]), _COMPARISON_NODES, traversal=True)
        return lengths + (
            tuple(map(id, itertools.chain.from_iterable(map(list.__iter__, self.lists)))),
            tuple(map(id, itertools.chain.from_iterable(itertools.chain.from_iterable(map(dict.items, self.dicts))))),
            tuple(map(id, itertools.chain.from_iterable(map(set.__iter__, self.sets)))),
        )

    def unchanged(self) -> bool:
        _admit_storage(len(self.members), _COMPARISON_NODES, traversal=True)
        if self._read() != self.snapshot:
            return False
        if self.members and not all(map(_IS, map(type, self.members), self.member_types)):
            return False  # 包まない値の `__class__` が変わった
        return all(check is not None and _state_holds(check) for check in self.type_states)


class _CopyFrames(threading.local):
    """thread ごとの、進行中の比較の `_CopyFrame` の stack（入れ子の比較: ref の `__eq__` の中の比較）。"""

    def __init__(self) -> None:
        self.stack: List[_CopyFrame] = []


_COPY_FRAMES = _CopyFrames()


def _compare(foreign: bool, operation: Any, left: Any, right: Any) -> Any:
    """比較 1 つ（`operation(left, right)`）。外の code で比べる葉があれば外の code の区間で走らせる（`outside_audit`:
    区間の記録を見せず、戻るときに監査済みの code が頼る事実を確かめ直す）。"""

    if foreign:
        state = _FOREIGN_EPOCH.s
        if state.active or _REGION.get() is not None:
            with outside_audit():
                return operation(left, right)
        # 監査済みの code の外（区間も activation も無い）: 隠す記録も確かめ直す事実も無い。外の code の回数だけ数える
        try:
            return operation(left, right)
        finally:
            state.count += 1
    return operation(left, right)


def _checked(result: Any) -> Any:
    """外の code の直後: 進行中の比較（入れ子を含む全部）の元の容器が変わっていれば判定不能。変わっていなければ
    `result`。外の code の呼び出しの中だけの変化（呼び出しが返る前に戻した変化）は組み込みの比較から見えない（双子も同じ）。"""

    stack = _COPY_FRAMES.stack
    _admit_storage(len(stack), _COMPARISON_NODES, traversal=True)  # 入れ子の比較の数（Python の再帰の上限まで）
    if stack and not all([frame.unchanged() for frame in stack]):
        raise undecidable("a foreign callback changed a compared container")
    return result


def _guarded(frame: Optional[_CopyFrame], operation: Any) -> Any:
    """`operation()` を `frame` を進行中にして行い、終わりで元の容器が変わっていないことを確かめる。"""

    if frame is None:
        return operation()
    stack = _COPY_FRAMES.stack
    stack.append(frame)
    try:
        result = operation()
    finally:
        stack.pop()
    if not frame.unchanged():
        raise undecidable("a foreign callback changed a compared container")
    return result


def _covered(values: Tuple[Any, ...]) -> Tuple[Tuple[Any, ...], Optional[_CopyFrame], Tuple[Any, ...]]:
    """比べる値（の組）を 1 回の読みで写し、葉を `_Comparand` で包んだ木と、写しの有効性を確かめる frame（元に変わる
    容器が無ければ `None`）と、読んだ木。

    包む葉: 葉のどれかが比べるときに Python の code を呼び得る（外の code・package の比較・不透明）なら、exact な
    scalar でない葉を **全部** 包む（外の code が後の葉の class を書き換えても、包みが呼ばれた時点の分類で比べる）。
    そうでなければ包まない（比べても Python の code を呼ばない: class は変わらない）。共有された葉・容器は 1 度だけ
    写して包む（identity の規則が双子と同じ）。list・dict の値の中の包みは容器を写す（dict は key が不活性なときだけ）。
    写しは写す前の容器を覚え、包みが外の code を呼ぶときは写す前の容器を渡す。

    `UndecidableComparison`: hash で置く位置（set / frozenset の要素・dict の key）に、比較の途中で class が書き換わり
    得る値（比較の dunder が不活性でも登録した実装でもない値: `_hashed_members`）がある、閉路、比べ方が読む基底型と違う容器（`_comparison_shape`）、読めない値。
    `exact_tree` が写した容器を外の code に渡すときも判定しない（`_Comparand._other`）。辿る量は `exact_tree` と同じ
    反復の確かめ。
    """

    root = _compared_tree(values)
    shape: List[Any] = []
    original_ids: set = set()
    # 包まずに組み込みの code が比べる値（hash で置く位置）と、読んだ木が基底型の値で比べる容器の subclass の元: 比べて
    # いる間、型・`__class__`・型の名前空間が変わらないことを確かめる（変われば双子の比べ方と食い違う）
    members: List[Any] = []
    if root is not values:
        shape, original_ids, members = _comparison_shape(values)
    scope = _ComparisonScope()
    wrap = _strongest_trust(root, scope) != _TRUSTED
    read = _StorageRead(_COMPARISON_NODES, traversal=True)
    origins = scope.origins  # id(写し) → (写し, 写す前の容器)
    done: Dict[int, Any] = {}
    entered: set = set()  # 辿っている途中の容器（閉路の検出）
    alive: List[Any] = [root]
    mutable: List[Any] = []
    stack: List[Tuple[Any, bool]] = [(root, False)]
    while stack:
        node, leaving = stack.pop()
        kind = type(node)
        if leaving:
            entered.discard(id(node))
            if kind is dict:
                pairs = list(dict.items(node))
                if any(done.get(id(value), value) is not value for _key, value in pairs):
                    copy: Any = {key: done.get(id(value), value) for key, value in pairs}
                    done[id(node)] = copy
                    origins[id(copy)] = (copy, _source(origins, node))
                continue
            items = list(kind.__iter__(node))
            rebuilt = [done.get(id(item), item) for item in items]
            if any(new is not old for new, old in zip(rebuilt, items)):
                copy = tuple(rebuilt) if kind is tuple else rebuilt
                done[id(node)] = copy
                origins[id(copy)] = (copy, _source(origins, node))
            continue
        if id(node) in entered:
            # 閉路の容器: 写しが元へ戻る（包まない葉を組み込みの比較が読む）。双子も再帰の上限まで比べる: 判定しない
            raise undecidable("a cyclic container is not compared")
        if id(node) in done:
            continue
        if node is None or kind is int or kind is str or kind is bool or kind is float:
            continue
        if kind is tuple or kind is list:
            done[id(node)] = node  # 入った印
            entered.add(id(node))
            alive.append(node)
            if node is not root and id(node) not in original_ids and original_ids:
                origins[id(node)] = (node, _READ_COPY)
            if kind is list:
                mutable.append(node)
            read.admit(kind.__len__(node))
            stack.append((node, True))
            stack.extend((item, False) for item in kind.__iter__(node))
            continue
        if kind is dict:
            done[id(node)] = node
            alive.append(node)
            if original_ids and id(node) not in original_ids:
                origins[id(node)] = (node, _READ_COPY)
            mutable.append(node)
            keys = list(dict.keys(node))
            read.admit(len(keys))
            if wrap:
                for key in keys:
                    _hashed_members(key, scope, members, mutable)
            if not all(inert(key) for key in keys):
                # key を写し直すと key の hash・比較を双子に無い時点で呼ぶ: 写さない（値も包めない）
                if wrap:
                    for value in dict.values(node):
                        _hashed_members(value, scope, members, mutable)
                continue
            entered.add(id(node))
            stack.append((node, True))
            stack.extend((value, False) for value in dict.values(node))
            continue
        if kind is set or kind is frozenset:
            done[id(node)] = node
            alive.append(node)
            if original_ids and id(node) not in original_ids:
                origins[id(node)] = (node, _READ_COPY)
            if kind is set:
                mutable.append(node)
            children = list(kind.__iter__(node))
            read.admit(len(children))
            if wrap:
                for child in children:
                    _hashed_members(child, scope, members, mutable)
            continue
        if wrap:
            done[id(node)] = _Comparand(node, scope)
            alive.append(node)
    covered = done.get(id(root), root)
    # 確かめる容器: 辿った変わる容器の全部（写した容器の元・写さずに組み込みの code が元のまま比べる容器: 外の code が
    # そこへ分類していない葉を足すと、組み込みの code がその葉を包まずに比べる）。`exact_tree` が写した木（scalar の
    # subclass の葉・subclass の容器）は、元から辿れる変わる容器を全部
    if root is values:
        guarded = list({id(node): node for node in mutable}.values())
    else:
        guarded = shape  # 読んだ木の写しは外の code に渡らない（`_READ_COPY`）: 元の変わる容器だけを確かめる
    alive.append(origins)
    frame = _CopyFrame(guarded, members) if guarded or members else None
    return covered, frame, root


def _strongest_trust(tree: Any, scope: "_ComparisonScope") -> str:
    """読んだ木の葉の分類の最も強いもの（組み込みの容器を辿る。閉路・共有は 1 度だけ）。"""

    read = _StorageRead(_COMPARISON_NODES, traversal=True)
    strongest = _TRUSTED
    pending = [tree]
    seen: set = set()
    alive: List[Any] = []
    while pending:
        node = pending.pop()
        kind = type(node)
        if node is None or kind is int or kind is str or kind is bool or kind is float:
            continue
        if kind is tuple or kind is list or kind is set or kind is frozenset or kind is dict:
            if id(node) in seen:
                continue
            seen.add(id(node))
            alive.append(node)
            children: Any = itertools.chain(dict.keys(node), dict.values(node)) if kind is dict else kind.__iter__(node)
            read.admit(2 * dict.__len__(node) if kind is dict else kind.__len__(node))
            pending.extend(children)
            continue
        trust = scope.trust(node)
        if _TRUST_RANK[trust] > _TRUST_RANK[strongest]:
            strongest = trust
            if strongest == _OPAQUE:
                break
    return strongest


def _hashed_members(value: Any, scope: "_ComparisonScope", members: List[Any], mutable: List[Any]) -> None:
    """包まずに組み込みの code が比べる値（hash で置く位置: set の要素・dict の key、key を写せない dict の値）の、包めない
    葉を `members` に足す（比較の間、型と型の状態を確かめる）。

    包まない値の中の容器（tuple・frozenset、dict の値なら list・dict・set も）は組み込みの code が元のまま辿るので、
    全部の容器を辿って葉を確かめる（容器の中の葉も包めない）。包めない葉は、組み込みの code が比べる（`==` の戻り値を
    真偽で読む）ので、比較の dunder が不活性か登録した実装（組み込みの `bool` を返す）でなければ判定不能。外の code が
    途中でその型を書き換えれば `_CopyFrame` が判定不能にする。閉路の容器は 1 度だけ辿る。
    """

    read = _StorageRead(_COMPARISON_NODES, traversal=True)
    pending = [value]
    seen: set = set()
    alive: List[Any] = []
    while pending:
        node = pending.pop()
        kind = type(node)
        if node is None or kind is int or kind is str or kind is bool or kind is float:
            continue
        if kind is tuple or kind is frozenset or kind is list or kind is set or kind is dict:
            if id(node) in seen:
                continue
            seen.add(id(node))
            alive.append(node)
            if kind is list or kind is dict or kind is set:
                mutable.append(node)  # 組み込みの code が元のまま比べる変わる容器: 比べている間変わらないことを確かめる
            if kind is dict:
                read.admit(2 * dict.__len__(node))
                pending.extend(itertools.chain(dict.keys(node), dict.values(node)))
            else:
                read.admit(kind.__len__(node))
                pending.extend(kind.__iter__(node))
            continue
        if _TRUST_RANK[scope.trust(node)] > _TRUST_RANK[_CALLS]:
            raise undecidable(f"a {type_name(kind)} compared in place by builtin code compares through foreign code")
        members.append(node)


#: hash で置く位置の値が使う dunder（比較と hash）
_HASHING_DUNDERS = _COMPARISON_DUNDERS + ("__hash__",)


#: `exact_tree` が写した容器の印（`_Comparand._other` が外の code に渡さない）
_READ_COPY = object()


def _source(origins: Dict[int, Tuple[Any, Any]], node: Any) -> Any:
    """写す前の容器（読んだ木の容器が `exact_tree` の写しなら `_READ_COPY`）。"""

    found = origins.get(id(node))
    return _READ_COPY if found is not None and found[0] is node and found[1] is _READ_COPY else node


#: 容器の比べ方・hash の dunder（subclass がこれを変えると、基底型として読んだ木の比較は双子の比較と違う）
_CONTAINER_DUNDERS = _COMPARISON_DUNDERS + ("__hash__", "__contains__")


def _comparison_shape(value: Any) -> Tuple[List[Any], set, List[Any]]:
    """値（読む前の木）から辿れる変わる容器（list / dict / set とその subclass。基底型の slot で辿る）と、辿った容器の
    `id` の集合（値が生きている間だけ意味を持つ: 呼ぶ側が値を持つ）と、容器の subclass の値（読んだ木は基底型の値で
    比べる: 比べている間、型・`__class__` が変わらないことを呼ぶ側が確かめる）。

    `exact_tree` は容器を基底型へ読む。比べ方がその基底型と違う容器（比較・hash・`in` の dunder を変えた subclass、
    `deque`、dict の view、`OrderedDict` などの別の比べ方の型）は、読んだ木の比較が双子の比較と違う:
    `UndecidableComparison`。
    """

    read = _StorageRead(_COMPARISON_NODES, traversal=True)
    found: List[Any] = []
    subclassed: List[Any] = []
    seen: set = set()
    alive: List[Any] = []
    pending = [value]
    while pending:
        node = pending.pop()
        kind = type(node)
        if node is None or kind is int or kind is str or kind is bool or kind is float:
            continue
        if kind is _DICT_VIEWS[0] or kind is _DICT_VIEWS[1] or kind is _DICT_VIEWS[2]:
            raise undecidable("a dict view does not compare like the sequence it is read as")
        base = _subclass_tree_kind(kind)
        if base is None:
            continue
        if base is collections.deque:
            raise undecidable("a deque does not compare like the list it is read as")
        if id(node) in seen:
            continue
        if kind is not base:
            _require_same_comparison(kind, base)
            subclassed.append(node)
        seen.add(id(node))
        alive.append(node)
        if base is dict:
            children = [item for pair in dict.items(node) for item in pair]
        else:
            children = list(base.__iter__(node))
        if base is dict or base is list or base is set:
            found.append(node)
        read.admit(len(children))
        pending.extend(children)
    return found, seen, subclassed


def _require_same_comparison(kind: type, base: type) -> None:
    """容器の subclass の比べ方・hash・`in` が基底型と同じか（MRO の名前空間で引いた実装の identity）。違えば
    `UndecidableComparison`。"""

    for name in _CONTAINER_DUNDERS:
        if _resolved_dunder(kind, name) is not _resolved_dunder(base, name):
            raise undecidable(f"{type_name(kind)} compares differently from {type_name(base)}")


def _resolved_dunder(kind: type, name: str) -> Any:
    """型の MRO の名前空間で最初に見つかる `name` の実装（metaclass の hook を通らない。無ければ `_MISSING_DUNDER`）。"""

    mro = _TYPE_MRO.__get__(kind)
    if not _within_scan(len(mro)):
        raise undecidable("a container type with a long MRO is not compared")
    for klass in mro:
        found = _namespace_value(klass, name)
        if found is _AMBIGUOUS_NAME:
            raise undecidable(f"a class namespace holds a key that is not a builtin str (looking up {name!r})")
        if found is not _MISSING_DUNDER:
            return found
    return _MISSING_DUNDER


_MISSING_DUNDER = object()
#: `lookup_fact` の `dict.get` の既定値の列（`map` が名前の数だけ読む）
_REPEAT_MISSING = itertools.repeat(_MISSING_DUNDER)
_REPEAT_MRO_READ = itertools.repeat(_MRO_READ)


def inert(value: Any) -> bool:
    """値が不活性な木か（`==`・hash・順序・dict の key・set の要素に使っても組み込みの code だけで決まる値）。

    容器は組み込みの tuple / list / dict / set / frozenset **そのもの**、葉は `None` と exact な `int` / `str` / `bool` /
    `float` だけ（型は identity で見る。Enum の member・scalar の subclass・それ以外の object は不活性でない）。
    辿る量は `exact_tree` と同じ反復の確かめ（量の owner の無い文脈では上限なし: 量だけで「不活性でない」と答えない）。
    共有された容器・閉路の容器は 1 度だけ辿る。返す値は `bool`。
    """

    kind = type(value)
    if value is None or kind is int or kind is str or kind is bool or kind is float:
        return True
    read = _StorageRead(_COMPARISON_NODES, traversal=True)
    pending = [value]
    seen: set = set()
    alive = []  # 辿った容器を走査の間は生かす（`id` を再利用させない）
    while pending:
        node = pending.pop()
        kind = type(node)
        if node is None or kind is int or kind is str or kind is bool or kind is float:
            continue
        if id(node) in seen:
            continue
        if kind is tuple or kind is list or kind is set or kind is frozenset:
            seen.add(id(node))
            alive.append(node)
            read.admit(kind.__len__(node))
            pending.extend(kind.__iter__(node))
        elif kind is dict:
            seen.add(id(node))
            alive.append(node)
            read.admit(dict.__len__(node))
            pending.extend(dict.keys(node))
            pending.extend(dict.values(node))
        else:
            return False
    return True


def truth(value: Any) -> bool:
    """暗黙の callback（`__eq__` / `__lt__` / `__contains__` など）が返した値を、条件が読む真偽にする（`bool(value)` と
    同じ値）。

    読み方: exact な `bool` はそのまま。scalar の subclass（Enum でない）は基底型の値の真偽（subclass の `__bool__` /
    `__len__` を呼ばない）。それ以外は `bool()`（その型の `__bool__` は組み込みの `bool` を返すことを CPython が強制し、
    `__len__` の戻り値は C が基底型の値で読む: 嘘の真偽を返せない）。返す値の保証: 組み込みの `bool`。
    """

    kind = type(value)
    if kind is bool:
        return value
    if issubclass(kind, _SCALAR_BASES):
        return bool(exact_scalar(value))
    return bool(value)


def _exact_elements(container: Any) -> bool:
    """組み込みの tuple / list / set / frozenset の要素が全部 exact な scalar か、exact な scalar だけの tuple か（呼ぶ側が
    長さを数えてから呼ぶ。入れ子の tuple の長さはここで上限と比べる）。"""

    for element in type(container).__iter__(container):
        kind = type(element)
        if not (element is None or kind is int or kind is str or kind is bool or kind is float):
            # 入れ子の 1 段だけ: 要素が exact な scalar だけの tuple（ref の比べる値の tuple によくある形）
            if kind is not tuple or not _within_scan(tuple.__len__(element)):
                return False
            for item in tuple.__iter__(element):
                item_kind = type(item)
                if not (item is None or item_kind is int or item_kind is str or item_kind is bool or item_kind is float):
                    return False
    return True


#: exact な組み込みの scalar（不活性な葉）の型
def _exact_leaf(value: Any) -> bool:
    kind = type(value)
    return value is None or kind is int or kind is str or kind is bool or kind is float


def _plain_operands(*values: Any) -> bool:
    """値が全部、そのまま組み込みの比較に渡してよい木か（読んでも変わらない: scalar の subclass の葉・subclass の容器が
    無く、葉が全部信頼する葉）。最も多い形の速い経路。"""

    for value in values:
        if _exact_leaf(value):
            continue
        kind = type(value)
        if kind is tuple or kind is list or kind is set or kind is frozenset:
            _admit_storage(kind.__len__(value), _COMPARISON_NODES, traversal=True)
            if _exact_elements(value):
                continue
        if not _plain_tree(value):
            return False
    return True


def _plain_tree(value: Any) -> bool:
    """値が、写さずに組み込みの比較へ渡してよい木か（1 回の走査）: 容器は組み込みの型そのもの、葉は信頼する葉だけ。

    scalar の subclass・容器の subclass・`deque`・dict の view は信頼する葉でない（`_leaf_trust`: 外の code / 不透明）
    ので、真なら `exact_tree` も写さない（読んでも変わらない木）。閉路の容器は 1 度だけ辿る（比較は組み込みの再帰の
    上限まで: 双子と同じ）。"""

    read = _StorageRead(_COMPARISON_NODES, traversal=True)
    pending = [value]
    seen: set = set()
    alive: List[Any] = []
    while pending:
        node = pending.pop()
        kind = type(node)
        if node is None or kind is int or kind is str or kind is bool or kind is float:
            continue
        if kind is tuple or kind is list or kind is set or kind is frozenset or kind is dict:
            if id(node) in seen:
                continue
            seen.add(id(node))
            alive.append(node)
            if kind is dict:
                read.admit(2 * dict.__len__(node))
                children: Any = itertools.chain(dict.keys(node), dict.values(node))
            else:
                read.admit(kind.__len__(node))
                children = kind.__iter__(node)
            for child in children:
                child_kind = type(child)
                if not (child is None or child_kind is int or child_kind is str or child_kind is bool or child_kind is float):
                    pending.append(child)  # exact な scalar の葉は積まない（よくある形）
            continue
        if _leaf_trust(node) != _TRUSTED:
            return False
    return True


def _compared_tree(value: Any) -> Any:
    """比べる値の読み（`exact_tree`）。読めない値（不活性でない key の dict・要素の set を作り直す必要がある、など）は
    `UndecidableComparison`（比べる側の契約が許す唯一の逸脱: `decided_equal` などが判定しないとして扱う）。"""

    try:
        return exact_tree(value)
    except UndecidableComparison:
        raise
    except TypeError as error:
        raise undecidable(f"the compared value is not read: {error}") from error


def equal(left: Any, right: Any) -> bool:
    """`bool(left == right)`（条件で読む `==`）と同じ真偽。比較は組み込みの `==` が行い、信頼しない葉の比較の戻り値は
    `truth` で読む（`_Comparand`）。返す値の保証: 組み込みの `bool`。判定不能は `UndecidableComparison`。"""

    leaves = _leaf_operands(left, right)
    if leaves is not None:
        return _checked(truth(_compare(leaves[2], operator.eq, leaves[0], leaves[1])))
    if _plain_operands(left, right):
        return left == right
    (x, y), frame, _read = _covered((left, right))
    return _guarded(frame, lambda: truth(x == y))


def _leaf_operands(left: Any, right: Any) -> Optional[Tuple[Any, Any, bool]]:
    """比べる 2 つの値が両方とも容器でない葉なら、読んだ葉の組（scalar の subclass は基底型の値）と、どちらかが外の code
    で比べる葉か（比べる間は外の code の区間: `_compare`）。容器なら `None`。

    葉どうしの比較は写しも確かめも要らない: 組み込みの演算（反射を含む Python の手順）が元の値どうしを比べ、戻り値を
    `truth` で読めば `bool(双子の左 op 双子の右)` と同じ（外の code は双子と同じ相手を受け取る）。不透明な葉（中の比較の
    戻り値を C が読む）は `UndecidableComparison`。外の code の後は、進行中の比較の写しを確かめる（`_checked`）。"""

    out = []
    foreign = False
    for value in (left, right):
        kind = type(value)
        if value is None or kind is int or kind is str or kind is bool or kind is float:
            out.append(value)
            continue
        if (
            kind is _DICT_VIEWS[0] or kind is _DICT_VIEWS[1] or kind is _DICT_VIEWS[2]
            or kind is _ODICT_VIEWS[0] or kind is _ODICT_VIEWS[1] or kind is _ODICT_VIEWS[2]
            or _kind_entry(kind)[1] is not None
        ):
            return None  # 容器（subclass・view を含む）: 木の読みへ
        if issubclass(kind, _SCALAR_BASES) and not issubclass(kind, Enum):
            out.append(exact_scalar(value))
            continue
        trust = _leaf_trust(value)
        if trust == _OPAQUE:
            raise undecidable(f"{type_name(kind)} compares what it holds inside builtin code")
        foreign = foreign or trust == _FOREIGN
        out.append(value)
    return out[0], out[1], foreign


def unequal(left: Any, right: Any) -> bool:
    """`bool(left != right)` と同じ真偽（`equal` と同じ読みで、組み込みの `!=` が比べる）。"""

    leaves = _leaf_operands(left, right)
    if leaves is not None:
        _require_explicit_ne(leaves[0], leaves[1])
        return _checked(truth(_compare(leaves[2], operator.ne, leaves[0], leaves[1])))
    if _plain_operands(left, right):
        return left != right
    (x, y), frame, _read = _covered((left, right))
    return _guarded(frame, lambda: truth(x != y))


def same(left: Any, right: Any) -> bool:
    """容器の要素の比べ方（`left is right or bool(left == right)`。Python の容器・dict・`in` が要素に使う規則）。"""

    return left is right or equal(left, right)


def contains(container: Any, item: Any) -> bool:
    """`item in container` と同じ真偽（容器は組み込みの tuple / list / dict / set / frozenset）。探索（要素を読む時点・
    hash の衝突の探索の順・set を frozenset で引き直す規則）は組み込みの `in` が行う。返す値の保証: 組み込みの `bool`。
    組み込みでない容器・判定不能は `UndecidableComparison`。"""

    if _plain_operands(container, item):
        kind = type(container)
        if kind is tuple or kind is list or kind is set or kind is frozenset or kind is dict:
            return item in container
        raise undecidable(f"{type_name(kind)} is not a builtin container")
    (box, wanted), frame, _read = _covered((container, item))
    kind = type(box)
    if not (kind is tuple or kind is list or kind is set or kind is frozenset or kind is dict):
        raise undecidable(f"{type_name(kind)} is not a builtin container")
    return _guarded(frame, lambda: truth(wanted in box))


def less(left: Any, right: Any) -> bool:
    """`bool(left < right)` と同じ真偽（並べる比較。`equal` と同じ読みで、組み込みの `<` が比べる）。"""

    leaves = _leaf_operands(left, right)
    if leaves is not None:
        return _checked(truth(_compare(leaves[2], operator.lt, leaves[0], leaves[1])))
    if _plain_operands(left, right):
        return truth(left < right)
    (x, y), frame, _read = _covered((left, right))
    return _guarded(frame, lambda: truth(x < y))


def sorted_trees(items: Any) -> List[Any]:
    """`sorted(items)` と同じ順の list（`items` は組み込みの list / tuple）。要素を 1 回の読みで写し、組み込みの `sorted`
    が比べる（比べる組と順は素の `sorted` と同じ。信頼しない葉の比較の戻り値は `truth` で読む）。返す要素は写した木。"""

    kind = type(items)
    if kind is not list and kind is not tuple:
        raise TypeError("sorted_trees reads a builtin list or tuple")
    originals = tuple(kind.__iter__(items))
    _admit_storage(len(originals), _COMPARISON_NODES, traversal=True)
    if _plain_operands(*originals):
        return sorted(originals)  # 読んでも変わらない木（写しが無い）
    keys, frame, read = _covered(originals)  # 元の値を読む: 元の変わる容器を確かめる
    trees = list(read)
    order = _guarded(frame, lambda: sorted(range(len(trees)), key=keys.__getitem__))
    return [trees[index] for index in order]


def hash_tree(value: Any) -> int:
    """比べる側の契約の hash（`equal` と同じ読み）。返す値の保証:

    - `equal(a, b)` が真なら `hash_tree(a) == hash_tree(b)`。比べると等しい外の object（`__hash__` が同じ値を返す
      object）とも整合する: hash は読んだ木を組み込みの `hash` で求め、葉の hash はその葉自身の hash。
    - 同じ値の hash は、値（と値が持つ葉の object）が変わらない間は呼び出しの間で同じ: identity で hash する組み込みの
      値は NaN の float だけで、exact な NaN はその object の hash、scalar の subclass の NaN は読みの写し（同じ元の葉には
      いつも同じ写し: `_canonical_nan`）の hash。
    - scalar の subclass の葉は基底型の値で hash する（subclass の `__hash__` を呼ばない）。外の object の葉は、その
      object 自身の `__hash__`（戻り値は C が基底型の値で読む: 双子と同じ呼び出し）。

    hash の値そのものは双子の hash と同じとは限らない（scalar の subclass の NaN の写しは双子の写しと別の object）。hash できない値は `TypeError`（組み込みの
    `hash` と同じ）、比べ方・hash が基底型と違う容器・読めない値は `UndecidableComparison`。
    """

    if type(value) is tuple and _within_scan(tuple.__len__(value)) and _flat_exact(value):
        return hash(value)  # よくある形（ref の比べる値の tuple）: exact な scalar とその tuple だけの木は読んでも同じ木
    tree = _compared_tree(value)
    if tree is not value:
        _comparison_shape(value)  # hash を変えた容器の subclass を基底型の値で hash しない
    _require_hashed_lookups(tree)  # 組み込みの `hash` が葉の型の `__hash__` を名前で引く: 引きが hook を呼ばないこと
    if _plain_tree(tree):
        return hash(tree)
    # 葉の `__hash__` が Python の code（外の code・登録した hash）: 外の code の区間で走らせる（区間の記録を見せず、
    # 抜けるときに監査済みの code が頼る事実を確かめ直す）
    with outside_audit():
        return hash(tree)


def _flat_exact(tree: tuple) -> bool:
    """tuple の要素が全部 exact な scalar か、その tuple か（入れ子は 1 段だけ。外の長さは呼ぶ側が上限と比べた）。exact な
    NaN もそのまま（その object の hash: 読みは写さない）。"""

    for item in tuple.__iter__(tree):
        kind = type(item)
        if item is None or kind is int or kind is str or kind is bool or kind is float:
            continue
        if kind is not tuple or not _within_scan(tuple.__len__(item)):
            return False
        for inner in tuple.__iter__(item):
            inner_kind = type(inner)
            if not (inner is None or inner_kind is int or inner_kind is str or inner_kind is bool or inner_kind is float):
                return False
    return True


def _require_hashed_lookups(tree: Any) -> None:
    """hash する木の葉（tuple / frozenset の中の葉）の型の `__hash__` の引きが、名前空間の key の hook を呼ばないこと
    （`_require_named_lookup`）。list / dict / set は hash できない（`hash` が `TypeError`）ので辿らない。"""

    read = _StorageRead(_COMPARISON_NODES, traversal=True)
    seen: set = set()
    alive: List[Any] = [tree]
    pending = [tree]
    while pending:
        node = pending.pop()
        kind = type(node)
        if kind is tuple or kind is frozenset:
            if id(node) in seen:
                continue
            seen.add(id(node))
            alive.append(node)
            read.admit(kind.__len__(node))
            pending.extend(kind.__iter__(node))
        else:
            _require_named_lookup(node, "__hash__")  # `hash` は葉の型の `__hash__` を名前で引く


def inert_key(value: Any) -> Any:
    """dict の key・set の要素に置く値（`exact_tree` で読んだ不活性な木）。不活性でなければ `UndecidableComparison`
    （hash が等しい key どうしの `==` を組み込みの code が葉の型の code で読む: 判定しない）。"""

    tree = _compared_tree(value)
    if not inert(tree):
        raise undecidable("a value that is not inert is not used as a key")
    return tree


def as_int(value: Any) -> int:
    """`int(value)` と同じ値（bool / int / float / str とその subclass）を基底型の slot で求める。

    それ以外（`__int__` / `__index__` を持つ object・enum）は `TypeError`（user code を呼ばない）。
    """

    kind = type(value)
    if kind is int:
        return value
    if value is True or value is False:
        return 1 if value else 0
    if issubclass(kind, Enum):
        raise TypeError(f"{type_name(kind)} is not converted to int without its own code")
    if issubclass(kind, int):
        return int.__index__(value)
    if issubclass(kind, float):
        return int(float.__float__(value))
    if issubclass(kind, str):
        return int(str.__str__(value))
    raise TypeError(f"{type_name(kind)} is not converted to int without its own code")


def as_float(value: Any) -> float:
    kind = type(value)
    if kind is float:
        return value
    if value is True or value is False:
        return 1.0 if value else 0.0
    if issubclass(kind, Enum):
        raise TypeError(f"{type_name(kind)} is not converted to float without its own code")
    if issubclass(kind, float):
        return float.__float__(value)
    if issubclass(kind, int):
        return float(int.__index__(value))
    if issubclass(kind, str):
        return float(str.__str__(value))
    raise TypeError(f"{type_name(kind)} is not converted to float without its own code")


def as_bool(value: Any) -> bool:
    """`bool(value)` と同じ値（scalar・組み込みの振る舞いの容器）。それ以外は `TypeError`。"""

    if value is None or value is True or value is False:
        return bool(value)
    base = plain_scalar(value)
    if base is not NOT_PLAIN:
        return bool(base)
    if _builtin_length(value):
        return size(value) > 0
    kind = type(value)
    if issubclass(kind, Enum) and builtin_enum(value):
        # 組み込みのままの enum: mixin（int / str / float）は基底型の値の真偽（真偽の slot が基底型の
        # ものだけ）、それ以外は `__bool__` / `__len__` を持たなければ真
        truth = _type_lookup(kind, "__bool__", _ABSENT)
        length = _type_lookup(kind, "__len__", _ABSENT)
        if issubclass(kind, (int, float, str)):
            if _one_of(truth, _BUILTIN_TRUTH) and _one_of(length, _BUILTIN_LENGTH):
                return bool(json_scalar(value))
        elif truth is _ABSENT and length is _ABSENT:
            return True
        raise TypeError(f"{type_name(kind)} is not converted to bool without its own code")
    # `__bool__` / `__len__` を MRO のどこにも持たない型の値は常に真（`bool(x)` と同じ。その値の
    # code は無い: record・generator・関数など）。`__bool__ = None` のような値も「持つ」側
    if (
        _type_lookup(kind, "__bool__", _ABSENT) is _ABSENT
        and _type_lookup(kind, "__len__", _ABSENT) is _ABSENT
    ):
        return True
    raise TypeError(f"{type_name(kind)} is not converted to bool without its own code")


def builtin_hashed_scalar(value: Any) -> bool:
    """str / int / float の subclass の値で、`__hash__` / `__eq__` が基底型の組み込みの実装のままか
    （JPype の `JString` など: dict の key として置いても値の code を呼ばない）。"""

    kind = type(value)
    if type(kind) is type:
        return lookup_fact(_BUILTIN_HASHED, kind, _builtin_hashed_type, kind)
    return _plain_metatype(kind) and _builtin_hashed_type(kind)


#: 型ごとの `builtin_hashed_scalar` の結果（metaclass が `type` の型だけ）
_BUILTIN_HASHED = _LookupFactTable()


def _builtin_hashed_type(kind: type) -> bool:
    if issubclass(kind, Enum):
        return False
    for base in (str, int, float):
        if issubclass(kind, base):
            try:
                return (
                    _type_lookup(kind, "__hash__", None) is _type_lookup(base, "__hash__", None)
                    and _type_lookup(kind, "__eq__", None) is _type_lookup(base, "__eq__", None)
                )
            except TypeError:
                # 型を上限の中で読めない: 組み込みの hash とは確かめられない
                return False
    return False


def _one_of(value: Any, options: Tuple[Any, ...]) -> bool:
    """`value` が `options` のどれかと同じ object か（identity。値の `__eq__` を呼ばない）。"""

    for option in options:
        if value is option:
            return True
    return False


#: 基底型の真偽・長さの slot（mixin の enum が上書きしていないもの。無いことも含む）
_BUILTIN_TRUTH = (_ABSENT, int.__bool__, float.__bool__)
_BUILTIN_LENGTH = (_ABSENT, str.__len__)


def as_str(value: Any) -> str:
    """`str(value)` と同じ文字列（scalar・組み込みのままの enum）。それ以外は `TypeError`。"""

    base = plain_scalar(value)
    if base is not NOT_PLAIN:
        return base if type(base) is str else str(base)
    if builtin_enum(value):
        return _enum_text(value, "__str__")
    raise TypeError(f"{type_name(type(value))} is not converted to str without its own code")


def as_repr(value: Any) -> str:
    """`repr(value)` と同じ文字列（scalar・組み込みのままの enum）。それ以外は `TypeError`。"""

    base = plain_scalar(value)
    if base is not NOT_PLAIN:
        return type(base).__repr__(base)
    if builtin_enum(value):
        return _enum_text(value, "__repr__")
    raise TypeError(f"{type_name(type(value))} is not converted to repr without its own code")


def _enum_text(value: Any, slot: str) -> str:
    """組み込みのままの enum の `str()` / `repr()`（`Enum.__str__` / `Enum.__repr__` を、`__class__` を読まずに再現する）。"""

    kind = type(value)
    method = type_attribute(kind, slot)
    if slot == "__str__" and method is object.__str__:
        # `object.__str__` は `repr()` と同じ
        slot, method = "__repr__", type_attribute(kind, "__repr__")
    class_name = _TYPE_NAME.__get__(kind)
    if method is Enum.__str__:
        return f"{class_name}.{enum_name(value)}"
    if method is Enum.__repr__:
        member = plain_scalar(instance_state(value, "_value_", None))
        return f"<{class_name}.{enum_name(value)}: {type(member).__repr__(member)}>"
    if method is str.__str__:
        return str.__str__(value)
    if method is int.__repr__ or method is int.__str__:
        return int.__repr__(value)
    raise TypeError(f"{type_name(kind)} has its own {slot}")


_BUILTIN_ENUM_STR = frozenset({Enum.__str__, str.__str__, int.__repr__, int.__str__, object.__str__})
_BUILTIN_ENUM_REPR = frozenset({Enum.__repr__, object.__repr__})
_BUILTIN_HASH = frozenset({Enum.__hash__, str.__hash__, int.__hash__, object.__hash__})


def builtin_enum(value: Any) -> bool:
    """組み込みのままの enum の member か（`__str__` / `__repr__` / `__hash__` を上書きせず、値が scalar）。"""

    kind = type(value)
    if not issubclass(kind, Enum):
        return False
    from enum import EnumMeta

    # `Enum.__str__` / `__repr__` / `__hash__` は Python の code で、member の属性と `__class__` を
    # 読み、値の `repr` を呼ぶ: それらも組み込みのまま（metaclass・属性の読み方・値の型）のときだけ
    try:
        member = instance_state(value, "_value_", None)
        name = instance_state(value, "_name_", None)
    except TypeError:
        # member の状態を上限の中で読めない: 組み込みのままの enum とは確かめられない
        return False
    if not (member is None or type(member) is str or type(member) is int or type(member) is float or type(member) is bool):
        return False
    # member の名前も組み込みの `str`（`Enum.__str__` / `__hash__` / `__format__` は `_name_` を使う）
    if type(name) is not str:
        return False
    # 型の側の判定は型ごとに 1 度だけ（EnumMeta の hash・比較は組み込みの実装）
    known = _BUILTIN_ENUM_TYPES.get(kind) if type(kind) is EnumMeta else None
    if known is None:
        known = _builtin_enum_type(kind)
        if type(kind) is EnumMeta:
            _BUILTIN_ENUM_TYPES[kind] = known
    return known


#: 型の側が組み込みのままの enum か（`_builtin_enum_type` の結果。型ごと）
_BUILTIN_ENUM_TYPES = _TypeFactTable()


def _builtin_enum_type(kind: type) -> bool:
    try:
        return _builtin_enum_type_checked(kind)
    except TypeError:
        return False


def _builtin_enum_type_checked(kind: type) -> bool:
    from enum import EnumMeta

    return (
        type(kind) is EnumMeta
        and _one_of(type_attribute(kind, "__str__"), _BUILTIN_ENUM_STR)
        and _one_of(type_attribute(kind, "__repr__"), _BUILTIN_ENUM_REPR)
        and _one_of(type_attribute(kind, "__hash__"), _BUILTIN_HASH)
        and _one_of(type_attribute(kind, "__eq__"), _BUILTIN_EQ)
        and _one_of(type_attribute(kind, "__format__"), _BUILTIN_ENUM_FORMAT)
        and _one_of(type_attribute(kind, "__getattribute__"), _BUILTIN_GETATTRIBUTE)
        and type_attribute(kind, "__class__") is _OBJECT_CLASS
        # 並べる比較（`sorted` / JSON の `sort_keys` が member を key にして呼ぶ）も組み込みの実装のまま
        and all(_one_of(type_attribute(kind, name), _BUILTIN_ORDER[name]) for name in _ORDER_DUNDERS)
    )


#: 並べる・比べる dunder（`builtin_enum` の member を sort / dict の key の整列に使うとき C が呼ぶ）
_ORDER_DUNDERS = ("__lt__", "__le__", "__gt__", "__ge__", "__ne__")
_BUILTIN_ORDER = {
    name: frozenset(getattr(base, name) for base in (object, str, int, float)) for name in _ORDER_DUNDERS
}


_BUILTIN_EQ = frozenset({object.__eq__, str.__eq__, int.__eq__, float.__eq__})
_BUILTIN_ENUM_FORMAT = frozenset({Enum.__format__, object.__format__, str.__format__, int.__format__, float.__format__})
_OBJECT_CLASS = object.__dict__["__class__"]
_BUILTIN_GETATTRIBUTE = frozenset({
    object.__getattribute__, str.__getattribute__, int.__getattribute__, float.__getattribute__,
})


def enum_value(value: Any) -> Any:
    """enum の member の値（instance の `_value_`。`value` の property を呼ばない）。"""

    return instance_state(value, "_value_")


def enum_name(value: Any) -> Any:
    return instance_state(value, "_name_")


# ---------------------------------------------------------------------------
# instance の属性
# ---------------------------------------------------------------------------


#: `attribute` が instance の値の無いことを知る印（`instance_state` の既定値）


def _dict_holder(kind: type) -> Any:
    """instance の `__dict__` を読む組み込みの descriptor（無ければ `None`。metaclass が `type` の型ごとに 1 度）。

    型の MRO のどこかが持つ組み込みの getset（C の型は member descriptor）だけ。metatype の
    `__dict__`（型 object 用）を instance に当てない。
    """

    entry = _DICT_HOLDERS.get(id(kind))
    if (
        entry is not None and entry[0] is kind and _TYPE_MRO.__get__(kind) is entry[1]
        and _LOOKUPS.active is None and not _NESTING.active
    ):
        return entry[2]
    # 読みを記録している計算・型の信頼の判定の途中は引き直す（名前の引きを記録・依存に足す）
    mro = _TYPE_MRO.__get__(kind)
    holder = _dict_holder_of(kind)
    if _TYPE_MRO.__get__(kind) is mro and _fixed_dict_entries(mro):
        if len(_DICT_HOLDERS) >= _TYPE_FACTS_LIMIT:
            _DICT_HOLDERS.clear()
        _DICT_HOLDERS[id(kind)] = (kind, mro, holder)
    return holder


def _fixed_dict_entries(mro: Tuple[type, ...]) -> bool:
    """MRO のどの class の名前空間の `__dict__` の entry も、class を作った後に変えられないか（`_DICT_HOLDERS` の前提）。

    metaclass が `type` の class は `__dict__` を書けも消せもしない（`setattr` / `type.__setattr__` / `delattr` は metaclass
    の `type.__dict__["__dict__"]`（書けない data descriptor）に当たって `AttributeError`。`__class__` も `type` から変え
    られない）。組み込みの型の名前空間は変わらない。metaclass が `type` でない heap class（metaclass が `__dict__` を
    descriptor でない値で持てば、`setattr` は class の名前空間に書く）は前提の外: 記録しない。
    """

    if not _within_scan(tuple.__len__(mro)):
        return False
    flags = _TYPE_FLAGS.__get__
    for klass in mro:
        if type(klass) is not type and flags(klass) & _HEAP_TYPE:
            return False
    return True


def _dict_holder_of(kind: type) -> Any:
    holder = type_attribute(kind, "__dict__")
    holder_kind = type(holder)
    return holder if (
        (holder_kind is types.GetSetDescriptorType or holder_kind is types.MemberDescriptorType)
        and _in_mro(holder.__objclass__, kind)
    ) else None


#: 型ごとの `_dict_holder` の結果（`id(型)` → (型, MRO, descriptor)）。結果は MRO の class の名前空間の `__dict__` の entry
#: だけで決まり、その entry は class を作った後に変わらない（`_fixed_dict_entries`）: MRO の tuple が同じ object の間
#: （`__bases__` の書き換えは MRO を作り直す）使う。記録は型と MRO を生かす（`id` を再利用させない）
_DICT_HOLDERS: Dict[int, Tuple[type, Tuple[type, ...], Any]] = {}


def _in_mro(klass: Any, kind: type) -> bool:
    """`klass` が `kind` の MRO に在るか（identity で比べる。metaclass の `__eq__` を呼ばない）。"""

    mro = _TYPE_MRO.__get__(kind)
    if not _within_scan(tuple.__len__(mro)):
        return False
    for entry in mro:
        if entry is klass:
            return True
    return False


def instance_state(value: Any, name: str, default: Any = _MISSING) -> Any:
    """instance の `__dict__` か slot に在る値（descriptor・`__getattr__` を呼ばない）。"""

    kind = type(value)
    entry = _DICT_HOLDERS.get(id(kind))
    if (
        entry is not None and entry[0] is kind and _TYPE_MRO.__get__(kind) is entry[1]
        and _LOOKUPS.active is None and not _NESTING.active
    ):
        offset_holder = entry[2]  # `_dict_holder` の記録（同じ確かめ）
    else:
        offset_holder = _dict_holder(kind)
    if offset_holder is not None:
        state = offset_holder.__get__(value, kind)
        if type(state) is dict:
            # key が全部組み込みの `str` のときだけ hash で引く（`setattr(o, K("x"), v)` の key の
            # `__eq__` を呼ばない）。そうでなければ読まない: Python の属性の読みは hash の等しい key の
            # `__eq__` を key の文字列に依らず呼ぶ（どの値を読むかを決めない）。instance の状態は値の
            # storage（数は値の読みとして比べる）
            _admit_storage(dict.__len__(state), "an instance's __dict__")
            if not _exact_str_raw(state):
                raise TypeError(f"{type_name(kind)} has an instance __dict__ with a key that is not a builtin str")
            if name in state:
                return state[name]
    descriptor = type_attribute(kind, name)
    if type(descriptor) is types.MemberDescriptorType:
        try:
            return descriptor.__get__(value, kind)
        except AttributeError:
            pass
    if default is not _MISSING:
        return default
    raise TypeError(f"{name!r} of {type_name(kind)} is not plain instance state")


#: `state_setter` で宣言した `__setattr__` の code
_STATE_SETTERS: set = set()


def state_setter(function: Any) -> Any:
    """`set_state()` が呼んでよい package の型の `__setattr__`（record の不変条件の検査）を宣言する。

    宣言していない `__setattr__` を持つ型へは `set_state` は書かない（`TypeError`）。宣言した関数は
    `tests/unit/_live_flow_audit.py` が root として監査する（書く値は live な値）。
    """

    if type(function) is not types.FunctionType or not package_code(function.__code__):
        raise TypeError("a state setter is a package function")
    _STATE_SETTERS.add(function.__code__)
    return function


class readable_property(property):
    """`attribute()` が呼んでよい package の property（record の API として読む値）。

    `attribute()` が呼ぶ property はこれで宣言したものだけ（普通の `property` は呼ばない）。
    宣言した getter は `tests/unit/_live_flow_audit.py` が root として監査する（field は live な値）。
    """


def attribute_of(value: Any, name: str, default: Any = _MISSING) -> Any:
    """外の値（注釈が Any / record の値・他の object・代わりの型）の属性を、値の葉を写してから読む（Issue #242）。

    `getattr(value, name[, default])` と同じ値。ただし値が scalar の subclass なら基底型の値の属性を読む（subclass の
    `__getattribute__` / `__getattr__` / class の descriptor を呼ばない）。それ以外の object は自分の属性の仕組みで
    読む（外の code）。返す値は読んだ属性そのもの（中身は呼ぶ側が reader で読む）。
    """

    # 1 つの frame で読む（ref の層の hot path: Ghidra の API の object の読み）。判定は `exact_scalar` と同じ MRO の比較
    if issubclass(type(value), _SCALAR_BASES):
        value = exact_scalar(value)
    if default is _MISSING:
        return getattr(value, name)
    return getattr(value, name, default)


def method_of(value: Any, name: str, /) -> Any:
    """`value.name`（外の値の method を呼ぶ前の読み。呼ぶ側が `method_of(x, "m")(...)` と書く: 引数の評価と
    属性の読みの順序・例外は `x.m(...)` と同じ。Issue #242）。

    読み方: 名前は値の葉を写してから読む（`attribute_of`: scalar の subclass の `__getattribute__` / `__getattr__` /
    class の descriptor を呼ばない。基底型に無い名前は双子と同じく `AttributeError`）。
    返す値の保証: 無い（外の code。呼んだ結果は、比べる・hash する・真偽にする前に、呼ぶ側が reader で読む）。
    """

    if issubclass(type(value), _SCALAR_BASES):  # `attribute_of` と同じ読み（1 つの frame）
        value = exact_scalar(value)
    return getattr(value, name)


def defined_attribute(kind: type, name: str, default: Any = _MISSING) -> Any:
    """型 `kind` の MRO で `name` を最初に定義する class の名前空間の値（Issue #242）。

    読み方: MRO と各 class の名前空間を `type` の slot の descriptor で読む（`kind` の metaclass の
    `__getattribute__` / `__getattr__` を呼ばない）。返す値は名前空間にある object そのもの（descriptor の `__get__` を
    呼ばない: `type(x).__str__ is KeyError.__str__` のような同一性の判定に使う。組み込みの slot の wrapper と関数は
    class から読んだ値と同じ object）。定義が無ければ `default`、`default` も無ければ `AttributeError`。MRO の長さが
    `SCAN_LIMIT` を超える型は判定しない（`TypeError`: 成功にも「無い」にもしない）。
    """

    mro = _TYPE_MRO.__get__(kind)
    if not _within_scan(tuple.__len__(mro)):
        raise TypeError("the MRO of the type is beyond the scan limit")
    for klass in mro:
        found = _namespace_value(klass, name)
        if found is _AMBIGUOUS_NAME:
            raise TypeError(f"a class namespace holds a key that is not a builtin str (looking up {name!r})")
        if found is not _MISSING_DUNDER:
            return found
    if default is _MISSING:
        raise AttributeError(name)
    return default


def attribute(value: Any, name: str, default: Any = None) -> Any:
    """record の属性（instance の値。無ければ package の型の property。それ以外は `default`）。

    live な object の `__getattr__` / 上書きした `__getattribute__` / package の外の property は
    呼ばない（`default`）。class の属性（method・定数）は返さない。
    """

    state = instance_state(value, name, _ABSENT)
    if state is not _ABSENT:
        return state
    kind = type(value)
    descriptor = _type_lookup(kind, name, _ABSENT)
    if descriptor is _ABSENT:
        return default
    descriptor_kind = type(descriptor)
    if descriptor_kind is readable_property:
        getter = descriptor.fget
        # package の型の、package の code が `readable_property` で宣言した property（record の API と
        # して読んでよい値。静的な監査の root）だけを呼ぶ
        if type(getter) is types.FunctionType and package_code(getter.__code__) and package_type(kind):
            state = begin_activation(value, kind)  # 監査済みの code（J19 の root）: 外の code の後に型を確かめ直す
            try:
                return getter(value)
            finally:
                end_activation(state)
        return default
    if descriptor_kind is property:
        # 宣言していない property は呼ばない（その getter は bounded path の能力ではない）
        return default
    # class の定数（descriptor でない値: `__get__` を持たない型の値）はそのまま
    if _type_lookup(descriptor_kind, "__get__", _ABSENT) is _ABSENT:
        return descriptor
    return default


def set_state(value: Any, name: str, new: Any) -> None:
    """package の record の instance の値を書く（`setattr` の代わり。`__setattr__` / property の setter を呼ばない）。

    書ける場所は instance の `__dict__` か slot だけ。package の型が定義した `__setattr__`（record の
    不変条件の検査）は型の関数を直接呼ぶ。それ以外の `__setattr__` を持つ型・名前が property など
    data descriptor の値は `TypeError`（その値の code を呼ばない）。
    """

    kind = type(value)
    setter = type_attribute(kind, "__setattr__")
    if setter is not object.__setattr__:
        if (
            type(setter) is types.FunctionType and package_code(setter.__code__)
            and setter.__code__ in _STATE_SETTERS and package_type(kind)
        ):
            # `state_setter` で宣言した package の `__setattr__`（record の不変条件の検査）だけを呼ぶ
            with relying_on(value, kind):  # 監査済みの code（J19 の root）: 外の code の後に型を確かめ直す
                setter(value, name, new)
            return
        if type(setter) is types.WrapperDescriptorType and not (_TYPE_FLAGS.__get__(setter.__objclass__) & _HEAP_TYPE):
            # C で定義した組み込みの型の `__setattr__`（`types.SimpleNamespace` など。上書きできない）
            setter(value, name, new)
            return
        raise TypeError(f"{type_name(kind)} has its own __setattr__")
    descriptor = _type_lookup(kind, name, _ABSENT)
    if type(descriptor) is types.MemberDescriptorType:
        descriptor.__set__(value, new)
        return
    if descriptor is not _ABSENT and _type_lookup(type(descriptor), "__set__", _ABSENT) is not _ABSENT:
        raise TypeError(f"{name!r} of {type_name(kind)} is not plain instance state")
    holder = type_attribute(kind, "__dict__")
    holder_kind = type(holder)
    if (
        (holder_kind is types.GetSetDescriptorType or holder_kind is types.MemberDescriptorType)
        and _in_mro(holder.__objclass__, kind)
    ):
        state = holder.__get__(value, kind)
        # key が全部組み込みの `str` の dict にだけ書く（書くときの hash の比較で他の key の `__eq__` を
        # 呼ばない）
        if type(state) is dict:
            _admit_storage(dict.__len__(state), "an instance's __dict__")
            if _exact_str_raw(state):
                state[name] = new
                return
    raise TypeError(f"{type_name(kind)} has no instance state for {name!r}")


def has_attribute(value: Any, name: str) -> bool:
    """`attribute` が値を返すか（`hasattr` の代わり。`__getattr__` を呼ばない）。"""

    return attribute(value, name, _ABSENT) is not _ABSENT


# ---------------------------------------------------------------------------
# dataclass
# ---------------------------------------------------------------------------


def dataclass_field_names(value: Any) -> Optional[Tuple[str, ...]]:
    """dataclass の instance なら field の名前（`dataclasses.fields` と同じ順と規則）、それ以外は `None`。"""

    kind = type(value)
    if issubclass(kind, type):
        return None
    if not _plain_metatype(kind):
        return _dataclass_field_names(kind)
    # 型ごとに記録し、引くたびに表の中身を確かめる（`_DATACLASS_FIELD_NAMES` の extra: 今の表に従う。owner の固定とは別）
    known = _DATACLASS_FIELD_NAMES.get(kind, _ABSENT)
    if known is _ABSENT:
        known = _DATACLASS_FIELD_NAMES[kind] = _dataclass_field_names(kind)
    return known


#: 型ごとの `dataclass_field_names` の結果（dataclass でない型は `None`）
def _dataclass_table_state(kind: type) -> Tuple[Any, List[Any]]:
    """`__dataclass_fields__` の表の中身の状態（key と `Field` の identity と、`Field` の種類の slot の値の identity）。"""

    try:
        table = _type_lookup(kind, "__dataclass_fields__", None)
    except TypeError:
        return (), []
    if type(table) is not dict or not _within_scan(dict.__len__(table)):
        return (id(table),), [table]
    import dataclasses

    slot = _type_lookup(dataclasses.Field, "_field_type", None)
    items = tuple(dict.items(table))
    kinds = tuple(
        slot.__get__(field, dataclasses.Field) if type(field) is dataclasses.Field and slot is not None else None
        for _name, field in items
    )
    field_types = tuple(type(field) for _name, field in items)  # `Field` は heap type: `__class__` を変えられる
    return (
        (id(table), tuple(id(item) for pair in items for item in pair), tuple(map(id, kinds)), tuple(map(id, field_types))),
        [table, items, kinds, field_types],
    )


_DATACLASS_FIELD_NAMES = _TypeFactTable(_dataclass_table_state)


def _dataclass_field_names(kind: type) -> Optional[Tuple[str, ...]]:
    try:
        table = type_attribute(kind, "__dataclass_fields__")
    except TypeError:
        # 型を上限の中で読めない: dataclass とは確かめられない
        return None
    if type(table) is not dict or not _within_scan(dict.__len__(table)):
        return None
    import dataclasses

    # `dataclasses.fields` と同じ判定。表の中身も組み込みの型そのものだけ（`Field` の slot を
    # 型の descriptor で読む。偽の表の object の属性・`__getattr__` を呼ばない）
    field_type_slot = _type_lookup(dataclasses.Field, "_field_type", None)
    names = []
    for name, field_info in dict.items(table):
        if type(name) is not str or type(field_info) is not dataclasses.Field:
            return None
        if field_type_slot.__get__(field_info, dataclasses.Field) is dataclasses._FIELD:  # type: ignore[attr-defined]
            names.append(name)
    return tuple(names)


def dataclass_field_specs(kind: type) -> Optional[Tuple[Tuple[str, bool, bool], ...]]:
    """dataclass の field（`dataclasses.fields(kind)` と同じ順と規則）の `(名前, compare, repr)`。dataclass でない・表が
    組み込みの型そのものでない・`compare` / `repr` が組み込みの `bool` でない（真偽の読みが外の code を呼ぶ）なら `None`。

    呼ぶたびに表を読む（cache しない: 表をいつ固定するかは呼ぶ側が決める。owner は class ごとに最初の使用で固定する）。
    読みは型の名前空間と `Field` の slot の descriptor だけ（metaclass・`Field` の subclass の hook を呼ばない）。
    """

    try:
        table = _type_lookup(kind, "__dataclass_fields__", None)
    except TypeError:
        return None
    if type(table) is not dict or not _within_scan(dict.__len__(table)) or not _exact_str_raw(table):
        return None
    import dataclasses

    read = _FIELD_SLOTS
    if read is None:
        read = _field_slots()
    field_type, compare, shown = read
    holder = dataclasses.Field
    fields = tuple(dict.values(table))
    if not all(map(_IS, map(type, fields), itertools.repeat(holder))):
        return None
    names = tuple(dict.__iter__(table))
    kinds = tuple(map(field_type, fields, itertools.repeat(holder)))
    compared = tuple(map(compare, fields, itertools.repeat(holder)))
    printed = tuple(map(shown, fields, itertools.repeat(holder)))
    if not all(map(_IS, map(type, compared), itertools.repeat(bool))) or not all(
        map(_IS, map(type, printed), itertools.repeat(bool))
    ):
        return None
    marker = dataclasses._FIELD  # type: ignore[attr-defined]
    specs = tuple(
        (name, flag, visible)
        for name, field_kind, flag, visible in zip(names, kinds, compared, printed)
        if field_kind is marker
    )
    return specs


#: `dataclasses.Field` の slot の読み（`_field_type`・`compare`・`repr` の member descriptor の `__get__`）。最初の使用で読む
_FIELD_SLOTS: Optional[Tuple[Any, Any, Any]] = None


def _field_slots() -> Tuple[Any, Any, Any]:
    global _FIELD_SLOTS
    import dataclasses

    slots = tuple(_type_lookup(dataclasses.Field, name, None).__get__ for name in ("_field_type", "compare", "repr"))
    _FIELD_SLOTS = slots  # type: ignore[assignment]
    return slots  # type: ignore[return-value]


def class_namespace_value(klass: type, name: str, default: Any = None) -> Any:
    """class 自身の名前空間（MRO は辿らない）の `name` の値。無ければ `default`。組み込みの `str` でない key を持つ
    名前空間は `TypeError`（引きが key の `__eq__` を呼ぶ: 決めない）。metaclass の hook を呼ばない。"""

    found = _NamespaceReader(klass).value(name)
    if found is _AMBIGUOUS_NAME:
        raise TypeError(f"a class namespace holds a key that is not a builtin str (looking up {name!r})")
    return default if found is _MISSING_DUNDER else found


def field_value(value: Any, name: str) -> Any:
    """dataclass の field の値（instance の値だけ。field 名を property が上書きしていれば `TypeError`）。"""

    return instance_state(value, name)


# ---------------------------------------------------------------------------
# 容器
# ---------------------------------------------------------------------------


def builtin_mapping(item: Any) -> Any:
    """反復してよい組み込みの振る舞いの mapping ならそれを、そうでなければ `None`（安全の判定）。

    dict / OrderedDict とその subclass（`items` / `__iter__` / `__len__` / 真偽を上書きしないもの）と、
    それらを包む `MappingProxyType`（包んだ値を `gc.get_referents` で確かめる）。`OrderedDict` の系統は
    反復が key の hash で node を引くので、key の hash が組み込みの実装のものだけ（値の storage の読み:
    上限の外の意味は今の文脈の量の owner）。長さ・真偽だけなら `_builtin_length`（key を読まない）。
    """

    inner = _mapping_storage(item)
    if inner is None:
        return None
    if issubclass(type(inner), OrderedDict) and not _hash_safe_keys(inner):
        return None
    return item


def _mapping_storage(item: Any) -> Any:
    """組み込みの振る舞いの mapping（型の判定だけ。key は読まない）なら包んだ storage を、そうでなければ `None`。"""

    kind = type(item)
    if kind is dict or kind is OrderedDict:
        return item
    if kind is types.MappingProxyType:
        # 包んだ値を段ごとに辿る（段は値の storage の読み。再帰しない）
        read = _StorageRead(_PROXY_LAYERS)
        inner = item
        while type(inner) is types.MappingProxyType:
            read.admit(1)
            referents = gc.get_referents(inner)
            if len(referents) != 1:
                return None
            inner = referents[0]
        return inner if _mapping_storage(inner) is not None else None
    if not _builtin_behaviour(kind, _BUILTIN_DICTS, ("items", "__iter__", "__len__", "__bool__")):
        return None
    return item




def builtin_sequence(item: Any) -> bool:
    """組み込みの振る舞い（`__iter__` / `__len__` / `__getitem__` / 真偽）の list / tuple か（namedtuple を含む）。"""

    kind = type(item)
    if kind is tuple or kind is list:
        return True
    return _builtin_behaviour(kind, _SEQUENCE_BASES, ("__iter__", "__len__", "__getitem__", "__bool__"))


def builtin_items(item: Any) -> Any:
    """容器かどうか分からない値の要素の列: `None` なら `()`、組み込みの振る舞いの list / tuple ならそれ自身、
    それ以外（文字列・他の容器・object）なら `None`（読めない）。

    属性が容器か分からない値（注釈が `Any` の field・式の属性）を、外の型の `__bool__` / `__len__` / `__iter__` を
    呼ばずに読む入口（Issue #242）。読めない値を空の列にしない: 呼ぶ側は `None` を「判断できない」として扱う
    （中身を落として別の値と等しくしない）。要素は読まない（値として読むときは `exact_scalar` などで読む）。
    """

    if item is None:
        return ()
    return item if builtin_sequence(item) else None


def builtin_set(item: Any) -> bool:
    kind = type(item)
    if kind is frozenset or kind is set:
        return True
    return _builtin_behaviour(kind, _SET_BASES, ("__iter__", "__len__", "__bool__"))


#: `id(基底型の組)` → (組, その組の型ごとの事実の表)。組は module の定数（`_SEQUENCE_BASES` など）
_BUILTIN_BEHAVIOUR: Dict[int, Tuple[Tuple[type, ...], "_LookupFactTable"]] = {}


#: `_builtin_behaviour` の基底型の組（module の定数: 型の事実の表は key の組を identity で引く。呼ぶたびに組を作ると
#: 記録を引けない）
_SEQUENCE_BASES = (tuple, list)
_SET_BASES = (frozenset, set)


def _builtin_behaviour(kind: type, bases: Tuple[type, ...], names: Tuple[str, ...]) -> bool:
    """`kind` が `bases` のどれかの subclass で、`names` の method を上書きしていないか（型ごとに 1 度だけ）。"""

    # 基底型そのものと、どの基底型の subclass でもない型は、名前空間に依らず決まる（MRO だけ: 組み込みの型の
    # `__subclasscheck__` は型の MRO を C で読む）: 型の事実の表を引かない（引くたびの確かめを省く）
    base = None
    for candidate in bases:
        if kind is candidate:
            return True
        if base is None and issubclass(kind, candidate):
            base = candidate
    if base is None:
        return False
    if not _plain_metatype(kind):
        # metaclass が `__eq__` / `__hash__` を持つ型は cache の key にもしない（その code を呼ばない）
        return False
    table = _BUILTIN_BEHAVIOUR.get(id(bases))
    if table is None or table[0] is not bases:
        table = _BUILTIN_BEHAVIOUR[id(bases)] = (bases, _LookupFactTable())  # 基底型の組は module の定数（数は固定）
    return lookup_fact(table[1], kind, _same_behaviour, kind, base, names)


def _same_behaviour(kind: type, base: type, names: Tuple[str, ...]) -> bool:
    try:
        return all(type_attribute(kind, name) is type_attribute(base, name) for name in names)
    except TypeError:
        # 型を上限の中で読めない・組み込みでない key の名前空間: 組み込みの振る舞いとは確かめられない（その計算は
        # 記録しない: `_witnessed`）
        return False


def builtin_iterator(item: Any) -> bool:
    """組み込みの容器の iterator / dict の view か（中身を辿るのは組み込みの実装だけ）。`zip` そのものは、包んだ iterator が
    全部組み込みの容器の iterator のとき（`zip` の C の実装が組み込みの tuple を作るだけ。包んだ iterator は `zip` の
    `__reduce__`（C の実装）で読む: 値の code を呼ばない）。"""

    kind = type(item)
    if kind is range:
        return True
    if kind is zip:
        parts = zip.__reduce__(item)[1]
        if tuple.__len__(parts) > SCAN_LIMIT:
            return False
        for part in tuple.__iter__(parts):
            part_kind = type(part)
            # 包んだ iterator は組み込みの容器の iterator だけ（入れ子の `zip` は数えない）。tuple の iterator は identity で
            # 先に見る（型の集合へは metaclass を確かめてから: `builtin_iterator`）
            if part_kind is not _TUPLE_ITERATOR and (part_kind is zip or not builtin_iterator(part)):
                return False
        return True
    return _plain_metatype(kind) and (kind in _BUILTIN_ITERATOR_TYPES or kind in _BUILTIN_VIEW_TYPES)


def _plain_metatype(kind: type) -> bool:
    """型の hash・比較が組み込みの実装か（metaclass が `__eq__` / `__hash__` を上書きしない）。"""

    metatype = type(kind)
    if metatype is type:
        return True
    try:
        return (
            _type_lookup(metatype, "__eq__", None) is object.__eq__
            and _type_lookup(metatype, "__hash__", None) is object.__hash__
        )
    except TypeError:
        return False


def builtin_container(item: Any) -> bool:
    """反復してよい組み込みの振る舞いの容器か（`elements_of` と同じ判定: mapping は `builtin_mapping`）。
    長さ・真偽もその基底型の slot で読める。"""

    return builtin_sequence(item) or builtin_set(item) or builtin_mapping(item) is not None


def _builtin_length(item: Any) -> bool:
    """長さ・真偽を組み込みの slot で読んでよい容器か（`size` / `as_bool` の側。型の判定だけで key を
    読まない: 反復してよいかは `builtin_container` が確かめる）。"""

    return builtin_sequence(item) or builtin_set(item) or _mapping_storage(item) is not None


def size(item: Any) -> int:
    """組み込みの振る舞いの容器・文字列・bytes の長さ（基底型の `__len__`）。それ以外は `TypeError`。"""

    kind = type(item)
    if kind is str or kind is list or kind is tuple or kind is dict or kind is bytes:
        return len(item)
    text = str_value(item)
    if text is not NOT_PLAIN:
        return len(text)
    if builtin_sequence(item) or builtin_set(item):
        return len(item)
    storage = _mapping_storage(item)
    if storage is not None:
        # mapping の長さは storage の slot（`OrderedDict` も `dict` の storage を持つ。key は読まない）
        return dict.__len__(storage)
    raise TypeError(f"{type_name(kind)} has no builtin length")


def storage_extent(value: Any) -> Optional[Tuple[int, int]]:
    """組み込みの容器（subclass を含む）の (storage の要素の数, 包んだ `MappingProxyType` の段の数)。
    要素の数は基底型の slot で O(1)（値の code を実行せず、振る舞いが組み込みのままかも確かめない）。
    段は要素と別の量で、上限を超える鎖は上限 + 1 で辿るのを止める。組み込みの容器でなければ `None`。

    読む前に量を比べる owner（`core/read_limits`）の入口: 量の判定を安全の判定より先に行う。
    """

    layers = 0
    while type(value) is types.MappingProxyType:
        layers += 1
        if layers > SCAN_LIMIT:
            return 0, layers
        referents = gc.get_referents(value)
        if len(referents) != 1:
            return None
        value = referents[0]
    kind = type(value)
    for base in _STORAGE_BASES:
        if kind is base or _in_mro(base, kind):
            return base.__len__(value), layers
    return None


def storage_count(value: Any) -> Optional[int]:
    """`storage_extent` の要素の数（段が上限を超える鎖は段の数: どちらも同じ上限と比べる）。組み込みの
    容器でなければ `None`。"""

    extent = storage_extent(value)
    if extent is None:
        return None
    count, layers = extent
    return layers if layers > SCAN_LIMIT else count


#: storage の数を基底型の slot で読む容器の型（`OrderedDict` は `dict` の storage）
_STORAGE_BASES = (dict, list, tuple, set, frozenset)


def _mapping_base(mapping: Any) -> type:
    """組み込みの振る舞いの mapping の基底型（その型の method を名指しで呼ぶ。`__getattribute__` を通らない）。"""

    if builtin_mapping(mapping) is None:
        raise TypeError(f"{type_name(type(mapping))} is not a builtin mapping")
    kind = type(_unwrapped(mapping))
    return OrderedDict if issubclass(kind, OrderedDict) else dict


def _unwrapped(mapping: Any) -> Any:
    """`MappingProxyType` なら包んだ mapping（proxy の method は包んだ値の method を名前で呼ぶので使わない）。"""

    read = _StorageRead(_PROXY_LAYERS)
    while type(mapping) is types.MappingProxyType:
        read.admit(1)
        mapping = gc.get_referents(mapping)[0]
    return mapping


def items_of(mapping: Any) -> Iterator[Tuple[Any, Any]]:
    """組み込みの振る舞いの mapping の (key, 値)。それ以外は `TypeError`。"""

    if type(mapping) is dict:
        return iter(dict.items(mapping))
    # `OrderedDict` は key の hash が組み込みの実装のものだけ（`builtin_mapping` が確かめた）
    return iter(_mapping_base(mapping).items(_unwrapped(mapping)))


def values_of(mapping: Any) -> Iterator[Any]:
    """組み込みの振る舞いの mapping の値。それ以外は `TypeError`。"""

    if type(mapping) is dict:
        return iter(dict.values(mapping))
    return iter(_mapping_base(mapping).values(_unwrapped(mapping)))


def _plain_keys(raw: dict) -> bool:
    """storage の key が全部 plain な値（`_plain_key`。hash・比較が組み込みの実装）か（隠れた読み: key で
    引く前の確かめ）。key の数と、key の tuple の node の和は別の量で、それぞれを上限と比べる。"""

    _admit_storage(dict.__len__(raw), "a mapping's keys")
    if _exact_str_raw(raw):
        # よくある形（instance の `__dict__`・record）: 型を C の比較だけで確かめる（key ごとの判定を省く）
        return True
    nodes = None
    for key in dict.__iter__(raw):
        if nodes is None and type(key) is tuple:
            nodes = _key_nodes()
        if not _plain_key(key, nodes):
            return False
    return True


def _hash_safe_keys(raw: dict) -> bool:
    """storage の key の hash・比較が全部組み込みの実装か（組み込みの scalar・hash を上書きしない
    scalar の subclass・組み込みのままの enum・それらの tuple）。storage を `dict.__iter__` で読む。
    反復の確かめ（`builtin_mapping`）: key の数と key の tuple の node の和は別の量。"""

    _admit_storage(dict.__len__(raw), "a mapping's keys", traversal=True)
    if _exact_str_raw(raw):
        return True
    nodes = None
    for key in dict.__iter__(raw):
        if nodes is None and type(key) is tuple:
            nodes = _key_nodes(traversal=True)
        if not _hash_safe_key(key, nodes):
            return False
    return True


def hash_safe_key(key: Any) -> bool:
    """dict の key として新しい dict へ置いても値の code を呼ばないか（hash・比較が組み込みの実装）。"""

    return _hash_safe_key(key)


def _hash_safe_key(key: Any, read: Optional["_StorageRead"] = None) -> bool:
    kind = type(key)
    if kind is str or kind is int or key is None or kind is bool or kind is float:
        return True
    # key の tuple の node（tuple の要素）は値の storage の読み（上限の外は「安全でない」でなく量）。
    # mapping の key の判定では、その走査の node の読み（`read`: 要素の数とは別の量）へ足す
    if read is None:
        read = _key_nodes()
    pending = [key]
    while pending:
        item = pending.pop()
        kind = type(item)
        if item is None or kind is str or kind is int or kind is bool or kind is float:
            continue
        if kind is tuple:
            read.admit(tuple.__len__(item))
            pending.extend(item)
            continue
        if not (builtin_hashed_scalar(item) or builtin_enum(item)):
            return False
    return True


def merged_mappings(*mappings: Any) -> dict:
    """組み込みの振る舞いの mapping（key は組み込みの `str` だけ）を順に重ねた新しい dict。

    key を hash・比較するのは組み込みの `str` の実装だけ（上書きした `__hash__` / `__eq__` を
    呼ばない）。key が `str` でない mapping は `TypeError`。
    """

    merged: dict = {}
    for mapping in mappings:
        _admit_storage(size(mapping), "a merged mapping", traversal=True)
        for key, value in items_of(mapping):
            if type(key) is not str:
                raise TypeError(f"mapping key {type_name(type(key))} is not a builtin str")
            merged[key] = value
    return merged


def copied_container(value: Any) -> Any:
    """dict / list の（subclass を含む）値の、基底型の slot で写した組み込みの dict / list。

    上書きした `items` / `__iter__` / `keys` / `copy` などは呼ばない（基底型の storage を読む）。
    dict の key は plain な値（`_plain_key`）だけ（新しい dict に入れるときにその `__hash__` を
    呼ぶため）で、そうでなければ `TypeError`。dict / list の値でなければ `NOT_PLAIN`。
    """

    kind = type(value)
    if issubclass(kind, dict):
        # storage の key を先に確かめる（`dict.__iter__` は storage を読む。key の code は呼ばない）
        # 写しは写す要素の反復（確かめも反復の一部）。key の tuple の node は別の量
        _admit_storage(dict.__len__(value), "a copied mapping", traversal=True)
        keys = tuple(dict.__iter__(value))
        nodes = None
        for key in keys:
            if nodes is None and type(key) is tuple:
                nodes = _key_nodes(traversal=True)
            if not _plain_key(key, nodes):
                raise TypeError(f"mapping key {type_name(type(key))} is not a plain key")
        base = OrderedDict if issubclass(kind, OrderedDict) else dict
        return dict(base.items(value))
    if issubclass(kind, list):
        _admit_storage(list.__len__(value), "a copied list", traversal=True)
        return list.copy(value)
    return NOT_PLAIN


def lookup(mapping: Any, key: Any, default: Any = None) -> Any:
    """組み込みの振る舞いの mapping の `key` の値（基底型の `get`）。`key` は plain な値に限る。

    `key` の `__hash__` / `__eq__` を呼ぶので、key は組み込みの scalar か、その tuple だけ。
    """

    if not _plain_key(key):
        raise TypeError(f"{type_name(type(key))} is not a plain mapping key")
    if type(mapping) is dict:
        raw = mapping
    else:
        # 型の判定だけ（反復の確かめ（key の hash）は要らない: 引くのは基底型の `dict.get` で、
        # 置かれた key は下で plain な値と確かめてから hash で引く。数える前に key を辿らない）
        if _mapping_storage(mapping) is None:
            raise TypeError(f"{type_name(type(mapping))} is not a builtin mapping")
        raw = _unwrapped(mapping)
    # 隠れた読み（key で引く前の key の確かめ）: 要素の数を先に上限と比べる
    if _plain_keys(raw):
        return dict.get(raw, key, default)
    # 組み込みでない key（`__eq__` を上書きした str の subclass など）を持つ mapping: hash で引くと
    # その key の `__eq__` を呼び得る。plain な key だけを組み込みの比較で探す
    # （`_plain_keys` と別の 2 度目の走査として数える。key の tuple の node は別の量）
    _admit_storage(dict.__len__(raw), "a mapping read by key")
    nodes = None
    for stored, value in dict.items(raw):
        if nodes is None and type(stored) is tuple:
            nodes = _key_nodes()
        if _plain_key(stored, nodes) and stored == key:
            return value
    return default


def _plain_key(key: Any, read: Optional["_StorageRead"] = None) -> bool:
    """組み込みの scalar か、その tuple か（node は値の storage の読み。再帰しない。mapping の key の
    判定では、その走査の node の読み `read` へ足す）。"""

    kind = type(key)
    if kind is str or kind is int or key is None or kind is bool or kind is float:
        return True
    if read is None:
        read = _key_nodes()
    pending = [key]
    while pending:
        item = pending.pop()
        kind = type(item)
        if item is None or kind is str or kind is int or kind is bool or kind is float:
            continue
        if kind is tuple:
            read.admit(tuple.__len__(item))
            pending.extend(item)
            continue
        return False
    return True


def package_generator(value: Any) -> bool:
    """package の code の generator か（中身を作るのは package の code だけ）。"""

    return type(value) is types.GeneratorType and package_code(value.gi_code)


def elements_of(values: Any) -> Iterator[Any]:
    """組み込みの振る舞いの列・集合・iterator・package の generator の要素。それ以外は `TypeError`。"""

    if builtin_sequence(values) or builtin_set(values) or builtin_iterator(values) or package_generator(values):
        return iter(values)
    if builtin_mapping(values) is not None:
        return iter(values)
    raise TypeError(f"{type_name(type(values))} is not a builtin iterable")


__all__ = [
    "audited_region",
    "outside_audit",
    "region_cache",
    "value_code_boundary",
    "VALUE_CODE_BOUNDARIES",
    "reliance",
    "relying_on",
    "begin_activation",
    "begin_reliance",
    "end_reliance",
    "end_activation",
    "audited_entry",
    "package_instance",
    "read_pair",
    "exact_scalar",
    "exact_tree",
    "scalar_bool",
    "builtin_items",
    "scalar_int",
    "scalar_int_or",
    "scalar_text",
    "StorageBeyondReadBound",
    "metered_storage_reads",
    "register_storage_meter",
    "register_unmetered_read_owner",
    "register_undecidable_owner",
    "class_defines",
    "undecidable",
    "signalled_storage_reads",
    "fixed_bound_reads",
    "fixed_reads",
    "storage_extent",
    "storage_count",
    "SCAN_LIMIT",
    "NOT_PLAIN",
    "PACKAGE_DIR",
    "package_code",
    "package_file",
    "package_generator",
    "package_function",
    "package_type",
    "trust_code_directory",
    "trusted_hash",
    "LookupFactTable",
    "lookup_fact",
    "plain_attribute_lookup",
    "dataclass_field_specs",
    "class_namespace_value",
    "as_bool",
    "as_float",
    "as_int",
    "as_repr",
    "as_str",
    "builtin_enum",
    "readable_property",
    "builtin_hashed_scalar",
    "hash_safe_key",
    "state_setter",
    "copied_container",
    "attribute",
    "attribute_of",
    "method_of",
    "holds_scalar_subclass",
    "exception_text",
    "verified_tree_holder",
    "exact_tree_in",
    "scalar_repr",
    "defined_attribute",
    "builtin_container",
    "builtin_iterator",
    "builtin_mapping",
    "builtin_sequence",
    "builtin_set",
    "dataclass_field_names",
    "elements_of",
    "enum_name",
    "enum_value",
    "field_value",
    "float_value",
    "has_attribute",
    "instance_state",
    "int_value",
    "is_enum",
    "is_kind",
    "json_scalar",
    "items_of",
    "lookup",
    "merged_mappings",
    "plain_scalar",
    "set_state",
    "size",
    "str_value",
    "type_attribute",
    "type_module",
    "type_name",
    "values_of",
]
