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

import gc
import itertools
import operator
import os
import sys
import threading
import types
import contextvars
from collections import OrderedDict
from enum import Enum
from typing import Any, Iterator, NoReturn, Optional, Tuple

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
            (_PACKAGE_TYPES if table is state.provisional_types else _TRUSTED_BODIES)[key] = True


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

    if type(path) is not str or not os.path.isabs(path):
        # 相対の file 名（`<string>`・cwd に依る名前）は package の code ではない
        return False
    known = _PACKAGE_FILES.get(path)
    if known is None:
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


_PACKAGE_TYPES: dict = {}


def package_type(kind: type) -> bool:
    """`kind` とその MRO の class 文で作った型（heap type）の中身が、どれも信頼する code とデータだけか。

    package の外で package の型を継承した型（`__getattribute__` / property / descriptor / 関数を
    外の code で足した型）は信頼しない: 型の MRO から引いた package の関数を呼んでも、その中の
    `self.x` / `self.f()` が外の code を呼び得る。heap type ごとに `__dict__` の値を **許した種類
    だけ** に限る（`_trusted_namespace_value`）。中身を足さない subclass（空の body）は信頼する
    （足した code が無い）。組み込みの型（C で定義した型）はそのまま信頼する。
    """

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
        # 最も外の判定: 前の判定の状態を持ち越さない
        state.assumed, state.cut = NESTING_LIMIT + 1, False
    outer_assumed, outer_cut = state.assumed, state.cut
    state.assumed, state.cut = NESTING_LIMIT + 1, False
    state.active[kind] = depth
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
        _PACKAGE_TYPES[kind] = known
    elif known is False:
        # 楽観的な仮定の下でも信頼しない: 確定（自分を仮定した仮の判定は仮定が崩れたので捨てる）
        _settle(state, depth, commit=False)
        _PACKAGE_TYPES[kind] = False
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
        holder = type(item)
        if holder is types.MethodType:
            item = item.__func__
            holder = type(item)
        if holder is types.FunctionType:
            verdict = _function_verdict(item, generated=generated)
            if verdict is False:
                return False
            if verdict is None:
                cells = item.__closure__ or ()
                if not _within_scan(scan.used + len(pending) + tuple.__len__(cells)):
                    return False
                for cell in cells:
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
        wrapped = instance_state(item, "__wrapped__", _ABSENT) if _plain_metatype(holder) else _ABSENT
        if holder is _LRU_WRAPPER and wrapped is not _ABSENT:
            # `functools.lru_cache` の wrapper（C）: 包んだ関数を信頼するものだけ
            pending.append(wrapped)
            continue
        if not _inert_value(item):
            return False
    return True


_LRU_WRAPPER = type(__import__("functools").lru_cache(maxsize=None)(len))


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
        _TRUSTED_BODIES[klass] = known
    else:
        _provisionally(state, state.provisional_bodies, klass, assumed)
    return known


#: class ごとの `_trusted_class_body` の結果（hash・比較が組み込みの実装の metaclass の class だけ）
_TRUSTED_BODIES: dict = {}


def _trusted_class_body_uncached(klass: type) -> bool:
    # 型の信頼の判定は文脈に依らない（class ごとに cache する）: class の中の値の storage の読みは作業量で
    # 数えず限界も記録せず、上限の外は「確かめられない」= 信頼しない（量の信号を型の判定の答えにする場所）
    with signalled_storage_reads():
        try:
            return _trusted_class_body_values(klass)
        except StorageBeyondReadBound:
            return False


def _trusted_class_body_values(klass: type) -> bool:
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
    """`type_attribute` と同じ（無ければ `missing`。値が `None` の属性と区別する）。"""

    mro = _TYPE_MRO.__get__(kind)
    _require_scan(tuple.__len__(mro), "a type's MRO")
    plain = _STR_MROS.get(kind) if type(kind) is type else None
    if plain is None:
        plain = all(
            _str_namespace(klass, _TYPE_DICT.__get__(klass)) for klass in mro
        )
        if type(kind) is type:
            _STR_MROS[kind] = plain
    if plain:
        # MRO の class の `__dict__` の key が全部組み込みの `str`（型ごとに 1 度確かめた）: hash で引く
        for klass in mro:
            namespace = _TYPE_DICT.__get__(klass)
            if name in namespace:
                return namespace[name]
        return missing
    # 組み込みの `str` でない key を持つ namespace は key を 1 つずつ比べる: その数の和を MRO 全体で
    # 上限と比べてから辿る（class ごとに上限まで辿ると MRO × namespace になる）
    scanned = 0
    for klass in mro:
        namespace = _TYPE_DICT.__get__(klass)
        if not _str_namespace(klass, namespace):
            scanned += dict.__len__(_unwrapped(namespace))
    _require_scan(scanned, "the non-str namespaces of a type's MRO")
    for klass in mro:
        namespace = _TYPE_DICT.__get__(klass)
        if _str_namespace(klass, namespace):
            if name in namespace:
                return namespace[name]
        else:
            found = _scan_str_key(_unwrapped(namespace), name, _ABSENT)
            if found is not _ABSENT:
                return found
    return missing


#: 型の MRO の class の `__dict__` の key が全部組み込みの `str` か（metaclass が `type` の型ごと）
_STR_MROS: dict = {}
#: class の `__dict__` の key が全部組み込みの `str` か（class ごと。class 文・`setattr` の名前は
#: 組み込みの `str` だが、`type(name, bases, ns)` の `ns` の key はそのまま残る）
_STR_NAMESPACES: dict = {}


def _str_namespace(klass: type, namespace: Any) -> bool:
    metatype = type(klass)
    if metatype is not type and not _plain_metatype(klass):
        # hash・比較を上書きした metaclass の型は cache の key にしない（毎回 storage を読む）
        return _exact_str_keys(_unwrapped(namespace))
    known = _STR_NAMESPACES.get(klass)
    if known is None:
        known = _STR_NAMESPACES[klass] = _exact_str_keys(_unwrapped(namespace))
    return known


def _exact_str_keys(raw: dict) -> bool:
    """**型の** namespace の key が全部組み込みの `str` か（固定の上限の外は False: 型の信頼の判定の側）。"""

    if not _within_scan(dict.__len__(raw)):
        return False
    return _exact_str_raw(raw)


def _exact_str_raw(raw: dict) -> bool:
    """dict の storage の key が全部組み込みの `str` か（`dict.__iter__` は storage を読む。key の
    `__hash__` / `__eq__` を呼ばない。型は identity で比べる）。数は呼ぶ側が先に比べる（型の上限か値の読み）。"""

    return all(map(_IS, map(type, dict.__iter__(raw)), _REPEAT_STR))


def _scan_str_key(raw: dict, name: str, missing: Any) -> Any:
    """**型の** namespace で組み込みの `str` でない key を持つものの `name` の値（固定の上限の外は `TypeError`）。"""

    _require_scan(dict.__len__(raw), "a mapping read by key")
    return _str_key_value(raw, name, missing)


def _str_key_value(raw: dict, name: str, missing: Any) -> Any:
    """組み込みの `str` でない key を持つ dict の `name` の値（組み込みの `str` の key だけを
    組み込みの比較で探す。他の key の `__eq__` を呼ばない）。数は呼ぶ側が先に比べる。"""

    for key, value in dict.items(raw):
        if type(key) is str and str.__eq__(key, name):
            return value
    return missing


_TYPE_NAME = type.__dict__["__name__"]


def type_name(kind: type) -> str:
    """型の `__qualname__`（metaclass の property を通らない組み込みの slot で読む）。"""

    return _TYPE_QUALNAME.__get__(kind)


def type_module(kind: type) -> str:
    return _TYPE_MODULE.__get__(kind)


def is_kind(value: Any, base: type) -> bool:
    """`value` の型が `base` の subclass か（`isinstance` の代わり。`__class__` を読まない）。"""

    return issubclass(type(value), base)


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
        return float.__float__(value)
    if issubclass(kind, str):
        return str.__str__(value)
    return NOT_PLAIN


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


def exact_scalar(value: Any) -> Any:
    """scalar の subclass（JPype の `JInt` / `JLong` / `JDouble` など、組み込みの scalar の型を継承する外の
    runtime の型）を、基底型の値へ写す（写し方は `plain_scalar` が唯一の owner）。

    基底型の slot で読む（subclass の `__int__` / `__str__` を呼ばない）。値と意味（整数値・文字列）は変えず、
    JSON・digest・式の文字列が読む基底型の値と同じ。bool・enum の member・scalar でない値はそのまま返す
    （Issue #235: 意味の値の scalar を組み込みの型そのものにする入口が使う）。
    """

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


def scalar_text(value: Any) -> str:
    """`str(value)` と同じ値。scalar の subclass は基底型の値にしてから文字列にする（`exact_scalar`）。

    subclass の `__str__` / `__repr__` を呼ばない。それ以外は `str()` のまま（Issue #242、`scalar_int` と同じ）。
    """

    if type(value) is str:
        return value
    return str(exact_scalar(value))


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
        known = _BUILTIN_HASHED.get(kind)
        if known is None:
            known = _BUILTIN_HASHED[kind] = _builtin_hashed_type(kind)
        return known
    return _plain_metatype(kind) and _builtin_hashed_type(kind)


#: 型ごとの `builtin_hashed_scalar` の結果（metaclass が `type` の型だけ）
_BUILTIN_HASHED: dict = {}


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
_BUILTIN_ENUM_TYPES: dict = {}


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
    )


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

    known = _DICT_HOLDERS.get(kind, _ABSENT) if type(kind) is type else _ABSENT
    if known is _ABSENT:
        holder = type_attribute(kind, "__dict__")
        holder_kind = type(holder)
        known = holder if (
            (holder_kind is types.GetSetDescriptorType or holder_kind is types.MemberDescriptorType)
            and _in_mro(holder.__objclass__, kind)
        ) else None
        if type(kind) is type:
            _DICT_HOLDERS[kind] = known
    return known


_DICT_HOLDERS: dict = {}


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
    offset_holder = _dict_holder(kind)
    if offset_holder is not None:
        state = offset_holder.__get__(value, kind)
        if type(state) is dict:
            # key が全部組み込みの `str` のときだけ hash で引く（`setattr(o, K("x"), v)` の key の
            # `__eq__` を呼ばない）。そうでなければ組み込みの `str` の key だけを探す。instance の
            # 状態は値の storage（数は値の読みとして比べる）
            _admit_storage(dict.__len__(state), "an instance's __dict__")
            if _exact_str_raw(state):
                if name in state:
                    return state[name]
            else:
                found = _str_key_value(state, name, _ABSENT)
                if found is not _ABSENT:
                    return found
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
            return getter(value)
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
    # 型ごとに 1 度だけ（field の表は class を作るときに決まる）
    known = _DATACLASS_FIELD_NAMES.get(kind, _ABSENT)
    if known is _ABSENT:
        known = _DATACLASS_FIELD_NAMES[kind] = _dataclass_field_names(kind)
    return known


#: 型ごとの `dataclass_field_names` の結果（dataclass でない型は `None`）
_DATACLASS_FIELD_NAMES: dict = {}


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
    return _builtin_behaviour(kind, (tuple, list), ("__iter__", "__len__", "__getitem__", "__bool__"))


def builtin_set(item: Any) -> bool:
    kind = type(item)
    if kind is frozenset or kind is set:
        return True
    return _builtin_behaviour(kind, (frozenset, set), ("__iter__", "__len__", "__bool__"))


_BUILTIN_BEHAVIOUR: dict = {}


def _builtin_behaviour(kind: type, bases: Tuple[type, ...], names: Tuple[str, ...]) -> bool:
    """`kind` が `bases` のどれかの subclass で、`names` の method を上書きしていないか（型ごとに 1 度だけ）。"""

    if not _plain_metatype(kind):
        # metaclass が `__eq__` / `__hash__` を持つ型は cache の key にもしない（その code を呼ばない）
        return False
    key = (kind, bases)
    known = _BUILTIN_BEHAVIOUR.get(key)
    if known is None:
        known = False
        for base in bases:
            if issubclass(kind, base):
                try:
                    known = all(type_attribute(kind, name) is type_attribute(base, name) for name in names)
                except TypeError:
                    # 型を上限の中で読めない: 組み込みの振る舞いとは確かめられない
                    known = False
                break
        _BUILTIN_BEHAVIOUR[key] = known
    return known


def builtin_iterator(item: Any) -> bool:
    """組み込みの容器の iterator / dict の view か（中身を辿るのは組み込みの実装だけ）。"""

    kind = type(item)
    if kind is range:
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
    "exact_scalar",
    "scalar_int",
    "scalar_text",
    "StorageBeyondReadBound",
    "metered_storage_reads",
    "register_storage_meter",
    "register_unmetered_read_owner",
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
