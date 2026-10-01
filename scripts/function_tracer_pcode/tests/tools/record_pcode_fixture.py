# -*- coding: utf-8 -*-
"""実 Ghidra の P-code / API surface を ``recorded-pcode-fixture-v1`` へ記録する。

PyGhidra が必要（コンテナ内で実行する）。記録は **再生と同じ production path**
で行う: production connector 付きの
``EquivalenceChecker(analyzer_factory=..., identical_fast_path=...)`` +
``activate_process_worker_execution_authority_deployment`` を付けた
``check_from_binaries`` を、実 Ghidra ``Program`` を Python recording proxy で
包んで走らせる。``ReturnAnalyzer`` を単独で回すことはしない。

Java / Python の境界:

* proxy は JPype object を包み、``__getattr__`` で実 member を取り、戻り値を
  再帰的に包む。Java primitive / String は JPype が Python 値へ変換した時点の
  値をそのまま記録する（proxy で包み直さない）。
* ``DecompInterface.openProgram()`` は実 ``Program`` を要求する（JPype の型検査
  で proxy は渡せない）ので、記録器が実 Program で ``DecompInterface`` を作り
  ``openProgram(real_program)`` して、:class:`RecordingDecompiler` を DI (a)
  ``ReturnAnalyzer(program_proxy, decompiler=...)`` に注入する。実 decompiler の
  破棄は記録器の ``finally`` が持つ。
* object の同一性は Java の ``IdentityHashMap``、``==`` の同値類は Java の
  ``HashMap``（= Java 側の ``equals`` / ``hashCode``）で決める。再生器は同じ
  同値類 id を使うので、``==`` / ``hash`` の意味が record と replay で一致する。

記録の 2 層:

* HighFunction 系（:data:`IR_SATURATION_KINDS`）は、production が**実際に要求
  した member 名**をその kind の全 object へ飽和させる（同じ kind の別 object
  が別経路で読まれても未記録にならない）。API 名を先回りで作らない。
* Program / Memory / Listing / SymbolTable / FunctionManager / DataTypeManager
  などは要求駆動のまま増やす。
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Tuple

REPO_ROOT = Path(__file__).resolve().parents[4]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.function_tracer_pcode.tests.fixtures.pcode import schema as fixture_schema
from scripts.function_tracer_pcode.tests.fixtures.pcode.schema import (
    IDENTITY_DERIVED_METHODS,
    IdentityContractViolation,
    IdentitySurrogateLedger,
    MEMBER_ABSENT,
    MEMBER_METHOD,
    MEMBER_VALUE,
    RECORDED_PCODE_FIXTURE_SCHEMA,
    RECORDER_VERSION,
    VALUE_BOOL,
    VALUE_BYTES,
    VALUE_FLOAT,
    VALUE_IDENTITY,
    VALUE_INT,
    VALUE_LIST,
    VALUE_NONE,
    VALUE_REF,
    VALUE_STR,
    ObjectRef,
    attr_key,
    call_key,
    is_recordable_member,
)
from scripts.function_tracer_pcode.tests.fixtures.pcode.recorded_program import (
    recorded_analyzer_factory,
)
from scripts.function_tracer_pcode.tests.fixtures.pcode.snapshot import (
    AnalysisSnapshotCollector,
    check_snapshot,
)
from scripts.function_tracer_pcode.authority.seal_work import SealWorkBudget

#: 飽和記録の対象にする Java class の単純名。**1 case の end-to-end で実際に
#: HighFunction から辿れた kind だけを入れる**（API 名も kind も先回りしない）。
IR_SATURATION_KINDS = frozenset({
    "HighFunction",
    "PcodeBlockBasic",
    "PcodeOpAST",
    "VarnodeAST",
    "HighLocal",
    "HighParam",
    "HighGlobal",
    "HighOther",
    "HighConstant",
    "LocalSymbolMap",
    "HighSymbol",
    "MappedEntry",
    "DynamicEntry",
    "SequenceNumber",
    "FunctionPrototype",
})

#: 飽和で index を回す accessor と、その件数 API。production がその kind へ
#: 実際に要求した組み合わせだけを置く。
INDEXED_ACCESSORS = (
    ("getInput", "getNumInputs"),
    ("getIn", "getInSize"),
    ("getOut", "getOutSize"),
)

#: 飽和の安全弁（index accessor の暴走を検出する。超えたら記録を失敗させる）。
MAX_SATURATION_INDEX = 4096

#: 飽和が固定点に達するまでに許す周回数。新しい観測が増えなくなれば終わるので
#: 通常は数周で止まる。超えたら（= 何かが毎周回 observation を作り続けている）
#: 黙って回り続けず記録を失敗させる。
MAX_SATURATION_PASSES = 64


class RecordingError(RuntimeError):
    pass


def _java_class_name(value: Any) -> str:
    java_class = getattr(type(value), "class_", None)
    if java_class is not None:
        try:
            return str(java_class.getName())
        except Exception:
            pass
    return type(value).__name__


def _simple_name(kind: str) -> str:
    return kind.rsplit(".", 1)[-1].rsplit("$", 1)[-1]


class Recorder:
    """1 side 分の記録状態（object 表・同一性・同値類）。"""

    def __init__(self, jpype: Any, side: str) -> None:
        self._jpype = jpype
        self.side = side
        # identity 由来の raw 値を、関係を保ったまま surrogate へ写す台帳。
        self.identity_ledger = IdentitySurrogateLedger(side)
        self._Integer = jpype.JClass("java.lang.Integer")
        self._identity = jpype.JClass("java.util.IdentityHashMap")()
        self._equality = jpype.JClass("java.util.HashMap")()
        self._entries: List[Dict[str, Any]] = []
        # index -> {member key: (method name, 実引数)}。飽和で同値類の兄弟へ
        # 同じ要求を出し直すために、key だけでなく実引数も持つ。
        self._calls: List[Dict[str, Any]] = []
        self._proxies: List["RecordingProxy"] = []
        # 記録中に Java object を生かしておくための強参照（proxy 表と対応）。
        self._reals: List[Any] = []
        self._next_eq_group = 0
        self.stateful_members: List[str] = []

    # -- object 表 ----------------------------------------------------------

    def object_id(self, index: int) -> str:
        return "o{}".format(index)

    def entry(self, index: int) -> Dict[str, Any]:
        return self._entries[index]

    def _eq_group(self, value: Any, fallback: int) -> int:
        try:
            existing = self._equality.get(value)
            if existing is not None:
                return int(existing)
            group = self._next_eq_group
            self._next_eq_group += 1
            self._equality.put(value, self._Integer(group))
            return group
        except Exception:
            # ``hashCode`` / ``equals`` が使えない object は identity 同値類。
            return -(fallback + 1)

    def register_root(self, value: Any, proxy_class) -> "RecordingProxy":
        """``proxy_for`` を通さずに作る root proxy（記録用 decompiler）を登録する。"""

        existing = self._identity.get(value)
        if existing is not None:
            return self._proxies[int(existing)]
        index = len(self._entries)
        proxy = proxy_class(self, index, value)
        self._entries.append({
            "kind": _java_class_name(value),
            "eq_group": self._eq_group(value, index),
            "observations": {},
        })
        self._calls.append({})
        self._proxies.append(proxy)
        self._reals.append(value)
        self._identity.put(value, self._Integer(index))
        return proxy

    def proxy_for(self, value: Any) -> "RecordingProxy":
        existing = self._identity.get(value)
        if existing is not None:
            return self._proxies[int(existing)]
        index = len(self._entries)
        entry: Dict[str, Any] = {
            "kind": _java_class_name(value),
            "eq_group": self._eq_group(value, index),
            "observations": {},
        }
        proxy = RecordingProxy(self, index, value)
        self._calls.append({})
        self._entries.append(entry)
        self._proxies.append(proxy)
        self._reals.append(value)
        self._identity.put(value, self._Integer(index))
        return proxy

    # -- 値の取り込み -------------------------------------------------------

    def capture(self, value: Any) -> Tuple[Any, Mapping[str, Any]]:
        """実 API の戻り値を (production へ返す値, 記録用 tagged) にする。"""

        if value is None:
            return None, {"kind": VALUE_NONE}
        if isinstance(value, RecordingProxy):
            return value, {"kind": VALUE_REF, "id": value._rec_id}
        if isinstance(value, bool):
            return bool(value), {"kind": VALUE_BOOL, "value": bool(value)}
        if isinstance(value, int):
            projected = int(value)
            return projected, {"kind": VALUE_INT, "value": projected}
        if isinstance(value, float):
            projected = float(value)
            return projected, {"kind": VALUE_FLOAT, "value": repr(projected)}
        if isinstance(value, str):
            projected = str(value)
            return projected, {"kind": VALUE_STR, "value": projected}
        if isinstance(value, (bytes, bytearray)):
            projected_bytes = bytes(value)
            return projected_bytes, {
                "kind": VALUE_BYTES, "value": projected_bytes.hex(),
            }
        if isinstance(value, (list, tuple)):
            values = []
            tagged = []
            for item in value:
                item_value, item_tag = self.capture(item)
                values.append(item_value)
                tagged.append(item_tag)
            return values, {"kind": VALUE_LIST, "items": tagged}
        proxy = self.proxy_for(value)
        return proxy, {"kind": VALUE_REF, "id": proxy._rec_id}

    def key_arg(self, value: Any) -> Any:
        if isinstance(value, RecordingProxy):
            return ObjectRef(
                value._rec_id, self._entries[value._rec_index]["eq_group"]
            )
        if isinstance(value, (list, tuple)):
            return [self.key_arg(item) for item in value]
        if value is None or isinstance(value, (bool, int, float, str, bytes, bytearray)):
            return value
        raise RecordingError(
            "recorded call argument type is outside the fixture schema: "
            + _java_class_name(value)
        )

    def recorded_observation(self, index: int, member_key: str) -> Any:
        """すでに記録済みの観測（無ければ ``None``）。

        状態を持つ API を飽和のために呼び直さないために使う。
        """

        observations = self._entries[index]["observations"].get(member_key)
        if not observations:
            return None
        return observations[0]

    def observation_count(self) -> int:
        """記録済み観測の総数（飽和の進捗判定に使う単調増加量）。

        これが進捗の指標として成立するのは、飽和の**すべての**経路
        （equality-class / IR-kind / index accessor の件数 API）が
        :meth:`saturation_is_settled` を通り、settled な member を二度と
        試さないから。1 つでも迂回すると、失敗の観測を毎周回積むことで
        「偽の進捗」を作り、固定点に到達しなくなる。
        """

        return sum(len(values) for entry in self._entries
                   for values in entry["observations"].values())

    def saturation_is_settled(self, index: int, member_key: str, name: str) -> bool:
        """飽和がこの member をこれ以上試さなくてよいか。

        呼び出し観測が取れていれば当然 settled。加えて「**呼び出しに到達し得ない
        ことが記録として確定した**」場合も settled にする:

        * member がそもそも無い（``attr`` が ``absent``）
        * member が callable でない値だった（``attr`` が ``value``）
        * ``getattr`` 自体が通常例外だった（``attr`` が ``raises``）

        これらでは ``call:`` key が永遠に作られないので、call 観測だけを見て
        いると飽和 loop が同じ member を試し続ける。equality-class 飽和と
        IR-kind 飽和の両方がこの 1 つの判定を使う。
        """

        observations = self._entries[index]["observations"]
        if member_key in observations:
            return True
        attribute = observations.get(attr_key(name))
        if not attribute:
            return False
        first = attribute[0]
        if "raises" in first:
            return True
        member = first.get("v") or {}
        return member.get("kind") in (MEMBER_ABSENT, MEMBER_VALUE)

    def note_call(self, index: int, member_key: str, name: str, args: Tuple) -> None:
        self._calls[index].setdefault(member_key, (name, args))

    def store(self, index: int, member_key: str, envelope: Mapping[str, Any]) -> None:
        """1 回の観測を積む。

        Ghidra には状態を持つ API（``Iterator.next`` / ``hasNext``、毎回新しい
        object を返す ``getImageBase`` 等）があるので、同じ key の観測は列として
        持つ。畳めるかどうかは :meth:`collapse` が判定する。
        """

        observations = self._entries[index]["observations"].setdefault(
            member_key, []
        )
        observations.append(envelope)

    def _equivalence_key(self, envelope: Mapping[str, Any]) -> str:
        """観測 2 件を 1 件に畳めるかを見る正規形。

        **object 参照は同一性のまま**比べる。Ghidra には呼ぶたびに新しい
        instance を返す getter（``getBody`` / ``getImageBase`` / ``getIterator``
        …）があり、``equals`` で畳むと「どの instance に何を要求したか」が
        instance をまたいで散るのに、再生では 1 つの代表へ集まってしまう。
        畳むのは「毎回まったく同じ object / 値が返った」場合だけにする。
        """

        return json.dumps(envelope, sort_keys=True)

    def collapse(self) -> None:
        """観測列を fixture の envelope へ畳む。"""

        for index, entry in enumerate(self._entries):
            members: Dict[str, Any] = {}
            for member_key, observations in entry["observations"].items():
                keys = {self._equivalence_key(item) for item in observations}
                if len(keys) == 1:
                    members[member_key] = observations[0]
                else:
                    members[member_key] = {"seq": list(observations)}
                    self.stateful_members.append(
                        "{} {} x{}".format(
                            self.object_id(index), member_key, len(observations)
                        )
                    )
            entry["members"] = members
            del entry["observations"]

    # -- 飽和 ---------------------------------------------------------------

    def saturate(self) -> None:
        """要求済みの member 名を、同値類と IR kind の全 object へ広げる。

        API 名は**production が実際に要求したもの**しか使わない（先回りで
        Ghidra API を並べない）。2 つの広げ方がある:

        * **同値類**: Java の ``equals`` で等しい object（毎回作り直される
          ``Address`` など）は、どれか 1 つに出た要求を全員へ出す。観測列の
          畳み込みで代表 object が変わっても、代表が member を欠かない。
        * **IR kind**: HighFunction 系（:data:`IR_SATURATION_KINDS`）は、同じ
          kind の別 object が別経路で読まれても未記録にならないように、kind
          単位で要求を飽和させる（index accessor は件数 API で回す）。
        """

        for _pass in range(MAX_SATURATION_PASSES):
            before = self.observation_count()
            self._saturate_equality_classes()
            self._saturate_ir_kinds()
            # 「試した」ではなく「新しい観測が増えた」を進捗とする。到達でき
            # ない member を試しただけの周回は進捗にならないので必ず止まる。
            if self.observation_count() == before:
                return
        raise RecordingError(
            "saturation did not reach a fixpoint in {} passes".format(
                MAX_SATURATION_PASSES
            )
        )

    def _saturate_equality_classes(self) -> None:
        classes: Dict[int, List[int]] = {}
        for index, entry in enumerate(self._entries):
            classes.setdefault(entry["eq_group"], []).append(index)
        for members in classes.values():
            if len(members) < 2:
                continue
            census: Dict[str, Any] = {}
            for index in members:
                for member_key, call in self._calls[index].items():
                    if call[0].startswith("__"):
                        continue
                    census.setdefault(member_key, call)
            for index in members:
                for member_key, (name, args) in census.items():
                    if self.saturation_is_settled(index, member_key, name):
                        continue
                    self._safe_call(self._proxies[index], name, args)

    def _saturate_ir_kinds(self) -> None:
        census: Dict[str, set] = {}
        indexed_census: Dict[str, set] = {}
        for entry in self._entries:
            simple = _simple_name(entry["kind"])
            if simple not in IR_SATURATION_KINDS:
                continue
            names = census.setdefault(simple, set())
            indexed = indexed_census.setdefault(simple, set())
            for member_key in entry["observations"]:
                if not member_key.startswith(fixture_schema.CALL_KEY_PREFIX):
                    continue
                if member_key.endswith("()"):
                    names.add(
                        member_key[len(fixture_schema.CALL_KEY_PREFIX):-2]
                    )
                    continue
                for accessor, _counter in INDEXED_ACCESSORS:
                    if member_key.startswith(
                        "{}{}(int:".format(
                            fixture_schema.CALL_KEY_PREFIX, accessor
                        )
                    ):
                        indexed.add(accessor)
        index = 0
        while index < len(self._entries):
            entry = self._entries[index]
            simple = _simple_name(entry["kind"])
            if simple not in IR_SATURATION_KINDS:
                index += 1
                continue
            proxy = self._proxies[index]
            for name in sorted(census.get(simple, ())):
                if name.startswith("__"):
                    continue
                if self.saturation_is_settled(index, call_key(name, ()), name):
                    continue
                self._safe_call(proxy, name, ())
            for accessor, counter in INDEXED_ACCESSORS:
                if accessor not in indexed_census.get(simple, ()):
                    continue
                count = self._counted(index, proxy, counter)
                if count is None:
                    continue
                if count > MAX_SATURATION_INDEX:
                    raise RecordingError(
                        "saturation index count is implausible: {} {} {}".format(
                            entry["kind"], counter, count
                        )
                    )
                for ordinal in range(count):
                    if self.saturation_is_settled(
                        index, call_key(accessor, [ordinal]), accessor,
                    ):
                        continue
                    self._safe_call(proxy, accessor, (ordinal,))
            index += 1

    def _counted(
        self, index: int, proxy: "RecordingProxy", counter: str,
    ) -> Optional[int]:
        """index accessor を回すための件数。

        件数 API も通常 member と**同じ terminal 判定**
        （:meth:`saturation_is_settled`）を使う。専用の判定を書くと、
        「counter に到達し得ないと記録で確定しているのに毎周回呼び直す」経路が
        できて、観測（``attr`` の再記録）だけが増え続け、飽和が偽の進捗で
        回り続けてしまう。

        * 観測済み → 記録値を使い、**呼び直さない**（状態を持つ API だった
          場合に production の観測列を乱さない）
        * 到達し得ないと確定（``attr`` が absent / 非 callable / raises）
          → ``None``
        * callable で未観測 → 1 回だけ呼ぶ
        """

        member_key = call_key(counter, ())
        recorded = self.recorded_observation(index, member_key)
        if recorded is not None:
            tagged = recorded.get("v")
            if not isinstance(tagged, Mapping) or tagged.get("kind") != VALUE_INT:
                return None
            value: Any = tagged["value"]
        elif self.saturation_is_settled(index, member_key, counter):
            return None
        else:
            value = self._safe_call(proxy, counter, ())
        if isinstance(value, bool) or not isinstance(value, int) or value < 0:
            return None
        return value

    def _safe_call(self, proxy: "RecordingProxy", name: str, args: Tuple) -> Any:
        """飽和のための best-effort な 1 呼び出し。

        Ghidra API がその object で使えないこと（``AttributeError``、実装側の
        例外）は飽和では普通に起こるので無視してよい。ただし
        :class:`RecordingError` は**握り潰さない**: fixture の健全性 / schema /
        identity 契約の違反をここで飲み込むと、記録がそのまま続いて不正な
        fixture を書き出してしまう。:meth:`saturate` の固定点判定
        （観測数が増えなくなったら終了）とは別に、soundness に関わる失敗は
        記録全体を止める。
        """

        try:
            member = getattr(proxy, name)
        except RecordingError:
            raise
        except Exception:
            return None
        if not callable(member):
            return None
        try:
            return member(*args)
        except RecordingError:
            raise
        except Exception:
            return None

    # -- 直列化 -------------------------------------------------------------

    def objects_payload(self) -> Dict[str, Any]:
        return {
            self.object_id(index): entry
            for index, entry in enumerate(self._entries)
        }


class RecordingProxy:
    """実 Ghidra object 1 つの記録 proxy。"""

    # 外の runtime object（Ghidra object）の代わり: 意味値の到達走査
    # （``core/semantic_freeze._is_owned_object``）は本物と同じく葉として扱い、記録器を辿らない
    __semantic_opaque__ = True

    def __init__(self, recorder: Recorder, index: int, real: Any) -> None:
        object.__setattr__(self, "_rec_recorder", recorder)
        object.__setattr__(self, "_rec_index", index)
        object.__setattr__(self, "_rec_id", recorder.object_id(index))
        object.__setattr__(self, "_rec_real", real)

    # -- member 参照 --------------------------------------------------------

    def __getattr__(self, name: str) -> Any:
        if not is_recordable_member(name):
            raise AttributeError(name)
        recorder = self._rec_recorder
        key = attr_key(name)
        try:
            member = getattr(self._rec_real, name)
        except AttributeError:
            recorder.store(self._rec_index, key, {"v": {"kind": MEMBER_ABSENT}})
            raise AttributeError(name)
        except Exception as exc:
            recorder.store(self._rec_index, key, _raises(exc))
            raise
        if callable(member):
            recorder.store(self._rec_index, key, {"v": {"kind": MEMBER_METHOD}})
            return _RecordingBoundMethod(self, name, member)
        value, tagged = recorder.capture(member)
        recorder.store(
            self._rec_index, key,
            {"v": {"kind": MEMBER_VALUE, "value": tagged}},
        )
        return value

    def _rec_invoke(self, name: str, member: Any, args: Tuple) -> Any:
        recorder = self._rec_recorder
        key = call_key(name, [recorder.key_arg(arg) for arg in args])
        recorder.note_call(self._rec_index, key, name, args)
        try:
            raw = member(*[_unwrap(arg) for arg in args])
        except Exception as exc:
            recorder.store(self._rec_index, key, _raises(exc))
            raise
        if name in IDENTITY_DERIVED_METHODS:
            value, tagged = self._rec_identity_surrogate(name, args, raw)
        else:
            value, tagged = recorder.capture(raw)
        recorder.store(self._rec_index, key, {"v": tagged})
        return value

    def _rec_identity_surrogate(
        self, name: str, args: Tuple, raw: Any,
    ) -> Tuple[Any, Mapping[str, Any]]:
        """identity 由来の戻り値を surrogate へ差し替える。

        写すのは **観測した raw 値どうしの一致 / 不一致関係**で、受け手の同値類
        ではない（``hashCode`` は unequal な object の collision が合法なので、
        受け手で採番すると実観測の collision を壊す）。**production にも
        surrogate を返す**ので、記録時と再生時に production が見る値は同一。
        宣言した面（無引数で整数を返す）から外れていたら記録を失敗させる。
        """

        if args:
            raise RecordingError(
                "identity-derived member {} was called with arguments".format(name)
            )
        try:
            group, surrogate = self._rec_recorder.identity_ledger.assign(
                name, raw, self._rec_recorder.entry(self._rec_index)["eq_group"],
            )
        except IdentityContractViolation as exc:
            raise RecordingError(str(exc)) from exc
        return surrogate, {
            "kind": VALUE_IDENTITY, "value": surrogate,
            "member": name, "group": group,
        }

    # -- 記録対象の dunder --------------------------------------------------
    #
    # JPype の Java object は ``__bool__`` / ``__len__`` を必ずしも持たないので、
    # member を引き当てるのではなく **Python 組み込みの意味論をそのまま実 object
    # へ当てた結果**を記録する（真偽値・長さ・反復・文字列化は Ghidra object の
    # 観測可能な振る舞いで、再生側も同じ key で引く）。

    def __str__(self) -> str:
        return self._rec_invoke("__str__", lambda: str(self._rec_real), ())

    def __bool__(self) -> bool:
        return bool(self._rec_invoke("__bool__", lambda: bool(self._rec_real), ()))

    def __len__(self) -> int:
        return int(self._rec_invoke("__len__", lambda: len(self._rec_real), ()))

    def __iter__(self):
        return iter(self._rec_invoke("__iter__", _materialize(self._rec_real), ()))

    def __getitem__(self, index):
        return self._rec_invoke(
            "__getitem__", lambda key: self._rec_real[key], (index,),
        )

    # -- 記録対象でない dunder ----------------------------------------------

    def __repr__(self) -> str:
        return "<RecordingProxy {} {}>".format(
            self._rec_id, _java_class_name(self._rec_real)
        )

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, RecordingProxy):
            return NotImplemented
        # 同値類 id は側ごとの ``Recorder`` が振るので、左右をまたいで
        # 同じ番号を等しくしない（再生側の ``RecordedObject`` と同じ規則）。
        if other._rec_recorder is not self._rec_recorder:
            return False
        return (
            self._rec_recorder.entry(self._rec_index)["eq_group"]
            == other._rec_recorder.entry(other._rec_index)["eq_group"]
        )

    def __ne__(self, other: Any) -> bool:
        result = self.__eq__(other)
        if result is NotImplemented:
            return result
        return not result

    def __hash__(self) -> int:
        # 再生側と同じ規則。``id()`` や**文字列**を混ぜない（Python の文字列
        # hash は process ごとに randomize されるので、set / dict の反復順が
        # run 間で変わり、記録が非決定になる）。
        return hash(self._rec_recorder.entry(self._rec_index)["eq_group"])

    def __copy__(self) -> "RecordingProxy":
        return self

    def __deepcopy__(self, memo) -> "RecordingProxy":
        return self


class _RecordingBoundMethod:
    __slots__ = ("_owner", "_name", "_member")

    def __init__(self, owner: RecordingProxy, name: str, member: Any) -> None:
        self._owner = owner
        self._name = name
        self._member = member

    def __call__(self, *args: Any) -> Any:
        return self._owner._rec_invoke(self._name, self._member, args)

    def __repr__(self) -> str:  # pragma: no cover - 診断用
        return "<RecordingBoundMethod {}.{}>".format(self._owner._rec_id, self._name)


def _materialize(real: Any):
    """``__iter__`` を「実 object を 1 回 materialize する呼び出し」にする。"""

    def materialize():
        return list(iter(real))

    return materialize


def _unwrap(value: Any) -> Any:
    if isinstance(value, RecordingProxy):
        return value._rec_real
    if isinstance(value, list):
        return [_unwrap(item) for item in value]
    if isinstance(value, tuple):
        return tuple(_unwrap(item) for item in value)
    return value


def _raises(exc: BaseException) -> Mapping[str, Any]:
    return {
        "raises": {
            "type": type(exc).__module__ + "." + type(exc).__qualname__,
            "message": str(exc),
        }
    }


class RecordingDecompiler(RecordingProxy):
    """``DecompInterface`` の記録 proxy。

    ``decompileFunction`` は proxy の関数を実 object へ戻してから実 decompiler
    を呼ぶ。``dispose()`` は no-op（実 decompiler の破棄は記録器の ``finally``
    が持つ）。再生側の :class:`RecordedDecompiler` が同じ 2 点を宣言する。
    """

    def dispose(self) -> None:
        return None


def _binary_kind(path: Path) -> str:
    with path.open("rb") as handle:
        header = handle.read(18)
    if len(header) >= 18 and header[:4] == b"\x7fELF":
        elf_type = int.from_bytes(
            header[16:18], "little" if header[5] == 1 else "big"
        )
        return {1: "object", 2: "executable", 3: "shared"}.get(
            elf_type, "elf-{}".format(elf_type)
        )
    return "unknown"


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _git(*arguments: str) -> str:
    try:
        return subprocess.run(
            ("git", *arguments), cwd=REPO_ROOT, check=True,
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
        ).stdout.decode().strip()
    except Exception:
        return ""


def eqbench_relative_path(binary_path: Path, eqbench_root: Path) -> str:
    """記録した binary の、**working root からの** canonical relative path。

    binary は canonical な ``targets/EqBench`` ではなく fresh writable working
    root（runner の ``EQBENCH_ROOT`` と同じ ``benchmarks`` 直下）から読む。
    root の外の file を basename へ縮退させると出自が消えるので fail-closed。
    """

    try:
        relative = binary_path.resolve().relative_to(eqbench_root.resolve())
    except ValueError as exc:
        raise RecordingError(
            "recorded binary is outside the EqBench working root: "
            "binary={} root={}".format(binary_path, eqbench_root)
        ) from exc
    text = relative.as_posix()
    if not text or text.startswith("/") or ".." in text.split("/"):
        raise RecordingError(
            "recorded binary path is not canonical inside the working root: " + text
        )
    return text


def eqbench_upstream_provenance(checkout: Path) -> Mapping[str, Any]:
    """**canonical な read-only checkout** からの upstream 出自。

    「binary をどこから読んだか（working root）」とは別の事実なので、別の
    field に分けて持つ。取れなければ fail-closed（出自不明の fixture を
    作らない）。
    """

    def read(*arguments: str) -> str:
        try:
            return subprocess.run(
                ("git", *arguments), cwd=checkout, check=True,
                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            ).stdout.decode().strip()
        except Exception as exc:  # pragma: no cover - 記録環境依存
            raise RecordingError(
                "EqBench canonical checkout provenance is unavailable at "
                + str(checkout)
            ) from exc

    commit = read("rev-parse", "HEAD")
    url = read("remote", "get-url", "origin")
    if len(commit) != 40 or not url:
        raise RecordingError(
            "EqBench canonical checkout provenance is incomplete at " + str(checkout)
        )
    return {"upstream_url": url, "commit": commit}


def _analysis_source_digest() -> str:
    from scripts.function_tracer_pcode.reporting.execution_identity import (
        source_tree_digest,
    )

    try:
        return source_tree_digest(REPO_ROOT)
    except Exception as exc:  # pragma: no cover - 記録環境依存
        return "unavailable:" + type(exc).__name__


def _source_roots_dirty() -> bool:
    return bool(_git("status", "--porcelain", "--", "scripts/function_tracer_pcode"))


def _header(
    *, side: str, fixture_id: str, binary_path: Path, binary_id: str,
    eqbench_root: Path, eqbench: Mapping[str, Any],
    function_name: str, entry: Optional[str], identical_fast_path: bool,
    ghidra_version: str, pyghidra_version: str, analysis_source_digest: str,
    recording_commit: str, recording_dirty: bool,
) -> Dict[str, Any]:
    relative = eqbench_relative_path(binary_path, eqbench_root)
    return {
        "schema": RECORDED_PCODE_FIXTURE_SCHEMA,
        "fixture_id": fixture_id,
        "side": side,
        "recorded_at_utc": datetime.datetime.now(
            datetime.timezone.utc
        ).replace(microsecond=0).isoformat(),
        "recording_commit": recording_commit,
        "recording_dirty": recording_dirty,
        "analysis_source_digest": analysis_source_digest,
        "recorder_version": RECORDER_VERSION,
        "ghidra_version": ghidra_version,
        "pyghidra_version": pyghidra_version,
        "binary": {
            "binary_id": binary_id,
            "eqbench_relative_path": relative,
            "sha256": _sha256_file(binary_path),
            "size": binary_path.stat().st_size,
            "kind": _binary_kind(binary_path),
        },
        "eqbench": dict(eqbench),
        "target": {"function_name": function_name, "entry": entry},
        "recording_mode": {
            "identical_fast_path": identical_fast_path,
            "connector": "production",
        },
    }


def _content_identity(path: Path) -> Tuple[str, str]:
    return ("sha256", _sha256_file(path))


def resolve_binary_provenance(
    args: argparse.Namespace,
) -> Tuple[Path, Path, Mapping[str, Any]]:
    """working root と upstream 出自を、Ghidra を起動する**前に**確定する。

    binary を読む working root（writable な copy）と、upstream URL / commit を
    読む canonical な read-only checkout は別の事実として扱う。どちらかが
    使えなければ fixture を作らない（fail-closed）。
    """

    eqbench_root = Path(args.eqbench_root).resolve()
    canonical_checkout = Path(args.eqbench_canonical_checkout).resolve()
    if not eqbench_root.is_dir():
        raise RecordingError(
            "EqBench working root is not a directory: " + str(eqbench_root)
        )
    if eqbench_root == canonical_checkout or canonical_checkout in eqbench_root.parents:
        raise RecordingError(
            "EqBench working root must be a writable copy outside the canonical "
            "read-only checkout: root={} canonical={}".format(
                eqbench_root, canonical_checkout
            )
        )
    left_path = Path(args.left).resolve()
    right_path = Path(args.right).resolve()
    for path in (left_path, right_path):
        if not path.is_file():
            raise RecordingError("recorded binary is not a file: " + str(path))
        # 出自の確認は記録の前に済ませる（root の外なら fixture を作らない）。
        eqbench_relative_path(path, eqbench_root)
    return left_path, right_path, eqbench_upstream_provenance(canonical_checkout)


def record(args: argparse.Namespace) -> int:
    left_path, right_path, eqbench = resolve_binary_provenance(args)
    eqbench_root = Path(args.eqbench_root).resolve()
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    import pyghidra

    pyghidra.start()
    import jpype  # noqa: E402  (JVM 起動後にしか import できない)

    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        build_canonical_result_finalization_bundle,
    )
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        build_default_cutover_connector,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        activate_process_worker_execution_authority_deployment,
    )
    from scripts.function_tracer_pcode.checker import EquivalenceChecker

    ghidra_version = ""
    try:
        ghidra_version = str(
            jpype.JClass("ghidra.framework.Application").getApplicationVersion()
        )
    except Exception:
        ghidra_version = os.environ.get("GHIDRA_VERSION", "")
    pyghidra_version = getattr(pyghidra, "__version__", "")

    analysis_source_digest = _analysis_source_digest()
    recording_commit = _git("rev-parse", "HEAD")
    recording_dirty = _source_roots_dirty()

    activate_process_worker_execution_authority_deployment(
        key_id="issue109a-record-" + args.fixture_id,
        key=(args.fixture_id.encode() * 32)[:32],
        key_source_id="/tmp/issue109a-" + args.fixture_id,
    )

    collector = AnalysisSnapshotCollector()
    recorders: Dict[str, Recorder] = {}
    decompilers: List[Any] = []

    work_dir = Path(
        args.work_dir or tempfile.mkdtemp(prefix="record-pcode-", dir="tmp")
    ).resolve()
    work_dir.mkdir(parents=True, exist_ok=True)

    project_cm = pyghidra.open_project(
        str(work_dir), "RecordPcodeFixture", create=True,
    )
    project = project_cm.__enter__()
    contexts: List[Any] = []
    try:
        proxies: Dict[str, RecordingProxy] = {}
        entries: Dict[str, Optional[str]] = {}
        for side, path in (("left", left_path), ("right", right_path)):
            loader = (
                pyghidra.program_loader().project(project)
                .source(str(path)).name("binary1" if side == "left" else "binary2")
                .load()
            )
            contexts.append(loader)
            loaded = loader.__enter__()
            program = loaded.getPrimaryDomainObject()
            pyghidra.analyze(program)
            recorder = Recorder(jpype, side)
            recorders[side] = recorder
            program_proxy = recorder.proxy_for(program)
            decompiler_class = jpype.JClass("ghidra.app.decompiler.DecompInterface")
            real_decompiler = decompiler_class()
            decompilers.append(real_decompiler)
            real_decompiler.openProgram(program)
            recording_decompiler = recorder.register_root(
                real_decompiler, RecordingDecompiler,
            )
            program_proxy.decompiler = recording_decompiler
            proxies[side] = program_proxy
            entries[side] = None

        # DI は再生と同じ 1 つの factory を使う（記録側だけの生成経路を作らない）。
        checker = EquivalenceChecker(
            debug=False,
            identical_fast_path=args.identical_fast_path,
            analyzer_factory=collector.wrap(recorded_analyzer_factory),
        )
        checker.v2_dual_write_pilot_connector = build_default_cutover_connector()
        result = checker.check_from_binaries(
            proxies["left"], proxies["right"],
            args.function, args.function,
            binary1_id=args.binary_ids[0], binary2_id=args.binary_ids[1],
            binary1_content_identity=_content_identity(left_path),
            binary2_content_identity=_content_identity(right_path),
        )
        payload = result.to_dict()
        finalization = getattr(result, "_canonical_finalization_context", None)
        if finalization is None:
            # canonical bundle の無い結果は fixture の比較面を満たさない。
            raise RecordingError(
                "recording produced no canonical finalization context "
                "(final_outcome={}, error={})".format(
                    payload.get("final_outcome"), payload.get("error_message"),
                )
            )
        evidence, session = finalization
        payload["canonical_result_finalization_bundle"] = (
            build_canonical_result_finalization_bundle(
                result_payload_preimage=payload,
                evidence=evidence, session=session, work=SealWorkBudget.for_result()
            )
        )

        for index, side in enumerate(("left", "right")):
            side_snapshots = collector.snapshots.get(args.binary_ids[index]) or []
            for snapshot in side_snapshots:
                if snapshot is not None and snapshot.get("entry_point"):
                    entries[side] = snapshot["entry_point"]
                    break
            recorders[side].saturate()
            recorders[side].collapse()

        for position, (side, path) in enumerate(
            (("left", left_path), ("right", right_path))
        ):
            recorder = recorders[side]
            header = _header(
                side=side, fixture_id=args.fixture_id, binary_path=path,
                binary_id=args.binary_ids[position],
                eqbench_root=eqbench_root, eqbench=eqbench,
                function_name=args.function, entry=entries[side],
                identical_fast_path=args.identical_fast_path,
                ghidra_version=ghidra_version, pyghidra_version=pyghidra_version,
                analysis_source_digest=analysis_source_digest,
                recording_commit=recording_commit, recording_dirty=recording_dirty,
            )
            fixture = {
                "header": header,
                "roots": {
                    "program": proxies[side]._rec_id,
                    "decompiler": proxies[side].decompiler._rec_id,
                },
                "objects": recorder.objects_payload(),
            }
            fixture_schema.validate_fixture(fixture)
            (output_dir / "{}.json".format(side)).write_text(
                fixture_schema.dumps(fixture), encoding="utf-8",
            )
            print(
                "[record] {}: {} objects, {} members, stateful={}".format(
                    side, len(recorder._entries),
                    sum(len(e["members"]) for e in recorder._entries),
                    len(recorder.stateful_members),
                )
            )
            for line in recorder.stateful_members[:10]:
                print("[record] stateful: " + line)

        (output_dir / "analysis_snapshot.json").write_text(
            json.dumps(
                collector.payload(), ensure_ascii=False, sort_keys=True, indent=1,
            ) + "\n",
            encoding="utf-8",
        )
        (output_dir / "check_snapshot.json").write_text(
            json.dumps(
                check_snapshot(payload), ensure_ascii=False, sort_keys=True, indent=1,
            ) + "\n",
            encoding="utf-8",
        )
        print("[record] final_outcome=" + str(payload.get("final_outcome")))
        print("[record] class census:")
        for side in ("left", "right"):
            kinds: Dict[str, int] = {}
            for entry in recorders[side]._entries:
                kinds[entry["kind"]] = kinds.get(entry["kind"], 0) + 1
            for kind, count in sorted(kinds.items(), key=lambda item: -item[1]):
                print("  {} {} {}".format(side, count, kind))
        return 0
    finally:
        for decompiler in decompilers:
            try:
                decompiler.dispose()
            except Exception:
                pass
        for context in reversed(contexts):
            try:
                context.__exit__(None, None, None)
            except Exception:
                pass
        try:
            project_cm.__exit__(None, None, None)
        except Exception:
            pass


#: 記録を 2 回比べるときに外す header field。**volatile なものだけ**。
#: ``recording_commit`` / ``analysis_source_digest`` は同じ source からの再記録なら
#: 一致すべき出自なので、比較から隠さない。
VOLATILE_HEADER_FIELDS = ("recorded_at_utc", "recording_dirty")


def compare(first: Path, second: Path) -> int:
    """同じ入力で 2 回記録した出力を比べる（Ghidra 不要）。

    差分は「object id, member key」の単位で出す。除外するのは volatile な
    header field（:data:`VOLATILE_HEADER_FIELDS`）だけで、``recording_commit``
    や ``analysis_source_digest`` は同じ source からの再記録なら一致すべき出自
    なので隠さない。
    """

    status = 0
    for name in ("left.json", "right.json", "analysis_snapshot.json",
                 "check_snapshot.json"):
        left = json.loads((first / name).read_text(encoding="utf-8"))
        right = json.loads((second / name).read_text(encoding="utf-8"))
        if isinstance(left, dict) and "header" in left:
            for field in VOLATILE_HEADER_FIELDS:
                left["header"].pop(field, None)
                right["header"].pop(field, None)
        if json.dumps(left, sort_keys=True) == json.dumps(right, sort_keys=True):
            print("[compare] {}: identical".format(name))
            continue
        status = 1
        print("[compare] {}: DIFFERENT".format(name))
        if not (isinstance(left, dict) and "objects" in left):
            continue
        for object_id in sorted(set(left["objects"]) | set(right["objects"])):
            entry = left["objects"].get(object_id)
            other = right["objects"].get(object_id)
            if json.dumps(entry, sort_keys=True) == json.dumps(other, sort_keys=True):
                continue
            if entry is None or other is None:
                print("  {}: present on one side only".format(object_id))
                continue
            for member_key in sorted(set(entry["members"]) | set(other["members"])):
                if json.dumps(entry["members"].get(member_key), sort_keys=True) == \
                        json.dumps(other["members"].get(member_key), sort_keys=True):
                    continue
                print("  {} {} {}: {} != {}".format(
                    object_id, entry["kind"], member_key,
                    json.dumps(entry["members"].get(member_key))[:80],
                    json.dumps(other["members"].get(member_key))[:80],
                ))
    return status


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--compare", nargs=2, metavar=("DIR_A", "DIR_B"), default=None,
        help="同じ入力で 2 回記録した出力ディレクトリを比べる（記録はしない）",
    )
    parser.add_argument("--left")
    parser.add_argument("--right")
    parser.add_argument(
        "--eqbench-root",
        help=(
            "binary を読む writable working root（runner の EQBENCH_ROOT と同じ "
            "benchmarks 直下）。canonical な targets/EqBench は使わない"
        ),
    )
    parser.add_argument(
        "--eqbench-canonical-checkout", default=str(REPO_ROOT / "targets" / "EqBench"),
        help="upstream URL / commit を読む read-only の canonical checkout",
    )
    parser.add_argument("--function")
    parser.add_argument("--binary-ids", nargs=2)
    parser.add_argument("--fixture-id")
    parser.add_argument("--output-dir")
    parser.add_argument("--work-dir", default=None)
    parser.add_argument(
        "--identical-fast-path", choices=("on", "off"), default="off",
    )
    args = parser.parse_args(argv)
    if args.compare is not None:
        return compare(Path(args.compare[0]), Path(args.compare[1]))
    missing = [
        name for name in
        ("left", "right", "function", "binary_ids", "fixture_id", "output_dir",
         "eqbench_root")
        if getattr(args, name) is None
    ]
    if missing:
        parser.error("recording requires: " + ", ".join(sorted(missing)))
    args.identical_fast_path = args.identical_fast_path == "on"
    return record(args)


if __name__ == "__main__":
    sys.exit(main())
