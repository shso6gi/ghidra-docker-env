# -*- coding: utf-8 -*-
"""``recorded-pcode-fixture-v1``: 実 Ghidra surface の記録形式（Issue #109 PR-A）。

この module は **記録器と再生器の唯一の surface 定義**であり、Ghidra にも
PyGhidra にも依存しない（再生は Ghidra 無しで走る）。記録器
（``tests/tools/record_pcode_fixture.py``）と再生器
（``tests/fixtures/pcode/recorded_program.py``）は member key の綴りも値の符号化も
ここから取る。片方だけが知っている surface 定義を持たせない。

形式の要点:

* fixture は「Ghidra object に対してどの member をどう呼んだら何が返ったか」の
  記録であり、Ghidra の object model を作り直した別表現ではない。再生器は
  記録を引くだけで、値の導出・推論・既定値を持たない。
* 記録値は常に envelope ``{"v": <tagged>}`` に入る。``{"v": {"kind": "none"}}``
  は「None が返ったことを記録した」、``{"v": {"kind": "list", "items": []}}``
  は「空列が返ったことを記録した」。**key 自体が無い = 未記録**で、再生器は
  欠落履歴に積んで ``RecordedSurfaceMissing`` を送出する（None・空・既定値を
  返さない）。
* 同じ key が複数回呼ばれ、観測が**同じでなかった**場合は
  ``{"seq": [<envelope>, ...]}`` として呼び出し順に並べる。Ghidra には状態を
  持つ API（``Iterator.next`` / ``hasNext``、毎回新しい object を返す
  ``getImageBase`` など）があるので、1 key = 1 値に畳むと再生が実体と食い違う。
  観測が**まったく同じ**（object 参照は同一性で比較）なら 1 件に畳む。
  ``equals`` で畳むと、どの instance に何を要求したかが instance をまたいで
  散っているのに再生では 1 つの代表へ集まってしまう。``seq`` を使い切った後の
  呼び出しは**未記録**として扱う。
* member 参照（``getattr``）と呼び出し（``member(...)``）は別の key を持つ。
  実 object に member が無かったこと（``AttributeError``）も
  ``{"kind": "absent"}`` として**記録される**（未記録とは区別する）。
* 実 API が例外を送出したことも ``{"raises": ...}`` として記録する。production
  code は Ghidra の例外を捕捉して不完全解析に落とす経路を持つので、例外を
  記録しないと再生側で「未記録」と区別できなくなる。
"""

from __future__ import annotations

import json
from typing import Any, Mapping, Sequence, Tuple


RECORDED_PCODE_FIXTURE_SCHEMA = "recorded-pcode-fixture-v1"

#: fixture を書いた記録器の版。schema と別に上げる（schema 互換のまま記録
#: 手順だけ変わった場合の切り分け用）。
RECORDER_VERSION = "1"

# --- tagged value kinds -----------------------------------------------------

VALUE_NONE = "none"
VALUE_BOOL = "bool"
VALUE_INT = "int"
VALUE_FLOAT = "float"
VALUE_STR = "str"
VALUE_BYTES = "bytes"
VALUE_LIST = "list"
VALUE_REF = "ref"

#: 値として記録できる tag。
VALUE_KINDS = frozenset({
    VALUE_NONE, VALUE_BOOL, VALUE_INT, VALUE_FLOAT,
    VALUE_STR, VALUE_BYTES, VALUE_LIST, VALUE_REF,
})

# --- member kinds -----------------------------------------------------------

#: 実 object にその member が無かった（``AttributeError``）。
MEMBER_ABSENT = "absent"
#: 実 object の member が callable だった。
MEMBER_METHOD = "method"
#: 実 object の member が callable でない値だった。
MEMBER_VALUE = "value"

MEMBER_KINDS = frozenset({MEMBER_ABSENT, MEMBER_METHOD, MEMBER_VALUE})

# --- key 綴り ---------------------------------------------------------------

ATTR_KEY_PREFIX = "attr:"
CALL_KEY_PREFIX = "call:"

#: 記録も再生もしない member 名（Python 実行系が prober として引くもの）。
#: dunder は proxy / 再生 object の型側で明示的に実装した分だけを扱い、
#: ``__getattr__`` では常に ``AttributeError`` にする（記録に混ぜない）。
def is_recordable_member(name: str) -> bool:
    if name.startswith("__") and name.endswith("__"):
        return False
    if name.startswith("_rec_"):
        return False
    return True


#: proxy / 再生 object の型側で実装する dunder。``__str__`` / ``__bool__`` /
#: ``__len__`` / ``__iter__`` / ``__getitem__`` は Ghidra object の観測可能な
#: 振る舞いなので記録対象（key はこの名前のまま ``call:`` に載る）。
RECORDED_DUNDERS = ("__str__", "__bool__", "__len__", "__iter__", "__getitem__")


def attr_key(name: str) -> str:
    return ATTR_KEY_PREFIX + name


def call_key(name: str, args: Sequence[Any]) -> str:
    """呼び出し 1 件の key。``args`` は scalar か :class:`ObjectRef` の列。"""

    return "{}{}({})".format(
        CALL_KEY_PREFIX, name, ",".join(render_arg(arg) for arg in args)
    )


class ObjectRef:
    """呼び出し引数として渡された object の参照。

    key に載るのは **Java 同値類（``eq_group``）** で、object の同一性ではない。
    Ghidra の ``Memory.getByte(Address)`` などは呼ぶたびに新しい ``Address``
    instance を受け取るので、同一性で key を作ると同じ番地の読み取りが別 key に
    散る。同値類で引くのは Java 側の ``equals`` の意味そのもの。
    """

    __slots__ = ("object_id", "eq_group")

    def __init__(self, object_id: str, eq_group: int) -> None:
        self.object_id = object_id
        self.eq_group = eq_group

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, ObjectRef) and other.eq_group == self.eq_group

    def __hash__(self) -> int:
        return hash((ObjectRef, self.eq_group))

    def __repr__(self) -> str:  # pragma: no cover - 診断用
        return "ObjectRef({!r}, eq={})".format(self.object_id, self.eq_group)


def render_arg(arg: Any) -> str:
    """引数 1 つを key 用の決定的な文字列にする。"""

    if arg is None:
        return "none"
    if isinstance(arg, ObjectRef):
        return "ref:eq{}".format(arg.eq_group)
    if isinstance(arg, bool):
        return "bool:" + ("true" if arg else "false")
    if isinstance(arg, int):
        return "int:" + str(arg)
    if isinstance(arg, float):
        return "float:" + repr(arg)
    if isinstance(arg, str):
        return "str:" + json.dumps(arg, ensure_ascii=False, sort_keys=True)
    if isinstance(arg, (bytes, bytearray)):
        return "bytes:" + bytes(arg).hex()
    if isinstance(arg, (list, tuple)):
        return "list:[" + ",".join(render_arg(item) for item in arg) + "]"
    raise TypeError(
        "recorded surface argument type is not part of the fixture schema: "
        + type(arg).__name__
    )


def decode_scalar(tagged: Mapping[str, Any]) -> Any:
    """``ref`` / ``list`` を含まない tagged 値を Python 値に戻す。

    ``ref`` と ``list`` は object 解決が要るので再生器側で扱う。
    """

    kind = tagged["kind"]
    if kind == VALUE_NONE:
        return None
    if kind == VALUE_BOOL:
        return bool(tagged["value"])
    if kind == VALUE_INT:
        return int(tagged["value"])
    if kind == VALUE_FLOAT:
        return float(tagged["value"])
    if kind == VALUE_STR:
        value = tagged["value"]
        if type(value) is not str:
            raise ValueError("recorded string value is not an exact string")
        return value
    if kind == VALUE_BYTES:
        return bytes.fromhex(tagged["value"])
    raise ValueError("recorded value kind is not a scalar: " + repr(kind))


# --- fixture 本体の検証 -----------------------------------------------------

#: header の必須 key。
REQUIRED_HEADER_KEYS = (
    "schema", "fixture_id", "side", "recorded_at_utc", "recording_commit",
    "recording_dirty", "analysis_source_digest", "recorder_version",
    "ghidra_version", "pyghidra_version", "binary", "eqbench", "target",
    "recording_mode",
)

#: fixture 本体の必須 key。
REQUIRED_FIXTURE_KEYS = ("header", "roots", "objects")

#: ``roots`` の必須 key。``program`` は解析入口、``decompiler`` は DI (a) で
#: ``ReturnAnalyzer`` に渡す decompiler。
REQUIRED_ROOT_KEYS = ("program", "decompiler")


class RecordedFixtureInvalid(ValueError):
    """fixture が schema を満たさない。"""


def validate_fixture(payload: Any) -> Mapping[str, Any]:
    """schema 一致を完全一致で検査する（migration 機構は持たない）。"""

    if not isinstance(payload, Mapping):
        raise RecordedFixtureInvalid("recorded fixture is not a mapping")
    for key in REQUIRED_FIXTURE_KEYS:
        if key not in payload:
            raise RecordedFixtureInvalid("recorded fixture lacks " + key)
    header = payload["header"]
    if not isinstance(header, Mapping):
        raise RecordedFixtureInvalid("recorded fixture header is not a mapping")
    for key in REQUIRED_HEADER_KEYS:
        if key not in header:
            raise RecordedFixtureInvalid("recorded fixture header lacks " + key)
    if header["schema"] != RECORDED_PCODE_FIXTURE_SCHEMA:
        raise RecordedFixtureInvalid(
            "recorded fixture schema is not {}: {!r}".format(
                RECORDED_PCODE_FIXTURE_SCHEMA, header["schema"]
            )
        )
    roots = payload["roots"]
    if not isinstance(roots, Mapping):
        raise RecordedFixtureInvalid("recorded fixture roots is not a mapping")
    for key in REQUIRED_ROOT_KEYS:
        if key not in roots:
            raise RecordedFixtureInvalid("recorded fixture roots lacks " + key)
    objects = payload["objects"]
    if not isinstance(objects, Mapping):
        raise RecordedFixtureInvalid("recorded fixture objects is not a mapping")
    for object_id, entry in objects.items():
        if not isinstance(entry, Mapping):
            raise RecordedFixtureInvalid(
                "recorded object entry is not a mapping: " + str(object_id)
            )
        for key in ("kind", "eq_group", "members"):
            if key not in entry:
                raise RecordedFixtureInvalid(
                    "recorded object {} lacks {}".format(object_id, key)
                )
        members = entry["members"]
        if not isinstance(members, Mapping):
            raise RecordedFixtureInvalid(
                "recorded object members is not a mapping: " + str(object_id)
            )
        for member_key, envelope in members.items():
            if not isinstance(member_key, str) or not (
                member_key.startswith(ATTR_KEY_PREFIX)
                or member_key.startswith(CALL_KEY_PREFIX)
            ):
                raise RecordedFixtureInvalid(
                    "recorded member key is not part of the schema: "
                    + repr(member_key)
                )
            if not isinstance(envelope, Mapping):
                raise RecordedFixtureInvalid(
                    "recorded member envelope is not a mapping: " + repr(member_key)
                )
            _validate_envelope(member_key, envelope)
    for key in REQUIRED_ROOT_KEYS:
        if roots[key] not in objects:
            raise RecordedFixtureInvalid(
                "recorded fixture root {} points at an unknown object".format(key)
            )
    return payload


def _validate_value(member_key: str, tagged: Any) -> None:
    if not isinstance(tagged, Mapping) or tagged.get("kind") not in VALUE_KINDS:
        raise RecordedFixtureInvalid(
            "recorded value kind is not part of the schema: " + repr(member_key)
        )
    if tagged["kind"] == VALUE_LIST:
        items = tagged.get("items")
        if not isinstance(items, (list, tuple)):
            raise RecordedFixtureInvalid(
                "recorded list value has no items: " + repr(member_key)
            )
        for item in items:
            _validate_value(member_key, item)
    elif tagged["kind"] == VALUE_REF and type(tagged.get("id")) is not str:
        raise RecordedFixtureInvalid(
            "recorded reference has no object id: " + repr(member_key)
        )


def _validate_observation(member_key: str, observation: Mapping[str, Any]) -> None:
    if "raises" in observation:
        raised = observation["raises"]
        if not isinstance(raised, Mapping) or "type" not in raised or \
                "message" not in raised:
            raise RecordedFixtureInvalid(
                "recorded exception lacks type/message: " + repr(member_key)
            )
        return
    value = observation["v"]
    if member_key.startswith(ATTR_KEY_PREFIX):
        if not isinstance(value, Mapping) or value.get("kind") not in MEMBER_KINDS:
            raise RecordedFixtureInvalid(
                "recorded member kind is not part of the schema: "
                + repr(member_key)
            )
        if value["kind"] == MEMBER_VALUE:
            _validate_value(member_key, value.get("value"))
        return
    _validate_value(member_key, value)


def _validate_envelope(member_key: str, envelope: Any) -> None:
    if not isinstance(envelope, Mapping):
        raise RecordedFixtureInvalid(
            "recorded member envelope is not a mapping: " + repr(member_key)
        )
    present = [key for key in ("v", "raises", "seq") if key in envelope]
    if len(present) != 1:
        raise RecordedFixtureInvalid(
            "recorded member envelope must hold exactly one of v/raises/seq: "
            + repr(member_key)
        )
    if present[0] != "seq":
        _validate_observation(member_key, envelope)
        return
    observations = envelope["seq"]
    if not isinstance(observations, (list, tuple)) or len(observations) < 2:
        raise RecordedFixtureInvalid(
            "recorded member sequence must hold at least two observations: "
            + repr(member_key)
        )
    for observation in observations:
        if not isinstance(observation, Mapping) or (
            ("v" in observation) == ("raises" in observation)
        ):
            raise RecordedFixtureInvalid(
                "recorded member sequence entry must hold exactly one of v/raises: "
                + repr(member_key)
            )
        _validate_observation(member_key, observation)


def dumps(payload: Mapping[str, Any]) -> str:
    """fixture を決定的な JSON テキストにする。"""

    return json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=1) + "\n"


def loads(text: str) -> Mapping[str, Any]:
    return validate_fixture(json.loads(text))


def fixture_identity(payload: Mapping[str, Any]) -> Tuple[str, str, str]:
    header = payload["header"]
    return (header["fixture_id"], header["side"], header["binary"]["sha256"])
