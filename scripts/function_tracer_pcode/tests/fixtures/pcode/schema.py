# -*- coding: utf-8 -*-
"""``recorded-pcode-fixture-v1``: 実 Ghidra surface の記録形式（Issue #109 PR-A）。

この module は **記録器と再生器の唯一の surface 定義**であり、Ghidra にも
PyGhidra にも依存しない（再生は Ghidra 無しで走る）。記録器
（``tests/tools/record_pcode_fixture.py``）と再生器
（``tests/fixtures/pcode/recorded_program.py``）は member key の綴りも値の符号化も
検証もここから取る。片方だけが知っている surface 定義を持たせない。

形式の要点:

* fixture は「Ghidra object に対してどの member をどう呼んだら何が返ったか」の
  記録であり、Ghidra の object model を作り直した別表現ではない。再生器は
  記録を引くだけで、値の導出・推論・既定値を持たない。
* 記録値は常に envelope ``{"v": <tagged>}`` に入る。``{"v": {"kind": "none"}}``
  は「None が返ったことを記録した」、``{"v": {"kind": "list", "items": []}}``
  は「空列が返ったことを記録した」。**key 自体が無い = 未記録**で、再生器は
  欠落履歴に積んで ``RecordedSurfaceMissing`` を送出する（None・空・既定値を
  返さない）。
* 同じ key が複数回呼ばれ、観測が**まったく同じでなかった**場合（object 参照は
  同一性で比較）は ``{"seq": [<envelope>, ...]}`` として呼び出し順に並べる。
  Ghidra には状態を持つ API（``Iterator.next`` / ``hasNext``）と、呼ぶたびに
  新しい instance を返す getter（``getBody`` / ``getImageBase`` /
  ``getIterator``）があるので、1 key = 1 値に畳むと再生が実体と食い違う。
  ``seq`` を使い切った後の呼び出しは**未記録**として扱う。
* member 参照（``getattr``）と呼び出し（``member(...)``）は別の key を持つ。
  実 object に member が無かったこと（``AttributeError``）も
  ``{"kind": "absent"}`` として**記録される**（未記録とは区別する）。
* 実 API が例外を送出したことも ``{"raises": ...}`` として記録する。production
  code は Ghidra の例外を捕捉して不完全解析に落とす経路を持つので、例外を
  記録しないと再生側で「未記録」と区別できなくなる。
* **identity 由来の値だけ**は raw 値ではなく fixture-local な surrogate で
  記録する（:data:`IDENTITY_DERIVED_METHODS`）。詳細は下記。

identity surrogate:

``Object.hashCode()`` と ``Program.getUniqueProgramID()`` は、Ghidra / JVM が
**import ごとに違う値**を返す。具体値そのものに意味は無く（Java の契約は
「equal な object は equal な hash」だけ、program ID は不透明な handle）、
production はどちらも「等しいか」だけに使う（``condition/tracker.py`` の
block 索引、runtime ref の owner）。raw 値を記録すると同じ入力の再記録が
byte 一致しないので、**値の一致 / 不一致関係を保ったまま** fixture-local な
決定的 surrogate へ正規化する:

    surrogate = (side_ordinal + 1) * IDENTITY_SURROGATE_SIDE_STRIDE + eq_group

``eq_group`` は受け手 object の Java 同値類なので、``equals`` な object は同じ
surrogate を持ち（Java の hashCode 契約と一致）、別の同値類は別の surrogate に
なる。side ordinal を掛けるので左右の fixture で surrogate は決して衝突しない。
記録器は surrogate を **production にもそのまま返す**ので、記録時と再生時で
production が見る値は同一になる。
"""

from __future__ import annotations

import json
from typing import Any, Mapping, Sequence, Tuple


RECORDED_PCODE_FIXTURE_SCHEMA = "recorded-pcode-fixture-v1"


class RecordedFixtureInvalid(ValueError):
    """fixture が schema を満たさない（検証も復号もここで落ちる）。"""


#: fixture を書いた記録器の版。schema と別に上げる（schema 互換のまま記録
#: 手順だけ変わった場合の切り分け用）。
RECORDER_VERSION = "2"

# --- tagged value kinds -----------------------------------------------------

VALUE_NONE = "none"
VALUE_BOOL = "bool"
VALUE_INT = "int"
VALUE_FLOAT = "float"
VALUE_STR = "str"
VALUE_BYTES = "bytes"
VALUE_LIST = "list"
VALUE_REF = "ref"
VALUE_IDENTITY = "identity_surrogate"

#: 値として記録できる tag と、その tag で許される key の集合（完全一致）。
VALUE_KEYS = {
    VALUE_NONE: frozenset({"kind"}),
    VALUE_BOOL: frozenset({"kind", "value"}),
    VALUE_INT: frozenset({"kind", "value"}),
    VALUE_FLOAT: frozenset({"kind", "value"}),
    VALUE_STR: frozenset({"kind", "value"}),
    VALUE_BYTES: frozenset({"kind", "value"}),
    VALUE_LIST: frozenset({"kind", "items"}),
    VALUE_REF: frozenset({"kind", "id"}),
    VALUE_IDENTITY: frozenset({"kind", "value", "member"}),
}
VALUE_KINDS = frozenset(VALUE_KEYS)

# --- identity surrogate -----------------------------------------------------

#: raw 値に意味が無く、値の一致 / 不一致関係だけが意味を持つ member。
#: 記録器はこれらの戻り値を fixture-local な surrogate に正規化する。
IDENTITY_DERIVED_METHODS = frozenset({
    # Java の identity hash。契約は「equal なら equal」だけで、具体値は
    # JVM の run ごとに変わる。production は block 索引 / op 鍵に使う。
    "hashCode",
    # Ghidra が import ごとに振る不透明な program handle。production は
    # runtime ref / parameter の owner 識別にだけ使う。
    "getUniqueProgramID",
})

#: side ごとの surrogate 帯域。左右の fixture で surrogate が衝突しない。
IDENTITY_SURROGATE_SIDE_STRIDE = 1_000_000_000_000

#: fixture の ``side`` と、surrogate の帯域を決める序数。
SIDE_ORDINALS = {"left": 0, "right": 1}


def identity_surrogate(side: str, eq_group: int) -> int:
    """identity 由来の値の、決定的で side ごとに重ならない surrogate。"""

    if side not in SIDE_ORDINALS:
        raise ValueError("recorded fixture side is not part of the schema: " + repr(side))
    if type(eq_group) is not int or type(eq_group) is bool:
        raise TypeError("equality class is not an exact int")
    return (SIDE_ORDINALS[side] + 1) * IDENTITY_SURROGATE_SIDE_STRIDE + eq_group


def identity_surrogate_band(side: str) -> Tuple[int, int]:
    """``side`` の surrogate が入るべき半開区間。"""

    base = (SIDE_ORDINALS[side] + 1) * IDENTITY_SURROGATE_SIDE_STRIDE
    # eq_group は identity 同値類の fallback で負になり得るので下側にも幅を取る。
    return (base - IDENTITY_SURROGATE_SIDE_STRIDE // 2,
            base + IDENTITY_SURROGATE_SIDE_STRIDE // 2)


# --- member kinds -----------------------------------------------------------

#: 実 object にその member が無かった（``AttributeError``）。
MEMBER_ABSENT = "absent"
#: 実 object の member が callable だった。
MEMBER_METHOD = "method"
#: 実 object の member が callable でない値だった。
MEMBER_VALUE = "value"

#: member 記録の tag と、その tag で許される key の集合（完全一致）。
MEMBER_KEYS = {
    MEMBER_ABSENT: frozenset({"kind"}),
    MEMBER_METHOD: frozenset({"kind"}),
    MEMBER_VALUE: frozenset({"kind", "value"}),
}
MEMBER_KINDS = frozenset(MEMBER_KEYS)

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


def member_name_of(member_key: str) -> str:
    """member key から member 名を取り出す。"""

    if member_key.startswith(ATTR_KEY_PREFIX):
        return member_key[len(ATTR_KEY_PREFIX):]
    if member_key.startswith(CALL_KEY_PREFIX):
        return member_key[len(CALL_KEY_PREFIX):].split("(", 1)[0]
    raise RecordedFixtureInvalid(
        "recorded member key is not part of the schema: " + repr(member_key)
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
        # ``hash`` に文字列を混ぜない: Python の文字列 hash は process ごとに
        # randomize されるので、set / dict の反復順が run 間で変わる。
        return hash(self.eq_group)

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

    検証済み fixture を前提に、**変換で救済しない**（exact 型のまま返す）。
    ``ref`` と ``list`` は object 解決が要るので再生器側で扱う。
    """

    kind = tagged["kind"]
    if kind == VALUE_NONE:
        return None
    if kind in (VALUE_BOOL, VALUE_INT, VALUE_STR, VALUE_IDENTITY):
        return tagged["value"]
    if kind == VALUE_FLOAT:
        return float(tagged["value"])
    if kind == VALUE_BYTES:
        return bytes.fromhex(tagged["value"])
    raise RecordedFixtureInvalid(
        "recorded value kind is not a scalar: " + repr(kind)
    )


# --- fixture 本体の検証 -----------------------------------------------------

#: fixture 本体の key（完全一致）。
FIXTURE_KEYS = frozenset({"header", "roots", "objects"})

#: header の key（完全一致）。
HEADER_KEYS = frozenset({
    "schema", "fixture_id", "side", "recorded_at_utc", "recording_commit",
    "recording_dirty", "analysis_source_digest", "recorder_version",
    "ghidra_version", "pyghidra_version", "binary", "eqbench", "target",
    "recording_mode",
})

BINARY_KEYS = frozenset({
    "binary_id", "eqbench_relative_path", "sha256", "size", "kind",
})
EQBENCH_KEYS = frozenset({"upstream_url", "commit"})
TARGET_KEYS = frozenset({"function_name", "entry"})
RECORDING_MODE_KEYS = frozenset({"identical_fast_path", "connector"})
OBJECT_KEYS = frozenset({"kind", "eq_group", "members"})
RAISES_KEYS = frozenset({"type", "message"})

#: ``roots`` の key（完全一致）。``program`` は解析入口、``decompiler`` は
#: DI (a) で ``ReturnAnalyzer`` に渡す decompiler。
ROOT_KEYS = frozenset({"program", "decompiler"})

#: 記録に使える connector は production のものだけ。
RECORDING_CONNECTORS = frozenset({"production"})

_HEX = frozenset("0123456789abcdef")


def _exact_keys(what: str, value: Any, allowed: frozenset) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise RecordedFixtureInvalid("{} is not a mapping".format(what))
    keys = set(value)
    if keys != set(allowed):
        missing = sorted(set(allowed) - keys)
        unknown = sorted(keys - set(allowed))
        raise RecordedFixtureInvalid(
            "{} keys do not match the schema (missing={}, unknown={})".format(
                what, missing, unknown
            )
        )
    return value


def _exact_str(what: str, value: Any, *, allow_empty: bool = False) -> str:
    if type(value) is not str or (not allow_empty and not value):
        raise RecordedFixtureInvalid("{} is not a non-empty exact string".format(what))
    return value


def _exact_bool(what: str, value: Any) -> bool:
    if type(value) is not bool:
        raise RecordedFixtureInvalid("{} is not an exact bool".format(what))
    return value


def _exact_int(what: str, value: Any, *, minimum: Any = None) -> int:
    if type(value) is not int or type(value) is bool:
        raise RecordedFixtureInvalid("{} is not an exact int".format(what))
    if minimum is not None and value < minimum:
        raise RecordedFixtureInvalid("{} is below {}".format(what, minimum))
    return value


def _exact_hex(what: str, value: Any, length: int) -> str:
    text = _exact_str(what, value)
    if len(text) != length or not set(text) <= _HEX:
        raise RecordedFixtureInvalid(
            "{} is not {} lowercase hex digits".format(what, length)
        )
    return text


def _relative_path(what: str, value: Any) -> str:
    text = _exact_str(what, value)
    if text.startswith("/") or ".." in text.split("/"):
        raise RecordedFixtureInvalid("{} is not a canonical relative path".format(what))
    return text


def _validate_header(header: Any) -> Mapping[str, Any]:
    _exact_keys("recorded fixture header", header, HEADER_KEYS)
    if header["schema"] != RECORDED_PCODE_FIXTURE_SCHEMA:
        raise RecordedFixtureInvalid(
            "recorded fixture schema is not {}: {!r}".format(
                RECORDED_PCODE_FIXTURE_SCHEMA, header["schema"]
            )
        )
    side = _exact_str("recorded fixture side", header["side"])
    if side not in SIDE_ORDINALS:
        raise RecordedFixtureInvalid(
            "recorded fixture side is not part of the schema: " + repr(side)
        )
    _exact_str("recorded fixture id", header["fixture_id"])
    _exact_str("recording timestamp", header["recorded_at_utc"])
    _exact_hex("recording commit", header["recording_commit"], 40)
    _exact_bool("recording dirty flag", header["recording_dirty"])
    _exact_hex("analysis source digest", header["analysis_source_digest"], 64)
    _exact_str("recorder version", header["recorder_version"])
    _exact_str("ghidra version", header["ghidra_version"])
    _exact_str("pyghidra version", header["pyghidra_version"])

    binary = _exact_keys("recorded fixture binary", header["binary"], BINARY_KEYS)
    _exact_str("binary id", binary["binary_id"])
    _relative_path("binary eqbench relative path", binary["eqbench_relative_path"])
    _exact_hex("binary sha256", binary["sha256"], 64)
    _exact_int("binary size", binary["size"], minimum=1)
    _exact_str("binary kind", binary["kind"])

    eqbench = _exact_keys("recorded fixture eqbench provenance", header["eqbench"], EQBENCH_KEYS)
    _exact_str("eqbench upstream url", eqbench["upstream_url"])
    _exact_hex("eqbench commit", eqbench["commit"], 40)

    target = _exact_keys("recorded fixture target", header["target"], TARGET_KEYS)
    _exact_str("target function name", target["function_name"])
    _exact_str("target entry", target["entry"])

    mode = _exact_keys(
        "recorded fixture recording mode", header["recording_mode"],
        RECORDING_MODE_KEYS,
    )
    _exact_bool("recording mode identical fast path", mode["identical_fast_path"])
    connector = _exact_str("recording mode connector", mode["connector"])
    if connector not in RECORDING_CONNECTORS:
        raise RecordedFixtureInvalid(
            "recording connector is not part of the schema: " + repr(connector)
        )
    return header


def _validate_value(
    member_key: str, tagged: Any, *, object_ids: Any, side: str,
) -> None:
    if not isinstance(tagged, Mapping) or tagged.get("kind") not in VALUE_KINDS:
        raise RecordedFixtureInvalid(
            "recorded value kind is not part of the schema: " + repr(member_key)
        )
    kind = tagged["kind"]
    _exact_keys("recorded value of " + repr(member_key), tagged, VALUE_KEYS[kind])
    if kind == VALUE_NONE:
        return
    if kind == VALUE_BOOL:
        _exact_bool("recorded bool of " + repr(member_key), tagged["value"])
        return
    if kind == VALUE_INT:
        _exact_int("recorded int of " + repr(member_key), tagged["value"])
        return
    if kind == VALUE_FLOAT:
        text = _exact_str("recorded float of " + repr(member_key), tagged["value"])
        try:
            float(text)
        except ValueError as exc:
            raise RecordedFixtureInvalid(
                "recorded float of {} is not parseable".format(repr(member_key))
            ) from exc
        return
    if kind == VALUE_STR:
        _exact_str("recorded string of " + repr(member_key), tagged["value"], allow_empty=True)
        return
    if kind == VALUE_BYTES:
        text = _exact_str("recorded bytes of " + repr(member_key), tagged["value"], allow_empty=True)
        if len(text) % 2 or not set(text) <= _HEX:
            raise RecordedFixtureInvalid(
                "recorded bytes of {} is not lowercase hex".format(repr(member_key))
            )
        return
    if kind == VALUE_LIST:
        items = tagged["items"]
        if not isinstance(items, list):
            raise RecordedFixtureInvalid(
                "recorded list of {} is not a list".format(repr(member_key))
            )
        for item in items:
            _validate_value(member_key, item, object_ids=object_ids, side=side)
        return
    if kind == VALUE_REF:
        target = _exact_str("recorded reference of " + repr(member_key), tagged["id"])
        if target not in object_ids:
            raise RecordedFixtureInvalid(
                "recorded reference of {} points at an unknown object: {}".format(
                    repr(member_key), target
                )
            )
        return
    # VALUE_IDENTITY
    member = _exact_str("identity surrogate member of " + repr(member_key), tagged["member"])
    if member not in IDENTITY_DERIVED_METHODS:
        raise RecordedFixtureInvalid(
            "identity surrogate member is not declared: " + repr(member)
        )
    if member != member_name_of(member_key):
        raise RecordedFixtureInvalid(
            "identity surrogate member does not match its key: " + repr(member_key)
        )
    value = _exact_int("identity surrogate of " + repr(member_key), tagged["value"])
    low, high = identity_surrogate_band(side)
    if not low <= value < high:
        raise RecordedFixtureInvalid(
            "identity surrogate of {} is outside the {} band".format(
                repr(member_key), side
            )
        )


def _validate_observation(
    member_key: str, observation: Any, *, object_ids: Any, side: str,
) -> None:
    if not isinstance(observation, Mapping):
        raise RecordedFixtureInvalid(
            "recorded observation is not a mapping: " + repr(member_key)
        )
    keys = set(observation)
    if keys == {"raises"}:
        raised = _exact_keys(
            "recorded exception of " + repr(member_key), observation["raises"],
            RAISES_KEYS,
        )
        _exact_str("recorded exception type of " + repr(member_key), raised["type"])
        _exact_str(
            "recorded exception message of " + repr(member_key), raised["message"],
            allow_empty=True,
        )
        return
    if keys != {"v"}:
        raise RecordedFixtureInvalid(
            "recorded observation must hold exactly one of v/raises: "
            + repr(member_key)
        )
    value = observation["v"]
    if member_key.startswith(ATTR_KEY_PREFIX):
        if not isinstance(value, Mapping) or value.get("kind") not in MEMBER_KINDS:
            raise RecordedFixtureInvalid(
                "recorded member kind is not part of the schema: " + repr(member_key)
            )
        _exact_keys(
            "recorded member of " + repr(member_key), value,
            MEMBER_KEYS[value["kind"]],
        )
        if value["kind"] == MEMBER_VALUE:
            _validate_value(member_key, value["value"], object_ids=object_ids, side=side)
        return
    _validate_value(member_key, value, object_ids=object_ids, side=side)


def _validate_envelope(
    member_key: str, envelope: Any, *, object_ids: Any, side: str,
) -> None:
    if not isinstance(envelope, Mapping):
        raise RecordedFixtureInvalid(
            "recorded member envelope is not a mapping: " + repr(member_key)
        )
    keys = set(envelope)
    if keys not in ({"v"}, {"raises"}, {"seq"}):
        raise RecordedFixtureInvalid(
            "recorded member envelope must hold exactly one of v/raises/seq: "
            + repr(member_key)
        )
    if keys != {"seq"}:
        _validate_observation(member_key, envelope, object_ids=object_ids, side=side)
        return
    observations = envelope["seq"]
    if not isinstance(observations, list) or len(observations) < 2:
        raise RecordedFixtureInvalid(
            "recorded member sequence must hold at least two observations: "
            + repr(member_key)
        )
    for observation in observations:
        _validate_observation(member_key, observation, object_ids=object_ids, side=side)


def _validate_member_key(member_key: Any) -> str:
    if type(member_key) is not str:
        raise RecordedFixtureInvalid("recorded member key is not a string")
    name = member_name_of(member_key)
    if not name:
        raise RecordedFixtureInvalid(
            "recorded member key has no member name: " + repr(member_key)
        )
    if member_key.startswith(CALL_KEY_PREFIX) and not member_key.endswith(")"):
        raise RecordedFixtureInvalid(
            "recorded call key is not closed: " + repr(member_key)
        )
    return member_key


def validate_fixture(payload: Any) -> Mapping[str, Any]:
    """schema 一致を**完全一致**で検査する（migration 機構は持たない）。

    余剰 field を黙って受理せず、scalar も変換で救済しない。不正な fixture は
    再生前にここで落ちる（再生時に意味のある値へ coercion しない）。
    """

    _exact_keys("recorded fixture", payload, FIXTURE_KEYS)
    header = _validate_header(payload["header"])
    side = header["side"]

    objects = payload["objects"]
    if not isinstance(objects, Mapping):
        raise RecordedFixtureInvalid("recorded fixture objects is not a mapping")
    object_ids = frozenset(objects)
    for object_id, entry in objects.items():
        _exact_str("recorded object id", object_id)
        _exact_keys("recorded object " + str(object_id), entry, OBJECT_KEYS)
        _exact_str("recorded object kind of " + str(object_id), entry["kind"])
        _exact_int("recorded object equality class of " + str(object_id), entry["eq_group"])
        members = entry["members"]
        if not isinstance(members, Mapping):
            raise RecordedFixtureInvalid(
                "recorded object members is not a mapping: " + str(object_id)
            )
        for member_key, envelope in members.items():
            _validate_member_key(member_key)
            _validate_envelope(member_key, envelope, object_ids=object_ids, side=side)

    roots = _exact_keys("recorded fixture roots", payload["roots"], ROOT_KEYS)
    for key in sorted(ROOT_KEYS):
        target = _exact_str("recorded fixture root " + key, roots[key])
        if target not in object_ids:
            raise RecordedFixtureInvalid(
                "recorded fixture root {} points at an unknown object".format(key)
            )
    return payload


def dumps(payload: Mapping[str, Any]) -> str:
    """fixture を決定的な JSON テキストにする。"""

    return json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=1) + "\n"


def loads(text: str) -> Mapping[str, Any]:
    return validate_fixture(json.loads(text))


def fixture_identity(payload: Mapping[str, Any]) -> Tuple[str, str, str]:
    header = payload["header"]
    return (header["fixture_id"], header["side"], header["binary"]["sha256"])
