# -*- coding: utf-8 -*-
"""``recorded-pcode-fixture-v1`` の再生器（Issue #109 PR-A）。

記録された surface を**引くだけ**の object 群。値の導出・推論・既定値・
Ghidra API の再実装を持たない。未記録の要求に対しては

1. その side の :attr:`RecordedProgram.missing_accesses` に追記し、
2. :class:`RecordedSurfaceMissing` を送出する

の 2 つを必ず行う。production code は Ghidra の例外を捕捉して不完全解析へ
落とす経路を多数持つ（``except Exception`` baseline 950 件）ので、例外だけでは
検出保証にならない。呼び出し側は ``missing_accesses == []`` を assert する。

「記録された None」「記録された空 collection」「未記録」は別物として扱う。
envelope が在れば記録値（``None`` や ``[]`` を含む）、key 自体が無ければ未記録。
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, List, Mapping, Sequence, Tuple

from scripts.function_tracer_pcode.tests.fixtures.pcode import schema as fixture_schema
from scripts.function_tracer_pcode.tests.fixtures.pcode.schema import (
    MEMBER_ABSENT,
    MEMBER_METHOD,
    MEMBER_VALUE,
    ObjectRef,
    VALUE_LIST,
    VALUE_REF,
    attr_key,
    call_key,
    decode_scalar,
    is_recordable_member,
)


class RecordedSurfaceMissing(Exception):
    """fixture に無い surface が要求された。

    ``Exception`` を直接継承するのは、``except KeyError`` / ``except LookupError``
    のような狭い handler に**偶然**吸収されないようにするため。広い
    ``except Exception`` に吸収されるのは避けられないので、検出の保証は
    :attr:`RecordedProgram.missing_accesses` 側が持つ。
    """

    def __init__(self, access: "MissingAccess") -> None:
        super().__init__(
            "recorded surface is missing: {} on {} ({})".format(
                access.member_key, access.object_id, access.kind
            )
        )
        self.access = access


class RecordedCallFailure(RuntimeError):
    """記録時に実 API が送出した例外の再生。"""

    def __init__(self, exception_type: str, message: str) -> None:
        super().__init__(
            "recorded Ghidra API raised {}: {}".format(exception_type, message)
        )
        self.exception_type = exception_type


@dataclass(frozen=True)
class MissingAccess:
    """未記録だった 1 件の要求。"""

    object_id: str
    kind: str
    member_key: str

    def as_tuple(self) -> Tuple[str, str, str]:
        return (self.object_id, self.kind, self.member_key)


class _RecordedContext:
    """1 つの fixture（= 片側 1 binary）で共有する再生状態。"""

    def __init__(self, payload: Mapping[str, Any]) -> None:
        self.payload = payload
        self.header = payload["header"]
        self.objects = payload["objects"]
        self.roots = payload["roots"]
        self.instances: dict = {}
        self.missing_accesses: List[MissingAccess] = []
        self.access_log: List[Tuple[str, str]] = []
        # 状態を持つ API の observation 列を、記録された呼び出し順で返すための
        # 位置（object id + member key 単位）。
        self.sequence_positions: dict = {}

    def instance(self, object_id: str) -> "RecordedObject":
        existing = self.instances.get(object_id)
        if existing is not None:
            return existing
        entry = self.objects.get(object_id)
        if entry is None:
            raise fixture_schema.RecordedFixtureInvalid(
                "recorded fixture refers to an unknown object: " + str(object_id)
            )
        program_root = self.roots["program"]
        decompiler_root = self.roots["decompiler"]
        if object_id == program_root:
            built: RecordedObject = RecordedProgram(self, object_id, entry)
        elif object_id == decompiler_root:
            built = RecordedDecompiler(self, object_id, entry)
        else:
            built = RecordedObject(self, object_id, entry)
        self.instances[object_id] = built
        return built

    def resolve(self, tagged: Mapping[str, Any]) -> Any:
        kind = tagged["kind"]
        if kind == VALUE_REF:
            return self.instance(tagged["id"])
        if kind == VALUE_LIST:
            return [self.resolve(item) for item in tagged["items"]]
        return decode_scalar(tagged)


class RecordedObject:
    """記録された Ghidra object 1 つ。

    ``kind`` は記録時の Java class 名。記録に無い member は None にも既定値にも
    ならず、欠落履歴 + :class:`RecordedSurfaceMissing` になる。
    """

    def __init__(
        self, context: _RecordedContext, object_id: str, entry: Mapping[str, Any],
    ) -> None:
        object.__setattr__(self, "_rec_context", context)
        object.__setattr__(self, "_rec_object_id", object_id)
        object.__setattr__(self, "_rec_kind", entry["kind"])
        object.__setattr__(self, "_rec_eq_group", entry["eq_group"])
        object.__setattr__(self, "_rec_members", entry["members"])

    # -- 記録の引き方 -------------------------------------------------------

    def _rec_miss(self, member_key: str):
        access = MissingAccess(
            self._rec_object_id, self._rec_kind, member_key,
        )
        self._rec_context.missing_accesses.append(access)
        return RecordedSurfaceMissing(access)

    def _rec_envelope(self, member_key: str) -> Mapping[str, Any]:
        envelope = self._rec_members.get(member_key)
        if envelope is None:
            raise self._rec_miss(member_key)
        if "seq" in envelope:
            positions = self._rec_context.sequence_positions
            position_key = (self._rec_object_id, member_key)
            position = positions.get(position_key, 0)
            observations = envelope["seq"]
            if position >= len(observations):
                # 記録された呼び出し回数を超えた。既定値へ落とさず未記録扱い。
                raise self._rec_miss(
                    "{}#{}".format(member_key, position)
                )
            positions[position_key] = position + 1
            envelope = observations[position]
        self._rec_context.access_log.append((self._rec_object_id, member_key))
        return envelope

    def _rec_value(self, member_key: str) -> Any:
        envelope = self._rec_envelope(member_key)
        if "raises" in envelope:
            raised = envelope["raises"]
            raise RecordedCallFailure(raised["type"], raised["message"])
        return self._rec_context.resolve(envelope["v"])

    def _rec_call(self, name: str, args: Sequence[Any]) -> Any:
        return self._rec_value(call_key(name, [_encode_call_arg(a) for a in args]))

    # -- member 参照 --------------------------------------------------------

    def __getattr__(self, name: str) -> Any:
        if not is_recordable_member(name):
            raise AttributeError(name)
        member = self._rec_member_record(name)
        if member["kind"] == MEMBER_ABSENT:
            # 記録された不在。未記録ではないので欠落履歴には積まない。
            raise AttributeError(name)
        if member["kind"] == MEMBER_METHOD:
            return _RecordedBoundMethod(self, name)
        if member["kind"] == MEMBER_VALUE:
            return self._rec_context.resolve(member["value"])
        raise fixture_schema.RecordedFixtureInvalid(
            "recorded member kind is not part of the schema: " + repr(member["kind"])
        )

    # ``attr:`` envelope は「member の種別」を持つ記録で、tagged value では
    # ないので汎用 resolve には掛けない。
    def _rec_member_record(self, name: str) -> Mapping[str, Any]:
        envelope = self._rec_envelope(attr_key(name))
        if "raises" in envelope:
            raised = envelope["raises"]
            raise RecordedCallFailure(raised["type"], raised["message"])
        return envelope["v"]

    # -- 記録対象の dunder --------------------------------------------------

    def __str__(self) -> str:
        return self._rec_call("__str__", ())

    def __bool__(self) -> bool:
        return self._rec_call("__bool__", ())

    def __len__(self) -> int:
        return self._rec_call("__len__", ())

    def __iter__(self):
        return iter(self._rec_call("__iter__", ()))

    def __getitem__(self, index):
        return self._rec_call("__getitem__", (index,))

    # -- 記録対象でない dunder ----------------------------------------------

    def __repr__(self) -> str:
        return "<RecordedObject {} {}>".format(self._rec_object_id, self._rec_kind)

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, RecordedObject):
            return NotImplemented
        # 同値類 id は fixture（= 片側 1 binary）ごとに振られる。左右で同じ
        # 番号が別の object を指すので、context をまたいで等しくしない。
        if other._rec_context is not self._rec_context:
            return False
        return self._rec_eq_group == other._rec_eq_group

    def __ne__(self, other: Any) -> bool:
        result = self.__eq__(other)
        if result is NotImplemented:
            return result
        return not result

    def __hash__(self) -> int:
        # ``__eq__`` は context も見るが、hash は同値類だけで決める。等しい
        # object の hash が一致すればよく、``id()`` のような run ごとに変わる
        # 値を混ぜると set / dict の反復順が run 間で変わる。
        return hash(("recorded-eq-group", self._rec_eq_group))

    # Ghidra object は解析にとって不透明な runtime leaf で、``_semantic_copy``
    # も identity を保つ（``core/analysis.py`` の ``deepcopy`` fallback）。
    def __copy__(self) -> "RecordedObject":
        return self

    def __deepcopy__(self, memo) -> "RecordedObject":
        return self


class _RecordedBoundMethod:
    """記録された member 呼び出し 1 つ。"""

    __slots__ = ("_owner", "_name")

    def __init__(self, owner: RecordedObject, name: str) -> None:
        self._owner = owner
        self._name = name

    def __call__(self, *args: Any) -> Any:
        return self._owner._rec_call(self._name, args)

    def __repr__(self) -> str:  # pragma: no cover - 診断用
        return "<RecordedBoundMethod {}.{}>".format(
            self._owner._rec_object_id, self._name
        )


def _encode_call_arg(value: Any) -> Any:
    if isinstance(value, RecordedObject):
        return ObjectRef(value._rec_object_id, value._rec_eq_group)
    if isinstance(value, (list, tuple)):
        return [_encode_call_arg(item) for item in value]
    return value


class RecordedProgram(RecordedObject):
    """fixture の root。``ReturnAnalyzer(program, decompiler=program.decompiler)``。

    ``decompiler`` / ``missing_accesses`` / ``access_log`` /
    ``assert_no_missing_accesses`` は記録 surface ではなく再生器の面で、
    instance 属性として先に解決されるので ``__getattr__`` を通らない。
    """

    @property
    def decompiler(self) -> "RecordedDecompiler":
        return self._rec_context.instance(self._rec_context.roots["decompiler"])

    @property
    def missing_accesses(self) -> List[MissingAccess]:
        return self._rec_context.missing_accesses

    @property
    def access_log(self) -> List[Tuple[str, str]]:
        return self._rec_context.access_log

    @property
    def fixture_header(self) -> Mapping[str, Any]:
        return self._rec_context.header

    def assert_no_missing_accesses(self) -> None:
        missing = self._rec_context.missing_accesses
        if missing:
            raise AssertionError(
                "recorded surface was incomplete ({} access(es)): {}".format(
                    len(missing),
                    "; ".join(
                        "{}:{} {}".format(a.kind, a.object_id, a.member_key)
                        for a in missing[:20]
                    ),
                )
            )

    def __repr__(self) -> str:
        return "<RecordedProgram {} {}>".format(
            self._rec_object_id, self._rec_context.header["binary"]["sha256"][:12]
        )


class RecordedDecompiler(RecordedObject):
    """``DecompInterface`` の再生。

    ``dispose()`` は記録器の ``RecordingDecompiler.dispose()`` と同じく no-op。
    実 decompiler の破棄は記録器の ``finally`` が持っており、両側で同じ宣言を
    置く（片側だけが持つ surface 定義を作らない）。
    """

    def dispose(self) -> None:
        return None

    def __repr__(self) -> str:
        return "<RecordedDecompiler {}>".format(self._rec_object_id)


def load_recorded_program(path) -> RecordedProgram:
    """fixture JSON を読み、その side の :class:`RecordedProgram` を返す。"""

    text = Path(path).read_text(encoding="utf-8")
    return recorded_program_from_payload(json.loads(text))


def recorded_program_from_payload(payload: Mapping[str, Any]) -> RecordedProgram:
    """読み込み済み fixture payload から :class:`RecordedProgram` を作る。

    欠落注入 test が payload を書き換えてから再生するために分けてある。
    """

    payload = fixture_schema.validate_fixture(payload)
    context = _RecordedContext(payload)
    program = context.instance(payload["roots"]["program"])
    if not isinstance(program, RecordedProgram):  # pragma: no cover - 防御
        raise fixture_schema.RecordedFixtureInvalid(
            "recorded fixture program root is not a RecordedProgram"
        )
    return program


def recorded_analyzer_factory(program, **kwargs):
    """``EquivalenceChecker(analyzer_factory=...)`` に渡す factory。

    記録側と同じ 2 点の DI だけを使う: ``ReturnAnalyzer(program, decompiler=...)``。
    記録器は同じ形の factory を ``RecordingDecompiler`` に対して使う。
    """

    from scripts.function_tracer_pcode.analysis import ReturnAnalyzer

    return ReturnAnalyzer(program, decompiler=program.decompiler, **kwargs)


__all__ = [
    "MissingAccess",
    "RecordedCallFailure",
    "RecordedDecompiler",
    "RecordedObject",
    "RecordedProgram",
    "RecordedSurfaceMissing",
    "load_recorded_program",
    "recorded_analyzer_factory",
    "recorded_program_from_payload",
]
