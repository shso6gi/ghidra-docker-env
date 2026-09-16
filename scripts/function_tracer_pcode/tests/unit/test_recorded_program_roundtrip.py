# -*- coding: utf-8 -*-
"""Issue #109 PR-A: 実 Ghidra 記録の再生 end-to-end と欠落検出。

記録は ``tests/tools/record_pcode_fixture.py`` が実バイナリ・実 Ghidra・実
``DecompInterface`` で行い、この test は **Ghidra を一切使わずに** 同じ
production path（production connector 付き ``check_from_binaries``）を走らせて

* decision receipt が出る
* canonical bundle の検証が通る
* 解析 snapshot（return 式 / 条件 / parameter / return ABI / side effect の
  書き込み先・条件・値・順序）が記録時と一致する
* 判定 snapshot（canonical outcome / c_active reason / q_open proof kind /
  decisive proof kind / conditional 列 / stage 経路）が一致する
* 左右とも ``missing_accesses == []``

を確かめる。「最終 outcome が同じ」だけの vacuous な test にしない。

欠落注入 test は、fixture から (a) 必須 API 1 件 (b) memory read 1 件を消して
再生し、**最終 outcome が偶然一致しても** 欠落履歴で fail することを示す。
"""

import copy
import importlib
import json
import shutil
import sys
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Tuple, cast

pytest = cast(Any, importlib.import_module("pytest"))

from scripts.function_tracer_pcode.tests.fixtures.pcode import schema as fixture_schema
from scripts.function_tracer_pcode.tests.fixtures.pcode.recorded_program import (
    MissingAccess,
    RecordedObject,
    RecordedProgram,
    RecordedSurfaceMissing,
    load_recorded_program,
    recorded_analyzer_factory,
    recorded_program_from_payload,
)
from scripts.function_tracer_pcode.tests.fixtures.pcode.snapshot import (
    AnalysisSnapshotCollector,
    check_snapshot,
)


CASE_DIR = Path(__file__).resolve().parents[1] / "fixtures" / "pcode" / "bessj0_snippet_B1_B2"


def _z3_available() -> bool:
    return shutil.which("z3") is not None


def _read(name: str) -> Any:
    return json.loads((CASE_DIR / name).read_text(encoding="utf-8"))


class _BlockedImportFinder:
    """再生中に Ghidra / PyGhidra / JPype を使わせない。

    ``ImportError`` を出すのは、Ghidra の無い環境と**同じ**振る舞いにするため。
    production には ``from ghidra... import X`` を ``try/except Exception`` で
    包んで object API へ落とす型判定 probe が複数あり（``core/signature.py``）、
    ここで別の例外を出すとその経路だけ再生と記録で食い違う。遮断した名前は
    記録しておき、decompiler が作られていないことを別に assert する。
    """

    def __init__(self, *prefixes: str) -> None:
        self._prefixes = prefixes
        self.blocked: list = []

    def find_module(self, fullname, path=None):  # pragma: no cover - 互換 API
        return self.find_spec(fullname, path)

    def find_spec(self, fullname, path=None, target=None):
        for prefix in self._prefixes:
            if fullname == prefix or fullname.startswith(prefix + "."):
                self.blocked.append(fullname)
                raise ImportError(
                    "replay must not use a real Ghidra runtime: " + fullname
                )
        return None


def _replay(
    left_payload: Mapping[str, Any],
    right_payload: Mapping[str, Any],
    *,
    case_id: str,
    monkeypatch,
) -> Tuple[RecordedProgram, RecordedProgram, Optional[Dict[str, Any]], Any, Any]:
    """記録と同じ production path を、記録済み object の上で走らせる。"""

    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        build_canonical_result_finalization_bundle,
        validate_canonical_result_finalization_bundle,
    )
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        build_default_cutover_connector,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        activate_process_worker_execution_authority_deployment,
    )
    from scripts.function_tracer_pcode.checker import EquivalenceChecker

    left = recorded_program_from_payload(left_payload)
    right = recorded_program_from_payload(right_payload)
    left_header = left.fixture_header
    right_header = right.fixture_header

    activate_process_worker_execution_authority_deployment(
        key_id="issue109a-replay-" + case_id,
        key=(case_id.encode() * 32)[:32],
        key_source_id="/tmp/issue109a-replay-" + case_id,
    )
    blocker = _BlockedImportFinder("ghidra", "pyghidra", "jpype")
    monkeypatch.setattr(sys, "meta_path", [blocker, *sys.meta_path])

    collector = AnalysisSnapshotCollector()
    checker = EquivalenceChecker(
        debug=False,
        identical_fast_path=bool(
            left_header["recording_mode"]["identical_fast_path"]
        ),
        analyzer_factory=collector.wrap(recorded_analyzer_factory),
    )
    checker.v2_dual_write_pilot_connector = build_default_cutover_connector()
    payload: Optional[Dict[str, Any]] = None
    failure: Optional[BaseException] = None
    try:
        result = checker.check_from_binaries(
            left, right,
            left_header["target"]["function_name"],
            right_header["target"]["function_name"],
            binary1_id=left_header["binary"]["binary_id"],
            binary2_id=right_header["binary"]["binary_id"],
            binary1_content_identity=("sha256", left_header["binary"]["sha256"]),
            binary2_content_identity=("sha256", right_header["binary"]["sha256"]),
        )
        payload = result.to_dict()
        finalization = getattr(result, "_canonical_finalization_context", None)
        if finalization is not None:
            evidence, session = finalization
            bundle = build_canonical_result_finalization_bundle(
                result_payload_preimage=payload,
                evidence=evidence, session=session,
            )
            validate_canonical_result_finalization_bundle(
                bundle, result_payload_preimage=payload,
            )
            payload["canonical_result_finalization_bundle"] = bundle
    except Exception as exc:  # 欠落注入では production 側が途中で落ちることもある
        failure = exc
        result = None
    # 実 decompiler を組み立てる経路（``lifecycle.get_decompiler`` の遅延生成）
    # に入っていないこと。型判定 probe の import 失敗は Ghidra 無し環境と同じ。
    assert "ghidra.app.decompiler" not in sys.modules
    assert "ghidra.app.decompiler" not in blocker.blocked
    return left, right, payload, collector, (result, failure)


@pytest.mark.skipif(not _z3_available(), reason="z3 is not available in PATH")
def test_recorded_pair_replays_the_production_check_without_ghidra(monkeypatch):
    left_payload = _read("left.json")
    right_payload = _read("right.json")
    left, right, payload, collector, (result, failure) = _replay(
        left_payload, right_payload, case_id="roundtrip", monkeypatch=monkeypatch,
    )
    assert failure is None, failure
    assert payload is not None

    # 記録に無い surface を一度も要求していないこと（production が例外を
    # 握り潰しても、これは潰れない）。
    assert left.missing_accesses == []
    assert right.missing_accesses == []
    left.assert_no_missing_accesses()
    right.assert_no_missing_accesses()

    # 判定は authority 側の決定面まで降りていること。
    assert result.decision_receipt is not None
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        outcome_from_payload,
    )

    assert outcome_from_payload(payload).value == payload["final_outcome"]

    # production connector を本当に通っていること: 封印された event stream と
    # decision receipt があり、execution payload が fixture の binary identity と
    # 関数名で作られている（fixture 専用の判定経路を作っていない）。
    bundle = payload["canonical_result_finalization_bundle"]
    assert bundle["sealed_event_stream"]
    assert bundle["decision_receipt"]
    assert bundle["execution_identity"]["result_occurrence_id"]
    # ``execution_payload`` は authority の canonical 形（key/value の組の列）。
    execution_payload = dict(bundle["execution_payload"])
    assert execution_payload["binary1_content_identity"] == (
        "sha256", left.fixture_header["binary"]["sha256"],
    )
    assert execution_payload["binary2_content_identity"] == (
        "sha256", right.fixture_header["binary"]["sha256"],
    )
    assert execution_payload["function_name1"] == "snippet"
    assert execution_payload["binary1_id"] == left.fixture_header["binary"]["binary_id"]
    assert execution_payload["binary2_id"] == right.fixture_header["binary"]["binary_id"]
    # 判定 lane が実際に動いていること（空の判定で一致した test にしない）。
    assert payload["c_active_base"]
    assert payload["q_open_base"]

    assert collector.payload() == _read("analysis_snapshot.json")
    assert check_snapshot(payload) == _read("check_snapshot.json")


def test_recorded_analysis_snapshot_is_not_only_an_outcome_comparison():
    """比較面が「件数だけ」「outcome だけ」になっていないことを固定する。"""

    snapshot = _read("analysis_snapshot.json")
    sides = snapshot["sides"]
    assert set(sides) == {"B1", "B2"}
    for side, entries in sides.items():
        assert entries, side
        for entry in entries:
            assert entry["function_name"] == "snippet"
            assert entry["entry_point"]
            # parameter は名前・幅・型・符号・ABI storage まで
            assert entry["parameters"]
            for parameter in entry["parameters"]:
                assert parameter["name"]
                assert parameter["size"]
                assert parameter["data_type"]
                assert parameter["storage"]["register_name"]
            # return ABI facts の sealed slot
            assert entry["return_abi_facts"]["calling_convention"]["status"] == "PRESENT"
            # return 式と条件（描画済みの決定的文字列）
            assert len(entry["returns"]) >= 2
            for info in entry["returns"]:
                assert info["value"]
                assert info["return_kind"]
                assert isinstance(info["conditions"], list)
            assert any(info["conditions"] for info in entry["returns"])
            # effect lane は書き込み先・条件・値・順序の面を持つ
            effects = entry["effect_summary"]
            assert effects is not None
            assert set(
                ["effects", "unsupported_call_sites", "parameter_names",
                 "has_unsupported_call", "incomplete_reasons", "synthetic_expr"]
            ) <= set(effects)
            for effect in effects["effects"]:
                assert set(
                    ["location", "location_stable_key", "conditions", "value",
                     "order_index", "order_key"]
                ) <= set(effect)
            # bessj0/snippet は store effect を持たないが、未要約 call site は
            # 引数と経路条件まで比較面に載る。
            assert effects["has_unsupported_call"] is True
            assert effects["unsupported_call_sites"]
            for site in effects["unsupported_call_sites"]:
                assert site["arguments"]
                assert site["path_conditions"]
                assert site["reason"]


def _delete_member(
    payload: Mapping[str, Any], *, kind_suffix: str, member_prefix: str,
) -> Tuple[str, str]:
    """`kind_suffix` の object から `member_prefix` の member を 1 件だけ消す。"""

    for object_id in sorted(payload["objects"]):
        entry = payload["objects"][object_id]
        if not entry["kind"].endswith(kind_suffix):
            continue
        for member_key in sorted(entry["members"]):
            if member_key.startswith(member_prefix):
                del entry["members"][member_key]
                return object_id, member_key
    raise AssertionError(
        "fixture has no {} member on {}".format(member_prefix, kind_suffix)
    )


@pytest.mark.skipif(not _z3_available(), reason="z3 is not available in PATH")
def test_deleting_one_required_api_is_detected(monkeypatch):
    """必須 API を 1 件消したら、欠落履歴と例外の両方で検出される。"""

    left_payload = _read("left.json")
    right_payload = _read("right.json")
    object_id, member_key = _delete_member(
        left_payload, kind_suffix="function.FunctionDB",
        member_prefix="call:getEntryPoint(",
    )
    left, _right, _payload, _collector, (_result, failure) = _replay(
        left_payload, right_payload, case_id="missing-api", monkeypatch=monkeypatch,
    )
    assert left.missing_accesses, (
        "deleting {} on {} was absorbed instead of recorded".format(
            member_key, object_id
        )
    )
    assert any(
        access.object_id == object_id and access.member_key == member_key
        for access in left.missing_accesses
    ), [access.as_tuple() for access in left.missing_accesses]
    with pytest.raises(AssertionError):
        left.assert_no_missing_accesses()
    # この削除は production に吸収されず ``RecordedSurfaceMissing`` まで出る。
    # 既定値・None・空へ黙って変換されていないことをここで固定する。
    assert isinstance(failure, RecordedSurfaceMissing)


@pytest.mark.skipif(not _z3_available(), reason="z3 is not available in PATH")
def test_deleting_one_memory_read_is_detected_even_though_the_outcome_matches(monkeypatch):
    """memory read を 1 件消しても最終 outcome と判定面は変わらない。

    つまり outcome 一致だけを見る test ではこの欠落を検出できない。検出して
    いるのは ``missing_accesses`` であることを、判定面の一致と同時に固定する。
    """

    left_payload = _read("left.json")
    right_payload = _read("right.json")
    object_id, member_key = _delete_member(
        left_payload, kind_suffix="mem.MemoryMapDB",
        member_prefix="call:getByte(",
    )
    left, _right, payload, _collector, (_result, failure) = _replay(
        left_payload, right_payload, case_id="missing-memory", monkeypatch=monkeypatch,
    )
    assert failure is None, failure
    assert payload is not None
    # 判定面は記録時と完全に一致する（= outcome では検出できない）。
    assert check_snapshot(payload) == _read("check_snapshot.json")

    assert left.missing_accesses, (
        "deleting memory read {} on {} was absorbed".format(member_key, object_id)
    )
    assert any(
        access.object_id == object_id and access.member_key == member_key
        for access in left.missing_accesses
    ), [access.as_tuple() for access in left.missing_accesses]
    with pytest.raises(AssertionError):
        left.assert_no_missing_accesses()


# --- 記録済み None / 空 / 未記録の区別 --------------------------------------


def _minimal_payload(
    members: Mapping[str, Any], *, side: str = "left",
) -> Dict[str, Any]:
    """schema を満たす最小の fixture（欠落 / 区別 / 検証 test の土台）。"""

    return {
        "header": {
            "schema": fixture_schema.RECORDED_PCODE_FIXTURE_SCHEMA,
            "fixture_id": "unit", "side": side,
            "recorded_at_utc": "1970-01-01T00:00:00+00:00",
            "recording_commit": "a" * 40, "recording_dirty": False,
            "analysis_source_digest": "b" * 64, "recorder_version": "2",
            "ghidra_version": "12.0.1", "pyghidra_version": "3.0.2",
            "binary": {
                "binary_id": "B1",
                "eqbench_relative_path": "bess/bessj0/Eq/source/newV-arm64-clang-O0",
                "sha256": "0" * 64, "size": 1, "kind": "object",
            },
            "eqbench": {
                "upstream_url": "git@github.com:shrBadihi/EqBench.git",
                "commit": "c" * 40,
            },
            "target": {"function_name": "f", "entry": "00100000"},
            "recording_mode": {"identical_fast_path": False, "connector": "production"},
        },
        "roots": {"program": "o0", "decompiler": "o1"},
        "objects": {
            "o0": {"kind": "ghidra.program.database.ProgramDB", "eq_group": 0,
                   "members": dict(members)},
            "o1": {"kind": "ghidra.app.decompiler.DecompInterface", "eq_group": 1,
                   "members": {}},
        },
    }


def test_recorded_none_and_recorded_empty_are_not_missing():
    payload = _minimal_payload({
        "attr:getImageBase": {"v": {"kind": "method"}},
        "call:getImageBase()": {"v": {"kind": "none"}},
        "attr:getSymbols": {"v": {"kind": "method"}},
        "call:getSymbols()": {"v": {"kind": "list", "items": []}},
    })
    program = recorded_program_from_payload(payload)
    assert program.getImageBase() is None
    assert program.getSymbols() == []
    assert program.missing_accesses == []
    program.assert_no_missing_accesses()


def test_unrecorded_member_is_not_silently_converted():
    program = recorded_program_from_payload(_minimal_payload({}))
    with pytest.raises(RecordedSurfaceMissing):
        program.getImageBase()
    assert [access.member_key for access in program.missing_accesses] == [
        "attr:getImageBase"
    ]


def test_unrecorded_call_on_a_recorded_method_is_not_silently_converted():
    program = recorded_program_from_payload(_minimal_payload({
        "attr:getByte": {"v": {"kind": "method"}},
    }))
    method = program.getByte
    with pytest.raises(RecordedSurfaceMissing):
        method(7)
    assert [access.member_key for access in program.missing_accesses] == [
        "call:getByte(int:7)"
    ]


def test_recorded_absence_is_an_attribute_error_and_not_a_missing_access():
    program = recorded_program_from_payload(_minimal_payload({
        "attr:getModelName": {"v": {"kind": "absent"}},
    }))
    assert getattr(program, "getModelName", None) is None
    assert program.missing_accesses == []


def test_recorded_exception_is_replayed_as_a_failure_not_as_a_missing_access():
    from scripts.function_tracer_pcode.tests.fixtures.pcode.recorded_program import (
        RecordedCallFailure,
    )

    program = recorded_program_from_payload(_minimal_payload({
        "attr:getImageBase": {"v": {"kind": "method"}},
        "call:getImageBase()": {
            "raises": {"type": "java.lang.RuntimeException", "message": "boom"},
        },
    }))
    with pytest.raises(RecordedCallFailure):
        program.getImageBase()
    assert program.missing_accesses == []


def test_a_different_decompile_timeout_is_missing_not_a_decompile_failure():
    """再生側の timeout ずれを「decompile 失敗 → UNKNOWN」に変換しない。

    記録された呼び出しと違う timeout での ``decompileFunction`` は、
    ``decompileCompleted() == False`` のような**解析結果**ではなく、未記録
    surface として扱う。
    """

    payload = _minimal_payload({})
    payload["objects"]["o1"]["members"] = {
        "attr:decompileFunction": {"v": {"kind": "method"}},
        "call:decompileFunction(none,int:60,none)": {
            "v": {"kind": "ref", "id": "o2"},
        },
    }
    payload["objects"]["o2"] = {
        "kind": "ghidra.app.decompiler.DecompileResults", "eq_group": 2,
        "members": {
            "attr:decompileCompleted": {"v": {"kind": "method"}},
            "call:decompileCompleted()": {"v": {"kind": "bool", "value": True}},
        },
    }
    program = recorded_program_from_payload(payload)
    decompiler = program.decompiler
    assert decompiler.decompileFunction(None, 60, None).decompileCompleted() is True
    with pytest.raises(RecordedSurfaceMissing):
        decompiler.decompileFunction(None, 30, None)
    assert [access.member_key for access in program.missing_accesses] == [
        "call:decompileFunction(none,int:30,none)"
    ]


def test_sequence_exhaustion_is_a_missing_access_not_a_repeat():
    """状態を持つ API の観測列を使い切ったら、既定値にも最後の値にもしない。"""

    program = recorded_program_from_payload(_minimal_payload({
        "attr:getIterator": {"v": {"kind": "method"}},
        "call:getIterator()": {"seq": [
            {"v": {"kind": "int", "value": 1}},
            {"v": {"kind": "int", "value": 2}},
        ]},
    }))
    assert program.getIterator() == 1
    assert program.getIterator() == 2
    assert program.missing_accesses == []
    with pytest.raises(RecordedSurfaceMissing):
        program.getIterator()
    assert [access.member_key for access in program.missing_accesses] == [
        "call:getIterator()#2"
    ]
    # 使い切った後も、繰り返すたびに欠落として積まれる（黙って通さない）。
    with pytest.raises(RecordedSurfaceMissing):
        program.getIterator()
    assert len(program.missing_accesses) == 2


def test_sequence_positions_are_tracked_per_object_and_key():
    payload = _minimal_payload({
        "attr:getIterator": {"v": {"kind": "method"}},
        "call:getIterator()": {"seq": [
            {"v": {"kind": "int", "value": 1}},
            {"v": {"kind": "int", "value": 2}},
        ]},
        "attr:getName": {"v": {"kind": "method"}},
        "call:getName()": {"seq": [
            {"v": {"kind": "str", "value": "a"}},
            {"v": {"kind": "str", "value": "b"}},
        ]},
    })
    program = recorded_program_from_payload(payload)
    other = recorded_program_from_payload(copy.deepcopy(payload))
    assert program.getIterator() == 1
    assert program.getName() == "a"
    assert program.getIterator() == 2
    # 別 fixture の位置は独立している。
    assert other.getIterator() == 1
    assert program.missing_accesses == []
    assert other.missing_accesses == []


def test_record_and_replay_agree_on_java_equality_and_identity():
    """同値類と同一性の意味が、記録側 proxy と再生側 object で一致すること。"""

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture

    recording = record_pcode_fixture.RecordingProxy
    replayed = RecordedObject
    # どちらも「同じ recorder / context の、同じ同値類」だけを等しいとする。
    for owner in (recording, replayed):
        assert "__eq__" in owner.__dict__
        assert "__ne__" in owner.__dict__
        assert "__hash__" in owner.__dict__

    class _FakeRecorder:
        """``RecordingProxy`` が同値類の比較に使う面だけを持つ最小の recorder。"""

        def __init__(self, groups):
            self._groups = groups

        def object_id(self, index):
            return "o{}".format(index)

        def entry(self, index):
            return {"eq_group": self._groups[index]}

    left_recorder = _FakeRecorder({0: 7, 1: 7, 2: 9})
    right_recorder = _FakeRecorder({0: 7})
    a = recording(left_recorder, 0, object())
    b = recording(left_recorder, 1, object())
    c = recording(left_recorder, 2, object())
    other_side = recording(right_recorder, 0, object())
    assert a == b and hash(a) == hash(b)
    assert a != c
    assert a != other_side        # 左右の同値類 id は別採番
    assert a != object()

    payload = _minimal_payload({
        "attr:getMemory": {"v": {"kind": "method"}},
        "call:getMemory()": {"v": {"kind": "ref", "id": "o2"}},
        "attr:getListing": {"v": {"kind": "method"}},
        "call:getListing()": {"v": {"kind": "ref", "id": "o3"}},
    })
    payload["objects"]["o2"] = {
        "kind": "ghidra.program.model.address.GenericAddress", "eq_group": 7,
        "members": {},
    }
    payload["objects"]["o3"] = {
        "kind": "ghidra.program.model.address.GenericAddress", "eq_group": 9,
        "members": {},
    }
    program = recorded_program_from_payload(payload)
    replay_a = program.getMemory()
    replay_c = program.getListing()
    # 記録側と同じ結論になる（同値類 7 同士は等しく、7 と 9 は等しくない）。
    assert (a == b) == (replay_a == program.getMemory())
    assert (a == c) == (replay_a == replay_c)
    assert hash(replay_a) == hash(a)


def test_recorded_object_hash_does_not_use_randomized_string_hash():
    """hash は同値類の int だけから決める（process ごとに変わらない）。"""

    program = recorded_program_from_payload(_minimal_payload({}))
    assert hash(program) == hash(0)
    assert hash(fixture_schema.ObjectRef("o0", 5)) == hash(5)


def test_recorded_objects_share_identity_and_java_equality_classes():
    payload = _minimal_payload({
        "attr:getMemory": {"v": {"kind": "method"}},
        "call:getMemory()": {"v": {"kind": "ref", "id": "o2"}},
        "attr:getListing": {"v": {"kind": "method"}},
        "call:getListing()": {"v": {"kind": "ref", "id": "o3"}},
    })
    payload["objects"]["o2"] = {
        "kind": "ghidra.program.model.address.GenericAddress", "eq_group": 7,
        "members": {},
    }
    payload["objects"]["o3"] = {
        "kind": "ghidra.program.model.address.GenericAddress", "eq_group": 7,
        "members": {},
    }
    program = recorded_program_from_payload(payload)
    first = program.getMemory()
    second = program.getListing()
    assert first is program.getMemory()
    assert first is not second
    # 同じ Java 同値類（``equals``）は再生でも等しく、hash も一致する。
    assert first == second
    assert hash(first) == hash(second)
    # 同値類 id は fixture ごとの採番なので、別 fixture の同じ番号とは
    # 等しくならない（左右の object を取り違えない）。
    other_program = recorded_program_from_payload(copy.deepcopy(payload))
    assert other_program.getMemory() != first
    assert other_program != program
    assert other_program.getMemory() == other_program.getListing()
    # hash は同値類だけで決める（``id()`` を混ぜると set の反復順が run 間で
    # 変わり、記録が非決定になる）。等しくない object が同じ hash でもよい。
    assert hash(other_program.getMemory()) == hash(first)


# --- fixture の直列化 / schema -----------------------------------------------


def test_fixture_serialization_round_trip_is_byte_stable():
    for name in ("left.json", "right.json"):
        text = (CASE_DIR / name).read_text(encoding="utf-8")
        payload = fixture_schema.loads(text)
        assert fixture_schema.dumps(payload) == text
        assert fixture_schema.dumps(json.loads(fixture_schema.dumps(payload))) == text


def _rejects(payload: Any) -> None:
    with pytest.raises(fixture_schema.RecordedFixtureInvalid):
        fixture_schema.validate_fixture(payload)


def test_fixture_schema_rejects_unknown_and_missing_keys():
    payload = _minimal_payload({})
    fixture_schema.validate_fixture(payload)

    for key in ("header", "roots", "objects"):
        missing = copy.deepcopy(payload)
        del missing[key]
        _rejects(missing)
    extra = copy.deepcopy(payload)
    extra["extra"] = 1
    _rejects(extra)

    for key in sorted(fixture_schema.HEADER_KEYS):
        missing = copy.deepcopy(payload)
        del missing["header"][key]
        _rejects(missing)
    unknown_header = copy.deepcopy(payload)
    unknown_header["header"]["note"] = "x"
    _rejects(unknown_header)

    for section, keys in (
        ("binary", fixture_schema.BINARY_KEYS),
        ("eqbench", fixture_schema.EQBENCH_KEYS),
        ("target", fixture_schema.TARGET_KEYS),
        ("recording_mode", fixture_schema.RECORDING_MODE_KEYS),
    ):
        for key in sorted(keys):
            missing = copy.deepcopy(payload)
            del missing["header"][section][key]
            _rejects(missing)
        unknown = copy.deepcopy(payload)
        unknown["header"][section]["note"] = "x"
        _rejects(unknown)

    for key in sorted(fixture_schema.ROOT_KEYS):
        missing = copy.deepcopy(payload)
        del missing["roots"][key]
        _rejects(missing)
    unknown_root = copy.deepcopy(payload)
    unknown_root["roots"]["other"] = "o0"
    _rejects(unknown_root)
    dangling_root = copy.deepcopy(payload)
    dangling_root["roots"]["program"] = "o404"
    _rejects(dangling_root)

    for key in sorted(fixture_schema.OBJECT_KEYS):
        missing = copy.deepcopy(payload)
        del missing["objects"]["o0"][key]
        _rejects(missing)
    unknown_object = copy.deepcopy(payload)
    unknown_object["objects"]["o0"]["note"] = "x"
    _rejects(unknown_object)


def test_fixture_schema_rejects_inexact_scalars():
    payload = _minimal_payload({})
    _rejects(_with_header(payload, "schema", "recorded-pcode-fixture-v2"))
    _rejects(_with_header(payload, "side", "middle"))
    _rejects(_with_header(payload, "recording_commit", "a" * 39))
    _rejects(_with_header(payload, "recording_commit", "A" * 40))
    _rejects(_with_header(payload, "analysis_source_digest", "b" * 63))
    _rejects(_with_header(payload, "recording_dirty", 0))
    _rejects(_with_header(payload, "recorder_version", 2))

    binary = copy.deepcopy(payload)
    binary["header"]["binary"]["sha256"] = "0" * 63
    _rejects(binary)
    binary = copy.deepcopy(payload)
    binary["header"]["binary"]["size"] = "1"
    _rejects(binary)
    binary = copy.deepcopy(payload)
    binary["header"]["binary"]["size"] = 0
    _rejects(binary)
    binary = copy.deepcopy(payload)
    binary["header"]["binary"]["eqbench_relative_path"] = "/abs/path"
    _rejects(binary)
    binary = copy.deepcopy(payload)
    binary["header"]["binary"]["eqbench_relative_path"] = "../escape"
    _rejects(binary)

    eqbench = copy.deepcopy(payload)
    eqbench["header"]["eqbench"]["commit"] = "c" * 41
    _rejects(eqbench)

    mode = copy.deepcopy(payload)
    mode["header"]["recording_mode"]["connector"] = "fixture"
    _rejects(mode)
    mode = copy.deepcopy(payload)
    mode["header"]["recording_mode"]["identical_fast_path"] = 0
    _rejects(mode)

    entry = copy.deepcopy(payload)
    entry["header"]["target"]["entry"] = None
    _rejects(entry)

    eq_group = copy.deepcopy(payload)
    eq_group["objects"]["o0"]["eq_group"] = True
    _rejects(eq_group)


def _with_header(payload: Mapping[str, Any], key: str, value: Any) -> Dict[str, Any]:
    broken = copy.deepcopy(payload)
    broken["header"][key] = value
    return broken


def test_fixture_schema_rejects_malformed_members_and_values():
    base = _minimal_payload({})

    unknown_member = copy.deepcopy(base)
    unknown_member["objects"]["o0"]["members"]["getImageBase"] = {"v": {"kind": "none"}}
    _rejects(unknown_member)

    both = copy.deepcopy(base)
    both["objects"]["o0"]["members"]["attr:x"] = {
        "v": {"kind": "none"}, "raises": {"type": "t", "message": "m"},
    }
    _rejects(both)

    for envelope in (
        {"v": {"kind": "bool", "value": 1}},
        {"v": {"kind": "int", "value": True}},
        {"v": {"kind": "int", "value": "1"}},
        {"v": {"kind": "str", "value": 1}},
        {"v": {"kind": "float", "value": 1.5}},
        {"v": {"kind": "float", "value": "not-a-float"}},
        {"v": {"kind": "bytes", "value": "0g"}},
        {"v": {"kind": "list", "items": {}}},
        {"v": {"kind": "ref", "id": "o404"}},
        {"v": {"kind": "ref"}},
        {"v": {"kind": "none", "value": 1}},
        {"v": {"kind": "smuggled", "value": 1}},
        {"raises": {"type": "t"}},
        {"raises": {"type": "t", "message": "m", "extra": 1}},
        {"seq": [{"v": {"kind": "none"}}]},
        {"seq": {"0": {"v": {"kind": "none"}}}},
        {"seq": [{"v": {"kind": "none"}}, {"v": {"kind": "smuggled"}}]},
    ):
        broken = copy.deepcopy(base)
        broken["objects"]["o0"]["members"]["call:probe()"] = envelope
        _rejects(broken)

    for member in (
        {"kind": "method", "value": {"kind": "none"}},
        {"kind": "value"},
        {"kind": "smuggled"},
    ):
        broken = copy.deepcopy(base)
        broken["objects"]["o0"]["members"]["attr:probe"] = {"v": member}
        _rejects(broken)

    unclosed = copy.deepcopy(base)
    unclosed["objects"]["o0"]["members"]["call:probe("] = {"v": {"kind": "none"}}
    _rejects(unclosed)


def _identity_value(side: str, member: str, group: int) -> Dict[str, Any]:
    return {
        "kind": "identity_surrogate", "member": member, "group": group,
        "value": fixture_schema.canonical_identity_surrogate(side, member, group),
    }


def test_fixture_schema_rejects_identity_surrogates_outside_their_contract():
    base = _minimal_payload({"attr:hashCode": {"v": {"kind": "method"}}})
    good = copy.deepcopy(base)
    good["objects"]["o0"]["members"]["call:hashCode()"] = {
        "v": _identity_value("left", "hashCode", 0),
    }
    fixture_schema.validate_fixture(good)

    # 宣言されていない member を identity surrogate にできない。
    undeclared = copy.deepcopy(good)
    undeclared["objects"]["o0"]["members"]["call:getName()"] = {
        "v": {
            "kind": "identity_surrogate", "member": "getName", "group": 0,
            "value": fixture_schema.canonical_identity_surrogate(
                "left", "hashCode", 0
            ),
        },
    }
    _rejects(undeclared)

    # member 名と key がずれていたら拒否する。
    mismatched = copy.deepcopy(good)
    mismatched["objects"]["o0"]["members"]["call:hashCode()"]["v"]["member"] = (
        "getUniqueProgramID"
    )
    _rejects(mismatched)

    # 反対側の帯域の surrogate は拒否する（左右の取り違え）。
    wrong_side = copy.deepcopy(good)
    wrong_side["objects"]["o0"]["members"]["call:hashCode()"]["v"]["value"] = (
        fixture_schema.canonical_identity_surrogate("right", "hashCode", 0)
    )
    _rejects(wrong_side)

    # 別 member の帯域の値も拒否する。
    wrong_member_band = copy.deepcopy(good)
    wrong_member_band["objects"]["o0"]["members"]["call:hashCode()"]["v"]["value"] = (
        fixture_schema.canonical_identity_surrogate("left", "getUniqueProgramID", 0)
    )
    _rejects(wrong_member_band)

    # group と value の不一致（どちらを改竄しても落ちる）。
    tampered_value = copy.deepcopy(good)
    tampered_value["objects"]["o0"]["members"]["call:hashCode()"]["v"]["value"] += 1
    _rejects(tampered_value)
    tampered_group = copy.deepcopy(good)
    tampered_group["objects"]["o0"]["members"]["call:hashCode()"]["v"]["group"] = 7
    _rejects(tampered_group)

    for broken in ("value", "group"):
        not_int = copy.deepcopy(good)
        not_int["objects"]["o0"]["members"]["call:hashCode()"]["v"][broken] = "1"
        _rejects(not_int)
        missing = copy.deepcopy(good)
        del missing["objects"]["o0"]["members"]["call:hashCode()"]["v"][broken]
        _rejects(missing)

    negative_group = copy.deepcopy(good)
    negative_group["objects"]["o0"]["members"]["call:hashCode()"]["v"]["group"] = -1
    negative_group["objects"]["o0"]["members"]["call:hashCode()"]["v"]["value"] = (
        fixture_schema.canonical_identity_surrogate("left", "hashCode", 0) - 1
    )
    _rejects(negative_group)


def test_fixture_schema_rejects_inconsistent_identity_groups_across_objects():
    """fixture 全体で (member, group) と value が 1 対 1 であること。"""

    base = _minimal_payload({"attr:hashCode": {"v": {"kind": "method"}}})
    base["objects"]["o0"]["members"]["call:hashCode()"] = {
        "v": _identity_value("left", "hashCode", 0),
    }
    base["objects"]["o1"]["members"] = {
        "attr:hashCode": {"v": {"kind": "method"}},
        "call:hashCode()": {"v": _identity_value("left", "hashCode", 1)},
    }
    fixture_schema.validate_fixture(base)

    # 同じ group が 2 つの値を持つ。
    two_values = copy.deepcopy(base)
    two_values["objects"]["o1"]["members"]["call:hashCode()"]["v"]["group"] = 0
    _rejects(two_values)

    # 同じ値が 2 つの group に使い回される。
    two_groups = copy.deepcopy(base)
    two_groups["objects"]["o1"]["members"]["call:hashCode()"]["v"]["value"] = (
        fixture_schema.canonical_identity_surrogate("left", "hashCode", 0)
    )
    _rejects(two_groups)


# --- identity surrogate: raw 値の同値関係が保存されること --------------------


def test_identity_ledger_preserves_a_hash_collision_between_unequal_receivers():
    """``hashCode`` の collision は合法。実観測の collision を壊さない。"""

    ledger = fixture_schema.IdentitySurrogateLedger("left")
    first = ledger.assign("hashCode", 0x5EED, receiver_equality_class=1)
    second = ledger.assign("hashCode", 0x5EED, receiver_equality_class=2)
    assert first == second, "unequal receivers sharing a raw hash must share a surrogate"


def test_identity_ledger_separates_unequal_receivers_with_different_raw_hashes():
    ledger = fixture_schema.IdentitySurrogateLedger("left")
    first = ledger.assign("hashCode", 11, receiver_equality_class=1)
    second = ledger.assign("hashCode", 22, receiver_equality_class=2)
    assert first != second
    assert first[1] != second[1]


def test_identity_ledger_keeps_java_equal_receivers_on_one_surrogate():
    ledger = fixture_schema.IdentitySurrogateLedger("left")
    first = ledger.assign("hashCode", 77, receiver_equality_class=5)
    second = ledger.assign("hashCode", 77, receiver_equality_class=5)
    assert first == second


def test_identity_ledger_fails_closed_when_java_equal_receivers_disagree():
    """``a.equals(b) => a.hashCode() == b.hashCode()`` が破れたら記録を止める。"""

    ledger = fixture_schema.IdentitySurrogateLedger("left")
    ledger.assign("hashCode", 77, receiver_equality_class=5)
    with pytest.raises(fixture_schema.IdentityContractViolation):
        ledger.assign("hashCode", 78, receiver_equality_class=5)


def test_identity_ledger_maps_one_program_id_to_one_surrogate():
    ledger = fixture_schema.IdentitySurrogateLedger("left")
    first = ledger.assign("getUniqueProgramID", 4242, receiver_equality_class=0)
    # 受け手が違っても raw 値が同じなら同じ surrogate。
    second = ledger.assign("getUniqueProgramID", 4242, receiver_equality_class=9)
    assert first == second
    other = ledger.assign("getUniqueProgramID", 4243, receiver_equality_class=0)
    assert other != first


def test_identity_ledger_bands_are_disjoint_across_sides_and_members():
    left = fixture_schema.IdentitySurrogateLedger("left")
    right = fixture_schema.IdentitySurrogateLedger("right")
    values = set()
    for ledger in (left, right):
        for member in sorted(fixture_schema.IDENTITY_DERIVED_METHODS):
            for raw in (1, 2, 3):
                _group, value = ledger.assign(
                    member, raw, receiver_equality_class=raw,
                )
                assert value not in values
                values.add(value)
    assert len(values) == 2 * len(fixture_schema.IDENTITY_DERIVED_METHODS) * 3


def test_identity_surrogates_depend_only_on_the_equality_relation_of_raw_values():
    """raw 値が run ごとに変わっても、同値関係が同じなら結果が同じ。"""

    relation = [(0, 1), (0, 2), (1, 3), (0, 4), (2, 5)]  # (class index, receiver)
    runs = (
        [7, 7, 900001, 7, 123],            # 昇順でない / 桁もばらばら
        [999999999, 999999999, 1, 999999999, 500],   # 大小関係を逆にした
        [-5, -5, -900, -5, 0],             # 負値
    )
    outputs = []
    for raw_values in runs:
        ledger = fixture_schema.IdentitySurrogateLedger("left")
        outputs.append([
            ledger.assign("hashCode", raw, receiver_equality_class=receiver)
            for (_class_index, receiver), raw in zip(relation, raw_values)
        ])
    assert outputs[0] == outputs[1] == outputs[2]
    # 同値関係そのものは保たれている（1 番目と 2 番目と 4 番目が同じ class）。
    groups = [group for group, _value in outputs[0]]
    assert groups[0] == groups[1] == groups[3]
    assert len(set(groups)) == 3


def test_identity_ledger_rejects_undeclared_members_and_non_integers():
    ledger = fixture_schema.IdentitySurrogateLedger("left")
    with pytest.raises(fixture_schema.IdentityContractViolation):
        ledger.assign("getName", 1, receiver_equality_class=0)
    for raw in (True, "1", 1.0, None):
        with pytest.raises(fixture_schema.IdentityContractViolation):
            ledger.assign("hashCode", raw, receiver_equality_class=0)


def test_synthetic_recording_canonicalizes_identity_values(monkeypatch):
    """記録 proxy 経由でも、raw 値が変わって同値関係が同じなら記録が同じ。"""

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture

    def record_run(raw_hashes):
        recorder = _SyntheticRecorder("left")
        proxies = [
            record_pcode_fixture.RecordingProxy(
                recorder, index, _SyntheticBlock(raw),
            )
            for index, raw in enumerate(raw_hashes)
        ]
        for proxy in proxies:
            proxy.hashCode()
        return recorder.stored

    first = record_run([3, 3, 71])
    second = record_run([88888888, 88888888, 2])
    assert first == second
    # collision（先頭 2 つ）は同じ surrogate のまま、3 つ目は別。
    values = [
        entry["v"]["value"] for entry in first
        if entry["v"].get("kind") == "identity_surrogate"
    ]
    assert len(values) == 3
    assert values[0] == values[1] != values[2]


def test_synthetic_recording_fails_closed_on_a_broken_hash_contract():
    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture

    recorder = _SyntheticRecorder("left", equality_classes={0: 4, 1: 4})
    first = record_pcode_fixture.RecordingProxy(recorder, 0, _SyntheticBlock(10))
    second = record_pcode_fixture.RecordingProxy(recorder, 1, _SyntheticBlock(11))
    first.hashCode()
    with pytest.raises(record_pcode_fixture.RecordingError):
        second.hashCode()


class _SyntheticBlock:
    """``hashCode()`` だけを持つ、記録対象の代役。"""

    def __init__(self, raw: int) -> None:
        self._raw = raw

    def hashCode(self) -> int:
        return self._raw


class _SyntheticRecorder:
    """``RecordingProxy`` が使う面だけを持つ最小の recorder。"""

    def __init__(self, side: str, equality_classes: Optional[Dict[int, int]] = None) -> None:
        self.identity_ledger = fixture_schema.IdentitySurrogateLedger(side)
        self._equality_classes = equality_classes or {}
        self.stored: list = []

    def object_id(self, index: int) -> str:
        return "o{}".format(index)

    def entry(self, index: int) -> Dict[str, Any]:
        return {"eq_group": self._equality_classes.get(index, index)}

    def key_arg(self, value: Any) -> Any:
        return value

    def note_call(self, index: int, member_key: str, name: str, args: Tuple) -> None:
        return None

    def store(self, index: int, member_key: str, envelope: Mapping[str, Any]) -> None:
        self.stored.append(dict(envelope))

    def capture(self, value: Any) -> Tuple[Any, Dict[str, Any]]:  # pragma: no cover
        raise AssertionError("identity members must not reach the generic capture")


class _FakeJavaMap:
    """``IdentityHashMap`` / ``HashMap`` の、記録器が使う面だけの代役。"""

    def __init__(self) -> None:
        self._entries: Dict[Any, Any] = {}

    def get(self, key: Any) -> Any:
        return self._entries.get(id(key))

    def put(self, key: Any, value: Any) -> None:
        self._entries[id(key)] = value


class _FakeJPype:
    """``Recorder`` が起動時に引く JPype の面だけの代役（production 経路は不変）。"""

    @staticmethod
    def JClass(name: str) -> Any:
        if name == "java.lang.Integer":
            return int
        return _FakeJavaMap


def _synthetic_recorder_instance(side: str = "left"):
    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture

    return record_pcode_fixture.Recorder(_FakeJPype, side)


def test_saturation_does_not_recall_an_already_observed_count_api():
    """飽和は production が観測済みの key を呼び直さない。

    件数 API が状態を持っていた場合、呼び直すと production の観測列に
    観測を足してしまう（`seq` の位置がずれる）。
    """

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture

    recorder = _synthetic_recorder_instance()
    calls = []

    class _CountingOp:
        def getNumInputs(self):
            calls.append("called")
            return 2

    proxy = recorder.proxy_for(_CountingOp())
    # production が 1 回観測する。
    assert proxy.getNumInputs() == 2
    assert calls == ["called"]
    # 飽和はその観測を読むだけで、実 API を呼び直さない。
    assert recorder._counted(proxy._rec_index, proxy, "getNumInputs") == 2
    assert calls == ["called"]
    observations = recorder._entries[proxy._rec_index]["observations"]
    assert len(observations[record_pcode_fixture.call_key("getNumInputs", ())]) == 1


# --- saturation は soundness 例外を握り潰さない ------------------------------


class _ContractBreakingBlock:
    """飽和で初めて呼ばれたときに Java の hash 契約を破る object。

    production 本流では ``getIndex()`` しか呼ばれず、``hashCode()`` は飽和が
    kind census から広げたときに初めて呼ばれる。
    """

    def __init__(self, index: int, raw_hash: int) -> None:
        self._index = index
        self._raw_hash = raw_hash

    def getIndex(self) -> int:
        return self._index

    def hashCode(self) -> int:
        return self._raw_hash


def test_saturation_propagates_a_recording_error_instead_of_swallowing_it(monkeypatch):
    """飽和中の identity 契約違反は記録全体を失敗させる（握り潰さない）。

    終了条件（:meth:`Recorder.saturation_is_settled`）を足しても、soundness に
    関わる `RecordingError` は best-effort の例外処理を素通りする。
    """

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture

    recorder = _synthetic_recorder_instance()
    # 飽和対象の kind を名乗らせる（IR kind census が広がる対象になる）。
    monkeypatch.setattr(
        record_pcode_fixture, "_java_class_name",
        lambda value: "ghidra.program.model.pcode.PcodeBlockBasic",
    )
    first = recorder.proxy_for(_ContractBreakingBlock(0, 111))
    second = recorder.proxy_for(_ContractBreakingBlock(1, 222))
    # 2 つは Java-equal（同じ同値類）だが raw hash が違う、という観測にする。
    recorder._entries[second._rec_index]["eq_group"] = (
        recorder._entries[first._rec_index]["eq_group"]
    )
    # production 本流では hashCode を呼ばない。census に載せるのは片側だけ。
    assert first.getIndex() == 0
    assert second.getIndex() == 1
    assert first.hashCode() == fixture_schema.canonical_identity_surrogate(
        "left", "hashCode", 0,
    )

    with pytest.raises(record_pcode_fixture.RecordingError):
        recorder.saturate()


def test_saturation_terminates_when_a_member_keeps_failing(monkeypatch):
    """普通の Ghidra API failure は best-effort のまま、loop は必ず終わる。"""

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture

    calls = []

    class _FlakyBlock:
        def getIndex(self):
            return 0

        def getStart(self):
            calls.append("start")
            raise RuntimeError("ghidra says no")

    recorder = _synthetic_recorder_instance()
    monkeypatch.setattr(
        record_pcode_fixture, "_java_class_name",
        lambda value: "ghidra.program.model.pcode.PcodeBlockBasic",
    )
    proxy = recorder.proxy_for(_FlakyBlock())
    with pytest.raises(RuntimeError):
        proxy.getStart()
    assert proxy.getIndex() == 0
    # 例外は観測として記録されるので、飽和は同じ key を再発行せず終わる。
    recorder.saturate()
    assert calls == ["start"]
    recorder.collapse()
    members = recorder._entries[proxy._rec_index]["members"]
    assert "raises" in members[record_pcode_fixture.call_key("getStart", ())]


# --- saturation の終了性（call key が作られない member でも止まる）-----------


def _ir_kind(monkeypatch):
    """object を IR kind（飽和対象）に見せる。"""

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture

    monkeypatch.setattr(
        record_pcode_fixture, "_java_class_name",
        lambda value: "ghidra.program.model.pcode.PcodeBlockBasic",
    )


class _Peer:
    """``getIndex()`` だけを持つ飽和対象。census の出所になる。"""

    def __init__(self, index: int) -> None:
        self._index = index

    def getIndex(self) -> int:
        return self._index


class _PeerWithoutTheMember:
    """census にある ``getStart`` を**持たない** peer（``attr`` は absent）。"""

    def getIndex(self) -> int:
        return 1


class _PeerWithNonCallableMember:
    """``getStart`` が callable でない値である peer。"""

    def __init__(self) -> None:
        self.getStart = 7

    def getIndex(self) -> int:
        return 1


class _PeerWhoseGetattrRaises:
    """``getStart`` の ``getattr`` 自体が通常例外になる peer。"""

    def getIndex(self) -> int:
        return 1

    def __getattr__(self, name):
        if name == "getStart":
            raise RuntimeError("ghidra refuses the attribute")
        raise AttributeError(name)


def _saturation_reaches_a_fixpoint(monkeypatch, peer) -> Any:
    """census を作った peer と、問題のある peer を並べて飽和させる。"""

    _ir_kind(monkeypatch)
    recorder = _synthetic_recorder_instance()

    class _Source:
        def getIndex(self):
            return 0

        def getStart(self):
            return 4096

    source = recorder.proxy_for(_Source())
    assert source.getIndex() == 0
    assert source.getStart() == 4096       # census に getStart が載る
    other = recorder.proxy_for(peer)
    assert other.getIndex() == 1
    recorder.saturate()                    # 旧実装ではここが終わらない
    return recorder, other


def test_saturation_terminates_when_a_peer_lacks_the_member(monkeypatch):
    recorder, other = _saturation_reaches_a_fixpoint(
        monkeypatch, _PeerWithoutTheMember(),
    )
    observations = recorder._entries[other._rec_index]["observations"]
    # 「その member は無い」という観測だけが残り、call key は作られない。
    assert observations["attr:getStart"][0]["v"]["kind"] == "absent"
    assert "call:getStart()" not in observations


def test_saturation_terminates_when_a_peer_member_is_not_callable(monkeypatch):
    recorder, other = _saturation_reaches_a_fixpoint(
        monkeypatch, _PeerWithNonCallableMember(),
    )
    observations = recorder._entries[other._rec_index]["observations"]
    assert observations["attr:getStart"][0]["v"]["kind"] == "value"
    assert "call:getStart()" not in observations


def test_saturation_terminates_when_getattr_itself_raises(monkeypatch):
    recorder, other = _saturation_reaches_a_fixpoint(
        monkeypatch, _PeerWhoseGetattrRaises(),
    )
    observations = recorder._entries[other._rec_index]["observations"]
    assert "raises" in observations["attr:getStart"][0]
    assert "call:getStart()" not in observations


def test_saturation_terminates_for_equality_class_peers_too(monkeypatch):
    """同値類の飽和も同じ terminal 判定を使う（IR kind でなくても）。"""

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture

    monkeypatch.setattr(
        record_pcode_fixture, "_java_class_name",
        lambda value: "ghidra.program.model.address.GenericAddress",
    )
    recorder = _synthetic_recorder_instance()

    class _Source:
        def getOffset(self):
            return 16

    source = recorder.proxy_for(_Source())
    assert source.getOffset() == 16
    sibling = recorder.proxy_for(_PeerWithoutTheMember())
    # 同じ Java 同値類に見せる（equality-class 飽和の対象になる）。
    recorder._entries[sibling._rec_index]["eq_group"] = (
        recorder._entries[source._rec_index]["eq_group"]
    )
    recorder.saturate()
    observations = recorder._entries[sibling._rec_index]["observations"]
    assert observations["attr:getOffset"][0]["v"]["kind"] == "absent"
    assert "call:getOffset()" not in observations


def test_saturation_records_a_failing_call_once_and_stops_retrying(monkeypatch):
    """callable な member の通常例外は観測として残り、再試行され続けない。"""

    calls = []
    _ir_kind(monkeypatch)
    recorder = _synthetic_recorder_instance()

    class _Source:
        def getIndex(self):
            return 0

        def getStart(self):
            return 4096

    class _FailingPeer:
        def getIndex(self):
            return 1

        def getStart(self):
            calls.append("start")
            raise RuntimeError("ghidra says no")

    source = recorder.proxy_for(_Source())
    assert source.getIndex() == 0 and source.getStart() == 4096
    peer = recorder.proxy_for(_FailingPeer())
    assert peer.getIndex() == 1
    recorder.saturate()
    assert calls == ["start"]
    observations = recorder._entries[peer._rec_index]["observations"]
    assert "raises" in observations["call:getStart()"][0]


def test_saturation_settled_predicate_is_shared_by_both_passes():
    """両方の飽和経路が同じ判定を使っている（弱い重複実装を作らない）。"""

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture
    import inspect

    source = inspect.getsource(record_pcode_fixture.Recorder)
    assert source.count("def saturation_is_settled") == 1
    for method in ("_saturate_equality_classes", "_saturate_ir_kinds"):
        body = inspect.getsource(getattr(record_pcode_fixture.Recorder, method))
        assert "saturation_is_settled" in body, method


# --- index accessor の件数 API も同じ terminal 判定を通る --------------------


class _IndexedSource:
    """``getInput(i)`` を census に載せる source（件数 API も持つ）。"""

    def getNumInputs(self) -> int:
        return 1

    def getInput(self, ordinal: int) -> int:
        return 100 + ordinal


def _indexed_peer_recorder(monkeypatch, peer, accessor="getInput", counter="getNumInputs"):
    """census を作る source と、件数 API に問題のある peer を並べる。"""

    _ir_kind(monkeypatch)
    recorder = _synthetic_recorder_instance()
    source = recorder.proxy_for(_IndexedSource())
    assert source.getNumInputs() == 1
    assert source.getInput(0) == 100      # indexed census に accessor が載る
    other = recorder.proxy_for(peer)
    return recorder, other


class _PeerWithoutCounter:
    """`getInput` は持つが件数 API を持たない peer（``attr`` が absent）。"""

    def getInput(self, ordinal: int) -> int:
        return ordinal


class _PeerWithNonCallableCounter:
    def __init__(self) -> None:
        self.getNumInputs = 3

    def getInput(self, ordinal: int) -> int:
        return ordinal


class _PeerWhoseCounterGetattrRaises:
    def getInput(self, ordinal: int) -> int:
        return ordinal

    def __getattr__(self, name):
        if name == "getNumInputs":
            raise RuntimeError("ghidra refuses the attribute")
        raise AttributeError(name)


def test_indexed_counter_terminates_when_the_peer_lacks_it(monkeypatch):
    """件数 API が無い peer でも飽和は固定点で終わる（RecordingError にしない）。"""

    recorder, other = _indexed_peer_recorder(monkeypatch, _PeerWithoutCounter())
    recorder.saturate()
    observations = recorder._entries[other._rec_index]["observations"]
    assert observations["attr:getNumInputs"][0]["v"]["kind"] == "absent"
    # 観測は 1 件だけ（毎周回積み直していない）。
    assert len(observations["attr:getNumInputs"]) == 1
    assert "call:getNumInputs()" not in observations


def test_indexed_counter_terminates_when_the_peer_counter_is_not_callable(monkeypatch):
    recorder, other = _indexed_peer_recorder(
        monkeypatch, _PeerWithNonCallableCounter(),
    )
    recorder.saturate()
    observations = recorder._entries[other._rec_index]["observations"]
    assert observations["attr:getNumInputs"][0]["v"]["kind"] == "value"
    assert len(observations["attr:getNumInputs"]) == 1


def test_indexed_counter_terminates_when_its_getattr_raises(monkeypatch):
    recorder, other = _indexed_peer_recorder(
        monkeypatch, _PeerWhoseCounterGetattrRaises(),
    )
    recorder.saturate()
    observations = recorder._entries[other._rec_index]["observations"]
    assert "raises" in observations["attr:getNumInputs"][0]
    assert len(observations["attr:getNumInputs"]) == 1


def test_indexed_counter_that_raises_is_observed_once(monkeypatch):
    """callable な件数 API の通常例外は 1 回だけ観測し、再試行しない。"""

    calls = []

    class _PeerWhoseCounterRaises:
        def getInput(self, ordinal):
            return ordinal

        def getNumInputs(self):
            calls.append("counted")
            raise RuntimeError("ghidra says no")

    recorder, other = _indexed_peer_recorder(
        monkeypatch, _PeerWhoseCounterRaises(),
    )
    recorder.saturate()
    assert calls == ["counted"]
    observations = recorder._entries[other._rec_index]["observations"]
    assert "raises" in observations["call:getNumInputs()"][0]
    assert len(observations["call:getNumInputs()"]) == 1


def test_indexed_counter_propagates_a_recording_error(monkeypatch):
    """件数 API 経路でも `RecordingError` は握り潰さず即時伝播する。"""

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture

    class _PeerWhoseCounterFailsTheRecording:
        def getInput(self, ordinal):
            return ordinal

        def getNumInputs(self):
            raise record_pcode_fixture.RecordingError("counter broke the recording")

    recorder, _other = _indexed_peer_recorder(
        monkeypatch, _PeerWhoseCounterFailsTheRecording(),
    )
    with pytest.raises(record_pcode_fixture.RecordingError):
        recorder.saturate()


def test_indexed_counter_is_not_recalled_once_observed(monkeypatch):
    """production が観測済みの件数 API を飽和が呼び直さない。"""

    calls = []

    class _PeerWithCounter:
        def getInput(self, ordinal):
            return ordinal

        def getNumInputs(self):
            calls.append("counted")
            return 1

    recorder, other = _indexed_peer_recorder(monkeypatch, _PeerWithCounter())
    assert other.getNumInputs() == 1          # production が 1 回観測
    assert calls == ["counted"]
    recorder.saturate()
    assert calls == ["counted"]               # 飽和は呼び直さない
    observations = recorder._entries[other._rec_index]["observations"]
    assert len(observations["call:getNumInputs()"]) == 1
    # 件数が読めたので accessor は展開される。
    assert "call:getInput(int:0)" in observations


@pytest.mark.parametrize("accessor,counter", [
    ("getInput", "getNumInputs"), ("getIn", "getInSize"), ("getOut", "getOutSize"),
])
def test_every_indexed_accessor_uses_the_same_counter_contract(
    monkeypatch, accessor, counter,
):
    """宣言済みの index accessor すべてが同じ terminal 判定を通る。"""

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture

    assert (accessor, counter) in record_pcode_fixture.INDEXED_ACCESSORS
    _ir_kind(monkeypatch)
    recorder = _synthetic_recorder_instance()

    class _Source:
        pass

    setattr(_Source, counter, lambda self: 1)
    setattr(_Source, accessor, lambda self, ordinal: 100 + ordinal)
    source = recorder.proxy_for(_Source())
    assert getattr(source, counter)() == 1
    assert getattr(source, accessor)(0) == 100

    class _PeerWithoutTheCounter:
        pass

    setattr(_PeerWithoutTheCounter, accessor, lambda self, ordinal: ordinal)
    peer = recorder.proxy_for(_PeerWithoutTheCounter())
    recorder.saturate()
    observations = recorder._entries[peer._rec_index]["observations"]
    assert observations[fixture_schema.attr_key(counter)][0]["v"]["kind"] == "absent"
    assert len(observations[fixture_schema.attr_key(counter)]) == 1


def test_counter_lookup_uses_the_shared_settled_predicate():
    """`_counted` が専用の terminal 判定を再実装していないこと。"""

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture
    import inspect

    body = inspect.getsource(record_pcode_fixture.Recorder._counted)
    assert "saturation_is_settled" in body


# --- validator: eq_group と hashCode identity の整合 -------------------------


def _hash_receiver_payload(pairs) -> Dict[str, Any]:
    """``(object id, eq_group, hash group)`` から最小 fixture を作る。"""

    payload = _minimal_payload({})
    for object_id, eq_group, group in pairs:
        payload["objects"][object_id] = {
            "kind": "ghidra.program.model.pcode.PcodeBlockBasic",
            "eq_group": eq_group,
            "members": {
                "attr:hashCode": {"v": {"kind": "method"}},
                "call:hashCode()": {"v": _identity_value("left", "hashCode", group)},
            },
        }
    return payload


def test_validator_accepts_java_equal_receivers_sharing_one_hash_identity():
    fixture_schema.validate_fixture(
        _hash_receiver_payload([("o2", 5, 0), ("o3", 5, 0)])
    )


def test_validator_rejects_java_equal_receivers_with_different_hash_identities():
    """replay で A == B なのに A.hashCode() != B.hashCode() になる fixture。"""

    _rejects(_hash_receiver_payload([("o2", 5, 0), ("o3", 5, 1)]))


def test_validator_accepts_a_hash_collision_between_unequal_receivers():
    """違う同値類が同じ hash を共有するのは Java 的に合法。"""

    fixture_schema.validate_fixture(
        _hash_receiver_payload([("o2", 5, 0), ("o3", 6, 0)])
    )


def test_validator_rejects_a_hash_identity_that_changes_inside_one_sequence():
    payload = _hash_receiver_payload([("o2", 5, 0)])
    payload["objects"]["o2"]["members"]["call:hashCode()"] = {
        "seq": [
            {"v": _identity_value("left", "hashCode", 0)},
            {"v": _identity_value("left", "hashCode", 1)},
        ],
    }
    _rejects(payload)


def test_validator_accepts_a_stable_hash_identity_inside_a_sequence():
    payload = _hash_receiver_payload([("o2", 5, 0)])
    payload["objects"]["o2"]["members"]["call:hashCode()"] = {
        "seq": [
            {"v": _identity_value("left", "hashCode", 0)},
            {"raises": {"type": "java.lang.RuntimeException", "message": "x"}},
        ],
    }
    fixture_schema.validate_fixture(payload)


def test_malformed_identity_fixture_is_rejected_before_replay():
    """壊れた fixture は再生器を作る前に落ちる（意味のある値へ寄せない）。"""

    payload = _hash_receiver_payload([("o2", 5, 0), ("o3", 5, 1)])
    with pytest.raises(fixture_schema.RecordedFixtureInvalid):
        recorded_program_from_payload(payload)


def test_record_and_validate_share_one_hash_contract_implementation():
    """記録側と検証側が同じ contract 実装を使っていること。"""

    contract = fixture_schema.HashEqualityContract()
    assert contract.observe(5, "a") == (True, None)
    assert contract.observe(5, "a") == (True, None)
    assert contract.observe(5, "b") == (False, "a")
    assert contract.observe(6, "a") == (True, None)   # collision は合法
    # 同値類が無い（None）ときは何も言わない。
    assert contract.observe(None, "z") == (True, None)


def test_identity_surrogates_in_the_case_fixture_match_their_canonical_form():
    """実 fixture の surrogate が (side, member, group) と整合していること。"""

    for name, side in (("left.json", "left"), ("right.json", "right")):
        payload = fixture_schema.loads(
            (CASE_DIR / name).read_text(encoding="utf-8")
        )
        found = []
        for entry in payload["objects"].values():
            for member_key, envelope in entry["members"].items():
                tagged = envelope.get("v")
                if isinstance(tagged, Mapping) and tagged.get("kind") == (
                    "identity_surrogate"
                ):
                    found.append((member_key, tagged))
        assert found
        for member_key, tagged in found:
            assert tagged["member"] in fixture_schema.IDENTITY_DERIVED_METHODS
            assert tagged["member"] == fixture_schema.member_name_of(member_key)
            assert tagged["value"] == fixture_schema.canonical_identity_surrogate(
                side, tagged["member"], tagged["group"],
            )
        # (member, group) と value は 1 対 1。
        pairs = {(t["member"], t["group"]): t["value"] for _k, t in found}
        assert len(set(pairs.values())) == len(pairs)


def test_identity_surrogates_never_collide_across_the_two_sides():
    values = {}
    for name, side in (("left.json", "left"), ("right.json", "right")):
        payload = fixture_schema.loads(
            (CASE_DIR / name).read_text(encoding="utf-8")
        )
        values[side] = {
            tagged["value"]
            for entry in payload["objects"].values()
            for tagged in (
                envelope.get("v") for envelope in entry["members"].values()
            )
            if isinstance(tagged, Mapping)
            and tagged.get("kind") == "identity_surrogate"
        }
    assert values["left"] and values["right"]
    assert not (values["left"] & values["right"])


def test_identity_surrogate_is_what_replay_returns():
    """記録された surrogate と再生が返す値が同じであること。"""

    program = load_recorded_program(CASE_DIR / "left.json")
    payload = fixture_schema.loads(
        (CASE_DIR / "left.json").read_text(encoding="utf-8")
    )
    recorded = payload["objects"][payload["roots"]["program"]]["members"][
        "call:getUniqueProgramID()"
    ]["v"]
    assert recorded["kind"] == "identity_surrogate"
    replayed = program.getUniqueProgramID()
    assert replayed == recorded["value"]
    assert type(replayed) is int
    assert program.missing_accesses == []


def test_load_recorded_program_reads_the_case_files():
    program = load_recorded_program(CASE_DIR / "left.json")
    assert isinstance(program, RecordedProgram)
    assert isinstance(program, RecordedObject)
    assert program.fixture_header["side"] == "left"
    assert program.missing_accesses == []
    assert program.access_log == []
    with pytest.raises(RecordedSurfaceMissing):
        program.thisMemberWasNeverRecorded()
    assert [type(access) for access in program.missing_accesses] == [MissingAccess]
    assert program.missing_accesses[0].as_tuple() == (
        program.missing_accesses[0].object_id,
        "ghidra.program.database.ProgramDB",
        "attr:thisMemberWasNeverRecorded",
    )
    assert program.decompiler is program.decompiler
    program.decompiler.dispose()


def test_recorder_and_replayer_declare_the_same_recorded_surface():
    """記録側と再生側で surface 定義がずれていないことを構造で固定する。

    記録される dunder（``__str__`` / ``__bool__`` / ``__len__`` / ``__iter__`` /
    ``__getitem__``）と、両側が明示的に宣言する ``dispose`` の 2 点。
    """

    from scripts.function_tracer_pcode.tests.tools import record_pcode_fixture
    from scripts.function_tracer_pcode.tests.fixtures.pcode.recorded_program import (
        RecordedDecompiler,
    )

    recording = record_pcode_fixture.RecordingProxy
    for name in fixture_schema.RECORDED_DUNDERS:
        assert name in recording.__dict__, name
        assert name in RecordedObject.__dict__, name
    # schema が挙げていない dunder を片側だけが記録していないこと。
    declared = set(fixture_schema.RECORDED_DUNDERS)
    for owner in (recording, RecordedObject):
        recorded_dunders = {
            name for name in owner.__dict__
            if name.startswith("__") and name.endswith("__")
            and name not in {
                "__init__", "__module__", "__qualname__", "__doc__",
                "__repr__", "__eq__", "__ne__", "__hash__",
                "__copy__", "__deepcopy__", "__getattr__", "__dict__",
                "__weakref__",
            }
        }
        assert recorded_dunders == declared, (owner, recorded_dunders)
    # ``dispose`` は記録側 no-op / 再生側 no-op を**両側で**宣言する。
    assert "dispose" in record_pcode_fixture.RecordingDecompiler.__dict__
    assert "dispose" in RecordedDecompiler.__dict__


def test_case_fixture_headers_describe_the_recorded_binaries():
    for name, side in (("left.json", "left"), ("right.json", "right")):
        header = fixture_schema.loads(
            (CASE_DIR / name).read_text(encoding="utf-8")
        )["header"]
        assert header["side"] == side
        assert header["recording_mode"]["connector"] == "production"
        assert header["target"]["function_name"] == "snippet"
        assert len(header["binary"]["sha256"]) == 64
        assert header["binary"]["binary_id"] in {"B1", "B2"}
        assert header["ghidra_version"]


# --- DI を使わない既定経路が変わっていないこと ------------------------------


def test_return_analyzer_without_injection_keeps_the_lazy_decompiler():
    from scripts.function_tracer_pcode.analysis import ReturnAnalyzer

    analyzer = ReturnAnalyzer(object())
    assert analyzer._decompiler is None


def test_return_analyzer_injection_bypasses_decompiler_construction():
    from scripts.function_tracer_pcode.analysis import ReturnAnalyzer

    sentinel = object()
    analyzer = ReturnAnalyzer(object(), decompiler=sentinel)
    assert analyzer._decompiler is sentinel
    assert analyzer._get_decompiler() is sentinel


def test_equivalence_checker_without_injection_uses_return_analyzer():
    import scripts.function_tracer_pcode.analysis as analysis_package
    from scripts.function_tracer_pcode.checker import EquivalenceChecker
    from scripts.function_tracer_pcode.checker import reanalysis

    checker = EquivalenceChecker(debug=False)
    assert checker.analyzer_factory is None

    seen = []

    class _Probe:
        def __init__(self, program, **kwargs):
            seen.append(("default", program))
            raise _Stop()

    class _Stop(Exception):
        pass

    original = analysis_package.ReturnAnalyzer
    analysis_package.ReturnAnalyzer = _Probe
    try:
        with pytest.raises(_Stop):
            reanalysis.analyze_and_check_with_analysis(checker, _StubContext())
    finally:
        analysis_package.ReturnAnalyzer = original
    assert [entry[0] for entry in seen] == ["default"]


def test_equivalence_checker_injection_replaces_only_the_analyzer_factory():
    from scripts.function_tracer_pcode.checker import EquivalenceChecker
    from scripts.function_tracer_pcode.checker import reanalysis

    made = []

    class _Stop(Exception):
        pass

    def factory(program, **kwargs):
        made.append(program)
        raise _Stop()

    checker = EquivalenceChecker(debug=False, analyzer_factory=factory)
    assert checker.analyzer_factory is factory
    with pytest.raises(_Stop):
        reanalysis.analyze_and_check_with_analysis(checker, _StubContext())
    assert made == ["program1"]


def test_equivalence_checker_rejects_a_non_callable_analyzer_factory():
    from scripts.function_tracer_pcode.checker import EquivalenceChecker

    with pytest.raises(TypeError):
        EquivalenceChecker(debug=False, analyzer_factory=object())


class _StubContext:
    """`analyze_and_check_with_analysis` が解析器を作るまでに読む最小の context。"""

    program1 = "program1"
    program2 = "program2"
    function_name1 = "f"
    function_name2 = "f"
    binary1_id = "B1"
    binary2_id = "B2"
    binary1_name = "left"
    binary2_name = "right"
    decompile_timeout = 60
    analysis1 = None
    analysis2 = None
    original_signature1 = None
    original_signature2 = None
    save_formula = False
    type_fix_result = None
