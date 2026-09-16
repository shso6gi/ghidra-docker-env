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


def _minimal_payload(members: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        "header": {
            "schema": fixture_schema.RECORDED_PCODE_FIXTURE_SCHEMA,
            "fixture_id": "unit", "side": "left", "recorded_at_utc": "1970-01-01T00:00:00+00:00",
            "recording_commit": "", "recording_dirty": False,
            "analysis_source_digest": "", "recorder_version": "1",
            "ghidra_version": "", "pyghidra_version": "",
            "binary": {
                "binary_id": "B1", "eqbench_relative_path": "x",
                "sha256": "0" * 64, "size": 1, "kind": "object",
            },
            "eqbench": {"upstream_url": "", "commit": ""},
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


def test_fixture_schema_is_checked_for_exact_equality():
    payload = _minimal_payload({})
    fixture_schema.validate_fixture(payload)
    broken = copy.deepcopy(payload)
    broken["header"]["schema"] = "recorded-pcode-fixture-v2"
    with pytest.raises(fixture_schema.RecordedFixtureInvalid):
        fixture_schema.validate_fixture(broken)
    for key in ("header", "roots", "objects"):
        missing = copy.deepcopy(payload)
        del missing[key]
        with pytest.raises(fixture_schema.RecordedFixtureInvalid):
            fixture_schema.validate_fixture(missing)
    unknown_member = copy.deepcopy(payload)
    unknown_member["objects"]["o0"]["members"]["getImageBase"] = {"v": {"kind": "none"}}
    with pytest.raises(fixture_schema.RecordedFixtureInvalid):
        fixture_schema.validate_fixture(unknown_member)
    both = copy.deepcopy(payload)
    both["objects"]["o0"]["members"]["attr:x"] = {
        "v": {"kind": "none"}, "raises": {"type": "t", "message": "m"},
    }
    with pytest.raises(fixture_schema.RecordedFixtureInvalid):
        fixture_schema.validate_fixture(both)


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
