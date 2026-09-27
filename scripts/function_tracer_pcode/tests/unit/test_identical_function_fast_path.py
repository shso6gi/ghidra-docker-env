# -*- coding: utf-8 -*-
"""Issue #15: 同一バイナリ・同一関数の identity proof による早期確定。

合成 fixture（EqBench ground truth ではない）。Ghidra 相当の Program / Function は
fake で、production の判定経路（`EquivalenceChecker` → authority session →
`build_default_cutover_connector` の encoder → `finalize_decision`）は本物を通す。

この test が固定する契約:

* 発火したときは解析器も decompiler も solver も呼ばれない。
* 発火の根拠は「左右それぞれの Program SHA が **その側の** session 入力 SHA と
  一致した」こと。左右の Program 同士が一致しているだけでは発火しない。
* artifact は pair / function / observation contract / session へ束縛され、
  どれが食い違っても encoder が拒否する。
* authority が成立しなければ EQUIVALENT にはならず、canonical ERROR が保存される。
* `--no-identical-fast-path` では確定しないが identity evidence は残る。
* 同じ checker instance を次の pair に使い回しても評価が漏れない。
"""

from __future__ import annotations

import sys

import pytest

from scripts.function_tracer_pcode.authority.contracts import Outcome, authority_digest
from scripts.function_tracer_pcode.authority.domains import identical_function_identity
from scripts.function_tracer_pcode.authority.domains.identical_function_identity import (
    IDENTICAL_FUNCTION_IDENTITY_COMMITTED_KEY,
    IDENTICAL_FUNCTION_IDENTITY_PRODUCER_ID,
    IDENTICAL_FUNCTION_IDENTITY_PROOF_SCHEMA,
    IdenticalFunctionIdentityPilotEncoder,
    IdenticalFunctionIdentityProofArtifact,
    IdenticalFunctionIdentitySessionBinding,
    IdenticalFunctionIdentitySignal,
)
from scripts.function_tracer_pcode.checker import identical_fast_path
from scripts.function_tracer_pcode.ghidra.function_identity import (
    BinaryFunctionIdentity,
    FunctionIdentityUnavailable,
    resolve_binary_function_identity,
)
from scripts.function_tracer_pcode.authority.seal_work import SealWorkBudget


SHA_A = "a" * 64
SHA_B = "b" * 64
SHA_C = "c" * 64


# --------------------------------------------------------------------------
# fake Ghidra objects
# --------------------------------------------------------------------------

class _FakeSpace:
    def __init__(self, name):
        self._name = name

    def getName(self):
        return self._name


class _FakeAddress:
    def __init__(self, space, offset):
        self._space = space
        self._offset = offset

    def getAddressSpace(self):
        return _FakeSpace(self._space)

    def getOffset(self):
        return self._offset


class _JavaLong:
    """`int()` でしか値が取れない Java 整数風の値。"""

    def __init__(self, value):
        self._value = value

    def __int__(self):
        return self._value

    def __str__(self):
        return str(self._value)


class _FakeBody:
    def __init__(self, start, end):
        self._start = start
        self._end = end

    def getMinAddress(self):
        return _FakeAddress(*self._start)

    def getMaxAddress(self):
        return _FakeAddress(*self._end)


class _FakeFunction:
    def __init__(self, name, entry=("ram", 0x100000), body=None):
        self._name = name
        self._entry = entry
        self._body = body or (("ram", 0x100000), ("ram", 0x100040))

    def getName(self):
        return self._name

    def getEntryPoint(self):
        return _FakeAddress(*self._entry)

    def getBody(self):
        return _FakeBody(*self._body)


class _FakeIdentifier:
    """`LanguageID` / `CompilerSpecID` のように `str()` でしか読めない ID。"""

    def __init__(self, text):
        self._text = text

    def __str__(self):
        return self._text


class _FakeLanguage:
    def __init__(self, language_id):
        self._language_id = language_id

    def getLanguageID(self):
        return _FakeIdentifier(self._language_id)


class _FakeCompilerSpec:
    def __init__(self, compiler_spec_id):
        self._compiler_spec_id = compiler_spec_id

    def getCompilerSpecID(self):
        return _FakeIdentifier(self._compiler_spec_id)


class _FakeFunctionManager:
    def __init__(self, functions):
        self._functions = functions

    def getFunctions(self, ascending):
        assert ascending is True
        return list(self._functions)


class _FakeProgram:
    def __init__(
        self,
        name,
        *,
        sha256=SHA_A,
        language_id="AARCH64:LE:64:v8A",
        compiler_spec_id="default",
        image_base=0x100000,
        functions=None,
    ):
        self._name = name
        self._sha256 = sha256
        self._language = _FakeLanguage(language_id)
        self._compiler_spec = _FakeCompilerSpec(compiler_spec_id)
        self._image_base = image_base
        self._functions = (
            [_FakeFunction("snippet")] if functions is None else list(functions)
        )

    def getName(self):
        return self._name

    def getExecutableSHA256(self):
        return self._sha256

    def getLanguage(self):
        return self._language

    def getCompilerSpec(self):
        return self._compiler_spec

    def getImageBase(self):
        return _FakeAddress("ram", _JavaLong(self._image_base))

    def getFunctionManager(self):
        return _FakeFunctionManager(self._functions)


class _ProgramWithout(_FakeProgram):
    """1 つの API だけを取り除いた Program。"""

    def __init__(self, name, missing, **kwargs):
        super().__init__(name, **kwargs)
        self._missing = missing

    def __getattribute__(self, name):
        if name != "_missing" and name == object.__getattribute__(self, "_missing"):
            raise AttributeError(name)
        return object.__getattribute__(self, name)


# --------------------------------------------------------------------------
# 1. resolver（Ghidra 境界）
# --------------------------------------------------------------------------

def test_resolver_reads_one_unique_function():
    identity = resolve_binary_function_identity(_FakeProgram("left"), "snippet")
    assert identity.match_count == 1
    assert identity.executable_sha256 == SHA_A
    assert identity.language_id == "AARCH64:LE:64:v8A"
    assert identity.compiler_spec_id == "default"
    assert identity.image_base == 0x100000
    assert identity.entry == ("ram", 0x100000)
    assert identity.body_range == (("ram", 0x100000), ("ram", 0x100040))
    assert identity.as_tuple()[0] == "binary_function_identity_v1"


def test_resolver_counts_zero_and_multiple_matches():
    missing = resolve_binary_function_identity(
        _FakeProgram("left", functions=[_FakeFunction("other")]), "snippet"
    )
    assert (missing.match_count, missing.entry, missing.body_range) == (0, None, None)
    for count in (2, 3, 5):
        duplicated = resolve_binary_function_identity(
            _FakeProgram("left", functions=[_FakeFunction("snippet")] * count),
            "snippet",
        )
        # 「2 件以上」ではなく実際の件数を記録する（走査は打ち切らない）。
        assert duplicated.match_count == count
        assert duplicated.entry is None and duplicated.body_range is None


def test_resolver_counts_matches_among_other_functions():
    program = _FakeProgram("left", functions=[
        _FakeFunction("a"), _FakeFunction("snippet"), _FakeFunction("b"),
        _FakeFunction("snippet"), _FakeFunction("c"), _FakeFunction("snippet"),
    ])
    assert resolve_binary_function_identity(program, "snippet").match_count == 3


@pytest.mark.parametrize("sha256", ["", "not-hex" + "0" * 57, "a" * 63])
def test_resolver_rejects_non_canonical_executable_sha(sha256):
    with pytest.raises(FunctionIdentityUnavailable):
        resolve_binary_function_identity(_FakeProgram("left", sha256=sha256), "snippet")


def test_resolver_normalizes_an_uppercase_executable_sha():
    identity = resolve_binary_function_identity(
        _FakeProgram("left", sha256=SHA_A.upper()), "snippet"
    )
    assert identity.executable_sha256 == SHA_A


@pytest.mark.parametrize(
    "missing",
    ["getExecutableSHA256", "getLanguage", "getCompilerSpec", "getImageBase",
     "getFunctionManager"],
)
def test_resolver_reports_missing_api(missing):
    with pytest.raises(FunctionIdentityUnavailable):
        resolve_binary_function_identity(_ProgramWithout("left", missing), "snippet")


def test_resolver_projects_java_style_offsets():
    program = _FakeProgram("left")
    program._functions = [
        _FakeFunction(
            "snippet",
            entry=("ram", _JavaLong(0x100010)),
            body=(("ram", _JavaLong(0x100010)), ("ram", _JavaLong(0x100030))),
        )
    ]
    identity = resolve_binary_function_identity(program, "snippet")
    assert identity.entry == ("ram", 0x100010)
    assert identity.body_range == (("ram", 0x100010), ("ram", 0x100030))


def test_resolver_rejects_a_float_offset():
    program = _FakeProgram("left")
    program._functions = [_FakeFunction("snippet", entry=("ram", 1.0))]
    with pytest.raises(FunctionIdentityUnavailable):
        resolve_binary_function_identity(program, "snippet")


# --------------------------------------------------------------------------
# 2. artifact / encoder（authority）
# --------------------------------------------------------------------------

def _identity(**overrides):
    values = {
        "executable_sha256": SHA_A,
        "function_name": "snippet",
        "language_id": "AARCH64:LE:64:v8A",
        "compiler_spec_id": "default",
        "image_base": 0x100000,
        "entry": ("ram", 0x100000),
        "body_range": (("ram", 0x100000), ("ram", 0x100040)),
        "match_count": 1,
    }
    values.update(overrides)
    return BinaryFunctionIdentity(**values)


def _binding(**overrides):
    values = {
        "result_occurrence_id": "occ-1",
        "execution_identity_digest": "digest-1",
        "left_binary_id": "B1",
        "right_binary_id": "B2",
        "binary_content_identity": f"sha256:{SHA_A}",
        "function_name": "snippet",
        "observation_contract_id": "contract-1",
    }
    values.update(overrides)
    return IdenticalFunctionIdentitySessionBinding(**values)


class _FakeIdentity:
    def __init__(self, result_occurrence_id, execution_identity_digest):
        self.result_occurrence_id = result_occurrence_id
        self.execution_identity_digest = execution_identity_digest


class _FakeSession:
    """encoder が読む最小限の session surface。"""

    def __init__(self, **payload_overrides):
        payload = {
            "binary1_id": "B1",
            "binary2_id": "B2",
            "binary1_content_identity": ("sha256", SHA_A),
            "binary2_content_identity": ("sha256", SHA_A),
            "function_name1": "snippet",
            "function_name2": "snippet",
            "observation_contract_id": "contract-1",
        }
        payload.update(payload_overrides)
        self.execution_payload = tuple(sorted(payload.items()))
        self.identity = _FakeIdentity("occ-1", "digest-1")
        self.domain_signal_state = {}


def test_artifact_binds_identity_observation_and_session():
    artifact = IdenticalFunctionIdentityProofArtifact.create(
        _identity(), _identity(), session_binding=_binding()
    )
    assert artifact.validate()
    assert artifact.artifact_digest == authority_digest(dict(artifact.body))
    assert artifact.body["binary_content_identity"] == f"sha256:{SHA_A}"
    assert artifact.body["match_count"] == 1


@pytest.mark.parametrize(
    "overrides",
    [
        {"entry": ("ram", 0x200000)},
        {"body_range": (("ram", 0x100000), ("ram", 0x100080))},
        {"image_base": 0x200000},
        {"language_id": "MIPS:BE:64:64-32addr"},
        {"compiler_spec_id": "gcc"},
        {"executable_sha256": SHA_B},
    ],
)
def test_artifact_refuses_differing_identity_fields(overrides):
    with pytest.raises(ValueError):
        IdenticalFunctionIdentityProofArtifact.create(
            _identity(), _identity(**overrides), session_binding=_binding()
        )


def test_artifact_refuses_a_non_unique_name_match():
    with pytest.raises(ValueError):
        IdenticalFunctionIdentityProofArtifact.create(
            _identity(match_count=2, entry=None, body_range=None),
            _identity(match_count=2, entry=None, body_range=None),
            session_binding=_binding(),
        )


def test_artifact_refuses_a_sha_that_differs_from_the_session_input():
    with pytest.raises(ValueError):
        IdenticalFunctionIdentityProofArtifact.create(
            _identity(), _identity(), session_binding=_binding(
                binary_content_identity=f"sha256:{SHA_C}"
            )
        )


def _signal(*, identity_overrides=None, **binding_overrides):
    identity = _identity(**(identity_overrides or {}))
    return IdenticalFunctionIdentitySignal.issue(
        identity, identity, session_binding=_binding(**binding_overrides)
    )


def test_encoder_emits_one_eq_closure_event():
    from scripts.function_tracer_pcode.authority.lifecycle.stream import EventType

    session = _FakeSession()
    encoder = IdenticalFunctionIdentityPilotEncoder()
    signal = _signal()
    intents = encoder(session, signal)
    assert len(intents) == 1
    assert intents[0].event_type is EventType.EQ_CLOSURE
    assert intents[0].authority_payload.proof_artifact_digest == (
        signal.proof_artifact_digest
    )
    assert signal.producer_id == IDENTICAL_FUNCTION_IDENTITY_PRODUCER_ID


def test_encoder_deduplicates_a_second_emission():
    session = _FakeSession()
    encoder = IdenticalFunctionIdentityPilotEncoder()
    signal = _signal()
    intents = encoder(session, signal)
    encoder.commit_emitted_signal(session, signal, intents)
    assert session.domain_signal_state[IDENTICAL_FUNCTION_IDENTITY_COMMITTED_KEY] == (
        signal.proof_artifact_digest
    )
    assert encoder(session, signal) == ()


def test_encoder_refuses_a_second_different_proof():
    session = _FakeSession()
    encoder = IdenticalFunctionIdentityPilotEncoder()
    first = _signal()
    encoder.commit_emitted_signal(session, first, encoder(session, first))
    payload = dict(session.execution_payload)
    payload.update({"function_name1": "other", "function_name2": "other"})
    session.execution_payload = tuple(sorted(payload.items()))
    other = _signal(
        function_name="other", identity_overrides={"function_name": "other"}
    )
    with pytest.raises(ValueError):
        encoder(session, other)


@pytest.mark.parametrize(
    "binding_overrides",
    [
        pytest.param({"result_occurrence_id": "occ-other"}, id="other-pair"),
        pytest.param({"execution_identity_digest": "digest-other"}, id="other-execution"),
        pytest.param({"left_binary_id": "B9"}, id="other-left-binary-id"),
        pytest.param({"right_binary_id": "B9"}, id="other-right-binary-id"),
        pytest.param({"observation_contract_id": "contract-9"}, id="other-contract"),
    ],
)
def test_encoder_refuses_an_artifact_bound_elsewhere(binding_overrides):
    encoder = IdenticalFunctionIdentityPilotEncoder()
    with pytest.raises(ValueError):
        encoder(_FakeSession(), _signal(**binding_overrides))


def test_encoder_refuses_an_artifact_for_another_function():
    encoder = IdenticalFunctionIdentityPilotEncoder()
    signal = _signal(
        function_name="other", identity_overrides={"function_name": "other"}
    )
    # artifact 側は "other"、session 側は "snippet"。
    with pytest.raises(ValueError):
        encoder(_FakeSession(), signal)


def test_encoder_refuses_a_content_hash_that_differs_from_the_session():
    encoder = IdenticalFunctionIdentityPilotEncoder()
    signal = _signal()
    with pytest.raises(ValueError):
        encoder(
            _FakeSession(
                binary1_content_identity=("sha256", SHA_B),
                binary2_content_identity=("sha256", SHA_B),
            ),
            signal,
        )


def test_encoder_refuses_a_session_whose_two_inputs_differ():
    encoder = IdenticalFunctionIdentityPilotEncoder()
    with pytest.raises(ValueError):
        encoder(
            _FakeSession(binary2_content_identity=("sha256", SHA_B)), _signal()
        )


def _forged_artifact(**body_overrides):
    """封印を迂回して body を作り替え、digest も**正しく作り直した** artifact。

    「古い digest のまま改竄する」だけでは、digest の再計算で気付ける改竄しか
    固定できない。ここでは改竄側が digest まで辻褄を合わせられる前提で、
    それでも decisive proof として受理されないことを見る。
    """

    body = {**_signal().artifact.body, **body_overrides}
    forged = object.__new__(IdenticalFunctionIdentityProofArtifact)
    object.__setattr__(forged, "schema", IDENTICAL_FUNCTION_IDENTITY_PROOF_SCHEMA)
    object.__setattr__(forged, "body", body)
    object.__setattr__(forged, "artifact_digest", authority_digest(body))
    return forged


def _forged_signal(*, artifact=None, proof_artifact_digest=None):
    """封印された factory を意図的に迂回して作る signal（改竄の模擬）。"""

    signal = _signal()
    forged = object.__new__(IdenticalFunctionIdentitySignal)
    object.__setattr__(
        forged, "proof_artifact_digest",
        proof_artifact_digest or (
            artifact.artifact_digest if artifact is not None
            else signal.proof_artifact_digest
        ),
    )
    object.__setattr__(forged, "producer_id", signal.producer_id)
    object.__setattr__(forged, "artifact", artifact or signal.artifact)
    return forged


def test_the_artifact_cannot_be_constructed_outside_its_factory():
    """意味検証（左右一致 / `match_count == 1` / SHA 整合）を迂回させない。"""

    body = dict(_signal().artifact.body)
    with pytest.raises(TypeError):
        IdenticalFunctionIdentityProofArtifact(
            schema=IDENTICAL_FUNCTION_IDENTITY_PROOF_SCHEMA,
            body=body,
            artifact_digest=authority_digest(body),
        )
    with pytest.raises(TypeError):
        import dataclasses

        dataclasses.replace(_signal().artifact, artifact_digest="0" * 64)


@pytest.mark.parametrize(
    "body_overrides",
    [
        pytest.param({"entry": ["ram", 4919]}, id="entry"),
        pytest.param({"body_range": [["ram", 0], ["ram", 4919]]}, id="body-range"),
        pytest.param({"image_base": 4919}, id="image-base"),
        pytest.param({"language_id": "MIPS:BE:64:64-32addr"}, id="language"),
        pytest.param({"compiler_spec_id": "gcc"}, id="compiler-spec"),
        pytest.param({"match_count": 2}, id="match-count"),
        pytest.param(
            {"executable_sha256": SHA_B, "binary_content_identity": f"sha256:{SHA_B}"},
            id="both-sha-fields",
        ),
    ],
)
def test_a_forged_artifact_with_a_recomputed_digest_is_not_authority(body_overrides):
    """body を作り替え digest も作り直した artifact は decisive proof にならない。

    `artifact_digest` の再計算で辻褄が合っていても、`create()` を通っていない
    以上「左右の観測が一致し、名前一致が 1 件で、観測 SHA が session 入力と
    同じ」ことは何も証明されていない。
    """

    forged = _forged_artifact(**body_overrides)
    # digest は正しく作り直されている（古い digest のままではない）。
    assert forged.artifact_digest == authority_digest(dict(forged.body))
    assert forged.validate() is False
    signal = _forged_signal(artifact=forged)
    assert signal.validates() is False
    with pytest.raises(ValueError):
        IdenticalFunctionIdentityPilotEncoder()(_FakeSession(), signal)
    with pytest.raises(ValueError):
        signal._phase7_signal_authority()


def test_a_forged_artifact_is_refused_even_when_every_field_stays_canonical():
    """body を触らずに object だけ作り直した artifact も受理しない。

    binding も identity も本物と同じで digest も一致するが、`create()` の
    意味検証を通っていないので authority にはならない。
    """

    forged = _forged_artifact()
    assert forged.body_is_canonical() is True
    assert forged.validate() is False
    with pytest.raises(ValueError):
        IdenticalFunctionIdentityPilotEncoder()(
            _FakeSession(), _forged_signal(artifact=forged)
        )


def test_encoder_refuses_a_tampered_digest():
    with pytest.raises(ValueError):
        IdenticalFunctionIdentityPilotEncoder()(
            _FakeSession(), _forged_signal(proof_artifact_digest="0" * 64)
        )


def test_the_signal_cannot_be_constructed_around_a_prebuilt_artifact():
    """signal は観測から issue する。出来合いの artifact を載せる経路を残さない。"""

    with pytest.raises(TypeError):
        IdenticalFunctionIdentitySignal(
            proof_artifact_digest=_forged_artifact().artifact_digest,
            producer_id=IDENTICAL_FUNCTION_IDENTITY_PRODUCER_ID,
            artifact=_forged_artifact(),
        )


def test_encoder_ignores_a_foreign_signal_type():
    assert IdenticalFunctionIdentityPilotEncoder()(_FakeSession(), object()) == ()


def test_signal_cannot_be_constructed_without_its_artifact():
    with pytest.raises(TypeError):
        IdenticalFunctionIdentitySignal(
            proof_artifact_digest="x", producer_id="y", artifact=None
        )


def test_the_artifact_is_hashable_even_though_its_body_is_a_mapping():
    artifact = IdenticalFunctionIdentityProofArtifact.create(
        _identity(), _identity(), session_binding=_binding()
    )
    assert hash(artifact) == hash(IdenticalFunctionIdentityProofArtifact.create(
        _identity(), _identity(), session_binding=_binding()
    ))
    assert {artifact, artifact} == {artifact}


def test_phase7_signal_authority_projects_the_artifact_body():
    signal = _signal()
    assert signal._phase7_signal_authority() == dict(signal.artifact.body)


# --------------------------------------------------------------------------
# 3. end to end（production connector 付き）
# --------------------------------------------------------------------------

class _ForbiddenImportFinder:
    def __init__(self, prefix):
        self._prefix = prefix

    def find_spec(self, fullname, path=None, target=None):
        if fullname == self._prefix or fullname.startswith(self._prefix + "."):
            raise AssertionError(f"{fullname} was imported on the identical fast path")
        return None


class _Probe:
    def __init__(self):
        self.analyzer_programs = []


def _run_production_check(
    monkeypatch,
    case_id,
    program1,
    program2,
    *,
    function_name1="snippet",
    function_name2="snippet",
    binary1_content_identity=("sha256", SHA_A),
    binary2_content_identity=("sha256", SHA_A),
    binary1_id="B1",
    binary2_id="B2",
    identical_fast_path_enabled=True,
    forbid_analysis=False,
    checker=None,
):
    """本物の workflow / authority connector で 1 pair 実行する。

    Ghidra 解析だけを差し替え、fast path が発火するときは解析器を
    インスタンス化しようとした時点で `AssertionError` にする。解析器は
    `EquivalenceChecker(analyzer_factory=...)`（Issue #109）で渡す。
    production 自身が解析器を作る経路がそこなので、package 属性を裏で
    差し替えるより test が本番に近い。
    """

    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        build_default_cutover_connector,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        activate_process_worker_execution_authority_deployment,
    )
    from scripts.function_tracer_pcode.checker import EquivalenceChecker
    from scripts.function_tracer_pcode.smt.parallel import ParallelSolverRunner

    activate_process_worker_execution_authority_deployment(
        key_id="issue15-" + case_id,
        key=(case_id.encode() * 32)[:32],
        key_source_id="/tmp/issue15-" + case_id,
    )
    probe = _Probe()

    class _RecordingReturnAnalyzer:
        def __init__(self, program, **_kwargs):
            if forbid_analysis:
                raise AssertionError(
                    "ReturnAnalyzer was instantiated on the identical fast path"
                )
            probe.analyzer_programs.append(program.getName())

        def analyze_function_by_name(self, _name, _timeout):
            return None

        def get_last_analysis_failure(self):
            return None

        def get_last_function_lookup_error(self):
            return None

        def dispose(self):
            pass

    def _no_solver(*_args, **_kwargs):
        raise AssertionError("a solver ran on the identical fast path")

    for name in ("run_single", "run_parallel", "run_sequential"):
        monkeypatch.setattr(ParallelSolverRunner, name, _no_solver)
    finder = _ForbiddenImportFinder("ghidra.app.decompiler")
    monkeypatch.setattr(sys, "meta_path", [finder, *sys.meta_path])

    if checker is None:
        checker = EquivalenceChecker(
            debug=False, identical_fast_path=identical_fast_path_enabled,
            analyzer_factory=_RecordingReturnAnalyzer,
        )
        checker.v2_dual_write_pilot_connector = build_default_cutover_connector()
    else:
        # 使い回しの checker は、この 1 回のために解析器 collaborator を
        # 差し替える（呼び出しごとに probe と `forbid_analysis` が変わる）。
        monkeypatch.setattr(
            checker, "analyzer_factory", _RecordingReturnAnalyzer, raising=False,
        )
    result = checker.check_from_binaries(
        program1,
        program2,
        function_name1,
        function_name2,
        binary1_id=binary1_id,
        binary2_id=binary2_id,
        binary1_content_identity=binary1_content_identity,
        binary2_content_identity=binary2_content_identity,
    )
    assert "ghidra.app.decompiler" not in sys.modules
    return result, probe, checker


def _payload_with_bundle(result):
    """CLI と同じ順序で preimage と bundle を組む（`cli/commands/equivalence.py`）。"""

    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        build_canonical_result_finalization_bundle,
    )

    payload = result.to_dict()
    evidence, session = result._canonical_finalization_context
    bundle = build_canonical_result_finalization_bundle(
        result_payload_preimage=payload, evidence=evidence, session=session, work=SealWorkBudget.for_result()
    )
    return payload, bundle


def _outcome(payload):
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        outcome_from_payload,
    )

    return outcome_from_payload(payload)


def test_identical_binaries_and_function_are_equivalent_without_any_analysis(monkeypatch):
    result, probe, _ = _run_production_check(
        monkeypatch, "fire", _FakeProgram("left"), _FakeProgram("right"),
        forbid_analysis=True,
    )
    payload = result.to_dict()
    assert probe.analyzer_programs == []
    assert payload["final_outcome"] == "EQUIVALENT"
    assert payload["is_equivalent"] is True
    assert _outcome(payload) is Outcome.EQUIVALENT
    assert result.decision_receipt.outcome is Outcome.EQUIVALENT
    assert payload["stage_path"] == ["IDENTICAL_FUNCTION_IDENTITY"]
    assert payload["c_active_base"] == []
    assert payload["identical_fast_path_disposition"] == {
        "applicable": True, "applied": True, "reason": "applied",
    }
    provenance = payload["decisive_proof_provenance"]
    assert provenance["kind"] == "identical_function_identity"
    assert provenance["proof_artifact_digest"] == authority_digest(
        provenance["artifact"]
    )
    # 同一性の観測は専用 key に載る。`function*_identity` は結果を他と区別する
    # stable key なので、左右で違う（同じ binary を共有する別 pair と衝突させない）。
    evidence = payload["identical_function_identity_evidence"]
    assert evidence["schema"] == "identical_function_identity_evidence_v1"
    assert evidence["left"] == evidence["right"]
    assert evidence["left"]["executable_sha256"] == SHA_A
    assert evidence["left"]["match_count"] == 1
    assert payload["function1_identity"] != payload["function2_identity"]
    # 結果 JSON は canonical な JSON 値（配列は list）
    assert payload["function1_identity"][:2] == [
        "identical_fast_path_function_identity_v1", ["binary_id", "B1"],
    ]
    assert payload["function2_identity"][1] == ["binary_id", "B2"]
    _, bundle = _payload_with_bundle(result)
    assert bundle["canonical_semantic_result_projection"]["payload"][
        "decisive_proof_kinds"
    ] == ["EQ_CLOSURE"]


def test_fast_path_result_survives_bundle_validation(monkeypatch):
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        validate_canonical_result_finalization_bundle,
    )

    result, _, _ = _run_production_check(
        monkeypatch, "bundle", _FakeProgram("left"), _FakeProgram("right"),
        forbid_analysis=True,
    )
    payload, bundle = _payload_with_bundle(result)
    validated = validate_canonical_result_finalization_bundle(
        bundle, result_payload_preimage=payload, work=SealWorkBudget.for_result()
    )
    assert validated["outcome"] == "EQUIVALENT"


@pytest.mark.parametrize(
    "mutate,expected",
    [
        pytest.param(
            lambda preimage: preimage["decisive_proof_provenance"]["artifact"].update(
                {"function_name": "other"}
            ),
            "artifact",
            id="artifact-body-changed",
        ),
        pytest.param(
            lambda preimage: preimage["decisive_proof_provenance"].update(
                {"proof_artifact_digest": "0" * 64}
            ),
            "digest",
            id="provenance-digest-changed",
        ),
        pytest.param(
            lambda preimage: preimage["decisive_proof_provenance"]["artifact"].update(
                {"left_binary_id": "B9"}
            ),
            "binding",
            id="binding-changed",
        ),
        pytest.param(
            lambda preimage: preimage["decisive_proof_provenance"].update({"kind": "x"}),
            "kind",
            id="kind-changed",
        ),
    ],
)
def test_bundle_validation_rejects_a_drifting_provenance(monkeypatch, mutate, expected):
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        validate_canonical_result_finalization_bundle,
    )

    del expected
    result, _, _ = _run_production_check(
        monkeypatch, "bundle-neg", _FakeProgram("left"), _FakeProgram("right"),
        forbid_analysis=True,
    )
    payload, bundle = _payload_with_bundle(result)
    mutate(payload)
    with pytest.raises(ValueError):
        validate_canonical_result_finalization_bundle(
            bundle, result_payload_preimage=payload, work=SealWorkBudget.for_result()
        )


@pytest.mark.parametrize(
    "body_overrides",
    [
        pytest.param({"match_count": 2}, id="non-unique-match"),
        pytest.param({"executable_sha256": SHA_B}, id="sha-disagrees-with-content"),
        pytest.param({"image_base": "0x1000"}, id="image-base-is-not-an-int"),
        pytest.param({"entry": "ram:0"}, id="entry-is-not-an-address-pair"),
        pytest.param({"binary_content_identity": "md5:" + SHA_A}, id="other-algorithm"),
    ],
)
def test_saved_provenance_must_satisfy_the_same_body_invariants(
    monkeypatch, body_overrides,
):
    """保存物にも producer 側と同じ body 不変条件が掛かる。

    bundle 経由では receipt の digest が先に食い違うので、ここでは
    「receipt とも digest が一致する forged body」を直接渡して、body 不変条件
    そのものが判断根拠になる状態を作る。
    """

    from types import SimpleNamespace

    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        _validate_decisive_proof_provenance,
    )
    from scripts.function_tracer_pcode.authority.decision.decision import (
        DecisiveProofKind,
    )

    result, _, _ = _run_production_check(
        monkeypatch, "saved-body", _FakeProgram("left"), _FakeProgram("right"),
        forbid_analysis=True,
    )
    payload, bundle = _payload_with_bundle(result)
    artifact = {**payload["decisive_proof_provenance"]["artifact"], **body_overrides}
    digest = authority_digest(artifact)
    provenance = {
        "kind": "identical_function_identity",
        "proof_artifact_digest": digest,
        "artifact": artifact,
    }
    receipt = SimpleNamespace(
        proof_kind=DecisiveProofKind.EQ_CLOSURE, proof_artifact_digest=digest,
    )
    with pytest.raises(ValueError):
        _validate_decisive_proof_provenance(
            provenance,
            decisive_receipts=(receipt,),
            execution_identity=bundle["execution_identity"],
            execution_payload=bundle["execution_payload"],
        )


def test_bundle_validation_requires_a_decisive_receipt_for_the_provenance(monkeypatch):
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        _validate_decisive_proof_provenance,
    )

    result, _, _ = _run_production_check(
        monkeypatch, "bundle-empty", _FakeProgram("left"), _FakeProgram("right"),
        forbid_analysis=True,
    )
    payload, bundle = _payload_with_bundle(result)
    with pytest.raises(ValueError):
        _validate_decisive_proof_provenance(
            payload["decisive_proof_provenance"],
            decisive_receipts=(),
            execution_identity=bundle["execution_identity"],
            execution_payload=bundle["execution_payload"],
        )


@pytest.mark.parametrize(
    "binding_overrides",
    [
        pytest.param({"left_binary_id": "B9"}, id="other-binary-id"),
        pytest.param({"function_name": "other"}, id="other-function"),
        pytest.param({"observation_contract_id": "contract-9"}, id="other-contract"),
        pytest.param({"result_occurrence_id": "occ-other"}, id="other-pair"),
    ],
)
def test_an_unbound_artifact_fails_closed_to_a_saved_canonical_error(
    monkeypatch, binding_overrides,
):
    original = identical_fast_path._session_binding_for

    def _unbound(session, left, **kwargs):
        import dataclasses

        return dataclasses.replace(
            original(session, left, **kwargs), **binding_overrides
        )

    monkeypatch.setattr(identical_fast_path, "_session_binding_for", _unbound)
    result, _, _ = _run_production_check(
        monkeypatch, "unbound" + "".join(binding_overrides), _FakeProgram("left"),
        _FakeProgram("right"), forbid_analysis=True,
    )
    payload = result.to_dict()
    assert payload["is_equivalent"] is None
    assert payload["final_outcome"] == "ERROR"
    assert _outcome(payload) is Outcome.ERROR
    assert payload["decision_receipt"] is not None
    assert "decisive_proof_provenance" not in payload
    assert payload["identical_fast_path_disposition"]["applied"] is False


@pytest.mark.parametrize(
    "tamper",
    [
        pytest.param("digest", id="stale-digest"),
        pytest.param("body", id="recomputed-digest"),
    ],
)
def test_a_forged_artifact_fails_closed_to_a_saved_canonical_error(monkeypatch, tamper):
    """producer が forged artifact を出しても EQUIVALENT にはならない（e2e）。

    `recomputed-digest` の側は body を作り替えたうえで digest も作り直す。
    digest の再計算で気付ける改竄だけを見ている test にしない。
    """

    real_create = IdenticalFunctionIdentityProofArtifact.create

    class _ForgingFactory:
        @staticmethod
        def create(left, right, *, session_binding):
            genuine = real_create(left, right, session_binding=session_binding)
            body = dict(genuine.body)
            if tamper == "body":
                body["entry"] = ["ram", 4919]
            forged = object.__new__(IdenticalFunctionIdentityProofArtifact)
            object.__setattr__(forged, "schema", genuine.schema)
            object.__setattr__(forged, "body", body)
            object.__setattr__(
                forged, "artifact_digest",
                "0" * 64 if tamper == "digest" else authority_digest(body),
            )
            return forged

    monkeypatch.setattr(
        identical_function_identity,
        "IdenticalFunctionIdentityProofArtifact",
        _ForgingFactory,
    )
    result, _, _ = _run_production_check(
        monkeypatch, "forged-" + tamper, _FakeProgram("left"), _FakeProgram("right"),
        forbid_analysis=True,
    )
    payload = result.to_dict()
    assert payload["is_equivalent"] is None
    assert payload["final_outcome"] == "ERROR"
    assert _outcome(payload) is Outcome.ERROR
    assert "decisive_proof_provenance" not in payload


def test_fast_path_is_not_applied_when_the_flag_is_off(monkeypatch):
    result, probe, _ = _run_production_check(
        monkeypatch, "off", _FakeProgram("left"), _FakeProgram("right"),
        identical_fast_path_enabled=False,
    )
    payload = result.to_dict()
    assert probe.analyzer_programs == ["left"]
    assert payload["final_outcome"] == "ERROR"
    assert payload["identical_fast_path_disposition"] == {
        "applicable": True, "applied": False, "reason": "disabled",
    }
    # OFF でも identity evidence は残る（oracle run で gate が読む）。解析由来の
    # `function*_identity` には触らないので、oracle run の stable result key は
    # fast path の有無で変わらない。
    evidence = payload["identical_function_identity_evidence"]
    assert evidence["left"] == evidence["right"]
    assert evidence["left"]["executable_sha256"] == SHA_A
    assert payload["function1_identity"] is None
    assert payload["function2_identity"] is None
    assert "decisive_proof_provenance" not in payload


@pytest.mark.parametrize(
    "case,left_kwargs,right_kwargs,reason",
    [
        pytest.param(
            "entry", {}, {"functions": [_FakeFunction("snippet", entry=("ram", 0x200000))]},
            "identity_mismatch", id="entry",
        ),
        pytest.param(
            "base", {}, {"image_base": 0x200000}, "identity_mismatch", id="image-base",
        ),
        pytest.param(
            "lang", {}, {"language_id": "MIPS:BE:64:64-32addr"}, "identity_mismatch",
            id="language",
        ),
        pytest.param(
            "spec", {}, {"compiler_spec_id": "gcc"}, "identity_mismatch", id="compiler-spec",
        ),
        pytest.param(
            "empty-sha", {}, {"sha256": ""}, "identity_unavailable", id="empty-sha",
        ),
        pytest.param(
            "two-names", {},
            {"functions": [_FakeFunction("snippet"), _FakeFunction("snippet")]},
            "name_not_unique", id="two-name-matches",
        ),
    ],
)
def test_identity_differences_fall_back_to_the_normal_path(
    monkeypatch, case, left_kwargs, right_kwargs, reason,
):
    result, probe, _ = _run_production_check(
        monkeypatch, "fallback-" + case,
        _FakeProgram("left", **left_kwargs), _FakeProgram("right", **right_kwargs),
    )
    payload = result.to_dict()
    assert probe.analyzer_programs == ["left"]
    assert payload["final_outcome"] == "ERROR"
    assert payload["identical_fast_path_disposition"]["applied"] is False
    assert payload["identical_fast_path_disposition"]["reason"] == reason
    assert "decisive_proof_provenance" not in payload


def test_the_left_side_reason_is_reported_when_both_sides_fail(monkeypatch):
    """`reason` は 1 つ。左右が違う理由で失敗したら左側のものを載せる。"""

    result, probe, _ = _run_production_check(
        monkeypatch, "sides",
        _FakeProgram("left", functions=[_FakeFunction("snippet"), _FakeFunction("snippet")]),
        _FakeProgram("right", functions=[_FakeFunction("other")]),
    )
    disposition = result.to_dict()["identical_fast_path_disposition"]
    assert probe.analyzer_programs == ["left"]
    assert disposition == {
        "applicable": False, "applied": False, "reason": "name_not_unique",
    }


def test_a_right_side_only_resolution_failure_is_reported(monkeypatch):
    result, _, _ = _run_production_check(
        monkeypatch, "side-right", _FakeProgram("left"),
        _FakeProgram("right", functions=[_FakeFunction("other")]),
    )
    assert result.to_dict()["identical_fast_path_disposition"] == {
        "applicable": False, "applied": False, "reason": "function_missing",
    }


def test_a_missing_function_keeps_the_existing_error_path(monkeypatch):
    result, probe, _ = _run_production_check(
        monkeypatch, "missing",
        _FakeProgram("left", functions=[_FakeFunction("other")]),
        _FakeProgram("right", functions=[_FakeFunction("other")]),
    )
    payload = result.to_dict()
    assert probe.analyzer_programs == ["left"]
    assert payload["final_outcome"] == "ERROR"
    assert payload["identical_fast_path_disposition"]["reason"] == "function_missing"
    assert payload["function1_identity"] is None


def test_different_function_names_are_left_untouched(monkeypatch):
    result, probe, _ = _run_production_check(
        monkeypatch, "names",
        _FakeProgram("left"),
        _FakeProgram("right", functions=[_FakeFunction("other")]),
        function_name1="snippet", function_name2="other",
    )
    payload = result.to_dict()
    assert probe.analyzer_programs == ["left"]
    assert "identical_fast_path_disposition" not in payload
    assert "decisive_proof_provenance" not in payload
    assert payload["function1_identity"] is None


def test_different_input_content_identities_are_left_untouched(monkeypatch):
    result, _, _ = _run_production_check(
        monkeypatch, "content", _FakeProgram("left"),
        _FakeProgram("right", sha256=SHA_B),
        binary2_content_identity=("sha256", SHA_B),
    )
    payload = result.to_dict()
    assert "identical_fast_path_disposition" not in payload
    assert payload["function1_identity"] is None


class _AssessSession:
    def __init__(self, payload, state=None):
        self.execution_payload = tuple(sorted(payload.items()))
        self.domain_signal_state = state if state is not None else {}


def _assess_with_session(monkeypatch, session, program1, program2, **kwargs):
    from scripts.function_tracer_pcode.authority.lifecycle import production_context

    monkeypatch.setattr(
        production_context, "active_production_pilot_session", lambda: session
    )
    return identical_fast_path.assess_identical_function_identity(
        type("_C", (), {"identical_fast_path": True})(),
        program1, program2, "snippet", "snippet",
        binary1_id="B1", binary2_id="B2", start_time=0.0, **kwargs
    )


def test_assessment_is_absent_without_a_session_content_identity(monkeypatch):
    session = _AssessSession({
        "binary1_id": "B1", "binary2_id": "B2",
        "binary1_content_identity": None, "binary2_content_identity": None,
        "function_name1": "snippet", "function_name2": "snippet",
        "observation_contract_id": "contract-1",
    })
    assert _assess_with_session(
        monkeypatch, session, _FakeProgram("left"), _FakeProgram("right")
    ) is None


def _bound_session(program1, program2, **payload_overrides):
    """Program ↔ sha の束縛まで張った assess 用の session。"""

    payload = {
        "binary1_id": "B1", "binary2_id": "B2",
        "binary1_content_identity": ("sha256", SHA_A),
        "binary2_content_identity": ("sha256", SHA_A),
        "function_name1": "snippet", "function_name2": "snippet",
        "observation_contract_id": "contract-1",
    }
    payload.update(payload_overrides)
    identity = payload["binary1_content_identity"]
    bound = identity if type(identity) is str else f"sha256:{identity[1]}"
    return _AssessSession(payload, {
        "operational_program_binary_identities": {
            id(program1): bound, id(program2): bound,
        },
    })


@pytest.mark.parametrize(
    "content_identity",
    [
        pytest.param("SHA256:" + SHA_A, id="uppercase-prefix"),
        pytest.param("md5:" + SHA_A, id="other-algorithm"),
        pytest.param("x", id="too-short-to-slice"),
        pytest.param("sha256:" + SHA_A[:-1], id="short-digest"),
        pytest.param("sha256:" + SHA_A.upper(), id="uppercase-digest"),
    ],
)
def test_a_non_canonical_content_identity_is_not_sliced_into_a_sha(
    monkeypatch, content_identity,
):
    """接頭辞を確かめずに切り出すと偽の sha が取れてしまう。

    `production_boundary._operational_binary_content_identity` は非空の文字列を
    そのまま通すので、`sha256:<hex>` でない identity も session に入り得る。
    そこから 7 文字を落として sha として使わないことを固定する（不適用 = None）。
    """

    program1, program2 = _FakeProgram("left"), _FakeProgram("right")
    session = _bound_session(
        program1, program2,
        binary1_content_identity=content_identity,
        binary2_content_identity=content_identity,
    )
    assert _assess_with_session(monkeypatch, session, program1, program2) is None


def test_a_missing_observation_contract_is_named_as_such(monkeypatch):
    program1, program2 = _FakeProgram("left"), _FakeProgram("right")
    session = _bound_session(program1, program2, observation_contract_id="")
    assessment = _assess_with_session(monkeypatch, session, program1, program2)
    assert assessment.disposition == {
        "applicable": False, "applied": False,
        "reason": "observation_contract_unavailable",
    }
    assert assessment.identity_evidence_ok is True
    assert assessment.fast_path_result is None


def test_a_binary_id_that_differs_from_the_session_does_not_apply(monkeypatch):
    program1, program2 = _FakeProgram("left"), _FakeProgram("right")
    session = _bound_session(program1, program2, binary1_id="B9")
    assessment = _assess_with_session(monkeypatch, session, program1, program2)
    assert assessment.disposition["reason"] == "binary_id_unavailable"
    assert assessment.fast_path_result is None


def test_assessment_is_absent_without_an_active_session(monkeypatch):
    assert _assess_with_session(
        monkeypatch, None, _FakeProgram("left"), _FakeProgram("right")
    ) is None


def test_both_programs_sharing_a_sha_that_is_not_the_session_input_does_not_fire(
    monkeypatch,
):
    """左右の Program SHA は互いに一致するが session 入力とは違う。

    「左右が同じ」だけで発火してしまうと、比較対象ではないバイナリを根拠に
    EQUIVALENT を出せてしまう。評価は不適用、evidence も残さない。
    """

    result, probe, _ = _run_production_check(
        monkeypatch, "foreign-sha",
        _FakeProgram("left", sha256=SHA_C), _FakeProgram("right", sha256=SHA_C),
    )
    payload = result.to_dict()
    assert probe.analyzer_programs == ["left"]
    assert payload["identical_fast_path_disposition"] == {
        "applicable": False, "applied": False,
        "reason": "identity_mismatch", "sha_mismatch_side": "both",
    }
    assert payload["function1_identity"] is None
    assert payload["function2_identity"] is None


def test_a_one_sided_sha_mismatch_does_not_fire(monkeypatch):
    result, probe, _ = _run_production_check(
        monkeypatch, "one-sided",
        _FakeProgram("left"), _FakeProgram("right", sha256=SHA_C),
    )
    payload = result.to_dict()
    assert probe.analyzer_programs == ["left"]
    assert payload["identical_fast_path_disposition"] == {
        "applicable": False, "applied": False,
        "reason": "identity_mismatch", "sha_mismatch_side": "right",
    }
    assert payload["function1_identity"] is None


def test_off_mode_also_refuses_a_foreign_shared_sha(monkeypatch):
    result, _, _ = _run_production_check(
        monkeypatch, "foreign-sha-off",
        _FakeProgram("left", sha256=SHA_C), _FakeProgram("right", sha256=SHA_C),
        identical_fast_path_enabled=False,
    )
    payload = result.to_dict()
    assert payload["identical_fast_path_disposition"] == {
        "applicable": False, "applied": False,
        "reason": "identity_mismatch", "sha_mismatch_side": "both",
    }
    assert payload["function1_identity"] is None


def test_missing_binary_ids_do_not_apply_the_fast_path(monkeypatch):
    result, probe, _ = _run_production_check(
        monkeypatch, "no-ids", _FakeProgram("left"), _FakeProgram("right"),
        binary1_id=None, binary2_id=None,
    )
    payload = result.to_dict()
    assert probe.analyzer_programs == ["left"]
    assert payload["identical_fast_path_disposition"]["reason"] == "binary_id_unavailable"
    evidence = payload["identical_function_identity_evidence"]
    assert evidence["left"] == evidence["right"]


def test_a_missing_program_binding_does_not_apply_the_fast_path(monkeypatch):
    """operational authority が無い run では Program ↔ sha の束縛が張られない。"""

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        CompositeProductionSignalEncoder,
    )

    monkeypatch.setattr(
        CompositeProductionSignalEncoder,
        "operational_authority_factory_for_session",
        lambda self, session: None,
    )
    result, probe, _ = _run_production_check(
        monkeypatch, "binding", _FakeProgram("left"), _FakeProgram("right"),
    )
    payload = result.to_dict()
    assert probe.analyzer_programs == ["left"]
    assert payload["identical_fast_path_disposition"] == {
        "applicable": False, "applied": False, "reason": "program_binding_missing",
    }
    assert payload["function1_identity"] is None


def test_one_checker_instance_does_not_leak_a_pair_assessment(monkeypatch):
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        build_default_cutover_connector,
    )
    from scripts.function_tracer_pcode.checker import EquivalenceChecker

    checker = EquivalenceChecker(debug=False)
    checker.v2_dual_write_pilot_connector = build_default_cutover_connector()
    first, _, checker = _run_production_check(
        monkeypatch, "leak-a", _FakeProgram("left"), _FakeProgram("right"),
        checker=checker, forbid_analysis=True,
    )
    assert first.to_dict()["final_outcome"] == "EQUIVALENT"

    second, probe, _ = _run_production_check(
        monkeypatch, "leak-b", _FakeProgram("left"),
        _FakeProgram("right", sha256=SHA_B), binary2_content_identity=("sha256", SHA_B),
        checker=checker,
    )
    payload = second.to_dict()
    assert probe.analyzer_programs == ["left"]
    assert "identical_fast_path_disposition" not in payload
    assert "decisive_proof_provenance" not in payload
    assert payload["function1_identity"] is None
    assert payload["function2_identity"] is None
    assert not hasattr(checker, "_identical_identity_assessment")


# --------------------------------------------------------------------------
# 4. CLI
# --------------------------------------------------------------------------

def test_identical_fast_path_is_on_by_default_and_can_be_disabled():
    from unittest.mock import patch

    from scripts.function_tracer_pcode.cli.main import parse_arguments

    base = ["--equiv", "binary1", "binary2", "-f", "snippet"]
    with patch.object(sys, "argv", ["main.py"] + base):
        args = parse_arguments()
    assert getattr(args, "no_identical_fast_path", False) is False
    assert (not getattr(args, "no_identical_fast_path", False)) is True

    with patch.object(sys, "argv", ["main.py"] + base + ["--no-identical-fast-path"]):
        args = parse_arguments()
    assert args.no_identical_fast_path is True
    assert (not getattr(args, "no_identical_fast_path", False)) is False


def test_checker_rejects_a_non_bool_fast_path_flag():
    from scripts.function_tracer_pcode.checker import EquivalenceChecker

    with pytest.raises(TypeError):
        EquivalenceChecker(debug=False, identical_fast_path=1)
