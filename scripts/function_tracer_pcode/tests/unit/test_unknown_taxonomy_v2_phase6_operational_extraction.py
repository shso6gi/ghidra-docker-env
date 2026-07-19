from dataclasses import replace
from types import SimpleNamespace

import pytest
import scripts.function_tracer_pcode.equivalence.v2.operational_extraction as operational_extraction

from scripts.function_tracer_pcode.equivalence.v2.operational_extraction import (
    EXPECTED_OPERATIONAL_COMMON_REGISTRY_DIGEST,
    EXPECTED_OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST,
    EXPECTED_OPERATIONAL_REASON_REGISTRY_DIGEST,
    EXPECTED_OPERATIONAL_RECOVERY_REGISTRY_DIGEST,
    OPERATIONAL_COMMON_EXECUTION_STAGE_REGISTRY,
    OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST,
    OPERATIONAL_REASON_REGISTRY_DIGEST,
    OPERATIONAL_RECOVERY_REGISTRY_DIGEST,
    OPERATIONAL_REASON_REGISTRY,
    OPERATIONAL_RECOVERY_REGISTRY,
    DecompilationArtifactReceipt,
    DecompilationAttemptInputSurface,
    DecompilationAttemptObservation,
    DecompilationAttemptReceipt,
    DecompilationDisposition,
    DecompilationInvocationReceipt,
    FunctionDecompilationTarget,
    FunctionLookupStatus,
    FunctionLookupOutcome,
    HighFunctionIRArtifact,
    HighFunctionObservationCapability,
    OperationalBlockerSignal,
    OperationalCompletionSignal,
    OperationalErrorArtifact,
    OperationalExtractionAuthorityFactory,
    OperationalExtractionPilotEncoder,
    authority_digest,
    canonical_high_function_projection,
    completed_result_structural_identity,
    validate_operational_registry_conservation,
)
from scripts.function_tracer_pcode.equivalence.v2.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.equivalence.v2.stream import EventRecorder, EventType
from scripts.function_tracer_pcode.equivalence.v2.pilot import (
    ProductionDualWritePilotSession,
    ProductionPilotExecutionIdentity,
)
from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
    CompositeProductionSignalEncoder,
    production_signal_scope,
)
from scripts.function_tracer_pcode.analysis.decompilation_broker import (
    TOP_LEVEL_SOURCE_CONTRACT,
    decompile_function,
)


class AddressSpace:
    def __init__(self, name="ram"):
        self.name = name

    def getName(self):
        return self.name


class JavaIntegralLike:
    def __init__(self, value):
        self.value = value

    def __int__(self):
        return self.value

    def __str__(self):
        return str(self.value)


def test_ghidra_integer_losslessly_projects_jpype_style_values():
    assert operational_extraction._ghidra_integer(
        "offset", JavaIntegralLike(0x1000)
    ) == 0x1000
    with pytest.raises(TypeError, match="not a Ghidra integral"):
        operational_extraction._ghidra_integer("offset", 1.0)
    with pytest.raises(ValueError, match="must be nonnegative"):
        operational_extraction._ghidra_integer(
            "offset", JavaIntegralLike(-1), nonnegative=True
        )


class Address:
    def __init__(self, offset, space="ram"):
        self.offset = offset
        self.space = AddressSpace(space)

    def getAddressSpace(self):
        return self.space

    def getOffset(self):
        return self.offset


class Function:
    def __init__(self, entry=0x1000, name="f", program=None):
        self.entry = Address(entry)
        self.name = name
        self.program = program

    def getEntryPoint(self):
        return self.entry

    def getName(self):
        return self.name

    def getProgram(self):
        return self.program

    def getBody(self):
        return Body(self.entry.offset, self.entry.offset + 0x20)

    def getParameters(self):
        return ()

    def getCallingConventionName(self):
        return "__cdecl"

    def getReturn(self):
        return None

    def getReturnType(self):
        return None


class Body:
    def __init__(self, minimum, maximum):
        self.minimum = Address(minimum)
        self.maximum = Address(maximum)

    def getAddressRanges(self):
        return None

    def getMinAddress(self):
        return self.minimum

    def getMaxAddress(self):
        return self.maximum


class CompilerSpec:
    def getCompilerSpecID(self):
        return "gcc"


class Program:
    def __init__(self, manager):
        self.manager = manager

    def getFunctionManager(self):
        return self.manager

    def getExecutableFormat(self):
        return "ELF"

    def getLanguageID(self):
        return "x86:LE:64:default"

    def getCompilerSpec(self):
        return CompilerSpec()

    def getImageBase(self):
        return Address(0x400000)


class Result:
    def __init__(
        self, *, completed=False, timed_out=False, failed=False,
        cancelled=False, function=None, high=None, message="",
    ):
        self.completed = completed
        self.timed_out = timed_out
        self.failed = failed
        self.cancelled = cancelled
        self.function = function
        self.high = high
        self.message = message
        self.high_call_count = 0

    def decompileCompleted(self):
        return self.completed

    def isTimedOut(self):
        return self.timed_out

    def failedToStart(self):
        return self.failed

    def isCancelled(self):
        return self.cancelled

    def getFunction(self):
        return self.function

    def getHighFunction(self):
        self.high_call_count += 1
        return self.high

    def getErrorMessage(self):
        return self.message


def target(entry=0x1000, binary="sha256:binary", factory=None):
    factory = factory or OperationalExtractionAuthorityFactory.for_testing()
    return factory.target_from_fixture(
        binary_content_identity=binary,
        program_identity=("program", "ELF", 0x400000),
        language_id="x86:LE:64:default",
        compiler_spec_id="gcc",
        function_entry=("ram", entry),
        function_body_ranges=(("ram", entry, entry + 0x20),),
    )


def surface(*, signature="int(int)", factory=None):
    factory = factory or OperationalExtractionAuthorityFactory.for_testing()
    return factory.input_surface_from_fixture(
        prototype_identity=("prototype", signature),
        calling_convention_identity="__cdecl",
        parameter_storage_identities=(("register", "RDI", 8),),
        return_storage_identity=("register", "RAX", 8),
    )


def setup_invocation(*, budget=60, ordinal=1, signature="int(int)", proof_requirement_id="q-decomp"):
    factory = OperationalExtractionAuthorityFactory.for_testing()
    t = target(factory=factory)
    s = surface(signature=signature, factory=factory)
    inv = factory.issue_invocation(
        target=t, input_surface=s, proof_requirement_id=proof_requirement_id,
        invocation_identity=f"invocation-{ordinal}",
        invocation_ordinal=ordinal, configured_timeout_seconds=budget,
    )
    return factory, t, s, inv


def completed_chain(*, message="timeout warning", high=None, proof_requirement_id="q-decomp"):
    factory, t, s, inv = setup_invocation(proof_requirement_id=proof_requirement_id)
    result = Result(
        completed=True, function=Function(), high=high, message=message,
    )
    observed = factory.capture_attempt_observation(inv, result)
    attempted = factory.issue_attempt(
        invocation=inv, observation=observed, target=t, input_surface=s,
    )
    artifact = factory.issue_decompilation_artifact(
        target=t, input_surface=s, invocation=inv,
        observation=observed, attempt=attempted,
    )
    return factory, t, s, inv, result, observed, attempted, artifact


def test_operational_registry_is_exact_and_digest_pinned():
    validate_operational_registry_conservation()
    assert OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST == (
        EXPECTED_OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST
    )
    assert OPERATIONAL_COMMON_EXECUTION_STAGE_REGISTRY.normalized_registry_digest == (
        EXPECTED_OPERATIONAL_COMMON_REGISTRY_DIGEST
    )
    assert OPERATIONAL_REASON_REGISTRY_DIGEST == EXPECTED_OPERATIONAL_REASON_REGISTRY_DIGEST
    assert OPERATIONAL_RECOVERY_REGISTRY_DIGEST == EXPECTED_OPERATIONAL_RECOVERY_REGISTRY_DIGEST


def test_signature_change_keeps_target_but_changes_input_surface():
    assert target().target_digest == target().target_digest
    assert surface(signature="int(int)").surface_digest != surface(
        signature="long(long)"
    ).surface_digest
    factory = OperationalExtractionAuthorityFactory.for_testing()
    shared_target = target(factory=factory)
    shared_surface = surface(factory=factory)
    first = factory.issue_invocation(
        target=shared_target, input_surface=shared_surface,
        proof_requirement_id="q-decomp", invocation_identity="invocation-1",
        invocation_ordinal=1, configured_timeout_seconds=30,
    )
    retry = factory.issue_invocation(
        target=shared_target, input_surface=shared_surface,
        proof_requirement_id="q-decomp", invocation_identity="invocation-2",
        invocation_ordinal=2, configured_timeout_seconds=90,
    )
    assert first.target_digest == retry.target_digest
    assert first.input_surface_digest == retry.input_surface_digest
    assert first.receipt_digest != retry.receipt_digest


def test_same_digest_copied_target_is_not_exact_factory_membership():
    factory = OperationalExtractionAuthorityFactory.for_testing()
    original = target(factory=factory)
    copied = replace(original)
    assert copied.target_digest == original.target_digest
    with pytest.raises(ValueError, match="not issued by this factory"):
        factory.issue_invocation(
            target=copied, input_surface=surface(factory=factory),
            proof_requirement_id="q", invocation_identity="copied",
            invocation_ordinal=1, configured_timeout_seconds=10,
        )


@pytest.mark.parametrize(
    "kwargs, disposition",
    (
        ({"timed_out": True}, DecompilationDisposition.TIMED_OUT),
        ({"failed": True}, DecompilationDisposition.FAILED_TO_START),
        ({"cancelled": True}, DecompilationDisposition.CANCELLED),
        ({}, DecompilationDisposition.ABORTED),
    ),
)
def test_structured_flags_not_message_classify_noncompleted(kwargs, disposition):
    factory, _t, _s, inv = setup_invocation()
    observed = factory.capture_attempt_observation(
        inv, Result(message="timeout cancelled failed", **kwargs))
    assert observed.disposition == disposition


def test_nonboolean_structured_flag_is_rejected():
    factory, _t, _s, inv = setup_invocation()
    result = Result()
    result.decompileCompleted = lambda: "false"
    with pytest.raises(TypeError, match="exact bool"):
        factory.capture_attempt_observation(inv, result)


def test_completed_warning_message_stays_completed_and_dag_is_acyclic():
    _factory, t, s, inv, _result, observed, attempted, artifact = completed_chain()
    assert observed.disposition == DecompilationDisposition.COMPLETED
    expected = completed_result_structural_identity(
        target=t, input_surface=s, invocation=inv, observation=observed,
    )
    assert attempted.completed_result_identity == expected
    assert artifact.completed_result_identity == expected
    assert attempted.receipt_digest not in observed.observation_digest
    with pytest.raises(TypeError):
        DecompilationAttemptObservation(
            inv.receipt_digest, True, False, False, False, ("ram", 0x1000),
            DecompilationDisposition.COMPLETED, "forged",
        )


def test_contradictory_flags_and_wrong_result_function_are_rejected():
    factory, _t, _s, inv = setup_invocation()
    with pytest.raises(ValueError, match="contradictory"):
        factory.capture_attempt_observation(
            inv, Result(completed=True, timed_out=True, function=Function())
        )
    factory, t, s, inv = setup_invocation()
    observed = factory.capture_attempt_observation(
        inv, Result(completed=True, function=Function(0x2000))
    )
    with pytest.raises(ValueError, match="differs from target"):
        factory.issue_attempt(
            invocation=inv, observation=observed,
            target=t, input_surface=s,
        )


def test_noncompleted_observation_cannot_move_to_another_invocation_or_q():
    factory = OperationalExtractionAuthorityFactory.for_testing()
    t = target(factory=factory)
    s = surface(factory=factory)
    first = factory.issue_invocation(
        target=t, input_surface=s, proof_requirement_id="q-a",
        invocation_identity="inv-a", invocation_ordinal=1,
        configured_timeout_seconds=10,
    )
    second = factory.issue_invocation(
        target=t, input_surface=s, proof_requirement_id="q-b",
        invocation_identity="inv-b", invocation_ordinal=2,
        configured_timeout_seconds=10,
    )
    observation = factory.capture_attempt_observation(
        first, Result(timed_out=True)
    )
    with pytest.raises(ValueError, match="exact factory membership"):
        factory.issue_attempt(
            invocation=second, observation=observation,
            target=t, input_surface=s,
        )


def test_completed_attempt_cannot_be_artifactized_for_another_target():
    factory, t, s, inv = setup_invocation()
    other = target(entry=0x2000, factory=factory)
    observation = factory.capture_attempt_observation(
        inv, Result(completed=True, function=Function())
    )
    attempt = factory.issue_attempt(
        invocation=inv, observation=observation, target=t, input_surface=s,
    )
    with pytest.raises(ValueError, match="dependency join differs"):
        factory.issue_decompilation_artifact(
            target=other, input_surface=s, invocation=inv,
            observation=observation, attempt=attempt,
        )


class Seq:
    def __init__(self, address, time):
        self.address = Address(address)
        self.time = time

    def getTarget(self):
        return self.address

    def getTime(self):
        return self.time


class Op:
    def __init__(self, address, time, opcode):
        self.seq = Seq(address, time)
        self.opcode = opcode

    def getSeqnum(self):
        return self.seq

    def getOpcode(self):
        return self.opcode

    def getMnemonic(self):
        return f"OP{self.opcode}"

    def getNumInputs(self):
        return 0

    def getOutput(self):
        return None


class Block:
    def __init__(self, index, start, ops):
        self.index = index
        self.start = Address(start)
        self.ops = tuple(ops)

    def getIndex(self):
        return self.index

    def getStart(self):
        return self.start

    def getOutSize(self):
        return 0

    def getIterator(self):
        return iter(self.ops)


class High:
    def __init__(self, blocks):
        self.blocks = tuple(blocks)

    def getFunction(self):
        return Function()

    def getFunctionPrototype(self):
        return Prototype()

    def getBasicBlocks(self):
        return iter(self.blocks)


class Prototype:
    def getModelName(self):
        return "__cdecl"

    def getReturnType(self):
        return None

    def getReturnStorage(self):
        return None

    def getNumParams(self):
        return 0


def test_high_function_is_downstream_and_full_ordered_projection_is_identity():
    high = High((Block(0, 0x1000, (Op(0x1000, 0, 1), Op(0x1004, 1, 2))),))
    factory, t, s, _inv, _result, _obs, _attempt, artifact = completed_chain(high=high)
    capability = factory.consume_high_function(
        artifact=artifact, target=t, input_surface=s,
        proof_requirement_id="q-high",
    )
    assert capability is not None
    ir = factory.issue_ir_artifact(
        capability=capability, decompilation_artifact=artifact,
        target=t, input_surface=s,
    )
    reordered = High((Block(0, 0x1000, (Op(0x1004, 1, 2), Op(0x1000, 0, 1))),))
    assert canonical_high_function_projection(high) == canonical_high_function_projection(reordered)
    assert ir.decompilation_artifact_digest == artifact.artifact_digest
    assert not hasattr(artifact, "ir_projection_digest")
    with pytest.raises(ValueError, match="already consumed"):
        factory.issue_ir_artifact(
            capability=capability, decompilation_artifact=artifact,
            target=t, input_surface=s,
        )
    with pytest.raises(ValueError, match="one-shot"):
        factory.consume_high_function(
            artifact=artifact, target=t, input_surface=s,
            proof_requirement_id="q-high",
        )


def test_high_function_entry_must_match_target():
    high = High((Block(0, 0x1000, (Op(0x1000, 0, 1),)),))
    high.getFunction = lambda: Function(0x2000)
    factory, t, s, _inv, _result, _obs, _attempt, artifact = completed_chain(high=high)
    capability = factory.consume_high_function(
        artifact=artifact, target=t, input_surface=s,
        proof_requirement_id="q-high",
    )
    with pytest.raises(ValueError, match="entry differs"):
        factory.issue_ir_artifact(
            capability=capability, decompilation_artifact=artifact,
            target=t, input_surface=s,
        )


def test_null_high_function_has_no_capability_and_cannot_issue_ir():
    factory, t, s, _inv, _result, _obs, _attempt, artifact = completed_chain(high=None)
    assert factory.consume_high_function(
        artifact=artifact, target=t, input_surface=s,
        proof_requirement_id="q-high",
    ) is None


def test_lookup_miss_and_exception_with_same_text_remain_distinct():
    factory = OperationalExtractionAuthorityFactory.for_testing()
    census = factory.function_census_from_fixture(
        query_identity=("name", "f"), program_identity=("program",),
        function_targets=(), iteration_completed=True,
    )
    missing = factory.lookup_missing(census)
    error = factory.lookup_error(
        catch_site_contract_id="lookup-by-name-v2",
        exception=RuntimeError("same message"),
        query_identity=("name", "f"), program_identity=("program",),
    )
    assert missing.status == FunctionLookupStatus.MISSING
    assert error.status == FunctionLookupStatus.ERROR
    assert missing.census_digest
    assert error.exception_class_identity.endswith("RuntimeError")


def test_lookup_missing_rejects_matching_query_row_and_found_requires_query_match():
    factory = OperationalExtractionAuthorityFactory.for_testing()
    t = target(factory=factory)
    census = factory.function_census_from_fixture(
        query_identity=("name", "f"), program_identity=("program",),
        function_targets=(t,), iteration_completed=True,
        function_lookup_rows=((('name', 'f'), t.target_digest),),
    )
    with pytest.raises(ValueError, match="exact query match"):
        factory.lookup_missing(census)
    with pytest.raises(ValueError, match="does not match lookup query"):
        factory.lookup_found(
            function_object=Function(name="g"), target=t,
            query_identity=("name", "f"), program_identity=("program",),
        )


def test_partial_function_manager_iteration_cannot_issue_complete_census():
    class PartialManager:
        def getFunctions(self, forward):
            assert forward is True
            def rows():
                raise RuntimeError("iteration failed before exhaustion")
                yield None
            return rows()

    factory = OperationalExtractionAuthorityFactory.for_testing()
    manager = PartialManager()
    program = Program(manager)
    program_seed = factory.issue_program_seed(
        program, binary_content_identity="sha256:binary",
    )
    with pytest.raises(RuntimeError, match="before exhaustion"):
        factory.issue_function_census_from_manager(
            program_seed=program_seed, query_identity=("name", "f"),
        )


def test_program_seed_rejects_same_name_entry_foreign_function_for_census_and_found():
    class Manager:
        def __init__(self):
            self.functions = ()

        def getFunctions(self, forward):
            assert forward is True
            return iter(self.functions)

    manager_a, manager_b = Manager(), Manager()
    program_a, program_b = Program(manager_a), Program(manager_b)
    owned = Function(name="f", entry=0x1000, program=program_a)
    foreign = Function(name="f", entry=0x1000, program=program_b)
    manager_a.functions = (foreign,)
    factory = OperationalExtractionAuthorityFactory(
        result_occurrence_id="result-1",
        source_snapshot_fingerprint="source-snapshot",
        execution_identity_digest="execution-1",
    )
    seed = factory.issue_program_seed(
        program_a, binary_content_identity="sha256:binary",
    )
    target_a = factory.target_from_ghidra(seed, owned)
    with pytest.raises(ValueError, match="foreign-program"):
        factory.issue_function_census_from_manager(
            program_seed=seed, query_identity=("name", "f"),
        )
    with pytest.raises(ValueError, match="program differs"):
        factory.lookup_found(
            function_object=foreign, target=target_a,
            query_identity=("name", "f"), program_seed=seed,
        )


def test_program_seed_accepts_equal_jpype_proxy_for_same_java_program():
    class Manager:
        def getFunctions(self, forward):
            assert forward is True
            return iter(())

    class EqualProgramProxy:
        def __init__(self, program):
            self.program = program

        def __eq__(self, other):
            return other is self.program

    program = Program(Manager())
    factory = OperationalExtractionAuthorityFactory(
        result_occurrence_id="result-1",
        source_snapshot_fingerprint="source-snapshot",
        execution_identity_digest="execution-1",
    )
    seed = factory.issue_program_seed(
        program, binary_content_identity="sha256:binary",
    )
    function = Function(
        name="f", entry=0x1000, program=EqualProgramProxy(program),
    )

    observed = factory.target_from_ghidra(seed, function)

    assert observed.binary_content_identity == "sha256:binary"


def test_empty_census_and_missing_outcome_remain_cross_binary_distinct():
    class EmptyManager:
        def getFunctions(self, forward):
            assert forward is True
            return iter(())

    def build(binary):
        factory = OperationalExtractionAuthorityFactory(
            result_occurrence_id="result-1",
            source_snapshot_fingerprint="same-source-snapshot",
            execution_identity_digest="execution-1",
        )
        program = Program(EmptyManager())
        seed = factory.issue_program_seed(
            program, binary_content_identity=binary,
        )
        census = factory.issue_function_census_from_manager(
            program_seed=seed, query_identity=("name", "missing"),
        )
        return seed, census, factory.lookup_missing(census)

    left_seed, left_census, left_missing = build("sha256:left")
    right_seed, right_census, right_missing = build("sha256:right")
    assert left_seed.program_identity == right_seed.program_identity
    assert left_seed.seed_digest != right_seed.seed_digest
    assert left_census.program_seed_digest == left_seed.seed_digest
    assert right_census.program_seed_digest == right_seed.seed_digest
    assert left_census.receipt_digest != right_census.receipt_digest
    assert left_missing.program_seed_digest != right_missing.program_seed_digest
    assert left_missing.outcome_digest != right_missing.outcome_digest


def test_unregistered_reason_producer_pair_is_rejected():
    with pytest.raises(ValueError, match="producer differs"):
        OperationalBlockerSignal(
            "high_function_ir_unavailable", target(), ("source",),
            "function-decompilation-artifact-producer-v2",
        )


def test_lookup_and_error_artifacts_reject_direct_forgery():
    with pytest.raises(TypeError, match="factory-issued"):
        FunctionLookupOutcome(FunctionLookupStatus.MISSING, None)
    with pytest.raises(TypeError, match="factory-issued"):
        OperationalErrorArtifact(
            "decompiler_aborted", "result-1", "source-snapshot",
            "catch-site", None, None, None, None, "forged",
        )


def test_error_artifact_ignores_message_and_seals_kind():
    factory, t, s, inv = setup_invocation()
    observation = factory.capture_attempt_observation(inv, Result())
    attempt = factory.issue_attempt(
        invocation=inv, observation=observation, target=t, input_surface=s,
    )
    artifact = factory.issue_error(
        error_kind="decompiler_aborted",
        catch_site_contract_id="top-level-decompile-v2",
        target=t, attempt=attempt,
    )
    assert factory.error_event_intent(artifact).event_type == EventType.ERROR
    with pytest.raises(ValueError, match="not sealed"):
        factory.issue_error(
            error_kind="timeout-ish-message",
            catch_site_contract_id="top-level-decompile-v2",
        )


def test_error_rejects_cross_factory_same_digest_target():
    owner, t, s, inv = setup_invocation()
    observation = owner.capture_attempt_observation(inv, Result())
    attempt = owner.issue_attempt(
        invocation=inv, observation=observation, target=t, input_surface=s,
    )
    foreign = OperationalExtractionAuthorityFactory.for_testing()
    same_digest_foreign_target = target(factory=foreign)
    assert same_digest_foreign_target.target_digest == t.target_digest
    with pytest.raises(ValueError, match="target is not exact factory membership"):
        owner.issue_error(
            error_kind="decompiler_aborted",
            catch_site_contract_id="top-level-decompile-v2",
            target=same_digest_foreign_target, attempt=attempt,
        )


def test_ir_rejects_missing_block_iterator():
    high = High((Block(0, 0x1000, ()),))
    high.blocks[0].getIterator = lambda: None
    factory, t, s, _inv, _result, _obs, _attempt, artifact = completed_chain(high=high)
    capability = factory.consume_high_function(
        artifact=artifact, target=t, input_surface=s,
        proof_requirement_id="q-high",
    )
    with pytest.raises(ValueError, match="operation census"):
        factory.issue_ir_artifact(
            capability=capability, decompilation_artifact=artifact,
            target=t, input_surface=s,
        )


def test_ir_rejects_none_mandatory_input_and_storage_varnode():
    class InputOp(Op):
        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return None

    high = High((Block(0, 0x1000, (InputOp(0x1000, 0, 1),)),))
    factory, t, s, _inv, _result, _obs, _attempt, artifact = completed_chain(high=high)
    capability = factory.consume_high_function(
        artifact=artifact, target=t, input_surface=s,
        proof_requirement_id="q-high",
    )
    with pytest.raises(ValueError, match="input varnode"):
        factory.issue_ir_artifact(
            capability=capability, decompilation_artifact=artifact,
            target=t, input_surface=s,
        )

    class Storage:
        def getVarnodes(self):
            return (None,)

    class StoragePrototype(Prototype):
        def getReturnStorage(self):
            return Storage()

    high2 = High((Block(0, 0x1000, (Op(0x1000, 0, 1),)),))
    high2.getFunctionPrototype = lambda: StoragePrototype()
    factory2, t2, s2, _inv, _result, _obs, _attempt, artifact2 = completed_chain(high=high2)
    capability2 = factory2.consume_high_function(
        artifact=artifact2, target=t2, input_surface=s2,
        proof_requirement_id="q-high",
    )
    with pytest.raises(ValueError, match="storage varnode"):
        factory2.issue_ir_artifact(
            capability=capability2, decompilation_artifact=artifact2,
            target=t2, input_surface=s2,
        )


def test_encoder_emits_independent_cause_and_exact_artifact_completion():
    session = SimpleNamespace(identity=SimpleNamespace(
        result_occurrence_id="result-1",
        source_snapshot_fingerprint="source-snapshot",
        execution_identity_digest="execution-1",
    ))
    factory = OperationalExtractionAuthorityFactory.for_testing()
    blocker_target = target(factory=factory)
    blocker = OperationalBlockerSignal(
        "function_decompilation_artifact_unavailable",
        blocker_target,
        ("top-level-decompile",),
        "function-decompilation-artifact-producer-v2",
    )
    encoder = OperationalExtractionPilotEncoder(factory)
    observed = encoder(session, blocker)
    assert observed[0].event_type == EventType.CAUSE_OBSERVED
    q_id = encoder.authority_for_signal(session, blocker).occurrence.proof_requirement_ids[0]
    s = surface(factory=factory)
    inv = factory.issue_invocation(
        target=blocker_target, input_surface=s, proof_requirement_id=q_id,
        invocation_identity="encoder-invocation", invocation_ordinal=1,
        configured_timeout_seconds=60,
    )
    result = Result(completed=True, function=Function())
    observation = factory.capture_attempt_observation(inv, result)
    attempt = factory.issue_attempt(
        invocation=inv, observation=observation,
        target=blocker_target, input_surface=s,
    )
    artifact = factory.issue_decompilation_artifact(
        target=blocker_target, input_surface=s, invocation=inv,
        observation=observation, attempt=attempt,
    )
    completed = encoder(session, OperationalCompletionSignal(
        blocker, artifact,
    ))
    assert completed[0].event_type == EventType.REQUIREMENT_COMPLETED


def test_phase7_digest_for_operational_completion_uses_public_authority_only():
    factory, owned_target, _surface, _inv, _result, _obs, _attempt, artifact = (
        completed_chain()
    )
    blocker = OperationalBlockerSignal(
        "function_decompilation_artifact_unavailable",
        owned_target,
        ("top-level-decompile",),
        "function-decompilation-artifact-producer-v2",
    )
    signal = OperationalCompletionSignal(blocker, artifact)

    authority = signal._phase7_signal_authority()
    digest = authority_digest(authority)

    assert len(digest) == 64
    assert authority["target_digest"] == owned_target.target_digest
    assert authority["completion_artifact_digest"] == artifact.artifact_digest


def test_encoder_rejects_cross_factory_artifact_and_session_identity():
    session = SimpleNamespace(identity=SimpleNamespace(
        result_occurrence_id="result-1",
        source_snapshot_fingerprint="source-snapshot",
        execution_identity_digest="execution-1",
    ))
    owner = OperationalExtractionAuthorityFactory.for_testing()
    foreign, foreign_target, _surface, _inv, _result, _obs, _attempt, artifact = completed_chain()
    blocker = OperationalBlockerSignal(
        "function_decompilation_artifact_unavailable",
        target(factory=owner), ("source",),
        "function-decompilation-artifact-producer-v2",
    )
    encoder = OperationalExtractionPilotEncoder(owner)
    with pytest.raises(ValueError, match="exact factory membership"):
        encoder(session, OperationalCompletionSignal(blocker, artifact))


def test_high_function_blocker_completes_its_own_q_not_decomp_dependency_q():
    session = SimpleNamespace(identity=SimpleNamespace(
        result_occurrence_id="result-1",
        source_snapshot_fingerprint="source-snapshot",
        execution_identity_digest="execution-1",
    ))
    factory = OperationalExtractionAuthorityFactory.for_testing()
    t = target(factory=factory)
    s = surface(factory=factory)
    encoder = OperationalExtractionPilotEncoder(factory)
    decomp_blocker = OperationalBlockerSignal(
        "function_decompilation_artifact_unavailable", t,
        ("decompile",), "function-decompilation-artifact-producer-v2",
    )
    high_blocker = OperationalBlockerSignal(
        "high_function_ir_unavailable", t,
        ("high-function",), "high-function-ir-validator-v2",
    )
    decomp_q = encoder.authority_for_signal(
        session, decomp_blocker
    ).occurrence.proof_requirement_ids[0]
    high_q = encoder.authority_for_signal(
        session, high_blocker
    ).occurrence.proof_requirement_ids[0]
    inv = factory.issue_invocation(
        target=t, input_surface=s, proof_requirement_id=decomp_q,
        invocation_identity="full-chain", invocation_ordinal=1,
        configured_timeout_seconds=60,
    )
    high = High((Block(0, 0x1000, (Op(0x1000, 0, 1),)),))
    result = Result(completed=True, function=Function(), high=high)
    observation = factory.capture_attempt_observation(inv, result)
    attempt = factory.issue_attempt(
        invocation=inv, observation=observation, target=t, input_surface=s,
    )
    decomp_artifact = factory.issue_decompilation_artifact(
        target=t, input_surface=s, invocation=inv,
        observation=observation, attempt=attempt,
    )
    capability = factory.consume_high_function(
        artifact=decomp_artifact, target=t, input_surface=s,
        proof_requirement_id=high_q,
    )
    ir_artifact = factory.issue_ir_artifact(
        capability=capability, decompilation_artifact=decomp_artifact,
        target=t, input_surface=s,
    )
    assert ir_artifact.dependency_decompilation_requirement_id == decomp_q
    assert ir_artifact.proof_requirement_id == high_q
    recorder = EventRecorder(
        stream_id="stream-1", result_occurrence_id="result-1",
        source_snapshot_fingerprint="source-snapshot",
    )
    for signal in (
        decomp_blocker,
        OperationalCompletionSignal(decomp_blocker, decomp_artifact),
        high_blocker,
        OperationalCompletionSignal(high_blocker, ir_artifact),
    ):
        for intent in encoder(session, signal):
            recorder.append(intent)
    reduction = ShadowLifecycleReducer(
        reason_registry=OPERATIONAL_REASON_REGISTRY,
        recovery_registry=OPERATIONAL_RECOVERY_REGISTRY,
    ).replay(recorder.seal())
    assert len(reduction.projection.c_active_base) == 0
    assert len(reduction.projection.q_open_base) == 0


class BrokerDecompiler:
    def __init__(self, result):
        self.result = result
        self.calls = 0

    def decompileFunction(self, function, timeout, monitor):
        self.calls += 1
        return self.result


class BrokerAnalyzer:
    def __init__(self, program, decompiler):
        self.program = program
        self.decompiler = decompiler

    def _get_decompiler(self):
        return self.decompiler


def test_broker_is_transparent_when_v2_route_is_inactive():
    raw = Result(completed=True, function=Function())
    decompiler = BrokerDecompiler(raw)
    analyzer = BrokerAnalyzer(None, decompiler)
    observed = decompile_function(
        analyzer, Function(), 60, None,
        source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
    )
    assert observed is raw
    assert decompiler.calls == 1


def test_broker_active_route_dual_writes_and_calls_ghidra_once():
    manager = type("Manager", (), {"getFunctions": lambda self, forward: iter(())})()
    program = Program(manager)
    function = Function(program=program)
    high = High((Block(0, 0x1000, (Op(0x1000, 0, 1),)),))
    raw = Result(completed=True, function=function, high=high)
    decompiler = BrokerDecompiler(raw)
    analyzer = BrokerAnalyzer(program, decompiler)
    operational_encoder = OperationalExtractionPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        OperationalBlockerSignal: operational_encoder,
        OperationalCompletionSignal: operational_encoder,
    })
    reducer = ShadowLifecycleReducer(
        reason_registry=OPERATIONAL_REASON_REGISTRY,
        recovery_registry=OPERATIONAL_RECOVERY_REGISTRY,
    )
    session = ProductionDualWritePilotSession(
        ProductionPilotExecutionIdentity.create({"case": "broker-active"}),
        reducer,
        composite,
    )
    session.domain_signal_state["operational_program_binary_identities"] = {
        id(program): "sha256:binary",
    }
    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )
        assert observed.getHighFunction() is high
        assert observed.getHighFunction() is high
    assert decompiler.calls == 1
    assert raw.high_call_count == 1
    assert session.domain_signal_error_kinds == []
    reduction = reducer.replay(session.recorder.seal())
    assert reduction.projection.c_active_base == ()
    assert reduction.projection.q_open_base == ()


def test_broker_preserves_raw_high_function_when_shadow_ir_validation_fails():
    manager = type("Manager", (), {"getFunctions": lambda self, forward: iter(())})()
    program = Program(manager)
    function = Function(program=program)
    high = High((Block(0, 0x1000, (Op(0x1000, 0, 1),)),))
    high.blocks[0].getIterator = lambda: None
    raw = Result(completed=True, function=function, high=high)
    decompiler = BrokerDecompiler(raw)
    analyzer = BrokerAnalyzer(program, decompiler)
    operational_encoder = OperationalExtractionPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        OperationalBlockerSignal: operational_encoder,
        OperationalCompletionSignal: operational_encoder,
    })
    session = ProductionDualWritePilotSession(
        ProductionPilotExecutionIdentity.create({"case": "broker-malformed-ir"}),
        ShadowLifecycleReducer(
            reason_registry=OPERATIONAL_REASON_REGISTRY,
            recovery_registry=OPERATIONAL_RECOVERY_REGISTRY,
        ),
        composite,
    )
    session.domain_signal_state["operational_program_binary_identities"] = {
        id(program): "sha256:binary",
    }
    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )
        assert observed.getHighFunction() is high
        assert observed.getHighFunction() is high
    assert decompiler.calls == 1
    assert raw.high_call_count == 1
    assert session.domain_signal_error_kinds


def test_broker_reraises_exact_raw_high_function_exception_once():
    class RaisingResult(Result):
        def __init__(self, error, **kwargs):
            super().__init__(**kwargs)
            self.error = error

        def getHighFunction(self):
            self.high_call_count += 1
            raise self.error

    manager = type("Manager", (), {"getFunctions": lambda self, forward: iter(())})()
    program = Program(manager)
    function = Function(program=program)
    error = RuntimeError("raw getHighFunction failure")
    raw = RaisingResult(error, completed=True, function=function)
    decompiler = BrokerDecompiler(raw)
    analyzer = BrokerAnalyzer(program, decompiler)
    operational_encoder = OperationalExtractionPilotEncoder()
    session = ProductionDualWritePilotSession(
        ProductionPilotExecutionIdentity.create({"case": "broker-high-error"}),
        ShadowLifecycleReducer(
            reason_registry=OPERATIONAL_REASON_REGISTRY,
            recovery_registry=OPERATIONAL_RECOVERY_REGISTRY,
        ),
        CompositeProductionSignalEncoder({
            OperationalBlockerSignal: operational_encoder,
            OperationalCompletionSignal: operational_encoder,
        }),
    )
    session.domain_signal_state["operational_program_binary_identities"] = {
        id(program): "sha256:binary",
    }
    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )
        with pytest.raises(RuntimeError) as first:
            observed.getHighFunction()
        with pytest.raises(RuntimeError) as second:
            observed.getHighFunction()
    assert first.value is error
    assert second.value is error
    assert raw.high_call_count == 1
    assert session.domain_signal_error_kinds


def test_broker_is_transparent_with_partial_composite_without_operational_route():
    class UnrelatedSignal:
        pass

    raw = Result(completed=True, function=Function())
    decompiler = BrokerDecompiler(raw)
    analyzer = BrokerAnalyzer(None, decompiler)
    session = ProductionDualWritePilotSession(
        ProductionPilotExecutionIdentity.create({"case": "partial-composite"}),
        ShadowLifecycleReducer(
            reason_registry=OPERATIONAL_REASON_REGISTRY,
            recovery_registry=OPERATIONAL_RECOVERY_REGISTRY,
        ),
        CompositeProductionSignalEncoder({UnrelatedSignal: lambda session, signal: ()}),
    )
    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, Function(), 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        )
    assert observed is raw
    assert decompiler.calls == 1
    assert session.domain_signal_error_kinds == []
