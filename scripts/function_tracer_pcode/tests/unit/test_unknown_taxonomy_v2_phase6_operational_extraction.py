from dataclasses import replace
from concurrent.futures import ThreadPoolExecutor
from types import SimpleNamespace

import pytest
import scripts.function_tracer_pcode.authority.process.operational_extraction as operational_extraction

from scripts.function_tracer_pcode.authority.process.operational_extraction import (
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
)
from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.authority.lifecycle.stream import EventRecorder, EventType
from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
    ProductionDualWritePilotSession,
    ProductionPilotExecutionIdentity,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    CompositeProductionSignalEncoder,
    production_signal_scope,
)
from scripts.function_tracer_pcode.ghidra.decompilation_broker import (
    TOP_LEVEL_SOURCE_CONTRACT,
    decompile_function,
)
from scripts.function_tracer_pcode.tests.unit._operational_test_fixtures import (
    Address,
    BrokerAnalyzer,
    BrokerDecompiler,
    Function,
    Program,
    Result,
)


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


def test_lookup_and_error_artifacts_reject_direct_forgery():
    with pytest.raises(TypeError, match="factory-issued"):
        FunctionLookupOutcome(FunctionLookupStatus.MISSING, None)
    with pytest.raises(TypeError, match="factory-issued"):
        OperationalErrorArtifact(
            "decompiler_aborted", "result-1", "source-snapshot",
            "catch-site", None, None, None, None, "forged",
        )


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
