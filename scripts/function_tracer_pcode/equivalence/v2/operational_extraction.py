"""Phase 6.6 operational extraction and decompilation authority.

The module keeps semantic artifact absence separate from operational failure and
records decompiler results through an acyclic, factory-issued receipt graph.
Final decision selection and durable supervisor I/O live at the execution
boundary; this module supplies their typed inputs.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
import secrets
from threading import RLock
from types import MappingProxyType
from typing import Any, Iterable, Mapping, Optional, Sequence

from .contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    IdentityScope,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementCompletionReceipt,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    authority_digest,
    canonical_value,
    requirement_slot,
)
from .execution_authority import ProducerStageContract, ProducerStageRegistry
from .registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from .stream import (
    CauseObservedEventAuthority,
    ErrorEventAuthority,
    EventIntent,
    EventType,
    RequirementCompletedEventAuthority,
)


OPERATIONAL_EXTRACTION_DOMAIN_ID = "operational-extraction-decompilation-v2"
OPERATIONAL_EXTRACTION_REGISTRY_VERSION = 1
DECOMPILER_CONTRACT_VERSION = "decompiler-artifact-extraction-v2"
IR_EXTRACTION_SCHEMA_VERSION = 1


class DecompilationDisposition(str, Enum):
    COMPLETED = "COMPLETED"
    TIMED_OUT = "TIMED_OUT"
    FAILED_TO_START = "FAILED_TO_START"
    CANCELLED = "CANCELLED"
    ABORTED = "ABORTED"


class FunctionLookupStatus(str, Enum):
    FOUND = "FOUND"
    MISSING = "MISSING"
    ERROR = "ERROR"


SEALED_OPERATIONAL_ERROR_KINDS = frozenset({
    "function_lookup_miss",
    "function_lookup_exception",
    "decompiler_failed_to_start",
    "decompiler_cancelled",
    "decompiler_aborted",
    "analysis_exception",
    "strategy_exception",
    "unexpected_pairwise_state",
    "operational_authority_invalid",
})


@dataclass(frozen=True)
class OperationalReasonSpec:
    reason_id: str
    target_kind: str
    proof_kind: str
    category: str

    @property
    def contract_definition_id(self) -> str:
        return self.reason_id + "-recovery"


_REASON_ROWS = (
    (
        "function_decompilation_artifact_unavailable",
        "function_decompilation_target",
        "function_decompilation_artifact",
        "operational_extraction",
    ),
    (
        "high_function_ir_unavailable",
        "function_decompilation_target",
        "high_function_ir_materialization",
        "operational_extraction",
    ),
)

OPERATIONAL_REASON_SPECS: Mapping[str, OperationalReasonSpec] = MappingProxyType({
    row[0]: OperationalReasonSpec(*row) for row in _REASON_ROWS
})


def _reason_definition(spec: OperationalReasonSpec) -> ReasonDefinition:
    return ReasonDefinition(
        spec.reason_id,
        spec.category,
        "proof_obligation",
        "blocks_decision",
        frozenset((spec.target_kind,)),
        ("stable_function_target", "source_snapshot", "missing_artifact"),
        frozenset((spec.proof_kind,)),
        True,
        OPERATIONAL_EXTRACTION_DOMAIN_ID,
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    )


def _satisfaction_contract(spec: OperationalReasonSpec) -> SatisfactionContractDefinition:
    return SatisfactionContractDefinition(
        spec.contract_definition_id,
        1,
        (RequirementSlotDefinition("artifact", frozenset((spec.proof_kind,))),),
        requirement_slot("artifact"),
    )


OPERATIONAL_REASON_REGISTRY = SealedReasonRegistry.build(
    _reason_definition(spec) for spec in OPERATIONAL_REASON_SPECS.values()
)
OPERATIONAL_RECOVERY_REGISTRY = SealedRecoveryRegistry.build(
    _satisfaction_contract(spec) for spec in OPERATIONAL_REASON_SPECS.values()
)


def operational_reason_registry_authority_dict() -> dict[str, Any]:
    return {
        "registry_id": OPERATIONAL_EXTRACTION_DOMAIN_ID + ":reasons",
        "registry_version": OPERATIONAL_EXTRACTION_REGISTRY_VERSION,
        "rows": tuple(
            (
                item.reason_id, item.domain, item.reason_class,
                item.decision_effect, tuple(sorted(item.allowed_target_kinds)),
                item.required_evidence_contract,
                tuple(sorted(item.allowed_proof_kinds)),
                item.terminal_eligibility, item.canonicalization_policy_id,
                item.recovery_addressability.value, item.schema_version,
            )
            for item in OPERATIONAL_REASON_REGISTRY.snapshot()
        ),
    }


def operational_recovery_registry_authority_dict() -> dict[str, Any]:
    return {
        "registry_id": OPERATIONAL_EXTRACTION_DOMAIN_ID + ":recovery",
        "registry_version": OPERATIONAL_EXTRACTION_REGISTRY_VERSION,
        "rows": tuple(
            (
                item.contract_definition_id,
                item.contract_version,
                tuple(
                    (slot.name, tuple(sorted(slot.allowed_proof_kinds)))
                    for slot in item.requirement_slots
                ),
                item.normalized_expression_digest,
                item.schema_version,
            )
            for item in OPERATIONAL_RECOVERY_REGISTRY.snapshot()
        ),
    }


OPERATIONAL_REASON_REGISTRY_DIGEST = authority_digest(
    operational_reason_registry_authority_dict()
)
OPERATIONAL_RECOVERY_REGISTRY_DIGEST = authority_digest(
    operational_recovery_registry_authority_dict()
)


OPERATIONAL_REASON_PRODUCER_CONSERVATION = MappingProxyType({
    "function_decompilation_artifact_unavailable": (
        "function_decompilation_artifact",
        "function-decompilation-artifact-producer-v2",
        "decompiler-process-runner-v1",
    ),
    "high_function_ir_unavailable": (
        "high_function_ir_materialization",
        "high-function-ir-validator-v2",
        "high-function-ir-proof-factory-v1",
    ),
})


@dataclass(frozen=True)
class OperationalProducerStageSpec:
    producer_contract_id: str
    producer_version: str
    proof_stage: str
    proof_kind: str
    capability: str
    execution_issuer_id: str
    allowed_statuses: tuple[str, ...]
    terminal_eligible_statuses: tuple[str, ...]
    terminal_priority: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "allowed_statuses", tuple(sorted(self.allowed_statuses)))
        object.__setattr__(
            self,
            "terminal_eligible_statuses",
            tuple(sorted(self.terminal_eligible_statuses)),
        )
        if not set(self.terminal_eligible_statuses).issubset(self.allowed_statuses):
            raise ValueError("operational terminal status is not allowed")

    def authority_tuple(self) -> tuple[Any, ...]:
        return (
            self.producer_contract_id,
            self.producer_version,
            self.proof_stage,
            self.proof_kind,
            self.capability,
            self.execution_issuer_id,
            self.allowed_statuses,
            self.terminal_eligible_statuses,
            self.terminal_priority,
        )

    def common_contract(self) -> ProducerStageContract:
        return ProducerStageContract(
            OPERATIONAL_EXTRACTION_DOMAIN_ID,
            self.producer_contract_id,
            self.producer_version,
            self.proof_stage,
            self.execution_issuer_id,
            frozenset(self.allowed_statuses),
            frozenset(self.terminal_eligible_statuses),
            self.terminal_priority,
        )


OPERATIONAL_PRODUCER_STAGE_SPECS = (
    OperationalProducerStageSpec(
        "function-decompilation-artifact-producer-v2", "2",
        "function_decompilation_artifact", "function_decompilation_artifact",
        "PROCESS_ARTIFACT_OR_TIMEOUT", "decompiler-process-runner-v1",
        ("attempted",), ("attempted",), 190,
    ),
    OperationalProducerStageSpec(
        "high-function-ir-validator-v2", "2",
        "high_function_ir_materialization", "high_function_ir_materialization",
        "STRUCTURAL_ONLY", "high-function-ir-proof-factory-v1",
        ("structural_proof",), (), 200,
    ),
)


def operational_registry_authority_dict() -> dict[str, Any]:
    return {
        "registry_id": OPERATIONAL_EXTRACTION_DOMAIN_ID,
        "registry_version": OPERATIONAL_EXTRACTION_REGISTRY_VERSION,
        "rows": tuple(row.authority_tuple() for row in OPERATIONAL_PRODUCER_STAGE_SPECS),
    }


OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST = authority_digest(
    operational_registry_authority_dict()
)
OPERATIONAL_COMMON_EXECUTION_STAGE_REGISTRY = ProducerStageRegistry(
    OPERATIONAL_EXTRACTION_REGISTRY_VERSION,
    tuple(row.common_contract() for row in OPERATIONAL_PRODUCER_STAGE_SPECS),
)
EXPECTED_OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST = (
    "581fbcc1e45076ab082856948e41bfeb0236b9b33a2624eb9d3da4dd834264b5"
)
EXPECTED_OPERATIONAL_COMMON_REGISTRY_DIGEST = (
    "a1505d67d3f430cb484d32b6763aa9f83b623437dc6269df4c83fba01c84b4a3"
)
EXPECTED_OPERATIONAL_REASON_REGISTRY_DIGEST = (
    "7edf2c910c16c7f872e988dfecf42437843dafcf2fe2b17c09ae3476edefa273"
)
EXPECTED_OPERATIONAL_RECOVERY_REGISTRY_DIGEST = (
    "1ade2e1a08d59a354f0939ac0bc5bc668f812a46a63a6582c3072ad809f99afa"
)
if OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST != (
    EXPECTED_OPERATIONAL_PRODUCER_STAGE_REGISTRY_DIGEST
):
    raise ValueError("operational producer registry authority digest drift")
if OPERATIONAL_COMMON_EXECUTION_STAGE_REGISTRY.normalized_registry_digest != (
    EXPECTED_OPERATIONAL_COMMON_REGISTRY_DIGEST
):
    raise ValueError("operational common registry authority digest drift")
if OPERATIONAL_REASON_REGISTRY_DIGEST != EXPECTED_OPERATIONAL_REASON_REGISTRY_DIGEST:
    raise ValueError("operational reason registry authority digest drift")
if OPERATIONAL_RECOVERY_REGISTRY_DIGEST != EXPECTED_OPERATIONAL_RECOVERY_REGISTRY_DIGEST:
    raise ValueError("operational recovery registry authority digest drift")


def validate_operational_registry_conservation() -> None:
    if tuple(OPERATIONAL_REASON_SPECS) != tuple(
        sorted(OPERATIONAL_REASON_SPECS)
    ):
        raise ValueError("operational reason registry is not canonically ordered")
    stages = tuple(row.proof_stage for row in OPERATIONAL_PRODUCER_STAGE_SPECS)
    if stages != (
        "function_decompilation_artifact",
        "high_function_ir_materialization",
    ):
        raise ValueError("operational producer stages differ from sealed contract")
    for reason_id, spec in OPERATIONAL_REASON_SPECS.items():
        definition = OPERATIONAL_REASON_REGISTRY.get(reason_id)
        contract = OPERATIONAL_RECOVERY_REGISTRY.get(
            spec.contract_definition_id, 1
        )
        if definition.allowed_proof_kinds != frozenset((spec.proof_kind,)):
            raise ValueError("operational reason/proof-kind conservation failed")
        if contract.requirement_slots[0].allowed_proof_kinds != frozenset((spec.proof_kind,)):
            raise ValueError("operational recovery/proof-kind conservation failed")
        proof_kind, producer_id, issuer_id = OPERATIONAL_REASON_PRODUCER_CONSERVATION[reason_id]
        rows = tuple(row for row in OPERATIONAL_PRODUCER_STAGE_SPECS if (
            row.proof_kind == proof_kind
            and row.producer_contract_id == producer_id
            and row.execution_issuer_id == issuer_id
        ))
        if proof_kind != spec.proof_kind or len(rows) != 1:
            raise ValueError("operational reason/producer/issuer conservation failed")


def _exact_string(name: str, value: Any) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be a non-empty exact string")
    return value


def _call_noarg(obj: Any, name: str, default: Any = None) -> Any:
    member = getattr(obj, name, None)
    if not callable(member):
        return default
    return member()


def _call_exact_bool(obj: Any, name: str) -> bool:
    member = getattr(obj, name, None)
    if not callable(member):
        raise TypeError(f"structured decompiler flag {name} is unavailable")
    value = member()
    if type(value) is not bool:
        raise TypeError(f"structured decompiler flag {name} is not exact bool")
    return value


def _ghidra_integer(name: str, value: Any, *, nonnegative: bool = False) -> int:
    """Losslessly project a JPype Java integral returned by a Ghidra API."""

    if type(value) is bool or value is None or isinstance(
        value, (str, bytes, bytearray, float, complex)
    ):
        raise TypeError(f"{name} is not a Ghidra integral value")
    try:
        projected = int(value)
    except (TypeError, ValueError, OverflowError) as exc:
        raise TypeError(f"{name} is not a Ghidra integral value") from exc
    if str(value) != str(projected):
        raise ValueError(f"{name} cannot be projected losslessly")
    if nonnegative and projected < 0:
        raise ValueError(f"{name} must be nonnegative")
    return projected


def _address_identity(address: Any) -> tuple[Any, ...]:
    if address is None:
        raise ValueError("stable address identity is unavailable")
    space = _call_noarg(address, "getAddressSpace")
    space_name = _call_noarg(space, "getName") if space is not None else None
    raw_offset = _call_noarg(address, "getOffset")
    if type(space_name) is not str:
        raise ValueError("stable address space/offset identity is unavailable")
    offset = _ghidra_integer("address offset", raw_offset)
    return (space_name, offset)


def _data_type_identity(data_type: Any) -> Any:
    if data_type is None:
        return None
    name = _call_noarg(data_type, "getName")
    raw_length = _call_noarg(data_type, "getLength")
    length = (
        _ghidra_integer("data-type length", raw_length)
        if raw_length is not None else None
    )
    path = _call_noarg(data_type, "getPathName")
    if name is not None and type(name) is not str:
        raise TypeError("data-type name is not exact string")
    if path is not None and type(path) is not str:
        raise TypeError("data-type path is not exact string")
    return (name, length, path)


def _variable_storage_identity(variable: Any) -> Any:
    storage = _call_noarg(variable, "getVariableStorage")
    if storage is None:
        return None
    varnodes = _call_noarg(storage, "getVarnodes")
    if varnodes is None:
        raise ValueError("variable storage lacks complete varnode census")
    return tuple(_varnode_projection_without_high(item) for item in varnodes)


def _function_lookup_keys(function: Any) -> tuple[Any, ...]:
    name = _call_noarg(function, "getName")
    if type(name) is not str or not name:
        raise ValueError("function lookup name identity is unavailable")
    entry = _address_identity(_call_noarg(function, "getEntryPoint"))
    return tuple(sorted((
        canonical_value(("name", name)),
        canonical_value(("entry", entry)),
    ), key=authority_digest))


_TARGET_TOKEN = object()
_INPUT_SURFACE_TOKEN = object()
_INVOCATION_TOKEN = object()
_ATTEMPT_IDENTITY_TOKEN = object()
_INVOCATION_CENSUS_TOKEN = object()
_OBSERVATION_TOKEN = object()
_ATTEMPT_TOKEN = object()
_DECOMP_ARTIFACT_TOKEN = object()
_HIGH_CAPABILITY_TOKEN = object()
_IR_ARTIFACT_TOKEN = object()
_ERROR_ARTIFACT_TOKEN = object()
_LOOKUP_OUTCOME_TOKEN = object()
_PROGRAM_SEED_TOKEN = object()


@dataclass(frozen=True)
class GhidraProgramAuthoritySeed:
    binary_content_identity: str
    program_identity: tuple[Any, ...]
    program: Any = field(repr=False, compare=False)
    function_manager: Any = field(repr=False, compare=False)
    seed_digest: str = ""
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _PROGRAM_SEED_TOKEN:
            raise TypeError("Ghidra program seed must be factory-issued")


@dataclass(frozen=True)
class FunctionDecompilationTarget:
    binary_content_identity: str
    program_identity: tuple[Any, ...]
    language_id: str
    compiler_spec_id: str
    function_entry: tuple[Any, ...]
    function_body_ranges: tuple[tuple[Any, ...], ...]
    target_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _TARGET_TOKEN:
            raise TypeError("function decompilation target must be factory-issued")

    @classmethod
    def _issue(
        cls,
        *,
        binary_content_identity: str,
        program_identity: Sequence[Any],
        language_id: str,
        compiler_spec_id: str,
        function_entry: Sequence[Any],
        function_body_ranges: Iterable[Sequence[Any]],
        _factory_token: object,
    ) -> "FunctionDecompilationTarget":
        if _factory_token is not _TARGET_TOKEN:
            raise TypeError("function decompilation target issuer is invalid")
        _exact_string("binary content identity", binary_content_identity)
        _exact_string("language ID", language_id)
        _exact_string("compiler spec ID", compiler_spec_id)
        program_key = tuple(canonical_value(tuple(program_identity)))
        entry = tuple(canonical_value(tuple(function_entry)))
        ranges = tuple(sorted(tuple(canonical_value(tuple(item))) for item in function_body_ranges))
        if not program_key or not entry or not ranges or len(ranges) != len(set(ranges)):
            raise ValueError("function target identity is incomplete or ambiguous")
        payload = {
            "binary_content_identity": binary_content_identity,
            "program_identity": program_key,
            "language_id": language_id,
            "compiler_spec_id": compiler_spec_id,
            "function_entry": entry,
            "function_body_ranges": ranges,
            "decompiler_contract_version": DECOMPILER_CONTRACT_VERSION,
        }
        return cls(
            binary_content_identity, program_key, language_id, compiler_spec_id,
            entry, ranges, authority_digest(payload), _factory_token=_TARGET_TOKEN,
        )

    @classmethod
    def _from_ghidra(
        cls, program: Any, function: Any, *, binary_content_identity: str
    ) -> "FunctionDecompilationTarget":
        language = _call_noarg(program, "getLanguageID")
        compiler = _call_noarg(program, "getCompilerSpec")
        language_id = str(language) if language is not None else ""
        compiler_id_obj = _call_noarg(compiler, "getCompilerSpecID")
        compiler_id = str(compiler_id_obj) if compiler_id_obj is not None else ""
        executable_format = _call_noarg(program, "getExecutableFormat")
        if type(executable_format) is not str or not executable_format:
            raise ValueError("Ghidra executable format identity is unavailable")
        image_base = _call_noarg(program, "getImageBase")
        program_identity = (
            "ghidra_program_v1",
            executable_format,
            _address_identity(image_base),
        )
        entry = _address_identity(_call_noarg(function, "getEntryPoint"))
        body = _call_noarg(function, "getBody")
        ranges = []
        address_ranges = _call_noarg(body, "getAddressRanges") if body is not None else None
        if address_ranges is not None:
            iterator = iter(address_ranges)
            for item in iterator:
                ranges.append((
                    _address_identity(_call_noarg(item, "getMinAddress")),
                    _address_identity(_call_noarg(item, "getMaxAddress")),
                ))
        if not ranges and body is not None:
            minimum = _call_noarg(body, "getMinAddress")
            maximum = _call_noarg(body, "getMaxAddress")
            if minimum is not None and maximum is not None:
                ranges.append((_address_identity(minimum), _address_identity(maximum)))
        return cls._issue(
            binary_content_identity=binary_content_identity,
            program_identity=program_identity,
            language_id=language_id,
            compiler_spec_id=compiler_id,
            function_entry=entry,
            function_body_ranges=ranges,
            _factory_token=_TARGET_TOKEN,
        )


@dataclass(frozen=True)
class DecompilationAttemptInputSurface:
    prototype_identity: Any
    calling_convention_identity: Any
    parameter_storage_identities: tuple[Any, ...]
    return_storage_identity: Any
    surface_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _INPUT_SURFACE_TOKEN:
            raise TypeError("decompilation input surface must be factory-issued")

    @classmethod
    def _issue(
        cls, *, prototype_identity: Any, calling_convention_identity: Any,
        parameter_storage_identities: Iterable[Any], return_storage_identity: Any,
        _factory_token: object,
    ) -> "DecompilationAttemptInputSurface":
        if _factory_token is not _INPUT_SURFACE_TOKEN:
            raise TypeError("decompilation input surface issuer is invalid")
        prototype = canonical_value(prototype_identity)
        calling = canonical_value(calling_convention_identity)
        parameters = tuple(canonical_value(item) for item in parameter_storage_identities)
        returned = canonical_value(return_storage_identity)
        payload = {
            "prototype_identity": prototype,
            "calling_convention_identity": calling,
            "parameter_storage_identities": parameters,
            "return_storage_identity": returned,
        }
        return cls(
            prototype, calling, parameters, returned, authority_digest(payload),
            _factory_token=_INPUT_SURFACE_TOKEN,
        )


@dataclass(frozen=True)
class DecompilationAttemptIdentityReceipt:
    attempt_id: str
    target_digest: str
    input_surface_digest: str
    result_occurrence_id: str
    source_contract_id: str
    invocation_ordinal: int
    configured_timeout_seconds: int
    execution_identity_digest: str
    receipt_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _ATTEMPT_IDENTITY_TOKEN:
            raise TypeError(
                "decompilation attempt identity receipt must be factory-issued"
            )

    @classmethod
    def _issue(
        cls, *, target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        result_occurrence_id: str, source_contract_id: str,
        invocation_ordinal: int, configured_timeout_seconds: int,
        execution_identity_digest: str, authority_root_digest: str,
        _factory_token: object,
    ) -> "DecompilationAttemptIdentityReceipt":
        if _factory_token is not _ATTEMPT_IDENTITY_TOKEN:
            raise TypeError("decompilation attempt identity issuer is invalid")
        for value in (
            result_occurrence_id, source_contract_id,
            execution_identity_digest, authority_root_digest,
        ):
            _exact_string("decompilation attempt identity", value)
        if type(invocation_ordinal) is not int or invocation_ordinal <= 0:
            raise TypeError("decompilation attempt ordinal is invalid")
        if (
            type(configured_timeout_seconds) is not int
            or configured_timeout_seconds <= 0
        ):
            raise TypeError("decompilation attempt timeout is invalid")
        identity_body = {
            "authority_root_digest": authority_root_digest,
            "target_digest": target.target_digest,
            "input_surface_digest": input_surface.surface_digest,
            "result_occurrence_id": result_occurrence_id,
            "source_contract_id": source_contract_id,
            "invocation_ordinal": invocation_ordinal,
            "configured_timeout_seconds": configured_timeout_seconds,
            "execution_identity_digest": execution_identity_digest,
            "attempt_identity_schema": "decompilation-attempt-identity-v1",
        }
        attempt_id = (
            "decompile-attempt-" + authority_digest(identity_body)[:40]
        )
        payload = {**identity_body, "attempt_id": attempt_id}
        return cls(
            attempt_id,
            target.target_digest,
            input_surface.surface_digest,
            result_occurrence_id,
            source_contract_id,
            invocation_ordinal,
            configured_timeout_seconds,
            execution_identity_digest,
            authority_digest(payload),
            _factory_token=_ATTEMPT_IDENTITY_TOKEN,
        )


@dataclass(frozen=True)
class DecompilationInvocationReceipt:
    target_digest: str
    input_surface_digest: str
    result_occurrence_id: str
    proof_requirement_id: str
    invocation_identity: str
    invocation_ordinal: int
    configured_timeout_seconds: int
    execution_identity_digest: str
    receipt_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _INVOCATION_TOKEN:
            raise TypeError("decompilation invocation receipt must be factory-issued")

    @classmethod
    def _issue(
        cls, *, target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        result_occurrence_id: str, proof_requirement_id: str,
        invocation_identity: str, invocation_ordinal: int,
        configured_timeout_seconds: int, execution_identity_digest: str,
        _factory_token: object,
    ) -> "DecompilationInvocationReceipt":
        if _factory_token is not _INVOCATION_TOKEN:
            raise TypeError("decompilation invocation issuer is invalid")
        for value in (result_occurrence_id, proof_requirement_id, invocation_identity, execution_identity_digest):
            _exact_string("decompilation invocation identity", value)
        if type(invocation_ordinal) is not int or invocation_ordinal <= 0:
            raise TypeError("decompilation invocation ordinal is invalid")
        if type(configured_timeout_seconds) is not int or configured_timeout_seconds <= 0:
            raise TypeError("decompilation timeout is invalid")
        payload = {
            "target_digest": target.target_digest,
            "input_surface_digest": input_surface.surface_digest,
            "result_occurrence_id": result_occurrence_id,
            "proof_requirement_id": proof_requirement_id,
            "invocation_identity": invocation_identity,
            "invocation_ordinal": invocation_ordinal,
            "configured_timeout_seconds": configured_timeout_seconds,
            "execution_identity_digest": execution_identity_digest,
            "decompiler_contract_version": DECOMPILER_CONTRACT_VERSION,
        }
        return cls(**{key: payload[key] for key in (
            "target_digest", "input_surface_digest", "result_occurrence_id",
            "proof_requirement_id", "invocation_identity", "invocation_ordinal",
            "configured_timeout_seconds", "execution_identity_digest",
        )}, receipt_digest=authority_digest(payload), _factory_token=_INVOCATION_TOKEN)


@dataclass(frozen=True)
class SealedDecompilationInvocationCensus:
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    execution_identity_digest: str
    invocation_receipt_digests: tuple[str, ...]
    census_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _INVOCATION_CENSUS_TOKEN:
            raise TypeError("decompilation invocation census must be factory-issued")


@dataclass(frozen=True)
class DecompilationAttemptObservation:
    invocation_receipt_digest: str
    target_digest: str
    input_surface_digest: str
    result_occurrence_id: str
    proof_requirement_id: str
    result_handle_digest: str
    completed: bool
    timed_out: bool
    failed_to_start: bool
    cancelled: bool
    result_function_entry: Optional[tuple[Any, ...]]
    disposition: DecompilationDisposition
    observation_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _OBSERVATION_TOKEN:
            raise TypeError("decompilation observation must be factory-issued")

    @classmethod
    def _capture(
        cls, invocation: DecompilationInvocationReceipt, result: Any, *,
        result_handle_digest: str, _factory_token: object,
    ) -> "DecompilationAttemptObservation":
        if _factory_token is not _OBSERVATION_TOKEN:
            raise TypeError("decompilation observation issuer is invalid")
        if type(invocation) is not DecompilationInvocationReceipt:
            raise TypeError("attempt observation requires exact invocation receipt")
        _exact_string("result handle digest", result_handle_digest)
        completed = _call_exact_bool(result, "decompileCompleted")
        timed_out = _call_exact_bool(result, "isTimedOut")
        failed = _call_exact_bool(result, "failedToStart")
        cancelled = _call_exact_bool(result, "isCancelled")
        rows = {
            (True, False, False, False): DecompilationDisposition.COMPLETED,
            (False, True, False, False): DecompilationDisposition.TIMED_OUT,
            (False, False, True, False): DecompilationDisposition.FAILED_TO_START,
            (False, False, False, True): DecompilationDisposition.CANCELLED,
            (False, False, False, False): DecompilationDisposition.ABORTED,
        }
        try:
            disposition = rows[(completed, timed_out, failed, cancelled)]
        except KeyError as exc:
            raise ValueError("contradictory decompiler result flags") from exc
        function = _call_noarg(result, "getFunction")
        result_entry = None
        if function is not None:
            result_entry = _address_identity(_call_noarg(function, "getEntryPoint"))
        if disposition == DecompilationDisposition.COMPLETED and result_entry is None:
            raise ValueError("completed decompiler result lacks function identity")
        payload = {
            "invocation_receipt_digest": invocation.receipt_digest,
            "target_digest": invocation.target_digest,
            "input_surface_digest": invocation.input_surface_digest,
            "result_occurrence_id": invocation.result_occurrence_id,
            "proof_requirement_id": invocation.proof_requirement_id,
            "result_handle_digest": result_handle_digest,
            "completed": completed,
            "timed_out": timed_out,
            "failed_to_start": failed,
            "cancelled": cancelled,
            "result_function_entry": result_entry,
            "disposition": disposition.value,
        }
        return cls(
            invocation.receipt_digest, invocation.target_digest,
            invocation.input_surface_digest, invocation.result_occurrence_id,
            invocation.proof_requirement_id, result_handle_digest,
            completed, timed_out, failed, cancelled,
            result_entry, disposition, authority_digest(payload),
            _factory_token=_OBSERVATION_TOKEN,
        )


def completed_result_structural_identity(
    *, target: FunctionDecompilationTarget,
    input_surface: DecompilationAttemptInputSurface,
    invocation: DecompilationInvocationReceipt,
    observation: DecompilationAttemptObservation,
) -> str:
    if observation.disposition != DecompilationDisposition.COMPLETED:
        raise ValueError("noncompleted result has no completed structural identity")
    if observation.invocation_receipt_digest != invocation.receipt_digest:
        raise ValueError("observation/invocation join differs")
    if (
        observation.target_digest != target.target_digest
        or observation.input_surface_digest != input_surface.surface_digest
        or observation.result_occurrence_id != invocation.result_occurrence_id
        or observation.proof_requirement_id != invocation.proof_requirement_id
    ):
        raise ValueError("observation semantic assignment differs")
    if observation.result_function_entry != target.function_entry:
        raise ValueError("decompiler result function differs from target")
    if invocation.target_digest != target.target_digest:
        raise ValueError("invocation target differs")
    if invocation.input_surface_digest != input_surface.surface_digest:
        raise ValueError("invocation input surface differs")
    return authority_digest({
        "attempt_observation_digest": observation.observation_digest,
        "target_digest": target.target_digest,
        "input_surface_digest": input_surface.surface_digest,
        "result_function_entry": observation.result_function_entry,
        "decompiler_contract_version": DECOMPILER_CONTRACT_VERSION,
    })


@dataclass(frozen=True)
class DecompilationAttemptReceipt:
    invocation_receipt_digest: str
    observation_digest: str
    target_digest: str
    input_surface_digest: str
    result_occurrence_id: str
    proof_requirement_id: str
    result_handle_digest: str
    disposition: DecompilationDisposition
    completed_result_identity: Optional[str]
    receipt_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _ATTEMPT_TOKEN:
            raise TypeError("decompilation attempt receipt must be factory-issued")

    @classmethod
    def _issue(
        cls, *, invocation: DecompilationInvocationReceipt,
        observation: DecompilationAttemptObservation,
        target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        _factory_token: object,
    ) -> "DecompilationAttemptReceipt":
        if _factory_token is not _ATTEMPT_TOKEN:
            raise TypeError("decompilation attempt issuer is invalid")
        if observation.invocation_receipt_digest != invocation.receipt_digest:
            raise ValueError("observation belongs to a different invocation")
        expected_assignment = (
            target.target_digest,
            input_surface.surface_digest,
            invocation.result_occurrence_id,
            invocation.proof_requirement_id,
        )
        if (
            invocation.target_digest,
            invocation.input_surface_digest,
            observation.result_occurrence_id,
            observation.proof_requirement_id,
        ) != expected_assignment or (
            observation.target_digest,
            observation.input_surface_digest,
            observation.result_occurrence_id,
            observation.proof_requirement_id,
        ) != expected_assignment:
            raise ValueError("attempt target/input/result/Q assignment differs")
        completed_identity = None
        if observation.disposition == DecompilationDisposition.COMPLETED:
            completed_identity = completed_result_structural_identity(
                target=target, input_surface=input_surface,
                invocation=invocation, observation=observation,
            )
        payload = {
            "invocation_receipt_digest": invocation.receipt_digest,
            "observation_digest": observation.observation_digest,
            "target_digest": target.target_digest,
            "input_surface_digest": input_surface.surface_digest,
            "result_occurrence_id": invocation.result_occurrence_id,
            "proof_requirement_id": invocation.proof_requirement_id,
            "result_handle_digest": observation.result_handle_digest,
            "disposition": observation.disposition.value,
            "completed_result_identity": completed_identity,
        }
        return cls(
            invocation.receipt_digest, observation.observation_digest,
            target.target_digest, input_surface.surface_digest,
            invocation.result_occurrence_id, invocation.proof_requirement_id,
            observation.result_handle_digest,
            observation.disposition, completed_identity, authority_digest(payload),
            _factory_token=_ATTEMPT_TOKEN,
        )


@dataclass(frozen=True)
class DecompilationArtifactReceipt:
    target_digest: str
    input_surface_digest: str
    result_occurrence_id: str
    proof_requirement_id: str
    result_handle_digest: str
    attempt_receipt_digest: str
    completed_result_identity: str
    source_snapshot_fingerprint: str
    artifact_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _DECOMP_ARTIFACT_TOKEN:
            raise TypeError("decompilation artifact receipt must be factory-issued")

    @classmethod
    def _issue(
        cls, *, target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        invocation: DecompilationInvocationReceipt,
        observation: DecompilationAttemptObservation,
        attempt: DecompilationAttemptReceipt,
        source_snapshot_fingerprint: str,
        _factory_token: object,
    ) -> "DecompilationArtifactReceipt":
        if _factory_token is not _DECOMP_ARTIFACT_TOKEN:
            raise TypeError("decompilation artifact issuer is invalid")
        _exact_string("source snapshot", source_snapshot_fingerprint)
        if attempt.disposition != DecompilationDisposition.COMPLETED or not attempt.completed_result_identity:
            raise ValueError("decompilation artifact requires completed attempt")
        expected = (
            target.target_digest,
            input_surface.surface_digest,
            invocation.result_occurrence_id,
            invocation.proof_requirement_id,
            observation.result_handle_digest,
            invocation.receipt_digest,
            observation.observation_digest,
        )
        observed = (
            attempt.target_digest,
            attempt.input_surface_digest,
            attempt.result_occurrence_id,
            attempt.proof_requirement_id,
            attempt.result_handle_digest,
            attempt.invocation_receipt_digest,
            attempt.observation_digest,
        )
        if expected != observed or (
            observation.target_digest,
            observation.input_surface_digest,
            observation.result_occurrence_id,
            observation.proof_requirement_id,
            observation.invocation_receipt_digest,
        ) != expected[:4] + (invocation.receipt_digest,):
            raise ValueError("decompilation artifact dependency join differs")
        payload = {
            "target_digest": target.target_digest,
            "input_surface_digest": input_surface.surface_digest,
            "result_occurrence_id": invocation.result_occurrence_id,
            "proof_requirement_id": invocation.proof_requirement_id,
            "result_handle_digest": observation.result_handle_digest,
            "attempt_receipt_digest": attempt.receipt_digest,
            "completed_result_identity": attempt.completed_result_identity,
            "source_snapshot_fingerprint": source_snapshot_fingerprint,
            "decompiler_contract_version": DECOMPILER_CONTRACT_VERSION,
        }
        return cls(
            target.target_digest, input_surface.surface_digest,
            invocation.result_occurrence_id, invocation.proof_requirement_id,
            observation.result_handle_digest, attempt.receipt_digest,
            attempt.completed_result_identity, source_snapshot_fingerprint,
            authority_digest(payload), _factory_token=_DECOMP_ARTIFACT_TOKEN,
        )


@dataclass(frozen=True)
class HighFunctionObservationCapability:
    decompilation_artifact_digest: str
    target_digest: str
    input_surface_digest: str
    result_occurrence_id: str
    dependency_decompilation_requirement_id: str
    proof_requirement_id: str
    result_handle_digest: str
    high_function: Any = field(repr=False, compare=False)
    capability_digest: str = ""
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _HIGH_CAPABILITY_TOKEN:
            raise TypeError("HighFunction capability must be factory-issued")

    @classmethod
    def _issue(
        cls, *, high: Any, artifact: DecompilationArtifactReceipt,
        target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        proof_requirement_id: str,
        _factory_token: object,
    ) -> "HighFunctionObservationCapability":
        if _factory_token is not _HIGH_CAPABILITY_TOKEN:
            raise TypeError("HighFunction capability issuer is invalid")
        if high is None:
            raise ValueError("null HighFunction cannot form a capability")
        _exact_string("HighFunction proof requirement", proof_requirement_id)
        if proof_requirement_id == artifact.proof_requirement_id:
            raise ValueError("HighFunction Q must differ from decompilation dependency Q")
        if (
            artifact.target_digest != target.target_digest
            or artifact.input_surface_digest != input_surface.surface_digest
        ):
            raise ValueError("HighFunction target/input differs from artifact")
        digest = authority_digest({
            "decompilation_artifact_digest": artifact.artifact_digest,
            "target_digest": target.target_digest,
            "input_surface_digest": input_surface.surface_digest,
            "result_occurrence_id": artifact.result_occurrence_id,
            "dependency_decompilation_requirement_id": artifact.proof_requirement_id,
            "proof_requirement_id": proof_requirement_id,
            "result_handle_digest": artifact.result_handle_digest,
            "capability_schema": "one-shot-high-function-v1",
        })
        return cls(
            artifact.artifact_digest, target.target_digest,
            input_surface.surface_digest, artifact.result_occurrence_id,
            artifact.proof_requirement_id, proof_requirement_id,
            artifact.result_handle_digest,
            high, digest,
            _factory_token=_HIGH_CAPABILITY_TOKEN,
        )


def _varnode_projection(varnode: Any, *, allow_none: bool = False) -> Any:
    if varnode is None:
        if allow_none:
            return None
        raise ValueError("mandatory P-code input varnode is unavailable")
    address = _call_noarg(varnode, "getAddress")
    address_identity = _address_identity(address) if address is not None else None
    high = _call_noarg(varnode, "getHigh")
    storage = _call_noarg(high, "getStorage") if high is not None else None
    size = _ghidra_integer(
        "varnode size", _call_noarg(varnode, "getSize"), nonnegative=True
    )
    flags = tuple(
        _call_exact_bool(varnode, name)
        for name in ("isConstant", "isRegister", "isUnique", "isAddress", "isAddrTied")
    )
    return (
        address_identity,
        size,
        *flags,
        _call_noarg(high, "getName") if high is not None else None,
        _storage_projection(storage),
    )


def _storage_projection(storage: Any) -> Any:
    if storage is None:
        return None
    varnodes = _call_noarg(storage, "getVarnodes")
    if varnodes is None:
        raise ValueError("nonnull storage lacks complete varnode census")
    return tuple(_varnode_projection_without_high(item) for item in varnodes)


def _varnode_projection_without_high(varnode: Any) -> Any:
    if varnode is None:
        raise ValueError("mandatory storage varnode is unavailable")
    address = _call_noarg(varnode, "getAddress")
    size = _ghidra_integer(
        "storage varnode size", _call_noarg(varnode, "getSize"),
        nonnegative=True,
    )
    flags = tuple(
        _call_exact_bool(varnode, name)
        for name in ("isConstant", "isRegister", "isUnique", "isAddress", "isAddrTied")
    )
    return (
        _address_identity(address) if address is not None else None,
        size,
        *flags,
    )


def _prototype_projection(prototype: Any) -> Any:
    if prototype is None:
        return None
    model_name = _call_noarg(prototype, "getModelName")
    return_type = _call_noarg(prototype, "getReturnType")
    return_storage = _call_noarg(prototype, "getReturnStorage")
    parameter_count = _ghidra_integer(
        "prototype parameter count", _call_noarg(prototype, "getNumParams"),
        nonnegative=True,
    )
    parameters = []
    get_param = getattr(prototype, "getParam", None)
    if parameter_count and not callable(get_param):
        raise ValueError("prototype parameter census is incomplete")
    for index in range(parameter_count):
        parameter = get_param(index)
        parameters.append((
            index,
            _call_noarg(parameter, "getName"),
            _call_noarg(parameter, "getDataType") and (
                _call_noarg(_call_noarg(parameter, "getDataType"), "getName"),
                _ghidra_integer(
                    "parameter data-type length",
                    _call_noarg(_call_noarg(parameter, "getDataType"), "getLength"),
                ),
            ),
            _storage_projection(_call_noarg(parameter, "getStorage")),
        ))
    return canonical_value((
        "prototype_projection_v1",
        model_name,
        (
            _call_noarg(return_type, "getName") if return_type is not None else None,
            _ghidra_integer(
                "return data-type length", _call_noarg(return_type, "getLength")
            ) if return_type is not None else None,
        ),
        _storage_projection(return_storage),
        tuple(parameters),
    ))


def canonical_high_function_projection(
    high_function: Any, *, expected_target: Optional[FunctionDecompilationTarget] = None,
) -> tuple[Any, ...]:
    function = _call_noarg(high_function, "getFunction")
    entry = _address_identity(_call_noarg(function, "getEntryPoint"))
    if expected_target is not None and entry != expected_target.function_entry:
        raise ValueError("HighFunction function entry differs from target")
    prototype = _call_noarg(high_function, "getFunctionPrototype")
    if prototype is None:
        raise ValueError("HighFunction prototype identity is unavailable")
    prototype_identity = _prototype_projection(prototype)
    blocks_source = _call_noarg(high_function, "getBasicBlocks")
    if blocks_source is None:
        raise ValueError("HighFunction lacks basic-block census")
    blocks = []
    seen_block_keys = set()
    seen_op_keys = set()
    total_ops = 0
    total_inputs = 0
    for block in blocks_source:
        block_index = _ghidra_integer(
            "HighFunction block index", _call_noarg(block, "getIndex"),
            nonnegative=True,
        )
        start = _address_identity(_call_noarg(block, "getStart"))
        block_key = (block_index, start)
        if block_key in seen_block_keys:
            raise ValueError("duplicate HighFunction block identity")
        seen_block_keys.add(block_key)
        outgoing = []
        out_size = _ghidra_integer(
            "HighFunction successor count", _call_noarg(block, "getOutSize"),
            nonnegative=True,
        )
        for index in range(out_size):
            successor = getattr(block, "getOut", lambda _index: None)(index)
            successor_index = _ghidra_integer(
                "HighFunction successor index",
                _call_noarg(successor, "getIndex"), nonnegative=True,
            )
            outgoing.append((
                successor_index,
                _address_identity(_call_noarg(successor, "getStart")),
            ))
        if len(outgoing) != len(set(outgoing)):
            raise ValueError("duplicate HighFunction CFG edge")
        ops_source = _call_noarg(block, "getIterator")
        if ops_source is None:
            raise ValueError("HighFunction block operation census is unavailable")
        ops = []
        for operation in ops_source:
            sequence = _call_noarg(operation, "getSeqnum")
            seq_target = _address_identity(_call_noarg(sequence, "getTarget"))
            seq_time = _ghidra_integer(
                "P-code sequence time", _call_noarg(sequence, "getTime"),
                nonnegative=True,
            )
            op_key = (block_key, seq_target, seq_time)
            if op_key in seen_op_keys:
                raise ValueError("duplicate HighFunction operation identity")
            seen_op_keys.add(op_key)
            input_count = _ghidra_integer(
                "P-code input count", _call_noarg(operation, "getNumInputs"),
                nonnegative=True,
            )
            inputs = tuple(
                _varnode_projection(getattr(operation, "getInput")(index))
                for index in range(input_count)
            )
            opcode = _ghidra_integer(
                "P-code opcode", _call_noarg(operation, "getOpcode"),
                nonnegative=True,
            )
            mnemonic = _call_noarg(operation, "getMnemonic")
            if type(mnemonic) is not str or not mnemonic:
                raise TypeError("P-code opcode identity is invalid")
            ops.append((
                seq_target,
                seq_time,
                opcode,
                mnemonic,
                _varnode_projection(
                    _call_noarg(operation, "getOutput"), allow_none=True
                ),
                inputs,
            ))
            total_ops += 1
            total_inputs += input_count
        ops.sort(key=lambda item: (item[0], item[1]))
        blocks.append((block_key, tuple(sorted(outgoing)), tuple(ops)))
    blocks.sort(key=lambda item: item[0])
    block_keys = frozenset(item[0] for item in blocks)
    for _block_key, outgoing, _ops in blocks:
        if any(edge not in block_keys for edge in outgoing):
            raise ValueError("HighFunction CFG successor is outside block census")
    return canonical_value((
        "high_function_ir_projection_v1",
        entry,
        prototype_identity,
        tuple(blocks),
        ("coverage", len(blocks), total_ops, total_inputs),
    ))


@dataclass(frozen=True)
class HighFunctionIRArtifact:
    target_digest: str
    input_surface_digest: str
    result_occurrence_id: str
    dependency_decompilation_requirement_id: str
    proof_requirement_id: str
    decompilation_artifact_digest: str
    capability_digest: str
    ir_projection: tuple[Any, ...]
    ir_projection_digest: str
    artifact_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _IR_ARTIFACT_TOKEN:
            raise TypeError("HighFunction IR artifact must be factory-issued")

    @classmethod
    def _issue(
        cls, *, capability: HighFunctionObservationCapability,
        decompilation_artifact: DecompilationArtifactReceipt,
        target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        _factory_token: object,
    ) -> "HighFunctionIRArtifact":
        if _factory_token is not _IR_ARTIFACT_TOKEN:
            raise TypeError("IR artifact issuer is invalid")
        if type(capability) is not HighFunctionObservationCapability:
            raise TypeError("IR extraction requires exact HighFunction capability")
        if (
            capability.decompilation_artifact_digest != decompilation_artifact.artifact_digest
            or capability.target_digest != target.target_digest
            or capability.input_surface_digest != input_surface.surface_digest
            or decompilation_artifact.target_digest != target.target_digest
            or decompilation_artifact.input_surface_digest != input_surface.surface_digest
            or capability.result_occurrence_id != decompilation_artifact.result_occurrence_id
            or capability.dependency_decompilation_requirement_id != decompilation_artifact.proof_requirement_id
            or capability.result_handle_digest != decompilation_artifact.result_handle_digest
        ):
            raise ValueError("IR artifact dependency join differs")
        projection = canonical_high_function_projection(
            capability.high_function, expected_target=target,
        )
        projection_digest = authority_digest({"ir_projection": projection})
        payload = {
            "target_digest": target.target_digest,
            "input_surface_digest": input_surface.surface_digest,
            "result_occurrence_id": decompilation_artifact.result_occurrence_id,
            "dependency_decompilation_requirement_id": decompilation_artifact.proof_requirement_id,
            "proof_requirement_id": capability.proof_requirement_id,
            "decompilation_artifact_digest": decompilation_artifact.artifact_digest,
            "capability_digest": capability.capability_digest,
            "ir_projection_digest": projection_digest,
            "ir_extraction_schema_version": IR_EXTRACTION_SCHEMA_VERSION,
        }
        return cls(
            target.target_digest, input_surface.surface_digest,
            decompilation_artifact.result_occurrence_id,
            decompilation_artifact.proof_requirement_id,
            capability.proof_requirement_id,
            decompilation_artifact.artifact_digest,
            capability.capability_digest, projection, projection_digest,
            authority_digest(payload), _factory_token=_IR_ARTIFACT_TOKEN,
        )


@dataclass(frozen=True)
class OperationalErrorArtifact:
    error_kind: str
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    catch_site_contract_id: str
    target_digest: Optional[str]
    exception_class_identity: Optional[str]
    attempt_receipt_digest: Optional[str]
    lookup_outcome_digest: Optional[str]
    artifact_digest: str
    invocation_receipt_digest: Optional[str] = None
    input_surface_digest: Optional[str] = None
    operational_authority_root_digest: Optional[str] = None
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _ERROR_ARTIFACT_TOKEN:
            raise TypeError("operational error artifact must be factory-issued")

    @classmethod
    def _issue(
        cls, *, error_kind: str, result_occurrence_id: str,
        source_snapshot_fingerprint: str, catch_site_contract_id: str,
        target: Optional[FunctionDecompilationTarget] = None,
        exception_class_identity: Optional[str] = None,
        attempt: Optional[DecompilationAttemptReceipt] = None,
        lookup_outcome: Optional["FunctionLookupOutcome"] = None,
        invocation: Optional[DecompilationInvocationReceipt] = None,
        input_surface: Optional[DecompilationAttemptInputSurface] = None,
        operational_authority_root_digest: Optional[str] = None,
        _factory_token: object,
    ) -> "OperationalErrorArtifact":
        if _factory_token is not _ERROR_ARTIFACT_TOKEN:
            raise TypeError("operational error artifact issuer is invalid")
        if error_kind not in SEALED_OPERATIONAL_ERROR_KINDS:
            raise ValueError("operational error kind is not sealed")
        for value in (result_occurrence_id, source_snapshot_fingerprint, catch_site_contract_id):
            _exact_string("operational error identity", value)
        if exception_class_identity is not None:
            _exact_string("exception class identity", exception_class_identity)
        expected_attempt = {
            "decompiler_failed_to_start": DecompilationDisposition.FAILED_TO_START,
            "decompiler_cancelled": DecompilationDisposition.CANCELLED,
            "decompiler_aborted": DecompilationDisposition.ABORTED,
        }.get(error_kind)
        if expected_attempt is not None:
            if type(attempt) is not DecompilationAttemptReceipt or attempt.disposition != expected_attempt:
                raise ValueError("decompiler error kind requires matching attempt disposition")
            if target is None or attempt.target_digest != target.target_digest:
                raise ValueError("decompiler error target differs from attempt")
            if attempt.result_occurrence_id != result_occurrence_id:
                raise ValueError("decompiler error result occurrence differs")
        elif attempt is not None:
            raise ValueError("non-decompiler error cannot bind attempt receipt")
        if (invocation is None) != (input_surface is None):
            raise ValueError("operational error invocation/input binding is partial")
        if invocation is not None:
            if (
                target is None
                or invocation.target_digest != target.target_digest
                or invocation.input_surface_digest != input_surface.surface_digest
                or invocation.result_occurrence_id != result_occurrence_id
            ):
                raise ValueError("operational error invocation assignment differs")
            _exact_string(
                "operational authority root", operational_authority_root_digest
            )
        elif operational_authority_root_digest is not None:
            raise ValueError("occurrence-scoped error cannot claim invocation authority root")
        if error_kind == "function_lookup_miss":
            if type(lookup_outcome) is not FunctionLookupOutcome or lookup_outcome.status != FunctionLookupStatus.MISSING:
                raise ValueError("lookup miss error requires exact missing outcome")
        elif error_kind == "function_lookup_exception":
            if type(lookup_outcome) is not FunctionLookupOutcome or lookup_outcome.status != FunctionLookupStatus.ERROR:
                raise ValueError("lookup exception error requires exact error outcome")
            if exception_class_identity != lookup_outcome.exception_class_identity:
                raise ValueError("lookup exception class differs from outcome")
        elif lookup_outcome is not None:
            raise ValueError("non-lookup error cannot bind lookup outcome")
        if error_kind in {"analysis_exception", "strategy_exception"} and not exception_class_identity:
            raise ValueError("exception error requires exception class identity")
        payload = {
            "error_kind": error_kind,
            "result_occurrence_id": result_occurrence_id,
            "source_snapshot_fingerprint": source_snapshot_fingerprint,
            "catch_site_contract_id": catch_site_contract_id,
            "target_digest": target.target_digest if target else None,
            "exception_class_identity": exception_class_identity,
            "attempt_receipt_digest": attempt.receipt_digest if attempt else None,
            "lookup_outcome_digest": lookup_outcome.outcome_digest if lookup_outcome else None,
            "invocation_receipt_digest": (
                invocation.receipt_digest if invocation is not None else None
            ),
            "input_surface_digest": (
                input_surface.surface_digest if input_surface is not None else None
            ),
            "operational_authority_root_digest": operational_authority_root_digest,
            "producer_version": "operational-error-factory-v1",
        }
        return cls(
            error_kind, result_occurrence_id, source_snapshot_fingerprint,
            catch_site_contract_id, payload["target_digest"],
            exception_class_identity, payload["attempt_receipt_digest"],
            payload["lookup_outcome_digest"], authority_digest(payload),
            payload["invocation_receipt_digest"], payload["input_surface_digest"],
            payload["operational_authority_root_digest"],
            _factory_token=_ERROR_ARTIFACT_TOKEN,
        )

@dataclass(frozen=True)
class FunctionManagerCensusReceipt:
    query_identity: Any
    program_identity: Any
    source_snapshot_fingerprint: str
    program_seed_digest: str
    function_target_digests: tuple[str, ...]
    function_lookup_rows: tuple[tuple[Any, str], ...]
    iteration_completed: bool
    receipt_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _LOOKUP_OUTCOME_TOKEN:
            raise TypeError("function census receipt must be factory-issued")


@dataclass(frozen=True)
class FunctionLookupOutcome:
    status: FunctionLookupStatus
    target: Optional[FunctionDecompilationTarget]
    function_object: Any = field(default=None, repr=False, compare=False)
    census_digest: Optional[str] = None
    catch_site_contract_id: Optional[str] = None
    exception_class_identity: Optional[str] = None
    query_identity: Any = None
    program_identity: Any = None
    source_snapshot_fingerprint: Optional[str] = None
    program_seed_digest: Optional[str] = None
    outcome_digest: str = ""
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _LOOKUP_OUTCOME_TOKEN:
            raise TypeError("function lookup outcome must be factory-issued")

    @classmethod
    def _found(
        cls, function_object: Any, target: FunctionDecompilationTarget, *,
        query_identity: Any, program_identity: Any,
        source_snapshot_fingerprint: str,
        program_seed_digest: Optional[str], _factory_token: object,
    ) -> "FunctionLookupOutcome":
        if _factory_token is not _LOOKUP_OUTCOME_TOKEN:
            raise TypeError("function lookup outcome issuer is invalid")
        if function_object is None or type(target) is not FunctionDecompilationTarget:
            raise TypeError("FOUND lookup requires function object and typed target")
        if _address_identity(_call_noarg(function_object, "getEntryPoint")) != target.function_entry:
            raise ValueError("FOUND function object differs from target")
        snapshot = _exact_string("lookup source snapshot", source_snapshot_fingerprint)
        query = canonical_value(query_identity)
        program = canonical_value(program_identity)
        lookup_keys = _function_lookup_keys(function_object)
        if query not in lookup_keys:
            raise ValueError("FOUND function object does not match lookup query")
        digest = authority_digest({
            "status": "FOUND", "target_digest": target.target_digest,
            "query_identity": query, "program_identity": program,
            "source_snapshot_fingerprint": snapshot,
            "matched_lookup_key": query,
            "program_seed_digest": program_seed_digest,
        })
        return cls(
            FunctionLookupStatus.FOUND, target, function_object,
            query_identity=query, program_identity=program,
            source_snapshot_fingerprint=snapshot,
            program_seed_digest=program_seed_digest, outcome_digest=digest,
            _factory_token=_LOOKUP_OUTCOME_TOKEN,
        )

    @classmethod
    def _missing(
        cls, *, census_receipt: FunctionManagerCensusReceipt,
        _factory_token: object,
    ) -> "FunctionLookupOutcome":
        if _factory_token is not _LOOKUP_OUTCOME_TOKEN or type(census_receipt) is not FunctionManagerCensusReceipt:
            raise TypeError("lookup miss requires factory census receipt")
        if not census_receipt.iteration_completed:
            raise ValueError("lookup miss requires completed function census")
        if any(
            canonical_value(key) == canonical_value(census_receipt.query_identity)
            for key, _target_digest in census_receipt.function_lookup_rows
        ):
            raise ValueError("lookup miss census contains an exact query match")
        digest = authority_digest({
            "status": "MISSING",
            "census_receipt_digest": census_receipt.receipt_digest,
            "program_seed_digest": census_receipt.program_seed_digest,
        })
        return cls(
            FunctionLookupStatus.MISSING, None,
            census_digest=census_receipt.receipt_digest,
            query_identity=census_receipt.query_identity,
            program_identity=census_receipt.program_identity,
            source_snapshot_fingerprint=census_receipt.source_snapshot_fingerprint,
            program_seed_digest=census_receipt.program_seed_digest,
            outcome_digest=digest, _factory_token=_LOOKUP_OUTCOME_TOKEN,
        )

    @classmethod
    def _error(
        cls, *, catch_site_contract_id: str, exception: BaseException,
        query_identity: Any, program_identity: Any,
        source_snapshot_fingerprint: str, _factory_token: object,
    ) -> "FunctionLookupOutcome":
        if _factory_token is not _LOOKUP_OUTCOME_TOKEN:
            raise TypeError("function lookup error issuer is invalid")
        _exact_string("lookup catch site", catch_site_contract_id)
        snapshot = _exact_string("lookup source snapshot", source_snapshot_fingerprint)
        query = canonical_value(query_identity)
        program = canonical_value(program_identity)
        exception_identity = type(exception).__module__ + "." + type(exception).__qualname__
        digest = authority_digest({
            "status": "ERROR", "catch_site_contract_id": catch_site_contract_id,
            "exception_class_identity": exception_identity,
            "query_identity": query, "program_identity": program,
            "source_snapshot_fingerprint": snapshot,
        })
        return cls(
            FunctionLookupStatus.ERROR, None,
            catch_site_contract_id=catch_site_contract_id,
            exception_class_identity=exception_identity,
            query_identity=query, program_identity=program,
            source_snapshot_fingerprint=snapshot, outcome_digest=digest,
            _factory_token=_LOOKUP_OUTCOME_TOKEN,
        )


class OperationalExtractionAuthorityFactory:
    """Session-owned issuance and exact-object membership authority."""

    def __init__(
        self, *, result_occurrence_id: str, source_snapshot_fingerprint: str,
        execution_identity_digest: str, allow_fixture_inputs: bool = False,
    ) -> None:
        self.result_occurrence_id = _exact_string(
            "factory result occurrence", result_occurrence_id
        )
        self.source_snapshot_fingerprint = _exact_string(
            "factory source snapshot", source_snapshot_fingerprint
        )
        self.execution_identity_digest = _exact_string(
            "factory execution identity", execution_identity_digest
        )
        self.authority_root_digest = authority_digest({
            "result_occurrence_id": self.result_occurrence_id,
            "source_snapshot_fingerprint": self.source_snapshot_fingerprint,
            "execution_identity_digest": self.execution_identity_digest,
            "factory_nonce": secrets.token_hex(32),
            "authority_root_schema": "operational-authority-root-v1",
        })
        if type(allow_fixture_inputs) is not bool:
            raise TypeError("fixture-input policy must be exact bool")
        self._allow_fixture_inputs = allow_fixture_inputs
        self._issuance_lock = RLock()
        self._next_decompilation_attempt_ordinal = 1
        self._targets: dict[int, FunctionDecompilationTarget] = {}
        self._program_seeds: dict[int, GhidraProgramAuthoritySeed] = {}
        self._surfaces: dict[int, DecompilationAttemptInputSurface] = {}
        self._attempt_identities: dict[
            str, DecompilationAttemptIdentityReceipt
        ] = {}
        self._invocations: dict[str, DecompilationInvocationReceipt] = {}
        self._invocation_censuses: dict[int, SealedDecompilationInvocationCensus] = {}
        self._observations: dict[str, DecompilationAttemptObservation] = {}
        self._results: dict[str, Any] = {}
        self._attempts: dict[str, DecompilationAttemptReceipt] = {}
        self._artifacts: dict[str, DecompilationArtifactReceipt] = {}
        self._high_consumed: set[str] = set()
        self._capabilities: dict[int, HighFunctionObservationCapability] = {}
        self._ir_consumed: set[int] = set()
        self._ir_artifacts: dict[int, HighFunctionIRArtifact] = {}
        self._censuses: dict[int, FunctionManagerCensusReceipt] = {}
        self._lookups: dict[int, FunctionLookupOutcome] = {}
        self._errors: dict[int, OperationalErrorArtifact] = {}

    @classmethod
    def for_testing(cls) -> "OperationalExtractionAuthorityFactory":
        return cls(
            result_occurrence_id="result-1",
            source_snapshot_fingerprint="source-snapshot",
            execution_identity_digest="execution-1",
            allow_fixture_inputs=True,
        )

    def target_from_ghidra(
        self, program_seed: GhidraProgramAuthoritySeed, function: Any,
    ) -> FunctionDecompilationTarget:
        if self._program_seeds.get(id(program_seed)) is not program_seed:
            raise ValueError("program seed is not exact factory membership")
        if _call_noarg(function, "getProgram") != program_seed.program:
            raise ValueError("function is not owned by the seeded program")
        target = FunctionDecompilationTarget._from_ghidra(
            program_seed.program, function,
            binary_content_identity=program_seed.binary_content_identity,
        )
        if target.program_identity != program_seed.program_identity:
            raise ValueError("function target program identity differs from seed")
        self._targets[id(target)] = target
        return target

    def issue_program_seed(
        self, program: Any, *, binary_content_identity: str,
    ) -> GhidraProgramAuthoritySeed:
        _exact_string("program binary content identity", binary_content_identity)
        function_manager = _call_noarg(program, "getFunctionManager")
        if function_manager is None:
            raise ValueError("program FunctionManager authority is unavailable")
        executable_format = _call_noarg(program, "getExecutableFormat")
        language = _call_noarg(program, "getLanguageID")
        compiler = _call_noarg(program, "getCompilerSpec")
        compiler_id = _call_noarg(compiler, "getCompilerSpecID")
        image_base = _call_noarg(program, "getImageBase")
        if (
            type(executable_format) is not str or not executable_format
            or language is None or compiler_id is None or image_base is None
        ):
            raise ValueError("program identity authority is incomplete")
        program_identity = canonical_value((
            "ghidra_program_v1", executable_format,
            _address_identity(image_base),
        ))
        seed_digest = authority_digest({
            "binary_content_identity": binary_content_identity,
            "program_identity": program_identity,
            "language_id": str(language),
            "compiler_spec_id": str(compiler_id),
            "program_seed_schema": "ghidra-program-seed-v1",
        })
        seed = GhidraProgramAuthoritySeed(
            binary_content_identity, tuple(program_identity), program,
            function_manager, seed_digest, _factory_token=_PROGRAM_SEED_TOKEN,
        )
        self._program_seeds[id(seed)] = seed
        return seed

    def target_from_fixture(self, **kwargs: Any) -> FunctionDecompilationTarget:
        if not self._allow_fixture_inputs:
            raise ValueError("fixture target factory is disabled in production")
        target = FunctionDecompilationTarget._issue(
            **kwargs, _factory_token=_TARGET_TOKEN,
        )
        self._targets[id(target)] = target
        return target

    def input_surface_from_fixture(
        self, **kwargs: Any
    ) -> DecompilationAttemptInputSurface:
        if not self._allow_fixture_inputs:
            raise ValueError("fixture input-surface factory is disabled in production")
        surface = DecompilationAttemptInputSurface._issue(
            **kwargs, _factory_token=_INPUT_SURFACE_TOKEN,
        )
        self._surfaces[id(surface)] = surface
        return surface

    def input_surface_from_ghidra(
        self, function: Any
    ) -> DecompilationAttemptInputSurface:
        parameters_source = _call_noarg(function, "getParameters")
        if parameters_source is None:
            raise ValueError("function parameter census is unavailable")
        parameters = tuple(parameters_source)
        calling_convention = _call_noarg(function, "getCallingConventionName")
        if type(calling_convention) is not str or not calling_convention:
            raise ValueError("calling-convention identity is unavailable")
        return_parameter = _call_noarg(function, "getReturn")
        prototype = (
            "function_prototype_surface_v1",
            _data_type_identity(_call_noarg(function, "getReturnType")),
            tuple(
                (
                    index,
                    _data_type_identity(_call_noarg(item, "getDataType")),
                    _variable_storage_identity(item),
                )
                for index, item in enumerate(parameters)
            ),
        )
        surface = DecompilationAttemptInputSurface._issue(
            prototype_identity=prototype,
            calling_convention_identity=calling_convention,
            parameter_storage_identities=tuple(
                _variable_storage_identity(item) for item in parameters
            ),
            return_storage_identity=_variable_storage_identity(return_parameter),
            _factory_token=_INPUT_SURFACE_TOKEN,
        )
        self._surfaces[id(surface)] = surface
        return surface

    def issue_invocation(
        self, *, target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        proof_requirement_id: str, invocation_identity: str,
        invocation_ordinal: int, configured_timeout_seconds: int,
    ) -> DecompilationInvocationReceipt:
        with self._issuance_lock:
            return self._issue_invocation_locked(
                target=target,
                input_surface=input_surface,
                proof_requirement_id=proof_requirement_id,
                invocation_identity=invocation_identity,
                invocation_ordinal=invocation_ordinal,
                configured_timeout_seconds=configured_timeout_seconds,
            )

    def issue_attempt_identity(
        self, *, target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        source_contract_id: str, configured_timeout_seconds: int,
    ) -> DecompilationAttemptIdentityReceipt:
        with self._issuance_lock:
            if (
                self._targets.get(id(target)) is not target
                or self._surfaces.get(id(input_surface)) is not input_surface
            ):
                raise ValueError(
                    "attempt identity target/input was not issued by this factory"
                )
            ordinal = self._next_decompilation_attempt_ordinal
            self._next_decompilation_attempt_ordinal += 1
            receipt = DecompilationAttemptIdentityReceipt._issue(
                target=target,
                input_surface=input_surface,
                result_occurrence_id=self.result_occurrence_id,
                source_contract_id=source_contract_id,
                invocation_ordinal=ordinal,
                configured_timeout_seconds=configured_timeout_seconds,
                execution_identity_digest=self.execution_identity_digest,
                authority_root_digest=self.authority_root_digest,
                _factory_token=_ATTEMPT_IDENTITY_TOKEN,
            )
            if receipt.attempt_id in self._attempt_identities:
                raise ValueError("duplicate decompilation attempt identity issuance")
            self._attempt_identities[receipt.attempt_id] = receipt
            return receipt

    def issue_invocation_for_attempt(
        self, *, target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        attempt_identity: DecompilationAttemptIdentityReceipt,
        proof_requirement_id: str,
    ) -> DecompilationInvocationReceipt:
        with self._issuance_lock:
            if (
                type(attempt_identity) is not DecompilationAttemptIdentityReceipt
                or self._attempt_identities.get(attempt_identity.attempt_id)
                is not attempt_identity
            ):
                raise TypeError(
                    "decompilation attempt identity is not exact factory membership"
                )
            if (
                attempt_identity.target_digest != target.target_digest
                or attempt_identity.input_surface_digest
                != input_surface.surface_digest
                or attempt_identity.result_occurrence_id
                != self.result_occurrence_id
                or attempt_identity.execution_identity_digest
                != self.execution_identity_digest
            ):
                raise ValueError(
                    "decompilation attempt identity surface authority differs"
                )
            return self._issue_invocation_locked(
                target=target,
                input_surface=input_surface,
                proof_requirement_id=proof_requirement_id,
                invocation_identity=attempt_identity.attempt_id,
                invocation_ordinal=attempt_identity.invocation_ordinal,
                configured_timeout_seconds=(
                    attempt_identity.configured_timeout_seconds
                ),
            )

    def validate_attempt_identity_for_signal(
        self, attempt_id: str, target: FunctionDecompilationTarget,
    ) -> DecompilationAttemptIdentityReceipt:
        with self._issuance_lock:
            receipt = self._attempt_identities.get(attempt_id)
            if receipt is None:
                raise ValueError(
                    "decompilation blocker lacks factory-issued attempt identity"
                )
            if (
                self._targets.get(id(target)) is not target
                or receipt.target_digest != target.target_digest
                or receipt.result_occurrence_id != self.result_occurrence_id
                or receipt.execution_identity_digest
                != self.execution_identity_digest
            ):
                raise ValueError(
                    "decompilation blocker attempt identity authority differs"
                )
            return receipt

    def _issue_invocation_locked(
        self, *, target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        proof_requirement_id: str, invocation_identity: str,
        invocation_ordinal: int, configured_timeout_seconds: int,
    ) -> DecompilationInvocationReceipt:
        if (
            self._targets.get(id(target)) is not target
            or self._surfaces.get(id(input_surface)) is not input_surface
        ):
            raise ValueError("invocation target/input was not issued by this factory")
        receipt = DecompilationInvocationReceipt._issue(
            target=target, input_surface=input_surface,
            result_occurrence_id=self.result_occurrence_id,
            proof_requirement_id=proof_requirement_id,
            invocation_identity=invocation_identity,
            invocation_ordinal=invocation_ordinal,
            configured_timeout_seconds=configured_timeout_seconds,
            execution_identity_digest=self.execution_identity_digest,
            _factory_token=_INVOCATION_TOKEN,
        )
        if receipt.receipt_digest in self._invocations:
            raise ValueError("duplicate decompilation invocation issuance")
        self._invocations[receipt.receipt_digest] = receipt
        return receipt

    def validate_invocation_membership(
        self, invocation: DecompilationInvocationReceipt,
    ) -> None:
        if (
            type(invocation) is not DecompilationInvocationReceipt
            or self._invocations.get(invocation.receipt_digest) is not invocation
        ):
            raise TypeError("decompilation invocation is not exact factory membership")
        payload = {
            "target_digest": invocation.target_digest,
            "input_surface_digest": invocation.input_surface_digest,
            "result_occurrence_id": invocation.result_occurrence_id,
            "proof_requirement_id": invocation.proof_requirement_id,
            "invocation_identity": invocation.invocation_identity,
            "invocation_ordinal": invocation.invocation_ordinal,
            "configured_timeout_seconds": invocation.configured_timeout_seconds,
            "execution_identity_digest": invocation.execution_identity_digest,
            "decompiler_contract_version": DECOMPILER_CONTRACT_VERSION,
        }
        if invocation.receipt_digest != authority_digest(payload):
            raise ValueError("decompilation invocation receipt digest mismatch")

    def seal_invocation_census(self) -> SealedDecompilationInvocationCensus:
        for invocation in self._invocations.values():
            self.validate_invocation_membership(invocation)
        digests = tuple(sorted(self._invocations))
        payload = {
            "result_occurrence_id": self.result_occurrence_id,
            "source_snapshot_fingerprint": self.source_snapshot_fingerprint,
            "execution_identity_digest": self.execution_identity_digest,
            "invocation_receipt_digests": digests,
            "census_schema": "decompilation-invocation-census-v1",
        }
        census = SealedDecompilationInvocationCensus(
            self.result_occurrence_id,
            self.source_snapshot_fingerprint,
            self.execution_identity_digest,
            digests,
            authority_digest(payload),
            _factory_token=_INVOCATION_CENSUS_TOKEN,
        )
        self._invocation_censuses[id(census)] = census
        return census

    def validate_invocation_census(
        self, census: SealedDecompilationInvocationCensus,
    ) -> None:
        if (
            type(census) is not SealedDecompilationInvocationCensus
            or census._factory_token is not _INVOCATION_CENSUS_TOKEN
            or self._invocation_censuses.get(id(census)) is not census
        ):
            raise TypeError("invocation census is not exact factory membership")
        for invocation in self._invocations.values():
            self.validate_invocation_membership(invocation)
        digests = tuple(sorted(self._invocations))
        payload = {
            "result_occurrence_id": self.result_occurrence_id,
            "source_snapshot_fingerprint": self.source_snapshot_fingerprint,
            "execution_identity_digest": self.execution_identity_digest,
            "invocation_receipt_digests": digests,
            "census_schema": "decompilation-invocation-census-v1",
        }
        if (
            census.result_occurrence_id != self.result_occurrence_id
            or census.source_snapshot_fingerprint
            != self.source_snapshot_fingerprint
            or census.execution_identity_digest != self.execution_identity_digest
            or census.invocation_receipt_digests != digests
            or census.census_digest != authority_digest(payload)
        ):
            raise ValueError("decompilation invocation census is stale or invalid")

    def validate_attempt_membership(
        self, attempt: DecompilationAttemptReceipt,
    ) -> None:
        if (
            type(attempt) is not DecompilationAttemptReceipt
            or self._attempts.get(attempt.receipt_digest) is not attempt
        ):
            raise TypeError("decompilation attempt is not exact factory membership")

    def validate_artifact_membership(
        self, artifact: DecompilationArtifactReceipt,
    ) -> None:
        if (
            type(artifact) is not DecompilationArtifactReceipt
            or self._artifacts.get(artifact.artifact_digest) is not artifact
        ):
            raise TypeError("decompilation artifact is not exact factory membership")

    def validate_error_membership(
        self, error: OperationalErrorArtifact,
    ) -> None:
        if (
            type(error) is not OperationalErrorArtifact
            or self._errors.get(id(error)) is not error
        ):
            raise TypeError("operational error is not exact factory membership")

    def capture_attempt_observation(
        self, invocation: DecompilationInvocationReceipt, result: Any,
    ) -> DecompilationAttemptObservation:
        if self._invocations.get(invocation.receipt_digest) is not invocation:
            raise ValueError("attempt invocation is not exact factory membership")
        if invocation.receipt_digest in self._observations:
            raise ValueError("decompilation invocation result was already captured")
        handle = authority_digest({
            "invocation_receipt_digest": invocation.receipt_digest,
            "result_occurrence_id": self.result_occurrence_id,
            "opaque_result_handle_schema": "decompile-results-handle-v1",
        })
        observation = DecompilationAttemptObservation._capture(
            invocation, result, result_handle_digest=handle,
            _factory_token=_OBSERVATION_TOKEN,
        )
        self._observations[invocation.receipt_digest] = observation
        self._results[handle] = result
        return observation

    def issue_attempt(
        self, *, invocation: DecompilationInvocationReceipt,
        observation: DecompilationAttemptObservation,
        target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
    ) -> DecompilationAttemptReceipt:
        if self._observations.get(invocation.receipt_digest) is not observation:
            raise ValueError("attempt observation is not exact factory membership")
        if (
            self._invocations.get(invocation.receipt_digest) is not invocation
            or self._targets.get(id(target)) is not target
            or self._surfaces.get(id(input_surface)) is not input_surface
        ):
            raise ValueError("attempt dependencies are not exact factory membership")
        receipt = DecompilationAttemptReceipt._issue(
            invocation=invocation, observation=observation,
            target=target, input_surface=input_surface,
            _factory_token=_ATTEMPT_TOKEN,
        )
        self._attempts[receipt.receipt_digest] = receipt
        return receipt

    def issue_decompilation_artifact(
        self, *, target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        invocation: DecompilationInvocationReceipt,
        observation: DecompilationAttemptObservation,
        attempt: DecompilationAttemptReceipt,
    ) -> DecompilationArtifactReceipt:
        if (
            self._attempts.get(attempt.receipt_digest) is not attempt
            or self._invocations.get(invocation.receipt_digest) is not invocation
            or self._observations.get(invocation.receipt_digest) is not observation
            or self._targets.get(id(target)) is not target
            or self._surfaces.get(id(input_surface)) is not input_surface
        ):
            raise ValueError("decompilation artifact dependencies are not exact factory membership")
        artifact = DecompilationArtifactReceipt._issue(
            target=target, input_surface=input_surface,
            invocation=invocation, observation=observation, attempt=attempt,
            source_snapshot_fingerprint=self.source_snapshot_fingerprint,
            _factory_token=_DECOMP_ARTIFACT_TOKEN,
        )
        self._artifacts[artifact.artifact_digest] = artifact
        return artifact

    def consume_high_function(
        self, *, artifact: DecompilationArtifactReceipt,
        target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        proof_requirement_id: str,
    ) -> Optional[HighFunctionObservationCapability]:
        _high, capability = self.observe_high_function(
            artifact=artifact, target=target, input_surface=input_surface,
            proof_requirement_id=proof_requirement_id,
        )
        return capability

    def observe_high_function(
        self, *, artifact: DecompilationArtifactReceipt,
        target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
        proof_requirement_id: str,
    ) -> tuple[Any, Optional[HighFunctionObservationCapability]]:
        if (
            self._artifacts.get(artifact.artifact_digest) is not artifact
            or self._targets.get(id(target)) is not target
            or self._surfaces.get(id(input_surface)) is not input_surface
        ):
            raise ValueError("decompilation artifact is not exact factory membership")
        handle = artifact.result_handle_digest
        if handle in self._high_consumed:
            raise ValueError("HighFunction observation capability is one-shot")
        result = self._results.get(handle)
        if result is None:
            raise ValueError("decompilation result handle is unavailable")
        self._high_consumed.add(handle)
        high = _call_noarg(result, "getHighFunction")
        if high is None:
            return None, None
        capability = HighFunctionObservationCapability._issue(
            high=high, artifact=artifact, target=target,
            input_surface=input_surface,
            proof_requirement_id=proof_requirement_id,
            _factory_token=_HIGH_CAPABILITY_TOKEN,
        )
        self._capabilities[id(capability)] = capability
        return high, capability

    def issue_ir_artifact(
        self, *, capability: HighFunctionObservationCapability,
        decompilation_artifact: DecompilationArtifactReceipt,
        target: FunctionDecompilationTarget,
        input_surface: DecompilationAttemptInputSurface,
    ) -> HighFunctionIRArtifact:
        if (
            self._capabilities.get(id(capability)) is not capability
            or self._artifacts.get(decompilation_artifact.artifact_digest) is not decompilation_artifact
            or self._targets.get(id(target)) is not target
            or self._surfaces.get(id(input_surface)) is not input_surface
        ):
            raise ValueError("HighFunction capability is not exact factory membership")
        if id(capability) in self._ir_consumed:
            raise ValueError("HighFunction capability was already consumed")
        artifact = HighFunctionIRArtifact._issue(
            capability=capability,
            decompilation_artifact=decompilation_artifact,
            target=target, input_surface=input_surface,
            _factory_token=_IR_ARTIFACT_TOKEN,
        )
        self._ir_consumed.add(id(capability))
        self._ir_artifacts[id(artifact)] = artifact
        return artifact

    def function_census_from_fixture(
        self, *, query_identity: Any, program_identity: Any,
        function_targets: Iterable[FunctionDecompilationTarget],
        iteration_completed: bool,
        function_lookup_rows: Iterable[tuple[Any, str]] = (),
    ) -> FunctionManagerCensusReceipt:
        if not self._allow_fixture_inputs:
            raise ValueError("fixture function census is disabled in production")
        if type(iteration_completed) is not bool:
            raise TypeError("function census completion must be exact bool")
        targets = tuple(function_targets)
        if any(self._targets.get(id(item)) is not item for item in targets):
            raise ValueError("function census contains non-factory target")
        target_digests = tuple(sorted(item.target_digest for item in targets))
        if len(target_digests) != len(set(target_digests)):
            raise ValueError("function census contains duplicate target")
        query = canonical_value(query_identity)
        program = canonical_value(program_identity)
        fixture_program_seed_digest = authority_digest({
            "fixture_program_identity": program,
            "source_snapshot_fingerprint": self.source_snapshot_fingerprint,
            "fixture_program_seed_schema": "fixture-only-v1",
        })
        lookup_rows = tuple(sorted(
            (
                (
                    canonical_value(key),
                    _exact_string("fixture lookup target digest", digest),
                )
                for key, digest in function_lookup_rows
            ),
            key=lambda item: (authority_digest(item[0]), item[1]),
        ))
        if any(digest not in target_digests for _key, digest in lookup_rows):
            raise ValueError("fixture lookup row target is outside census")
        payload = {
            "query_identity": query,
            "program_identity": program,
            "source_snapshot_fingerprint": self.source_snapshot_fingerprint,
            "program_seed_digest": fixture_program_seed_digest,
            "function_target_digests": target_digests,
            "function_lookup_rows": lookup_rows,
            "iteration_completed": iteration_completed,
        }
        receipt = FunctionManagerCensusReceipt(
            query, program, self.source_snapshot_fingerprint,
            fixture_program_seed_digest, target_digests, lookup_rows,
            iteration_completed, authority_digest(payload),
            _factory_token=_LOOKUP_OUTCOME_TOKEN,
        )
        self._censuses[id(receipt)] = receipt
        return receipt

    def issue_function_census_from_manager(
        self, *, program_seed: GhidraProgramAuthoritySeed,
        query_identity: Any,
    ) -> FunctionManagerCensusReceipt:
        if self._program_seeds.get(id(program_seed)) is not program_seed:
            raise ValueError("census program seed is not exact factory membership")
        function_manager = program_seed.function_manager
        get_functions = getattr(function_manager, "getFunctions", None)
        if not callable(get_functions):
            raise TypeError("FunctionManager complete iterator API is unavailable")
        iterator = get_functions(True)
        if iterator is None:
            raise ValueError("FunctionManager iterator is unavailable")
        targets = []
        lookup_rows = []
        for function in iterator:
            if _call_noarg(function, "getProgram") != program_seed.program:
                raise ValueError("FunctionManager yielded foreign-program function")
            item_target = self.target_from_ghidra(
                program_seed, function,
            )
            targets.append(item_target)
            lookup_rows.extend(
                (key, item_target.target_digest)
                for key in _function_lookup_keys(function)
            )
        target_digests = tuple(sorted(item.target_digest for item in targets))
        if len(target_digests) != len(set(target_digests)):
            raise ValueError("FunctionManager census contains duplicate target")
        query = canonical_value(query_identity)
        program_key = canonical_value(program_seed.program_identity)
        ordered_lookup_rows = tuple(sorted(
            lookup_rows, key=lambda item: (authority_digest(item[0]), item[1])
        ))
        payload = {
            "query_identity": query,
            "program_identity": program_key,
            "source_snapshot_fingerprint": self.source_snapshot_fingerprint,
            "program_seed_digest": program_seed.seed_digest,
            "function_target_digests": target_digests,
            "function_lookup_rows": ordered_lookup_rows,
            "iteration_completed": True,
            "iterator_contract": "FunctionManager.getFunctions(forward=True)-exhausted-v1",
        }
        receipt = FunctionManagerCensusReceipt(
            query, program_key, self.source_snapshot_fingerprint,
            program_seed.seed_digest, target_digests, ordered_lookup_rows,
            True, authority_digest(payload),
            _factory_token=_LOOKUP_OUTCOME_TOKEN,
        )
        self._censuses[id(receipt)] = receipt
        return receipt

    def lookup_found(
        self, *, function_object: Any, target: FunctionDecompilationTarget,
        query_identity: Any,
        program_seed: Optional[GhidraProgramAuthoritySeed] = None,
        program_identity: Any = None,
    ) -> FunctionLookupOutcome:
        if self._targets.get(id(target)) is not target:
            raise ValueError("lookup target is not exact factory membership")
        if program_seed is not None:
            if self._program_seeds.get(id(program_seed)) is not program_seed:
                raise ValueError("lookup program seed is not exact factory membership")
            if (
                _call_noarg(function_object, "getProgram") != program_seed.program
                or target.program_identity != program_seed.program_identity
            ):
                raise ValueError("lookup function/target program differs from seed")
            program_key = program_seed.program_identity
            seed_digest = program_seed.seed_digest
        elif self._allow_fixture_inputs:
            program_key = canonical_value(program_identity)
            seed_digest = None
        else:
            raise ValueError("production FOUND lookup requires program seed")
        outcome = FunctionLookupOutcome._found(
            function_object, target, query_identity=query_identity,
            program_identity=program_key,
            source_snapshot_fingerprint=self.source_snapshot_fingerprint,
            program_seed_digest=seed_digest,
            _factory_token=_LOOKUP_OUTCOME_TOKEN,
        )
        self._lookups[id(outcome)] = outcome
        return outcome

    def lookup_missing(
        self, census_receipt: FunctionManagerCensusReceipt,
    ) -> FunctionLookupOutcome:
        if self._censuses.get(id(census_receipt)) is not census_receipt:
            raise ValueError("lookup census is not exact factory membership")
        outcome = FunctionLookupOutcome._missing(
            census_receipt=census_receipt,
            _factory_token=_LOOKUP_OUTCOME_TOKEN,
        )
        self._lookups[id(outcome)] = outcome
        return outcome

    def lookup_error(
        self, *, catch_site_contract_id: str, exception: BaseException,
        query_identity: Any, program_identity: Any,
    ) -> FunctionLookupOutcome:
        outcome = FunctionLookupOutcome._error(
            catch_site_contract_id=catch_site_contract_id,
            exception=exception, query_identity=query_identity,
            program_identity=program_identity,
            source_snapshot_fingerprint=self.source_snapshot_fingerprint,
            _factory_token=_LOOKUP_OUTCOME_TOKEN,
        )
        self._lookups[id(outcome)] = outcome
        return outcome

    def issue_error(self, **kwargs: Any) -> OperationalErrorArtifact:
        kwargs.setdefault("result_occurrence_id", self.result_occurrence_id)
        kwargs.setdefault(
            "source_snapshot_fingerprint", self.source_snapshot_fingerprint
        )
        lookup = kwargs.get("lookup_outcome")
        if lookup is not None and self._lookups.get(id(lookup)) is not lookup:
            raise ValueError("error lookup outcome is not exact factory membership")
        attempt = kwargs.get("attempt")
        if attempt is not None and self._attempts.get(attempt.receipt_digest) is not attempt:
            raise ValueError("error attempt is not exact factory membership")
        target = kwargs.get("target")
        if target is not None and self._targets.get(id(target)) is not target:
            raise ValueError("error target is not exact factory membership")
        invocation = kwargs.get("invocation")
        if invocation is not None and self._invocations.get(
            invocation.receipt_digest
        ) is not invocation:
            raise ValueError("error invocation is not exact factory membership")
        input_surface = kwargs.get("input_surface")
        if input_surface is not None and self._surfaces.get(
            id(input_surface)
        ) is not input_surface:
            raise ValueError("error input surface is not exact factory membership")
        if invocation is not None:
            kwargs.setdefault(
                "operational_authority_root_digest", self.authority_root_digest
            )
        artifact = OperationalErrorArtifact._issue(
            **kwargs, _factory_token=_ERROR_ARTIFACT_TOKEN,
        )
        self._errors[id(artifact)] = artifact
        return artifact

    def error_event_intent(self, artifact: OperationalErrorArtifact) -> EventIntent:
        if self._errors.get(id(artifact)) is not artifact:
            raise ValueError("error artifact is not exact factory membership")
        return EventIntent(
            EventType.ERROR,
            ErrorEventAuthority(artifact.error_kind, artifact.artifact_digest),
        )

    def owns_target(self, target: FunctionDecompilationTarget) -> bool:
        return self._targets.get(id(target)) is target

    def owns_completion_artifact(self, artifact: Any) -> bool:
        if type(artifact) is DecompilationArtifactReceipt:
            return self._artifacts.get(artifact.artifact_digest) is artifact
        if type(artifact) is HighFunctionIRArtifact:
            return self._ir_artifacts.get(id(artifact)) is artifact
        return False


@dataclass(frozen=True)
class OperationalBlockerSignal:
    reason_id: str
    target: FunctionDecompilationTarget
    evidence_refs: tuple[str, ...]
    producer_id: str
    attempt_id: str = "legacy-single-attempt"

    def __post_init__(self) -> None:
        if self.reason_id not in OPERATIONAL_REASON_SPECS:
            raise ValueError("operational blocker reason is not sealed")
        if type(self.target) is not FunctionDecompilationTarget:
            raise TypeError("operational blocker requires typed target")
        object.__setattr__(self, "evidence_refs", tuple(self.evidence_refs))
        if any(type(item) is not str or not item for item in self.evidence_refs):
            raise TypeError("operational evidence refs are invalid")
        _exact_string("operational producer", self.producer_id)
        _exact_string("operational attempt", self.attempt_id)
        expected = OPERATIONAL_REASON_PRODUCER_CONSERVATION[self.reason_id][1]
        if self.producer_id != expected:
            raise ValueError("operational blocker producer differs from sealed registry")


@dataclass(frozen=True)
class OperationalCompletionSignal:
    blocker: OperationalBlockerSignal
    artifact: Any

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        artifact_digest = getattr(self.artifact, "artifact_digest", None)
        if type(artifact_digest) is not str or not artifact_digest:
            raise TypeError(
                "operational completion signal lacks artifact authority"
            )
        return {
            "reason_id": self.blocker.reason_id,
            "target_digest": self.blocker.target.target_digest,
            "evidence_refs": self.blocker.evidence_refs,
            "producer_id": self.blocker.producer_id,
            "attempt_id": self.blocker.attempt_id,
            "completion_artifact_type": type(self.artifact).__qualname__,
            "completion_artifact_digest": artifact_digest,
        }


class OperationalExtractionPilotEncoder:
    """Encode the two semantic artifact causes and their exact completions."""

    def __init__(
        self, authority_factory: Optional[OperationalExtractionAuthorityFactory] = None
    ) -> None:
        if authority_factory is not None and type(authority_factory) is not OperationalExtractionAuthorityFactory:
            raise TypeError("operational encoder requires exact session factory")
        self._authority_factory = authority_factory
        self._cause_factory = SemanticCauseIdentityFactory(OPERATIONAL_REASON_REGISTRY)
        self._binding_factory = SatisfactionBindingFactory(OPERATIONAL_RECOVERY_REGISTRY)

    def authority_factory_for_session(
        self, session: Any
    ) -> OperationalExtractionAuthorityFactory:
        if self._authority_factory is not None:
            factory = self._authority_factory
        else:
            key = "operational_extraction_authority_factory"
            factory = session.domain_signal_state.get(key)
            if factory is None:
                factory = OperationalExtractionAuthorityFactory(
                    result_occurrence_id=session.identity.result_occurrence_id,
                    source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
                    execution_identity_digest=session.identity.execution_identity_digest,
                )
                session.domain_signal_state[key] = factory
        if (
            factory.result_occurrence_id != session.identity.result_occurrence_id
            or factory.source_snapshot_fingerprint != session.identity.source_snapshot_fingerprint
            or factory.execution_identity_digest != session.identity.execution_identity_digest
        ):
            raise ValueError("operational encoder factory/session identity differs")
        return factory

    def authority_for_signal(
        self, session: Any, signal: OperationalBlockerSignal
    ) -> CauseOccurrenceAuthority:
        if type(signal) is not OperationalBlockerSignal:
            raise TypeError("operational encoder requires exact blocker signal")
        authority_factory = self.authority_factory_for_session(session)
        if not authority_factory.owns_target(signal.target):
            raise ValueError("operational blocker target is not session-factory authority")
        if signal.attempt_id.startswith("decompile-attempt-"):
            authority_factory.validate_attempt_identity_for_signal(
                signal.attempt_id, signal.target,
            )
        if (
            authority_factory.result_occurrence_id
            != session.identity.result_occurrence_id
            or authority_factory.source_snapshot_fingerprint
            != session.identity.source_snapshot_fingerprint
            or authority_factory.execution_identity_digest
            != session.identity.execution_identity_digest
        ):
            raise ValueError("operational encoder factory/session identity differs")
        spec = OPERATIONAL_REASON_SPECS[signal.reason_id]
        missing_fact = (
            "missing_operational_artifact",
            spec.proof_kind,
            DECOMPILER_CONTRACT_VERSION,
        )
        cause = self._cause_factory.create(
            reason_id=signal.reason_id,
            identity_scope=IdentityScope.UNARY,
            target_kind=spec.target_kind,
            canonical_target_key=("function_decompilation_target_v1", signal.target.target_digest),
            missing_semantic_fact=missing_fact,
            semantic_proposition=("artifact_available", spec.proof_kind),
            observation_surface=(
                signal.target.program_identity,
                signal.target.language_id,
                signal.target.compiler_spec_id,
                DECOMPILER_CONTRACT_VERSION,
            ),
            active_semantic_precondition=("function_target_valid", signal.target.target_digest),
            correspondence_contract=None,
        )
        requirement = ProofRequirement(
            "operational-q-" + authority_digest({
                "cause_id": cause.value,
                "proof_kind": spec.proof_kind,
                "attempt_id": signal.attempt_id,
            })[:32],
            spec.proof_kind,
            (
                "operational_artifact_target_v1",
                signal.target.target_digest,
                spec.proof_kind,
            ),
        )
        bound = self._binding_factory.bind(
            contract_definition_id=spec.contract_definition_id,
            contract_version=1,
            bindings={"artifact": requirement},
        )
        occurrence = CauseOccurrence(
            "operational-occ-" + authority_digest({
                "cause_id": cause.value,
                "result_occurrence_id": session.identity.result_occurrence_id,
                "attempt_id": signal.attempt_id,
            })[:32],
            cause,
            signal.reason_id,
            signal.target.target_digest,
            spec.target_kind,
            IdentityScope.UNARY,
            bound.contract_definition_id,
            bound.contract_version,
            bound.normalized_expression_digest,
            bound.bound_expression_digest,
            (requirement.requirement_id,),
            signal.evidence_refs,
            "operational_extraction_producer_signal",
            session.identity.source_snapshot_fingerprint,
            signal.producer_id,
            signal.attempt_id,
        )
        return CauseOccurrenceAuthority(occurrence, bound)

    def __call__(self, session: Any, signal: Any) -> tuple[EventIntent, ...]:
        if type(signal) is OperationalBlockerSignal:
            return (EventIntent(
                EventType.CAUSE_OBSERVED,
                CauseObservedEventAuthority(self.authority_for_signal(session, signal)),
            ),)
        if type(signal) is not OperationalCompletionSignal:
            raise TypeError("operational signal type is not registered")
        authority = self.authority_for_signal(session, signal.blocker)
        proof_kind = OPERATIONAL_REASON_SPECS[signal.blocker.reason_id].proof_kind
        expected_type = (
            DecompilationArtifactReceipt
            if proof_kind == "function_decompilation_artifact"
            else HighFunctionIRArtifact
        )
        if type(signal.artifact) is not expected_type:
            raise TypeError("operational completion artifact type differs")
        if not self.authority_factory_for_session(session).owns_completion_artifact(signal.artifact):
            raise ValueError("operational completion artifact is not exact factory membership")
        if signal.artifact.target_digest != signal.blocker.target.target_digest:
            raise ValueError("operational completion target differs")
        occurrence = authority.occurrence
        bound = authority.bound_contract
        assert bound is not None
        if signal.artifact.result_occurrence_id != session.identity.result_occurrence_id:
            raise ValueError("operational completion result occurrence differs")
        if signal.artifact.proof_requirement_id != occurrence.proof_requirement_ids[0]:
            raise ValueError("operational completion proof requirement differs")
        receipt = RequirementCompletionReceipt(
            occurrence.cause_id.value,
            occurrence.occurrence_id,
            occurrence.proof_requirement_ids[0],
            bound.contract_definition_id,
            bound.contract_version,
            bound.bound_expression_digest,
            (
                signal.artifact.artifact_digest
                if type(signal.artifact) is DecompilationArtifactReceipt
                else signal.artifact.artifact_digest
            ),
            authority_digest({
                "artifact_target_digest": signal.artifact.target_digest,
                "cause_target_digest": signal.blocker.target.target_digest,
                "proof_kind": proof_kind,
            }),
        )
        return (EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(receipt),
        ),)
