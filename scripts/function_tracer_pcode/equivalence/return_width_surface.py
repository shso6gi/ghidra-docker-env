"""Function-scoped return-width facts and pair observation surfaces.

The semantic target and seed types in this module deliberately exclude proof
completion and pair/caller state.  Consumers may use only a ``Proven``
observation result and must apply their own validated parameter/argument
binding after obtaining the side-local terms.
"""

from __future__ import annotations

import hashlib

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Mapping, Optional, Sequence, Tuple, Union

from ..model.render_smt import expression_smt_bit_width
from ..model.signature import (
    get_data_type_display_name,
    get_data_type_path,
    get_declared_type_size_bits,
)
from ..model.structural import expression_provenance_key
from .formula.returns import get_return_size
from .obligations.model import ProofArtifact
from .obligations.snapshot import SnapshotFingerprintCodec


RETURN_WIDTH_IDENTITY_SCHEMA = 1
RETURN_WIDTH_SEED_SCHEMA = 1
RETURN_OBSERVATION_SCHEMA = 1
RETURN_WIDTH_NORMALIZATION_POLICY = "trusted-semantic-width-v1"


def _key(value: Any) -> Any:
    if value is None or isinstance(value, (str, int, bool)):
        return value
    for name in ("stable_key", "to_key"):
        method = getattr(value, name, None)
        if callable(method):
            return SnapshotFingerprintCodec.freeze(method())
    method = getattr(value, "to_dict", None)
    if callable(method):
        return SnapshotFingerprintCodec.freeze(method())
    return SnapshotFingerprintCodec.freeze(value)


class ExtensionKind(str, Enum):
    SAME_WIDTH = "same_width"
    ZERO_EXTEND = "zero_extend"
    SIGN_EXTEND = "sign_extend"
    UNSUPPORTED = "unsupported"


class ObservationScope(str, Enum):
    TOP_LEVEL_RETURN = "top_level_return"
    CALL_SITE_RETURN = "call_site_return"


@dataclass(frozen=True)
class GuardRegionTargetId:
    return_member_identity: Tuple[Any, ...]
    guard_slot_ids: Tuple[Tuple[Any, ...], ...]
    condition_source_refs: Tuple[Tuple[Any, ...], ...] = ()
    cfg_edge_refs: Tuple[Tuple[Any, ...], ...] = ()
    schema_version: int = RETURN_WIDTH_IDENTITY_SCHEMA

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "guard_region_target",
            self.schema_version,
            self.return_member_identity,
            self.guard_slot_ids,
            self.condition_source_refs,
            self.cfg_edge_refs,
        )


@dataclass(frozen=True)
class FunctionReturnWidthTargetId:
    function_identity: Tuple[Any, ...]
    return_member_identity: Tuple[Any, ...]
    guard_region_target: GuardRegionTargetId
    schema_version: int = RETURN_WIDTH_IDENTITY_SCHEMA

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "function_return_width_target",
            self.schema_version,
            self.function_identity,
            self.return_member_identity,
            self.guard_region_target.stable_key(),
        )


@dataclass(frozen=True)
class GuardRegionFact:
    status: str
    condition_keys: Tuple[Tuple[Any, ...], ...] = ()
    unresolved_slots: Tuple[str, ...] = ()
    normalization_provenance: Tuple[Any, ...] = ()

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "guard_region_fact",
            self.status,
            self.condition_keys,
            self.unresolved_slots,
            self.normalization_provenance,
        )


@dataclass(frozen=True)
class ExtensionEvidenceSource:
    kind: str
    storage_value_ref: Tuple[Any, ...]
    payload_value_ref: Tuple[Any, ...]
    producer_refs: Tuple[Tuple[Any, ...], ...] = ()
    identity_flow_kind: Optional[str] = None
    detail: Tuple[Any, ...] = ()
    data_flow_certificate_key: Tuple[Any, ...] = ()

    @property
    def supported(self) -> bool:
        return self.kind != ExtensionKind.UNSUPPORTED.value

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "extension_evidence_source",
            self.kind,
            self.storage_value_ref,
            self.payload_value_ref,
            self.producer_refs,
            self.identity_flow_kind,
            self.detail,
            self.data_flow_certificate_key,
        )


@dataclass(frozen=True)
class FunctionReturnWidthSeed:
    target_id: FunctionReturnWidthTargetId
    guard_region_fact: GuardRegionFact
    storage_width: Optional[int]
    payload_width: Optional[int]
    storage_identity: Tuple[Any, ...]
    payload_value_identity: Tuple[Any, ...]
    calling_convention_fact: Tuple[Any, ...]
    extension_evidence_source: ExtensionEvidenceSource
    unresolved_fact_slots: Tuple[str, ...] = ()
    normalization_policy_digest: str = RETURN_WIDTH_NORMALIZATION_POLICY
    schema_version: int = RETURN_WIDTH_SEED_SCHEMA
    diagnostic_value_expr: Any = field(default=None, compare=False, hash=False, repr=False)

    @property
    def complete(self) -> bool:
        return not self.unresolved_fact_slots and self.extension_evidence_source.supported

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "function_return_width_seed",
            self.schema_version,
            self.target_id.stable_key(),
            self.guard_region_fact.stable_key(),
            self.storage_width,
            self.payload_width,
            self.storage_identity,
            self.payload_value_identity,
            self.calling_convention_fact,
            self.extension_evidence_source.stable_key(),
            self.unresolved_fact_slots,
            self.normalization_policy_digest,
        )

    @property
    def digest(self) -> str:
        return SnapshotFingerprintCodec.digest(self.stable_key())


@dataclass(frozen=True)
class ValidatedUnaryWidthArtifact:
    seed: FunctionReturnWidthSeed
    proof_artifact: ProofArtifact
    relation: str
    validation_basis: Tuple[Any, ...]

    @property
    def artifact_id(self) -> Tuple[Any, ...]:
        return self.proof_artifact.artifact_id


@dataclass(frozen=True)
class PairReturnObservationTargetId:
    scope: str
    left_target_id: FunctionReturnWidthTargetId
    right_target_id: FunctionReturnWidthTargetId
    semantic_anchors: Tuple[Any, ...]
    schema_version: int = RETURN_OBSERVATION_SCHEMA

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "pair_return_observation_target",
            self.schema_version,
            self.scope,
            self.left_target_id.stable_key(),
            self.right_target_id.stable_key(),
            self.semantic_anchors,
        )


@dataclass(frozen=True)
class PairReturnObservationContract:
    target_id: PairReturnObservationTargetId
    left_observation_width: int
    right_observation_width: int
    projection_policy: str
    observation_semantics: Tuple[Any, ...]
    provenance: Tuple[Any, ...]

    @property
    def digest(self) -> str:
        return SnapshotFingerprintCodec.digest((
            self.target_id.stable_key(),
            self.left_observation_width,
            self.right_observation_width,
            self.projection_policy,
            self.observation_semantics,
            self.provenance,
        ))


@dataclass(frozen=True)
class PairReturnObservationSeed:
    """Pair-semantic facts only; proof completion lives in the proof bundle."""

    target_id: PairReturnObservationTargetId
    left_seed_digest: str
    right_seed_digest: str
    observation_scope: str
    semantic_anchors: Tuple[Any, ...]
    unresolved_fact_slots: Tuple[str, ...] = ()

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "pair_return_observation_seed",
            self.target_id.stable_key(),
            self.left_seed_digest,
            self.right_seed_digest,
            self.observation_scope,
            self.semantic_anchors,
            self.unresolved_fact_slots,
        )


@dataclass(frozen=True)
class SideLocalCanonicalTerm:
    owner_function_identity: Tuple[Any, ...]
    parameter_namespace_identity: Tuple[Any, ...]
    target_id: FunctionReturnWidthTargetId
    value_identity: Tuple[Any, ...]
    projection_width: int
    projection_kind: str
    diagnostic_value_expr: Any = field(default=None, compare=False, hash=False, repr=False)

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "side_local_canonical_term",
            self.owner_function_identity,
            self.parameter_namespace_identity,
            self.target_id.stable_key(),
            self.value_identity,
            self.projection_width,
            self.projection_kind,
        )


@dataclass(frozen=True)
class ObservationProofBundle:
    left_artifact_id: Tuple[Any, ...]
    right_artifact_id: Tuple[Any, ...]
    validated_closure_id: Tuple[Any, ...]
    return_coverage_artifact_ids: Tuple[Tuple[Any, ...], ...] = ()

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "observation_proof_bundle",
            self.left_artifact_id,
            self.right_artifact_id,
            self.validated_closure_id,
            self.return_coverage_artifact_ids,
        )


@dataclass(frozen=True)
class PairReturnObservationView:
    contract: PairReturnObservationContract
    proof_bundle: ObservationProofBundle
    left_term: SideLocalCanonicalTerm
    right_term: SideLocalCanonicalTerm
    canonical_comparison_width: int

    @property
    def digest(self) -> str:
        return SnapshotFingerprintCodec.digest((
            self.contract.digest,
            self.proof_bundle.stable_key(),
            self.left_term.stable_key(),
            self.right_term.stable_key(),
            self.canonical_comparison_width,
        ))


@dataclass(frozen=True)
class WidthBlocker:
    blocker_kind: str
    target_key: Tuple[Any, ...]
    missing_slot: str
    detail: str = ""


@dataclass(frozen=True)
class ProvenObservation:
    view: PairReturnObservationView


@dataclass(frozen=True)
class BlockedObservation:
    blockers: Tuple[WidthBlocker, ...]


ObservationBuildResult = Union[ProvenObservation, BlockedObservation]


@dataclass(frozen=True)
class InputCorrespondenceContract:
    left_parameter_identities: Tuple[Tuple[Any, ...], ...]
    right_parameter_identities: Tuple[Tuple[Any, ...], ...]
    correspondence_pairs: Tuple[Tuple[Any, ...], ...]
    input_relation_precondition: Tuple[Any, ...]
    provenance: Tuple[Any, ...]

    @property
    def digest(self) -> str:
        return SnapshotFingerprintCodec.digest((
            "input_correspondence_contract",
            self.left_parameter_identities,
            self.right_parameter_identities,
            self.correspondence_pairs,
            self.input_relation_precondition,
            self.provenance,
        ))


class CorrespondenceValidationStatus(str, Enum):
    TRIVIAL_OBJECT_CORRESPONDENCE = "trivial_object_correspondence"
    NONTRIVIAL_PROVEN_CORRESPONDENCE = "nontrivial_proven_correspondence"
    BLOCKED_CORRESPONDENCE = "blocked_correspondence"


@dataclass(frozen=True)
class InputCorrespondenceProofArtifact:
    correspondence_contract_digest: str
    ordered_parameter_bindings: Tuple[Tuple[Any, ...], ...]
    proof_basis: str = "object_parameter_index_and_exact_query_width_v1"

    @property
    def artifact_id(self) -> Tuple[Any, ...]:
        return (
            "input_correspondence_proof_artifact",
            SnapshotFingerprintCodec.digest((
                self.correspondence_contract_digest,
                self.ordered_parameter_bindings,
                self.proof_basis,
            )),
        )

    def applicable_to(
        self,
        correspondence: InputCorrespondenceContract,
        left_query_parameters: Sequence[Any],
        right_query_parameters: Sequence[Any],
    ) -> bool:
        expected = _validated_nontrivial_parameter_bindings(
            correspondence,
            left_query_parameters,
            right_query_parameters,
        )
        return (
            self.correspondence_contract_digest == correspondence.digest
            and expected is not None
            and self.ordered_parameter_bindings == expected
        )


@dataclass(frozen=True)
class ConsumerBindingReceipt:
    observation_target_key: Tuple[Any, ...]
    observation_view_digest: str
    consumer_scope: str
    correspondence_contract_digest: str
    ordered_substitutions: Tuple[Tuple[Any, ...], ...]
    binding_proof_artifact_ids: Tuple[Tuple[Any, ...], ...]
    proof_closure_id: Tuple[Any, ...]
    substitution_policy_version: str
    projection_lowering_digest: str
    query_parameter_lowering_key: Tuple[Any, ...] = ()
    lowered_left_term: str = ""
    lowered_right_term: str = ""
    proof_bundle_applicability_digest: str = ""
    correspondence_validation_status: str = (
        CorrespondenceValidationStatus.TRIVIAL_OBJECT_CORRESPONDENCE.value
    )

    @property
    def binding_digest(self) -> str:
        return SnapshotFingerprintCodec.digest((
            "consumer_binding_receipt",
            self.observation_target_key,
            self.observation_view_digest,
            self.consumer_scope,
            self.correspondence_contract_digest,
            self.ordered_substitutions,
            self.binding_proof_artifact_ids,
            self.proof_closure_id,
            self.substitution_policy_version,
            self.projection_lowering_digest,
            self.correspondence_validation_status,
            self.query_parameter_lowering_key,
            self.lowered_left_term,
            self.lowered_right_term,
            self.proof_bundle_applicability_digest,
        ))


BindingBuildResult = Union[ConsumerBindingReceipt, BlockedObservation]


@dataclass(frozen=True)
class CallSiteReturnWidthReceipt:
    binding_id: str
    pair_id: str
    observation_scope: str
    observation_width: int
    left_value_identity: Tuple[Any, ...]
    right_value_identity: Tuple[Any, ...]
    raw_left_term: str
    raw_right_term: str
    projection_direction: str
    left_projection_range: Optional[Tuple[int, int]]
    right_projection_range: Optional[Tuple[int, int]]
    projected_left_term: str
    projected_right_term: str
    assertion_text: str
    assertion_digest: str
    return_relation_proof_records: Tuple[Tuple[str, str, str], ...]
    width_relation_contract: Tuple[Any, ...]

    @property
    def binding_digest(self) -> str:
        return SnapshotFingerprintCodec.digest((
            "call_site_return_width_receipt_v2",
            self.binding_id,
            self.pair_id,
            self.observation_scope,
            self.observation_width,
            self.left_value_identity,
            self.right_value_identity,
            self.raw_left_term,
            self.raw_right_term,
            self.projection_direction,
            self.left_projection_range,
            self.right_projection_range,
            self.projected_left_term,
            self.projected_right_term,
            self.assertion_text,
            self.assertion_digest,
            self.return_relation_proof_records,
            self.width_relation_contract,
        ))


def build_call_site_return_width_receipt(
    *,
    binding: Any,
    pair_id: str,
    left_expr: Any,
    right_expr: Any,
    lowered_left_term: str,
    lowered_right_term: str,
) -> Union[CallSiteReturnWidthReceipt, BlockedObservation]:
    left_bits = int(getattr(left_expr, "get_bit_width", lambda: 0)() or 0)
    right_bits = int(getattr(right_expr, "get_bit_width", lambda: 0)() or 0)
    records = tuple(
        item for item in tuple(getattr(binding, "proof_stage_records", ()) or ())
        if item and item[0] == "return_relation" and item[1] and item[2]
    )
    target = ("call_site_return", str(getattr(binding, "binding_id", "")), pair_id)
    if left_bits <= 0 or right_bits <= 0 or len(records) != 1:
        return BlockedObservation((WidthBlocker(
            "call_site_return_width", target, "validated_return_relation_proof",
        ),))
    contract = tuple(getattr(binding, "return_width_relation_contract", ()) or ())
    observation_width = min(left_bits, right_bits)
    wide_side = "none"
    if left_bits != right_bits:
        wide_side = "left" if left_bits > right_bits else "right"
        values = dict(contract) if all(
            isinstance(item, tuple) and len(item) == 2 for item in contract
        ) else {}
        if (
            int(values.get("narrow_bits") or 0) != observation_width
            or int(values.get("wide_bits") or 0) != max(left_bits, right_bits)
            or values.get("wide_side") != wide_side
            or values.get("extension") not in {"sign_extend", "zero_extend"}
            or not values.get("proof_basis")
        ):
            return BlockedObservation((WidthBlocker(
                "call_site_return_width", target, "validated_width_relation_contract",
            ),))
    if not lowered_left_term or not lowered_right_term:
        return BlockedObservation((WidthBlocker(
            "call_site_return_width", target, "ordered_query_lowering",
        ),))
    left_range = (observation_width - 1, 0) if wide_side == "left" else None
    right_range = (observation_width - 1, 0) if wide_side == "right" else None
    projected_left = (
        f"((_ extract {left_range[0]} {left_range[1]}) {lowered_left_term})"
        if left_range is not None else lowered_left_term
    )
    projected_right = (
        f"((_ extract {right_range[0]} {right_range[1]}) {lowered_right_term})"
        if right_range is not None else lowered_right_term
    )
    assertion = f"(assert (= {projected_left} {projected_right}))"
    assertion_digest = hashlib.sha256(assertion.encode("utf-8")).hexdigest()
    return CallSiteReturnWidthReceipt(
        binding_id=str(binding.binding_id),
        pair_id=str(pair_id),
        observation_scope=ObservationScope.CALL_SITE_RETURN.value,
        observation_width=observation_width,
        left_value_identity=tuple(expression_provenance_key(left_expr)),
        right_value_identity=tuple(expression_provenance_key(right_expr)),
        raw_left_term=lowered_left_term,
        raw_right_term=lowered_right_term,
        projection_direction=(
            "none" if wide_side == "none" else f"{wide_side}_to_low_bits"
        ),
        left_projection_range=left_range,
        right_projection_range=right_range,
        projected_left_term=projected_left,
        projected_right_term=projected_right,
        assertion_text=assertion,
        assertion_digest=assertion_digest,
        return_relation_proof_records=records,
        width_relation_contract=contract,
    )


def _parameter_data_type_identity(descriptor: Mapping[str, Any]) -> Optional[Tuple[Any, ...]]:
    """Return an object-derived, replay-stable parameter DataType identity.

    Runtime Ghidra DataType objects must never reach the generic snapshot
    freezer: their Java wrapper identity is neither serializable nor stable
    across analysis sessions.  DataTypePath/name/width are the object API
    projection used elsewhere by the signature model.  A runtime object that
    exposes none of those facts is intentionally unresolved so the binding
    contract can fail closed.
    """
    data_type_obj = descriptor.get("data_type_obj")
    fallback_name = descriptor.get("data_type")
    fallback_size = descriptor.get("size")
    if data_type_obj is None:
        if fallback_name is None and fallback_size is None:
            return ("declared_data_type", None, None)
        return (
            "declared_data_type",
            str(fallback_name or "").strip().lower(),
            int(fallback_size or 0) * 8,
        )

    path = get_data_type_path(data_type_obj)
    display_name = get_data_type_display_name(data_type_obj, None)
    width = get_declared_type_size_bits(data_type_obj)
    if path is None and display_name is None and width is None:
        return None
    return (
        "runtime_data_type",
        path,
        str(display_name).strip().lower() if display_name is not None else None,
        int(width) if width is not None else None,
    )


def _parameter_identity(parameter: Any, ordinal: int) -> Optional[Tuple[Any, ...]]:
    if isinstance(parameter, Mapping):
        descriptor = parameter
    else:
        to_dict = getattr(parameter, "to_dict", None)
        descriptor = to_dict() if callable(to_dict) else {
            "index": getattr(parameter, "index", ordinal),
            "size": getattr(parameter, "size", None),
            "data_type": getattr(parameter, "data_type", None),
            "storage_info": getattr(parameter, "storage_info", None),
        }
    raw_index = descriptor.get("index", ordinal)
    parameter_index = ordinal if raw_index is None else int(raw_index)
    data_type_identity = _parameter_data_type_identity(descriptor)
    if data_type_identity is None:
        return None
    return (
        "parameter_object",
        parameter_index,
        int(descriptor.get("size", 0) or 0),
        data_type_identity,
        _key(descriptor.get("storage_info") or descriptor.get("storage")),
    )


def build_input_correspondence_contract(
    left_parameters: Sequence[Any],
    right_parameters: Sequence[Any],
) -> Union[InputCorrespondenceContract, BlockedObservation]:
    left_raw_ids = tuple(
        _parameter_identity(item, index) for index, item in enumerate(left_parameters)
    )
    right_raw_ids = tuple(
        _parameter_identity(item, index) for index, item in enumerate(right_parameters)
    )
    if any(item is None for item in left_raw_ids + right_raw_ids):
        return BlockedObservation((WidthBlocker(
            "input_correspondence",
            ("top_level_parameters", "unresolved_runtime_data_type"),
            "object_derived_parameter_data_type_identity",
        ),))
    left_ids = tuple(item for item in left_raw_ids if item is not None)
    right_ids = tuple(item for item in right_raw_ids if item is not None)
    if len(left_ids) != len(right_ids):
        return BlockedObservation((WidthBlocker(
            "input_correspondence",
            ("top_level_parameters", left_ids, right_ids),
            "parameter_arity",
        ),))
    left_by_index = {item[1]: (ordinal, item) for ordinal, item in enumerate(left_ids)}
    right_by_index = {item[1]: (ordinal, item) for ordinal, item in enumerate(right_ids)}
    if (
        len(left_by_index) != len(left_ids)
        or len(right_by_index) != len(right_ids)
        or set(left_by_index) != set(right_by_index)
    ):
        return BlockedObservation((WidthBlocker(
            "input_correspondence",
            ("top_level_parameters", left_ids, right_ids),
            "parameter_index_bijection",
        ),))
    pairs = tuple(
        (
            left_by_index[index][0],
            right_by_index[index][0],
            left_by_index[index][1],
            right_by_index[index][1],
        )
        for index in sorted(left_by_index)
    )
    return InputCorrespondenceContract(
        left_parameter_identities=left_ids,
        right_parameter_identities=right_ids,
        correspondence_pairs=pairs,
        input_relation_precondition=("corresponding_source_inputs_equal",),
        provenance=("function_parameter_objects",),
    )


def build_top_level_consumer_binding_receipt(
    observation: PairReturnObservationView,
    correspondence: InputCorrespondenceContract,
    *,
    nontrivial_binding_proof_artifacts: Sequence[InputCorrespondenceProofArtifact] = (),
    proof_closure_id: Tuple[Any, ...],
    left_query_parameters: Sequence[Any] = (),
    right_query_parameters: Sequence[Any] = (),
    lowered_left_term: str = "",
    lowered_right_term: str = "",
    proof_bundle_applicability_digest: str = "",
) -> BindingBuildResult:
    nontrivial = any(
        left_ordinal != right_ordinal or left_identity[2:] != right_identity[2:]
        for left_ordinal, right_ordinal, left_identity, right_identity
        in correspondence.correspondence_pairs
    )
    proof_artifacts = tuple(nontrivial_binding_proof_artifacts)
    proof_ids = tuple(artifact.artifact_id for artifact in proof_artifacts)
    if nontrivial and (
        not proof_artifacts
        or not all(artifact.applicable_to(
            correspondence,
            left_query_parameters,
            right_query_parameters,
        ) for artifact in proof_artifacts)
    ):
        return BlockedObservation((WidthBlocker(
            "input_correspondence",
            observation.contract.target_id.stable_key(),
            "nontrivial_parameter_binding_proof",
        ),))
    status = (
        CorrespondenceValidationStatus.NONTRIVIAL_PROVEN_CORRESPONDENCE.value
        if nontrivial
        else CorrespondenceValidationStatus.TRIVIAL_OBJECT_CORRESPONDENCE.value
    )
    if (
        len(left_query_parameters) != len(correspondence.left_parameter_identities)
        or len(right_query_parameters) != len(correspondence.right_parameter_identities)
    ):
        return BlockedObservation((WidthBlocker(
            "input_correspondence",
            observation.contract.target_id.stable_key(),
            "query_parameter_lowering_arity",
        ),))
    substitutions = tuple(
        (
            "bind",
            ordinal,
            left_ordinal,
            right_ordinal,
            left_identity,
            right_identity,
            _query_parameter_identity(left_query_parameters[left_ordinal]),
            _query_parameter_identity(right_query_parameters[right_ordinal]),
        )
        for ordinal, (
            left_ordinal,
            right_ordinal,
            left_identity,
            right_identity,
        ) in enumerate(correspondence.correspondence_pairs)
    )
    query_lowering_key = (
        "ordered_query_parameter_lowering_v1",
        tuple(_query_parameter_identity(item) for item in left_query_parameters),
        tuple(_query_parameter_identity(item) for item in right_query_parameters),
    )
    if not lowered_left_term or not lowered_right_term or not proof_bundle_applicability_digest:
        return BlockedObservation((WidthBlocker(
            "consumer_binding",
            observation.contract.target_id.stable_key(),
            "query_lowering_or_proof_applicability",
        ),))
    lowering = SnapshotFingerprintCodec.digest((
        "bind_then_project_v1",
        observation.left_term.stable_key(),
        observation.right_term.stable_key(),
        substitutions,
        query_lowering_key,
        lowered_left_term,
        lowered_right_term,
        proof_bundle_applicability_digest,
    ))
    return ConsumerBindingReceipt(
        observation_target_key=observation.contract.target_id.stable_key(),
        observation_view_digest=observation.digest,
        consumer_scope=ObservationScope.TOP_LEVEL_RETURN.value,
        correspondence_contract_digest=correspondence.digest,
        ordered_substitutions=substitutions,
        binding_proof_artifact_ids=proof_ids,
        proof_closure_id=proof_closure_id,
        substitution_policy_version="bind_function_parameters_then_project_v1",
        projection_lowering_digest=lowering,
        correspondence_validation_status=status,
        query_parameter_lowering_key=query_lowering_key,
        lowered_left_term=lowered_left_term,
        lowered_right_term=lowered_right_term,
        proof_bundle_applicability_digest=proof_bundle_applicability_digest,
    )


def _query_parameter_identity(parameter: Any) -> Tuple[Any, ...]:
    return (
        "query_parameter",
        int(getattr(parameter, "index", -1)),
        str(getattr(parameter, "original_name", "") or ""),
        str(getattr(parameter, "smt_name", "") or ""),
        int(getattr(parameter, "bit_width", 0) or 0),
    )


def _validated_nontrivial_parameter_bindings(
    correspondence: InputCorrespondenceContract,
    left_query_parameters: Sequence[Any],
    right_query_parameters: Sequence[Any],
) -> Optional[Tuple[Tuple[Any, ...], ...]]:
    if (
        len(left_query_parameters) != len(correspondence.left_parameter_identities)
        or len(right_query_parameters) != len(correspondence.right_parameter_identities)
    ):
        return None
    bindings = []
    for left_ordinal, right_ordinal, left_identity, right_identity in (
        correspondence.correspondence_pairs
    ):
        left_query = left_query_parameters[left_ordinal]
        right_query = right_query_parameters[right_ordinal]
        left_bits = int(getattr(left_query, "bit_width", 0) or 0)
        right_bits = int(getattr(right_query, "bit_width", 0) or 0)
        left_index = int(getattr(left_query, "index", -1))
        right_index = int(getattr(right_query, "index", -1))
        if (
            left_index != int(left_identity[1])
            or right_index != int(right_identity[1])
            or left_bits <= 0
            or left_bits != right_bits
            or left_bits != int(left_identity[2]) * 8
            or right_bits != int(right_identity[2]) * 8
        ):
            return None
        bindings.append((
            "source_parameter_ordinal_binding",
            int(left_identity[1]),
            left_ordinal,
            right_ordinal,
            left_identity,
            right_identity,
            _query_parameter_identity(left_query),
            _query_parameter_identity(right_query),
            left_bits,
        ))
    return tuple(bindings)


def prove_object_query_input_correspondence(
    correspondence: InputCorrespondenceContract,
    left_query_parameters: Sequence[Any],
    right_query_parameters: Sequence[Any],
) -> Optional[InputCorrespondenceProofArtifact]:
    """Certify nontrivial storage/type mappings against the exact query inputs.

    Parameter ordinal comes from the Ghidra parameter objects.  Width is
    checked independently against both side-local descriptors and the exact
    query symbols.  The artifact therefore permits storage/type representation
    differences without claiming that differently sized source inputs match.
    """
    nontrivial = any(
        left_ordinal != right_ordinal or left_identity[2:] != right_identity[2:]
        for left_ordinal, right_ordinal, left_identity, right_identity
        in correspondence.correspondence_pairs
    )
    if not nontrivial:
        return None
    bindings = _validated_nontrivial_parameter_bindings(
        correspondence,
        left_query_parameters,
        right_query_parameters,
    )
    if bindings is None:
        return None
    return InputCorrespondenceProofArtifact(
        correspondence_contract_digest=correspondence.digest,
        ordered_parameter_bindings=bindings,
    )


def _function_identity(analysis: Any) -> Tuple[Any, ...]:
    method = getattr(analysis, "outcome_function_identity", None)
    if callable(method):
        return tuple(method())
    function_ref = getattr(analysis, "function_ref", None)
    return (
        "function_identity_v1",
        getattr(analysis, "binary_id", None),
        _key(function_ref),
        getattr(analysis, "entry_point", None),
    )


def _return_member_identity(case: Any) -> Tuple[Any, ...]:
    info = getattr(case, "return_info", None)
    op_ref = getattr(info, "pcode_op_ref", None)
    summary_id = getattr(info, "summary_candidate_id", None)
    return (
        "return_member_v1",
        ("pcode_op_ref", _key(op_ref)),
        ("summary_candidate_id", _key(summary_id)),
        ("address", getattr(info, "address", None)),
        ("source_indices", tuple(int(v) for v in getattr(case, "source_indices", ()) or ())),
        ("return_kind", getattr(info, "return_kind", "exact")),
    )


def build_function_return_width_target(analysis: Any, case: Any) -> FunctionReturnWidthTargetId:
    member = _return_member_identity(case)
    conditions = tuple(getattr(case, "conditions", ()) or ())
    slots = tuple(
        ("guard_slot", int(index), tuple(getattr(case, "source_indices", ()) or ()))
        for index, _condition in enumerate(conditions)
    )
    if not slots:
        slots = (("unconditional_guard", member),)
    guard = GuardRegionTargetId(
        return_member_identity=member,
        guard_slot_ids=slots,
    )
    return FunctionReturnWidthTargetId(_function_identity(analysis), member, guard)


def _producer_refs(case: Any) -> Tuple[Tuple[Any, ...], ...]:
    info = getattr(case, "return_info", None)
    refs = tuple(getattr(info, "return_value_pcode_op_refs", ()) or ())
    return tuple(_key(ref) for ref in refs if ref is not None)


def _extension_kind(case: Any, payload_bits: Optional[int], storage_bits: Optional[int]) -> str:
    certificate = getattr(
        getattr(case, "return_info", None),
        "return_value_flow_certificate",
        None,
    )
    extension_index = getattr(certificate, "extension_step_index", None)
    steps = tuple(getattr(certificate, "steps", ()) or ())
    if isinstance(extension_index, int) and 0 <= extension_index < len(steps):
        mnemonic = str(getattr(steps[extension_index].op_ref, "mnemonic", "") or "").upper()
        if mnemonic == "INT_ZEXT":
            return ExtensionKind.ZERO_EXTEND.value
        if mnemonic == "INT_SEXT":
            return ExtensionKind.SIGN_EXTEND.value
    if payload_bits and storage_bits and payload_bits == storage_bits:
        return ExtensionKind.SAME_WIDTH.value
    value = getattr(case, "value_expr", None)
    operator = str(getattr(value, "operator", "") or "").upper()
    if operator == "INT_ZEXT":
        return ExtensionKind.ZERO_EXTEND.value
    if operator == "INT_SEXT":
        return ExtensionKind.SIGN_EXTEND.value
    return ExtensionKind.UNSUPPORTED.value


def _extension_flow_evidence(
    case: Any,
    *,
    kind: str,
    storage_bits: Optional[int],
    payload_bits: Optional[int],
    payload_expression_identity: Tuple[Any, ...],
) -> Optional[ExtensionEvidenceSource]:
    """Validate the complete object flow before accepting an extension relation."""

    info = getattr(case, "return_info", None)
    certificate = getattr(info, "return_value_flow_certificate", None)
    steps = tuple(getattr(certificate, "steps", ()) or ())
    extension_index = getattr(certificate, "extension_step_index", None)
    if (
        certificate is None
        or not isinstance(extension_index, int)
        or not (0 <= extension_index < len(steps))
        or getattr(info, "pcode_op_ref", None) != getattr(certificate, "return_op_ref", None)
        or int(getattr(certificate, "return_input_index", -1)) != 1
        or not steps
    ):
        return None
    if steps[0].output_ref != certificate.return_input_ref:
        return None
    for previous, current in zip(steps, steps[1:]):
        index = int(previous.traversed_input_index)
        if index < 0 or index >= len(previous.input_refs):
            return None
        if previous.input_refs[index] != current.output_ref:
            return None
    for step in steps[:extension_index]:
        mnemonic = str(step.op_ref.mnemonic or "").upper()
        if mnemonic not in {"COPY", "CAST"}:
            return None
        if len(step.input_refs) != 1 or step.input_refs[0].size != step.output_ref.size:
            return None
    extension = steps[extension_index]
    expected_mnemonic = (
        "INT_ZEXT" if kind == ExtensionKind.ZERO_EXTEND.value else "INT_SEXT"
    )
    if str(extension.op_ref.mnemonic or "").upper() != expected_mnemonic:
        return None
    if len(extension.input_refs) != 1 or extension.traversed_input_index != 0:
        return None
    if not storage_bits or not payload_bits:
        return None
    if (
        certificate.return_input_ref.size * 8 != int(storage_bits)
        or extension.output_ref.size * 8 != int(storage_bits)
        or extension.input_refs[0].size * 8 != int(payload_bits)
        or extension.op_ref.output_size != extension.output_ref.size
        or extension.op_ref.input_size(0) != extension.input_refs[0].size
    ):
        return None
    if (
        not certificate.payload_expression_identity
        or tuple(certificate.payload_expression_identity) != payload_expression_identity
    ):
        return None
    return ExtensionEvidenceSource(
        kind=kind,
        storage_value_ref=certificate.return_input_ref.stable_key(),
        payload_value_ref=extension.input_refs[0].stable_key(),
        producer_refs=tuple(step.op_ref.stable_key() for step in steps),
        identity_flow_kind="certified_return_input_def_chain",
        detail=(
            ("extension_step_index", extension_index),
            ("payload_expression_identity", payload_expression_identity),
        ),
        data_flow_certificate_key=certificate.stable_key(),
    )


def extract_function_return_width_seed(analysis: Any, case: Any) -> FunctionReturnWidthSeed:
    target = build_function_return_width_target(analysis, case)
    conditions = tuple(getattr(case, "conditions", ()) or ())
    condition_keys = tuple(
        tuple(expression_provenance_key(getattr(condition, "expression", None)))
        for condition in conditions
    )
    guard = GuardRegionFact(
        status="structural" if all(condition_keys) else "unresolved",
        condition_keys=condition_keys,
        unresolved_slots=() if all(condition_keys) else ("condition_source_refs",),
        normalization_provenance=(RETURN_WIDTH_NORMALIZATION_POLICY,),
    )
    try:
        storage_width = int(get_return_size(analysis) or 0) or None
    except (TypeError, ValueError):
        storage_width = None
    value = getattr(case, "value_expr", None)
    try:
        rendered_value_width = int(expression_smt_bit_width(value) or 0) or None
    except (TypeError, ValueError, AttributeError):
        rendered_value_width = None
    value_identity = tuple(expression_provenance_key(value))
    kind = _extension_kind(case, rendered_value_width, storage_width)
    producer_refs = _producer_refs(case)
    payload_ref = value_identity
    if (
        kind in {ExtensionKind.ZERO_EXTEND.value, ExtensionKind.SIGN_EXTEND.value}
        and str(getattr(value, "operator", "") or "").upper()
        in {"INT_ZEXT", "INT_SEXT"}
        and getattr(value, "operands", None)
    ):
        payload_ref = tuple(expression_provenance_key(value.operands[0]))
    payload_width = rendered_value_width
    if kind in {ExtensionKind.ZERO_EXTEND.value, ExtensionKind.SIGN_EXTEND.value}:
        certificate = getattr(
            getattr(case, "return_info", None),
            "return_value_flow_certificate",
            None,
        )
        extension_index = getattr(certificate, "extension_step_index", None)
        steps = tuple(getattr(certificate, "steps", ()) or ())
        if isinstance(extension_index, int) and 0 <= extension_index < len(steps):
            extension_step = steps[extension_index]
            input_refs = tuple(getattr(extension_step, "input_refs", ()) or ())
            if (
                int(getattr(extension_step, "traversed_input_index", -1)) == 0
                and len(input_refs) == 1
            ):
                certified_payload_width = int(input_refs[0].size or 0) * 8
                if certified_payload_width > 0:
                    payload_width = certified_payload_width
    if kind in {ExtensionKind.ZERO_EXTEND.value, ExtensionKind.SIGN_EXTEND.value}:
        evidence = _extension_flow_evidence(
            case,
            kind=kind,
            storage_bits=storage_width,
            payload_bits=payload_width,
            payload_expression_identity=payload_ref,
        ) or ExtensionEvidenceSource(
            kind=ExtensionKind.UNSUPPORTED.value,
            storage_value_ref=(),
            payload_value_ref=(),
            producer_refs=producer_refs,
            detail=(("rejected_relation", kind),),
        )
    else:
        evidence = ExtensionEvidenceSource(
            kind=kind,
            storage_value_ref=value_identity,
            payload_value_ref=payload_ref,
            producer_refs=producer_refs,
            identity_flow_kind=("same_expression" if kind == ExtensionKind.SAME_WIDTH.value else None),
        )
    missing = []
    missing.extend(guard.unresolved_slots)
    if storage_width is None:
        missing.append("return_storage_fact")
    if payload_width is None:
        missing.append("payload_width_fact")
    if not evidence.supported:
        missing.append("extension_evidence_fact")
    surface = getattr(analysis, "get_comparison_surface", lambda: None)()
    storage_identity = (
        "comparison_surface",
        getattr(surface, "kind", None),
        storage_width,
        getattr(analysis, "program_is_big_endian", None),
    )
    return FunctionReturnWidthSeed(
        target_id=target,
        guard_region_fact=guard,
        storage_width=storage_width,
        payload_width=payload_width,
        storage_identity=storage_identity,
        payload_value_identity=payload_ref,
        calling_convention_fact=(
            "return_type_provenance",
            _key(getattr(analysis, "return_type_provenance", {})),
        ),
        extension_evidence_source=evidence,
        unresolved_fact_slots=tuple(missing),
        diagnostic_value_expr=value,
    )


def _emit_return_observation_need_blocker(
    left: FunctionReturnWidthSeed,
    right: FunctionReturnWidthSeed,
    pair_seed: PairReturnObservationSeed,
) -> None:
    """Publish the exact proof gap for a pair with no common observation width."""

    from .v2.abi_width_readonly import (
        AbiWidthReadonlyBlockerSignal,
        ReturnObservationNeedSeed,
    )
    from .v2.production_signals import emit_abi_width_readonly_signal

    emit_abi_width_readonly_signal(
        AbiWidthReadonlyBlockerSignal.from_observation_need_seed(
            ReturnObservationNeedSeed.from_pair_seed(left, right, pair_seed)
        ),
        producer_site_manifest_id=(
            "return-width-observation-contract-blocker"
        ),
    )


def build_top_level_observation_contract(
    left: FunctionReturnWidthSeed,
    right: FunctionReturnWidthSeed,
) -> Union[PairReturnObservationContract, BlockedObservation]:
    target = PairReturnObservationTargetId(
        scope=ObservationScope.TOP_LEVEL_RETURN.value,
        left_target_id=left.target_id,
        right_target_id=right.target_id,
        semantic_anchors=(left.target_id.function_identity, right.target_id.function_identity),
    )
    blockers = []
    for side, seed in (("left", left), ("right", right)):
        for slot in seed.unresolved_fact_slots:
            blockers.append(WidthBlocker(
                "unary_width",
                seed.target_id.stable_key(),
                slot,
                side,
            ))
    if blockers:
        try:
            from .v2.abi_width_readonly import AbiWidthReadonlyBlockerSignal
            from .v2.production_signals import emit_abi_width_readonly_signal

            for seed in (left, right):
                for slot in seed.unresolved_fact_slots:
                    if slot in {
                        "return_storage_fact", "payload_width_fact",
                        "extension_evidence_fact",
                    }:
                        emit_abi_width_readonly_signal(
                            AbiWidthReadonlyBlockerSignal.from_width_seed(seed, slot),
                            producer_site_manifest_id=(
                                "return-width-unary-provenance-blocker"
                            ),
                        )
        except Exception as exc:
            from .v2.production_signals import record_production_pilot_shadow_error

            record_production_pilot_shadow_error(exc)
        return BlockedObservation(tuple(blockers))
    left_declared = _declared_observation_width(left.calling_convention_fact)
    right_declared = _declared_observation_width(right.calling_convention_fact)
    observation_width = None
    provenance_kind = "source_declared_return_width"
    if left_declared is not None and left_declared == right_declared:
        observation_width = left_declared
    elif (
        int(left.payload_width or 0) > 0
        and int(left.payload_width or 0) == int(right.payload_width or 0)
        and left.extension_evidence_source.supported
        and right.extension_evidence_source.supported
    ):
        # The eventual observation view validates both unary artifacts.  This
        # contract may therefore use their common semantic payload width when
        # source declaration provenance is unavailable in a stripped binary.
        observation_width = int(left.payload_width)
        provenance_kind = "common_validated_semantic_payload_width"
    if observation_width is None:
        try:
            pair_seed = build_pair_return_observation_seed(left, right)
            _emit_return_observation_need_blocker(
                left, right, pair_seed
            )
        except Exception as exc:
            from .v2.production_signals import record_production_pilot_shadow_error

            record_production_pilot_shadow_error(exc)
        return BlockedObservation((WidthBlocker(
            "observation_contract",
            target.stable_key(),
            "top_level_comparison_contract",
            "declared observation width is missing or incompatible",
        ),))
    if (
        observation_width > int(left.storage_width or 0)
        or observation_width > int(right.storage_width or 0)
    ):
        try:
            from .v2.abi_width_readonly import (
                AbiWidthReadonlyBlockerSignal,
                ProjectionNotFormable,
                ReturnObservationProjectionSeed,
            )
            from .v2.production_signals import (
                emit_abi_width_readonly_signal,
                register_abi_width_solver_candidate,
            )

            pair_seed = build_pair_return_observation_seed(left, right)
            try:
                projection_seed = ReturnObservationProjectionSeed.from_pair_seed(
                    left, right, pair_seed
                )
            except ProjectionNotFormable:
                _emit_return_observation_need_blocker(
                    left, right, pair_seed
                )
            else:
                for reason_id in (
                    "return_observation_contract_unproven",
                    "return_high_bit_relation_unproven",
                ):
                    signal = AbiWidthReadonlyBlockerSignal.from_projection_seed(
                        reason_id, projection_seed
                    )
                    emit_abi_width_readonly_signal(
                        signal,
                        producer_site_manifest_id=(
                            "return-width-projection-relation-blocker"
                        ),
                    )
                    if reason_id == "return_high_bit_relation_unproven":
                        register_abi_width_solver_candidate(
                            signal, projection_seed
                        )
        except Exception as exc:
            from .v2.production_signals import record_production_pilot_shadow_error

            record_production_pilot_shadow_error(exc)
        return BlockedObservation((WidthBlocker(
            "pair_width_compatibility",
            target.stable_key(),
            "projection_applicability",
            "observation exceeds return storage width",
        ),))
    return PairReturnObservationContract(
        target_id=target,
        left_observation_width=observation_width,
        right_observation_width=observation_width,
        projection_policy=(
            "abi_declared_return_width_v1"
            if provenance_kind == "source_declared_return_width"
            else "validated_semantic_payload_width_v1"
        ),
        observation_semantics=("return_value", provenance_kind),
        provenance=(left.calling_convention_fact, right.calling_convention_fact),
    )


def build_pair_return_observation_seed(
    left: FunctionReturnWidthSeed,
    right: FunctionReturnWidthSeed,
    *,
    scope: str = ObservationScope.TOP_LEVEL_RETURN.value,
    semantic_anchors: Sequence[Any] = (),
) -> PairReturnObservationSeed:
    anchors = tuple(semantic_anchors) or (
        left.target_id.function_identity,
        right.target_id.function_identity,
    )
    target = PairReturnObservationTargetId(
        scope=scope,
        left_target_id=left.target_id,
        right_target_id=right.target_id,
        semantic_anchors=anchors,
    )
    missing = tuple(
        f"left:{slot}" for slot in left.unresolved_fact_slots
    ) + tuple(f"right:{slot}" for slot in right.unresolved_fact_slots)
    return PairReturnObservationSeed(
        target_id=target,
        left_seed_digest=left.digest,
        right_seed_digest=right.digest,
        observation_scope=scope,
        semantic_anchors=anchors,
        unresolved_fact_slots=missing,
    )


def _declared_observation_width(calling_convention_fact: Tuple[Any, ...]) -> Optional[int]:
    def find_width(target_name: str) -> Optional[int]:
        stack = [calling_convention_fact]
        while stack:
            value = stack.pop()
            if isinstance(value, tuple):
                if len(value) == 2 and value[0] == target_name:
                    try:
                        bits = int(value[1])
                    except (TypeError, ValueError):
                        bits = 0
                    if bits > 0:
                        return bits
                stack.extend(reversed(value))
        return None

    # Source-adjacent declaration evidence describes the language-level
    # observation contract.  A decompiler-inferred storage type may be wider
    # and is only a fallback when source declaration evidence is unavailable.
    source_width = find_width("source_declared_return_type_width")
    if source_width is not None:
        return source_width
    return find_width("declared_return_type_width")


def build_observation_view(
    contract: PairReturnObservationContract,
    left: ValidatedUnaryWidthArtifact,
    right: ValidatedUnaryWidthArtifact,
    *,
    validated_closure_id: Tuple[Any, ...],
    return_coverage_artifact_ids: Sequence[Tuple[Any, ...]] = (),
    return_coverage_artifacts_validated: bool = False,
) -> ObservationBuildResult:
    if not left.proof_artifact.is_validated or not right.proof_artifact.is_validated:
        return BlockedObservation((WidthBlocker(
            "unary_width",
            contract.target_id.stable_key(),
            "validated_unary_width_artifact",
        ),))
    if left.seed.target_id != contract.target_id.left_target_id:
        return BlockedObservation((WidthBlocker(
            "unary_width",
            contract.target_id.stable_key(),
            "left_target_applicability",
        ),))
    if right.seed.target_id != contract.target_id.right_target_id:
        return BlockedObservation((WidthBlocker(
            "unary_width",
            contract.target_id.stable_key(),
            "right_target_applicability",
        ),))
    if not return_coverage_artifact_ids or not return_coverage_artifacts_validated:
        return BlockedObservation((WidthBlocker(
            "return_coverage",
            contract.target_id.stable_key(),
            "return_coverage_artifact_ids",
        ),))
    if contract.left_observation_width != contract.right_observation_width:
        return BlockedObservation((WidthBlocker(
            "pair_width_compatibility",
            contract.target_id.stable_key(),
            "canonical_width_alignment",
        ),))
    width = int(contract.left_observation_width)
    bundle = ObservationProofBundle(
        left.artifact_id,
        right.artifact_id,
        validated_closure_id,
        tuple(return_coverage_artifact_ids),
    )
    def term(item: ValidatedUnaryWidthArtifact) -> SideLocalCanonicalTerm:
        seed = item.seed
        return SideLocalCanonicalTerm(
            owner_function_identity=seed.target_id.function_identity,
            parameter_namespace_identity=("function_parameters", seed.target_id.function_identity),
            target_id=seed.target_id,
            value_identity=seed.payload_value_identity,
            projection_width=width,
            projection_kind=contract.projection_policy,
            diagnostic_value_expr=seed.diagnostic_value_expr,
        )
    return ProvenObservation(PairReturnObservationView(
        contract=contract,
        proof_bundle=bundle,
        left_term=term(left),
        right_term=term(right),
        canonical_comparison_width=width,
    ))
